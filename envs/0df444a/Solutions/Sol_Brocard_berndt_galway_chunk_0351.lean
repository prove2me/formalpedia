-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0351
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:21:54.997204+00:00
-- url     : https://prove2.me/submissions/36fea506-cb8b-4ac2-b55a-7333c546671c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 62949643 ≤ n < 63129499 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 62950893 1250 62949643 62949659
    0xa0807031b0b04061d0a0909020306060102031903180507061e02010504030e040b0411041e0b19140f030103030906020c0307060801091505040207060203040213020c06070c0302031201 80
    0x111500003101c03003908500c8003411014140318403009580010501d542400d040100494084014510100380541c1c01c14039030b603d540751542c880c0040c0600c80c10100341020705005152a0140250400d811503000304843c0c2d800100c005014990b41d50240790100d01407141a507801850f6610f00b4000d007442c000e4810002d5015000b458a83c02c036803106425003c00d0030210420390885904507000f6000c036100c180900c00515281d8400102040c004000040311300d442c07551901180c1040e0131a0100c900c1c1440358801c1c1c8000a0a908002c00603e8005850210003002038502ca515580b041c0061104c180404100c03c403a120650301011043c4600395200d43c0d40b410001c0203907202c1e100744d00150050103150021400d0109a4405466403601d8034400e691a10440000800605440d248031052000001c80c540da924001005114020f0384d0168507414280100641c0000074198a441e0f02e204200384030300c0c540c01013011588000e0074282892505810309003a411807249414405c82441c00000104602c4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 62952143 1250 62950893 62950903
    0x604080111030f01060903030e090405031c0218060708070b06030a0615030b0919030f030e0307060c030513050c041d030307030501030b010f1404020a05090603010b071e1101080402040b0a08 83
    0x20210f2080c0040d640d980b640d0075604021030b0b0001400007403103100d03400c9440c2440984107400c2440740b821a03142c40001c40e0600ca009010325406c46680b9000142e10502d600c940c1e4001d01c64100844150b480c0c032025545060562044101c000c1c400300001d00000c200d0394060014141c4a904a401440000085410254000c020340400c68003110700310040303510034000040c84100c2d001000c4a802ca4500341d0f4a06480600e10408220109500d410301c450f581c03003090000d07000341c82c407885003c50111650034015065650003820305c006034000640350301c0840ea0024034045140d4003502c00151340d40b012030303007040f082c9020440d6a160303200001c1440181c80e8540d0080c2c0c1281d01605004049903201c030541c50200384d86c0d1250b03130004860b1852500b030524290b4010100c82d420780c1400c610b460082e0b0042080d5820036807000740000801710300803080c0035803074403001311180c1c2c000001503d0080320343c6d8400d005145519941e040014a50001d4115151548003c00803013008000c110116a210301c42d80daa6 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 62953393 1250 62952143 62952151
    0x24040b040303030b0901090b010c03030f0b06070308090111030c04170a0606030b04050c12030403021e0d0b0106020c0117190605030303130510020406080c0a021609020921030d0209060408011103 85
    0x346505c440009a8a4070300d00c181d80410740169184051000c040d20110301800443c01d56030411580c5031100c0540d83c0d248002050400d2007078451a200e4070f440b004d22400c46600341408007a5034410001c00c50b24489000450381030301c9400d0410301c2c10703000b42c407440343c9021503d00005010300c5c42e10341d001c03050044132540c00f03105520070812158030070b950409100418070080740e00c201c194000e00040c001071a01d49261401b4940c490340c1075449440440010309840c0d10203000fa0f0b055460305005004260f0305020300440c1401c20f00388003400d40040d0400c0102554002c00d55203065102203640b203d008071b290403940080100600720394507410803122145a40c3c015010441d89446144a49940c40f4202c0c001d0301c049841c181c450502170382c0c40c03000b8003c1540c06545c0307070380c114043c604a505100150010030000b03000d0645005840303a00720002d0003072502e66040945000003d60f101e8920502e000000c40316041d42001d000758451a240020986034003550b0054040d6500b41180b00301c0340b0340c102e4080c5200e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 62954643 1250 62953393 62953399
    0xa1106040303020408160f090f11070609020306100e01140303190224041e140106080106050f01030218060c100504050d0e1804020913050105040c0f1424040b040303030b 74
    0x9520b905003032006e481c1c1c0c5100b51011994070a100300041c60340d560111403803c1c00e02c400407481642d060052101d59015100c102d0b1543d0b80c1d000c018003982000c02c03005600c070307001840d801525800d0103400c10380a00144611841d8203000e07017003619591024030643d00203010014040140d84400000691030b01030b0340580810b01c035108108070203606280c0e1080c0e0300441c1c1164802c604183c4030440088030f003941500513620b121003c0400b1400b0042403040300f000740f0b000d8000144942c02d02c0d08100701e0030031150016040500520007a12042c051038445014020229211942d44500e909994103290004482c041107920f0701c010070040c01408a0040441d203c555100d144100d91034080100606041c1513044492410400081c0141001c1104681006c608005003404090703a6a5107820b4450072101194513641d031040410030300e810300e46001c018100c4804c100c03c640742d440340818040c81100101708490500000190b00c40c5684200b143c003c3c00740028407598440c0c8074103028014203021030715240 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 62955893 1250 62954643 62954653
    0x503190e03030a0603030f142d030a02040e0106030203060306070e0f0d050303010e010504090f030309110a12020102300f19020609070608130b041b1d10060e060a1106040303020408 79
    0xc5603620a00500c00c401100081e80b6040203502020024804140e404840d409c04081d00100d80c2c500459001c0c620600d403207940560350740e007450b811004401041e803100d0141030040c800c3c032070a40e601107070f6107600c4405841c2006003120702c40005011040d030303400780d241c2001c010351003042031140200045050351721284621410366a104248400c60b1048500603102c42982961403002078403030b8100910040c01083d114102c004042e002840c60802540009402c14a52161004558040c481d4080340d01a18207203200c4801c03000b040d01c40703080c0068034080146000013140c1711018203400c1602d0001764501c04441c00e1940130310002c1c0d5601b00030750304580c25100d10040042c10074450030303500e40b141d2502041980a0011641c1313440001802801c201da079071442003499100c00c50912066001041c152503901d500d12500d2100c216452005803203420000c03440031050050f030b0382000803000742c41002e0720b02556410718036204450b2500380004041c504e000d502d0030321045c194160068402e4500e05000e8035 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 62957143 1250 62955893 62955917
    0xc0605071403130b100806041407080106060302040305100501030c0b09040e03030106030c08090f0d0c0f020d032c0a0b0708070c0b19110705040f020d0908030a0b0a03030503190e03030a060303 84
    0x405c50008502c2806010f50115000800017981880560b1640c40000119074000d501e07074030942d0070359106811241c0065030105040061001c1048490401500401d041040e0b50468446141009a030f00032881d07680000200060b103500da5070b21404003544400d003070701d45950f190140203000d4070103642008009a4103d021480c505c201185042c054200d00004140042080405440070a4442c0098594503110b034020780244e02d0b04141c0d002800c2c4a580d070a1060030b1070711a9096803041401c0e20021a100c400081c82d2a0b031a80d0582d00142c91110044940b220382904c1c050340e0781d10912000811007003843d500010113040480150102900c4015038042e00c202c49a0b088500d014040481032007680060400c1202d42821b038040500d0543c9a070b405890b1540108456065803020b9200b00c0396400008208080c1c000b561255240d18a0110341410300a450354800601c1408081c044091a841e0080c03040704c4200b103548508404180341c82900e40301c1c80d10800c0ea00082580e444183e0100b00110240 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 62958393 1250 62957143 62957161
    0x11b210201050c0f0706230415060b070201020606040902150d02030712052e090212010503010f0507080718091a01020c030d020304030b040804050d0503040906060f0c0605071403130b 80
    0x51600c116130b0340e0b28a0f0825034152683c0018240102c415102d0700c404101245068006c0c0c1070304c0c0e02c5640204885000d50031050454030031103c0952001910180501c55080103071b83c08540d86400034011a07010514511500003e0505c1e1040d8041c0385402c81d00192485216440b42c014620503030160300e4011427031140b60190410748100b1162849072aa442c0c0481c046d2140c050440c00c41d4a00505101c110280c5503000c01c01280d0280d1984030031040e201004215500c0c2c01d010b501c0c4481d03902c2e0801c0c41241080d01d0060038045000e00581c06110700803600c440c0c140700403079100000300300e81c0405020101040130311005491a8011040c01801420a0300b04103047c001130440136a030780ca0780114a018030f161119094074801401c1203564480402c0000f405640f080b01b4450f049000358050f5945078500700f04601112055800041400381c50141c01030601d410500c52400c098228102103480c0d1b980700011a1500c88001c5040407190012082c040c900441c0c00c4618000d9100d1a42130b80d00341c03074020340 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 62959643 1250 62958393 62958397
    0x6060e0402060304120315090b0a0803070803010611120d050106030b03121801111608070f080a02010e010203130b0409060501090b07140a050609100b0607020a0302011b210201050c 79
    0xc0650426810404100026000c079044801c258540c680021000311240319100c49864030f510007489a41ca0f503c2ca14100d1410039250002840564015480c0a1490b0b54a1119000500c9900c050040d900080b0b11110401d100f0a000104034068084c2c0c1c0f241400405402002e080c007500c1c0c0020301e04660300d4801e041c00508014215107a01101c5d040149030307050040c252a20081c034a041040f4440c080701d444404000302005242100581480c0c1818111080e242c07905a40c0482c0c2a20058202085a040c0204000c00010307020f00e0a21080558100180d20354807a20803002001d0141e1500040c01031503e10242040d2503a03002c045c0f000d659200b004643d50784081c09101504142004044001000140480d820b6400d0708240c8a4031101c60b04c0c1d1901b4214221602e5803a0741190110f5504032019111760f52121008881e1141032a03055004100c43d007829000090601c07a010090b0301407460310780c46440076643e00511490741200c40060b0700906080c00c0f003920000d50308100200e0840116242 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 62960893 1250 62959643 62959651
    0xf04090c0e040902010914040617060402010215040317061206150312071703040c05120124360f0f0e0601050d0b040309090c0507330f0204050301061206060e 69
    0x502c064803170341002c03a6500c1c250015147c4990140d60781c0310001c3c6811040c0b2544800255110140100e4a0580006800d104803500b00c0c00c03000c24808104070009800c442400074002240d00c00c0f0400340d0b1508085040303030700c0360548000d5900c60b0b40b0400c1900c80d01d4005031003002c1410340075681c500d003c40104180174000d00c100182485410740c1c0d10040359a90f1005903601c68015510171914941e5040842d08280700c030300c0303100c0035651281e04603070800034070120151907010b1030003103000ca44e450010744985814200c03244041c1e038045025241c1850304c0003148192166020803080184082e01e440407402408240450102c01d0305007051401c0540c3e02041480c103c9101400359007010361282e6802442034401071046081c41050000825807030032032300c0703100c0303c42d24281c848580d04ea12a040001d0847d100c40381d0441c0801c034209102001580e601180705030780080910206000144107084400b80c05039801144d055840d100b80000d0301141c4c4a103665044d80503500402c82c2c140c4030100d41e100030728100c03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 62962143 1250 62960893 62960897
    0x717070e010e0406030b070c06110913020903010e060c0703080c0301080706120207060203010608010e1b0f07020103060b131a040303020703080c0c1504080d02010506130905030f04090c0e04090201 86
    0xd60428415406000c1210414070b0083c030015005881c0d548600540c20b0503a109800035400319590310801c1140c2c031034180c0e10000151000d00300746071880003e44481c0307141d04001801d600450600c0941c1c400b5041103854010704400d0f1600380ca084440512290072031901540019805404a1180c801d00003c980c10380b0034030000390070307810309004013030f03411a4141c2411b8241ea5400c000c1100400c20314030145005c0c03c1d05a840c2946075260a222001403c40a4861083c5007001c100e0701016034074000c101c401809405900c9601c9461500050b8000c0400d03600140e941c05001910b14100b004190461007524411032610034807100e21107140f00e00b0300940c000240582e0003d582031002c2072404024049851440044030750800c1d200303020a00e180c5521011241255005c0703028020503105104042c0c110400c0d100030070582c50701000046042d60310300c2040181607540d40310601403027070a10448041d02c0b07842001c10b6585948024a400400c49002c040c8006601700301180c03290325180c05444616030b016 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 62963393 1250 62962143 62962157
    0x4082805011e14041e05030c1203060f040b180603010f020c0c0109060212030705070809060c07060e0301020a0813080909040c05040c0801150f27090507030209090c030705070206070605071707 84
    0x150882c003445ca85942c103440c14403044c8a0080f0841c2c040005a04001c0031107019610f900f4640f00b0f00404800b010040ba21803810101460303020f450f034000d41030b019401e0314048542da4a9807000300380145014100f400e2170a00001c2da04410890014504115141c2070fa181640d140c0e80b01c80413611448003201c0480d841c442000441c10051244001d405101e001d070603080d103050b2904000414661082c0b10b031030b45503040000c04022490b0090249070b40388205400035460305e20400b05c02400400011300c046162040c104001c0140a003140036030b070040f034014100d650142018208002c00d8410b0f481428403950030842418816885a802d9078122840001035400e0070341e01d0300094881580e034040c244200100703804c00c2107010b50840002001c030800c12400000f660300342010102680c2d801092101854010020280d01e5112031a4440d4059032010005403a80c9520101b1a070030f1082c64006540203001107400001d02c092030744410700400c4a510395049d00d00700b00b82c40c1c074403405003212880c0200c2c0d64 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 62964643 1250 62963393 62963423
    0x3030a02031e0909070206071d0102030d0f140c0301080607030902060a08062b0605061512040f1704060206150a061b0c0b09031204082805011e1404 65
    0x2c0c00e01c00240146648228900384101580456516001103070341c5001680300714144500c5c140c100c3c0350100fa00c94012000910fa4402c480040d503030740b0441c2040320495544003916150b40082e540880c0e02e0420409030801142859030008204d03030400e02648032140182404140654003d1207104440d0b40d0103401c1038106001c1607820355140100411498012070a02d01035045008695454500f0001c0f400d4400320010840c18190101c0b0790091003980900e1128550305c40c0c0103140c0080d1038000040308512104c035641c5141050340003070b46030030003020580b2400e0140180001503010b441170340c401c1d1b8220340302542d87e0549840c01c480301c800703541e801450700c1c08180510761040c88030030f80e00010540b81855040d09a07035821000b1040e503200102500d40810361010311b02e410700492031003200c01c0c0c0b0300b5805d0a080038004d94903405100295802d1004d0101154140c032410149501c2c91600000204241d403078103801344025101544010401d2458080d90200101c1c2071742070303039001c2e030340246002c008002 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 62965893 1250 62964643 62964667
    0x20c010903030806040b090703050703060905042105040e040c14090403090515090d1518120e0d120c020406050414010e041e0507061233050d2003030a0203 68
    0x14100c103410a454103060b51a40c2c8508600c2c1b80103900c8c641c0c0004407450107241c0141141c4207a04640075485c2041c00313100c0820000c040004401050845076000010324039402e032003c3c4034a40c84281c01504400400c0b0034410115a1541200c0d049610f800c6044080001c02c02c80300012600100441c1c001c1d0000e004c141040080d1806440380741d042c3c14a04500d440001700d0054540204130782c4594240b0120000e220b2501500d141c0c03600380e03d0315004c031098a940340711681e2904045803003000b12180d0555201c0c3e840601b12040540c03c4045281c8005070200c0050075617502c00c01c143d0143e0b092000014440c20a841240342000d410b1290101503400d11010b0207540303101410507a000314030a00d10919403107102e000140103d2080e40107100f450b00d450030141040c0090785020102610b00202d94584645550304021402c1004c0c019440d14502c10388841040b203056082280c01800040c074180402c2041e8141c0308d01106072240c20058003144008255a0703125501c00c41006030014080d070806a2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 62967143 1250 62965893 62965907
    0x1050306130c0b04090603050f060403080703050718060c0308090f0307110f0a0e0411030303070c110112020409060e0901020c03041203050f030403170609060307060509130f1506020c01090303 84
    0x40c1c8164401000e039aa0344040d2060f0740c000350401d160031561040100100b180400c02e801c011f40941003e0043d9192503140a03188801c01050700042c0340d1180c0000304050320600011803c1d0303503039490302c110403502c0301d20041011040c140d08a02052a02000c118004400a90310a2440c80c5000851808040d03551b102e6aa0041c914440e80250000d00c0c4c0858984c0c420740714202600801900340e84a15003401c2400340381a9515145000742c004209212906600030700550201d41c20407403d01ca80c0c01c001c00121401c0d80035154150030b01d0310124000c40c02e400070303410900440c0d0740c11480e050f60782c03103032041c1600300c1c0f10750080c4100c9a8400c0108015201e44005145142402030070711500f80541030220042c1548110f9007200028001241c1c2d03c5020f000c0c42c141d54102c00b058601d8541303407522034080307aa074a44d503000b80001e00074003107100555542c50414004080160704418030100c901c8081f0380703010f4103500c24800713001c1482d6440412100c0c4005a59800804143e50b00707400c0070302c1e5446c241c90310 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 62968393 1250 62967143 62967181
    0xc05011d0705010c110d0614100303080c0306130c0809010605030718050c040801110702010807110607030f1d070f050d121b140606041104080a02090702010b1008070801060801050306 80
    0x440e0010800ba90b89564002c01d4040045c00307114042101d8523030000c080002040105210900c1203e90710510100343c0c4140030a5200060741260740e81c9032510000a41480c01c5030b83c456244c90704003001840d4456010201c18001c00440c0001c2c0300c11511081050703282c0d03a15003d420b40d200e01002c2e50b048100203580209802131250340d600391509884805650a5070760880041e144042d000a4580855a11040082d8001c8540c58065034455046456940b110000391800013010b481d41d584240031403e96116802041c41e005022503248110300c2503648540c00c52003044a944ca81e071200041900f002c517002003800e603002a881c080400500000d540d884220500a2a145210f04070140020044c4190009240342440207059500d092420401950255540a003034901d0510082091a00024540907030990481d014172040d9a012400c030300429242010946c00b40510651100d640c1e0005040c42c0500341d146e40302c1c0502c0c0c2e2a80302c1a609444288502505540450005186d06407100641554 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 62969643 1250 62968393 62968403
    0x50414040b0103060b04081501050111030d0f0b130f0509060402030a1407050a0608060a06020d0f03050415020f070302061f0501051e042304051005011803060c0c05011d0705010c 78
    0x70840c2c03241800070b03480c1c1051f000100903a218424116803614010b68090040c1024070300741c50494420200240c49000301c910100d0100d40381d12044203130104642082c041c07000060841c80d031042107815144083c1c5107982c0c0f0305405624004c0071400160001c10383e81d20032600039005000c02c1c0c540e03980c2c2c24840d00003200314001c240106400030500e5541d0191003001004650750390602d60030420b04125001203140c0c0b1690030f560003403130500500782d0080e04803800c03501982400503407942c032030410b0034003041001171b400030607407001462010303000f039400242030f00a001c1e1b4201c80d841c0d40d030500c0c0590b500d00c61410b04240880300700c004024540c4100b00070310200052429189002c0c0c8000303400400c54009811401c1d03080241c5018040402c1040340c032040303015040720144001d0405020b54101000140103050410203d003d0a00010060ba420800103640c400c004005400f04080000c21072141c8076022203803942001c1c40d00d2071180c8001c00102d04614071202818031949001c0041d11410f03d0600b0440d0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 62970893 1250 62969643 62969651
    0x170103080712020a0605040602030f070f1d040207020402070503030412050721030f061410030615140f160b090a110f0d0512030a0c0906020616090302030d0c020907050414040b0103 79
    0x40066090300580f1f019511030311015803641017803019a820307201d00804c2c04040050718a682c880290b4419500c117031152440084940000da07840109003c5e2244510194205000058030310030040000000c5102c1c030300030040d42c0c104a24a0034115014132808801900c01c1c00654041140b401d000d9425000300d42c40ca090001e80504071428690a9038036035030000d10800d549072440844d905001c03070301d081c1c80041403604002240c2085400c000000c83e201d860700404c54640407103a914a440003c80300b1a516242405881e213680402c001e021401c0300000b1a202e20301d0300041080b080000444c0c2009950004121000c0941d03039050080079a581035500c1c1c0e00403100e400000c00b00d0f200f40104540e03a81d0b00e2202d280d403861708540c50801e0300d04640000c010440e804c1410841c05a021074600c5d00161410001a0700c000c01e036400316440d43c0340e508040d40c03501a13640540e000036085440301c080320380b09980c400855a20000107441f9800307948500000781c0c05050a81c142440c0541c000300140d00d050500003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 62972143 1250 62970893 62970913
    0xd0603020409060c0809010212010e0705120108010b010216080a030309111002010204091a01020d0f1202121006031a1c0506010303020f0c0f0a03020105030403090e0702010c17010308071202 83
    0x141030b101d03841e0b02500c52690700c81214a2440d40032a1040c0e008407228029071070401c000c0c100841f007010500c284e102d0f0560304000309444600c22401c480c45110000f0380c28200c0d584400c00c4034003d0803801c030f2603409032080d1200d8070405007409070024201c9843c040685000a0607850a030040e0082a4085130b0342c0542010010352076441e95044080041e8590006884500b031078440004c41d400001c00c1c0400007902999145142c1e80003820110045151900780c2462001060a4440204040b80315003401d00116407003a101c80429500f03481480859000340c01181e49040540449400054560504c18858052045d5040c83d1214000700d1a040c04520310201c982c2d140c2d40e007044000c1c0c000300c0061700309541101c200c0d80100314000c6c1d0000d007111300070201402c0900140c40300e030741c1d440000d0501030003000060074075006201c600010724400044250034078062100074000c10b400d006c00c00200340e01ea01c41d00102044c4200b0079059903844280d4a14204c2c107511260064500441c0410840c0b0400c1440 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 62973393 1250 62972143 62972149
    0xf170601270602010f06030b010510031812200d0302070f020a092009030705010c030203270427030e0a09140f09030c0a120c0203060415110406050a03020d060302 71
    0xe4007002400a40d80005070b050610007030a4462203a0015052410602c040c0081004030082c5811078100301c402461550403002c0907030140c03010b408041d0000c0d401c481c424041c001d0240035011400180d07074a1815500401105080102028641c2001d030781c002040c0310b9120f4040c1c0e005180c0d007070003001c0340c2c01c100c4d02550001c0d200c0c040540001036501d490b04546003440c1c4000000e655a1444030003858100013003e0302080d99403555200d47e90401c1170fa452500b007458004d0040700d40c3d0217042c80c041407810344101c941c07044000c80300840740d01617454581c030269800e0805064500b20144038a881010b050302e620304580b08000840c889501402c0c0450001d80d6150900c98169101d0300e424080040f407400080042003800000e0042c91076070020481054100d80c081101c807600d960000c5600821003070304204690b0040c110368020b4043c403800c8180400d0005100401400d1000a0028410116080541492030096100c0c080205405211000203140a034000e01441e152409002405580d81c1d000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 62974643 1250 62973393 62973437
    0xf041b1404120503040e100b07021011030d0c08061008060906041d01050411010c030509090c0c030703020c040e0c03100c02010b04021603080703060b07060b060705030f030907060f170601 82
    0x3c0360349600c005000c00c41c50801212840d8000b00e40c0c81c0030f10341d09140402c2d080d110b2082250080c8180e4058404c4503500d03005548000c01a0710000032651501c00141a800003890784100e841c02058036140015414a400031040510f030076140d0b16180303151225801d000005c1005040700c2d9019855100f503440d5001c0d80d034030440d0194440800824030307041c1400c00b01c0707503685644003160411680b109204082504a0115005101d080e190051705644102038004a40505482c44520303000000d024424543d0005000c15540001c44081020340e80407091030399280d020514407901350300541c1082440100d00c0d80480382a03001c6000200302e143d01c00001500300c0e84408012a20015410007400515a00501c0503500c031a5a04040000500b0016075180e10f000d82200109010380304d0410259644484099580355a40300d01243d8855050f010001c0c401c0c1c0003120284001d21412000040440c0724214000070070707801d41c0f540c102c000088a11444111002000b2505012140031170142c0d01c134441700 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 62975893 1250 62974643 62974679
    0x501090308150907050417010f11090109080601030c121b030b071101050105031011090d0303062c0f070c0b0a0203010609090902030c0d020112020c0a020f041b1404 72
    0x500d04445140000b040307900100e1041c0b00c1e0340504114000c201c80c00d504401200c0940303422281c030854010343c040b2401d01402c0184d880d000346506052200c081413928a0180107030100036201d402400d030b120005642c0d01c140c2440050144c41c50342c00100145452003010080b030074090090750114044003654548204c8084d8000c451404104040000041c3c4c000708080c805580180240b0541d40f5080c0045d03034550000c4c5000d00c00c281e454401820a810400c115603100030040d040396800162404c0c05401891140f14814040201600403039074400300355103c001d5100c0000c160406500e40c40201004904001c0034002404003020390301010410000c0d03454400c01c84000c2c007690700d41c18100010064542039100103500c134244030041c00107940100b003900c4007601c01d40303121400032048e00040b684000307141c0268540500c001004401044081101803881e4025614120f17032114000501c01140d54001c14002c60041d55455807465910400c46a1410701c40b492509041645a25648000d407440c10 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 62977143 1250 62975893 62975897
    0x61c0506100512011215020319050c031608070908060c0306030106051219020f09040501090c05100507120509130c080c120a110c16030606080304053d0c0203010501050a050d030c0f05010903 83
    0x41048010f840d2710b000d070070740c020580180c0c107042d8207041c80000401041c103040f510038041f20900081c8a6442116580300070f04400e001c490071420540e4046419a1055a000d4000d5082407000310307107800c280b0b90302c00700c406c1d00000800c2d0b0442503403171300340c100085154101e030302c0f10100404000c503a45441c846c43c0100c4c0500c000044100c200d01e095a80e100c0158041c0d03024000b03040308010f21942141c2540c02d0b1503006440803044a0344840308599621400000641c072905800d21040c4412056104c100d142642e61102105603c82481d0b001d258010201e0491310445290001803149040e138000d1500c1c054034405090070540d002c2c080ca41000c400766418000032075281d00400c1030103018010f02d0020002e01e40914134090a007008607d001200c940701c8010600d0400b0040952a00c04107155902400003600300350f10040075900810810f0040810ba1107917003428008916440c1c441c0b5a40d0454038002d16504c4001c1c0c5582e42600c030b90801103070550705030b11088148404a6400c0c090540e030f040c425 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 62978393 1250 62977143 62977171
    0x5090402270918070303080907080604080d05310c05060f070203150105060f07030c0506040c2306090d0501020d020304120207080105041e02061c05061005120112150203 74
    0x1605001c42c10100510180190804200069100360041480000d0320341610386440b0b80d6031603172503603032030300b200740c1c0c480e01d00c034880c00d810003041c84544000360003021507204041c01243c03550140c00107411405603c0e0411030b22010070740a0390240c200381107080544107040d000e010b51303075030303000520705412070fa0203034038989000074010046250901414544001380da02207080f03035051402041c01070255120840181a00061110506010b104007050459101e01190024901440c190000c41918401e00d144202902c2d910061095086401c50040d10090892800c00d107583d0b040028035000b1081c280c0c4d070b03950b0070001d80807150543c1c00254880d502444c610750160101540091034000d0503401100d059250400703000000351000120308c1000b409040640e42c440782400010350703034842c1270602000d03076450f0f8220342400c6c081d40d003020384030f05400c5071154090384105100792013a00c1869424040c88104a005011440e010040030311400d0154000c0d44c001502d510034282241e0059803c09650200 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 62979643 1250 62978393 62978467
    0x7080f010c02060411011103190201021206040c08060108100b04080a0201180f050d020a0e0f01060f020c0904300302030109050c04080309010e0102032104020a0501180605090402 78
    0x1d000da662441440e10091259103819100c5c3c22600383c40c0c0c03110604202d0790040312040c04004100781c50602070032004511028000385006070007580940c01d410b004043c070b000080d62502e49403049150b00b000070b40300d0101c1640c55100444041e180180b642c080404e00c4400820341011080c0944041c002c1003000302445040b500002d0400c110400002c40700304e2070001d0034002100e80e80c00701412688180c43e154206001440085c04552050300300e404020041c83c204a14049045d5285048802640303500c000d043d03c0c40d07c105e84860301d42901580109880022400143d04039600c41c0c40b59803210202c2e070428440200146514440041000000ba0040014800c02015200382a0810f4007104950714061408071840d40b203000d080c88180c18440d6141d0308a007603074001c2c42114500c0c0c1d036000300f454540010030855020720b502035909902030742c15540003091303550048084030034503c014603641e0301070340c906001140e0303a510881045811540900065084030880000d00303a400d001c260000701b180403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 62980893 1250 62979643 62979673
    0xc02011b15140105030706050a02030405100503100e0601170a060b070503070605070206040f0201030b0103060314030c120906120c2704050601020d0e0f0a050907110f210306030f0708 80
    0x1180011190a031440b4800400050f0f80004048045400504149441c2c41c06808164254003031580940c1e0000a10074001142d640d0040c011442805c903d850004c1441c1c680031314041000c400c440c1540031400030010042034043c0390311100ea1250084101242543e03c8885424807600215012034140e40003056005c20480e180c0141a0320801500c0100700c14600303607c3c1c018068800100281c181a034800c612141030b4865005940a503420246045d1081300c0d1600c603640d1307640031410350781d210b0048403090203200440004807020317a5402410075081c12100c1500e90780700000503164124810041000d901100003540c0c6c0c2015070210400c1c05281d0400c0303c414802610b170010301c1981190049048044619041754800300101d1b0103075511a1568034407030206814441c0360704001e034400307200000c01219aa20002159441c44080c01352002103035044c1c0700d030f940c503a130b01c18610901e400c0b042503e101c0d14a080e005160b000c00b00030122240d54200007240e9080c002d450b0029a0b0a8100d01d00e40c0c08850 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 62982143 1250 62980893 62980901
    0x702070e0c03010302060f0d0504050c03100203010b0f0a0c050f01050f010608060d030e0a030c08030a0f091d0a0b040e07080d050406080a0e12030c070c05060306030d0c02011b15 78
    0x311514154003030900c0c1407a0012039510050200074800c10001c9170a00300a08840180c0c1c5240000c0ca4013003016081500f4001d54840305036560038403c1c0310780880f40c0c07030348040d500a03039040f00c8021480a050681608a460a98010030140030030801d0300828000400c90420050740d160200b400005502e0408030060545c05005801500504c20300c4018400f56445074044c1d00c02664040c40d04520726028900040c0758004c882e40080c24000040340301180b1440f0200c0107007040e00c040e8840725103000e140314040d03510394101c6c0304003240f039205107820220181d41c0e440c02c254400340d001c10014032109100001002c6a07110780d00568180d00140c0e0500c120402003010400190301414160700307280c40d21a00800c0302d50002c2c40101c0d01e44e103030600318020060401a045104000c000f0140d281c0c0780501450a050300072850540340b0002e00000029103041140441e07000e40f0703010340030b08200d0a001c0810395540032410700c12410010840d600c0106121203070000751080e441070114401249030820004195 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 62983393 1250 62982143 62982149
    0x303080f0606252a1401020f0d03020f0702040203090607120b060d0e030409091a0c0f07200a06030b0301050a0e21190e0102010c02011104050f120a050303070207 71
    0x110010010f4607507080c1c400d03105400031460040c0c0c1580350300c414501040c528030f210f0b151031005140d051310707620442156100c25040c1c5030070300301c2211590114001203a498400c1005044643c01586001224600c01d80081200015510455291000d15404901242d01c1160b2290007608244148880741303602c580e5070540c0c0048244140070021a030701c0000c80c203115543c8201403203540c440340708004c4031091050f100200300c184000c20004425040010060301c0d41e43c14049000004400140e0241c45602074903101d90000e5900b500340345035a82c1e02040b0507030340401445140301c2c440c801111503607140035400140a095401160380c1000768281070941c2c00c050715541e5664107240d4000a08040094004401e208041c204c0200c0d0080c403600d41200c1c8218040091541002c1000880d13041c1c021400501a0000703038000c010307007020800e00b01e0882e80c50f098040d01c0904108410004c52811607400342600000400403a04200c2d0818450f142040340c146c102c03443d401c04010000320580500600c001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 62984643 1250 62983393 62983399
    0x609060e18060d0f02030f010902010801080601030308010306020a02030715020a020c0f100c0f05010f0507090e040c090e070e09070521060703050a0e160302030d0f05030414010b0a0303080f06 84
    0x715007209546190150004080502820300c0e07600b82c500303201c1003c07890050f094020703060750300e0181c407150041e002e018072a40c2a03000c503003440d00008085d100002c029049903019075586030640d0075a0740d0040a0340c000c2c4074a43c02c5200a104803008200d10301103125a2107074506005030f0701d4516070300281c2000c0310102228429000022064015100d4090204450380c1b24034041442c5a52842c0200c0c2110709040050034a6180ca90500c5201c91035a02c8140101e031551541c40e041642e07181a10001541290001c080408400d010021010607420800ba90b162110a441d18191500d041d513076080e07812100c0c210b650780034036000c21060500030741d20080d1881d00c4003d010b280420000743e50b40c485000e002d0303904140c1d4520002e003104100d41e20040080004c803003500c1324a400c460202d031861000f800140c0c8a4050100320b400454020580040c10020580752507066907181d45a07000c3c81400314001410700c1d501c5181e40700082d920780011001640c480d86450102e41003075003071742001100041c48180 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 62985893 1250 62984643 62984659
    0xb0316020c1e04020a02071206020405012a020d030912080405090a0b0612070c0609031e02010c0c0318030501050c03040606050a050924030102040909020f0301060b0f0706060b040609060e 82
    0x181d000c0241d04180b8041000362800350fa03811503040120318001e216070148540001920180042080d00d80084c03040390f000340d031106007901381c105018884219603011901100c0f02c681c030f184010b0400c00403042ca1507004c1c1c2000b210b0b44c0e40d20700c00000345224960b0202c0d2071044c00a404c3c026460045140354001c961482c1c10008000d52070080f034610320400c0c1d8004001d0b80400000fa01180c440c0030b4024650ba4080010300243d4810b14018080740b10b00030450a070003044408007001c4620511890120307001c55590015009216203055800d811100414141e03614a000040003080c400d005c0c0314011400c40381465582e140c02c0c248002101c45940100e0300c9010b81510800c0547d0310041216000401e4050224044140001d2404625191800250594004580040e442c0d1007580300c11401170007a244510305070801e0040500302d802038001c0d9001100180f18885200d1f120b079014040319841840c001400686541480c40b09811682c090000244012410b21a496019004070342a00068405503 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 62987143 1250 62985893 62985919
    0x30302010608031e0d020c100b010f030516140d020a09050a0b190509040b1005040f0911070816050f070501030c1b17070b0406050a0e07080c01030b0a0b0316020c 71
    0x81344200c09011005000f83d008100e00c0d000d011075038101c0b2901d04c484070446000c40c0c548405880580f564100c00c0340031034440403a4105e501c0c024000c0c54494107154596840e201000c0000b0790b9401a150a1203909510601c0310007141d07030032407008290310f849030388850029524040810504000f503800100c059213081c000c50954000590500414018a04069881d0501500840e0041c1101c250003a0301c0710b24083c10908031500300c001002580e40d0580b044480c44e44800c0383c9419151041074a280031317030080200c1004500320f08090714001009046103401603049807074091a150b07400e0f008000c50340050004015560309841850641c96540c104054001c072030030b1003000074030444500900703015030800d00c5c03d2410503079404079103c050340410724501d0360a003424164000c0c10b084500d21001c61074a00c04128030440000ea81040f2807884009103200443c290044014110b000b96940d00314440c20f8010540e03028503005584a42d8184000903101880704000900d0b03c081101d03194005c03500c5000c05 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 62988393 1250 62987143 62987167
    0xc050a02030d051e1609050a06021005150d05010203150a030f02010c0501020f0f1b06060901120203120304061401050418030c150203040c0609060810090509010e06090703030201060803 81
    0x40d440c40042400005004d0355080c00402c00b0107456031060710503014000c10000c04104685203071940c140255034410403540c0310001d11807810002d003e40005030742311040006000c210b40d08001d601812403400c00408054910108419042208007200c0300d940100c1001941040c4c0c4c07030044035800d012117402c079120340b454aa040c50841001000303410004012460003c1c450250101d65001c04812001d40e51260f0b194220500e903000981080c01c6004418003000c0800c10004030140107103c000c0c40c081c1720380d1034000d2246020030035480c01c80e0140200200001010356480107140300d0350040901090745103200740110606481604130b50320641c0b03000d080320103142c040c2e200d00d0545541810400280c074203506120b11540d04e00d5102ea8801800041048100a0b24403d1a0304031070403500d6085a0030f8030341d50280c2d200c400841d565a04c01000803010010100d042e044a50099182000018508400d141c2c3c0b50424400710b44400300ca0713001c443d04008141e42482598020044c4401039414440c403100c90b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 62989643 1250 62988393 62988397
    0x4090c091a3105010206100608010e0703090c06030203220c1203050403021c020310180609151127060a05090a08030301031203060b180411070f0602040302040c050a0203 74
    0x800e14900c6010441d01108000c0e441215603690a4401c0140b004002924071581d07407046010f010b00500440380421200010303008804d0542d803068840e065641e00b040c00d07a0002c602c00414031410035071600d002c80045200e184480c0c0c06064165805650780c60408410705480c0030300c07c400c00d5100c1240c1c1020011440c096480d00c01d541e82109816020081414201e0f03150140d034101942c80b06020303071048000d402200f443d551b2903100350306032810030f03004040e44803c4400d440b4502107200c0e40300c204000058040c0d40207940e228410b4040c5c045145003c02210100e030907138000c07028000d07400100c00b410062480c460f01003809036030507401031680070710340405c1daa80140c000340000d014020400c5041030362071206680c040d245c5034049a45947e900d00707002110300001d65072000481c2c900b12001c16503403c0041210144083d81803007410809104003408002d00b4084a030700c0307016005001c2800051038041d80494101e009a4002d6220340c00c6004000c02c85448041340340a120f02041030306805070700402 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 62990893 1250 62989643 62989679
    0x60e09190618020909071401050a090b07080c01020307031d01020a02030702060306061611100c0b040210030e010603030c0b09030301030b13020a0510030f0e03030c04030803131704090c09 82
    0x1e40400e0a6800d01c40035120382500c401c000b507104800d9010050100c00028624046400448980401d49444001500e4034070074000024002040454107005a60441c4002c200c11032007424010f2070582541c0d50542240c005a40c8040040e45a0080d040104103000c028010400000002c52500c081032201942c1e078440c03401e001307000e40f20110000e10f9558a000590b01c03800040d80c00c2621400c12440c0172510301e01400d00311849520540c1e8000b140074840c071091840340d035204020420799103d84d000c01c504000382070914820903880e2240247c00351070a001d41401588a9110821104c802c0c4c0f41200e0400c00040c00c50207194814001000407400e01c030304140d041512040340400c1c0d641075002156224107203800c400c0c0c000380c00c0a007102a09074183e014046800401004020507060700815a80f28030041c1e540582e82c03d400e2000344042220400203541081102113050702220042e901c0c5010100e0328400083c2c040c40c042010420b6820706c0c0903d0b02100024a03140c0a080d09002c044410f41041c91 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 62992143 1250 62990893 62990903
    0x30a02071e1203210b0a17010b03070b0a0206010b09060f0d0b03060408040e090c0f040e0c030d02070623301501090515040524030901060e0919 63
    0x401c1e29401124212409080d0b1024814103540403818060601403004125810741300d401c2070b0381a001d003007030321400c85800001004110b40ca03152442803044942c2c403191110032556101c020040c40d42d01007244100514003450030540b91022200041d04100050780508501030040240542541e01c110840380100104640d050719080700c0002c940081c140d010090b40c01d4800c0100380420300400c0340250040303460718180d80c01d00d82d48000c01c190b00c51312101c0405811840c00781481c080c628141d0030482c180883d43d802c89185030f0400c0c2c0000d151155020090001d42c008100c00c5c003000e0781c0501507440d800c1d03088030355180c1380f4004c40852040303100c2c209a040a18100074074130b500e2f49c0d4182c803103c4541d8000f082da488a0f0b0900c2e131403505901c590340c0407a90200b0010100040c150501e201e0310714250b40b4804140b41401d00e041c3c1800a003030032420078072000c2d113150403083c1c40314000740d40034500800100c400001e94608102181020100213080c8509980c40409501400428a00025811a889 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 62993393 1250 62992143 62992169
    0x1e0d03060f0b070309150302091e0d060e03070204110c0105070c030903031412041a010f030c050d03021e060109110306030303040303200d0b040f05160c150204090905060603030a0207 80
    0x90f0504403640c6101d0b40192481c11b4100051806d890ba054024040c1c18201302d8445426440b03d4807501c07201c4001c00e0945030009032000e0380c80c0206040b0707400000003c03000300c1501c3c50000c269001070304a13446e07010600e0000c0750100341d0500e144401d10070940c0c0300c5d0450400628410031038402404481a41c4030040800c090102ca0f228118034000640f40604001034200c0780c43d0070286022088650b807499a20b90a0180200014049801320325081c116604110320740543da040800703100b20312a0305401070303065105112210b94088200b95800560746000b074041c20440d41002a000c2c00c0d00c0a1300c40540da0904c003801440100c0d5030110031242c105501d800d00107a00d4a04440380c08ca544941103160403400e1010581c03410b80740c0390b40c006020010381210104841d9007a500f00c0c10490704140d40101c010300c8007000403801d2902842c8000d241500890304400c003020602c0c0c500702a40d00c6500a1950151103508002c00c10104224458200004501560501d00303000e400235a05d284520501d14884c1034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 62994643 1250 62993393 62993407
    0x10e190201090504061205010515010c080915041205010b040507051602010c0203060106121d0c061c15060e0102060702060a090f020909070e1005090109020d020c1e0d03060f0b 77
    0xa442c0440003440042d200340030b1140e9a410b201301704000c482d010707203c5500b4000041c81413440100403029040e016121180003100d40e03114518507801c000d040740d410501d40096200c040705010085c00051140003400201d402d00741c80d126081d1881c00e80030a001e40e080c581480038180e00701c01580c1241800340b8510500071010f0004035404140d480000c0d405002e40c0c40007044040d44511002d0400c5c000603818000d6945040809100c00405c00d02c94007582c0200c4101451b515043c0d008100c204007446001c25003480c44100081240c551611641c0c86007007034001004165084000c05081c01000d0003d0b002d149000e0700c000e0340b6420300801140c45075a88107019010400b04c010b03c4080e054000d0050740451500f660225500c1d4101d00415001030840700002c0d00c50030b442c6c4111800e40703c1c042c144901603481e108100c00a500320700e400e561004d40900041d10221403c10950001c0700040403038814807140400d46608207403803516074070105400c1031805d2089a00d8189810101d0b261800d41d1956008 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 62995893 1250 62994643 62994647
    0x30b0c07020d14030310050901030b010308070c150309032c10022803230703050d020714070608010501141c02090603010e070801060f021903050f070605010e09010e190201 75
    0x1882d220000c00d490242540c02400107000009144181c00c0103c03040b0b181a1030300100314aa02003440014045503250005000042e42d402c05820402e00c0340e02091036094560600c038071350603841107402000030f42c0e031070048050640c482c48105029000c03600403001c15610000c40f05550031141d40240c010b446101500e180075108100d0040915220b202e0203155074041050b07004068071402064002a080e00070980d030b4000c0650a58401c401c062452600d00351555406a80940040118010307142e402c4c0410004a0030345000401c0281944014001140c20201c0c064404070040c2c0010f810408220011010941c040c1c04031034000c42611040320940d0140400c09019203d0180700302e800000c040b00010f56040d5030721100d0f0080b202c4d500e50140c0d50384c99401c00c560850350b0030b81c0500160b02014200c4400032001c0b134a14a4107010b4034215182180405c01b0031100d0340512402c840307041d612401007040304150311903583c100001000a200114800d14050350320a0340d80050240c40d4014014102168 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 62997143 1250 62995893 62995909
    0x1303050904060308130603020307020d2d050c060f0108030d0b1c0c03030807030209010801060f09030501111308070f0312030e01060311031009051209060d050f060a06030204030b0c0702 81
    0x80c00090051003025101c2c5004074550b046440d0203020554480c3c00891554000d0084e070342302d0340066004102001c5140002c0f640c100309155114044035421080c07103107840d0018518040e00380240c403034954a03c03111000a00e8120f009220048191000b40140842280482212201c4070324103004207215011000141e40c00308440c051442104040f40040100108100e10000b124040c0c3c0b40c013101656550025416480717145240c40c0007070064001401854000d418080006506203054070410303403690703140740c211080c06c1010414040041884413807110380d1004000a8203c2c00c01500d503c80c40e00d00d4444948890740401003501420392103286449100b98042c0070700c110301a0091004c1d80e0b807424060300003050410070501a000e0554840030302c2210307008200940da4854001d010070b40e90020101e48a820462810307520420420a94036002d410f8041d140c0205000d20b2080c009050500420401e40d84c1c41e4400000c0c14010300c8100040743c0d108005551014442c402c0d0b56460140c0c1c40050200 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 62998393 1250 62997143 62997157
    0x230114041d06040302070810060509011701020c0a06021306141206190f03021005183f061014010e011103190306050307080a02131b050c24130305 64
    0x41c400c100403c0141540040e81008035280781090399074003260100c64100f40e411600505e90170005400041064900d502c0f10185004090300005080034000c6801c2418508081810741742d040d00406c7c0b282e014032031848102c0080c0464104610201002c10409200340030341d1040d203040c401c6c058001200d98440c6001050030100487d020008103484800d20f4888081501003a07009501e110000c08001c1d00602c102c0380600300b042d080c440c3c003140401c100100c0800920810038207200e03038001c101011424a03190041c610009408181c150081c110305807902c0c0006004804807118071004000c208a410744d00410710000b86420b143c0c000c4690300503502e0300200e0b5040f24061000003048004003035100742e61b04601580d0341d014000c00d9a240c1c10141c0c3d81030a80515000c580140c0c0c401001850148100320b4003084560000c101e140f41e1005051040c2401540c800101c0c40008140340510810700446c510740c46289581140b091403011070040003c0300400c1002c890075541c041409250099007907903d4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 62999643 1250 62998393 62998451
    0xb04150e0d02010204080115030812070e06070f021c0b010312140a030b0a080f0c060304060b060f0a08070305070c110406090509031b010207030806060d150923011404 73
    0xd0040c00e004020f0003903005100b00803042d483c3c01d2802404090760800081203980000e442c5040c00181889101c030014040d00040900078001c01c0828142c45503005800320501450b82d0b50316405040c01031084040d02103c0c1c080c03e05c00d001d1803010010f4910100b50381540e030041c0030090a2400b4070f03000d0700e61400d5201154042d4001282040f815545500503039502002969450101c541c1c610a0641e0342450012091013030f0001c0b081d01030903042c604080d44d032180c0a640080380030080c00c0080f41807540300071801c0791505400140e00f8401608180e02c030b50410550300c1c0c10006413810b21001000307040500d0005180a0f00c10600100c2644c55421810141ca00300104011a06141410955a910002100a18445190410040003418800e50382e40f2074254654804556901c020090640d0046207448208c03581d481010484a075500c1c01180a007181c41e40000c0d800040041490044440210145042400700c00510811045182038042c8a006a80c0801c0e000c0401c14262481d07203a42080c980 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 63000893 1250 62999643 62999653
    0xd090e070c020d060603050f061006030c02160b040f0e041a070c06151517060613030b1501080901020720030106030b090313080706080115050405060a03091506030b04150e 75
    0x818082990700000460380305102301d8540c4030070741d2001600c0d80012030380310380a044240320401103e03000c0d0b0804900101d15205403000b0b201460100c81300148950080c3c0540e075000304040c00150420300000c0701510030030007000d40d6860a40d07140e041012050040c020414082d501240710107001d070814685e0282d00103418000c441180c00002807002c1d0070320803140704041d040040303107040740a400103102035210490300044503034482e018000030b948821400414116021000000b052848510358090f094103d0742034525022131000510380d010161203864140d01c100484000583d40351854501d507510200036141e41004240060f0040080b5440901922000400c104c3c50413400300040c06075945140d0310b000301c551168503040da42d000c0390007500d0128506100500c0122480c0a030890f003940703145460303450603860b207000c58200d0300b00880040c042a200c0640c0b50800c140700000464488500310b00704441483c540340d040f080700000e00054840c500d01401805121819080f43c080300d8441c4045507 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 63002143 1250 63000893 63000919
    0x10f331206090509100c170a0504030c05120d0b0604052805060c010e100501080607120908040e0603070603050613050901020f040303210b010c02090a14010603020d0b030d090e070c02 80
    0x1a072101c4080003800b04891404500b8180c0e10b0003400304502c420080d041d1f20710f0035a01e80c0e40180c01004094001e03001d1186032901000011001c018403a1072060711084952141c070440020803e903440361034400d1255070f052105008584940780c081103c0c0706047c1603400c00310820003900d03107400640e0308419000000050002130580054200380080c48030001114003401c0d5000c02901155828012640c480e00140d001c04d0800c0d100b1840b440c80c00b014035100040c80841565041c010707502641c40041c01c03214a100300941d0f8a018800940100b0036801c05005615024000070702106034002c20070805540c60012803200c1c2c3d001d506072060030107044130319a907407500ca00b0b001d84418800046021040075806c0000d0b12a400c80c0107203004c0300010b84a6204c00c08440d401c2141c00da20042005c0b86240d0340b05030452001c002448d25500801d0315840042c1d0f51300c8021040d10035038071184401c6000c3d60000389081e031051fa108c4448801c588103900360a805464a89003103a4040b4141c0b80654400d401c08008 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 63003393 1250 63002143 63002161
    0x70c080c03040e0c0301050f01050d0e0a0311060702010509030910021c0e0a1202060d02071a01180c030204080303010501050a020a05010908040509010e0910020a03090209010f3312060905 82
    0x41c802d035494032464402c944d46a06102209200900409400100c9504403880650082740070301000d52a90b400072038071040318004145017140108045c2c000030074a000605003c01c0074009150407007411310003406649420001c181c2d90380705142440f070280e914103281014003842442590603020130f104a10710030801d00e050080000c2c000d00000c9125920031000040e6103050403030b20101c01a030190901382441200701d032a41c002c1d0005202650140c5e54501154040030045402c2406010700e00198080340f40c1c8405d9400c2203460080342103052610421040c00481000001c0d241181c109281c01546c40304450710481c280b001c0340c01c004105c2e42c00c01100d2010441c03101d024106603481550b518801baa600c0c05048600c1c1400e4500c410300c0c0e0003d0800200a084540040158618038200402c000d220343c0d000c03500544003603022000a81c03500c2c000344024014081d0741040149107428003e041404c0b114801000c00742039500c03009016110070500d80d941c00c20b4020350001c00000b5801c0049103058000d03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 63004643 1250 63003393 63003397
    0xf01050f03090c01030b010215190e0d02060a1b0e210f030304030e04020403080a0e030313030602030414060403050301120c0e1e01050312040302121c1106060306010518070c080c03 79
    0x1484c0c0400d040c40784190840d44001100c0118100c0c0e450002103989403505540b00b04c2101524203200390344c682c10031000c105000c001d603000e0f2418590040146107004070340b58040b02d0541052800c0041c4207150b025055030720083c072821441044404900b80001e29207202c0c01e44080c1c1c4041196406103030012909101c02002a40c8114029152a0380b00f03420002004200d206600005080c401c040c44124220751003000c030b4186140000c0d00712858903d81f00404c044030712440d4400c49070f05400208200400250029501d0350500400042590782459500074120b400140540b02c85034100300340780c40c140000344107804024210302070304543d1424515480c01c41c0e14030602c9540c0c0e28403542400003d00e030500045400380012039a104900f400d04542c20003512100382002081248540e00200f1030086803600960603241da540c9602c007141500003c140e003455030040c60340344240c1052004102c01c1d1a045140101d42e112540c43c410340d6034900314250b03401c003039464000d00520344c0032071039040e80100080 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 63005893 1250 63004643 63004663
    0x3030c0a20040507090b0d11130f0506040303020c0d03020a1b030b09060c040b09011202040f0807090209010f050c0a0c0303110709020304050a0605100b03040807210e0f01050f0309 79
    0x41816426051000390f410503201c4000041000100b00314200402c0c02401480c490500042032103800050494050b400416020700d004031079030303020080c4170a0b5107d640c005000969141d42004e240d81c0700651501c1e5007104260007401100d126078200b40c824420f11010341e43c001d2001c5200900b2940114140708540011940102010080303000010005245403003500804100b6240c181083c042c1c0d00c070303a0001c055460521410784003004018041c6d0000d8400750459802a84d0100e181840e580d107460303100c7d8042d5031101d204000300000ba0342d1002034104403440605141e5a12211007010518040041e4005012140c00c0b190100405620440103403407410100200c035001034031885d19100b00e100c00e5400401c50b5008031218400140c541d00900e500c02c400301c900c4c40420790341d0707c200c4070341c0e600c219070440d000c150000b400b1080000100c0c0346403070307079980c0156000740c0413030408050080c4070100d021901c00d4100d070f80d4580107607114008882108003121203494030382c144184403d0780c60250107 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 63007143 1250 63005893 63005933
    0x507030807030b090103020f04021201090b03011506080f040206040e0a0c120e06011701180302010207060507030c0c0605062d1e01120f0f02040b07200d0206030603030c0a 75
    0x80040341c201ea20901400400c4400103260b000d0326480c6a00b00021041d5044640c1d0b0001d4007807018180c2e2034030304040c0038000d1081d81d0021514108103820503085800f000612a08031524260070700506600006259000317610543c0504139440380e00010702c081c02180e12410691030007404000303001e4040d41107107890619584074042e4010959407414256440306012800d1075101c540104040e4805c1080b80e00e40d401c001c800054051180402c403d0398102090007900540c0d0006018402c100d602c0c070032503070301100300c0c03504000b0b802400380010500c5003034000c0544600d0700c40f030101d0680d549904080c2e40c030f0148802c0011409000c02510b504581c400000c1a2254540100342e00005010040c80c0008000c141d41c0e01d40e60103a96008000200890b0454140c00c540e0303208002510206440108003400100c8070a40d22440689070bc8600d0750320043d150a201c5499141050702d40d122030320301d45810780e41210103a4030ba9a40030042440c3d40140b519074600e51085d20601c00910040c01c2c8660b11108200c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 63008393 1250 63007143 63007157
    0x403060f09061506050a050d0b030604050304080610060e01110f01052a04140108040c03020303040e0115020109050d0c02030330090a020603241e0a080a0206030609071b03050703 78
    0x300c3e003140005284541d802183c4c0401041d00b003540f2410050000802d00480051144c0001003c245000000c403022500d5070f2001070148180082004013981c0280d41821540c100390400758018440d0128681c2ca5061103011078103000780719400d12046030700b5904031008000625040c00800384d504402e40d0718840c4494140e44203180d44070000212004e5400344d40d00988544a150300442c2e01100080c0203843e1904001d00100040e40d06100a07c02040440c20102c62941082c00072201109200010419a0701d02419440000d02c0490313550411809401c005810324058008a421841880f600300c0c00b07101d40952001082404d14846109010000c0010f40d8603070700d00d2111960b50044ea60081d601610034000a2400869124150030003200c12000d440040900c40224400700e08100403016a00481c503020041401c007002c1901c010072907500144000c550540119140c0d01c8042d0956000340841800142070502a003260340300c000002003000c10821050800030300751340144034220001580 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 63009643 1250 63008393 63008411
    0x30b0402040312082a13081b040e010f061e0803131a04150f0219020d0b0601050c030f070303050c04050603070c0203010b0315040b070201021e0f0403060f0906 70
    0x22910036281540c0e8070a8814101e000f181800303440b10707003004016030489948800031003d40f00d4900d850000342000302c8850b41e02c60344400d000f140b41c02060f4000c02c0e926405001402992060301c075102c22581015540002c540044540c2ca501403c401c000b03040030941020f20000350343ca02189221061800308000708030294a40c41400c0d00c1c1d00ca0004220390709101100240100e01040319001402d0610303860444ca03065460030b4040c030040c011800300012482500700c601501e50180152601c01d8040202c0e2901d070105680025401070424101a2480e0005000100c059010304101c4e4060b103000c9045a48070304481c08009159440780308204c00290074540420000200070003a5400d55000801c61810342e40c2d1400119810703443e40303070141c1e030540d29804058919107040c000b01440d0780c206c21000c02c80c2d140c030b410080b5401e58050003050842e881000700d0300800071165844091b00c00f5400740b0a0703035a44601030303401c02401260409010507260860560309140c180e8000c0300c107548030302020f20071021 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 63010893 1250 63009643 63009649
    0x8040b01090c020d03020906070b07030b03060601091a070606080609060901140402010f080a090c0906081b01050313110405011503051f050d030314040303061d0702070501050d1b050901030b 83
    0x1c40c00455016a102c4d03181529420b0098020f0b0602c84800340030241040003d4540d1082c5e403209940d000042940e07000d090308242024003540d680000c0a081600f011403618011205080c009054400c840001140c08800c1083c20b4100340028184601110b01605100c03100940b41c90050f54540e04c80d40c0307004110000c5545e11541148100e03016140d40c0070021110f0000c1e188542e00a003450361255440c00d40c0d00020b4201000034026111125001490078205100380d490000a01007140da140e80c048811040790780d01504480d0700084140040400f02403903d4404075400319105480d600c0f60420300080340950004001c0002009550b50030b002544807200076a070100041c4450000070015440103004905081c460901114480d1400051106000710120314042094070110000394070343d00100121443c107502e005441482a04190840c02c240101940c0c8000c0c2d485901e0501802158a01c08a00725078454290014401d0701c4541180030340f0401000c40d07101c28285030209140c0040e8801c40c0c2 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 63012143 1250 63010893 63010901
    0x20a05030f03150a060f090b090a09020715020a02010203040b0c030702070603050613060906050114030c04090902040b03150709060203040f09020f07020312091503040503030a09110a0608040b0109 86
    0x94000000e14036001008058486590005261042d942602c03101140d55403124070401d0002c1490b5a00c04400140002000301011040d5001c0da03e008024405202184d0310800710104640c003d54005941f840949042c41c8039544c41d0141c00d0f109440480c500148035019001107100d144681c940c2205a5685443c450050005446040060b80f0034001801801d00942c895038000d007009140031b0b007044c01c3c80d64031030035a1195002031491644441d0100903a5030088101166801182030107800c5184c0007012176524081ca103e112019611084400255101c0764040707640040702405a402c40031142c8809a0fa15905a828000094941c140010820301c04825070b01900e44561915914619000381b40019400c6a800d5911002c7d00300f001d100142d5007007003503080407138841500355110301280080205089005035a2101d0800402c204400143c0c044122a8841c4e601d150000740a0840e08243da00b80c5001101140c11811a1001165140c0c0188100b03110324070a9218406607038a034015017080da = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 63013393 1250 63012143 63012163
    0x907020c1009080703150c020712080a17010e06011e0203070f050705090106080106020105010b09330f0d0f2f07080a03020d0e0c01050d0906020403020303030114010f02 74
    0x40e003080000004515116a915201d0a818a0440551a1500f80c2c140c10020268001c440d604100280214101900d0103050605a440e00182c5011850030f921079582c81c0a2500042c14403000040d98031302180500d030340240e0700000b041c601c1c440e90b8541368223000342d0100351482408200d1401000d440e00c0212020030010b00c6055016605101403551000316114030010101d90600031800045495150304103000d00034012961100499494100040d0031150103030012588090100048801c0392103800c91003140d9684800c0203104902c2c8140b001c1907020b42002c0119403074200160b1030b005420717101c0141036481d07603c0404100c000440301c81c203400c59480350710002070440d4240c2c0e110074919590085880100d080c2890b6407816046640303858240c0e00040e182004a5400f00344030300000c103a0f10413403c50741410350040043c09000310020349140a260303d44003a0b1a02e85060720204501c1d0740541340156400b82c00c407916540c4071600841c403600349000850015221210076a50948005036400302 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 63014643 1250 63013393 63013397
    0xf0b040b04061413060b0708031b040602030708090105130f05130525020f0105040f11100905060f0405180a14070509010507031b030f0807030e07051c0c0608090106050907 75
    0x55100f49905115824040e0545007070040e0343d03020001140d40c0c043e802022007911510000780c1e41d103480c89250710300c042007401866640e03500344028046035070000111244c441d000610292260300c1000103c40903c1200401803400d4800000040c51101070554101901e00071280c08280b441080240310450b002115045c90305802a03580010070b004991030050900c159106407807640442e42e040e2800d48130203450407a054550200d80f0b006004c045074a00c0d0340e00000b211008041c00c1c906100500105150283c0d6104a6002821415a4142c2c1044a0041c074024210b80c091809050044a0ba41d9040716000c10352401e089081e0780c1101c032003826511450701510f8080c01c000480c8011556500030f05411002d00c01c00c6640c001c4034121809465000a121755a203540c00842c10760014221400070302800149070a000003d6007014000c9a1241525010340c2d8070594040040b494900c2c049642d0f40250070541a180e00ac240d0384d500a409500c20b0030900001d11041d0340d24001d000410004690a0b00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 63015893 1250 63014643 63014669
    0xf060605030d05040e090c120f0d030504030e01110c0d060b090c0906180f1507060e0601080a021201110412030908030f04030201081b0a0e011701080d0804150f0b040b0406 75
    0x3001c2c58401d0903082d001046c05c0100c1d03144040d0f000101c3e1502c03a03a848590f005a100c50364980c40c0e00000c0280350300000c4035140512031810541ea004d40b100110b0300b101414008001c001c0b00203000e00304034044280e40001c0803490f0784242d07400c1c0f8400810806010758001c01c03065001407605501c0a0488081c1d01d005080545040c4004e07410602d048205d5070096401b910140c1303a0030071541c40d140c0c400444004601e0007070350ba05891070088200c0e010125003e0403901301900400c00604085140000d45405a65403c0d90b4502d1102c0e460040404080d088400310f000704010031b00513a04c2a940301417502c00d40b500542c050712801c910343e89000300210041d403004200010300055209000c49a00403a0425407514039078081a421801600070b540c0400018404001c0160a5070380111091200275140300591000d50400e99000e44a00c50300e9552000e204041003c00c08210741469242d05840c4811420800104000203240240042007100361040e41005810710305454544a82022140c01d160400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 63017143 1250 63015893 63015899
    0xc040305120f070206070305040602010f0e101a040203010311130207050616020123070905040203040b01060c0f0506070207030c06020303100302150c060f040b09120a030911030a0f060605030d0504 86
    0x240d5194040036034500031500500a80c3c00503103a64020703102c2280f083d02c82c00d0b00c481c24030300001d084410074420011ba403400c103240c0c0348400002198400203800c200300040340d105220110001219045c49038075070000c1c80040000280aa20812018480c404840c0c1090711209885640141c2c0540751015009400c468081a00b4498080c0450f2442c0c00a0002141e1110380f4075290383e9501c000f070311218100c1c030100c0c10820b40c950301050007000340800721021419400c0c2611240200e00050090308140810800341c0c80500101c2c40311501c0e07165112007141c0c4c0500c1c2c2500002c0d112041c4d484210740b085502d0030041901c0c0e001000740c0f03208024030000ca44509146408201104003c0d2030180000c10003000603160020703050100500c02d008640081844c5c0c1054a031803d29043d008107001810303001030300114a00074000088401c8040d0514022484108504001060103030307c43c8250390521440820300c0800102803802c982250160004208140e901d005041d01c0b54038020203740018000c20040c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 63018393 1250 63017143 63017173
    0x14070816020f030f070618080d08090f0a05030f090406050a080114100e27030d0b0a09050601080c07020307090c0e040501090c0905010525050f010c03020a0c02130b041a01080c040305 80
    0x740040340c80800580080c0766480f030405003440101c1300b003400028071003400c10030110bc08200c19103080840310000c080342ca01940301c6c180c581c01506071044510400088074840c85c4d8503500024060300000b03105114950750752703507014001c0c9110004079a4040c1c0c000005030088004003280011075140889032803d59481c0e6021480e80b42c0240f03148070212080e02558000b409040024194021020b84000758030303c000c404021065806a201d841600d00b80401c00020b640d00c02850b036001101c42545a481c4c01c1a84002402c101c1d5507000007550603e402c3c00e08402070303804101c0311074281e0b09880800141c6d0300d504d1040166040c0c00040750103d444800e0400203544a0401090003651010400780da10b901044051441c400d5120b0503517580d44a0910320082e461b0a124004540d9600d040441c640700106030040c14408004c50040d1044c01c1c0140050151442030300b050340e000c000284108035800503104208421001809102d000407a0f81c0002900300c0c502608580c2680d03040401001505000070071 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 63019643 1250 63018393 63018407
    0xf040501030e0a0b09010e120a020312070224040b0a0e070b25030804030f020303101203020c040f020309010c17041e0803040b01141c0314070816020f030f0706 70
    0x4424000e2043c0e920034004645203501003805029003400210b80c00c000c9450103454014070001d011a6442c080201042d410703000022160045107002c0b520304a943c1e414000e0b8101280c0901c4d0b40e00b110b050707200080400f049100d0340b511551041d240c161180d11405042000c0f81ea601c01c003010240c3c02004144408510000070704080c03200515000380790700070354081381c00000e10014101c0100b06c603d402e00007050340040410050342d410384011402d6140c1070780805900c40c0284903054200f0018034403802407520901c084116007102a2090003814403003404c4000030741c0110717080c041a5103032503103e0b440d040c4104005070318859034810440b960785032074488404400308180590f1100503491a0407000070782c103401562040c0e004141c1c0031800d614021030744511840001b03145104411002d1040c290038100746420f02d2150301441d0a000300ad00e6840030030010310800d0300c09401500040740018041503001b001900c003610079604040d03c030318032000b030503907944c04201c485020b500414014080107204d207030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 63020893 1250 63019643 63019661
    0xc03050901090c030803181b150c120901140a08040309050d03081906030506010b0a02210307080a110f04030c05010201060e0a0209030c220605060405010c0b0a0207140d090b0f04050103 81
    0x8044059107044c1c1fa105e45007022480c01071242c80324009044585213000b0382d030100654000d0720482d02c0c004010841c55121158001c4035200b0f2040403d002600da4070840d0981c0c4c01c1c1400c030780c056a40301a41c12025001c00006c131411030024460000100d00c0742092020040e1007541611840001d4841840c0e02c15521010000031202c2036881c074001010800030440d140c020454681d0700c0e56101421800282000d0031842d00c400c0e22000c111074969081745007411254400b50f189055000c6440d49042c40340a0306080c1d1200032201404034214000c3c5078484000c2049a03c100300c404800b541e40e03001a42a100503101d65030000d50400001241c1e4081030700103111013007000701514100e101d04030008500302d80c52040d01609000c0080f012420b03c010703106a1002c0c100440e82c40d4182890140020074940314008000c1c80c4400e17410100306002c0594061701c3c3c0540c0d1203080d0300341030b680700c4e20040c0c0e880c00b01100c40e1000818034180014035078244011519014000c81001d4941403c1400540c05804010 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 63022143 1250 63020893 63020911
    0x103020c010e01060b040608161b020d0203010c020705130501050a0b070501091a040203210f0d09050f0f06160c17090414060f0f03060115051204060c03050901090c030803 75
    0x1200b010070b8803080c440c003c0903144058040745c4603420318400a140c40b00003049500e102200c4850041c1164014603801031100d410004040b04207010b2001c2003c640300c82c0302c029051b609101ca0144030b950082a0742041e03a07020307510741000f40d00e64000303802a00c07000e02c41c030741e0414490741061002d08a0301c001442100c2c01440041080e6110303950b0032855070707000c545c00c2e0440c999501c284801c61905001c00c11000380f000e400b6030a0421149040e00c40c0748601c06030b1815064000400c01e00c1c422103600f2011600ba08034099421450081009a444480e00024403281e4000c030340c0014042d14100303440b4500300120743d50b2503840c0c800c550b550205e0130214085a03e020001801754a07a107584600170740f060001343e00441034141c105002444400302801404510903980f041504d541074a000481d681140e40d10941c0e12060011030400381c51603c1030043c0380c0c0c0c2d0212410100001d200098000c0090034800e560300f04034641d0b60050031422aa0000001808009402c3c4204041141c007005180c00040715 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 63023393 1250 63022143 63022151
    0x20310050f06190e0f01180501031a0604090903020c030609070e07031e09020405090d080406020a17040c060206060105030403020a14030c0a030804020910050a15030f020301081f06060e0103020c01 86
    0x140c25064a200c00b60f46030030001902d086044c41641c03c0c080782c030320604082800d0089410b0952a00311000c00680c1c0142030400d80c0d142c03800c800300c20043e03221003104e0202800495450f074071106000c01034502d850058003d445022880c1c0002c2c1000908207214000d680043c01800381810480c15004801070040301c201521816441c5121440d003084201c444940340c00094166540d10500041e02e8000309840701c10b402070100c024a440d00080c0d8140d01980c080e2006a030380b07003038040c103a035641c3d07049080b2021916a1010881001040d480c14001d44025800f212495507515004507001e100845000700160000d80319400017400e0b140b58014907161020680c1d0a000e5000c010f189030081c4087c0c140d0004110308140029030429420540d04503000014a8034080c5c10240410403407290b602c100c100b0720001600140403a4400c5d4070062218016480075540c0307594500c6502e554030500c2e8002d61444010f01c2084420000074441e640072500207850748500e01407403c0044d0000d4008081e00e460b15521 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 63024643 1250 63023393 63023407
    0x200a0801140102070518060102060703020a02120912032209090f0f02040908030a020d06050a05010207063e0105090105040b070309050708060907150309020105032e060207080f01020310050f06 84
    0x303c0401c5140d500072040125121f01d080d8000a1402c04007500c8041494410040b00111660110381c62901da010b48403201e42e10101200030407104540032400c40454000403909007608000704540c41c1003006042c610754805030b182c107460821154080e1000344020080501940001c07294826074071018002030001451000710344806195500c125190b070040c42c0e00140145c1000090721559010300000c3d070741c08160318100030010b90745503124051141880580300d41c44454001e0503080c0f10300e004110b4031980402e0200e00800d800d00c0000007402e2450350030200021310007041482000e2080e40c020007003140c1c0f070f100c461041c2c00400d001c540c2540c5501a040300072031409003c20240b8001c3e4003030001045554a441c00c4541d801600305550402c06050a0310640503030391040c15280c101192001e01c107100c2c81d49880700c3c801898800da0007034150402020010315160007081c00c000b180c000205a0ba000c3c18007202c80c6080344821500c903214078900361024886410282c01640c43c00348081c1c002c3d854041 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 63025893 1250 63024643 63024649
    0xc011b06020d0c02030309010e0715180b0a020106030605160903080307020f0109050307020301180c1e09090b060f06040e0c0c03120109050103120f021507180603200a08011401020705 80
    0xf0710f0092503003d0f80c000802c1c041c0010091041070000c9000201506000d801c0140040b40c600860307180208001c1c0e2425116120740300c001c2c3c00e1000380a03d1148680d02d158145019001c0c02103403009503400c524000c001003016844110b10440c0141a0390b03140799460a66a5100040c0c00c0502110110701c20f2942244120100b48900030840d405040115194852407040500391048004030080c050050044080090800c2c24944203903060340c3d0107011800c106260740001d443c82ca91001d0000c500744400c01d003d01c14400b41c1c09000700002e8484003035118071030052010a00c0b59105084130483c0076000103074840d481c0700140900000c0c0000340d0f4508441628142e00340c3c5000c2e0010b00100c0d6842c00104104210b0818040040707496051000305490100b5010f034175103a421100b04041c9988100060324a031050003105040341d000700706644020307200c0100900401c0c11890124007200b509a0080a07035403180c0640b500d4090036607412109070709212042c407202400e0600c10703055104034180850303199 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 63027143 1250 63025893 63025901
    0x100501080406202205010201060e040b0618130309050109051c0c05060304080a030e12030708060d0203100b030c030c030a08130909061a0d0c060c1401060e1006020c011b06020d 77
    0x1c02180042d00000300c1c07144c192900c80050b406941968500303141046408913060101d940143c00150f9401c081d41ea4101240c3c6010046a840700311890000c00c00c040285a616003c1e0064026940c1a04c2c441c4c40324010b44000059000e881d40c0054200d000b0a8640a4070405142151140c0c59241c68151307610302080564100341d0701200c20300c1d80485c5245110754944203005a102910f401443c0d805c0107032075060818800a0300405c00c11022200085664441c008911703001c5a014003143e48042902c0c4041004100b80c400e01d92081c0a20300c1400b04a00c5c00040b180090080100608480c40341555200394aa104500001d189010044009856520791060401d014014403020400440362070100c1d03200380241140510400405001d02c01043d00d041da5507065551034101039201d0001c90902039044c14a41e898020300d50300701100490007a150030009409100d109117400102d44d1a00c17400d90300d80883c2c40d011070010b1815007480c1c6450030f0b09500c81c50581d000c0c0c080145003040c076210000580d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 63028393 1250 63027143 63027157
    0x60b060403050102040317030408070807020609090f220819020a051504020f0108190b01030f05090c0307050102030a02030306012001090516050409050a02090a1415040510050108040620 81
    0xb596012400f0020300c2501644581030700c1c14418800d2851615540303c1c00e40f4090f2150183c0f518170046040d80440d11900d08807200d1072001840b0919600c1c02400018016030100c070144004c00928100e0780c40c80e0400038498501c140d010045d9400c0c0200e42864420004003404084110311591311080c000c1001800151920310b81c4030110120f40ca003e006001442244000326030400442070104901041c8134044140079100e0000701048501586004801600c1c21601c220000d501e4a403c0c44040840018601d01d05201a801e0340c000b00c1c0d9441c01a82c0364092211144c0250b042000050907035840b40440e0808407000c60000400b00900017800da084602e5400200c6140e03000044100f1210300e032410410040804031428440e024255890340c0c0c90f071403d040001c0c0110b0705080031450705810740d08541003e010300701c94402186410000e424001c42c444000e18011480c02001c588021001d150344803e903803041c2c6034051103440d00e94901c0000c0c245080d031480c203050528124209000d0ba0300040a079 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 63029643 1250 63028393 63028403
    0x304030c050c0d030c1416140310050c0d051009020a080f100f0501140408060f07080601021c0503040f0b0106020d02010608010c21020c030301090e0f01050408040b07060b060403 78
    0xc14140d281c9580380140206049120f11240841e100019174040c0610007410761003010a00d040300c0c03080c00345141c0000c04a640e0801a41c42c480401c551000303c032030100161084048841c03400c184080442107400685d007004085504004218000d840c6130030440d0000940480010702d955a0303038901e030072a008004031200060582c41032001090214001e6a040459107560070499446c04400030700494480c850300b410300c4594554440b025070a082554014900074003070300c40ca4988402c0450b40c8403012078240c0d01142c020750118104d944001800f50038220850040c0319104108801079802e078200078822600c08400c901801c0024a003007080c103000b081c0c41c1d002024109401c840c040d09503031040c0c00001c0341e40e242c00e0002c01c5c0f5541c448134621032042c43c4031400004606404086000c5d1280b011142c0c2c2e648000000000e995030583d0107922010b9143d1300769103c00b003848070761600361075007940c002c0c140110600c41400300f8080d120040c44000c0c422040001c09403000c03030208610740c10552040ea2 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 63030893 1250 63029643 63029657
    0xf060e03061b0304020d24020d2a030b03010204030213060305100203090a030e130c030615020604050309010305180a1a0f060306070e0604080a050a03031b0801060c020a03020301050a06030c06020d050f1e030403 92
    0x3011340a01e000c0c12911041002c47d52b000c50101e94920084031103900d900004158407410070011684083d41141e0182d600600001a404032607440a00a001e00b444122154414801142c07025078561081c3c0c0d01801141015181c41021920201c03035128114525a0788400005180b42000074148907441041c841601c010480600d0502c000c00e0300704200c025401950800b004200c000341010013200e81941c02400d00203131036103400d40710007400304030522101418483d51229100b4000c80070f400e000e060f204141c0000d82035440d10400c2c0c40d0410152142d5401d81d00030000b14480600038003000402c081d010b881e92742007030340e04c881c3c903440d0005003002601d075504104441400d240e490b00600b143d07404081207104240c1e5a105005214640510a0104000c44000780504541c1c0e1107000c82d00440d0018001d200d030b0f0404001070801000b151008441003d20008001040c03400401d12400c140810740306c290502c0c56150040c20540d016841c0079441c40a000e050481f0907441c2c1c000307980078070f0190fa9504 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 63032143 1250 63030893 63030907
    0x3060424060f032a09030b04080306090601030b060720030106031110020102070f0f0501090b09010b0f192d03050d0306090908040501030c090f060e03061b0304020d2402 74
    0x70745102c03101d07204041010b0400000809400f41a5000c0c41d004c141e01c5080c1c0702a0300342d01000c484120180e040148280792580c2400b0605c400100914003601003250582c0c8140c4aa000540848031481038032500442c091048501240f00310041c9003401245601d2000c10a1b0180002030840d0f4030ba41007100d00300320314048140142000e9547c40032048841c0021032070803d10f9181c616202c11502c0c4c00800784d00c07681402c4c00c10444c7c29004001003a40c0300000d80d03100d0400060190103800c1a000c024014110709401d24007a08d440c01440703800d0490048501c0280381409407005181c420407000c0c0b80840010b83c8143c0ca4a010f480c000f500650140f0042c0c004c80c1c506403001019a40d50790300102c04103061450300c8010400000854007100e00900b400980d02c00d5064082c0c0e421070040d4065003034008601c1000541c19004001440c0d8124200e050382d1541d901d000c104e01c0720260054903584950018000500181095810a04090b01451600c1c0c0868541007600c90403003c5180301610203900850780c2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 63033393 1250 63032143 63032147
    0x20307020708161a0903070e04060e16080d090e0a0207020613030804034b0507031101031409070b251a070201050f0703320103140a080a050306042406 66
    0x5081c4c144161180140b600e521034000076520000c0e4092441813442d0b241c0441c003004056813013841c0b0840510150741034003100402c2030034004080c0c8100c004034001d40c0c003000c52252041c40d94500780d803502d96003042c0c4e0b6240c8c41c0040009401c03d18040360051010041c0c1204145601c82010045110f0091a0f40c0c1e207095103000802002004d40070411080050304054404003000c000422494801c0e8040f02400740c80d032125105080345000107031903401008000710034040c1d80360304400c1c120000e880c00e100001d410018141881c1c003c41d180c1896800a450a000c2080080020140d1003408d28600142640d6440841d45055040034100d800b6600840008210030802001950243d00d80c0000c10192030004802c031081c210080105042541d2400001e4250313083e042c4110030800340b07411141641d610042e941468a00a000c15101e0751700e881030010003c1d4000640b05442607000b070405052803e40002030341c05400207099294440d071110380c40084502d54410003106e5001001d58100300b14500780c40 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 63034643 1250 63033393 63033419
    0x31107020a030c060f0c030c0b0402010905040906090b09031e0f04080d0f030c05070506061210090501020c011505030703031206150c1a07090b090307080d0c05070b12010902030702070816 82
    0x7020091001080754000848d03040003990174140d401010014181e51640f00484001000ea040160301c00d00d010601818000382c2d501401c1203c1c0f01d22480b040b0768840d000000c0e541d00580e01c240781c56a410601d8010301c1d1010102600046400412527401c0540307580c1f425040540c10301020001804400e4140e000e650301d03004000d400701d194200320745402d0b8561205c988134907000304691b00035240d5203007450316040100b10000384061141c40c20006100c103803030402d000c0e510030708954400f982000d010400c1540f994070039808a81c03000340104180c42c60b40d03600f512589401c14601d003804e0f6507a1b50000e098a10403209899107405a92103502c00a141c0c03405d60083d0800c0f00d041d8501030394400c104142c840d0098094401c4e0740b010f96a842d10750300d1a0380000d141c0311054210355811301615921100b11600400222502445103094480c06034503840002c1043c052a40e44610f2194103500401c4032156035402150800001d1042d582d07035540b154941e600d028900381c240c20303903041494800c00c108549010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 63035893 1250 63034643 63034667
    0x2160c030f1514060f12010c02071706010e010501180509190f051504090f020a090203160305040203060402130912110d11030d02031f0e01031208070f031107020a030c06 74
    0x4410800c14401c01a14a107543d0f00904c03860081c5070321254440142c1d40e482110b9100e041c044024841c0082e021002074030b0703600522408500c00640e205d04040c031100071a20354143c42c40d00a501d02e02d0fa280c00011140450307100e03110414040d80c99030206450321b6080e4054482c8056122141c18904c815203020101d03203602c040560510b203800c00384030b02a04c580c09201d4089008a401061180c00c505200000444030040207621425038a0001882d51842e00518030442d80200051a104041001501550740440703009515412002c0080d0044c034012070000c070010b0340c003c80010004c00079642c58041c0c01c4031048a0007c541841c0b142c040b0b28200f000552440c84842c80d042c0241090700b40496682e0140040c410035031078011000400d0a800004605064050f0201c10444160380715114101c41c40c4c2070005072001c0b15486d0383c0e104001c1c007901d0003a010340000d584905100918950440042480d0549041d080300200214005641c4640c0010061070041d030903c4045850400702414140e1490 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 63037143 1250 63035893 63035933
    0xb100807230f12060109060206010b0d020f090907030504110a03021f05090d11130504021c031103070510140c0d1505041a01080c0c030a0302160c030f 66
    0x810080389a03480300720901c05181100d4000000d140311244140140078510740300d1081400440c01c990168200403241380203500a0321900768980c0c45074412078070f50b0400d010f030f00000b0900304108880c02142d54002d04290600f010702600706250000000c0d9000010703111800084c0e2a01d06100502241c0c00806040300012542e40100d40c3c590f602140441c1d011207000c0078001d00040c04560701c03500400445d8008007004001074030074110707494050300c000120341000d40240041c42060b0015500f52040c140103030307002060702910100c044800801d0a251150440410854060f180e08490040025142e42c0e8810750250008034032100a080c00c407030040c100909021811401e001041c148002103031600120100041120304044004050388220b5038040307500146030500940030281300100c50501c0700000d80e0f40c1081c503283c81e0f41e8071403e4024000042284c0d0000c21107004030900a42c020010413032035268562030700410707031500d4910213281c0d0305c1035a600c02c81030000700c10040240b6808400220817 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 63038393 1250 63037143 63037157
    0x6060503011e0e0102090910091a0d14010603061e0b030303011401050a02070b0415030f0506010504120515090303060901230d050f0f0d0306050109080604080a090305100b10 76
    0x208045450003034020034848041a40c4500c3c201083c1000e404660360498080d0503d5481c0c107102680f00c1c86041c86104d1240c28624140aa202e29208200070581c0410010019041413107240c45151006094000458440d0350741c440010020b411402048030501c080074600c540c00514240b1201941c0001c4c94441c442c0d003003000180200c041c42620b040c00d410702860a65107a8a88907801d92030000700703070820803043c0070210340010f617907180c071079101000d02099170207112886540ca0303a0030664400755241c5001c21010300081c40400305149482071860f00990484601c01c108440c1101400c4040c0c9060485400001c2080340500f030581c0c07950f0051405040799074804030a1f144510303140c11100001889180c0e005421402e2080070840015600758a00503100741a440034003555480000e0301180d001300c0d0030103400140da507000c3c070410000c480818019240556650350b50758007980c419803005040c00a14040400811800c0142514000110b100000d5004a01e010030112101d4a03110341c1c200805 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 63039643 1250 63038393 63038411
    0xc1612080705030f0313030905030a0209070807021f02120702060f04080a090e07180f0302061806270112050103021f020c0402070506160f090e060121090606050301 72
    0x5526444909103400020039074841005140003400c5114034005081280004000c1c0038200c0303200800c14041500c00c1c2c45200c207440c1d0320818152200c1011801941c8040e8880000c9c04c1640581c0300c0b1903101c0c0161040d0340c1025140c03141c80354200d442c2c8501300280303940894882865040c600345260003400b00d0000301030a1400101c40305402e0f60040004101510100740c0c508100c0c024240c100c044c0c40c081154a001e890101c40050081e0480d1500851155060754002a602024451601920340143c0150300e0020384104941c0c00c2d0558289450f00404104400c180108807441b0038410440855140c40901c41708100040454000c8283c1c502503528010042005036648005101000c0d424401c1d00c214881c9054182c0c03e00700000c4c14503420a00000d41380b000c200c40411031a101c0c5002628900c20880a02c1c0101d80084c8890801c1001c90400d0740148942c1424041003640420145841b414031020041e00c0e00d00e144029035003820380c2d038a0b0b22140003000030b1406441d015149c00c0d0300810494072 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 63040893 1250 63039643 63039659
    0x32b030203010f03060b150a031a040209010e0415050303041806080318010c061410030302010501080d0e2407060225030e1c020a0e040302120310060f0c0b0a020c16 72
    0x3084e100083c40103603100c2d9042c0854a850003c0c1c1c1d1445102c0c2120745e02c5d0b0b804254080e02800079042600300f00e48403814a00d98603c1c0501c02d6840c4148183d540c0711292000b03002b4030008003080c000e02c3c20340c1001c0c04000202d6a1301003000780098a0001e400030307007401e007c84a0009a41c89a00404d110360006e2000410001d0056440c00c40c4003000d181c45c020703038031f40c41c107048c001040565070711a9181004010840700c000004500c4c8100c2e07200e580208020faa98100e11504e030710514042900050402c12400c40030b01d8540c112141c052404040c0481c7c655011040c001ca81d441803604aa4107034011401c04028815403102a681602d26080003c40350703410f5400400c101d08224002d485448945a50301c0217401c0011a14040c55003e0629100c0d1922403090110b80e00c42124114010300c01d00801048845014040e81e004401c00708900d040f46041c554141e401c0402da001010400c000c50f000100410095000b03640a1516107800694030441d514a050400008103804220b0082c148410800783d2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 63042143 1250 63040893 63040919
    0x7050603060904060e01060306020a020c090630010c020a170306031507141617070807060209062101060809030403150e03040803070308010f0f0509041101030605032b03020301 77
    0x10102c0c0c42882c20f03a100e2510384028203c400c1144400d41c07811a001c4204070b80c3c0d070300402c8810119001c40700c2c00700c0110304000100404542c0035400180c034018a841140b000c1c0f1105120300302c10030754009141003580e240c0303003104c1c2d01002103401a88160b1070b11041c0700b01d403400c44042c2100080542d255280c8000442e07500e00107400c02129071560000085c03809445520054410845a403015948108400080c40a0395500e01c2c1910305e0305c50641d09800a001000c11038808a42c00301600d0309040f419120130000b900025102d40e08540200062740c02d900d500010f10120014030b42800100354140980248034040040c4858590781c420007051000c40c002d004c1c0301c43c0c15201ea51020072000843d110060070350003550700ca04040c0c030000c500700d0101600f11030540d0607140711407200404955914a030124042d010f104103074000c05480302080216920f200c1ca400c0c0080181030100c3d625540c0c00100c1d152400586014208000000703c9200d842c0d0105850341d04400c451405604550400d40180448 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 63043393 1250 63042143 63042151
    0x40b040509060f041103070b071b05150304061e020c2107021507080f12070201110d0f0603080301060c0203010b0d050705090901060f0b04090c020a0507140d0b040f03020f07050603 79
    0x615121800101000f12500045005c8039014056880071550349903079122603003004504031001410701d681c018098000881680850b00d00801c940d06140d04110340d01030035440036109454481d11050752540041c06902081c4a01c1c000000050340d40c10901c04c583e08084007800c12445032580403c4a4040f08001c03000e07550034940494001c518036410150f000b0080c801d4410082840e1008214151101d00d0301026100c440da0148140342541c2d103480b801c9027250345001c1080810030b01440782003c9041d150344040c00b24080c07582c0000e00142c40752203000042e00241d11440020f000c400b200d0045060038060715600d03c800350340b0345006014551310240c840b86c2e03600446028100140004281c00c0d070075001400101003540080c640180c950401841a6102d4084d8150f13190074001082110f43c80001c6100c20203400001411140b802e01c0c28003511488501450f95100303002d6403e400104044500d118020ba1199080203601041468081d00b0901000c83c281915000420308000b1358035020216684 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 63044643 1250 63043393 63043411
    0x1120603081806040e040302031e0307050301030b060f0d0b09070b030c190212070b15120706030f0e0106150314040308010b07020103020705060403080402010206010f051e1f030605040b04050906 85
    0x440101c0000b085041c0100d030300105c0521144070a11040c1030b0048002c01c0c00340c0000e4001c0e45211008480508248000d98150b000100204010008514154152900003000604c40b90304c94200310000340340003806410030b46281c180d000500a00c0c11080103800010300707118010714190320f013400d0645514011880b840d0b080d01c1c0c00c456141416442441150400900c11141646030b20140c00d050100074021102c2d02c8042c40320501082d03540c58040261001c0c44481c070024484181007900031005041a81a90145a1384840e20400000428000da0000e0106140c18002c090941c603270040c01d60360001444951080f042042c0004682e01c40c1c0c03800d054805801a142d5149110701c0100c0003446525030291007400b5401c2400201580004c030140a18001d03030172a0820303602c03864400c104030414030a04c6d42c00508075908070281403e440781e00d40480801489130541c3e250b010705031046519189030010000e5640c51003031181f403400d442000920407041d541000245882402681c1e0b441c0b01500d003000c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 63045893 1250 63044643 63044677
    0x3090609030109021305161119020f040e030309070902040302010801060c08070b07020a0209090106080a0b04060f0e100c020307320118030306150206040b04140a030e0112060308 78
    0x580d070786003508001c3c4403507409403c00d07800d1441815050b001300001d03142d2940c824008900304040c284640c1c02c0d14100000c0d07401608400c0112401080a0401078004a0f040a134940c40c00e02c00d9600e40c441d001c94201c0c440e01840c3e4914001000f075041400f950072070061140306103c14000350b6807001c400c506480030350920203491440c0e0300340f919a5014517030300200700d04401000c12080f42d80c00b00352184154402c0d2001c02c025190001c08600303840c0c2c280105403803540a452203401141079940a5070f08035000798400108414040c5050050329001100c1041650014828000d2415144240c80044580d4405076041c61003a0b40ca810b00d200c4070003203601c0d101e00050000d03035100148400307000c03074031aa0400810001020000046c4030713845008095011924100002030181600750000d09940e03810b50203401136030f40b650f40c0c010b0201d0015209858104100c907000807004400c11562031264001d449006420442000040010200f4060761002c40e00b001410000964280203032031403c1d188404402c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 63047143 1250 63045893 63045907
    0x803040b090309030a0f0308250e0d050607030c120515130b0a081e010e070b0c030d11043204020c0a0c090f0b060301030f060203040c03080a0810120302030906 70
    0x980b460141020882e0305000b944421010055602c030070310203d51081e02c5407c015a14102218504503441040c440b240000b40f50072503509100c0d00f680142c2d00c10090105c0070000c03054988524004c411a03588000c260303200a1402100d412100484503804038500600503131512541030341025055031100da005250f0382d00c02010490b496002414280d002410343c081c980c0ea80e02e0b00e25620411454400840d50811301800e0a500042c0942e0784213a5031100105400e518140700000c646c1d20030070924800780010320105414880ba0700590484800c041d002c0c40e220b5041c4502d54070031000c040e0049210010386d2002807010140c00d48040074210044a0060b15414803183e080d0030200d2080d03005000c2c016600010628911903444040c9800d10030004000c01c001c0c840a0011910007800058549000701e032160740010f50b103800542c0c0c0244a2840070800342d50740da49110007500b1500c00640400c440c1020400b400c40d010110720004c00200f6607411502c0701c640c6006c0e45034030424601c0d81c0542c00026000f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 63048393 1250 63047143 63047161
    0x30a080a0e0607020907020706080106030905072d03050a23190201030617012304020a0909020f090103200906060a0c0503160c06020c03030403020f120f061609120803040b 75
    0x43c91a03a40c01a10f1190a03141008000f9111401401140b011850100010513410b1007440b5002c1410b9000d801010081e08211700d9010b0702c035800304500d040c1440c076440400149131600340303003008520810017001c425800d03103004c2400c2070024220122640e0315000354403030160001041c0d0500300200c2c01d00b08000d0aa800104d0150550b0b030040746200548281448910304c05501c8010700148107504c039103032140e020b8405559820300340c0e40654003051840c01400a0205513000d00e03640c2d84006c00e000f6000d041b10b0003040b0081c07801d0b401074941c0c0a001c0441003900d071041c58550781103a01195600e48034a020000070f00c3d540100041e030740c204603440c6a803200b00201041110a030010014694911161610309908071080034001e18006009030074030440d09046c00402e80f8180c0754024941e0040d5000b0409000e80207c0505c9003c031907100b0a41400c00c500c9044c402540601195242818088000c09024204450b16407016620568010b42040410426800e89030410341c040e04004454980c4004 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 63049643 1250 63048393 63048397
    0x61403150f060c15010b04030b0708090f01050106120b220c030e070f06090803090307050103020c162309011d070c0c0807180c0f0f02031209031206030a080a0e06 71
    0x1a400460028000390f00d6000010311a030303e03d92030485282542e0700e038900c15403240103600c00141041d0201000c0f031210342c06081002e50000340b00e0b04441c0984401200340f030940e402a8000804036513606011002c51409005090b0300c104285e5a03e140ea0101c0804c1e07101e0450000c04080720325647e0a0854916403194010000120001040310200741c0c65001100d8040c066101e0440403982c0c0b0030000605a202205481c0b104500802070000700d4903150040d4003950104610035180d00842c02d940202950004a0f88082c000d2009410203500068500798500c1022200c51807242c4080c03001080101c81600c1d9090075505070404644458980184c2501c00c046410030007402581e00c2c08000c900700034006041402c4840650400c0340a250065401c001c039807600c5c4000002807109004281201c3c040c0480d02c8070300314584122440d11005900c0500740030402e4843d40b05070b400000c2d12003441000003c01e1600681c00710058504c180c080d940c0c40000c4e21407652a0f0062080d0b042d0307400e04c20b940d0b64003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 63050893 1250 63049643 63049669
    0x190e04020f040e07080906070c0206030601120c020703050f03070f1b03051e01050f2e120c0510051615140a0e160807091a101806140315 60
    0x1e106860700e48840d2100c0810b03604036040d00000700148005115140001000c82c001c07000e0361a0104503401903000e000b07031035000400c503d060085450f07001607141031034400c0c50b410102640c01b41161a046207801e6040c0b003001d660b050a268024031400b8041041c000380c544081d03900289201904107400040c80c440380d165800901207014142005c18005003000b10040f0780d0710600000c111540e224001001034103010703a40c0806d001c00088151840629103092200c0040419218841d82c55440d00e4280f049010150100c07841190500d0030040790402d0000c00d2420a480c0c10424240516000752050030341d0b01e500e000e0320220100600402c2c0e041c2c3c0d6841302c800710b2410408669a407030030f91480c0b0003601c219042d003201d1740328429007544a505e50560100582e0280720203005403e02d004038160190103006000928502400b02c8074516642d1981002003031404d546400d0040c003100414810840403d5024030144106241102722803080038085952000040c8201c2403072011a201042a00d05c00305 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 63052143 1250 63050893 63050917
    0x203010b160c081c080c0708030601030f14091005010e011a0706090507120b15060a200304080f0d18030b13021801050406060c050d0807110303010303091406190e0402 73
    0x441c00c4c0e180340c511a03c2c010212401d4031038007402c1d00c6504120000b44036002d00508204820700118040e9071181c0c2143c4440036403001c011442445039540a160303094103481414640e8024100e41720910742c680102401001d8254010a41e0361604030001906a0348100c00185020000344160402620b0b07070004003000d4020b02203440f810b0f11102072034889952004169058100c20740010100000c010440d162094044c1c189810009080c1007a590400608080350300e11498101c0400c418404101401c0181a044e00415281ca1010055800d00011040308000c2000304e09150f034408860b6210202180d9118512041a075109102c1050701103403000029400f0002c1c144071030000302c50b0f82d40c03a070503924115420450980c0d41c4c0c509480600303d00c440102a504140b08100d1524000d00700b1940c400b100d03080c001c840034900308804c0d00f5075000740c10850104103604030038840000e10701c05003c12058140d410a1412030107c00c001803c1508125200c104283d010446003180c459030141d4400744002c0c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 63053393 1250 63052143 63052153
    0x9030b0702060417071106030c1b010203060a060207080d0c11030d0f020c0d02090a050606041701090302150c190201240311010804020603041509020d0b0402010809010203010b160c08 80
    0xc444000d460749010b46094545240e15a41d240d0010300e4403080358a1544d0161041d103291180c0020f01010f0b0f080105109650a0107110328540d10501d071080c4800c401d101000180d8a14140042000002d21500000c04542c0300400900c445a40041c07a41504c04660906005200441c5400c2c0103205154042036018003c4a4200022680200c1a136540116a0f000d44d24900c000e4800d0040054050340d02941c0050008046902d1029640c0820703000071001e40100d1400e51a450b01042580c614004007000c5c0e9582c41101c000c0c140d0500c42c41e041144000c000d00c07100d00f040c071408003090260106400c0b210980d00384c190a03041c001d6000c1190443d43c94240403103025164a400d203010701d50303c4291000000c0200441407076110341d0034548035941c010245801c0d0386850300c900c034030011810410102c0942d107460182c09a500d441007542510310904400801c1c0c0341074400107104ca5009005c1d843c40da80148014081d00c0c1301c2c041940c0000000b500d08a05443c0e81c2e0a0269005016600c040080e00071 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 63054643 1250 63053393 63053401
    0x809070f140108160c0f020402072a080304050105120a090c0801060305060a27050709060e0121030905040e030712020609070b0f07060f23072006061009030b 69
    0x50380e000200c1203078003600c0c1c4095039612203100074901881e00b6450400640840d4003180026910200286080d00150005003045d003d681d8882c2801038100200d00c41044062168403107840c0d0020200142901201950034645041c00203000c0d4056800c1c2d50221840f07000004030300c0c01c2554020820580c1140c0b4421400c0d87e2001ea003402411103000642d0b0324000e01c0c00040d41e064a03405020801c06800ca41c103c10700d01041000c00d0720741a8110100c440340a070240026a5841502900000e40070300e48038410709500d410391032240d24046600d81448410305802c42c4000c0782d00001c20350100c0700250b4012410058400da0b6600314420384074010244441c48000d0b014041e40059014429a061401c0384c01d03060300d40911010b075002d075600840e6108810411880041c0c110707042268031301400c81c0042600030b03582c00b540c0035501c0d0301e1f180c410155021070200581d0301e60204800d110b8442119450303e004400402407611000c006091502800c100881c0040b003d1041d00c0c60f40055400000c0d054080c28 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 63055893 1250 63054643 63054659
    0x706020109170d1e1508150601032301060302040f0801050f0103020411070f080705060711030316111b090601030b061603020c03030c0105010317180904050c04110702040e060601020d0809070f 84
    0x17821081e05d000518404089094080010004420328010300c4001c216510a401140941000c052040c500300c51f4210710102200ea44001da806803909440142c3c03280d04001c0920300d100a2607014524681c100400d204003603280494140c15a501035401103a100361a4901ca291482000c500400116008203880140946003010f403140b14401d50540c2c0b881e80319288201c1e202540c420f144802c940081010070301d9041c1800c0c1c002120070160501080000384400824180541d443c09441007000081030200d0510300103294a5103d40c0901b0300b04414035120010032001d000344411100c1c90081d0364040c2e41803600800c4403022184005003280d980d06042c0d064136018041c284402c035480c410656500b01c0e8502c410040d00d50400c0700c072502000c0714000500b0450941c8000d80196814040e112010f029038540c0d0095a0344070101c1c14401d039842010f44103210450b00300245110f120340209003404900da17404074608028203624a0f04114a840d50b824190510788150b1001c0a68500b4a8001510384 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 63057143 1250 63055893 63055901
    0x100e31060213050904020108070503090106030c09020309100509030d0902130519060e06090402010c150f0c020c0d08030103021e0603070305070f0309020906011b050f0c030706020109170d1e 83
    0x841c2c40c0942046035074074070600c00c45040c2034400a010030341c2072001030042813156007d180e010241c0800850302e030341d5070f40381c100e41002c003600410b030616000001c0040e0003c04000c0c024070084091010442c610740203c1c000d0303ca0181540c5030825684403d080b42c00d42d40c407164245060540c41a08121600307040f403104000402d0f030500485ca150400078000b820302d0842405c3c074461013026042c2c00f032035034665004464140c00120221044120096055281f00320303445241c0c1041005100065400800308000c0d15008100c0c0f00700c0e2280b0084032102002814100036281100d80c160b501940c00004020202804800359110540180c404001c01071003d51541169015130b825403519030110b80c0c103002c22030a48400a401a4100c4c082d08040703000c40d4400e04c0c030840031300424020102564803656646051400001540495030b1291041d80403034034080c01250010b1559000030030514000d82d842850000d03040d81f02042c0d09001140054003010590000007104d140e582680c161700207107043d001c0080c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 63058393 1250 63057143 63057157
    0x303060b160b0901021e0901021c0f02120403020a0603020c0a050f10140f01030308060607060e0c030c0a060f03180605040606060305060f15031e0103050312100e310602 74
    0xe1076220210f20f8481e410b200302d82100d40d1080900083d40181480340404e640700c40b4120781117106944402c5841c0c1c9882e1014015072005542c0e0107603034428003c00034038000c408540401d00d68010001000103131303580a90041105c04500340981c80701c08a02000382400c0c003205003e4400c1c000d80201410400c0081100d000b2080441401c111410b818502100c14107801c65143c1c000031401c074011701c0800c0c003692038668800c030000c0407d1310704000360b50344200796a0030a000b03501c6030748050010b50080c942032240d500341c00d50644508190038500307180208a05034041c42d02052640c0c805400c0041020002070040345030700302d1002d0245082901e0b07c040103000b548282c1d80064940300120308a0700d010b0194a1001030b004194000d683c40380c0c0b207504500d0f44040c1003004508842c3c0c01c04403500c210590114025800f84c0061601d60f80c2c0001154030070a40104608490111850180000d44088600680041208003030440a00348520170b206602440303501004e00c41c51040c04c01c001c12503190001d00c10 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 63059643 1250 63058393 63058403
    0x61201090807050304150f0e040506041104090209040e0102030610030b030307080307020d08010801020c0705090a06030b101e030b07120609111308010b01020604030c06060e0106080403020d02150105010c0303060b16 94
    0x44001c500900702c0c7e01c00b0300130445000140b00784410942d14030301500102d4000000800016404034a807904200f5a4041d601034180c55801042045152910f413081e92075200c0550020340c80c40c50300f08001074412405550307803000d066172200e640e900758070200305540c0c8960740401401c0e0f5a050410707020390b070781d41020528800140d0030320001ca0b200b4810700075220100220001072400e035003044200101c050000703003410385d0030317550b031100001142e550b850290250307100303241032140355092070410824001024982c0b0005103150380d0800000c0d00c10140a0342c46650b0746002d0308a0100e194080010740139961201d02030905014a003488550404024000500700c203141c4c090903980d8094845c01e03649180d0304d4601503000040014040790280e1842c0014500c00d100004401e6114594400200e0084e007103000010041804c0104050301008054020403450004002c9071281c0818103561200501446040106003400750080501a41181c0c01610300c42841307688a01100c1c1d110349250310303480b100f034075 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 63060893 1250 63059643 63059669
    0x2070807030305010e090d080c09011e08041b030816020f03010c032708090d030c14010f0509010905060106050d0902030601080a05120a080a020a1b0f020423061201090807050304 78
    0x2d07460740001440c100d0100588c40351403950390f42801d0301d98143c0080603241d05000c0300080780d201c021411a0380c85190801d03a15135911500381414013841452440300c1c4012940424030050020408003002c0d9a502c4030101009208100c0d01e10204945510950444da019804c1c1070350341c0e44a50301900505800039038604241010502c004002e0104c425010000c0e122070410001a403035401e20381c104152050180c10105801d8500e46d95002c0c101140d4040c15185954a80481044030061300440307403c0103100300203100741100d94450f030741c03100340c1072003100c0030700000040341070322070101d41c000c090f40341d40040654249607074564110b61900c4c20703980c04854501400d03880700900d2503181c041d521100280d41d180700d038aa84014010009600c154400c505000403842e602528280c2141500c00c02440386990b10440324244c410700055403071a01d404040a003080342982c040d8001ea881d55644450216450240880a6070310f680c01400b8003100a840014006841002c0c040008005c004841764480210 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 63062143 1250 63060893 63060901
    0xd06050601111f050403050f040315150303120c1b08090f09010e0f04051203070c03030b0604050d0807060f020a020d0f020111030402040e0c12011409060615030a02070807030305010e 80
    0x1076161868058100b40c0d003c0c0069804680903150f40c03040303a10601c00c1c1003140c900100d103214840e131030308241e10480350b141546e11096004d60142c0140f13820050843d008401c1d140c11960041c204440d03c07040c081c2e07c50f03030380d03222007144912441846642942c01c9400e50012005802d204049900485506000c2c40406020800c94200030512078100c5402d4024907549441d41d0020942900d0050b2041e54244101c00b1010b801c0501d0710002e60207883e05884075203d1504601e03015099808080d40c40740f0231801440100000d0301e40c5111450b10f50b5200e40c40f903a442c941c0b1302c0c281008024000c080b081480c4045184806560009242070440155440b009500c200703c95040b42614103000c00b042c9061014070104006003003d42280214901400a80da80102e01001080c1c3c03690409080700c06a1b074542e03601700d0200154154040e046100a03000c1d0120b4034048001c43d06101d6043c3e2603101407500040000c400401e1981983e0344241c0c041212a030701c05043c00c0090241a080c0030740000016100041 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 63063393 1250 63062143 63062177
    0x60203041d0f01210503181305010b0a03020a02120f031f030c030609060914240105030606010c030903080d0605040b0d0506070503100509010306020c06090609070b0a0507020d06050601 81
    0x2188210112002c0481e241e00305012a0852401e0030020007100b8414008440028024400f8101030003600d900e103141b42c508002000011201481880055480c0070014800c1d1000c09080b80d2449202c0d04015a4035498803400300c1c0f81c00c15110044041003008901d40c0c20302808800154003c4084002c0c0000c60b610385007d90750740c0300e910304c00148410040c100800004440346c2081e0343e003034011540002c0740341c020b0300d41c8041d00d615009100c0c1d49801400440c5044420030b95170303c0c50030100c000780110b50345c1070401185d502c01000d4405070611240380b125804143c410500f52029545c0864120307201d5429200d820b02401c80ca0055501c154144490101c0c507041ca01400016541c1141c0100610740f210303001075480d54809800078800620403c1c021855840d0584050700079807041d1001030340c81c064030303001c0c0f8144ac0001d07149480301e41000d0b0030701c040c40d400014404140c2e550206a140d403400516816103441c81f80500080d00004c1422519085c071155600c1188503180a03201ca07a00d0765000042 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 63064643 1250 63063393 63063449
    0x30f020705040e0106051f09050d1e05010b03190308040b0a09080a0e240d0b030c040908070204050106090605030a020c0102090405010b0903010e0d09140d061d07050a03020d0b06041506020304 84
    0x7644000880c0c0150410081c5802b1000c240d00034003401400b840a00c061010030507100c0780c0c16098541745c0d115030805810b403e08114078500101007401e9000f9801031950010096607001e8009008812001d0106282c54a10360041502aa01800140c2d90f004c005001904106110b10080e02c02c1c0c02020310307260054030003e000c00703000c02c2104a9510b00321041400381c004050442c4425094882d01e843c3c01000d440758440c440310107028009480e1145000d01c10041900c405801070020048400c00030011250030000ba00d070050300c0e003440543c0310546c8414560082c014203a40591103070604c0c2c0006400125400280744281080c1c0c024000721728030b80b00190365000c0c2e198850002807041c0c001004503000c020302c0a03100d0f19008080b9000040c10303491300800d964100c03044000c9001c041480000500040101d0001004142c4d52034040601c0d54000034080c015480014080d040480001101541d6961100c2c1100c150440041d0503140c072024000e5482d009401364022488000011108800322411 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 63065893 1250 63064643 63064699
    0x212040608010b0307020c0306010906030606140604030201111504030504091409030904020f0d05010e160e01020604060b0409020d061a0607020f04090503132709050703030f020705040e010605 84
    0x1c0700e40d4280d01c0c02803443c2455000a11920840c003d20302000465a414130100f8002c100c00700300820075600310f00f4031074211032481c1d0201002468280d40032459032508400e0310100c83d0242041a40740200b401e541d4209a030309041080c0a050400802c0109a004000b92041c2c41c15144208100041c0c3c0c8841050480c0596240889500c1400782c001c492902e5001864200d100310b9002e403c200e9072a0104041e94002c1c0c1080f950051040108500c555a622003030b01600c40b01d00d0300d298524140301c0041e4442d20080c0000e0301e0540c5801a01005d510780b0303041488072aa000e4080c400303a0b1100e08198000b000d02404032a1b0303075029070884505601d002001c0c0c94846400500c2c031910072084204000043c000d4110482c0e1500091051010001402188400601c0b501074000c0d01d150588079205c001401e841d03d50143d0900d010048000303e400050000140e95050508408980000758242c0c03424400d90301c0300c0d0b41300c0d082c5140c0e214242c0043d04040102d41042d00d0107181482064440e46145c14000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 63067143 1250 63065893 63065897
    0x41203050405070308131802030105011106040b060103090809100e0a0f051305150a08070302090604050123041d01140105120a12090b0a08090d090513050603120a090602120406 77
    0x50f01800800c40f40b02c0100300c81c80d00c0081c1242c0c11650342c06814007402d07400e001507a06030782c040010005941c0040328511201d80280141c070180c03400e0307501c26281c00d0f0043c02007810542d55414400c200300c4030800b01e80d4a000005e0114044945074034005040038142c0000718000d0300a403100084049540c503d8200761a00200b40440000910940b84000c100c01051030018a1060464074060b071903550307650b806801d501001c0e10070a03066005006001c54041d00c034501030b520f008010401d0f240352201840d9050b50803800c05049000d40000600600a07034208a40b102944982992003500158800c034040001c000410496a99540810251072048410744074a9004817540301e000401d03003a8000a50383d010304107500d4654850302d40e880703150807110f24a4080303034070001130205240b42001b06022046061803c0c2c07010504180100b01d510320b42c1003481720155150f03008204595024056483d00055110f0f081c0d45400180030b004050404510820015001d20090420070891510440302521419 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 63068393 1250 63067143 63067153
    0x30612010e0a0209041a0907080d020615010c06060506040909020f04090809012006070305041a06010905010e0a05060d0506130506010e0d050f010603030201150605160201081801050103030206041203050405 90
    0x50f0244541a0b90003002102d00b6500320700040e540910496480c0d0041c44d03660010824181890702e018500a0040061003c1d5486142000a001181003815025250030318014080c01c2c02d500e0f06801402c51030708656800398000c200802d0551003a40b201142e80c4c000c40d180483c8262600601c01250200300300602845410410482554007540300749040e0820342000044100d40c020800d410810300362091400a900d5409001c01d000700c1001101c40400405524109420040006400c41c0c1043c8210742c10b010100c0d1115140c2d545080100c40149800740c4420b80c1c0f00000720001000384002c80306103105001208502080240c81d2007400c0c42541b044c1c60f1030b095074004408200e079005461204071981d104001251a0000c82802540b00651180d000030640782c0c5080ba100f9205449c9030808420003c007445081000b008840071800c0c0d440d020308211100762a501c444800b40c00756414103140c15030800340000101540003d42e076210710b0069819840c40030101c2c00413000d50350160790281c06a0301c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 63069643 1250 63068393 63068413
    0x20339120703020d2d030806120706080a060807120203060c03040305070b040c0503010207060c02060603030a1d01021c0e010201140402030a0303050601051603020114010b0708190203041208030612010e 88
    0x100d802c003c0d00178000d02c1040d50009480f50082d0700c441c070342140300400030303d405030510800d5000200c4a402c1703441100d40c0440500b00e0341580b0764422207071080c00d0070001031001046a04403140c1c0a0005420014290341c48291200b03c80300c14240c440ca0101c0c040c0c0f00d4040082d1440c050542030300d0040f503150351480d2034408503482d01121004042c0c006d444503003042000107640d903424130041008a100d114089640400d40b1806401e01c04020b1085010360070030042c0080059019100c00f05002c104003000d001103400c400101c0c60811076403a060140e07815488010211500035851007100031091f8001d126403c446100f59181d407030240c0c0c0082d0540d000120001c0000d0098000991203001071600d6418404400141c01d4180d81d521010760160750b549640518500b580c0191a014000079102c140ca4528550359070060792249624040889039158001140c1078403c0c400c5400174103040705d0754010b966881c14070090359032095602c41c0c801d07031011800740400b0030103028400f00e0004920140a10701c41c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 63070893 1250 63069643 63069649
    0x3070509010207050405070824010c200a0b0309010605030115060f030b091503070503030708070b07020c090f1501090303050a05070201030f050a0603050d08010f050d02033912070302 80
    0x3050300d80e040d80903420700403665483c0c45c0b041610552907551245c0e1142450346080031604441d50010000418442403603680b40d0300403602c004403a0780041c01203a4004050320050380b51003001162a80916618400600f5100d10401380d4015280c0038001c00249581c3c00030507080741d0040742e0419004482020410101e40940c07540803d07030728141000b0480040000002d48458000c4454070201e090102c034002ea107080400110001c1c003410f030004c504d447d603c0e440d1120140100312000701004501000a00128400d000105074000b005e8038280d81410706d900c041c11005401c440102e00c124107900b00d03003070541c850002c40d02284c2d016291a440c0c46584d0000300c0301a1300030f110690525848565000d001030f514858240b00701c2f07882500084a50551500e541003564810f0312304200107810005100305d45000404030b080b034000303c0b58200385032402c2c4040b0f070a22812044420361020a0703070035055880140003404050141501181c40e81d080c0f24000c01080f80e039084800300c0c50707a00c00101480141 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 63072143 1250 63070893 63070897
    0x90f040501020d09120311070b15060c0118060b060a0c030503090102040308070803070905010504030503090603130b09070302090a0c0207120305191809060b0313080412050304051e06030705 83
    0x150180001510f03040040c4072003010b9807003103402100d4440b11040760f51708090b40351250107100300f080243c4500d001055141d070a00c59102030f142c440e600c0c0d001c6149036203642c3c4440885511a88180085c401040000c8902c1200c10312410290740d414105020180315103081c03130441e5181d010903124a1400c01032620101d4032900001c0090340690343c00c000200100750703000c01602c0c1d1140308001c05503907464401c0b801004440c83d64480360500c00d0501043c000242c01000b9a0b000610075111075407a50368800441009070300352140980b0650b1181d00307200754160301013000f1060782d00a44040c05c45883e158120000c40f00050240b03401a0003941c1c00f84050409000325151300b60092405030b040003140743d648d80500104151107008520123542e05904405544c04a200400400d802000b00a26244100b400b51000818002c1da170034201010300c003000026000d1b10041d04000d50f0502401e0210715005d5565403240c02100c1c8a00c811601c404034030f20002d5a03509020303101808a03400c5440d581c00590703183d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 63073393 1250 63072143 63072151
    0x3070804021c0c170a0507120c050d060b030106060806030d110307081c060602031c09020a0806070906030b04150501050a050d020a05030105040c020a0c0b0904020702030a0305070b0a060302090f 85
    0x1054086036003000c0006242d0b10b203038441c09048034000ea9407429100e800108000f101c86240d50300302640301d4001c2031000c6004000c603400e42004c0d4443c201a07190000d070340c4440e40c00c8240d12031002c4411800f070145079400000719080503402041126100c1e4000c0e200ca9500b210000e80c0b40c1d01855410300c00e076100702c02c403850540c0001c00316414105665180d80503500034426050b0075299070005810b600940e4010100103001c00e0014529004580300c4490051900151400090707848600810441d140c030600003005045190580d111402c1161008000c00c1c00c0348191800a4140841100d9030301d454410a82c820141c41f404040d200d10b050015101130704844180f1061002c240249442050300e40002e00d050301180d5105941c032760401c0104011602c4044800341194000800000001c1030088040140c4072000e620301e465070740b64000140030340310720903000750076004840801c410160440040c3c030510740701e041c9241d095074403c020030086940d140b01c040d41c0000c02c44040307204829404286504 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 63074643 1250 63073393 63073399
    0x81801030603021302030f0c03010b0406082703030907060e060d0b130615120c021f02070206040308030f0112050c01261f061b140a1a010801050f010b0307080402 71
    0x2a03070382c80d000074000c19151486286038035000410004181036101580f54407107914503459041d54104000ca1002d40100c0c041e0500b40310090340443d06041000b02c5207825102c440038041f54403840344903e03581360f401c1921181054402c401c00420500c1c0504000400114090096070920203035008180c0030305201d074101c50f044150800407206084050013075202078064103442030001036488000412003070511500824051411000304c440685c0400c0c80e4112120101d80b5020b541c10400c1c0a42c000c0c0b0074144000c0d030004000400208110340c080146100c2e103c94604819507a076100f15446420b070040d2001000ca170001305e0101d201c1d41c0210300c805143d50340d501e040c0c3c030884040b0303040880024042e6000c1114400d981c2950000e14110641000a00b003285440c0c008201c059000103c0001c074a94010b0480138a032080b0515010200070315094990481446400b03415030803000c0e400000213004244955090400148511a104007494100c964884c400c0d80707036590b11081141c00343c078094000c80e4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 63075893 1250 63074643 63074651
    0x6020307030e131805010c0206061f08090c030f0106080d0c0f030c0c030609050318040c090e0c0d050c180103020403030c0308130506070201020c0c04050c0703050f0408070609140d08180103 83
    0x40d0703c52120b80000484c0e21900c00050150908030020b49085c1303008081d144605500e200d02000b0508191007000405414100002d13107840d000c101504141c90707a03554980500ca003084002103010150040021108404181c2c0e0a10800389000c0300ca0421000014220902c2c210f05072001a1080b080702c4c3c50b50b401558507058858a0703681d190203072250300800b522182d201242c0c070030701400c1a402c036005041086130200003402c1c2d0b241000e005c1c03d50030320400b12800e08243c0010401d0007400e04403104099420003c00441c40c040100042e642c2010a5468407890305a490004650084c4211003c1c0d94160325044000c000641c0d0403a034140d8000e08140303143e40c0e40e05203000000c80c2044281d000f1b01d016000907880c0c04106c80d4a0307142c00b0848085611981c10101031240d548148001c841c44150103107085c6540b941036a54100241c4a42e034001000da10940400284c9250300071841030503a04030403140ba1400b059079080001164150f2000745c03050200300300d003e1021212001401e00c015041c10049 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 63077143 1250 63075893 63075911
    0x1020708030f090a050f151b030f120703051005040c11011508061e01090506010c060e1b03160303050903070f0f030210050324040b0d0602040302040e0a210306180c0906020307030e13 80
    0x600b16007041d030294040001c08900c2802100bc0251840d6110300c1918003042149801034000408500602c60a4001d5585e0a28042c00758460401010000b40b0000240100031080b03907182c00800861103100305038014507010411508002881c0075240052221903040c99007008005c5000f00400f07000d49040c0181b40407104009000c1e03000e03020000071701402421040790404c3c915807550403048521351103504840048002000418042c2c0103881d050702d00161540f01c501b0120303141c0a401d800004100c5130813480084c217299420503681c20f9a10a81f80140d0040c1e080106403500d000c166000c440320340c21210160700e591403131000d4104002e0006d001094000b5800e02260b190542e1a2060301c110307800180c207000b94202801040410466007004020340c1c0c520f41c0f21a02c0442c0c8402251800340041c00007030271420300c01e4000d040501113400d02c107094081441881c42c000c0c10015250404150015400581a0300110554034070b550036442e44000c20004104102178000314203180791407150354000103 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 63078393 1250 63077143 63077197
    0x10f0c140c031009050a0b0a0e030301031410020a17070201060902041e050a0803030109020f0405120109020109060e062b150e060a030201050706050601020708030f090a050f15 77
    0x4214101401010703000c001c0102040c141802584040400030701d040180c00c40000e0300014829003426000310310032219486003600f40c00540f14447d20700860b407001200200a20442d444041c02c452501011201c1000c0280703600b4082c1d00401c036100c0e000c034032701002c0d54800c034080c02c3d0072a41c40182840005107c0307440d001e03841c04030380054000380400c03140d801c00320391507105a0200304040d0100b00ca5802e50603141000c01c42d5280f105004030800d054002c50b0b00c00102481d002510003401000b400c400c080c6080f242420700911219000703900048031041c2c001032041c001c01d0942d00007800541014170b8011441302510b105208038070721980c0300002001e0585101c0b064802c0204130500c1c03007a5501031510348181c0840c101c1d8042d00041c40742c929100304200507030304078085604072903004c48007085030f60341ca40050707050529544c00050240400030740c2000d02e0340100001c10b81e92100701c51400d030007038444041c0705201c60211450f80c0c2102c60016203603e079490100203480300f19211149030303042c24540f2250b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 63079643 1250 63078393 63078413
    0x6120a11130317040807180b060a050702010e090103030e040903020f07031a1006080103031d0a0308032403030306060705120a09060801121101050a050f12041202061005010f0c 77
    0xa00d5004601c008824003c02020904000115603901000c41c141810b04088684400c0700d88101c0c00b0f0030410546d01c5941d446660084001c1880040800d0788400340d035030002d0420f07403200303400300d00160361000460309500d82403440c0341c180c0390943d0b207071005005040d0510004003105034042d020b43c0b140c1c070503c4032181c40800070b000107544503404882c0c0e0140b40400c0c031119400064135411800e075282034141300d45079001710aa81182d0705482e06800e125070007003040c0884010012495000824004e01209109031100194090b203940100385141800030f440400e00d0f851480300f440c0c1e158008002207022484d002c1c02030841c1c91301800c01d5036600107802c042800710350320000860001c00c6015000f08107464000e904540142032520001d40703098801e41e1018102c2492098560500c0b00202c0c0c5442c060744614140c61007861280302e415a038a043c0d240d00c203410300f0103d400701c0b1201105190025040c0c80032444034060801614003c0940d41098015101080501000e8040111110180000c03c2109007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 63080893 1250 63079643 63079657
    0x20304060c080609161407060e0a0c0f03050a23030a080f01050f03030a1202130303030b090106030204061d01142a16212901050a0506120a11 62
    0x200090300c0c028001d01030300c184402082d40c0d1082c040c0c0e50410902c3c011190460740014400d24100843e0021160380f2546809110b6019041510344a00d6a1020300c000480b044458010304040c03291643e51001520725a00d035000091541e000080020002043e4020103019555403140c90ba0020b03840904003444c641010011400040b010301c2889130a54500700d5190241500f40c402c66240102e00002c0395891003030072900d41c00c118000b2000a1003500c1c03503042c1c81030400d49030f0410402c180d1700c0c00d0041c0680f2655000030711900080000054460180c401c9900700d03201d584034040082040b01a545000d40307400c0116041c000c458051003254000e410040024822020028050701c041c04410000c007200c45441510540c000b501400030100000c036544d08440d44011032045100040c0240400f0403d4030000404801e02c001000302004400c11107049408403500b40e01e5002e070f98a000b0800390100921816030020020040412501703840780b8615400800070b5070101e400780e00381e0700040c02070388018 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 63082143 1250 63080893 63080903
    0x1303060c1715060306060a0c1205070b0c1204020d060e070b0c0d09060203090d02040e03030a02030f100f030b0c16050d110606031507090801020703080a0605060703020a06020d0b0301020304 83
    0x7501425800203500380d0359401406001c0d00041060404012a18510011700305911601001c5191000d0920412040311040d501c41401c1ca840d108020010340a0380121800f00c4625400e140021440004407054818150b85c00f507104515844039001e12200d480780c0c480642e4140d8841c007403410604000c104020040030500140d82c0d80300c1c41e8584a90404002d41020760811541c210300b040013580c0001690340840c1d0071070304402403181134400078005205008544001e40404002c000e00807a07954051445560750300b203800d0084d503864040d4100d801ca240241c0301d000a040d0414000301c0c4403860100e80c070a0420f40298600f450902030b03410f038003c00702d104503104e03030011002c3c070101544041c00141c0803964500070040350410300002a110507059400320804d8040d04000303a515441200818001d1031240000c6542b00307254200180303112012621918903d0400c2400509401c1400c203c1d0703281a0943c1c0940160405a0b5513040654800001a845682c586c0b6814116560038030007540514400e0f = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 63083393 1250 63082143 63082157
    0x31b060c0504180b0a05040b18011202090f0403080103030f0e12010f0f11040b0706020405060f0309010c0903080d0b032d010b0904050d08040204150e270c061303060c 73
    0x4941801e940082c07500d1401c0060030990a1340e82ca48982c4580700c1950412640861180d10ba0008900d11200c4581861007104060000280001ca2001c40e050080d009035945001d0b56140118036090410554004000030804c000400101e84100701d401540091890b00c8090a100e0400141d101e0344600c41011079655a54540d0301031403460300c039000904481090501601c4104002c0140074042c03881900f1000200040000800c0320540c1100c0c00b8000c0140059124204599240126042111038089641ca01764414500714055009641107907070040e101382c50a000400700b0000b81291040c00341d014881d420740381c51548000407200e03483c24030151005000c001c440c501d01d805d489040c41080e020b000008240b0000c02d07004191020187d0107420042900d4035a403000c50001c0003c000d174200c04044e00c0e03101040207000180158000e400e803840c3d000307104550324204070001c1c080000d5a40290b00c10181c4614500707190000c1e18500d60100c0e24922215601d8413136905031902100818006206 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 63084643 1250 63083393 63083399
    0x20606030f0105060607060207050f15010e010501021504031808060115090e070f08040510050c0301140312190c050601030632130602070515010503100b030604031b060c0504 76
    0xc204503101d22041c0340003030005050802c0071850600c14424007a018940015041081c028108800c030405001c00c8220b8200c4006c1412104141c0720030b001e00f03c0407880c10000001c15610015071002c5d00310000311a00e11076192a90141c3d40b00c001e01c9045150b071040108005107400060140500070405100c50600004590000520780e134556044400c04e1074035203050140f2030354000d0a4165089050400706071a882d070303040491a148608201082540c1401c0800100c02000720185040322096084400e2800348030701055240c102c60030080446860a00c084070420008018880321030f0158240010012202d40390103003441d009030403d80341c160301c4440031400013182001c50803100ea1030400c00f0071034983d2114102e03100f200140c49019016003002d000411710a0355811600819070220131109415400c4414080312402441400c1c42400b0b81800c495082500340281181002c00170301801150340d8643c0c05a81c0018246041ea0802c045100740c80000344071403089050062164450303503142c0e03123 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 63085893 1250 63084643 63084649
    0x12030c0207061b080c0709060311010906020c0d08030601030902040504050601080c0105030103031d0105160b090613080708180d0b0f010b18041e0c03020301030c0504090203100207110a0303020606 86
    0x107030380c1e00160030081c44286001000e208010a40c485a90052429a986120150322440d05041d030b00131b0f01d00e803172500c100042001240c80b0007110a0400ba2250707034440381da0704400d0b40c440113400c0195400c028048004000504031100a6074000b80504002503141180d030085402c03504111f408882d240c2c0848010700c015a0200140200d1407070903c0c01c140303158111381d00140382140c41055602002c0c10f181d9180714984c000d0041d81d41d41c8071304d0b10000100041c507007005445a10140d501100901a06000c22710745d0701084584024590480412841d1407da581d45421a1f8000b40100140200c4440d9041095443c1d841d180c24140c0104004141030a1010400107045810b07031242d42802c004111030b040700746024031041ca82c800200e50000b42da4040c600400403c20807040300a0780c0c6031601900101c0c007900342e4060340c1a2406040040580368461040c401254402100a540340c1e00100f041c82c082c0025400404066200308101d2050f56000e10200311880e41039041100960011801c1103080c4c1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 63087143 1250 63085893 63085903
    0x2190c15020c030d0203041a0f0415060515030405030906040806011508130b13120f0806061305060708090d031707090311100504030c0801050105121c031812030c02 72
    0x91a015030031450090b101007015580c1c0314044c0031004c0707581c01000007420b00441c4080e040740b10170041ca0380d01140ca0610042ca800440031201290661112449406075003240d109400950340c0281814190f1164025400502c3c0c00c01071040f10644410020580a07890b010050b100410790fa0300280390700d50401148111903144503041e030003089414000c1005c0c80003103891100c503141c4c001c082c4500a48414200e41d07802c1d03801c0c800190018010000c0c40d00c2c2c20b6404009103103a840c060f82c604aa944402080006900c644041c2c07280ca8030303a8140c1407215107040401800074500c1916a00e1400c1c6011002c911086880e003801c0e000b0445040510031038400242c4850b41c03295032450000d11081c1160395070f00258184000c2c050158240300300300401d9901030000c84024540100403254826076441c0e1150280c5004d0243d1405001007401d00040c00303000060340c4c0c2c622410110015201017103103904074001d11404960070901c1280074007100200c0e510780c24a80400a659034045000da0031002c0203031501e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 63088393 1250 63087143 63087173
    0x801060b07050d050f04090203040807060e060a0c02150c030c0d06092c06010b0a05090315090d09030803070e040609020d090309050d08070807080705061504050c09010f0e030102190c 80
    0x200508200c45d014550840040354145d5918070001030316a21141016000b07030040140041145251801058856200081582c400c4545540a116981607060100d880300c805020400c1c80900181c0070501501d500c601031503000d0742018a00341810200c440b5002940c140341d02c0030700401d542c2c00e240004030650300c0c54901080d04100303804c02c41841c9600046d996100501c240c60041c80081686103556200304100d814107a401000c507041e901680c1018805000f00350b60b5190184122200340c20038a000f2904030003220b42203003a081c11a65400f40c290b440e291040506039101d41e8849000c40e401c80c4ca031000d0400e110341d400b00050244014680941020f41c13507004244a2203203102c0040000c0c900c0c00c100c8112590020744951624000d10b01180607004101000340103004000070081e40800303401807903040080c05c4070180b10359164140c1450070391059180490004440c8241c2d41c0c1d4280c05000e44801c166000f07000180390030b441e0380700e0406000c1c400b4072800018105440400c14050555090080 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 63089643 1250 63088393 63088397
    0x2a0f020c0603060102100504110409050102041809080d0e0a0807050d021b03030d0f1d030d0b040504030801030b0907030c090b04060f06090303200303010303080402041805071802040801060b07050d 86
    0x140d0f080060010390b41d07012480c0140d40094858000400304200c01081c640a0381010b0b1091144d82d04901d4035034041d401c0b034000d0727800d03501040c240d0481121450003204181c07508003e010b450480d40c1581000a13185254004a40b40300d486010710004034044020540d00780a0b2000d0b00318280000700003420003d40e1240d907400900710943d81415954084125a4103540b140030020780c480ca01e079490350180c96030b1390405ca26800507442c801d440200201c02000102c142d01070030400b90120304208003c90b9415a00640068942401800050303809041150040c0d800d10403500815542c0c2d98010905220780c02c036030000781c1c40780c18808442c109406004c3c06400c482c1080c5452504101004200c1e011a100160400c0700d00805000c0c440e2906844c1400e8030344507000e42c0e66070341e124100903007041002e5170100d020700d00d80b104201d04401686c983d800115030200240001900d07221403a2842050074402040850b0308000020b20300000b403050200420a4411700c07603c41280d41801070030115200c41d8807003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 63090893 1250 63089643 63089647
    0x80a0903140c0a060f020109021905090127020903100f06080f0604050d0c080409090309050f060a020a02010e040b030708250f0504110904140109051006020309042a0f020c06 76
    0x20242d4480c070f682c8043c0c40c858502280c0c50001c2c9441207015001100010350880c104558800f141640f14a04500352a41a01d0030842a66a80c02e401141038004d600d141c04070030210301081d070700d00740c0750000d000300540102207d1403c600c0d95600c1049030144e001016078280d60b0b50042003440f8090105101c0885003101401d45403409869464586400101190410031203c2c3e0034010003c2450541d4044d210300c2d1020032640c01d1702c0c0b8002d002c5d0781d003d025051040c2c58034070003076080340341c80011505500400d82c040c0412401949c0151a00421400300b80c0d031040c3c0303d0762600b070941c408214140050280c080101511010300010f003000c07d003400000b03000c15041030018000b88440e1030a013021103005940004180c0b0101c00700444a024010640d503005041009003444141007166990680c0c5000400300035545130301c080c40d217102040f4415840507820a2110a421f0319055101034a07100130100c281c611000c1c80240f0126600340e0003c00b03004107101d040705544051b8104022041000166070f07542c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 63092143 1250 63090893 63090913
    0x90212010c08040f0c080a0602040f050f0f040504080c010c1d01020303010e0c030603070f0b07030f0e0a170102131806050d020105030609091f0911030303060906060304050307080a090314 82
    0x420140c00104094101c001301d685000800049411030001080000306446201c845468140302a60040c81101e40140c1c2d265004240c0e4078108400341c18181d0010705080122040c2d10a2201901c4010001d840a610910200807403440a0181c08460b84072503658541842021074440440c03007002114a045600901c01800295600003519400598072051161039554280c0024600300342074111070810004e002e0300240c0b050400e40584452846515402c4d43c41c1a16641103405c1c0085211050340310000d0001040042c0c5c01d5440050148000000903240041d00071203d411106994000e0502e00c00c40c0390303c6180c1041c103200d044e0103008210703103000c1c0303509141d00001c04501000e400c5a01c90f44c010301c0410f0001408001d118120310100d2261020165503030303c000b00800c00001c080e9004134040700392400900d8081b00701c912641e002455400142c859006106154000034421111403104004607800f10f44402c0242680b5021695114020303401c500c0d1030710040111094654071544000040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 63093393 1250 63092143 63092147
    0xa050a18080606010c15090f020f0d050303010b092d1f140903031306050a090e0105031c020a0803010902070c09140402010f0306050604090e0d020d090302010f0e090a090212010c 78
    0x2080e00044240380c9017180b0115820241d03086003290403007000c1c40d89402612000c0158905031350262074003c031942807840ca580024400440c0c4800d00050682d0000c00050099143d01c0f400345c00c0c0c0c4800940a0f04168806507600c4e5a8031048816103030300c641d00c1c0e0303502c7e00c2c0c103140c00c144020040500010007100801d25140180c09104417140d002c4501a002c9a50b0040c1d031020401ea0b0100b0b0381103044044110b0f0b584c074019007250310600088000403520f80000c44d80c08800d8401d03504807100a001840740303448880c1301d08034003208240c40c10110701a800c00c840c00300b86003902460203008210300050b5501100d00c3e003081c56000c10740c0407030292410b0070080001d100622013181d601caa02806c3c500320700841c1d0f020490007040310f0340103564440300101d0081104c4110350300c03001d1101c6260048544060210f0b601740e0380c50615040d403000080381c80e80706200551007108124100040d80c06d207000d050215800054103200100c402e81981541c58500f1011341c54a080c0031484d01425400800200c2408140 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 63094643 1250 63093393 63093403
    0x51009150905220206030a14040311010509030408070b07080f1c1406030a03030b040209030a0311190519032a0b01142d030a080c01110f071e06020a050a1808 69
    0x1a2040c45c000c000030301c0190640d00100110929241d4403281d07481c09181c0a80304800074402d0000d50340ca058002a030048000044034140d80b000c0d4018035401d0f02d010004c1c512a400940121501d01060101a1030440c1000181c43e08540040181f49001410348400c8115000c403e405900700c441d107400e1100359140031600c0d6070029003518022032909181d4001c54044d1040f11a8240c15200301c070388000625601620190aa000b610183c4103004880741c4c003480700d8640010003403d560890342c1d804184000422143c007244e880b900700481d003400300c81c036184003400d500d215082001740c05502c4101082103507071080d405031190030000065480010007040e000c0b504582d0f00c0340302c11240300c42d40804004405800d500080c0050448880e2607103890042410b07002015550041d608004980680c3c040b400280c4200c2e12420048a04004c000d2712003403444240103c0004102403492000004038410340020070020215898040e1796581d134520050110604034002c3d8241070015405000012011030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 63095893 1250 63094643 63094711
    0x10e09060a02121503011b120e03030601051207030605041a0321040b0705030403020a14090a050103120e01030b09040615080106050303070204020f0f04090c080108010905060a051009150905 83
    0x1134180e03043e54510003c60300500030701008982030a00b40c90101c920907444001c00c403082004400c14032092155580245c0d83c2e0100f51086808514148071340148080461540d035440b01c203520300422002d6982000c1030403180801c03024400c104002c8400010703424104025000c1c842c03048003c00266078031600c00065800349001d103440c545000200c00052020810549000c0c40d002000881e0030355071100d04000428007003a01c035010743d561000058500440f48038440c100d130741203240c6410b05001920708464281d425000581410f90301e044103500791300d0302c0301315a02c10b40c03050100040d42e9103c0b01c2c3c00140041c4580c440c081580c10314200784110b480110580d00c074140e040d00c0141e01d80181d000c03801c101d4010b4a4401c80750250202e80081d00e03c0241d0401d075400809503d500c8101c0e43c841d0202400e8503812080600070b6442580860300101407075100a0344000624480c0310025101c00191003036500403840810304116001040c0400c84176481400c1e045945410480d07282d075110100c420308001c11380 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 63097143 1250 63095893 63095911
    0x605031b13030b09030c0102190e01090f0e040c0819110d020d0807080909040606241e05160803040b0f040302060103030f0c0f030309150e07030204020918010e09060a0212 75
    0x2001113200c0c10b100300150389150045400175911a42402e09111907031081c03a154800080d56180c41c2e2400d035014065440984001d07414818006050803042101d04002801c201c859501c1c003480003813082c0c003d0180105041d000c03104001203811034103140c040078403801c0c2c02c14440e101c61042c03180141e490704583d040441e8008041c503141e100e06e04005000780504c9911a4100641204000800c50154040000ea46032000c1e011008142c41100c080fa1040b000524000b16000e0400c29402140440d03c503905001c191412a25061031035038801e40c94691103a080b1645200070042c4000c00c120015803550040e0408811303210340c174150314003d40d0350206120280078080139220040c0e02a10400c0300100d03180d08016000c04400b15864001d0040214100548410f200030105105045590090f001c0b8268084000c100c0c250440d02000006c0d800b20481943c001000a6681507400107003045a0080502007170b021403030b00e03002c5c43c01030800c107000f001510030500c1001001120b90742c03030141c0c8d504103c0b00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 63098393 1250 63097143 63097163
    0x20a0809010e0d081003020414010906080105190b030705041503050f030307021507090806070807021c051801050403170306010f02010e030a03051e0f06010e0f0310240605031b1303 79
    0x1503250045c10031002d400c082c2d003040c240510540741e0441102054101c5002a408001b000c0c1d45105980c2207500603120707030748503101c218101c404c00300168000321076129008040d500c1d4a541c0d000054222044c5200024885084060410030300000340b01c80700ca0a840140039601d90b15091400030b4a03401034043c00340080203528003060703c89109a040101522400b400c8404a04200c103002d07010b80e90881d044c60040c0300700750000d08501e80d80050101c000b50f02c0d80340c0c03e08261040703c3e922400305601c540356041003820700c00003003c00d100e070701030700c0e60440c0711018542c0e2810424001440e841c131610b18101560b0403c4403050f00034000100702d804004443c82c000a0703588900245140000d0382940396400d01200304240200d0203030f0b98210300e025850980306e00710f05041306820b0042002504100541c1900304454400000c0b1082c0c1014204200040c651240518481040604598103400c0a0000380020081010b16140c03000d100000e1001081740c01d05000c0c04040481405029010003003600c0c2e08 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 63099643 1250 63098393 63098401
    0x27091f0234060207030206160c0b010324020706020931050406111207320313081201050301060906120f051e01090b13080a0c0213050703020a0809010e0d08 68
    0x85480201d030703a41d101d10199554143c50500070341e10801a5a152408524010406a0140500940c00720554454804c4000b40e1854540241c290f419007002c034103107035201000340c52868440c0300414940740324080050300c1c5d003c20804d00020480d4418071001040c500306000840c40c05140a1090310104c840002c03600d030341d40d4a007444c0075040b21200f258403113401003108101c0424914075244a88165501c40d042d84080c040200322403d11109887c0b41c2040b40c0c4452540458100015070303001c01c01d17031445401000750380d640744d02a9000c03401c4410043c81d0107005102e01d00c2e0a0140b04010514404103102c41c17828207011841c0c0400c6144010300ea1106501810304100007404842d40d590410021240c1140500612030f01a000e075010490f085c910b000300040c42a41004404050181c0003140e480c10000c0300201941da0f4004503100f43d900c450b001e036003551001c105004a078411903c1da900541c9441e580a409001606c01030005400c1e641444845404154000b0745034008402524004070543c0b1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 63100893 1250 63099643 63099727
    0x90e0c040807031e2301110405100c0c080a05030c0105010902071707050c040e0106171b15070206041805100501020c040b0103020c0709060501081003020102070527091f02 75
    0x10441d1402403424402030710003411748142c10801c1080c8003104000707000c1c00c010140c40301c40c14402c0e80940c540c0003d4141040d82158425080c982486204114500c500d54480000300d2034120280402ca481c0e40c8005400078184100780200e41c01007131451015410075a0759940d10500c0c00030520741981c0034002189070024000c08100c0c40404040c081c00c01c100c00c108200c0301c2c034041c011601900900f4600049031040399500000da140c0040340d20707803980728000ca64400b007210b210241c0b0b181d00c1c2140010300c040e102680e65000200024580451500104518500484143ca100030405062454061420404d690b004180d100041600710342c0000c14240010050703009000b100c4014074684600c100220380300c40c46510480641e40c007626112819640e8075071103031440449000c02401a00001d1041180c2d041001d840403100b200c01070b000d0f1503015924202070951400310f9007903105500c60004500703030001c100c111046103200d2003019132411080c032480d02441c40030f1554110320b80348400b600000b00300b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 63102143 1250 63100893 63100943
    0x305040603020a0e130f0c05181c060c03020307031404022107180b01020c0a0f0603051e040c0303120903020303010e040c0b0f03070e04020a1205040804080d090e0c04080703 76
    0x640043c05c0404090030440c051006100c62003c07440c00900c0c0c00c0e00e10421074054026036a0140115009115104a8100b44003c0c08030031041d04009000060709440010b031a03000d00031742920f0664005840e45000d150040c10b860303c16549a00d0031107114144005622424510b56624071405125505440b10f400030300c6c80c01c038803540104036954074080329002d107202c02e41240182200076401c072040b280c1507900704002e400280c85513060500c0007400420005000350015a40488560405c1d46440c050100d0710902e0071040b24125030b4082c41a07024001c154024000910140da46d0038104401c000760398020350340b440107010f251106011030000600700001c440090f000b4281081c02a51140300652a2814640040e140382022450311550143c06050501c240d0b564071519982d40004040704061900040c00050029900b1f11000c010114048000300812a00014196035002d41c07189400d001061601c005401d855600600700010803150b400003c1c54029290030100038080300a290304a0261a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 63103393 1250 63102143 63102167
    0x509030306091512070315050105010f140d1112360a0804030302030a0905240904060504020a0504030201110a0b0f19050c0403030e04090b071103041701051806040305040603020a 78
    0x248850140c13085003501007420021284294900c04004141c80401c1060311070900510303000462744c1c02c10f010349038420003181c44902840c440e0507180209210201c1709841c808120100300781d00004e12890f0362001c22600e142d2103051020308059a82e0044031240e0460b44243c0d4000008030110054408100140002c0500581c00480e0784c1e030341d613030b00e14001e91a80c00c0b070815280803032640d001c00155800d003810703501c80c064400c5007401c0722401c0c8040d0302200c5801036802a90070555a01c000b00e960307199440104030210140d1a0300c1e413510700d1403000602c034441c800851007c0c1d401c8090880d0000d5011000c80c2d4010300000c0320100c00b179440c00700c10703001800640c4080f11014140404c0c42601042c1e10007c2c010389000e99200c1138045944402c0c00156203084c42c2c01061717110b9080002d820f240c450640150701038280c20569182a5994030300900480b2140c10310f4034039942d030750f0901501d6901c185611030b03d003030044007509051425441c050308a000340c0c42980141078002564000b054070070103402c0e9074 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 63104643 1250 63103393 63103399
    0x1d211810030902030f03090307090c0e031209041a090c03040201050c0102040e060a0b0a02060a0e0f060108010606111212040206070b040302060702060702070f03110a080303010605070c060305090303060915 90
    0x480da8600d004000d40401d8009a000b07008070301915071501c4012088a100c0c2e80e0180c0100001c5143c040000300a120b5240003900b00101b0300703203195455800780510b6070003132880c000450703e034100903080108580002c40c0390b030782072000c00c0c05445451701c40e8442140e110611006003901c942d1a40010b031001d01c510141c15156520028010603850b410b414040d0083c00b0658440b4406d0352200c2001c00c00e4840c4900c5500940e103c4c00c0024000d0110750011002109420b041c1e90102d400040b9841c50007400fa0001c6566945450060142a2f4050302c40f0340f05000c410001c1c0f03009949030b40c540b40c25210380f4001100d001e0101c030000c1c00b5034486408485034240e0080c0201800c0c506410025103400003558108014080d00c0041000280300007030341c1e81511698811000c50901e95945e884104070582c008640109003450006101081070020314001d040503164182d44a6041c0340010800109070040c4042c140b030300040c0680341d5000829030340d2080c0d042c0d4120006499004007443c582c000d0900d4240c1c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 63105893 1250 63104643 63104659
    0x10050a110309060709151e0210020d05090c0406050a060e011b14010b090907060c1b06020a03030b0604060804200a060314060f0906090a02120106031d2118 68
    0x40742c1c880010301e00d1280b15240da4a00761203480d040c0e5180ca4100c0c022110000541d0120390780760500c8040786007a241c1c14030740121081800c1080c88607041e42c12064003080041d45d9070013001003180003482201000401110108030307050510740043d2515425024690401c0012a500480c0d64005c1c00d2034105030800c1c00159800d200980b40145e030f552903141c138016455080c458802858140486254003074004100a08121410214119000c5141d00d00580f183e0424542007150031803400c0c5003034060021980908a20b0501e0b0901034141e445c000d00c034a00402d410042003002d9030380884146d0700158041c00c89400035085000c1070340d0f100d0034442444d601c4121420001240c030b4041d8000144012030b10802c0a43d0b50b02c0d4000c000310304070f40440b03454002050300c0c00a006403802e160308551020000c2c100500301b010703d00d2031814600c026006000429076400c82e20070759031142c42d20140c80103048801024176000c40c1c0ba01035401d806548040380724440118541c4039034111400c80e520b4560014050113 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 63107143 1250 63105893 63105901
    0x2010917210105030d121401030309080706140405091806010e01090f060b0f161e02010305010905130206090111060a0b0a0e0108030901080a09020d0b01060206060102010e10050a1103 80
    0x10440d41d00501440403400c540324440503190341d2050032207048520042c054000344448030342c295032903102282103c5100d56200c03019110003043c000c1c1640614025aa0907151608080d0300034a072104641080d4184480c20143c6281c032070b162412138003078501c107407828001522001800412105049401c43d606d029000000c5070010051620a0484400c110140507881002e0140400c640b80d0b03008515644004025103184410401c2c02001f04940c1c0f07050300c00300e04c80c440c2c0710780c100103a20000301100f01d86010b41e40e2040d90b0f850b00031103016061410f002c0101d0b04050b04502c00c50008804024000d9001080008507030f0f006041212010f844001034810a1420745032003070090410500c2240b1480c8034074004261044400503250503124000021803600418400544519034020001c41c104c503204c49400d00143c481e40480c03030042e8494103d074200b40d41000000381c200340c001021030341168500006024031440006410018108d9400e000030369496001070040940f00140f103031220010000140 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 63108393 1250 63107143 63107183
    0x5130b01050d0804080a060c08060402070c031205040b030705030403021b1c140f161d0711010204090c05030603061b090607050f070321020a0b0406020306042405040605060a021c020109 81
    0x600040c265030b600d0103402c0d559441040220702a404dc0600990034608040c800210030503d4490201894102641080d6503510303c802c0700d5004a40e40c1c400610013009204c201501000f0140c0a81402c00b05a4000c6a01034082420706854a504500001366042e42c0e800703119003d00f0501c2100190310070b03220745401743c070381d00c6568500307034400312007480c1e05440002080b940e4401b2000c00302003007052412880e100e910049544000d40c1201c20102e5508000016580c20103114007800e0040c951102030316442e0a404150400100411019082d85519618158001c40a04917040800202c400589400301824072521b41510029070b8040c40c810a60b001c410300a179004181600030b181c10383c01c07155015040c0101d03110007018200400e403c09a5002c9800101d240d00603507840071014000080c041c0501031407640c40203503203510500e0795507440f81c10b10403801c160042c49c1c090003041c0d64071450814250700080d6079000c0d20841886401c1e40c03030079282c2054400e40042c0d00c40c90300148003202c158405072503 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 63109643 1250 63108393 63108401
    0x9030213022a0c010e0307060203030612070b03040f02010305180c0613091d06100503060105040e0f0a0b0105030114090604031b05120a080105040c14130e010f03020405130b01050d0804080a06 84
    0xf07640d02103100060001e000d440d00095050030b0350407640c055070540d11103605004481c80303140608400703401841008500c00e10303114090340c452405800340b001e0300c2c0d02600003d41264405040b140070301264075144460001c0010b40e0702c2c442c282c00d03a461542d401c5442100724140c5500e40084501c03904001801403420b48d0b044000300c45202c03038003e50f000c1da102d541002820890f648a0550140c01080041009107003692050340740e07294000c2a42c44030006001d9150400710030701002c603a04000e020041c0943d0a0034032445240340780c40241e940380340c1840382196a5902c8010002010010740c501852802c2c1d68402003060880c2d4020116280360310110784188030750300289940d4000502c518000600c41c41c0900455820384166190451241a900e54024040e4406010181c07684611140055192034003084a030092040603825040c02d400c62042000341c51000c0d0441c102d040201080c007001c2480d07030300c1860468101b2a405120502c003480c005a050080ba4000783e414040d5241c41414480a904 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 63110893 1250 63109643 63109663
    0x50601031e0c081b0105070506190e03030a0e0706020708100e0703080a03020702031009081e160c0905010801050106320a0201090203151b1308120a0f09030213022a 72
    0x100c5600f8400d1132000464090160b0030002d4500c0e4484001310f08030400c000700a03003072002c040300041001c0d03c0e4100740e28a07560023030b1035000001da40c030400107071003480a02080c0040d040610180112500d402e49281d51401142c0560040d00c2e42c803902c02d219803604120700e100a540c0151515190200c039038000d0025080500d0590180c02480103140d0300c0c11040c1700c0d41800d29401a10582400080c1011b00981002c41c0300c1c1c03144081c802c02c00030401030650052405014450346114180b1030804110500340e50301a4806880341e070401e001480384907001013600c410782403e110f0b05080e1a80c8600e0100202030301e040d400401e4000010244c000d5a410f4000000081c000d5007210426003803c43c1a00c2d0a05045421110030304076591400c0704c00484d2001080301d1044144040c0e06582c44020150901010644030744019600299088000d900038028200c0315042e070409401c00ca1841e0045550600260141007004c0c1d40058580c80b614110000e2071007002440e640360b9003012840406a94950718030bc = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 63112143 1250 63110893 63110923
    0x3022a070e130210030903170c0702211c02010b0a23012f0a05061807090b01090b09060d0905070602010b0402070816020105070b0a0203071b050601031e0c08 69
    0x11a94601024200801c43e8040c0c00740350250480c88044004040b4450210100584034000100000c1d003030290368042c0c2c801d074904035500c0002d03104010803001582641001200b0060b140405c0820205464a0459055902910388210054101d004023100b18006500c00e6584601041c900740340c0c09004c0040d60380b800c0d0500b9001c2040015105800000100301c505020904280b0351804050a51440c0b803044904980200220f0756440e0b081100031180a08100410518100c4442080040328018143c0c10f00400034a070032540000c09000c000d00510001780c03400114444c0d030b9140c3d03800700c8070040050041001945000e2502e01d88031a024800d89005600b003003c00c105a103024802c032820168000c201c24a04004140c6903503000144000613810f0210911441002c0f504c00025140f02d40c0c00e90000580c1e80c5402c2801610700d003185040c012520f00140000d03400a10001409030540f60041140d0040c0c03141078004e18040d0340c5401c802000480b40600025004400045e07018a0790565 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 63113393 1250 63112143 63112169
    0xa0b19150f090207121202070f0506040203060f0903090d0c0b181f0804150204051801030c0611030a0e03030c010c02030301080c04110301060c0809120f0c0102030f0a03022a07 77
    0x940702c0206a002d69100504041281848549514081c20311381c1c4820301188805801c0c80015240c0319132858911105450356042907082108500d81800240e4ac01b41c2e8140d000446424688902c82e964000c19a6460082c0101c1d0309890500c454191200001c12154034201d41d128003056414000e520350699041c010b101d0080c10398105006030000d0700701040507a8441c1c2007941c50b51103039030145d59000092403216900b0000480c4d961280c42e280c0d01218041d50300300c511945546000540c419047d4008420092502840d011440c000b0007282d00c541c10f0361404500c801c5e0041d000905521074101c0d40d2042d50301c0c20200d003024a070040050746c121801c080540b2092a0020f043c881130322412250054206c1041005001d018052a00250b600c1c3c043c5522a0074911010003040800003400b00c081c40c103612410042e04402401c00c03807000c0c0c401d401e102a5040c801881c24005940c000c0407484c60a1640216019001200603419002c500742c692420002704450100c0c26519180305014030150380c10300d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 63114643 1250 63113393 63113399
    0xf060507050d0507090b0a050d020702040204031a070212180a08030c0f0f0d0f08092422050d0f0509040203010308130b070b01150c02040501030b07020d020105090a0b19150f 76
    0xa8045e210883d04d10907445032404200e00411621503114660304104150300307110500168446101410207103104181c68580310072160417a00064000402600456000301408071400b1382c840181c0305c820f2101501c01d12450341860002e92007052580152445103c04141c146044800060300903070030f5608410348004d420a80c9603035854820320740e00000070031042404410800c2c4101c3c08180d0000c2c8400581e2170700c401510304800d40c4198024500f480f4074201092007404400d10740440400f5400021414690110307a80d4591030311031080420044c000c510106102440c054030071a5517110000703204650320740c1c49240c140c0c01a0040d65040120b82680c58003c40e60340100d41c01c8941090700001c503054180c0c64810301c03030401c0c10707142070301e4082184140c1c08100580303450185d680130314442d0201e101e152a001100a1038900841c0c960411681040c0500c0050b00020410800c0c098000d014130f83c03d590340500809a0006880541031032502d00585410400302d43c010300c5c81514004400f12802542e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 63115893 1250 63114643 63114647
    0x9061a03010b100807051c090b010e07090902130305030708031006050708180f030a0302071e0e0a0b040b06030f1504050c090d060612060b0a0f080a0305070f060507050d0507 76
    0x8950b401d1160420300d4030448034506401085642d5001d0340c24503080b86800c07085694035010315600200d10b8038664503007016208100e450300c66640546001442002d051400c6c4800805c000018483d24079031a6000407030110b66402c860654000d5a0820708032640d031141c1d85040c941a900480341030002204040c8042075180c030074be040351607186d00032807035500344101103000054078501880c42d1a880180e00080034465141071003010200e600a030040c083c50780c03030036002200403101314111081030008000240034814480e0700d102d8105103031060004501041c000032070010702401000a5014602008000020035501482031140300c05011032440f2091752400e00003551003d4a03240c103103090a104440760760400c0140920b00c1e81c003407000400e03220380d203640c0041400314115090380c41c40d0303c0300360020180c14a503016500800c001044402c2c05403802004640321864107100404204001500100f0f020100180c180e030190006803c000a050001c0041d101340d01c012031940754076042c000080d017418 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 63117143 1250 63115893 63115901
    0x6060504090b0408030a06150f0e010201020901020706030e010609020f0d110f0307030902130509010b01080612061303091503020406020f0d081b0d0e0303090708010204080703060f09020409061a0301 87
    0x10307901c90708202e0252259650841d40d500001c0c41e181e041a52500001107924109184445c03000b110b032200c41c424007402c4002024200401c0340700e81560700400140ca0903990014040382200c5c60b0785400160b0f20010640d246c090900c80d4024032007d800070a10b14441c102c01c0d00140b00b8624240b00c01c0183c00e400b040e1680c11800b60182c0603004c042d0034000516464020740190350302c070b440181040001009074020318101c50781910305d801642c0d0766440c1d1288650b00b03e089207401c1502100c040c3c502c16180c04402d503070b504000300902e104903100043c43c41090300403044400035000740840d0b048800320a030b0004000350014443c50006200c5d407060300c20301401c041501c55500c8041c1c1d031442da003684c0f803031034030640100541d000c460146410403014a02d012280302c5c589030400064003440c0d80b420101022458240960025034440e40704110400030a040011440201c03a40480042001c016010041e8000c192204c0701a41240c100405101041907903400000d03290380c041d01880d450b05180701031500725 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 63118393 1250 63117143 63117161
    0x51201080a03080402060304050a060e03030a0e03040f060e061606090b060f0928020403050d0206180c04050703090f0b012d0302040203060f10090e0f0c030402010c0c0f030b0406060504 81
    0x1c03c802401081c00740c00c2142c020340d4001d000c0d0b011620644800d641d580100da07c040c0f0861881c4c0c2000c000e0016080b014082d800d0302050070801542082e08104030005c0183c40340c40350406110147c0e08071b084e680c842c602510b44004088094074054038a03414108054400e484044030803010303030b070001410742c83c202d4440d4030306010251450003a82c0c2d03602901c040300100c16940412064140062034680350540c0014005540f03e8000b60500103201c0801a242220150030303400000c0140302540d04044001a81c11484001114089540e44800300c041d00100380600014059200f21038805051080c2089460304960318070600317403601118640400140320b03070820384407c1d07007450398002c001518040d000342d6001900104807000b00c01e01070001404800b11890404045542d05404018803802d040906900c01e908400c070081c1841c00460030f54180c80700610003818404000c4d8070b142807200550105010742680704001900544a00746901c11a0040720106e0708581071001c04601414a4080e030032074 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 63119643 1250 63118393 63118397
    0x90f060f060603091e0321020909071403150a0b04031b140a0501080a0b0303040312030b030a030e060d140a0b0a0b13050d0f05030d05040302012a0f020c060406051201080a03 76
    0xc0301700100d0101c1050707007440d0400c0d81005203080722134248112554540c00840810b400059450041200f8080079001c000e000b141400450340e6a544681070110441e0380c0610910075410441b952100012042c542c260014800c07040c0106000c020005540442c020034210b140c0038071102590707060b540c202d00ca2960101608800c504104008550180c001140c018503110004650b001d52203000c0380c0f9603042503006a4654015000c00003105402d4820803820740825000b811281d01143c40203488103603009400ea0143d0300005440c00c2e66800c5912010400b00d4107c8400c0c01405c1002807400940035070100c2030f104a07617542000a0b441d550400326210b003601140000641403a1034100111514a5401900c000a00250703070030025005000401e005036580c0000034040c2400e05000342100c41104181c91081c40c481c0d0942c00c0c0380b0300d04550341d4020f96986005242070040b0407080781005c00d0141c45a0304141c0128011550a4000014040c420b22060001009a9841010665a2250401c0a00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 63120893 1250 63119643 63119663
    0xc120711010305130c1e150819061a070f050601030b1503060405060105011404090c05070c050d03120507050c0609030a11060709090b0d020612010f06050a050306040f090f060f06060309 81
    0x10141001d803900c880500300700150410f030280e8507c4030342500a00210020b0000700c002d002c1000c640355009620003002502001044510708003108001c0006038020301e8061014042051400c0060f1804101d01d5151b01c0400c0d0b58543d40e507860825900c600c10340b1660f00210b40b0510b004505e040028500e4441e6070050000d00241e442d100054038410010042915030038810040410680840d0080c500e0307010840d80c0c0c990341c49955080090f600c81d90b0b070700014422030031f803485800800d600101d00e08034210094000951070702c0b4084140c65600c50780da40303040c69000d84010800407542c00300140000c0744441e1200300e014007500300c10030340352601182c0040116040510070703c0070000ca60f018038040c650180494041c10280c0d00010441c0c0c01020022505680580050020300c0d034540f0460010405801c09609009000c40c019040d404002c0100b4055aa03c55003070381907828a4002c00d1340d607a04494202480206da04000c0003600240125044290a00d4400a443c41c03080c07041403c0c490b040b10f0b40c14 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 63122143 1250 63120893 63120899
    0x6150e061512060f0d030801050922020f1c0b0103050607020d020a0305070204060e0f0403030605011407080309070932070801051002010609050709051f0c080c120711010305130c 78
    0x184500050f19054018150a0380a201503c0c0c110811504d1406034a40c40215803400d01080802d2200074a0a038002c040101c075a0900009200c0c44440582c1c1111007088421105001c9a0380040c0e4800d05003440f9038080340306043c050749a40d16410780e4016000c0e1a80c9640e251000e03a40e42e4504144c0d500140d01016011020038070174000342c038026100500c0400c25030341e90300036107000c0c010035500c482548070003500780002c02d5014401c140c010542803c04004841c3c00c0c1076280410b024404001c0c00e1844000000382c0c0408051140c000504041e04040103240003022140d2080074480c40048005070780503550894510003003c10034495005580d94461580c201014002088046c0d0b0001c0250343d225140402c000308103006141c440c0c0041d550f03021085140504001c031300d503914407404005808042424407155440048504c41941090201c0c0e500c450130101c940c602b0066540f41101000041645000c002c80b009600018800903030301440f503a00c841100042d42c0f41c8085008003500440e01c020 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 63123393 1250 63122143 63122167
    0x9060703080910020721030603111c06020403060623030d0302070302010902031b0a060e0904020402090111010c080a1a010c02010e03070b0f03040303051008072106150e0615 76
    0x9640602e400342500c0d01e80301c45140382d006030b81006008070340c10041c0d2001c180000c07400890f08040c0a200e450140400341c41c64655080c421501d5030100e00945095400ea44580c4101d041030b21080c1c3c6c001001c66844c3d503a41410001400e040c01003a820300034007103400440070703065003c0c038450400c018060200584441401d80003540220030403829952504461005030340d040c004814204c9062841d11070f00740b0001c080003d824000e4100390b007400001150911039444d05080643d001d54103440059841d01c4180050700c9902d02c14501c00e100790700f0010100c01c42c59000c0e1701c1c503002d07403035403e000e00a2065030714441d20481445060540001d0040c445072001d580304042184140d000501651143d9460303a8a204c190fa0101800c0308100b03c000080c17100301a230520a81da80000d040d403a101510303040c0031304a03485502c2445102c220050041480320550010200c40e82c0070745d0b02980400400700042800710160011f4440c10140d085401c000956a0500c0510f18000302c180500301d80c40c0418240704 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 63124643 1250 63123393 63123407
    0x50408030315131a28050f0102070806090a050c010c08030f0415020f032410050c0106170c03010e011e1505120a12020304060504060e150d060303020c0609060703 71
    0x181e22448002c2140c450003028803c00109808204d0b83c41c20030b52428081c0115001c442550031202064001e04880d20034002000c1016510200c840030102c1041c900103c0c03070600107070003490140c0261400d000c508040001c0500a0784d1288040c0c401110407000151281e15500e07001a100003410000a1813101d00107000562040c401c40f2114041c0c41e461100703000701e81114142a820b05000428005034210b8181c0700c402c8200001b00c030392a5030f155840464040045034511206003d004281090424000c0d004280a803500c0055a5410158503101c00c0d501c2140f040c0e1240a0751030411031310308000040c000c10305082101c5048140405c00c140d154801001412000b188006030744c0d00201c2d2030781d00e03044184d107041010f00042100c0000c0c2d04090940343e0104d0060310541d801088100b00440c2c00ca016607003211030a0421034010b010303c1d0040398038001246404a221031000521900880c110f62190080e02e000c1d500300c0301d4a8144006124007403048184090703200d9000e2040000181c8641c203 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 63125893 1250 63124643 63124681
    0x903030909020d11161b0f0303110c0409081c06230f130e0d0e010e0d0501090f05030d06051203040314160b041401020114060108100302090f010e0105010504080303 72
    0x80001c0070803015070b800010350840d100f900090b40184040d170082c004941e000202035281002c5905807a40f401c0c12a158102075032100805102c0504a40741036034905014241d81450064018404441d50386088440c0c1c3c0c1c000078096010241c080383c60300c10100035106200594175010360011038500410f01809500141c2c1030700a0380540003000003074594649194080c0f007001d00b09004200000151102414201c0e864810010030401200c91455a0781c45031001d00c40340300035561502c1840c0b03d410154050010080c000d007010035001d88003420420000000c015400c0d482404010203502c40e01001100c44006420300199882404144081410301c08403e01b0001c90070304403210252088a84642142680d0065500b80f0f40840d040221010392680d222014000b440200540001504411071840c0054903150400c04954005490800340c02c17102800f0f135800070454411407605201e00802c0c00024000c040e800b01d40d05000146a5014038151005e65400d04099030441e40c0b05041203601d030000f45 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 63127143 1250 63125893 63125917
    0xb041104020c030c0a110306040f030305040602040803160201021b130f0618020a03050a050105061207050f0d0f0c080702031e0405130506030105011a0d0b060d0501150f090303090902 80
    0x40c1e04a00ba04100502c10003251002801c0310500c24201060300821a00c0c1c1c540c000e070070500400c00003484501d03959442690500b400203507030306c403400c2103002401181c11108843c8000076070b4403032450416068900d014800d0f802c0b00c207211951040140466880c81007950004003405d80d46140315841c0c1c0003141010030b170f92400a49181d0710321101c100801d00c68a400300c2140d0010300c0b210b00d203070700d40181c5a0001c800b64041c40b66501d40808909944a14683e00000d41c003420086001b09214030119400c0c051003505241d259028a028400182108038010440342e227420f16403807102d409010054800d2070b99030050340c01d02d01d6203402e050070505084201c4170024001c00003c00c1c6a512041803e0241084501c002400c6c500700c403d140c212101070304020900d40500441c1c0c08101d00da60100d41401074002404940700d14003c003c00c0d010300544500c03940190400e800804d100c04001c202d0b8800059039680c62140c3d00c50f941c03090b1030b200814000600002c01c0107506109c0d04829800600084e1100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 63128393 1250 63127143 63127147
    0x70b060a14040e010e060403080115030c08010302010309210917010513031d03060f07030b0109030203070b0708040518040c0e040b13050c0301060303050406140c03030f0402061608041508040b04110402 88
    0x71086041c11b100f140d04a01240005005100108016a81d00c00281c4103007401c002040f15100007800b15841403100904054407500700204001005854100202480c003411541e2341c08010081e02480b40390142e4014000c1340e910920038030b901409080d0003091100d800f842e007020a52400c0780d000804642822000300b0043d000700785610301708410b40c40f55179081000c0b407060825810040a40c5c0129405e141040104c0105001580d0080344800459606a107071700d83d54a840e240541d00d90003942d03c4070b50310941d181d440d01c500e2010a00000d02c918481d00506400d20385410b200880d614041c0c0d800752000d03200800140781c62580c07a0703411003400e00440441c0d0107108030b60002030030b641c116041140011400700d401c0150740c1d0454001030301c90000c81030060901546194041d600d01006000403072007043c0d0b001082c2591185011030782102c481c407140068812503424031210781e40c081c1c03044800c0b2503032400454000350f10a00c1a50702403030384030280d03031400c1d1100c0d1a112604030f04c0d00101030703006600b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 63129499 1106 63128393 63128411
    0x60c020c0a05100e040f0204030201090b0418020304080415020c0306060604060210051510030b030c040207020d0b090c0a030f0b01050301020c330c070b060a14040e01 73
    0x800e0f2100c0c5400d2035980012520003010351021a0002d00c3c04940d44103948003a0000d10039207000b0380b0307116407480c1e554540d42214801e9106510414010040404032002950001e5401c5402407103800e08040c1c444e10b8646030b000d8041840d0016074040d0700308070000d040c18820f0342e502550803540c080c2424500900a512124020000c0c000f041d681d02c001000003285011080c40d00c079014204100782c94501501070000d1a00303041c40c910a12a841000d50140350500803550352a9000d444058400070554075451f076804090805260341c0180c424070005500e03078a200c40001c6000d408a1010240381e8285454000010b811440c0aa40104600a615040021516640c002c2c0075000313094090b0701c4a480c103500c3c6800d00001c0a1402580074040a600110043d2400e14040c0400810b40d8541c40100b08040095115070060013888440e540010b00c1d0a40c4951444840d890000c160140 = true := by decide +kernel

theorem cover : BRFrame.Cov 62949643 63129499 := by
  have h0 := BRFrame.cov_init 62949643
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62949643 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 62949643 ≤ n) (h2 : n < 63129499) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
