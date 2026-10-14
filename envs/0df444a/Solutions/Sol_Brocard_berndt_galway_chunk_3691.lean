-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3691
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:23:55.388832+00:00
-- url     : https://prove2.me/submissions/c9d85619-f134-4ff5-9592-254a72fc5fe0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 663669064 ≤ n < 663848920 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 663670314 1250 663669064 663669101
    0xe0102210a121802011407080d0605040f0e031c090203010207121b05060606030403020a200102160b070204022d0d0608010905060a020c032206020c0105120c03070e09040b0604 77
    0x2c000ea01c030980e0304140c06810080e41b00b291103d1410f22000300c0302d8064210a2182e80c52203807a84600160841d881003502592500f0b560051440d114403c50714a08600340182d45891092000340c511032401c1001001141d94038664200180d40900c010001135204515194030340c1460b2130b0140c00388840340301085483e0001d00a140000d40082146644588112030103512074030f85040c100e1500d45550705c018248000c1070120310f2101303100c480507020807a0903422254000340ca600d94490309076140c03141c000501e10501c00c80c0f00500d03041d0040e04101fa03100a101a04070008481480204d5485141d2850103500107041c0d021403180b03002c3c00014100080007840362510a688065a841c0c00805c1d1240c4c490707011030080c4003048280304460551074000440c0300420001c015007903a410031031052801502c40c03902c802e40154040d03407d07035500c4440710664421a07a42c07000511030380e03400180762038200005030810180a588403e44a4000d45c041d058007865450020248011a030040442c000107201 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 663671564 1250 663670314 663670331
    0x50306060108010f3308060f0604030c0b090f13051012020616020103150602060a1b050403140a020918010c02011a060c152e0b07030e0102210a12 64
    0x4c03d00070603040b5044180000220080403d0741070080355540005a40c5080350304500c40300642c0401710a016002c21500b2400e04c0b0070322010801c062145110041464003140c0c0308001450004015050881018107040100c1030303000d0004240d011000069132500f540e400501c0121079240140340080c02d000040c00d00c246240c1d800003055070180b888802010401c03006064116480b0350400301850319481c03440f03901c03a519604003039103c0b5800c42e10202d40a16054a100e00428510030700c00b000c19a80e01c5042c1340a0850700c90383c4002000e502c400d03246105086440300140c030303001c486511403115207d806090341521104242515820001c540c11a0306100c04414503081200608403400d100b00c600503941c110410129041900050320a10010403070420481e1034454401548600e6800c540040c1c04000343c18403e03150750f04d480c050994001c00511001002901481e1010050030b0305004889800075030005080162510140700007031241c1c082105401d05ea04100f8a0090343e01c02c0a00740803005 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 663672814 1250 663671564 663671579
    0x203091f0c12150b040803070311030717070c0b040b0307020f0f1902040906050901050601081b07030f020f0601030320060f0c09120d020d200a2a0f05030606010801 72
    0xc00103030000042564954482c0e560081c40f14000000b408454401501d60382c0d00c600c2151603402c00c1c5010340c04078042c3c040805000c140441115003142d48580742e5031058081c001c06004a401c107240464510092a04c080317025414180580b0042403016240c590741e1a01c0000281452404050040b443d40700303001c0c4032102c15020400b880803042c032000c0c084034030f6014000038000e0405d41102410300c07071426062101c0c0640641180344158001e88039002c0319280c129031120302c05043e240f0020b03c9842071208000291045202c080400140d104541c24906080c2d581c1d03040180a030b100b20041009243e005020030340e072110030030140360140050812441e0650000100240050904c80001c80000d807070901c03a5184108100005280030456940248001002c0d56801d2208204c0c0081000b00e684140071050410301115109081350240502240607504c0c000da2204500e000042d549040c80c2281c1d00700502c2c8454402004000c0602000c2c034640818541400f4001e810641041031002c01407180700e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 663674064 1250 663672814 663672827
    0x1090503010c1d04021b060402011b05061f051012050c0f030105060f0c0d032304030203090907140a1706010c031b0821190213090e0309040203091f0c 66
    0xf215141c00e91142000100150091041e03a00c00b40c0807600700301c040c60003240700142d801d12461003a00c0e130210200000c03c2c12041e00484500c02030543c0d11420028098480e0710b00c6a034100038a6014648805d034890002800000503a44508000755502c144030380d4601c80c90141c250014001d40100b4039061203c0e4030340f40c15220500485000c1c01000a40f07945840c02a01140c104071401020f0781e248421521008001d0912071102d091481c644c3d240209850b6440e13a2032600a0350305030000d40c80c140d00345046c01050a0000c00c96000d020744200c412200780d601c2c80084c000340c40242d544031003640c640a0514000300010f40a58104943d2200320030000c1d80101c1c0c00c12064003000c40e141d01e0b003000d03450100e0b89407040d2400f81c14004086140900803141b8101007a02a0b01e8007000d030740418600e04a00d008030700a804c0b1400d10140001c0b010810481c0550204110b42c400e033099924008d10300b404101a40d00c03e407028421580710003155040151700300e600a04c02c9207814421701070a100000001e004 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 663675314 1250 663674064 663674087
    0x6090f0105090303130b1b01020a0903060b04272306010b0309010b03070909031101111b030706090f1a010f260d02032703060a090f060213030201090503010c 69
    0x40c060005800035403076070300700150b8201082501a4120303094940d0304020294125000c25900e100070011441c1041d14103002b030f00c25510380b907038036481d80b149191103060240209014560b0455644c2d0000041170340c0d00301508202d80380d9080420000103032031400c5946102c65403440080071549a0303070300700c1107540403031038034111727402107a207280c9079121900154010720b1046a15036041c4074040c1c0018a00365980c00c0813003039a009488801e400402d00d4030311400d07114805046000c0080402481ca0942038600080305074501410490b8182449a41c511048618070f030b0341030315890581c007140420000039171a980740300d00d100f0b805030040394544201d10001c5040c3d801008181c6c42210781101d19100001c0c0c8040000f0180c000b00c03a241c5000c03c001075225400114503400d00d83c00c1603a801c5e2034181d80c0440495840028000305501d540740258940182105082110b0f0f403102d00d00e09030013280f6a800545a83c2c81464071880000c0e2031480090002081070b800305000b0790602250484807034104008402 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 663676564 1250 663675314 663675317
    0x809040f0539220312030f05130201050a021002030a061a070b060d032a050c04020f0415051e040807050d0203060f0601020705060d0204080123040816120804030e06090f01 75
    0x102c4000d2000380150141c0000c0b060600b29010f03c0c8000140700f5201c0c044041052251001c01403100d101904005480c4201c454054030f901081c200801540b146004003a580c80780d20544140400e0542144203076032082c2c039801030060b181c41c8207000c540040c00d09003810314040c0c1685460104156150400000024103040c42082c59800c004180f60050071105075219201100003180d140840020300b4410105034280d0700c9100c0c40e02c0f16151428544200c0c0c40c2004400d40c241d08242c644920590040e41c1c0c0b042c054100101845202c8540750001d001040d1100c80a22560701d03a030812401514224043c0c1c40644a11205600800562800704003150811958003c0d085281d45040050780380c20401e6004a03080303840082d10f5404941039074003510960361290001d0100300d00c40440c0200180d010002d40faa6030040c0300c013290010f05c0d42c100900400311050041c0040c034a0a48a41020540403041e400214038400200000c141d13200c200b881f8111411a100760034901c1810202d00b07680380c1124501d0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 663677814 1250 663676564 663676567
    0x6060306010b0c01140127061d09010f060b0a08070804020108040803040606150c020a0f0e01170a020d06020405130501032409050307031e0306060e0603040809040f0539 74
    0x3c0400a40220044010501c0b598020f03503584c406040c8030048003800004116150480207181040c036000799005c81e43d06240f1000341200b50700e4011200300d0068410303402d0759a42c000342c43d07030628540111001004c0a070070954903414440005480300f04000c0841c41044425410007005170b81104016170000d0f000a0000d4032507560b460703c40018000f58201c0400c407018401485045544008a00d5506200341c86100302c003036031410f8038152140c10780240c842c420b402600603c5003804041003d001c5035154030032542181d0f01500440d03102c01089900b6039101d0380000c0c0c00e00643c10134038118104c076140d071032040115625584030311400107058217661a04080d0100174610131812504844200b9400100b40c3c0e0b551850b52a01a060305006092046115221140142c003036005e486900704850300c50f1503501000408a0421415500003002201c039160700340884840c1740c880f0301c01d00d48000702d80000060b041c1000711071a848081040c1d20204002080039044014010304800075a800c6200c1d802103 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 663679064 1250 663677814 663677827
    0x5090703030930030c2406090207020d030507031404030b011401020c030c0910090f02070c0b070308070c140303070f0e1c080904020913061509060804030e010210181406060306010b 79
    0x44079054280c5e1805003050803603083e07182d40000b4602101d240601441c0d010403074196241110016409100c401960020070b10080d8008240600c000300682d510030314000250180443e0501c4140e00f254105840700580240144010b19100302c04811502090004001280f1404000303079990120429160050501c0004505580c4440e01c420001c0c0c944c800040c0710500c034540070300000b50403840d030a641c40301c400c0d0400910040d480d800c40c0c0e55990955165240d9543c0c00906542e183c80c440c8048481c0c503064510402100820b01c05580520340740d81e41c11003d8100000014542d882218001d40304500c100e07120051303112450040f1541681c8414200c0c0c4a0b190500020024010310b010707960007604144c501e0042c3d2065902007020b42d04801c10462aa09001d40100d0740116140112070200e0f54000200d0b01080c0544c40d0a00a4a41441100c0c0d075104110784210a4581d0b0340790ba85580d0540c4203580d0200702c19015004c01c000c60550040c0164503006001070380c0c661040c4982d404503507000581 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 663680314 1250 663679064 663679067
    0x1061d0a0c09050607030315060e010912050304090227060313170705070806100b0310050609150d0e12030f070c080c0312060f030f0607031e0509070303093003 70
    0x20600908005000745d858440038280500a41b0000c104113659400101c00495101c0c02a130700c1800a0b50103948210706207051045044c1410380c0d503401070f5624481032200041c03107201400184581c114404080320f1150082e001645c071200041c9141d8801c1d88144100703c0900ca1141030f614140c6d4101c140c0c521851810550700e5400c3c843c1c02405081030060340b501140307d840c006086809240e040d40d86821042e80c4840b0342c1d055010030340714000c2001a0600811051420402400404500514000c1c20180b03600c165045540512248400c2c03e80b00e52000c1c070040014861103071180e0204801c07510f10f15161701d010389000c600a1050090180b04450403040c000081c054031501040301088940c3d0740e0820511006491003140e019100b43c02c034011b8480c0701e007004245603001c40b4800004044a031155102540071b083c503c003111800c00001010760342809064000c103030062822901504000f415030400800383c0006402a154031000d00800ca9218011615501e12559440a0a14061045150 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 663681564 1250 663680314 663680327
    0x110a0c121514130320070608090138040603061b11030702090c070807050309090112030c020108130c030b060f010503100501140f0a09090e0c010504051c020907080901061d0a0c 77
    0x441203d8070702c0da0317084030014002c0040d01c1c900f07030703005529842030303d0365114085402e88501c280090400358a03100000141c155205c0c4076101c04000b10030b84500c0e01d41e180f02150844c1c1d100d50060707030410344810a00c40c0301800c128155568414a140c40c0403031547d004111030703580c8a6120001d01440710100010f60101006050b00c03481c1c1e80c000311656461006040ca2566030308118800b03445036000f80e0000488030402c95034010156410b842d004a17140c0301781c0040d43c0184008041c1d000300340d09091541c0000b95501041c40141d441000703446c0003420048207102010300903d100c103041c0001001481250b0050107a01e104072042403800b0016406511148032030b50140b561002c0c8882c00c086101151f0f541c00c504250300340d4030380880803c083c0e843c410b000f0b5610643b00410038003080c4108811300c11410000c51075400744c1e582c2c1d01d1107040c805c05603002c182c21500845078440050b82040c01d102c1c1c2642c082c01440e0051080b0800d11400d020001d01d810305959020b0b007200c0c17030180d484003000d00740c80c040c84 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 663682814 1250 663681564 663681587
    0x3010e04050c060c010902010206060a1518120311070b0f04031412030f1501020610050103050603070503030705100b06041401080a090b010b132301110a0c1215141303 73
    0x80460341c413034402d4101c1902038500100102d026003d048000b07185801d050040d01c0c12603c010008002502c0c0656040c0d41c4101d40e10028214000c60300808034500d1110b41d0f200207141d10a41e140600c3c150844001800c0080c980c120350080341d800c00c001000f64030b2000070346094031f400c484500350301711035080d0341454180c1c440300c4138184d5a0080308115100f10403280c664401c40800e00103441400c905801281c80d0f85040760b80f20303103800e28401e00740220351003a0b001e41c1d4000d074080d0460f0606500e40c800240342d41c01c01132003299958410251202c014286003d074800c1140d058070140d041a08240d81c2d2081c0c00024a1010b0410035060000b0721400c0c031075004210703080d030400044851542c5455560741e6030703071224943d41d0b00d00020b0310000483c4520465542407003c1400409031b05214803800444c0c5030340000700501d107223218510040010503003010900c1c0041004141c080640744003417400790f0000e9114480c4a02c094501510300d41342c01180c00019501c202894240804061180340a50310051048d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 663684064 1250 663682814 663682819
    0x20d1206030b0c030403020c010206040b0a0c0c02060c0f0d0215010902220e010830090a181d0606030a110604090f0c091a0703030504230a0201030e030403020603010e04050c 76
    0x480a1150f600000e6004500a5029a0070703a43ea03003041c00016a60b845081c0c130004c0a00a5010011300305440365440009034144034030b00307103210703a640b42c00003802a00000058082070300800c840c159240000c0020a1040584c0d002a014401c944165106502014030401d1800e43e0001100f803040d5900301030000101004d25624021140ca451485203040004d0040c04454400c100d00d000042c40c907404d042c42032901c100c40c5044150117100d1110100c0d00400d0916410021160b0007092006011500d000e4a061860002031030700c0d4883c80400e22074008042d00310498100206104d81c94402081d0f46480070b800105008442401d403011805d14801e40d4000312100b03240c089085a000110381028401c030710700d41d66100107545c6654070b040c2e00401c03030203629042c090104411000603000b90815a40325008100ca941405080041c1c40340385040c0903845509034009110740f9045680501c035400010841100541c281402c40c0d000c2240d40c0b00602035000207a2100700000e0400c00204016104450003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 663685314 1250 663684064 663684083
    0x6041b0f1b0f0507030215070803011502150421030608210d060801050417040b0403060b0103151d01060f020a030c05210706230a020c0c06030711011b020d120603 71
    0xb6040030b64a840940c04102d1103401301801d11100c180201c1c050316035041d0480d4955285901e001c0c0140440c031040305407030341580900341c82480d60020600c02c05110340d00440c0140c4030f1149109160b141d10003422103440a0500c4c09134140040317000068140c020710f50b2007458003c0f0340308042d0741036902c0c050500380070301041c1040e60100d0300c054103411190140e4801c0c50b20100f4404410341024403030045000b21900c076281448200040f40158001d048103041c103040004403c0f10000440f20703104d0050300008004143e003214210001c01968031140184035500d0240c0d0350300000b0100940701c0203139074400b808000c2051803510600c0740038000c0c25058480b00c5c4041580405a00900d0056000250250707401e501d000c80c031980c3c00000804080004a081a00750030554410f502c0324025041540d400800d40304200207148183c40d03d0000358044c0300641c0b00d41c00a010399043d281e0a60316100c3c4405180c9801c0c40d51000d00c00c0c0c0015401e8110116807d14500e0b038101403c2c54002400c0341c3d403002d403c2c14907 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 663686564 1250 663685314 663685343
    0x6030c121a130c260c0706020f04090c120510121b15021203040206160521220f1514030c0702010e090f0a020306010302120f06041b0f1b 60
    0x4040c0d0002c84000e0240c0c5403049415000c54105207038000c0c0c4508000130040410008290b203200300300601319140f150a006050807101a002e000f01d0708581c000da004941c0c0d541d001403455410102d40b179014185500c0502c0940390903012691948030038800e1940d00348071103036081e080000c0c01401042106480d440000055683c0d4468907c44000c0750140001d4056440072068068569041b00d101e80e80107040c0c07078942810303030f03504101c40b00010506540780d0241031207910400c031003010f80003400103245030032640340c1261a00611030b440c000502680440c00c518410010340c41c6400340d4104031031152100d912061100c0030140c071000702c51017421452000000400007100070840182c1415030003030345d0318010b51100d4024803103046070075900865190380001c00a10000c1c1150019540a80b041c5405801c2a040603100c1e200c00d001a81d06e00f000d01d001c40704000d60780c2000e20440c00e4419407416100080b207050540078041610f80900784040010b01080c40290380b410304c07040501c4c0381d800552000341c0030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 663687814 1250 663686564 663686599
    0x9040f0b092b0801060c03090509040c03060c180b250f05060108031c0e1c05090402040b0301090e120a05031317030a0509061005040f0f1508060106030c121a 69
    0x20620300b4540100d00500c0c0003280750f038440c1c8904110b01d94076891708084581054104104d60718000c00c1206c040c038186002100007956406a021104142d8036450b01d02407080d001d084c400203464001941c071f01001d11510402c2041c0b007940440c03010942c4001c410803201c50601c4440e0040440e0054801d20480000103448040000141007202c440243d940c0003810025007002030320080c61000c07078503902506100c4001c8074004040b9405004a081040c0b07003545441c00700d030582e0416400581100400310041200e03060300e005400030522502d020700400c8040c068101118012160220200310300800041c041035020445e440d07501c1e402c0541c003500300c1c4100000000e41e600840f0034501c3c807410320010511032540043d502e4011f0307070904182a10b1742d0500043c0002400c3c19010b04541316107480f5005c400000030310800030206000807801c0082c90030159a2403800b141030340b1000400d450600c8248403e94088041d91400d95118004103010342c40120b0000709034000380c0c4a036448810000c080e412007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 663689064 1250 663687814 663687883
    0x114093c011e0e0703110f030a050f071a0a02031210120b181b060d0b060d06050a0b04050f0f010201140f10050d0503040306020903030f0a0507020f09040f0b09 70
    0x11045082c06501c040601084c0c48080c41e00c80204052040c00c002111490604900d40c0c0300040179040b0b45030002d0381c1e06c4035450300c6c41c220400c0c1c4c5c16400548082c00442d505040d10102c0800c420b1800346881c0c00382400960360302c207241c104d40f80c041d0300f42d01081e4182c450700851001002d1000070a0f80c18441810080c12402083e600c19103c141a0395140d54109008030703000b06040c40e404e0507025011035900510a03594001180340310400e5544059202958400000d040f6580d5030581c0058418100b00500100d4006c907041084045001c0c40100701d1a41d582414030402441900d8030780114420070010707405480040c1003c500088640100051024120072003442440241240207600c1d0b514000c0c800c103500c0c000400741258004100600104ac002e8000b40311300003014086a203012880d000003a0b8a40000704003000247d000a0410b0540c81c05244030851403002b15130500c41030901e65a18600405010002007141401d200000c40d0118140014041140003e00000142c8001400c0440a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 663690314 1250 663689064 663689111
    0x7060c02010510081b2709070521300a0e04150b1909050a030f1a0610080a0f02130f1512090503040906080114093c01 52
    0x300f04201000107044400084075041d08150200343ca10b481c17145004c0c04442c00028181002c540b400d012003048031140f9003017891098076000060044c0d681402c0403c4444000c0c11988038111481e804050044640804c0c241741482c0100d1070121000344c1804055089003600d00402034608020980300401500110ba40c40e0008084400b0440c84400c4169002081c240d0301807007406050a00010075440350125020181512904210803159650000104003540f203820450f5804650508041000740c250b85408003c07024000c401d4040c60000041405d041c0b40d038504108121074100400e405102c01d6200652007025030301b0965650110030010b20301c0b03c1040c8a100c00c09000b10704009000030168130b0310f034a507180940e0380d4241003000340405d001900c2d550782d040c0c6642c0020000042c40b050107105541c002d08119001240f40f4405900040f6503440c002d144e0382980d00900c41e015070010070b4021030700040801810050b086100081d008a03c5910200c082c43e0325881c010041300610100c0120030325 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 663691564 1250 663690314 663690331
    0x301090c14040b01110d0804050307020a060215010807050f06130504021809010b160b04030908100b031c05041a0d020403050f0d0309050c04020d29010e150a0c050307060c020105 78
    0x1d4203c0200110344103450b00c2c40014868002400311000f080c0f140c61001d030018001c0f001c0b0303800d2003034907000a058648540d1040380540d002c204941c01404456400b1401040e0b003174050b0840500d400d0218505c00020720920b481a040000c00c4080342e07202003000400f80001400464888a00c000c2100c4001d04043c400c61040795083c000054940c040c41c102c40007280c141016140b2080280d40f03844107008007410850071702a070544046107038041080b10b2900c940300d480c07001ca1b40c840708506142c241100c040d10703a580000710418115006030402d04580444070b610203800c040801e400703042403087c0508811001000d00000d400024000c000403403209810940c1c003980c2042031a140d042d402c8680e8800c00401c640c1141c962200d1600d4642d02070302080d03c0300c407804100d00302169410303181040d14010180b03d00c44203804c007a07081c3d60311a0075000c120b00291012070001650311605030301400346405200c01c00c41c2d51100e04007081400e0084e10074541d80b0000503c410364940c0c2d00640030b807004452100c0c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 663692814 1250 663691564 663691571
    0x301140f041401031412091e12010207080706050c03280603050304171e0d03020711090907030302010506010e010e04050606130608091903230c0a03050c190b13020301090c1404 77
    0x48500b40360404441d007032017008085c004801c414410148a4905008c1801e9104007070448008502e0800e0005003841d40c458009585d4500051811408407803024000c11081507080c420001c041c043c1d4070346022031240c801d240e0360303940c44e00104820140030180c1009080f80408600020b000d011642c40f1110315400000341c03000340d0850425006000c550f4002003106070b20405140c83c0a42c0240d00070002a4003d00741d8000b505009004078452030416504a000c681c800341c4104149039080c400e43e90040c0b001d12b03200c0d02042c00040020901c0c040c0e0310515100da51b0f0b850110b10326a84400c1103d200075400c0c030038030341140c0c1c2c1d4242c00b400a02d011100c10790b2038090150344840c880f1041940b401c40a5064454004828210110410404e0038244d4104010001c0003a020010f0040050680040c4207590ba190b6440c6401c00c2d0500f0903a22418000703404118154200c0080c5580050691003070040260501e000c141d400041e014114036803014001e48e038584004545051030343d807a603461100694060 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 663694064 1250 663692814 663692833
    0x150801180209070806030607030c051918060206011805090316050706080108070b0f0d0f0e030705100e0d080a022104020102060714180303120703090b0c0301140f0414010314 76
    0x241c036141c00c11280e550345600150001040c0c280a0790ac40110484030f4603246040c10b0b03000c01041011807075880c10b04041059104540c1d80341d40f000c0354440242580f8405003015502d4000c0010821503c1c2401149003a141e0300010240b171010401c1e20308030031115130009022031321400c003280c403810140258000a140c480010840103400a0700034200e03080d2206451a058440c00004c040c0d81080152a450030745840c55040c50800034000d1618081405021310b41e52032641c904145050290543e03281924140445a10041000310344060044602e04041050350b070b40c5580480284510000848121040e40d0a8901ca400441c403080c0b003240b00b038085861035118084140e806125030035903840303000400c21840c90350351455460040b180e5005030841e42402c084510450f0030000031204180041da443c01100c0602c103001103187d4001100c03055891440d41444440c5140340c0c607103103c19006603030b9041c51309095103a0768440f6412618540301004656141e1a203800c032400071000741500c0c0e100d25180c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 663695314 1250 663694064 663694067
    0x1b1b0512010902060304060c031d010e0c04090807030e0a0b04030c1d13030e0a0306140609011a0405090408191d0f180408070c0602210c03090415080118020907 70
    0xd4040d400d40081090342075595647d5032101030030300085000100340e01c0d0300984050110303c0300c11038018051103001091115074000c040d490544008d2a451149051a805101085460045800050700740c54400c0c104640720010a00240c0c141d88101d19409000074000b050151400c482c40c01e403000302d00034070320b0420682c40c000d064850a55201540341d40d18100030000038011071a000103d0b0004d420003030300c15502d88600782243e0311082c0c5a84080104010040d03030340303030000d2903078051712002c055481180d25202c1e0190300d0340258001ca9020b03e02c1d01c0c000c01c00f07000e215001c0e80c1c06010300345030090a4240f1000c1c02842c05039140c2810342c4190700c845915216240102000c41040310103881003088504000102614031000b0700142c590300c0d0204540c50100c0c107012086405450160020301d15810b000e00700c8105c035000c04000c41d1318a0402e0107003029505000c002c5403040002100d022030494001c408103400d4451990112401c2d628103916003840740607800f80d07015114022100c900d020b9aa80f0f00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 663696564 1250 663695314 663695321
    0x501061202011d030f0102120406060b040e04080d110c0c0a210809060d090c14030106030812060a18140f01030b19140705071b050307061b1b051201 65
    0x20002e0214103902c044914400341005141030244008044562510420403003500326408442c00082c80308a2000300401d002a50240c00003c0401c03020a40c5094600039a4844406001e00010240b0701c000519142d180c91a400c030401c040360403800590341c1c03150f00c1140c0f640c0380101c0310054000c440d284000a0721690614080803c0c0b045001810b600c44e03e1552410b807543e02c8000816400f510900001d42c00390950705c51103058501c41d00e900303000e0b5418955980010b2100310b904920036810304005000103409801030720392440c41034603850b2080d16402c002685440c469007004140340904410b50504d5015508210420804240f84540c540c60308403a40c91004000d000c06810388141c0400b0588100c41c2d90984480102c40200c0018030142207100c4100d04113042e10310100182000c0740d02e005004424500140c1518905c800d09200d41c81c001c007294403440544035190521a030b9181c00401c0100f43c50765005c0c0c21358080d01c45c0440d80e20b03034006062488800c1c0038030340c010910b61042d50f250450520 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 663697814 1250 663696564 663696599
    0xe010608120c070e0a0501030c080c030a030f05070b0709060f09051f090e0a020d0e0613080c030f030124020f0a110607050d0314070311091905030712050106 69
    0x80c0a8402079001c01d1401006920440e1440d00758883c1c0c800c0020003419012045004102034030000c1025451402c000300c0301d0026402c0840da541140b521612565000200b4610540e494200700e100c2e041d00305420303901e6010751440a02041441400c20901e103520951031020348401d0b48403d2100c01e40309404580a400c84e0244039006070044a030304c0407017000f96030480c03c658224a400ca2507161101483c01051000f035030200a06a00407034412000d4096004002010f40701d50010301452400d000565030341294001c019289801c00114446907401c103004a840c007a407045041c1e50b403541d58802c3c0c82d6045414110050b11154042c01d00d00341c0f5440441d5504071480d0b03c6000b05542000b0742c99154058242c0880f4030750201e42009514001007084c49016003109040e1000140018100c1c9201142c0c00000d010030101072502e8140c0d000a100d0708251610b049080c6c40c081030800d541c03030310351001f030b02c0079044240d0600c600c440010361161101862018144100020b016480ea601c0110071504000e1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 663699064 1250 663697814 663697829
    0x105090c0c0604080325020303070807210e010e07030f12030903020601140402120106020c1315060c020a05040603050d021c09033518090603030a201f0e0106 69
    0x510118012031448000345411501b503022030594598405215100e580740c00b0803d80141e040841007000e10ad400c40c0740035a00c81810f0030081c1c0c080c0044510b0340c58208a5680403030804c2daa4142c7c1003e40300c070951044410714030000840c6d9101c4d07203a051040344652410300c00c0303d040070101a40040c2501c2406240005949900181201d9007803200c21007500c00e20740d280c03d0700103900384000b20842403074900090090416030043c1a4040200003800801001d10448420050500c4c45504100c5a6410100c04881c001e10f040c0c58a1400c9100240000f1526030285501034205003000c02482000b26200d4550301581c0c00721780c940c0c0308070a4044080f03142c0d4481c0b00c0104407030340f40030004100400040001000465551a41807802256104010009108240c400303070006c111010b007416240102c11000300201d5400d40e40d403400c580041c0e0340e446407100d200100701c60f250702900220701494100d9501804402a500e048041c079490310751200101d20310079455414031071006485007040c81280305079001c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 663700314 1250 663699064 663699073
    0x30c0f0b3904050d03020c030105070305090d03060302010906030c26180c0f0906010c0c0f0810060509010302060f04120b070806011b231c110d050405130b060c01050105090c0c 77
    0x2884100302c104021404c0a400794016007072082c1c0769075801e106943c030a003042e40300040d00d400d084d41c4662911130081346040c181464010240003503a004408401100c80c24513000c03404010b41c880858082d5140745030001418040d090b40c1504904050340e6a202e80098910300e091380070320f8108581e42c0e0a50194080d00908042c82c682c400c0e003843c00c0c0c501c1d07203c0f406040c1003c050313003140e440890383c1420380d1004589032024501404449401e1242c000020300204061200c1e604100028400d400b040c0f0000380b043e500020514480f0303145030161401010b015040724203100c000d00b0034000f42d520444034500010800f600081d050341c000c000309054400441c0c04291034508695a00e0700f1212a4044801542c02c510a03240500c1e004004c04200e404507850800813282550342c0107001d2151100340710710550410300040449591000070784040742d004903929201000030951000082800e0005240c01c002d0000322000031040540240c0d049500c1620703058050782e2100c11010140c020070301c0350401e40c0c10 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 663701564 1250 663700314 663700319
    0x90103230708040f05060708012105061909020607061505040203010e1b45010f0e060d0f0516030b030c060705011407120e0c0a03030c0f0b3904 63
    0x2c40c2410b542e009209015422a83c036098072031500d414822202000000c4c9204014082c0c0d0240e8000000b4142551010381e0380c0250b07595555890720710050052444903c1007011520710502d54001070b2065030080e000c00d41d03039080ca090510180c0107140d6000c480030030640340051181018401c0320f040710950302d00c02480c1d4443e18131403a0400202c000c80101c00b0028808030202d4540500a840c2c1c071406403d41c2e00440142090202c00701c410544004401d08644074010b842d40d800895040510410b0704c1c0c0141080042c200203445030091024051629203442d5a000f01e01c1c0e0180d0005015924484031054402180344d0200e01b5100745480e504d4244e0045000c1c6102800e2010150240520420001c50380316050b14512501072005c13284900050021051400c0d01d51080c82181170703004001000d03108205c0101d000c070350340914603c401000c0216a042840910610303400b00c008007544020405403034244450240c000312004019030103e03021502080301c0c0780f440c180540460344840700d070507800c091 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 663702814 1250 663701564 663701567
    0x60512060d0b090109020405060604080c09100f0603050603150403090603020f04030605070507022707050c0c03120406020706050301030c17330c070f08030a0e030c030901032307 78
    0x144050035454001c201188207400141c0100091485040040c00001300d00b2040d00400c001d480d0b01502c5c841c014541000b052003000c80100e841b52240c0d00075580c400c02c540310901d5080140b69580d02c02c10207500c10010125030700c1e42c55004640030b84d100f201200e0018000010810914905550050104150441c00c1016038081c0d0042d15071149803802d05130801b41d507621004143e401c101d400400154000031140214609400f901025000400201411a000c8081038681d108080c2050040c444042035070020800d081200e60088074000d03060383c4001403640c040001039046406503901500540d0800700d0024130401c10741c0e040b2600006102d100c1031801468082c01030f00d0804040040c0200d90b582030210710320782d40c00c0000c0400084000320b030b8029580c1442181c6409071082001c428108a10b1000c26040c25000390300c940c000c100b15540381c40380710982005001d81c80c20360000d40004111912441404000780038000c03020b0303c0621200c03140400394588104048081c200705608113000c0faa201d0b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 663704064 1250 663702814 663702847
    0x7121b14031e0903130f0e010b0715090c0302031b04051602071703040503030414030c0d12031a03190b010905071b080412080304023a1509031e090605 66
    0x1040440549140c468500700710101446131b90024480202e60b4a010024015180d404600400e0318410075418010030780c0e81c003590000c0001613004c07900e40b124036510a20003440d40100041d540103049070843c075070100b24403650214964050b840f9a141c82c000414008581162071420662640035000d01070401042c4081e44000d115043c040d0300c802d0202142c6518204000d0000d8038044410605101507841050b1030401d8410145001c1c00d5054a0040040c0300001080702d02c54140c1000320703400392811010090500a40701042d494402c003c0d060100a50659164900728050701d03900c2250fa27291504042500c00a9500400180c208080240d0381c81c08144031048061151280601d40350f47d40700001180e050f000030903900210f000050100318945136403218a400c0c0030301c072000a4050300342d145006034220341d00e2031101074410104200c10070000c803042c020512805a010850410141401406007003640c0c0c41d12005003941c808202c82e680205000c20031289107035203842c0352100401020002 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 663705314 1250 663704064 663704071
    0xf0915240f070c12110904050f07180b0a081f0204081c08070c1509020102010b030102030a051e0405071a09031e0706050f030406020307121b14031e 65
    0xe11040c25021094010103005042541e00c10280d00d44900c280d0502400c1e5040c0ca600540c0c120140c1c0e11100c0c001040e40402c6501c1000403038241203240d541d4245282440004a60710318240644107001c150444240414400d1100d82d2400308400510310007442860010750080e00440d0b4010a01cbc1641000e043e140c0e504334a041c007002504080d030b107006180c07a01401000c50401c0200324100280400c1c0d0120950707601c071081d403800c500c1c500c405440b000808d003200c8184200040c0c071900b0030300c2564001d4002d50300c184000b500031580e034905084000000e10f810f0318aa02e0b521364645160301110301003c20750f80a04c0c2c100300601000c9140515064036500c0920421240800510405140303036028400448884e400c0c080040d40703c072940c440642081000d401800038007038148000d9140c41c06820503264055400000182d03641c440550a6038409203489550190a04141d905030440206050b806001166a11101100b071600798102c8114001286c98100d001c2490401c00380b4905000d08241c0c2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 663706564 1250 663705314 663705349
    0x60f170309040b031005040f0311031306120b2709070b0d02090a0b071a16020c040c1403090703061407020a0f0813090b090703150303080403090b03150f0915 69
    0x6145c2c0240c901c903c1550401c4405540350305810081c00d084c540c00001c20419541200d001d0344c900440c08403040c0e1220218001c4508000348980c2c5240c40c0316030380e03002e400048030041510300101c40340c60001914100c0410486080c2c00c0c41c0b408200c0d011000100f4509407007021600c5800e24004c038490030025081102407941c02070f04c035500090818464001003082d14010742c0441c409410003441030360078810241a613034881041132008188241c0c0070484c8644140c00701c0c0c010400840603041180c00d04680c0c20262603280b0b000051151011001904504403446480103000601006205c0c1c004140100c07510b80c003680004411400065210391611030b0184100411814110006180d40d04001f650304110051030340c5060400003407400e02507266002d02d0390f00d0280700019014200c0d400407800307840020180080300303011070105400b81c1d40e59009080d107680680c1d1a07180161aa5019180982c0c0d1503028081e0102a400c20303050141655100d9040100d00d020100000710074050380341c084004400d0b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 663707814 1250 663706564 663706573
    0x203012d0b0d020a020705100f140c030307110c060319020c1203070906031805071806080a060f050f060307050105070312020301030507060207120b0601080901150801060f170309040b03 81
    0x64101c0003040a4108142d40400050310350a0101020349860029000140300b625285c08241c050341e40b040311840d4402091400307034030011950664100c03070b004408001200d80400700c20000c001c0d6118442032074a6200c8000c80d2006030202c42404211710054407145485c5480895a4024074980c0d0010710040f050441150070b1040450340b804000e400681c0d03100c0014801e000b04003e1b10b5414040d41140400a4401da00066071a0760303940d556160a214810405c0b68004e401c14000c02c0640c0000010079044040e0307011041b031413501e24001c1200f0420b41851515000100701d0b181d8904e04214850368019004107040c0703080900542b0f00c5c0c2c00072001142007044000380e204440756540042c500a40c07150000340444c0e030500c0b40190904da4290000503041e005000120045003003003078056003218080c00c02280320340ba155030048c00f4098544020f0441040300c2000940808154440401c0b510560f103040394031502d9003000d881036070300c001c0c1968996006000c803c0c11482c2c03561080040040040449 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 663709064 1250 663707814 663707819
    0x7050a0203011e0f2915040f17241b0f0403120f0c06090215181905030604060209240a020115030f0b181e0106090203012d 54
    0x6801e4901810161400c01d034040080001d4140742d0080d044913041320b0f0301c20b00c107058000c94021600c80486040d40d0701003600812494440d01e4010141800c282c079400342560b99611340d0101078a04074988140c0da04618070840d1070030b031464041101c071010048010406040580303249480c1a0010251000306183c69424404504501c514001d100390b00300041d083d0384581c518100942032070102c0e881c00301484034030440d104500303138007020040080d40d000e40002100b00450011807000d40443d203000380c0401000070304d0465080e02000c071300e00b0108102d41ca004110300a400d50039450442d0f228842c1c141c2d00c40c8000c64002140c80e00a099032060203003c6820707011001d9400c020b5503111810420b054100061500c820640c28001d01c200c80315020f620012180c40e40d40c9101c42c00c0c0002001402d504621000305a80c0f42000011001e507501400441d0140d0b912103c10740407144c1e41c0005034280d50310700400085e8410b01402601d04170342500d00455280001c40907000380032b030030284d2134004108402402 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 663710314 1250 663709064 663709069
    0x91314010213060c0b010e040f17040302220b01050a022e020a0f030b01090b0405121606033306180e0127050103110402090105120115080c0a08010b07050a02 69
    0x1050040411341e40f0301c5a216020700380303000d0300c0b5810b800c41048018024200400b1070b03e8002044204c60740001400149070710006810800d000341e400080d8000c1040c603148000c100615004994144005410011301410b000152921300c80c07840100d0158004a100224a820707400c6841d28803d0048100300300c6d80b840040c0c0e41d080f41e20008004000c62080c10055081c55410f1164520691080c00e02c4035101d401c0107201c4005014034441c035482140410581d07a841f413403c1c80111044105442011105511031901601900b521161600344009001e1103042d1071800390300d866000d86000124010550520100711940000f041da8500d202d20a8500040c0c48050038a070b5900814005181c1c5452400a8903860305246000300225034541c104130040c404102206061310040da000c80e00182c0d50115035005071421700550000510240e030040c0005080801c10310108440741d410764a240041e41c521b49005410b0003202d000800042c814030040c802c1c1c00400000701b44203400f446c210b6052032400d500 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 663711564 1250 663710314 663710347
    0x3030406090507090e07030f1a09010606230d09050f150a060503030a080105041a0607080403170c190602040801020d0b01030b0102070810020f1603021b0913140102 72
    0x6046505a556140306018810203000180150031490310038050429509211696421113000c05003040c2400c0d42031808100d9400301002d01d40c01c0c00400c2c21801d01e080c94100f8001c100b544203003804180301d405040e0204100480380c0e5145026061407078100220499200c000f007511400c12103a511070303010b07040160501005a07084880042c44085031520780176a4501c25240b1a41c8414041d034011321040c140540c00404940c19103000ba1400190a0114281a000000c1c0d85e045543c100b20009160818070216100600035203000d00203845d2542031142c090f140c00d02c91003035222065044405214010f041c2e1149800600d4000c05003d400c0640b80c0c00300307a08a900c18420324118039601e020001d01541c040c081c14401d86070900141a0070741ca4009603c5c0c8482d02c892440a116034000307103104802c004c600030fa40c1c02401e0030091050921035880c02a40d2000800d0b80000040801c0340c5006480c50b0486207688141d1840905200100c0150303030320a20300764a24000203440d50240b01400c00c240381e010 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 663712814 1250 663711564 663711571
    0x2a07031401051e0f0f0a18030305040c0b120c0304030c0606060e0a060f05040512190b01061b0206090409030c0b0c120f010b03060607080f0d140a0b010f030b01020f0303 74
    0x80c00042c4504000f20008440c03642c1c03042c0d480d440c02d0390000700540f00302c0c40301100e1360004007a641e0002560342c50407100700600c408404040b92a0b04c582802c818180d15900807807045c1e20910740300403100d440710310400c2030b80142c0c60088a43c203042c800280ca10100d05000e55041032090810383e2a00380f0f940c1d9001c044d284030b60440340028041886410f00781c0b400f40d000341c00a00c0c860400751001400500c0c0103150340300707500445014000202d42d261286508025a0510050550b502e030200c01980c80d14110000003882440300280a2290040d6110804500100c5895004008070b1610202405100c05080001019014084d8005040001c918290b09a80c480d050302e27448195604942801840f191001814110810480a0040c42828032250031a40c200c4401c840303803902c840d00c03894103211512464090341c0422a020a82c103000c400c0c145c020224802c000440d1404503640d03621400100c4041030201400142810300075000c0707501a5000010009061040d40c91422407071020a15640c001d8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 663714064 1250 663712814 663712853
    0xc060f18020103050a151406130306061701020c031905220816030c060c020d14070302040605030c03060406050903040b0309060f090f0c060d0b04091a0105062a0703 72
    0x2490980e04540c0e05100c0c05501540703648040010841c0c1400c0b1045144c2c3c01e01601c07008080c03110700940c0c00e035141402d40d14250750000b00405119141c0c80d114014000c144110700c100303c0c3c0c905c15621802c4041c0280c82c8152494002503040020f48043d81710300d50300059414061080c100144030300c02140a60300e80081c46030800d441e2510303103410300c540c0c9007050b401d08020440740c1e400001e10010359903070300308800c480c0313580307010610501203000242c4a0140d9500080954544a030320191200d408182401200d000720340805c00c459445007455103036a03100c090707030f54143c1043c4c00040018805a1000750420000000c0764102038840c5c0c601000c580c820b84494440340c0c0f180c0108130300e4020584602c1d60107401d40024014200c0c00385441c03503581c5141d203210380c400c4002007070b281003454007030b44030b058290030003881031040190509006245c440700c2d078070480e1340c510640000f0800f41010303412a04d0408d1600d84002107030341088078011a02c800c404007000750b0300600400001240c031251400d00c404000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 663715314 1250 663714064 663714101
    0x405060a08090601090e061303020c0d030801050a06051207030f110f0403021e0303030f07052106041b09090e210309060f15010503072304080f0304080c010c060f 71
    0x10a03825032503c2c10580c41890484d05040c40302044d04400b0805981010a541ea81d9606665601d01603050010010034150042c821001da2070605501002c10740c1264020b842c0c0c0100e03552129011642407081c1810315240b401c100000c201a01c0c400e602954945550b03e90000c0c003922103c16100b400e078811031000d114200081414415450541f141d010501000c00700204550fa0705408603480b408024200c61502100c0000284098000c0e0212020388481a1380b80d00f003000c881c0c81c1c103d0300c5c41c4291401d41c002d0307141c003200301e4812650b1406130000403000e03240c0e070400c03501c0c01c000b002c00b50503414100c515600504c58503141c07007512100c1e4a0210b600c41e41449440c2c0ca81000342d21b18005000b0580600250a4001e1002d840c512142c0420b00f80340a2030171566941d075031002624140c10003102c0b04d90103401c0c0c003100701240070041d000d072042d6410321003511403a04080081940c0da002d10300991000ba0088024040c241d8041c0031003519140c803902d400320304291245110702c100d444001115100e02074 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 663716564 1250 663715314 663715321
    0xa2c1e15130e10180b01030f060b030109030305071d1509030a0512190e09040803040204140910060501090b310305030a0905040513020f15070f0204060b2701050405060a08 75
    0x1075008050210003051088580c0002d19190703012405c9040c4006000d80380d03005e08400a0110300c0d0404440000040e009002c815070501e4010010002115070030005040e450000c02d51080854070104082c0340109815802c80c041410468164004400b07668103210304c5202e8400558103200d550801010b884009884405100d418514020300801d50410003110040d10300c0c0715038601c0c040c142c0241e00042001c0d04d90342c440c0702043c02801c800742c01213800e000c08030810030724550000d242c581d28240d0f00802c0c040142c2e25001502c0c1c0c078400b8083e51032a2401442100d00c00000344400301240241500107040420a80381c10303108507041d5800680c0c2d1500002070300c3c004035400080d0303840141401d0380c0400051a00c0b0f042d403510aa2140b000912070010601240d05a50725098658200c40700c1c004d45a5513103420f0f141006122440140490013603040070800100381d0300100070764070a031f00c40c400c0d0703009460406242c0c407551205100c03003907050280038840410181c84450107414a80075540b107003140c504 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 663717814 1250 663716564 663716593
    0x22401060f0c0c060c080c1c1b0c05090702070f06122a0c020a050a0611240c030a06170102030405120a020309040b0a2c1e15130e 57
    0x7003403002030420312005000c1000020914500402114068600942140418500b290991040092040f041c1c414a031800b84e0b81c500c01c00101440c0c00d0345441c2c4040480c03240d501403002200319100076040c1801c100b81080345041c0a4100c1d80e005030548159000c2c1134a40c030140303c000845800c0f1500240e80b61b09403541c0c15142e4031403840000300f05402e03030700c0c1d02c46c070b61015140ea00d041a62180811021111030011500e80f40710b44005004000c2004070280e40340c400060260003841d10854140c818546000c80c440c0e6000420540d0801c41030030307202c0c541e6440701c0f410320300d600150080459a964000c0000c850305074000c004140300802c4000340c0d403800e05050203407902024540c46c1480c010100501d0b54074907000011162008416140858500301e4140040c0b8000301680c800028a002002c0030744401d0100742102180b2685410b5030380d001c0e01c9808000190340c0003209000010913820000c1405000c1d81c860001e04494002d08040003010000c0c8440140e1303a40081e2596a980b00d06142c04240707 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 663719064 1250 663717814 663717827
    0x9042001081003031206030b0a0c0207170703030c0f02030a0b09010b030c03030307120b0301050108010e1507091a0c100605030f0f060f33280e0702240106 68
    0x40500746080a0181485180314030704410307502c00282401194400b28440c0c0c0441d400944c0150f801c445104810300d08100c4c1c0e880900fa42c0204000140648600443c944000c81c140070708480e406401003810307138155034040c0d0b0061045501512041c0313000c1c00c940f005a07401c005190503035105140010031400c0c5812040d080d14201c205061080d00300340c0c07050034140c5000003078951040446c03500b61007006507003640000521030407a419030954248000410341c0e181c150403204500780d50601312010254120b46200390310704141d80701d000013008030b04108075410703200d000184860200c0c0449440d2010000e0150302e424541c2079803900c400d44412040103e8a400e020390580ca210708409000208000c60100f1b44801004240400114400000c682c911a405100001c03060003401b5045405051821429454014103081480b07a0f510262894588055500501040360103404003401d03d800c3c0808040d141d90020020001c5100e511403031240070042c100804010140307085900040d504164004001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 663720314 1250 663719064 663719123
    0x70306060914090408030711150f07080907050f01110105040c0807080a1a070905030d05030907090209010c020906040b19030c050d0c06031806020403050f060907051c0206090904 78
    0x3010b1041c403184280c3e141d00c1281d03a0b0050f4404050b680d07a58410a09883e000d45054080e6040e100d00d4000c139401000c1000c049020343c503060704900c030940d141002150b42c400122031400c42c5400c5000c0400880c00d008100010602e0141082400011012501402c640007140c1c240c41e00314644604100030784050100401502c502d90107044001e0b159290880c03074038002000c9003910706040c000180c00c02d12811041000c0c2c10000c0c15038500400c1450014142e40050364202d109004100300019004403c2c1b080350f00c0c034039042e140e0440404891b0200402c81200516547e0010340700c40c00c03189141d40f100d0261140c0381aa84a0160f001c1c251f0403c2510404190009405000401c14050220705200803d00840f809071030046803a0305605080201413840610052a803400801c1c04002c010700420100f0701640c002046904941d40e0b5a2110780e1032f410f511425400600b54884110b110102c840341049650010b44501d14001840011030000041254203032995150441038101d81520f0041d00a01c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 663721564 1250 663720314 663720329
    0x603320309060f0c010e031222020d03030504060b040c020706030b030102030c040b34051c09140102030c0a0c15050403150f09141c0c05030405091803030703060609 72
    0x52406039030100b2140d110310300003242902c2011482c1ca46107030302500602c2c101410141035917154070701040090701c6000107489090102802040b0402c0c82e421000c4d010307510135001007002e4542041500e003900100400b410641d40705888400003040c989603805040703402c021071b078010000186403402c000e00f251b00d484c1b2250300c26401041488130494825061b5410788054903001070f80c40c00a411000d4550b500007001810842000b040484100080080d540000e8010010740c2c1841d4a14503051008200c149c1c8040c0c04a14084014444109030100c04d8014a10600440e89030444016400b440c0001c14042100c040300d82c201c06004004d04410409800c0089040240c2454119510421540701155126280f1580d42803460500b0029800114909400402c00308550b080144c52070748940120a5456899142d44d600c140c280d03104050352a04a60020f02541c2070600f00010400c078244080d020010f0000700c1c1480814540b4240000c1d070250080b501d000540519141015006030400e45c015031 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 663722814 1250 663721564 663721567
    0x909051501030b03070801060b0403061a10050a02070f0b030406060501050301060f0f030b061206090c16020409081921060506030403030b1c0b011a0306150a020106033203 75
    0x15a005441000395424002401c0100300a603030321010a1500c0100c1e40f01c410f0940c2003160002c1d031485044000c1059a00030001070010400c512448000429109001d6808c4004400d00b04502407242010703140004240c8180d0b10b215966232440b840400030358000c100c003004008140000c103d103e1040c00010700d030a013800340c02d56150210181071440303158240014084402e90801c1074034402d601007188110001c01c201e031219070702c000c80c0000320011900b00c0d0042c0903030f4002c13910058005041c1c4d10400001d007425844181c3c281c2c24000030701130100c021560740d4028010724141941c50090b50a0a0503543e40d8600880c1064020080e0b14020741396801c2c03103610f0807038140265200c00080b6584240c06041c08600600741c030001c00c0d180c501030356241c500040000541c5c0204500410824100c911511505c2c9a41e80d1420500b070403880305490341030344011080350132044c04c8542000b51503240b503a40000900345650383c075008001074070050400d904101c4007540700d2592000c8051102c900c11400006c6 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 663724064 1250 663722814 663722821
    0x1d0d090608180115080d081f050d020d02064b09030724031a031911040614090a09200f03120403020a0801090206250b0c0406090905 58
    0x500070000207084801a00c4000800c41c82100094122a002490aa01c00b015642d40d4034104c0b912441014820030004480b100800e00c542c640c0c2c025445e0307001400c0005403080349840c0407c4000c00703003400200d803c4201c5100030303409a070380d040152050050707210304480e06100784200e8000c1040300190310307405441d401041901c1000c144840c0c041c83ea407030502060fa18000f18001074604005039111340c0e032881144100480755601a01b000e0080c0b00941c4090002c94003042c60f003105c07035803000240b07505644074a80c2c0111450341108007030386060140072500703000051034000c10140d46403500701520075404801e03014400d0511003c04c80c0e10580c0c02c42c041188003c0ca948041c49034081d102c0170500100d220005e05010b984031881d0001a800003001c940401d507441d400150103800c0386c030040c3e105100d440400240c021040c055425115401492140340900016403000b01c1d20b40001628031042c42c0f52024070004841101c294016004108e1190b160b80c50f140d002010001181c09c801b80090410003803 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 663725314 1250 663724064 663724067
    0x21052a090607030e0a03081b0109120503041707200118270509011a0d0c0605070807141b03030703140708121005010e0f03150907091d0d0906 62
    0x40c0d54596a084480a90324550b9003000c640404a41c1d100c990700503484400001003200c0c0c0002032104209000d0301ca450000307949052802c0f1100f628000d800c00d048a054240903c0c0f0400c0207540c400d10903804040682c200c1401d5400ca81c12442048503404545103800005010b80c54603911580000d02c0e01500609481c1c0844205449030300c1400000410818201e5410440040c1d84040d0609400701b00841e01d880884036020f030404814011105040d140d00760388500b05207002588094000b21259103c41c503104007141c042d0304c40c1a050b184000140540c0e0006060400601014031740b01e4010301040e041f40c04400c1880c4281401030340b003580100007250019070440348408581184120307030b5803a81c5007030410005a00c02d80305049256a003400400c01400c59001c1048155002aa103d43c1c001d103003901440804071400c203a1507810b60110303a25000f8003151075002d039030011781c52080d02da600d80c5d20005101036452149485e010152200c0415280010401c15481e89450702c0c6000c00013289017490 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 663726564 1250 663725314 663725317
    0xf0204031e060b0319060614010f080705091804030906030b1003020f070507062024090a05030c1f050c0403080703050702150d140f150121052a 63
    0x35030120000c100008a01402403942c00510f0310038000d02558820500c1c0c0382c0d50f50741101c020700b0848100f45403041c0400d00e40c03402d0203218a00030301030310381141202425205a82d2158000c0100c42040020400302443d43c450300100000400c034500100c00508184c40c1c085c0440020740c0264082601e010b0010210b90307aa62442c440030241170400607510496080d403003c1e076200d4400b016009110b100400144d4583c03003501c095100300400c0508003c014040240c60310358200940c2048005201c5006980c07010108450355003200030401181d0482060303560f1070742150001070361390000790810310000d110354203003080c41c04011500d0b0404000c5860b091045a40078011400041c0240001141020405014104894400b82c000301240716802c0000c0900840d940070b01904d803112414990413508035a000b0272014050b82c0286000c1505c4d03503034a03104030041c85110308a10304006840d00300304020761141c031192001402c03042022402c3c0c074080550340f41480720107041c42801e200405241414100180 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 663727814 1250 663726564 663726593
    0x402060405041509060803030105010206010b130e0c12070918060f0b0901210501031106070203070501050a030f021801020d022a0d051005040b01080a05060609181605040f020403 78
    0x4034002107004080306250f800c400540c01c0041d25038a8180c001c114000000050350403200242d0031612a6030302c5c0c0602c481c107801090030005018003004400e01070700b031544044983c81003401d052907042000b00000c1e9104500c0560740304010a00c10308041c01403000810b41c2e00c2082a00f10010b0250030b2501c1020b50070104544111020404040348120b2180c1c401c01081e012010800c100200403640700c641c0c08000c110030710044a0342c0c0310300c441482117824410140c5024540040c007804c01145044015a100e41c0000c5011041590350040b041c0342040c24400b0700803c6400c3d501c605441032482001a2800a4803404c0c081550300c1400c004104020012802c00502032520070942480031400101c0c0f0050f1446600900902a180807001c01904c0d96101602c514029490030100b642c0c5d405419403144031900010b0080c0e00107000240c0f4500740071410a030441000c1090764107035520360440509010100070040c030340580b501c4081001d4609802800c0b416400803400f1481d11346180d032544191003028 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 663729064 1250 663727814 663727819
    0x1090501140711030a021e1026190614090a270303150603051b040501020a021c020a06020d090905190c0c1e0203160803030403180815070e01080402060405 68
    0x1c906503d10b031024000382034210340c040d10190346140402c001d000c542d083d0284c404d00070603100c101e0300141c610030000004a162504045800700302d14188070100420300030f180c0030261200800f0640c0c0b608203440f40720004c0403400001d0342a4904801005400c00000c1c00c0c5403030711414441808000700901d0f10202c140000b00b090604412900c0c5000e80140000b040b581281d030200c03003070000d80d498064200d54031410624050354428404c032044001c05004d1402031030300690059020360014100700b0f00454444010b503003190416440c0382d00003081010310380c210300c0068000c80c042d00026608162400c018000c4c1c05421b011602d041c001210501c2c80754400042c078107032110402c0303001c280038400740c401580e000110506596032134a440000d61b030204008030300034443c80b030032142c01603003504500c0203807031a80020798a55191034030300702e4007050b02c0a041560140c0d404000900c240080010011400128040c1c10241c5000c0001804a0000c40c441a040c00486003c020050780c03044122002e880d000c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 663730314 1250 663729064 663729083
    0x90b090c1f0c0506010308030114180a1d060c280c0209040807061a100903080301030602460c0b07030e0c0301020d020408160b0909040f150605010905011407 69
    0x401d00304803560000400701400d14000c8100110501c28100000c40c140c905103c0c42300b000303018090500034800a80c140c00c0c0c40216001000c40c02c2584950442c0112058141c4c16500c0c034000004110300707082c800e0706c9000c1da544000030800c0984001c1400380c29041c1440346200d44902c01220040d00003d040341c00240304410a1001508101c0e5140c2902c500c01c2d0800010028148085406c1d00204040c0514a100f1012041d451300c840340b02e824104281ca41c003107240c0341144d195648080294200c00c45c0b808014841c1c0ca81d2504000e8a210882c9003480a158940344500058030b0700e014080035144c0030b0003001507021809001c02d00d60f22006070070041c01e14001500c15102140c0504014851072041e41c95400000d20400701942074000e0f009460030807040c1c0e024405020b891004000e414414950314103014081e040480c98441d00d05030b4414002c1c04200b0300c541d01c3c0d035610710300b035800d401c1e03100f129580ea8641800301c0e5a00c034045402502083c0ac01541201d606402c02c010f50007046401000d2001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 663731564 1250 663730314 663730369
    0x20a270e041e03081b0a1b170c0114010909051c02070f0308070b150306071409090103060f0c03021602040b03070803030c0d110f090105160c09090b090c 67
    0x41003a1030380c0a081c00c200328140742d50501d001001d0074070a440c0d02d00c0c9a0a0141c40c0c41813005440212440901d1549415a58000000380c0c2154044909001c2d03403080210504030095a11483c000c215143e10600000f07240001c01c061903240b0304040c0c11141d0030600e00610312000440014241c40b441c000215021106400510300324075007103a40c1c001840c82c0703500e0070001041103c50009422054810b4043d0415a0b4401c0b0105425003005800c0b0f0303605500c040041001c45000304094012040418241072030311840758041a050b00c0d0a0f8000c60343c040c0e0310307282c045003502580b01310f1511400c0c03468290f280082d18007254140c200c8000003c1e206a6454404050f299810800c41c001040908151f03600e0f490f042005018030380010f20f9403d441820701d002d15080c11201821611801c0b00303007960604201909e0300440726908801001c0c4010f4a5111a460214941242c014010090a82d01007a003010610b0700d07141c10f82015091030459801022500c041d6a91000c10b600d034200c0f509001c100c440c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 663732814 1250 663731564 663731573
    0xf0a0912032c0703020f0f0a0e070c051603030e090f06060d0608100c09060908030d1d010f06050f0a050901030b06060706050415050606070c0b0a030902060c01020a270e04 75
    0x1107960101c820100b945008115800b010a49004580c000c4a80031040d0340710005008411341c099001d00c3c0d000b1203c900501182c1c00e51145560050fa0a15141c84506040c1c2d072030034135241400190041c20b0248880800805602140c4072070941c00941d500005418143c0d0102e202e40070140283d0320440700403c492614400f1580110b0080c41c01404441c41504a080e0704402412240800d000103124101d020400e24040c548a100725422400207600d0f004800003c1c800428070034400c8a2903105c0d98030f440c89024024040c1c0c042000600030006031843c904010021001c40518116014020350141001a51f031444519811030307401004519403590390b200040c2e214032544000401c0140340c0410b00040c080c29205480c081c0319100c80801594840380d04020341c0b40140d0b40000c108a030402d000740241c0100c1000f42c0b80100345803c0224103403c403980094171907006201d1145050b90301282c09251031b0740c1701214000d400307200070003e404800313107060711450170b42580500c03202c44020201240400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 663734064 1250 663732814 663732851
    0x9011521140103081213110d140a0c0906080d0203041203020114040f0203060a020304050a1101020106051203030f280b01020a080c0105040b0702030a02031e0c03120f0a091203 77
    0x1032403988403a40d2203686130301d84405117030441c03505c901c182d09401000442288001070700c00405a000000240401854810022520150380d000c44511401c106400045c030820040400035030700c2410100c01303160800501c08201d0b0040e1380032802a40c4920700803450b01e60007108641c00d542035140f88002803003540c14140c1c0035012808400454680480800080c4005003070321221345032086050f20003544414051005a000588000d8025000b04c1d441078001104442d406811241c18000403c48a540f080060491702e40100e1012058100000308203203402c50f80b0f1580c0e07000155690b90b840d4508114990070540040003510303d040d42c5c0c2c3d40c44859450380200964074245503c40c01c0326a0362080041041d019140550341100c1185a01e0040b13103210b4004400c3d00c9030340032140e000f90700300984156010000d1901140100e00600d041101d00c41601c030a00040124040c091260349075818000c01585540c60001e0038000707040c3c40d10b108400081c20505005041603041d180c0815a00c800080c1ca50701c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 663735314 1250 663734064 663734081
    0x117060d080a0c030207090c050d021b06072613022403070507050d03060501140d090b0406020304050d09080715020102092101060b21180106030c0509011521 69
    0x1640030486100503036009031407001070f9200b6402da03031000340d4442d005000d03507404c03510703a90200341c0c14885a1a1503545a000c1c0041401243d0300c0d02d0707081c002c84032290404500381ea80038001402e103004a036203101d65000c1e40344003d82d18205e82541e450701c81c4060320b442e618610300910072100001340d8041d281c44500002440201082c80541d43d08103444054159441464201d40380d004480b184185a0700078401c20b4125041a1076459103002140c05c0e5004550009000e03000040e034034100c1c000440c0b0a030031428407480c820900140c0d00e00b4030741403040c03906c040003143c5030411580080a014210303021495104561032070390000e1030150803000c107074064018001801c1d0032950500200808460b02220718203406200310081000740e8440340f10b1405423090b40b0440343e1940c5078a003003603a52000c20344040c1d8071011417640484d00e8103076030050703500350b4205600940f040207801034248203502e80580702034010b0103500c8030103000e120100f01c0600307101a000070402d0b402e000d80d270402d1000c2c442c2e038105a41 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 663736564 1250 663735314 663735323
    0x190603110c15061810030b09030c07090b06040306020304081e0a0f0309020a0816090b01030209061c0225050d030507120903480c090209060706020a08090c09060117060d 74
    0x80d01d401208a02000146d10054035034240d0540881e0744424084100e582441d9017002038a000c40c20400210050480e00d1070454020000300800408201144003031400b03144503180c41650741481c41d2500051a00c0b954001480c102c08105054915030484484080380f6400e09001c16a81c1203030001512208559108144a0040081005510f03c1d01c2a07814251062904100030324141d90f4011004c83c01036004081d003080e4100603010358000d00201c80400c00061910151519110340081e160075022401c0034102c14010402c00810080309004900d26071041e4a01000140b03402c0307000505048a2501038104d80781d4501c2e00c10b060610411a5003100301e0031410031a82107040000314280d0359480c01114031400041d810f02100701c240011071341c204d107811a8500345158200304003200294003065500d540a03c080125100085040c00500100300b1075885d2151303186401c00d180c1c0c8c2029400c2030f049114240603004c1194580c1c00a00003540080034441a10b5a82d035403038089410b40419482c043c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 663737814 1250 663736564 663736609
    0x50d0f0609020d060b0a06031107020603040c05060c0d0f08040b01140103060b0c07290f030a0204050d080c06060405090d11030903060916081b1e190603110c1506 71
    0x213114643e0045c4a004006607401001217603507040850071601004070f0482149810003916003d864031030003035508140074030150052296600001603651b40905404140350300580f0a0b090300d40d40145d126595640786080010003890300d56502c01c02400140a03904440c855030100e170031540d129a06c00e9000e455510711495807000405150340c1c0c2c440152203240110094a540d91640c0004495844c20103000c0c14030403810440d41c03003031492154200030840d16810394280400076940da128031442c003105000d0480ba582c0c0ea896009001d042440c001c0c40c0328081c50904042c42100b450000325040303d05128504003d000400c425414114450800c1080d4140b080710280314012401054601e41161044c1c9003290181e81c99110f0b07500d4000283e504a0000104040070f60141803404001040e14200104c408111030040e0024040c103510400080c5809400d4009004840e01481b60140d001505c54100d0309000080841c0e6540d8a40c14100381c24003000400030a2080d124148400e007508220a101c5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 663739064 1250 663737814 663737839
    0x4140721081909170102460909050708070207211704050f0d050601120f0609050d230304080d1e0c080f040210080916230a050d0f060902 60
    0xb02100410b0040103064040c0907146099003038141b084030201840702084010495600040340456010080c04038800c40c044400d403e21100301d685ea4055094268542c625030701d0a04140a04450004119100780250341c020b01114503000940d0200316410307607218100d1b13405050341e51114040800d1004001e0010310050100689030500944184d807416141c3c2c440b00380e0803004200d410085130102408540064006000b40003201c5400b4403441e000d44850000d240d01580d45004880d090340d8180e83c00c1d000511410706040d44049482c0c110080c607107101441c0c4021400c2581c003031201600040240b01c000641a200b200315400100c280c44100c015181342e008104a580080c2c40b00707280810004ea244000508880c0d501c0f6010f50050350041d0520112020340001940c091001506c0000e9901c00ea605680710340c1e0000070114041c01c0301c01c900d820080020140c00d1000f684001400c6e00c80c6118810500440d1100c10b0070006680d08074114040c0070b41603040c00001004901c0c00a9040286080c2d003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 663740314 1250 663739064 663739067
    0x10c02010f0f06050108150433270203270304030b0c0f040b0304051f151203170a020f070b06090a06050307230315041407210819 57
    0x20044440030003401c2c450b2801ca08003100807600c071406480c0c0421041d80100320103450300c2802848040001d040001d5a85803060004043c8411400506a4402182e24204070400d20b0640300002d2510742c9030020000c0364034000355085145400c00107507030703a8003000045032128010710345055681d0905e030424017442030b03401c0d1a84903802804251500b420b0380000c181d400500d50304481503070440b00c0045041905020390f2003800d03840070300140c8461241c0044617507505044100c490703000e1840b440003c0d5110120200c002c00e06596801409204200d400750b1020a400051440307407624003400c00000d5548005100c40280510082c06100758408100182043f05600540380214000c07207256059030b03a24588441590144d014494140e0000c20b02000308045a0301d4200a1070500c402d089020031849001c44d14203051a001c03000c84059071030a20090200446100d00c4035000d15002c0d0034401c1c2409080700c41c0b004440d051060a034140e00d894428014204166420b1980ca40c125522040d0421030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 663741564 1250 663740314 663740321
    0x1605120d051e0910050a09060f020301050315151c0b0a0b0a1205120f0c0609060402041410150525110103090b040605060301020c100c09050904050316080c010c0201 72
    0x102c215454104482c000b45802a0003100b0b0310442c1860000d02d07140000c0003140000d07007000342003024103a4940081400291448c003c40350b6602d41014016103070361404080501c2c20001c00b030484240c0940100340184080b540e580c0e403620300e200362440082000030300024000600d40030301c0038100d14101d00900103084180d822020a0001c1207541c044816102c00c0c0c080000c00b0748580050841c0c6c400001300c400102c5a002406100c6400500300d801c042c440c1485e18107080c0e00303c4001c00d040c1c20010401c01145041d02c2401083c5405000306e00c420304e000c02203a075501001d0f00407404020112403021092500c01c0d8212008442c1c0400003152070564001d8180304c0040e000c81c120750707140483c020002154407a11035116855004114020355480c0c40d1a14001004050000c40c0c055401300a000c0e1411803c10000002d681107980019651070079850081040845070030251040e880c11081c000440c00000a40740504c8071011441c8152169280040052080f1100d09049500340502034618940642c0f = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 663742814 1250 663741564 663741571
    0x3060111030c0f06011430010609021201090204031a04081303050f0c030607050a0c050c04050106020a03081605071407030b0115120b0306041e3207050102031605120d05 74
    0x101110405d0341c0340c926076596203c003403000c0fa410400d41410310100194404207030044000580ea28460032180460490940703800b508a260348640010304400d2001015460600402c021841181005e0456907000740b4180000f50094074101a100030806120141c070232503078101080c0d0000e40e440c543d245482078885004001d50390041c0039040031141142004611310748160403640d1020b00c2c1075070002c03080d50344200d641c0301643c191103142c100c12003507100e52040303038040c08442d0000d1000c3c182c01c2c030380102001d10042c1003100c030504040d1803520140c0c0040c2660000741d405005103000c0c00c1d09400183c5002486d80c8003400118101c0000100b80d003c0440b014100c00295807088044050807242c03205651215404540603440900041e003c6146411380c2c0702103208001c1940681c102c10303210045840320070150010380003000035085c443d5489068441842500b03a42c081e150180c40c00e8000b039140e001e1503444440c80744220740d482c002c1010500080c0032020800b41b00b90748a4542040c030710010300040303 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 663744064 1250 663742814 663742843
    0x1b1212070806010e03101104090c050c070b0c030d050402010c0f110315010503070e0714040b18220e0c0a03060506040e0f030a0f05090409030c02030d1d0603060111030c 74
    0x1002c280c06500c246400c850400c005070017880281e480b59040b4008002541c0d17411030640c010300c03002c41c03111311a00980714189540d542d9030344c4032014170080900340032071f5502c5140700d0034041240354a085408804e0340ca030403403445e1707002400303a0311400143c40c80002c8040040c0080080ca004000700100d003110040460710950884000704029a02d14900d4042030041950650240e401006011a0702040715489140b500c2c0052a60001260741421a0455000b114800c0008200d01c400c8009140f409e9141b0001110b251400e070303650800f585442c88292102c0016191034014082c02e096007088a4041144064202884c0950b20708004004200035200780f4402d0f0300740703001c0384104000010100300080040000c1c42c50051692000e5414000c98402e400602c02c003070081c60b6150341c55104480e4560702179100c41381601318a204160400c05481201c20920480303c40318044040138103a224001c92003558070340d13640d40701c02c070069456010410018500c0d00c000500301c3c4050102184408044120 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 663745314 1250 663744064 663744077
    0xc0507120b04080304030201020909010e0f06010903080306011404080708060a05010905040819020a020d03110d0306180f0f05011e0e0708070c03030e030327030309031b121207 77
    0x3500319103030490040c054041e2221454101150108801d04001d5030400d00c68000145041640d4000c03900d144426400031403400e60700b0b020083c004030842c0c1e4880d8028003d103800a40b007410b644d9461410b02000c1c1c000390401046901c44061030460f6411107000c2c12003001145d42d519a55844190381d22000c07120440424100300c0001203400842c0502401141d10003405030802109070300d81d25440c00d10042c9a411413040b01e07100c0b40543c4072001c010b00b00711300030b5a40065405001705010311f00440040001c040501d040400c1001960340c403629420f0000703041000c01d07038400200c58000035001c00c041800c14203140070000910f80c1410101c44000c103100150b5502c0681e9100f40b0384c000780c1b40845201c004030740150006003020f8030800140350340702d11034140020040706151045145400413100380340248000303528071104c040000e1646001520050007145507181114040d038407405001d030183c40b182ca104180e4800000c00f0f02c403c2c01101c9940c4001a200c0c064081d018064900540c2e0000101d0007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 663746564 1250 663745314 663745319
    0xb0102010609020705120f091e040e0a0309051302070503160212030403021003020d09051b0102070e090a12051204030504030209091908030a09171305010203211305010c0c0507 77
    0x603a402039070313103258010024110303e44911901181e0755020100394640b2070400c000c00b5a10355110b40c11190900c0302e10050940d00304d10b040602080350203640903901c1541c01200c2d4100000ea21119800a83c1c600355100319040304001100f90203405a004010414000800c4200200d4941079084020714001c450080401d4901d0480d11b07100d11803408080c0d04051079110f15000d160181d00184802000e801c1c1c00240310034240c8a041c00d245406403400407048002c1e00c2d0711102d6a04008000c0a0003410000300e00c01e0411925056540d4110703800100304400740c407900002d0030b004138255000d034245079840c0405450f01d8900101b079035000c0d02049125102c03c0c4042101440300040e80544610800b040007021400c688070202c25410050680c1c41494440c0707407030700c00943c0e4203105000210044050544485c040040001c00040640201e411944140480004503503a0503040328108640810f0f050350340c49000ca9031403020f81076507003d001907003050244004954400c044503d194029400c1d90101c41c0c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 663747814 1250 663746564 663746579
    0x140c0a0518060603130203010207150605040c0e0d050102070b070f021c0206040609050c04020d06030203060108210c070b0313050d180e1f08070314011407030e0709020301090b01020106 81
    0x18000c07400ca1100003001030006801d42001d0000310780005d1310b40820080d40383c842d030004c0d0030b903444004100e0b244028149660302e01c60050240d1005330000302d500380080310384504024603119031056041d02c41c05c0c010181b202400400c0d41281e40e10340c3c01c61540310803031404c0c0c4409080210440c511500600c41c140c9a9510b03080c81c09034a040140f840e6002e0100364540fa29030a010741440030003622503015480c1d09038203aa4444c402081352804104010070701303910b180105400c1c120168042d00b902d8000c020481504001121096201c0d0344041c4000e8548010f130410505d80601034008081204c0e0007c1440407103548994030002e414490b10848403030034210340b000c40f8900003940c0003841140c0301c1c443c10300400910011581d171201000100301101c441540101007082400e074880140341c1c01c90740c018000d000d81840b03284102040000203201070030b9025030030030407030f80c00030112000c150360b460f400b8504190500818000300480c540030754072541c458035120014911103260901541c40d0841c00900744 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 663749064 1250 663747814 663747829
    0x60e150301091218090e0a0212070302060f03092805011a09010b0d020f03010603021b030f03131e0311011a0604090c1407080403030314061f020109140c0a05 69
    0x259842561015240002030090303c411a100419500070081202c022a4114651048501060b1031b0f0000b05116804ca0040c40001c103108442540d107900681e03018400341c2c0328401210080da030100009039503540c50181c2c45051601c54005000c04085200424030030a031a40008581c0b140250001c04c94600800b021803110311200c2c83d090303007224500004021503d4440302502c5440d841c0c55001d45800b95005006205034400d0704602c020a50118100320945c4841d60311141d00c40710b40c00214680390450b404c130019404004c240d01071010150880780204404102c008120340030f60041024a4440313880c0290040032480050080ca61a20340c080180b44c00b01040d0160300040680902c1ca42410a01d450b03000d80b501d208440c2c14400180c06011f1386e8001c04c401080c9070f6026000c1c06803a1400e510b4010183c0f07404000b031074500c1400742c05210b00d40c2da807904503a1101135100020361007511040300c01c0e409011003540107000c54030085808c00ea0100c01040010001004550f0000100d440300104000d8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 663750314 1250 663749064 663749081
    0x507150b1216090209010c050a262712030d0603120518120109080301060c06060509040218040c0518040b0a020f0703030510170c030d0914090613060e150301 69
    0x40c840022010014a14990f0045c520550b041c0741208030500d0366100d661070498480070841d4100800240058800051451390194903090500e01c0d20781898180e201e05021111000031030341d03c02501101505907581c030b00a001600052050320703203955401c0000c00062006100941c0c103607036a0440f100d4000c0c420411540c40e640c0b803200201811003079205000005101050703402145d03603518049030202c3c07244405140280100c0d514080b08500c240f60400c10b43d24294070550080303455506020050f903550a64286442072201d459009a4817814042208405c0b41c0c00150080c000c01d1070f20142c034180b01c2286220b01c0c0034088840681e100d08030700000300d108003c51031255a009014080009110782c200e560407109000402c0316240d00d0704801a420120400203240710b0b40055502c00007420140000e0b00c560745281448080e0300d15180311142d400c120303000700c640f0622418000070340603075030f09c1280660002d00d200100140c1e41c9521010300506001d4034034280d80c0788201e02040c0d80d4901401410113 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 663751564 1250 663750314 663750343
    0xb030108100221040f2001271a040302040506100806060f1908070e1032131a130905040302031215100302130e04030507150b12 56
    0x40030700d03108010000940204049a18040f01e1840801000c0c1c0e0000c201070040f402100602c041d40f00903c0c1000f0341c00702c1b44034062441e401d000104d20300360382c0010045481040c00340c902a0035541c0d11050f041791404603004011106100e80040c201040d600f0054001e9034400d07142008180c461104110024900800320b03800101401d00094a41c2000303006001c20640340c408243c200164480c803021840f01030001d100c001548041000005507101200a4880c50181c070040010710054000400000503100501d41c00b10300ca80203600c031146101c00a01003c5609100103454080618450b504400d40740b05406448801c24500c0c440e411140c1c048451084070010300070400b81c40c004014001d010014401d90650200344415555101d401e0340040c810360101c507400c0840a495010003aa11102240710301c00c1620622070100010180701e500c0082e10a041102151a40c031481c04480c00e00c0b50000c014680c0d48441079145020646810103d4507200445401301c04801c140d6030389a84014074600040b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 663752814 1250 663751564 663751573
    0x30c21040524040603200c0c010305060d1b0e060108131e0b04050a02031c0e09090a02060705010507090b07030503161808060406050f0108060430080a060b030108 71
    0xa807034010601901c500707207900c0031500c11062044120a41e0041d134044e00101e529043d00c0000314880c4800c044200044054070b07410580380e601c00310750391085c4080d01c0c0d062695840210302c040e0340d503800c071500c110350240690100c0c0d1001e07001c0001d02c2c0320910401c01e4502d04500130a910350300441c0000d01c02c55090442054100542e140c4001a4060000401040a44082d40c0002c1020740742c207a445203000d84020907202a407881818602084081c4039080c20555800407960681e12980c400044a0200e0f014812903d602007800e09203482d103070b8001c0d489840011624104201900818401c1c0c0c402c0e02d880e40a40d41c0d4a1410f21144100c07080100010410030001f499015a00035000c568401480c0c03102c002c0f44040c02d03803aa08205500802000c2e4400c501b08410402c150144c260301c41000c1e91103944952514a0f00c580c0c03110081c100412103901240c03a182d054084040ca04400040c2c00004030070740e40f40a101070001002030380c0c001e0b4884e08100010440d02d42c881c040780e040f160310b00c0042 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 663754064 1250 663752814 663752819
    0x90a0b0112021809041101110c0a1202030312160e01142a0f0705040b060c06190b0a060e190311100203090d0302161208040e1512030c2104 61
    0x2007000703521107480c0c0404944050103801107038a6010203144038502c100c01e000c45820b60701001401d4000c0c5000c00d44110307800b002d00004a1b8542e94280400c55018041180d100e42103480040d0840c01444204200380032440100803a202401c03880c030004941c2600c5644040c550304004481842e826081892080c008101d0b41002c12004200d01c900030b92610350340c01b01e12902205460038240c0e0030f038614140343d004d003100340458a0144216460300008440503464010080d4140780c460000500f4114a15a000171854480006403c512200900100300800c0303540c448002074840000840b40500541c68045a001c070b619621119409480c0c200000b201011a0201008a840781c50701c1c599007180014408041d00740c80300e40315940d02d14860f4014003110005034404440124942d13010407540740c02400107501048110382150269071231701c111186c0b1590b500010380031200300b14654a030044c0d07054076021445d0a02001501260540e082030ba08141308100d6401e203041c0840b43c4030411484200000c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 663755314 1250 663754064 663754097
    0xc1226040201180905090c0a030507061110050c1b0307020102060f0c0d0f02040608070212031303050403081b120a0207142106071b0f060902031f0b090a0b01 69
    0x1540c030520500d07144000a40c0c80d031507903c007400154840b030542c6071103400b48501c0d51014085c0403250041514a00342c10b52031134594a030b0380c281034803c034028803101134071203c0000000e10401c080c45070301d801d043c041410300f1081200300380d01c0002a2903410300c01c3d108040300c1407408011030b24000c1d0140c2c02801c881d01c1e400c5100050440185c2505072000e03040140351225000c0d030088400004003040f006071074901e07146002d401514000d02c20800c5400c01103142c159240c180060300e4002202d4966150032072098541900c0354032803900701070501c81001c00c09604d01c2d4825080c138140c1001c8803060b40c00340348504d49031841d5400303151050005608a403500b0b006000c8500d003034010841c8010b00810280c900140d0141031144140d942443c0c1d500100e01700924a40c0240d8610302c0c0000070035000b82d1030001c90311a00020842813500426003a22134039041d05555080040c1c100344014100c1c0000000180f0540400800c0c001d030016006072010000150200e065110741c20000768103840c0d444825843d5601e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 663756564 1250 663755314 663755387
    0xc030603152a0504090506060c070308030603120d020c0d05090a0b1c0e0a1118010603090609050601082407020309060c16060e040f150b0a090909030c12 67
    0xe01a00401c00e126004009502c0490b040e01a080e240c95070f5a4070750800c5d0f01d039020303601c006214a0252404000385981ca000015101d03080361b4111060035245c0d03e41100080c241904d001038110710750740c08940500c44d5151039008050215030700781101e410001c8501d043d602c80c080c14100e180d10080d22181080b951040c840100903a40160009152698204031581c04403002c1c0c1e1203c0d88140d100094507c02c014042c21001d203500000c85a81540010408140f640580140503205c02c164681ea180c101700401900112003540d0700034259034196844070303500e50340c8100c4190613039039101c0075641c4d44c2d01442414501500801443e4082d501d0030311460203004440d1310107955408144200d000d070282e502001001e49000c0c006544da4968020100d0040005440700041000c41e01441c28622140200c1c421031000c00704e880003802103031200003881054135a6003940c1d00c0350a64508060407042003562102c04030740031360b22409507112174400c20b8008407500c02c1c48040101c0f50044c001c0000d80003040001c1c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 663757814 1250 663756564 663756581
    0x90519080706020f2a1c0c051b030c1905040510080102040b091807020a03140f0d15060504270e01020714060a09020d060507030216050c040c03060315 66
    0x103682403504415a403680204ea11407030346554546000b05240840c101c0d084121a00c0e4005e4030680b210040000d50041d403500c840c1400d500c0311201c4808485502d0f0b0080070a05941a0008182c5500210f240040f080c0f43c0c03c1440150311a015440c00d10045192440111450030b18958003074a440d800c04090000038400a0010b12840201c8507001032140003d000030f00182442c00c0201c1e032154000e1040c0f014524607030803043c04c2803c3d40000c0104081d40014022049070b0980342500160203850036054680c4100c0030800e03203008001485540007132581d0840c60032502d02c26651040d19546100444003806035008a41c601c8401d17a428840858a420032401e10f8240207a00045c0071250503882c608aa0140c0c5007201e5411a5003200c0030841e0040c803805a014540754400c4c41403900c03d0f400101121480240102170035a1440841c00d9103220351b040d10140c0e00d095500044694590070b1a9684409400b140303803040d0b0400500c024030911038005c41040300e502001d00000c1001004128000d8a03819 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 663759064 1250 663757814 663757823
    0x1401090b1b04121203061a07060b040509060615090303040f08070801020322050313080a02130b180a0b12060f0c040f181e060e0903030403051c060e16030c03090519 72
    0x342c0700400c183c0c0d8042041f0320a00000b01c0081d555110b20324000b010b8800031028644124603040801910300d0000c0344940c0e000760100e8850241050441c042d84a60150103a07072500f51102040115052948038a280140c9402e44101d4030740a40c2c070600e007405e034801142e400c0b0040506c10418800010080c841d001d4003031084003070740d08009118280704140142607102800076841460142c040d41400c104214460b10b10000c107012407a60307440800d911040070b0071210400145903000980c11000c030b90142146480003004c07a03503580c02000c1010f545020030759518076544c028a01103150510340e982100c0440c1e010910b1401e0851a0052103800c20410340c4901d890300f51680541c804404ca480790840440703400082c00100345042010362410500010695081a4010401d100103c3d4104055aa1130840d40c07942003207415103001c0c1c10004d0540c6078800c0c44408080818444555410030001c0b00c0d10f00d2070380e010800c00340806002c4050300c01408002d0301540204801d0f01c0048282e0b030310034085a014 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 663760314 1250 663759064 663759071
    0x21e09011b050f01020d020301090f14150a17010501180b0321120106050a0e060c0721150218010e010e01120605030a060b0f01050a08131401090b1b04121203 69
    0xb0040d00c90b080e40d0006c6100d03018142c5c0000107002040c01c900c01c03440303511402c1c0c0702045011104c0e1540180703460b01800410780355201f0365001030075035505a42003010380822244040c5030307183e0301542c40c061300c420f0150b0742e541420813002445c50b08962103940314102000300100003208044540c440c4040016012600c41c0000700010034101c2400e007074079070007002e0b15512140da80c001c0410007041006030040080c441c010800096220380c400044440948003c6c411401e20003104004540203520701140003440a902c82c6050118080181d029052402500720303d40e042c068554011100b41d4040030302c1c20b001c50f6250031602c405510075842880e007600e407828001189912040000e00d000e1520000b22201c1c2c0d01d40c01d00061038100b16171124044102030800340d044c402c1c2c0322000f03440b01c4802860040c40140080706801400100c81c6039054180703425008000300e03101da007029035006404403440c1010030b00158216000b0301400041710f04898441c0c90f45000c10300c55640d0304604041812000007010344 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 663761564 1250 663760314 663760333
    0x6060c11012a050604020a1a030c1303120e010305100e0712150e06030f030c03030c09150a03020c06011a0706390e010e1c020310020d021e09011b05 65
    0x4102c05280ea140504014090b41c40c0510420650364400c0d0000528408440790250b84030800d103051b00d03003281e4040e00a50f142d28002c03e01c1e0740b42c420b0381d81c00600315443c3da510300d108440d002003e440881600307907814880ca541d941c10841da0340d80944912290305040400007404240f04030198102110048030120380340b06161300300010203500b90800b411103001002840b64520f010400c200b009402800a581800481c8004136203d0200410341c0e404520b0006510a05070389100001c800325400221864903000d801c1402002504030900340341c1079204d45c10010032201841079040105040c10034100d40307000403698448000d4a01182c42281548898909001202210412031240400c41d4200b240d8141c0c69140100380d017414568203418401d002600380b9841d100e101700302c4140c02d0780a854000c540f1081c1b011030310700f401282c440c0101e40e1000c81d003941c140c0700640050401c106062201d903080b4092404500702071007141c80c00c0f030100b0b1042c000e120000450600302d001c064010801d442c208030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 663762814 1250 663761564 663761627
    0x60503011508010e0a0b0118270302101413060905010603030807090f0e0610110609030a0e030127020a030b04060c1d090411061b030d06060c1101 64
    0x15044850a02045079101d800d009220b000d1040442410400004204004043d01d030780055000601507400d10b88101d40190101d1030300c5400c9a4041c050b058840034103000c010280c00d162030140c2c1407c1340140240c000001c0b00041034040c4d0105d00711410380d9600070391510000b821000c42a0b04048038815114940380c801324400f131240c04c000350302945604ca802d1414042c0240b03040c82075000325402e400314050510085c500d40d2100d07a8840c200766400740c80d40c82d1102050f9005003010381700d08098825401041020013010015200164903512041e81c140c040404140c00d03101c4a6103a191100074125071270000100428440c062140064a000c0f00303503481c0c0e141c68010301c004641c1981e10f151a002c840404580c8120702c0303101c144c00710f40c0b402c2d800164500062103a01d4040c00140081440340c0c0c40e01c2150f95172030120703002c912203030201156014401104580300c1d0000d001200310985003070000210b540c0541d007840d40195004484000680d031a000641d11102c42880550701c0a0000c0c80031540300c1c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 663764064 1250 663762814 663762821
    0x120f02160524030412140307050a031116050708010c1d0d03180b1207050403051b041e09110d0c0b0a0207090612050c1005090d080c031b060a0b060906090406050301 72
    0x80703009041401e140c001c04503014107521070100345a88000c001f0410484040e5000341074a8000f00c592a0120b100041006d206004d80130340c08070078a068410f101e01d0010040d0004102c011196144000e00c50f44131113450070b0b46c01d03e04085aa058155a0701c002e980c2502d8284203241c2a24400e083c900045a21910104040c0180c3c4d081804000400540d070254801085034040e4810740c00d2074520310309030441d501c0c0c94440400403102845880800003e042c1c0e6030350341d00180da40070100007403900c10303062103281e180c06401da0603400d54884c40c04441400040c2012403001c0d558030b4100c0c0707001c0215490320b00d0044482d806000361301c0450041c1100418184658080d2034010199100d03030700681e40c940e0a0860412511100c03541c0309002c1e60382040c03411038216055906501c1c0440f0144600b642908051045104180a008090000040289204007801040d03911500148112001903440c0e02c6107c00b195400526031341d200b00c040c0494061858407034020204100086e20100f8115030b1103022070b094 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 663765314 1250 663764064 663764071
    0xc0a1502120c0a02100515010c0f06050702011505030a0b06010f02070e010308091807141608030403030603171317011503060606141c02031b0403120f0216052403 71
    0x42c290000340f08042c007541000941602c83c01e1100410150038001c03d01038964016000ca24140301d0b0580c90b10040c00703545030810b50410740081041c0800c0c500a03000a000706507088003002d05429280c404580c608001034a8100b4503400000c518142d1241c1e00190b0f001ca00e0041400110f12450340c0c04205094180c4846009600ca402400d03241d00d80c240030002400014108402c15041c040104406290300440c07a155000350424010b55800c002d03d07040d1103555a03108050001c9400105000400d54154840b0382160301441407404191000d4808400340d2080c80f21401700049804400d20407003030004000c03012078299000010b80300005403000524911180e106440d81544c5420800145400003030404460380340e05500c0703190000741d800d02e0b03040d64050310341400d1640d80440081e940154800300b0030b5025204a202e0b5480e076540345003401075407500210144c0007071058184210000c3c00001c250705621460790b44542c0c0c080c140014803511a6507220529403032081120712280c2042d044006601 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 663766564 1250 663765314 663765331
    0x31407060908070210030b0109060f0c020a0e0603010632011e022b020307080d0212090106030204061205060f041506030506100b25080405060414010e01050c0a150212 73
    0x443d012940100001419212240c03818942081d04503040c580c2d00030000d5090354070a04046554400000c0c045881c000c50b068000e401c030200b1400400c0815000504500c120b00440c020300100d82c031601800300c4401d0345900c40d076030384c070140f5081030b01c8508011076030102c41c8040c58025000300c9104d1100c01c01c40d01da1480c100c00340c1c0061100c1078043d050041c0f08016101e218040400c2c46480c00c000a56a1241900c090103240c004030302402d015606030100c410491800780340b0300490034030301078640c0240f0703071480100c3c8524509a030028003440b443c00713401c2d00d05800c00081d00584e550340469684585c1c005004440440c0307104044008500da81c031503040503501400003001980341c02860f1040322080354001c60580281844844405c03403840900d010b1225001200408001851a00490307600cc0c4e0f03044194020b20118011480324001070311002071039800d07624045032100b1140152281d01c035000c0603840640150131036501107006500c0c0e100034920007000052804980c11004801c2120aa03044d14 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 663767814 1250 663766564 663766567
    0x803060312070b1006020610260307030f030e071406070302010f1113080a2109080109030c02040f06050603010b090312030403082509150512010303050a18080a031407060908 76
    0xc1a43e12180d04c0a030440d03000400c0c46041ca2020050744945600c650b1030075050520803d0302c144ca404a018035100e500c0d4044a88650f03061074058024015003485000103031800700014184440020120112813180302c1c0961a02c5249051100503484800140c040d59200d50f01900ba10345688582d04011515142c440d4452000c2200d00120142907404490f0701e5020302e2600001c682c03031603000a41c00704d021100720078107940440d090390850071172f03401161075500e031111039410f050b00920300303082c510710884003000900c8015280008581290041341c1e08403500740018030100e90610014407103507400602311505281e41c00802c3c2500e5104503400c6000036940f6080c48028902d2200760301c1685c500350425480d41c0340d9001c4c0108040864400c9990140801c184640024043d404654041c0c0c4110702184043da103d0030003519541c441e801540010b500c421003203443c9941250000240d69080c8080c2a039080e058030100c5020040f01c0310826400800c010800c00910b1500c0b6000080d0300c5005c205 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 663769064 1250 663767814 663767821
    0x70f0804051008010803031501020f15250c060c0309140106060e030a05060f071704140c030c090f0403050c10060620150901062303010c05090d0803060312070b 70
    0x1c801104100681c2440f90610062143c03080200540b940701d0034080380045441007550041b1301c2d204000c4410000780c0111400c0c000c1d81c090668009106200510300c3d2000540f20030303801656103c080b20410b00145c0c0800524000486940100c20b0f00305e02442c02280701035280d280c2d19248001c50801d154242e560f145c1c00c00c051078100c0f080c2d00c07040c081200030b004507025603110281caa820041c58003804019240c0000d0f1079600a20000c80314010560b80c5088928192a108450304110344a0342214468032151092a01c2c0000342004082c0001d042c0c1c00590300c03940d080a00143e009013049046c0f00b414088a041c3c4003080110703a200245141c07000c030301d151034100042c00005079080e03041c603a00744221940507800000925607001940e80c4118803925541e48514074014915900002d046c0d01d130840706020b60455080100400f240124020403c241104806407aa446904c85881c0c2095485c80c2c1103004c01c5c040310107141d1120025045d00d4469200d840e5680d100d5100c0c1c081120440c00140030b0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 663770314 1250 663769064 663769069
    0x50a0e120702092d09011b030203040b0c1e0c0c04020f0a090b090a03030c02030f03160c05030d170c040510050301170106080c100e03150105011706060d0f02070f080405 74
    0x250065034050f242c510300c1d038500140001400c04d03445200142440c0344040307a192002544510020000c041015210000c10213004002c0c2d4010780b020f503030106c1000301040050395074400302c41e290380a61003000d1405d03607104201c48094015035450184ca000306001c500d81e41d00e40340014000b48015070062543d84895000207091000134be005040111414000801c1da0f803107620000c41500d40600304106071080c80d10000b4900703800c01030702604038000407130300c10001069a100003415501c101d01c0408031075117540c185650b942481d4890400a140f0102c0c60001a658003141c1c1c2d004a03101d0602481c040c7c441300031611804804002c1c138000386002004001c080e12466076580e40401a0000f030055a240ca901a603452104040441c0309040103801940c2d8580112a402055007001d0b0a4071411840c0d56401d01c200303802403040601003450400c400b80148010311a10f40b280000400250038412802e60840051000080340b0380307510f0b420012880446c0e5042c070000c42d00361151003040c1d52982030106 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 663771564 1250 663770314 663770329
    0x30e0a031806030203010315020d0213170706210e0f01110d0b03010902010e10090503070e06032b0503181605040f0e0a020909070b071a070c08030604050a0e120702 72
    0x200e0782c00c0500c14001480003e900f01e229a894070120700001d0b80b1515680001d400a200701742507550080340034100015080080204a2148103149056a00d0785a07169803e9132507859504e41e8100042408060070300c014190b910103090403900c03404540c040a0354404040c01c4480d01c4181c112011804039890095200700d024181c2000c40540080c05081015400070b03014402c00b2840c148509115800c0d411030900c20460480140f02c02811110f820380d60f107400b02d00902082e45c60301c0c001c0c0680c40d84112200d00300358240200f00141103000052458841c01110b2642001c1c102505101492414203040c0d80100040106501410b0720501454600006c1002b1503003021602c429207420800082680c400118070320380c040d40c040d920034040341e03148481c80341003c010390000c03084000003080306000d009100c4140a0240c1c504022282d81e51a100c00549503030b212500020704c21602040010145e0909801032500001d0485021555184091f419820107000c61407202c04400085222020f41c6000745 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 663772814 1250 663771564 663771569
    0x91507120c20100f02030903070315050a0b060a0e0402120906100f080d0e240403110a12020f040e06130203070b030f13080c0d0c0203062410030e0a0318 67
    0x41d21680321841c0808652a100300c80c0c3c4070300038000042c0e44504564001e0003190f12404d0024152a0700e0764491402c4403450440700c240508084c5030000040c620311007441032081c01031000340210b0804c22400340898881e40d5201070305070816020f004541200300b00001c09400349402074060503407440c2492410302e003000b0795400080d102e2142541040280c50100d840e240c3c146103031a00b6004d40c0c0885d004a41c00f5001c250b01218540c6082a2403030b20301101002410503203108014076208107000008004c40c2a43e02d0040114550001c1c2d2040300601d804680ca0104040c060004900655411403e600303000049441007001c1a0382c1071010308500c0c0030b001e59009054403100103420760420700455003134200f00610a6010b0407400c801d00003440300d00ca0035500e401c0b21800845510813400c07000144000c0b0940d8040780a07100da4008200d2242d810070a545500006c41c03084941d50750322000304805070241080b01424166505200500e841d0309016000030035000ba00d07041205030058025502030101903 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 663774064 1250 663772814 663772853
    0x1005220524030a030e0f06070c03080a02061b04091806060e0a0c051315051209100c02011811040b130911010c030206040615050d1511070305091507120c 67
    0x1800b0b1080001d0b04440d00e1721124101759030400501150034045641441040005005489800400070030001580000d01c840d150700c2c0e007514025104c6080d01120464115462030301081d061005004071412a8400140c0b08000c06150810816039245e1a00701c400f00c1e000746141d02c1401c42081120aa240124803000820345411841d0240d48055070000c006a401501d207a1542982800d80c0d04c1d1141050b103600325240343d0417440c80e00f464054140c0d20001004000c01040c10010340300412030061040f1807411711a00d441c0f0740420241d958500d040003407503e10590199a54074500074503110281048842d101c20b01c00003c409085e401c200e030388a03000d0080d05041000d107036441c0002075130100c4d1a88c0c00541c041c2c4003003181e9010074050603800d401c40d00040d4128400032001000d200042050106000c001d003000c00140705000000700c00341c400c010001e80841d00c20400100310307040c0b44d100c2041444030511644e0511800e0780e6100e0384400c1c0c000000c1c0015040030700318420301030134100484045001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 663775314 1250 663774064 663774073
    0x20108070e1c051f090b0a09051009020102030408070902091507020d080304080d0e0303040201030609110a110703050102120907052205090a23010e06100522052403 72
    0x22000050204078030442c8082e141c1e80c0300c6081c8010400708101c00100103400144030a58030b10b00d69801d1008058a00c003e44020791800b0124400780e13620b10071010303501e402401030503041414001321805440c1d4071100b24114403040000280e0840207010480c0500309100001d40c0e182d005000300300308800c0300e0001401108081202c000185c1d9003040080c00700e64092400d58a0b655181004505401101a000c0e00c10341441070210660801100451084c0e100340ca0400c00036031100c2501040783c0321b116103a08140030030441c00040b1030050b0b03036044a80041c60220b0300c525031280c2d907440c2681c0090004500340c020940501081e81014018540a03000554035255003680080d00d0b18003550314610b042031010760394400708500754814881c8110300c90308211a29450b040082076503800b000c043d5003100c110b500e407400d0314008510121b04903014a500c21500b1010f2403e0078100806000c2c90400c400f800c1035064480038400d58140215403044d281e01e038841c280d078285041411003401106d4550f9200e13070803 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 663776564 1250 663775314 663775337
    0x313060b120304270c08060d0602040503030304120f020703050d0509151206150307020601060c210203030a060f0308070219091104030b130209151c050c031219083102010807 76
    0x281b155815034001000c5482481105560030268020b220795040150540800070800040c06058560300700c00f5411551001034400c5514000c0f0380b20f05e0f86000040c10364001503a01c240446c403480183c000756000a000d01c02024080219204503070103265580380690b40001081500e01e0101c12040d48401e503d04110701c1d51828803002500c81105015030814051103280c54800e012149242e480321a00c80000c0b2550700ca48020003a59030740003110f08501e0b87c1c2c201040803481c0f80c500c440d48000c50303034004003080c18078409900f0002d2031120000804a098400700c2d0018841c2428007548100050060046560382c1c2181016060300c1001002d0509503e9128001001619031010b5a580708105010b0300c00481c50030000180400b0052801c6245007140c00e02d441e0034024046140d60070020100c00b00c030191080b802a0910394010780d070042c0e50544114580741c000c01e00070140e480d4402100e03503007042c40c44440c3c03280800c583c070961940111590f103580440704550700035519582103105410580d02000307 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 663777814 1250 663776564 663776567
    0xa0b0705120a0915020c0106180c020c040c030e06040f0c090525050915030910050c030a0e0a02060408031207020303090d051602040207080c060109020313060b120304270c 75
    0x20406801c2d03103003083d51554018144100c4003200d84401c4503d64040d5079448002074102d029010501803a5103010303c2c1500600b40180758424181003841603001303400170010b036604220040075840d490b0000c1c5138940f00f0084502e5024000da5224a201d0440e0040082584c01e05450707205890b0411000030307140009105600328000301840d0300d0340c010004100104071507a07040f24503000d0703100c140350805c501b1075015882504407030245100e104030108032040d80071010310402c203540d8141c6100362046400c0001c02c0ea140c10503046144110079000403030b0f210302c0039907020034001da04c20382c0103006c00d0b0008584414141c19040505070070039036920041d815414100b0390151147c441c41082e03000d124001940b40c00c0e41d242c484058100d40c0c0c0040085464101c68180001035034409010340c159030103000004142003105200b500c1c0103c0c00186000300700e05080d0344e910000c080d40f048855100540005170b90b4486010001000540905010110000c00f800e4030440740c1caa004120b03500030380c00c09070081c203140d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 663779064 1250 663777814 663777847
    0x13061d0a030c06030b0328050708030a02070503011103061c14060106050c010e010501380403080a0824090402041404110f030307021302090613060302071203090b0106031a030a050a0b0705 82
    0x40c000c004507010280c40308c0c500307680740100a5100c20580e00004c02d0401580b90045600001c0b1003042c0c00134082c40c80c03030031640040f500c030489902d44d00000324204c903800c5807141c40c100340e840d62140d232200102d000490340e09445d0034000d9100740300250f030000c1e061035601d40a01910801218900090046504080220600d034548622038241c071035080c000da214014050403080305000705109019951520307400d242c04558058440440461003220218010902c000201d02c007080e000700e100c0c18980001c104028460700c0152017660300c82e45413000c503003018a80c6064580142d00c1600592100050305080c014001d803031030030b000d22981003882918090389403a40006403440c1503000040e507076210000010902e00516800c0380c12102081ca000c42c421b40c1507802411840c0c0200310440d80c880710b5480403000d90f080410004c08814112004110b01c60207900540581805105c0000e20000c458000c81d1401000102c02c0d102980040903003014496465240c940100040c60903c0c5443c5c0d00700340c0941c02 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 663780314 1250 663779064 663779113
    0x6010504050604060306090b0109200f1305190e010b0f0d0f06080f030706110703020a06110d020d020d050a0b1c0302150c0a030501060513061d0a030c06030b03 70
    0x34a8551000442c1907030f5540c4082c01840c0d1000041100740090305144001c000c0901401008910f45080d807079044204500b400769041102c0c0b032151814000454024494001880d0240340074035499010a89540b80600401d020031089200ca0714540303028080300d19aa01a4082c0c0100e01d010480361482503010011203446420380040401c1039050b0050340c00c0240016030003509203003d5400580f0030030801200810006004400601c0350342140c1010751050b00c00d40d40018050f0780a042810f0000b6021340003905d0106041e402503003006111000315041c0e912825071005400e0b80003038041c020700c110b4410550043c080343d1003004081c82d214040381d1145840031300c900b1071020707032550002010f201304902c88102c004410700105500b8074a880010b513400900144011034109400400e400788190240d581c0e90940c2c000c51036402d881e288060b0740799039511215500e1106615813400715525880c00c404010340c0314401c003412813407900900171308130303a400c00f001840f0703411000c1c0d038941c0201d112080d03461 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 663781564 1250 663780314 663780319
    0x2010504061b090e0c12160e0a0b070327080a0308130308041407091505030c010c0302030f0f0706020408070503100513030806010c0b07021e07030b011707030b0901051806040302060105 81
    0x50f0302e03080e010700f1755030003031070307105440c4007020f104000120702c0100302c003540c0d06c0e40c545806118403090b0080040341c1e5803a01078500e0440f130500c00100030038482d6402d2501040c82c071860b030750401400300020003036910076041a1081c0d800350a0b42410140e2003040d207507102c2c4160805440b9826141c1d4010a0211b01904c003a00e49071030a542000e50b0081446000b00034010810104101140b0314050000d0360b28512804c1c1c4a4041e00100100e13550050100195456140c0c0c00366150003c60218800540c002d154055401b17a014440340000070b2051000b400034010031001411994500303800c2518148040c0503044070281030100f44080624000a1a411380e035142c1401c44190f955900100c5071040940e101421644d03001e0284182d032600868102443c4542440b0250781d0a07214588503900c40c0071344401461000c03604e0042000300482a80c0028140450040e20221a547e4440e08a512000d0701c0400c12a5074440c20300140e050110308540000742d0580c064541481d040d2800794482005100d82c90 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 663782814 1250 663781564 663781589
    0x15030216061e050403091d1b030711070f090c1418010e04181e02010c0b090304230910050904030305042102010b030c0604051f0c1202010504061b09 65
    0x2069014060050303502c00200c032810800707440c05040040620490348030700b00041d400c006040c50320741040c0746114030440e801c80840c1c0b62102c03100c21454803503000400300d004105a5103100c0c0d001050a100c2c0300000c1c850f030710076984001d00300b4440c07a08079001100c0d900d06208100950301d18002429080d51841400c44441d00c4000111100603900700b00c00d6124240d01a240814203405c40400040d61241c2c2c501404420614490b0300d481c1400d020b82004020780485c40c107080c43d00010381900601d40d80030040c8421f030b034282a0380700c82200c1d482540c2060b0400580c1c1d603100084990402004040d0b102c103030f642070407141624000c081040100302504c0907042548500005003030101c0816000c0b005000f8081c4a0580207417200d00900134034442c0155842030085000b200b456240207403d03501981c03401002007581d04030215100c0d00740d6171080e0000013031080811070b1201051010380513200004054001185a1a00d468081c04841d42c40ba481090324000110310440281d008003088103031352907411400c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 663784064 1250 663782814 663782831
    0xe07050304030207050d05010c031109060702130608010e0304450608070b0903060f01140d060b0301090f031106010b0406030c14040f030c0e010e060409020111161503021606 76
    0x104c0c104285a041582c0080e6032414000c1080301c1548480e180d4803242d5401c0221850910482005108480040350301440601262015142658004207824522400010700030350300c46e40903003903801e8001100c9186d000031500300200c90143d040c2e238802d060070341c91584018903111155071808841027038070825580d1001034400c814100303501800c00b0b0301102c030459201e5580c50502107202e03804407007210702074010b007804210000300b4004001d050f1100d40f141e5014024504c3d0510403a4031403804142c1d05540c5800c0320b281103440c02c2c403030f4400d43e81c010540c0740e136055098240a4441c051000c8071a006903c1000104156035030041520181ea81d989008258940d03e14012507110410514401d0051000140000d40303480c00400790080781c5c0f10f800700780781a9644000340f0307858100920501c1c56a4402d0f02c00524289040e80c0320401c8507205040600101050302881032070301c480d007403028005095851041c40324000750503824004245919080d4501079103040556441402c150300180240d4951069 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 663785314 1250 663784064 663784067
    0xb0703030b22060f0504061a07030504090e060a0516023309010203011a1903020a0c1a071b0218060409240c110312092a12070e0705030403 61
    0x52420b41081250944480c262009610080c000c5101e60044144082800283c81c100340c0a0740040b900c0682180c2d139000d00c0445002c40700da105040417810044200804500c005840c0701d8003420b085070000074015803924182080071100085c1c0448218112240e40d04543c0c2d9000800040b440d02600c5900e0400a1501940c0b043e0384203443d0510020044600300036586405601560403600c022400640001a854584c0d405200b100e40f03240400300d00c095480d0320940030390010300f5641301f14a040c4940e88078545400c00d90b40035050014408002e22414803c184d680080f0000781aa42d5010f103903101055580000d42041b460400d4040701e05038200010b01c00e50700ca034007071000c240c2c0000d409401c21040c0c000000c000301000b624401110b16040d8424416441144206002100b4030020351620680c1700c4d481c0d0050304002c1c00802603114510124075000d20541c84481e0710f003411016000307005010300c20000b06005c0c00101c1c00c11541300590070444800381c06640ca03000303103250a03c01e03582e4a030b5080 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 663786564 1250 663785314 663785329
    0xa0e010608030705100c14030c0c2a010e0a151202070b04030807020607170606031801020a03090b0f090c0d08090915010818121809011715010b0703030b 67
    0x1410300e07400042200c4044c01404112508040400c5204120154078a542550f13005c484081201d0411001c0c00040c2d000d408050043c40f0407004401219120500c0da50881740c1480040c41c8103042c00aa81c1081000c0d5800c0001c0f032501260840c0c072070030298100b6401441c842c0040500c0c0d42004250302d0380344007610300c030783c100c80f0019084a01d1051074a401d04015001840641d0004014400d050000f03101a110b103e0ba02248000ca01c0100002d45454081003015000030742082c8001c00828429540c03240c3c00d00c0200350502d41c640b000704100c805401c041410300030080291141c0100310003000b20925020400c0588408200e5080d04200b45605043c0520b018144042c0d03002600390061200c0e800b82b40c4141e4141c48026038414186a840443c0d0b076841c1079603403640300d00799881041c44550740e45e141ca000d005010b405c3c5107c140701150210008000d000b084e4481c1c40407805603902c4044451060000c030100b00002d4503421034551501403203417098412848050b040541e9440309484070307a10382c0c5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 663787814 1250 663786564 663786569
    0x1502090604122904080712020c13050612031804090f0b0103060207170a23071b060207050a0311010302070c0e0a0c1d030613060b0a08030408120405090a0e0106 70
    0x441c004080c408624100d4825111204401d0300040c2c00c290070f841c410003400c60309101e95440b12171181070665942e03420300c1002080a50710254010a00b00c12000c0d00c3c0d41c01c0900c6040d14000020800d414400140000305c0c600b0341008069400420914a000358220b030115445d04c0d00384c4c0d000503050b00c2d604081402e0f803107800780100701069040000040c49103a802a03c2c420303000c0d00004080440700c1030042c42500c212121000030600c602a0081d0400c0c018500020741d040c81000b11346000401d80d0b80c0711182001c04a84480c2210400d014010300b5410003228003d020151641d0f80c0f540c0c1981c854071401a0820362841c100b41d0001612010000d80e600c40400901084a407059a0700705510400058001c00e640ba50001e5420000100080380360b20200c500c803c0d000e4054603040c2c07501c2160f4040520000400c4d20b0643d15400f080f601d039260f194041004040f1b030780c00f440e103a600300b800e4103043c200d000c5140d41800c1400c0c001800a40d890b03503030441d007260800340f0004500c0c1050165034094501036 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 663789064 1250 663787814 663787829
    0x1c021204030501050403080a0515220c03060e2802090102031318050f06010c02040b0f0d03021c050f2506020a030914060705160507080618060f041502090604 69
    0x20500000b08141504602d001e90701c01e4130342d080165206e03c3d5490445a0841c0e80c46907044484041c40001c5c1081c45081a800c00440e070700048001220307106605841241071290300080e51031404110b030201054005070415656039250a40a15480c07001303545d103851485a071041c6500041e19202030b802002191048032100c02d40f0700c550b681d83e10040c1c41840d000ba2032022101c2c1440300040340a038484513020310481058442c40c800120540900000b021140b0710710790001c3e00309412005d03541e10010b20344941d81c0b20354010304410400914058142c420a0640b00c14008180002d41b4525450406d1b50030220010303102400030b8100c3d900e00005960359410140c2a288001190131a0b0765168100708505c070f000b03d40b80d0b0030441c40003200725510b000c1150f040340080d5040c031810300c00400014038130616038000e02c1100c4002d030b202c104041c00c045040e1142071016a800300d44250204040c005076502c41d02c03046000c221844e080c0c440c80f81903005091401c1d4481d07170024141b0b01540d605000d45020341800d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 663790314 1250 663789064 663789067
    0x2030309151c05070206130c060e0103090807060b01110604111314190b0306060a060c1a07080403090504090b0703240b0706050903040f09020f0912061014031c0212 72
    0x1c2100400101404c0d148a0300500990000880400e1700f61440701c03140707900041c1601544c0c50213034220759600c11542c00a0405445130000004036407002c0c06800514041c610000e284020800050201c001c402c012015903000b1408000105007070090000b805002a602c01e049051240e00d907000410004d03240c40b6a981001c410f110b0901c0c000b9611801c840c103502d01c2007003d901c260b820036548120466900c1c0d4400450501400708074461000038850134881c041403880042442c0040800041c111810400150b1250401090660042c030342001060262001c0141d540745480e0ba400071b540c0149203100349500d0700e400c0c00c0d035502d5134400c2c0c01d01454048081c400b030a4075520407a046900141c0107540d00b60406c3d001c1004468080200c0d4100c90346501502c440601c0c003c03595003e504042d02540b0358071401d009604994550000801c1c2160400b0301603d428506412503180780c0340e107508103680d4000f4813107852440d500c00258070030002400301512941c001030200d080349000078000b10041401d00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 663791564 1250 663790314 663790357
    0x50f0d23091255020a0b030a0b0406210f0213060303080a14010501050403060c0905090705072001120f0b0d03050712022b14040f090b030a0203030915 66
    0x2090300f41c80040d5000c00101c600030380200303081407802d180d05040c914a8869040000f440001d9140400b01451026114039501a075800d6051081c2d04100d400c110266240d06182d401441c151103650043c2c000100c0e500240e20941c04ac0da5121200450018000009030400c3d01c29940d0303c45400c00740340742a40041c000c05489107030003402e030b100584c1e81d81200380c1016007042e40502e02142c5203041e5079041e910f490030300d072540e120344001d489519080c3c800d00c51091000f040c50b803509800715214a00a4039000d940c0c072618581100d020700340c500c01202c0f070007512401c01485c2ea0b103c2c4003e00d0b1170325980c0c00803c1c840030305400380c230050411500c050b40c40201d41c004042019041000313899058010001c3d21154183c012081c0c0c7c03240d0b40c000100e074030540c021604d070041c4018601508644542c0340340c40300240001d0340d60040305900503003040c064000c180008102c2d01c20580503654514205030050b106c00170496020130764174002c2014040c07003560071403002c12510301d110090702c1c20084603840409030b205 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 663792814 1250 663791564 663791593
    0x11070b180f030f01020c12031339030317220c080f01150609080a020108071b06021b0c0607020d2906010e0609030a12090909050f0d230912 61
    0x1448440004414024500740d071043c5c2a4002c180c0384100319140025049c1492550780c8004c09180494070045860502550581000e10900c01c6401817a03680c130321044c240c11410040d0540ea080c040101a4840d014100800080068012951a0b04c2c60254040c1c0d40036a1030030000d0b80145400c2541c84e03200e403100342c0340c00781415001220340ca161040940d1083d500d401048400c0d1006000d07880c04e0354004800c040055118802c1154010300c0e914081c401c641e0100d0031500300240c4040c056032013035000300f00c80d00500d981000c2d6481860380040100383d00c2c40000c000c11103034010043d0180c807401c1041410307004d000300602c412081750308114000c03d00ca080c140c96088001d02c10b90b48a80010508200f5403000d0070000101c4a910710300074006e1001c1c02030747c1c0e110000410340d2102e41d02004054000021000214050504503030b2041c00589605009142e002e49005000301c0094200702c8240c00f00c080c42110900d50340d442084803001103540e9131610020400c0381c500c2805002107842104c000c0480b00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 663794064 1250 663792814 663792817
    0x2006162102071b0b03220204021b1606051c0b040207080f030a110c150411060a050c1005010f062601090c08091c0e151911070b180f030f0102 62
    0x380c0340d450035883c0c035145801c0f030501003198506080008460186050f201b0f031070041c200c2c90700c000d1025291211150040640a100301c5845120340d11010200c04811018100e140152095203002400d00342c0d002c954203852031286256880301c50b912025104184c4840d01146c0100b0b801055841e55111044804140b03580110754010046141c03450682ca14610b41e000c03a042c5641d4a4018421840b9045441014660103070080781c6028801c0a8401d0030b8850501800d4480960b0321140c3d1204001c0c030080782400a040683c8424901e0b1500502c2030980382d0314640165401480e0500c03400c1ca003184c0f405a0b00542400c09a052200c0200000b4524042e4000c0e01c00f54405558064040d12410541e6540d00211b241640d0380342e513128070f404030f4940b2070900c4414a150050804400f002c14030360100311603101112100036860001140500710b80c0204d50b61026120b00b10050104600d8510500c0460044940c4201a074a140f42c5c1250117a41d0a00360780c025400003010780f04901510050b60703000307 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 663795314 1250 663794064 663794093
    0x20090604030c0f06180b0a0305060a081207150b09040f050f01050a0c0f03140123120303040c080d05030103060f0e010e0d0f031406210d200616210207 66
    0x1072204038010385103038021811714111400d10a00a0070030403081016005000300800607a0800c65030100080d00940c200300c609404e070151003e0984d82c0d00141011458091013510450100d410070b8116030454540311142c0c0da1040e084141681c0307801c3c09180c520b05200e08150044015801c1109202c8010039603400440c2d1103481d500c0c0d00c1d442644c02034080c1d0648e80000194101c0c401118010414813182120020000d0004020700541f600d0810019615142103040180c1a9002004110802882080e588064442c03180200000300b00c001e0010310502c01408002c00854440101c62101e503682c2d0070000c00c4800d50740c0240542c06605021640e5001244880307400150001409120a8021320030f004034081c003040b100d1030075610142800b0b1211210002640005440452110064010310410040d0b05e1607a1b01d018035000c1040d03014003054814402200c11760014401d0140d2000381c0b40c0318143c41d050a003020041684404070602062001205810b045400010614100401562902c11 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 663796564 1250 663795314 663795317
    0x8010501120c0207030813080102040b03150a0e06130b183702130b0c0708010506010302120a09020613060905130b1305060409060603121220090604030c0f06 69
    0x680700c060200740d0040d64051440352001d40c00c4018180086814500200202110304050111003981c90b14500e00f2a07000e680003250b8404048184100314400114045800c5030807941c0725102400c00503000d0084a014041c14403504840ca101440f1003031b6500200800d440042501600c1e86d40c551100e403500c0f00807581082c03451600111592038201c4003036283c054210645403a80c492203005030b110000c0d0710080d00300c002c4c85004d4800090134a1110000c150b1044a14060444c15140400403425500e018060a05040c0188514980c1130494003c0941c400004080890600214000b040152080d41c141198403501140c000c079186810062210488000399464542d080c5a00d400f40100d444100c016540036074450b000050503465030b0410fa0300004002c3c00041d00c0039040d510001251116403040f110f107400d00301006400c5070010800c4000c149040300600162400d505020000a55000c0b11445a4404250408691158410744016661080c15642240c0e155407031040184c003140702d07100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 663797814 1250 663796564 663796577
    0xd15031e020a0906080a0303110d0915110906030610090302030607052d1b240f071e0f1701120b070315060f02010b032a030f0c0114071208010501 64
    0x103c43d69a07110704c0702140c8600c8054080d0140715502100901410760000c01c1c00305040c4200024030040d4170a8800c0b0500c40c02481014001400d440d030f00783c0b540c04809524061042c4201c201c1903d40300100d0303501200883d110900040043c0007514090381c99000130750035110b8101041181034000000300303100c0c0c803c545c00819080050b20341214900a02a80d520560401d120049030403080d0910b00a241c48014113480700c120b50140e15450081032000a4000308050005000240002000254002c0181c3ca44809054100d00e02c0320341051803c14801c080003c2d541031009003910a4035140a24610a5521724103035944d0b500103039007000e200c0c0043d143d900b46000481c00040c02440380210409076418800001854030400340d41810030225414155500c901001d5035698082c40040401e94518070f180f81c0c4c50040c40001003080882c1a803080c0a0390018410604040002516000080c42441c0c01d0b42c0d103a203a80307071602060040441c0180780c030b20742550202840d608100c1082c1030320b40070b03038490 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 663799064 1250 663797814 663797819
    0x614010f050a03020d03110f0a050714030105060d02010e150d0f110a02060a0519090c06030608010e0606061312050c1e0d020d03140f0c07120302030d15031e020a 71
    0x21420b0212032100035481084601c1c0c2a002a020f011002011040c0c1c000350380d0f81d6190005458280050a40202e4050304200c03024000d02e000050054001e1070150020440b92401c0000b18115042c2d4200281c14030062a448196540e00d0340c2c09a01485a0101010384130088090318030003801d881030305a00d0050603c2e034044400c6035403c0607160358510319802406c16485075148a401444080c2900043c41d00740e80d1030501c1035500740540f650f8540b1449400007043d2034140c0050032517140350021205c0381d0402d084a10003041c00142c01e40c12081c12100244e9544040700e0000000096610601107130400c1280041449800700c1d0003514142c054640c80403400840f000540076000c0c1216281e031000914003a05c0c0075003030500c50203524a02c039003041c1440c41281c01c00c031075990304940b0400c0401103000696141364101400b980c401003044d44820140e075585c50781c2c00380d242c0c018080301d844070a565034007000050030120340c90401140c102141095a1101680c0031180d40e0342980c3c00d1703001e42c2900c41c00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 663800314 1250 663799064 663799069
    0x105030d1205070210090f060b0f1e0f15190c0b040b062e0e0301060e0c0c0c060a0f030b100206061002100606090302030f030a050d090f0614010f05 65
    0x110160100315600d009441c03808103240d100070312010b40502c045100350240c41445031290f1041400460084840340103408152900c40d0a4410108100d801075082850326446521850b07403001f04d5501400000003504411000301c3d4010340490348042c0e200300303800840360b603101e0544018502141a000f07064444100180107540c00c0b200500001d01840c24000003801180400f102e10750403180c01040108400c030441e40e0500c06a4101e9203000c80c0d02d410310114129a03401041c00c0f84907010560082c0701140c5000705070360504070010700003440070000044180300c2090074059200b04800040c0001d44403074900100400c1c5101c210305010129241ca10b8100b40d40c50210940b1038440b610360700030500d0742d0f645014040e01d8008481031740d09500c143ea6280140514501520001c0c24183d42c808400c10b295004040c0340a0426194071000d40040090850142e03100080b44c1c80110440c901140301600ca180000000018034009081d042c070303090f207034006103083d800032a04a81e8800b1700603031010b85a404 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 663801564 1250 663800314 663800323
    0x10021308010b1005031302120c030c030f1b01020703060203161d03100b0109091812181e030b0a05011e080705130e030304050a02041b050d0f181505010503 68
    0x440395804a9803c081554491080e0001c40d482601e41d0010106d4105030340c041901d08041901d0807030290060700c50302078107003020003103452140c2c0304800030000003035581d082a85034000006125550001c0c49810780f1607034004c2001d0b100441d4407007811940c1c0e26000714012000354032180030b64005175800440c1d1040300502410034a501400034040d00c0c918030a028000300900e01d0782407050500841000003d00d501440c070808002c4500300c2c090601036915450180c8003640e202640005018083c09201c0714084160902c409650110340c0c6912110803075803243c1140300c032a80c0012704c0503010000300041d85401d504180e0403503004084c58030300c0c000820140d69004040b40250551507008001c10040c07403410390709000c0b202206080010f8404e20500d002821584103e4082e911544001000c0d01141098490820131400c1d100c408400c2e5481d400c001406445031840100300a625003c420220f441a580518850403040152045002c510700c2c02c0c0c6544229040c0d1616124503060000895050104 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 663802814 1250 663801564 663801581
    0x1031805060a05061c05100f02070c090f1d16051f03020304020607050d05130b03060a0b18090115023706090602041409070903020915121002130801 65
    0x30080c081d140c1e00c2d40400002440010845035021103410220031000500b4510300300640d01840103003030740820103403a0a003900c004041951086104110031408200000901c20649800c284085040d1a031342240354082c0595640103500403a060b00e00f0306062000180d040e070302c9020380c00070380e03101c9994a0070442e02e10601050310000e01164129052060701c2540190ba000d803000f804242496640d840b4189808100150b000218200040c6001000c2d68200150002c2c544403034898174602d0840c02080f0a007000384a1045520004030b0701320240300c280411701d44001030281030050300d50713503c60082028020300b0710050058024003403440301015060000c01c51591841c50366000101b170084610020f00785a0300d05490303050f9103984520006500740010001080011680c1070340018090800807083c5005d0205030a201c2c40e0281000142c0758144100d60002e20400015822400c0e24089844003660b494a00303a1400381c1580b00710010101e9010340f140300e0f4840802810b240c0c580310840d080701e1307492 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 663804064 1250 663802814 663802823
    0x3010b0c1b03061f12050c1c0507090f140c041a03060d08070c0906060306060e06160b09160b03070e0312030f270d0806031204030609050c130506010318 67
    0x40e030b07030000da000d032500300744c84a68008070015074074510511040300d03840b001c80d0350390016a040038075450300e001030035100c9140d0034807101421410350b16070796100960b1089102041e103912059a060324580d01824600f0b040030303014506803030301c01c02a0b0300300e074018003540500118226106885030414001e4030f202c0c142c003a12421aa1005859400c050b81155504540a90440c40f01094580e107502961000300503580b0045401e50a0000143c1514035000d0024011311b02444500f070a1000800c1010500c0d410002c0e186541d1915000c1078117005a5500690040a044600080b0000c0000081d8425241a070710301000b48000400c1686503801e842d00901900b609001003101521074031041078120a0012644019003103540c2c9810903003211912517007035a00010310007080035401000150340301000318054203002078803280315a6140687d0001a10f00e03136a0b800d02d070301080303400c000107400e50340014520b1071444051600e04003d4217044442ca800281001c5008544003402c0d0b100d4461305030320 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 663805314 1250 663804064 663804073
    0x609020c10021602030f0a0309270e0c0d03080a0501090216110d170d0606020102090607030315050a0f0915060e01080a060312170f060a03020d08090603010b0c1b03 72
    0x24400248041d401c01c1d000c1d000d42d1803c1c00f82c500d00582c1d080045480c0c02d180c440140101201c07600300074001c546681d2011002442e030020268940c00c40100c200c03460920444006000c1c039002251a107006c3c0d414404640003d4411500e406040d003140f42a44140c08048003401940e885500f90340690142e0840c60305041004181c000008809603048822143c0140005540c068607450356940c8a08815002510f10b40004d035100344085180a42005070034640000d61038802d404021a9070b61144403000ba0070140d0310100d1101040591203040020034005010711141ca4842d2000e0425401900ca030384d0f0054604950107421400c21103801c42101c5590700c3e441c084222030f070015290f120000b01056215544c2c4d250103c002003c1c120607000403c1582d0b9044010749074000c0c04881c4000c05400011219451001c0040542e5078106000603a0f90640f8070a4003103005180c969002e018500c000c0d58010300110022a050850304081d2003618050002c48081c41c1380201038412224030130314030301c1d00b43d0803 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 663806564 1250 663805314 663805333
    0xc0a21020904111305060909150114221b0212030402040209120109140d1d122e050a0203040c05150906070c0f0f06020304031e020d0f03030609020c 65
    0x40c040364950b07025020b03c2d44071440b440401e00041d04020700007034480b51965228180710244c14120142d541c400c5690300102029020120740703a80028051044c1061405d400e031440c00587c07501c80340c41c1524080300748d250f41198280000c980140c019040800292403403d081500b00d6072000500d03055a00c0d0540c281d9246454940900010b540b0542040b07401c01111043c6a030088001d00c03481a50b03074003552801d045c1402c840c1105082c51000390300b0a0802100284410300654078528404110f841241c05845000700b500d02141058ad040391400981480e0319101c0d1201c002141120303940448038070040005944e40c9150f0300c228001520042c0c07140800400c24481d03401c2041c0040f0300020604000303810711007280c0000f0069030000c0006c5409644040f020010890042c952101901c0401030451044e824079900075524096484040d0605200262030188680c02110300f400f410b0300907004460051490425080ea000011b808400092802c6400503502120340b081c3c030007005061014241020 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 663807814 1250 663806564 663806569
    0x80306090709031b14150409052508070f2c011e03060e060301050103030c111f0804050c06090d0807080f13030c0b090a0312200c0a2102 60
    0xc001031803441448032407100880401d086040d640b0484245080441c0c14a0528452041d540c9032262003a0182e82c40038001021441c0f00c030252015502001d5000945a40fa1042d842ca0009510880c50034241c0f464144c20100d0380c40100300d032003441243c60f030300142000c001d4220791151030000c8610700c1202d00504403000c980a000041e191070014980740103c03808081d0722401a000b1f503103415000c00da031510b003040a002207070589907000c40c1c1140200040e41c51a00c0242c614814400001c00316202a140b00c147d591700e40142c2c841208282c0303031070a884180d8240c0500304e0402564143c03001d1044000f01121490100100c0e1201e00340540110711450069803500500d80090b20f08545502041c07080b198000d03503040140c949a20218bd0501041c1d245007009901e0403015004034000340010003d0191a0302c0c1e19011900300c0c1c0d40468000309480e01e64504507440040001c803601810315400b60000301c0380c400104003401c560100c6d68404c034290303525142d90000a61400c900003001d6403010036005072 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 663809064 1250 663807814 663807829
    0x8031b190b09100c0e03070f030c0b07080c07091e0b0102030406200d170901060302091b0c010f1d030306100e2106011802120103140c03010e0a1a0103080306 69
    0x325030340c110f07910a40a5000d0b0002c1e560600c20100005041d01d11102840c03900304a0100140140c100105d1400c0c11600ca01103075100a028028009400140350000c01031a2404c80e0886410075065590f003a07181c441107005000308200e0081c00c1c1e04800600b40105c46684100c0344000301c140c0003503141c20300d420410780301880710ba05103e25040d041940081002e070244100c1400703540741e9407443c00800c222200640d031540c01500702d49031a85000c60600040c0c6561070035507040300c07415103585200659400d248507184100140c080055080c00c10340010084c05400400d03852548018010410344181c0c007290f60317800101c034040e030310240d40125610840d000c0c0c010401f241d2406421040d0610700050010b14041c1e034054003050b01e0740800c00401c25154010502031144a003090258900310600c84e050050b214103001c041d060700c40200c86090a07280400c00c1d101000d201400a2041c00101c4081c29150072015005940c0070b4058203a4424840b448a081c0d41620343c000b8449082d074440c140ae01610 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 663810314 1250 663809064 663809071
    0xb0a05040e160e04120807050306061303120e1005120a15030c03030c06180f020f01210b0907030504020a0e040519110307050a120305070807020a08031b190b 69
    0x740c05260161010b81c0486006000509120942100c10b414586028250000c20000101c1000000741c2400031040d801000c60f50890b100720b85140c4c5511301c04011b240b003509141d100801610a490ba0020f44980120301c170781ea019070441c2c1c445110100800280d0700d51140311440c0124000100c001242c1d01300719444812200c0c08860f84000341074590395048145030003604143d0101f01c138a0208001c00010b406010f2001030503031142c4c03e00544036681d10b51100c1c2100c600070f1240682010344034143c0d1003406141420038464116802540300403c072000142181c0081d0341c0140242000550003c1c040d003c0c241c0078540c0a42003c68403840c00c03544022103100a0411074042c080c80c00280c060190a8440452150040901801400e492400c25180059590200380124200a0f080043c0264008240360f00340e01424050368032507640ca000c070402d10a0304002544a8801400418000b90010240c07410007172004116001000d64100c455542041c1c0000749810091035501400040d80c800c22a0341 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 663811564 1250 663810314 663810341
    0x10503070c0f06020405040c02100510050f22020307172a0a0516030f020616081902090d06051e0910020904020d0f050907240f021e030a080108010b0a0504 68
    0x8291b1200c0008069480056200006138021316201c00d00c40d040744281c6801640c24601038150781d00c0c00f000f0503850040107002c1c40c820103800028079813245e03050350800340c0680705c003404550b00c1c42c3c155800360010102c409001c0030382c0304200010b085600d9040000003d0030028411902c81414000002c1d0540e10003038000d0108081440511040000206100b041c0d078461780350414208080c24000345032003001032282020f100003090342c44016420902d501c1e04003044503112034850718821030100103845104078258000407804180380601c94158041e90080d000504608200d820700805040705800660720310529400071440d108403100140e00504809034054000750600344c03054011021a0361040c042082d1544803802c11803a5002882403101074070702105810180800281d080f100c400c5040d41410921414090100c441c90007041040025178140c80c0c1455030080490781961290401a050310114140701c00104510380180600100d900c009003030700c41c1880c5000e013040054143d4204084 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 663812814 1250 663811564 663811567
    0x141f021305120f060a0f0e030702010e060a0917150c0a021c030b060c06160212040905040507050a0b041e1409100512060415020310060c0204021201081b010503070c0f0602 75
    0x19003283c000c0c8842413107642060780001d10b02c0d0000c0b0a100c25510442c3c0075901c42e4004000c1200142e03008160380760b420303006680141d19030f8000041075441001540204180e442400d4401210b100b0004180c182c0c01c00b403989005203030b201d5080c5030f0a24001c01c1c41c2030016070003004070101021821445108038440c1d500e00454242511000305d41c1551010f0707840c49040d0401410800608101d14406030102218030003049040e240ca5180101801079004500c03d41d500c810114042c024200b0101c400780c5070091040002e640d644280130309540c001d1160407003445910207041490403039510010308882c046c030305801d00b00e0128001c00c06020300081214a140c459040c012409403a10f8840c0f0401c001000000c00e26801c0504001240100c4000e0320301d0035078010030412100c01081e00c12481240e8090800a00700c68452001602a0080340c00314600465031f00000070b01c0d00301c0050038210040751034141c4044070801000440707440c441210444045940410110006825a1090464030b030113602d005 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 663814064 1250 663812814 663812833
    0x8061c0305090a12170f0d0203060d02040c09090c022407020f0f0109030311030108030a080a0b0d0b07110f0618070305060702010207150605090c070f141f02130512 72
    0x34811660700c1d081044a985010000b104200031700701d0f010311003914a54030b103007410010f00d003000245c0b041030780d84180300f500400880e54a03240c2c0070003124416402031041c0041220218000c4c403110703841c03040c66082800c0c943c19408603400400c15004003144503070002c1d03842caa805c80f640244000035020804503c00d410310300c940001c1c01c0c070a40707201d894084008900055981401415128a2141c83e08590010401000399034000011241100d243e82070994a5556200d00040208806800282c03c940410681310412110109603481a0031603120b00c1c40001d20a200d00ba9104214000000d02e5440030010440e80c100901c4a0840540a0421103241032307120340e143c07800c0070010346000300541c1d0049500b80400200d42c7c0d041c5d18020074440d0812100d86071a0000c5c2e1014006400c0c00b404020001d100b400740440306803500c4209800c60840c800340500e058640c0c0e96540c01c620003c40000b003410214401910900803100070701c0d0310300100e0410900f08410480000300804d5150351900c109940c0c1e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 663815314 1250 663814064 663814069
    0x6090e0402062b1e0e03040e040503040b07050607110a2006040b040b2a0a0303091a04050c0112140c0309030c15150103020c1b0f031e070608061c030509 67
    0x10702c0f1400a2042e0007141603020590076030307640c81c004020000031505050300d07054250380010984045410441d4950326a84032410058118403a40e0080105000009145070030700000181c42d42c080e0300705544a40131a006100026125000144010940300d1120408407580f003014500f008444401400305140c0b5544081407601f503481079110030442480443c1070002000d002c21041c0070343c0451540b4840010440503000d03100c0e082508010103155030392100400740008079503030180f1070f61502d44a061a08207410031941d03854108007110f0002e400e07404548a100307424041c4190740c14841d0b0a0b0281c80d1201d145820f41c5410003840c1403181d03c8144a1500e2504c1e08118154030710040724251005030038180714003000100002c403540e052500400180c0241140003964400508002901000c0d0760003010010f44114852611654144500c0c00000070a00d0681d480d018854200c2c1d0407158040d58a03401925000011511203500c44d4250003065510481d00c0c8110310951700c2443e2252410030b10400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 663816564 1250 663815314 663815377
    0x27010f1d0604050618030610050a1809081b12090604060809010f09140c0102070b0405060a030b09150f0d0b060d050703051504030809010e060612211306090e040206 72
    0x55060312424031155525401d003400300d48c1c2c000284502c55204c440c07c203030105130740c1c90213445181c810108140b407080c4d2294403540700000ca168060011035541d0101c1020709840340c60001e058010b809202592800848180120307020780c8405409142414a0004299208070303004103015030954803900301000c4c100c454450107208500c0f03001080c02074103a0101440c07a046184000310b0540d03001103401e0003941900703819102218001c0f44c2460f80c40210200c200d001c1c25081030348a4100c0042420b02103100e04401c04050140c105403a03c00c41c001c0c0c082e0400500043c0020040d090040c4071020542d03a0401605603101d4030f004070b040f00da000f0394940d2070601e0000348440d070340e20f5504078806100070075911404c2e4581040c803c100a0240c1041810001d440c0d05000c0d011078881d891000480192010a0100150000000d4644030421080c0c03c2c6800e505e900060501c1490300d2010004206240a03c603c2c606a512010540004d50340b59800c1c058568044400c419901d9540c0440306600d800d0141c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 663817814 1250 663816564 663816577
    0xf14100917100e030705061303080a24080304140402120423070306090b060603040c060509030f01060b181c060203150d0f0302010c030908070b07110327010f1d06040506 74
    0x3d005581e644070701d003000390400c42c01809944140e08120300e0740c0d01180e40400c0164001642c0c0000058407601444e8490100611001c0319030b20018420000070f5101c004009001207440e00345100071108480d00c20441203103d0038036041c64040705400441c0108004907554204180d420000c0700c0f82c14599003e4a2034109694002c58800f40ca40b20160108207541030700a41040007560010f0540c101581d84a456200b540108410401c1c046140720066074100002c20031114640020041247c9414120fa001e500402407143c543d06100360400f03143c01d1510400c0d000b0300d07035044251310b882c0c810b07170310a406903101a00080f40fa01070030180d007000303994101c030848503688203420300e5030400c00310714019007550b0214042e03a0038103103030010300380c0840c0409040b60401030384000042c840303940e500f5081c0c031814a003103a008007a200c0450803640c01d141c45d600651094005181d0000e5200c04203004507042e91066000200042c120740fa03106070701c0e90390000c90620102c0100407900b443d031500089120b94001a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 663819064 1250 663817814 663817841
    0x1506160606031a091903021e07080c0102060f0106080c04090f15140d03080901090605340504060f0306180b09010503150403050a03090b010f1410091710 67
    0x49030204100f000c0b5000c100d2041d510003400c2002450001c091540311520080b18107017644020310000c003010b00c203220b1000c42c1288100d07110402c10880302c500790303070b48120700560203503101c1e42c07084e0354071507000051003403107a1039034070003030ba1240c3c240642124502c0c006044445520424080842c03c200e85004100c0d520303030700810010b030f000e419200702c00060025600035030031406885100c4200e80c0300c403000700d05072940600741402107803608158240105410030020b0700c041d10701011711040160980100110550500c00040c030084081d1072012440418007075100820020041001454020781a241d4010001e09000507040e0380c407508106401c64060170503642a6607032407594464540a545a40585400d5000b0701980d0300c1c0c500c4440355030401070406020700801080c0214164866000003803c0c99010019040559550041c040c0340d510501030181d051682122080450a06121040d48051280d4545201518011443c40d940d40080003642480c0900040c40d03800c1480d0b8091035140d18041c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 663820314 1250 663819064 663819071
    0x3070b0708060109050a0b0a140c1c0905011e120f0203190605060708030910020c330604020d0b0d2102030325410901050315061606 58
    0x3110080c11000d005208074140043c130340c0103000640b03e4090316401d1301d984213415590303450b20b0b100682e8480c010340d070f00d869043d0002510018410300400d480d80d40501d2298407540c03d280d04081030f0f171422180d006442c0001c48000007500030032000c0d0030011501d82c060410480042801c0c400106642083d403034140090f80001c08d01850040c40f81815904114105040200a05020002c2d8061003001805032541d18040089044d441003480a89008400c140b170455880d800261241d4861600484e0348002c408400c030b500c40c202c0313900c0702001c0707000001503403050155071030808020003504410008025140c2e52403d050680d01e80c19044072000303000d08501d48080c254803098000c2400064201c404640052041c41300700c03011010400010081c80351444444030115400b11003c00c01c8105c485c90604034a040c0c420414411840401c035407000c0c41070b0b801d144c10741a4410080b40300b02108140010f50800c00030300311800c10f90b02400481d500410161410694070b000181e031158032002620a01d56 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 663821564 1250 663820314 663820321
    0xd0c090f090e0c0d050c0a0f0603050c030105030a06050405010e151008011e0e01020f0f21071b0f0c061d01020627100e0705091f05012003070b 63
    0x240d054800008006141051252201c0e000440d038451240000d80c60040180a1400c2c1c00c0140610408224400c046c0c440410aa603525424000720498807800d4082490302c4003259079030130503404032810303a04d0150040c07988081c240e4481000f0a00100700352125540c83c0c0da2070401401c20b01142081100000590066040218502c100003225511403000c6a1500c49101210b81300c0f25200c07003010800410000e401c404801401f400ba10856024410742b240008d500e4090540790f1b80507005a07601c07420144840e0160503a460301c01c4805403a1030300840c500300904000d81c1d036000340008485100300b00651000140756100c07400010990000c0010440d00c0e4802608016983c4070500e0b4103500b4401049907051022030030b08a81d80346042c0d9001c41081d20711801c10501c00300a100040844030038200448c8020b90304030b6407201c0707050013182d2081c90341074040760390003c0c1825000c0c451682a10b14050701443d000c010344146400f1503030050703044c51304801114400c03804d201405500b801101a0105441c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 663822814 1250 663821564 663821579
    0x90306050901050601020d0c081c020a030f0501030206030105040207050304030c0b030f0703091a04060209090a0b0a1d0f130f0804050108072c0f03070f090c0507080d0f020d0c09 78
    0x5100400001c05603240a042064070f0ba40090910000f0805007880403503104507040070340d40c51040a8050941c40c0441100703500d0100700e40e004141911942e9802c100b01000304a41c141511020320000c0c0d440312043c4018007161038641d00820a081c861000c0343d24203540c076542c0101e00c00060380b0102c0c2d040004010005092240c003401648040305244c10000382c105039641c3d4080c03207200221800f100b40701d43c0c005801c100c1a94100d8090f00e000a0021400345084110702d0003800201d0080e07070066000d40400a8481118031455040511884010003244e0b0340d580e03200811074009001e1b8040203070b411801e2000c00c00c1c611042c1c450324068071040d0b5556080200242402070090314903003c0015200e410b0061101e0104401501440c01e011f203044804200c000802070b008a441d46a810700526400088112180300048200d0705581c6c0184441e42d18184151520300032200b01412401c010170440b040030945034480c1c00d40005080c801424030492100c6842125158464000462500c2c00140640c0c3d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 663824064 1250 663822814 663822821
    0xe1306060812030a0f0e01051003120e1c061401030b0130061a060a02010f06090c17040c09020d020904050a050c0d0b0a0302030604050d11010204050a1e05040c090306 73
    0x800c0441c000b012110030300d154207112840700516007401d4640d07848829200d45410381260b8004d0030200e0080c0300c01d00f4030440b2504000214071007140c801c81c3c1086901c41142c001d12481403140c0c1d00900d084103601c0480c02d16803091903000400c4070301903640c104480c030b00d00540750070601a60203003184200c1981480842080c0718006410400d8403100440840c02c5800c5422140003c03580c80036010542542c95060110300d0f8000d102455404500400c04c24126941544a0000120f21020601c0403555a022940c00c50f0642d41c0007400180e107407101a0f144a45002d89142c016200c0c40145180d542d841d4000022078106604881260385c0002301040c5a182c14052250001c0101c1d20402c21801c082d110318141f031050450402680d5150a0b04c8001e40d0395495240b402190040e007955040c6c42c00e40740c400d0b180d060404820020851101c50741060000504c02d5a044e01e60107487c4124880c2007003945e5145440401005a11500c1f21201082944550289110b40c0c0041c0d10783c1c08116007545080e1054 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 663825314 1250 663824064 663824069
    0x8060411030a121d152511060703050d02040914060a061b0f060f020702031c140903100c09090c0503100b0c031201121a04050d0e0a0e130606 62
    0x180e40b00394840700208011003000001d00a190038000c040b601aa100d03901c2204d10360f1407003a804004004880401441040101550b2030318650382004807103404070240040190f8034002d0103441d0483e03820400c6080c100001c001140c0a03040c0300c0c1c1480070154003401668030581151031615151060400200941060142c015504890b609803444c00d003500242020660400ca00c10302c40c5254440041c40100c0c074450101942000302800828060181000a540103d208a0081c03060828038002d07000b00c41400c414512080c1e0307880c60b181030201c0264032160030043c903d6515000320446440350300224420010745e407003940c40e00c0210529008004040b07a102a042c141442002c000308038881159050310015505202d45507602c4560f5800500c2c5980103480700e0007071206043c0c0002c509100d420842ea4222486880c45e501c0200740ca0442c2580082c080c1c40041007540241211200180141c0101c0040c480143c81541c41550f41e2129a25100094900d2603088200801c4207007480814000e4001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 663826564 1250 663825314 663825319
    0x3070903240f02090f0103020a03060e040b040203070f210201030b270c18040c0212030901020403120507020303070b090c04020a09090e1c0309020627100201050907180608060108060411 81
    0x4c1034101d0001c500e0502c0c9202e0640c0c101680000c1c44c0e482c96004c0d600c0381021380882ca100000c640b07003d107010308185d41300380c1c2d081c0d02c248204100098625210b01804007030350403c00e41100c0c0c11b05036000c061a40010300e0350480c14141c40780d480d41c4031900c8483d49942d045184210341e8070780c00205c211306c1c10860b00180841281050070814160b02c80301742804000100025280045c208600c4503040341031003807250740381207100c0c000014130585041c15000340c82601d0141441d002c0407512910207848a100c0c3c140025016001031044a000c21191a001c42e40b1005030000d90b030041d80b0303520000c0c003207038803614520000c500d4811090020340690303c1858400f003154401410b440480e0810305421000000704c06081548030a242e600710f40701c0d0710a440c03800c0d0b81c99041d982049140460302c0c06502c5803601d014024051140000c1d0303541e1050083d00c0c090307100400035122403410f15040307000341c0340d0100842d640340c0e0320303440c00240c80042003200a0003021070354054030701800c1c40d250807502c424400414a2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 663827814 1250 663826564 663826567
    0x1e04030503040201271a1213031119060e01110a0f080f01120b0c070501020a111501030c0b0921070f0b19050702120105040b0703061a09040203070903240f02 69
    0x80081e00b05174415210011181848031001000415203446000009101424040140310348d1a2106203a800322922a031241d0303164021444130303d40c1c0c512147d907207000524440311065000c0b070703c50b51106079041c81d0200089092503206503800c29079404016408005251305100e07045e0030313910000d10740c0c200c10b00b080908510b500d00b82c1d00c400e00c0c048400000e0f00549060011400010403003044a43c070b82c0d40a0002e6440301c0c0c0c440405840c0c0240300380380c0c038054080c040c0c1700d070000501d0034a060f050360380c4840004c1c81b0f03174100303000704600350003a4441c03903040300c8000c0009090072840c4211460340062100284a09170500340e21501c2100b4540c0584000001070103031084680c0d909040070312a05451414686032020342c0000b40ca100443c007210b00d41ca529002c10f102c10700030081c01c540d02c10100c6440601c101c55071105190301a00c4202a890301d580c60603c06c3c3c0742e480c0b419070000c5800c041c20740381890b00c0b15107035102d4406036002c003d0800103c84006081d01190b4039103015120303114003500c0302103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 663829064 1250 663827814 663827867
    0x1209180608030d180b010801150603051b03090102070803040b0603120c0d08250f030b031b061602060a0503150f100f230706060b04080d081e04030503040201 69
    0x995034001e890181000b103131181000940e10001e400c1144a00c0d4226425100c1940d41d0751109000b00784852502465010b040c2021500501a0181ea40103401c0e20740007107481e5441907034a254039040070380140c2d0203540801060012664003400b641c00745010300940381d07036401c1000825140003000081c400320b404051040d4807141e4404a001034080a20381001700490381c81d108248250200c80005208020b0444002c03070b412940719a00c0342c1144102c1d02c003040590000130030103507612449540ca1a004d1450601c000b042c0c02d0580c0589554000050150179803042540001c2c044d0300030700b5001c0c000803c0030080001d07500b0f0b1072026188040041d160801020000d202084c00846100c818500b80803410889900013071003408051011b030b1400b561075080c0003d61001c0c0d48254000201941c040b070900f0008614070942070216011221800010f0030062400c0b0425501001c0003899040c0c4001988240c5601e210348000307107031140e8030175a1680d40d246010710001d80f0f49000180007444007030108069 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 663830314 1250 663829064 663829079
    0x6110c0c0415061b061b051806040b1b0309030a0311071a0f09191512050907120609020a060c03111f09050703051203090d0305060306010504110712091806 68
    0x620030711401e030500c0c0d044da200607040103005058194000500020340e1194011025031010150045c140d0002000c41074010b6482080200d01580c090341e0704c400c40810040c0c40304041481000c80c1488140162810500e05000003414101413040943c041004005a400031003014000781c800f910304807402449140007402100344c18099481c01c01d80a00c0d00260b51503140d914000c0e12140d802c503051080070150303100d0501d01300c03000c0504014030100b002c40100c1d20541c4446e0180511a01c014801061050300d481159052014a004140c402c260768031200c402584030b240e031540c0038051a0702c8982a20441c0d14004200c1101101410600c0c1c01078015000312102c40800e1059402103502c5c00b28840f007050070710500b40466580020001d01c2400e41d403a060070300c803401071841050b035001501e1b6042c10f151019401c0e1030085488903855000720006202c40c0c9029801112250440310080341403500030b99503980200140b02040d4045030440d4001c0000303201e80700040b00c0381c840e944024045c580c80c0c010f2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 663831564 1250 663830314 663830327
    0x50406020319050913060503281e08070c050901090902030604081c02030103110102150403020703031404080f0a0c1a091e06071103060f060906010c06110c0c041506 72
    0x3031000c0030002e100d0741002440c89801a0369021000501100c000340004400d40003d044600c02c8600a01a54500b04215601c894850400c00041c08015691076019507488502d41c1e6049061420300d40b04414050204843c0d0018042c0148191024815541414200035081da0164005100103042000c1c000044e207000c208079030040c1d0b11428840c0c4400301a609403180c0c134442c1d03005004041c8040000010701044651418002c282a000c1e40c02072038040c601303161000012280500035901c10724007040020300c12602102425841e022032820140c48500042c04d010b000c6041c0c803c0350703010300051410f1126030f060302c6000b49800260a00c15090400c1107140500505210b503125101a0004051110007001d04844071100200f80503039501031860101d9031030341c03e904124043d1007154001085084022a02c4e401500001c190f040b03c0d9444200441e00741c4406101242c180380c458a005642802078005000060300700c60140200c01c0c5000c1c240710445004c41040280f4040c690410400b0980120 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 663832814 1250 663831564 663831577
    0x9030305181c091701060302040b0f061e090a0801090308060301051608061504060804110a03210e030105090304060212040509010612110a0302070218010608070302092b0b070504060203 81
    0x903141c40c641c2040802c252098000c03031303000043c41980d2040400d1111310642c001001c3e28400c0340c04210307100030501400318180c1d0411956400c110108107080c0405582d40c07151078407401c2e0000c046c4c50401c144000c5a084143d990040020760344406c1c0c0d02d020540c001c2c1c2011b5004106030020841480d2106407101c041c3d071459100e0080c064003402085c2940c503846501303490b00c1041d60000780e4440d41d455000702011811901666604501c840700300360780c0ba0501c14002100e41000c03610003c2c44c0507010700700e40c0c0420600d444007071052070b458548081d2420300a0921944140700510340b01c5160800c00790030b0645194114008010400042c4801c0e560101c61506581a502d000340120402d0343d81000101148101c220b0104000f180003903519034140c0007045154401c6c0c84003a181e85901c5010b0030150740038010500480c03d002c00141c525407103580508800a001003135201c1101110181c806090103aa100445111001c0e90178410b20982ca204507070010294a4600c2c038081ca4001d00a49a00034030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 663834064 1250 663832814 663832843
    0x90d020c010516030e0406061707030b09010302040f0e060c0c0c010810060c05030f13090e030a0c03110c06040e0402010e0a0305060604020703030b10031d0106050d15021c0903030518 80
    0x5808442451720420034440d50600c05001000065103401015140029610307600c0030540d5200002013460303100c1c1c040c010914802900800d600e034219420000600012003518101d04e90740e180c565180310040100c1d40c0190714040c041a0740c0c901400c052420540700c1c80000f8144441c0000f4042e801c2c45450703254085a407249000c100008071850308505603c40d501510303031000300100d41101389401c6011503c00b12154400c04000341031004110b00d4a070b00440b0011000301d0480301506010901410341c6007000d10f841c005841d41c014a5400003445900203800000154401c28200f2046503088030195880110448031036441c1c3c1c0c650b680c1c1c90f5440382d00901103805a90041800c83c00c03d4025042034050020082c0300c0302d0b00d080e24450080040c40000b80d034501001c0d030102210841d0310107208001c20354201400040c0d0410280c0c89103103441e4568049101650b5003000000c0d036640f14000c0508410390760141c04240601203081c01800d07968060400c2031000901680b40c400610001a1034440c030407031 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 663835314 1250 663834064 663834097
    0xf06090b04150510030b1f090e190b13090b041506030803180c0d050c040507031509020f07060203010605040f0806010b09010e01170c1213020a12050c18090d020c0105 73
    0x344d2011009820a084840e8002d100c08000d800e501d00c0151078660554070940d82c56008c1d50b9601e00b030b400883d105030780450701c540384035001c11011b044540180c0c401e100c01400c1041a2000201c182d41207901c01c0c503044d00c40c1000c400910040200c0a40c0201042c6400102407013001e007141c5845c03202c1c3c0b202400b03007804038901e1081c0716504041070040002d000030007400400b41040c14104552580280521207104515110010302810b010340706e245865041258204000d038140031900c0d0003584106041c10300c8041c1800050001307442400214040c1803180e2f6020348a9107800441262032406402a08403031b00020010300c64207030107200b0303941c50310424078040d0000404100166407810410103c880c0201d00041045545410309004201032600d04034005000d50b206040040a6408564020751100607542c00b0004d0800c41030540502e1405902540c59000c00d031350004010f01d498800d4540408814401c20490350014082210b204403240080c3c851018842e000800520480c2e210542d011070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 663836564 1250 663835314 663835339
    0x150302101803050303040b010503010f060311150705011113060203090907030b041404050f0c03120406050318010c091a0307092702120604061707090f0e010f06090b041505 75
    0x20301c40c076100450300002a00c0e6a0b003001c0c10070508601d003d018981c0a507003494140c0c0350400303140c803c0c541200d070810051301100c070302401080782c0c455800200c01c01e01700060220002280080c818014401c040c60400c550b5a0140c000c1c0020200d20741c4d000d81d01395001403048800b143c4506588641c008002d1400040e904465800140149800d0309820b240000c45010007081000009041488550300c408840d410b00009003050340d00e8064940c51080301200f03200802076240188069500003280f020003400e0300c9600391000b4219441084060001140c0d00307020001d110010f9894282d8042d090b4400381340d450100c201a00388203651159400a424444420f41101c3d040300e039505503200801c90641d40e440030201c42031940c00e000d0351a00d01c03d0346005030005005158a0b0f038035095000d030401900000d481e2910301d6000b056074003001e86100e0b0b160f0b00390b001910405c1c0310320100fa1054500c0000c00c01d041c8900d04040b61285c50078240654508185c10303d518015120780c40440d40103d0b02c1d10320b19403 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 663837814 1250 663836564 663836597
    0x403050d140c030a170903091c030309211404050622081006181b0518150304121407060b030106030206040308071a0c190c05060106030e0115030210 65
    0x41095150880d50002141e0740d0781099101034410100758417006252036030303162611a10b84a20410080d07550000a08502d1034000515041c24640640203040005502419495820b0480c00740048400006030707219051202d0b0380c022030108408422041e6003404d0605003000300d04141301d010400a80b61001042030401c2a481001c100701138400c100c04d4a01d00c01c103991095006e00f100e4007500030a8004078402024a0069101360b051b82842927905900600244c00243c4040e44552042c1050349411a9a190140c80340d49040859040c400340c0e1950703a01d000e050000f40c1d0040c203002c08080007124804643c00c4100c14050f22015500460000f962040c00030001c1d00400b0183d100a410017004940007051040c60b070082c040b0351b8040c00c10b914190325150603036148448101d454100001040c403c00300880c19041484201800d2400c0c108402d05c180c3e1142403030301c50240e01c4a00001c0c0c8812030340007114020301903850942c007400144900705056600040703600441d880343c0420050008c84004854 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 663839064 1250 663837814 663837817
    0x1120510021305030c04090305032e03110405090f03040603150503160509090601030c120218090c032104060509030a14160e040b060609040b06030901050105150403050d14 75
    0x491140408569907080034002c403501c008948103462181c02805010364490800340121242223a040c1d40740c51455484600640241010740486245a1180140c00801d1001a08040081c6000b018440798400480040206a0f54010208031f030603001140b08420032100081074070142c1d24281004900c0e4001a0058034010b80d940e804140e2612a00d0707000380b80201000c4940081d1502900d44040c50b0b640c50070080c0c0c2c0c4034028480180f1090028008203d45501e5140700c1020034030003440019a174151000700000f0300d03001d88003448035411105074080340e89410003030486030f03210003e040101e4624624400d9190300641c4220428040006820b40207580c0c144038400d03041e50b10025444800341c800031a20364446445251004000e150000840c0800015106e288501da000c90303905c4048d55074a0034818241c100450b042d4105440d0101d81c18a6a100c001944c401c0c00003400000340b0350700d030004200f185420b18500101001c0100010700118034081000d20709200d01c1d0405c50144181840c03210304030b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 663840314 1250 663839064 663839083
    0x50a02060d021e0a030c05040b03070f050f0a030f0e1f09020a21050d0905061b0304170f0c01050a0c0b040305070213050907050307050109030f02120a2315011205 71
    0x140c8070a44403d500510140c4058104030107a42c0d000c01c402c4100b14015106481360303002d002142a401d0000075009803040c0741d481c0d501003251070894105510316082c02c94175004005040c1c00b283d00d80c541f4507000b8010348585111020f80100614004015002c044204800c1d0901c0d4100c240d00d5145d1441552103840c0014003d00f0903e0840000040f103608049100102000c121980c0c024401e4246801d8803a805a02c00d07038a00800c0d551130b2203107600c00c010003403c2880103103445010510001500000c08403043d21054044030181c12181d8040710210304013003490010905000d8180326207241c00d5409010f40080c103601c4006a859034680d424207542d980a4800d000794496254041101d050010b41c00090059248030100c070051900c4400305030311109140145400074040581c00c0020916040c0f109007068000380074a05140400b1083c1420300e2100300081e1150700161103c4081d50300127111080281d251040a82110a034030544850048418031506a4060f041001b0344140141804413400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 663841564 1250 663840314 663840337
    0x90902060f0a120f060b0f030403170903131211120a050303160e010c0503031906090f0204030c0f0305192109051005030c090402030c0f070b060f0607050a02060d02 72
    0xc84081602c2c000341010010740740c600640e4108000301c0000d8680740110303800e030340700d401800e404c00001003005031850304014410307000c200341c1d0041c4a032152400703a0440d004030402c1000e15074500c619000f03400c1c87e48030382d0701c4240417254002c201000b1444020120712201c9040343c1d003000d415000c210301031824000b10b402a0030386c000002842048011741c6c041c6200e401068442a4124004000641e01285034040291254208000085250007050a00010204014800a101600c0b50600b40890f441840300b000b80590008041c010b000740d001c020310003440c4a821000825085541e003c1d1200d402c8004155000c5850b0026420019140303040c00360002c1c0108840d034484180840104031b240b2074410a40a284000f07492100c052050782124464103c9851035860b02000780f05100c020b50000740001c400c507900344421004800040b00405045000e0410716485041c10010002c1c84502c154000340b080d4010001000090800305823191810b030100d81c203503240e10041e0791800c0a80f143c0c640004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 663842814 1250 663841564 663841567
    0x60c12110711060306031518060906010306051b1206361308041202060912010e1b220612060203010812040515030a02040f1202030c19090902060f 64
    0x41030504400a04503681c0500b0300203402e020040d06002c81c500c01aa110303509500704815640c4c105101907a12038000e10800c1200b1104070241908605024060715000640d070001401001440058090182c2240d0680700080304c0400c150101c01c01032240030b00e0b9442d0905e0031000502103a031000002c20114400003102e00e06100010621110007405910144161b01140041102c800c00259800120381d13000080c1444d0500b0000f150300003080190040364044801c1101080a8a40b05e4546009042d50800810011007007041182050500c540d4543d138010581d01c405800d907a651200c8080b03441480d400030b0780c119100e04141c040c152a400076001c58050201c86c0c020041c0b503030300841c100c504103401d450001c0800140c403010b5114a20496134414100c056031841d8454910080d504602e940d00c006180a07a5a54000c0c44084d10364841c2054891003508002507003028080f8502c02c035801c5030000c1205075080d08500b04505640902e0003043d94450a10007191030f80000c450446042042c032a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 663844064 1250 663842814 663842831
    0xb120f07270e09030a110705060f0d0e010c02060a060b03070f0f140f0405090a231504061403102c0f3304020a061d0d03080105031501050d060c12 64
    0x59500d80c811480100080d2000c2c21000c131000021501d0781c10389800910280c6002c1c0804c600071680e4202f0481000810341c1c8200b00d407101a0244103a0108400c16006003040d858414034200494156502424031036008100300700c0200d070b021100040700b05d214108100b2020250508070703280e0940086000c0086c000003004c900c4081e000f0003510448104503640b030b90955800e110744d420744403130b403580c4480e40f4091800f004003000200d005503440060500c1e64070410880c00009000d544003a407250041000030212943d0b01e01703061040e240042461402402801c01c046410410b0740c01201c0000804200f603140d00b1051201800a0140b001000049490b400381c2440011502e20b8100c0d03035510080408440e19890344402d0120602c156001800030303000a242c040196903405150000054004c1c1d400340c6543c05a035201c814a12550280e66221002c8d03041c103050601c6c01d185000481c80784d003860401004580d9841d6600c01c203859000c40081416501d134507041c0c8500e000d04000102c0b91b418401300 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 663845314 1250 663844064 663844081
    0xe04082101030305130602011e230a020405040b0d030e0f03120706062c24062803150308130b031602100b0f04050903130b120f07270e 59
    0xa006100749103170130303d60038a5842c441a42210008888055410a00506610001529404441012000c901000303052500e40000d1221140c215804030541d540030409101c01e0600348a00301c6035102c00e54155000848588010384000b0103400c007140708100c0d030710300c15009407000d00070354102016086038a6124100c91401802411540c05404004410301c6815488408001307120003c0b80ca6034100300c513032503c2e00c982158541202024545505031020028402921141c0c028910070b10488510f0194110707201100c200070f04210054802c042c1458840154403199080b02c000700d0343d000860304c2d925032400842d003849852503440001134003c0841005035854015960350400c0b10070f0390a0b074200a880d1076441c8102c80c100301206411651076004a025030810354031140d0003d8185084a0400b40c085000825105031504000342c18940031407482d00440505a11a820140034080b1015900d000740f4000c00c0c1c00d640340c2c850b54105e021000e28141c0d00c514596010003600c18081c003d429464a40303107 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 663846564 1250 663845314 663845317
    0x90503030a110105130804140f0a0305010b030c19060c050a0209040b04050c0402040e060907090b0a030207020f03030c0c09100509010303090e0a111815040f0e100e04082101030305 79
    0x70b01029400c0c0000031703026034412031040b0281e551010031170b410a41085c5541c440c50900042241d004000c80d1024082c0f942d40340e0040000350f01c10800442c482c0d04800c1807500b007485415006000344e80c040131002040030103055110581d031240c42c1591510342142042840c2000807039019420500680038003044c07108100c4050300c5603000c0c0c000c0b0303848000024207020403441244140c00300d9a004202083e814030300081c0150f001711461030003207201130b220080311006620540c04c0c030020950014480c4d0840c1041c41c2c05c150954012005981800c1d0100390321512140390b20306a0f0721621001d0005210444840422000740c1000703450070103590b84901c0c014082810380e0003085a079032082c000240c4500c035140268504150050b20003030a007401003c5443e1420b820744200c036403000c2500325051401502501500c000d00c00040080034540c074094030316044290140600390002000307a030070700018451404498005500201041c1e450b0b2f000880810581c0a920707d10710007454400000007455030000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 663847814 1250 663846564 663846587
    0xb09010c0611070c061e02060a0504031101050916060201060305060a090c1a0d0b0d051f27110105120c071e12020105100f1e05091306050a050f0a0c090503030a 70
    0x444008040682122086d640031003c0640d00050340314900140641a442c2c1000350414803a0420300d5120f266a0142825100d0880e200c4009034018100e4800c000d80a040143c000c041e13a0008200882c15a110340785c450304020401e8400e59103034856a010403030030400790350082c0718104501141b200002c603900d10b01e91140d08021300150400c50070b02e50a10b05100c2d10300000381e000c8020b00c6803080810030140c011886880030314085a4a0011400d8404880d0200c0036042c100390102c030340c80c0300c07900d010303403e103102c812100d41000424040340114410034000c8036000028140003e84603006850810b801c001403100404241c4500190701d0100400d034240d864000500383c000b4809941d43c00ca442d4a504500d203e04042ca0302814030402c20402103c600ca8240c0a1801d0142412500c94012403131501096550380400b0110103023400c01d116881c401c898000c840302030184000d04046103a220805006132a91044951b03401d01108107134043e5103030000900024044d01e882d9490480e0181601e00b952 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 663848920 1106 663847814 663847817
    0xb0d03080a1d0c0306160f050d063204020c030403031803140d021605010903030f0c1e06050c04031e1a130501150b09010c0611070c06 59
    0x3250a02c480220b03036000300310040c008010706181540c02001400c44028910481500302c0d4000380e11000030f5420300c5c0007a11125100241002011507a111000403482c400e00401c030a90300700301c1140f2142e40d400c03c00b09121052001e10082e4868000c404c0e515820030001440021301a240a000302002a041611382507140d503560386814000300c8041140c2e81c0074108529846504001482040c03161a0080710414502000a45880c0203404014144081d0740e8071074100c58820140040015001002800019a07019110290b00503511095403450b0070710001070140d280300300c101c0d82141d0b0f0002c82154440049007001496510308242128290002c0c100c845203a80800311481c060400c10340c01001c0c20209203089421a48a4008400b61240580d010040007609406450750803000f0300704041c0c081881e00e400d00050880d4042c203404050b0218a6900b80911580d400059a425 = true := by decide +kernel

theorem cover : BRFrame.Cov 663669064 663848920 := by
  have h0 := BRFrame.cov_init 663669064
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663669064 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 663669064 ≤ n) (h2 : n < 663848920) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
