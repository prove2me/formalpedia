-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1118
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:19:00.345986+00:00
-- url     : https://prove2.me/submissions/87f8324e-b2fe-490f-bf69-ea41b05e502f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 200899280 ≤ n < 201079136 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 200900530 1250 200899280 200899301
    0x80a111501150207080303091c020f01050a020702130e0a03030b0d1e0302060610050a0302030a02070b1e0108010b010206010e040c0506070b01151b060c140703050d05060105040f1215 80
    0x500103440407040d000b070130068554062405644284280480003201148610f04c0e110b41c050b0000c004000b1f08003ca1500f00070f0705856215519000034060305041c940c0042c280c480c02902c84510015110351241c0c100c900c98031440001b0382180f003802d0b00103071290b0047d10700c02d40f00802000c85110a51103c094100d00c10011402088040e8180342c10140c041c040a0f40c000d90498901122401d8548058000d102c9c01966a042590000014030a03865a41c195140e007601300090210314901050101c00c0c45a010124415081d0514000500c04a0500844c0079400040e400b41a19900e03010390906000301c041c0c0100d810900240c3c002c1050b0700c81700d010b05032140c010813210030030f035240240b1b2003002080c0d0002c00c02000400c803900b1611141c00b217500710340ba80d40481d0004400c10800000c5410a08008981041001c0003491000341907000b005800c0007400014200710b1a20f8000c0150f84920a5120b401259140710307408100f2541c550f0418201180204808400e078084401068221400381c0c02 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 200901780 1250 200900530 200900549
    0x80402150a050d0c0e0307360e0114011d090703120519080c072a090c020c04060807120807020d210c11040b01090f090606120504080a111501 62
    0x20f00c2e000d0b6200768010600c80541a041941d003240d814804a0b407280014054004030100440191a0607000460b44d038140e0550703842c401446600f1928078002a00c424401410107608180b410300041000351880d604940c50401e0000840c00c495003250020b000042c0a14400d000342600000402c0011141590002440e51006d5445286e1030b03800410844841d041030070880c80008000300041d2007001c440540380c0101a44020100d0b503001014150100d03070030816540384903400007900c501160485041003405400341c518082d1810140004c4505a02c10460541c0c0012000c00000d00d40551511845014000c81440c12250713801213100b0b442941402c40d442c0000804440440340e808803503501da2a010714040701c4142403500c03505050f1030000b84407442166145401c0c08168010300c1a4402403100d060101e41140e40c1e80304d110000d000a200c0c204c08180010360816a15400e0300c989481260f00040c091306141c094907040320462040724018026100307a4090344aa1050040c0460003080c1404 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 200903030 1250 200901780 200901787
    0x3060e070e091501020a02130e0a0516121502070203030403081909060201020a020606150408070e07030e1903081026120702010207050f060403120201061401081303080402150a05 78
    0x30140305403800003c14810044200091604803030780e002c43c00403010703a0112954541071800c299010000c0c94860100c0455103e02050442000004140c4003c0c8031242143c0d0b45e0083e503600c8115161500030301004150f144020210028130b04107501a003c01c2e4000381c100c03420192260344a075069403102d8220100050380003040380f0030b2580031a00c20080c221900c02541002002d102c003958804014211500c6615441b041154511001e4207440c01408044102ca4401d640e40344082c11407441a10340c2c000290400d495142c02100c001404101c00f11081402295411543c800311514000a0030207a100b01400a0014005d41031504195201d0030001050b5140d100810200b450444001008406034606201c00300140c1e802180c11000c650b416035a03c490070b00d1000005603130344110381000780f06400312200da1100f140e0541c06401039800d4800e00412940c0700800555078410111401170664182850705000244100703d0a43c100d0701c060001c8402c01c00780e00208c203464101e41c0b204030000d035022 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 200904280 1250 200903030 200903057
    0xd200408010b0f1507150f0f02220302030703030305060d0602070506090d140d0b030a020402190e01020115290a030b1509090403051c090c17070501020309010c0303060e07 75
    0x101c40395a0800c0c080b10040d0000d42e41011614150040310001b0307003040c08080007003c1e2900503402004400308105000c02031f540424901c00025041100c281000e130406200c00d0518040480d0018252500100180080c518550701103002c2c00006101035000584105441c00041d080c2c005420030030301c12000b5000340e2a24080301c3e0310301480c0761f11301410030444480102c1c550f01140212490b0807105840410903e5080001c0f9280007020315000790010b02c0003444241c3d4000c0a8407140c0034540c6a41d40041e540c0340900124280c415020f0182c1d102c80740e210342007140c035228a1b04130025900100000380c8600307a14419807100d4000141300c00c0813903100d5000c45440e01d040360000c0c003031481c0145041d06210101d00030500700140100000c00340800040c034188040000c00c0ea002800a0000c400c0c00203c04614041c111031400344220001d64045410a04a00d400421144142d0b401a0700542c00c0c00a500300441e03035144100000e8060503aa5080450241d00a0b562244241425240c2c5600040ca1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 200905530 1250 200904280 200904289
    0x12030608060a050c04050d03090b0f070209010e04150504030e040504150f0e0304050d020111030406020109110607171b0304080106080c0306150d060204170f0706090602030d200408010b 81
    0xb480451494502030420020609100c01d580c00e6400c10ba48207600c0402074030301940d192446801020910308046201c4110b2100c2d6401400001e1081d80c44500310790742c60a400004075005e540040105081e0040340590702c84540c40942d00c54000d20701481c840403441c0125088078004c3d6025a008503021500e45580b2809006001002403180001c0022201242d811034072406240505489400012042d400350780c402c900b10743e01e80b00000b0580707555a5880714060700801844108490800003208051502d14100e000c1c0c0d440e488e0000b0303d01001c1c403010005405103500c21150301d02e00c3c24101408020510003000900044e00c04a00005040790030310080744c1c1742640d0f50448a2003640321508100b481c880c8041482e22902d000d40c0c40210ba4000c03860901c01a01403134220329401050120000d100080002c0c801d0300034100b143c2621406921280201e8000b40c0380e020b2400076a000704090144448146d11a521081c44c080052040c07500400402c01281d10030b501c51b60b0240e440d42d503281c5c2d280c0750 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 200906780 1250 200905530 200905543
    0x3030606140405030a0b07050903031303050105100503060a0b010318050c0307050406030804180b13090212010203010f1e091806051f060c0213180b01050d080715060312030608 77
    0x1491108509040c070f4500003a80d590501d4070001d0003014003038080b525840c0a8025507003420801003d07240ca40c1d50380a8005544003c0303100030340e00c0798200f4001c0b409540c000340c0300005442000d80648103694a40340000050880781b1961410599a80791b20898510000607130581c06102e139000d030040b4410f480030186026459001030748a03d113821030400c0003840c48002c48085801401c00400032007440d000180092003944d0400e03030071050b54421201c40700c903140e0120352954803c8507100074800c00220301500301d00090142c16042040c07180c09000d940482c25a800302e0180c01a44002000d0301c414540042c0c4440700c9903000c0b082c150041032410025640915917204034003869803820001c0c0701e07400c4c0c2c881d000b17584206002d006044040130151340701d1502c10300300704102520600c000b18005a0156584180c0c110031780b207a0b0084030007c541498000c82400e4007581000c10681011146e07140c0d08a0482d07a80b200440c481d0750b0b21000000901e85040c0550000f4658600080c90352070000c4103414200b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 200908030 1250 200906780 200906807
    0x4030b0f07080402090c040308181908030322060e011b03090b0112080d1a040605190603020c03070b0a14060306190213080a0c05030c01230702040207080703030606 72
    0x140c030081040280c0e94000703405540103404450321600c984440440ca28240700f1900050000b40d40007906c4001054140000d0400d90015100044844c52108000003841054090507d83e80c000300041200c10012049541900907001c8510340120003130365914003125074806250b48aa512114841c105c042d443e020030352140750f181018011342d807640d6542507501c1d40500800d500300b42c03050384000c00d2020003019501303043c076224003c1004410445150611182a0203400c0c0308900300000410203080100600c040e000b24140a030001d0b40c10a20150040d411401c00140c032484180321040210b6030b00301400b402542d82041c0000c142e2070170f050401402c14002e12315402a4000424015640c2206c8101d070801182101e0040c0c8992802d180c0d11440c0c0e81e60781c800542441145068014403287c00c101e01d00310b84044049a01c0d00020300300554034010003d04940c3c10300401c00f82c4541c03054242c0028408984010801803a1001a03074800340980c2003040150006582c031842801242e410451115170803 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 200909280 1250 200908030 200908051
    0x4090e0105100e060105250308090f0706090b03040305130f091d0d03050c09040c0801051921020307030c0618050102030405060d021602101115070516050c040e0304030b 74
    0x5401c01d1010004080f02a04a03030400c640000c002180c0e00518245000380c6040d054071820400013414000d145560907a9800e41d41e01400032030711031034180080ca200484000d44c4603010404d207480402e19071038100810580510004005450010711078125410241c0001010b004440d0b040041a00c01c5a0110301d2020341e01d840942a0301c3c1c18000040c941500001c245230114140d51001c0564810f0f004800070300d9006820718000c181501d4010080e241a038909840b890071026102c030810b008a0100e1041030703104541342603e09800900d540303068088a00203021103400310b40c0c940e220040d240c200d50003a80005c180c03405600e8050380302c0310700c0c0000701000d2005505050a00001900700d214030f103034150180358000ba54100b0290801101d40c10b294008208090010b840c1e14003501100032615507e00b28003d120f014249081a580d080d405001640d07549410039190180b5905080c02180c0155268800c0f5520400503543e1400303a9480b01281502840c3c5440c0744d842c240d407080070080d0824050 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 200910530 1250 200909280 200909311
    0x20f18070e04090b06060a09032909070f0b0a030204150f0e030d0206071b060507030b0111010504030509010f02030d06060905130501030b0c072604140105030906040303020d1104090e0105 82
    0xc00c44c40c041c0160030100840d8000d07075a21219105452006481e0b1000342400c42d04d040f603608180c2882d01c1d400b0090b4503d014040603990b03042c0d5864440044d802681010800d5100a2058244a6000d00303803024550400524160325440241c0144080e2100040026941166030340e0040c1d0004000c605030400343d00a040c024500c8101035260080101150108803601d2990701030401b80340342000110350000820081420440c270001c000d00b56034110503020078101d08140c0a807000501c2500d100e990942d5980d420040302c4001103a0701c04c0d0140e0b1000440c4001d0010054886940c40f07440014241e98032800c507140d02c3c1c02c092200752203101b44c1c51400c040c0f401d401000801c461124255100d21140309075580d4402e54500201c480030119440901ca0314028041d0342079001900041c02540e844c103544401801d060700046400d848122000c0c02990070030320101d40024003d80160401c2c1c45101008030703400d0345014004076260450361000031410b40f03994500380b4208003031049a4112980750b403420003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 200911780 1250 200910530 200910533
    0xc061902120105040c020102070c03083004111201050f040605010f180b03070315020309060c0a0c02010309030e10020709050703020c0304121a0a090501050108010522020f18070e0409 80
    0x5070759814411580110b442c0c1d41c60b203119034030039412651050b500103e8150034503240c1c1040070068002d010b10590400e0883c0d000850340b11811018401c901104000940300c0c1ea0325a29100050395801e0841c0d0040d000d400701503000035027800340521810000014160364501303400d04000362001a4801150360031001400d0051500081c018400064004804070344041c901011900c2c101140d88050190000c482041030456400c0e00114040d4440c10101c076219242d004000800e8130500c4101c04c00318100d2407650005500a42090303c20038060f00b00b0703094000d60f45003c980500401000c400058014041c00e000e4440140f15242c0c100c10140303130442c10b080e004401d46a0341e100720302038071031507131000035112040180b04031132099442002d50100c25941000541c1074003500400504035515401d110010501400510035a803045109160381548000b0181c0844004840c000301a604101c144005180d50f403181d16a100c010300d1104500d01c807030302d00450000c080c0c600e840d002c1441142807616000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 200913030 1250 200911780 200911807
    0x6071e091e0b0a08090d0e0109141801080a02011b0b060d08040b07060603120e010e0d02041415010f0503011d060f030a0809010f05030103020d080319020c061902 71
    0x3410340d1051003152000e0aa00514211004103030b6101e8656000e0003c0c0c00c440c0c05601c420000e01804504044951091104400355902c80f200213565001940c0c5810811808500c60f034000e902c0c0c000a0130141500320350000b00b041c03d500903004540c0941c8103400520071542c1c401510003403200c61070403602680c4440d03170340c800c482c0320050306481c460412004a041441400e8003164010700c404201035980c1d603681d18001e0003a0036184416544690f03038103544000540603c1200ca40e0510580d190001100c400c07007080400c040300c0d40c0c207a80290303482c84071101c1d1080d590f5045000c1e82201c09003042c4002404001003020f4410300c0c6941c00c2013018001045078080c14102500a03001d0103d04c000e180e5144000320f8001c240c01d05005515202d035940321401c2c0b020190084c489090281d0740c03a503d031040c01e40184c550f44030a100c0250040300b000044004600d844000d550003010700c0c960100720252540d00300303090303800a01e00500390303820100600c9100d05560580d100030420400040d4101400392540c0da = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 200914280 1250 200913030 200913047
    0x150e0d111c080405150906060a090b0102070614040503101505060f072910030606060c15050403020118050303060307090b09070c080c0f0c12010e0d0311090a0806071e 73
    0x705000c801e5001c6000c008050000580a80350107448206618000400b1580e4080540b216405100c000b903000c1440caa2500900030f2100068006000952030300404a0702c4100c0c941c0c400d06104400c1c000881c20380c1d030034049e40c000030480050200b060b039024000188440c01d141d0100d4440ca00400048408002d0707101034402443d0448041c2c040c00c00e07000404100300e510410b500b000c0a40c0c00f0208165007281c0311114040d00c0c00b500003008600d03102c107400e4070480407030003026000d4980400800e40202c4150041503001d0301c644004141c0c030011411442e9014a0494115860303000442000010f0804000c4500200007403607091001060078804180f4103240500dc00017008644985c15090040c0102110380c01c0300183d0481d480002c2d1300003959200e182540a10f4401d0008401d000c01c82c078414000c0c02d0102c134170390000c1d00e03000251410030744c01451000e10803210b146040c021143c0071b680720310240009052301d4018001c9858103220051802080f001015603101250b00d03900715250780708060 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 200915530 1250 200914280 200914333
    0x10230f190306050a09060f090303060f0f0e10170a0308130b15010e19031e02060f1305041e051305030d0b0105070b09012f03060409150e0d11 62
    0xb81507210300c0c0011026101405019000c1da0500c03071f01e4a040e48469008400040c003d80d02001010348441320145d07a2140380c864595255007815051051880b2a083c3d983c00804040311030802650745d0a09108807840301002c1c8509030004003810090542010320304e6132001c0380c40002465441c0c99550000a20310142c80d50702030482030580d03c405a401525004036100c0d0003072502d40000d03071501142c0341403003450104455419640540107028281d110490314540e5004040ca414005460030045143d00400c240c18070146100c900000d003a1141d100f9188091040a220030085d41c01449000980b036019100d862022100802c0d080801c0b00402070750858080c07904007180b6410701e00012a054041c0300e0700900000742c00410310280180551043c0181c076200d80340e003031140300c80f084208111110f141c031031018441e040000406502d450380c0000e144901c244480700e204810035840f00e0031100c12004191095200690030040c154020441c071041041480c0117108004800180c0d007000d1805819 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 200916780 1250 200915530 200915543
    0x7090306020a0c050105041112070509151c030909060803090a03030e04020d021207201005060a0902030907090f090203030429070c0e0a0203060f0910230f1903 70
    0x3140c0714928442c1140d44070f6941c005000b8001428581080a019075007481e00d284607425080d0348490143c8080b800c90112103004211401c3c40e40c0f1700081d10111400d1001c0e4a5000345065032039103810042200e40031641d40a80d0764041c06c542800010400c4645580050410798030502603190240c1e22054614103495151420070006020b0b000407070040d001348040592440d0010400c00001800a0b9880e41700c1c080550303840c0780304108440c4801001c0a034a01009054200c00c2c030858415409030021a081800500b28040035640c2e00e9901040360003d4805602c1c9400000b001c0050f9443c5005520210000310003c2107e00d0943d40026603034495031080101c02220041550b02911250826298504029400d1035441e0807a1a00c409800914043e007242c510092001c0740c802e0b000c51080c1d03807040e84044c00245007070801c2c10404c0f8502d00c0040c44685440d07001c00c0c0c0814a5141b400071481201142400c6500a004d10f6080041211400501074062110010400d0050034a240110212070b001103 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 200918030 1250 200916780 200916787
    0x903170606071506090e010b0306060103060e040609050a12080a050601020309030d030f0b03121e03041e05010b100c020f0d1a0a0207020612010504050610140d0902120f060f0709030602 81
    0x3004401402c085e60041000300e181071002026502d064019428140d030441c1a06c40a540d210010350440c0e000f40a204020855140060009000c503442807020a000b03d08403100e01485c1d46e1040003e290110f5a800020f175038105000351030040d0b0207016000003090010718101080000803941e03c20013003c12200301a00c0d85610045040a5807004111005c080d090b582c240d20040c9154a9036400780c103a008621120341c00c0718102c0500c0300d060700d005980c450109440711040d03814042d510710209a050700c0b295a24540041c99030f03955a00a030502440f0707124001c141402e40104180e400d465512039000e510161001c4002038240b01da030441c02c8451201011064903107084650007030213041030003900901c0000d01c0d0001c1e242201000d0f41241c0c002c0b902400f04c0c1d40c40c00b041c4540301e240c080304100403941c0c5100040743c982800340075001c0d8078000d21002802c100d00f600001d00a4071444040009ea03044501a00724404052100a903c5400c020701b0101c00d01b4181d01c0240915900d210144c00a079020 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 200919280 1250 200918030 200918063
    0x40503100c080c071403040305030307140309031903021c1a09090601060f140a0504090609200d0b0306010f0e070c050d0e0402040e090d09050d03080402040b0303040b0c01090317060607 81
    0x24104007481c185000105c17900c65823240b07040d0b03540b5072040c3c40c550702103800b1041e00101350500300100c2c1d200c4c1d8800d002950802400d080b04080c0301c42000c040c00d06058003405401c50300804800b10001580c28114080703044510580030a082000e0000750303031302a00c1d0f4041000b0b101c1070f001814a0441e006031a160301c0491500604031445a011403100408038000581c065145500c18040d10517101401c004100f0b990327a40b580c0100b150115103000c40752146c05c1d03070085030840501c0d0260081001c88000031078000750342c40c00282050001d0700070800824a00d5003d001d00305100d40c0e074a13030140903800e0400010100342c0700c0c29a01c00100250b5410071001208039091519247c0564000b1b0006078809125800c04003445038450141858600028100517800106c2c1d01d40310940c840100d4250f00c1d02e180d991103e03004d000251001802c003030b40511041000003088a00080100032884000300005140b071002d103001080c440ca038098007541d26a01c0c80070b01550f13954420444d4051980500c3d0300800041c2c8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 200920530 1250 200919280 200919293
    0x540b0309030403150c031116061d01060303050309010b0108060a121106070302010b130c0e01030f06030c0305061503060c030105281d01090e0613050307120302040503100c080c07 78
    0x201c0e04020a03c000c0d0b4601c113500111290410300b50000c10b5281440f51500040d250740481c010480741d014151420240e0b90b0106034260f200b4250703050f0a1851901f2130004880c9d581c00d5400d50b500480010b0390010404c481c2d03000a214001001c002441c150185d0b01704400061445400b40c0600f808410b01c41903d00108000364940c0c5c00011030140c4083c0e101d50950901034002c0000b50070083c0110010000003201032012301ca080030031651902c1c4c000071003910800440041005040101a880d0342e00700100204c1c02d6021110011842070300204080d291400b4080021000b100015019600c4070342404403d04075002900e055400a880c01c1c8418050070380c050078500b04405070030802130461034021a000080403482031400d0760100c4100e006903070380c80d061000c0307030362030054514076400400200e030790051110441c81140f4001d1007141d080000a0b1108103443e0b0818881f4000300e0b900080400c502d040600c40f009401d14403042c10028580d00402c0542070013070081c0110401440011080c007003001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 200921780 1250 200920530 200920537
    0x90603060f05030d0f1704080702270106180305030409061701150b0304030c0b010e0a0e190b040305070b0f070e0103150302010e03030d020414040b0307030c05060307540b030903 78
    0x35120b00c55078140c1460b007894012381c4d0116109078001c0914018084191082d420700c0402c1d101003a44c002800c6e8030b42541240d45c04c44280718051000700401c40000820400c002510141030501da00041491501d4000411003811002c90031503641400c11241c51851071240380c204442400004039070340d503154641103803d0002507600425207038184c000401c0300300ca03642040307201c0c0541c481c0c10048140c0008031980e4405002c8020b08201a950f510903001603a000b10031600144207040050410300941d5841c40f0601c1c0880e49030000071140010080b1299002ca00d8200c14a07007030030304002c10035442883d08450459400301038180840c0c0e540400307036a241017084072110390550504640b12500e4240000070300c0380301c140c114412410f001c1c024103103280c0402c2807000c1325480460f0030445807502050210540004003034006001010038000784021030400e07007170b070584180301d04940c1030f0b000c25a41d0850300130085018031070007201c2a41c1c034840503500d1804a081e28040c41c00c0c503469a540403e00d918511 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 200923030 1250 200921780 200921807
    0x105180c040b18030d020706021015030f1b1202010f050304030e09040201050903010e010501050f040c02030d0504030c0f080d140105103207120c0f02010e04060f06090603060f05030d0f 81
    0x30619a04171a210790124138442036440d1542910035103c2030160340d0302a44e5003400380407101100340000b00002003034840804003640c13090b500c654004201d915820054010307544410000e058001040c400c641e4071000c00c0b0035020090906600b503080588000b00340c900541d4000340a60380b0b000104003075a0042040d204a03540080080c031056946404e414043c00080c07099600800080503508032520700382c00b0b001d280c0c80c0c09500860808900b450078401400028005174140308000c0040c1000c1020540c48803821402440910364441c4903100030002c8130310080914080407900f81c018000755880e080001c0c507641d007920f0002c07600c0c1d4400a8282c1c0e08a0103200c00f10b0303030641a030201e80c900410103015001d0b444c01041c100014004000c016039200229100c002c000030071082030751005602445001c00031560142c0f001a4603511900c4141c60400550410400304508040070403240340c0c58010302000c2c12250700782203e101d15203004a45c1d507840050441060140030b82d0710b1024244140395401194 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 200924280 1250 200923030 200923033
    0x303090605160f14101d0706050a0507060f1406010e040905210c070825050303160f2027060909190606030b1303120b0a08060c030105180c040b1803 65
    0x6a4240b190020581080411b400c43d420030341142014101148620446080b9254686806103c51040304c43e9807143e102100c20035910181042d104a15229000c0c070010207600c0c503455410701400160420700706042d107074812810481307030400103040400c2c0000c6140c01d840108100404008215025011b13003003002905109070100005d00050000d170301c80900500b4005207600c0c0d8241c200442440a840c0201d03a00365204000030800451803242260b00f650040010301b9074980c80396100c1c49610030394142050040f801c50701c010301514020021301f414010f8001500d03000c020f0b00c00b01a11803a00103000030321403651240050181c600900000d001390b8400a211186400c6c0b07880c003034006292a00040d24009564400180c6110400f501100c095405445440c0d210055170700603006407003002c01e4940c00805801000840301010001c503070190315001015a1258100018010840100b840c1d0500e0456040b00707104444ca00c400403201600c041c922443e40d00c0500300c5100038000c00d40800150103 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 200925530 1250 200924280 200924293
    0x506150d38030a120807030609020c06010e0a0e2119230c060412030209030a0309080c06070f150b100c060b01030209010e0118090608070303090605160f14 68
    0x281d0103000d0603000c6800201a1030007508201d00c042c5582c4044800000b4042218044030f1080d95000300840c0b5402401031401283d500e440342190400ea800c80d8520280e41c3d482a8018050700411000c1d840e0302601d8004204660020340000695540c8212406544021417419002c982c00a05046983c4c2a411110501c1480001d42000b0203c00801d01c82460424150820250408101d800c0361103450907039009000c070341c0b030f0b45d11500000c4121910303800038540c3c01c12000d002624288640c1d64080d0094550384481803604240134101118099001e2050307508200c0c00c1c000a01ca00c80131240d054000b403004108100c0844050000c2c980d12034400d6018003602566075610b1f901c5445252000e00c0b030481889000007080054007039001d601d43d120701240141c8002c13501c55100350313a4011607404146420300d030343d40d603403085108840c6250081345141d009a0800d209040d00813440f80010030b05450070500d8408081d07205d40c02c810000340000c0124420b903600206110f951201501c200310442c099581 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 200926780 1250 200925530 200925581
    0x204060503090d0806010815040f1a0111030403240603020d080a02100c05042310050915130b0f07023a02030607031805030708090906040506150d 64
    0x40381d00101c0301844a403142030600300903e4491026107000f0781c010703103890140d903c401c0c00340d901d1200c004450301e4000d075448608001880311405018040c400341c50700070600b0441e400c0010a194007003070001202e640100020400620481d00310320b0318000c10211500c040b6500907980c03025041c039600103075000a1044944080c03002c2c040090458078015000c546d441071003000700c0c0302600c0140c001000030a105100c01c114240042070412980c0402403c0e4256030a80318000807400702c100810180014400f043c800c903136080402c1b04c5540030a40c88481030130a5085c02e1280034610040c06550420100031540d0401d1116003000c6d150360b9035001780103400c07001c0c1c0101c2e48030100c9e243c0012140d0900c540b80c80445a0028000c1450005070050060b00b080c0d510350300164040c180d2030f80f09103141e04fc2c1802040105000740041c09100c0d10030200d40340c0d2150284100000c8042c0a000f091156260030244411541ca11704244440541440766940b50a14007541800070b280c85841c0c00c0b21000340c450b1004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 200928030 1250 200926780 200926787
    0xf010203190513020a030b0703091703060102071a160303020903010f0b090604060e0c1b0607080f070908100b0a1706010806090f0d0e0303040f0603150927020a0306020406 75
    0x822458030060200140c1e92440f05000c4506090000650802c152030700510104140342881544201c1d40c1c140400c0c400e410391b451064406024001e85001d000102c240421907074188402001481506800030740c220b035440d0344d40b6080c0b00740c641c11444000ca8120b184105806074043e500c0804005008010f5410316a0010008d8818000264450404040094035501d064443c3c5410389001d1260880755a4031140022680d0b0720001090b003180300c2c040300240c1c02d441c08004c083c0c821042d941e900c00c01400c204140f41c4000034040c10040c03d00101074028801d4040c00240b901c40c0100e07050b000700c0c4010000011034078030f00143d000024041982c010310b440c00640094140d04950b000c404644155a561070007941b03d00c0d4440c01600705401014540d0003151086820007076020380181076a140560b2501208d6000255a1109002c2034548a410300c5001000c00c0613001407914034818009591000040340110a4104a071006080b80d0101003056407140040312020b5548154215640c585595002d03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 200929280 1250 200928030 200928061
    0x3070b0409091b06020a021c0602041701050105010c0b0f041515030b06040b220204050607032706020d050c0a08040603050f0c0c060604090203150a0b010e040509030a050703020f010203 81
    0x10340b400d0084001c3d42c54802c0d03e41503810100c9256902030301c1504102e40c00c1020b03082c54002d500d1b58000148010102281083c40208018115501d50401c06940107400a09450050b44200c1c1440000d4041c20081104070b10364030b500c00e9141d00d901030240e0320351a0032400c0000080c0b1032804589030022008100510540300821340c0d00030070402300300341d41d50010002583e000201290f0800d24911051080001d86a100142700c2118000035081035192804105280c2010034280c002504401c026001c05944000c04408090a24400748280e030030644d0107552080381108078802c00000048036074150000384207004403a070303000c0044c541c2c4542d00ca000402804042d1b902a02a00300305010171b0100c20a44121080c00e2007010140c10603642d0350007000010700f100d04060340c050054485822000c440a542c0354819883c16400195076490000010400e08444803118016450320b428802544800801d88200002d1494029a14003007031034103e040504a0402d04520f6001005000000e005101c55 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 200930530 1250 200929280 200929283
    0x4080405120106050f0f0307030f0f06110a0c140c09040506160207030c0311040603081902010c020a0b0112020d3518091b04030f021203040812070203070b040909 71
    0x421401104418818200c0f00c1a1158550011800015611900748028400b490074002001c1d14660b035917a480b1141250740c4c050382250f15004100011080000754401c0340c2c4c0c0386d60001400c608209101b400a00022100c01000d001c840d040d000001d0107000811100203000300142000342e083c02c2c20b1a140b83c0e82d203400d4606450500c0fa03031001840951001403035074102e13038120380c80e081054a903880b0564030f04a5401440d80241d1661400301c0030612600081148460600c0c00c5060403140c03060007070844045807a980215000b001090001c14403040d101415100d000c02c4481410040d4400508031404140000f8603c10702d43c1500785648000072224450000000d41142c0444100c4007200643c1c8152242d251480316500551120703404e006550a13400625126101303500c500400080105400543c022260381454000d03400843c180101300700c1d24080300c0e0740207509041c245801c41d40c0729001407016400d40e03200030510400b990740030410800100395a542c2565101d8071119000081c0c070403441c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 200931780 1250 200930530 200930539
    0x3070b0a050a2706020409020c030a0e011b0b060d06050705070b01120804030303020a022d010605120717150403032f03070302090a170a020901091505040b130504080405 74
    0x10002c1c441c901401c0551003a8000544892500766a0b01d0034040a030802550080d034288008610090240f0040c036614038218011510b4a2560030b00600c141601241c0c075041100400c214064081110f0300900115440402281036986001c04a86000700b82007019101e18180003d1003400b64009006100d01406004103d215a03200c4507104030000011000905006040100704080381c070075405014103109a1064800714068140c107040803c4071252a408084510080c00f091700d80b091103000300070305c82500d803000c0302070030f08200c2d540300c030707254801c1c110400c11090301d0042c44e200c20302070003c081c03e101c444030b0801d00301401d00900816100d41882160701c0b000550802c1c0d03540c1a0072621103d68a03a990600d503648003e0200c5c0a500498142608844900004161904914007481f403122445006040300c222900411507030746010380c40740080fa847d0848050700940403003e40819544262b40c0490303a04550000309201686199403a02d000340303000b080c0f004115190000f401201c2c021034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 200933030 1250 200931780 200931791
    0x15061002190b060a090603050c3601150305090d050903032101030311010510140a1815050d1703070e030a05010914010e1b03120a0201290603060f040e03070b0a 70
    0x2010071007240d80d1800050401d51000000f04001c0c2b429886031354100e0141380c021a0f60f03464184004095503428111480f1440c519001400000402c044860a02c030f810702e03041c40282004102c1c583ca40b0140024041000b20000d04113906450030001c0359264103050044c02680c6014420700c141d081d070280001c80014060720041e00702c01505008450181c070140240e452190314050f11140c800180da00e00940056050300001580141e0806411442807250404901c00c0404101030024030115008031303103c6c1100800201c0030a00c1e541c0314a100708260744a0035070343e855800065845040612000c1e03490b2185200e80004c00c44c06411464122f0f100b00080ba0000141700d0101e03013a905c01100501f1194002d000113400359080c88201422110041d003903a2801182640441d20781d0300810310000980c0d10303016031084c82c050300003821103030012103091000794480c0300380094628072018004c0780c49002c6190403400c00740e603540d01a44505810604072543c1c0c100c1403404204448046135061042c0c0c0c03514 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 200934280 1250 200933030 200933039
    0x2705010b0913020415060806090a1e0e190c030311390105090f130b09010f06090f030b070503090114011503060b040f030b19050c190215061002190b060a 67
    0xc5c0c0c041582c0319901c440007076649103414071031010380040c07142003440e80300ca6040129040451164041001100000c144072001d40c9140e8a032108994044505035003035035402010820142c20b80c4241c030f5151030412043d0b404100b07114505006003c1550422003405107400c1210441001c03240300200007031084046004050054400e4054858202d400c250f012411070880d10340003684815581040340006000080c5da80401e005001c00d8000f505403245190782401403540201c0f200c2c0c02411803200300c42005007160f031092080000501840e09115005c0086040800c00b90050000e561040e0207211f10340d82c0d42e414045042c0204103109003c80d10300035010441c61901700c101c48c10744654100e541f14042c599603800e40e903194010301145802c00240d40301d40030504180106c6002d4120f41180a44800104581100641c0791b50080810b56104a0a0451402107215126404041100c111403001040d00041e41000f03440c0903a8041001400111020021148107150181500f514101d400d540c45 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 200935530 1250 200934280 200934311
    0x9010615030e101b050c010603060203010905180105040203150402060c12040f0f03050601060c02120a0803010626040201141317070b130b03060d061b0201050702012705010b09130204 80
    0x298544d0800381c0d90520310005864011001446044040c2c00001812940c90f22510101d030405e0b0400240e9944803828002180c40340e0203d075000d000260000c11580c10940c3c0002d54900c4204405104079860000060035560b41c00299030300440f070b840c20740d12912640d10340c0f400642d00a00480c6009049040b01141030144040b9040c2520341c0000240f92a90900400f56050402050201e0788417201e55a08580c005043c0090750380c1c244a0740e8000d40341c0d4104040a843c54050302d4074100b0221100389141490080800039a03003042d0282024940310f19416140703a2544500c0c00b84c40005a50301400042c055144000a454900300c070702a00c100a4485041c00c4803031052555003c0c0b00b03141000c092103100b00000c011900028010404111900c6a0391464140c13400388001004405c0d001c40304452844d020302072581e1100315480204003c00301d01c5e1420351041c04000700726516504640d016000c20400350b101c4180c00d04020008030640c0350160864160051952040b401941032910714440d4050 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 200936780 1250 200935530 200935541
    0x13170714010504140c0a090f0e07030308040b0a09020d1202030f040e040c060807080a1a090c0a170709060c0c031b030302010f11030705130306111b06010501140309010615030e10 78
    0x2002006d4690580c41e1030b4128014001c40e0f1207807000280e83d44800170122404012040c003c502c60b843d035074440e103030034248010b40843c02408100c0c12800d1800400c0182d9689144a10b0030342c0c8000303041908101140100e14600400c082105500300029020551030f008458082c42188207042c9480081d86580085500781002d4854402207081c1001042d0120380c50380217207200c0c205404403401400304071300005110b4070003030765091011040011032001d02540114081301803030b40d520307084c2d401e81452100148410307038502c5000700f00403d040e02c41040140d0807054000540e0490a650910740000715482402c0d5030382d00c0210701540ca85210301d26580e0039402082d6826421842c001d041d959400c200f62a03031740c000f1803c1d222980b00c514021000034024441e2140701c0c55049151500d68178440b20135002c031740c000300188805901440041080380e9110110200d12250500c3c202d44a80310070841c40d0162206401801484140d6889590141c0d03066001801c8040361a0841c0c4003000010030709002c0780c4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 200938030 1250 200936780 200936803
    0x9030c1b06030f0c09090a062c01090c0c050304060521090a020108040501150602030408010c03060305030403061509020409270308070f141c11031317071401050414 72
    0x303410702c00902240100c00798541c1c0034581c030700d103149041051000a00d250a040b139a2504a80e651042440003408401c800c04481e048070a482010440890001546900501c1390341580c980f03072408150440c0c4113141c0207a083c2d501000b102d8441e521220050180e4124030bd030340380c0c110524ac00d0316052001014074a4042d0305e0780005004480c107030760011204000c0007402600c05648606400c00416200c1d4890710040203540d0145440701d06101d141425112040040401c0505091041c0041080482110100c03540701748009a54556400c00c00d9110205500030300324140b02080000f4007002030703000340a4442183c0d48001004448840718190b42d10b0800700500098282d100080c0d40a0040e6101c006103811402c0854800250306000c1009500500011401c031800380504d90801d0f045006111300b004619440c1429490682c1c1d81d200000e507a64405080402164a00050b280320b120849446075080340300c1401c0282d401551074081c01c000e89045a200034a607454040c2440d000c43c411400c903 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 200939280 1250 200938030 200938039
    0x5180a0f0501110f0d05060d0227090d05030109020705011104090b0a090507020a06150503010603050c03010e030301060f0f0e04090605042f1e0307081b03070f06210509030c1b 77
    0x61705180540002c0c503000f042c9940107040c61041601584d568103641d45458a2401c513546100494549104c0410001d030000141c2c0e07020f805c400303032001d800405480c1920026400141c94108a04045001d400002c0740001440c02c001004101100700c0d811a04a0040948120b070f03500d030741c9a041074111403049601e8401600000081800100b1582007010300c18134400c108a00242c44000203030840b5074030752084500741e03c004035481d0300d42428001d034221341e014a0051070441d0314245000d0030440c00b07a07207802d0401c45001e440419040c01004540780c4010040d1040002d2000f51618400421050b00e081c0c0d10600f6001c40384100c80d804000501244a0000d04610740c010b04505003c070141c05031070350b0303850f0840741ca5100b9500c0c0c4007000402c000704401d400401a125070310000201d450302c1c0c051854080e17004004240213140c40f04d034400d001c0341c50601c2c007211100003000c4003041c810b0106049403152810b00043c0440c500c00080034000b003002940c10703074014507510708080d44804406130034290017 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 200940530 1250 200939280 200939287
    0x1f1713080f0901030617011a060901020d050a0309061e150b0a1d0603040b07082a0a020f061801060503011a0f1c05030a0f020c090a05180a0f0501110f 66
    0x1688030039005041801810b050210305d00d500c03500001620042c160b00c0d411103a5444080c002021100c031107032050004207a40301481c2803100c000007500c40700c00810050500100003446070200c0e2080d4082c542d2150080c5042080e02c840c8402c2d860200344240502c2100b5003800c03a4040c1c115080100442194007041c040c40c90090300301000d45845000560454a0401c0707000c5101e030303030307260a0003d5100f240310740c1f50000d4070f10f0203a0025103000009410010710800803a0134400000709a080c4243c26640b40c040d0b20744400c0c01c807104074944811840303c5074882c06910f041c000207400c0b800c401c0c1c05403a00341009000c0c0317a869005141c00c880c941d4500360442d0040c00e5201d507250030b041c07400640e5000040c0a0032081c0a040e0f1142c07a904101417400c0390135610005400f16100e82c8440c0400d40c0110b903102606005480200092503000040c00742c61a5a0b13480011900100d0b60000103402c00c80240240e40c480f101e80d0a20703002c501c08181065445509220844400c401c0e460f04580403415014811400c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 200941780 1250 200940530 200940547
    0xf070305070f05030303100531061a1602130b1c030906030e030f0a051e090a0e010503030306010e0a051003060f05040501031208060a051806030f2a1f171308 69
    0x4400406442701494170985000300c00d0b09000126141100035078403140401c0e428034081215224404403401c800b00f001040c800d101c1030206ca02c0c44013100c6501142c6000054800013040700c000d2032891201c9500108250070700381403001843d442e0700c1c554000d4440600c4296611010780956048070b4550b60380c0e420810130100800458030107058506101d14206003410015655404592a8131304d640d2860b50021441030310b14a03101d6213400207049540745211184d450000820b541e80005000706050000d40842048140c98900d402801010020201009226071060240040000f0b001d881311094030f030400401c03682081d015041c122031340521103052543d5240f0048645071000f510303855100c030782550b00049503550b200040469141c42d0700842040e09012081525025a0030400c6040742c1200c00019185040b030260403200e0401900304240e400c4529000403140408880044900c0c060700400440c4180e01c1155a844aa09900c014001c1d845000c810780c2071011072a8002d103118010002c13040e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 200943030 1250 200941780 200941789
    0x30c0f0112140702030c010f0b0d151104062d0c020105030c0c06040c0602060a06031707050129180f07050c0c10030b0a050607020a0b07050f070305070f050303031005 73
    0xe400451031500001e40c802d0056181660303120903078845005a001292028884900f8410300091100900040062408000104040c25800c180180007550201240e0388903200a80061603c50180c0f0602540d5603101d500180c164280d09507031561802e291003050a202401098480220010780c907013140c0c200180c2e00440b0503074402800017140f510107212900b40c24504000315801284501040114141400e60091074100d0007092a13006c0b070b091060070008a01c40030840c50780c40c502c4c01f000a98445030383c1000c6000d003007880d4102010001c042d0030070b44103608001d540350b56564101c0e0b4074280c1d0320f0500e8008501e07800c1940c0041c0050800e10110320180d0194004080d0381054401391003031400010000b5040304061851640401d480750301408080c54443c486401070b103070031283d10b400d141564001c00c00004160290800c4804006410310a0050070040440f0100c41c8501310341001d0f40328070700252240c01600c9480008000740402181c9450044142c034800d03043d4a11580344c0318075200410 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 200944280 1250 200943030 200943047
    0x30f080304050f010606020a14060709090b010c0b040b0103060b060a080604200714060703091505060105090a0f0e0a09030806041a060d0212010902280509040c0806040b030c0f01 78
    0x3142d02e403060210416a44800b8002c2ca40200240e4000d0190003581d4286840120380300c4995840c80e0b0450420004100e03000200760091f01c410503000100d83c000500140c1c2c132601400c202504101800b01003008006c00168921305903440754100b800301045071004d02181e07010b4078510001041c440d800040c1c49003081c0d48055200c41c0403800d80440303500c5116513180b041c0c0c06685d0588501820f4142d85003451010041141c000207145410414071740d003600d40103012281d02d5010324a180e11100424150f030300c52820303500141e000410042001d503580c2c035811103541140c40391050310904040000c004030828443d001c41c0d10303003540b1101010798940c401c12005002070f100400880c0c03901aa40d21051300c80c2e03006070004066414bc0181d4031420341000c400b000348141d01031407044d4010400f41d86541d000da81380340c281c90810a0340c0200c650808406542501a603041250414504072484003901da2220b14a4040c500c01d075800c1000b04981014140c41d594a492141d4008075540c1820b490380d445111340 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 200945530 1250 200944280 200944283
    0xb0306190e130606031505060a06110a02060c0c030d0906020f070317130e07020102090a0b0f1b011118090a06030507050105160f291b07030302070506070201061d01030f080304 77
    0x400e13a03203d64444540721091950441250354890070403000b800d0045150007e8a518100802e8604111440b996110030302c070030084c080d4001083c4051076036002c010b0081902d2004081d4bc0c040030710b03240014400300042c461600148a030201c06c540c140008581a4180d03078200e804c80400c1d00081132070b8803503580411540008401d031504000340d081000070209000383e40c1ca40c009079417035100d9020041d05055a4001c010070607000c115144102d211b140844c0c0c03000101d4450380006a04820b00da80c01008040c4441147c4100058040c4001d107080001e58030386071080301e000c910741d00c410f000841215000d003c018119403069038284000c1d80980090031440c820142c940d20f2807a402c1c0c0d60690864031018084401200300c2c0e0b4540c0c100760101c40700d482c6900900c5202d600c40c0ca02000c5001c8100e07544800c1c0030100e60001903d10926100b0740403240303415044805c455907401c2030f6a00a0080a840c801c17203000340c0940b1040c0103d00100a01030341200c0e005403010700180c04e00d07116101079a0000d0320 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 200946780 1250 200945530 200945543
    0x9060d090809030d030605031b0303031611100207170a14180a1203090e040b0426030f011a0f1c021e09040b0a05010807080a11040b0306190e13 63
    0xc5690700d0f901003001c3d5080105650300851442d01e840141403906660b40c1d01403006209050a0041c00e490000540346c0c800302c1c0c40340001c0c9000303940c0d1081d110388000d0204c08005006916510000c180b6540007012814802c030185000d400541e40d00c800107000d40c02e140c1000544d00c0e800500740c1c000e004007400c0c10480030071860801c94145000100c411410742d11003507094090010074014541c2201282c0c009000b0714924072800d01d41a034500000b850000c0006200e8a030440844090a21020640410b05c48410b0125503a0601805282a0100034821282c072214141200060100703d0010b54604954641143d81040080c205641d8510201502c9104e2140e0030722101c1c2c40c90542480816140400021703081c0d94107241c0e4141320580301d541c0c0b038441c09030147e15410010303643d01c00c500c0341d070244a81c5030500690310f61441c170360050092200c601c54051004140411150860030040d8000c8c4400c5030a0710048d5501811003988000750302c90a802420180000340c4d4510500f80f5250300c0b18030894 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 200948030 1250 200946780 200946787
    0x90705040905070f060c032a060513020901080f1203150a06091a1801050307020a0506070e0909060f070c030504030b01030f11040b0901180608010c08100b09060d0908 73
    0x40030508890034038509462960060781c00b08542c0031051101c1020340140d01e041d1112034150385028101c0100203100c0203e0b001d4a0b90768401c4406d90246d900071466020b0307010700587c1072440b2421140504860300b0791103002c42c7d81c00011001c20006210801d07640c040089c00021840782ca0b007140c0c0c0e42000700072039009440307024466119900c180b2664064400d036207880e4041c1f0304280101011480713091108001e64420402010881c0000d0002c0e501070a091030199600d1f610100100c2c00c01c440940c00400c0341c8108018040e5a136002610b0664030681504d08501030f0b50f070308200c641e51b107100b520901d454400e044086600740e0300c01c01030302458038064101649020707034942c0c031011b80607002d034015900440c00c4210700c000c006c0e045510420035241100d00740a60700010f000122014410322681c0160b20f443d8202254a001c2a0442c0b00180003450082040c810703010740250400e882241c0c440c0d000c3c080c40a000c2004010401a40c1c4143d001410741820301907075411850040014004c01d460400090 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 200949280 1250 200948030 200948039
    0xe210a020310020a110c060f180d0606090b0105030c030f13050f03030f1609140d0c080d08070c03020c011404090213031214030a090c0f082a010e0103050907 69
    0x40100103280e411203140181d40744d00524008003103440c41c0c1078015550f0801d11261102e56254025562408840101280c3e101e074120380030014141c14054040d004043c00386004288202c0d544010121403400d40280040e1003a00011111403000300c1e0000501e0009002180b819195544d10726405040b01084103242e000903120ac42c581542d01d104c1000aa2000007000052290342c882c05030000821209648605c04003100600b000c0a0b40c0a0512502c190501040071a036580144208060300401104111a125402d19488851507500980402d00c0782004c10722682c498071030701c140710342c065000e0002c004000c0d00444400e405440401e0704003034140030204005c0f00034802007105007030050707a10100510b14500135407208039581985060200e9078034181d8203400c00318112580b0800503030f00001d40c150549072101002001e0740042308000d441840226800c9000200103100864103001c00408141500d007540c0c02a400e203000b00e0010300c80c03030f41c09038a40d40aa0081500304882d481907800307040d1103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 200950530 1250 200949280 200949283
    0x90102010e1005100506040e0f061c06020306040501060504181806180c05010203030907091d0f07141c03030b01030902270a020c120c19060f0c0e210a0203 68
    0x4014203142c800c3d65103081c04403040b401e691010040c02c1c1501c0260505142540409003200000c1a0340d00c410074100c0081c02554803139240740001200c5183c03940c901012400c2c400000c4d04100c80e041d014600d8500086911402402510210b484003e400845200581c2805c40601040d00e00550000c0b68640c0d2000010814050745094502001c0000d2240c10241481892101d0640c0300c603056400c00c2040c0580884041741490a5500410003c20b02c0104050b580000ca000d01c60910b001e4003030030101001c44200481c0c40000c80b803800c1c0c41040e07416045420000d40c0c040c3c42c0100f031050300700440340c640001e02030b07000383c102c1d00814180000e614200342c000c194240444401d100009150300940d07400e00c0d407000e4149411000b041011810000804081995951083d81081c2920f001042e210780b045400c0044912003d0740004c507404400c95494074002a0071041c00d1100400c0c2081600080d26100d20303154291380c0002804207507001c00c0e1403143d025003420300590010600030121402d000d80c60 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 200951780 1250 200950530 200950543
    0x15120a060614090a0c02031603050403140102090306090304050319030e0a060320041d0c070501020f030a060902030f0c0c071a0309010506010c1101120e0124060e06040b090102010e 79
    0x41d801c040b0b00c000000c0001c03c502190010001130a41e4a060b00106007a07500005640502a4035032001003411110708007618140219400103000d00ca91000300c0742d1340070041d0040c1c5140e000a900700d45442d2110014a51a8052800b4498040d80041e00c4806411010004840014003a003070850502900d0720200d55400c0031504140c01190300d0300c601400f5150081e0307102040b0403080c8100c03810030b81082a0f40322100500d803c54040d10342401c1c08180e41455100c01c540c040b940c881c008565a1750b2402d02000d40b9042100e40c100b2030703440c1c800700241070803041c02200c0c4200c140e4450101a07541b401c101c5a026000100412130621a00304003141c00c1940d0801e02130000d4440b1011500c03072405940b00c41c2502c000421071070400030030180680000d41c0d500f210315600c40013400d10007000b40000440200804003001140c5c0ca643c01c044c912202c0d814018684085801c0c0319a80000407a01c460303003600e07076880c9041c201d074120004004c200140600840a046514030510020a10340301d4910030909c1c102 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 200953030 1250 200951780 200951789
    0xd020910170606040f0e040314030f06030c0901151101020f0a031d071809031701030f060c0e010c0f020303070c0b0310090b1003020c0114091b0915120a0606 69
    0x81c5141c1c0c0032103025240848580d40460101d91541c601402c1c0300c4500c1007180b503440364907075014916003ca0101800303880242c00e44012101d00540713a10b416104012128800d0b82e4030341c000d0294040400050170407103012416101100441b802e14a103200b03080f6004032207e2106201c0355800d00800c1c0001c00f126000740125085507402050f55010240c03800500a9181d1850700c90798041341c41007182d0319a070709a0500b01d01100000240c840480d05084c0c4013412075030f4250150050703100005c000c00076524148040c69000307103020040c1c040504400d441814007000000c0c0490b07540780358400050b11010510462600c060309903414111965100c1c074484450360021001d0020200c20400300038514548040189006041070146406220106182d90007107a4510105500060b0841004d10300350801d00200c66601d070302c600e02c0d240600030103031500b0720300b40c6800c8521011400d0759100d14041212500480c01200c606540000300d800b00220031812841051301030181d843c0610201d0078a220b010002c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 200954280 1250 200953030 200953037
    0xe130b0103050109090230060736180908030a02090321070f020f030706030f0e0c03071514030411040c02010213151710030203300d020910 61
    0x4009950000d0265003058010300140d620344600180507a41d0600c0341c006170b050000401901d454400340e0f82200314101e0740c216802d4800c01003485a8980c0c0f100e0054031000d0041c800500304c410300800c018200301816100a8034500b120800c2c424520301e84c0d510441503000000000d0201031565652046400444507241080e502003000052802c06010000e1003025140c2d43d50f01400b004c007c004030901603000040e0001d040078440c40119100c11400c13814040000301141d0b201969410020003526250081b548014200164402c98441c00600c04039090b9005000d0000c81d802c0204000725035090040000800c08030158005507580110021070186000315001040d00012130240015a00c05540360411603104014401c80502d012107050709a0b100444440100c8003d800c04858a41550b0150a41c0c12540d1041c004030520344021041106c1c821340c2902c407201c80c11080741000d0036840c2c4043c24100c0d44082281c844080769070080000e140072000050504840c100070400060710f075844040071 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 200955530 1250 200954280 200954291
    0x50c010608010507081e1902040504090b011e050d290114090f010e1305122a030304020d080d1103040609030201060b0405010f080411090903190c0b160e13 68
    0x46648410115440a002e010008a00920308806d00c07459100078030100c44001008412418041d16070100d40081200030030600c0040110f0070103c070407840038442c010410001880003100e03081110308a20450350014030b001c40032074440e00d88007030300d0141d60000025000e90f400c3d05a1841c542e061038601a00c800d0340c000c5540700c522020300c505400044c2420344000020f800402840082c5003400c0e60000d5518015064005039142848c41c000c074080c50111b103550081910503080707100c0c800c80d891a0010718443c01e11180d02850141c1c4a120a440194025042410f20804100814000c111214000500140780c16091440342066002500c04840b02626403480c80c3c24141e09000e0040a0316480c1502c519041c40c110020302403194500c080d005108142000500380300890002000155000c1e00031022840c0034000c5c6922503000c00c1144400d1102c03050504c4400b0300ca000e219954540c01062164291503040e400c1d0b151411561920081113410b6892034183e46400494400507181d2010200d0b0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 200956780 1250 200955530 200955541
    0x30103030804050d08060a051003060807080d1704020307170309030d081806060f040903050f0a05040512030f0d1d011a1e0d0605090a06140a051302090610050c0106080105 75
    0x10940394480030810172515805200c59540d601c2c100008071802103600344006e8103084016800b800b0300d076000c0e803014000c091f8001018800400c1d245403c0d201d66407179880218031940004000401a54065010381c4100c20621403071450801c4000f920107164116824251004000307850809500f1094000031800418031554403542c2000c0c02160b0300f0100138213094980480030910920410f0b080301d2041d504d0388203020a160281b8101c1e040c9503040002da5540d030076a0714000c0c1c80c82c1d2252145a01404240c50020002c0001009456081c8038403001c0f10f1900034401c4581c0e001c1c000501c1c400105142030468250b03410800d10400c40c06909184032064103000f110108041407210b44030103840c0d02802d9241081030f55800340d03400c40ca02c1e03000c10002025165074626918001561000511141c40c0005009078030b058084220f02c902800c1c0301c103109582d21a108481d0b0480b1420000390032a10f94804100719161484000910343c0d418074015040c5026890941e080d00c040d680252602d940d00e0f0280701 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 200958030 1250 200956780 200956783
    0x6040905031603091406031e0604020904180210050a1d060d0216120302090105070f0311031605010506120a0f0201050d0f090204050603060601020d031107020604080c030c1f05070c03050303010303080405 89
    0x181715501203500a08500c0d180710400320030f110040400c40128200b1001610555950341070701c02a281c0680208526501d46a490f810848a21026440740070007444103440d09220308120303004010781e59035400c000250b11769801c203d044400a11136100b4414846148031500c42c0c400382c01c0f8020408049074402031181010300c03610704285122020980100200d00582e40c100040310b12031640100c114901500074141101ca142c6c2c07034070310701d03919001c0059142010001c000340210024050710080246858100c100f00c3d070301a44001d07000702e80e0081d10450001c11440e03003060b200c282c01810402e10341026800700c0822109429842c5088950b14a00b0500b0342c106446400c0d481034040d00180104c2c140100083c3d40c500c502d100c20802c158491a01c0149083c6080036903407156405802584c4854036840f68540b82e8411300e8805010303100c0c00c0640704103482e080705145622a140030840b01d4520401208648581c03042c58259441c00c0030550000014600300021030080d8081c1c0e0f108403140c100303031900c903 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 200959280 1250 200958030 200958059
    0x1b0306050406050d0305031f120309050414040305070c0801020d06290316030605040f020306011107030305311d01090204030b0105060a030b100807091d0604090503160309 75
    0x440c02a40b82034010f00c180d482c1c607601060040d805003065910386d51101d81c0d080c1d9142410403110540034900340000345001040500201c880d00c2600c40e50142ca45030014401114902119621864441808500031901420050903480d000d040c000c45000d032502c1002e420799202c4d002408034903961b04401c1094080500c50450320390420382003450b18100203007000040303001c060422041c0103030b80c02c04180c9040c02507120b000242006030007031058004418514000f500212203540c0403c0310000682c024000118400060301d61503206c0c242000100d5075403000c003002810038461101c60034100070f07601c2c0e0355008401005002881541e103403030500c007130b00c4200c80c0010b9002d10500c5006100520004030300da038180f81510800e841460700d60541880440c060107050a401c3c1d0408210444281d006a001040e144038408030348039400c20646c0c0c0c2c9840804d0f000710f0401e040356210380c84013040b01440c0540100b12110f00840440e41080c1441000030301c10006080c084010800c1c00204000e4201a0300d4917 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 200960530 1250 200959280 200959289
    0x418021b0d020f01140106050a122301060c02030a060b01090f0e090c0109142704060b0a050d0308010e090703052b05070f060b1f20010207030903080702030307061b0306 74
    0xe01000032902c05e00f074028181130140d5010b0010120300041e95511640740d62490300e00780360050008202c5445400d030100723211203085101c92403200000c10b800740500b030000e102a5000d00104200411610341e5801410344113030a41c104444450000386040a04001d90042c2580352881045410002c0c0c185180c0494003032074505012075001d041200d0032101c0041001c10005541c11445a807920002c54246140d60b015840584c074800e003848207000c42c0e603104542d41e20302a41c9600304240c1ba030b010030070405084a0010001500b040060020540661145070000154030440710126102c1d500d250502040c0000d00801c07240044c540300f0340060408888007680c486d42805842d203041501e4012186907200c00c0540416290003c0c80c0c150789a509102c036140c60140c064410812070500020801b280d90203a01d1601c640220500712189018400c8884156150303e611000d28a1907540040305c0d0030400c030699160000744030100201381c0078001c04460030040001000c040c8003a200250444603a40c11 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 200961780 1250 200960530 200960533
    0x90c3a0506010503010e0405030d0204061e030612080d0e0609060a11031311030c060409090c0e0112170d05070c030f032f130b070b0f0702030418021b0d020f 69
    0x1c1c404903903040320881e0f0648030703445400f804680c0c0714107281d460740c071444000954107480040c002508551060101001d1100030f02114104821003408400b070340d005000d9080c02c0e2400c908064000b5044000800080d00084004548000080001414000d040314084481c0c0c004400700900101d00b807290180f404a4800e03002c6c103508211005141004d217080d4000d25444140c58000c65030b40d400c01c031890440c8001003089503500d0711044103002608000c02d08441c0a10400000728214500b00042e078140c60f80484041c24020460303c031a13280031012403855503180020401e813100130080d80a80c5100f04615101c4501030744491500800c030f1081d520348441018501141c0d49007071201c5030b5500503996414450800318051420140c00c440c855507183c03050901d0900c1b000a850414600546402030142441c20000e50713031403006581c41d90303040f0303500d5005030030401082c0302c0d2425003405115180c1d150140141440c0c0141018605003013251a5a05142e0004903002220b40d410815044000e25100 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 200963030 1250 200961780 200961791
    0x60c091206161d12010621020f01140f0f0406120e0a060e070e0103060f05010b072607050a03121b080c0c0f0304060e0a0b07030e090c3a 60
    0x3460740650408074001c0e420480d4994140f014140c0e1640110643d07035005002c80c0001c2913450700607000786034038462030020203008400102c44929490340b0b50460b80e000380000034124036140045030046200a02c2c080b5800091041c07070894200c0a01401100c0d05076110580d689007031220180c42081754682e280c0c486814a0071500b0318420104249206642c05440814400390040280341400100d4000c100c4104948000006000081d080380402c60380a42c8104034591b2100c08220b85449040e4019101308140c00b0100c9425030400410050901d440c001c490924401e50b4840f0304007031041205030002000c011102134001843d109066014000c120800d45c0c03081650400351000c08000d016406180005c07580c025192010b1101c00100354008003a00d50750354540501404014803405054040c2c0d0880c6004110352201504460130750380c15444484210007080100070b6020402480440c001e074040c054062202c1c1d803143e403000301c403c90040d4859000e01440c4001d0400da4615031450250342442c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 200964280 1250 200963030 200963041
    0xc1203010b071407050d061b080601080f06040906110304032a0206070501020c0d0207030309081b040b0310020d1e05010303090302060a020f150118060e070c0212060c091206 76
    0x541c1114035042d44810698000811880c600d414220b15501040d000303140d200b82403040240c0d50340001e0013110400052011030f0344140045400c40b40c1203641e9808594100c000c507480d414014451740c0d00c10300080012507518001ea0301c00382540c84400c0ca4000513074000c02880700309a00141c0c000d2003450019211003603d00803840940400300d1428019000e07042c00a03c800c1409004c6d01141c8000b200c00088400310911014000d41d5405184001e0b00084c0103540f02049006010591030030410029a090151301505c1d4104001401000039107903241c420380d42400700c0d0803517500240200f01c0c42e01c400002d824458015108410010b20100c1e1003e5291100500001c0c0d0000700707950640350160752a03034551090704426464800005003202c4a4030404450714142000703684102d040c1c2e501c28045a00c6441c7d14044034041d65002d01a20a564528030700040ca403034030a0000580b914001042c1d2001c0c0350444440c03505021050780d00741020500041c0700d014a09100c0c0701541c52545032030042c69240b619 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 200965530 1250 200964280 200964299
    0xe1c030b0d03021f0605090f040507140a05090c0702030f160f0803070305030c0d050f06010f02010e0607050c0a0b0c0705011404030f120905030a080414070b04030210170405030c120301 81
    0xa400c01c80109058031501c2c1802c05581c3d020700050400546609480e048c030341b0b106107054000300d404850701c0c866010041606030504c19042d4000e00c010700441e0b981818101004401c55005046a0b51028140709000140e40e04009114040c002d00026040c000c0401000c0010070712a5000700b510701c045d0742010000031200100b01d52500d80c2518109da166100d40015800305c1c070898810f000032a042006000d01010400c0940b401113409807184c1403c031444402c240d0036121041c200e1a5141c01c2940040c0b1300b0ba0042d401091600b02d61000d40300142540d03503032111120410b6801c9100d54038081016810010240324044408040d190b00e101c0c00d181a580003058800154807600c208000b06816424186898102c00d0049a000c807d49454a0103094001c0209408603401d50b80445002c4443c2c0b400c001c040f43c0c40042e19984100e241c239043c2180c00780b00a520004030286c3c00c00c1081c0d50024043c2c0c0b4002403807401148503802035036427100403880186ca480c2d04c11050380c0310094200010030041c6e40 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 200966780 1250 200965530 200965543
    0xa060903020607020a200a051002010b09101d0a18050114010501110304060e0103090c080c011d0112020309030c0706170c040b04050d020a08010f0b09010f080c01120e1c030b0d0302 79
    0x41c18800c000e0341d0249440403c1587c0c4e00f039800340307030480c6030682d007400b0081d0107401400350110280d450030360980c3d5405502001d0304880c800e00d60a1240310360903041c100b080d1a5070303da1100256002003102d90105588202c109860501900c29942d038440c1c448843c0d128100640c018403003440e0a20100102140094072481640302e04030602403040c0e803014072640650000000355030040d50b1075005a940358100c5840f402480101800a48805000000e8060309511010b04010695a130880d520352071660394000d40c0068003a04007440213011006034100c0030051030000c2c120780ea503002000c3c0a10940c078003410f640585030302d08242c020301c0180b000000e8201998110385040b03c4003480803800f030000c11009031103600111000d501305008088c00b40600e03000740c0403045050b034001025a0340e844603801c084090303010f0b030030742600300784540c19081d8030070745004c1d0b080c0b0164240003418003140c1109a243c001401034035401031780c1910043c22419098811842c1a20060350403180301300b12907400a46960 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 200968030 1250 200966780 200966813
    0x2030603190c3309230109080604030903030f03050708040b06061e0901110a02030d080907090501030b07170f01091a06040b043f11030a060903020607020a 68
    0x894809000050200d414070b410b008000c0c10085001d0704100f18200001507007402c610550320118001e41601507032007035010404860f5010406580c140240d03080c03140303101680601604020301c868012451850600150340214070030785071001042d186141c041c109494a41c1d0080500d480c00c01000100d079003020381642e01c00c3d4440040c1d2850b541d0240058114094003a60403c0f039002407a40303400032103100c4001c1000080c00d803180c0008400c0031442c03d40d00d1400520080d01a0400d05a4a60813801011415000140030003503034507094680e0414012034a090b40141c50100615003030113031180c1c000003441002e0f10707d5800b0500e40d1609110881031102d0610820074801c0e0750f00450200d0703031309022801080c118010800d65a40b03a44420340c0750350740c009000d2200380340d08a40390a10070b00340c105000300c0c5000c40fa1100b80c0c0868480e1101c01041c5001a400f616040902d0030616800e980070b010094409101e0080050703010b2250034000d2825034010f250900b9540580f900802050300c41000a0480 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 200969280 1250 200968030 200968063
    0x8070b16060e0604052e0b04020906030c07150e0309100e10021f02090d08090a03020402031e0705030114061b03040b0c0d020d090303320903010e0102030603 69
    0x800d003600040c01180d03140d500103004185041651030040d100440c000340268010030444541e4030041c0c01204c50440103c5101c0c0100c00180c0c003070003107901c0c540c201864404000300300500300000710000c507000750b00c1192007a000340e4001a0038010404004104400588400d80230000071901021150b501e1041e04c0c6102e12490142c80200c400c01e1041c2003401c010741c000b9010341031f5280300001c042e541d0a081c0c0c66061806003182801103010f801c82c400e9800da91002084180e0144540c1c0307031145207a000341c200c550452040f80003c000340c0ca42d400254000c0d4045035400742c05540c0c800e42c0900c020005080030040100810040044021099003030140703071401c88065a032140d0004100e1b0022640701e05000c0310380030101e0006000740303203100603000c600d01050517154083c2c04004100e8540c1040e600d40c5020441c5410184040f0f48200da034004c4150401e242900e0100c00d28138660300025a5600e0300e0354541c5c0014841c481801c085c010322500700c0d0210000d5065003071500003c3d464a00f1a19080d511 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 200970530 1250 200969280 200969287
    0xf1f0207020d11040f020c030702040b1905060a11070b0901030c0315090b13050106030504030206010801090b010332030417010510090c120908030604050c09090a0f09080d02090a0605030108070b 85
    0x50b9113030341c00300700100c0c0342007011903542009801083d100e401640c0c0030f0384214640305c0e02d0103203410300a0841240c8842d410781c800f10242040c0402540d0303000301409208220050141e11800e03034040180320084c2c156403040d00d40381c031103000004040c2d82d0546503036010182401c0c10300c020495414203401c01c0c1d85a0030b10101d0000c078038101080c1d00b10900742c10f00c60281c2c200000054900d801da4007040c0903074002d03420f48107540c0e00c0c0e01e04a0b00344c0320051802071070940709000400c00320b820604107072407002d00403155418160020114003004084080d80c0d4105403c002410406181c040c5055040b020b11540213000e0791520f41c0441c09030304034610440c1d04003a218408100030520480b000114900500d40410084506051024280d00220b07a6a80540e00e40808070b0034040e07900055821643c0002c240d9511079450208000c09850750003003649055888401303000c0020700e040c0281a071850700ba0401600d9030501c00c108588950158400b5042c03020400050200950124112050352009001540e4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 200971780 1250 200970530 200970563
    0xa020a110d0c4b0f11010e030304080a150902120c090a060509040807060e0a0c05030c0d2a051008090714010c030f02120d020307020d020d090909140f1f0207020d 71
    0x548000c84000800e01c84e1403001480801002c0c03141000900400c0e038030340002c0040c903414981d0368416400342c421203902001c084000602c1c2010403400b02421200c0c0841c4c0d400d446d9001c245d1014104000c0c64035500700014030000e6041a0400d02c5e8054032000381802400d03c0d0030007241940d135004d0000380c405480000c16000344441078000c0074030704001000b00c40010405042500c08200c11b8040c0724460701030704600d5812490041c481100d05600018064140c4501a0344940d4041400d01d040080307403031220000540d40d4415594100644c181d444031038480c0b500100082c104005a00800c003200b800a06104507668030010003509164142044131382e20601c0507099142c07241d40e5200765804540000e903c01d41f081e068010710300528564007141d2494903190802e0b0707280c1c18088070000001e00d07910001c1144d101203070400c0010a0213800d80c0880710008580315400c1c41c60152a074541c5034002c084154031004810048246082c1040d030450419107140d000941c6400303000005005030094091100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 200973030 1250 200971780 200971913
    0x120515011409100b120712020403030503180106080618010b030105010b19090f03110102010f0903120c1202070302060106020613080f03071206081609140a020a110d0c 73
    0xc002d0200c00450617101d603108403000c10401c0b002c44011000039006a14034500031b5042c02542e05aa515445080c116600e40409040000348507284a90703a42d2203c40000b40b001e01441518047e02d01050012081400c4405031429075003218021800b80c0c0c90b01d80100705081e4a00c05852400f004200f03403840342502a0342c11125001540c10004880312902e1001003013250a40d0b0041c40316400780c00900c41c001d041d00c003000844040c0e1b600038000c02d02c07140c68120141c01c1988411800070141c2058041958101050012a000035000300c0241c0d10a000501c00a5010081103911012140350306070b40d04420799841b103440c01192100d074030551000c00031030382c854081c030100304000780e241d441000b5559031200080e176244141901f420b00e2980d082002b1440704610b0040b003095110b010340901c055181c0f01c80782c00095003c0403a01c401c03c400100c08045c42d020030700c40102c66015958403c1403085050600b5a901c0038440e4050550016001358404c0c0c15101d080c3c40100304800c401500c49182d040b50031103 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 200974280 1250 200973030 200973061
    0xb0a0512010602210306010e0609010c0512040f121703100302030f010c030c02030a2001020702090405010c084c0314060106020a02090a090813120515011409 69
    0x140d0003032040d002094041d80014001401e1007540b40c0f00610100341c07a010000c034030041c0c61081c0080c900b00c2107410a4100b041c01061072078818075040c0c00c100f0094072100e00f0a803100703800e5681c40c43e0000d420020640041c0d12113002c4d00f82d442507410380d009203903508207441a031000c014039801030101c0010800100c01c281c9200664010341a20302c1840448801c500174080e20511a02203890300400c407180610002c1902c4050307000f500c0701c101805007040c0b40105060220684402e541d000c00c06140142c4a4090b080d0040384a8000130960a141070310142c02c42034002d000040204205508001c21403540030020000206520303e076038941c807003103078030558844400d00c00190590300c1c010000800c26840d102c0c06c98480d03400141c0b0010390b01d40c0d008a0300e41040001c003a50241c402008508900c2c079a40c45600503030311035000e1918008401c4000480034005600c210b05d2141d54030008001d01005010f032844100010140c00155030502d52039040300841035507010701402540300060140d08180404 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 200975530 1250 200974280 200974297
    0x601090b19080105102309150301290102061003060213030206031905013302030408070303030606030c140f0906070501140106020f0f1207110a0b030105010306080c0306010b0a05 78
    0x7039925604268040c10066030b001c1102d418044002414003040f0b0b00d0301801182080b006190f006c0707803034200404210050150b03420710380600301ca40b6240d50240319002c030700441e134044440c1b0303c1c0350290994202400c0f0004039040d9007024080240844d5008c50000c02e603a03000c8030042c1c07141c089028108681c0415003000f90448000402d01000350f0b480d22502e05088d680000501c410307030300d4409801201d00c0120070307a10420420103402085038011080c0085000341481142c1c20540d0b00e00340c40345003020720361081c0e0200c3d40c2d4080600c440761340b600540d10003d43c94103200200210003420100c6500c40c42d210020021800b00d250385480c3d4800c4200e6903101e800500a03c46c0800d9452036101040080c4520b00240c418002890071041002c280681e403204a08041c1400444800041c0c07902e03840240e003160740d102c001703081c0c002c3c0382e8074580c1c0040502104400152298144000501103038210703082468198094141f500701640d0005019064030340b6600708581790105840d0a4859020710b441 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 200976780 1250 200975530 200975569
    0x602071a0d15060e03100905330a0f0f0203060f0108093a1b12090b0c100e07080606040906090203060411030c010e011b0203030f040e0421020601090b 66
    0x42c001100d84c1c0c00042d16a908004500f80c0305581c04400e4030760200c400c40700004105400c20000800390070207a003580040c550f5106074000c40c07004a030200000c856001c4071601d000c0340d07580302000400c0c280c41c0f207900114a0f0f40b000c118075505000002a000351100e880340740c100f051000c005000e024081c081100815903030003640c039070340e8400d5480d119442c03180c032944001d0510b803520a00c400e52080c3c890841070703082c0a149010002c0c603901c818401034001e0080384184551020700003220810300d40108941c446031000741c08486041001407098602110030003055070b00ca6142481a00e102188c1d841d00500211000244a0107515200021303164061002c0c1d41801038004000a0084c2d50555600c240c4048090301c2e5541c450b0740c01034a040724503810490014a40205002c11a000c90303800340607880c00102100d06058070902d044070b4a9219070031805010114100b4042041040300501b80200041c0580341c65084109200039a0344405126525806450310040c5800d40c0f18200e172810300c0519101d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 200978030 1250 200976780 200976821
    0x30c0f11060a0e100207050108010306020304020312030903070c24120b0411041401090315051f1412150714070b010b04060e0a060f050c010f050f09070602071a0d 71
    0xd10180040c80043d11582c02203042c00600c2e07000c030f4030104040054a82c142c4841202c2d90842e283c10340203400c0200201d03094030520484160780c10000c8e01451080c61184007e590f1024286002000329105130300c2000000401c04c02204020807217502419400310510380510020244100d442c061701310350311401d81103450319404402a10b010001002519414480c5407801c01c82d4000445034500184006846184101d5006401550a4100076008088410103d00b500e603400d410900c3c0303c00c0e035442040c855801da00c0600d1503060580201c0760f00c0c56614050400900d419800c3c07401c0c544000c0c143c1040102343c0c520380c81c02c1500c0c10203407061103410450700c6c000d542c2c40382403120041c3d006004010108201d0226507001c0e1402101c80c8080c0d4142e0b075288002e4041e0500700769034a1300002104580c1d5501c0c8c1400d4007190395144180e40c401c94100300b0702c40d15401e240e003645040c0456a0018001c6401c03008090180b400c2419030a0241a5000c41c0c039a40c0c0c245510452000300585580305c04034608a8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 200979280 1250 200978030 200978047
    0x6040308130501110d0606080906070c03030902030a0b09031b012906120f10090b180a0609020d09140d0c0f02010c05032206050a020c0d14191a0103030c0f1106 70
    0xaa03c200155080c1e5100c04040727488a22500c1c0d40e9420440d070b00c400040b00c001c00b0b800080d109411004042e803000c0c0868490f01d445641d04052902d0440d84107882d9480461840c03c9a5119801c43c41f03111080b5000b040250f88400007041e0504280a031600c0c0805101d03491141a00d45000b25110308882c4c02c0001450309200c10548041e82d415600c00700c09980c0c001021500c0743d00743c44de220351000024000701c0845e6a0503080c0554a07801001e401ca181c1c4d4a5400042a030018001820f152504060000c1d95021526022071000280b0703030007001d40d50102e00303400441d580207082070401a4014800c0740d68030300716200494020340c202e82e0042c400e01020510000e41c50059840b030171100000c1123900e00b01a101e000440d02030150409900040e072141060b07205505102500c6822140602c4010040007849066540340c810004039441c40c040844065000b401007151400705015003400d01043c1c95491602c0060540368036140140c080c01180c840783d82003007940c40c10a50069800f030310031078452009 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 200980530 1250 200979280 200979307
    0xc07080a060603020f010e031e031608031608010f0905040609020604080d021002030c0a0c050a020d150b0919020a0309050f0c030f030901201218120604030813050111 73
    0x743c0300881c09422103036682e08132503008a00301203200c0300c050000c04042e2075012820100060044e840c2d40310740003c0011080161554400303c404074000c950444c0e40341004040b003d40c55a59000e0013040100c4a0018440c0c139100e0f07081c00381210103001c0003060301e456074104000201203054000f0b51001001030b0009100c040440c0740401c004082d000e441c038080100c0d80b40c6050b0310049440f103099203070401400e061a8011294003210078040d4003124101c1b40154046041c001c1d00c0701059840c000011042c000904440c011902072000a40d01c1000d6030030890340c0405065600d0321101c00701d50300416080321503440f80e440702c041d1541042c225004441540c280603210308000ca091030180c05240e800c4007002c0710000846641402c1a0755a118000080c2c1e440b845d80c00800c0c0040c03456010b2468250302504001e1302800e810038603800f0380c2110300c00c4a000c01801c0d60002c1c418140c0c40d00b20b80100b0011940010000d40d102e000c002400c600668070f80381c240d0043c9800c60307000300084000301d0807a00f080e00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 200981780 1250 200980530 200980541
    0x30c060c0709050a1b0309020f040c11160e07180501031a0d030807110106120308040302120a050406120504050c1509090406090308100803041a0f0714010501060302090a0b0c07080a06 80
    0x200d0400c150117041c0c003a60110103695400c0400317034200c80300b20350807105801e10754004003a041e02c0d480d080c00000c48481842c0d0170020183c40309000e2200d0701c3c80c203100c0c4100b1848203980012080c200141034580c9145c5207180e0a046105003414190f44481510f0503d20704145d21980708802441d402041007035140141c844042500d040d00020000708508160702814400d90090312030100c584910210143e07811101400300a0003101140901a1040d42090200c0c014104402640c0c030303803c4d191420300388c3c014490501c02600d442503038241414040400e83c04940f030010360300141c42e00c24440c0d88000c4080c0ca0ba118a4000c1500110a24100401d125059000f80c000d5486039803094441c0e01e0b20f1001b03440109860262103020f80080008008840350101c03400303900e0346820313403403030501919540c0c0c4a00c5030002c407000c0d211190110741e0a20340032001c0c800c19001d000c6604007141013030782400120385203454600400300a1180000e0804100400300440c5c001407540704220380340c08440d032425001428 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 200983030 1250 200981780 200981801
    0x204090b092a04020a0201020c0303040b0103110402070b1515160b010806090706030509100e0d1419030b060c0d051201060201110a080a0b060a0207030302060108010b030c060c0709050a 81
    0x1901c80ca03903005202d201402d00b00005600601554102a41c104002580078800030700556508102e13015101d0001e0005d58031072030254846c525a5891424042501c201036418203200f1841000703100c0020b0300f59030405401000c401200b00c085170b0400042002803644407200200050041030b0200305810140a10701c11500c20a141c0041c1e0741c0c0c8400007543c4480517180170340d0942099070248045072113944200d03030108049080350b054910064840e41150031411328408650003410000c2a119006140c059028060288003450400b03000584054113410303e9044041588034070701400b850f5140c005590003440c81105841d00f15141817006000c3d940118020101c0c142d80100002d00d0034018866030991580078501c1c149001c42141c8100d400e044003c245038011942c0314001e10341a121240500401c40541d001040b0250841c1006450100c05921606d12030703040a44c50348458034081900e035241401601d600d40c440300003503000350600000e13412407900b90b40b401c01002007051030b41d0440704185 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 200984280 1250 200983030 200983033
    0xe040f0813080c100807050a0903060c0801080c011713020117070c1b030302030301030201050d09140309130e1507120207050c010e030d0c0803070c06050c04050301140403080703050c04030204090b09 87
    0xb0803c160034441c0c00f202e1105610b0104030a00001845c5600900080c125618140340c4a103030035440b65606011540780c44c0007040014840c2005100c6810200400d000700c072801d00700b89101c1005402d05000b8024020308207032403545031020450859004460b401d00440d8001e00100d000e02e4085001040000b41c280203580013441c070040c81008019091f20042580c6d05a809185144e080d90010745ea00d40c032202505000a40d2900325001043d0041c0562442c841254041c6644090800400003003180c124002e10a0916020000b0a8000c0000351800d1052030405103001558508505680b036940d01c0c4006000b40e40001861020807601003000c8002182c241c8070501580100c4c0c05240e40d0341640c2400d0800700d9a40320308100440d55002c082e6078002d040d8500400031070400d659480560f2001da40311210494081010b1120746000c1c0658080c114260b4042e19403458282c41c000c01c07464020300300310180b55071100810260000c680455001e5074000d0001d0240030043d140c42c0010150440d0b4105e881e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 200985530 1250 200984280 200984293
    0xb03030301090c090e040308071d090a09020906031f0c02150f0103060c09050f040905031e03010512030a0c0b090109080c0a0c05040203011214070306050f0103030f0e0603010e040f081308 82
    0x103c2170300c450014003d640503503810000d5941c0740303c25610301c800ca154803a0f00c00003d0b0b500b09030554400c8420391150b00d441c480450201007520511014040242c1111700c240c0005903203140d4100010710340050841503842c08160844910000e0f130618050b901201c00d5031105008002c0c0340700002600c28101c0c5c0c4180410002040f604d0411241011070340115a0303c81040040110325180c603401842e11107000380280c3e0702d4901040e00550240c0cd001581c08018103000c0f0041150b440c0c02c1044c03107042c0303e900002d1885c001e540f0300014020035030b0302d2000702004031040204107000380035804600290360024441e0741e40e041e501030071a920549030104aa0064000201040c141024000c2e00d048130110141c1d1b40d0f11203815034030001c6086d8075900c0e40e00184141e01001011515030b01500e402003500c044281c2c0d5070b5055080c018002803035800102e050064101003482161908030480341102c5003000031403c103403920f1814509800d05218003400c011004955184c600c02e5050f4074030101c03840758040b03940c03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 200986780 1250 200985530 200985539
    0xf0c031804020703140703170112031202030c0306150904180b071e0c06271e02010804020d080d09061b080408070605090f0304080304030201090e091f0b03030301090c09 74
    0x580c40707403d50041c001808440310008032640c4501800f001c82c800e090806214110b030402080840d800d0707000f0131451140075800d10130301d034024101d051030740403180382540781d807901c1d8144401d0361101800f82801000180d03000d000c517181400545010813001082840740400c80f01030411010b01308242920b00261b444007040c44a0302803a0001c0010342c215226042194211400b650418001d42007030785d855480d01c0082c619081c0212014402c02641121464942c1c0d1905104002d50601d40d03203c0c1142c2244521400940e0300019101d511540c100c070625001072480c80c0c98401c500544280c50840f5080031801803c00401d41c101c981401c00ba40b90071722614180403022240200c055038060030007401040070304085141900315075400503503c411502c600340c100100a246a01c59480300440f90000300d020f2003150ba01094841c01441d000d031003480d15040c1020040e440f5104007594044c00c2c0c441c02e040f003691090a80124006400040541c0e440f903940b8000c10300600300c240303080800661094030116 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 200988030 1250 200986780 200986789
    0x90501030227040641180303150109150801050306070f0e04050a09020a030c18050103110907260906180a111f020102180406050f13020f0c0318 63
    0x1400d41090700c503800d25807116168100200400380e0081d00d0115542c0300c0c1c4d4000c0c0c8000c00103801c00034000c145e9110302c0a1090011501007800340034255280c280c001076041d401030010a0740c0c0c105120b007805a8a0000b0f41e401070314840b04550000c011107510500198049800203401170494202790f00769200c0ba5100c91003211401c1f0123024540c04646101c15486081c00c00c0e40c08280c1c0099844000111200140c0014031b01071140d5000300c1f44410302040a110152403040320708004003012005101c2d5504654404140401e4050443e00480c55107000070b10b0a803154984040382c0181900030803030700c0019003049400e56000c4883d248136104800116100f20f0044207601044248400034003041611036880c84008461640380581c003e034035411040360701d84842c40181d10307a00e00e9000180d440524804c1050061108040c452195150403000c00c025152540390800b09001114241c490b4016502020000c0c0504000030000581c082400c0c0364980c0000010840c0c20680c0e50030310100c454080410 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 200989280 1250 200988030 200988079
    0x5060708271b040e0703031206080303180c0d03080604050712230906040f080a03110a080402030609161502030f120f100b040e06040e25080304030b130212070905010302 74
    0x2041c4d90303003c503804101291041c3c044181c2405240310200c1c101d542c0c1c6440a103035800c251000001a803506060300d02612040084d017651140030749030007944031000d86015101144c000e03c51070080da214070024104034400c69000c0420944080e0810440b14100c009100100301c1e40c01200c0003850075800700e030641c8000124240715983c00041a84240c8855641c10700b25042610a50f060644a040c560811030010f0042c0801c0060b90f40c80803e036203824010075160100140501d0615044012803452804490410f0780c06d4030f40e512603000810a618108134a076109032040200543c0713001c5030700d1601d01e543c04141c41c00b5004081c0d00c0403450721015002905140c1501c42d8482d0403504100410100e031502204540c448001400000c91424010046041c079184406e00c4200c0c00f4480011204080391414820241c0b407041c0056080a09554510400c460042c080d13070580b00c42c1c2c142000455440a600d00c108031001000d0b100c00700ea9800003400a84400c3c00100c3c0b09411000d480032200880c400207 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 200990530 1250 200989280 200989301
    0x1b0f0b060a0e0903041505120a021c140a1a0a1805060a0605070b040807020d06090311030f030105040b0a180e0105010902070209060904081b0318040905060708271b04 73
    0x44c503d401c1c80c0810030a2190348142142090080a10007481100014405d442c410840b04201581d0340100c1c4043c0b0051402d03a400c203042107480c0140f802c82c03060760090980e50100e540c00340002c102180d1061030b10782d4984590042d9000ca00c104010564051240c0f441c451022a030f0000d002940f6203e0401141410798090800094400c1c4402c0000c505001401a00b00780a298034610f0156180c02103020741e05036100540ea041e0b200e0800e0301c00c2590113890050203003d10000345040000040c03420800d88018410310b4841e9481c2e507120403482da00d4101070030080156030746483c4184010390811000d8a8140c6240c1c0e119481c040c00003035615418021101c04940c0117156020b65510802005010b40d4090820703110a4000e04c5219005201322000200c2c8a03d000c0080d0303128042d10007020200c51241c00c20758015802d2010140015800060b1a44c010300c2c0c03801e1000031655100680183c0950407030500842e00f2820800031600c0c81c0204d00e42101ca0944240c1e0200801d015042c40b0940324110304 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 200991780 1250 200990530 200990533
    0x3030206040b0408040e07020307020f0114090d060b180114180c0d09080d091e02030d050a0e0414010e0a05010b0406051b03040303030c170603030304031b0f0b060a0e09 74
    0x10300040c2c0400a21607020744690103203410302d0b40710005c698001c402100d00c040540e000164230400d502c0c0c00601d07509040c03400d00c0c0184075000b42d41c50f02031182c002e00c10058051484000d8a00401005d50810b501d02003016141d10111151081002200d00f030038131440c028410603510f4102c080c20904001c046800d01c00c0880d11958840031b41c405602e07803005203070504441d514421003001541341401030408074400500031510008a041aa403401d100c4648d00c0009421400284c3c0180c030045501c1c150302100d070500507200c0c50b440200f511000c040301d04c020751291402040c45059800042410705a42d400c56051525a03201085071080740c0003070040002458040c8420000284201d0084c20f40030f00c02a1400017030118000100d1440e00b103504101d001ca910354503503c0c401a03001d011000313110091882e640280c00d10201090326803002500141c02c01c51405600d0011040c054000d09805501240d800c03c04605401d04460148060380c9407442203000d0701000484010f034042d0180501080e00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 200993030 1250 200991780 200991793
    0x17100803030f04110907050d060807240513030609060606030504021f0504050405040b070e03030a0f0807050903030c0f0c0d031d03011d03030702010605220506120f160f030302 77
    0x700030040d2007200410490b2503110303030300c0c604e180c030b44412103954024000c03a2030741c90715003422502400c180c03071441d00415520350083c401001b41d82c110802086014501c68082c0d0f41300c104c106012511071184441a80a40da8000700010421145a200705682e0b03011b900708001413511810224113544c0c0a0f03d01039444103903c1c2209695118480c2141d85610050030803514259a072004038095401c100e40c01c0d01d0710b100e0300c020000c0381e503003102010702119021005140360020035030011701810f0340f21040b0800c0120b03410014180740d00640442c1d05003032008003107a440d449a43c00d031580c0c0d002881c2e4a811540140d440b45a0541070410a60383e09541c99214285040f003003500040c035900382c000700c841c1c1c590340700c6820000c580d21102144401c2c3d140c8001444c0c0d01e20703240401a0030b4078005d0340818010702c001220a030100ca101c84011503203038050480801d281d01c03440700045020f114040480e00c180141020a464480001100a90b42c00e060303c16881551b920140c282688580c1e11004e000b40c3c00c01d5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 200994280 1250 200993030 200993041
    0x1914060c120f0a0605030d02060a060b040501121509110a0f0e060f0708070b1f06261506030a06260309010c0515010b040602010e0c0604061803050303071710080303 72
    0x25003071907800f608942c80003036120b41e40c1c80005e03d004420f8a600c40581c100800f0300101c9407103405140b02070680117a00f14a014079020000b080e00745c01100002c4c05a580e0191174154000c2044204024809000280829001c407416000c2d65800001002c0100d915145101d42035402281181444000104407608000c548584100180d006010484000340c0070802000080c480b03400031b60043d03020440c5120549007a0114040b500d400e5003010003880356980c18109030080189000000c02c00140740800300c2e071240d80b07892060724030080480340c1c060804410407100c110254000401c8800190100140001500307410340645162206182c00d60001c0114900039400b400d60000114800c0e4101c510b800442c8000400b0b4a02c2a00f0042c9241d1b00010f04001d131903824020711500c6c1c200c04015000f14501c100000352548945e02c10701c1d050241c00040e801000d1485444c1800541c1c000082c1e070796920300400010000183c082d4201e002141130404103544480c801520402d88c1e000000952a54664 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 200995530 1250 200994280 200994301
    0xd02060412030c0c0e090d0813030e010c0b0f0910020702060f091503070f03050a0c09031b09020d0c111917091201050a2003040609051914060c12 64
    0xc1607040e002d20615060000c0001d000c00071a01c0288203210032441c10341090060715040c100000303800340c108880442401341c941c19014282c01e2490380360400010000b90b90005903096000c1003400b400713100c0b8040400c07543e00c540e8070704c0a11402036442541ea000b06501c0c140c3c0128052124069000041840b49004194000d00100803c0c80d00402c7d1b240005003800399050290700403203441d4001200d0b682d00c04d8802d501030140355042031203650280004580d8460040901c10716100180c0050f00d0204909140c09800c4c6008000d070171016000d556400b480d40000f4003401e04100b2a000086070094550310848020909001c900c02d144d101c80c01e411089d0f110820000c0c80d000030303885803000030882d41c5419520b400741d01000c3c41502001266610700760034214100c0d03160204000c510750300b02d80c2400c0039992450803240d11a5110400240300703404c508080d4070f0028688080c86c107007030412120f1400e0160f0b900d0082c90125844044aa40e0b40c5c4810714040940a901140c11900e9000d20114050303005 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 200996780 1250 200995530 200995559
    0x50304140a0b160506100302030c0127060207051512071409060c01090606051905060f0702031213140d030c1511091906020a0209040303140106050406020c0d020604 72
    0x180309002142c0c0324060810700f5445055000c445216401d11241004400d015641e44089214410303080c1501d1500030030b8440007a03411040c100051003500503042005400c9803c1d00c817440cae90008103456281e00000e5a00c3d039250154510816003445102c0740211244200d40500200c450703001c4285d222814107480c490758048018682080a0000810b03944a00c8040c01c240c01907940041048080303414000121851a00301d58081c0b07601c1d01c0b48003402c58010507810304880c005d485c8907079240702c200703400d14080c003d4103c0203500d0300070800610601a211380213444002e441c2451941080e95504814201c0341da004056038118222500110200b40a209000202e50040300940654228a420341d81100c08061865010500205100c90305050000c0f40c0500300c7c4c0545e042584007401c1c09000382d940c50403104002c1c8280032580c00641014802d8000e02221000081101d047e96154440a0000d400c54081c1500511a43c002c01c0a00d2412a800080382030f00030f0401031038141000c040086804c0d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 200998030 1250 200996780 200996819
    0x9011107050301090b0f0702120a0e0a0506070302030703120b0901050f01030f0c1805030106050a0e0405120705060402014d061303030501080a08031302130c08040308060607050304 79
    0x10414000744585080c050150620701c10010760b04149045240700c0d25000c3e01a00c00c034115405441101d44000490084a030107040c94140224020206000125078840c0c5400c0329801540224a240405030000060402a0700c04d0300e400c0c80759410b0a010000b02c07144407000e2903100358000b004001d1414400d403004d80100303061401240e44201100250140d40d40f0b00031000018140810001442640401c0355001e054124002d2007510720708400911100050b028080c80026100d002ca010090b08202104c0f20034420a211f0361241031a041c91902d42e5001c4070164042900c080003105601808160768080305c1d074000c2d00b00c03d801000d0745010600001140800000d40410744c221001c41000c005030341c45020003448840b07034802130b468010143d0344180c1c0000b41543c0b1040030b450001d40f92100f600d90104070000c1040031980207000007801d407940501c0d4801d00c607113060f07220203038154000d9041d8800d074080d4489070301c1c2d41c841100b4001310744540e07800134099420a210901c10840c0394942180c120 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 200999280 1250 200998030 200998033
    0x4030302030c0712090f0b04031a330103050c0a0f0f022103040215090d1104110409090506010609050f09100b0f0301080705010f14070203071a13090908090111 70
    0x34005685013940540c004000358081002400204961244482c1c254080c00c41140744505042c0b6503074800304002200303c3c02401845031b290004010400c45440d2164100b11050b144c0d13a04040a40c0c0450142598081e4a00082c10600060880b004440c21281000f081c1c0e90303800700c4000650030803a084a02100000214083c544151304081c2e450810a0b211120304440130756030741054030401c03000c1440070440c0305520000744016400c50b940c1030502c0c01e2264103c1a500d6200c5010700000c0c2c0280003400e06962000000b1901040c200b8460307000640b00b600c00c03412155266294501170310402c000f8801c55a01401e4a04c00040340c0c10502b401c130b5001302c28050b140f10740e191034040000258000c02040c1d86c03545008401008464010001440140406e00780040703805495040100104d0b00c0041c0041c3c0707120005403590442d107040101030300425007841118210140218501665801403441d9000910318843c04540c81500380700315043c02e07500510207460890281d0064580c0c03080b421038154203 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 201000530 1250 200999280 200999287
    0x40812010504061202041d01021c0b190302010f020304030506070903030e0901080d030b03070509040f02210a12171006030c081909050a08130620120f0f040b03151804030302030c 78
    0x4002c0700340090021900d040003802b80d4070603c016a94200ea8100442c688501103002c103031302c9104e410308001c02c1500c1c0c0a18000441e0180c41c001a032540c03243d80c2c001002d5101d45400c1120a070703444164134042d80d100350b40d841d006c84050010024001001c1c0100e404a40018843c00807440c080e0748103001ca03c0c0040e05a1f035a00740d4810002da40800c046074280c44424002d0006021403a0034000441d0a004107003041e8138400014041507610382c8a82c0d00186025810902d503050306008240c1d4108d801c80000030500715180c1030080c5a004002c038414400441e0500d1840c081c804d000c0c0781040c2c8255808088021b954100d0507401c2c0141c11060010f076181d016500c50080401c0300000205035a20172540072100d180e182c038400802c1406040f400d00050810000c54626058010800d400c1096128100c01d44031050192480c2c0d1522a404075500f0426000900141c00f41c004405144121211041c41151200380001d00c40c80004810807070000070300c00c10018000034084e501940c0c100c209500510304 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 201001780 1250 201000530 201000581
    0x8041505130c080703020f0a0602150606070203010c0207051e0306060d03090e0c0304020a06110c130b031615020d0f050c0a02040e0309040b030316030c0809040504081201050406120204 81
    0x1a0302c42d07143c0040d00c284d0004401130080d402c01c80c0c02501a410b041e1100058507103064070003501e503180e08aa02d0821500000401c200d550780e00d0559405a400400800c00306124410103981d0780710340d1003002c1c01100001e02c104048044604440419900540a8962544c800d400c0203011305c911a0100c0602010b1440459011954415644100e201c00da100c2e81e02d04140c0100a040d10982c2d10000070410664405801c2d9000420302c010b9401c0142c0300e01030365101603407903140074008402c001505441446c14030000508183d0100048940102d000402036000c103604913120400e44450001045121b010b0200e0b00703120340b00030301e40301110009032144285c45900103000c0e95001e80a1051b6940082001001842c0c0751181c441d600e1812401946440b20018142d10580c40200000d82840350304401801402007a400b00e440311a0024000c0200c0d107400d18004c0e50710f4010300e188803601d80f100360011440e81410302c03501050306e11000e8560208080e6508000c09045410b12000015012964018 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 201003030 1250 201001780 201001793
    0x8090706111c020307050c0f010e1e040c02030703030e0c06070b0a24050310051009020f0c010e0a12020a030801140613060f030f180335010e070804150513 68
    0x2d031441c0c0507038007645e500d0143e4200149800e01031036105116001000c60300c0b101342e82110807084010f50030740b1510006543d04d8116130070914514566a00641482480c60b02640d010009001c0b0324881e807402c101503203c010a99a5480d40100000c3d008041009008041650404510751107969090b011400080c88450040841e881c400d4a21141c423070000705020a20b0700348001400150494030400c00382c6000c008100031031480c1c2c4112500c10303500080c181c64000010080351071342d0401d00c0090005001d000d10700340d40d0311111542074550071402c1901c55002d0b4030200d40d500480d60107959500959082c00b803c11104141071841a0340143c0801c19801a4201504003100070080358590400440407000003a003600c80c20780c1312050492500c0b03043c032442c6d10034141e602c3d0100d0305803504900300040078405585240b640e01c0c13800c440ca009080d80000220040310f031181620100c1c2c0d42040f403500c40f020162884601a6001801c44485004c5401c160019501282c2e000c4c40e800040385d08102e080d102c00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 201004280 1250 201003030 201003073
    0x50304021c121d0a030201180e0f1506040e07031a030607030903080117070314010216080a090501030b011709031309060807080d090303030203060a0506030711010c0809070611 77
    0x1c41e05401c00c01030410001ea0003112400d1003c800c141c1c90310200d00100c0028035544520b0200034180403030700d143d10040b01c000032202c9000c0c1010480081c4141414000e60b814070100321420060564001c81140903800c2107010b5604171003401100144a41360b104054024259194211100c010995800f401d1542d0401c4018003030425034400096170b00c424140140707448416041100600c1c180500302080c19800200e01040f01d400c040380750314012030150b8050281c4071310078110000110390000542070010000040c42d04a2403034444540081d500c80041d81928114a00680841d60407801321300e0181504a01079030204405055a181c409000070400110b11941c00082885503540000d001c100003c101201c040d2405d43d0080a0b03503004810010140f04031800000c042540100209940c0d4449090420251a008100c2d5480c0d1500900c01010400c10301380540c1c1940c00c0031510414940182c40d01e6002d4000040940603c50920500343e4200d180f40c602c0e032215125110f04200312140e9080da0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 201005530 1250 201004280 201004283
    0x20f030c070c05090603070e090c0303031f0504060b041202030c060f040603050112120f02120708090103051b0f1605030301090615050a23070606030b071202030f07050304021c 77
    0x120762241c0e0981061004414150805030050704078900f03010b0640c2e00000d14000320798914002d0300880d65000303546400d1113840320307445405100c040244209485141c2c2489103806103030b981c4a8881e0f5980c01040166a10f0788240ca6082c0b03c2040300b4480c0c0d2400c401220031250001e8101c0c0c01408420007c10955404011204040c85001c501400856403501881d0700400d2560b100541500c80e98a41283c20448207202c0e206100000a21200040c000d00c2002d0521045201c0640c845049041414069200c1c124035400285003600081c4105c0d04040c0003404480b040b44200e040c06110302000300b442c5e002c007545020483c000e0314880d000800c00c100643c0a0300300b0520204101d840c00d40c0e00c1c0c1e12268660b01401c213101c0240090030b42550304c44255203480142c401e403441146016050000740c1e12904202404190a202c3c0100601c144491903d0061109944040900085041f500220300050b00d50400c1c0310748000c0030a2215200d40090764126000504207103504889149203081518222070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 201006780 1250 201005530 201005551
    0x9130c030e1b04060501050711010302071b0605030403080106020a0c0504110f0c070603050c0a0503160e04090b090606010c2a080601060905190e040318090c030204080c0f03030418020f03 82
    0x102c0c007083d06290140c500100020b0900d81c0c01c0c52143d50364071542081d400491410598089144024003583e40040e92001d40c401212580e1300c0e44423040100f55500440c0e058003c6002d10300000b81e25031002840345032864000914084070750a20042101614045801c058040028410100c07220f407a9001011840b40713000c005c08641b840c1540c090103441c0e00a101d6400b803d0107003c03c1020a4120040702c0d0710003400040461036a803a440c041d120010000741c0e8942182ca4004800c0c101314003800400e0085c1c16071000c8440030b075510401141c44000c60310008210b8600e60b01100c088140e4100800c071440035071200e882c0140c0d2540061481d00d18240d002400042c0701480c00c21480c20003090f841c4800c9426136410046a0a000c01525045c1001d0802004c0000c0c454807038000c2c0380391200e0b03000500103400042c0b00c43c0c0c02510004029405c103000d281c070700b4082d40c0e0315541a031401500320360000f203001e0060f43c101450a40c02d10300400202c420205059001c01558001c48001c20013544102c8194a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 201008030 1250 201006780 201006823
    0x1807080a05010c030203010501050f0d092108010b030112060f022101060311030c04120f140c011b0b071b0203030301181a01050f0708070209010311090a0209130c030e 73
    0x7400e03402d4948403030040051503c100010f000c01d0341c0c071070200c442c2e1403401961640d4402031602c1a000518a900c0003621481c100d00c00d0111201064024440c80b1a003559102851790300c0d100800507600c0f0a02c20801a43c0c400c144000c0015166081982140c240800040c1408501e0041d840b40d0801903140b0320440d0b480000502050b0b415110700c160501c8152a13090035880c0c03000b42e04030240304a010341a10a2242c5038040704212411b03089509142e030003401c03403500041421803c2d54440403070031240d001c222070f001c01d1000c002c11f1180410120b40c10003607891843e11014016903100c614000e034a0308111340b07000440c001d600c2c100b0045000300712409894048100c40d1003040704850303000381c22001d03541d030104481c4080e0f07030700606a48010280d119007a03a20700c0c0c28503040c1050b2040103002504a0543c1e0000400d00c91244d02840c0c091030b050390b5810681c0d883d01c001c00d040b4440d40c9840c6501200e180d6450000804982c0601c1d43c481080c02d0001e046c8039505056450809121941140c940404 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 201009280 1250 201008030 201008033
    0x40e0f0618011509090c06020a0809040e01020d1a03150f070309050a081c0606110606150c0708060f091c0e0112020315030d03060302011205041110110d09030210081807080a 76
    0x6c0e81e400300614542c405084500740682d03c0e0291449082c2015204030784600b48043e007100290304407400c00301c3e807039810030080101442e8070f4010710207181c80510030300400780315000c01c410b0781e407485200e002381c1258240580d0b01c01c0019001001010015500303481081c010000080d06500201030040c00350b0200144034818049210a441c110340108081010160981d01c07036100c009030190700804110382e41444000540104451030003500100101172003682c1340001c0000000c40c00e6405590040e040c00302e55501c441000b9510508070600d52420b924200461601512540c8c4c039042c200814500b04680009420b485001c2c0c0e00190744142414404843c03180091070100300c1040f001c1b0350340c20f060141a11303540029000015508500d01a07079201c90004040011040004001c140c00038160408d1046218000b0984000174002454034818010001c0400e8003170b01c00f03402101d80c020200720603241204400c03281141c000d095120380704803151080500745814061100a049000000d040d0314145 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 201010530 1250 201009280 201009293
    0xb040f20010206070807031e0e060105060403200315090c01020d0816050d020f0a020604031202181c0c1403070f3f06060302040e0f061801150909 64
    0x280c020254500c900d0080c20540e41d8001c40c840f0743c04842e81c24031442d20b5031045020b40190000b94400b10303d810818000140c88016070f84405c4001c010401121240d0ba214014043d461055000280900841400b035501406a038013807101c3c08000501641d000e0900080082e104020540340c218080d001700c443c40840e03584c100308540303501c01c1c0c034070303204501e4209018221071001043e0a1a801c00c000024444010005501100c0461f2580280b02c0c1d034403200444001c4d02c5030001c0d13504600084070308660800e8644107000b591900b0034607030601c523009503809c41040801c10403400b0141022115400110114890f00525001040c5240d001e00203d4086020503051070500d8001030105541c0400510481100c6141460135004185070b41d1016044240400d83e1202e4002c07e800003001d0182c140ca041015580100d421a0700c00d0310103101d5482d4103103003607880b41c036480d102080c5035200900190b0701045440c00200c4241e2030303000016460840140ea4604403559800003048940c5899110080141 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 201011780 1250 201010530 201010553
    0x30b0a0917190c020105040603111608040509130314070f02031f0c08040f020d0c090606180b0c1b0f030a0614180601151110060302010915120f090b040f 67
    0x10b1803906080d0071015600207050b40c0070b1409a082010398234a001c0c402010440211041c07146814425004200c0d207281542850348107000c1c2c0e9005400c1c0b000131403c400f101c203003520300b1190f050301c1d00c0018109409044070613800c80c000655900d03148003a01800368809100c02e0300c4403604580700040301020f140030750042c1c400c1180d030401040403510800011840040c0016601e660440d9206d100c88a103080401c00d1420300e8000085492030414002006900b100d022050380303000042c0c0714042541c0d2402c10019002e103010382074064000310303500d101e10301065079407210400d070003410102c8601c6501c000c245055000b40c011181d080c0d0ba03004940928460001c419406421201185400c0d00044500b1741c860006116208203100c041038595401da0080280c03600550701002210000c480c80e01d401d802400f044e10040e8042132500c1c001240c0301900c0d04030b004092881d034481e0000780c50040998401000d88000d41c1841e2603440e10070100241e090000640100d01500030034601c41d10078203208030b8240f0b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 201013030 1250 201011780 201011827
    0x15020a051902090f0417030703050f0c0f090f03070801090807110a030c090218040513021008070509010e2404091109090f0402040e070620010b0a030b0a0917 69
    0x1030394805141c00581e1012052940000350b4901c45186403164a06001003440c8009646103591010042103151507060f44520306c5420386c46404074094640c500002c20600c1400448640448100010700460900400322001c1c00d00c050304882d04e46903110320785400c50f03240c884100d80030800011500c0501c0030f580001401200300301c5014501b04c0c0b441d901c0681c108403d00c16003c1c116008909804e1042c0b40d4200030741c1c0d9550140c0284040d10300b0860300d90001240c0c01c8c00300c1c452481c440c1e07074903c0180706200d03140c881e0700e075600d171789140080d03040042d00e1926213a826541c3c80050b4840c5000004819851101e45518001c82551140d0030f003141ea000f42e85868002c015a8a000d0010704203e55500c0c9200350400c003d02e40031102a101d5001103000741045a2440e18171380f160440000c1c5260b4412103141d8200c10340c030b02640707061819000a5082e2703401d035400154401358050050010590280a0540210446030000380c8002070b030f0b0319242c0c11503c20265110198020445040c902c00200315a500c25 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 201014280 1250 201013030 201013063
    0x80705010e0a0b120c04030506040609030206070828021c060303120509030703120b0307031209050f300a0c06110115031403041d0601020d0801081507050415020a05 72
    0x190420103d90444c1c0540950803142a0b00d9602140124040200302c4000d10740041c1569141c0c41d0a00f0904064001c0c10411001440f50000081281d8814881c0c20b0240301300c81d902080c00d4404245021080c0500b01c00550000d0303082000c8030745280c0fa1220704013050204480801e07210f2541c24040c0585108405101e8014284402c101441071701104a4225036854204130700080c142840e90001805a0000350b0b400d446064008405d011894918404214841da0342e40710f85610380302401850031240d0300d088d4000b403c441051001c014060748600e0140803280c4000c00d1500645440e52070410342e50002d80766440094002c0c0a015842604649080084d41c028018102d41e41c1000c07240d541d041c03202600c0c402040ea0355100d17400d814012140140030b00c00b00404000341514003240822030070385c0e416025100d1400340c5c0342e40301e01800008c1c1c101c1c1d0203c4050011908902c1023441c801100910f0281041010480840c501520010005c0403a219034020b0404007464513041d4034054010044407102c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 201015530 1250 201014280 201014299
    0x40b1003030905091b0a02160906051f050c0a0311100501080d0e0a050a0308091e0102030703030b0102120f030f06030313270e030c0d05160f030e0307080705010e 71
    0x2080d00400c40c2c03011180d040c2e54820036603403204441508120094040c1d12804030025030030500950000d40b4280314a01402c0d03100c2d0503543e5000007011140309210361900814410302d0514035030840c1c11024180502c074100380780b0740100f20018078109016160124080360720346030728014000c0308005c5002c2e1000020b800b04515410b092410b943e071003140500e0320401009079584181c1e030320b44802c201c0042c10058215405035440e4031b0301030340513040111018003500d01c00090420b1345034501d50801040106030091440c2810300d48040700500800d18889065110ba91103840030802d03040001c0180f09552401c80d42c490610100a510300b00015084074800d43c0180507042c0300e440c1c04081740040342d54289400380c998446010002c0382202c2c040411840c5890050040104107010000703115154101d0180c0b0182c034529007054840b40100b0a4090096074051843c2000502801015000c10700a0920744001c6840b80002840c100b01a00401c403941c1202500300410358000c02414814482150160f42 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 201016780 1250 201015530 201015533
    0x5030103061103220c03050d020c1e0105040b030a14070309140109030e011115090106030302070608010e0c0a020a06090302010e12030108030d0b01140d0c0815210f06010e040b1003 79
    0x42500c081c01004086041350301c0d41400c0248042c1880000c583c0300b02070b281c00c9050074001035203544000500c2e0b80a080c071240c0f48440940103002002542205840d101d0400b4200707421000e182d0401080200e0780f65132912169082d005030b0716540d1140c0e0b15560302003218859440d080000a58002501d08180c2c1802190390004c0c3e040184400010b00030b2902c222590900c1c01c4d150b240155055800540c030041e40d0500219000c103401c488140c0e800b07a02111001c641e101d80454031150b00740700b072404c45001c1d013002c107840c10800002424581c020b441280c0c019000d58446500300c4001070412400b5030340d11071401307000400078403002d48000b2810050f5400d41d0301d01206251a4402d0940d040481c5546903080c1241c0d82c040c8580302001c1d101c0c00b0030135480f003851000040003080750320b5002010410000014150644860030320300b80c0d0038064406035500910f44066850a0f102201007150382c0140381c1070071400002041500d00800000381c00c10464240f42c28042080e0501800014422140d05400d20 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 201018030 1250 201016780 201016801
    0xa061a0a0504050f060609010e1c02180112230d09050a0602011e0b0114040603060306060b04050112090602041d150303030f0f060d0c0602010e0c030c220f020a05030103061103 77
    0x1644a1021b5030150746c3c8003000030040f40c0c10a00460080e91142c078408444010346401d05203880094801d5885581001141c520228064001d201c0d41c82c445003c40d000000090303480ca04a1941e0002800e15200d1500c07013420181004d441d00c00032000186031650811844c500309151034010103c0340001c010b0701280c00b82d156043c540480140c20429104d5621504c140d105043d60042110b000e03200c55142c40e1035480c000c0c040d001d10310055900038203120004c6001e6500170708136011a0016100e900c020170b1044c4051020744407441003507640c15420f00001920390041705c4180e51400c482d135840c4216240070b4616081c1e850075078003094041c2c0e005000300180c603043c0c81c40c42c503001340400d030580324107580360000600781d040080c6c03000b0306501c4d0700080000c0c0681c054200c203441020350b00c181d845444507441032555408a901c500755202054071422142c03062a400b02e0074071080c482c03c0101c1c08400010112003643c3c041c1d010b89000480000040051002a1244c0c10884440c43c08407465800c0406d40700 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 201019280 1250 201018030 201018061
    0xa0311060d0c08160306050a0b091503010e04050705040b13050711100209030f070501090b18030a1406090a0b0c091908030304120305011503020c0a0b0f090c01050424020a061a0a050405 81
    0x103400c40600000c040080d40e441c000c00520401c0038000345503981d0b03153b86035244e1403c002c0d103080303c4901c580d89000c151854540a010210034000e0905e80034102003020400c05020060107400600107880800184400306001d03040000c4070312071b03015903100c050905242c07801000c11842d06081e0000101800141ea1140350709085500344055103840d0f08403908200c03442c04401c45c03041c3d41407040f400d04c02c0412207a0741c007c040641507003040d40c00554130180181d4031113003450001080c203103014000451950b681400b401a950015004d00d011001070642603140100c19041412240e10200401c0104500c0e015044c100710355609d801c0c4040d5240c01c10401140c10b1040c0d480c024580c0204070400081c01c10010310307050765080444d000181c00c00d000b00d84045803054400349158001c1940110b61940120200c40c1180c2c060070110700c500c624140082c4820415803038100450141230111341c049070003070040ca6552840403410300c4031903400300d003000243c2d22240d010700d004900b85800c000c124120207124 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 201020530 1250 201019280 201019289
    0x108120f0703051c0f0902150a020607050318060108100510030309030b1b030f0105040f1401090509120d0b0a090c0c0303050c0408030a08190b0a0311060d0c08160306050a 75
    0x46625040d51307403d5030400321071038031032840c0c260300c0c104081403022081d40003010440c0c02038070001c1a250710f072050b1071428425041d40ca80560311640104860901c600001c41e0300c81900040c14000081c0c88a01d00c0c01c201d403e920000d442d50085204a41000b20b611460b50088480000041810301c3d650b40a003210706030b803001130103c8000c08000758699140081d140c0c407c1960100c0c0b10790302c0c44e05080000c030048081c0201c6005a281c000003a2a042c0c40344181c060420840c01d549230140e1800d14003401a1030010a010498003c2e4100001400407503005010a030403804004074000d081034083c4404015079520500c9a2130402046101d019009039a210076030f07825160200d040c0c1e480d810041031511650b4800850303440005000381d2181d80c1300c401c03036000e414040d0910180d00d56614414090351007540040c1c0d8000c104400403c00118992003050035070201400c9641807001161544044a48008a5002140ca080e0800c80107080ba2906020004880c2c181002058204804101451098010f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 201021780 1250 201020530 201020537
    0x1a0901060f08100e19110313020d0212010903020a06151a16140d020105060906100f020a060501090e1c0518031504030302220602060c0702040207020a0e0108120f0703 73
    0x116802c0207043c00001c1c050142045080c0050420241d62130465980b601428005803400441d860740140c04002c503402203003100c4000c0189101a001c00520701a00c26013240d221818440d41888890213001d040c20082c000c0c0c000d403440c1e030180c0c200b01040d43e540c0300502c2800c00c0b4148061111108500300b941020050420b51600c42008911501c2c2050310850087c0c44c1d170618000d00a40004002038500d0940340507402840680c48500511103003d20030380f40d040d413025241c07a042090a20a50084143d600a803040f50071405090722a4400c1320420b8014484081d02c0780c8507806008010030a0300f01c00b0400c100010f0100085160060043c02010355a18a803076408406050b190740030400c89048103030408080b400c908092401800940c03014905030801080502072440c0d0203e4040014100c4800b40c0140080f6500c21190350a41c0e404084100c0c2c0c0b059080c01400c0243e1a4040060003030070500841c000254180300c01c1d2817414441440c0c20216820401103030340da513044981651344080d0f241c01c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 201023030 1250 201021780 201021797
    0xb0a050f15120a05071d01031e150614090c0a020c09070c0602030c1b03040602070b03070302040b03090a060f200702010306080f0a0c05100c03110f01020a02011a0901060f 75
    0x4601c40203115a1901611501200f441884004102c00003100d22104003c141e40b040e04940610100c000d200c0030382100c2202c00c00c09900b610070701074040030034407815030050111080c8964004079007841e00303c84451880e0030b1070110281002e00c609600803840458050400410090003940c48003034600160084145802050440e409540d40c80c1184e903200c00290f4032450f02640489040d00520b180702403201c0c64030201500c407400842180d096034110b40c00340c0002c03030400d40f010400c0d900251940c01011350070000010700b0070b0300078082c1d40a294048050b020b210000c0c1811003c0d90340301c10590a0841c5845141030b00c0c001240e02c00030402c00c080d041c240e1503201c107000580040c042c96102d100e50b4090061002014007000c01d031114003071301c0b48452400c4c40c0d80710410b01c14041003184002000c103130040044004070340075544d0f050821034000215050301030005842400da0304080240700150f0744403c0c0fa0150403594040c0100b03824000d8600d00c0056240002c000c00c0d140c00c04e07940209000601 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 201024280 1250 201023030 201023071
    0x717040222090302010f06050a05060d11041203050306010e06041203030504050f010516021015050409210e0108010b070203150a0608070b0a021c0905011202040e070504030b0a050f 79
    0x15080d40c1501c1200c408208500c18841c20068081c08407403a0a002d1140f84c448007164a04d4240b46041c1076401c040c10707150420001101c50001011039004404507040180300001d10040251200c4c00902e10940d185501c80c100580007401030f10030b03c00c00e1441a8014403003806295418030107440a036805107000b254544031424545e00b455540c0040f80c0003542068200f22406440c0c41c2110082d211640c200c81d0500036144024040b10c0d087c13100241d003110031070003c001600d0a900005c1c00103000c1c070280c0760899090f40d82d001304494482c0342e440101e0030580380301c4559a04200034500605803494400c2c50100301e540004c0c0c594400d800050301c8080d10401041e071100c401c0e8042809005002c0031108000c0e1510640d43e4107030014000c030300042c4245490b1502c643c0c00c47d444100030030047e0f2181d10900f410a00103580820f01c02840d0ba0b04036500b40700c001001c1247e030410b14060155512842d60729800e600702401841d01c0206840c5441c1c0c109802e1158140304241a01c0c3e029610009083c00c0a03041c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 201025530 1250 201024280 201024319
    0x10e01030f02120417180114210703060512060406050c04080d0519030e060c22180b01020d080f040606090903031b09050109050907020705100905030607170402 70
    0x1d05140350641403001c1100410021820390050003507000e1244004407074200e00740d018852251150540c80000d02012400095006102d011700200501c5203403403d2010f810300e28140d0f10703190351403060b20b080558203000e40c3c2e0342c00d44030b100f000d0002601c0c200d004002d556100c1e9a1404040c0c00242039642e074000140c1103055010680c3c020b442c0c08000e6030382c681c2d81400c0003030054015416411040c1c031303590048031981c0d0080c41103400600c03070903001d08820350b01c07031070a820140c216110403032070300c1c2641c0b2144c95001e110710108006406441c2107130700b07210032010111040302c03406542c0034103660140034000c055030340007241070f80e0001c071840c041c0e260b0380c0e19441c02a02504007603000498860400351001c0030190540c2015041c088a481010550a8020422990240140300c0c0c1400b1070941a01404241040711740c85030301680c180101c560180e696008a035206124a102c20000313007414405100a00e424440700350807210618003114030190202c2aa0851440a40001d1041a180c80351782c03040c092 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 201026780 1250 201025530 201025541
    0x3050a120905061b01050105091303083c0c040b030f100e010b0304110301151a12090a06200301060f03060302040c051201080102070b13050f0a0c06120b0609010e0103 73
    0x544803640b1403038011401544c8003144503540542c0d5082000110305810004070b502d100d524003c2a460000d40991420f855000015018001540c00a05804607000003410825480181d4844201000e03101d03510b116041d82c00034140e410301d200c0400081000482000981c2d030402c583d0f98202c002c9854a5040c1d212540041d402282041c0c9400d000181c800380c4500a03610403070182200742c0040200c54101400c940c2c0b10344840088044a046c02d001e400c240040c4c040b01c14612200e440c2c900001c0b540c00010403d0129901c0c8c0c05944400c0c8040d007040f455000b4120b00400e109285400d032100c82c080088a40814091601007080c050a01c0c220280f0a421200007983c01030401c0222800c600c50040c2298881c204054a41c1407030800061070307100c1407007215025500b200250b00603440303110328030400030040715058589205208002c05801e0090004e601d5641c800e0f06c034112060b1a040010f4152400035000e84007007464440b48040c00e40324201203031090042481c004048040400046e0014403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 201028030 1250 201026780 201026789
    0x3031809060b030117160b0d0b030303040c0315020313030f021e0c0a0b130b070219140909010902010e060310090207060603030206060303070f1e060e060114030703050a1209 76
    0x741000c40000341200200021030583d00c2100c5000b5061031041209503030760151648031080c02614140402c58441d01502070b00c940416464007050854003000002c0c6160010344043d01c1072203400c1d500300100845c91142d800034200039a425419032600c109881d074240d01c91000502800280c003411800c4034401d0068900802d114000780030040c4103402d0907695085035103c0701d401200524000303e010306080e01a10200c1c0345200d07102421a042101c075a000380c00101040f60004050301000545607204c5030144040c115081003442d02005440802004810185c40c2d207203164940380d406005030b40d0098040e40102000d0394041c2d500d03201c0b680d840e100b120150740701080c03851020030030608021041c0c000e80c0481e030096080307031443d1310b0303900826440e03210301031000f0301801c00340f680c92000655070715000d40b448040600030340c6c0c03100c81a107510701640c20b40c410315045500960010301c03560351411290400305c6001e40c000c04040c1d0035aa10a580c582044001602203a0300c0c08111028500c20828240500b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 201029280 1250 201028030 201028049
    0xa021209010615030207051207060915091a010501020604020f0f0d050708120f0a0f03020702130e1501050315220506090606040908120a090803010f060305010b070c030318 75
    0x189040502603000b050180500d20f040e02410040300100341c400c0c02910181500b0601a010032421860340d50036a5000d250111029a154010080170504060483c6517064206130007140304501031034082c160100c0c25500341d02528804005000a90740010b40961041e81507580c158000761140010720160b483d014610f5010180d120f11900300040420742e201265100012100050802080390b40180074085a41c10080c40c2805030300d02040c030507002d0800802050600520f040f000ea000304e040215010900f44419441e12000329031000108076948000b0058022502c80b5410040000d4503110760b09505411042c03007c1c04655400700c109d0008600100050320700d41d20300700c54680703540c8518007219511018040d0100140301802d2034001c2e4406281d03c03c88003031034160760109018441102030302401400d55100e8050000902c844001c6018000700d01500c2e4009103044401001c3e101c050300f0a00e540d1000344807110019084207184001d80382d040c180501c8403514a00e070804e16400650110345c0301d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 201030530 1250 201029280 201029317
    0x70306081f05190f020901081005010c0213020c010204090515040b010e120102042301080a090f03081801050405010e0c03070b0706090212031c0b01020d02060a0e010b040204180b010c080f030a02 85
    0x8130541d030380100343c0810282c0750031074a030740c501640e4200300000c1d226071804a0ba4554400c0300603e4030a0021011403d602801410310444501c2c0c28221b0704150040c5581c0390351382052183c0b4211102160401202c211802c0c04103005000c0002c085040416515005100880d0b040412810a405440140c851600d21a104070700b160840809041e620140d18045000d07070002c200e5900c2503001c1c0d039064642000c2542540034056a00300c580080040004c000003541d028142440042805010b000d81d02840020a032803c0c41440d450900300c07081810b900c260b0101c003080103135040f80800d0f05c46a68200500258444140c0049400d00b802c0110101d241d00001981c008a0144d400700c203144a00420010420034000e04e0040ea1b40b502d80610030301c00769110348001141b201d20380d0401003081580800108850740c600d40410705030f811035008841d4041103500070012074a413a10a1580f003440034a883c036602002a110307651588a0791001420202000000808040345074044a28a00341c02503000003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 201031780 1250 201030530 201030551
    0x209040803040c0b190509011b030c060c020c03070b090d1205031009022a071a120604050c070f0201021f0b0915060901030b03070902070506070306081f0519 69
    0x21030780c01202c08480c152034050380410329030540e10544a1202c0070013841c1202d40c001540589460304170b900390700d04019240307070550b400004040b041c0b0341680c42915180703070302c021519060081c1c840150841c0215441301c0032140e11a41c002454504980a1b081c1450b0b8828102001c00c41c0091a0740e0b02915400003414411142036104000358819585030501c50301c41529000180e00360f114000b6407262400e61400203c3c2f00110710350320f072603d0b54021400c82e000c80d60396801d038421a9038100705510452038003144c840340540001c4600c07580440300711810461450030807000748090207034480292034011328180c45011a402000014058569109164200b40c0090300a8014020003001a8016a840004100c0c40c6035018040301020350300502c141d0034036000d10011001440000390690745446400e00015441a50b4402001c18a014601400300b0307240404001e81502e103168042c004961102c03800681450981c40c1c002411440712070040303200e88030b512040030140012008590034919014441c0d8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 201033030 1250 201031780 201031793
    0x1d090a060305030309030c010c0201050f0a0f090b09011a0d05120705010b030712050c0a0b270904140d0c0503180402070204060902130f0506030c0c0a0503181f021018020904 76
    0x407c042801009121290009904a080c1e0f030081d83c04000c603402910102d03549000035040940100c0180c90001802c2c041500c4111780b0140079104825a41d560341e48000f038414403240c07100f4540c030054440b54100401035959581d81c00740c5e03101c05c61480c1c1e008101c803020044207404c410030101d030003011100b43c1d139150510294000c194030310803a039138490342e4860390070340c14807110010031503e03c0b44090b410a450103000952580112985440a881003030304201075982c0d80c2e4099005500030200303a00c4000040012901c3e200740d80005170240400180d4000000300004200e50889250440588900c45580702150182c002d07003c2c02980641412004a512a4603501500c4081c40455143c0d400955640c0c00c0e45c85000a8003880d9045401000090300e01e40d409030051002c009101c040301c1d1003081c0c580fa200c0c1150001020b24501d19001d80034900303245404502109482c9901d40c00a83c130311540300010b0341d6280890750102480340c55401d005030071052801c801c240c298001d402e0000501d070518090 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 201034280 1250 201033030 201033037
    0x602071a010f170115171f0b0a0608040b0a0209040902180f0c0406020c060f1c230c07020904030e060c01021b01090f0f06110d0c020d1d090a06030503030903 69
    0x440d0070f0003440416050b42c0c0d07014041c048810001c00c944250071410409807555640002504513074910801c01c50703d03144014040c25680d4082a40300004500c20f20b4010080900b00c194442402c03c02c018061002040340c1c1d084035a0030040e02c0b000181e48034690004a4003510800f23101035030100175041d140141c1102c07040007034860412202d1244196641c0102140300f4003030b07070040400581c440c4a24034018180603000303040e009101561541080300100343c11000c054081d181c64540b0b601c0d00020480d65585024460f00c98800400d00740c124031f800014024030f0702803160082e110304a9580451300f450b0040034515410303a4041e2110ba0384401140c680b82c041d40c008044446090000c01c68a000c038401841041c10a83c0c1c002c0e603030a428503054440b05415a0b00c1c4800b0f480c107581d00d0b04100b60300c41d4800024195100319480100c0c0a0641c80000380c00d04c00030182800600456144030710302d05005918035102550112442c481545650310350000821160300004c250388000028040340b401d001014 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 201035530 1250 201034280 201034289
    0x1205060604151a0904110a080c0304020f040218090c0c0717071512020a1d04060308030c0703030e010204170d0309030206070305071701060305180102160602071a010f 73
    0x22101a900e400c0103000480d81140501c1d010746204003001d002e294000c0c1100d10048040180c003e04003484035002400b142e41c00c81100200b01000210031403026002031800d603000482554541c210715003034020440d2039100c0507407036224039800109940f2945d803c17940c541401c40302400700b001c00c1c9442500c01180303a002075040c0590744620300d4000344c031411040d00400e404000c0406002072901d0a052441204114009402884503042e0440051a00b81c4081c04404c0b03091355842c071003801040790b02039045400300c8a040c00395091503028008207100780122500041c08040b20742e66041300341000c800619054510885550000400044e06c205909145000404c0002941e0756002d441030702760102d840d04603004001d43c20a100192069000c0e034055503115946003021150044c00da024000c51603402d030050f02c0843d41c3c0300d013801034442d4040d64940711101900e000314a400201c40c411103255400c0c1d40f0080c0314540028a620030050345200c02281c2d14124240c04680e940c4030742c2100d803201d81d240503 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 201036780 1250 201035530 201035533
    0x50f0f011205011710020414060717030708010f050103020a0e1201060306020d0501092403020d020a050907110606151c060e09010207030e1e0108250302040f0f08030a0c0c0f1205 78
    0x4010840b05d8461003158105d81c0305882501c00b401d500400c2c00b601b0f40080c041524102601d034068440241190000c61181c000c941d1010106d40c1041142240c0c4111074024904051060000030446a0012a620380c40f01c0102c8081c00b1804620340c105000d024030381c1000741254008610070000090b6504003c1c182c40403540300380700045644810b20800051015028141e2002d00400c00c003505000e0003e001d21b900283c00480a503449001103505c4440a480401c0040e10780d001c0c82019201c14440383d50010703000c89054618003400c4080000e5405080400b05c041040d042105810b4940e96000701c0003044c145036101001d03d481842c540c000d420064040c0c000c109004017021452500401420080c01605450400380080e0300044039982801400c3d600010740b9449101e0480e000030412198441c80c07580c0141e070760707802e12203440e040e4011948526200e20041d41d003882940e1010007502d2030300388a4544031001c0c0109051024180080d544111181c0100500211751800c000c400358007202d00070320 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 201038030 1250 201036780 201036793
    0x703080c01110306010c1b09050903030411060f0a030e0313030c080c010311180d0204020d150e010f05010c05070e010b0a032a0f0315080d090906050f0f0112050117 72
    0x40450b2624842203c1d5140042d8140d51841c0c0010103038074030141600b01400b0803090498484a20700101e400c1950556819880403081200b009284100c450001d0740542d101428082022049025405031384070032024103403681d00e00c4940390820803d0740d4110001d8a054031030305960341084500801c46002e5600c2c41e00409910356000e5019000e02d1000f8070002c04001c0c5000380c0c01c0d10480a01908540712070b48810721405a9015981d540003a1802d101c00c10f000052000f022441d580c0c4040c01076010341a51b015050041090304203031750600003220020300f0301016042403883d043d0700f020890b030009100220a04000f01e10b54a0030405030400003201e0700d0811600b43c0400e240064803140c0500940d800c819405001e40c070521440001c01c4005281c2400300320312145912030300302c1b410150084806075200080105203d50301c2869100200851002000410304240100748031400200d00240542c441100a4006901c2040c0c031407000c000c0d40f9000c020558407510b00c065403030f52034040c6400621402c0c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 201039280 1250 201038030 201038051
    0x903010b0639120d0b0a180b03010e030711010908010203010f050a081f0f0b030105090d020114160c082104050f0309220204230316061209050f0703080c01 68
    0x151820300c0b90841680080220410303a1900c405964400700c060001603844100d4034901d80c6400d0024400b401c0c41c0c4580803d0004039411000889460a012038401e80c101742e0001840f000100846005640003610226400410760041c3e03124005544210010b40c0300000021707040b4600d5003000280c400403103076100210303600d0084680e1018141500d000c03a850b20304640b00301d85803a41c050f0f400c005401030045030706240715000900312001240d81d1842900003400e040b030707080d50a01c51106007070a10345c403000e11804e0030207440310302000d811011070610402c2242e400c107224402d01500c005031000440c0c03200c055410900849100030940301161244146c11041c81e40e4100801513a091103c050700b0218440712150050401203680658203540c82e07070812010465102040c0100c00c02c141e0030581003a04c800000074580381c500b5a0b80448500280c0c00d030709111480d40101418a0f000814002160581990805070304007950b604168441d03203e2042d000041200c0600948405180c140003000a0f0592 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 201040530 1250 201039280 201039367
    0x80c1308062d06011e11010c02100b0105040810090302032a0d020321060a08030403080403032a1b0905071701090605010207150507052a01021f020903010b06 69
    0x50700e00b42c1c041460041480d00c10074005c5401c12046100d40342000243c4a0604181e0843d543d080340400180c002900703996451001d4040c40ca14000e0a1030494680f524190b01207444280295110f00b1040c4c440090340b041c50310810696002c189001c0409090ba405000c25104135400300400122a01a010484120328008001e60b10058915014045610b861411404000000130110307a803180d400c02012420805c00c201500c0618820b2424686d0fa40c1542005014000150006030080805c2d115524844003007080341804103920094208804403d1203159428000940103003503000e2030b003410030074460307888941d0f06420300a0070310305101c9989071402c16060343d0343d80c0242800350b800041c0400c01014820203203183c914a41c500f503401c10300e0aa44041c100244070507a1418180f112410400d001c101035094004d078842400102202c1351540000300703d0090350040b1082507039020408050a03202034000032203858006101566403500e01b94001c800401300706030341020340d042121005030201c4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 201041780 1250 201040530 201040621
    0x80f1809070503060f06040314010b030f07080706030b041e0515120606150403050d02030304020f0409020901050120030319050105150d0903030f020a021c050406080c130806 76
    0x2820754031946590344d0301c400c0c4008084a03c6020390031070000c000000c040340c4c503c00f85684400001d000444e40504c0c8204043c602502c0001d49596500418002c2029000001c0c111007150840d0a003ca04082d101001800618070905045040101c6842e01c1100442c80d41c07044d841441c4080ca1025003090b800207201c0c4800c621007841c440782e80100041801ca28005403074041c401c40c1441c046180c00d840c1c0da01d8604003503c000000025901c0401800114545103114511702d000036141003004c01c0c000c0c1c001510210040c414a030512540c1c04c2d6003800051035103010640301c00020100c0340d880c05d01c0890140c0300c0d030310100b8082c01c052a0000200d4507107000903400451880e81c054160505d0f03041100e00009203446601202803540c0c0314950a51140540098008840b45401408425035030039040500c006070340032140c040040401003484a503030401400368110f0309600030181c98129101544c4945942d0780c008420720302c201010031000c40400c00c8107009071415405440c186500c14020024000c2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 201043030 1250 201041780 201041791
    0xf19140906030c03090a0507090c02060604110d0c052101090608060c03190609110702030f0f0a030309060b06040f0816050f010e010201093207060c030507050109080f1809 75
    0x8400c2003c581d46501000245401616400588094100551790b091070083e42380d0054400c00d4a882c10b0050840e010300a00303501400a40d02840f2120082854111601c250001d0001c5103a48607074140f021841070080c1d51480403205010743ca0107905410071b04840109104507204181404400300e0700080c0842c001d40951032140c2000c1c1141ca03020090542500c50454484503140e5885001070b0196546c002d9010441c280072a541d540c819500502d0300702000011003122a6019408080c1110400121943c01c10740618000400c20760b1443e050b0042c03c4d0700080c032548494085000320325514003500c040c08540307070341d0200c940050104050f14510412441210380c080040703c8039800701c0d40030300d54080201c0414400001d640255030303100da980750b4200b1918001202d0200810010100704450204170401810003440080e1030144020705007034200e0002410000045468001c00100350489440b00d42d20024098654000b1784299109820691a150840e0440c100042c01d500b44090014080d1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 201044280 1250 201043030 201043039
    0x32315060301081513020102060c07060b0901181401060806190305011a01021605030d030513050d08090c0d020907050c15011805060414010306150b0c060703060806090d140f191409 79
    0x5a80c0c1c0302b03050005401c44a0240c0d034258075000e106072290364034140a40a0503032603028100c40c1950f9055007003100c10640c40f01d06282c42080c014011150400489075000c82c0c1114a285c074907284c070744121141c500c90751004209608015440b1010300d034860039100300700000c0e421114001c10b0303011100d00140452041c2d54154205428201d50248650000f590210b0030010106100c0026517a580c6006550016400040c00c0e4a060100400c8240820304800b00100c9510500300256000070b201d0540291a410500100080e445c4962905100180ca900f81c000c00b212590740c1d4411055060036070545038144a145090001000b80c41c0a2180a100001501d1685103d03130130f42e1385060041c9100445a110300c2003100c1c0000e44044441c00902003800f20350b01400241c2011342001d4240d64080d0801d040c1c0d82c10407010048201d5001a010450300082c6ca0900300c1959805415202440b40440200080d200065602818004166800c40c03502080d900c001e1a0942c0c044444164044e01c00d1081c0e00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 201045530 1250 201044280 201044293
    0x9150a0227031c081303030b100c02010905030d050904090c0e0906013002010c0501021c0b090121060b011704211404030f0804050405041505010501032315060301081513020102 77
    0x17020324008140c50b0b111310070704000030300d24076000000f0340c1c1022042400d4006010f0800c0d103411942d21490810080000f900100300b404072150000e440c0340a240003050003203598001140c148140074020300d00a21040e8400d100030709024841d21b46900003400350303c45600030300a200c6840d00311640500321080801149603803d40c6103500440c0c010703100c5103060300c8541d0248180c10312134140d8403141400629070200003a00f00c140d071003441046481640401c4541e0741c1c080001425203044845141c0c80f5520000c0007902031304c510300580d03803c59100e0442e00803000c0c0340100000c110a048002840c041c00082d1a0300036160354400b15a2070340011220b0116680c103210030800100310500042e141c922550902d41455110808079080f10030460f4191003104450004007080b00141c810a8003404c8203203001c0c004010034000c51509503130000285104007807064002459025400054504a0401042c3c140d0702c1d65688503040c0c0c0c42d40054201060703c6413040100d40d42c0000400a00b64031075040e0080c142 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 201046780 1250 201045530 201045541
    0x1a030112030f020111030702010605120105060303070f080403050d0c061a010207090c0e030f16140108130303020d140615040f15020f03130f05060309150a0227031c08 73
    0x94202c0c082d0200c030255900d030341000d81c00400840143d80f04020340ea0000555614207000c001d00c0d03041e040c0c02c0c2481070740b43c5014410140c502004507603c0f01d0b08480c44100c04401480c0c40d4900c2d01c0345500c080c0840c004c0589009609500402d1440c00f00d00400c014004118913181d62000500c1c4106101d01503030081c801040f084210303410180d10003806043c4081c44034010004682410b080701c04e442900e400c401518981092058030b100050b16020710310642d89040c28002a1a203807002c1d22a22864290b41444000c0601c01d804440e030600180205019a880b001500500002c0c10740d11144104a0305a481c0e03928030301c81c030541d003c0302c2d5209003148515203011071070400e5403010760745801180526240030fa0034940820041007442c95400e58400c040f07241c0750340c0b0241079030035070085841040100180800b19500040c0540000300250502540e074549050300c0000b40324035110f04425807903100326101d161800407401078100c90150165200c0c3c2d462540c042200c001006120404540100081032 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 201048030 1250 201046780 201046787
    0xe030711180402101b0506160f0801030201050702040b030a11090105010e0f09070908060702030418020307050904270506060405090a0f0308071403160f0e01020a06110f030c041a03011203 82
    0x900c01c1d00c0604091003101032001071100e105685c004166907580c043c1c02800504855119503400001107132a00100416807428010224441888043d04010020941c402503598030317441122044801012150304101e245420300d844043d002c42c1034840c6814500005441d40144a81e041c891001041c1c050030507034450410201500280081c01000280c8501041c0c11208100c141c6c001e40c4150019501e0b5440c2011141d0030a0985185842a50050041c45000c54001c000daa011450803640400e100e01c0d146c0c0c801c3c1000008500b020403518140410400344200855200d0042000b0342d414449513070750205c1c0b0f0360b40382d0600300c00806058007907040c000401d110f110711680203001ea180941c0000c68690224440e0342068580c503124091080c0d02c001d4054004480c0028500e01d0704081030b0080c203410000c0d441c0c5400e0310000c3c00031512800300070100d00d03100080b20600441021065240d0408201094241e0024010303c04132036801076511228501d04003e60741240e07143e920306d038001e800640c0c085 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 201049280 1250 201048030 201048049
    0xa06090303110c0d03080f09010618090620070209060a0b0306150d0504141e1b0a090f050105030607230c0a05010c030c171b090607060e030711180402 66
    0x4010ba00464242040300d07580e08251208680c000d070348100d42401c041c0040c19421a0103017140421381c3c50802d007007080811012800d8102d035104800083c42d45400c1c24640003034003100c4a00c440002c003000342c403419071281701d02412529000b130b29059400e980e50411b1000000700c0e8012070030314540034000180c44d03240035216040905001c107940d50400f50201c61800544600780d030200d41500001000285e54441006161501141c0c2419460000c40070101161160304c0100c290b280111541c040308160344400428100a0107900020400c0141d0a40c9600c0240001e01407030344680a4400454a8540701d41c28041400d903040122044100780c7c8550f1203000d900c5104040514040c1041c404c003c1a420300c59800e203046542c5021800406030381c4002c000315406c05e00400080784100a1141038590301000c0140fa0951100ca00c1e652201400010b0300b0307000c0c0a900800941c02c1c140300c003668400110151120610400c4c000c41c1051142c0208028625240d24811500c201c00002401518100074103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 201050530 1250 201049280 201049307
    0x16050d0804030501050f0103061406010c060e120c030a020c060f0f0a09030b13020f010f0c1b0b040306140114030303040b0c0d0906091209080a0311011e05150a06090303 74
    0x2800d14082e0380b40d030f4450a6071400c84000044240c144010001e0140900071a241c1e500041c2413200b940c81d00b0000a803280300075190240003103640d003020a1016808000d00d00c078400203030f00035a0b01e40000e0b4030555601c0e40305d040140c005001b40703146240306003041000d442140303044108450030800c080c2840d06032500040025810011440b200002080d03100c80481c0c010250100c00c1110320f001801403042896148070a1810807468001203140700b0b902c00c1d5186045503010301d90754003a103450008042d40e150a07030005854204005030000402c046c507071180041c0c0612030b641d035034240ea03944004407243d00c0002d12960160800c100040018414980c4917074841007001d201402c0c080c224040d88105d4842d503c0444405030b98260b9841409401c00c0a41406030880c0307005026282004c2c0e5890305ca060000005003030203408450400c4150081d00441041b07007908803000032000002c00f07588090300c000da501c1c0340c02204806d804606414040055001c0d40c4e065202c0014491071580d003283c1c07580c0641b44 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 201051780 1250 201050530 201050543
    0xc081c080709051c0b0705091e122508070308180415061206050a03050a2414041101020609210f0406020313170d1101020c07080d0f0216050d 62
    0x101040c2c2d40d82da5000d00c06220310000713200262100301c0c03904541c4148007521030003d026007441090001e5503001308540502e0340c00320b0202e004c041c0d5403000c02c0c4001c08000400072103001d180c02d20509040c0d489501c0f0300c05c810038010b501c0c141d80c0e9484042d48581940c00060410751007040701c0d190b07184103240a1640d0f00c6015100003102284d20090f0306031121550050000a29801000c03580c50100d80940805440215213081c804d6107117a41d0320342c0d02d07902c515000b0100204101501c4031807101000070000a8098002800040480030b03000000413011078049400d80f9040c0341417809544006011445100d48600520f000e10020044900f100e0f01051743c0707003500d94100200d2101205c02c902600040005400451701e8a0304080160709180f46c503000720000195000205250b540c00241c1159200840e05101c905c500000220134068420780509071198405c49100080005000481509951345c5a6840d41c0000f031a01040b80c9541e0141c1d451140088410028890b928022000340c181621580 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 201053030 1250 201051780 201051797
    0x30e0a0b091e0a06020930010b010806130c05130f090501080d0c03140702030a050705090c071109060f120615010306030b06090a0212010e100f08030d0b0a0b04030506040c081c0807 79
    0x607003482c40407841000c3c60146140c04c0c0c00401d407c5409004400754020b09080a5101b498620085100a44e80a14032106181c4a240c000ca20502600407101585580303010410f1880d2541c11641c282c42d190300c1100504e40c6480300000e08102c011800c803900114603540d480d4003118680b4220340701a8150340d034034801d50040050000594040101507135443c401e030040c0c070140780703001c040000c2620002d0268440d801c0070010440042c0034071304002c0310a1800c4542904c1511140c01064001000e18a01d0f0b4000d4016010702c5048000010058481c4291010700c155000c590401101a5070359880000c11210f090303c08500b00c0e00d016008103034065010040103003003000514040103810001c1e0b011382c014000c00c109001d10291210118000b43c0b1180e038401501e10302d07107807459950b4414200380c20801903950303d980d18541c2d507440c16140209003901c91035403110b881e03081868070f6010a0301c044500c40c1640b01c00252010004ca5943d1941030b128a00307142d0000100002e40e8036203070007403407841040300c8031 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 201054280 1250 201053030 201053059
    0x5120403051b15160504150306151d04060b090904150912020d031a0103020306120303090717061003290f06131e020703030e0a0b091e0a060209 63
    0xc8412155403442c4500819031030f0780e00b82c00c1c0000540040c014640c5500a4107110b80c003260050111800c80740c200e6658200704004180445c001c01c1550040c10707012a000c0b501c07840140e07001c100a581001150300c005c00c0440c40c10f08000884480b8130070909010014410710f80c503882e051541e41da22501524010740400d0714203510b00104e4200460440e1940c0d85046407001441d81000b01a00e441054102000014556001c0b40020703200d840ca4241050f8000002a9042c6c4030100c6843c0c40711000c2d41281c0d201e05280d074003a92035141600440e22010b01004425070710500000d2194020340726080d6003281d140c1591500c0711140c041c1d10b08a1030303508858460301a101c201c1c111072442003c0704918030b41c5e20306000782004500c4050120b41c00c403c500700130b0355aa071300e1445200424440800708005950b0040c80c5810f901034094000005014080d2003168014000d0401c13035036120320706560559001403028807558201c2d04d0301710728200040d400003482400082c016801031164110086c00083c00e56043e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 201055530 1250 201054280 201054307
    0x7110c130204090504080325020606041109030d050d180b01050d0309080318091e0106082a070203120f04180212070c03020d2d030212010609080d03060302010512040305 74
    0x142e50444080c1400020854250fa03a04d4541205882e01d942516448040c1a000ad5030f07420003814441c0b28036514a09104d820060000300c0748140e901406aa02c1c03507540920242ca150401c0f019084554185079054000c04200805403101c11384c011500c0f9621307400c0c48103112318a06807010817000d000c10400081107001041000d0100802082c100c44402e8070040c00703002d1512805040c035524a680c0150b80300c1409a02c20a044c155000e91070990041d0740c5541c001030f80404400e10702122603004422100900840700010310105009904998007503200b000d4800360b80c814858841c0200005202c2401101d4602c00c401c0c850b14070042d009410402e0905440b901c2440540309a00440d1030500e4a1f02055014402403078245000d007406244294200c2c070402800000d081c40302110054200c00c89051402541a294140b040f2103602c1902c4d038503220003420009807401609414885e1034003a103a1180b1074002e0400f52903041c3c3d989828043c544036900903d00010b0021014401c05010382a241c109 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 201056780 1250 201055530 201055541
    0xb030102070f08070c06030e0a0308042102010b030c030609100e030702091501030f0b0f150d181704180b010903060f0605040b090606072607030c0b07110c13020409 72
    0x18008184d03680302e945884509007009034003203000d05007414a094002200420110701103501814a22003607507a40ca08060f0b05822440e6003885048009a40780b0180c0d41544100c4207004150111907411000328205541c64108803520b90790b41e0311220000746902c800c2d8000e1456445100c0450303041c05180c0c3c1c0000e89013101201c20311a55001901c030f004071581d01d0b00480080e221049810802ca0083c00301082d00c421443c500c560003030180c038034212050704483c401c403500d400c404501007010b81c880100e0b2286010050f42c0984001d0743c0e0b01c101ea070b1145002000c9030202c4460040c039803511450005008042d1040610031811310144000010108605006203000c002224400264030340c14041040308403500c585486001e903000c541040319503182e181c100d41da020b82140c861401c1007100e50041d090700303002c000040d05000003c0b44003c2015000311144001922500e130500031a41d48000440e50a4441c54400210340e002200041040c100003181443e503e4840c1d0000d45059222100402500c4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 201058030 1250 201056780 201056783
    0x9030109120e0a050108060d031209050c10020102040503060402010c0204090501050108010e0114010308070221010c03140703090b010b0c070512070510051201030b25030c0305090a02060d0b030102070f 88
    0x4880c40603822182d01850b040510607085407101801418500028524200200a07600400b100b50140c424540229900d8900750f0382000188840b00091906a1b11005410710441c000d9076034200c0b501a50340180261030544001400405090b95160011200d041d034101044ea04241e60b0140b40e00861000c1c0109400f902d040d500100d0503843c0402001d0850745115006410000c1c0c030001403002900040840e604590100c6040c140d400f10280c00c4c1941007940c2c0c5103c403680d07103014440036960360903030403403001c68280e02e0260784a6036072070109074240c402103c001000401d0400c01808002080d1000d0f1420500c90001c5845144e241d0010600442030000b5031441680f0112080040d441e280c0b00c40e5000071154031341030381414010401c59090450601000f0219010307080001c9031010181d40c40c000301022011114060180210050014124003520000003030818000601d110400141c1d408502e03409864540f800d60744081a0006040d0705055a40c555020821000411044146840c146 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 201059280 1250 201058030 201058043
    0x90602070506190c0e060c0f030706050f0a051312020c0a0807030209150904150b0402040311040e0f032508040b03370203071202030a0f1112130809030109 68
    0x40c1000340d03a05044a496042c9441c3c00740c24028400281503000301c04044104003943c4440e100e114000d055400d001e07203940503908902c40880d8030300c00c2c00600d805c094040c09414165a00f02e840b0480450141d8078100c446c40140070285041d10300240015041080e442c18a00c140c1e005402c40307400103203200000f50310120555200d008148198645500c500303400107103c07013603110398041d504041040240c2c0144007800c100308800c4a541ca103882908440181c080c010421995184c5a02d060883c6000c244071442c0540e1500304101d140c458001010b09d1010b03041c02c011800c1c030048941c0e000701444105074108801140c05c0384400001c03041000303400a4110002141d0b01d034a0120030742e000c507a08020410140c41c10817402e40024080da445010b100000200d000744e52076035601003d803403912002105006040c4004108402030502c0e40c404501c8400316482406070300080d0b10518000d0243c82111442c0d1070380d200115130440c0080c2c03002609280308909850520860780c0010742161074038a0203031800b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 201060530 1250 201059280 201059293
    0x50313020f100905040b0603280e010f0c030b0301051005040e01061508070f0804032f0a150e0105060906040905070305030c011a09090601030305090a03050a1401111204080d0906020705 81
    0xc601e0903001e01b6140f80801d4442e9421441d0507000c04a0342d6610300280001180802c00000f0070308a0707a00011b84401c4a000244000e04007205414010000014940000380c50308402030090726060041d40e0050406401142c1098100b00803c4018110103c0c0700c0e41640d23a90303500003130309410340484803460400c1d91140d050900e001403000d0090b0706804a42420840c00343c1c1003200003031700300d5010110240c040b01c035403018a44002c0c510307003000b850065004d050704c43d03851030b141000303200d0f20300c42c2620507607800034051901503a202609032501039403c2d9900061082c0001c0442c00d0503400090030300d02500c115070030b032507032911003a0a40c0d005201281c456512559151503400e11081114603d02e000d0f91110300610306621440e886c0c4106000041c1080000103200f0314030369405014002030350304034055a9810106191444210031140b050210b25401c01e240701c446400003070142c404400042901041d0341e0b480d5510705000d54003020704c11480c20768034803440b40480c0c0f040c4040d240383c61103003004028 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 201061780 1250 201060530 201060539
    0xc05182202090411150301030803010e0a020405030f0a1407060813030c0c120c05060f0714071502030d0506010c05030d0e07210c080c0310090c03060e1506010f050313020f1009 77
    0x5000d82c8800710309420b5501b080100300003021141160704503018010b082820b511740e401042c010b0f11996110540c94401c1000d03890b20440c01140403200340380b04140d902c1103082c2c1440002d444403400d10421011508050004541a0a01324214401442071030700c3c45445095030f031040e2407042143c10014110651000d61030800c114030610501521085031024188860504100c0741d0f44140d150003000c01003600c8848000d0181045800040c1039030001002c218055440c00a40d243c1042801445007818400440c0d01940501124030440d500300d001b442c82e103040c480810b0b001d40f5910000348024420080d000840da0b03014802044100d800c4412954107420034101208041d01e541c10045840d0003461400c4480d40d800107a440125031203820100d0030449508000f41900e1450340042d00c55810a420500c0d4404081240d03440e90416500e040101d032078000044031342517240b1800c0c5002c210b041002c20070200500c4080038510b0f01c000d080b0420048490045008905858400d4010070b40d422001e00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 201063030 1250 201061780 201061789
    0x152107240302031b070c03021509130903052d1801020609010c120b011e030605030d0806010206010603020d0b0301110d0f1505010806120d08040c05182202090411 71
    0x4040181e2a080d421814903284200300780b440c00c12020311a490000b0f0510421985850600041d2340040c41244a414142002d0003140c4c02150a544240154910080c2e00c2c0380d184500c01100c1d41655030704d81400e8100d2110062450340c03085580c10004074016a405103c1c1100c014122076407080c007100b002012540000e868044013400b0030082d80d0500c0d40e15020b40c3d5020405240c511403448001c141d0001607401a204204d05281c0e100d070070f00889048100c000c0d0190445021201c05400702d54243c080e1903804c44000201780c1c4d11a00681000e030041010501c0707a00030b44003003d0401c2000595940031000a82140d080584051480002141e2a4a161041d109800800034289403d200404894030740341d10400150150030f0502c0b0700040481c42545803020180d0101d40c05400f1100c2d00f9a04402c09814408125000c1341d01e045036000106050a00480d100140610f0810070302e240c1d00c0d6480d01d1044007404a09a902c40c556814041c2c0142ea00c1e0003455000d68025045100c20212440070300 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 201064280 1250 201063030 201063089
    0x21010b0f0a0903060e0c1017070f0306120605090607020307030c150e10050a0c0908120706060518040501061203081611010212061c03080408070f061b0e0306152107 72
    0x204280480048e0384402d0501c0385112a50240f01443c14522000c54041c061340140714030b400036450300d552840c2c0f41041000513030100b40201c0c0c64a08503039890b0b40d16a0200e86c0c2e0310580303800038001038841002070001020720030701c060600700f008000720b40c502d01d080445142252002d03003c42c959403a2818088016594410707016111030501d04034400500704029130b59503c8000b8950010600001910b00a100c80c99104501504000702081541e07022408240d42154094405030f450354038180f0000f4988004a01c0c1291150b415101c815076070352000c090080d100b1440301e42405000c1c00d01481e040085083c801055442d01c80e01c1c440d00795040a40c280a50b014000303044514002031603000d10042508501225405070780503907501e96600c481d00d0400280340c8980402861a07040c100d0010802c038580448181d031201d544e82d14940b11099004240d0360320010744030540c00b15588240b00c0b2040c10055800f10b4031088444645410713252103803101d483c14006612440c4004010808070b8a00751030490b52 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 201065530 1250 201064280 201064309
    0x20d0203061507080708161707060518191109040c0f0605090112050702010902060a0f08011706190b19231c02010201111204030801090501030c211721010b0f0a0903060e0c 75
    0x250007000f148a0241942c0c0c980e120055491361680211920400c004c81c3b0300349212000c0500211854140381c5824500c0380304074010705148070100380340844c803148200c0c1500e00e1610169614490b500b445110a00240f40c041c080e103045540360040311000d170320f0310030040c052084240e413400c003440c0ba040790003491079806030801c0a14a40320481aa00b00c840001c02541189807000484101c030441540c2c80010094804100d400030700d4450340350f210464a4103801d048552802032000c900100710452a102140b1b810000e90180c0040003802d62050070104ca41c143d5032044c000000c203074140f01004549604140c00440700c038145201000708069000340040d0040c1280503083c400365045a803443c0345070090f8095040164000c054507a81842100284144a90806406141041070801c04c90543e40105180c40b000c4200315070508155803134400450494071911401c505016031a981e400c104d503c204e040d072080107840302000c008a41544522800c5125540c01850aa603102007880710b030000c071144 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 201066780 1250 201065530 201065551
    0x80705030c01090803091614270901061d060117060402040509010b0703030c020d020c092701060e13030203030a0902060c1902030c0a0e1315020d02030615070807081617070605 77
    0x4100510501c80585a0b010a8101c50302e00d4240300c070389031020f607a120048011056012704011706c6101c02c0706610590a4420800806120708001d56002a104d007040e05d801e400103440c02a1056a0147d500025810040044c0003502d4643da690004604070000c3e0880803070201c1c00980c040070541c00d40702e03111443d80940040c00050111580c082d4513082c0c020646401483d5440c00942c40c03801200e03000c8440d020038045038007091042d044a0b0700a04040c003480d541c000c0d900c80401e2520003030b11005140b051b4141e000303601e0355403107442050280c036004204070780084050081d00000c17042802260401072070007030108412000350041614000d45401c201c0d010310000c4a003070094440c11f0015940c0800c51300300341140040d00e850304488000701d007a62085000e1003c2806001c810312034008500030401110340c01034451242281d002a0310030598001c0c1012400c020728400590724030040c01003480816841d00180c51241c90300491001000d034000e220190000e10b1500700302c0c1d40d100e226044450104c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 201068030 1250 201066780 201066823
    0x706080f01030f0203010609050c1e0f0a050d0b06070f03022401120215160c081605090c09030102070308060103150f0909110a0b13080d0507080705030c0109080309 72
    0x4080500ca01070201034001003203104581c056440c00d40180c4000c0400a0701000303d480e11143e0075241c0d81110070041241c00e445898040045006802c0c0c4103c001d1752014a0b1801ca41c0900660710756108070410003540c0e40b2082215903680c0da420150001502a003100d01c400700d902e2400a0912020b8915000b88040401018074031000241c2c0080c103484103281d80b160a11802d000240104552a0304d03c5441500020155404010890780003030442c824502a912107895a845940b00c3e0005000400c503142125004c1115103401e00324150420b010481c92484d051000c1c0203e8203a030320840050300885c0b00718050250551b414030821000e6880d403560128264103040310380d0007045a6202c0e038ad01d420303140c041c0d0b9818440c140240c4003100200070680c0711002c0d6210900c0c9615000284003412000d400300c00020840c00102c3c1e001c0c43d0011946c0c82601d008040d59504980f50010b2805494030310050061b003071800340910903503d07080e004900032078403440d241590318a4260301c0c5041da204007100740d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 201069280 1250 201068030 201068041
    0x90318090406090b091c0302030f0f0717010f0611010b0906100e04090f0209060303031b0307050c2a0a03150b04110a0305071b0503030415060b0a02010e070608 70
    0x4408800050031545218262210306140700a083c8040d006019401c0343c02c00d1000d034840004000101e40e5078000c411101c480000700940480c00200c5c1c1e0340c1c0c0c00100c40c0000030341c0c3d0061481d04940c001401e06040404a040c0d00e8000310384c075000d801111a0038004801442440d8114041d001130080e0362009005800341c85010804e0b0b054003810b010300500c0c580c85155581806130351226286440944208103000240c1040380164201034020b070302441c00e001c00310702141408802c99205a1940303441540d018052a501d400b81e0748010403010410509001c014041c1c0c405002c41240e050703d005a480502d01401819a5601030340c07032085d032160035041340400c00181c090001000c019207150b40020760043d0b100102e000340c800c02e08104070140340020000b00c1c1d2605540071502412190380c40000415800c000c40c03055201070800900340354400c1c40040d00244518034000c42c0b050b0b201c0c8010640507540c406940f200c0e00400038120150f5101c9924603204201007201c00010001468042681d003003c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 201070530 1250 201069280 201069307
    0x7020312030613050a0e0f01050105090a02070c0605030c09090a0506100201020a0f050309071502030a0e030a020a051003150b0a1706061605010603080f0c0c0109140d1403040e0f0903 80
    0x10b104408481d131102c00080010929500088002c01d0032001d50303410800d5860351034020b0409004852283c002c0388042085000288241c0c2c401d151b100c2c480c06000c50030000c0545150b0401803114081c070704100955000354540d110f20714020180e040000c0f5260900000b040300c84407101d0501811a80b040c000140255440024005c102d10b0b0b5081a65480d26201c2e001c0d82000380c15007180a44298910903481d09a40c00002048640ca50360344501c4485040c9080545480a280d00030303507c4400300c402800607141480310300500d865a400d0009022081c2054403050780701640c8495281440401d2444405400003e0ba24075500340300e800100520b0720f00000342c10f03405126401000301208202000800c1025404103015681010b1016218511071205c10180c1d03101485402c20790042c07031181150380d401440d904054074411912211042155828800d01c107070300c8001130f5104200e40341c5010b41500b0510061016210a41c440350542c03804038802e4004c15409810110705500402800004014 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 201071780 1250 201070530 201070549
    0xd0806030c0d0c03050a1101090b0702090a0f140c0a02012313030c050708060a0c2309040b04050408030916080a030f120e100b030a020901151e0203070203120306 71
    0xc0882c1d244100503076900f42000480d110790001012803140c0d6040000384a0b0210700650002c600341d0b90740313803080d803203001c02c5c0c5480c01100b400a40001d02c2034041481084d894002e82e000700d04441c40002c1c02000400c0e4100c0490080c0c1e00150b03420380000c2c01c0881c0960a005915a0001c80728030041ca10844540a070f6071413030010080000300c0b510503010010103204101d001c48083e0080e04540d0110f8584082d0354944500f47c80b0b20018520706046928034901600400d40300904403030145000c0701c1c0d190f200c0300b100c1c0d000f04c0320b00b0b500c1651011070101c15522441190301960041300b126407a490004201441c003d200c481c08481c001d0740c05020018900d000442ca01c400e41d044c070742407000204110341541e9403264441c0c26058142003008980001d1400500a0400042034030140b00c0d40b1a03507000d058450141c0040a0340060070b01d801070008400400600311a4696440d0a804d4152450550054141c0c0c0020f5040160000510803007903103000c205c108540c1c030114048034654148200050800745 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 201073030 1250 201071780 201071803
    0xd03090e13240e0607030507090e09060f060102011104031a060301020f041a09040e0a02041409070915030b101406090609012304121704051c08070c0e0106020d080603 73
    0x14241c01d030ba8003107103507002000054002011144e280c1014040a03004d03260458102d40000c44181001942c9010002c019000d0103d5101030906615603440780c2075011002043c1505640d20340b00b91038001164117004000440c010808075414185020b20040d032280003806040c400d07030047c8503044615a00c1021682200c40154800750b40351a5960000004d02803030004c10b51285ca40742c4520040c200c040b0308400741d18400c4500300400241e480207501640c10039200418594000070040c0700ba10b019600604014051606a0b801e417a035966650302401380441d0307004881c0c00082c404002011081503c1c40040700c0403504a41030072400d00104400c0e0191f03211203410042c2c00c41d402d403110041c481c039000d404145401e6041cad582d1f480300941054116070403011181841c0a1503001504040041035800390389004001c18030744000c01c04c0d546400b100610342640d0075101003180038000f80744851520010001540603040940c50004041d00303101c0104903520a01c5003081c100901c0d1340d808038a4075141d1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 201074280 1250 201073030 201073073
    0x80106081c051b0303100801050907030c0501050c16080102090a060219020103020f0706050702030903100b03030313150204090f061202130507020a1406040c1203050406030216020d03090e13 83
    0x3810420101c1c1d5209940403156062401300200b0f004c01319000700482c0c01075a100c13000a00c040e8684450841e40c808180c8400361030394902c032005100380e61060b0000c0c640400c0500031034012682c62115060203d2550340141c099070750014040015040c03070100c502c002d105c0b600180c1078a01d466020452180740d0b01a000b03042690010f444482554100181c81c551034001740100039501d0302c81c0001e5030341d611007643c5071321900c15280400070300c6100780554115501d011340a10f046850b56030719000506000d00d003c82d207100c0851084d0000003c2c502c003800c01400403450110701000340020181c100c03085500441c41440c01040702601684501c1c61000c010807021400241d00e596034107089040c8412450010b104509a002020004000043c1a07001c0c03402807180009036540d42c1c02c202400940c020004010480c00e010412205020703902401400700d00c2450308c541c00103070758005181e4000001080703011031a08078003032115644040f600c3e64009500e190b0158072260a0329840d862000e60380300c40509 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 201075530 1250 201074280 201074287
    0x601060e010c0501022101050402090307050d0311121207030b0906010c02031c030b03070f080a0f0c0b070f200303040308090a0509010e01090e0a0c0509060f090a06080106081c05 78
    0x103074810300001c58050f4008000b1903c3d4024010403029011a030b29404444610780000840c451903d0300c201c86a52800070014134810b03142c413050210204000034141c0900065509028030903500b8000c803403080c04603941003175443c029007400350100c3c1000303040542050b00d0a00c40c4251510f036009050b81028003420b202025a007117200280c90103191071715a00651086800b8058000d130550055404201e04a044d20b04498030769402c2c0300883e049110780c88c01c0d68810741e44000414142812108010b000f1441d9140136521101c811010358001c1c4000c8031240c00f071032203401c01e10404191041140d44204042d45c9180c9107480000d40c2c034080c1d404050001840043e01d00d000e40e9410041c42c00500f8080d11a2405603540c3d40c894402140906c64003420314100f01d604a085c0102180f11a900c42d0f03c480c0450482d03007800c00f8001600f400405070b5802a0b580041428280c1d11004074612408020801049080c1804481800c1d60515800940140d2042c144040b0218103035903009810040b03803030120345 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 201076780 1250 201075530 201075557
    0x21161d03012004290301050613030b0411030d020705061b01060e0a09020102160605070b06010509030111030106030b0303030f0c0c1204030f03030605090f040602030601030f050f100e09060106 84
    0x511101c02c01c01003948503008212101c21680000e032046510160400858051000200805110515810300100c0f01000180164940304000d0101c2401940103c0da9150b100d94804020f5030b02564151402c0c6600c1c00d0202c00343c0340801c5440d44045091020f031aa8900d010042604c81c0682210298079011205003c2500d040941c05a00285074141c1091038030305242882400610340a40241c0c01401243e003549102d11000d40c801c800c4800755039443e841c014080d00c42c4115110044c00440c100030040098000ba0340e02405849003010129076a070340c0e42d500d4001d01804035400240c03060b0081d041401003101c501307050007603140e000c900300b0700840c2d40c0d03094040900e06001c0031003c26801007801181c08420712000c01d0f00204041d111703407020003009441d00e042000c00181164440c2442d8039800000d800504560091a0001018103010415205440c070321820344404484625640b4500410807100c04811008540100001e0706d10f5200c174181100102d880b0342c814052841845400790360b021 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 201078030 1250 201076780 201076783
    0x5070b0a02030c060c1b1507030c050c24130b0a091b180c050324031e060411040b01020d1404051e040b0406140103050a1121161d03 58
    0x240a200c0c3c02c0140d804503e000c92038602181c000045c00c100d20103100d40d071882d6001002601c2d240201e40524031480030380c0c07609011006007012505103410003109110404420400700030130010704d03035041c0b00c04107690b042a0040c107214000620540b00000c1441e140ca002c03500907034049401c801070344400700f900200750034000e00240c0c844101c0000707140340c0c0900242e4003005400c07807884d5110148040c80f4103400d10000729010b000c255001c548503102c8039001d500361419500c84862084000c0c0548010034060004108602014000060b4070740100301040108501141c0f04035200000700c40400c00f000d140c200003076441624140840034002d2407012400030403a01001d81c0c0003414010b01c2c0703000f803c8916a80140420340c00b0001d9000c1d82c1810045256450720b0301548050f604d08582841c4001046001107001d00f202502010b0402d1340c4040800d0001442002800350102501c00001c4102d440ca070b5018000078000d05585256607072810701110140e210f00318a002c5148030311911605a098400217 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 201079136 1106 201078030 201078037
    0x41e06030605150d060b0412150204210f0501020d0204050103140408190e0d050f100e0a1101110f07060f05130509091204031a06030a05070b0a0203 65
    0xf245424080405440307000c00518010841559a804901c5a9442078100c0460441c1c00304200045c402000c82d440c3c4034018240701140781600d04081c000c1d44152000003d003207014034a0b12482845000b110071680e864121000715030312203a286c843c0c8002c0d4054800c0c0c1e40880e0800d5281d81c03030301c11500135003849282c01a03034075407900c2c01a901070721148407103610307a0080c0082452008800d44466001007a03880c82000246148140c052510749448440030001010300d003000c481d1016514045450b461044d4030251000c0004603940c0140c9034448521400306c050311a00140507460100012044122107894540d903440641c1264101c0c3d007441140100c0c2c0400c03141d030300c00b0440c50501c0120b603a4403c42110968072140c00000100b04c0702d1380281d00c144c0d446e41c464841c100408030b00000d41f94025104600504400d00141d8513181c80d0551403150355900f000c0803130032130700c203500034000c5 = true := by decide +kernel

theorem cover : BRFrame.Cov 200899280 201079136 := by
  have h0 := BRFrame.cov_init 200899280
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200899280 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 200899280 ≤ n) (h2 : n < 201079136) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
