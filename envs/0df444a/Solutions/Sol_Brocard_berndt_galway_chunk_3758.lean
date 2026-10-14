-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3758
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:35:30.888603+00:00
-- url     : https://prove2.me/submissions/02cc7f7f-e9a4-41a2-856f-89c4db808d3a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 675719424 ≤ n < 675899280 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 675720674 1250 675719424 675719453
    0x40e091f020c03091806040507021204140a05030604031d0d0f15020405060403062003060f150f0c03090a0e27120a08070e0a0f0603330e1b07 62
    0x8a220a0180c0c41c40c50316070170500d0002c1c100768107004d402440e0903420401901c000600340d008640150206188815800040d1010b440000f0222180340044a000c242081c0f283d6002c150300d8460f803800e02050540000e5004000542e54003a0f14281e21940701784244c00c2c0941d48010068a6192440d0001c1896480b0f84084940c0004000d0700e842d607144000f90b040d4019800540b90b05550f280400302d03c614030041d10400c840294056415440d0000c0011842c9e810462468058608046124003c0020b40c0c12201014408a0044c0d111810300365455a242c005580c1a405080342c140c01041d603012800010f07100f424400581400851f125449052019031a003460b22280701d02c6445100c424032040107001010116541d010303241c80d021030000c1000543c3c0d072301280140350010041c4920444014407606441c1e03a82004520700300501c2022001d4076411500c200d103110f40c0c070510507840050600f6181207540351365081e8002d807141808001aa60401112034964004110b03500009002d818000403 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 675721924 1250 675720674 675720697
    0x618060c030c0715030902060405060c0c033004080606100c0606180b040e06071404080d020303040506100f120203030d050c0d1406090c09150f040e091f02 68
    0x80624003444a45150088818502c1c10380262005100c00800ea4941d0030391611580f07400e00058246402040c2180300d607001301401120300181650f00b00c50100320b03c48003024064210350850301c87c4039080b0030f00b04c90880701084407000680b011800c1000030054074181c0704048081d22840d101d4108000505880804050500c1040070350701d00810751511555000f442da0341c0071480500720796050002219822462148100d16002071410194400230f0500d034000410700b01406941c40603140e007000740c009c42e44000d090f407084e048408034460b404800345010314400d000b1998142c4452034501c01d02c903818018900380b0703030841008008001000d10307000c03600c1e80082c0503039150071460442e03501950704c200d4003d280003070300081c400116000d030700c108991248010903c26250a1030400591820070182c101190a4004140c0520541e078007480540505030558001d0703076583e0301003807042c1d00750402c1c071400f40941400d13400104140e0707001c605a0904c000d020310140e04081031448210080d00090403498 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 675723174 1250 675721924 675721927
    0x3030a05040c1802090f01030e0c010e0d080c07050415030f080a12020310050f03150c07021804050f0601060e090402101101020406030e0721120e1507020307060e061806 74
    0x2951248508244a4034643c000303003da92075038003c09003d04d4000c3c000007607040618151454480044c00324000940032001d19102d101119810001503038500100009081c451000940e9040c80300300182c00c00440310103a0701444ac40044202c40c0c0d03001c402c40c2c8000307014500d80c18001c90000d00b2690080629220b44e040c8401558450000300381203803c00c07280c150210840701c03000d015a190101500008403001c034024841d0b0341041ca02c0340000c6d00058900c40d03050700081402d00865640c0b001140f8558035264864200d4a01030400d03903034907240c10030860010b00a010010035185c1c070982c924088008043e000c0600c2c3e40300c036400c2c800a07800c100400c0040020303080e10390b1040d02080c0001d000408450703030b000c129000d50200980c01e14200d5070012130343c108080e0361481c0000d00307070200400d01500040002035440008006560750850054055401160b5107603002c03030103205002409455000b074080343c40340e40d00c440059031400741803104294444010310034040072003100003980d030303071030601038900c6 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 675724424 1250 675723174 675723179
    0x10031505071206060c0507150909050901111204150903090b09040b150403020a0b04052d030303250f1b1a0c0a1803020a0e0606090a0e07020106090e03030a05040c 71
    0x18220791850b00702c132000a207003c05000521030100419070190010140404845034540030240a400c2c46d40f1464510b6611200001e0003c40d00394040d01075001c0c414240d603a5500e0b01c80041e190740b039084a0842e2120001118540440348522603228100d80c107842e2141c0c15400d1101110a0f40c06c145603a561083d2660441c02990301c0f000903036500e100e50034050a407034a080d441004040300c5281c01901c1550810301c0300304000d035918259510f00d00c0d4210286480100c01c0401d03400117001e03102455816100010520074200d01c03080c8040000c04034444400c0d000202c0300d20403075107000704048210024058190300006410441078104090b4070445000300c1c1c07000c94151868101310211180c512401c0082400b1500300d8201100908000d21171032800c1200d2305542c0001c840140701d025080c10946468005011a1224011150b0340f540080001e480996940721105140e8002ca030040015420114006000c2949000d0b44800d40b80200140d410b540d2020518001001c000300305407200d28542c07000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 675725674 1250 675724424 675724457
    0x6090614181f120b0102010911061e0a0801180b01200c040e0a050708070b190917011b1403040602210a0204080610030203060a0b24030a051003150507 66
    0x14500001e185807604041102d9071400f510803071340d103071502505590500ca01200001e40300403460300c1c0f01104644081d21074480e440c0318400c41d0140d8130040480b1400040001d00c01c3c1c0c0081060741210b10020420120034a080226020f89400000b0240402c581d9940c2c80904140340d020541000c400300c08864015280f2030010341a644042d000c1c0182c0d4010103000400c0c4034040c13000c04050f14101000b40100c1d4504a01e0b107000d0b100300c10181e46414104030100d91340d603100d9140c0d0001400c19481c0f88540b528000307103041c002c02c8415201d043c0d0940c1216202d402c0d5005510b44036a030348181071000c1c215030f955143d03c006584000300f45401380030182e2150b4090f50f40c440c1003500075013408800588a900703000406107000c01c05066400201102d5034200016903000412070303440904400040b030b410341c202c00840c41c15141c0c4030381050702c404400016200002c072080034602c01d80c25541c0603c05503d039201c5640054150303020140460015071384081340907240c3d41155070090554501f5500b0b690b1749140 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 675726924 1250 675725674 675725719
    0x31212110a03021305090408072d21080108101109092403152a040803180906030a020904031b080306090601140301120203030d050f010609061418 64
    0x56030010aa000c01d80e1100e80f50010400710141800746d8800070701d410207486070316407800b50000080050f081180d413000e0307000400300264080c80c480048842c00c1c11003460115031004002c0c0c41119060441403a0f0030226108510300c904036540c80001d03003215149805604050702d021104540c1f00035007044a01c0c002c0e1a0305201c244110440f0014051028444d52854049007228110354840da018904441c00d4510340b2803401c3d0048210030f07003140c00c034031048a003291000c030035107654001c0000400c0002e8401408001070004901d014107210088180104024045505031a00e50f010340c00f02c40c03944010300382550300c907030001e01034200340003445820082c040358034095000c200c40190001c8180f09060402c030180640010003400d20521440003801080c607540414807401103840e001058030b0041d91400e004845007a01404010b01c2607160101609c02c1c061000e2103000d00081003040005461071196107501c90040c00c1e003107040e04e054800426a0040300040f012554481c50b5056910045100000c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 675728174 1250 675726924 675726937
    0xa05030a0c0c0816050405090f0a08090111011404060e120301090f0b03210a0908120703020d050c120f0f1b06060d11060a020c09040f02090a0603121211 67
    0x203458100c1d4020700d25280e0408410741e03021801c10307842440414040141d180590b0f09403041540c00188581d1010034040c074001e0300c85485449402060415018440300f04000c190b1842c0a0700c0ea00340046802e010390b4200c030110344000c071b00080304402081c0000e5864200f02c2e4401349540441e0a0a10001c810100340da1003a807180c0500d552740c0e000c1d400488010300a0005001045001d08001c400f03400d580c80a540364201e403221034180028110b252103020b1100b030300c0580707400002c8034030a0b46000850350f419449440290050b00c500c9101680b420b00c1041256080d5500101401c50340400003514012a00403094070261500c3c20b022080c0240f8410b0080c0907000280c4c4038a108810400c5841404c000000e030605005249180c500c9001c0388402410003282001500c0c0141e84e240300203130490400c1c8441164550252000092000b80a240488500014003c540c090000c1c1c43e150100b50131140c1500c40184500c4010400e401c160b4000c42c079903002c0445101e404a19a06920718800c269440750 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 675729424 1250 675728174 675728177
    0x15090f040b01092402070b030f07110f0304030803150a03021507060605090405030703030c031a091302090915221209050901180e0c06030c0d0209030111120708040b1303020a05030a 79
    0xc0704c08041590b041008000401c900c086081c03a60400c3c81007250005001040041801800649140010310800105c070391180800c2c15240c5441e05ea1424007860f03402640c01d00d844003401182038559103401944681242e0b0f00601d80f100340d000f112409a0302d42c1201500b515440c0e52680009210348510315203e110314461070245580351064036020701140d04d007031011010035140c11104480d41803041070356420018126a4180e1a5442c50345115415000810081d0001c030b41c4c070107003c00c5074030005048011882d071002c04140307039940c100011a40001c502481100702c0004207550b010849402c11070380b00464600d0113501c000d845501141100c4c50aa109c50b545544042e141d82062025205200c00803402402500c10007403480c000804500025025202c00440001d02507041042c03030341124603581c4050300a1040f085004003c400b260000840044203500c61800507465a109181e01445140e00032165140c6441c2c3d410380300141d40000400320107610840100f1341c040f42041002e0701211240c0d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 675730674 1250 675729424 675729479
    0x1409090c040f090605090d20010f0e0703030801060503070503040b0612011401091103010b07062a02060601030c051306210203180c03060717060a05040c030b15090f040b0109 76
    0x6071300d001c90407507200508103003040d04014041140d450b03203e40c03c00007984031807220105c21001c2c0340d0b000f801010b6000ca0f4400840ca00078040c60440c40110b91202203d0090301c59080903a0303124815a101d110440d002e8001450030400500002c103224401c503000780c0c2c09407002a08070b407a21203c1c5e08480404010540d103040f95401049090350a0060150300e003080c4000c54115450203845080c070f4041c94200a00743d544411500103402548107035075000c0405010701088100307003032034060f40320b81040e910280042d0900111650b020300400482c1e0000180c00448103015107014002c88902c0442c0842101d9a449000a0004400700d40051070080c400f0320909100740503130000452500c43c40d902d0044c080c0c0c0000080145440c1c1000c0105142107002c019811180d40312000a00222a10782003541d21924225100c2d5089906510409400c0d4003a5000300c1e40144030b01d0520791030300a1085070703a840240104a103a0030b04054120000d20f00c010b050070044551640c00042030881d500c403840c02803031070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 675731924 1250 675730674 675730691
    0x1109100908060c0c1c02120a030501140a030503391006051503070e030a020909060907080c0607150f0603140d0804032f190c08071409090c040f 63
    0x5061201682161107101c12600e45081d409200d5120b00c1001400f05000400e4003540b031000f8021b10101002d00c000030781f641c0d03560924110241c0100800c1c020600c40002025103007481c1d0924044207001c0d42d82050085041c201d4282c984903011142d041d10004075032100390940c02d1484042400d500020800d400303082110090551401110016804140b0800c000840c410701c1d0745922045039080916031030140000a5a400442e1500100130340083d0000100400c00c00340040c040361060041c80040c0503a80d84569840e813443e81c4400c040e01d007962140c1d080018000060a00800c0d1640b40d4402d036011403031000c84c80001c401c40c2d2042e403040d503840d613148400c01c8400405000e03460301c44102d4180b10400f800d060b20004c2c82004000d4070100312a40080c0c500303d151803000302c01065a0b1600045900c03501c0d00c4802c4564040c02d1420880703030a10625400b00b0b00003008560501a80c1210000070301c513412100401c110341e400508041e0b400c0c05a003444a26030b440c0c50081c071507403082c285004102280c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 675733174 1250 675731924 675731939
    0x3070e0306070e092202060c1507320319090807080c060c1806030402010e0a0f06110a0510150e0403021e0307030e060307020c0904120906080106080103020411091009 73
    0x1500202021004c84442c0100c3d210f1741011904c3d040c896805840d80c985a4160045007450b01d940a80c2c140c40e6100e02d02c0800a00c41d5103c0c4440c44416400d0310121007075280b0100e05800c7c0350b1040c0310301c0003060003800000c08d10f448011030840d4055440310040703207400940d01c408045a00004003a2203038100040c001901c100104070840d00003040726900c40c50007280d000e0300191a034036074180501c030380000004034066a2040b0035080d0748050080c4082500d940c0c81c40004280000ca10840c0e0124245224000100d40042118130225401401620750099000b0038440284801000c4052009100c0000300345c80c2110a69540304902c02c0e0010700004031405004c0c0582c1c15283c00100c0c640d401007083c10006940404079102004c0d0070340755151284c868520584c1001398502459400076409420401400b165520355100700e41e954035000c55064607048201c88241090081c2c1d00070958560041005040c00d60010000c000f11071221401e1501510000342c80301e240708150000907041050600480 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 675734424 1250 675733174 675733189
    0x50133030c03181208090d0212030c1b0f0f010b06190c1209080705040c230c011e05060103060e01120804031a0a0f0c12020f0708190e0d1703070e0306070e 68
    0x105c1d102c1c0c01440d087d42001d500941d034141950b482d550340750780400442c2101e410300c41030360101c1c82c450703981910107004a01040d503100d480c440c48041d50310a440c06108030b000107214004c800f103005002d940c50070b00c40500031000660f9440100042103020b9038200082040d401c21450140072541d50700030b890303203000031f11480e108641e00500e2084c0e1401c0d80c0c20001540260240c403107010901c0c220325800540640e002803900403554429a10b50030903c1210b0f0505c0101c52070681084410000c12080e02c900c0300441c00ca41180c02a40070404424005008501581030308003441842244007600d0251070f80c2d107107603048000002414030000711005000221700781d400741e5901000100b50070031410344c80d40c100038241c43d843c03144520555400100c108000a140040b00c5849030070510f62030792000a0350703a02c07500c00e0064064000250303050044e901517103000200405601c2e00a5174509003208110507025465002410950038000b40e0f01c52501e441c1c034240300c00c521450f80707511180c1062100c107081c17141c1d1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 675735674 1250 675734424 675734431
    0x50601050a0c03030c110304121a0f13060f0228020f0c01030903120e0705121212071e0207090e2a01120609050133030c03181208 57
    0x40c0101031048022076580110b10204098140c5004a0505a0b56005450400106058100b103020024000c50071551003e2403035a000c6c49012846c4070260070312b013032181c807110035a48a61072451600c0421990080d5840301d1200602802e0000f40724240000040201c0c3d00003004900c10521751700075030100c1c040742c1c441d42d031006440d80050300d1641000a1030a4444041c40e030414140360b84e0b08000000c0c14442d900c0c03003681842c1070608122400143c0e00d12503986406200c0c0601c180f845901c2c080d080da4001c941c00c1c484181c5405410300745250480c1e04141c0e10b0000340032400b00802e110825400c051504185030714401c8503000f52545e10305005110013691490b0003c0345456106440034004220381140d21008404c80c000121501ca1080c40101c4124078001510011607040c0400803800c140342c1c0d8440c6048800b1034200f0054054815120f10b0402294121a004040c040c0310201030306000c0d400901494803285000682c00f030503c00b00c1c004410b540c03802510906458078048107801d030002c03c010740 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 675736924 1250 675735674 675735677
    0x50f010e0901381203030a150b03010506030406090f06200901020c06030402041b030f150e27120c160b03010924061107092315031f050601 61
    0xc01c100102190200040c10654540c0c045128106000d82c83d00c00c040442c3e10000041c140000c100c1c0140b20300340c0d07a07041690b021000301e180c1f840105400c4111038504045540160301d550840c1c1c40d0404000c07441c1c000500a42c1c4850300c4d182050001000d24060442162044c4000540300074810001100d0600411007001105001c1007205000da80015006d00d441100300d500a40c0ca5469101040c0500f4540c0800401815400380541000350907801c0404800c1d4806800c01c0050701d43e00c1c40c250300c000715110345151400d240011400e10105501000b00e150081c0c0a03c4000c603d09114441c07411319026003040c81042c02007203d1801840c04d0040842c0b083c0b01c0605009030340c0c01e080b0381844600c010b2043d1850a55268090918044421048446800034038a03a45070305907516000b034090b00c0e43c120750385054000c1030004510b0940a101b080d005840300c0480d0903108240d4104c03070314036000150010707140e1581c101c0d200d44e40f42d500300b010031440602001440f001038800240e00050b20b0f00501444e0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 675738174 1250 675736924 675736931
    0xf030f0e0411040b0309010e010c020d1b031205090a1212060f050f090a2d1b1209020f0a03230303060922020a030506090709090c090c12050f010e0901 66
    0x70b00e010300d2542a80c081c3d61010020f140d0f2910750f89000c80c010b00318101d004c80c0c5e0307509100d111802c0940119100351001701d151076a41c00b401d8626220038a0041c2050020081180403202d00003490080c1e200c81c3d4808401c00850310159415111b10040b09200d9440c00c0025100100c0c4034011117460240500405030065583c0d03000307040400003a050001c140220f801802e180001505144150700b00505541c1d00901040718010035941b45034100800b1980b0040345820210600202012035400c4112188103a403410f207103c01c9070700c1d0300000e4451010107aa020401302090201943c0b0824034400039449021031410450082d20000c0f850300440b02043d146400600c00c10000d41c4802c1c901903800341e8510310b50a1b8200d0000e480c01280c115000c0d010f0f410040140c800b004000d00001c2030fa00540b0314074101c6110590300c0341e40700207946c0c000c0c1d0014042200008100841c50386904141c0e500c40150400401201c00882c00404441d81155503d080142036001084411445415030f9044480b07103000f80b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 675739424 1250 675738174 675738191
    0x315040b030307060203040206120a020a0f02060f060f180c190c0b062707020f07050a03050718060b0a0e010e09220501060b07060515010f02070e06030304030f030f0e04 74
    0x940b00d0080120103401280c000000404664858003100c186120503134842c00242891001e090083d08010100400325405018840c2d0f103e000103030041c0310341d04481c0d1490060f6100818420701c585c0000071103030484488020504014009a0214070410032141001d848850742d4500784099410790b413840090011204485002c80d600c00c1840c1e44c800c00949041d1400420108610064030703034810600544080c00c028460b80960105030400e00d0198002110b0b035858842c4100400c48129101c0200750398401d10f420001c0c0710a407440301c0030080003090002001e45d03543d105220b8a81c00700121b03e0000d15101125040c83d0b07009840131710120300903194100e043c07901502c003400d481c50fa98010301400907815400005c21900750410302c080e001c10603070309448544619000f0041c00003a00d401065401a5684165039445600644550340180d801410014035024407140081c1c17020b040f003a0140010040400850500300090f2207691003a0340d420301e40d906008000b4100940c241c1194072990a05156 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 675740674 1250 675739424 675739429
    0x9020a17032b020408060601110d0207060e030c0a181a061812011505180402030312040f0506160e0405010612180b0c0901090b03160309030e150315040b 67
    0x58800c518241c9074040000c0007600b0042500c0e1046003101c86200d8000103000c10b00c083c000c2040d0740160341c00e885a00200340d90708241c41d01c1e002c01c690714a006a0100d074041120b40c7c0724011141000c1d00c0076082d00e402c20030803404203050740c0c083d0b000341401e01401e1042580040092040906042600b407003c6030030451800011107078843c04451010f1091003040e40304071a61032045883c5000b103440020000e0348003140005800e41c4030791061602c01e0324800c540c4108000720611851045034001d024510b8100300b0600e00c1034010700908181c8109284d40c1c0e0301400900208505ca00800707401c1c01210340d03e801e03010005c04000c00d003401980690300303120040100d150020369800c884049480f01140000041001d070301120020040940014258014082c0c5030f643e0100900d02a1020707610b0070049601d03840da80c0030350311068a003806060419562080c03c41d1082d8050410b46100c0c7c40d2010760508000c000440d900c0343c021381010303074071400020310880400025480c0030004050740d040c00b146200a00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 675741924 1250 675740674 675740677
    0x1303080a140c0f0c011d011503021c1401060602060a06080a02330d0609060806010f0905070504050d0309090b0a0f0312110706081603050408090d02060906040909020a1703 75
    0x1046007114000c200210362103510425140044c5007000200920b2410b200300b0540c001c0b0030400800a546442300a00030225440000c0c41980d4014010541c80700111103c0040000082e000f03413011000144038054202e0280140401003904d17900401c00c605103114000100d0b4801c0e8000703101507110b1103ca00c016201c5510009c030124400002042d030041d91883d80790041c0a1500f0b1440c2c0c8000051744002034482a88054103540c42181e0400007181c1b41d040c49aa038007002c1c0104100110040420006000e550f0015540103845103407040c102070360303070021900500032610708130045041d0380400c3c814649203101e6020b9030801180c03100000c510300f030b40f003e00380f040c14040a17040241c100901c581441c090b0006464034140e00b4100c50382c2d6655076030010203070724003a20030001e00100101084e4400340300c5d0045c5070240342c20543c2540782c803901d1010000d00d90f2012400b26080001440203207003690f03846010700000c054100b4007003109080b42c4104414007469070031101c1c4030000301074024840381c0c0020 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 675743174 1250 675741924 675741931
    0x10806060d030201020412030819060e04080f16200a0b07020418020604080601140d02130e0a2909030f040e0415050a06080c030c01021209181303080a14 67
    0x241c1c00e41040c86181012406842140c1065101441501600c030405a00605203031180310744a00c6c2d6245080e254081c00b003611003621401450b1420b940105021644801c0280111000b1003203240c03034226145004118401000d9040d0381c100443d0214201c55003107003890745502c4c50b007100d1410410b414000058018044c0c540007900841e95403141803400b80749a00300d00c00c4a6001803410b074803180d5441d02590340366002d01841001110021485003103041c101022026194028595010010b000240d0b800926091144d04040e2180741c05e4a00481c0701039605550b40c20580c0200d83d520848420003000d0345401038042d41d0b9a41c01000344494280d600070589040d00c0034031a107c030362601c560034540d6440d41c00e903516890f40f502d08800c6c448564926801201107801320710554148a03811001c150b21014214070300c40c05030304600f500e088454840e2009004258008007440e080310315a03880008803031401c0303c1080d0304070880c0c0c3c0030b0000d054100c80829482404401c0c1441403c0ca0070003044990003014 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 675744424 1250 675743174 675743179
    0xf031e0507121505090d0909180b07020313090213080c0a0b09130509030702102d050f0d050a14010f06230d09030e031b0f040204050a0906030c090501080606 69
    0x9010b810030800c94810454a0b220b00c4281800b4a0600a0142d0348880c03c45540f8000b00d140c1c0d0000040c504100c1c040c008803921708180f59070f00040700b0307260038854480052040c02140800c0100c182c500c0154a4100064089407400580798004601d00312560b04441d0170011050b84468041c1c0c8841e0f45150030001603036074281805888a614102007000c500110300c4504132541404200808000e0020242c25000e000f1200c0e0319000010340c00c01d8880038160b08041440110b8800c1000000002d99440c50b080320092074118540701c0802003415003500b1608044103003e80b00c00600960390210b0040c1c1140000d0001103d809514103203848000202511030081402118000105804501b054568000040b403103c01c1d42c1d4a0011400001040b4102007200869061034590290f810300140b40221106181d40c265511094501040030300c40d07040580c9680300e90200004601600d440c0591002807020760b4000c12014190b107411105e40c111600004040c03441c01004001000d0b0010f080c41e04002c0c01d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 675745674 1250 675744424 675744449
    0x1008060702150a09020d020d0b09010506010c030e040b030f0313090f05070504120203120304060c030509061005041d0102070302030d06050d17070312411609030c0f031e0507 76
    0x103417000c02e0010300e4074100039510034500940071050100380340c5028416a8108004c01c080d98810300150360200494202400144040140b00500e0920703038408801248005c04940e0680d6030b5940351031456028180681074102070000070451401c0c503000d01c0701c0e04051480c052050b4581400002c11501980c420007603804000c041c0801075490610903141c1e075819581c0560703624542030920380090010700d503800700003174500400175507458800b05c1c200f402a8003e01d205102d13a80b0340030070003000c0c1514580c0e5449900c908184100c141000b4402083c80da03200360061a140e0602211050072078150764056070040c80c3c20280b2100040c1d401c27012038035003071603c408281c4480c1981021516140011032204d0191b03c0d00c2c8090380c000107104009040010300c04409020303019004400c200800001003c06080d41400000c604030503111844450030010501d860310049540c2c0c1c540d08952034040c2d00005030000000030034003d10880400000f104007038410440c1d2202000c0e62019aa40f0091180c103001c07070074 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 675746924 1250 675745674 675745691
    0xe15040606090501063b2b050a0b100303050f0307030209120303100621020f0d050a05011401050a0207090b03070e040b0a1d0303060f060d051008060702150a 69
    0x106a0200000c1c180b0a00104a00d44c1c4440d40a068044903040325803d50a624400401c120711000280502d942015000d030b1045410000b841113050800a905641258080320504640701c01a40c0001203401440140300c1071001d400e003007044101c040e250403070b40c0c1041d96040c000700ba041412940f1990360340640c9641c03692481c10440083c0521000ba6038000251219a60404c00002c041c50140c900790307401a2800b5074070b12042e40d00f500d0641003024400d002300d520703a00e01c4440e580640145421708207500d10300b04081200000701c9400710703000040b0b1039079a0b00501520746a01400020040282052441e101c40304902039981c086a00c903840105440307105c03100c01e9403000c2c020540184400ac4035600c59050a2070003507001c240c201c80010701c4503d060605c2207502848001300c201200224007652540c3c030b4000501510482881034541c0003041001400314035121031146901c40d070340a00c420030309070b82002d00340e9044c200040e0003c1c04540c0919900f40b9219144000e07070742c00805a0b0b000040d001c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 675748174 1250 675746924 675746933
    0x17120c0a1715092e03150522050d0906031806050712020a0905091006050a0c061404030302031b0301050a05060c0703050607080901150b070b0411040515010201050a0e1504 75
    0x2042c40502c0e0000300d004284840024842001994000b030503104480d95250802d69020b89040c40c4000380041c0100ea843c503d445007640e000c50b40005001c4069500c000314804140c8075081507410032503090784104110303103ca81d4001805009080145000d001a0354010042c0c0d158103860540581840d942c4c50219400c98060612040310050221056450711040c0d0070141c0107050a10a543c015106400014016007420709001c096461a486950910207200c0003100c2071a039010084401c2561802a0442180315050030b902c658400e984c0075076685031000c100d540381500104591107007481440140407d1ba107211040c000e441d0150390064a509005034050301c2d20b9866400640b1070300a1100340a00e655000c0d0546100d000020b000307226103503107a84103200428040c0f04a107445007082c80b403940000c0120844c540c119015807402d001121411300003c0c122a4240d414100d2007450701020a060350302030140c0c603801581424200100703100009050f0320b454002c4550180040850000390400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 675749424 1250 675748174 675748201
    0x6030b0f0703090615030303060815070f09050a0e06040b04110307030b0103020f070b18030c03040b220f051504050904030305040822030c15230717120c0a17 69
    0x94108005000c920445c500d0101080c1841c00150002400d20b0b43c082661203001a20582c81259440c00450360f40c0c0d400c8040300c031503203400205d04c1080800c0b01c0c001210b42e124202040a44060076800b000c40c1098410041103450400a03680070341e0a2051003540c941c540c07416242d100d18a402d000c1003281c44600124001d201d842421140d030036000c64240240404100e8180c480e440e502c0d452801460081e400380da5a014018414545900c10031007846130040c41e2000d80848114000185503040c10300007103201d450481e401c002ca44105d400da0811003464508802d50004800304010f80c034090402d07020824598004101400b03154546000c1400c000548088448800c0303000c4505003540003040504180861507c001d441002c0248004035400412850114020b54035440d91101d0740700e05514034407805804013a49215800a000000102d4208410819105568020fa50f69813080c5404410401009082c1d0008404280200ba00807a0440704c080d81249030540c0343c14041d40c514460074080e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 675750674 1250 675749424 675749441
    0xb0f042607060e130518061819080708280c0506131719030c050412141f0506100c020904060b0301061d040605071409041509020c0d1206030b0f0703 65
    0x74180b40104206c141c4141000d942d000e0034140060320000e0721254669801d480d501c00100d81e8079000300264489400c000640342e80d40700e01c2609100e04040558840302c6480e000652100000359401c00210500c09261076003000b03c82850800000c2e421450b100c0640d903a0004001140d079411040c2c03040c1c240250100b2040c1c410f000310201c15501c44401d00792003402e042003c4441d0110381070141211040b400742c0d041d42e0035640120400e000185032034840002c08800c24040b0b410314016412624450b600e5400c2400140c02d14200205039418000d0501903441d04800480042000542c00c500040e40c60700c0e0420780041e0012408214603050000081c0149820343c0011101e00700016140c03c006900018bc0d482103006010400c100c0e924200d095501d0301c410020020508000c200a907180e1a0aa00081500c0303200303a84500c015440d032129404903406001300110b00d0348800d1181d420181e00c034801d1490030010b02c0f401c2c0884c0d851035940d140342d0000600400d420580d80780010b04003d100380e100005 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 675751924 1250 675750674 675750709
    0x1e1d063108030c0d0e1c0f14100603021801060f2303010f0e0a1a120f0f0601030b0a060b070206090d02091801060504020304200a0b0f042607060e 64
    0x1070390218643c1095039291440162000719120000c51090362a04a24901d9000242041c0e8085800c040c0e4801625040340c0e401140c0403a4540c0c02d244c0d82840030001802100c0c12002c0004442c1e0450040001d60b602d1080e8040d0900c0c4068014460b155003c038100392245900c1c02e080300ca1908190244050401421a9078030000000c0000a00c0c0c0700600c44c2da00c100c6010700000e100c652540301070306043d184401281030200b4860440c98400f803c0200c0c1240c05540c20b0b20a65401200300650070341002c9401b070382a90542e008400600900203040111904a450a802008160f1501c0941c0910740100b00b00a072081c2000b1070303030304019100d403043d501005500501580d03c900d010300c08040d52503002600d000c915071034400c000c40c103400c140c403c030780c001c0b9000b4204045803440c400041e2a02010110181e030414a02c000c00100815020041d00841c0d07500104503840d5801e2000140080400da81c0d0305c80c441880c41440d100c800c5020a160042c0c2e00f89141401e5404080f001089410699103103044 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 675753174 1250 675751924 675751927
    0xe061201090303060e0a1b050f040e09010207030e1f050d14070309060f02180609030705031207020102210d0e01022a120405011e1e1d06310803 63
    0x1c0c1050f81c59802102907400c1d1100016054503072240c4001250900000c03104840042890304942038010f101810350941c8a0b8041440c281d119065000b20300700030342d04401a13039000319040c0101508240c54140c002c000f92104182000040340050040b001580031100348100024900103030303034030368100958104048803056403604082d40300400401c04840241d91491800e0301c20111146280212b42d00e44988850541091100e8000c0105651094501a5141c418100c00168a480038448507400c2000055419290100350001904155002095402184440c0c600050304030303100041e6680303140b4035103000074080020700c665802482082c4082d4410760f40880c0f24618840840c00803488030610b1001c0ea0340d209204204c5022500070b07801600e001c29142e0080290750851a00111104441807401c082c0201038401c0116002c00247c156500051100ca0341c8911150240360260345c04034240d0341213203040040040381c03420381c4840e40900e050340d401c03181e808001c842591522020303000c200c0599 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 675754424 1250 675753174 675753191
    0xf0605010e0f0709140918010504081e0f070615080f0a0c090c0f0c0c030611030a050609060102060c0904060807080715020303010609060c15050a050106090509060a0e061201 76
    0x107801c4150444410096101003000074a5441c8500d0b02401203561845103003514000750700c10400310000080c0401e0281d03000703a900c00c00d07002c000d0103107500030b50040740c20360341c1c031201c5840c0c0c044a880084030108a0764010008a0341c50140076003203c2030039070849400a0038801868030200c0c2c51a41c0e07889541c49110b003805078a085d5034085080400320703100b0040d909007250740d41c140130152400c0c24810000304d00d2900f01401c00310b0051003148101441a90170607071094903a901e0508407901c040b02c806110201004001145d8490b1040742c1d001181110040250328202000075611f18004090f450309441c0412640041c3d2543d4000d080a000d43d50141c682e42510742958507a1a409071240e0b4564820b5640b004001360300100031241640c11035a40c0e0450300b810504242c032903424500e01100c10300d1a00a0000f401100b41c8100c40c010703040304c1300216980d450500020509903075500203601c01e952001c2444030555440d400c084c202e03880034601203079aa0b079030fa0001c1d40c41d92900c55000e00650034645c10 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 675755674 1250 675754424 675754439
    0x10e01060501110a020a061103210a060902120105011d150d2009012313060201060510080114030f0a050309030601060c120e0307080d0207030203060a050c0f070f060501 74
    0x1210070303900c0a90329074140c195000409a500ca03031807800a9005480d00ba030510a0760311400c42c81032240d4210003224036240d41c1c1005080840d1540500b0280c240c512400c0c400f00e0f4505028010081c45404010740c10014505000c1203850010b01c9024140480d040c0c21005010b1844008020702c00001c0101412071034004020940341c0c8490228001b0500d0711a251408042940052140d00c080034a22420000f0318801590740c3c0103103242d010031004023035103940e1190020000505c0405501c0c0c0c1c9a400c85440c011000c2e09481c1c041d0070481c0324a001ca58a900e24030b50240c202e604503680c5c94005010303984074001090034442048290003460040b806004207000c0000010300646c68150200c44175603036900001c6404500400e001000900d9044400032a14460350200b50308000013003d90b9021503403105607518020b1440c50a4002d80c001040800640c581448030641c41016aa01840180340102d2003160f540710f058520842c00c0704c0450303c0428020700300740050100d82c2c48103040099503103a106 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 675756924 1250 675755674 675755681
    0x60f04060b190908010c080f010512030703030b0d120e030f030415050d090c0b070c0b04260f060a0c17040804150210020304060204170d020318060d1a120f060613020705010e01 77
    0x1804405184c023640001607034200202050010101580a1420422613550460141400507901d66100d004003944101003002200a10b15070185900c8260215101d04149400c22580582004040d0000d1008000c0c0c0c500081d03011032002c0c520302d40180d0b1905051180d40c0240311510004e015840e1041001c101200c4600040c0301c50760103407501c0110715036100c01000a611860041545080c07000d011001c4200300c80c44195101c10003901550b0800f410b40d415245000401c0724042d0280c7c2d12051640324140c0c01045a4031450800a1f181c00185401e417107501403841148590000f05d00d0508076052030500c20701c100c0c0e46e808030803c0700350b541c0d003018141b210103501b0500818040d81e80300901d02440c602c0002d00644412107640155040801e010300d007180143c1c00500d00d170b80205c0304002ea0b00c0428810310800180441178056030581c1440e8206104441d08050100042544075203005469140c0c009560341d44120f0480c0c1180050040340c8a520290250780c0c0c0c018619820004c440926603010340 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 675758174 1250 675756924 675756931
    0x2e1203050f04060932040902030a0b09011b030605090402010f09122402090a052209080c010b0909071802041d152220030f060f04060b190908010c08 65
    0x1c1c21112888442d0502c05c4050003010396190500e4801c1500803a9401d013500102c0203a4001030a440b182281500d4800c2030316400c581100c41b907550744a07052542480f100c0324605503045484c04021131410315012a00f0200702400180c1482031081e61201220b200c0d8010401500c00401b040f01c0c807014a1810100f8040300b20a0342200e00070081450160346194030aa41031410700030700e02c070100c80c60801486020007126903054400d0ba6060506550104103000c0d1000882c460b5007440d95504021400a00b100d21700310b05e8900c05c12070351007400750540001031200240ca075810140c0c000300381811921402441540d218010807080d00380c01c844841b501c0854a071041d0b030441c02c0d40c08001c000008101100300050140790703040340603600601d4425a81d61080245040702c0780b030000007129502c61030003603410803a071410f0346c07002480c200500d41c00c2040308010700d0201940c0601030756080c5920800c0a002d280c0a40e01d84605213181c03100310700d11610f043c0d0010300c50900200103a05451030300425600046 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 675759424 1250 675758174 675758189
    0xd260301080723010f03150e09010509070e3403050405010b040e030a050c03040f08071401020c0f1c060e0c09060f0a0303050a12142e1203050f040609 66
    0x910006a070b00707000b115900c961410000d0410300060f1840c0199503101c52004a4000c0581e1390015402d01c82d01042030300040d0140c8941031246140c034400c03090940c0d20042410700309410007201000070204268549800c41d25148042c0c48a2010107400c601d2541c407210b1345060102c1c440d01071076545405520040c00b490055003b400040891001e000c03d60b45a41d0041c0e150381d00822400c54282e00c00d4001e020345013164000d0340e03d040d13a0340088940d08012900aa2400d411841c001c11031092201c20001c5c61103402c1c0058a01d1107400d20010315401c1181185500510440c0741c00c03507218030010070004081d5442941000551401c0905550f500c2144030309500402000300801e9240c5012405c0940343d8400424030784c481406c6603421500c60f088402c0a000784014541c007003100180d2401004d80000003450f80070035601d80591a00740b04020514044c1d1020015882c42da408a0320810303050035142c410b41c096003000028907044075a4032498403140000000842c01050a945c40b411b56811250f46 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 675760674 1250 675759424 675759433
    0x106030f0209180706030c02030c01060801140106090b0405090702010b03010f0b0307060206040b0a021309060603020a0e06090d0305180a0f0501020705090f0f0408070203031201050916020c0d26030108 88
    0x1e42d0440e00100311001c4049480768400390080205c0340c803075000a8154010745c815203003000c0006d1503041c00c0d54401d8001010b07c0c1d448002c00c9419040c9a46203900416281c40e0480d2458640001d42c1c42e548541d02885002d41c070307040c0008492078001d410a00c00940050002c02c10070031a60005802440c0000a4911900801d100001d61620008055003c2c940001d684801c030748511000728000e60101c0100043c0ba81c841000040e110640c0c840c0c83c0052a0a4502580d40c1c2200f5400500314003803012103a22408060000c2000c03503c0380044030481d2949420140e80e0340d010714022210400d44940112340c0b0881440011680003d01c0d6840400c55000780c0031595030a44407010803080000032941c40c81680f5001c1c0010344044c1d8000c400703136001400fa0201918024440d00401e0641e440942e0410402c0e20401c01040503041c07040071a0380c443c0b181030000030400c503451002502e80c00c4074140140701d0485010f4800c140720443d45441089015500600e80206199030011401c3d0002d104940e228000c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 675761924 1250 675760674 675760681
    0x803061207060e0f180a3c23010305060906010501052802031303080c07121208060a090614030705031f09020a050d0f050f060411010f110303131e02060304230106030f0209 75
    0x4220070040102c0490700f4807c0381c000394030088080240b0380ca0105c40001c2e111621004080124084414040c40c0100040c2c4817500d004010145001c00c1139200d5810890200701d040455101e010040180c031528840440c80454407440032031079801000440c42d1103800c074000c004108100c0500408070504c0441c01c1e00e02c5c003580d4000f442e020707408687c00504100a40d001e110005481408503540c0020010300e0a01a5510768540004440d0540c00018100d20304180803003051400700120801807400300c00800000c1021090041400850410700000b1a212101402150744401514001d8130010309a080c02000d03d041031400c101d004481a100c601a03461b4103480f1000c00f00d86544216009001a185040c40200458142960129070410840b1040450f10b81080a2001390b015018100b581d0b1840740b1030b401c00e0100342075107007442d12082c2280081140142c8851003500e03481900300da44200314908007101001c021810b07810085103540303480808410848903070300780030742a402515101170781c3c1d5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 675763174 1250 675761924 675761981
    0x207020102211209120712030b0d0c0b090f10020604021c0c2709030e1305090c21060106020607030509030a0905040203090304120803061207060e0f180a 67
    0x21800da620741036854200041c00e045043c3d4282250418104001c07500e5006840f51180c04a4024200440d1a5158034200d0840158540107040c9224822030b01c0460104456850056243c0c941c07094008010002c1011003540d5074504030b00800b090060504d4400c0001e003a4002d4440e0400c981c101c0c82a8042039040d111003003a441031400503640414504c0c411403d00485540c0410000a18805018054028800740c002401900a0a4426100c0c8a80c1244007000c00c1030826501145199080c54402045014080003c0c2c00d0516001610001070301408803102100c00c000c0d150015000e442428000100180c1c009003061003210990340c10009070b10f4402d0f503140c49204107a50a000a0317903001060080749001d50045403c0110b5000301c905e410340e941c04089000d1950241070f1040f180100402a043c145800200c0390304c510603010b840c1050401ea0b002d852078a032031703c1c1d80e80901d0480304080d40d50744689112010191040d401c0d10750f107190401c103040240c2000c400c1201500341090a00b650308 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 675764424 1250 675763174 675763213
    0xa1d071815030809061804290402091c05070b0a020d020d050f0306040510050d050a02040c0305040c0e0406020d020d0920010203040303180302090106020a060507080c0d090c05090106030207020102 86
    0x240d603c030544903d0000365000704000c5400441504041c64017075440c1164965561007a000d4900e9131064410501d11101c07050045c8044001603e40201d00410144145555080480c00c424056212030700f2640c2c01c904005251580940000030207220010b030a10710660001004149020b045c0c0c00c540410749a0075080307850340200115080320210a1010035142c0c41e0580085a2200250071010100b03035590b800100800000c44040d18590810700700c0ca0306600346800b0b10040c84900341028401400d06da07130303030440210709481039000d610b000c00040b030104529a01115260701092509540320154251898020b02030b10100b1501c15112a0307140c1c441c411924004881d4020507006503003002e245880607140384900030a120703d0400e0003000480141c0d41d0082c201c1c003802090340108026111031030400200e5801070f03e464148502c280400882c0d461003030480385110182a0003103884030b8a4908174214465035086240d1002c0c0346000800c05540c994083c180700d9000341c2c2140c01100c000d0382d251020 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 675765674 1250 675764424 675764429
    0x305040e070e010804060f0f112109060f040305070c031419080a05131d012310111e0d030c05030606030a09140106060e12030a080a1d071815 62
    0x100b807a000005006c1002588a520b00c250308580101c0c6034544003d900040783d030790554080203071303201240074080d51410b42130b1000281c8442c01c00d18041e0902d04a4542e03200303c01410311000c0e6508000042c1014461803e03120302d50b0b405180f109806860b490807200508203410050040d11417103a450141d020344010350400150040f007018030b03081010b1011a610b0740440c1400c4000340910000041a1054003180c00e10b95040740703420700381c65040101d0444c503030601c80041c086030300401400e0704466644030120350310380d00d280c20321010110343e499005003030140308044481c091030010030f140d00c1c1d6031740400c05882011561b035040002514802e403d85030740c00266050307504802d0910000d0041804bd40c440d600301d80c000e200d17000f000030101c000340f030030b4450a402180001d68008403002450801c4900c04e41d0242030040510305110302d052000700700500003403208061a8642c2d00c070424284946e444d2105401050b410b4507181c0f5281c01c5084503c074000c64241012510308004003e0742d12000d1100f009 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 675766924 1250 675765674 675765677
    0x50601080f0f160912080c060c2107200a0615030b04080c0102070b09010c020c0904030507030c020a18020316030e0a200d050c03100501060c0b0a0908070305040e070e01 74
    0xb1141c540200b050f58510b8420a82418403030941404070340b0f9500380c1e0302500c24500c60b11001d5a585140040581403900c0501011190b02c0141f240039032405043c400000c2c0e175190001c441d1502d680d10030b0f080340e11401c5114550400080910884416400404c3d135416050044006104600203070030f618060303515910002d0000c10000000c00c0000c0e41140003000d003200d40e54005410a17047d500c45050b045410307140c6545503907407085007844598041c00544962002190009014502030300d000e0b0003841144001420030503c84104411036488000f040094180d58034121940410071400304000e43c020b440c498074035031b5040b108c4040140b080c0681d440540c0000081c0c054250a541d03072030460760700c040400503083c02000f1154119125411a0030f00d050044004021a01001e0305043c10684864540c04401d0b007048010710030580c01a0800040c140d200860ba80607a42c2c42c11681e006008442008040d0b20700001d07004213041d4810041c0c0207460141540d1505501c4980c0191411120001400d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 675768174 1250 675766924 675766951
    0x6090615021b100311071a09070e040b1f0305011a01090b070804050d060e01230f100501111f06080f0318130e160906060809120309070f030501050601080f 68
    0x83ca6688241c010010100c81c13a0318440c10110180d840c0076800d2102000c540c0f603140c10104215002030204410f030000d0691745003c4140d42016124445d18401c0206028008001c0c03600f140c0c6091010f1100340c0086400400030000e208034000d00410000c41c18111500007036030300e60041748000000c01122506940546103a1609140c5424801b0291010b038054408940d5120f6000350b1140178060242c0d8000c060781c6036825142000f071401440440074000b500120000000c12092140c043ca0500590300c2c24200010340c10002441c0614140b042e450072055024034954441503230301150030000558003060180e490201c1c0c5076000664a00403080303500c4000e03641e00c140d0080360918070114803403590310f00780c0424104000300120b45881c1480c02050f0402205860421403c5c0144c400c0802030012442e00d10101e0503c00c0615a6070f089540403050101c90001c041001240200451002068200088508581d80e400d0040c001d1004440c0d403800302d652000003601c5154845100c5216102504000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 675769424 1250 675768174 675768199
    0xe041505030c090c040b0706020405130c140c031309020a0e0d0f08090a150c0507271a031606030f0504030c110a080f1e0a050709050a06090615021b 65
    0x1ca0840003416a9813166010840441d2000c0b281c00188201401100c0160303079140703840144038403104070405007403c003894405007000c0c09a10080c03401e00d001242d0445a2940d515000190130341c400c40300aa0700002ca40e01000a074441550040c0c4064505501c1d44241c20302cbe10302c10721461103400a03004040300520b150381000260484040c04402e600070f41088802034030354414540c940d80e0302c0d1404001c58458003405040100820151000d82411000308100030807a00e00c0e4003940fa07030b80d0807900c282a1109400b181c00c09480e0410810f4450040490703800c8540801101e21503a01800f45000190604104c060415424080d0303070302a660540da0003090140d20744921604052001340c2c1c13640301e00d503504005101941080340c614860828000b8285403148200e02c0328003050031340046101a0007041101c0d001c42c00104d211030480796803000101b015520b001e4200014941c9410215459280a80100386c40340d40100469006020b0f400b141c000300d0054641441c02146a518541d1003015564107 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 675770674 1250 675769424 675769429
    0x114010f06021c05040509010320041b0521070f0206010e070e0f30010e0609060606030a090812150a0f0519030818010f1b120c120e041505030c 63
    0xf044400140d00e401c505081c1c850001560080c020b0b41b058442d10301200e207152008400314280f0760480401c40c0e08000c803030700d02c441c1401d0070115044004180305010070314014036004940311007085605003029107121701e0454409001031001030a0900140b01c1c84c070000c29000c090b44244e90081d141a01c0d000280f1500c0820071034480e0406007060f82150010090b45080b105603400507408030544110104280100c2d2422802c43d0b00c54104401d980c0e110b6403c1c008020404241c480c3c02c400291400c5681380c3d204520b078006003103003c8c0001c01f500c4001840b8804410b40310b840d54082d1803916001450350f03219000700108441180200055043c40321002c001c10303d0700101d084400601c85c102c440c40c066030394950503026044810100020364901410a001e50ba20440c088002c1c1101e040c423550f411603840c113200000f406c0c2e80b8001c002c1c51100c0d9200c08800d005110b00e603d1140d12040d00d50030800500e00c0104428655a6800c0c000c90411200e002d003800c3d00540001030f9a13005e8014210032840300c04 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 675771924 1250 675770674 675770713
    0xb18010623180a0b01122313050a08270906040213050316090e0a0b0103021302090603070201090302060612032512050a020d08010b09090c09030f0114010f0602 70
    0x4400e90b12280100c0c03244103141d031800c0d045110315040803000038841074031070014180c044500f1030502150b1900e85801541c1118901545080034846000320260791814010403908003c054054070a01c0780821540c10025560010400f1820f01c102d01c00000c0451210904000719148481e50300c80301040014200342800d80c0904002480185000019035588001c81c0c2002300d0b55400081440c4c0000d03051120f922a0b008560705d50307205000801030090345454800c810541800000d100e82d5906090110380c407007070380503240800c8004000c035690b800d01c00e4010340203000300d0340c0440240c050640000c01c00d00e4105820507010003408007841c6070250046000d84101c40849460414031002521003000c10a040004600000640c5560f035a0712074114010740f1b04a080707051700381000a040e00521081c3e4801d003c0c0e9040d000243e440003c070b80c640b40b0184956000b5240d480d50580b0608064141c0380390150880550300304001280403031a45c807070184100804441c0600c0015a0100341075110542940c407 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 675773174 1250 675771924 675771989
    0x8060403032406111507050a031e02040e06091b0f09150307020a03080f10030b040203100e0c1f020303131104060914100608061e0307030b180106 64
    0x9000c400e14034202c2d070300c040c490704080c0c101d000002c2c02d0003041d68244000b0002c2c001d08100040b5600c50b9498080001071041c41800e402d001099181c52a00d4556800c401d11403400b0b0100d41e209644990312a02c119101d00c20484036544a101390001040103040e54a0500c400c1c1c0800501007840c0c4604000350141c2680b1082540e504104105420404400354001031405482c0d50741c050131011401c0d04008100d0b81c03000c0c0c00149100b0304901442501404c20a0f1202102e0b402131403000181d966000080c00d0000d0030712641051401d0003011101e1b6080800c1d680c020f03a82c2200c8603258041c40f00c0380390444c0a40102e011016074000c1020401075032581d24102509807140c40440c080307001500203d8240c40b680d504c000e650b1034440480c000381c0c2e40748038103281d40084485040c8000b9444d10000900c403410161070240291a01904450b400d0700c0076410201314a8046d0031a0856980d80c42d000500c82c108892000c0a02c0c40941d5044e405c2038180100421181c09882440c0349004440c00b42c20007d0002 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 675774424 1250 675773174 675773201
    0x10e010b0f0c0703080c0615090406111c0b0a060302090a050f120a080a080c07020d03030c02070f03080a03051806010b0a110a030314161205090c031207020a0504060806040303 77
    0x6014401c1000e40801115003e1841403200b0390b1161000b111b61841c041f8084c0c1000402030f194139181c21300c2e0b11010b240c942d1260304610041010341c40c100c811030305031141a80c3c103240e880340c0c05e000506012254108603001181a035402c1000c2c0c0ea41e41d4201c00301d000380ea4859500c050031400c2000a4078040d40340701c04501c2c0090905420880c90019289403d50101d0f00719604078001c9240310300c0a0300419075aa0202c0d14030441e40c607110b09640040d02440c02034000806040c0e85a42c1c200045100708869070107000c03030110521141340c0324280b0010f07981007200d55000103070500d400605c0058801e0354003074140b0000340c010035560742812961006908aa1074400c10000ca00740d600b210039108110700e4484500035180003803410800d24010000c460000c11051014840c548160031959000c0b284180601c03000c507001403261540c08065003800013940722a0fa152140d510510310071001140103008061088691b01006075640c000d010550b0b00138441c180f2160050300008001ca4044e812003000007010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 675775674 1250 675774424 675774427
    0x130201031506031a010c0209040b10080d0c060c0315090507030207200102010f0e032b02030f010f050a0e07180b03011701150510230d05041a010e010b0f 67
    0xd414500c840d81e145500c04800a51144210221036031a5104c0c07440c00a4203203803005a04240340c012174004040034000400d51050390307001422480e10b1400e040c015200420a80f01140d20900008042e10310340c880654420389800b00a040c0c5d14003a00c6544080c80030000c1d40c0808910f4105404001c1030002d06003401d25408001000010300b0070170781c2c6110341c00c14255070244c1c0e00f00400020300311145415030540d8140707484a800709041000007600c841c2044c01c136603018000d0440d15201c49104e80780141c2c5030164004814080c110142d0005141a2914500103441c2140e03103c0c00c0240700c802d21700c9003040c80d06403031300820b411b107114043c142c14244001c420b10012607510070180c42503034000d900c61540362110302000800e0400078010705601c0d0765040001c2c4100d0341001d00180c80301f284125480180b0900c8001c03548142000c00303084200254070384280d9203071035403501641c014043c2180e003140c043c0b0f14500b2160503915201d8401d41655010b502d40311380c603802c03c0a214080d50100032030b0b5020200 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 675776924 1250 675775674 675775691
    0x109050d080d0903031406010c0b0109090c030b09011b09060f27140301182316080a14241905010906260d030f020904050403092301020613020103 64
    0xb080d0246042e00e6109a500055002e00c2d5101001c1110300582064100140f03c5207880c0401c0c6210b06180c15200b03150000140c1d14180d00e80704100d50a07560008001d401a1070812a403010b0660000035645220081c0c00440d419990040b5180700c10740c090000419800e41111100d03610031088419004405481202403d5900c0c4400e104180c85a00030300d0101c001803514203031400c00307000303155410744141c00142002d425035079200000082240e89000d00740250300071400486040044505145100d5060b203549602c0d00303640d640b25020f60350141c0d030303045440030803e00f0400009804c8200d000b10f10040d0080c003194410700180343d100540203840d15409100d40300350710f90003417046c0c90091580174000251140f8003c0595010f40915140083c2506c100c80750402c4a1030209100c020400c13185000201c08104e401d1110083c01415030035500545820100000c00d0303001100780c01500c000e1500401d4a059107546804d038002d00a00041c010b8101d840440c14504400c0071407580719105040c049401d40 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 675778174 1250 675776924 675776947
    0xc030910051302180a061a190c080f090a06080601020303181e06060a06030c14030c04180b01031d0d080405030415180509061c0f080c010f0b0f0109050d08 68
    0x1640841401c00180b0060038802c075980144603000c007d00100301104103e007a5003115a03094082d100b10003000b085200724081c0d01c0b9104103009803281e9417005105403948050f03180600cbd40e8010146841c014803100a01240140c002c0400b540318a50585c0298170310351b0341d4111058010300c6402c00605070f2142501c4418480f0543c4180200b0203196002081145800702c1002200d403825031003401810f20f8050780242c2c540e4071104011407404034501241d0303281c483c0100c488580c031480c0d0180740e40300108a03418525104036046960481000da030284000075030400c012115081d82260403140d540280f8400200d0340c01140840e034030034020710949081c01da683c00c4d200f0380290401c1c8040001207150104035514448092528054542541d262003285083c0c008a02c1d8104440d550324180c1c421003101100b00850320b903103104502d41c070441c1180c641d50300303003c2180a040c0030190441c526007400b40c0303e5428144480c06c1c004ca040f0580d80e1001c401c1c604014020b260705061310503a61a40104440200ba6 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 675779424 1250 675778174 675778189
    0x903020715020c03011406090c0a02101409010b0f090a2304030225082814211e0c0312010f090f05072705150c060c030910051302 57
    0x41e90329801900c0311000301c6040600b115059410285600c013000240f18540d10340544480e4041c00b5502019034031001240282e11705110f50412400711f60a04442d01021040f4400e002d0103010082c00900402c4d100b1002c0205440c0e0100c041a0040305420014800040e03075000f81300306d5892261100750388106400b56600c0b01c03404540a5015030b0200040075110000c102d051200c034141c010419001c2410001c41c2500e0303600b400100b0514400d80b00510a8480c03020b41c030035400f564440607084207021050503080e11348171003c09d840300c1c036402c0703441c4881c401c0c1802040354100c1d074400d113815480ca0340130140c0f44007942000d15041c001e44410b0103403964121164403401d000c2c0c40a281c401002c0e61805901e1025552103040d03041040341840c1c103005a0a812803040c50180781441502440c2040707004090080003580c0d407000d9480604844401c00c00b81d4203000070032030b49040c10143d032019518401c1c0d0303030f0140c4001c1d20241800d80c85008581a15030180d0300580d045090301c10b00d120110b850ba0005142c5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 675780674 1250 675779424 675779459
    0x30b0114190e06210c0d090f1403031e07050c030c06010602060a020f090607030513140306070521093f040605070b09030f0d0b09090c060a031e0204080a061a060d09030207 75
    0xf03800c0300c1c4230340e0028404040240003a41d181140114075600d050444200c0316031381f401541c501c1c9c44449007c90102409001a1500041410308403525491103210705644c4880a1092074090b00901005c111820304c10700031280010f0381c0c000170901d00308503031b0140259544014030a400700442440f02e04040402c6071088401424000c0c60b40491001041c1014244107014200c4024040d0402403141c440201100b000103091201e60240320765030b10303044840c0c1481880740b281d44940b441041c492400400709502000e0445641110b158000e070000c3c0591942d101c1c0d07004490205c0c20602002000801c03403042c09a101c0700c01010750703080c101c69a885588903040406280c10306503d46c01d240b025820040c1c0440e9124140f03034020301660b0300341804a9014803030404450101074175114917000004041d1540b080c0c1d090303101d50440d0340e143c0d03d04a8a8a401c441c913000c40b080da0a00160302010091300703158070b446131001803504d072070118985070103401814001012019402014030000c1c09228241e00000c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 675781924 1250 675780674 675780683
    0x20010e011803020706030525110f2d150406090203070620160603021b0601140306010b03100b0a020c0307091505030a1101030b0114190e06210c0d09 65
    0x14101516019081c10031342e4200c0d0003010710b0035003045400c2103141366000c144000104c00a0025250340c00c01c49140e0801e185001a520848440c00340302e4000040306200c3c00c66000240c074119003202e40b203d0001e034015020207440d6020305050740004014588041d0020712035040051060b11641c0400e06200c595409080803405081441e0016075000030851880083c0c00c001c8c0500717942a04004c0b51049240c054402096030200b80e01c0845030086440000c2c048000046922641c1c1d609140d8006030313103161159029000b41c4000250840215003664010100d1880b062030340303410403001d8211074100c10309603030440c0700b201d002c5070061701c00380004000f4000400000c01c50b024141c0e1130640148445e404540aa80704600090100300807243d039180b0030300240b902052034221400101d45114181d400141c80f408002100c07111507911703030380a00a0303c000792154800540c0c01c008010302800340c44480c000300141148034905000700408030302e03402103a46038007600300b14544422200711418001c0803107 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 675783174 1250 675781924 675781961
    0x12050a06050f011b11010504090219110304030b01142706030f07060c02040b0d05030d0516030504150f060f0303110f0c130f02070209160f080720010e01 67
    0x642d08000c0c0d00c0300c001400a080081041c01040c0c880895143c0c440c4000d8542d04018101e01e9403a8406e4040b40c0051400c00e0040d9200c0c0152024110340c04d549213010300106140c00c5090300f151301d0200543d011a50400c85201d5070760310301013681a15100381e404840d40141d042000e2201c40c0c3c5465814001c101c0d92071181c01c0585030130010f242c42c0582040703141a0b01da100c0c00f410085260322100c108446581510003140d03880206000c9168419104030040580c0000306215080c100b19034085842a00519901c00e102138040c1c000b5001c443c03040c1d80c0039090904040b0400340c0340360030b03030403403107110f0030703444000034141d65858074204210019003040b40001c094054038108200100082d5042039803181c0500381c42100380001490102040250b0800c054550b000d501849010b58140d581c0c0c550050b100307140501c2c090440e01d241211190b1408041003921003800342440c414684d113407150318152144c4902c001d1100040d540c144c0408040b108664880702c0140b6420310a000e418528240b003082c42c0c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 675784424 1250 675783174 675783179
    0x14040b0409060518160909060e0109032a03120515120c09010911030105011b0b2707060e12160305010c09090209031f33211212050a06 59
    0x16030420101c1d050313101c000d62190403d451a4400f80040c0000c8607102500040c60f800e0625000000d4107243d042548a5407038482804289504201034001c0d0440c10010651034821030702d400e03205904000e40203030000c1c840542d101e2814100342c0c0425000300002210110101c078600014962805c04034682240c0e42202c00a40c0d52410128a01400750401c500140013031031039030f020809540014402c1701e042004142403112110b00da40e03a1300d645c89400208400c0c9a18007015116178400d500144c007841c5810380d00200551090115040c0261400c5a80d00103803007403c030041207100b55019002c0321090180310708544403141c01d40510f00003544244004030b074038502e091000c1d24007511030340080140c3e40100b004ac480360790003041c00706c0c170000c0102c99a05040701c0904800c0041201d0107000d0000c200c800701061340d1110070b50005211112440f860301040c1d4075025010101c2102a09900031141038617511000104030390761030246101d55192540030b4900c200710720002c0d20000c2c0c1b0311504140e6205401e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 675785674 1250 675784424 675784441
    0x11101060f05011d0d1211070f0f09020307020d030519050411040506010921080c031813060b04030f02150307090f0b070201020303070f0e0301061d0a0e030414040b04090605 76
    0xd060812008410401001211001240c0304220310030f0700500d10300e2885104031a4a010301c075140340303247e035070802c03162000e4440300c04407403004c22030003901c070800d511031030016000d100c600860344600c4840d4041c1083c0c0c26003c5055000d000c0140a1108118031042c92000903c810f00c11140700303a00841456200400f42010f210480d040078003a81c0c10050611018400b020514245a00044a000e641c14110040e0308020400d030183d807540d0340240c080001d4110314400c03480e484a00140040300c0c0201c0000c00764140400b00c0312035101d00d215540040c44108042205124041c92003800a00111080200c042c13444c10036500866440010611440060010f58540e111040c00340c003003108200c0c5441e0441c2c00103540c81c003005220703800300200b2501e000c58091103241d52a201b14009402030050503102c001040a202c00e1008010544a0702c50000d14940401d018a90a00c000e04015625117401c00e0403240c00c103a0788071900c0d50000d44a58000c00103032200d20641c84000d009140028a50422018 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 675786924 1250 675785674 675785687
    0x101511280b1008070311060403020901030b040b0c0415140c0601030b0f2d15060d14090601050f092e08100b09010603152d09020708090d02011101060f0501 68
    0x310180c94103401c0510607583c000400c201500e07001a0303a4001030140c180052510300c02d80d04025004120f580000040144620426012b6840b0f030058119556580455494500a500c070b1200e007900c060351031228090040c1103643c03400700f030000024944120a1081458030000383c1c022a0010001810081190780d0854a59080b2580104004400b42c2600500500c004000c605030a800c0101c0d000c03c0d508100d0070303208011000060b005c591184100c00c610310040129600440e5079828000c0018441d0001068081c180d90005140240c0056040180516400c0090612000702c401d00c0c00d0810070300641242090745030301c50105e6100541410b00e91030904440e0b0b5100002d19003000f141c9410350351103420480c1914120301e00081c100340000c0940c07400203d10361218454046507491380c40795110030050100c600310b100d00200034060303036080c41808a1062800c050803200050020319850319043ca29883e0f05401450310500b40e816400101e801c40e240b81e40104803594010200b003000303580090 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 675788174 1250 675786924 675786931
    0x40e070608160201021c110903010c390311030c06040503071403070218090c1504050f01090806071803050d030902040b010309110409020414010608040308101511280b 73
    0x2000b91b040400d0502c03200c455015101ca404c4201d070b143c00440c0c1d2252103140c10b403228100020024400700c01d030900c01501000e4114980b41c0e0502c00c4000841a0142204501011100d0b000e039000c02c840040e1801c95140c2c40c0724041103010301081002060a0700c04024440c02203005201840c1e4942862801c6810b21038007200404064005108100140e580d89506074080107000301b1007402a581d00300118100f002e1744510b20351010300d001407000d41c0040c2201403c1940d070150760000f910b4803120010340e00d9030710358441c100940e4407620001d40503901c2480c203411800d00d4585104001074482d030f2a14241050b044d65800000e0307480101d801585047d009050440c41c0a003020403c02d500c54841c0c1c400a055441d88600558840000c14110740703507a40005a0000242380040d02540c561900511002090b9020b500150880b0b0105007001c02c810000801c81c0c001c008184100c40000c0010360b210044000c9803c121301800d80c040d01c000c20403c000c17440d81d1300c010004140c64400c5107402450184044e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 675789424 1250 675788174 675788177
    0x5250512100c30020c12030402090a0203060607200621360c1503040b090303150f0a031205040513020f071b030f0c0306051f060e040e07060816 63
    0xd1001e00468007081d060001200c100143d59206200c01c0301e8400e02030b1056038042e8040e0f1240004d40b0070f540f010300c0d0103036004502c229401e400c10346428a10303400f82d02080c1c5119901c01c804000340e0000030f040364107c14110781180091800110700304005007903030304548500701820308503441010a000c440e40ba0980d201d40900303900d020403400c881c400340d0b0a150076005c6000c940d440c800443c0c001c5004201084c90544010440441003200101101c0300350070540b82183d81d45861070100e0f00d01000801500d03c80d0090014014a0480410800104e00f075030410b140e803c44540c401c040301241c03000c6c140e82c00540c420f8503103030360b990701e4441448503251050411a080b1403040c09500e451600f41c030102c41c98103810159591080c1e2400c402c40034010200e80c070041071540d02000c1d01b400c01c4610300010701101c0c0650b804004c1c0e5a01c44a506442501d0340700e265400c0460b5140a1003800e010702c07290001848054030000703849180b03807851441d100c1c2c1034100d080811580c0e0200300482555000200708103025 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 675790674 1250 675789424 675789437
    0x504082508040911130603090b1b030c07030c050109030503010f0b040f0312111c17060307052106090a0c15081617040b0402120a05250512100c 63
    0x5071103030301040c0224066451040c1d11105141c02d00540341050b9911008415841d008040e5191000f074010a241081104d0485040300044e030210202c40e0001c07100b10500441506d10754030783c484242e0a48c004031044003404804800300010032824443c07284080d209445156581d41003808144da204200d612a5070300000c00c10080c001000c0030008402200e078840c0070304806240140003078404002c2d55141c1a4248601805256090601403101781e0b100a10b447d0201c0e11104551050f9039001e04554150f01a0300c008000c0210f0308103031100ca10820310004884001c1c1c4e88001b81242400c01c1a682e01c0d00f154000300c088024400321640c0c10009042a40c0109841244ac607405400c09000401d050803a0034004203181096004040e04010101e5200d1051254070f81850100946070081d17030705a000d060300c0d03982c1540c2c3c00e00014071000c2d8181c000d0000c0040d0103840040304c442013203034842882c1542c0c15000000b025101d619028900703440c17401c081e007520990914400c0840d01c4500c40e10080124 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 675791924 1250 675790674 675790747
    0x50d020d3b01090f0f0c0509041a010501110a0b07020115031a06030307050d030c0c08030c0c0610050f0d0f12050403121e0c0201210b01020c04060f0522050408 70
    0x11030300d2109521395440203501d104425903040c0b4407000042d59000c6500102d1200420080100c001656a9000082c91484070641d881304011a40034ac1d40c0780d044c842c2ca45c0560203903004903041800302c55100340a80300204052850755910030741901d59034400c5910310000c1d11800310801c0c000d00659480b4900b60700542c2010348540f6116900d40900181c0c209040d036032044405124800c000b031411040d0481c07007107952820825051402c0b03034040c1110311003500410300400c1100745000c803242c00b1580004c08100c94501ca08041042001904504890003181c548035080050540c44203411684419103545850707030320b141003403002c40d4407103440f60b0108058624042014213003049200d441c62014034184040004610058030141d160f1001441d00d00f1009000780307860f1038941c0000101c240d0070380c00e031108507000c101072000f6201ca5004101500201c18014405800d01c440c0382c180061901e4501d018002c082000e200484034182c03410f0390350b44000a0840096100a10401c402e0341100c0c081581001 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 675793174 1250 675791924 675791933
    0x1c03060506130e070c020405070509030c10120f06081014010b0f0f0a031515020f030c0318030a0f12030b220b01020f0106080a0b090d050d020d3b0109 66
    0x1500d010381aa15001c3e50045801684103040c0d51100550280003080a8200703020302908a8004058031442480352002140c5030341004417200781c6101c3d9a40f610706180010402070006000b50804000c0016079a50001030420020041106c24005011000030031004240c030300c80c4e00400580094220310f00410450301e9620b40c0b001111804002c02030318a840b4409403a003140a0007100c40504041e07190040302007009041d5158142c200b0845070210b40500181d001c8490320ba00803200144004d070802e003d2420040e4072400c10060b50480142a40e42901c12540ca803488884100703000c2e036181540c0c0345842d10b082d405200340001c0400841c0e10004030a9248103201c0d01c440c030404a03070041c4d910740d880008180d008210480044030001c0091245035240c3c0041c2c2d540740500001918014801c00102e2003038040440e10814492079955940d1501c07454030000301c080e41c07180c1440c3c000250b690b81c9008420344000315048141d06080e66014802c0c1c038003060303c65084000c014002803640342401080014 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 675794424 1250 675793174 675793207
    0x1060c0215040302040e1005060f330c0102031f150c020420070b0c0901020703110307030b07050309010606300f0e03131d01050d11031c03060506 64
    0x116811146400c0d00030281d0201d41d0380d80100c0e0b2000350001d040201e040183c0703102040c1415599450f090411071f50341c4640801980d45c0c421a5605c3c0c128404800054281002494150b019031001041c0000c4458032110217403070b80d04c09400c901c1e080e5404000c1c480066410a03601d88000c10002540340c1680c1000c13400442d040c40e0100283c140120010700c10115262078002c56110071400c48213200008118920285c03a81c0079401c111b40c840c1d840c00020340380354903070383c150b610024040c0d005003502402c5560712104401c0c004205035144c4203101001000a9140760040e00c01d00c150369980342c607410b048640c00d0035145660001c005000b011003a086901034202041c0300c0141410501c52110b08138802c2640c0100681c848041c94181041002c060308040040144034402c03010008403180b50b03a0b0750f1a0411650b00742038006070114180300402c403920344030441880540c0521044100307410302100080c030300540c01d07500a9201c0c89071000c50001d0f5405126100c01803a003680d6103480d01d441c1c41024a80f0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 675795674 1250 675794424 675794447
    0x30f11060709150201110a02010606030501090e1c0507020603070905100c080f1b0106060507031b0201020606060d0212090607180e0412050d090303050414013b0618010506090106 78
    0x2241c1c143e0f00003101c2c1d900c00d421694121202c6c03070006540c0c440b1480001d028101d140606400303c1d0402c000000c4c200d0051003220114040e450181181c41500c002070b2020320034500c146810018284158030141c1e4503d00114082c42c42c0ba00c40d40505441e14046c0700d11500e050301303040c060040e0714442d000401d10410480d41da90090383c2103203558490107513020b0741d580340c03214000400358601b141c0440e00582050040907414000c0c1c4810901c0600499440703105000b59000038016040b10003c50f0039803c1a5002e800550049600582000d040950703618181804840c0c015695002c0c005209800d070300031241c0b81e02a401415003845980c10f03e807108a030810060001000728114094070100e9522a00c00d0328000d004049060201380968100200a06402d0b01d042d10000c0e0300d1413042040d40390500c14420f20b00e0000c007c0f6800351025184090711051040a01c000c0c11359010100c07524800c00b40a8940b11300006403549202105c5030040d01d0840703e00a1519004108440c0184441900801b04440 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 675796924 1250 675795674 675795689
    0xc0f06020309010f0b191413050a0605031e030409020304080d0510061b0203151308030c1c090b1b0c010c030e0106050f1323070c03020f0303060d0b040f050307030f11060709 76
    0x1d603540c0110110318540f0b400c23095810b1442c5884240070f41810316401c020103c480c11000c5031040c140c00000d00c0320034107900d00420b0295004001c100f0a0b08116000b45030b0050094a11505000003a4040011f03035804440300e41100d40303003400034042c8d80d4002da040c0c1400d182c1c113240c182c903020090b40840c3d501d00490004900700d0407035000007409444460700c1d02c020760303912910041d100d0511610101d103a411122251040080103144064002c6c402e205a269658102e8002c1c0d00c2e0741c542400406003c20303283d8070151426402c010120290310300f40640c05060904e981c001a00c0340882e44014211039a60304040d10401481a002c801a0f54155041185c027018200001c1c0c21591080c0459454032038031081c0440c3e90300c1400304000302d60042078050b000c0b0f0090b000d60318003111010125441e44030883d14243e1103c5041204130114000745013180d801485100110810009a120b207031840e040098200c000a54a400131994254001e140c4280c070002c8034000c04d0345080580010302040001d004040c0c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 675798174 1250 675796924 675796949
    0x80a090614180f030106080604210801050d150509150606070506061023070317010503030409090c0506121f14010c061503151512030c0f06020309010f0b19 68
    0xc41c0b81d0754070b0381e000310a02c000a008100042c1c1c0c45122030740700c2c034003140c09441c071243c1441a030a0505000d80040d51000c440d6541804580c24402001824900010251044268440c41e02c3c840f180a20405000b840440010306055505200031560044014609402003805003e41400110300044858202500700c480b0243d1010f5030804a5440070340b003031003a40300030508801001c0303011140001e00c03445002c0da0710703580c80c107080807800a20084207202c2c00390558400c10041015803043d9000c008a00d21031450400b05d556284000744a6400511055021540c41d0701440310303d80450b80c221a142107100000c85445242c0010541c101d0401c946480c14802000c1052003008026400305a503e04d19403074401c0c14036180d040c0410090f000c4509045828644007000030030a4412204a0442d074048950080700c07807041c0c0d802c44003010b80c420201c034800b41c503110b03000001c0c0075030003e0b520442024000040c1014000303401c00c299200c00109501030030000030074112150003030101000f070710440b40920 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 675799424 1250 675798174 675798217
    0xe1e06040302011b08070303020d05070e030d08060402040f08070819080a050310090504142a061810030e01060f031104110f1305150a210609020403080a090614 70
    0x100b41c0044800b0000b403100c5e000003000f104041d0564040c002c10803104204110319901c10400741d5092980c0321403a030b80740c4c0c41412003400d418440d0540310b510000280025082607550740400423203400580100302286c04c440f00030b101100e0f00b008002d08401d034441a00354140515141c498441c8540c0003000d082200c0000011036245041c00080021300300c0080800c0140703058203200d01200c14106106900e40181142841010180318205e00210b0348020030f50690a03403001000015400400000a04480040c02c01c456a0302d114111003000074580780400d61002d85400c0c1406c54140e5005205007145404080c4040380d07076086000d044103001e48002038141c110005010301d50013402c030a29580080000d1503192540e072040040129002a141c21480d00d4201c0c0ba40d0040780602c000c00d4001861000003000c0b040c510b15807043d00651507050010342a41c0380c40c00b00e0245e0b846600b054403100f000007019a81258859035080082c4014070b000341a130400501540c43d036100d2500583d175480409101c8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 675800674 1250 675799424 675799457
    0x18162303040c1805040c090b01020712140105162309040c09050301180203070801200a18090c11060411010c0204022206020607050703050306010f021c0e1e0604030201 73
    0x42c8050030411001c250032529030000340b000752000304c80440d030080ca8000002186040303401050448103058000e083c030702d41041c000d900e580302d1000741070b41e00300c01d44601000001d90a04c40c46009034060044404203104010003d4000024580031800c5e00fa55640c1d0000b88401410540c3c1415000b03ea011545104ea010100c91310400c41d00915450f500e0906102d4140c041203107201c42e081e1081d4181d03000c4643d00c411023400c852404d481c4401c0c050030b01c40414403400c00300004009240705820001076030790f00c0d00502090344940c1d400ca0031503c0c0c0d03583d002001880d0440d0310884c48208243c002c0c4042d260640c0c5056030386124540542c103008045200034115555034041c0d40901403000c0340407a411402d00b1f084011001c051084401600036200403410143c4180121920503070140c80311482c0d9100c04004580c001000450401103009001711000400001444e070003290840b50343c0e0110811070b480811035004c1107660300074412045208058001d0320b882d01500c0c100c039024240304200d1a25182c9 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 675801924 1250 675800674 675800693
    0x117090102041a030f0708090a24110c07050603090a20121908130b130504051311091003051c0f0903020901090e0c06070302060a0b06040311100e1816230304 69
    0x1401104829110b40c0340401c440c0500304a0481903c05001e0064490bd07482814815150800c0c0d6540040f1030a00440c02e14800942d04000b03174000315140c00d202c03500da41c0d403880e504031700340c800d12020154940e0652030801e82003103074100884003510b0200b612503d500300c100c10380c0324014420310020410212024174206d1580c000c0000340d071415504c043d009920840c002507402040d1003280303000040f50304a55040e030f030107001c0d41d40000603460b10584c0c0340c10005d006000405035005003541d14000f00010b01c05200004041611000c40c41c4401c01580003d8a80720800c2c141d00300f0050030660800140c0d850000050440d440707014000380f2400711518450512071001c80785a004103001a1170001c269001030300c0d41c400d1000000402c82c1e10400d00401c0300d02d1107103201c051302c080b060f440700c04401c0c80c0103a0303480520541400d0085003007141d080841c0030b803803603030703106a803200b00381c2d42080b42e0030340200180310709000c46181020600400e00d01d4100d044032a04860030080e1404400a01004541348 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 675803174 1250 675801924 675801943
    0xc09040903200304090624030902040b0406180e06070c0f0c030f0b0405070b070c050637020f010c0c14030f030a0203071d0102070b090117090102041a030f070809 71
    0x12102c852048000b101c40e502d0348144203440c00c0c07910b007010000d040b045940381c020740c0c07c40070000c0c000041d00c440c204074054540340f2404e0340c2c444d60f9100d07a4001d82d03586100e000001c086941c00084424007214424013110020038031900d03143c10000800640c154440d41c616034150b4840129070030b090190505407401e080d09c0d0030080c2241403c4550009000704440680d1140e8410000c03940485e403540040303800d90040b54070080c5100c0450406104503d004006001c80e810110007001488034913a020318451400c0d01b9078031146040054140e02c01607814840d280740c44581d00000c1c0301c0c0702d554480007407808161410251440344c003018420140002801110482c14800041e19140e013031101c2244020342c0b0a0380c3d101c003ca0900e40b54240c03a5408245c2d150032581c1d050300030b0195140f40c13200307000443e402000b0302810407180903540401203410b001c0c000c0c01510010300042c0c079103052404c54401d01e10040700000c07503180103004100000301e502410562000941c030304002e0a8542c958818503051869 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 675804424 1250 675803174 675803207
    0x1a0111010605060d150f0b19120f020901020d0201060e06060a050c0a03050306211e0f030726030112110d0807060902010905181b04052805090c09040903 67
    0x203e55a90309013980240345040c4c0c1548480e0142ea40c0c83e00000060703581d80c03140c428050030622100000900184103609030050a003002800c04e042c5d20303000c10880b0300203422141455808115501300d940d04100e8030301c1038038a600081041900303000c0b1407081464004d0089128180000c5c090003850f105000b6a00d00f80d07050400c030754000d45039280241194008652443c050488410414280c05c82001c001c81c0921066000d400d01f01402e18180c02e0303075850301c968100e41c1d10505140440c00c80003007000385481d03401904040b400c1c1c0744800c03411000c91115100200201c2d400d00050001c0f104011640b0010303544038003407501c1100080d0108000500c09100904941c401007540024062642c2069032814400d0303880f544807030740311000c12046241a402d80ca20a00744c450000740c100b84070b0b00703801c90140200000282410303920f800040ba8080701d0059003441e000c840d05010010034061104001400044411a03454500b00040314018020b641089106076200c841c05018140500704200981580 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 675805674 1250 675804424 675804427
    0x2071208120f01050301140c03040627061a0904031205040302190807020f01181202030c0406031407050604030f061e0606050703080f0609041203060f091e1a011101060506 75
    0x1542d0381c541d89409110f554029428880080001003076544128440c80e243c1d003070b05081d40c489460324002443c00f5100001c00000350090844c0358010070310ac400140b4031035007001c61034660000f050480c00704440c0c02a4050340f9864144000650041e03030f030b0030500c4d4108000103079035074450404034030b40304030341942134502404078503080e045c400c4143c020141c02e03001b5078050325200d08500c01100d50102c503140803040d00517111030600c01c25111138143c0c408640000d08590320f010082c000a001c171642944110380c00804186c5c5072902000038401d8500404c002c5038443d041a155465101d42000c0c0d4080c020649692000310003100f8400c03d040c0d410100503084d003002410f442d02c00c0506560b001050070b03804140804001b88030142902c0d0b0082c072504000d4400390b8152910366803c42c400d180310080d40103050301c0c0c0102240e1425104c0307541e002080680c90116901481c018214001204000380c08402c038100040111008285a84000411400c0c6428400003144040f0342e0f00501e069044a54007540 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 675806924 1250 675805674 675805681
    0x40606090806091b0f030a050d0206040506010b0c0706081915260304060509060f160332091206010b03010302040e0643080a05160207120812 62
    0x240040580103031207000040b5001034541441c55681c501c50307520385030880600840f60400d43c0c10305c82d104250104015080340c2d02c03a586951030038103158509a8500c0160720600070001408410003103036004001000c1150300e0160b81000c003c2d1521442c2c020041404420f038045034500d030f01c036005030312440c142d00c1041003002982d01181030806828070829021030cd2941c0c01041c00c2c0d0345030b40301f00007489051008516042c500758041d903450b0040159907512607024002d4003200740f0324400802e441e0040340010b00c0c1c0c00c0d06c6461b000e404010214107001c040400303240000140002c84101d0724400005080403030311050040005200000c01083e59402d034051075000041521800380078506891003158144003220380d001d001c1e0f588603412510301000e1811215207072030341c100300c01240080c002c0a0560b0307620306c010f0b0540400f4284442d017030240001c126a040001c05600c070b04c01e994209003040102000b0b4562030030025550182809170b00207090b0485801d00400802d0401c49031020740c9805020302c58136 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 675808174 1250 675806924 675806927
    0x140613120302011a0a05010504030b0c04030b0103210302030708060910050a0305150705070804090504110402032404051e09031209030d0b0303040e04080904200a030b0319080a0e040606 81
    0x510b032892034000c0569071300c101580345042c030646000c0d503106960fa103040600e1504c07007580d0003202520340d940d80b40c410800030000c10100c10320903000c0c5004981d61050303642c1600d5a2201010249805801c15105000380003085501c400b000c0d07080102141e1401f500d44641040034004d403040d51000ba440f14402c030001007000804a150007900070032005880055a400c5030985051103801c2c0000c044007001c000a1001216692000e50014011b4403080152015540810f04903802034a01c04c450100b03140c40035400300400d600000020f141030380e06000608003001c031802050804000e13801030300f20180014904400c10404c1c1d0ba241142da5007800c00e80c0c2480b115958a0341c0c00308040394210380c20501d0840340d9080000c1150211152000c991b4026566a260110607802c414881c2da4055110300c051600040ca9030a010051040500b50940e90303400744030040c0840b1098844140a13030060111524070b800b59008804103146c002d10000d9031801e802c0c0c4111103294082e85816407217441e00fa000f05086 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 675809424 1250 675808174 675808181
    0x4060e01050f18040e0f01270309030321060608061e06030714070606121b180b060c0a12120b0604210b151203090310020d181a070914061312030201 65
    0x35050503182d60408c00509255500c0d40d0320b5038001501040a40c0804c2000a2040041c001015120401d10709400340c20096807065680c651f201ca400501c0309418800c40c1d242114411101903d035510801e928000700b030100b1010b000081040e402d01032002da003100510000c4044078852035104000b00140780e1035080154214403480b07810364540e04004840b680b95080031082304141c401040d510000c10858200c04009052210700d015044107090010315100701d4100988003c035032060b01c20b41c0e000324007201c0c014181e01c0c0300c0e104010140d00307182400c0104e0711000704940540305c40b44052902ea04148458814490110100a107143c091808200c015041d000d00b9050650301140d1000c52880c044c542107580c0d0043e19955545500840708482042140754000c0005411215001ca5041050301d40d003c0b0408200c3e000b6203a901c02d000640781c03600443c84040c1ea10030902d0030660030281c101901c49002484282078540542c40000c2c0051905141c040c5c1c801c0100484085a8211981854001d019 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 675810674 1250 675809424 675809441
    0x90a140a170705100b12030d050106020d02070302090a0903200601091d1b12030c0f070b0f0a08040c120303090203010b0108063601060504060e01050f18040e0f01 71
    0x160114041d01e40010100c07401210452070300708000b0080e05a003001c441009103c4480420740c4066840c40c1c5a05850b4240080c0040307940d00e001c0040d5075850107601030b081c94031010751101150840d1a0038001641d484140580101415400140345412032074107460301598044040e6070211110420a0030400018415042c0c600d4a8018003400581224445800c4140700c030402e080d8100e040318244030038200c26107a90b03038030000384464802c1c008090140c1c1951300000624801c0e80000152040c540820031102c40101564031907907141440300d507010503260240c1c004c9001048031500c0810140441c420030300e0007408e44050810408441d901d0050028588104201d0095080c242c2caa00f641d1b010704ca60500c2000050f0048142001222100311403110f0790030300da9800521000e50707034903008000100c0760103058162549070b0740c2c500b4400b01a1080c00f8080d01381d410002d0402489110200c8401a50302010a00c8003001007480c80b40000390142040000c8002c1e00d2040c0404110f0000c01500300050 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 675811924 1250 675810674 675810683
    0x7060e071d01030c0902090f060a0e1c0804120602090301050a0b0415081f1803020d120608030706020a030e12130e06090f1b0a090f080303130209090a140a 68
    0x4021842440d44071000400344806480c0c418403c1c02001000595001000c0b198001800400540f03040c40020705980c02c2504c0c050000313030f580320b1010710302d00300b10b121100200030900c0581d5280105a85080e10b034400c5000d4121032041c1e09804008101c000d8058030180ca1005000748510b00c2d000b5041c00042c40d01e010101d10490410f4500011440c002e1801010765180c0c0c40a400360201003000520050440c7c0d502c1700708556105040d40d5240300d101e008100c041e00c2580501003080305000e00419000b401c5034031404c024a0844100107483c800411521410b9001e00b0158451030110410f400070905004480c0790b42c0141ea0801c10302900e010f004040f0501e800401540d043c0e1903034520460000c00f111015000344841b004103031042d0b00382e0300580d48900c10103c1c0781c201c0000707000289030070f0300030656002c040341212000341718139034420903c640a0300c5074000450861500a00c203044150708444003901882180000c5901c006091000f500802c1d0400c80c0b0064030311550521540d200c40180381542e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 675813174 1250 675811924 675811949
    0x60c0a1b15031a010509030d0e0a091103011a030123150d0b0a1a03041509020d060506010f080c120919050f060601021f0b030102071208040b06031f0203060607060e07 73
    0x304550f00617415507052103006801000c0c84400b1180665840c0104011a07030f11160f0700703100240c2c80409004000c100c0b10b09040890320b079403403e0716401e0300b0259a000d50f0300280040c401440440c801c0d40805500d01c111101e00034440241e00c02242e50b21000310f2410b011fa40c0000b480303140c400da20380c0100792400e0f01980c5641c0d520341e564014401a524030041400c1480040022401082038002300c180c10304804040010128810760001c2c80d410280202202c20076112410400e05603040f0030382e102c040b200c80c14080302a10b0480d4120825100c1e001d5404040c2d01a580880c8542c0c0c2c003004a5400c158170070910008a600354100940d4480b095203462009100300800170304194400b02da8407561014800400010b0312007010500060b02102c11610340541d420300c074000c00f184070880f40e0b070a4102e05807140c074003030309207410202e224040080c079503806513100d0880c0f0500c40810001103212640c282000584039162400010410f03c035026014201605242d110001424007040c1641154950000300 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 675814424 1250 675813174 675813221
    0xf0209060d020f16031116150e030709021617040b030a020703030905010c021609060806012304020d060503150412050a09031b061d211920060c0a1b1503 67
    0x706c4204504c2c02542e1417003002340c1900d074509009001d4001031400080c207a401080e150103c3c20100c0e003081c010b03085c01c1c100b048860800d00c44c5c909000740c00c41a40c28801303481c142c248a240d0082c1d02c8040c10440c0e02d2540003403090b050520941c070600d02c196008000b8001c840020800a43c7c9400740d00006c62110f44d10007000540e500180b08100460704032001410300ca0780f0b8007030144180c0450000c2c0d010009007000c041c0746d05580c0e502c0285000100710724002041801d00d170a040c035200c0d222158541c1c41ea450000d000124620100900c55468145015903813030704191400c48101200b94002420030444460700007141074050441001d81d0310030759030200780942054113000c003814641800c607006a05100f0002c10810800355a13403045a503081242c2081c00d4180b50003100d01315504042d1101a003406805203c166400320618449500b01d4201e0b0425030101d60310703515801120002400102101f100410800d008030459009089895005208240c0c2103005400380c00e0300c145913030040d000859907 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 675815674 1250 675814424 675814453
    0x50f030a020a061b1703010f08062809081b010b01140f071113150f14120c090906040303060f0303021f020f0a0507060f0209060d020f160311 62
    0x202059560000d018820042c500385094420300044044c0c540140601c4019601050400300d224801c5c5440c8410036031381e03616129070444d400340c8940101806420a0052040031030951060304010000340d80702c0d106076030312582404014492000020280072010a0b40081090001d0602080308030740c40090016442200044400003c0091b02801011080c0500c1c0c400c0e107400c4003e0b04600d4480e94031010340b24140d030002241c0c0c0300300d80722942c610b40d00c0d10b1410001203142c000c0c003401440c2d0082c0c9441240c0c00c01c02d184040441d04588240145200c00c595110040100b1084600880242911000b4104241c80b2038662004940070f030701013420850001803484d100d5601404681d09940940040c00e0b404022145595040408a004d0b640a00000180d00e00341c0b0020080c41c0d0303080e00d409989500a241c0402521a54013001200034814401145140c98031012102010b1514a005070703a0700c3c0d180150207440c054400d2003e02038401d144c55400305034008850300381400700c580c22030f4102d01d0500007 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 675816924 1250 675815674 675815683
    0x1020304020105071502090405010b03041505090a020f0418030c12230a18090e120405010e010507030207092c0a120315080d032c0622120504050f03 65
    0xe000b80050800c01920f000315070480c4000800d01d21045026140000500005080c0c0b14280c01c08006110004148401c00c2000c412010064a43c0c107070a009500d03009900540b90040100c0c040d0149412007840b040d83d940700d5111100c400380f48854160f04201a04008148e41489401161100b0162200045080c000c114203514a660150b034207940c0f2400d14007484d1142c100c0e014207028090381d8201c214070309040d110050302614000d18001380e41c2107115481031410305021188843e60704104801d01c00c9907800100d207501c61800303080103076072540c807854100d00c0c014207980015141d92030003030742c10084800d242c02000c51440c100300c02a0b04240311038025071940c0c0001d00082010705400c001120725030290300200d51140d08501410003282c1c4d180c4800e0300307083c043c0c071171040000d40c4c400d400c00f0582c510203007105140d108200c8181846180001c00c0341c2d5000040d21402c0d1001080ca001000744005400034071645602c04450303601000302160141c8940c003d40180d9124a86030034a88100c0e040026 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 675818174 1250 675816924 675816931
    0x20c04271b12031836050103050609010606030b09060405180a0804030213020a200717060406050108030304150506040207060c021c0507020a170a1217010b0a1d01110a05010914010203 80
    0x595442817820302c40c802c4040c484000062103003280203200c031190030030503510401c5e000354007900140c100d610b000f0381c90500312465500220181441c005070400349451b0308060550000c07054800107080e8403042c00786040305040150600e885d1081030050400c00000c1c4000e0300c2168402d0f00d121100301a5540301130140d000e0300700c00d8800501500c008440a400ca000d07000b43c494000c1d802c1c0da034003070748030540e1900c2c85000135115402076001d041132004100c45841814018465040903504504284e40d81d0a0703070410309040c0d031141c1c40c1c407107010400944d10360341210402c0f9400036081203081c0200802a4444d00d604400500c02c10300d80f0388a1038002c0c050f0003181c0342d03180e009080e00d144034182240c8a10f9250b2080d030782041441035034420310014222845866008096480d424007015103600054101c8005801c4225120000c0c0420742d030403a0015420018078410030b041540000b100401200c0540320808225400e21804001c44144141940030701d292030300481c0c02081c02545030310394078203030302c8141e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 675819424 1250 675818174 675818189
    0x9031806231801030f0b151b030915130e0a09140c0d0b041a090303040c061d1e031002040e25080a0603050105010303080601020c04271b120318 63
    0x26842e0142c640c0b19501c88005102c200d000020900c0c0014085401c101c117040410b9003801c030000c0c10001e0741c1e90704014100781c0b0f4030440c02146058100404101c2607051681c010700c3d210004151000e2041501c141000a0422002c0802e100e03c0c0c01e1450101a0408080c2518401c1d041816028402c1c008035080c602d00c1d1004d00089075070340c041d542c1e1408100c0700400c20307105600100002d00c10000607501c02401a84188010354403410f01d820300080ca0307109075005006100001d0410909403601c207603000d40341c25044444c2100c160b1a80000380317010410b070301050b900d401100c50b001c0005038107501400545445121103021642d9405a1341010b043d46480601400212905010803510460080303030300000007031011601903541c0e580c03107095810a0300b00300d000c03814080c204082546e0401c003c451141048905001104028001e03200c214600c818410f1000f64030741c0b652044c000710050704181c00803e04441d6a44da940c0b61100151000e013041d0860000d400e5200e03420342d2030a4040e41c0015603400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 675820674 1250 675819424 675819457
    0x2040b071a0f0906011e0b2109060601080105060d020c10051005061314011b032604020f090a1d06010302011103120c0721020109061506120903180623 66
    0x1c084420544e02d01b103c02046409020140c01f00da404403072009458000c0c4444800d06084c0ca0002a0031100c090083c000e81c0a68001020000107a0340701c0802811a50240c5440b913494862880d440081e1007050007202c02072194803510720f4100707056484944981c1303100c803403100103d48540800c5030b54410070885025505011b80b00340308007032218520308842c3e101410803104030300b0310381200040c16400080950100d020343c14440340143c803e03004042044500c0080389400d14151b800620100030703d001c4917019850b4140019900c0249a0100040c0c030040003011101d100f4550006e9501c407800d00040380018600c0001903881507002090b509040c456000025440d55035031580192500400410f40300070b00c130300145000c000710046045140401c254008a48040e42d402c02c070082e00d220385500b2aa0891a2a08000343e503445241c00716410269040071401d185141011280000c1c242c4007c030501e1100b04000070b5164003c030b003da400421003001c85035184410708000140e4050750408640341000c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 675821924 1250 675820674 675820679
    0x151103040b07030605101e111905011113081504080717281d030c040b040f021306030e01060f03031b05061008010f0b0a051302040b071a0f090601 64
    0x703014074099009645280000c1c0040e660400102455035204408012404100c0e48a80c1d410440108480c2000c017400d209541e995060962a603c82c2401118022406280340c61010403600703421144945904000342c540b9200c40803109942e2014a11402125120300541081e44903c8141c1c01072040d50010701040c02c0641640f24110510307105100310803208010409400f110341101004400098144070803404e400507401c000e00001d041d0801035001c0c2910b2410868944c3d40061042d10b8200280c0b00824044040d9020a0240c107451421542c50382c008142650703480440c555140855071595014802c142d5032644490803031b08940145103540719421028408640201480f9810410b6814003c0b07034800d640e100c003400c000341030f500341c601c1c540091020845070707100340502880050082c20803c106101c10001a0401aa900c030304c0d409051401d416502c100c80c9641500d0003803407680d514503928080c51030507800d04072003405062410485400800c4c107240c00c01b69030903c1200c481005109590 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 675823174 1250 675821924 675821933
    0x3191715060f07120305090c0f060315040906020a0c0c0603022107020a0f200415090c110604060f11030f0705030907120b0a050c03090304030221030a0c15110304 71
    0x82c0140031015910400704000d0000078401d070207460400041d50360014440c100320b1415400c1c600400c400c14416010070b0490308003a580d22045030340180502003070b500c40a26881c0414081c1158400182c61140f012460301c640c06e8004165004062003a00000c1d80c40d82c441c24190128040c4134074070505081c00c60700707500002005000d801c0d003114242c01111281c2030f5980c3d450003050100071003101c02030000084c01044450300009803440750012203040c030021028a42034640c80c1300d1445804112901e804010030b0071405564140b1a00a1100c15206a1700d031904010000c0c1008032400d49441d49400c1d610b180101e40f51050b01c0c01103182081c41c004075240d1150850b102d40000d489100b150040d02c6000178560b840815280c2c05c5885221503050070b150110340081110002412651a80000c104100410401100f1501540e0781143c10300c0d003c400452010b1000e5030000000c52141c4000a006c0e407203a07802404102c0326905c0341c802c4c0d17040c8036527240482080e02c61741c004102210b00b09101190009 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 675824424 1250 675823174 675823177
    0x171c0309030c1407030b0702030901080a1a0901090b09150112090c09020403110f060307020a080d0f06180606050405130f0b1807090905100501110705030319171506 72
    0x114041d1406079528010340c1c8420710f0320314203c507450820790b101590800401010b11130050b0301040a001460801103580c0c0040c0c00c40c10014002e010040d601c03d45c0b0038011410010b20b11440703801629841803981c60b2800f040040c0304441446200e803550300001144240c0c0c1da455004501010303500c40a8000340521100b01030107154100716203a041107100410450b1031440a4001980203103c890700715940c160911812003140c252490040a007002004100c40e00040c91604e21980802d149507103440c80c5210030000d00310401030300a21401c00e040041e210748680220300c0240707500d6204002099450b07400781e41070702c100c0c07044e60b8202c400d500d81d048085c2110b51160300600030501001c1030410015000503c1400b4400102130f00180000600580b55840b00c14080904149582008103080420f80d07461050880d210741c0f81045050385210072408014403000009110240449071202c02d01d030450f1100718a140500f60000e940218004511480d03040c01030b01415040350500240c02e50b1700c052280a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 675825674 1250 675824424 675824441
    0x30a0905060c22050a03111f020312060d050303040f0f021305070e01020a0b010b0a020a05030a20010e1009150905030405011812080901020f1204030b060306040510051302060d0204171c03 82
    0x1180c1e1041c0b00c23861085200e9548001c0b05540c05155101d00c017001c10784000c140504442d000c0c22814442c41c4c0010000800c89800c642c101000d1401d40c1741925002240c0c41c1100002504007456440c1c1000580640d00018003e5189480e007050b080010801281d803017405034406421303054000010801600d0090040c0f1003100b80d44181c94110f840b50f11200d1540c1c0c0149003010005100490145600584280a003072030300500009001d41252448125540c0d06c03a88806000d0680d1004690100b098035400c51500c140044001e02a101090400903203a0f00030348a450b0202c2e40e00c5078005081d03103403a02d8440a556400c0c01c02c2800030701507105c10707446420040c101c50562080d0304001b09214010001402d2114000d1f0180355117a040d440e0560340d041c0042c1010b8042c0c1d1001b0140310000b20046014427000c0d05600b00007906a4980d0810504802120b5002c0d400400005249a0200480d0020415958000c2c541d042c06d2030302c001080d030b51300714108500c156880024017030111180700c0e402c550721 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 675826924 1250 675825674 675825679
    0x90604030f0f05160c050102010510120b070903050a0309080c010e21031b06041b060e19090e0109140a0203031e0426161802030a0905060c22050a0311 66
    0x14801c1392001d090315075402c0b00040c0e55254030007508018a60b8240034181d0300a019601c02000c0d24a090390b1b01b14820040900105201c0101000500c40f0344600d146c031004541041c202c80b030900490501030104149802021100c5c0600350009142d075000d03501c00400308a0141182128090b410103501c01040c06882e402d41038081007107802c076440d6400400940c2150344a001d409181828604bc1c40103890289075090304d081114010400141c00c03c0f04082d02410540d1800400f490001420f405150315070003200505103095002d40c00044158011f2449030b1280001291426145048664039807030528003c0d4554410011007071000640150f1283c0c52020441050410391603410201c14024500c114268011009201c0d00c10b00d1804c1141d00040001c0400100b61681460060301300341031030460b400782e1140c00001181c80ca90290b40212149500300040d640d00b41000300c1c10000070b920075100750132401c0b04141b0300d1983d0b4074024580021550010300c103460091942e9152410b407003d505d510355 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 675828174 1250 675826924 675826927
    0x111041d06221a0d0b07020d0201051506030a0b04061d010e010506161406251713080706020a031b11030a08041103072607030f060e160803040509090604030f0f05 71
    0x3c11912030302008106240f145110030712614204a0091030031101540700703411603040c1400d01c21030900405014031080c500b034130700039a039984511015000d4990415010303041440e04e034000a03030703030340c40380012040340804403001500c3c1e41e81300c070301544491003801481d51001003040320a012001048070f0308031091084500045058130150490706010b4101d41c40c210105401c0d03201154074000d540184944c58950400030406c1020101c52011b864004100c0c02d5415000d42c1c03008207204410043d100c040354400000c0d5914100c030034000303000d09018030390865040040360300740e01154050448265071040c42d00040d814552010381c01c07502c1200c0a80103903101c031042c01502c0c00e103840c144007038405000c0d0450a442c400c2504d0802c80e01c11900c0c04549440d542181c041400003880030301d540c0641c6c42e088403003c120b000c80703608441c0c1800003100d8180b9002d09001030016903180c010018004450045039018215501c00032007079200c0704c0403a001000039090b4411260064000c4d00100301e071140900d40346 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 675829424 1250 675828174 675828221
    0x603101505030106140c0d1b081605070e09060406051504020a08071d06191403070e0a12030c021012141b070b04030e01020111041d0622 60
    0x1108400300040356180050000001800a21703002072070110310440f441d0302c4600d801942c103078854031144124404d03010071215200d0004062606c000c1c542186030455101580c2e003080404015440342c40040803078040c01110800203550403102c40b40c1d44115401e1001c3c103c0c990712030380d03000c0c0103010043c9000302d50200c0f440e5001d51500c40e4800780200d5400c0e034032814000d08103030381c01038002e41000203840c515051404000d1400e0315280151b40102422946100000500080a0b203045500403120a100200030080200442d8405041e030701d2448103440da03c2807076031507004100d9100c60316500a0040381d5140e000c0c400500301b07402c200c06503494924207492565124080501a60f2404c860103c4820310801403107000300000c1580026401e91071040d52801455550320012590000c1024080c40123040c01202540d00179007041080c40881c96406503610b484e640d9401d05404541c881340c03000c40035440010b4240c10118052190950303035a0814910840b1128050b002e804600308441896182d44510b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 675830674 1250 675829424 675829439
    0xc0303020d02030112060b090c18211c0215060d020a2615090d1b0206070f0302100e12131701050712090c03030e0316181a090105060310 60
    0x20f180603040d407007513400c10f5250390f080500599003942601881488040700340b00180b5040812102074881c200110200d0f002ca0000084039140b1302c4881c1d070908140030070401000f03540402c6207078010006018900340ca0008140032aa40e104483c1c800c0b005c09000d10105203a460a00310b0b072607000d07100600c04902283c991030740980d129264070050701b41c0864640c0e52400f0709410f1065101c5414142903000d06450041051039407180c02000b54001e0112a20213a808030494102181c43e0980180440d60364800c2403514506602940b20181c005009100c82452803071154010f41e00d4082c0e0b224024814228641001e00c110340c465401e00143c0111440009060082e241428140020007800014689005400601a034020802141210345000f0030040019000048041070b2600341c0341c108601581080443d1501a2094295840ca80c18480010340502029071111114010031024002c0007403503c1850001104801c240341d2003861500180039030f0174110040d5a01c000380d0700c0c5050080d40c1e6901e4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 675831924 1250 675830674 675830677
    0x12706270915020316020a020a0e090a1e02040f09020a06081905010b181005030f040305040815010501110a0206030406020a05071703010504060f050d02090402031213151e0c0303020d02 81
    0xc04000b590340100401407220351035450800c030704642d4009000030511541c00280c0d011414000c0c51320001d000b074086000c04404001e02d448e1a0f50082e40a40d094480d00348000e150402000204e100c0d50504480c541444441e0151012456020f04840142800d100003038807203842c010400402040414102500426980551030003081c0b581400c2c0d543301c03031034000905400920341c14640074851039901990500d0340b04045a6001150841c40d4003591030b1403404503940d05c501e82c00040b40c1e100e482c1c1207444041415607000d040350000d0b00e40801c10401d0092454a50200c85c8010358010307010b10004003c15041d80003440302c841c0c41d04c1c1c924030700106a070f205150360403000c14418141d0004030040c030207400c01e4071400000c1c11241c82c0c20b05401d403501c0005982036200c110000d01400040012404540702009243d83c002c0c00c0c0041a80c2394088000369803056081841668805201070a00114003401580501007848198207124809030001c9002d54500e0303d450001c804040c1d00300308500c0040110b20 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 675833174 1250 675831924 675831953
    0x17070e0d0f150605100e06130905090f3c0d0f020c010302072001030f180302070b07050606010c0c2c090705030d0f09030b0127062709 59
    0x1001c0392204050a0052100d5060600000c8003850480248800e684d0314100d64030780c1580c2d203004e041c00c01c21400840d81c2401404480001202c9105021070301d8411908a144103020540881d04000d2641040075995001070f0903e178108184000305000c00108220b8480390104005142880d0300b4075081c01925082d41511200006803c1100c0c0180c0903a05114406120800346400d505203800c80d19240b1420242c035402040074141104110312130303406038209442195170b1034010802e800d8050045a18208240c6084005001301d62020903c06035007000c2d00d1010b90800014505036507101e00541c1c00f603410078020303940000c0c0d00000095070750b0440000c04040c40341e0705522031204070188001504c508080c02401082e0071500050109440c0000d043d2040783c1e4900c0c2c01c20301400910705c01c1c1c500b074007135810107001c41d01244000b080c40c03030382c00102c9001d4000301a0b003620a52160700c480300c201c40702c501070340c00354010541d0142d000c4005164240b40c01c111004000482880d41c0ea60800c42c0280d85 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 675834424 1250 675833174 675833183
    0x904020f03250903030806100e03070915050603130602030612160603060503060f150d05010f09050d05040f1202181806090f060f09030c030c0c0a050d0317070e0d 71
    0x1503056180002c4074a1100001044508280040f07030308595010b004c400c0300034442c5000310380c0c00c0c12035a2880e00c1041c0020403001c019042d00c10380e80c1c64a00940290201c084080440c41c5450000103003403c010003142c1c4100e5242c5107030f440c40c145030390350301d0065800a0300c1c0517846808200081c5e03403a982403109030310829009181e21003851a0420242c1900c005a0100e0710a130840d100b00802c412042d00d8880e4084800201c2030300410361440081c1c16040e054102410729884c00159071007440c1c542c1c0c050206280140103c0c1c01209408004980c14861409983e40c070503401c1c441000030402000302c806815100034055812407001d0560b4035504501112541404c109134100f01d102620107204841c6c10220303950150107039026501030542d0b20103016202141c1d00791030f900065001001801130301d000d00d03148801d0326131782c1e042c3d180923580c6c90b00be07411618810301c4981000580f45c40e1100900301c80903495140c070710328050b039041c4503088082c0003004202444038032043c200d00c030350b41d2858403048640700303 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 675835674 1250 675834424 675834451
    0x1060320040c0c050307020d021f02061915090c0903141f0506030a020904140313060323040b040f0206040f030b130f1403070c0e01051e060d020904020f03 68
    0x312007004140d4500054001c1409400524071010850102c12520041d4041c0c0705107850b0030482c40400c0e03400c44002da00f94003442d5103012600000394007160f21030180f001c6034542200d64490b81018021039000344444008015085400c121901c4550803804c1e4500da40d091007600503549440e10350401c6c7c030101105c1c00769080201140c001e2410403180351000e04052104100601e42100480c1d075070f0f80c01c5000a482003050000041c100501c1000580900415170241d0361600103041c10119204d90038050080407034100442c426032505195a00100310341c10007100d1203507854a07203c4c800c0e40360380504241c07030301003a15071100c01585440c001040101601c008101c00b03645103040c4000020b90150608070540016121070000c81c5e200c8044280003904600300030071100100e20300b40c1c95441071907402401409481c0000039004401c6480070304841c01550800c00e580300e04103e80228a80b2907a00e80d502002c1404032540c41032195000d0604010080d000514000742480c011009030411a401c082e81904c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 675836924 1250 675835674 675835733
    0x110709050c040e0f10091505131514010906030209010e0d03021606030b10110f01050f060a050105070b0a02090d0c09021e030c0307050a0e10020c01021c02120c010603 73
    0x10803991240c4c8084454009a103a0401c1400701c641c03030801e0312030036402c2c54071a8061f588141c2c5100120000f00700081443d0701450030703082c041000e0f01548e035400395500854140007803020094591f0700e109000580d281d1a606041030802d0340290405443c032810040096002e10a58641026540c0d40034040c0d0001c150b024080e40e841c0c89000020307041101094240104c40d841e0703131111030301055a05803074105010b000d044003040620300902c00c850701d01c0640c01c00090002905000c5902400707004180c411840e26911200151418887c4032002007200d05a40d00041c0300301219409080e42000041510f500f14250340c0f50b100360101c41d60068040d180c0d00080c2014042100419802c602c42036003a01400c520700046e04102e1404000c15140030300100162141d41e10f4403032804226500710041c1610404c03500030704000d64034000b809a407030151203004900c2c0311502d05030b080e4401d07000141c1d00800240e10051060001d03038202c141c1070f0032907640341c1d032010001850010300c6044500523814118071440 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 675838174 1250 675836924 675836939
    0x71e0303110a09080c010203070203120304050115120c0e062d22060906030c03170d020705060a0c08150d0507091b120209010e060c1002030a0c030e010c0c03110709050c04 75
    0x417484038009056610400004005031404541418120041d6010b96102e0b59541004c0c1d0151491304002c600340602c0c088003113036072040c9280c101c48140c0190880d81c0050784400c0580c2d599881980c4659024801441420b0300c2214048410b90b8000700b001c40b84509104800460194402583d0102e20b000301030300c202c0032001c20f81c466103000f0040a0001c0c056541703141c0f00c03040c03902c140b0301014010a204103e00803001007000225055820403079011940c40202d4203000b6221102591211040e6060a003031845082c441c241c0319004c1c901c51000c1034148113061080080c22a112035080b5003a00a201700016003858510490107010404003402c0c11001103170710010a00561014149419031061105c8009039900c10080c03c5c01c1c0d4010f48d0310b10364a0030a842c01e24606103206401e1360440d40008100309004907103401c8082c01d039442ea101403041c12074551603a800c2e24070803640900040e072003403c109c000c2807007070740b41c140700700c0400741a28880f40e00c4101c3d501c180d90080707074140d1017100001001c01502 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 675839424 1250 675838174 675838183
    0x1020c03040317070f03050d06080709020409150803030a0f0b040f0c0809070315050601020c150a090b03040503090f24070c060203031009020903012706050903071e0303110a0908 78
    0x84000380806241100c1582c414010b00c4010b03c5c06420000003007050042904540e0012000d40041e8040304d812036506e8142d840a0340c0503020703030031186060407a00c050542c1d15000f01007d554026001d1403d542e50f0485e48001084141981440a91191400c200e240c07118031603808020703040203022500d00d07215000a0082800a050041e80740d114440c00c0001c20014208807904801e4620301007a41d46801300101d02e4001038000441d8404584d8103900c40440c2e044006180c075440986802c4110344d03170340c20141b000303010459001e45580c00401c0954404c1c50180c110300413110f40103269000ca0b1070035502079aa20204021400103106000070313078a043c000c0720045000100b0840c8029441d514110451840d0103000b84142c44500c0d0300819444c2a43e0b41c01c1d00002e400040a4454441c40c0300c041c424000c82d041e00e0708040d10054685804260f82d040084112a010354000c1e284400a0585051005c403000b174131402030b01010b80e16000981c885083d000200030248a50361554002400c00b43d540b03050 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 675840674 1250 675839424 675839453
    0xb090a090308090d09030320030a02060f0106030908030412050c03040905041b080d0e030f01141b0a09030b1b040311030616170a021918050d020f1e0301020c030403 72
    0x607031100400c0030884da88401e105090b0ba0b807600d00f4900130f940d2122620402182040c01c0405800042080d04203103900081c0a84280c58518030540142d0ba070b510305404440011f4400f41815a08000041c040383d01074202880c0c03420315103841803500a010322440d0864100303030071a02d000fa032100c00f88824401c440843c1060200603e0140800b03605c1c0c0011144d89010b0300e4409018031101951a514594043c0301801c1610b01f400001c1c04881003000395020900390840d040c521310701702d5000c0303640510303024010b88129403101d44803003110900b56124941c01003001040d0104421402c07000b00d0300da0100c0406000214494040b40c070f0ba0340a12800c16080180c01007641800d00d100c0d1038603040b40c0d0303800f81d10500314048080702500181c80315006130000e8820100c009040401080c084e140c03040d801442c2443c2c0c0d004082c000c0302026202d208100c14103400d414042c0d070007600d42801400c5031925100b01006400055005c075201c40704100480d083e41c0099401c0300c803a400109040051001d028203910340c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 675841924 1250 675840674 675840691
    0xb010f06080f0a0f090b135304060504090e0c010207090b130606080603100506130b0105071a09010c110d2601090903121503060f0b090a090308 63
    0x14914042c80c01c942100c100810308910991203e04d203d90f0002240d1101c2a2541c00c01e1402540d440c15210101954401c05011a1030021141c000341c155908071084441009940300d003c03414440140f0644c08000e41801c1c0851600010001c8144c1c6c9a21140107000500042e2a4662980d2400720b5a1048238451207505a550704401c00d085c80c80e80c0c2c049030303420a83d0f05034000002d5a041400c0410715035010f0710505041c0c549808000729080d9041901c09204070000c5084038001810080c484c0140c807000c0da580b40e0462a640e0a445d10020b1640140e240c518040c90910f080c00f10384d8651204140c0b8154210644041c41020b200d5021000e006240c01610b107400d12807580c00c2c0341540d069450041c00ca41c134080081c40d2504070229031040361000c4070380005926100155031190100c0005050007241140403800c4103898680501481c0611b00821440b100e40703090040c9107031038180150031464501c100349541e030440001c6a41d6041c101a01170007000c240000d070390320140b8000c0e00301c1c0b10203082e208 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 675843174 1250 675841924 675841937
    0x30303060f1707180f050f09160303020c010c240b040605030a0506040215040f081f0c020a0311010b03010903022a130209010201020702090405010c090608072f03070b010f06 76
    0x40d51400001215002c542c005540c00851000d00004c03500100507404a101c80541840f003441140e1100005040c081d4a9540c00e03a040d115000c0c6680c1c0c820b113918803001700580c01840d40c81d126503020300f00804040e40100d00b1002080041600c90212100c41a0031604c1541d8a01554030107003030034401c03c0054501900100313080c005a803281980c907040280300034031418500c042141c0b543c0c56602500c0042000f009028150340c0c42e103560a4464010700103030101510307d10ba84441c002010b000b03201c203ea0864001d4100c03408240c03021900e5039040800c0d0b00c503964030b03041071480d552000d04c51301c0c000074002d034058800a02600c2d54540c000800b080e050001d1004280081501da803141c081c4100403010210040e52009040010b0780607001320240a54010a003804110070b08c030b010340055000514a0307030307034110158580300203a800d840184c1d68640081e0340030030b1491051402c5801000c1038079007101d601e860389500910040c0b4503031102d9002c60310658110010080a01100e200c0b9020740503a04010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 675844424 1250 675843174 675843209
    0x50d0c080f092134150b0a06080a090b070509030f01050708070507030c0f0b0609060a08030306010c060618060f09020f0a0e01170103081b0c06031303090f030303060f 73
    0x20a6410b000d211040e420b45000813000706041c000b00e4901c00010380541e4240444034070120143c1c1d442072190301510a440070310b0311107000340510321a044101078010840390003142030003402c540d80a80104014a0644c2e81e240160100d01d2140059100341502e0b502e00d81d6034160802030500b481c3e5a18158546a8184014400542d0700074103156031211a83c5081c0303403501d5050800315005038041c2000b4141b615111020320921090000282c45444299031024481d250001480003210480c030424096410038804282290710600750341018074013a000129015803105000b19060200072a1906a05e0341ca500030000078040c074101074010714800f00b085090100c009004406071145c00400800c10be04140c00c3c1a41d40e01a6070105000220301086129642e100c1ca040c01e4a0740c804d002d0140d00d41c415030341c1d010440a00050811102c000a8040c50031502e9856052100000410303084050000c040e102007002c4154040708402903000355804242c1e50300d803c21b540740c1c5082c03c2d048060b01d40001f0000c0b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 675845674 1250 675844424 675844453
    0x1c030b06091f02030f0301060f0e0102161a07060f0c0801051c0b0403111902010e0a1805090a02030f030915070b18030c030a03060f0909120c0201050d0c080f09 70
    0x40d415045681548000d1900030070407815440317044805800004084004100540c1c0301c0c1e4107494220584c0c0f58007920ba0301c08401665240002c5881400341c00000314113000b8204e910455804160948601d10705002c01aa60182a95902003240100300c1d80c40032125000f6a0040c015801080f082d584201001030282d6946607210031081d01404241c0140c0224040602c151081c3da40711074160b0996202c0040038450700c00c0f4001440b010fa0000b00d189284600d41c0ca001c00600e82150348240c0d213449030214918107080a07100041c03c070304503400748150030005603c040c4028030a14102001440d562102e690400c038015691031044c0010341c0381444408005180c1180868214500e01c0b45801c4140145901074614466216130440070302012a000e28004d030150013147c06d848144c0a12400d060319109814211a0010310140c00103c3d0010036030440c6001314030444e0380c0780c018580545007003200600c41083e142c1c110031400c00079081004001e19484203009882d00200c0c50005410000c00d8401c1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 675846924 1250 675845674 675845689
    0x6090a050615160f0b07030e070b040513020c0a081b070b0a11011119030b10020c010c03170c190c11120304050d03051e040803040b0901030e1c030b0609 67
    0x10000d60b1214001440c220b0040001d051010855011400c4200381609140c00a000013003600c80c003000ca42066502c401041020902c0303c02c0d2170124508904041ca818208584075843c0d42d64403003104d80c200120500c0290602040b8030590043d880300e6911404290b0102504111048906064004d690140402d83d904000c0707681800180c540b104400302c001c0b00041c01400c280819010146000606400a0680c0d1174207030401d003895242001110501c800b4800000c05003018503005801c41c0d0341c841100d60017440c102c20706074064034004005801c0656510403c00055455014a03900403441355946142d020221107603031210314086040551540e640b42e1500c3d1840d000c148620fa1070300d1111502c18080060768003c090060409400c41000d04015003160300c10011003070740401a0318880e070034148840441e811034509000031440c05142a80201c81c81c1c2000308001e04060300c500003800003000800c820050a801044603040da0008980c024040756008d0703001c1400b901080c4940d1950799211032 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 675848174 1250 675846924 675846949
    0x50a060c0b1506191d030606180c0415020304360b03120708070308010f03120305070c050d0e040501061106040204180c031a0109020c0606280e06090a0506 68
    0x40d03200790030460b880001d241e6000341100709141c00d060b904544111a840000c2d041c02c00300ca81542454080b0200c140342d00c81c101129100d80020020301d00c0d204c1030f110301940c241e005000044860034107854036190254035044024000050740085030074480c0f001031824454400b6840c15000000c01039035884084032029090240100b6030b598040318a0300d031001c0c000c04c2108034000c3e242c1562401d181c0391070384c035942203444298000383d41a00041009031100f1140801e9030341010f52009070303041d805000c40c081c142c0200000204010702c0c042c0d500040040004030a030286d0303034940c204180240d00902049441c140e201500700100a444c4950009011503101d8016806442c041840c0d90410f585400403980705600078968031f52000d00101b801440c418810040e0401c103e5070302030340d9942205100364080c0713045030201a0480800f00c1d0007031401840a23031008101c040c0c40382d81c42c0010704c850141712a00d03500107401c822545003000034600e00900380b40c0e404142c3d0801007049041c4000840d00e80da040d107 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 675849424 1250 675848174 675848191
    0x20041116060906020f0d020c010f1e09050111120a0b151e040b04030c030605090606100309020f060334090e0411030105040309050108161d0103020c0f010501050a060c0b 74
    0x54090106104042c2c040326034010171031a42a54920004014000a6002d054042c480c0d51030580c045a00948a0040740a02c180e6020040c1002c3c175100e449070010f045030002103c484d941da01801002840f42c10280c407007411a03107808130483c90309141840940d0700d40d43d81d40c4c0c425209005c400ba42012840d080c2c4540c5410589214070300e40780f801e5403042910035508415060500031400004006200180314281d80c810101841161202e80c010385d5039860035960103078040812404000482c7c840d5100030001d40c00201180341c030b903a406011640c95401a9201312881c402807040c1000480b1021007242c0f55405c200c4540242002c0385002045003075540034458016840d500801d00380300d6151800c0303030b054034000e008000700d00782403501814030000d52081ca40400c17682d00005549055141d01040f080d4995102c0d1420345043c40c3da407814401500c4409c9040c103500340140c1c0400303107003003002ca2101c2d4a0345000003441d505020030050101030390341c4000108210201d002c1c1c0099160342d001600718040 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 675850674 1250 675849424 675849431
    0x6010f0c0b070c03030b0a14030f0a0f12051c0e2401170708010c0c0b010e06030a110d0b090a110a06093b040b06041a0d0804032004111606 61
    0x103880c0440c061b010310120140c1c40f004200c40806c0c4941082c1c08485a040220308664280301480410740d1030346517416024048986403640030021507828810340e0f801240c0c034540f40e0304d0100450803680e4800c0b44e10400030811562060b120049140c200840c0703040c0a184401481005580389111540782c90500680102085036a1043d014003410400301c00a8200d0500901074040000c0700103000040c3d02405441555410000284540c00c030004580140c0000e40548281c070401d440d600700741d160110440d80c0184410804d40045202500d62502802c602006001821040d0074038403000441300c0c00d444d00c9800040020495507070408101c408480d00701512961314421980d800210840c0d110341c0d03110740c201c0e04144404d50159201020300c610310404a8084d40c0e25244103000c22a80b86562004080a05604400c51441d062040c0d0340161701c10320625251030748030b984583d8400810088404408803010b0a04a14a000d006101a1000032900d90b400c15100c1c07002c1420800c1402d1010f000d2958 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 675851924 1250 675850674 675850697
    0x10608120d0905010e1002030405060c030103050a0f0219090b040b0f01020a03080c0909090d12020c03070318080d02150f04020a030813080105070e03101b05210a020306010f0c0b07 79
    0x102908080b43c942c0442098a251b0000b500845005e9482250100c5950003041e0009a00c400d981307043d44d06072600f09000f0946180326580d4007130b641403d03e20603a03100c00030051415400440c801010082c02e1041c0010841000b10b001788019a000442070030310a07540c41d40183e0b042d917400540c8000b21501480d100710a9151000143d0052050302561900082a0030801003103030381c002150102c805d10395440d0050090159943c4080b80101180000140c004004074000701c0e02c10100201c525030040c0714170300e845654004542c41e0040f170900200160300011070b801c1c124224408803d900c1201ca020001643c41c040c6e00140d000700c40b80c000100407807804a01c04011400501e00e00340a880c3c000020811800c1801c0003620019203901c666120307110b0300314070f42c0000b0034500441c1a0704035540000000e41c203400b201a207258005000072a000300e40c4024140040320504003450144030704c040010380c2ca09241c800104081e103c84c000005001c40c009a90000440c4d018944d64080e41e186030600340d141 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 675853174 1250 675851924 675851933
    0x22202090414012c0a1a0d0f05060a0605030303070c1a04030809121201090504030c120c032d08060406080f06180d020c010c030e0d0b09010608120d09 66
    0xc11000326081458034100390b1039100c000c4400c5041e11100800c44000030303882415240c5125071041e002800300100000b203070b02020340e80c111200640c0c82503030b8120710008400c0400c3c1c4044030940c05681c0c45000f04646404e0050034002d1036005400e4807030500c001810000030079664400a01180104159420b140042c8507103545140d81545803074480c02c04a050a0400405010040c2c5440c0c895019060441900e400018211400c000301c2545881a07a0710385484540180070040043c0e0501c80d800c110080041c0c0d140f141031014182d1901c0341513452040b4100200946081c0b0743c404e1090b1201e0040030f000e0008801d0f281c144100a02c8c2c1b0b408030f903036003a01090140c00309134003480039807003124041d24502d4008039000c3d1013150481c40303416025800c0300301c65a0700e0740b803410880c001da084098100c04e254811800003042c18060b0030f069010300c0300c0d040840c000080e441003d0300c2d0003140b003081c000104402e0007260002c2407804014060f41d00a05400700282c402c0400c0420101e42d81c501000801 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 675854424 1250 675853174 675853177
    0x30b011a04150507021e12030901020c120f060a020d06050d0f26070807021003020909012108190e0609010210021c02040e0a0609090b06100908120c060f0103022202 72
    0x11503002d40805c403151006c030541303586c090078408800d200300c080070000b2001c00d40010907609400d005a0041460809000034031241c060010240c01150145003841c01081d001000701d60700486494100581e282c1c0c5a5550204461164126600c10080e8004401c04944542d6914103002d0b004480720400000c48804e01d401326420740c1c40c270422000041801018044228050160180281d03a079661084819008908a04c501e02000d40c0c0080c00c2001880a50140c00307240a4000070001c140100a0040e06e9408030341d0041c505003048549056115403406074054600f0703046d03c0d03060383d2940c20606814001b0352220b0034601c004580546c04035410100c541c013211404140f4201d20300c115038954861140ca070308210111022800b150a0203000a178000040c07049110f103a0b00f000c0120b5080d25142c0400405480c10010401001100640450300c0e40d070900103e0741000007420040e070b03540307100444613040100003000c101104003140c00410151700ca12025114480c10b107908509000030b450b003118000d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 675855674 1250 675854424 675854437
    0x7110a0c1401021504081902030c071518081c05040e010303030209150f04090504051c0e03010c1419170103061406030f0d051305090907030b011a041505 67
    0x18040500c0041c1c0034000c0380490710140800c0e401d86441c0c4511036140e84030f0700801c0d10002e04070a030802c0b400ea0425506100000c2000851050b2460301d02c20100d4180b03400d403076410044d420880710012610703607074008524140541c2c108103483c103002d107084105030305c03442c04130a00407440d181c50500f50085886501114094001000e0090095840e824018002d401002c0414014041c1440042c40509520f00703a49141120584079031500d402c2c1010100a050301070030881d81c0f4498220030682400075010040c3c2800d080d540c8270441500365100701030a50381030003600010b2100c1980000b548405641c00c54940c09051182c0c2074448994550031101000850304043d1148000e00001c8200422174001c4c001d41c11054082180c1034441d0f0701056101c2510491200c502c0d07000881c0d5420442c0110050301c10706e040c0405440000d50b03103802040584c0c008488200051f040a0700030b00030001a4440d45024200c50504160001503161180d2a513104074051240c000c0304102c1c4954a1501c1402102e81 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 675856924 1250 675855674 675855683
    0x52406040305340b0724020d05070e0609030c0d1a0a060510050405180916080a12030b01090611190807020f011404090218091f0e010e07110a 62
    0x9a5905142d226501d03900d06002d0f000010306242d0314810341407070b80c071412800c0d100c2e403074443c80c030f00364555640c52029521030b1084e404245070020400c20f07036402440a02001300034144040360b01d18003007000411080011304030910501040c40682c1d0b268400084a0050400644044000d0310b0141080407154122241c407484940d1280d041084c0c1542c2a00280e00b1500c082d1105100c002c031480c416201c42c01a80601a007120300e0708a251f4080640c080aa07810102c004180ea41c880c9481d0341820b0410855000100290b000300e00901c200800805030200c1480c1528080082d41e0312000000d2998501d0301c14003041040e1110b07031801d8500d007407011400c0c3d5505030f0901c1e1111400c1c0c0c548003c25812111059200c0c80f01421513500c6540502001203204a00e9421a8640340c200752509009401c00000e807040742e900681d01401d00d45500c44100d000701c0da99640410040404d920340355800d40b0b01c1c0c02118848542600401030507054008594000240b414038141040705216054604450120041c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 675858174 1250 675856924 675856933
    0x20405010f0e070815041503021002210a09060507030e03010c11060a060605251a041e1a070c0507030803010807050901180b033c01052406040305 64
    0x34003465042681d002c881c40302062000035901c94006881850f4111858405186015001811442e099000356007058901d03905031103141e203d4000c113802020030747c192805030f4401948007050f01643c8600a01c0d40c403540d00640c0ca00094134000034094000c80c46004248000810b5281c105402008101c0c40490b025001b04185020041c00411100402405908a019080102d82840c0301401500152250382d26200e10b04a41034000c10030b0003400c1d0055079861440a00b010001800f00c4010140c40340000d480740d15035017460704050110b8143d011001008400381c0981d180081c100c001c0720000313455802281ca0803640e6000f0140d80100003000010401d01560304084200840d8401550580d0800c604440c199600c0b101840043c035030a003d072a000711000b06c0541141c000c55001840d503500081d094903903848017140203207245421090040d5010301c450f0710b0075000c41c020411200610103240001d01250820405542075900e0700030120b000150054905c10700c0742c450b04119401140c0c000d00301e4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 675859424 1250 675858174 675858179
    0x41d1504060b060721030905061302030712200a08150a0c02070602060a0213051c110907080f040501110a080a0b01020a1703061507060902012003120402060702040501 73
    0x6504011281141c90368503200340c8015074201101903659040e4441e98800c0c415295410b400e4403012403144180801d5140c00041e0009001407048901900c02005d0300d01c041c803414410076003014840d800040500b0380c1001c0c54030120740702d98000c07041810710aa00044c40f4180001240ba442002e402605051203440d21120250b41e41210481c0318030b112607402c10040801c0b41080740c4810581c4034000040e401351000c9014100294000c04810039a031501003103013651000820040aa0410306070025078181e50210103000c4c80c8a001c2e00040c0c0102c600545a141018029080d15001307805005485034000c0002c003004000d40c003101440c7d400310f007407d4656000843c014007040f021207020b6125402c10454907220b50000034100010755010340700c1c554555080e2910030315504014031441d8040d01c881c07920601615010020000710303014031030202d4680c0e40d900000d8a00c4020224640441c650003155445c110703800f00030b4455507030341150011100c0c1c455000045190044c4807000c2c0d031040c41c04000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 675860674 1250 675859424 675859453
    0x50c010f05010803030a0f0c0e0f04020405180103120201020f0316020109021c021201141f0f03030c0b0708010b0a0e0a051804031e050a0806030f060a020901020723041d 74
    0x2035441b507064605d05000c07904424402c0000e49904c580c0c0500448c16031341c0d02c3d100b14604080704550b00b800c0075000508050341d4a000540c404441c83c281c3c45a41000c03801031060107404904442e00e5021030000354a0803079402080e030003c1c0b0000b0310990384004c82102c1d00110501c04c0d041030900c10303002848032104000542481a510303014480881c46000884180009210103000322007400c00300c02503400c00d43d9104120040d04403160386000d0003103c00c021001c6000f19490341c030310010f1400703680c1e020b840070000e162416205202900e08418400050300400c110440e11381111a1001545402c4042c66410300100b09481c4490300410345c030942d070700350900c010a2840303240e81c8030310300070f03a60451412440300c9528001c1000c240d0040018604000420200340144400c1d6003201c4050200c0301c03c4295410a80e080c0102070302d4040d602d50300022115034079030b4100548070181040e003600c90710000342611a00d090310526100741e030146031a80e00d20200b5024030380991500482107401c0c0d400746501942d8 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 675861924 1250 675860674 675860677
    0x1050f0c0d0513051e09130b0c180108090604060c03060f0810060e101e0b0c1e070807150e0a1401020d140313170412020f090412050c010f05010803 65
    0x3c1400ca03001c0c028001214640907500b8583d02c0a480d88801c0d0800501042c0304a04500801002c0c0b120100c2000c0000500088091480f035500411516241d410700c500c02034a4641c0603c0c2c96041000084c01c0c01181c0d0004180103800c20b611910010391000c003488180d01400c529800680c0c40c0c1c04101c0000388540010941d84e861320001e20303081150503142e042c2a00104000c0d01d024031507983c00f40060042e407800151702d15000461003503840c034260b6252840e0b04658007100c1945000e1701302c2c0c032114224030695041075480190640190440718102030601b035545d4a244500304a55060a0080300b046016841000041201401065685886403d000d01c000a40703da181e00600c21840c02101346841051680c1d41007107640981803a58441c2061014201d0003c1016075804004500c141c002c860404024001090060090413801c005401080b512091500c51240114002800c010000e5110322010000652a0401985030b00c10b01160f6401040202045842c942c0751000103e01e4000000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 675863174 1250 675861924 675861937
    0x120d08070e1e04060801021e21071e09050f0409020d0b041b080106060507020f011215030b090f1507020c0405100e10030503160611030a0912091401050f0c0d05 70
    0x30f0741030204954940426082344210f0f5080035519454103018500c45101c4401800341c9030100644603441901d03074070540010315094a110002c11962507185607159540c50903034480454500302903a1051500010a5458044070302040c8140d580c1c0b1054021551101280005160805e40142840c0382074507180e0682441c06105210340d468800300003071000414006e6400f134500325a221401c0080075401e2204072409074072a14140907280c412400352070b03118850403510400329290f40c0190340c558240707140c1c8107001801920080d041020f00981c0000300290488469004200d60040f83c2d8a01310102c0c205629182c8103175026040005101800d50711160310b00541d00f0034209602c0b2501c8141c3e1100040c805480024010340050001e901160400680004154002e04000c00e050307001c03006080050303004403035041e9241e96030200c040a2040202902021078200c5c2070002c1902c1c20701054114030064103a211f410400002002c00020001e201680c1d034000790402100c0c00094480c402404580010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 675864424 1250 675863174 675863179
    0x50607080f0f01050612150915040605030a080313080c150a06061e2a060204031109010b1204080c0604030914030706081911040f06030b120d08070e1e 66
    0x8080342991142c031900754100d07840200842d1400044040c001045003005100d403001c80105038522980303403200d20070f252050b10100c51844070101035400704400c84106030010380c0264807104c4110001030710700d001c803904002005850403688070030f403801401c50b01c07518000090b5400b030810b061004130000101345016070221a42800390540f90401240c07240c1d5410095181d141c02d004038642e02c107010f0180f0300750482c40010000c0c0f80018414054841c10040141203071056400641001071084040c00c00c1c040e610200c0d10101d46500d1300f40340302c0c518065805402d540801c1e0790041010000580c04540080f1214802e849051401d814081e040c0101c9100c3c00d40c141e00201456003042c60041003242c10345e10140c9408800e0f444501010151843d603c501c5801c031655841102034000b90000a04020a5018203005d0300605100c001001d031030540314100d01442186c1c0007ca246076000c910010300c508103140c40646655101c108a601500c80d16510790082c22003141880000d0004500c0041890b00303 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 675865674 1250 675864424 675864451
    0xb060304020f0f131e021c0b01020111160c090605010207090c020c040f1406220e03090901030804060f03062301090e0c09150705071a0d1a030c01020a0209012105060708 74
    0x502881c5c03000e910443c002e2042c0001c003480d62144c02c1e260b550080c01841c01c103100010710a02d94049000440d4011090503803007040740c11482c81044001c2c001030340500091501800400d14200010356942058000c45005640358403009248900c00c020211201000900c140036550000d42c100b8010400191883c01000e80310700010b07018203200c01506004c00c0d0300c512450000b1540d140107402800b0840381542c0c280010090024207580c0c0b14042030185024102c05680c1e213190003030140101088001d100300f070605040d41048000111241c2e0b5484130400c64050540400c20350049440c05d6150700101c40034034000b001d00c0b00c07601a901c06820201810b58248081d128410195403503405100c4006286a00c0901c060101c2c4030a0780103084100f0440c41c00c031f400c0c04408507030101a1851040d0344510760150017401031440c0380400011981c034000780042c3c1042c108039004100c203d803050084074068030003a10722011482c0408040035880360480c099906a00340309100800c0c2c0340c000d8802c0000d0300784 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 675866924 1250 675865674 675865721
    0xf050103050703090b0c07110603040b0f07020601061d1930020307050609060f040303030506091312050c030904020f0a18060801030605130b1602100b060304020f0f13 73
    0x130302c1340d10140b9800c11503000440d41c441a5004030365110420072900d00032164170050309600e070580914003d61185213414454503000d41703c408070f140020810000c646c00400104001504001d10913225145a001000140542000700b130013510703038a0354030094034528240001d841c075161541b520404d000c855020485070303003284440162440e00300081e5040d000010704100c039283c170f0801000300d240007504990401c284442c036003103a07800561007500426158010045107207491030301c5036803007075848c0d0030142c904405444440602d4414010742041c13040005103e003441c0130410540d440d40000410070340d03940e96551075240701038119141c0c02d1b0202d032906581e26911f58a00c2081c1065031801c2d03031091040d07803950b11244080c00010b000020440c1207644510302241c01d4404c2184940074210952000200d18000285440460b18582d92411320748440c462403603488000f00d0750411f8040742c081a032240858005030080c096000c002c4d5020360306141d10049101a034020341d80e00240262600003080 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 675868174 1250 675866924 675866927
    0x12220e1303020c0d11060a02160b0901020c01030911010309170f040f08010c02030d0207061103090d0206060604050f010e3c0301020304080403030c0f0206030c070606171e0c03070f0501030507 84
    0x1088540102012008040c0280130300b01381000d00390302e443c1c601c11a292101c5025501100000070b82140e00c14480c008bc2d07419242d6010006002e10500c20311b820021617503952038580e80c80d80720200340f60405031100116014401808682480038018415140d92180138040c484204c0d4000d200f080358582420700009001c0906200b20400e404440c0c01440c90005030403002d4001354000c0d0001c2301d400d0780e18081620a00410f02c0a188140d880000038032400348032120103890040000e00342c0384a10810002407040780c54540c040d4148410a007400144080340b1130002c0c00e40c0c0d442c0c009207a4060498801024045c1900c00360143d0242100c809000702a440008d0500b46c6c8011580504000c07001c01c401c01c0001d108900c145141c0b402500d8039403185a00303500264590380151540040036001040200500101d881928000d1503411001e00503420508202d944507401c00304071120344402081c1c01d6800402c14004902c2d10f200040542d90920780750081e50012401034007550340001d08c2c00d8002100b55 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 675869424 1250 675868174 675868189
    0x24060304020328061d0624060a0c0602160c090621020f09010609051305090a111801030804060f081b1803070b120912220e1303020c 58
    0x116000b40151078000f95042c4100c2c0d0345070401041d1001c0c00800d000301e1000c074000f481000c0d11601c4040070b214000c2000103e4524040e4080e1140d080c09804c46080f4200880742400c511805406540742512445540d409171490b03000f908014007010300004824540c4140000e2031808680f15101d810b2246807240b246200f11082401030500b2100d6412018600340c3d820001380c458144020003c6403905004808500440400c2c1d11401c081021001c01740310783c0c034004403181681100754104000750720305904400d5960701c030f019001c1d140803052016180141c031038444400701448244900d046a50750307413402d441079500030b2180c2d10000f5912901c141c1c0780c0c0c0c07003100c15a010381e0020b8403040098a0b0f43c0140d46041e448600c0d03002950803501035001007502c3c1800107100900c0401002c544494010051100c4004004c0c080c2070700b40c001d180941a6444140d040d105e102e528015054100b017040c99004091140380e0f0041d08e42da0034014100074800c42d50681040ea65071003942944d002d401c00f0717424030440 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 675870674 1250 675869424 675869431
    0x9010206090313120c05030a0b0a05090d090e06060c0a0b01052e0f03200c0d050702010c08070f06020304050109030306081c080411100c06050c03070504050621240603 73
    0x1100d01c00380200300c10404c40c006500705900418421003d140e681c0c000170b160200e096003c86a103407040d0200003120700b0702e124041c0e00ca44c401c000b404c2d60035004a4000d184030104c0c01080703c01c540450204685880d507400b91015603050604640d0b0102050a05680019003403142c284204680c12006000592007111625540e031241c0303400e000403500d0308090305d2801e0382900321800c00d9611000401300c2194001170005042e1502407007a40e58907071039486402e000c0e035142c6a02c14840708200440040c1d81c826035a521441d041805e09031100c006280650704241c800b040500f007c0d00110078002405010340c040c1380682d1090b14204003140e80d6221103512030382c184400701103000100751194842c3e4000c04c840d9600610600e2a045159128000110008030a5100c0301c002094400180708110151162075005519585041e06625000c94000e11038405d900605004180101d410f800da01100b20000803a0400e4090903d8136142c505950035200700010f00c40c801420000841040704d0408c5401c8131300 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 675871924 1250 675870674 675870697
    0x90e03030f0c0414100c020a0f080f01020f120405010e01022b0504021f023a0206132a090e100207021309230604060507020c1315050a0902090102060903 67
    0x42c861381c40703401c110700fa001c070001090074059440400001a921500c075030700035144692900c4070715400c02080f240f60a20740044420283c0c410400350080c00d0041c41030746c500c80100c541c2c030000c0c4d40c0d4a1800c0e0b4050103d0664101c5150b00205a511502c0c08480f5402d400344804015000404202d106990664a01351406500400110011814081c0c1403078050445001801111600c0aa4601d0742010244260710b083c0c11118030105240303a820900c80b0113110a081d44010911420a2002600600380468006003461120a040390b513000d0700c500604031410311028881050f941c3d8560501c080c0102026854080c0135120840004100603c00d840c015500039214010800350b400101c0c00402e010182602d1030101c035071101400242c401304c07040c107811031180030341031908240c0307051015500081d0141b401d45d00188402c600d00e46a400f0b0b0146c0c4001e20440218440904110121900420790070054024103032150100c1c01030550b0300288042003007a4202d80c501d9841c0b103002a268000ca013031341007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 675873174 1250 675871924 675871949
    0xb070809010305091b01050a0509180105151e07020d1e11030307030815060412030e090a0c020a020409110a08030909010f0303080103060509010612120306060e0102071e090e03030f0c04 81
    0x3045e075220308091300c0c0c102ca1508000c0d02e409003060000c0e00c00209803240a11921070701c40140100c1c180080101d020040b0b521740e2900749044ac550f11446a0f5021880507140200450300c5010340d0345100d002030200e80c000030f141001d03410b03408002045941105080e40e01e10111510914541400401c68604942558450006c0d44882992050704605078030310710750060f0244808520402214190744000303100340c885e280c2581d640d0091003c0020300a1000100606e414180c1c944d41ea00402e40c04100c0d80d0407600040c1c424003500c0c0108080901c941c150342c0221107070002007181400000105213131002100c00540a0703990b4401e9551404084c00000d0001e90407900400000d44150030440c0c1003600c0100100d01c0b04d480303a24040705d50450940a071390000e48641d1f00c041413901403203450040d1609140090320030b011000040c1d07803041148641c0b4240489441400c8858407541c0c110b001514003e84203010418030202c0a03a0389820940b002e5492903075071804160750107081400c0710300701c030075000f410b0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 675874424 1250 675873174 675873223
    0xb090708100b0306030a0506240a050612060a030b161d030309102a111005090f18040506041a061012020d0501150212270303040b07080901030509 64
    0x3080ba8001820b143d802d0300c00c0c040c0c202c001602c140b00407440342055100e181d807030350ba441031352801c4a204102000c0c01958510414800c0b601d0f4071048500c40b01c0c9024804c030076920782d01c0c081192841e0030350014080a203040144550030000f00e2415148400942d54454036644015440344440b21104040703134190f00410a46131941031603800c0c054260313040d05004211103c0011024856443c2280f40c0d001160025507003420062603550340c200e124410b580a0400c40078000b8041c4c507500c1240c60341e030b11590001f41101800d940c0c0200429010320300130403c00c5142424a0072656500c0140c404840510040740024001d40d14101c01718171648009008004035124000c00391560011005076200642c1c08100082400380c060040b9402410003007a210100e812a010080c140304c162103620070560f43c06c006184200c83c4c59110440d440468119615041c0072140c0000e01e548a00d034008000f03214007007019018001c206e000340c4a01ca0b02a00c0500a075901e00b500c69468541079111507051400c0c95859 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 675875674 1250 675874424 675874439
    0xc020f011a01230c0c0411030403080126070306020307110609030405210f0d1407020d1704031b141c1b05060408010207050d03110703121e0b09070810 66
    0xf00d203000340030343c28058a24520f0100b2800c5a002c0d031249403059102d0018054242001d01c2180500390880c00c200782541400d650042415006100c1c0e000702c124041c1c41001242c030442c072b0386000300389000c0841e17a510f41d4074506000650402c5580c540854010b40c40521a5080850010312415041c0007640c9003504040c10080401032030381114a0450108003100b01c0300c04108944c007800c002c2c80300208009900ca42e0000d2105040e070b0302d11546001c2c14401c5100607228070480007082640141e0440c60456510400320b5240210390010f01127000400f400e52940304102802c206441d41d002e82c0342d060046050500c4400321403148501c220700060340089001c00d0b00d041100c000c11184000240384156990001070307064000740c11892007654000760700c0b0104101007101400c1d0514508003801201140c0d0240761f41402491400f5050200031030030350940c81c0e166404a135424100d2040c445601c100c590803100100108441e1340d018030b1342c6101280005025854442c81980119099071085080885 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 675876924 1250 675875674 675875687
    0x1050415050903040f081624110f06010e16021908090a03022817030a120f0213050111010b0609150912010209090115120b1807030c020f011a01 63
    0x10715405003c20b10020444202c01c540303100080c50460018150a0039031a001c00c00c40901e1f6000e64143c07840d904a907900841d0310545520038038054100f5541e18a45039008500f4252140d409071910b004e90743c000f0414001503000140680c2c0719208804881c00003074030581e0340b8611080c4208000b4445141500050004401401641006001006020f50342e90200d100c144000c00d80182da07407540b10b06c20752001104100380c0700420581c1020400760007422003c0e80c070b900c5007850078020006502c900030310204164020718400e8107402c4045546005036201005151190b0150500050406803464002c4405001d5100c400000421952501d8008810003a00001c40500045000c07030500c1040c07090790f1100700c16507400103620005a5502040c0c07080101c503001c1604040d01241225081d10b14156010070f21601340c80315254009400c600500005003180303003403204052109080c000304201c4c641c0c50741068028500c590226a8104041c01c2021309036800065080c7c007181c1c1a29182009600c90315 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 675878174 1250 675876924 675876931
    0x923030c010e030d0c0e0a031209080613020a060806130e01060315050103050c01111c030204080a030c020a0b0711060d021c0e070e04050d03050603010e010903090306050105030105041505 82
    0x141140e190450380e9040c24296501103104030307000c2c1c2020808001042150060039081d880610780b10418200f15000038401022500010f07000c161084999103d040c0185c03800c0000c1c12040b412501c89280043c680c02c51004041c1040380589090000040e1080c020204580074a100601171541072404118000040c6100907003030006641303460340080450a290b040c4542241002400f084940c19414004d1400082e9032207541049103010010301c610380c004c250113100f075064180c0c150160b1100030048000c2d0055800c0162113000b80e405c0101003540241c4c400040a2098032007034442551150728040364003802c680a40620240c0780c00d0580c0f4030780a4001e00245c01c8030a00142001801102d03d440c03402010110140c80399103900403002d1110401003500105620782c848001072526603501030325524444400300a050715140407031140d507820b40251b8901082e0700000c02214502d41170041100c01648401c1d03959525110020409003810301515109940040f0703007054012304124000c0c003c00006 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 675879424 1250 675878174 675878243
    0x11d0d0c030e0406060306051f0203030705030a0b090108060a050609060d17040314030406021c050a0804050703081909090903210204050405040809040507230c010f0c09080d0309 78
    0x282c41d0180e80c3d41d1548103950240006039400603c0c40c0c240f1060003c07511030080c80044a118014101000d594000101c0794000b90342d151940d01c0b601d40c054070001401c84ea030b50440d40f19070392000100d055070000862030303c00c580c0c0d50002c0c000c03601c0d40310a1054000c0d00342c84070341c0c2204211616402103a01c9070300191000c0810b1441614107907894681c0400d104a005030224203400014040101d9a410003070380018424a880151000c00d992740302420500c2010140001d102d1804001414400f050020800031070300400520754030840024005d4500f0340d80360310100450601480426076207240d00c246045294143ca17081d04442603860560014002d0380c08544101e40c003008007003500e03100c90140c0c3e802a403040241c82d4817990401c0401081e54002400d0104100e450b0350008000d090800c0403c80c140588910343d59901c403039880550140c00858200c0301100d00784402c01c2c0d1829401007000046414120540d08039420b0800202c0179124041e00c0a006100c07240c2d030040c02c1c41c282c4c1400140704043c8 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 675880674 1250 675879424 675879437
    0x10020a05090306040809030f010c0e040b040f0e010b01110313060e030307051002030f2503050c070b01030b041b0b030609070507151d0c0d06090602091c0203011d0d0c03 74
    0x407800007481e0110480d81203d0700c1e200420786400b1410200641520312050300001d100103049904020302019003a64018440c644600c9061304940720b03680018005c2690359005d01c18403025888881c042d010491340d03030303001030b00300a0114104800030081d216003024543d0250140c40c13801800701c4e00084107404460b07050104201030b80c0019010450502c22648081c0003607140c0c6080c9010442200c2e000b0084400720720b01501e007030710403e681d144d41008038925040c001182d4640300f900911501034128000d08403005000040300340854503020074402c038401c0d04480654070f502d42c3c601640380814401c02541d4403041c000300e00189003941050b60310000743d140817400c3c0051a01c4280c00004441d510300d004990b20b0018003820100d8a0300300d558050007100410440c3c1102011070b4001900c05000b51885660b820400100a8070b501101e25002008000b8211441603041e80d08002050040880c440d40c40e03d0794001400403c803c1c02c00403003006101400c6d090644140551300c0404010b021800c0245 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 675881924 1250 675880674 675880687
    0x1d060c010b0a06080106030c05040602032b18020f060c06070e13020715060b130b0d09020d050d0f0206070e09040201090b16110a0f290d0b041a0310020a05 68
    0x45403041c0d0300050030f4903a039402d82035242200240484602010b08001c102d010031007400169000012210110348c05450103600c1d0b014084200080288610441c414a0038109214201c0c142200c00031010341c001c54090031a403c040007081003600c503021541611742c2041c40000d035031900414411180006c05802c1822131400380807101c04a9004150803140001c0d6104412400b05491103403201500d5900a402c0c07404032810b256544020030303880b5920325144009000c000c00001c64008260395a400f13003013030040417050b1808545442000b0041e074000f4030074036640f42040f44001461809910141c4a142000f0020401d00c0103c00004200b80d041c8034241e02c0008043d1071200003004820980d40846900354490b180110b0111280c400061041200120030301401c1b62000c2c108045452028500c03600391040c080c1201118500000300c80f00355070101d000482008aa005441200811a8100f000802c000c0e0030b000c6031504003003000d8040c4d2107600a4410b5004690082a0140c12400c10a06110 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 675883174 1250 675881924 675881929
    0x10605090f04143c1f020d0c090510030b0607020d050a0b0f0601091d280203010e1905070e01050c01090507080f011d0303060d02010c020d06090b01061d060c010b 71
    0x4444020400c1c04c41030b01a20318200301140d1000748100ca5410710039503060102029102d90300d00c5414a54a291352180c2c20b000c91940d807650440340e414100c168188426184810042c180c241c0c0c52142c46c1c02008140a030f1130000d41b00340b01c0d03221840f200509541c00c0c001150244095001c03442c01c100e503103104108003600820041c101240c80303204d048003031010301e15181000501e01c405940c44100c1818004e0303103442011400645003544008100750004183c01c5041081041241006a95140610000000c18803041e4000d5003403003a0f0100d8054201c002c85104000103c5508881210000b013103500c1c81d102e15803250700108404205107001203a16202c070f4480900740565076100036540d5000d000e200100c00000c0c0150500c003410b164030000740c03c0144030219140c0c8402400c040c40361071240c06600071a8004c00c8110041c03900036110000e03d10241c5003a80051015581c02d849a0b0045400010921720402402c011a0481d54000078414905801d000701904142c03e801c04079502e60708a000946c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 675884424 1250 675883174 675883183
    0xe07090914070207060c03020601141c060c0206060a05061206041b020307020f0d172b0b0111030a020304030f0203070e09150a0605100f14030901090b09010605090f0414 74
    0x1d01c100300000e9070350304003908041d00d080e20fa9032015050045600b1120080394002c40d69504403505181407031940c984440005600e80441d10001c0664040c8000c10400e008103035024519032b1509400302e40c402e807035140070800e02500780c0c4140d03a03000c00b0402811702d50094044043e500308001801c08184000d80c1c444141c40e501c000004440168070115500007980b9100b1042064998280d5580c1e041c1c01b80e81c0c03103200201040c001e0b941c0303d82c04006001e40030041c200120104841d12010300c000c824a02c10300b1580544000d580b8140001e0861411202d15500401182c0d280c420381d400440c509440e45d943c0301802d0900b02401e0768180200c0c2400501003a45003012032082d288030024128500d0452010640e118003e400302e00c1c402c3c80c0c42e40501036a1904420052101e2071814070600c1070401103812140300d00c0401142180a00200c1444a601015001540598400d85020503a03541340c4103c6400c07a2024840c00780d210b620b800c04075010322580000b10340c1050007012031400c01079024622621b403 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 675885674 1250 675884424 675884441
    0x30f210b04050609010b250c0f03030f170a0911030d08060a0b0c10020c1c0504060306061103040909080f120a0501080c010806010e04140f0403110609070e070909 71
    0x1215114008515607250520515034441d03411190b0700155410080101d03c24018075052140364503030780c1811381038554080c10384814194800f0908180c503442d41400c04100915100480200d03800d07d020b4083d0a000c1d103d2a1506054200c0b9004070b941d0344000803010700400070b419103880d06000e0702e0341c0c43c6880c28816080040309a0710386032440d08040c410700c40304000c07980c00307051200c0e0107011049090380301091410002000e590056264883d4800040c00c00b01c500e41750a0f500341d208010820f4480d0000080c0c41154096103040061941d94117065400107240141b090b19a001040b00380702601c1c00c0d9020501142c00340708c0c1c090a200c46802d4800007a800607500000b91402101049a581a5402140c0c090b001d910090b1103014103100010b00f603040301518941c140b2100810451441c0c0340c1d41e0103904401c1c1c081060668600b405440c804c040c0805641c00d0700011502c4414079203810002516070300034100da00007000c2503440d01284003040240901f0385410000c1c10302c00010300e4640d50058400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 675886924 1250 675885674 675885737
    0x91e060f0316022a090a020d140a0c0302070b010b0a0201140118060f0339062a03090b0304080405040c110f06070e0d0606080a080c010b090112030f 65
    0xc80b40401400030741380c11501c0e4820351343c1407100c504048004c0c008200144022030300743c40c0b044080c0c41318010480079005885503060380700c0c42c00461246030551400c0a07130003007001d10804c121004240904a06a1007084009440704208034010003450390484010300d01460300f880000f03011070340352801c61006142070303000049041000bc80c0000b10060f43c42200d005050481d100d01c007a03841c650300e6160040c1c19421418050604150f07020601480c5c0d410b64115010300d40f1218800d54803000040c0825000428001c4503040d90282c8004c90a80c0350a11844d264142e02c950803158600008001d1b0303503000605c110f44901e41880009019144c9000b80da4000b0866285d60286000030780d0103503d04401480c15a500707a006005215106800210310f0710904001d6904903070921040c103005001d04442d510040300c0780700b501d00610502100f08080d02f5518291802800308840c0c031030822504507404c1c0154010107000b0a07030b201c0003a00406507440d0030109800e1841114000e807030441000a4035006056 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 675888174 1250 675886924 675886951
    0x6030c19060906050a0917070e0106030f050108070e011815030f02030f0d05030c0f040b0406090819231536210412051f02091e060f03 59
    0x110168104010402903d4a450201d040840e4107800400700c0d070142c858903020914540f00b0301c111034010f01c03140001c1c107030624100e1941e596540d4010010544003500c15007252610b0f001086022002c02d42d04110b84031000d9402d80c9900f0b1650b0f0440401409030551012507039a650301c0940a00ca14140c0000c5010703403140101d0082c6401854100ac4082e14411001d80003030b50f1003002d140d0040180e036003282d00d054595403510008040e0745803920980e0010304100c94041000181c15600c401404155454030342a00c0d18511401a00c2400075100d500c020400001c02c0b01c200c400704540030405140c032410a007104e0120f050b290301c0090025054540e001c0c1c0d2004681440d00c82144142d600e41c19480400f41c1204094501090356115803454100086010004e046030f480c98900b01c050754094040b00000600050711481d0217955040c2c0f410350110703091009014807a50b061180f0940d00b070404094081c2c0048492400c0e03c0710586a03203006030360b00c0300c1c007440281100c42c12980614400d0300200c0c1980d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 675889424 1250 675888174 675888179
    0x51f050c01140f0f1308030912040816210609170d290303030103060c1403070507030e18182a0a05030d020a110a23010906180e06030c19 60
    0x21410042c01013841c00c6000d00030040c0905490550000c1807640d03040181e0340d840c1c1d25814007450620b42041e0b080701080201140c081500c10001c26041d2140060b8401d106100da9504030100c41004ca0807824000d0116460300407020956075040329401c6407243c480210004c2d0410a000b129403c0860001c6402ea550b81c20669911540400e00d4022041c44500c10584103025001a941e0710050100500007a111000c3c500f0941c01400b461403110990310034241c60349070280000f0001e81240d0340507000141151049101424101c58220124101c91180311440d17440c0305092582803d41c60000b02c1e58880c04070820a0200c0d041d030040c1c2c43c1941c0ca2003007040444418104200101e868004504c20380020904807043c580014140144031740c004540340d1081044000920355001b82e601511780005450340078003e0a09600d14452201e509032121103a490b1940c904860340c110b201114203000c140300030144501001c0141150380301c803000f4100d950601c07101010a0018030b100b15031543d03403000b00c00305 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 675890674 1250 675889424 675889441
    0x301090209040f020a050a1a0903010603050712121409010f0207081905010f06050303190908070b040e09120906160206070501090c060f1d18040c1e051f050c0114 71
    0xc171002000200c418154050405140d80b244211403801e401d89030078005502e914684081d041345009580000554240c0c684d01c01000b82c4081d84000d0403101c1440002a1800490245401c0041c81080550780d40c14440c3c40401176441011085440c030541c811100f00180348082040010071301510f500408109515a1801d030b42940c900340c1d000442541400c0003800035880000c00d5508080000700d82d0400e000010006030781092903a01b037a022401010340105480c0102802441107802840c80040d1f165500c5c2da090b5220414180c0b100a940c004000380102403504401601c41d140e58a80840e80d2038600760700044450340080011220303030351111801e000b400825407121000740b01c141003c4201020f075210003010b41000202c0c02038207000030b060302130840c1c0f07400700102941c0c03030700c022140d445080a0038040390440c001d100302140c030f07120b055104a6523920300c840f22084a0000c1c05d0a042d043c00311484102c1001c0c41e240340030402c803003403284a010300002d0241451284442c80c1302a0340341070030340b00e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 675891924 1250 675890674 675890689
    0x20c1b01030c1e140705060c1801030b0d0611040803040f1e030c1208070f200604030201140c0c0d0b0403180b0306040e030903070f1410021b0301090209040f02 70
    0x5003c1c090031510f454081c1c00c0005101c00d0442040c540300310301d50404518a5050b004000001d8040d2150380108008010b4100082559200782041e941c2c060b880000110141e070ba0030035115800c0501101184c0024015410414848450b40a103d0030240c80d0700b01c4a1a582041e81b02d075039219014501009420000c50015014002002d8030728006030864a4007004060710384244d9584081407020307441801960ba050710003075580440d0560f0b8148550614485ca001e00d000313038100f90705807030341d5000d901c3c0f52000485084a0b41a141c161200940d901c14004a070041c541098241c0910030103401c0a5a601c41c0d0001c0b1284548200511400c0a0400800116a5180300e1a24400320b80e42884481d440d44207482d0f00c282c00300d50116140c05030346041400c500444001075010b00c180306d0301140300007034400c141064540f604004070300b5203152000c000f000c134131b030b4a030190142e080f8806840f42c0b00282d011900881c00c0103000804c2c01006640824004042140c00741d542c42100c3d0f2000c000c43c603040310f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 675893174 1250 675891924 675891941
    0x40e0a1104060b030601020601061119081c0b1c05120415120917210a0c140910180503030f0a020607020106052d03060408090312040e010b0a03020c1b0103 68
    0x3e2403182585860310001c1d640b090103009a03814030800d942c0c8031180c11000c2101d007514034002c040706000f40740300b0714000500e0b801002d01801c4402540418800c090014070034900d644a0007480c040028142201050241d01c0000c026200d0b0f0080b00100e44101c0c0d80200100010060910000d1a41c030401c903000b452082c66540e10a02c02e42800010404107010306440b06500c44190400340c3d0f6110002c8000500041000503060030b43e0700d250070001841040da005650613039183c2c40348101117034004124400c900c18008000e91000b4203003480c9284602c1400103034968080c402200d030219489030006846c41d00541c08840e01c40c1c1e400a041e00d82140d05100c595082140c0d40000d100f1641800005260182150b801600101c65242030703440c2943c540e0301d046020319020b01510b4440c2820f09100110b680824104c0d1b005c2d01c02e4105500b003070006981101d04030380310144481030590818a034210b20340c0c8078038201c204058080c84880c810710000c1c4940503403c5041c5030700006110001001606640010 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 675894424 1250 675893174 675893189
    0x708030c0d020c1012140411040f090b01091d010e0a120c0201080c03070507140a02042403060b150c0c090a1406120a12050d0b06030103030507020f040e0a110406 71
    0x1103040581d501c481c00c0c6000d8101e04d0742840c0030b1244400c44000028a081d0500c2c03010201d02c4020301090210800b40c148040324195410300c0510346428403001507482d0714500070065021940100701c2c0c601030382e002c00200c040000b18020800c007004516070a4070b204148454081e00203d1621003000180190b8401401c100c0c104a00c80c18065000a003c2d290000c3c030b0344201d00c43c00000074140030b20440884000d650700824030644507500c03403031155940307007010b02c100c0c003a91a144040851142039100383e0502c03001c2841c40d070803d42c116903490740909081031895420004c4080101c01d01802000a85001029040241185100ca10410030301e4080079254442052405400088074104603101c40c0d403262007500c039008803c1c0c82044081ca0111a000060041d000002e4000341c030355840740003000a8607408100780710255820041161622081c840280811020400b0100500304007681d41d035408001040001c601c45030034140ba0616500140c115030340d00490003007001d01c0c9070501c100c01c00b801c07c6 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 675895674 1250 675894424 675894433
    0xc12030209031011180a120606030c08060405032704020d091205090f010c05190b07080c090d0b2703041d010e040305030406021306120b04090302030301061805030708030c0d02 77
    0x10100d40203000c5c450b10a280052090194400906131602041400101850301c005140000c003030a00300014100f17408200c600700f10b041000900000700243e2240210b81200245140c8000290f0f504200c5803030201c100b00006402e8400d6000383d03143d2001d01a00c0011400c0410703448080e01d0322900041d801c4031b40350306204051041100d00e4a800c0308500ea402400c0c28010b0a100d05410070030b00e0261201e0442c1003005a070f0315601c041140d0064024081c5009807281c01458803002440348140c041d10750000d4104c1c651850300400b080b04041c605811100ca103034541880c075420400e03655004460307115801e1581c0001010850804600c0c9403228404616402440715414800c8a200740c1001a00c081c0402c040800801c0c02d00503603038100c07901c1e0382d0503ca02d51300080d07543c074000c0d01594510042c04007292511040002c03600741f074020108000d51540c00780d8516820a0b100b580c4900241c00c08142c100349060002c11035440400895028090300c07002140c4406000841d00d241507049491582107400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 675896924 1250 675895674 675895691
    0x60f1103150d06150503070f1a180414010602070501140904021c090506041a07020d260c031b0f19031b0c030f0306050d020d030c120302090310 63
    0x21100640341c018400648071128805640006804041071a402503c3c0d503141003811656114415401000c5410035400e13140303d5030b80c5400007003030141c00344908140448003840c0c2d1080c10007240300408800b0380c3c1d03003000c032603054640d4041021240182111074001e41aa80184072035a010410400200710134178158140d1030a44152064600600584070f000ba900403a5075210f500b40c84000c42900d5506160030003103680380e4208150b58003026501568481b2007101603011208803040300c0d0303206060507001040070350580310040703400c66641c1650f90744000b455101274400f4604c2421150042c1c1d11312040940781c0c01c0c822101c801c0c4115a82d02d00c00c05000c01c020340c0d06000d650070255061140403c100c00c20381c00941e50107401418150502d070010104807003401448640110b07180c11014025030391035072541c039540400c1d4100c236214010a40e022640c42c100c000140741c058071080c4224883d1070010640f410320364803000c5a4010b800c0180200380c0109540f1100d060401000c111009181020301c0041d6 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 675898174 1250 675896924 675896951
    0x30c08090a08030d092102070306051e0408280806120705060c0619020c0d03020904061205060717060a03080706022104060b0604120609050f1b0301060801140610031103070309060f 79
    0x401e2484001c1c0255292070000340a001c800c04cd0541d18880c43e100c0c1075003841c151829041c5035101140302e5001001c214404c0c3c48000103000c900c8010400f40e1540c50542c0c80e44000c101111035110040005442591000f248a85549001e01840f1130034600422050501d1405880b1403101d541c2403140491040c000c00001d0a000940121510010706005a5031083c0c180890050032081d001259141d1044001e40d08115000503100e209106659605102c541aa60140c0f800c4e00240c400075440b02c82c0c85030034000308401c14020320030300b4070440005241070441500c9899001c803401880104103450402c000a01019020721243c00b441145c1a514203070a15441d100140f407168000b411540d51004982c08003c1d00300490030103001d80d1001ca5000100d1021300103517501440c100c00d800382d400c00000180340a03050041401a0f801111206aa65030f05418084144009801a0105515032051140403c40403009600480309036801161003000307810403005a84000141c480780c903103850f86c643c4014 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 675899280 1106 675898174 675898183
    0x204090f0b063a0f03170a0912050a0e1905040e060112020d031b1a07020d0206010314010908130f0506030103030c08090a08030d092102 60
    0x2d903501c03000d1014400015006401000765414449032051201c00b5554440d1a001c0d9820407610058a5903000c0b0034040c0019008a10403600c4d6003044400c80d10410f500001c14102030055441d070350341c2c8603c0d84c03100d10100c1e000c115020800d03007003161043d024540c0110004007625402d101076055140103010611600f4444c034909031840b0910f08020072404d04079844001450746030101381e0240098841d108000320100443e41c0821104410103241c4081081d000c0c0d5614076609070640c00450610744040e01c108103650010420300c0d4219070015500741540c0d4041c51090445054100d058058044104024aa00400f250000e80c1206142100342141c865428000103159103506005803840207001c0a070005802c44901404614401300411941d0000342407a201280d070744041c103065070882c030b00400ba400e0319402ca0304c051042008440403e149420a4103c0007101158041e548 = true := by decide +kernel

theorem cover : BRFrame.Cov 675719424 675899280 := by
  have h0 := BRFrame.cov_init 675719424
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675719424 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 675719424 ≤ n) (h2 : n < 675899280) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
