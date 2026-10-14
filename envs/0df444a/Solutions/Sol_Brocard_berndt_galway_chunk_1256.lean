-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1256
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:01:45.19059+00:00
-- url     : https://prove2.me/submissions/e69f22d2-78b4-4ea1-9a44-e13c3dfe2c0f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 225719424 ≤ n < 225899280 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 225720674 1250 225719424 225719443
    0x20306041407050403150b180403050408071707120305040611100c02010209011706101d0621010e010605071e051b01180e0f07030f0614040510050306060103020c 71
    0x4200550040202c0d882d000800340060303c0c001e1711441015880c1c1030540b0300321081040c070300358400840b0380d518000b01034580d504d0340e116108ac6405410540e907002294a001641d8100c1a24040140070b90300b80d108040001c00000d2040c1c00f0303000c60906454502038040d1166008200070052040b80300c07012403d003008030754041c40380d1510411040c0701181d0300038000d421a81841d4006034541143c64421178070384503114010400108505000b16046c001a140744e03035000b001001030046a401e45140d82d0b030320300180c90903407258881c4600d114a4100340c80001c0c02d050f000461503141040040c41480d62040540304400e0f408902c0d41c00b861000c440c1d01500c0051800b0007481407250700740e0000a08602e0450044500007030b00c516002030184500071011007024050704120106580000340413856110720660016140e08002600f600c40201e203030203840c901c0e0046a4044584079a00300241040c1c450564402a01c0d24001c0740f650a0200291f203c0001418490400d6004102c040c2c00035014000c00b4203 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 225721924 1250 225720674 225720701
    0xf0a0c110627151c0f1503030807111b0f0a03030302040812070b0703091410020a0e01030207030f03150e0f040203060c16032102070501060e0108010902010207050402030604 76
    0x44403070012505845000030b00b42c1900e1820444008140a410b00c0260b034404151203194490812142c200a00b45151540d010300344e8064a42240c080c0500b0540304542c03092151086550300c26046003400350100101074107450802c000c0325520b000c0d1560202c1c40b010300c01c19800c4500c524503000c2c0c00082c9210308000200d944110040d000208140d095401402214a02015102c1c501c083c001c10740c295000d02a0007605005200740042d400b907229074004000c2512502185a140c0b0300f14040c245810240d488007522160300041d40c0321450303008006903400120928043d85444403030340d001807a422104502c8820306446800344a03210960303c038100054075100e40c04184503d850550410280819102031f4000d0242e180030544602d500021103a0100b804140c00020b00b645503000c9540f00b04050041c400a80401c4c026495942d580c001012624007400010440e913090182d564103e101c1a4002405a03150105410050b60080b942c101102c3c3c08850058030f950303401c0b02103000b80001021549 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 225723174 1250 225721924 225721927
    0x10903050c01200d0c120306031a040206070b01030b060108010f0b0a0f030e0f03130f0f150203091008090606010e0307090e0f0304170106061403040f1112010c02120f0a0c1106 77
    0x2c500c05e40c041810400107000d0084081444021041502103a41c940009000b03121a031000840032403425100e1500305101900c42840d00529860344c200b03041c1d007078004a54580004040c48020340e409542c0794090300301c4180d07025105103030800c44402d82c80740b0085c03602801400a8440301d954041d0340800c0f02d8110500a03079030441c00424141e078480c0d00411120003034850003031b0042100c00650341c07000141c410200e030309040740d4100380802c207242d07807888031010444c4000c0125041d5502c3d941190310001a540e213030390540e4205203810505224000305568100100d01d04608655500003400344102e80c00f60500080b03d16980e8561414102089003440d00d134480080d0000e1410015030540040e080650001c012032a2501d00446c1c00c0042c5900d00c2d0007200302400490007064500f00b2916015101d9052003a480e0f07008c4011400c100c2d4540c00212036a596180022030050301800314811054821320b5084c54010352014409060241313929190800c80940d850034204000000c81c0d40001c2d50040296 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 225724424 1250 225723174 225723193
    0x50c16023708070605041e0909060203060f042702030c1215150f010e030c04061e1e061b0507030501050a0e0109170307260411010903050c0120 63
    0x11104040c0c4800c44101d05954103800141160003150480a8820f190380340b51a182c900110307100480d45e81d01c0d181d01700c0c03075107500000740ca456207101d400071403841a6000340e04c0340350800c100b1659200c10a4800d0040d0306103092a103050074001c02c84440da120702c9418194a401c0c81c00403a15184d600080f0a410864200429035004c00004021181d28496440f2140903035422258005000500442e6608104003842504a941c010150102c3e1100c01404403281140043c0010301039452a5000d141070401110002c900041d9a1266201030628942000005125900000780301c9000b8400c4c0341c1000030b80e640c0000c01c3e02e042211002c040d5001401c5840031600c80c1000da0007403d081c6e5210210625020b0300c2040705d0700600800c81810b404c038034410b210f00340840b0b0481c40d6038401800d00040200c02065880c4138010040092000501e0036024041890b1515180074294003503001c15060101801c1c0400c0000c0e000140300c00554000e28140c66440794180742a2503088070291080a1401208400f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 225725674 1250 225724424 225724489
    0x10f1b173d1505070602251b09020703090504020309031c020a020d081303031109030a060b040b0f061605030d02040306050412030c0e09060f090103030f03050901050c1602 75
    0x1d45101852480d074829038542d24900860103000707800500d00070660900032600407481582c0500000102e4824040341e000c81c1d4800e90112500070034044803000303005959942071900103d054805441000070840c940242602d01502007007552048903c5a0f400000280c0c8004050017a04d000c0c6030440b840c1d003203401214003848040c0d0003030980f1000602c140307001d44406034403e605070350003803a160060a044a085440c120b015100002484854000800c0f540d6410f450400111904038010a40041c03820302d86820803040d6195545403921034100700b102120666180008c5130185a000195410880c130b0074540f59055020750811180320f207101050000a01189420030380c07140f8891191a400c600603040c0c15412144490f03060000030384203410a0107541018007d5a03004140100400d001a1401000031500403098108400042c0001035000c035046d0503000300c40d00800f09078000c0c045464042d484088501a184030302e50145c201d8020708041d510740c1400b44200c001c1d60110a44046d20600d070 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 225726924 1250 225725674 225725761
    0x1104060e010f080c01080412110a02120307060e0304050612070212030109050403120e0714010903020406060f0f110c090403050c0604050601050102120903070e06030717010f1b17 78
    0x74580c6134080c00c042d1041e20740c07140350071603c04c9500054110303040100007003c42e100c0450521115043c41043d02050140e62401106031036482135000569071041c0358941802620f400d800702c1115036205000030b110507600d10054680c1491181d041209550300c2000072440c1c446a1400148000000000410300740c1003a0010352045c2d02903102e07100422074401c4103c0c22034400744500403ca800441040c4590b00b682c40c1510f80d04401458020399550f10790300094100d0b0303442d901000100300043c003201d20207900080d0441c5040400d04064400040c4658565201c800c040e50701ca203e21b1248000408050007142a900841c4c8694102c0b00e480ca080d02d01207942c0c100a00a5601601ca6003046082d074100700f00441d800914040c0140115514003c844809240c000d842c50f985801a404e010508045145c500304041180034000f0501542e003252440480e40300342540c40e160400c804006829940081c481480d440c40b25070807040b246e5515503441021014a21182c000049002c0f140070700b01110003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 225728174 1250 225726924 225726929
    0x40c0e130209071706120102040b0f04030203120a120f09052401120c0504050403112505010809190c08070303020303010e0c04030b010e070e12030c060114030a1104060e010f 76
    0x3540b088980d101c00070191a18001c003642a65440010000070700682802c03101419003110400016003050340f0b80140444540081d589150304c1040403c0030401d507d010401d218217a50a0425186000449400185800e4400b045202a00d07102c1d042108807242c254014400550050155032083c3d03895080c2c11080400940d0300d00b0b81a0b170748400802c1000c211060f41c420a40d20921080e20b0501d80410b00000e00360042c01078040c4511031880d4900028140200c201c041013050403c843e5100b110040800d8106503000765040004500800080c0c3c24005040e01044000c50b4207402c03024018506411240d15580203e4000d0242120020800d9000400745050307408000d0060210395491702c048100740614800070300880c911340c0c0100300d0f003034032418000d401c84c01c107140c000c502c4c80000000c9100b125031a0f20b505a503902c0011561810102031000714090182140c2041c001103807200020384d194010f020142ca0304a404030322404941e507551000004002d038a4034011176603074605415890341e2952 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 225729424 1250 225728174 225728179
    0x718030614070516030c02040b09010e0906160c06051911040602060108030f0a051c021306020f0604110f0402120702010506120304180f021605031c060305030909040c0e1302 76
    0x241c0071805141c003c50139907000401c000f143e02c19401041c1c60803600b03494089416604241c1da014501030076100c06909602030948440c1d0f0314684c1c104070b4030b4a0300c9c000e0f0052884041c0d61540c080c45222582c4a6000c280c640d03080840850103849944000d000c9000b8126070140c9180382c29502c44038007500c5405030040301d50a400341c0b1150381e0303038107129900c03031150328000300c8120310400844c004940502c000c0c0141d50344481e600740300005411482c404a80c0004000f20002901c41010800c07554104800800785082e6805446141466550922580e0308a140b00b841510901c07041d440d503480b40d90613109000c000c503071992281e050207100a03000b828103a51150194102403500c2000c0f0390000211000c40381910004503d800328010101c0c0100020482c1c2031080b5005c011031401d100d80f502c010407032107004002841c0e640b1515540000407100c0c1021800c0c0080c2480e0042001c500c01005982060005441c2d40f0303090754840c641002a401c858024029100c8204240134080c40300003441602c05109 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 225730674 1250 225729424 225729461
    0x50c040b090105131509060e04022805010f021203010f0f050108040506190227130b090103020f010c1403040806010911091302042607060306180507180306 68
    0x5020902648841c00d00541d9040042451012002c962540c041032061207840c1d402410303a600d40c0d2441d0305560301030b80580f260b100040203120651808607071003003907401454101820128201803000440b000c82c81001e043c801da035509090703014004c8c010480302421003901250380e980c5030701c951140d14107a80124030808a0169001c1003650007005828001e0790041c00800d19940d503070591320303220528101c5038800150240285e000700d40740400041c40e030b10792006040c480540c001040c003660340180d0307604500d02403c20079810b84540303801404506407501918043c019030602070040c2c07210b1266510090103201c05949160503054040060415140380d00c050300d0450741d960300c0690135515107682c22410507504008000719840c05c440241c0021021500c054101031340da810b906001e5841044082e035a034140440d01002c85414450b80e401f620450508000a0f0b00781000e02801540300d00303200e190782d684e80000c030301c015001d1580c4c1c049500c4940c0500391000d889250c4175000c0d0604c40c00340d101c0001c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 225731924 1250 225730674 225730691
    0x41401020c0307060e0304181a03010c09060309021f05070b0907061707030e06011509091407260703021206010908030901050a09090615020601060c0804030f11030604050c04 76
    0x1018001c54000d80c100d1002181081c0b9992520b5000f410003e40c04003540c4801c200000b032100d50781c407624120700034194000034200030b444219180032840c0817516210740d150034600c25007030380c000c11150107640c02842c00055800d110b2000c18030004054007586040d01102d07560085c1c003a8041c006050700d9101751035900c0f554482d0b82000b60354001c1e40c041d140c0400e07401d41800861080a00c0d2895000203946000f058461907a1f44440c204402a0803800c0540e400303807090f141c4150800b980e11300a09645d501001150301d908206803000300301410b400200410041c00c1d90401e0074850306000c0c1841c00c0100746105040c183e03009802984080800c1d5040e5482800142156004000100c1140c2041000e58501681070004481e0303580140d03103210610141341d2001c00d03003d0031440b0f0140607100317404c0c400324174948000002c2d01c0c100059110317604001360801004002a810130940e02140d42c80500603850604620300040d03400e0b103000300103416218407802c00080c0300001844030f40001c02030360104010036 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 225733174 1250 225731924 225731963
    0x31002040f0303030e0307120201230c030c0901110d2006040302070303030203060613030b010515030c070807020f06161e021804061806020a090506030622020d110304 73
    0x614490314a440780880001c1011030700079003101c01015040e03801d0720728012207685c601e0400d03520f486006005039501c0c0300c1c42d1070340c1261500d000c0309035007404002c03803441c54600c02d0383c0c1d8540b100411032036007002e0100d20700c0076590094404c0d0401c010b4078010b8910b540200315000b442007200c0d92014803040e0010302076000e010800b0038054040c640560207009200d04584040d4042d600181007290044030402826003460091741416000c1d503c03881c220740b0780d5450a4200304003d0144140c034007803020300300184110000b0550031109610381c071540050702e81c0c05038000110030002c0c1d10b02980d0000e1000640300440b10811006000292003000f08211400740303500c07030100030048008002e4001c290120f050007120580b641c0c07580e0103445400c3c0451100300c00b0340346a10504080c0740c104c407500e4000c20013401c01c1c2c0e0001000e0000d0102511080d00f145030143c0000c3c4550280203c6415028440c140700c200d10803241c044038850b01e9102801d200c4196103000d040b619074001c40d0141c0b8581e000c01054030101303 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 225734424 1250 225733174 225733177
    0x120040506070209100504020703030920010c0b040201260a060605040f060809010906020f0304050c01030911061b0f0309040e030301030b0415020712030608010c083304020f0306031002 81
    0x150320103409107080855507800d2008803100134184407411070b0341180002c1c095490380001c210061083d90041401e0a0515240c1d070b0300b070941804442d44603030700031100b1b2550764803142d0818140d0300405085800d44a03400181c40201c03002101e0000406410145071031400e030080c10b01d003d41a0000100107042d81c1c1c080807a02d900542c090341a600c000b1003010040148210b03840e81c2c00c06802400080c070f80c00c050307507007000700c0c0c1c0001200941d0f0b1402100704820700400380450b4803600382c00c2c2400e001040d0244c2d1040c0e524611004014450140820300308001007001c0300795405150528200c90082e121085050b0741c0e5004149901d100d1800d2444000041f040401668102c03607000e041c240450700c4580d111b203011404450218007042e801e00c42c120108081140c0d81041c00c00a44000403130340d0509072601d094a80c120729080030301c41c03400148404543c0040e4010451091741d0a03001c40e440041480351800701201c4142c1d6441800030581e00102d11100f00111f000b48800c4086444502d0b01c4031451069 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 225735674 1250 225734424 225734429
    0x806160504050f030c04020c0d1b12200d021e010e0c010c150f140106020d170702070e01030605090d02071226070b09010b0d05071a070212012004 64
    0x152060004000da0f05054040c2c2a4404000307003580d000303030040c4000c90103e81000c194001a41d2200e9000c0b4081e0740c04ca10105e904202c046039194808103151210301d1050707400c00402040240480c1690045001d400d80c0341c840b500e07560f094800075402c40100943d9513400011000d00042c0301008040382480502c100c42c005c503440005820b01402c42401540c9035a00c040742980c55100a450820251100c0e1155800340e100c515000100d14880461713242042605802c80030641d0302c4440b56400d4aa0014055071400445820208280c1d41d0400c0490420310550721400d5074a130004008030401c1003a400584c402e4030301504407107410b00c10280c1266580c500d48180d052240703000d41c1041c003140e80f070f00221810702d07403504280000c17010400340b035101c5038020301054905501c2c1e00140051842c0078042d0100790078040b00c101680b401640c9901e070b151102445000b125401040480c070200c991101a58465034004002d900305034000031501e8042d0007400d08070004c11101d01c010003d40400c1c1000e6905 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 225736924 1250 225735674 225735677
    0x90609010b0a120f03090e090d09141c080408010903020a02100f08011707050d150501060e0a05130b03011404050111070f031107050a0609051e030a031202070813080616 74
    0x806002c580c13140c8131941e400300340030b0381003001c106400b0640f011503102e020300a403c914010b285103244c0c5200105582110341107142e1010b0000304e440050f96901c0c0021050f4150756540e0a50380c02c141c541f4032113522031a0304c000065403c0c0262002455001f04034892080d0007174a03040ca55141c2d1020468040d404d8070791280214080c031005011203101307641d91400423891007048407803460b00c032000540c1071171010300200c48401c00b035a004100361005004a90041c90a0b04140d8011225a4000b8003682514015280135080b10341040b0040e01c01038003d074650200150003040f005501d01c0046004c1c2c5000c079800c0d13544c1e6080c820400c1540000304200c0704215000a406a4a581150303400c49500683c035444c29114451008041070690700c0000e6800140026100c10300c071645401d051080713554070600240103211a02c840782802d903d000c5400080290700d49407180c2d90341140300d00c4000900600700094801000428200014000c02000906a030700c000201c90147d40c82031a1301b2800c000c0c082d520700 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 225738174 1250 225736924 225736949
    0x3021201051c03080c0d09230c0102030406050a030b060d02130b040509220507060f0306060201020c1015030804030c050a15021015090f050105040c05070c06050f04090203090609010b0a 81
    0x200828031900c081030f00050304118141c5802d100400314400c2c1c0f07c0019003699059207144428601140f10072540407000201c5010301120650100080c1d06d90089200d10b41c144080000d944480703034401d41c40031200180c01801c0684480b004030061009401403016600480e1500301c0102d4108024002d41d0b080781c00007414480640d59040c0f042c42384d107640c070984000c810030100c94280000c81c184051000b4010781d07554466510340c4106c004040d10307410760081082da403040140300e420100100d8021140d080112011584182064841d070015699900c06445140c0c003182c0442080040c2c44180200d4400702d40e10f41c0103d80fa1030300b0040c00d050b880398800250340a907082e18480d284da50440006103c0b330160514541e42e44071a00c005683d54025440b9050360b0742c0006100c0c0d0b140034810044031600501d40103050a205955004816080340207007414064040f03020106040030104640242c201c2c01d00640d142d06102c100b2a58500090b10b58a2840d42400700700e224509000d418003013241c04101040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 225739424 1250 225738174 225738229
    0x1501030320190602070b160e0a0b160809120c0103050a2309030d0c02060a0e0a030f0e03030d020406030b04110910080c0d150608070306030c0902030a060e01060302120105 75
    0x2030300c102d40c0c20104a96a54003405404086010400035a20440e0b001e004111074a40c00c1c00020008914080c0e0b9922030020100140031141c031503801e07605110341c0041130807030348034150030030030542e00800c080310381d00040582500003141008100c1030712651080e00e05000300d80b51100d1203401d84014a85404010f8095684584040350171b400752a0807100c4a02070702e1914110808290560703d0500c00800036900c41c0041c0616800948a00d80c00d1402041c041c00700008280c3c2c0040c8541c1c484000c0c44104018028a00e4599134103000320380c0f060500b403030119036484d80d80b400035010f002d0a018891017180380c11480010100410103c030000c010082c00f441000144000039100f850000d032040b203050703406114804000d00984505d0b205c02c0c0c0b000090382116450000001c24102c8001e007000105801c104013040000d006614120949641010151b2240d442183c0100240910791103c1e90355240c20000107080c0313030140d0052015440952203188141e889006200010090b8101a80b01c1903080350013 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 225740674 1250 225739424 225739453
    0x180408130e0c03061003091e050f01052e0b070606091a0f100315080c091f03030c02030a050d031a01020f0a0f020d050706120b09040f0b0601020f1501030320 69
    0x405c985980d0741e0400040410450305c4500040312684a040105c1401e41c036020306000c0c00f0401b082616022200038040c61030b08086d21000c00c886904680d0140e0030300782c0c06040b98001408540090000310f03249a444461900300380014140c0c5215409a040c40e108000c209110350b200040c589190103001d08259a01030401d00407400d244070340b044201560303112501d00a8a08401550007011500c0090007031101640800000e00303009000c1f06d4401c600b204082c1980c120802c030000859401d41403441a02c60140007003401c080008034004c02d94000d141c0d0101086030143e000700d00602c402d803c2110300609410040e41d49e0312002490311303ea40d00ca05121000940c0070090040c1c103500c0501440d00d40a000d5a40da450204260031406c08141207402500803030503e80715805281c1c2c0102c6205880c0d082035250041c2031604040c02409c0c80c0386400026140e64001c115407000c120030501141d014034a03200550192040a00081f8002081c010350711a00d038240320340e5840b9003905000a010340030700c610034 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 225741924 1250 225740674 225740689
    0x120e1507020106080102070606030b0f01241101020c07060f0203160b25021005060405040f020405041106070b060f3c0414060103060b0315010e180408130e0c0306 71
    0x12104541d03d4076800301c1d49100a0010f003002503c03808022450f81d0952408030030511000b00241808141140100516480c2e011042071030310424801c240101800e400403104100c558280a482d0760001401030000b0321700041040854029640791007442d184001c0890300d0744903807618912740040c0001c3c004045690752803081d070060603040341e1168090340b0119290410010361841809030708100742450764100d05016040d4070581c1154100700c64075080ea103118610380704441c06170003155606c00050070440000c1c240c01184000070b1456480e842c85161140d03400e5000c40c0c146004a140c0d8041c10800c3c01d012561a07500c0d00b408502011a402c100800012500c180110509055041c0d44d40c0c081900d40c0c0c0303e1070041c014010201c6005141c048005026110540c1c05a500d643c0108100103110703402e40280c181002003460541040405000001c240c0102c000740596004499024002001403040c0100324018840c1c450444050382c80200607640d0608031340c039002c601000c00002d0800c0c60300c1903 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 225743174 1250 225741924 225741931
    0x16110d030221070207092f0703021e100b0405070c02010c08160602091c050d30050103051b030c010c05160902180a050d081e0c0303040201120e15 64
    0x102c0c03001d00b500d40ca80b01d40100d602d0070760342407001d42c00980c010f001c1090b43c0c0c01000341d24154050741c01281802032a032201c803a0000384850802c03480c0400c020040500c2030000009900841480380308441c0090400c80e2036103c0940700e000701c0b502d480741c0c4103020f040c94011603100700083c4d294032202d0030304c6400550740b041200360203d4000b2001c0100041000455944851040c0100e0740161101c7c0c0c902e0600003442e2062003015026210540e0403000036100040b4032030f21545603d440f2209070202010340360b000d911098200510803000a0703803c00e41c40d45174407850480e8014401c48040480c1d04246443d1003e03118000f9805401444800100b03500641001010921940072219001008031420800340042d41140401540004642c2c0756400580c0f10442040021510001654a4100010003000448100520312440401c1540e030501c101764101c2c06456403151201d170340310781c0807407007944aa200300c4d022070200c1c1c0ca040e0140000c0085110350b4505000d40e0380180310340100081218452803008 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 225744424 1250 225743174 225743197
    0x2090c0309150f01050a120b0c0d0209030f03071e0f02040507110a030801060806030318090907050a1d010b03010503100f1d0a020a0603020903030301031e0b0f16110d0302 75
    0x2c840c29071800a016400074442d04518008182d603504020070001d00041d283e2140210b80d020080785004a06ca80c06e030b083e000581c0f042000d588211542d41c10000c0d000f41c3c0c500580c14014034a2655101c00084028070501c0d201c0e90035070b204a8a4031506920880044c1030280c83c43c44542c4400e00181030660041da0008042d0610b098603816440606181116400b8118005025030b00100306981d0441d0702c140d0040c4080740911308000301d07081c1002121591082c00e510a10160010500201041c020300c8007500c0064840c3c0260f640700e01c40d031220600c200401151800c6107000015440d00a0002c0d02c2c10b851009015000703040d20700985c84090011f00140b4100c442d80e4031b041c005003e030b52000050078854108060908090702d401003281d02e41c65070b8042070070300d030040103410b056903408030859044d80ea0084014112507402c0320440b007030004946d0001c0408800c801800700203000b0011461155603484c85e802900550070008441001003150741d4802c503800b06000c101c0b80b0b40203802600c01c0a046 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 225745674 1250 225744424 225744433
    0x7111c0809010201270c060206130209060a03080a110c0f010801060e040e0102040612050c0c06070503071403270a390e0601020d0f02062e06050c010e01060302090c0309 74
    0x22000005c42009034450000221000141c0008010710048078000404681c0083e104030310703001744022041608450001c2c4240c0860000035042d40e111804003002c3d64014400356203034200e004018007600006241c0102a2040540d00340b0f4a1401c2400200c07400e0040c0c0d5905400c1e4603243d0107485071001039031107950240c1c441c20301804440c0244050b0005010960b41c18501800e1100180d00b1a400641000300c1201c040010010403540003c4903070f000a5a494542c1d62035035122000c54058001c0422132a261200000303010003840401d00d01312030314550300b00d80c0c104c0d20407011015545400c40c14004203d04c64952401209640005c3c0c142c401e500340042004440f41500003c0c4110503554104108401a03082845400d507810458600302c004c0509110304012a1508017a41d80d0b64001c04589030303049440e2b1044d40301540c0b80d0114025940b01600c200c20300d43c4510014045402200021345c4540ca0800b0340c00001c2e02c14003a0b44122500503129041c580c88030003041902d45d00040051081780b05 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 225746924 1250 225745674 225745691
    0x1111212060420130e04080406080403110313050907020615100c0605040b011409040f0b040204020d0903020a0605071b060b060403051002040816050102190203010b1507111c0809010201 81
    0x6102c1482030f034280d1107103681030b582c4040803a0300e821340c95550000c0c074699118004100c002031180c011201130f00d070913060500380c0d42d0f034034a001c50b03000841542e8410140004544c1400c5000d0400c00b1701c1c02c0d10401c842d40c01c041c0e035506400303c0c1d5070b080c11200070031700700280c460090250400c2d9122042180c410310b8414119507050301d5140030b5070010380e0b04480c40c1c10010010401018403900400c0d03050f03011a4866614201500c403280120040c12000d0103102c000408541159502d504950a0340100c0c00f0038801c485160402075224a0700f01d4050354001d0401c2c3c00109064441c0b172410341302000c181c9a162025045482d4000146a42d0031000c1e0030000030080480030440400460945417000a4096500ca0905190354240800085940a030304500c800c1070015070380209040c403000048c4039140e5515078850000a002d00002202c0726081080c414002420034022401450244c0c010310388001c11850b44003c1c0b020415003d283c02c41100903000c0c400001aa4050003462444014070002c070b80040d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 225748174 1250 225746924 225746951
    0x311010c02060f15010f120216050a11030609120f0403140f0c010903030c0b1b0c0d0314010f061101060e0c0c0d0212160201020708060f010302011112120604 69
    0x45240325080007690003901041400010703184056480742c14800100310410301d0b00c0c00649000040b0341d9020a001100d5035000c05151154140d802d1800d0b8503801150300704060614130340360322003800140c0e00d4680106003c14542800951640202c4101c0b00415200742d003000030b5842604503d45901848004100000100d01504071011103c2d0b5108050102008564041498000c03040c0c1020305200003544100b0100e900540d0800c80c0e04d41140409549a0b41c0307802031107121010704100c0600c0c0d9400726030100c2540e40040c106103207240c0c2c3c0d1010000d10f000e10500f820344007024410055608100d19003406100d10485888070700d40c901100205545031504032404501c00221450030340c480b000700d900d1075400410420340c50a814640040c107a1141048003040700761085d410022817007800303c1074440459100f0130006000349155000e071100c5081100301d95966180c00c2c4010780c001070640845005224010480440400b69a04034920344120384190f01d00c00d40004081c241e020340d13114680c44012 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 225749424 1250 225748174 225748181
    0xb150f0f0a03050708070c0309061101090b01030b01050a08010605031e1c0513090c0c080c16030b010911031e060109030206030f0f0108010b061c0b130207050705010c031b031101 78
    0x10704035900c0101e42c91070070502c000e00d20741000b00150100084c083c200b40c046038100d51140c0c19990b1a1034041d914504035a4014058008000003d081080daa03000200384600d030fa0403281600c0303007111311000066890301c000d401da80c1640115641608144118060b06242c260641841101e120540320038060051a0055501c0660781c1100410400940411940300100540e409040103000801100264900c001e04551900300001c2112500040384070056008000c0001d40820034594480c05a0720b070b2405441088017031107802c01003410a00000c250100740c1c0242d0744105104410029a007002d94060108040058007550600c03002010120150b116a401035104a0810050b001c0782d0424001a84034044140d1201b00c803a45081d0800c001607903404c0484171000b80300c1180c1d40006001c00942c600800803020f030315901418403407600c503044d080c50700038160303440c011707000e0f40d0340259103800544201c03812410007000145c5d1003404221701100403548070901070080c50108106400303a401c45085 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 225750674 1250 225749424 225749437
    0x402010c022706040203091c0203040801021602100509130b06040909030206040b060316050d080f190314010f050607050705031209041b14160c03240b150f0f 69
    0x900350107a03103000c201d4403403480e0b50030800540381107203141f404416403516070318421440103090b2840900203c1039032080080c9e501415100c4000c55a400480c2d035500010100804128020740980d0a0146401c1c050740a5414501015160750903140b804108507008204600c92a40c2c0600240300100301c0c58800e10690f15070501ca0780040c1800e091505003004501c1004140b58445d9100401c401c00c4200401e01c079100f281c0007a2460181043c46180041090060f01d03400d070f401100100e86e4081072902c0348980d0000c0441c5440401960a8075124124900340034007543c104a645218204030310304114008001c0c260007078095030300440c0c44000103424888405580030032039001240c05089440c16101e2040720622141c000051180b0b0020007820440f000200140d1100021660a02c40e009003c29060321507071051070054080d4030f0380740c05940f10040240310b00400d0200c4124445507007441c495010b60f03d0005090107280d654840940f0510791140d08070501080c3c0034420380c0c0b405e092070800342c240e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 225751924 1250 225750674 225750709
    0x50d020d021b060403090614160503041701050105030613060902090a150b1606090f0b16110c0f040b0303040b0d1a010212190c0206070302070e0106260402010c02 71
    0x3511000c1c90207075591002d0910301002142c00840c20303c400a030704403841038100c0d140c0c1d043c000d90395000c121160304203000d520141c102c580c4c3d020a910040180120090080d00c0f113480321071401c1e013408178400d4200c680134060350741c156006c8008603c0c40c03003a685207202039034030030381c2c0214541c15141e012500302e1700107031140d889550b110402031140c8030f58416130a002d004031000c641d060882a000d05001c1011140b4050034031541c56103484280964100e4141e50260041c00d0030400341441400d02c810083c06801210000d11080d851030780c40280801c0c0c61070002802400b041c86240c2820030400180441d51080c1d5151004000025104070204041c00c20715a48000000d08030100c168000c01c00600d0784c000328119041540300c0b4038403c045e4401d0b10401051200f014200441c07c10094030099511a0f01960083c8003150440c105640000d00800b5180c8203081d203445666601800c0e1500c2ca4050b4200754082210f00b000d401550b200300344254030900500d00018204200d4000c24011003003c4031012 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 225753174 1250 225751924 225751927
    0x5040e01050f0628020f0307200303130b0a0201050a0903021c110106332109080f091806011d0415031a07050f0301060e030a020a060c031101050c09060a050d020d02 72
    0x9080c1e43c0c051100582058041b0007841ca042402e41d40d1019114540b5016203050801030400b10068408000b50b4030031000c0403564132205030b01d0700c2060846401c90101400150300388000116000e03880e000300540c080d03040d0020030744030015022090044c08030b010807a007000180321000b41c900e03009005480c001c0c00c080e6843c2c0e401540f07041c1c40f15004507070b02c441c032561036240036950b070061640f2006090031090304980d441400c08404e01d501c009000c031494060901c1d41c0120703079042d10400e00390042c243c0c07681c00c40340008826818403e0000502d02103500a01141e4180046007244c00100c114a20004000704001820f4448000000311015681c10598208000500d61039007078212040d1641c102c04541426800c000f0381400c3c82219100500605003000101441d1a0550b102041140754240e4014000b541c03040c0c07038000003000007074501c1c016000984089003060003407106101d99402149419809442e003c07080c3c003800b04a90152200340304001041080b000d8003513062020b400d01001990015 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 225754424 1250 225753174 225753247
    0x120618050901020408070605070503070f1406070c05120703030605090106030c11010605060a120f050a0e070605090306060909100203040b0601030506040c09090b040f0e0705030d05040e01050f06 85
    0x2004498008148903410380c030410041c800041c001503454212000c2d860000d607200e180c0c0c5030160642c0200340000385000c580401c2c1100304548002c1030b0703419001150071a01a60703144d50301114540e10502c8040c20682000e000c5101a070240304c02845e441d0301031b040100d5007d646402042d0b1006090740900d0009a0364a560a9119800010400001200e4000344202400c010008001c0e20603003c00d442030203000105a0303080000c9401c441283e1022510400440c0790407080c200107045d0703c0c00d03420b2007802540e0000c120700d8000d0040e5a840c80000d0001c01056480398144581c00c00301410b048600e203e00119248101c14500056109500c6146081044c0c1805400903054440c064851403056040c200a8205141d00213105000c0341c44405010901c10404404580240300c0005440e584038104880d410740c00200054481c11034106030112041c846040608a585008038010004407001440c010061841c0038010000c03144d0340180128680820710410048900e0340c203120455840401c03540 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 225755674 1250 225754424 225754469
    0x50918060123010807021f0e0303070e01140f19090305030c0d08060f06030403082805060f0d0506070e1305070206070206010803041512090f03020a062004030201030c1206 75
    0x102d40c042502803c0c50151410207035800307900c6681c0440020780c482076543c04684200c0c1035030000b01968614405590740e1b070400c92030081140c140c42c20210f000c07031010700c502d20719034039460102c5054805a945072030078280f40e180c0d24208400f56400a000300b00c189400400800c4040c80203050b00e00c100f4004103140310680c14080e1400a00801c440c2c42491031403258041c40c2c0710030040340c6d849a81072800480035615401c0c00300040c0403a01074032458010380300c070250030102d8961081d800390a0484d60344002810b400100805a01141d000500300d4100d04003003080c1600072030004003503890003042080760181c601065804c0342c0f0226003420041e40007006011850760103000c1203001d88160f00185143c203051284803e0b401000741034840c1004507542d02214580c9240c3c0c0b085038003603405080010681e802e4200250398154098056405914004110081d130388186403181100b80384c4815241094a1038005400a00c06009010705009130081e251003194010320074623014003110900711340702c04003440380c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 225756924 1250 225755674 225755729
    0x3080a08010e0c03040807080a230717031515070614160c020603010501110a150c020609010618020d020903010c2102031005090711010203070503160e0a0509180601 72
    0x81c0301c1401e00f00b0003e1101040740e540c1110308154122148941d10b94038100229103c05c1030000010001000400300c4040491400c010140c0e1790184500c0e0b1071141211444400314071007696a82c15071080d10442e4400d60410400c2c0c1c0d8091407000b8000b50a000060f00d0360b000341c4400220885400e000d1a04001d044000c1c0524107640895615204008299070360201d945844180545d81c103200c9010402c91030400c040040031000382e030003010712500f40c040c041164050002200a2400740c0150b01c0050a400340510414080700c66090f8500c45084035142e8860096000b0a0040383c6d040d000c00c12000652001d010307482d5942a0360380c9400300d43d8100c0000c903454400050060140d54010000c2c041d040048500e0f550940f82e0031904403010391214070043c0c9100c3c542881144155002200b0400c1213500007028610036001e0140704410b0b40041a0100d0300141c00c05815540141501d0782800a4205801610b07070203000c4c0700c0149943c080c102f23481450a08260300c1142145003111074003201d034000e40c1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 225758174 1250 225756924 225756931
    0x10150215010b0304020f060d020904110406140307120b0406152a05060a05181c0905151204020102010b1210060503031201060309030201091a09070f0b0409090c03080a08010e 76
    0x2c00740d00314289a400644aa860058210f101340d01c08035200e01404d01c19411070b000c0c8107006100f04075003240385020b00072036089840781c9004141c00c03040c000c050300c0c1900100c034031400d542c0d610b19003034101c046401d0b030060a00052481d0081d40d15000403030720903c8045070340700d441550386486020a5040001c03600700c002d070785190107886544001800008800203082600604480401320382980e0790500102c9410801080c4015481a00380c05000c1c1920803050340e038060303503d030b540c00c55907038480c414800c101c281d038071984041d00350411100c40508052a0140d42040c07051001161115052000a0801d11f00100740406034000500070460180148680001440190069801c000210b03d00c21100101403080b003003416220f40010040500c00c3d880f02d0159070b80807280105030080802c008034028030481b01300409100307150010807c02510400c01d0301700c400c0090100d00c0d10381405081d8014080407103085615030000e403c040002011900a801c10300c00e6540ca0000d25071615051003c0182d019 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 225759424 1250 225758174 225758189
    0x519020102130e090c0603040b1603020f03040b18031801031503050322050402040b040303030b0a08060c0703021005130c0e010501020a02060c0a0507091e060b0702091015021501 78
    0x10440200015600d160b0a001c890101e80081c42c2562000000c0e410444600d008580c4102c000082004110500b224940101c00342c042d220101d00100c1c200760100e118048400f00d454000384001400100c80c1d441d800d0344514402640140d9286508205265070030801000214402c0030a480c030a80d41d0501c1404001d66010455864007440c5403210ba480b03105003181c0e84804a151080c003d04d900d24540900d00401015004540c0c03076907502010a12500f050208400082c1010201102c0e490002403481c141c9401c1c00140c5040e4403030714003220301680103120403021340c0100391860024208501c640c0b407040050700800c3c000c03000e452038124070407452508014080c981c803c0042c061640d001035520007990381611156a20307200865443c1c94040401c0e8003e0030b91050002c00b1504070709a0f0407204040e1070882c10307031940b00c115846000a5800c9402482030441040c8105000351030a0302c2c08541001e40c5c3e5000400d455207444940d004501c4554a82d805071b40300d500c0a03614214854000c83c01031049 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 225760674 1250 225759424 225759427
    0x1a0f0609150a05040f060302070b0a050f24041d1c050a0315030b09010c0801050d08090f0607051b09160e010c08090d11031501060c120315060519020102 67
    0x310340001c01e82012041104020707500490024407440c0188110f401400c03035400b0400c04940c0d2008010003a41c01118102c8a0b00904030200d031020a207402500c3c0a40c0031100d00c98103540d102030b0008013282d04014446404280303109005507a481d24450110300658210812150200c0140780b0380ca0a10752560030078202d02c07a5a5003850f49139000003603e4a03c10725140c04070f4010100c050354100e00d08142c1010742200c0c010340c14000031010552200c001155117450b0380e482a83d0703402c10850340780000d40d40a4460709081140d42090f00d810039103e000c02100030460750426545403980c91030891203165200604400c5040328007145404216503510041d001c0a01061090309640141600600b00d109030500c01c01620301c8040001d210250703400034902410814000ca4982428a48a40800c603018000e00881810000400e000c00c02281a03035110b80358901500c0345662254004802824003400301540d641c525506480c02b80350000003000300d55070325600c9014005040c0101c44c0746030040001e5a20 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 225761924 1250 225760674 225760687
    0x21030a0e030c1005101d060310180303201617040501090308030604060b3609072006160809010509190510050109090c0b030106140c0f011a0f06 63
    0x243c4040c05208560040350503107a0807410281442c2c103400c203802000031450f40f89011600740d0940d510900044044a644c07904030704d100c0c0b04848086480742c00b01c10700d0080c45004203020750085004000c134035020321011003a100d80426650003e48100f070b04040307102090001e1060b6000044684142c488125140c246440300180c0f010740715110040001c20b0220005980ea07075154000c0004114204046a4400c0c40d80f9103240c8841101d01070381401c0c420300086243d05075482601c0d80580f00d01810b403240c00d84490809036054a40715000b0205004c0c14111310040100c11b01c640c9008400500e44a01c8908180304080d180d1100203003182a16032400701004070029001401c4501d40c505d844c100200303d030842c140181810301c001d2138180704a04280000a8181c0142d000c001e00d240154000050340d6240d00240e015844213104080010341c1101c0c407600c450b19004014404240780c401214200140300300510b0030740b022030101c9010b5680e07030700c03481609060000e405450302c84200c500921700007 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 225763174 1250 225761924 225761947
    0xa050102120c0309030a260f03070305070203070c060305100905041a040c030c18180c0b0307030609060b0309010e0706050901031a04090f02100e06030406020a0c0203030c0105041b080c040b0321030a0e03 89
    0x40213288ac020581c0707c50100701d1043c024011917000036000140444400e40390359019010304810b8070685c84515003582c0001d0b00c880706129460080d41d110207a04200802a80d0404403620040c0055800510303030038001000540c2603080400529030700010a044a4003002054110343c00140c610a501c40c003a12924000380006000d641900c10303100d0f46684980300c1400450052a0940040310780038039150300841c2038103202000c0c500c01d00f00320300240032040c9202110b07601ca020038810740d00868414000d82e00302d0345c043c3d00320111004100b0103512125299900141c15a8149801510700034004404001542403255050107100301c141410050400d410010a0307040c1300092010380960341c04181a54141e1046141407031564004080b26162240803608900034101034604589000402904c02d141000d00d0042c4812100c502002c2c024003011034080c04054800340b0703a1a40c3c540034844440c0d5008104040c091481580d8580b1035842c2e141c41084142103502248010105610a20110302d80c0d2 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 225764424 1250 225763174 225763177
    0x4060b0a0215040303110f0309060c19111c0c020a05150706050618160e0a0302090a0519050a06030302060c0424120f1a0a050102120c0309030a260f 65
    0x100c62000b030300d9655003400c4004080422580500d040e001840b400351030307440c1002e036000308a9a420303120340d52200b182d02c3e8003a00c039039080c84510841040300340744010701449403040600d02002c02e50300042020040d000002d5040e18568004c03d203005106015410444542d40c007038141610303c1031441400c160500400c0c000e07014024a07554032680020010745400e42041d4008521a01e2a011410300c10816610300d0740c0098034500180504050544604d403606107241200e40240c010b110640328040c9180c05010014950042506500c2511885560300c0c0f06084c030810324502e00060890440c40c00a0402c1c50150035917030a10b02c24081880a65004035155100e03007003009501c4002403c0c190306482c040c5034240a40140c0303141c000006c844c1000e64000490000800e640c82d100d24049100304996403891707000f458016840450381c0b00d110210800142400c2d0001000c4a040c0003030303c3c2c0003031328000c14100201c807040c504116191001074210ba44d80d000001000143e82411401444031100b17 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 225765674 1250 225764424 225764443
    0x40513210206190f060b030f0a0203040b0a0f0207050a08041703090f10020f0d120e06130615030f05211c090213021914090105070b100503070f0504060b0a02 69
    0xf101103520105919009640c4403032220100311000384030603079a481c2c0390a200d800403102e80c01940d610030300242d2480100d01c00c49103d2a0321030714403016a01d0764420f0350001c0c800007c501c442c0d071303070701300075843c0890400c00c94044031074030a100c4980d40301c1c201281c4850710901c0d8aa1551181c0c001d1100c0c44813540e91281e0795031a180305446640807083c803034604914129038041000800d004910210305075a52295180707400c17541c460800e119180f4000e100940da00c1c4200ca5441203000020000b50004507960000c202c0f0708410240101c46940300c1d26042c2c070f0000034110880e00c503400910102c000c181120011030900d0401d40034070b424283d299a107580c0028000d40201246650303065814210358a619481ca1418500c0004540300d07d080707084994010224940040400c0017032034645000710002040703a0b03070900180c0d50303542000c4007507642c060200005000c0900e0b00011000100d46030f02c0c1040383e0780080810250002c0c940d4905000d01c8111900c1350030071100c540d4208248040d017500081c1001e031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 225766924 1250 225765674 225765691
    0x1f0501020c060a0c0803070c020f1804020f03030408011409010f06030f03080a0f0216110906010504120606080102030f150a0e01150c06020c160509160f0e040513210206 74
    0x81c0d98000a5084820313a4803d01c004012400120900034070b6580f226044800c10710030b480010310103640c1401c2150030b8070184481d8001c4018280000c00500780140e02d00300c1c0504c080d00716420162a108542d094880d84055040402ca8110400481b13072000d008541300c145100004100c41da055407a4141d12029105014041c086c00e4004610060440d03440b0000000c0c803440e045440e594041c0320151601c15214050360141d14807020888217280001b1400d004560503107079030f4034183c0761800d11000c10700780e0361042d41c5442e59950001403c40003130006511492421000d002c1924200f80000c00f903076a01c0e841e4a0149070204801d101e0303890f868404605495985082c0f4908490262080300c1c0929841002042140045554003203201c00240c140b0541c400b020b181d500864480041c8104510100c84103a0b8600f0409501c606560081c064046065264904500b0080c9031501150503900c05076100c00310104540241c10900c142800300c011486041200c038140304180c044003d5075804060f1001700d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 225768174 1250 225766924 225766927
    0xc0c0d050c04050411280512010e060703020909010f050d02060904180302012c1c1808330402010311040e15240a051e0d051f0501020c06 60
    0x1010301000708400074400d4002803091049241510700300041c2c0741c480764a070b40a82ea0500c0d109050f0b09002d0030882183c104a0400e03a03905107010100a101c08407040017034995540d030503081240c000c00b40610b034400c1c0e10586003d6510412241800014107050748481040f6183c0001031245945102203401c002d50101d4445031104240c000150003091420340740d13009064002c140100305501908040f0301100742c010004002da084190340b019001c5603104080c215002035200079064110300c0280d1031400340760311f032912607101e5141e207540c040110b54001c41c1055000c4c000001d950781e458018001104003240002c50310100380c8011035034207400600001d05158580c50f40c800001c0e2280d0550303000340800602c0c242103007492240341c0c1000700b140041900914828800000d016120b11071480c0c0540c44409882c41d26505050496003074001190300e40400c01140b040002040243c2c0c043d1000d44a43c0e03200013000c0c204046021281c0b01c41d03282e03403007082c00e41d44002c008580e000719400c0c82004040e07a00e01e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 225769424 1250 225768174 225768199
    0x306090a08090609040f15051918020903061312261909030908190803010611160602010f140c070320250902131503090203060a0b090109020c0c 63
    0x2c800b40107019003117810914103500d001051442d038005240099800c2d10a50f28540c4a03420b1003806284c0e4018810f48800103101080440c101850390414800041801801d2185403000242080d409807106120110302030b015800b0300203420400c0c400c0e001c4505146440030720031103071058080100160030a003c024600040d602200410726400b601c0c0e40c51108100c41001464050030510340380c0121041842103d107450038040e172a150b45150660008038143c210385c40c2c900e04498046210720700801e1409840c00c00701d100351070381e010b00000c1d18140c0c00118008550f500a5011249010300c0c646e03c01c00c0800506c110607a400c41228810303a01407900825110502c582d940d05607031503008280640c4a640b6050707101215076003003003040360304004e01c0c5c9254a84c0d81a8200c01c0c2d00410340384403074074109103c0401c0704107000c0c80e00d10608045030a02080c0c2c0d0283e900040e00f403800413190012920b0b141c11002c1e0191400c80701c0f05001d803015240460034213940151503561100d004142c1c40c015221040807 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 225770674 1250 225769424 225769429
    0x90e07150f0c080a030603050606040606020312100305070e041203150b0d110c011409030c0712240209030c010203040b030a0207021c03020d030b10210e070b090f0306090a0809 77
    0x2c04902d50340000310213680d0440d89500030020001481b05640b11300503100070480924003401198212015070f40194102a40c2001032030010b00007811112100a00000c0000060003d0080000802c401c01038200d40e4070789420f00107008442c118502042614040244140000715042901a259080c0ca070341e03110485912080024030ba041c0c036180b1410000708142c541e0001c15000106003060000c001c2d802c4da1544100c031030350380c09080303603c00b003940040009002d80c0c1c41c21207242103064043c0b0b690406400c881130509140650114a4181a0313400140d20403036403c4c1005403d041200a200440c54503240842880580c00090520480d05400040300015076071180742007a9a2800001c201c0084500d82c58040e54866020320710b5000b083c20540780703180301c3c40c064a845408200c00d071941c204000d01e002c0079a4102c0503101c6210b0b62941d440007480d40700401044284c0181a25000c20fa588035040c0f0b042142d004030300761400740f0070f6008008102c1c01c030101082d030814269110150300d0b21035242000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 225771924 1250 225770674 225770687
    0x90106120602090a0806100306051b07030908060603070f030b06060f130519180903031506090e09070b1b0a0215070b0604050601050a0503060a050901030507090e07150f 74
    0x469168441490100303401c1c848150300400c1146800c031400c1c40302c15a2072150648503c0111030030203000d944583d040010038001e030880ca43c407550080041c0081121603400006a401804040e80040c6400d9001c0c81400020031055030072200480040004a180003030946000c410717400020050103c2c0d10209641e074950806032822030031451915074940c2009030300c0c48261805880f40500c102100d075603540c45148081480c4040d00e0740f003182d03100b030a004000780384050a23404204030304140d50340000c104d501c1c080000041c00f500c665070b00c0103803603031812800d41280200903140c1907803500058410818400b000302114000c0d04103d03d0000040d1000210324184608241c0180d0815000500101c085000b0380040024901c2640700d903001d5100e00007880112402240c0c614007080d420414452014041c038007030350744036070020525000740ba01c460102d07400c1d1400f80c0c4100c0e40b44e4400c8034284180001801140580d507000c1c0001d01d8100d19011140100f0b010410a140a0280c0c18200c01c4802e8032504 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 225773174 1250 225771924 225771929
    0x3150618061c060501080118050403020a080408010b09090609031905041d2202100c020607050d0c1e1208040204020c0f0f16081203060303071e020a0e04031205090106 73
    0x40806456202c15089001005820955148428a050000301d00d035030040c200c1c14161074400000e03025901405000500404018100341c0551042d00301850001c1d8444000300003800c00c00002150251114050120490300602001c40907080001080340320540003084d14042c0c689004c1c00d0b0717450a511002a145480355800c4400c81d540c201610881c10340807801d03194029515080d0481400503a203108240034011020000d50000030313211414052842201d5160b44280020926403618600da075a403850b01080d00055804612225144070520103800d60325000004804030300780c2d010302c9a944461011110308401c0046c8081c4134041000d40d240da5058135146c40038281101c1c0c0d0000384200b980e94840b400c000c41c40f5984241030000c503202410024400445032580000c0041d14094001c101d02034100602c01a05440240100008a150000304404071301960b60900c0100505005110501606070000d03407101c019001030200081e4000311072107000d401d12000203030540790701058a02600259 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 225774424 1250 225773174 225773179
    0x20f0906130e34020703142d0c01090e0c071a0a060f050105130b07060e0303040305030f1b0a180f03080309160b07081303080406030f0605040203150618 67
    0x301040301280c042c0140300f41d403a9040c407080210400b5504a404420825100f240040e0410301c01000000c0c07151200b0f1404089240503a00540b41c04e03200c48d2203c01ca4000104401900d90000ea40c4900e418040f0307502405c0207280c400c60b458101840104010006007100c024040c000130000f050160181c020b8041c1403480480816078106550340c84050708083c0903c1260054004000502d036014900711091445010400c00f901407074036039465800e42103001c00340d8085850f281030780c0318100184020b6214901c291103213526420002d542d90025100100442e06084000c40e010740c0f1155a10243c0c0c032040c0c2d9901e030081460414206a031081442d950141e01c4501c0302503408020441140302840c0304000b000200c40303d42d9039100401d003887c0c8252040da00b41a80c20850324010802000061121917100d0307000400031541c940e140d940035030066000400080e40c1d068040908a242e0040c0e00042004603010360440c14070000103d04c21805a450900c114000940c0840401a00b844111ba10100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 225775674 1250 225774424 225774449
    0x3090c0d14010501061d040902060702041b09050409030c0204051806010609031406060904141c03050601030b0301050f060d0c030c090914070b030402060703120c0201020c10020f090613 81
    0x524160700508041088901c042d424140003103086841368090f1086501e404101d48229040c410902004140d581c0090760401d00411a4102684641c0242880b01c1d40542840701c000d40300c508000c0c00c1c0d0603e0341119204a051a441601080c1d1103074158000340d804580020b21174480500f58054503110b61103400711405a4000003c1458001c03516100712030040d500760307940103503003001d4a0302e03000d00301c0300d603a130003400000420045980039a85c0c802c003107460000c490b084501e18882580d4412100303000000640c484040000c1d035645400743d2501c864003600203028900b13002680d40700d4014000d0500d80503100c520042d10500c610214607038015600080c111012584903d440406040b08030300994028403c0c0201140141e00068254107d500751808142151555400c200060344000000e404004504950700036401651142048400d03a907000169110000040a4100f0001c0102000c0e0310b4814040c2620000b1220202d503219081200c1d03495907000d51070544d022100d400d4200c080520603 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 225776924 1250 225775674 225775699
    0x18030b07090e2517100f0504091205090103091502030417040602030f07081b0f06010902040605180301060315090b061c02010f1e2609030f03090c 64
    0x84280060040409a444414042d2550700500c01c0e02c1096031540401c6109000d410b295031040d41c007800b103000f4103140c000c1101452510342d460158055030703a0700001c040030380c040041544503d41e52004050a84d010f0000014948404c550341c4d08400140003030101c00510100580c1c46503020746001903000801c5819000084070444c029041142c04440340c070f8900c0b003c01c00c800c3d2800e091b40e0450b051540254501000310310381040503000080111002c4109121003801500480c4081d60049c0c0704000414445020101c2180340007010b0b403005207210300c100008c0c0b20495000d400c0b51281c1058004c01d0b00344800f442c000c0313401800740c0e0b48040c00c2400071a20403011884a9080040c8450042c9050a0707252125010003400d10084801001c2001d17004803500c00650240c0c640094105e150b0403d260001e5150329882d41100641d501c82001441100412480381c0d01030f440d0012542c141d41c0d684140d454110742d0079540740301d5405040201c0300c0120004866210030001c070062180f01070310030581d182 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 225778174 1250 225776924 225776933
    0x3010e06010923070c150e0303040201020c120a020f0a09020f04140907050a03091502040803280c15060f0306140a09030917071a03041202160b09011803 67
    0x402030003002e03071980c1070815401680d0545094141103d41803455107031a900e40e40303400d80303003241035030381c1202c004040d200a402084080d204940c001c01d8440f010355074034036107880028100380c80302e01034901c2000e00079244016641d0002c1c84041c4036a05075a030404145115002540c55030301548801d855600000d0700b803104810080103001190b040d82903506440345003c00b002044441211110005002440309243d1184280c2008440d41e00802e02005940040e1003050182d91080d0811003199000040c860500b4664060740c1c60440f01c43ca01006543c04403100040080c41d02c488081c040c00c108040e2161048000d82c00000240006001d1541440d1b40c0d1901c0e1012700704240c603003c0621400c0e400103000020f02c0c0a2031551542c1a0f0707d882c0d5107030400c1c804550040840300403000178842c0240202e40c01d0204400752105c00c1038441c80b00e4032442d0500d0711038000501c0c4903000046400240140c6803200300c0c0001b0f082075410140c0044e85032100038004881500101038003c3c00401e143c0f00010900 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 225779424 1250 225778174 225778183
    0x50f1801030c03021f0813230c0109050603060913051005011805180a0305310e160c0312091b09110406090e07140d0614150304030809030903010e 64
    0x41384280c0d074451500c000344d4011034190741c4514401d4003050b0351030002041245c582d80301314106407180b819900213804660501c16041982c1251070441c0e071000600e40090b60300020014010042141e20501c2e500c0c10b41e01007401440c000c0c00d501c0c901c42e03c050312041001421f000005034003000c010f08208a41e5901e85007c42d004c6105200c0548034a068040b070901404400035070300000c2c51500a06013034481c0e41d8200c805a10401c1505080810544410400c6410083c03070444080b01081c41401c05003010b480c050304000282107540b819450b800b6091072690403407050a203041d05418032141f00c0c1503a03403003800905180c1e07138018010481c4003c0c0c1c140013100c42082d0000e5841e603410800105042c144500000c2c840d90080c10041044080204981455100344907070103089850888090f03079000000310070344c0c1c03c01d0200f40d01180d00c46e0344c00e000c504158450401c10250446820600111107108141a440064405070400040c0c44c00140310481c10070448034141400740c020480440241c0c030807501c5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 225780674 1250 225779424 225779429
    0x90f010908100912030c020c0f01050c1b0a06050a02060c0304050a0c03080715061a0c010608070305030d0f0203071b05070302060f1b0604020109061b020607060609050601031104050f1801030c 84
    0x40000c45894184a5101b40325010116905030018480c40c3d00c49410030800040081b0b0300703410014200b0150200300001d02a684500252003840642483d0000030000f100100341c00a03c03c2040c00d0088a00856000030302d0398100c2c0c080540c8940d00e40380c03030078614100350000b40c000d458481d1810001082000704030061105c24000c140c1c100704005482c2100301991800c1c868856100c401d013403504106015000200b0510b10048000076a80740da41040e0b90401102c0e40c420f551075000840c92544109060068514814080d03104501e1440c10348005400c1e09640410020000c111072a94800c09c80100a0701001c0e5400a1410b9158010303800c000f6201d500510504881c03044c0a4003000c0790150004051340180c0d4140c4402c0402810040c048440741100d001c8442c84018203240540542c640f2001040d10b103004e00c3c000f01d2007904040c01007080d14005420141094580712103050f840820406660a4071400c5840d00701104080001494804a0705400122500010000010800700141e050304 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 225781924 1250 225780674 225780683
    0x1308040e060f0a080304090b0315070801050102120a120b0d1b1a041404020a021c09170d1710090204090504051536010509010b120111090f0109081009 66
    0x600d20401d003c1c030001e0051403040a20b160300c1848144000c1c00300c0c3c0c0103e07200303242c044c007141d43c10f80e80482000310014090710054080340c42da00041c0019681881201a04414012030f9403074600750703072030080521012801041644d40d54014941e02603482160005401d50400c4a15090849291120740800f01a10500031001015031655019011b12001e88013140d6503411411030043c20360003800040d61101d4400400c5005040c0d403428180b41d25042d03403140940699421403110709044041d12001c400c2b5000b4510b40e4000414500520740c4000d502d1240794441d18a020780b5114021300c190340f82c116030440226180040f07008281000280c1c0194030550188086032414423a80c294415940405ea510300c3d050014414503168803401c228000c0b41c40c0b40100c10019240100c4004142168000e80c1c5800070b903511040d403400107107003070141d031102400b030103000304220f099450001c8054401e0503146805464002c160502c503a000300d03445e4000b0010401640e2041c03003803000c60b40051004110846 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 225783174 1250 225781924 225781939
    0x10605011d040504060608030a0507020f0a051003111c1b050a05070b04050c06030a0504021f0c0605092d011103010312030b19120c050d0b0106081308040e06 69
    0x60561158403044840c0c096080445001e50108060002401000b08195080c6403545000181f500013080100031402180d602c00e500c0306050f20401c056401e100800034801c402d015014031650340c6d41408518006100e0400040049024110700c4440c0255482113900220000b02103010b024142c014401c0d0006180640d0b150345000981a40c0e14024411003600042702408004c2c0002c1110300c0b41034105e4041d0b8101c03941c850a581c00240350394022100c0004003900c400070f010071400d041001051910b86100b808404800d0308200800030300ca0f403140500020340310000300d000d01c101403101040c01403441e100c0714070355244010660403489842c3c0201c0803a6180c49030f0310341000248000d40303041c3c1c0d130301482108481c0311554040300585907401855a111a03200d44001042811040800042216186007414003103182840c2e0802052a071006014a0200002c44009022040c0301415101141440c42040d110100c4010038142050b100034030b100c80000d804510340c03180400c5148903400444801 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 225784424 1250 225783174 225783179
    0xd02070e09011503140a020301022703010e0c040c110703050f0f0c0a05010309081b0c010f020a0b0f090304030b04061b0f020a02130209030114040b10030b010501081b0c0706020106 79
    0x107500300c8002a20001008694240910015a81d0107004d05d03d07080e040b0440e13008a006030001390881c9c5c80783c5081840d108200d00003031400340c286019007601141c11002004000803c85100f91507a000d80c00d40c038840c681c5d40f5003505c0102c0c020840ca120205030030040300c101d280c40746012561040701c150240920710400c1384003508802d0001d0303034807420507000d00003c0c0b40d00c1c070b840b00540190420031021240840203214032110800b00041c0741184112075002818003108039800034120180b428661021504002207800209503210b40d119046208441441090340c0d07409507007410342c001c58100130300051381501440240010b50300103541c00221411110010010528166100000c400d4224090f810940e40b510151900908417980014036410240c0f0302118240020f0844050072811180310072507000340801c0c482c0400ca8142d0003822800d508980c82e00310b4580c02400e5005105490400032480005070517000c1d03810b044080d1000c4130b5182921103014004a94945509010ba400190301e0300200 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 225785674 1250 225784424 225784441
    0x109110108012102131b020a06050a0c051605190c090b1206190612140613050304030816080c0a0209091f0207020303040f030309031a04080901030207060e0d02070e 72
    0x1441d8402c41d203c082040f08019401d2060880d1a0072400340420307a600d802d503074400300c1a03440c941c011215601400035914140303000021210040c201e44440c500d002071566505030040202c40828494010503446020310f480d10b40d180140003004c1039440c244c9411100b041100040310501a1421200103100040744041030159001e00b840d840302c2c0341c1d80b1602c041000c100d10040341209007100c088000c070302c240e12140680b43d0340c5060070044581925071100c0001720001489441d40003104902064081d0303520f42c0300d55175240100d020244c40d5040010b040038200180e00709000380d603640b18200f20b40320307404407031800d40703a800c81501a0b000381442400902480d50200d2500000561441c580210004c0708802070002c0d00560340490f0103100170000401c65885170103224009600c030356108011790303003581341c00004501d0f210742c02c020000070b00302840b0019103a03d06403032159900b0310f40143c6401e8503040201c090702c0e19611080c0c1601502e00044130380c40d408220101030b1801c010ba00e00740b070780700c2284 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 225786924 1250 225785674 225785699
    0x20a0801081023090a02100c03020105010b040f1e030b13140607020304142e200604020405040807060f1a1903020f0a0e09210306030726010911010801 66
    0x1c0f50f001c0c8240d0a2424540d40c0d0020310740540241503001100d03c10845580032403120600d4840c120080740e417048001c000c155090081c0c90250414000c9141010302c2c0408031280840316006420040741440310a8407482221016940210f41043c10050035040050701c081c09074072440d0058400c00a10210b500c0c0e00030f000523180b40120b5450f4011441c240ca44001c442e0943d210340710007584180c0090010803101030b40e4501303500d0500740d4601040080e00d180d101400740b4650510b5210102da01f4025000e803070501103980b592058041e03401107490f90319864100040d126100c002000540380643e40b1440d075030355030b1100041c10b09069030303c0215204d00f82040903d04000289081030b000c1c0c07480c14001410125480240c000c00581002542a1202401e006071501120480c040b680007440d03001c0892032203581302003a00034140105203182440c03404240c560f0780c1c0d0f00a4944081101b2142d0b00c000314800300d45a1000300c0b0400820508120707180c80d600d24044081a54000380a15002140035214000c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 225788174 1250 225786924 225786941
    0x605041802180703060e150103051b0a08060f03300c0303060409060209090711150108030909150a0608190501050120011d03091311070212030904020a08010810 70
    0x20415000040c084210450100004000f0030030151140740004080780d005070800d0003808981c500c68014285e2800040c100c2d400100001240502c044409010844444c1242c070749080318900302ca030540d903100219a50050b11003020b034051150f00110b44c00c0c40101d0711202a02c4603920302c45043c0495100d0809d00c54041c025100c80203800400c0410310030b02d0280d02c41c1d61224810350b00941450a828001041034404880450210b8845c0310202080c080c140402c0c61441100992070b1085d50424102541e01e00038007034030794018501d104c04034050410041006000001c01448441d107031f6100d2000522503441030f24105034a00d42002e5840c0c9000850040c43e0503590107940f0131460255410803200359501086200c03410755610302da0303072010079aa0800303082c0c02c1421200850b921300c0c000b0144415040d905101c5038500346050505001c1208110403618001e404880820800c8420741b032013403c61046c4002554071610005041003200d403c40001c81c104c80858007034503202e201c5c03120704500343e07042d80c0c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 225789424 1250 225788174 225788179
    0x2417190b090108152208210f070f0c02060a050a32031801060603050613050f070507020604090617190b01050103050c1b010e0f150402090c0c0601090605041802 70
    0x40c0345210204020381c80b443d910101180802000701c00483c946001740c03400e80340035660f403100014600007800802d00624904000e00000002618040135801c1040002820000400840c51803032403419109048a01801c2d40090405580302403010001c3c00342e070311118580002c0f40c84240f120050300720008281c805015401c07111003d285070040c4000150b8030041c6070181048035504980110390302482180054050b03610f00103054140303082086412103004036084826400d0100b00041ca003451b2400320381010031410800e07100c00d800d1000071840d000f2074000030003842c41c1110000c1c901441030054160302414000742c0700c000720380880d241c0312614040c1014000701d82900040102e03520917404941d201c0101a41f4504010007030b910308448111202e80d05200fa9101c8600c0c0c102c203c410300100c1c0300c0c0d40300304008201e14108400003c8000c100140061310851100b00052407150114080702c0303000b09010281c640560316400ca1074001c010600035640078910f89510200d000c2c0c8000100d04106400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 225790674 1250 225789424 225789433
    0x1906080402120c09090d090b070b041221060f0e04050d0e0612090105041101090305120a050403020409060603200a12030306031a07020d03020a0819060801021209060f012417190b090108 81
    0x31a1165051002481e840701c04014500c12402c003008011040400d50182503400801d033b407850201d02c194a84141d810512010100d4800d0000180c4006406041c440341c134103000f600e40800f5400a81c443c043c1ca00118002004102000703100300d4194411403045108000000901d40e2203001143c80601d503010040007030780507103828000d050001026242c80446403030100d29180d2203a0204003071340c000c140200c40141e01d178042802000340a0011a0448510040307a5a00042c41c200041d0f121015109003000d081c2c078000b2000c20701d8440c2c0c00c0740700510382001c1d049012045a040e086944101107942c003006005410900409500c44c0c0221100600b00755100107135030300c4503400c01104100602d5a09203907035440c40002aa6102070018000000510114446500c1c0032041c050410318010b0007020150402c10060107681014004003024080c285411144522800825245481116040030002c500002001080690001d40054005002d502071110114000a00c40c94010038080d90803203410 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 225791924 1250 225790674 225790681
    0x112502010c0b0903071203020c0d0e0307140406030b010b0a111501031e05010c02100605040b1810050310050601110c030309130b04020a0e1906080402120c09090d090b070b 75
    0x40c0301c2c0c20300d500075840d001070701d292101944c2c8525220350140d62220200380c001c86c0c541d12115050110710030910b66802e1411014890350002a240c1140d4000d9900d9001d400c5a0b80b805a1103030b60109010b55071080d0035002c2075865408200c010380040c0302140004024060340c403244040422071900e403c1c00900c0c0c0184690840d51041031118010311064103103070301c4007007200c00708409000b070103261403180e001740035285a0403510340140d030f406030080c601a40c10105000f5280e00c940030a91071010b400800910291543d001c1603c208401d607105a60600c0782c1c01c010001d52160794421401140d00341c88a0150b00c00e01150f003030b281c82540301c00a50581007401104441c0c10b014550321f80002c7c1481000890f0340d400e10010b001c07604030300c680100144000414000508140c1d155400940c08074481141d030510b0107030003e225240044c0003e00582c450400746000100030801316803020001000d00300e141c034250501a036115507264004000664031440000c01d00304000c216602140c1190004401b44e8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 225793174 1250 225791924 225791933
    0x4080a030f030f1401080c090103050601060507030507050601060203090f0f010f180807080c01080c120705090a0305061503060a0902030303040605100e0c0d061431112502010c 77
    0x40d441c01d120000e0503200c10225562150302d1294030508111002d0b0383c091941421900c614040740c1c420406e000c1c0c0000001030011030740024003e41103d04c145006a562102440c003200c0500401000502a10503400003058603600480a007140b407078183c480f9400003038204c0412824800c132540303083c04a4040d5008103d014418010080106090301500010310340d00c545062901d121540115010b8020302036441c01584d0200c0c03000c2c0c00486104005c1d003440a41c54100000307000152a0030700303004000405a0a0b9100e440c2034070010f54015068030114a000c844d458000c28160000320700c240140e47c0000d882101e036110703824502c0d070042d00850071a41c4540e075501c01803070003400070888030306582d00c0000d8800c43c14202c54482c60100311002d460313144801e0201d040d01e00700e810030041020200c0c0c0700700071512810003201c55a8610840300d2405040c0c401e40c5001c9600b840c050f030541034108142e01c055a030540009003403404200b0f02840440000049541890300701000090001c0c1c2c45111800208 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 225794424 1250 225793174 225793187
    0x209010e13020408150a0e010504020a12060f02040b130e010f090f09060c020d0908010b0d06021305030102130602070b130b030406020f0a080a0b121e01020403020402040e01180204080a03 82
    0x7407052180052030b0035160310071540340840680554805100e140700304a001c502030301030300105010a00007400f40e41815400103100d060140503c0304010328003800c400c240b001d241c12489210082a00455a8948499000709154001200310070034819815000a81200c4100e2440c120340c41c0410540365907081c640488090040c0c41a100d02103a15150380c040420070500c200f00407080c3c160014144e000d174201000c1e00c40398850b440348070070364900bc00c124025100d8840c1c03403204d2984100d00582c2c800b041420381c408800c15421035034040d0301c0801c100046c440000c0c034080030303114540c00700d540e10f940d508107040c202d11886c080c00c2044080110b0820400340b201c9c0155810a00c40d00025042c00c070b81d001d5802140d00f021440c103000035000700502644910510604c2e04001c01a01c06135041d81400c1d82d01a52181034044da920700304602c155200b02c1c1d090a506840295500038000c0d540c2e5659005100c581003c28040d2444030400a206d44440070340303e03c02c8600300c51040b00502843c0ea920788042d2a070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 225795674 1250 225794424 225794449
    0x90709030b0705130f090b1206070804060f020706110d110906040b07030c08070305030604060e1506090d08030f04050706020604030c0f030903020909070f0803210411090c0910030209010e 82
    0x94810800010402170f00141a0b107001e4821110006405900c140c01c0240b00900103501d0f0295400030380c03d00c0041343c2d1106980b64090b405c4000400c170465204042c0780248281e00014181c5454a288002c200b00e0315002082144141c68091001000e501c1200e00c4e503100f03e220031588100208001c01c1a804c01d540034152060007401d1540c1110303107548a000316075000d61021400140f001040284a01c1c09105e100c02502d121a10603c00d0716082c107400601c80b040e1254a40701d800041010b40b0300340c0d5a5081e08000651040b180b54403400e10a900c09030502003a14100e449000d01e000201d11148005900e62050f90141c0d191082d0b8034540d22801c2401280d040d040d420030054900100140e20b80c00255801441018010404640b914641c004400400d40044005400421090802044070800e5002c9458010145202b0b510381d0f1030046d0007000e41d145180d401440c08070821181810010280c0043c2c8025190490305c0303070161004804034071440b2003460210391280e081000d0f03030800d010000359 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 225796924 1250 225795674 225795697
    0x19020d02030c0a0b09120406050702031c0c020409050c03010606120501050d02030d030f150314010e01050106120225050a1b180b0307030507092301050a050105070f020406090902090709030b0705 85
    0x11b825100501141580302e81c0008011400000743d200460508004801060515a032101d503503000c0380703000405051b58158080c0c42203403a07070200d40a02400f40f180c000e00003001002040035580d254800b801c0b40d0103140828000d0351400c4000501c50070b104044a19040c1c1c010f001c1c0207950071604041c0c00611120003002e40f01540d4414000c04942d91406d0607014500640a03012220f803001c1c0c210707003903d000304c4400300140d0500340100a120303080f08e818812210303600000368071090622034039060309200990390180c0c400069032401c107102d4086002c6101601851807100f1002d0300c0310342c401c1562118816112042c0000c691141e150b03042e64413124070f00c54010140d5060715506e072601460080070760040e6500c156518440c901880a800301c00007845d440034496151980b4180008416103046e200d0a418480005098810030080b5180714083c035a00030303c01c0003001c0c0c032500400020003000c1012030090303c0c030002144034503000c1c04000c41142c0d400a130004180d0b9440350304440c00e4100509110 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 225798174 1250 225796924 225796933
    0xa0905061803060403050301030605070f14071104090b0402240d0c11062806030c030f0c120f03080a09020a051c0215182e050c0319020d02030c0a0b09 66
    0x1c0e68080c008180154065600d040e00ea5041d400c0c804216040600810b003404a090251417013a9041050329440c2100d00003140c0c1c49584500740350340c0e42950041c1c21980145083c11000400c00482c030703001d014038000d40310a20540c04140c0200f62520700c1c5149440142d02c144403007500020282c001c0c04081140d407603c1c03024415411001850312109030741c07150060703140304a403070500880301c84200a804a031040a010f0f451468039941011002c50001602c1003042c1c840100522046030171910040111001c004041001401c00014045034101304900050482010414194660080b110501d40042c03141003c02c1c5010104040c1120310742d590070a000301301e0f0320a000b50780e5818448602e2484a09050b55420003400e42200f0481c0300700107188600d42208ae049543c00e0f6400c44608820809041410504050b00c002d0300c0b03034040c110186d10035200004502d8070021044502742140c01c0c4540031030f031018280e18000c0e61207008910149800303620030601d91010500d40442d21750404880700030348 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 225799424 1250 225798174 225798217
    0xf0f06220b090d0e03010b06030f0c0c06040c0513061404050601022404060c090602030d0b0d08040b120a0203150123030f04050f0706090905190e0703020111030a090506 74
    0x4245040c0d0840d401840b03500710031070101d01603811103e20700007000700324000c00002d40e400300002c0321030201420000608002e600040c150b91043c900b216902001c0d20201d0b4910b1401d8540341034807485900a05025410194540000c8050380c000d440550704507000009400b80d64006000080000410440c11842040743e031a400d6510040300b104540111900b503d458a0581170103400c0e5945803c6800070001154010440a540401900e400501400010031030600039000140103804464000c3c1c260703800081d0000e005003c00b0001c0c014020002c1100070346030f9690018800300d001c121014058251007034005141c07980b046d600460780d215030802c501a0407111000090301038004494000d00d001500091006105007003101661610014000b41032080c00c10400520880d4140b040d81c20313070782c1c558010800000b280900141c00d050141d0007004030000641982d9030b20032032840241d02040c059200c5c4220103134040120751806d02301d40c5441000c145409d0034061164040e00c0002c101c4002039181 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 225800674 1250 225799424 225799433
    0x5010b190e0a12020307080c030d05030711070906030516050a0603020a03020d110408060c0703091703090907050d0e0102040e01050d080c011506140c060606031003050106080d020f0f0622 82
    0x26501809103c00002001e41032441858030744409500040c090740d00060f55400250340004100c0c2c0c10048500e000c0d42c0b41e8503491001d03184e114030240d0200b954081c0303440c0070a140c80030384d2102e021240034008440241103041014032508503d0b01805800400302e01c41400302d00e000f0740040c031411442c0c1c90014034211150b1079500072603c030700300d02903040d07000050104041138040203c6504410300444131858410582e4000d030800d1803a2241004920b802180a0285182031042d81c000e0b80340941086414989084004d040354060f81580c292680b9240910040c04814400d039802d03130324504840441642000100302070116004002c40d04400c0410018114010038065810b2003c00d0050f01800c0e90f00300b4401400c179500114010100d45014030144c19552000104503070000425200c1555a8490b50325124500d02d882c0c0003c0c000358213002001682c00c0740041c09081c0e500d0150f003924040009440300d039841b91084800c8203413580c4802c0210700a1400d407400b01d060880c00201e21681c07102265603 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 225801924 1250 225800674 225800689
    0x20a050c01060807060315061b030e09070801030c1208030406020c0a08040b0406080a050402031b0111010c022104150806040609050c09090912040902032a040f0905010b190e 76
    0x1000f042d0f04540420024650140607c0807400c184131a94601a42403500050103600852882414410104450420b01d03005520204c507512001d0304c0314038a07250540014115020038801155204117070000001c00d01c1c6100c088200040d44011103900d143ca458032550301039040300400c9500c0707016a080340301c001540c050090000308142c51900c2e441d070f850440b02603c110130050000c02c00d80c3c105010000140c0d008155103030800c5e180441d09111030446070040354103417140e80300d032041c0f5880c02c016242403580010750301c803040032268086848088106442c0c038040c040d51280752010b01144280301b000e980160b1519a21242c0604000f41c6070b55035560f402d040e01d4081e035030300700c07036240000c0d520b400c50818074125940310610310010110415140d4449203544290301c50302d003200c5c1c0d011000c281c1f03004800c42032040070440b01a40c200c02c2c9008844020669110b0301c200250303110134207400a1044480e010300d6040b900b002180303070700300f14001c1c1547c20f12001c0c0c01c1c404d0341040340c00311102205558040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 225803174 1250 225801924 225801929
    0x1020a0e0625031205070513180605040204140a151707051306030204060f0201110f0a14030114100e210a0b07020601150306030809011107080105040503072d06020a050c0106 76
    0x15a60320003913102c00419411900003030b10b828200031080041740e1001c0920b42c0741c3c400b19014404584a50100b004400000300ad5540203c0c1e40716000040008203400e00c0c0c50b43c0b50303014034121250080c0d15600c0301071718041d0960501072804140204d807031b490780d4031600603480e0b0b01a00904200b8600310010580b1200c80200390481d50120398046814003800d50320901c01c07800455070740020480c100802100c0d0b0100c2c0a8122141a142400180030f51202d10503800e00c0d40c0311000c620703c03d0b1a0b584890a20034010f1031058403601039010900e0789100248141c0c0d03040031500300a45881d01e101982c0c080c1204490300e80200312400e1007588103200026103c00400c62003011070741e029103242d506220a010300440009003400415003094028001310300a5401c540c00e012003400d251140b01c040320065402c040d610340c00b8259a519100c108428064080001c010040c41020a1901c89080c01c030552a0071030703030710074400d800700c0800803036000140310344d00038040801c813401c025040101004aa50949180d034 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 225804424 1250 225803174 225803177
    0xa0b15160b060d050111040614160b09010e0a14010506010c11040506010c0f0609151505061b030a080114090f0f090c030703050a150606050a03090f0c0e160201020a0e062503 76
    0x31f01002202e41c03041031b2908860400d00780718a401d01031910a003221000300b001614008032000401c008801c01d52010925803000401c1c3c0da0000b1950400344401c01418030f05510035401c100010b89198840c16188200c0b9038411842e860500707541045c8001010f00038241810312110380d03100e10210b100e950b15101d94910840001c0765000c403600d0002210244104041e124909080544900e110004201002c0e98000c0c0c1c0d07010349807414906131503020b54548658504a010000307440158543c015841070582e240303190105041c3c0000c1003484810705080326985408091078003c212030f5001707021010740041c0001c0882d10344072019400642048210760080321103130b2104503a030040198900c04a840400f40d00401c00c1828070b8003601801a11400c444142050350b143c0d0b41608000000908640480c0c100c61400703400c0d80c540c54000034110003520200c81c4040120700d91a0075610500840307441d5600740d550840c01032003000510048d0380007050210140300341c11200601e01a614504a403009019 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 225805674 1250 225804424 225804427
    0x1180305073003111303021c06050f09071211100c05070602070e0a050105100807120219030b0409050712020d02060c0a0308011401050717120a0b15160b060d050111 72
    0xc20054120340c130441009040341d106000a400c4843c05c000b2031000c480e01a50b002e05218544c0c07800c20007801034088003e007114a0407040c0b00750007805519062117202480100c460070f5807100b40039144d90083c0c80d0002d1102440178488002428080000c10108041e814100760801590755200d0801c41c083d005200141d010f40800c015185c4901ca26039000300b003026042040d541080089004481010142002e0003c40c0d00491400380c800c0181484505040e07000310b4030f81c183c06002c0400c4c551031070110741c0002c0c01c3c1150a455858544507142e01b0b584d022000301034491919141050018080b102a40d015040c404000c02680759000244201a4140060440ca500c90f14002d40030304410b0f0071119090311100440c40450740c001044402032500041c8042518048501080d13861090300e83d90208480068148079034150383c2c0e000300451020403111854240060b4204a01c107005d0a40880860203000f040c090116000030003450b0441006005600c01d09643d8441909541c1410f0100386100f10 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 225806924 1250 225805674 225805763
    0x8030903100905030d0902010c060509010915021908061c0b2707061b050d0c2001020a080a051204030503010f0b03040b070e04060816090606020118030507 68
    0x302400300028446908000b0019640c080d02c42c01c4d500d018960350a980c1560300c1030140306580c007a030746815150340e0020042c006071800041d403501030030003003100b210210815065540030402038003c0e1200120064000100016611030031a451000980302d00e401c540030310381e88481d40c8142d0350341780d06982c0034804174000c030700f81107403111002c0d4103401c0407041030406084500c02910000c26000b0445145150050924107080d01c20102c1403800a40101103126002003441125044400c521041d809103d000ca030491b03000c0048419140c48503540390060b0445840c00000030126070103000d69002603c1e003203050403c003002d404e480a105450035408a03c0101c0100045000b010a9102400d69401410b08505140d920305400520240c51740b4180040000034a00d10b403181c2e4405001044038400b10743e8091526090f940100b0303100c1c028514013030f041050102c0e016005010300b0319104a158000c1800d02e045880440e035030f030042c00303044a54941400d229411000f00c00e44011600980381d0b4101da01c40b2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 225808174 1250 225806924 225806929
    0x32001020903120403020604090903170109090302060901180b0a06080d0c050c0105090d020105030a0f020a030e010f0b10120b0901090b04050f04030905040f090b070207080609030f0406050a030b0a080309 89
    0x400f00700c0d0090080f040200740011307265902502c044864540303000c14460301038541a01c0c6030803448801c032940007c11000007083e2000c3d4005540441c00fa80030703540c1740c1e10b034a1350140c203071038205210901c2640b001d591034000550403468154004100d02000940584441202d41413002c2106924000f9140c5d411400070310500707201e203180061003400c002c0c1c9400d900e140440e01d0789403207800203030510001000213121640c3c940c0104408d0240c003407046564a5070110702500403c10040503145641c85d0010014913500b03e80b041c15802900240341180750f6800e001b00300c2e17844030031280d010348003078440c0c1600116884042c1054003904e611880465500740f440d0900c021104000c040e001070b1a4401c0078003010030b8001c0c0e07800301034950a50303001c41d88502c03186d05000600711100740100280c0c101000c00410b50350210b0042c080c0c1d80400107450b450f4403003681c2039942e80540c981907001c42c2c3c002c100810915002d400200030315090b506020651000190014420492583c084110b0b608002080324051 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 225809424 1250 225808174 225808183
    0xc032705090a091e03030905120d1a0307030204090f120f1706010801230a0f09060b12151203070b1611030f0702040b28060c0519032001020903 63
    0x24070641d2081020f8422622030f01c0c0c2600c0c102d0886039295001c1c1c00d40074107161190308100007a0b504802280e12025034041e54804560040312080c1c1c5d00c0b03107013403210703901c0c01150340c004511048010024603110f82945c00b007000034051908100d4620310501d071450001810105044500d040d16203507a00010420360001d01203d40103500001038249840810a107681c1000c0c0b0503064501514006c101454103000d4651242e00544c9550392241c004000054140c00d099480402c0d00d64150042c0881503454444030302a001c1c058416200302840d00c0054200a40c1c0710103901300160041c41403506588100103d4251782c0511401c0d50f10200134000c1105c0954039400f5106d18045900e00702c060307880960030281d143e000b0b111022026000004800f400d540d126045042600d030014401444080d4502054030444800400c04000c101c100e8070000d4101c0c01081d01204d07064018020b00059505e1401106200381e005008a040c40741d84038040c0c04032038141c0124962001011300041e070301c080980405161 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 225810674 1250 225809424 225809431
    0x70507200f0d0f110622150305010602030d020309030403060e0f060906060a0506030411120706090f060c060e0715020a2a0b0c0c04020703050403061503020306070c03270509 76
    0x30b280112039a400081e11105040d1002c1c3d00300d58030303490440c02d000c00148107118a90380414048500c00440001d03c002d2110003045480c01d60030041d022041c18025015100c013440341402582040c000390702d1114103034009580c4a5998402d4904d015202d40c0d541c3d0803588490422489680444401061802c04006d12034001010400030300480c580b03100046c00c2054140500c902400010020404200350014410380d001301c010000c0001e000d40071326032035039022544212800a02180d0740026200c40d144652026101c0c01d595603005082c1c0c40e1500c00103448041441c80c0103202c3d0032000103841048481001c0000025400750880c0e49040c200950070700c07150a607400c0501c400e4030301402c81c034411407450f0707084500380301c82030781c41d6480c042256003004191811190494000650481050361000041c0309681c4201c0c800c01c20908401c5100503403600700d0000035050b500600200c2d201c2c0740075003000c04405100c1d01d085611000504201500002c0c0310811441122000d44240710030326045003600d0380b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 225811924 1250 225810674 225810679
    0x20714010603080d23041113050906150d0f03030f0c0206061309031107080d03050702010902030c040e1908030a0606020a15090305091207050405090a1703070507200f 73
    0x100d085481d064120700c01c804c950402107541c1d602100340c041300090500c903610345000b417810b800e29003401c0050402e8000344429215080b028901100c503050741c400c01c2d000e62249002070506590342c14a10300e4140041c1152640300c0f5050900b100041e0003926050f40c806d20950700400c842011040d4035055865600d41c1c8410740d0000420051a61a552010700380303031400340c00118134603400b400d0a6629004031322001b0001d000300c100124081d1000120900e904000c3c1d5001c200940c4d03110812070881d07841c1078009500d50130814112615103003540001309041114016500407807129840342920a0017074034100c0d030b1303583c5c0401000301d09000b0b44511001132916001410000039240d55055103030304203041c682501075032007100a06040c403c0c3c080c0e031905940900544400704c2c41e031076515600c02462103920b21940c10200050000c10001c03074100c1c8003d83c094071710020303294030004130059504020301c5081044014454000400c1003d01c0c1d580510044010f1510407900c400180400c560038400ca4a0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 225813174 1250 225811924 225811931
    0x807091203030e1e07060c152022120b240a0303030b09060f011e0302090904030806030c01140a030f0b060a210902061801020109080c01060f050a060206071103040e070302071401 78
    0x480c01400c2444940c00b01c4410024a043c1c04100700c1c0c0003000c1402048070391243c0480d24a8441c031480400a0590300007030705444012fa80c0c2c0d9541898158251401020700500c2c01c0032502c20a4040503d4202c080703005ea141c0030317003510100400d19004a81c3d0003940069110001d03c46a03040c03805205400039020b44d0703010447d00051002030300c6c15180c0b4015100c031034001c07458825190300c05c3e415a80030060080000791581803030300700105103100031340e5254800d00841e0340050343c5600400d1250580740c80c840c007488c00c11140d00020b070b0041078068802c2041036125000d11400d82d0343c0d20020300b02c0070001e444400304030008001c444500344040c03e110241ba0300d40f010080250391a503003030740c0000102d03001d110724000003a80100d015103145000140a40d42c040b518810400040d0480ca0585007204001424260750710704002c084a2079201d07683c05a00f004000c00da0300c42c030641e0700100340104401101d03c0d00d036980c01c20b04002d40f01156105c000943c013081c102c040010345041c014488000f5002070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 225814424 1250 225813174 225813197
    0x7061b0c02120a080703091701061a130305030706090b0f090a0f051005010e0105040b030313060809120c07050901090207020a06030213030b0f0105100807091203030e1e0706 76
    0x908524042a4003920840d550710902804050401a400c840e1341e000004944620711450040c0440f01c0c1c078040c0c8038415044071800d1403400c80500c1401d0441d80c80401886d500c03c034420180d002c0b43c7c0070007641d072604d000030000400450820001410082c0c070941000581d5403075414588520300c4043d02a1646980c0380d000d110811a0000e0329108144d0491a603400d0001c41d8600245422900050300039081e003098000504001e00b080414100d070f0094505001240c6080c0425882b0300c1416500600c03041c60400c14044a4401c400495100e4408000c80320014016441106580c0000c02c84400704c0c0e00c075080a100c20b0512070041c90040c10120008c3d030404582c0da00103000700460740104c41c2015400700d0070f07071840010100f41000864220061040d1410300300314900c2c04031400d004807409015080c400050b01171280300c0c001c0c46044140c2c2c546401d9403c01d18203a9000c000084203504147d102c0c40c3c5801289014445602d000c0c40180312007014100d26880d99050408517405101031055200303d4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 225815674 1250 225814424 225814427
    0xa02090301020f130e280209090a270b0112060b0312030709050901030b1b04050d080c011401150e1503071d01111f0f020a08010f05100c030815041107061b 68
    0x10715401d003844900361b00c1c1d101500100d90003e004140440c1c1c1d1100d00c00c41030085509990b4006519a02c400b241c40565203080c010902d2418a01500204902d426900400030300c0764401c8400b8840d80300d00c80210703050b0700510000380b40c03c40c45001c4000118001003030044281c1c10110700002088c0564030030910b58955165181402c10040c1070180016030114603191249041044501406000f4507200b01040c0c42e041220b0300b034000220781c0c40305600c0c5c65000704048660340c41c80e5040f41c403607103a050035085800c081103800d01e1013183d00325001009494041d062800d054091841000c5030354580e001e0b08a460b20301110804145915810300c22084c107240404180070410180d890130758072207001480326420044008112248065800d0340c8042240a000c030ba100d18000c1c100c42c0c1d040c40c0c06690984540c104104032403200d8803d03001c144031f01b2074400043d010301c01ca1079009078010010741920b5001c00c007080c1515014281c10489050020301a001c02085108210205007404990300c9500c40c160070 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 225816924 1250 225815674 225815701
    0x109141b0d0803040309080619050f01030221121b010c030c0815010c0503040314060907050a030210110f060a0c0306050a06080c040317031006260a02090301020f130e 73
    0x1c010300207074000800141891300544d00300c0300404d00c2d00704960151402c2c1c240c0350a07040034410480101c1e410407011410300e40c3c3d9070000c42d0603240c0084c41c00117501508180407159000855204000340285015541ca86140074040d010702c08400c0c41c00100754400c00d0689007103c600c0002c80c0c0c181485e1241c10b0f648a03034082c1356541c1c061465501401030300350030001681c004c008000010721910000801104000340207001c15030100c003e60850346640c41d540c2d0035030b844e90780a00a254002c10203840c00c03c0589402071000f441003003030b810402c0945154504003810225034043c8900140e2001c0c041c060b1046040c41418840d10b032524007008141c0c1031800103620460b0901c10b2000b00f00e48100403500a1500d0310440d001590311580c40e40701e10301c500909a005070022240414076a1420000107526401100c40340032542403e0028919a8589404000c0b00000900003010890b13080c84405203d0720248010400889090340076031710f6a1480d41d90f40741c840401e801c4250390001210a100c03205800c0d41 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 225818174 1250 225816924 225816949
    0x31309050709080609030c0705010c0323091008011415070209061c030206040b130b0a050405030409110304230601030b0a2309120a0f030f020c0109141b 67
    0x14010540d070700c549004a412803882c1c2c11064540c0074003410b00c2100d010000c0104601000a010350b54810340d502d0041d0703487c0301d82c035201402141c0601d800d134030303003808515040d4881a0180e03681800c0420940100302d002c00c10410640100d43c4190047c040b5a46d01008030707170000421a100f0411352109901409280207296009000e4841c40c0c0200303a0b640d494000c41118040c5821142145900c2d81c20000c0d5103035816901a205070190f200030070400c65621100740c1074143c00140166180d00d03820520002004003c0013924240018017010480302c0c030901072020743c405284862a00ca06250800d114011078040d0106c02c44400e45100d40107107034010a8542c1140d0b0400e00030741055880c5002c040c017074802c0101000300c440c00010310311880203480122a0080800c44215401c032401e0180891951090102d801d0100301c8901a4900e8984030703030410701018652102c09410110003851031821760b00e485c1c80c100c80c40500c8900b10208148104184144a10950032245a03c101039010a007030b00300301c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 225819424 1250 225818174 225818189
    0x3020c12070f05070807081b061204050303010905061c020d24020a080105030a120c0f02060d020d0b0909120a020a0b101502120708030a1401061d03211c06150806030313 74
    0x9076085065a2759941070314104102a12005100d25051800546070f038824000c1010840c50140400c5460600c0340320702c0300b20490418000e240001e143c0802400314003d1b202118407010854103d48004c0200c1c60b98040c0001c1281d002d82c075002e0185003d412030340d050700114000d034000303003481010400c151342c01ca054501e41c0c18040c02c00703012400c02c82d10b02a440d1401940002000800007040300d03543c5d0041c84600b0181c0700c00c124446030941003062049040d1241c8519274481100b40c0c0000c040d403001000d0f4295940101d411101d400d81d524454220111800a14800010401c01c1500d9105121400e008154406081a150151004203650083c0b03a0050f11955011000400114080e8440c4003800b40e124120300c490b61351541c00528020348031025000070f0030420004074840c140040c07200080c031720890320102d4800c3d018580382100d4001c4034800f00040c88102d180d01d40071155105481c003a054070302281c20802c13101341d40a45400005442d45002c1d0380100000740e54143d5290b1202c040d144407 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 225820674 1250 225819424 225819463
    0x61703070303020c0f030a090e060f0f040506011b0b1b030106080a0506060d020d0b150c0c0d0203011812090b180d020f100503100e06060a03020c12070f0507080708 72
    0x1004c02d540c43c26982001d1110746100000d0300d010f60640110840046070304e0320410075119034070841407104407403491403c650480c6d26050588c04614154000c2d5501010601d0706500500d0b05403c1c0c25101c21810307005890807264034050258903840c0da014010000032710401e041c0346515018005108003401001d807151280da54021650790382d521000c0f1070008822a10541d110030305825000f00034074524103000d109000f11449518000b81a100380c4072070402c03001c060091410f8100074444682801481203030b16550f030780320b9242d141c1901040300500d503020344041d040b4081c01001c05090f10f42c40382c101d0110090103000e49001e4029030250301d59508001e4440c16031655852010946c032542d04c2c1c0c0b01c01c2c0d1082d0810849000c0300c0c2d214000c0c4d446000307540292507035141c0ea40410340a8120550f00d054028000f0490400210301a070010b250000703940f0100c1e100f841d00c0300d0007a22141c1200404803000b00702001c1680c103210f010840caa001c1c1009101074040709140520183d079850602002d598400741 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 225821924 1250 225820674 225820687
    0x308060f0a03080a0f1d1e030607050c0d05191209050601082505010c140c06070305030a0b1801060c050c030118030810050108010308032508090106170307030302 71
    0x15040c15280c0011400361850141030345078980b00a65400c140c3c0344000140080481c240b44511410304c40e810020340f0350090000c0803c0c04140000c01503a202c3d644a050903a00d003004054500f044090321070911a0740b566100e211449c2c8039420f10450346020410020284050b00c8281c0c0101941901105581080d0503010b501e984580081c1000c918081e11a000d0754000040030100850000c1c1a14105000c2c0d034a9640b190408505845c407502500380054208951a00050021002441e85080840465a12004d22000a21542c0c049281100007030800302c00d1091068941c001d06010750811200006200e942c0d03000ba4211140520a03841000303c19040301083c030800f80106910941c0240080c442c40f050138034030350144824840120000380c3d96a000501c00130801d2003000a07564140d450340e085929503250003000350005800160070180d4140d0304209886244d05040e0044a2600ea0034104d00c1c107112260308656141d440442000386c0580c2c618845600401141d0030786600d420300684410 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 225823174 1250 225821924 225821929
    0xd03020a0201150e150301050108030a110304031b0509060306040b0c210c030f0912040302240a030504021c020f13060803070c081b2413030c1502030c030304030806 72
    0x940c00f550410b050841c03031000304003c0c1007400316038411441c3d080a40351415244080c1401c9920912482440e50000d2080c18050b41c4039010740c400b101c03502c4d011a03003403e4503a20b03802280800c00f000031801031100b000c1000241086501d81d0303030102c1c080300600f8080c43d290321101801e103002040c005007040e000a14003000c440204245c880600c000c2c800c413078145000400b003643d81e07100f40c441c112801404000248c025100140398229010300420b0036041c24519401d114426041e101152000c6103641ca02c036860103c0c01014080d034081d2030741c0115050401c0d005002c0b071491200303501c0c5110345078032400101580300c2c122020800c80c0f040e940100603185403000c41c0c0c02070003590089040381c00f0028200085c040c00101c0181a41d407603a00f55008032140128501162045d24500d41c0c0010304180840401002c41d41c5492000d001d41c1071540c54018007000c41700e84010705820464102a01e61030a0001c1e0903407191507445242e450000b10b1801500c201c0059903800b0040c0300071304120102c40061070b40d4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 225824424 1250 225823174 225823181
    0xf06020f04030602040e090102040303020a03230f07030f03060f18021b1006050a12030c061e0c02060c0f0306060c010906110901080f04031e05160602090109090b030d03020a0201 78
    0x19021100001d45a07500c07860314001035032283c842c40a480b061900418004581803084038126030b8903400030090002103940c00d41c0c9000d42d4041d201d402e8203060450312481c45000009144e119890444d02d03640701490303d0054002c9840041210426107480c0061040000101d491400d0381caa10001d0410703000072010207000703885050149215050403078030170071510f6000515108090500e1105000a0392a0300034405070074058422007101482d054004004280101c403100702d160300901340440d0507550020303842165607a018080c03840c00e50b600100601e10741c0c1407040b10340001d04100784d49c3ca4200100055030503400050324040c49110005080549400250710181c107590b482403062041d500c034801114400d8201d40409400300c0c40f140e0003d007111284419152180d5850345a1708103410400079040c100c0912409040d05000003042600c0b1803101300901e11110520580026968001000c0014440700c0c055115100342424615004c1c0302d59030106003050500080e01c1c0040e164408110201d024 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 225825674 1250 225824424 225824437
    0x3010e190201081506040b0d090b10091d0a060c02030409141501050307020d03050601020a150e07050a03080708070804171b0d030207050409110909010b030c040b01020a0f0602 77
    0x14031806189030032250800500e1880c4500036203686815599030142c80c10b06030201c805040d44010100402d002240ca100040e040c880c3c3c901c44000381c90396055840f943c03c4d20040c1d80b900f413280720f189001c008550040c0500802e43c0c0408904084407440e16800f15928042c84070000c041c25251419050f030948204190f800a0200d210140030601d51215911400001914844441408042d0700c81d400d5019504a074007070716140c2c3c010003034102003002c21401090701509460460181903e46400320310025001b00003000b10f04d400164416034030700c00510740742065010381c1c0200e10840040012848080c00d454a00e0382001055070355103000d2404400c0f610594100e00c0e03c4105070340c0e0440d05c41d0000200b503d070300980034441c2498508130404004c5800340c880402801070384820410b21560034a60003420b420b40c4290484104130050f0300015004600480302000903a55450014541d442c082090400800c0305480c104001c00b44100004d480744044c10002e400c141038484071030200021070381103411 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 225826924 1250 225825674 225825701
    0x50609010c120503070315151110020403140c03010504081207090504020301120c0b18040209030307080c0609160608010e07200d020606061303020d050a020303040609032603150301 79
    0x301040964400f40898000361340c00400246420b05034080d100301030409606030390a10301200c00d2042c0800c011030310030a100c4001c43e0507000e01400c281d6116107a0000d000614400d0703800c2098202c0d078604292801600c0038105100381e0610040c03001003001e02d012500e9202c041d04c1c0b104d200765111102540c42c40725590080f90424400400000d10600d101c807a042e55501c14000300c0350590355070050200c0c500a055105841302102101c4403000c0c609a40140903c01012301030707a080c003607071340c0343c0b0100b9801411240707289400510400030001418811402c00401c07007250446404d08108000300058014001d0711f065507004008961414003a080c0344181241c3d00622001c21550740b01c0c801e13106e1512107030714409486024082019403900c0b1080e150b0080c600c0310580206403642d002c018041484110581341401021104809601c00303100800107480c094840c000030528618140c46840381c6801d00602d061040004400c6940003601100d07001542520b46442d0b131503628001a006101d484e100c10f0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 225828174 1250 225826924 225826943
    0xc03020603070c021806010f020d020705010c051f0902100201110a080a0e07081e0c100e0a031b051f0804020411090306040b061908031c0603050307060e06090304050307050609010c 79
    0x3c82d030011700a1503910801c42a6a1500540780150042ea40c4040941400025030400380c1d0038006544254480c002d491b020b5000c03615a0552003202e5081407400d0880000d201e0b0f125502c1e44103608041c00104c0508100344004c2044c0c50b642100e071015405803005c240200080640400d9052005801c101040d50032031007aa18020350340d0240f281d4414034104e0001104101302c8030707101e000b1004203949480130400350117514945048407081394500308580f44294024103002010011682c5040f17119403800f8030047c0c4400c864288020042c81c244d03d400904d01c04c00c0f14211030349800f0ba03c103190a812a505546c00300780c91542e482c08002c14094012100d8062164004100610011070310030b900490b410741d94030880b5a003405104132081040e004290031540100314210089405050f6950010300c08030f00003d03d0f685070350b611400d50384103000a80d40651514104400300e0780502800340c0040707800c00154585803070400071170b4542c03001e40300d480c0c840c4402044d14510390340280050b174800c1da03110380d0a1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 225829424 1250 225828174 225828199
    0x40f020f031501020d090501020715020f0d02011a060702010e0409020f060a03060306051f140102100207060c02011a0d060908090301090b010303080c0a0509040209010c060f02040e09010501030c03020603070c02 92
    0x9610102c00c9a820728014400c184852081c6030042c42800b00b0b480301a80038108880c1030410b001520045140340100b140708461001c05480801e000c070360030303007051680007299540b01d5a510300301e513181d4240503034458501001a500140c0e005411700d1040780b802d480205c0c2410003400000c4400011820035134001d01c000034003040050745035100d0703c1501d01c1054200940e4460740c12030252209a000c0d042180d00207808203210604a2210701c1c000450148100c540c1e10b4072940401069030440082243d00e01d807030303d10b940d6a264081c0551303c0520038801e6180514110540040c0c0041c00311032000e40404c1c0d49002410038002800121800c3c2d60015009002c400a82d117041480c01078244030a500040500002c1080c04480500300e0f907807440e403556141d0610004004003c000c0d480300c0c01c401d052110344201300001880754056a60840e000d2600180c480d45060126020514020b000442d9039242c1001400054036402c43c20059a4065443c0c64581c5d031105c00c140c88009032010041d41c44982c8007540c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 225830674 1250 225829424 225829441
    0xa0f09020c190305030f040c08030a03052226071406070f140702040b010509030109062012010311060f04081b0118030311010908030f0405011404050c040f020f03 71
    0x10008100001d04031207400d650001d0745000600071800040014004101241801d2486840c0d0780d0094021041044038969900442d89540d002442c4000429112020002c0742c8240321241760301941c4089200c000d0185035542e18880542a02103101c64441d070807000c441000c11407080d124120b61154100b44014600d00056944040444001001a0719203806541c260322078800105072040b1002c400c2d04008151f400c01019011525a50741002070130300c03c09010350b070f0074041c1c00324050145074002181c82e104d00b680000494080d02c1d41c2c0c00c40301c04010389900701c0d418090b40ca0440750007405088440503c1c01c00a4405c1c402e083d4200d81d00500820041908000800c40b02c0d0803581074031907487d004580788010f540c0c0b000c002d2201041d4802d04042080424080c0740b000c0a81e0b141400006808806581c45c001c860f0425185c00036441030010800081050920642c0ca92205c0401240c00303900e401d503241951440c01c40d00f003034007440d142d02494a440307075280c042d5481281e42e01c202d43d8030f0b442e09400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 225831924 1250 225830674 225830677
    0x3090f011a03010605030a030503040f0312140403020f0307050a060506150d0b09010f0305061515040609330f020a020604060c02130e030a030b03030904060f06080a1a0f0a0f0902 78
    0x1c0103200307510304040068180b800144198406501d511620700307603590340e1911101c0000e511000e5040c40007100c0403081da0348243c445c8607440808104005110308107820b000f4645141010307994601e900402400303010034000a03250b090198003100104080c0c1c1c410004c03401c10300708140a03922071301c0003148080740b101c1150000b2081c060251411041a84e032030702070103440600c1d440b0152441e0001c001062212039100424805003070301a00c9e40c20040e050032819989540942d0000001581140d01403003484440e201e000c2c45a106070200310700010f00000d000c10640d50114042040c031000688a08110f4000c0c44141462900141881d44030742ea544005070803580f10f60700881c0729400c80080c002c40008a8403450780304640c144020750403c10840750944c0106212141c559052009000d00300e003507603e41c0a65000382200d01c1e803011b81107140800c0034082c0d8a01a01948580341080c014448900070703c00142c10700d00701240c1c5402000c031050080b44040003180c024018804410f4004101c6102c10f40 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 225833174 1250 225831924 225831971
    0x406020c030303160e010e06040b0c0601080303090d0c03020a0209070806010e04090b16051204081b0307120819060b0a090e0603060f061809010b0406080a02130203090f01 75
    0x202903805900380101015101e1000320707522a03400341001c002c072100d288140001140c244d03040c1441086002904c0000d81290015408031176a5040007030998504181417200c2c900400c0e10703000075415818009400c5894103241004042005a1100315406262007000715107841600544640c000d07081c804001005c0c0d40089071000e000c1005800c90750070a0a042c868a0801c5411075050760164494000410348031032901448810003105000401c661034003034007a94000c5118009403a504d51118100c480f044c42d45440c1341665400c03c1c084540803660780e81c0407440d0f5011501c0c0020b01039a600380c0d814100d07010003021070b030050300d00080498010140c50040078040d06c1511071084040d45d80034940502103049486c15055005807012800b40880c001c102900924003c1c489854980e6000c90802c0f9600100d54012143e0b44071051000103090a109000140415602405074103000f600464034101012040301c00c020303400000a030055105012109030190743d10700a114810442407820f00750005070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 225834424 1250 225833174 225833177
    0x30602030702010b1806210109080d0c1812060203180d020a0c080a1703070311070503090a090218120c1909050121030509060d14040510050601020a0209090c12030406 73
    0xc04682c5e8040220a1190300c079590080031500840d1003005801c81c06140011800780942d01c40c584003001403919409030215030800c0d00001345103103417120000c00415034002c541070311000d00d15040c4940086240d150b0401070b000307180507a507600e0303c038010003450716000b002e014540600d01c0300c5115140e02140c80c8400174080c80342002d4454840c107a141d207450103120028401c100300c00d800b010101200c4080c6070700010302d08000034964024011440c203130384410350841d681d820019501cbc1191407c050003802074a40c0000450030701881c2809180741011040d440d0344601c5101742c20300001d603401c00030f440705460046d00e1071250b050b89003170b4150000110b0050340022810800045803203541752594419842c01816080c0010b0587e44017a83c00f41d01203040c0746c0c0c01c50410405100c40d0041c2e07004001d0121320300071101c0e02c1460581001420105640034460203241018280002da82c2d00040d001c0b4070b9901110b00140310f40321845c485240801c5007603220740050311940c0d4120603c001201900c221101d5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 225835674 1250 225834424 225834439
    0xc02090f09060a1e0905070504110a0813030e0103090f06060609090b030105060306040305210f0103022404090f0e06010909030818031204051005090c0f27060307030602030702010b 79
    0x52010034010390740401352101d4030310300131003004038418019040b1404950088007601c25503034441011034140d0701840e0b41954106000111002900c0e4000101e503800903291442e5640041590350040c03004000d0300202c1c2c1016214104c0c0703000c1c400c0190041c80582c0d4000e004114842d038450015212841900c00c01d00802c2c6412400c1203a8241070250780d00c42d203801005040c2036983c81d5025541c2d504049026202d022000e864905c45071455409940103440010400e402c3d0340c550f10410101085015213805640c03600003c100c101c070950360aa50645000282c0401d22804800e0281c2c01060510380c02419840782000014001c03030a40d104842c100c0c080e0342d03000c400ba910310f60b4a00b9403454500844213940c1c02040402680884010807d8101c1c1c800c01c16100d40707000c0d181440c0c0030741320203941c2c08980d0742004503005007a203006948010b40c0c950581c0c0e008000790840800800100b003500a4a5032055801d001076500c2c0c1e42070203c503001e150300070000c540703904051400038002d140c0384d204903028610 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 225836924 1250 225835674 225835681
    0x11e0515060309070e1305010f0501170114150102010e1209010e03191502040e150a090c0e121212090c0f100c051e031809010f03030503070c02090f0906 67
    0x201081203c2c0301e410b0740001410007610f41512810110300007000094040002c0814900050081c00f58696074400d091020401d5414540b01c0311000c404c000030002103a01d00300104489803002c0001e40da0081101d030f4645002c140c0c400060740502013101544c2d886024403040005941c1168000e403600880030380c0c83c444840039074414143e49a1120304400d9081010f904000c0c000f40c55002c500600c038024000150511799034200003000840159900d800c501e84919201260781800000440180007103042400307182c2041201408440d13413800340d03e000f842d60744413028021a080080507828452684440c1c0d4070b91103515011041e01069840d01c01600550350f52811034506180c4800348400d0082c42010015a88a4241c4820711154001c584600511002d400c54007180ca100d9829400100055a51041c1d030340c5003801901051185540b140118200601a00310602078120603250700d81069030f0b59840d101400c0d2685405400001e5011014808000e5504d1612200358090500384003141c0040d00c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 225838174 1250 225836924 225836929
    0x708030d0f050c0703090b0313080406050d0c0e010f0c170412030905060f091c05190507230909101b02101a060921070f0b04050918011e0515 62
    0x404c050000c0c0c00141c40b2441440403020b1000115000f20710340f501040851a50303a070309034154206610500100b103010810348524025130003070150080652924003044800400083c1501080340c0c42041042742000204003081002c0c001001f02480f4901290b407501da941c910b07240403410040c4114006940d00c040050f1606050080d1419400036000140c10b01c030221044c0070244801000050481001c0c06140020541c28000c091548490040c01b40070b4101c1810801d1070904a940540f002d003500704c800f00b0703520b094010503c445050803500f031212504c0d00c000c1c03245004040c074410348c0414604000310b00e050f0f940000810448503a5000e45a0100f03144400c1c008648903407026040190440c02d44881c1440e10030010119400010040b1810a00031581c04014041031130ba480103990026030148001c0d07030f980103d4001000b1100784180f1302420b0002040c400030001c1d1a0200e268503002807003000c0b4800707400201948900c1158480c82400c801010b178041c04d0300f40d80c69202801c0c0044040d0890 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 225839424 1250 225838174 225838177
    0x1020d0915030f0f090c230a0501080c041a030103030809010203090606060f040305120d153008191107032006040e04050705031b0f040b030708030d0f050c 68
    0x2035102024038000401c00000035805000a1111264229924845141d08002622500c0001801411021403460030304c05040010f240a1100840d00c9011041424041d07503800303000406e4030001e10b04401c46848040785100c5074002c0b0380120b55030401c0e45c000468024241e0740607504076406680d911207a40c40d080102800c034442900e030070819070080800070318542402d4008120240100582514099032074440768201550302d4080d04a2034000540603580307101d01d004d4000d84100c20500c1d545550314051742086000ba41c0117103200503c0a601e9681d004001a42c3c0200640e07070400301440d07840340f1020b41042140b8240700305e1004280c00220040030000001100d10a4950144044130303109109041c1c0d112140100d01d000303038411400c00000c80c0c08a69503006a000d548120004e1881c40d0030b11082600b00b00c04005c82c500c00903001c00303c0030500c1d600c41034681c081c0202560005a28000600824185041c82e0803944080c030001810700d8450034268000801c01c0c200d4802004684c85131807954009 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 225840674 1250 225839424 225839429
    0x1b010b010e09070e0d08040b04080109060c02060c04030f02040b150712021b010804080409060b0d0615080c0901020f0d2303040209010b0a03060f03030903050606040e07180e1b01020d09 81
    0xb803181404c000b05007442001070540a025001c042d00301035139880005d003180d006410038500359450311414401c00c1110b003e20340090030a80041e1034240f1300b10030420b94900541c0710140420010103140b20640d2182d9000c8820400003510051b8414411500c18001da40031110440b215041009050030092000c42c0004240c0c0c0715401005001c01307043e004441c800000741c016224100304101c0002c15100e54450720f001002d58408182d15200e0842c180c170112030b0184d2110488614060700200380b1540205501c0d07208124100281d211440000101d28055002d4071190491294486e0781481c5900903a441c00658070101040d076600c1c810400c5014580400e681c0250042d4001c001405034502e00805860381c4805894001205a41e6030111511000290b03c15000b04036015004e000f0f02c201401442e600100503141803000c04079010905130b4882c02c520552103540f0210300c0a411703440481d0080323a400c40415088545410190380120844030394215898090310955000e0300f400c50080980c1ca04 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 225841924 1250 225840674 225840677
    0xf0a03022502060d0c0e12060108070e06090106110a0f06020306031e120c15010605030a0b0409030c0204020a0e06071407050d1104410601030228051b010b010e0907 72
    0x186800d6808650191001e402544140000c07101002c46c1034a03141000b1140440450040c10175516080c4030500b4000c0d5034100443e04240c200c1000300c55107805402c07504503840e515204814940e48180d40341401c600b000d000340f060f4a03150f01b604c140081e035000756006a5048098405c000b039086140044c40350316640583c519005500b0903040403802c2ca019220305061441961100744280521600440d8240c1221011030008024130141231240c4c0302d0440600d0303062781c0401210059403170290103d200c8050080c440d540000d0450b145034070442e120310b407005e0050246134403038001d07161080348d62068100c002420310400c4400203da24014036054042a000154001034103041400d00c405040051046c6488a481e03400604568002c408180080041e10381003004c02c00c0c0a150452a07900040c10050415005020710300b03000e2004030440842c07514030a0310b4040d1b90300c01141900c90b4050360b0390061443c3e56106074822200e2043d0005036000e0001da07a1100c0c10744c070807403c21900c400c05444e89030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 225843174 1250 225841924 225841927
    0xe0103110d1d010905120c03090a060201140609090604260d24050904060906181203050601050c071e030f050a1109011406031e07090302030f03040305120d020f0a0302250206 76
    0x214a141030700c02040000e2101f0152403800c0025030100300c103030032503910140050395500380103c07080b00300100075900503404580034003450804000d055580c0724003a01c040e068249160204014083d22841541e0408480c10107071345400c6802c1e010070041030300071003461070a048011091a9040d24a202e6002d441c40208100c4080d142d07515840010503142c081110301c0d0350360b5040fa03141c0d80703c0c4141d0804072510031030307011380e40d000d4800c00103007502e402819460601c40184500350840c007000c28000c090703c0344101d10a1902010218124524151754000b414400d007100c0380301c0a20002084042280b80500707000000828844d00b8410300140901c54141d682104820100588c90607070700441c1c00c04111010012040b1041303400000d442c1098507040003185030800200110b003014030500c44072010742005141880e02d10380b0b450341c581800d0341003030105039070004440c5070240031541540c03449214000030f00c0d210021100c1c041c0081d40030b41380c410962400190301c50760a00118000840c403984c06007490b13 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 225844424 1250 225843174 225843193
    0xb1f230307140d081e03010b0405041b0e280803030106080c040302010905041e050a0507030b220513050102180a170a0803060411030a0c140315010e0103110d1d010905 73
    0x304454100600038003610384a40b10700c03020801c1d40d5020394023078401e00c1101a50399217802e0800080700c0308060442c13501e90200540c202c0b00c0b44c0108070385030a0341301901d005481c41d080b220620300c550704040c0076050a0329032280205d0542800000385042e900203480ea0f100c0c9840384890928140200e110003130000d9040303602400281002e401510310b0030042d01c41500a40d08415a0005980d0708882c5c0045442da01d03000c200d40300350b06000f00301602170242d4208000034440700701e048100d01d02080943c20a0740394408209000c4401007014503140d0804001c6481d4080da109482040d442401600d00c2860010400302346000005151b85865004900500c200403407907580f9482c0b0342005100d5039126503200c060116000c1c044000758420410001c00040e08503002a0181842c103102e5130071212241c040c010800000040520481815070900300544c0304402c010040300500050000d001021001154032507400c0c0072a01304032480440030320469010030407645103908075448038201511035030011549 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 225845674 1250 225844424 225844433
    0x40905012c101509020a020d020601050103090c0e06030a1a0901060506040e041101050405030a03020f0706080603060c03041110030b09010b03070909110c0a0305071e0b1f230307140d 80
    0x3d503d542c3c11044800312115502e0200c1000c81e080310110740c02582002440707030305413035040c40300c1805010242010001011152505404002039000f40c0c0052003125010076600e03602000503a1400e6442144101c10182c00306d0036a010791020b403040340c00c3e5030811201040794038140050310103443c0a52a001c1c11666152240c00400c0500410079050090421011516403010711000542c075002c0d400800240a00c007540c24508262944140100084441800443c1e500400e64540010b00042e8041c0c507521103040a01d00d0403c4004059841440c0666100c1c540b505904520321860040b0b9000950f681d8501c01500743e4402100c0d00b0000810042c000c0c00301d500e165000f0100a044e5000030360402c80c04c540341c1450301717034103801c15400702d480402c100b0b0400846001f01d80b940c0ea01002c190803810a95a1043d040c2d00018010002c5801043c3d818800c6801c0001000020481d4025890401440d1050452130072081141d5034001d02811001007200007401c00c030003030712000c09841c0da401c981c0283c48 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 225846924 1250 225845674 225845681
    0x140f07030504030c08040902041404050405030915090904060605011722080705030a03061e030c05011b2003150f13050a12030c1106100b090d02040905012c10 69
    0x40701400261100d580121700d040d80607001810b00e5200050b900d504094000c2e134990001182948514100410440018008000e552807a031042d140700f034840d0018102d540b118020041c005402840c40390030001804001d420074011180c00f038982035480c107907a81400041503001c41c1c00c540d028440b54070100e1003988a20180c0540f03030085c600c480c1425a43e5841c142168055021000080d071248014081300c0c0a04148200c0c038480002450083c80c82e41c0d17a420040503603407181034184488032001c040070600900e41d00110a5100082c80e0005c4480b400342e1041c044041d44490007441510380311141c0040e140000d60141c24a031240d904a5540c203a071083c0d2003003541c481180c03140611240d0390001821040c0c1081002d109480211381003405080080101480403a4061664001000e008000b01410308160035507409192042d5602c4c1480302185201d0300c0071070000d40251504000005004041d40045a00c08010401d01f160b11032040034120700d07545c2808020384c103411100704119150421750 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 225848174 1250 225846924 225846931
    0x30c12020a0b0a0c020612010303030509070315051003021c060f02120c0a020a0c06031e110d05181207020405060303040308030f22030c14030a05071704080a0c09140f070305 76
    0x3801c010740c0004d581c04070f120341e0132010b11403071094400320040c410035070580200390303005803c1401003030090300e0b586800744028206141400070a0751007012444407000021084007a50300980103094501d40340740140d08075401140b0a440c400d00d0204884860013040c003c8484800603640b400c802520360386450a616440800c6e035805600c1401242d800050fa4496403100400c0c2c207440004a05500c610402c0ca48000090341008580c504520003c141007820b003078400001d02e400000920760b07201c5c0c940c0003100f1030741c00e206201840f6008483c200c8982c91401800c40d184207070360501c1107449030800d16a032400b0303c0c040140340c180184002010041c9401c0c815602481c240c0c15002c1e601d060610010182d40004400d40c00140740520500034004401d0228054600b40c8004514142400100800d240605903004040e03002020703002d50141c00c00809d540c040d20b001e5058800030b00007480c0c000c20684c17091103581c11190030300306280c0004400c0e030000b61248058192500856540701e90880040c50001c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 225849424 1250 225848174 225848177
    0x3120a020d091a0105010c080417070812130801060e06060307030b060406090503010516021902010c230f0109080708071e03020d02010f0905032a1006030c12020a0b0a 73
    0x740070100d50203480d4010340d04214001c0c401c0e10b08100c00c0c81502d1010400503002141444408400071001a803c14222406c89003055481c0d03540a880840703560403c2d50b0b69025516030b100d5a4505000140c0800040511182ea01400464680c0d04c00000d03003a50310502c00d60b110181c4c520002009810f14000550748880c003483c0000b410020600011103d4100740c006800241ca04a000c2c84175013400d1180f01d4005070316042144440d203030b10078000e54825902c1c41d01940b0031a80000941164080d4103110443d56105101018211240100b41c08074445100d4030071582c41029a03140d21620b061041098aa801c0a04180f9003039054550352415030005500b282c041c945007482c2040850754034540040140319502812404550010081c00d6814112803200114503007c0804009080001190707151070f020000c001c0f015640d525101219600606044003a001d0410041248620344d8001c2c0160707442440507624403510750341d06090028003040020b40040040200380141c51000e4050310414405 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 225850674 1250 225849424 225849427
    0x12030a05101805010614032404020d020409090c0f03080a050306060405120705120706080a0c2303010303090e061311041508010f080607080a0203040c0312050c010b01030c0203120a02 80
    0x6455001c098150400211039042d6540e20042c01100e9100071000003440c908481c40341582018103500030000328148007030100c9200003043d01c1d40342d19160161070340004810011902d440c0d55140c802d02626040d101103a0200709950b010078070940d6a00c50a059940148001d41000032480c2c3c01c0d01d0581c0080c100c542d000c82c0910001907190f50310303e101c0119a2045011305010340c545800c0c0503a0007851075007034074545c0102c10180003450303118030780a03031080c070100c80031501d468904010340b03a80030100789030b5510b41c502d003d0302554988003400950403a0301c00c3e5110f076810ba80c0c502e000020b81c54281d41140d07020059840d07040b041c00d41d50700080f812414188415150903503c00f0b078984880c0745181001e001c81c030b00c6d03001000a2900d0b48400c0d002086040054015842d00001c02003010074000c2c00081201da0110126050050002108002d90b0740014041882c0f04007120161035a0810381500300c496080000c8030031154800c0c0601c0c200800a80c00035402e1122012441c8103158000b401c01410690 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 225851924 1250 225850674 225850679
    0x301020a021911100e040b0604050114071407081b0612060f04060e01090c090e04030c14010b100c14010e0d11030f0703090503070906030b01090902041d0d09050312030a0510 76
    0x100c01c0c0c2410780e040c14a4445d50400358000050000790780602c40c805110300c00c140000c02c19079801882d02c4480341d07901d00003280d035a42e0300c0c50078041c02030003a40c1103405c603ca280408588620000b07900b01da0282c188075040542103001040010510440c000c52281032442c4c40480c12505061007003007a030203c010800702c0c01a031540d603641d0008809a02102d416610340355881c0c4540c0d0070000c0302d0041d0524120f2400a0724041c0c5000d0a90884428001c0c03001280701e03400311210501703600084c0c40070001006c2c089800e542c500000c1000407150400c2c1da0711000c034101501c00326030500c1550145008140134001c0070010500075640300c004000c030a130b0503000c20061880190b038107500a060061007030319981c041c1401c8c042803529003410b42c0c12448010f850500280085000d0f1413801c2e0468a4904011030244a10700c00b060290100c41580d1480014203c800040c26001144000c00f07110f01340d507580407041c1d4410030540c1d21100382455414040b4108080390380003480303401140d800340807000003c24956 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 225853174 1250 225851924 225851929
    0x30402120a051e06012904030c03030504090f2903031308061e070804060b01111605130911040216080f030703060b030606090d0501110c060a0b0301020a021911 70
    0x501c00101c4803904103880c0310350441d0030428501c1068070000e00508180d0704121903580444041400103c1740d1042402892010801c1022038003d107601080300320030580d81c1d2070003800d1604240105c684160820419014025151040c2d0916405213050070300c508a0303803220712418501c00f000150b007501003040300c2c1d25550540300e4120001c1100300000c001c40c0c546062800314490f00300d0f0720740040c81c42c03401c00d003c0141d51260390160040d8100700001190f100307400040c1c45001e40031040e400203000314900442124107408900c41110020f07039030100100254452041150721401c0014208446043d400d445410198042c0281208030802d0307028800701d076158507489820030740d030400c40c2c2400082044030040d80b501810700280b03001e100507400c0d420010b00103100c0d40525141c0a0141d2040401e02c800d00c802504004200c0c180d8124003070740e600700c080b0030b640c44400c120380321420317a414041091100d050520840e0340c403060907800380501c82805003441d1303202d184030b4405881100c5104540a031aa = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 225854424 1250 225853174 225853183
    0x2103182406050a06021c020106080d050c010204030b07030f0f020f25170d060501020c1c051204081b0a05090621030d05040b060a03080d150803070b010f170c040203040212 75
    0x41038140c0050041442511120b502c0c020406d04d074100f1a41004c00800c5140300004d0850355103005400e146448440c122426802809594406481c81d0400300074000320f0358246d40210070142c07501500380011000b000d0144103901c9998201c55101c03c04200d0b80528000706c103110041030b1490365802c03010b940c0607100c40d454900d2410042d11404000103005000c91503038480c50004100a002500d80c0111079400554000f0000c809180c484003008ac03c1c1c07007001800e20200e03201000040403191126103c80d905559000070600105100c00240c040154501e01401850708840d4010608034560b900c13070050052118400d822103180b0804440c1c0103c4e480f03c00e101030304800c003880e6400511864981000c86910b503020385114010040754609001150407001290180b40b10040042110a18110072050341c0d94580d0100650340408110101000250700030603049918001105400d55110f081060061560b54040080d035400815844842c0c141600070b90717030190009160701e540200345c800e004d040 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 225855674 1250 225854424 225854429
    0x140118030602030c031015020a201002030408011a030c1c0501062405070201080601081806010e010f0803030c0406032c0106080118020d02040b0d2103182406050a 71
    0x1358000401000740f03501101c03011800500001400c0c82c1200519030b8065180d803a15800a0144200158905000e4080344105050b000740504454601a440d003002034807074100d1b0207210444c1d401c0c80031a90340054942c0d100c00d51079500602801035040c0010030014500343d500c000700341081071211a80c0205000384508001850203d12400050401c0c503482048a60000480c00621400703124110260368000c030003940c40f0300c080c00c0100060b101d40a0420000c4082d00c6070322054827600002082d0002182c40c0c0030304a0f086c100c00050196200c90b14240c0b0b0307000466040701c0020013070000b003020342d00c650843c414042c01c080c0030006503d0408400b16580c000b00d02458021381d15144100042a02485004003a140301c03d6000100c01d82a40040c4201c03642c400007912031038490699040c150380e1a005464010b902c0b40c518108507001c0c90fa100e91511140760f07403c01013868288200c10400e880c1042ea070f500b950104a00d00003280244c1010f0b054030342e800300221020b990704c07400701d00b0752a000c040380302 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 225856924 1250 225855674 225855691
    0x1091205120a0305060a05010504180506030c1509120c0303070f0c09020f1305060f0706050a2408061501050712140409090512070b0105101704030e03061014011803060203 75
    0x56614042c400c0c41b05099441d40f10074100801040b0070810385101c4c428a410b801211080400c40307480342c0740060f241c103d41d12001544494854441c240c16440000140041c407802d4482e038040c905441e03103194441001941c41a0181c00170005003001030100800c5450251184445000e5592690301c0791040303801a0301c902052007000201c1040d41d07400660a2001020111703642d0b480c00d51840c910305000d02031250010011b603241e0001c41c0803024660418074105080100c00300610f42e40d801d00c000308160314801d0202902524001c2644600d8105a0340100501078650034542a180c0d0f80d000c2c00701c1c80010f488020409070207404040c65101c032008100900340038402003000f80c05801d04a040407500c0d0030006940b80100001030003d609000300c141101c108452244d14403000c1407056034100c000f000094840404281003008054114a0f06811100241c3c21241c1c56a81d0700350640509038a0b000d1842070f0341090850103590341c0304800b4581d0500c2010409480243e03a5542d440691300291030802 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 225858174 1250 225856924 225856931
    0x903061b0206090c03030d020a030e1204150f0219030c02030a1202010b060c0a061e0908040e0a05070c0b0711030714010c09030f120c02060d0c080901020901091205120a03 75
    0x101403030741004502d800c10710440103800c0c0e00b1100000240c2e01c0c41911880c41165401140901904d0f0280c2e120740c4480b807154003900d4028003c1011036005501600984614a00c0c0280280460b8818051020305003115001000c0140ca840e52001e0301c0d9190940803001c102804944c040141c500744000c58000740704410114090b42c905602a0940d5000070701180192824010204148400507000d0841a041500018822402100c118544000c104089003a80c140028082005140030081003243c0059202e00300c0384d19200101c04c1501c03000d5a2403000071751282d840c440410703401e542054000da01400c054940c94481503000d0b0039500202029a0203401240140c502c03c6070a006d0a60410154a45401d41d81e04503658000200301c0c0c400050400c0340d049003920300c13035030242d00c200c031002da0010506070f196120011400058084009150000307890003000ca08201e40500070b50380300b844161683c0341072a00b0700c8a00070440c1001501520329214001040c5900a6280020280c0b50210b0341c012 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 225859424 1250 225858174 225858221
    0x7030f02060a09030203120a11220e010b19200f010c020604082217030a120e0a030323042d0b0123060313060524010807090306 56
    0x80e0618000502c004086400c2020b6240001e41c003004541c951b1549140480081d2207a25105004007440005000d0700b2078002103c1c9045942c0707031000110b103a038000a00304c0352611140c40311912003080c40360030100318040c00104d80901a07150054460016494a20045002d039240060340340316000d0312030b105410845003080520000e0142c07158058544c0010002828295a607a10520500404100010600003101001d62545e080c080c01400b00808a000d4030300b0700e0002e50345030303841070403200c01150070400c2040441816016443c0d40c414070034007a026064450310140e018140044a881c451050200e072a101a40c030414418050f41c000e500c82d0f03850400c5480c00480c1aa5203c5601046030f60042400380025402c00f41e19040d142d140780b0b40046420414040300c14100c9104003d40c8c4030700040100f0903811460803050b004180a40828002503c0b00240c80d24a58aa00301c00130b40d816009405142c00e500502c4490f4200704c3d02c0c90903440c0360342d03607032605021510310001d011940a0500c00b00c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 225860674 1250 225859424 225859427
    0xc09040b0405040b06010c06060803130602010f0e030a05070c23030d17060111100908030601022506031503050105131202010b0108070f05040308040f08070b0a08280207030f 76
    0x45040100d01030341c00308032900782512036400c008401001c5c01e04115141184e4820041603403c981700610a9004590325140d520f40c0c40706001000e8054a80150b00c1c2c00d4101c4040b0065001d08070307201c194803000d10728000c1e1140e000c8406911160065460702011031000078440007441c8800000740518540c00682800304041605150283c1d90500800002042c80781a4502d12034402d41c003d202420701d180303007804030b00071503080c42244690103040b0340c0740c80301050034404900015840383e1002da083d1403002c0f00d800103640d42140402c2c0c0b0b803c00e4400015040c80024000e511920a02da80f401480c004c0c00c3e41e03a603d040c2034500480c6ca81458007135800c0008100300403640300601189442c00244000c1801c0c400007403044000503c00c0c0104a61140e86009003800303003085401440d00901620b0396942c880d00d440c0440f40441c410f00d0300610440c00e000a40744140e1050350280c180f688e0301d601c070645461300207201e80e0301140380c0d4040301c2e10b605501c06425900c1d07200420701140b0a441d0442c002c41c10b000d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 225861924 1250 225860674 225860681
    0xc07090b09070e040c030e01020c01060602070b13091d030a0302040302030111030105031b19030b01030b062d0619030518070f030305030c04050d080c01060f1203050a12050c0904 78
    0x3101d01909800007840401c0d6044110b40300c00351004e0320300040b01022880100d0140940c0b006003011544000f84c211880340307064009006965854007203500e074541e501039804191003608150201d901c0c11800c140a0088180c03c50038146845048840c3c0450080c880942542e100700e0f00800469800282001141028080c2011801c05168a01c5c1150325050110b0740307408501e442c1081040d600c219030003480e070b0381c0b840701401c01100c0640c0288864407454411000300d000e000650b801c00d10000010110314206a0460540c07036601014810404100e180101d080821910164800424400d814512941080034480c00d40f02d03560200d442d00f0114800d5400e04004204038040350801c9100f40459268500050704030303541840d05568980e038001200300540519044254805074440e01d0320300340a6a103000d015841003d400070009255661f8580342004c41a00c20402c4046003507183e14042409040540501c0b0070a0030400380b4541c040311310030300311a000c03521904c2841d004035915589003401e20 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 225863174 1250 225861924 225861941
    0x605010e01060e04050405150a02040608010e060a05120a0b190c03060506090d02040b0d050303061002030c0c060a12110c210d15180c030506030a0c0b0a0908030c0709 73
    0x10400103035414928010510400e81c0c3c4494000d030b440e640442d00f00002003100405130a0800040f41c2c280c01c1507841840070b07511510070b00000840c0d200c004188040c0c207098840c001c241c001c0c0b0800e0b8040c0382000780001041420f00074039640c0540c0c00d001001c110b6460055200d0361201014803600c2014580a40880d14410f807154101031804a0901c0b030b44d00c491007240c2086008070342c000a01e682e584000340291482d0880c05400080d020011402c21200101540c000c510480d0344a14a588004040740d03240203142e61804103030701a4080a040b810200000d026003030052030286540c2090204013401c0d6000542c010b0640540002e041c0c01c0150103001d4104074480c0d0142079010b94070481c04060483c00f44000d44044a42d42c0d05030075001402c20320300c0070000c020441c00003c824440c034403408014840070f464440840e003800c0c0040c2c064a004039a200301c16030b0001000d956035081150381d40954105170075003400d01c0001d240c041084901000078003180380352203005003851400c040d400e5081d01c5407107 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 225864424 1250 225863174 225863189
    0x30f010e030403060e1c0324080c0324040312020705030c0c150c0709050612060108031c02030609040b0606040504060b04170705060f090d1509110f01020a0204180b01060c060501 78
    0x1e40203a40d458207108861b9455005510380400e20824a2a1307014990f04082031520800c0a00640021074440c04940a42d030744c00124241e8080d0004044400b400c0d140e1070b051090b20085c41c1c1c00203800240110000c84494001c94001802d080d05541d03401d145900c000010880d540c0003100c400118a01071041c0c8031800440440705080111000b00d40c1d90300c05960203281d9000c0d84903030006a01da154064180349842241086814550355100c045480f6407114155500039842d04404c0b40003991300d4003c40303006810142c00b0b0115a90780781c549200c03802010304120381c4560104030000f80340c0ea0b1801510083d103c81c074480d698072440e01110081c6041c0e0740c0d02100b12904440010046035580000399031b41c100c031101c145030740c581e95800043e18070190510000d00c810403c0402c0c1c11003050070f60124030103d2040c90000d100700003600403c064410010170160040e40000c9440b401810180c00c2000c0303401042c4d01c2c440d01c25403a0307620400c0c65203098010314006401d013940d600501280d40111401032021 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 225865674 1250 225864424 225864433
    0x8070609061a0a050f010e120c030d05031603020f04120201111e15010e010b03040501060b130512070f0b0904020f030103061e090b0106110f061f080615040b030f010e030403060e 78
    0x40170000b8001b81030940c01c040c494002c110100450307510038003001c418008002e0603103043c1011028044e100e6002621a0800642c008202c5070b03040e4024400c45e024080c2c002203242c01e0a10700714010f0b50148640100b281000341d00b541d03107120710004000d8541001e011660481503a41c90001051a00d480014109131200d020070040012601464946055500304080c00d5502c0d07440703061660140c100d81c0e04c80f0150b01800104c001c08080881e000c14141c8070100c402c1e070002c00300064810390f540c400703000e2885410b00705002081201c489034018500303104054805410b002028041c94860740090b4010b40d059500d4070100c08640c816942c2c0d00c1c2500e608030104010701d8100d82c580104c500b00500400d01030101d04c110000071054104041101000d9040441d5014a00403400d00f0a10301a82d4004103405020712000c1105040031030028812400303040e060104002004c20040a441e06140c52a014001c0300c000004034802806448401c500c4100159501e901d5451f00780704455038028203001d150407 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 225866924 1250 225865674 225865699
    0x30a152c01050d0b04051c030911180609130222150b031f150c051b060d1a06030106091a0c0c0d05010b121b03030408030708070609061a0a05 62
    0x11640301403c1c0e000d400c052070b000c29507101d06c0d0581c40e0080d61020408a41c40d18101d82688543c580c000e0300000744210780ca58001c0346018180050300ca82c0e9040401e4071304420340000d810341806000c0561000c0510010b144d55005900404c5801400040d5401031415070b82c103413200b16500f4003a09a0752841500f40542d01890000606032501001c0c0c080d9070b400c00c414442a850f443e80c80c0600703010b402c551441ea06440d00c05040034029480d00030003145c00d0f000381a8030984038040000c20214a00c0d010b4074081c0340102058000000342840000c2120302d600d0200d96451640301e1001450180c1680d480700300645043c16080604440300e1900395121000403c10003140b84408141c2542d65041034524401240d2580741c80c03405400340d140c103d600640c10349518552060001014001c0c00700c08140d13001b12500e100c0906480c4c2c420350007000f4840d40100940000103054800900f0381c075005800010ba210455035030768007038550b010f5000c4044010400c1900040ca8940c64a1000f00012908108900d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 225868174 1250 225866924 225866929
    0xf0608010e1f060305070e0a080105060f010f301404050c09010506070303090f05100c0801080f0d1d10050403030f0e090a2708031b0403080f030a152c0105 68
    0x10035600829003015117030b00c042150b0601030046c2e0030364814010200f4854644a01c00c85000300310485060b81710314000d000c3c03201076500440c034051100c9065030380c1c0e5601c502c40c00c07441c40b0a1316800d40c5940c55400b0300074107064124228401c0c1e80c040480c1d401e400d9084d04281c209030385452110701100b4400d480c44c0d40100200c1d82c1e000112200380d64581804074055100f410142e503900c3c0b403090040c005004a052908000140e6400400400d4031078507400d0083c0d072502e25040e524100d44031210080d0303000d01c941c00c00035800b5401a0b000020030700840800048050046886480142070001c042078022609008140e0032022503481c1007290701d40032120450300700000b444000c0281c101e030ba07002c3e40c0f501d64060820440c407110300700d01c5003091030076050308140c505408294800c60307140c0301c01d965403803000d20510311000c105e6040b650094101c604102d80d010443c29164005032558800a0b0389000400410484812190080440a0310032070036944035200b0b540c030942c0ac9010503011824550041c011a0b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 225869424 1250 225868174 225868231
    0x90204080c0d03020a060e0c0a0b0c0c0d0c09060803040608150906010f0c0204110301051203120c0315090901090318060c1515030c050a06080402010e0f01090f0608010e 74
    0x50700215041d0600d58080d04059051030344420019213040e051401e517044030324002448200e103800945007048a2036540e40d0601c00c0e8041c0e8480200560010805074003240790080325600c280e8040c5000409440d60748907050125003950384412640d0b0004a41007002642014001e984030b494811050b2050100c070340018400d15000340720905024100a151560a200c0e185460407a90301030000c2103840c8003000010002e40091240034406c000d5007207142c003410808400e4400d050710320324105a01e521032100b04030b2690401013000d114000d801a0781042c0365030310301200707000708603810001401c0e0310701e400e00401611548281da100c500315034a04000859002c0200341913190000700100402002d001c0304005405a080c0d280500903004101006103c01d11849404480c8201c5a980303a0a5550f40140c900200450300070b8003285c5420940a142d003050425948181e4051600b044070f075899608442403080c40f60403140010380b8203030061169100001840d90030003410701e41d45204004c0d0613a4030900 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 225870674 1250 225869424 225869443
    0x70309020127150305010f15140904020f0a261003170408010207030f0219030c11010c05010509031e04080601031506080d0302070312110d18020306070c030909020408 73
    0x101c07548030400307241d002c0c103000d1040c01508070220405038440307400000501a042c00e006240c07100c1c100100000d0307121000550302d8105074080d110300411050762600e21449412420016400c26000c001c400745d0199908c0003440321201a84480d005e20003444d0109031292003003003141001e100c1c84810300000c07010042c2640708903a0311051681505405c625110524021548490020340c0049401000c040d04045071242c02c609503800c135020100e1921490007032108800015010418203154440420540d08803c1c040441c181040079a50503d6501c0030700711541102d200785140c101181124400482401c021021700075444202e00303060810880c00e03101c034018400101084a000d0440c0c036040c155401010060100205aa080d000500000f034003035841300900300e00007800c1654400e220744581c0f01c0c0491856409802e2400e0055956416004115030360400820303401d180b000f000141d80810155100740f034156100c4140002c54a000380103581c02c1d400c0b004131302d4014803080c080c400b2300088451f035 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 225871924 1250 225870674 225870707
    0x61203040b0d02090904030f020d0305010f090b12060c030105030706023f0304050a030305060603160f050d0603060b0108060607050a031b0219080c030c030309040f020f03090709050703090201 84
    0x76508042c2c06101c00a102d6200320720340000d04e180811080c1500480009005a02502500e9091421060880031100300b402030b00c00c0d01d030701c6071f03410b200c1e1800315880b02c2c10011020b0542000413911030007081c904a4115445003c1c000004014031160030140005001040d081c00207003250803024266401c214040c00381c80c21f4486550300b89014504c02c00c25440030314035202046030359908140c1400790722001003000c2070f000320741070070b02045072801c18004580c030555000c0d07240f007240041d40100310751400b2590b111504100c0d01b0b10000aa010042c0f0480e4000c62240c50005440840100050040040141028414181401410b011500c04500e001200d03034140740c4001f001824010314081c0d619000b0002e500410400050320206100040100641e040401195414070241c010156203980700c0510380c1e0103820901c03814805080c550055089041400005400d04144800d041000c0e00201e44120b1707254401102082410500c4c80b030280c0100701844c0501c040b0085400207444ca80505483c0b48 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 225873174 1250 225871924 225871927
    0x3010207170f0f0f030702060f070806040c051c0207060c090623040e090d090506090604140307050409150506060708121308030a092a0b03090114040605040b061203040b 74
    0x2c02c0c0d008510440302494450303849151100702503586036166800031a003810240c403442c4041034003106070204241c03254400d9a151031250b514041840050451144400c081c0300081c800d040c8035607001c603c8480200c2d03e04000680704d01190802000740c440018681e0300344040c038403007403044540c04100904020701d0400764584603d01b6040c0d07440b41c1d10444d480b1141118000007440901800403c4940d5141030580d145031040791101c0400c80750744611101c20340d000700300304800c000c07080350040d103081010001030544440954840c007081c00d4420b0310000300c0f82002245040341d03840e51180b00d1150480e03403c2e202d460401c502a601c509040c13240521840391a0b04880018402c200750b05ca0314000070f07600c009202d4490901c296050082c03c04450f048844144619040040c001880081c9601e107400e90303c040403040c0351a41c082030580c0003500e131080319502c42c00e106c40780b05025005c80340101d22444001800f46401d0900421207900941040d1203040d00c09100b180503000082960141e88400302c0b0203 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 225874424 1250 225873174 225873187
    0x218060c07121a1b09040f0e06010f0815070e040e010209043210141309050c010906030c0c020f04060515070b07050423040e0f0a0201020c0301020717 66
    0x64075106556015212034084080c0200c1003040c0c4010148843e410906412142c1c0c403400c03245500c40a6055000b90410030901501ca83ca103020342003081012955100010001065909141403200036000304c901e29500e007030100014034082001650f2124130a04100482c1002840140300c0003002060500c1151101604003d40000b035040300c046190060003000900b8141034412040318013255180720038031540300041e9041b00818a8244201c0c1207040c80300c44107041442e102080010402c6481d00aa40e401d0450324003040d5114180320a0300580061036051540e60005007100003e41003e0101410000f1100215802191842502d541101d00d01d0000100401081c014110b542c0070544c0696207519a00c5505900e00c001d00642b40541e003003d400e0b554010017580e01d44110301c00c00000341102d410520800704000c9401185910040000c150752060441882c41c00000e2240e00c0c0c125000500a00308568040001c01440c0b5801e07002541800303400d45444007154142102c40d0010170b07002920 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 225875674 1250 225874424 225874447
    0x40b092e06050f0f0f0a020f06060d0803061201060810020903060112020105121503010614090c041a03040f080c1e011b0c0203010f02160309051507060c090f0b07020103050a021806 79
    0x2521917400d1100d420300d480301d1100c0740007903480c6010f080d119170500444002c9011828104080811590040f04a920f152106028011151000346218602c0e5503103000114240b0028400b24010240c4c45102684135000c2c074040504000040c2d2258100711400f104140050342c05c00c003510380000300082d10205035915500301440421002c92119407651070854003003404c0182552001c08040705441c0140240e1b95060703102c2c101e11850282621803002c081102c2403c403805001590322610600b01d1820b12901561104c099400540c0940f2060f0801c0c80d941d00c01e04d54000d02c0350002c80c4400001d00900c49008482c20812004c440c150082003022103075501507403800d4000745c040d40a00c1008550702c900211900110024404003200003841401d800503180c41d0256440300b4500402060701d03e8200c2641e20980105002d94500083c40702c41c2400041c400f8101d1a4007005020003181d170340e600c01144c03000604441c0010101c98940b03205001c040c1c1402110700b00050707890410f441d96075496005814 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 225876924 1250 225875674 225875677
    0x80c0904110a091a03040309120807020405040c03020102010e0a031b05030f0d0b122a010c140d020d09030b043c020f01030902030d0806040b092e06050f0f 68
    0x41c0c071103031040001c0c14a00b00c9501440c190111150b9401c0100710390074002118a65100a56014001449905007817000b07071700750582036515501c21080c540c42d04085d5808a002d07160116010b548030150360104005558081c0902810440400c000e0f1120b54801d9030080c0c0040c2c0c43c460f1007520351260b400300c1000c019080045a1011200c0410240c40e4090f00084174040d0101c6030303545000703140d5906040814000001d20f18204100100811041c9004d0b5110b038071401f241c02c5496040001c111041400719905148050301d43c10b4600140c08030109907a030103440c2c4803060020b81d042100445007080030460248101e40c00030390140402c0205064030f4001080d4024043c2c07114502071011a40360302c0864440d04242c5800e1090312028441502540150101c42240c40c02039003603048000f07040708540c802c4880951103c00140006260410348011503024501158542a00316814201c82c400b440c6441c846980e01584040b54101e01c3e0502c0c0b0010024060101d10719064007007c200007120850080 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 225878174 1250 225876924 225876941
    0x31707020c0904060b030c060403050d0509041e09200306010302060307140d0b1921020109080a081201052202071511030f0f070e0d050a060204061101050115080c0904 73
    0x2002c1e2055401c06040140060054030b40d50782c803900c10710031500c101d4101041135030210fa4121019108039040c3c400300351007961048190303d901954030041c00c503007209143c002124503084200f000600010030f10302012010f021006130900c072149045048650740d0001052030643c0d5042d01d13941d4036511810f03002d884a812840e150018101c0214a05102010980c00004148811a1041c19014040c0e01c2c0902140960084103607200c9030b178071f030550f14040444004004502c10700d41002c0040e40e9a07422820310390106011078019100140e2008100102c030071070390142c40c044800303d124040001d04a40c44607908040c001d095900803c041c010311100040b0011303c0911414207004034041203540380324580c800c8889040c2e114500011070b210300709000e061b40c89802c4540f10650601e0715001002807103640f0700c0c012540e03841a07e040f24005490350010300001c00301a2560480401c1942c07001b425244142c20181886115040c50444607502c1030029810050216134503a030360403001c010901801029 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 225879424 1250 225878174 225878179
    0x1b03140f0313030306050913060c0c05030315091f0e07110607030518010b0f010507061104060e030f0a050c0105220305030a02010b030a0b070f020f0a031e020604031707020c 76
    0x10040001000b103106402454511075035040011645801c20000181c0c41911001d960550321030150b00060f0080c0d001201403040350800c2000103a0ba075848914541c02282e440d0500409041281e6450401c1d24070070ba0841c1104014001840d00008a00a03555440c0f01d40d5001d00300c22004200e00f01d005414685000c00444181c403913910348008050701503c0103030b41402040e804022440c100000605c00d0000640b001081039036460300d01801120305410410f0161080340c4e41e030003454001d0400d0002003000307007081d803203c19000300d06400305802c1040800c00440d10341c0140a920000443c007099648040c5000d09100741c40304021035210b03069100c50600c030308d020304020f8404014400000007500201180340c0c001c6c04104800340c2070586682901e00020895502540800d004070301403901000d844071544101c0340040c089030900e92422464240c2500481e503810002c070900d40083c64001c0100c03510307000500981c2481d035402811040c007a600d80c6100414030000c195418828860b007481000300 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 225880674 1250 225879424 225879427
    0x90109180207111804080d0b1e0102070e0702070603020a0903050a05060a15060503150303120112030305151f0509040617060f0103120c03090509041406071b03140f 72
    0x44600e400002d50210720181c841512000020140e40b9140e40d0380e00340c0c0d2419041040d055260380c4d40b038041940050224403080364642680800b00c0c1c60300c80e4000780d09040315031012426913525002900300200e9400a04131900e1410402c041d9980014900007256254600169952210801110803481c0341d00001d14a019822511090010006409026000103881005041309a540d00100b0300414407072030300030030824000191030840c0d10041140b0401d016041e20f00d025602d04601d104088240c100b01c90260700310305200103069261003040c0d17000085600404034012201e000074140c00900d06203102d601d480c0080c0c00c3c240d52055082d58a81d000207041030145079240e1590348006101002b00300d5181c1f091200040c0300641484034a4101d1360051803102e035001490300c0454140080c07503000d0703040c0046604005a0350b102d51001a1046000e074031813040d4881000780d410b09008025000a08210b410381c81c2203000c0407600307401d40c00e90794907080c0034081d07851243c13450f0514040d000b00c00010300030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 225881924 1250 225880674 225880709
    0xc050705060409020a020c011e1d04140403021218090a06030b07030605040b0f0108040b100f12030806030a0201080c07050709090c050a1d010e041e03051b060912090109 74
    0x10320350058440ca1400b40c0030307690300c0d54541e4011a40021034425078a03035040280003a182e00e070300ad0381b6040d00320401d5115100746080018042010b44005140e428118140c070410042410b605200b0300030850004c1460a01d040e100032400d04c025280400d4540c861510723080460301418a95220000031640008400e0140c503080502800a02440c4141400785050840501325450440b20303544101d54140c4403482151135940750605c071500010100e40700d01d04012008a5a080d054040b6001042d0f000041c0760500044c0ca40141031080140284e8080d07407000285000603a003011045a0000100380300944601d41030404500c0d1201c9540041303000c031325003000314041c800900203440c10365405035211062a60340d060107018240448180b900c0b01884000140b02011000086c00d8020303001e403001c036110b01c081080c440c81c0590181401c0b80460000035081d60f100d41f200b0400036015069001a0241d03160042d601911004442c034401c1c13203080001416001c5a010f01130401c090015540f141c0708140 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 225883174 1250 225881924 225881939
    0x10e0325050103050c040b07050a0f050307031d090f10030c1e0806151509180f060402071e050118060504170703021506041d07030204050a0209060a0c0507050604 71
    0x1000d80300c0388400403801103004aa594028040d0328010100c24034550700d40740c50300740300120070b0300703c0c501c210b440d03008819404000c1041e500d00164468001c3c0c01540c0e03501403500c2e028066222281044601e03410440c1100381c5581d4010155034403d481124540c056030b42c01c00d42000a5003903420003817008482140100e842007841d07411030341d61101040710110454031100c3c4643eaa04040b130b006050304140130380c080182d041000350f41c1e07420800c882d411420410f1000c0007682003565001c80c0840d1500c841c04101c3d0022a407801160401d0050300d04525100d00d0b134541e4043d079011030049550004020031410700300720003544100d403a00a20003044500166030725002d8050001071ba0103840c1070150f411540d0750f190030001102d13407a65144d00241022502d4000c10a0810002044650b01c10351700c80c0c0d131103100c884d04c11003040004025001303049118110320420080b10005000c0100951060200c110079403583c4085611204803414414440003840ca0410710380091504046c1d000000400c0004030740 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 225884424 1250 225883174 225883213
    0x6021b03042105060106120f02040602010f060b0c030f03060a030501050c0c0106050102010c0e040515150901080a0c0804140123040209070806150d060803130303080f090703030e010e03 81
    0xc54102d6071014281218400710070700c0e003072020720180c580d80140c0c00410805010b51034030988003401c1b4801041e0000c5140c5c21500b07d070420f9214001503512808001810601751090a004d030009001041c1005000201c00782e41e4040c80d041903459000001c080b9100b0b0752215449030003140d1100090002e450310b05908080340d0803001d00000a0341c00c00c50042055801809401030300d480d0ba60300c4900070a0000100009010098000914002011414111501c0e1000e40915540c94800304130341d54010600014a02c640050485560320320b003a4000c1c0b8501d500103d46500540c00c100c003000907030040b4401b0707801408091000b00d1464054000418030130608920704e485a4001c0b00d1848480d50b07502c00680e41d00e081225040d07440b50b003d0380c81d0342000e00c201000d040c08112449001401d103480396090303403a645c80210004454008050100205075011148913880280c0400c1c5641c03500380000a039944414a000003024000740c0d41c1d6070321050748540102c16203940c00a084400f250b103180c2090004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 225885674 1250 225884424 225884429
    0x10e061501140a05030402010e010e04150f0b040e070e03070e01240305090604080d060513062409051005070b0f040201080108012a02031b07050a1d0a0906021b0304 72
    0x4108800031400340c503042d02007510749040c020348541e441c1d40e4450780111030f050a0000000d0601a440301181d80302d0302d80b4442c000d4110180c0480c0c400403810100c0b0104031203050790150780319120400060061810024400380c00071000e00740f0100c00d114040000341441340c02d1300850183d1701000000162101034122041000b030401030b0807400003510440407800d641003120788030810707801140031400144502c0300405490180c5d030b000041045c4c03100001040d0043c2c44030340d0394415442c1c141c148015803a40003261b1100c07609820030a108400f10300c0182104016200d0179100380d215507051403206004000f00d6440b550300080d060b00e503181406001001600549041e0700180b10600089140a0148541904502c0f107400310705056200c001c9000403403401c030342c40c0310841c00140b0045e03e02c100349551852140f0488000313040282d0401e014010040c030554064004640d0030060300020361b2a1a6416402c0030030000e011880e20b0035814a4030107841030007102c1660001011410410200c040081c109 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 225886924 1250 225885674 225885677
    0x24030210030608060c071e110f040204230a050d050607030c020c06210906010605071704030b18061605070602130f06030905010b0a08070b0a0e030106121101021b01050705010e061501 80
    0x60f0742d07154a01f81c42c840c2c0300c000000d000318684401c0d0740881c60104120318a40344010000340c41d198440003004020311541680c845131080c80c0804907541d28009042c1c40c00b80201741d80d60030b054507003600c660b541d85501804550525a8910700d000141d4030901140c03818003006014155225258464098140000340400c0c088080c1040403410184000c200281200c2032903440740e0030314541c0e0f00c0300c1c003020595080002100c4000c00002000070a01a491840342e4000380f00441c0b0f100c004240740b810290001d181070580c12004c0701040615030820244d440c1113802c401c0044c0c85a0022140130154074943d0030480700031aa800c4009201c681c50b0f041420068441d40090061031030003014003100703d90500907207803036412907202486292080809000302030040c0c0786c0000e801e200c14020908645050700081e1036002011001c000344030400190b000c00740300c00e00c010100701030301c0440b00722490031b0140850304001d000512401440720940080d2450344100054902c24148000030901c0c00c0d444020450 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 225888174 1250 225886924 225886943
    0xc02030a0b01091406061923031602032107020a050f010c02010c03180b04020d0c09020912240c09030609030a0e0d12030c0311031924030210030608060c07 68
    0x40c1c56004213140c10300404016106c030b03040419054501c041c100b030050b1039408000044040b0382c40042e00d0b10b1002038070180c90100c150342e0300b4940c4c0c440c020102000c000900b03651040104403840c14090a05504044011201410301c0d103030580100d00b000c0e64403c02610600c0b486050080031401940b1504218146400801000c0500c10095050301e00704400d1200155407198036101041e11003c2081d406072000700390710328924456440b0103421030141c2000c0b09140d40802c03694201d09080b60040c12a5079100c0081c070a9908254103495040a15825031004104d690701042518a0f00c1007a6180c000000302a513802d49460b010060f0b0302e8002e0184080002d20205c0d04076000d040804419498035008000c2c0c0150300c00c803000540180400384480b0041659400700c0420040050b80614043c00030000c1d10600a200401220141c42d200703070300041904280b840120711840081c003024126036041d0b420040e800bd4041c1c05400428240d0702c149841e0207808100b0040c0c590050062089501c03482060 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 225889424 1250 225888174 225888191
    0x2011415030c060a030212100501030f06030b0a0902060405100203180a03030206071103070204060e041205030121080906040608010315110301170709020a03150e13120c02030a0b0109 80
    0x381240900019950140c0190510840c142030000082c0070303502050501516000340c02d804042429400c40d101c0c1d80c1e000441e40c003400190781c503008520b28a00e0b400307001c2c441c0d1400c54446c0c641216000d0858035440742d50ba4000c10440d1954001e4400900000b0000d401250080d540a902c82d030007402040700e075520003400008070345407200061096a8043e07004002c15030f92200141c80180e0080415120303484140801d10041e9141c0c05120050028241031189900700381c94043e0301c810364034411900b400000d000502443d003603032055003c00c400940620080500703a003400041803150000e00d41e04800c00240125a0350380140344203048038400e51080420050315010b105c2107039440044a00720080400c010040090505485400b14075801c0c19205160342d2280220100d0f4080d107404130219856003805d51210955014900003020a950340c45160714110b03150148843c00b501c4010720f45400d440a4161861081c4100001c00307902804541130307000f8508004940c40024401e50000c103043c03d050 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 225890674 1250 225889424 225889441
    0x2b020d0e0a080a050a0306050a0603061401020d0e010e0607020402030406140705090a0302010807050d06032a0b0403230d080f130c140112020d0902030c060a120b1807020114 76
    0x4001c0c9034001c00700c0b505242d412101280c4551002692404054680348042034590f0b4450148009040c0d40d20001295882e09960486c110030040140303041d508a150307210300d85600310b00036540b042c209181a400d22005100050b12a010300003010750450301c013000300703c00c00c1302c07582c400c0342d10000115800e05556501e078012182c5112350f02049401c16203194081006500038810250030040d582441420720700070105040c1182c0b4564410f40e1400c0c04e15858408a41c2c0030a0107451010382c4084001515007460040c100f036101d02c1c80010890382400da0b202101201310b10950002c20002000da6004800c4018010151281030740c60311902d070250004181700440c107030009180194400c900110091a20701c038400c0010303000c48614144850140b4008002c0200c2c4000c0850350140c2000280030250360044c50301e05148800034501a420410101071110b03000010f042c8418540d45001c1a0380004401140b2101c50000d025460002000240810180c064001360074407a00c0185401c00703581c61000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 225891924 1250 225890674 225890683
    0x160b0a0206100f0902030408040302040c02060f0105010507170306010905030307030302040f0b030402030604261b060702010608030301090507030b04020c03031b34050f070602070b040b0306062b020d0e 88
    0x10b403c600d4038a5036070801841c403154018592040c001d00403c0e04282e520740116054510f64078484006800c408200b040ca00d032682c15103800f51100386005130030200c1c650f69400e1803465a01a030020745801100184060307214a518002401d070150503291552a07526000d4042d401c980250f09040403034200205045500d941a244165001030003403142d0789482d1240152090454140129101c003c0b641e0f03120040d0042c0117290115400046284800c40e01d40729504210010b082d0703070116414100104091040041903a041d50341990380000d0700d403664513065004000208142d0340160011610b0300c01e140c80400954030540080350001c0004145c0d400031182486808084000385440c4d60300c00f1446043d2039042903900000300c50b05e40384030050b034076814070b80305404e1158089035005a205100c0c0c250305020700c4d001400c540110313030f007468140050120640030080080b0b004031070209000070a1080400b9904142d5004444003070a040e01d254100701a60200788440011070404003a52511800041d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 225893174 1250 225891924 225891929
    0x20105060a090b01092c06060a020d0f1101061502010b030c011e261e04050601171e010b040b0105032a0403080301080312090c01120e160b0a020610 65
    0x5254114440c28900c2d628020124882c1039810000342d0480811100c0080f424800303c0300014840700c03d5281e00d03001a2500081c01400340d80201d2040c8640c2100980005040c107504a66090507200030300c0740e11f01250442c1070813421038251b40c2800d0000581d082c0d90a003219545120354001e00c00300c924401803560300c9000305041800a0341c01141d040350040503000000120700b180c82c5c0f280c02480304007400714000818207401201e10200501340815910450724000742c0e400c1c2991070080c04e24060321901c1d1182c2c01403081d030b607903d4141880900d400e1402e0110050b40094844102c4145a62074080d50003030240c2041c0d140544e107044106803041d030044003a6841200c801c0b2410203000440c030303508002000d402078450900c2405000100004030804040c501809103d0010340d19410213191201044101506840003030f00f107001a80c1507030340d100d11507043c8540025800f140201800d45560b241603500b8005441d51030b14a40c000c5a40c055001c010300307003010300d036017100d01c9503c64102c100070a01051 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 225894424 1250 225893174 225893179
    0x6090708090a0b09030403020303071109071806120212090a0318030b01050f0307080a1b0b0408100504080d090309080106081203040609030306030f060e0709020306060f09030115030f0308010602010506 88
    0x4403108070001d24011a6668460104c40a480c102692075021901d0b5410040f402c40380c20b03c0d030761031048490401c5000640c5c054654030303008410241c1c0c0300c0c0005040d00140980c2c3c042000e040250301a200154044413803840074640718124a1801c1d8411075181e152250048002841075100b14214415200e4541d0507242c0146082d83e65910303250812410b4009440c25540602481d90300048a00003804814051800760b84400800c801d9069400d41c4802c2c6908a0807100600f40010704c0840b4001800c00402c0c80400000502920b41307040588842c09046405180c40d801c0824003010907901054200842e0070001c002d20060703440c1c0f001543c41c0c05030302c0400c0528640030710005001c01c2c0240c1003480b030540642000030b10f10b9101c5d22046403070f1507800f20a850054440e42c2c100f001c0c200411420005080e0170381d085042d03042000025007131384a5a001071503a5080441e071006507076029844141e041c0044040e0808695403032405624150301004141c001c90001c0c000002c14a0040c010b41c0e00ca060f00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 225895674 1250 225894424 225894433
    0x60a02130e06120607050301170a0f0209060a0503030a090e130201021c112d06070f0c060e0312060a060309050303010504051f0f150201091509170a080609070809 71
    0x200001c020a03814000d00351540b100e255030b02041a40c0301440701e54090005590307002e030f0b65814041c83d804645030600d10009a540440b08203804075070700c6c0117806582c0390f0485400c083c6442d60070025400000e02d41010360300d400b002610044203a04100307402d0440d1800c0011a00766951540d40c82038020214002034056049141050200102c40c46090010220b500380380040d4000000b1291034100e58914504600c019052020380105004c010106110b010341e00402051801c2d030700c000e2035800005680c00901a10400d184100080c07900b26030001e040100460703480b0501c01c2d07c02e0b0340c50501690600d01442c0e5851001c41d02d03a11a01888100541010065146902e0700d4103100080c540207000f02440c50fa400683c01661002d014002d000f440d154141010440c1002b0802c04045802564601036a01d4072001500140340c0e47c1c440c4207101281f03100040c00c01403c2c1401c030380810428003031500e1580001351140d1502d07008a60240109000d4442800c05d581d22102510128016a080c40d4550700 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 225896924 1250 225895674 225895679
    0x3070302010f020307080301030f0209060603041205300105120312060607210c0605241509030a08120109050106020a110f031203010e0a0b01141303150c02060a0213 72
    0x7214406860601441100d02d0705c0056218516942c1080e0011102c2070400c1d0004c00561800c542c81b1034001808440452460505a59840b002110101c403d014080041001081c80b0080101007613010005c80b007a10102e0151004400581001d009840c0302d8440311001070325003000001610b0b988580c904640d9055240c80d002c02c0040d03040f500088592040d140c40001201040c403030748461079403150300d82c0700304c1c841035103414070035658010504240c007140a08060740e4103013450b07042130f80c2e4401500d04041341c032400d42c15000e8510860080389d070140320780b4100908018030f03040108002002d01000c00a80e036204d4201d142554021301c190340c0142e10408044001c20015650190204402820034091146000201e400c000c107040da0040b00c45008801045001c091a491681c0141d070b010041061042d00c00020705400101660f0b840120303008500d40c04a2480340c0644000745070070160903d241c100c1c0c030f0309040180c03100c0810100180151030101d9140c0341e00d4001ea0f55121101c40c60880d03000e0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 225898174 1250 225896924 225896927
    0x3160506040e270f0c03060601020a0201050c0109060e060a0b0a0605070206090a080706030221010f034e091406090409060207030f140906040306050705071b05040c05090307030201 79
    0x140c0940000110f90401d1000f00e1182c480c0403041e012007484401900b0905900c551690078000100711a9000e90446410801e040e80e01007894800e0590908209860313a4a0340e03003403801420381d001c0c01000f4a01e00740c1400040c24000501c0b0b1f1090813032100034090b50a9000070311401c600e603886102c0100c1e60038418040140b50820180044240c0a04050601669000060720345400c9074441d401082d40040c58540a405160b40d148013040001c6030700c0d095525101080300340031171a01c005050082c00a2103c100190610001a81da0190030341402407a4540c0b40d65003480c068807040381c124031481c0e601d10031085000e042040101d640c3c00940c904140714050521665504c100d418541c01640c8a80c0300c00007c24034409416075501035603403114502d0b01d802c40600301101e0b903440e80c12011003d01180303003581e6400b000c0380c040c0c0b680000041079a4545450a6416003d076038001441e010740782e102022403804199902003222000c42d004e1140102c000c0013905c403880f40000303031500f68114010600255 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 225899280 1106 225898174 225898199
    0xf06080408092215030b0402010305070216060f0807020c0109061d03030d06090c08090607031d030c060708101202060a0903020d05010506031002030c3108010501050316050604 77
    0x180c2951074146c500710b0010802410152108005440180300740080c190312004000d94a075a262142c0b80501050603010b0804009065400019181c80c40000e00e106081c1040c5c4601032150308118040754112101c1d45003611120814902680075181000107006069441170005903445c14a0300034020f0b40c842451071000c02074014140f04c180503021034040e8000aa508000070455510040e0070211100d0b5003003072285000100e00507500507004034ae070714414032079070f610058980e8071072084200c03d10302070003070003041680c01d101e09005081050080c0880580750402d59201582c0b94005846a107120504603420794582040c02034a08081008521580c40c8660650030761038038180350740301c40c01880900068903514124590f8002c00c000c511200c4506451030302107046494003580ca020340803c0c811580240b05001003200d00707400d0b07141e4200940d01e004010616152420a105010 = true := by decide +kernel

theorem cover : BRFrame.Cov 225719424 225899280 := by
  have h0 := BRFrame.cov_init 225719424
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225719424 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 225719424 ≤ n) (h2 : n < 225899280) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
