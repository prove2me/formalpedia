-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5008
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:26:46.009984+00:00
-- url     : https://prove2.me/submissions/0743ba1a-8ac3-490e-85d7-346c309eb2ee

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 900539568 ≤ n < 900719424 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 900540818 1250 900539568 900539573
    0x100506070b2a0c060402090615030a11090d03110705010201060b04050915030f030318070b2d0d0207060f02070b22050d09030b070807020d0f03060e0702280807 70
    0x210015003950400b03080e82030320750002006800003404411080fa805408140780c9401400790494009090710302c50303540d001b0000242400c1e00142d940080400100240c1000b001d03902005921521640b0b83d404260403620301c04150b0b05c1242c00d40c4120446094691017035880340164240d901c0b500a001c040720080c031080c4401c0c04c01100480c2d00080c1940c02040046154011904007680503107420856000001001410185002100d19920400000b000d40c03500d0240c00c1021409122145011700290061b038101c0ba80581d165416040340604095540383e034072104030002540402000c0b1103280c1009102c92070b0483c01e10075a04040d4100ba01c1c44c1181d41c86501e0620f0911b505a50801d03500d030f00c1620200441c00800c1141400c00254a820707110b00e04501b400ea024002c0100a89c1c20450100c0800262a0b40420445008555030400d03a9020244050590240c035942c1c001810280c81d10703080003100c80e0b00040302020101c143e02d05d80d615040d401000324903612040d10140c60481d003008010b00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 900542068 1250 900540818 900540841
    0x4060f0801230402190503010e07020a03020d1b15050a0b0603040507031212050a060e060301150e0c0c060a27051902060904020706090b0603010b180a23100506070b 72
    0x540000030801880c20691040c400ea05d000e581802d040000d1010005125681585594030740100071030000b000f008049a600940e92400c4c07402600c10404990789a260b034014158080c0c0246a103c00001124030001c50f000c001040102d88101010b41051103001e810305009007203a01650f0040e001d08449400c6456055552202c1d286510421a5144982c4182180d901c00d460042010180c003103841480d0090703440c1949400780c40103100741d1410319455014081c160515080f13b09110f80007155030356145c1c880026026130b15000c030181c028241005800e0003541e11054025580541c0c845250f4001c418200820780c950700000c01030f500400707120454036100284080f40920041c25145041c20200218060b40c0000404443c1d0340d88510540301001040040c495110751b00703800800906400c240080d82401c042441a0440001c40c00420855042500003080004080320300c0152810740518140508008a980c10904201d0b00310200e45031822404442c14030390014000b43c126192080780340d1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 900543318 1250 900542068 900542129
    0x109061404110903060405010603060f180b0a0b1206160503090a1b12080304030212090d06021e0c240106121d1902011103072301020c0a0804060f0801 66
    0x940a40c00340b00c28001584e00b008582c1c132440c418030001c140f03189540f42c01802d54110502d044c802504161904107182c0c901303414010f0407504580c2014641c0c880b5400b0300c006140e180c900c00e800c12600a00c0001b410400540c10340a55a160800390384403a007402300301c1d0729010a4452008a0b00082e0071000440d1010005200807644d20300c0c2c00e2903031136458500a44400f20210106c0368104c0220401c03080c980c06110819640b00d200002c28540182079000542014141340000c1c5065030100e401d071152030b10703050118036114005248a99078809040150b60f034510040725400e0310702d44d9103102e840d58649520310314100c840348e88038941e000c0e001c003003801c008e0950b12603074000401d01c0d0044402c02c0b0350200141c038041f00d1044c0441d102c3d424a4000100343c58000e22002105034020000d140004078641c8450480110b1b10483c651284072501060380a44908400c90390740d84503005581c424040903500034411541c068681c00c4000c2140300007a02c030030b2024814031059403002d21100301c92003600d0b43c614 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 900544568 1250 900543318 900543341
    0x260103050a02190b04030c150804050706030e010207020909060f0901091208090c03100b0f06180d02061e03061003140f06030a060203010b0a020c1503062b1a0109061404 74
    0x18810503464200414198100307520954000702d1f45901040800400c40840840484900e44511945080d07142c50307a80e02c0c5640301c4c401c00c15646050340440c910082d4107440c25a64000c0071040c0354246603444075501c800981e60418844da5001c04110640014031a02c4103459001056aa000340214010340300c000009141e10b030343c0c3c01402a814160b5030b090111110501610344001018081d000a002d80d20f90310201c014040d81c0d00300b0a90310b0001c41e500c00348903d824200c64002e602c080300e01c081807190044030461030011803480750351952820344601540c402c030425103d1381c0c805654880304400381c401c50b0030004281150310000c00c080d401c60301a8203600100c06821180981c1880d5a52070481e8401d0780443d10501000c510f08080542c10302c004581d48034100c5403104030f5035003020100303000c3c80003a02e403501c2621a1140c01128a5400800d130b400d001000d1106002035141e0305001c0482d940410040c0882c0701d5640011621b0307032051080700e05540c40303405074108011031142840000e2000c00102c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 900545818 1250 900544568 900544609
    0x1b3c110604030f12140703140d2408010c140306040c0e10090f06081909021503190b0303130b13050a081f020307080705070f06020307260103050a02 65
    0x407000c5040000306000742d41c821103181480344c08011000300402c2d074007003500b85003d00411510b800300303500040350303130404101e90012541c0b0f00c030305002203000300030954038070041d100301c00c0640a216480207008001c0b503107640000c0c4102b50807072504850040d50f40c10280d51040081c03002c60803908059200c0c40c0d00004904080b840c892982e00012000070940140310002900080309102c00410784038544000d00e41030400c2d0390b0608240944500d070482c0c4030b4441d00d50175a0b5440c0c0c0d41c10340d44da840d034840f002c600040d100d81da45e0401c8000b202c0a105070303407154095103042c0b000d8000107040c0002101c400300781080071201d400e407c142654100d9031104c13545140980b0315981c085582d64400c01e04ea40189041001080c1d01b180360580b503016685c500786000a01403043c800c000c911900121101d130710010f00d280c110395a15940ca003603243d00061010181040c0c1c8003000b08217085411510380d0520004aa203a038031262240c80200c4001642400300405940244001000504140c024a18030fa4800d000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 900547068 1250 900545818 900545827
    0x140301060b030c0403051516140708030c2d0406051c1b080a0209010806091e0f150a05030c0f0a1211181005060a1b3c1106 54
    0x441c007041c0c0c10a45042901c0c0400040c204200601042200010300f89480308142601d844c2c9420382188007400280005e01c05002d210b00a51103250b82200c4089500680e01a22418042988056030300080241c02d0000d007009110200b41d981040341102030008000c4261419090100844650308910343c1f01c50300114900e061a0000310b02e009030b50480c0c0c41d5203800c09402045440050043c5805840036a40d98410005001266481700070b15070701c00025100b0908903119008203440010805002080b080c101034113000f01c0c1607103000d049010b100040c0c4c1e4141d00003c500200200341c6141d1081982c107505c110180750603408e0644258003d1400203002402c03065443e1400d58105039003e0048540500c020b4403036040789895469581141c0d0000e9450b11280303440901c40c18148481d0241c1407283ca03022030070341c024901c140318000f00800c8282444880d400c1514000303581c00d0300603d900801ea181d02d0064002d40f220011079080c501d51032030881115648a440c0c8013500b140420000750080e20811 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 900548318 1250 900547068 900547079
    0x3110607082d0c030909070512070809060709141302090603070c0c12030c030c050115030b0108120f030c071505040b06040e0106121b03240c0e010914030106 69
    0x400342400d040d0904514002801d0381c1008040501a01042c0100c15010300c400803040000005480441c0c505544e40c01e510b440b043d90a490724000c4484030f03600c03108028200403c0e6a44945203d003d04006400c65666865000064618007624002c04094000c00002400e162405000910008005400040c6480d0749000070810350b50044031008042525214500e0800c2904060300004280c21143ca03070382000e403035400070200c00c2070f21000340c2000400c49410051003400e50000f1280c0010030b020443c61903684c03500e2a50b42009125655240c082d5400b06d1a0b6031941004035141070200c0c1e00d000b880c6903608000840c807a00202c000f0380300326030303040c2c410180307410b03e03100c1c070b80c081e0b40110000200ca18002c0c0030441540c0c2e8101503403c490341010020803580302504030b1407410f03030381c460b0714403084c464500a6008903001c264006080624504804c54607000f0141c5c0300d40f088a08201c061054400400050303503840041088136002030546a420030012424000d41030b41d220000340041485542c40 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 900549568 1250 900548318 900548333
    0xa031a0301060b04170d08040237091104030b0c2b0203041103070303200c0904030f080907050604060f050d2a03140a090c1e050f03031303110607 64
    0x20b41001c1c0d8048400982171041c044810801c601d61001c58004020341165560024010340b0040e1000340280c0f80c00c0300d25511010341c00b1002200014081c040c4071580d08003900d262091215210b9905c0252402042c89000c000c2c4c1021101582e8201e1020400c91312026460351441e0b01000100010038100c0d41c40880c090307528581e07601608021303c00980c80e8241070806142c00200140514480d50110070b00f0000079800265000201c038a0a00d40803045031611a11420b003c0d503200c0540d8015885e0007080201b642003031031001c8280440c0d480c0100d9980d011441c0b681c0302c031140a2a0360190090008010161103a01e4412070b0901d10f14105091120060058040da40e02c110000004c90030b40fa076908850f064080303516405200d038a418080c0c8401c1e0078001c806404042c20402055448800103002d00100068450003080500c0091005038981005214521002d015041c410810f5500e0a521071800200740c0e80c14540004481c4001851a030f111a40746d04031015990300a42c081c0701402c04600003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 900550818 1250 900549568 900549581
    0x70c03060504030e0103140f10080f0a110a06020601030b06041b09031b0e1f050d060e100504030e09101208030a0501080f03040905060d0206030115090e06060a031a0301 74
    0x80c85000c201420680360280c11011403c412904251801d214211403041d402d4409812071036008450055440d546003816141d83c25170441890f41c0b0070004130040782040007505150380c41c0214070090040104808000041c2454400c01c00180e00100043c404281c044042c207801c42c100409c0012409500003121f202c01680000d46804103504a80070014407012081d410580002440c104070800e08140c1c0390120700c20302401100325040da04940c0d031002134541c14820040c2800401c00d00c2e14640f503103803e0003e014400880750a6004100742d01207121018040c090041d9816140d100054119070240302c80008014000380f2012408500010000c1e11500d5101c400b501401406990b480c000300540191034040e400b0074007503070240b814248044000710941e001c1c1c80da1100c012400e40c40f02400100841c4042d007000e54440e0340080001800381401890024060b195110224000c0c1d4860785084101c070100c2e42144c100100308061906548268012031014400301105107d003150f00d40880c1c00c6a94 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 900552068 1250 900550818 900550823
    0x501091e1211042f0309160f090c030501060c080d0f1a0108061c08030901150b180306042d120314090307080406140915031608040507050d08070c03 65
    0x181000b54460400d0b01034100a90590380480b452802c04550180401010104035080322030080041420340b081802012100752120002c110902d4071040c60948843d11803154406140c1790401240409009008043c1210600d441d60004403003262901212030b801540c240e80240d0b595080c00d11144818482d5502c0c0c01c201c410601300e544503207400500201400380c038071407003081c00030b502c240ea016600c902c0c0034601e9403251510b910b1b40c0300c071030300130b03015002c0d01e407400a20038803004010a8030354007800542120300c080e04a1aa03600300c1e0300180740c0c07038040554000e003400306240c8031016240c0c0840c402c090108412103020190b43c4641d1500c000d200750a02d06400041d86400460b140304218014032900500900c0107117160906e81d5032404032504c1280f09410a100010400c6c910515403c2d051765140c0c0e1020780700e00c61103441132401c4001c0341e04c215070162200c0c424420100301c0c1442030400f280310326441401828940c2c00c01040042e8000b200c0340803a0101c0007007151000244807030b0f010704005c1d0b1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 900553318 1250 900552068 900552083
    0xd0203041412010c090603150311012a050a29061905130b040c1407031b0b07020a050d090308040909081b0d1d0306060d080c070f090f02040501091e12 66
    0x80c06d004c002010b582c000841c0c07003941c3e900302c5800d001060352403111400040302400e01141c00c4040c0080040c401c240c2c0e41a41d006c080d8160142c109001001c0307201151944201700c0103007181030301c01c0040078400102640c60480b1101d1000900c0c0b0b0300f0441b207070440c04900300600c001840e075500005044983c07500d0a8681c0030782c07111380c440041c2c20a4064013848c0010f50410f220042c00c0c000354460180030f04031015041010641c09100030982007050500c059410188100c45450100e201a50304c8444031001c541a10411170a400c003903108490240c2035907889541e039843e181c545000d600140c41c0c8610107541a0748104114543c0303044084060840c0103a20000d407e01d420600030251030610340882100d01c0c0c5d554070800d0545a90082070b0a40e0211044400f52000c40c0700e400d01816038041c4240880c8140b0518202140b0700c00151102021a60340d508240403804e84ca50320759081c0d00440c422103000ca10794007070511000400d044202d05028240181910303042e910080030422800d003407015211103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 900554568 1250 900553318 900553337
    0x403110d0c0203010b01030203040b0705091f02031201051e061312142a0d060f2910020a2004090809090a0e030a0f020f030c0d020d020d0203041412010c 67
    0x6003005e002d036804c00c0c40242001c5007180341039154550a40c40041114040200c006034000306a5242c1c1e01503001900480032010b405c030070040e40a9070ba0303400180d690741e0400043c800003896142503038049944001c07220041a0382e502c2e200612055030429522420703205079914007c00c0e10069007583c485540d0085407600d80081552012034209100d81041140075081d007120f0707032072488491000b00c06941084d80c001d0000d80f1103040500c010f00300c506984d1109410650000d2041240e50b113102c09440c180000d941401c10100b08001e904420b013150314025810440c65940072604410640804040060110000034100750001302145d823410070844010102081c002d00074104506d40c198070500542c010030040c000349580716641e0040ca0315441c20440000304285055109225030001400c4441c03c4a460742e50411400b84c0b00e213281c1180e8001031090350340285040b03100081841d201c40c1c007600a9840e090406048130642018540c0490300045040d444078881d0f042482603c100320344665448004 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 900555818 1250 900554568 900554573
    0x1a030d030c230a080114060717090a030b010503070e22140607030603060c02060403090312030f1406040507020604150b0117040501060e0c0403030e0918120702150a020c090403110d0c 80
    0x1642c81030301b03d80b00c444e402c0102c07850247c640c07204031441c1e15007182c040c007210006240b4131541403043c90445500007000100000401846510080c140c40044090390361890320303802c90a14994044503410800810751790b00d06503409000c800801e41c20300507180f4001c5418408015483c3c6041034800c04002a0798080070003c4c0034240c41803c0140c45180701525841c1080c0c0c5000300444914000541280b941c40b1084884d140207a002091a80c1070070b80500001d1900301c210141640e0071204c4074061800c050000c1d03203c501c0403030740510841d40b0120071000c00d503200c2120001840d0484255051241e0641ba01c00d80204010156102d503101e003001081c0c240c1000030322040000081c00904407480188014000250041d09068401005440c0001c8a079a429421101d440710784c0915082e5000d80484c8a000c4080000100516070081e9450481008030341d031119041d216102450300140c110240c160100d00e040e00d2405d030040d00901d04004e119898544d52428400644041310200e501d60404808 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 900557068 1250 900555818 900555827
    0x604050106300b03010f0b0a08030304020117040302031b1c050906121003060207080a0305070801050906120c0405010602010903110d020c09040309080a0305070201031a030d030c230a 80
    0x15040610304407102c00c048051108030103192800401c110215554403003507201e96940140b0161000500a00518000501c0d840007458500c01083c0203892405000c220402d000041380d003d540d06030741d01000b454907172060b542c02c0c001c060400c40440c0001c004210303500007800c0c40c0c065032861180140990640524940c087c10510105d040244607080c4040d400300d558540540d0101c1d800641d0380d0f1540c0c1e07507000c0c0c1c07011021101e800c002c01312440803403040c052000074006801004825181006a070712203041c25280300d43c003440f03460782c80070401c4005003013800c0c507225030909400d06404560746507504100150545009800a00c0141c1d55010940c00341a800305810108900200c080e020502406900a40704c00c2007101c1c86000b0704004000c80c0406105a101600505000f070694888841c41d2030000c150b640401026030000e0f040500e401040ca225041c9540c1510000f4014091059498016000f4200b900c82e05010300c04038a04003100c154044000c0045507103400090380d03481c1d8100710081d1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 900558318 1250 900557068 900557071
    0x9060c0c0f0e06041805100b030f100c11011b030f091a0919020307090c0c050312240d060b01030b03070308070b0f04050601140604180e0f03090a0b0711030601030b060405 75
    0x4202c9083c5c0080d5000304038003084c0480c0c1d958501c44041180301d0301c00007007840c00c070301c0e003102a0391482260150022021a43c1c0414501902c40ea61514200c042510103426902141200c111090140d1919030183d400f0790b000050304028901c0116840d03920f51141c6140e0070010f0045a4102039140070414001d20601411000070402c3d031003400b03a203140780c02003a620641030161612069a46070500000e501594850301a40d038442d04076a500d880c881c0e03060301081030a0341c07520040c01d40c121a0f64050131451200501c10100a040d8441407001034a51a02400e11001d446060581d2000c460019440c1402800c0c09503001d403103c103984030283d18000e003c15a000788058268200700041c04000f42d00462910304446050340b1001d005000782d00001c43c0c03031207280d11251581c50740140005000c0303929002002c04600c0042950030082c0402070f441d071a80314541c0959070004000d08180140001540a044001c1c0603c0e000070b1003422500c0407903c0c0c20401c0e0026207140c0d0440f001c004140c83d09001e240d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 900559568 1250 900558318 900558341
    0x5040c060906020a1a0c04051c020907110d140f0d051e090604080c120d2a0e060c07080f062413020d0f150608100609060c0c0f0e0604 59
    0x3031070130090320384480c0550313080540022072200065000c242004050815100988402041102d54003c02d000b07411000c882d142049010f004181d0001d040c0e40c4c0640401603c081e42c480142c401449001c0c0f041311580704d20b02c080c0d640400b045c4040303400b1800a40c05440d0112420030000341c0e03403c01030010011001181490107122440600f049800a00820000e40260340140b001b5190514215060300340102c4203019280904007091490f41c1d03e5160f0003005080e00c3c0302c00e000c140200852509120700c401500008049459080342c01528107201c4002c04403411040f0940d0110398840c03040da420040703050b0a044041e489003040c0311411026540142c444078a907004242d02081e4000419070b40d9030b0b4120650342c85640890300072a00001600002001030340200300b00650603040214110091140c020500068455400501a151801c58150950b4400d442d01291305240c910110384821f101c0104858207441150000390301210125000043c1c42c440c0c510303891074904242484102c2d074100c0c440 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 900560818 1250 900559568 900559573
    0x708010504030e0d0c09110306100c030e0d1406010f08120a0f03050c07050d120c08040203060615040308041202041a0d03051b0304150206090708060a0c1205040c06090602 75
    0x40c4800a5006845108142015681316807980080c0c100358090400560050340e18506000c08104440e1100300250307c6040221040d121007412110110784c440c2100d040200070503103100e8110140d203000c400a1568520032310022030002009000e031400d0130401c1e4044890031700080c0d800d110072402440724040c0c8800740d00915041003280700b07005041f00c00c04a0541d040c10355550110f00324481c0c0c6c01c2150450743d0808110fa50100040100800e01c041c42d4030189011845c0c103003400201880751030f40c00c0c0101d4000303000302099103d020400a0444805018803e2954104000400210b003100900020120728030b14082280d02801408144e4418018036004000000c103814042e9403542603c1e090302e0b8062810303640b00c0c0448000c20780300908c5060100181d200118001800201040045550f60016400d0f20021b45504060940da0109401101c0e003c1c1c002500155031810f956000d80d040d6141464469010100004100b040310300694003501d0509610070213101168000c15108020302d050b100 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 900562068 1250 900560818 900560821
    0x60d05010e0c0319051302030d08010501080604200c0a021206041506060f0c05010b060708070606091503300f1e020304062003030c120c04060f050a02070312020f07080105 75
    0x422481d00c4d80303400140682c15a841003c11080d007400c1d00203141d9182c0c082e0884400000c15140a041070b0824850300e8001448080040d00c3c506140c060011503c92008070450b40204854008280e50400700c0131028501c503a52412000d0381e1505e10302c9000618000c040e01c02c034281801c0c2000b0503e0080042e12640b030038220100035150f4071800702001c51280389032a00e031a5145140181c00360180240d030702e034030000c081903600038005864014540140300b11000c103e8503917940030f020207588042034454a00fa03100709082000c01d201c655a0400e00c0189420400000c08400c10802040011a920301c00117440070103440750150404070640700c124404441c0420f5417803031700000b584c0e803056001d4041000020b9480d41c03129100c0d22a00000c1400d807100b541d403607140803004a10982c10040da6000510021400306400e00c40042c11907081e6031045d641c00021300c088036429200c0341c5c0641181821486402d0300040420301204040b04030300705941c0500517003903c9507140e618100268020060701c4c1d14100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 900563318 1250 900562068 900562081
    0x60a0b0109092c070501031a0f010c0809030d0903050c0102070e0705070201110616200d0c02220c0228230102130e010803030402180603010902060d05010e0c03 70
    0x42411140c040c400466102d244a55401804000107445410084400f0070107091500202d040c006503002a6000c11103205420103078911900f20301b218a4020101c42c0c01c02c0e80c1035200d1510108503d02a041d46454461100042481c11501c8082d6000140e42050706104001c424801c81c415038109200410080f03003048201001c0c080c0260035041880300005020b0210f9001d011010700e10140354064615071301c3c00140c0c01075072006940b49000045c034090324840c007404c4d50038a074035544110f01c0e0080c41107459049098030b01000c6440180d90140e902030042c0c40c2044915030b9068542c080340c0c0d01241c0c41030300e40c801034900107000c01422904080141901810710300300040130803aa0308031681a40f15155203002d00c80020300c4149030140b650001a0900a2100d90300144040300d008049004c0d00d07aa0f0b480b0700c0c580300c0c0410b8034000e521641d030b03203001041c0100200841e90000ca00400005840e051070740050f4180e40b007184000710254030364004000c48101d42041030ba100a00c486890702c0c514049 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 900564568 1250 900563318 900563327
    0x31b07030c122d060501030c05180405060f0a0e06040321022d0c070e06030d0531150801030b0a0507051207170109050a0e0d02030a122705060a0b01 65
    0xa042c0018640e0000e003109a01c00003103450f40c84581d80000040009503168180f8051020040c0501400340280543c084440030024880c0c909c180e4001000d041c0a45800c00b801c0041803000d051000c00540300d80d480c540c01c0805020060085e44640c507824501c11440388404900c1e11182d00c0f01d00c1c1a44188101d61141c4007101800924403113100383e1480d803203910005990140207044089003c0d101340301001c0341080c01c0e0707420f03d4050f110482c1250b05151091100311030a116003031525002c400791625220004022034035001980310040e11200c103094072072202c2c0050700450194100050494001001449100001c258020000f41e81c280800e1910000141181c46800103100c0c1480060000601c281d10a2240054043c060306d00301060396034849030034001e00400e4a106520303524116040b242c4800001e03400c1d41b1043c140d0099402e00084079000d980c9080e080b4040c440140c0c0f0390036182441c49000150825280700d10810301c00440d07050800380e1030b2400c01441c05810f1460b1500c0b01c03841d40c2c1c20 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 900565818 1250 900564568 900564593
    0x209010e030f0a2d05060a0b0307120206072103092102030301030b04110d060c020d0c0213021c050103080406020d0c02011205091504060e0c030a0c06050903031b07030c12 75
    0xc9045580074243c5040801c0a0011801314595410344001d0104108100451800d0081540107014000e25011004041c2c03220401c2c4605407001381c18004070300042c105100501203041c05400760340d00008010403058111041c64020000003507031a100032040003180104031054400018070101c01c500c3c100d001035500d00c0306010103000d04501000250401801034588220b00001401c05c01d03904045182c00c0014014034010500540245810300035410b128900c4421665001406442d0205030307284540000d51116100300070075810403041c102c04900d1401028021403007403035401c5e9940e03d001d01c0281012647d400020400008008410150781c0c0072410350100d0021790000521364480d40202c6250030700040c020070741d45d0040300c1080240200c41d48a024035407191019601400004010142c49920211000300034211021040c8603492080b809040f100b0400340803240f4103886038201982640504090b40720a81c4942000e00806c40529002c8005069140001cbd410300f00550398035003080c14 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 900567068 1250 900565818 900565823
    0x123011a0906040306060803030a050c1306030b0a0512060402011103030112150f050a0e060106090503030f0702190f0609050114090906011407080c0f03071a090715030209010e030f0a 80
    0x40c041114803565803000200c40043d0760244003000001d680d1a03265459400440703100c81203a2500c000030700312010f0324048a0841845a545c03001070340c20680264010040d032414950410584070001c100c1c0e07210040c00c0c2c0200d00d000002840301d49400c3c400102240d20050312a9810b030402e0004200044071441d43c0c014096002900e4204d01c0c410110620051030300341c00492520b4108010701a00e00d9441d0700c07840a5440210646000d030380c0b00c2001b5182101f891240c5501341c1e00401c0302103440a03501020300700700b0744002c0404000707a03030902c092036040172180c10041d14410303000d004001e084c0d000a83d5200400e002e0810200e14128110490160700509020a000721007000000e1900c0c1e00c0744040b40c4440d44118801d607100d07485400c00701d2890300407032100c00d03162242c800076450b60f8000001f507541c140d0b80b110044800d500040c00c06007401d54064403604252007111000b04420310040754084444030743d5640103890710711620006000100c1049a01d02a410030720189224070f0010a00407803498 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 900568318 1250 900567068 900567119
    0xb0702104e020d0c0306180e0102160506090f0a0c0308180a0b0a080a0504020d02060703050d0227011701210f050313090e03090f130905012301 63
    0x1086103000808000c420341e0714148221003810315a10300d8a40c05007516403284407042000003903e400035070440d085030044000b03e01c1050b00c420040607003500301c101c5000722480050700344a841643d5407090181100b0442d015005041040100c0070b08000c68540318003482c00030f01c10248941c4400310043c203580000380405000086c4071801069980320380e180c1400c040c01d0f12203190369503001441c5980050030080005814040450300d40710a60041e1030141b07030010291802968603908016207a030207044200c090180903c0218200181b91014180740285205800b42600312040200a03d000d94400315052103c1480407515130b84440d0f1081d4196481a400140c003000818244010100d0286000300080e81518008080103004405001d20703504800c008084203480d013501006588107811804242e80c000d01400742549001c2200b003c0701c0714094031a060000100001000752040c4803000d039000e0f0b45541d0704010380000402c115420708080c1c40419807a50424213240807500341c0217103942804 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 900569568 1250 900568318 900568397
    0x40b1326210105131a0907051b06150f01110102040b040f120b0a0c140c1b010f021015030b040f0209130809120c10210209090f1f0b070210 61
    0x503185c840d030248260000f44409011b141c020b01c01401607011003010b900e910070300010b02c155030b08000340044c0203d01d20070b02c0c034401080704020b0101100419204d41d04100c00c100c0207024285080c070043c0f018050031644640c0e920f040000c48000702003944e001c0340490342015400da01164003403940a070003000902d000703d44035100c54011100c801180071400d40c803180c0043c0007441c03503800140b507040a00100305c3c00301003000100b006540886918074504056000b00060f4202c48c0102c0e03105000ca400404840d540c482c0e260744411002020444040310407003e101c01c50400d40c64001c0e0025400300119000085840281e1740e01c8000b80520300c1d00c07070301803180021216a5100b040c0311550b50540040c1a240164803448001004401d890100e402c10100d6010a400c03140428002c0764451ba0019080b1400c6880e503858000c15413400400b003086500c40c0b102040e0410242c02c41490083c0b1007100f81907107541c035034010403001015031400842032041440000d400400d4141010030540204081100f95 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 900570818 1250 900569568 900569591
    0x6120b0f0901150801020d0c030b030618100c052107170604140403123b0f1b01021203060a06110a020a060309031106040b132621010513 60
    0x900841030f40183d10b40010540440c4004055000d0849681d0b0101d0601c15032000500580880301c8050215030076801c070700d000411507502d8000300c5003400c00b14012142c0213014043c000382201c2a000240000990010b148801440c40101c4101500c2004201030703000d003040302c005415099407858841541c40c039600010040d6555038000180720762007520b00381c181d280134540140b4481150304041210361030001c81038501100c0ba003560903800340c00c0b980500442607034a6240312400c0381031805c8448d48900a020420780e081071101d034010300d0841100c9170b61300700100000790824071014060700f032604050040105d5035580307860410458042c1d003810f203200078184020504041c00710402a420002036000016420b41c10b60203141034074001e580b01c0c0c001603900b80c025601d07080c041d1400340c0070483c0540417405101102d400788903500d20800420703d03403020740e40c035114094a0509041e42c0441c80458204d508a00034019140b40c0d030010000e5031034641c1401c0c00264050413101c202241d4698a440340e400b0b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 900572068 1250 900570818 900570821
    0xc1d0a1b030e011806020405090714030a091115040f0501030b060d050705070602040806160203030403091e0e0c0d111c021602090a2903060105060d1b0503090106120b0f0901 76
    0xa101048440701d1841002c0c0c20510007a52042c8070702c0d4050600c00c2700180056200e010b501d9800b03510304c031495195403118041240500341c1c1800030340b1800061810504145e40d029186502d2250101c07840d0f450714a81340390343c040005564003c906140c2860300014851f600e190032180c141c0181c0034002541d4a50840c112101c0c050104000c1c44a440040c0209041000040700c5100782000b181d40e60301e071010400c04a80701e00040d0b030028042104803206100b00680d900e141c803421a08210700c51016070f60754131001072022042d604a1804000040c240790041901d00610381a010310001181c5400c0000c003490502c0b0000a4003c082240c0c049009442404908041214550024403010b000d0070001c25040c0203002c58900349404041a4240114001c20303051039040c450360041c0508000d80c030b0300b014880c5642c00700700225111541c0d990700c086010f6440d0341d0b940c0c0070708480e40d0707141d01c1740741c184d0b0454215603460300100400488400a140043d42c40b0400c00d901005034150103c140c0ca400d0032550 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 900573318 1250 900572068 900572081
    0xf03040311070605040305190f06090503160c0806010503071a0a1806050c060609100603021b1903090f0f2112020c010e040c020c0d08070c1d0a1b030e01 67
    0x1a0740d8010080b000542c00d512001030700c1640c4c000e60136140c261440e0048404400b45240d4001c15a8007506100d07004079002c1d602c108865401002503c0c6050180800420100c0b41500100d034095121070080c0300800041150340c4c0580350540040281d5800c2400c07504180346400c412445184000070049001d501c00c200c0259807036000b012140413180c8521000e001900440e540b81e000d441118005100c0b403500e0300b11103000f428441e89054084d41440f20440195005404000d840d06115541c7c1088200c208048540300106201203100312005160051800807103502042030308406172004e0100d81050440d0500301c4003044080c400001120303846a114004203107000c0c00c40c003001d8000c0b41c5419004140112807023802d07666420411304000411085a880e03c007160016840b00881514030f0400f035148104040c002c00b8203604018080e650b6402d6070290740c002030128510410402186a102e608258004c4244d403028006422603150601c24001c4000c0303110b04140e240d007220b04800d2029031248 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 900574568 1250 900573318 900573347
    0x509090a0615111c0509040e01091406040b1608060d111305010f06260c04090203130201110307170306061b010c0e030f1902040204120308160e01050f030403 69
    0x1912501c4414040d003c9503081403807003014007031180d0120004124159040e8520310030b48400c0e04000d942e80038880105541d2900c00b0447d0b588100c0d10000c10110b00d0100b0f40c240c400c0e0014902c510305071070a16201034001d0311440403803c3c0e0704c2003645a190031400c07165028900f5140f151000d04c49003005070000c0740c004050764000801642c000500c80c4e940c0c02c664141d0b03140446040c2c8007950b40c0012181480356890340905000c01f03045400180341201310a64203c1941da90440c24203807903601040c00c0768030684542d940f1605541a29046503000405c10858111030006542001e9003526400f00079060400e0b000e003620710002c009820381d903c0505855102100c00a0901d00d018503c0074039000348810702d24031010883c4081400801e01d000039100e400300b0142006071180190b07884503640c00450b46401264066004d01c004100451940c1d03d00180e01d00a6860452900300203a82614040135000b4010800c203074045440116600201200e05165580480540c0d070340d503505040310170200d1182d86 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 900575818 1250 900574568 900574589
    0x7050d0c1109280c090530070314010b010806121e010f061e0510020706030b150a031e020a35010303081b040e04060f140a020c0f01020a0509090a06 65
    0x1802d40c4640c007584502c4007062192261150b0329180c00803c0365060b100303048400c1c20031030f4214002c40f40b00d5513681e0707c032000703401c100f02c0b1182522a036902c481041001d80a041030f0f07548141c0e0300d07002d41c0e00c80e500c141c0103102036540312040d800040c541a00e03805403212348064030045c5020a62195400d5000c0e01104401071010401070f80c0311503007022817200300304c05041c0c407008001020940c0d183c100c8485080c1c000d06c0c0c0080c1030700e91401809401420380c1d03802690348403111900824012169600400451500780d40c0003034821560707002119000901004040070a1040c080c6980c8560000c21500c807000706d2440c90494004441184816150140c009a9071640d44400020405410909285c040c0719011052405005206000240d50040d44146440111600003260105400307070b0004842088044d8081031002052240900545c400d403060041142d0004480452142c2441000b041402400c006d505d05184000c008149005080d2003601c92032102d0049002c45080784c0c800b00044c40c20b03085 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 900577068 1250 900575818 900575881
    0x171005160f02071809020406171e07030f11010f090f120809030a14060c03070212030a09120e18010e01141c1a0604050415111b0307050d0c1109 63
    0xa413000d0000420228012400c142010662000c1410343c0e92421220314001c0c05605410700580a0141c5031710100f0540d03006010011020502c5107070005a058024802c0c010030143c48000103001d0b2007141e00300001c03c41c11480034800c1e4070240ca5020210340341e14400b035640d002c80e4200350b840741c400c0301007141e0300d403081300c044074108045a13010491403200c00d8107640442c0d40703c40c03083e829440111010001038000e80c200a02002e802c5000d1508403500035000580110544d980b4001c903000791814401041c10301c44006040d10b40700d03280d1600c6401052214256515060041601c0c400600510820764070401c00003c42e519181454800d2003648144a102540c0ea03092400c41114154800184004000c00143d02800c140c05558001c80e4009004c80c800d605000c0510014801c084000c000b000041240c0d1460000384800017540c8008070340910f54994503441c0162800320601c4e404000c2c0040030b11100701040c01e05800074a1700805aa15141564656901540358442c640c0580d000003030410 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 900578318 1250 900577068 900577109
    0x90c030e1605041532030a0b011a0703020c101403190f2912010c02070e01090e0714011704080306040c05031603180c171005160f0207 59
    0x840300e1003102c00554041111401214010007044400d0049802030400d258a90380c500d8481300707081040c2c030f07010002c1000c01c40501001a041006100040d00c000c8030080060060907410802d00743c4c131524844821b45000c03000d130f41c065180d100b1181c180340b182540320007441010f4000c60060600c2c00801d10450780e20300c2c16141a404551210b0259100c551a26048511100032131040710350f102d58451404035522001c1a41c0003440f0610308205800007042d402001808209000702c11220081e47c026180c1c060400009912020050b400004900e041480b6207040345800300e412002d03640c1c1e030a2140f414079850030050310000e840032030401500d80d45d00204004d0194801c041c501038130041b00d0900a032940340c00100c0e4180420344a4848400350203240c41c070494002d0384905454284200c0c0c0aa00e1324840e200e0100034043c0d9844010f50f65034034158007005a01c240a048818000704d10304002c80d090141c264200100c131041071030140714105800c84600c1c1d00800c1420300a05030b10349082c0d58011649c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 900579568 1250 900578318 900578353
    0x11b120203040e091b060d0b1207081b0a0302130204150e10080f0612010e03160c0609030503030a0504051005010602100e03030105150310180207020f0105030f01090c030e 75
    0x18482c0080b08103800300403400204001c210880c05141100c105c0b40c03100f008408110880e070090780e00762000707030780c40a982c04e2589904414510011104006d4503c03e4640705d0304504244d09120304000b00046280444003d9849e8442982905d4050303401040304404032210000901c15034000410182c031140d0a00c0500e503100301541e40f800c40c03e441c540003003031040c0b8058500400076951100800d4100c0001109410956010b40343d421081001103120445c0d51121425540031458200701403102041d1703001440300010720040102000d14000b00403a2541d1035540d2207020140564654075240e801080500c9010096a900000161800c00003545d6070800030b55a00401c8a10313003080b90401283e082c038a0008000d40341242e001420250301c6230306010006195500013030a07241e10a01c035800c0410251900c1c0450340140c0c0c400c41006a4685540c010008103016140d003046c1004020810048924802d44034241142e54007200454401420b44054000d09004901503a56100c0c00c072106001304800c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 900580818 1250 900579568 900579577
    0xd0902030f0723011814010203071b030317070503070810080123090102090d020f12191b180905210d050a02030112030e06042102040b120c011b120203 66
    0x44907440985243d503400152490b08241d40100300300b841c0543c0400c1146140301d2003174600e41051065910b40300441daa00f1000b0814441c0000030100b0303080c0c1c1401015000444003900d28170744111a5a41e10300880010028403004014004011001d000315203505038000300e034006003001030001e02500c030080802c441d460541d803052041003400032011880f886c2e018401c55480c0c403c007800b9119090815001c1c8801c1d442111401a04440c1c10303c034070f541601c2d09010214040d00149000740500c0340c5810100f24034100203a002440d06c684141c204030300d8046505080024800c3c0f42e010810b9069400d20170b01380b4400d900a6060780d040b4a40d000c81d6030070706100504003084900410000e80c2c450411860407404240610705800d11800b0315407012a01031050b43c050800c00800061401c0e454901c1004070f120300c840d015108540130010703101146030034050303a511020180d60541e026039a41e00c0d07103907075a0000c42465050161351410341c119241240c0318455929002844000560404440203550390300 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 900582068 1250 900580818 900580859
    0x6090105060a1a1b031303150606051b124605070c0b070609020913020112090303060b0a090f0b0702010c0b07051e0a0f05040b0d0902030f07 62
    0x60000040c00c02e10b40106188151503000b40b51164001102e0f540b071049a1204901d10524a480020710702d01881c104020a0b9046030040e42061507031452800c40b41101c02c4000001400d0b0a0880c1406490780c404291601205210310200c29482000c0c00c1d0b50034072654000554940b03070300084c4580b4802d080c90040481204545410391482c00307032400f03100804c0e8081203411241d040550815440d038031030340141c0085409414001481c960310003000d40260300c90b85c4100c8007152950400020352074190342c0c0fa644101d4032030000e220b84c0140d500081109031560f40700706010f50786001710b8050510a5100b0400b0b442984507156807520840e00180104c0d4840c03140202000c0e02c1d000c08910300c840c1c0f9003592100b83c0e040c1c65078407601c02166030b2014103100c024914010040305010840d121001d202003042d881c0e00e103034005a65600d503400b0042c400000c3d803d11a013813160411040203e101e082c0219204a01110030001d4a014144002800c040c00c0b02a0502c0764880d07824003158010266804510f040b1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 900583318 1250 900582068 900582071
    0x50f0903010f0b121b12031306080711010209101101060f261c0509011412091b0607080a1b060501140f0105030609060109091a120a080f0d060306090302060901 70
    0x680c842d041a54070f48188007114180c011884500d8114181260711b80c00503034249050f00c1c01c00008100b181c10b09882640140300103071094060114550700a00e24011001214009500d08443c0381e02140340ca50001e0080420401c1ca211928608c0c1400e500c00c2c40074103c110100c022540e03907080741030300f844404002007002c0c0245d80c0890340c100400080c400440b080310300d0010440d40420708290b0f1240c02c80c002031410301c0704208a049612090341e00402181c80030207810070b064102030150b5480c19245154404804040360145000741e591307132041d02c0707403103038000000c0c0c0d80c4080c007010485109202d01c03001c0201e04200e58001007009640e4000905841d514000440d009500360b00304040c00450000181c04500204041202070600750140c40c0d003d0b1060610480c0340365510425002c450240142929802c0500490951031034240f401e2a0b4094011004281d02b0029403071b40c43c40d030b214a140003a0003800c00500900a14580d4100070003c0d60000010481b480380d505010f501d0b040d00300c0d030203001c55 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 900584568 1250 900583318 900583339
    0x90e0705031605130525030c0908280602090d030207060e040c08010509040c052211130b0d2a0314041106070302011b030617031207050f0903010f0b 65
    0x80c032480301503000c8940c01011034a4075085542040d00901002d4031b0b084244113400d208010681c1c0c80310300c040c0000403942c0c000600222408000700260003c1c0c00c00441d94210001d03801040019109408050b07401668103000b8405601d0048000d110307440354140c0024203070200005154000c10074004603180c0f92200c4a000c088a01000708403041c960b0200045440e0f03a0062107181000c4c040f050340329104d650040c280c20f840e00002010042040e8280004600308070072407500120a0081107000010301041c0d81c03c140100303000d4001840180141803800e070340400c07000740c201403030b4101c20050301844c20220814580c001c800156000040e45007408a0309104101060266080349144181e422000d40b1508098010400013154071280c402d8003150b4031140c2c1400c41b200b004a88044170070050b24002405490f11010507019019901c412580380c005009070307200c40c0c5503174240c142d000c0100d140543e030f103440c1c81000400c140142d80b805074040d0710b85956420395140aa00c480b100d03600480d0f10150701c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 900585818 1250 900584568 900584593
    0x60f07080a05060a140d05120d060e01080a0204091a0c0d060b0c15070905180f0c071a04030908010e0c041104052b050d210c080708040507090e070503 66
    0x255031083d0b07502a0041c00302132013044000c045009852451200a010031019801c0b07881c0d0902d0b161800070780104030350b00041d2440039040903104000082016070201c18032585841d40641d11085501c2c4042c1c0a80d4036441010104690400783c205402c80d00041c400003810410401d50a9400c10321015900c42e03c0c1100104405071100240c1c0d400004d0003005022803507001d202484494805060382d01848252000411a0356511a0b03140003501d0340c82c000d0704546040d1080011b039a90213001031a25070700401a03400403603065055800c0e00880142d41002a0711146000c451140542c1d00080e01c13546048018100d2200c0840c03401d41c0150203d4062003140f080100c1a00d441c440c5100c0d0342e81c40310384007198801048070082a14003503d420034201807400041e4940301d04013148140b84000041c04180d8402a002c004400d401e9201241501046401c2600c40064214100034201e00140003101e40020b0030071504100510161a03444000c4c055500220b0040d40d83e6080303401440d01ca4003560403122503 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 900587068 1250 900585818 900585821
    0x206091504080a0f090f0303030f050c0f030406110706090302100b033d020c06100f0f03021c0c060906350c0717121807170c03060f07080a 61
    0x3035800c0907840d80383c403d07003403000c1d100c90121070407040912000010000b4044c3c011a461401140684c5000c00c000d44d80c0200c2c8401c4030801001e06150540921845440401074415a948103501880026004602d00d40c0c10100c0d004062005041c03500b0300054004255012070140c03040c900c001800d02ca11140a4105604c92450000c801c1861001400114a01020b1481e120308ac100043c0c1c010b2200ca00c3c2c807000070503640181c15950f03181e408103051103284d0803002d08100040080d0520504c2c81403c2160b0f1039090320561102911070101d040a5140c04c4204900d0056a6607004601c507480c903655120141c0080705500c142c00114140041d80243d2082e403071340820840c00b0f0104201c66401c51520382c07001070000a031208a80f0130b0203219140000b4103003005c003a1110405209a81c83c0c103105400111181d070002c00251038616505a88040d5000c0000d083e0b040d5656861840d42d2292035100992030f10f104680307800d40c18031460051090ba0a1510301c054042c07200350b40c0b100e0803035640f01300307010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 900588318 1250 900587068 900587071
    0x504030b090d02030a030c23040f08010506150a18030507050a090209030307170f03070815010e01080c0904021204060204090e030703020705130e010510050a050a0f140402090604030302060915 84
    0x82c00744c0c0041240101c1c4074403d51080d4000882c0e800d00ba5240100a03850a10355041c8450210424400050500080b40c0c0c0c10060002000000300a002e5071421102040c10b25030b801c01101030803100411821881c5010380746429904100540c040103050fa641855aa28046031007040d000714904000428102030a0013103a604000180040d4a029103603590003c407541ca9a100300b4002105100c02022081c103c2c0056005188541e1110403500304150383c0c06024001c102c031141800f0040c40c407424540d03040081a0303480030315440c0242e2212200000300f0007070b201d1104403021101c0d50104010030405154080c00c107135066411708000b0110315902082e520301c200c10002c5c000d42e0100400304404d2402c02200d01581d13a22160104400769004007580c203607032094401c606070242c1c0c41d00500540c105401f6040040208070340001c00ca9142281c0d414002c1514003c003101d9075420603419000b62101d80480d0b00c000c238054006940d40707035079040094644109940c1a007031405144160490a0170890405 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 900589568 1250 900588318 900588343
    0xc032006220504060e04080a110f01050105100e01080712061206090c060c2015030f04050c01140d02160507060f031103270a0615050a0905010e010302120309060a0504030b09 76
    0x252a03940b10350300c038503039030388c20003007881c42002680c450180b00342c00113120482100301884008185941401c04215018400e1881c2004003d160085418180c3e03002000503000f400c6030800c00500b4030602c41c2c032405040d06400ca0001c940b402c4403100c081148651104140a010303c10484039981c030b580c000c03202c080600c20040c048004d070b0700c0e81c3c806800380383c40d000200754002800c10440d6110405154182c0d08229070112802d100041000203100c424402c031850380100b468016181b13588440f0010060064429504800c4e5000c11008420008400751034000c40c0c020040310f040d541e076020020141103e803200c450010b03003030803003040e0000242c4043d20b000d0000d00104541c00010381c842ca0383c071710481000c084181d100d0880000040750b458030900014001c8400c50007007407420201408940301c4541e016070f011616041c010000c44400700001815030f941220100d1201c2c007a600c003207185024665032560300240c001000c44000b07030440020400c903441203c400105a48640c03150f5110340042304c01 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 900590818 1250 900589568 900589589
    0x5072f221107030f112d0f15011509050301090507060207240f05130b04080c0303180909071e14060a0210050903040914040318030c03200622050406 65
    0x555643c0031746920340e04601c40b076003190300c620012400d4020300c0424506580d9501d42c0c0b1480c4025042c0c06010900c660604c2c40010405001005102400080140300f410a0800302e150444a031078495140e8000404004000703010030082c0c1d040160f114121072081c28050300c41d41600142d602d60846450510000f01030300c0007c010f100703440580ba0032180c1001c14041001c01c0109a85440040c0c04c2c1d103000c0c22100401e0b603150350514042c5440c21740c1618440f88654001e0080c41400890b03080c126800c20401d59400d070b91a1a800c0c3d03110f190070a15041144102980d1464803144042590110100c0c4c10220000c01802030440c184240ba00c02c4100c00001a00290b0640c442034080c0d4100e5600103000208480c0340c265a0300e44501110102110590265a19014041815400000c42c084c0c5080310f404403100c4c81c6550b607880003000c882d2100074145520300101c042d0600812502e0710440d48081d181564a10b1003480141c107014441071592040c40100c0008689401c0a01c1400251000c400300c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 900592068 1250 900590818 900590837
    0xc08040312050f0c0d0f030e0c150910020d02070911030703051f09091406070912050319020c090f070504030204020d090204021204110105072f22110703 67
    0x795865601001e0000700d050001c1040448054400c0f41c0044c5a0200e00201038502060169001405415011018402c05041c984c111003040008100414102c0040b21a600a4030444004d144c0d103028034240c09030300c2450540103005894000c100561125990b6003901c01c2292141d00702c0040300c01c2e0707807140310050702c0900010f0600d5000e030380072541002c814850b06001508020b002003180425800c58007070152100c46403007c0000c0b000281c01d003107400d90040d05c41d900d80004002d105640a2242d1000c005013484540f003408001d00481d081d0000d00d4004003610700040c600a5521046102030b24043c2203c100003c1c1e283e1002000d0340d0041105603151032819181d0340030000a900144606480c15a541c00001d0041ea60340c8000c02e604503441001080c14981070400801d032202d042860381c1801020415000000e1803052a45c0d001d000e000071000303245410554a20920001e0000c0c250800700c81c8410b0b84101d9507004615420f070f81042e1007440842d03440c188009650042e000000d0114400c07c4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 900593318 1250 900592068 900592073
    0x130b010909170a210b060703050a090e180d09051f030e0f0d021207030c0b04080d05070815011805010c05030f030115080618040b09010902031b0405070c080403 70
    0x70003030800103024490202060052a000c4a11a0300c02e0000708003150700700c038504840b040b04500d04540c02e84d0300d03401008142203980c0418546d104c4c0300c90050400800103021400303540030340c0c5d00002401007500118405e25022500b440760150680440d40b4500c1a103034408c0c1407601c2010000251032000e030000380c0d0500d06280000c1c2030540000f04005058440511500d046d81c00c01120f80f03518060f00003006c02101c0f091019041142aa504500102c41000404d01194000703024411840e403002480102d0780d26418058070718096020303d1a0b0050900d1f0600c48183c3c1d01c10043d40c080c820244100c1144806200152007501e0540d0034903054215602c0700f00300a43c0203209940f2254002c0044d20f02d0502c4000b01030503564000d8108003100404140050b00290b071110210703a003d5026214200d0030303042c1e84c4020910341c40c01480102044075013400544800302c02c0d00701c002d02c540d0260885040d40310304900c041001c2001c5e111540200e140c6400079200611500c540c003041d603003001d400792a20341180c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 900594568 1250 900593318 900593321
    0x10211101030b03190218070f1407200103180b0604020c010b0d0308010e0109020c0c041a0a06050702041401031a0402030a021003090b011e090b040f180b130b0109 71
    0x42194149030369800e010005460510843c8030326107015a40319850100341c1704101076100c1000d610010002d03240100300d88250003040a280c403001d01d041c0800035407075804a0f61200d21640030000c004451511450229011701040c42e05941800d0728240400410302c048042100d0411202422100050020072103505182d8014000410107000101e201d1051a0200f800030000c03403800c5000884032001000384048036203405014194100c020b42c5805207030341419070f4a0105400f2180704994541d000b0b04c0140f0460005048000c001c0e040c00112a9166005420f6411424003a4025420841d03011111001c6081045c10b0740d9005205805440700866400704e240c0c0002e008076014451f400c0d802015989503816105129299640421070008c946049051540306071710442c2100c24050b24480748651000c400c5064804080c0e00040110b042c000003000340204c580080343c242e250035541500c0b0744001c400e1690160080b100441320b40c546550503030400300180005880e60101200506c000c2505 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 900595818 1250 900594568 900594593
    0x1103072901050312120c0f1c0c09141002071a070302071e060c06090b040f051902032a0402030a060501080702060708010e13020907080106110a200109090908031021 72
    0x55030f000303030700f0141f8040c0c983d80383e54005540e0091008610109040c00c51050240895110441c6020040c2070300d04000b511516180310b140d58400c840f160812003101e4400c000520082424002041d100043c1310402c2c141d640c0898015001805164130225213965407400c503942e58180045844062451300d2403c40e40044424070031101e041d120340d030381004550701c604124025070284070b5142981c001403070b202d46050042c1d5190f64001009560140241e0b0340450390a0004600c58142340b4070516442c080c4408080740e007040c591240c804009e200c41d044c05c980c0300c10b0680d903080c1c98454490700c441405a0b0b40383e0003190706d040011015001400000040c51a01d82c009089a29095076541658001000e00e0b800300c90007800a820280100201c9900c0401c81000c441c00c81d0180041c001e4945551000f8140001081c40e600c509658642c0f481e441462203c0003461010b0040081000760b1525a0b080d520568162000301c6061002140440c0142404000c84441040741e940f1406c203079035200c80a00c40c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 900597068 1250 900595818 900595831
    0xb0a0e03070c080c0a120302120901110601080a121d040b0d020414061e0306040f02031e010c080610020c040b060f070f02040e03120106110307290105031212 69
    0x2841010009072802116101904043c40a404109140b60501001400360f034825502080820038000200740c0124248900c01d2071000510358444011b80162148044950140c40b50310400d40001148103011031912b031040e1103040318202e0070354006001c071111500101c0403101c128030b90f10340c50300920301a88a010083d00103801407880003041c6e00003c08841091440542540d0400204145c626042801220241c100c01c0600308891001c2c01195680d07500510003406420800925025540c04004034081c1c2c0c5108044080703c3c0307141c03540041c064101d103010180803a4185000c9261031410403192103150a01da40100b011034800300411000d480466000758000b07030104a0011070340010001840e40c24000c180c8a4000c0041c0d206001c01c550b03200301c1600c6c0c1900305100c1c100440560620040c11104030707103020ba07003000712020302509500c5140002000e0b4020401503181d481140c0181003240041d5080580b01c2e42e80c0d600602d91180c04202101c2d584460400501c4001582c40301c0e070941004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 900598318 1250 900597068 900597073
    0x7030b0901062106140a06090b070b060a050433120b1b0a1808010203042f0414071b030f031a030d090806070513181514011b0b0a0e 58
    0xc4081d500a01101c00381d8005079440c0c1c501c1d9170780303034940e0428402a01c0106424a84420003d140c00c03e0603070103010b6040000e01d003c480300c0214a896442a058071b0141c600103004003e800b50803000c800114140641000c141141091081c2c0300161841100080710010b2141c084130381810369904440550090228040c000c803204800c21484118019200001240d100e40d121104501c1740c00c07104001640c00122142c1c010800c0000054420424041c11500840c10311042540c030b48025401f00c0c07051134141d130403602e080e000268113040d00c02d031140149056110240812a103d00c1c01c0a001074080c0d0160100e00009408a0034a109e40d02801e11085910111234200c03080c41c00003030408580320000d0000030102e07002031101d00d42c240540390300141d041c10700501d42018040000000389451064004110307540421030402812038003c58003154559440b00d00898454002a1f54020542c1c0b00c50b0000d0b441c0140c0406116045140712540c54109121101c0c980d5001e140300c02814600301420900d0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 900599568 1250 900598318 900598367
    0xa0e0405060606360406080106150f05071b140904020d030e0102011e1b0807020c1e120601060f170610020703050304150f050901170711030c0105060907030b090106 72
    0x2502a0b82903e03813030b544126682e03024a0581c00810003034a803d50000300b8a64905801009411104204409802160700300115844840394050706c03240900c49024045028130784480e01070340961a80c1106407a00b9040105d08003540d04184800001c0444009404c01158080d400c0402d00400a20900160510010400e070781d8100020320300c44085a10b44002d1b684850b00c18014420740f5101c600f092581c0c1c58240010701d02180025500d9020b041c03100d0003040403000e60b586841400c126070314403517030140402d940b41c012417807003d694103800d01c101d6001030321031078021240c0c9100d0010a8103828902d012054140c680b0130800c8000b04040c0802d00551142481c00800940207101030802820136203004c0c55400410f00e00541406100c031907140400c202041030303040b20ba0b04623518500d60503d499440f40706991b481700640f10041000c401c002280310108a2040c80c445c15003100784503100070341d1580c1860f00c4800040d01912907001c074056101503034200502407584200000044201e1109480c12007 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 900600818 1250 900599568 900599617
    0x140405031f18030e0307060212033603180406060e060d0b0316030c05100507031b0804080115120503041206110313050606030a2120010207020a0e0405060606 69
    0x16600c002c0d0048000c10401d20820300780e8a420301480000f044c003800505807209503010040d610f440f0083c0018400320030700d4807095036108070690810960301d04104040004028008903070381d070340010402c003401c00012a80681242000d0081e042150196280c15036080155800c114507500300d82003400c2a07581d00d503040100c0d41c1d4104000314407141091020240c0a007181000030a80806402032401514954a150398940d84407040703c28003901850001c5d6070328095043c000c111144281d000e82444070205c2c01040c1000194441000301c15952034103450107644c4c00c803aa400158440b00036066800c04c4c8000c01554604844c8544c10340d210f10300c0000d00085145007400720750802e5440c00966202e0320513400411204000140d000781048004000030070aa42e1401c07203034500b20f04240d00012140001280d0b00380180c1c686020440f00c0d4a402c0c00c509c000c3e100b0300c0e0007034111140680c4298011800041c0e80d00e41d0152580c010354004001c0c2c4495540c280034485654420f00900d80030014844080c403c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 900602068 1250 900600818 900600851
    0x305070c03032615100e09041b06080c160c090609020901030e19031103210708011a030f0423070501081807030b13051c140405031f 58
    0x346100f074a0301403039140c030f4503040f4100c208800140d50040c03040005000203800c00c0000705151403401c40b5240515042c156045980c80e4014089030740140d030381001d0004000b403c802040407201010b030754110759503890400301e41840040d07038450a0100c00300403100c03600c24642c5000100d2402100d00c031280d2603a40d0003010483d0090307071100c9180707503020800f015a9a494014081c940400000402c0c038000c0126621041c020720010043c20300c044170b101112542030604c00e13145462817074014400e40c0c44d0080c0d05070f50301d14030803900500003588110002c24100345200760404002c05030302c0201c0c00c507a19840342082d1507a004e0001d64442c0c1c44400c5481c00c0c0c180005a5070020180c410140103040d1034480054900800038103501d2401200e640928803a1500003023500c00c50742c05c413052003559194810a00050f03241042e0103016400f52014001086064041000d0820402d0390351880001e031407102c0c6005c03400355004040d45038202885010894102841010b80030008600008a008003a001144d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 900603318 1250 900602068 900602093
    0x207031e08040503030c0708010f0209330721022a06130b13170316081b0f0f1c030f0b04020a1205060603010b0406050c03041a04240516030507 63
    0xfa603011400074401652301f8080e481d00b401c101c00301581804200400644030501840e12a05411150880c10046204400b03200004028241015684442d681080021036102c0c086c2d00c1c0707591040902244226200184080240e2825000f4800004c0402500d480c01d00b03c25003a00c0c1e02050070302c40c00e0010741d40c48511100400000c42110356840221400d0100d10840fa4013820107000202c201181c2000c1c04022222000003000940155090500c1c0400ba00d010305642000c609002c0d900341074070031100041258100d0309810442d0440c41c0e20a01d525034038070344a0301ca4074803403a03024034403411280290005c1d000c081c0300034400314103800b0340c801040c01c907040103040c0030004000c500c410402d0f52051040c1c0350400c00030382d04185035605011001c80315100e10b129200c104800061a280e8021090060342c0180402c404800003140071270b07160751a1500a40170302040e0342c502e005061081194000034804000a41d180c282c02c03c14182e8005221929001d029020320808020303400000b4040d084a1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 900604568 1250 900603318 900603337
    0x20a0c090c120b0109090e10090c05120c0604090c050d1415010e0604050603070c1502120c130311030f030c1e190b061804050109060c0207031e0804050303 68
    0x18088104540100742d4000b610809511a1070401e03501d20b00d90344070385584180e4800c480302003001c0020210a0b03240c03c401c0012040c83c28605007040c800c0003031110700d00c0100d540031600001c0c2d19404c000c1e529165903024110b242d0142c000c1000b041144071070380010400a9584c14114241158086900140c030080e014030300c41640b1443c20010040b400b0044451503800a180803113200c007d038004203007148a00c0c02414400c03400070000034056072050303680b03017407840d03128541d1151303210509502c2c0041d4100c00b075000360700f0361428002424080e110040e22050f0300c1c80030b0780900d02451a154035280c5001c2c844403540500520f9500d01c4104010030040aa510300c103402082d0400041ca402010400102d49102083d000030702071b43c8030440d0f00c0703c0400071960000c110100c3d64440b0720014003038220320701c8925070000031401048144601940180c076054003500d024401801065412a19094140801411030545c03820f1622040c00a001c44801c951280b4065890301382c4a4001903c0e503003150516 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 900605818 1250 900604568 900604571
    0x9050c07060c0e120c0105030a0b0a17060703060509040203191403040303080603060105150d0f18290603100b18190e0d050a030b0118060c06060e041a07020a0c09 71
    0x300f000c03424800c100c0500700703240001520001c540140024420311010303146a16032910f60740c42c1c1d40e403aa01c0742c0700704000f0085c501400114400b00c3c2c5107683c0b1110704680c440003003440d09100107210b061010ba182c1c4100d134020301500c61800c2840c6800c1202c50032801c1510001601c84144211002c02c0000348045c50183d11009090b01d0007104062901a05802143c01034407034041c41d26410001341c081c2e421448001c4001302d4008a0625040000c0c02c00400c0750719002c9828100d02e0901c001da030301d06005c1c3c070032000d120004a1540f40c0700300c8034084181c60302a00b5600028005048005a070321080659800030401c07044031001c1d01c202014000c040c0d81610801c400242041c0f4030024610903020b82c105148094072102d0b4810314081c0007402110f44000c103054a03a0740c0103416a01c90f0044592011a04546000c0103807120401885100744c03000407101140303014400701e40e4484000805101e10380c026840b64100c3d40d8907004441852000d0410415441108400b4000a124141c032001612110a0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 900607068 1250 900605818 900605837
    0x120907051e0301051305060631020c011b050306190e0903030601020d02060603120d0e1218011706012003040b1801080402031005180f15060603010f09050c07060c 71
    0x1c060031144083d08403c03880d5108500c0d032000138008103a540d0701c0201103c3e5812007079606038000143c68040f09e00c0c06081c2c07121070720140124170254040e02da00700601c4000c1007442130b0240c48408107928201c207980810001d0002801d20700c5d01500241501134000443d445540e502d141031030042000769040500b0790408820440a568100320407004000c161004284601304240802d45031a854200d003040e0520000303003448425010f401c607900000c12401100c0c8000000c40c0d0b08102a0840f0540842c0c01e54115600111503100c0c6290030901c0c100381c02c4516041d156480191070361070b08200c6141c1158584840c601c8034182c1800544001c103041c4004a5807030311298018034880704149800380c1031003184814040940c400080400b6141c040e034500092580b0b444403141e50b1880688402c64841c421111800514903001c00c0c948440900c0c2c4441d030341d4a0301c4480c108481c5020034000c49441c1e0b91203481c10041c1d40c40c07542050360030420072410603140c8141030302d80d101030350000200000414120704 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 900608318 1250 900607068 900607129
    0x2040e010902030120120c09100c02011e051611060c010507230901030e1c050408070e0721060b0d0b0f120d0509030106080609070e07020303040812090705 68
    0x844003000344241c00214003080038421402d0900490034150482101b0710000f0303000c800500102d510042004220080f400d03902d00d002040c2d100340b6203040780003407180620035207000c44030241e8907240b20280e140c640c140000380c414003e0035151424256440341115403842010f444280080801e00c0c01e040010600d890702200103000420b46810030800c18402000f4038014514100c01d40c0c074200000d1802007070b00c80c07018041c1c0f460084040030510280c01824040600f940d0010010400c48103c6000ea41003542d50786080030035840b0481e034400c04546501100c8004464444a00310108080744001401640300c090b51301158008091400d1040da032040003400a180c5480149018082290070211181d04980d4064807111041340fa00305200c1c000c50b03e178100d5942900081d010b011241c040301d03864a8024409a80c0d004103103d0000340c141c0e008045000389202008803482183c010418901d4900e8980c481c0c041900014404500ca0142003c041259a10605098035104510f1000260f8203640d0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 900609568 1250 900608318 900608321
    0xf0a03090c1203050c1908160303060806070c020f0906090408030a270302010e01090804060c08040306111c061505031e070302221a0c0a06020c01051e0f0c0d0902040e0109020301 78
    0x40345501c004411b280c0d034100244146084610403402180c0707400326109289410b8014041c40d4003d2029809001e082150840e402084085503500031240841c25a0a201c01d1165510055401a4108100a0010b00401c40d100700854101d00010390010719890540404442484051803c1d90001a80b020050a040d0b09003c2c0c10728410f80c50780200b29a2099076203200182c4203510501091248000c845414442c0702004d44000319001141413000d078949100301da0b0f15900400e00341c4140864141e036400c56980910400050b0b407082d031148500c10298900076961134000418001044800300851800201d985040501500542d100541c403480703004a8072030020320b004040c50391a03c1180007009440f44a100d001e070a1150158800da030355201c140920b0a0807400c1201402c2940002030608440030154002e40c17181d55000a005d103013805400c045041080d0681d00c0c03007480c60201000c660904d42980c010094804a01000214881e45a002c28292032449186001c0e59540b1041c51041d400e00b03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 900610818 1250 900609568 900609583
    0x3040506010f0602030a021c020a06020d0203180303010605040302041a030f0601081b13020a0302120f06100903050a14010b180a050f06031e070308030f04050f030f0a03090c1203050c 80
    0x190025500b8980f1300e540086d03407072815062a00d40c2500c00790003024058002d0002cae0342141e820203000e43d45d030407008d0400006507000380ea04101003d00c0c041003e0749000c010060340d0603105c40790b80d090b1600c2d1440c5c0821003e421000340f079020013504010000e0165030100811200364801001401240d85414201800e101c1c0e0034042101086400e03401000554448086103140c1d03941741001078582102c40b104800a008100c015a00c8250500a1250032103203040c0d03a40c031518084415002004220344102c5420b2401c4c880109280d002c40d500f00d00003003900403007400604400e800085c02c083d5090010350700000d01e2002c402922051000c0c00341151180c0100369111100c0d40c0840114181100400d6a420b003901c04110003141151424100310030901c052001950800d0341c503501c07401e003101d05240028040d6011107452280d0404000c181c18080103664161001c4040181002c150100603030151224040445140ca545840410805d91187c160200580a991125155035800010600d400b08 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 900612068 1250 900610818 900610829
    0x4030210150609050d0501020c030a11011811060c0f011a030f07060e060315150a1e0503061c0f060516090b07080904180605060f04091703091203040506010f 69
    0x24124010310000d5002080d40d81216005e5078000c2601c4a5814028020f005090305c500480c0800203100c55000d40c02000345600b000100e0080001015103c520f6100d420082c01c001c01180106038200160314204019000e000d50301420380d281c11400c1e00c1000d003150076140041003141846a42c0405030b0808100e0b1208014114000b0940c80b802c1610241803103e00c4000300c0d00c01c0c00e0020014105c12042c040303c240d1890041c20105d03c400e845801541c854004441044c0080c3ea4000c0c1c50f0608040c1800c800d0315001540c0341d5500c1c43d11008c0520202d920f415440c81c140c0c481e01013070203000803e1b0110340b01505018a40001e00c0d410607103c2c03421243c80d54400c210030010301c00d20900200907403208a94038070f54407140aa686040b05004a00900101d2240b040d48040d01c078241001c1c01440c1c1c03c200d11408045030713807800c200880010402194503d10f0040c10011040b0210501064810011904590808100d0b12940400c01a81107a80c0c011602103405410900040080380d0301e65500d070003c2c04 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 900613318 1250 900612068 900612101
    0x50a0f0506030304030f020d1208070f0512150102070806010f03050d0f080a05060a08060702010507020c0102011e0e150a06051003050606090f0a0f030c1401050a0903061e0504030210 80
    0x34400300080c1d6030f02580c0030260000021260106c00c5540d00038020385003079403218003100305103040600505108000c482c40c0c408600400301ea0040180300b84100d44652913141c030b02c40c1803074454092070f8070345040e2071150b241948240040810500c0c010030000c1e0080c60040e031105000c608510b0504d0030300003040c03640c5062058090320815650340060009510107c0c51500252940d1346000042c03088980380d010410900a49090144250741034008038414035040d001c640104212800490032601411200042c0b4040c015000c0030ba100c050b008030302c49280b03110841311a52058888810824420740398403200942d6640304114508052640c510640b905007801c020340d14080c00444c109102c0c0c0d070301082c451913484100072500d98544000102030260010843c518584a103862414000c10703000300b80307550104c0e00b81d01429610910840c3c1d40c40101d995580101ea2440c0e5840d00508500ca80d008103c000d03010690102d03002034415180300c0ca0281d4010400c20115041032412030b02522250003826 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 900614568 1250 900613318 900613321
    0x60610030204150c0203010b04110901020114070c1410020406110c040902060304020d061e02040501031a0a062001020a05180d05030f0f090607060b090a02040305071403030913050a0f05 81
    0x804200c481c0300b00755840c0342484c100d00c002600c00203004261008144d41e02a182994a501811f01607000d010260420f8000300301040040042e401070b20307800c0715940005260300040304002030241c2900c1d90701e502d6010403034450603c001000320076030700035030004030014882070001e043c184c3d810400200201400c0d2070801c0100d0140c2c000c502c00b480000d002174055090600d03464200310301703648621440100c0040502e040c024400031840070b035200e0702c0f4560020b4104222003051010404198080c200b00601c0c100d90070f27241c40320559020300c49040c03201c1c0b103105000031041e0903a001e00003043c072600d1640d205641c888140f1420203620002c01915030082090002c001e0001d003002045401602103000c40d280c82c0c50421881c4000c034812000e106804c410041603040810040790441403403400100c4030312040380e4810820600300d008c0d41c88007400c0c59102650404c940c0c07804100c4400d203120054140c1e864101d080c0040352030303034001c2d1002202c101e640d40104145083c89218030080d8001011051015 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 900615818 1250 900614568 900614579
    0xc06141303140408061b4e150a0308040807030606080604050a0803130c090e060c1309050c16031706040e070306022a010c26040f060204090e060610030204 68
    0x58010040801124402c8480b241c54036140080555a60170340340c00b140c80c820f58080041c00000c3c002c4c05c07418528903861f441c5684118400d0b0140490300c14060602c0e03030090755400c4201c0780d007600f1102050340161000c540800030072100b40c01800a050403000901c140d07455031034a1406c5a5941e44003410303a82102e0107000010740081340383e9455640200d00a9142c4d1140300c2d2000034908403030b00040440c07112180000c0c458005400c0501841c0f11107054030b28699038412000c5551142600300424501d07094814003105049500c81900030705600031250805600002070803010380a00000d801251806404500c041c1c00900c185600a005880c18807100c0180170b0308036512143e50000926040d0085040c9c450b59504001c001600100340301e403c5460070141c40501d00800e14001010005142ca0151070311824007040240d1a40c0e418079440003950f170302d907243e6603400d200c0302d2404c807541034080000048411031801480408110301c0b01500ba941845410041544c0000780d289041c5401800b04101 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 900617068 1250 900615818 900615823
    0x5072409120f0602130f08010605030c01081803042d081c030506060d1b08010b19030b0f06030a060f08010e03040e09010207080711090603070807060c06141303140408 73
    0x202039010034082102c160720716060001e40900002d040950a141e01c000580040c59940340702100d650340000c20129890384241078603400340ba5656800f2801d10000300b85840000315804132200c4151064030b0a2a4603903400300c0558050b0340358810059042c0700c90280000c88420b1020051020b480100410310010007107814800d280c1c4001000d0581d2203000400c1c94407118115180c02485000401c420400c01a805180d01080c8000d500050a07140002c0f81d10044642201c1000b0340e10110041524042c182c00c90241201b04452500302c0f480b0780f0403660315111140550300031590710341c01081c85c0d130411485005142c45640f0003440baa040c2195000031080100407101529503514024410b03944004503d4003910464400401c1d0a000080003824400e80580660814200b201c13a0b140e95214501010f030f4079480350140600d2508810020082c1d180181c0b0b45200d094400d15004c1034040c03004080c003406c0d03502100c13800820300001c8d000d00c0415501607005442c000c81101c0050509081c900c8003507 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 900618318 1250 900617068 900617099
    0x905120711091b130b070803090610140d03030917030a0c1b0210170a0b2809020a0917060403020c0607030206011e0e0709080c060c1f0905072409 64
    0x3e003849000201620014500f02004000c0c007046846150b80740118039110280794811201102e25001d8200810080712080c0040e9089484a00c4100303410603840781003140e0740e00035440860034907566502d40d00001310014400080c1111008110f901e07494500d0000c8107071803070075100038208081008c014250608400020b030b6422f230150b40e00e45400c0030800f4140d070141d45402030751b1155213084003044641902600f0228140b0010795003c2c2c45000c03142403c0c404051780400c01544111200f13002c6c8092251a406041000d806182c041c1815a41e2001c01020480300262400b047e000881044240350301040074a91506080d24624a0100c2c00d440003500d4100c18000c4001000c01c0e180307121003201000b83d011000e49260840440103081106010b4170806591150400d10701500a090896107001400e03141c0302c86580c3c010300480e15111002c0304149904040e140100e599030402d0b5001314038100407104c003400c510f0751022141a40706001d200301240e8600d030301d410811140d8052012141244100 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 900619568 1250 900618318 900618361
    0xb030f011812031806150e0403020a11190f050a0b0313060507200105040b090d0e04090c0e090d030b0604030c030303150e09032208030a0f0201090512071109 69
    0x700003082e0800403c034041c0452078991081d890100224506001c071551006818041584004003015900c2e140c0142d080403c945c043d004d0b0b0401d142a0700450f1030b42e152000b038440003d00a100d007030050050200b001f0b40c40c3d00030020004204005014500300008210054411184894258a803071095008500504240144125150000305299a00403440c8607c2c03600900c0090100c40603005136107008203000c4400359401c0b107a0a01084010a01056030343e40e4502594412284050314000d00011742414030303003240d068265034800a40300c5403844941e4056500180545203c0b01c0484000701a9030017480d032503204440c10002000083c840c004e1500889034941004181c0e2290400104149015603200340c01419519040041020012004101c80700d85100110300d08903807202c1032401c01c7d00038003c60010398410441c441440d806070101d03080d90410340c400414071400d1656481d0a1000b801c030800d04082001c501242000000d020b200d20808003541d85450070701e00000000465440c52101 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 900620818 1250 900619568 900619583
    0x307061119052116080601080c03011e08030307090602071e061209060f0b01030c0504030b070e03030f040602030a03110c3007050a05011d030a050a030e01050a0b030f0118 75
    0x1072129072441d40e404032007401c3c41044039030242c540840f40046202c0c01c21007000000e4121000129558005c1c03070340034040c000781e4415a045a080180c03400d9071072101003840d0140aa01c100020764202c0400c0294800c0343c00d40e440c0c030041d44c90604040d01c2c1c0380460304200c402c5145116503002844e0140c190004035841c1c0c0c500300034828032160340d0710020800c104000c0c1c00a4108158500b40380e02035000700d15141d9081e6400c1201d000e003054129198096804014a0f6681c40c00200301041d10070440e0256070326004050700e143c10610140b2003c242d010381d00c40c80142c1c01c04281c04100703d40611420f4000d50031000c01600d0448600e214540312030010f01d1068441d0780a200382021020400115060030301c0c160780003542c40140742401c61b900c00ca440000c496640c01e003600207981d1345401915540340c2d16060011410003a0340f41090f28a03400a0115008156484500301d03a85c00003405014010201c4120003d11804141d05050a050b440c003100300341d60b8140040d0071507818102c140c81d82c20307542000302c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 900622068 1250 900620818 900620827
    0x160302070b2107091805011e031e020f0306010f050a090501210809030706051b0751030c020102090f0d0f02030a0b09070f060e09040c0e09030706111905 67
    0x244c50148880d00108030040c04160b902c000c034500741d48118141d0311aa01d040340842c2880304c42140700580d5000c02883c0e000d062211610245140081031001440101840c10006028004c2890168260b110500d40004003a040285003000c0700d03024068901d811041c000f0350b04148620007545090484945009514407000c0180568401a201000001004d48005039500e03a0002e0068000d424402c005000000840e800d482001030340b18101c401c012000444000000c50512010030501a080c10070140c81003040210394141440804c80503c2c030440480704913814600408450041c0c08443c00d40e8810001c0c80d4040e5545480841d03001b01c01c907042c10782d01c0e09900d8800b11503100315000075014454440d4001c1040003022143d4403520300c2400300c8100c590f490540e00c0403081c2074030404011544c42c090818079402c0c0095525840350180a20000350b6903901034542c01d485013180e0613140390b0400b003400c200b0480ca5010f86508003103500031450a1802c02041c49407480e59800d02082403103400034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 900623318 1250 900622068 900622081
    0xc0503030712110705060301170106090614060d0e030a030c030c0f1d010210050702010207050f0a11091f0e07180b0a08180d09030605070c03080613020f160302070b21 73
    0x80513000e000301502494495035581d80c0c14140d40500f0f901e2020300d5081203c0401c1641d01440b50000701c800c00701502500203019414004e2542c840e003c1c208401d1784a03854241c0b0880c080000784500c1c0c0556070001198000500020304590003e0103840400449440c4654459402080c104a10030710f8441004910142001030b0b1520a010012912050a200401c0a0680c0640c09010340b680034400795110840d5408a807602e4418001c1e0040a040c0d14101c1380c2032a080c0b40b001d1503070241c500e0030740c1c0181204440011440c0c0b91036900c1348019140d18400c026203d580f04182d03040c40f802c087c510710076a904000c40000c0328024050030303800300894000041e0501c0c2d0014100b01d2051098420344400403200700009118491a0005840c0c0310f00f40f10114050b10b114081540040c0d4040d912034200fa25483c04000103000340c002040803403a000c0c0110204010640d0041c9903001c070500c92450040c9207440d020782010b980d540a950804014848440050005001d5034542a5103002c02c1030a540c072903 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 900624568 1250 900623318 900623323
    0x240c2d02011415010e010c080f0706020d02070606090b060f04120206191707080c0d0c1e050405100c02030a1511043302031204050a0f050a0c050303071211 68
    0x452000341c101c0c2c402410700c50218101502c80c039440c807081ea10080780c0640f100043d1800488294020b081c18410000505105c6102000e0700c0340510500c00903190054544076481aa003001009a80c1a0b60f640c030100810001c2d40700e8005603800c159800750402000b00710f034520034040d610450055a500044801c2107640d0350048a804c84100a00b04ac199030785941d00030031103d0780740c910030038411400740815001800f45450b030384100c90815200b80380c8850706540d0b0010301801c2110805001000620480034112025402c0050159a40300c0361210f107400304110845243c034003c203040c401901410740142e01c002c11010241c07a0000d488001240747d8003400c41c024604c0c0fa03454407101c2c10200307000c40c221140b4801c2707403030003907070008004602c0d07540c141d40100c00015000e1f00c50160348104000350840c02400002c651260151003a91600c000039110500a0300c02d00070103d8107030b00b0900ca10310030800c441c9901c034090702c0700303900850900754140e592070040c0441200078018045500e03048422101c04 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 900625818 1250 900624568 900624581
    0x320a0305030c04050d0f050c0102152a0d1a0d0302070302190e0114090f0601051911100b0909070b09060702041d0303162606010903240c2d0201 63
    0x142c00c907059510b160904106d141d0b010b0f0001c444d030340a4141e20900c198070000f81002c42e415410303a802e03030340e0f02e46e421050348100d00322278080e941a441c41c01d05a04540408081c4c40701861003000480c3e1074500013200c10070381161410441c030a18800c83d0450110390f002501005980e0b060b60310004030042c103a800b2401112684c4900d419601050010444403141900c11800070b0042d200e88a071619910800b5900840480d0244e00013802400343d04141c0d148411028044401420050b801d400030541160a01c3d0001e00c810202c10f0301e901c4c6120950a0406403243e00050b1754019118440c100007080d03105100308003481e4803a071804107240055561b02d0340400c030485a00758030788521012410002d91260011111040846810280d00088502481e00c14500c01c040e080f0015403003003103902c5905002c001406c0d003410021414004030024045180b004184da04901c940d05410034284140d000b52543c0e24001c50800000020704102001c286c1e03400c18078500c10417403c402080300c0d000c089005121 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 900627068 1250 900625818 900625829
    0x212113140106091416030b04020c06040c080f06010f0501030c14030403030e01060501050a02300c060f010b16020f0310060f0905070309050a0b090316320a0305030c04 73
    0x11500140c4036400158401800c80f048010b007403241c116403940500e40d981c01258004502d402131486010303402d1090348440445000101b0040c20044540595480e20104840458102c0c25080c0148122a8100020a00c0042c00d500405880d0304042c54540c0680c207074814076061544903208000624002d070b6003600c20341c1c1c280010648070f00c4c085c00e00501a1003450000c001e00c3d46007840204480d44500d00b21000036900f50010500815413010440130480e5008250b80010303082e02d00d0303032800006000100b40c03002c11080141014100400003022400060344059424002001864003240d062100005d02a4048403c054085060404241468003e5a84400d801c4c508640420802c1496241006840e03592104001560307440e00141c00315943c40310044c2c550b41c014100e01d400100c80f0510194000e80c0d07801503e00302070710001c0762a200301283d8030480b03981c003254030702101c0200c0742481c50400d42c200c8213a64405400441250380c03640c14552000e4100540000000e039070f2003000088900030030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 900628318 1250 900627068 900627083
    0x412080708250c0803031006110f06010e04030f021c0804230307140102040326040902030f010e090705100f03090819080117030a0503060409060905212113 68
    0x1000325051440c800b03150088840071043c100c04035040da800025248102c2c400ca0030070001d9800d000081e284c200e014040c518045c401c00752844403900087c05024002d01140b403070701030542060701c1c0250440380c060303c48004541c0103012071600d100d020300703c500c407103421403c040e6496265402d11280c40e0300c151106003a601d000b0034452018031400001810724a0240c4d120440c1c5540c1400b840d801c1c0c0c0b280d0303c4050403126001140345610b0002c1401d100741c41e16000846440c2c540d9651448050ba041101e40e05001910f400c0100840ca807601c80da244c1c440d401a015014146c10180041d0b45007003664072945c10091901c0c00d15503428020350140700c0a90300152116211aa0000303171180b05012164404001080d0314000a81a46129038000c24141018040c6040c07402c0828112007640006003500c5c0d02680307c6400b030300450303014400e4a03c851f0240e0050b200300c500f828190241141c04039055207842c081001048005a20844140c03140a480800301e0550340307a0542000c001000c0c0100500100c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 900629568 1250 900628318 900628357
    0xc03070b04030c060c120e0708060a0e0304180501030b06010c15020a0309080304080a18030f1101091d060901050d020f040c020307020a1518050904020f01121d0f030412080708 77
    0x360086c00c8115516a855070074014080d661030160385070260f9106400d0341d0303070200c40070a480b420303d40c01545d040e021602c1202c0c2000c1e070b00d001c004104d201d00444c0c0504107540f040140280041000203a0340705500b800d080d0f502601c15501c18074031020100101880b190301161242c0d0340c62090304050402500480d07003680b681000e04101880780e015003000c4010400200c4104800f801d000c40e01c40032280c01002c070040b1130425403074a0b20384000c801102410052480001308200010a145400d803011910703071240a4540b04003072014003203040e00151321070108035640e9001aa1600d4051908450a417404254017a111070141e10b50300807440b000394085031112000ca03080003000d20075900d410443da039101404400710110075122449000f10380c1c12441020000340035091490880099a81c18901072030841c18240c01001120300120884104002503070100440130300810901142c4003005015510b00b41c500607848031003031403441d402402d400010a004080c031102000f980d544544000c280c0782407 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 900630818 1250 900629568 900629591
    0x801020a030e060f100b0c01110a030c11010510170a02090f07172e080f10241a0918070215010e0c1303021009030b0c0c03070b04030c06 60
    0x2030062103100d035103544070390700002e914441c1d49200a4003c20b40c50296034841c50030b0003050080b99020030980d2440390748604503030809d034100b4001020101502d6030005030702c1c114a0380040141240f81c3e180da686a040106025800c0c0c0d10600c030b10115800300484410404600021604010507001d029501c10f801104101d09052540c2d0904c0c405c040660f10103203404a16502c41c0018002943e00b036200c2818481c1000864030400c0200c180342c458000390f145620741c1c440b812450114158070702800783c3c0000c1c2d0034001d00300b00d80c0141490500000410802c00d0780385e00d602500e03442e0a1040346454244c114040031005030101c125219a0307000307400941d08202001942901c000182d40d80c01c01480340407030000c1109400543c681c1a602c0d0301c940d001d40c5458040071001180c000d03031440000010000000030042c3e9415100510821140c0c88120f42640b842c1070015081c1c0d4000c0c030340b540880081008140c175680c04403c07142120303400480c0502c01d45441c02c0031114050219030003408280b070032100c40341 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 900632068 1250 900630818 900630821
    0x8091f0e010f051605070302100c030e121306110c04111e0304020a05040c020d111f06060806060a08010b0a090e09060103060f060815182a0a08031b070801020a03 71
    0x41011012035182206071024805c8903148a07084014005030061506074806441035040b00f041c4066a2502240b1445490010742c00e000c0340c1600c85d0222080090807102c03e4094000d203000070312281c00d0003c5480f80b00743c0120b454400840ba9a440380c1c0c1c0d00d24003200100103180aa178058070400719104560242d05812850030b91050701c06030703c01c504070f02d4005058500781c0038a12003220b0715409030400d22070403c0d003030b03404140300c4010b00414010b40607290700c11032440380340070a0203c80c0c83c00070889914000018105081c040c003043d018001c10004e105105801585040c11224011101030303441c5405007040381c0004854011845040000d01400410313280054510f069a000380001c100c1c4042a003001b104640c0035100f80c5555030080c582e81c4052040421825610004a00c0c1d680b800000b07030402d03141095004100080c00240e540b2040032414071030402d043c6a41801c1c0c40701130080d4103108019960f80941d2845060388886002d20b8490050140004401020208025510707078800b840d0160 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 900633318 1250 900632068 900632071
    0x30d050109050c070b04020109080d03020306210303040b0a180b060103050106030b0f0906040e0a12090806042117070905270403082e080d08091f0e010f05 68
    0x10001810100003140700203140c42a1030054204007043c51900e44243d07a103250b0304100410590600c01c0042e00002d580c4c030140240308425010740e900590701d181c00d40c00c1011180c0c0c00c491070707103101c03000d0301450f0840d0300c0c000100e0b40c205800c628104a180d0702d0041c0c150103016000e031500d041810084181e81040010303580140a040300b6202070209a032a6102182214205000140d200802da0703480b010600f01404102c1c4c1140000d0404071341c0fa002002050315201800c00112407003401040e0a54a681d402604000078120020142609080039103a85120f9580358040c0f000007000c002001140c103000c4c61040d0207251245001b00161700d007290014051458612620307000f018a010000d088075840102801805065480303840c050325946c03800c61703403020300030209150040d80d00794100c0448a071600150442c1d8402003140e46030742c20f1450140c107096843c01071400b440b01071800e00030550b07400316a056a45110071403c4d1038911080810740050b0504096001955103007441e4466414a542c000c03d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 900634568 1250 900633318 900633337
    0x22d0307110c100c060c1e1b0602130326030f13050604031206050102150f04030c1502030a1107120503070525021203041a18030d0e120c0a0302060d0e0f03 68
    0x8009011445000740d0398402c01203c1c03030001c03251f6640796000c00d42c001e120003609a00014003403520083d1030340e10441240d0192286d40352014404e01e0810410a8040120004684420469441040c00e01680c2d000f4000588007650450b401800690300a04101c03c80700440d03081800c4540e02d0400f130401404460540c0a0324404a0501d800031529500000c0c112002c10b01d0b00794024295520240c2c1da1201400c00b500031410000d081001c540840d0405e803000b4801100d4100050342d80c2401140c00040320b01c41901007459240c2130045d4000304815800088041506060266480d6070b00103040b20786108045c40b40c24901c2c071300140322100030414042103440602c04e440701c1c030807401140040c9550b40030300d10902d900c1131804200c182542c180400500b8900e00741c10f0340c0d8030018403180d0009007400604148180000d0f080d08811605140c1016850402425000900914403225020608081407400040e000704400500f4010299156001c060080c0009040c0c4400c20800e0000315125031002011 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 900635818 1250 900634568 900634571
    0x212100906170a1103010603020604061d01090503060402090a150303081906150f05070206070812060a05060a0305060324040b0a050609010311180109022d0307110c100c06 75
    0x120b12200c008812405410700d20008100c01100da0b600e007130908048040c00e540654a6400000068441102500150155443e00c2a8905401100d040c108a426013030a040181e170000030089500d0200314550042d4040c4c41e10b0409075148038091000d400b84140070600c02c001c2003400004c0c0f40c6e0101446010310502c114011560b000404004190707a020b01640940b440c050750303180c0d1034500501004001d9261070501e5030400b200da40004107a90060007059030356181c000780340c41000c050411441d5108a0440d00c0e0030f440c50900380440c1e40b50168035400014180e07640041000ca5904020751018003228030b956140120003410101044c5405890468041c04860003186d60004e42d40211442401c010f4024603c60f80b850700c0d044442141805841d400c000d19281c035000d80b40d1044209070107090b030b20070003582c0c034030b01010343d01d03100c11000e400038442000c580020100304a0b1a8110b941184132482e2030916440c46001c072074100301c0703510a903070390124504102060f00c030b4112030000b41c1140944030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 900637068 1250 900635818 900635831
    0x121020a08090c1819060f06110106060503011e2102090a02121308190503100602012309030c19030806040b0f15090405240d0c050409030302121009 65
    0x120343d1103070240c040c540c0c49641d1031400307000010041211a48900b80c1c0c1040240b82444e03540304c604454150f080000303000319022050101a80099403200d01e0003030107008022861070154001c04c81e02043c0201801c8600d41c1031411800c2880d0000a0058051688041d42046581024205008481404a001c2c070742007000900384485903c291500c0890a0b02c69464940d40d66034080d00014101d1001c8a0081c4140b0080100740c061500d0491001c4071622400c1e628200b01c03c82c807203a4056948030100316818103030600c0d41c0700c40041401c1c0c10b0740c4910700c00d00c80a40b200320401d8250300a1281c5a4480d00c0f4040c285030901095149403022540691240c02c041d84400d424082511500c10905411604000d4041400d003400180034a51801e000c02540c1000d4031100001d00b91201a0f804200038440214464004190b01010107440b4208550306039142c082540c914218101c43e21420b40301d140e4034020034003894002d804995a052684014045034a01160220b0003120140a280981072400d01b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 900638318 1250 900637068 900637081
    0x3061703041514030610050712090608180709020a020a0f060c26160201020405031e0d081003060c05120126030301060c0609050f0f1e1606030b0121020a08 68
    0xf43c0c0702040407988102945140d6912042c40001541c6105110410208004560100e020004011020703040c907510032074010301e010b0000701440b0340504030302c5030344038500c16620b0b103844005501012101e000c440543c81d2001040107a0030f09660041c040c00c042c0c1c40d01074890800c070031644020800c1a203a22026003504a141164001031014504085000a800c0c040340010310b48281204040301799100240c6030a80798400b0a04080c48107400e4815030702001507140c081d180070320400301000300038541911945040704055203000d0161101820482d51001c0c0c002c886c611900c01c8507800380900340d010845507075401588004000c01440284484410310504010305008400c07641210300e0365607240c0c880d01c0180c855600030007080c4801c80d01071003000403000b0800400e01200240322a020094803800c00d03250f44402d0b031101c0301070301d80d00260007a41c100240743c0c0b00080c0f030070107603412490001580d80810700160313495051843c4030128000d4039680003048001c2c40e00200900e00580c0d40383c030355944803a03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 900639568 1250 900638318 900638327
    0x8010b13051b0f1926190e07050102010f09030f080709150c02030118020105181809010b03100c0f031d0f100e1f09020303042d05010e1f030617030415 66
    0x4c00204156a22401010099507015650b291b089551003104021740c105906c0890210307550742da4070b01c0c40350f00401030820241da020701c503441480765840828006883c072541c008200102c44c4c4841d4060188050102c1d2108e4810b0001c64080c12070345440d4464400b458601425510900070101c1c8a9820042c40c00d8103110700b941001062681038482c43d003002c41ca41075045020818103091904420802d00316801d2a40da41d1a55001d00100400094080b4540d0281401c04001c1400341100d40d0030319150305190341e800713080d01c0c7c1a06640d1400041025441000f803550880f1282040c01501c02c104010b1011030740402c0c04403a904000750700300b0004004480c8a07484003c1500c10101007607002c00c4604031801290898120903100800780e0b45000d4a840f10080c0040800840070103000d911390500c45104440300340e90015242c2400c0918040c111080060664001c59201a06880705481000d0300f2a00940064000c0c00411034191580040c7c00c1c40d0baa80d03030300240300700c1640c00d081d00000c0c5102e070b004 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 900640818 1250 900639568 900639587
    0x30f070c2414030606250b0f0f0601030216061b20060a020c070317040819020607020111010b060f070b010504020c03040603020a17130c08010b13051b0f19 68
    0x407521000781c204042030960280f600010030503030b0070240422000005182d210700b82c1095a020b48203080d451695401c1007022190010001e407040841d060070f02c14450b02c80034a0b103030320150900e00540e0b02c1145100c68010204040401025030382001e880f01e1501002c45013404a500307003984c410505050400d00b030207592000d0004608130b5040400460fa680040740c00a1007020b60f00d0085800701681c0e81c1d1420304c08481ca0815880c2240049400e00409600740000146455040c0564074a2005600001c1262181c1e11000781402822040c00c504410207402280010701c004005070786883c4640b09200050b0b002c140c0c00c889004181002283c00e01d000d00c00e48030920a1030f4002c40c241410094180d00945c0445010405c1c0b1001c03003103d00000101400c401d104a110b40c4c0801e181407a60316010304184159044004030364100b030030000c81070f218044020b000800c88c030f0000c51a0f0302c0d0b126003250803802c150710120360482c00145454036080b21f28003c29a100404400350f00c3c401c071010088403100e00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 900642068 1250 900640818 900640889
    0x203031813060b0304170a0c11121507030c0c1509020406030204020a210603050706050a0509091003050c0f011d040b030d020a03020601060203091008061201090b060a0f0302060702060a02030f070c 86
    0x81c1000c440070542744100c054281102a100c40f44211381e01002034540201140c80035000b4010702c0410076080d606000e42210009281054101d003195a80d0320f1100002d8049014000b030b95668101007959550b411840056070050402c40d40c0d080c000c4001030050f00b110541d1550404017003000012140c6910800048030b401602910015003402e800721810b503c441001d404004003840710780c2c3d50744d484d00d1200b80209000d115103081c1b10300e145042402c2481144070644603030051481c80c410b41e6001656051b421381915110f403401484600000c00a1109201007901446074000c0104420f400085510311140642c003100c0c0c1e60380ea1900101d9903845008071942d0030080c001d21485005004174050394100d10003c1030401e241c440100950308450b1440b8054900180850501000b820040d1050000d009440038552034a81960045001c505c60240024000c0ca00001c2d0155270074070a00030750f0a480106000b45070f075014170f4105541451500e0046082c0301003640c106141070f1101030b61290f955003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 900643318 1250 900642068 900642077
    0x9050a0b03040b0405070905010f1a0c0c011202040f0e010e090601060c0b0a061508070332040c050603041101090e190c1e08220203031813060b0304170a 67
    0x1c0d255603e514150724041c0c0220b5952150304004601103000e070003158041c01e4103d6a05c0110f504d0440c0400d02d0a85420b10042d4010301040107544d4481c02058010301e079402800d046d918502680b130b1110003889154010a00d287c1e15410201d00090380325600f0341280c0984006280c11b840310041b0b41e0729444288039000110b08114405800079281030307941d5911528100b0300090361940d030410b21581d60b8200d01c40400051001d0200319600381c0601c204c0315650194584551a82400285120607005854513940d280d4101000030301004180c07035244c0c01402000c0c15154403410240381220040d40013543d40d40c0414690700d008502d40f0b56400d030b6140304000c20b80c1c4032000d0b40600c00a0030010401c90030034608000000f19410b11400d0040a0380310a00c4243d45d031064070f840d01d01c14151011201800c0082e4220f10102000d0250780d0000948014a03e2001010b0044c4541000500d40c1240342c031f0350001650a041000484030000c6010b1445075000c0c0500c003042d1510307000c40301254440d101e90b510224 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 900644568 1250 900643318 900643321
    0x160e1501080c04060c05010b1c03090819080c0c0402071214030c0714010f0e100e07080a03080907120b0403020105060405010510030b0f040f0c110f1f0f05070203090109050a0b03 78
    0xe1203030116800c1d45d406900001950150320700820828421804044054401d51150708105540961404c0041c41c82502401c0c402101c0721042140c4400090040c0c10b8140201c0d8986410405005642400000800441d61b401340743c500315812007020100c00d00802d982d4088000f00212100440344514941494140b41c91142d40d03a215042100400c560348540da07071004072240d418070b0306c100c2c913207100400c005110031070311f0020140a60728441c00e408002d80180c1001c101140c1c0010344001c80c1507060802110a40c0d420314024a007031140c0e4001c01c8004050091031060200400049001d24040d034024840d9684a4092000741c403028031450390402c90007202107580d01c3c469408100ca0030f600500180c589012400000c007502c200300c4841da542d03a900e000f03050381980c00c0a6504080e42c4664040c3c4901600103400c03d0b00e0f181d0940c0d10240c40a0400b03000d12100441f0b9110307410300c034013542040100e420086c00003982d0b40c001485a0b0302040d03034a480814135152000140f005c54035030366081881e5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 900645818 1250 900644568 900644579
    0x50306190b03010906021b030403020d030f0c050709020d0f1a0112140c030919050601030b040201110607022d0703061109121f0c0e0f03160e1501080c04 67
    0x14800c59400c040d00541d2040309005598007801034204a42c000c0d0790250700c1d02d880902c40c000010f00c01504000d01d9004000400040e100c041440540ca505800c00d07607861040844261000740380c1080003441030250310404918184207a003d869036142c8040208001c80001781c064040b82d9500c8940030701d811f0490580c54081d0300c200a46801704000c90702c0802d001050080c501f1440e801982c2442d4028004010012403007001c00201c1d4043e806101c1080c202d420076100c8948545041c00080c155400c40390009041da40106200603030490880c089030740901e040070009489000340c2d414150700900c18000c424000c00c2c030f5081c0041c074500c908050989945155290001400412480c41031100180b2244000e83d40ea940000d50452202c0040d04500c009680c94407031b0420392400440d000d51a2001840c03040b41c0c070012103103c0c98001d4a6035401091403100080c5025003045030070f40766aa0121012500c2002255200d019640102e00e03150740d00c50a100640d0030103421a010b0b41540d40c20b0204001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 900647068 1250 900645818 900645841
    0xc11010e0105120703020c010204030f1a07080109110f070302030c120405060406030213050301060f32010c0203011416080f042a0803030f06192702041d011e050306 72
    0x804c4a0700b814018a071080c00c008050998005a00507900c0351042d000c0801403211007004442c00c95030341d2480c51310520301120041d1440106020319501540d17240840c100300c9051004907010f12884441712611803c0a10f4000c0d540d0303224280d0300f103c0b40100400c1c08410401d10088d90251807004007101d00709420100b0441c002d400c412541c01d11b041c104540040c4944085c800c0b58098820b41c06e4602da00c40c240000200105480842c0c10107910b03000c2c4280030741c060290085e0603181003d01e040420500c0500009007d071000c2040750745402044010320030300322081c85245440c14203d884411195071609000e0034040300845020b8154820303888003c3d04100ca17181600300c107030b016801c1c08040fa52150301503459070300111100c180b9140c500b82401418503180319480f035108001400c0f110348030305109211456001031644201680350500191310f03003458507016034014041201c004107031006482c0503480001d8081c8110300e107800c0c5a0310710301d01200f0404d440b401a40c0340a8003c0c019500c402c0510132 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 900648318 1250 900647068 900647071
    0xf0c150904090210030e0d02060103030e040902040209090f101202090f041e050313080c0a15090810020a1b120c081c0903020d03140f0604020f03070c11010e010512 72
    0x194815602c501040041e0b48810704010200c3c500e0b50300046094141624500d4074080f42c10890030755206000402c002a48620f0755281d9140a41c0c002c901604284041b4001c1d001e10110a644164000200303c9024080b8810300c0c030485482d44516021a82c54040c15031801000002a4008030074000103000008182011a040b41c0b0a0161505200d0b0044000401440a0350100c43da0380000420340c041400d19020b03a005440b5100c09010701d1003509000030091126403181c0720880b4000f06901144034014203601d801002c4100a0703071036060078054810001e61210400c80c0c007007100191198800b03c0da204a8090655000815442d64216180180c55141400200720380c0c5840030030080b11101260740c24520740b01c047c1e040116041101d880d000e4100400c161010041510f440c490183d0020f1300960150404070304003180300c1e292129004540a44103258081001c490000144030016a01109110600740030300050390007a0340a900440301c6200d86540c02d40080c20500104504a0851f410309 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 900649568 1250 900648318 900648337
    0x1a040f021507151d0610050108060603010608180c0d0b0402090c070c060309020d3305072304120b0f100b0406180905130203011407091e0503060112050f0c15 69
    0x11001c400c0d130703440f28902d8840101c0b0105000309811408000c556004094160064001c445890441d8100100245030940c010300545001e4501e803c0c88d50502c60078482e0789102d000151800c481c0d540b00b4108a00c10800a4034100d000341e060400150742c2055580941d03900950050011403031501d0504210058945034000341d902101c411009000a030350071082a0184140303500580c4443d80f01d0f80c085014400210001061700d05100400031843ea10080d41442c00b12000e000794480501d1042d844041e0003070780c02c48001c0184800c40384040c000b8944a0603c83c140401d20a915640c0d580d007000003080780341c030030440520028482407000500481c01d4903440c54000c4081c5425079036445800701580c805460b00d0340d201e0014100e440960600b80500c1c852100d0940b014011400d00c8840142684d416100781460f080c042900c0e000004042030040d0000c08004040f2101c5585528400301035008420045130103100b1681100d803403520205c2d540c10705840061004400d011103050f40307a02a4041c0c0f8a0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 900650818 1250 900649568 900649601
    0x609030405150909010905073c020a08040e180106050901050d03110d09051009030b010b0901050f040e07030c031503020f0d02031b0120060408071a040f02150715 71
    0x14100503112136415600038007801901017860300303000c0809003248049088440040d900310703030044080301842d02d99001011a502005082c186204800ca041078003941c0c00416080700007030005541c00c0b0071841c2c00e00031803036a11811401c56511203400e00701c030824821303280c0011841c8010401850407084540601c0d00070b080080c00c001411051904101c0414400c2002c20300c011801d1259051000d4401145840385c20701005c01811030311600310791901449a00800d0100040701e40c2c103a4440c000350b0300e4102984100d65220713a02c86100c00b5190300d08551500000c3d19019400441912074001c600103250a00b440f00103e9045400b4080010221004141c000728440140c2005031010025080807643c1104070030030500c0101d00051026203064100140501c2c1c128441020300f00110b50545c00c2540b20110783d9603400d0360b241a0352080781d6070011000343d04a001c200405e00080b4076031518414030850f00b07007480e800c450007800c100740140354000d1700201200720800c4400310254480410180442c40 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 900652068 1250 900650818 900650827
    0x80c010e0115030528031b080a0909050604020c03090904050a0c031109060a150e04150b040905100303080a2a080601090b0f07150912050c2109040b011e0917060903040515 75
    0xa2304a05640142e8850700058017004042150951a1044a402240488065141070038280c0541c2c1d4900440e4041340c880e03118200410200300c020030000c0b518a81c442c040000c11a0789040143c25055690190b901503a1400001307502440e201451500303441c82c02c0d032020992030100004452500070200f000342c005965a20030000200010050001008441c4039a962076003480502c0d01629005004c0b01d9600220842c20b10029410046040d40320790142c00009007113840510087e088200d9820820713200c0343d1005025005c1c1d0380900c41c0d0303128503420b89810b40003d544521f41c5a0070311924441030540711f42800004d00050b490000110103800076000850201c1564aa80304407401011440012407000503518006440078041110501100b40224511329200c170351440315031040c000344900c500d9403084541143d0b8011010409084400d180200301f0824a070000b404842240c0a022549550002642c900b0200001c10381c0c481e0801d100614209842c00b0f0030300800c0c107000a40381c03024013070900 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 900653318 1250 900652068 900652073
    0x90218090102090f0d0218100509011409090615010c03120222080c0105040b07051f1a09010308040302040e1504111503060904080c010e0115030528031b 67
    0x42140260303084000166141505800c0000941d401c401e002e0244445210200c0543e0340c2001c0f0b03194045280700100036564958400b00703404666a001213030310190050000c20040b5604024800c0c40400761116840c0d510703400e0900d999941c04648551840b01c44142e06c3c81c085d4410801840003a2082c1070450420440f403a0202c2a0703080410300d131041da07040e100f480300f40da000a00900c3c0204a42d0020b08002c040e020f00082040c442c0e40a500300000c0001340c0c01c01001010071811000b882d0302e403148440164030110440151001e0200c0d03129040005680d10107515048080b036040b01d90120f078007460300b8603540c2840701805441c4802c008078000c0700e40c150100140f40107030394071841c8078500000018031400304009102d40c0c4400d44007400c40c02030040000a8440120854005801c90021600c9444100101d40075004410b850896542452244004100302038515002d0701c3c40303002980c24500e01500350030310310480b40c2400c0828408a29a40d0042030154681e502c90b0062240c1c8643c1900480c1c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 900654568 1250 900653318 900653359
    0x10c0506091b061e070c0e070201060509360a0b010b03010305150f1f1206020301090c08040f200d080307080106030606020a0b1e0f07020705041e0902 66
    0x840e6001400d811800d40d0101e85400b030b8002d901e032a5811140c0c141011000d242480d1000c44016106604250010b0180140540300764008010009182d0700c200d50304d0800c200a0107007103148180c3d40a1a60400481c21a10a4030401020001a9034050541e881841c4d075131114442d036486c12940a0041c1c03001000030583c0601440d001e0490740b155142d4075495072a08070303d840b821605040c02c082c000c80038071155480020103590031907012031300d540103011100302da808500d296502002da0510481c0c2c902080094603000345040b1242028104071301041c071602501c10f00c80840c2c00600a40f010f9141800084080d206001b0f100c0440446103c4009280003003018245000800e1300d18004c00720030040559401a0128003400c40781c50207101c0289445d001039034542403070000030920344002e00011040b980c0001140c070324000d5200d64503880d00300810144542001070312078000600409c0000300e41d41c2801d01504002c1a40703052100e040d0b508184001c002040c0c020000c99009260006c0900c528051 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 900655818 1250 900654568 900654571
    0xf0103150e0709060e06120c09030f060907060908010e0309060c07090f0207050609120f0c10090303090515010302130b1210270209040803181f05240f010c0506 70
    0x50349850034560309148010b8004c0c45c4500415225500c100300d0328803865007070030f01160081da00d82d503010348548880d00001d042100440300058644124400c000c2c00110000d02c41c82102c2860302c401c610342c0e03100c503007190980d1520356141c00c840c0d0040008820608155006104904483c015106050b490325a02c4040e00e0601e0701c014422500841c420080c40003d00c00e90350018201801003078030303089101d40700c1810300960310b402200e00c00100b4900a80c01050110f40d0422000c40400c004820080c5009002000c2c0300405442c248200c4080780040060031a28605898004003142100107100070380b0005010000c2080790440408840c1550a41081110345404460300d0b1021940b0300c08025010a010a60528086031031243c0d02040c0140c1c131500700c1941c0050304191010303581d9685440380d110340e62040d2103025843c8240c0c41004c1c504542c402202c00b403420341d6502800262607114501c40e62078442c042c2000e0b0a8003d8120804915100c0100c540c081c1040c18035100c00d8a40d92140c5040420 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 900657068 1250 900655818 900655831
    0x5092a0703032d05070504030c1206060807083a0c05010b06071104020d09080301030b190e0c040e010b0a090207050d02030708070b0c12090312150f0103150e 69
    0x10003245010070540c1502840031200b800d6803108002c0b8080c4800a6031540300c001404040c65621004140e0041c400c1e000c640240d50040d00081c034169481d005000c41e407c070207006451280c0350040100b01190b0120b00c000464040c031009000b08403900d042e00307000010007808208002200300500c8070342c1c1c160700d0322580e8203611074840d07030118480d83c1440c07803e490304080110f02c611010840c600000701c0700d2119442031a0140e800680320303410007441c60014040c1403405044814080000020069074980082c4200789190300702c0140e0020000400c183e0f01d01e42c1600c0690781081c2d4510146041c80d6115103d9181650004280d0124600100d401c6043c1c0d42c00c040111900000c09030180001001007115202a07440214030b803074681d0300c0b07a07206800713039034030082c440040040440c0c1d00b00d501ca4151149841141048803050070400c0800343d50354406101d11014000140014440007018101401340e0640540703802612117030580110020000e074200c641c0c05082d040b502103030b0080c0940c405481440b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 900658318 1250 900657068 900657151
    0x90106090c03020c010c0305011d1317190201050103080904021e040f140f01090e0a09052d16060f0c14030309060a0204050d1403120a0c09060512010509 67
    0x1001038041500b56410000c011b03092508060042110741100481540c21170080c1100202c0d5848154204d807241e0300c41ca502802045039030042903860300304c400042900d54070140014016206580c410fa003642c01c01d200180004406101e140c6860030140c000f003205024510050010811140030034146803c1500300300c0056183c000b0601401c0030300540c8a091307241c00c54000418285083c0002d001001034040d81c2d018048500200d06400810b40000e0443c5500c402610010100e0b6400060700104001900c40b030503402d107000e003d00d0540400c985a5501c030040c1c2c00316106050000554142c2c2c03104102c1010060444042c03800f041620502000702c12241d005175949007040341400c0d2a02e18058070382503015104010800081d516a860f02201550281c0d104403a01c0d4245112400d43c02602007910704141880f0801864412590007141c507d401c9843d41c0ba099511070f00101c600d8052104170b0b000c03010301d410050016103007651010358000112505074419654440200502000c2c0001411010 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 900659568 1250 900658318 900658327
    0xb030f070501030606020f031e04090507050715020a0c0b1807030c090e0318010e0a09021602130b03070e0c09030706020609010515101d0607050f24040b090106090c0302 74
    0x2983c2c5030040b0700042c081380c03000b0141314406003500d940b030744510640b00c1220704074150702c80003c6180d1019074005104a1000308181d28004a0180480d40044022920440c4002060340c042503540300382c80c0c5202e40c2d80d51b14619a01e241d80c2e0140b8076800a0320748c040000b40c0d0741c09191600b101f00012009903104024210000e8606070122040d0f5444a201500d1a0028031107445048140309450200341400d2800011480e451000f280322002c40f40c00c46200311303000254802e011064040c12a6200b0310039034090300344010382c02004046a4004003e6641608aa03008006846080c007003079070000c01f0f60b1012854000000c000903e050708680c0300c1005604101c0c108441e0400070b10030703568441004880200c09201c420005003428040101460078007425000702c003d0300d6100d040301d20310943d020f4415542c03400c56050090743e41404a0110f031980c40f0f4440040c1d1a080c0c0c4020155004518030700060194031107544e41c0240c0140200000c2680d075a6020026170042140034004660b5030588005a86 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 900660818 1250 900659568 900659579
    0xd1d011505182a0c060a1802040f0b09040302071526091c022104260307021903111504150512012d0513050402040b030f07 54
    0x352400c202505540c00156481080642c03182412003880c860028814002030340e902c0c2c05198403c10408041d8508850700d81d0400d000c11800c4024072001c8001380880d2801d603280f4451000f40c07842600c034030340300c009509026401400c05400030526a46e91910106045007281d000c00c0e075a050807031301540140d0052204000c424290341c0010304031003d0345814110001c01c040d0010030030171801008001130003c840056280f079000c2c00601400d2002c4507000d00401901d44000b540c507140e4403403194840141400c0b240320000326008035400c0301c0c124607102d21056500e01c40510300a0b4803078000149408104408001640c1300081e24034000c00c4242c1c00c401e020b080d8280100485100d0f01400d0007101900c020385ca24048081c20f89040740c80e903500281035901c8070319080798680500220b030020f012410001047d4440e07580c85c680700d41240318849a0000c000780c880c1030b500a20b20300c03034141c203d400805420341000713140d0003a5038000d00151000c5444088440401c1c5401c2180d4000c41d10751300002024080e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 900662068 1250 900660818 900660821
    0xf21030304030e09010806040818220509010b040e120c030d0f0606031b0c06270b060102011104061202130b03040609050f0115120218101503061d0c0d1d01 68
    0x146c1032010007020945059503405100c0e10505a00c400210140c90402301c180e5940206403121146406000c0540c11507070104502508042d00c1001d070550800c2240602030500344919203060200f04010310300c068a844080721180d0120045400d00d000170040e8580c102510b0003a6801000d9010001a18901e0990300604484011041c9a902d402c0030103100c4019a00245040b103080d003221300007034070720080500c65042d0504200c013001003074460801602400b1400000c1440340000382c00903c403050200b410041da0748140c2c001c0201007005818a06008407055015002103d4000340115410f07440321002e07415038008403002c070307480ba44400f01e0703004001040c0004c10a002d1010002d2112080d05004241c04007501e00980840c040c03407800b01000d550b502541c091101e4400040c0002c00e04218100d0a00071f03800e405800700968004200c2040c1611034880c800488084034101c80a0484000c19a99500c0000e0003040703011106028405403d8454490880130502d100700382e045a00314440380c10b0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 900663318 1250 900662068 900662071
    0x10611010b01030216121b05010516020303010308070303020a020115080f10020430020a0e04030e01020a0b010605031519090b0406060c0209220b070305150f21030304030e09 76
    0x30b04050062046140304100d010460540316848040026000c000b440304031a0350448002c42507080359007040403414040194085405220040810305216051301c50503070362444280310090900104001c00c9000c64465030103030540303002501c00443c00c1010512241e07144080b0307030041c1c5d14a4000307902169020004025100c04030517281015420186088100c5100103000758040c400c600c81c1000817035200340043c1d400340721590300074084022036856100038000004212004c070f0100700e940780d1402856000040442d101c1d503001c50f0f001416800d255046840d5040642010300e0300b10045405243c581c0d91810320208005242a5070f003940e45814500c00c2038400c55200140030724074041c000d00c251940004c0c4502c40940644d401c00382519203184060540c0642c0c00010b25044100306860b04024820409134002c069585d420b1001d83c4074075240703c05c12501944030590009640126090604001101010076035a043e08203100019002c030b11400c591044070201d00061a0780c0e60403541d4a0440100d6 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 900664568 1250 900663318 900663341
    0xd030f0513030e010e0415030804050907030e030702012708011a040207081207120501090204062021130b040f06110604060902060706020d050709090b030a080c07050901061101 77
    0x118a2501c0c0703514090408440c00c81c1107410414403c1c44984961195004803030651040c40024a03029600d0820030095082801544d225004210102c1c030030320711a00451200983c0030026500e0000030750700641711010b1090802d801c0d0106003542082401812000d28001c0030301c080081303600d100748a50344070a071b500d142010784207a02c14420079020411300d200750f8041142920385500741d078a403030b41c0646003a042616850105410711001148800780c64000c1c0c0100c41803610b030b1800f20425000315000f8103000320286182d03544005c0c44001c02e0034400c921099044008010907260a4a0048825208001d030f0000c9113a5000010100040f00c51401460000c0c40d103460300c0e037a02090541030035145c144c0600040c01c415120001d100544d0b5501c1c01b200d200d6a03200c002103695600701100c00c4050001220b80c1e0007c1443c1c00c400080788265401582029200200500482e54065440320cc5035080300d8500042c501c203003440411240c944040e11800b902494840d41003007040c0900d0f01782900c0707200001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 900665818 1250 900664568 900664591
    0x9050705360a0326030103080d05041704060e09060a0b0406110709060e060111010506030a0f08130f0806070e0105030a0c12020f0405120c0603071b050d030f05 70
    0x1040410110038030100c840282030030014110655200c00c21150341500610759510070b41d03a0b5400000c00010404610300415000b180b56100e0501c0d842508460200344006801da04c000c0200c1c107c2510756030b100c2da034004c0c030508162448104400301d1100c00e4001d03400000100380c20455001781840c10715001913000381c3c21110846c0c002e0030850070880e503003e2403244506100411044040c80c034020b01400028109281041000c07941d90300c00e01e04400003d84105020408003000601d90610601a0340d1150f072014000b4030702c3d0f400b685c1d80c03410740c0c0200500c103450502c0140511034084c000203000030001d0071b10b0640b00300e18034144040a81810b1015140c0c1041c041250741c40e44540c5d03042025258420000600000c500f0050841030758440320691841940c40c0c400200c0c2c0428a01c080b0142094901c1515485207545c08403482c2c80c5d4030103407405825405242880011003640c8620401ea9900303004480c0b05150386e036981c1e41c16290604d0400214046078480c0407801401e076403031069a6010100224 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 900667068 1250 900665818 900665827
    0xc0b04050f10200c03161403012901140c03071703060a14040e010f020a03060b2a0a0f050c090703090f060c020f03040315180309090c09090f0609050705 67
    0x203001001c24203d00d41e03150540c0c140c080038404062004070840c410140075039404510103418004200032a020703940102c51200080c4040e1705052254003407043e18405040c0300c0080c001c0c601402046d940413514100010328850405454500000d005a002c5500080d510384403d4900032142482c0c268251080c00e200340204055a541c4c120076000f02c4550284034801d0041c01070101d0040c01c04440e0340d04040d800c007003180e210320260342d0080100060f00d640810031309440d0362a00780c07644030380b580600c41e0782003208184001c602c4a03003541800c0d01c210803c507011840d066607900e02e00e140e0407d0544283d082403400a80c01d04000714229444012407408000c051595a1068160126148007400744da6480840000c154001c10614254078124001c59440720f40e81e00c3c040300e0b85990114000b030f91500b031468507505502d9056500c42110350540364400f83c0d41c10619024018103c030302140e01001109100056144068030420a0030042210040b40140c2400c20240a03242c000c0c20302001c1050420 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 900668318 1250 900667068 900667099
    0xf07140703080a0908070c0515070312111306030609110301030803040f0501180b0901060e10180615030504110a06201c120c09060f08040309030c0b04050f 68
    0x888814039418204001c464540c524440010480b41c20002c0813090300040d406c0030702004203140700c111501103034400301c2d245c0c90b17064100a90294120040200c0c2d2030041c6951040489c0d004050421704240c03800b0f0400040e0b4000081860240e0302080c003203036440d40e080c060340c80c403401008049041c041c18240366500d945c2e60b08425200040c0701a007070410485840b800c01001b0f40005400354000d8007840d5640d0201e062185800130b0907520505550310f41000000c00c04228a07080380718010100c007010700e4503d031110428482e00341ca17000794103a9984490114021f00b20300c10302011107540d07a0300050141381030725162400e0b900802e2154860401138000b0422680c1c441c0f5035441000300c00355501c0a24640365001441c00e082400d144250340c0c0300c140b503601015400f160ac40c1c990100f000c0b0500c070001c42800d040d40c8124050142d10005103640103040035040c025480e0540041c802d00d00f124070203550751281042444190441200ca0700c00103420812032410f800c9008006004440386124840061b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 900669568 1250 900668318 900668357
    0x15030a05090c0a2705010914090606241c0e010b030c0622030812040c0905090c0618040e03180105090604090504050a0b0c072001080a050621060f07 65
    0x4e220340030020701880c4610924101d01c01c8212401d8010007424045540c444080c4406845144505442c1c000084002400340c1400a80c10f405904003918029104962500c041e100480008600900081c100b00650b0305640c601540100189000030005145041d6926a402d5a0900c03010500c81d40c05106420b02d00c1d910202103861103428200c1403600703000c9031419014210b16a40c8041c1c880c0c0801324103d0345101d04c0803405482248540c80c406601c1f81c40c0d103000e0341110b000780d030f0350009644009441c288500340343d07004100380d11a042510360300600c15400a402d441c40a4076122507a0000302d041c0b00c44426032800071440e00c03001d003400760070403203c0d5000c5200c0b800703030340f01c1e03580030940382c202080601801b484401906500040203013094070b058091515207900084046815948040f0303070081c1102502c440703c0b0100c1e016074a41e005921410101030142c10040e0205070b000d0a100c0b20304802800c2680e40054006154018058500e0100029020944014a2002400102c0c015480da24030309 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 900670818 1250 900669568 900669589
    0xa1523071a072115080105090102041d0103030203090103090807050f0f160605071b0509151512060d1e0510110f040b160c0e090633060915030a05090c 66
    0x36031000104108480b10b982c4c082540c035440141154a044180441004190000d00543d00281c001c0c4611855005100103400000d01c4042c00603081401400300941c03003a0040510140100999800d214168880504081403020b1610345039002070040d42041d1418019401227a000c01c0300c1c00802d42c81e0020182c558456040c0c000e0005980800b544040520f80b01d03058045c0002812142c0e051410008022862000300c4035a8810750200c610391564940781001c803400c014120044010720f4840d4018040703441e0944100310344c8402d09080741a26000180074440c038050280004000f18548184007100b165840f61401d403007424100900d030138411040c01140e04580740704c90700c5940c5461080c0b400519202d030030401084554010b000003002d8602030b040780d02904081c400d82d007180d181d21101c150707800344802d1821300303c25480760708404144140300040c0800501400d154601000c1c00b0008a800d201c0c40d06c014045040401071207140f881034443e280d4026180030050400c09026030029062010 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 900672068 1250 900670818 900670877
    0x30c1006080a03080603010e031603090905010323010b032401050a0302061603020c060a050c190b1906180c0801290901050d0c02010f0b0a1523071a07 66
    0x7080800310f05e03162402d40c0038082d04401e41098076162024a03018048002c1c401d8020307000201034480108840965104540c12240d1000021501c0b901c0b109121070314ac0c1480f200310507155a40c0340d040042d5201402151042c2425565070a084200b00d45c0c0440404c806800c03175800340c8481c11040c00146c40d000200e544140404000e641400036500d0205d240c02003c260071901b05801040c1046129005406008100c2002042e03651141d00c2c5040c0e0000e2100004001d42a401c00714003183c122010500001c000032480100411020b460311240d04e10400c0c5403d83c4003c41c0c0d03480341039050003580042103a024200754a5108046a002e048268803c05030810b5424a0031002901034400d80c06442121010840b00000303000e14103204001074001c01091007000406810416405940e240c111454003d0366502985461074002880e0101ea80c4048007401c290303469500c19030414030401980c05032170620b10036081d440001c240680000040c07803016000e881404854401503019504c940142440c0700c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 900673318 1250 900672068 900672077
    0x8012102151b1c0314062409040204120606080304060e09130b0f040b0105040b01050414010207050a030f170315010c0206160515060a0503030703050d0617030c1006080a03 75
    0x1540014810740c0c61218440745980c900c54400400e4a0544410b4851035406191302e040002c040402100c003548581103c441b503100441d400b50b40c0d00c90080c0c0c0300120322103550040f01e41c10b002107400400c0407a40a9045142c13000704814070003042204600400380509000300c0078500382850300c10080c143d826100c0507140324480b02800a00c4d4840344164a00f0b401e078103c3c503442e0079401c0221280e8a4030200b80e6094814640d4400007140034141400758441251042c0c0d600c42c58149014511a03080300c0c007140036811805603650002d420b6440b04a10b0020318014520650b0003041c40c44e0640c6600300710036005010603001c2c002c010702c0f17512044030744580b80c80c01e0820008d561750034400101a8032494090b051080104021007080c010001026200502805204090313911181b040280c048003d204095040d4030801c441000207100c1c002415010054580c04200191070320408105000301d43c000060036032001c40c0b0104003c1d01005840c40c401c014036002c0014500f0400155192020000083e0510 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 900674568 1250 900673318 900673327
    0x504060f0617070603200d0b04050c191d0607050a080f0a0206010e01260a05010207030f02010c090f140d0503071101020d02071d0402031501060801210215 68
    0x251504030680040e10303048100700c03607902d41c1003a0542a15104640c0060311440c040420001e019101d079078440340240c01e001046166a150f801501c0e402107007822000d17503d8113500e140b1600c45016290140c0780d180c400c1e0b5285c0b43c00f02124401000d00341841003c00c4000301e182c00081305030201211070001e013901c010f03640b0141030514031702d003030305040c4000c0400c140042c03070640da01c078400050f101003406d43e42524107903641d0f403074050504082030017041300040020741c03e095100324071058418138504c100705548400c81907480f0542281c11584050b40803503010703d9410340941c0c3c20320405020300581d0130300410f52824903148030070704015806400010702d000800403100b40d850300810440b4691100449c8e82d5220f880c0b800000040001500c0ca02521403004001d10f00790000c154081030b14030901c2d25504018441e000b10f01c0902c000b0300140d8160151003039103c0c0018000d04528003030724054541d100c0c19494042007420903040c07181c11000d48403143c04c00c000140d403000c0300380083c0c81e60002000d0311b8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 900675818 1250 900674568 900674573
    0x702060f130f0c030803060f03150a0e0f0d0f08061c1106090d3e0d02010e040f05060a0f050a0506030717010312031107051504030504080322050a0503060a0504 70
    0x4000b0b0300c81c000c1d2684100860000c00c00c01e18200035407140f107082d1100c440b012500001c0c5aa20300301c440022310804800700004507640300350b501026000c0c080030101e41c402c000c0350703100703d0030581d52001c0040010341c80d5000b80c00d180d400c90342e0150082802d507420001c403080e001415014104040c402028101c4000d49208690f0341e10b8251212100e00034040c160643ca5403401b44980c10300303521400032150400c5400502e00780f203007900001000114070300c3c800c5904c06100700007030411140422418049032600868841d265403091511060b040900050103080060801040c10107652010240f0390041c001070009480b070002040480340141ca44545980720384400790b60034407000c088401c28059120001040c4404001d810041c40d0b1a920f00300854100e080f9004260f100c0c00c440a40258028800181040581e1413503d6006000c0d18120381402d03280c010950445d440154400d82c0d21032160342c42102e5071003001c4650300134001242c03902c4110346030402103500c030440105030000c2c00d5902c800041c01e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 900677068 1250 900675818 900675833
    0x1052b060b1c0b0106020307020105180d060f050604061520100915060608280b03010203270703030e012001110a1205070813080c0706170702060f13 65
    0x4062401412400020301c091040401c410960701c043d42d80c0900c5500000f0b555002004451030300d90180e503114980403036031180b08005000007044030b4001d10140c00d0003001c15002e129803a0490035025002c15181401c008100c1984c4054001914a007155040c0c507080d01c1c0c10504882c07041c030520307922a15407001c51909500700195001c060005605047c80c0b541000b01da41a00916264150005c00513180c80d42030880ba10041240c5104014007c004019180344040c0103102d0b241da40700310003040501d40c600200303082e41c0003601d070242001ca11106101080c1c065240d9010031503a000020b003c61071458800414010a960000d814032291102a2244071310b1042600d41006001e4000d004118003490030440325440210034500084000507078400c10102401544c1c00340d00386555150312034440c185445a0701c1403106086800c8141000009501c100c107100300c40c000e000d561500089409101c0c1080380c8243c0061520045402c04c108000440d00240c2410350007460b904c00311800007406142021 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 900678318 1250 900677068 900677081
    0x14010819020f03102003040201020c01080c070606080d09050f0303030a090203030d020408030a0e03030c060103060b12070e0405060c03010609030f03090306021b1b0a0512011103010b1201052b06 85
    0x98160284000d61800800300790070108000000c02101c4034601700e5035500301d00900041e90000d005800108101c812903100750f8031240c0108440811519044040c2d6035036040f1485035200d1a4941c0284d03c050320b10303d801148440080c24259224003042880c103002079103e100040003015010360310008081952030400076030b410380c020000115650364440701c07180d560750407901000d40058010080e42c0c0b003074100401507401e408448401070030964215950700024003568104580c001e42079981c080c403214410003543c00146045e001128042c02d09050840c200701c801840c5030170402040004200850b4001c0560007200e03002003007001600c805182c2141d807103040c3d50014000c00d00114144040b142c00c100c000c4980d201c05001c030340c09960a144042203014900351b18039484003004004101340c0c204050500100340603000000396141c00c028003c10941c10a030040c010807035020411400038040042c0f9103000d00300848002900484140285445401d10318081d0040122030000e8807c100d442d40044 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 900679568 1250 900678318 900678349
    0x302040e0715020a0b060d20031c0305040b10080706080a09060c030e0d08090c12010912210b0d02060d2d1103150126191401081902 58
    0x1480340802c00e21009685002211040d21a5060140400c156103132498101c41d40d6503000d082e40c440303002c01008401020300c03082ca6117909805280e2200c09000d101030000c21444600da100041c09052901700350120140c000c00740f040c08601c0400c140207541c000070b4010103c60031850841d41c0e0780d55000c4071002500703032001d0041409007040900925150580c00400016004008131001c8156500d011240d142d000c1c0d0380c0000b182c01200d00c80d140d5050441a1600a003030030b40000c200003c40d680d0f00e6255a03440c0764008000b50900e4020010000b0902d00201c48102c050300c03d11840003031000080300030340c0e0070070001d1050000040d40042140b241d04440340e04807010b0715072520403120004820050200034500159030340381c444200458002e80301628019444051041410303581c1400548401025030340407444268840c0711003004140071102c13184500758244800b000420300e002100140e5090501c0e518040140c03100602403c00700180c0103010314060000c6c050400014008207440903da003c21 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 900680818 1250 900679568 900679589
    0xf0412060609180201020c01030c050301060f0903020a060216080309010807050a031b0509030f0a0f30030c20060f1308030406020318062e0b0a1d0105040f0302040e07 73
    0x91030391802007030780e444003241d000386c003a5036500021000450842d6815529023022035018030040c41010b109a90081c007005207404e040306595102d4000a1020100f54007000060f4025803801c1041245071060a0042401c48011403d240c40400041c00d620b800600d114100400410309034449840394006031480ea4103400c0b4030074280c0b0903810080880d404240854043d2152003098150b000b00002d00d0700c0059044052403069000f590382c0d0490400d0020b0200d003401143d03a001000d04070202c000d01440d403802c1d03280014000c3d20040d01607d4504800c040d1145d441c12a029800d19900104021394404070154016407265a40a503900c612105404003400c00c80c0c011082104001841d80154005e0300c0048070780d214010907250325960b170f40d0101d445800d128145104212400443c0c2c0001059078042d003028413183d61125038511003500890500000504480212649038070003513108120070304203103040c43ca41414410002d004003a40c0c4002801240d445900070400d60040c40060043d16500c200c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 900682068 1250 900680818 900680831
    0x1905031c0617060a05070c020a05040c0c12030e0c0d15110c1209040f050603120c07030b0c0a1701050d2006040f03210f0c112101050c0f0412060609 65
    0x80303030b07a4910301200d400d00041c1c90803010806e820f0140c40e00f030301800d80c020280040a820681404090042c0100b800e052100c55039070f160000d055011034244480c900c1c0e900040070040e4415080c44c017185410414014005400c52901281000304528841c942c400c6022480b8940a194050188540b818421903806110039102010040c03900424900c0c1d01180c06000b50301d0081303050700c00c842007556200d42c16480a14400078007818200902590b5103881c0548542950700e45071410031a074101c0702c80e10315540000301d000403180c006a005100040c0041801c00d198109000f0565a0038910720240030308140340c040d20241070414102c80d640103c0600003039281c40da1148100700c53340e00303130004403151001810084e5419402c050071f0015002d481d6155589400c020400307907940c0960440684100c0c107460b061144580700e4003070070981d854410003c0c403407072480c514840742101d002038060b104d110310801c090450400180156402d480681c0342e0703584046030601e45000200740e6a44905a001d0a20301d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 900683318 1250 900682068 900682109
    0x5130807110f1e0103050c040608131104092306070906110124171c050c0f0106170c03070e010504020f04090c090f0608190507210e1905031c06 63
    0x30f07410080c07000a813000c0c82035403520600c02d040d60041e4090280000d10b00c0c4000342c140074070034500c84000360081a86500e50040341c40401d0a481c1021815944014240c2261145542d8203100e001d4468140019041c035040003800100300f210103108030020041890b900c3c0409c4003082d4070104481803000340c0c907025216245600b41c420682d0b0311a090040907040d620251402010541c0515404400301c140781440c0701a4080d00d90350041145035625208403030111303401140034455240a410418006c0800c1e000307508203c1d140080c1c801d426402034202e040100860140c3c0314001c3d047d14021900075031180c01c500514001800785900c9080170504005c40a100c482e0002200400e8880034500788850790307200c800c10788a01005a641708900201321003403e00039010340d406103410170040c1c81c02d801420148818801804890203906990550f0f81c104c407180301d0400c10101d40c00003900f40c44544680c03240d40710544c4174000d09078905004003030904021840003456101c10080d010305400300711894202d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 900684568 1250 900683318 900683359
    0x150c1205040515071d060a0c0203011811030102041a2113021509030a02040b040b040614040e0f030d0903030b06042402060115050d021201080d0305130807110f 70
    0xc265449183c00c41008281c0e220b1041401218004070b00035146107140002c0b05001080d4448941c1324108254150000c006a4080c01080103503c40c0d01c0c4100660f14075420000c03494600c2010540c030a81c41000100000250703105140303100d0301520a0107860b60444c075031070f052013540c6481c49031034140010100110b2001004000548900039200e04548034005083c01000d4441c010305d40e0b0b4507500c1804a0401490542c11410010030040d01c0800c00d1414000400c040d54a590840aa4540400d08803850390400c2e2040910000c842c4009005404090607020380341d21410406e170030135a407501d420005050103a001100071b20710242c001983c681c1d94008403410004904078075841030074a05c0411030a17910000f28a0f0503105102c04030a4080e03282401035400354000308080314000e80901c15180c0f100d090764640c82c001c000710406480c3c600c4840000a084481c02002d20a603540007003070070400309110744296514164481c14440440c0e050900040d80c002518920951040d50300b405c0c2031020b00c20 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 900685818 1250 900684568 900684583
    0x4120b070f08130f06090c06031e0b09011a0c0a03081807060f050d1103131203091a28020a03061a0a0f051e03040c050d150c12050405 59
    0x407603640104620208004440c550020707500a118944400d03801000700700125075031038400b440780d4000a04032099903141e0300c052605a019078007180d5100fa03010030140081081c9103114001c40700401c1007102c07400029014003410f01030f101d01144c040c011941004443c40440301c02c940c0e08c034100c41e5146494500100500301c2151111844144d0300c000441c594000100802079031143d864400e0110503c0da4102c80c20f4015045209181781c075030214550110000009502840c030394003031000b80300701d00d0801e011803410788101c520030545480506000300d50000403501503801002d00241040c0c50352019000480380c04401344c01040384a1400c2d501154003903008028940041d102481841da84001d07000490030701c0103103c560010b04200591220303110703420bc892110b0303581c10024242800540a1b0a45421540300c0c0c414001c800002d000c00d220a2014100080800b01c0e210762456200e603550700d4250303503d42d8541e240c058444c000c140d405070088a40a501803415181001103150500740340742e50304803 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 900687068 1250 900685818 900685831
    0x6010203130806100b2809030f0b0105090c0f070807030c051014090c0306040b1f0b0703200309040c02101103010e0a0e060f040203070e0408180a05010e0d0804120b 72
    0x180c02d1300001d00e5111000030703a100b9514100b40c4c1605e05151401007a0b403919425540800c2002001020000954107041440da540c01503020b05410342c144010700102c442c0c040d0180c262144180301118031000c0010807911041c1d4000d0860791510380d94502695036045040d001001c0f4094410225880e0529a00002000480e0107511311682c40c4d002d180e60b1211040300301d19806400220009012441030901c80d03801c8070380e0300e10075041c03c01c11102c03495140c0b46641051690200001e043c03401d05070f101214840c20b25003504400d0f45c8881e003103240c6669110f110340e91030243d038485a1a6000600a00c0b00c000706a28401c8140001e0308980101000c0364800d00501c8006025000840c4091040c0d1140d1007001030390070001c2016443d400982a100c0b40c000704100d900d8400c40c030300440c101c0800c1590030f025512414100b6280d0428806c40c8950300f2145c0700d028014042e0b000300f0032950f03900801e016640142511090301200f4941820b001c41c2c860744d008110480180c034940410001d81081e154821031 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 900688318 1250 900687068 900687091
    0x40509150411040b132309060a030209070c0c0801050c030a050406110d0c031401050d080d0603050d0801050418121b050d0807090f03050a0201030b0415030308090c010206091506010203130806 84
    0x1900d44514500c8111b910003c03504030800d8000c1080242000d6440d10740150000f00b0241c1216681d50018443d42011641c48000800c2e0303a219204005000c0c01c241c01421030314000784514130f002140e500e40ba0200a00e14007081e83c84001013024416160300c0b040a288161405c00d9407054110342c007002a29040e40030f1000646001024500f003207140343c43c0c0e416203c0c000d0603007014003000d8451110b10307002441d0943e0340c1a07507900c0000001c2c0c800c101d001303410503e070b0711143ca85600d0402048111620807400d07006200181c11020000f13150300000304070508542c1001900020343c405043d1415030490402801c900c10406c1002607103410845481c1b062116070355400c616034641e40191101400d5100061043c1d000702c205000540c002d801c0203040c0d4102a00020768090021080400824aa8030580104400718140b190b015001d0007417040d6000280004c0c001406c12200042e40c400b04c1c42000c1e038624089030003280c1142c2c03080c400ca0740e030320851a540300c17001c41d00d9000f2a5181c0d8425100b4411b80c1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 900689568 1250 900688318 900688357
    0xf04020a0c0204063510020a09080601030b060a090c08160e0a0b18100c060218060d0b01110a08160c030b091c030603120309020111121e040509150411040b 68
    0x401c820009440d00d511710f0301409a005034518204040d40201400405004100002281c04c1030101b040900850159211554a0030500240038414100c0e0f0490310b81c03d42001c07044020503800203451500416000d41c22460b00100302e204540e505a4070100f40d501007085c100001d00710b5640340140814884e01030500022020301c0041200701246010f00e01c02203030751520044003144481c3e010304203000300071031400c010000b018000348059201000341d14a6a945606629003564407264401818141c20002d086a0202d61200022801071005000c40071404160702c20412000c0314442000750360065a40c3c50b1400d2500340107072140380c4d5001080f000c284840340080e84601c20300038101220303080550380352086428103040b400341152003001d90620074001e41c2683c45060400041d9520f4200900458071000c81c1d001c030101c01c405c41442c044001000348010301039a0345c1e100c481c58200780d90441000981102001240280109110040d0a11000f080004e0202c140c2401040003107460904911b22 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 900690818 1250 900689568 900689639
    0xf0a1202130626010e010303050703050d02030403111c1d13151502160e060d0210030209045001030c0501020f0a050717030d02040306060609080105060f04020a0c020406 74
    0x107904240f00307076904405c8140041000c24040c000074401e0038083d1404914080c040c0b041c1405a81c0140d03000c400041000c034103450011018880d00e440321007581d15603a26001070b600001d0209007480c59400c104807004034030b5101035440c001800204110b0100c20f01c042d01d00c0308140c03555400c07584a011a03507860700c08481609803011a110030320a0049950340030030f03402e081c102480c406005004980100c8840e4440001da41c1d40e000400c580d121903a0301503507c0610a081c4416185003018900700140b0140365208405005829032480410454520b02c0c001c030800360300002c0c03c0c10b036003d10028014290012060064400b034110594400f0380031221aa403c0c0180d42e80ea5030200b441c060a036401a1406200400c009000d102c01c20184030101c9040c0356a40a20a04980c420760003103405940e6260100006904014001c0c01800e01200030802454010041480e102e00025018070455000480510003402429000003454000c0c0c1f08101c0d20341c0303c00e00f030280490f0f03820000f0603180301c02c400b0115 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 900692068 1250 900690818 900690887
    0xd0f0c0e10060503040f060e12210103020f0405041e050d0f08130201180308030a06240221070819030e0a031403040f1b030204110f0a12021306 63
    0x2150010350f6101e240da034458840c401000041503040720b04a4640c1c0c454124a8010000d1068400d540c2d01660350b503114034148520801e42e03c04050b04050181c00c0108090307980c100c400780d2110b41c2a80e003c5035550747e5190044584030000040c440c1010f5506105003800000103090486214a80315516501609003003581c240100700c400b458170100c01d421000041d40f0851700303d000607501402c440651612651040f681d60070481d24107019654403a002c200c0104880205800458080349403001809c0b650720003512140703111003400c106014904240c020003216022642c41c25004400903450381c6c1d0300301c0c1c9441c4c10300105010304002814000c4010710720790701203446000c550345074030b82c01e146104010100d1000d400041040e12070884a01ca102d01280c01500e16104a5603075800007403d4900710b204200031a0907003107800c034a45805002c001550351881c000c80300520038500b8140d5000d0fa034001008080e200e800da410b038030000d001c0c4001540c4c64010b002c6251458844122402010348650920f6 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 900693318 1250 900692068 900692101
    0x100f0906060822140304260c010c05060a02130302041109100806030d0e0f0a0305150109061805100f06021018170c0715050306091005090a02090d0f0c0e 67
    0x30b10054002e20310002130300325500c8102c590803601030702c1c2000c0d51154410351219460b080048408030740c00390500100b0302402810441c0c1c17424242032603281982c0c0c40b225500c850041c0302507600381d80000c89409080c180c8000c0802180c0c0200f0600115030120079025183e0440c0168a014800704c418202141e8050349249203d004040d00030031240317071000700c2101d0540f101c00c000c607085005801c14442648503a20241c0246010300020018210441c40103d0a907005032b0146003c18640b100c01d2104020010300c00ca9241541807003c030311034035000844048182140d100d01e01c0d100d1045000190303140c01040341102c40c814440100004088200f500d885103109400007481e18400b844207101902ca03510180035022005002c40d141c0b42c0e06c1d80500e0301600c1d08005144003080340401001074501e400a9081e51080100c050031801500d0800407840d1a40301401d107154540d00450814030540b04e0854400d152600401007540644150500c02c0d0500c134603005203c02c842c04540000e21090754480c240 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 900694568 1250 900693318 900693361
    0x7060507080603122a0109050d080609041113050a05240d030c08040f030b0114060c1b031029010207030b1b0d0f050604061d010e100f09060608 63
    0x100b07082c000c13103440464658014402c200c1003180340000c00c0403803400c1101e40060380c1a51400040d10b604242080d40c07800c0c4080c00c25204120b0244100041c5480b21040160003e40c804246aa0510f6200000712044c40d1031101841d52840e0804001d4a00041d13040980a84901e4142081049800591002c121841805550009001000307407000910a60490081602803580c03681410384460902400410b10340c401d958114400c80140403d00401e003031068900310886000e881c044030090016140c1d000d0450b1500020708820002d034450314280003010040e1007000c010800003402414640000c942001e0b01805242083da1010031540002240c2d070641750044120281651412903025540da25008001b004010912444000c1c030310a00550094034070841e40441c892034480180011a5025840584e0756511100506403031404505814155400603000721460760354803200c0c0360b0020b200e42c00020091b0794201c000521091075030020042d68101c0d65440d0050b01c82c101c100c2c04072800c10001 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 900695818 1250 900694568 900694573
    0x20a05030c15030711030705030901080a0203040f1113140915010806132d0b0c031003140f0706020708071509140a08030301060e091803070f050708060a0207060507080603 75
    0x80c1c410b4050b2500245902004901e0400c6160a10f0448542107800c074100c121415403011591410f1507070007880300d41d44200c194900714210715190b00e5503108a4411600640240120300c0800342d6030300c90380c1c0002041c0c5011542480204401060b02484140445140181c3e0083d01201400361252440e910f0403100c41d400100f4079925600048500244000000c6071649000d404010781c14a10b0000080460001004241c12403041e0425000c0d0b000001d0141c5078981c8104200301d00040c2009140044e0780e003206d01003d820116000c0c003480e0050564408199101d082000074207030b60f0008070307107056540d980d0940d0b003855138882080741062408511640451606101030010640c61824110fa1040050022804543c6c8a5001c0d040d54001e07002900040e034841c01951550a12440981e081000c082c41c40c000201651242038481c082c0ea24018160f14a1200402c01c0c45010070a900180400742d064500904201800320b0003580104800c4a9860800c4001a00107000700e503090300c22200a0007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 900697068 1250 900695818 900695839
    0xb1b070b09010f0f05040e010609060807021c1d1903170901140f120903030a140c0a08060d172106030a02090a060f0b0703170403050910032403020a05030c 68
    0x800d40e42d2001300c00480e410440107000000351882c4d11a0fa05000b060315171654a101800e20800030400e802c000e00840965000c400d415451844143c1d11282074481d500d40320b02c00002040030380d40310030f070741a000075072147c580c02c2c1054074200d41886d460100d0344200120505a2103c117406005c900400e4a4180840c140c0000078806080010043c94002d0f10b840326a443c1c243c07101103000c2e00030010758204406920210410100c41d10500c145035540c80c003440c1d4000c1030f282c511114030b541d1003a00c00160402000740082149a02c40e10204c00300c256100d020040351000b0001a03036503540180e282c100e4140800b00d4640d01c103040c80d041ca280500c1c809409031501c003007980c0070b000f00d03000040c1c0210402507440038001600c401c0c0c0301c1540c000c0d0011510456031030044c0e080040a00383d0424400c44180f01c1c0f40103100010781c00c98100d41d026001074502d49101c500b818004d90061456400604026440105941c1081c00005c00d060503030b842240c082030032580303840034156901071000c0d0386a00455600d5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 900698318 1250 900697068 900697097
    0xb25140706080c03131703040f030e0a0f09110c19170c0a0b091006080c12011e0e0109080a17012418210605130222060b1b070b0901 58
    0x30311103503015008550030b0180300300315171001c541c1f58011142580c0e01d00b410160f48041507404070f840b003050030003203400740381c03540c207000c0b000c0052140b83c402d1650342c55560400c0b0403c80101e00c159819040c10006642c444a5544040f1840c1d50790110708aa00000f4080c1504282030900c081d1102d55000000402804a05070754940600d44090100103452142d904005490081c03409044080c0c82c6072005000081c0e20b841c24800c14011103031444400342d051141082120030150030080520b52230381e002142010a0085e004d0040c455007001401203d00001e4244180b40c10440180344801c8a07400f00c181d684c0d8030345041c20706000d48509444003800381c0b2008220107101c2c0410030f10744c600094443c004e05030750b640c03111210310900a130300b0100c03140020664280081485590380c44581c01e8806d50509100707500140c10340c4000d0030700141c48004200018020741050b48084007501042c01d1140d5601c1d04014500308090500344524014460004042000c9101000351120340301c0684544200341d8600 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 900699568 1250 900698318 900698341
    0x207060314010504021605070620060603150403050421260406121b02150f06130e01021c1a06040f170a1203060f0b090a0b25140706080c03 61
    0x2201b0320659807521050360b40402e000b406104010b0226440f10031403048000d038a40b0303a00582e6441c2c2c1115030080c00070004962404148a422b5014172505802035a440389019105802079410005008060008801d803400300c440e030b030f0207640307001d01005900980942482c0565842c0c5200343c1c400b02800781300070440ca50040782616021945c182d404550100d02c2501c48000d01e40c49aa0440140e00100d5002403017072030323016610b402903400704500083e1320f050700c04a4140c902c445007a41070035a132604900c0000e4403e46c142c41504024a503000c00041c03a0089807030140040c00c0c0302c00c407191462500c801240c6069800c0b50212240540030300c40b50f52901ea40b40d40324450700c25030160301d4090400c0000c0000c1f0000207030b050525641d00c0000e10503080241a2030140c40b15005450141c1c0100408103481e0307111420081180e0149040d16550800c0c5443c2c45450301103010f900c044039981d50321240800c1501c1040c05950541d178001c80710324a40d51030044484040980700e8820100081001c01d442e0500b0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 900700818 1250 900699568 900699577
    0x118200319021617121603020c0607020a030f030c0905100e100305090d0815040b040b0310060e13022d220e0c06090d11060304030807020706031401050402 68
    0x1c1d410070500d4107000200c9001a6030001c220389095500000348103003040683c40141c0103122a004c3c665042c00c03680c41e401a4001c001405c1d5018100c00216042e18892003601103400d00c3c1090f2041e0b9907c1d05103200e002c1d54548280204801185414005183c95442841039552024060361010303415417602091042100e499040d87d0200701a2015220540c3c5400424543d200c515950004952800c00102400e100302582c50b4420468081d051000d11003c07a002542e01c1101154002075401d141c40000d001070200b800e12a4250003000d1030709456042a0b4003600481e15502c0b4444480e40e01c00340c4561810b05850002503000b8403400c01d81039581c415030280c410b0310486a00d60f80300c0c800c291001031500d840a00703521528035a41d8140a4002d24103015100389140100300504904070f0600025145d40034000b140d50040c0355100307010061200500c50300320440380c0507103d555641824200241014800c0f201c58002d44203401d00000e541c0d20078454848038402d0701c00014004d0b42010100800b0390320 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 900702068 1250 900700818 900700831
    0xd0902040507052b15060207230607060f060513020a080a0e0715090b04173a020a060c030501030203060c09060304062d0609110f0a05091306080601182003 68
    0x980d5421703186400c0c03004640c900601880e80040c14024a0010f104a494030f072519a2600303a4100d0143c00032540b100000e46e03198660248000c290040400748040007000c0c5580282c0d402807820840d403441241550041c800c44880d56124007a41d503c488140b02230b550f1081d800070b010b522a02007004480000c10b64690141ca144c645000c0d040d90312406000e4a41280d0406001e2001c0300501c4a043c180030042070400c200301402c20541052080360703241404070280b010b0084000407590810206109025101100e1741c0414100600142c0e070380d0040c024002404101d000e1711a00020a040403c0b0100744d50100400814075465a40e8684c2d03260b002c0c10480d40e00c9060302d0008220142c0310b0480b542d5000c03210400000028501e0724150010080d11005141c6290904080180c0d007124550f840880d1802100390038841ea80c1c82c47c01011610002d0b0440e158440a483c4c00c0000c10042c0000c150241240d640c0d0540001909036501c014007100c13803894850b0841e0314003c1030342d05005002d10196038403c2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 900703318 1250 900702068 900702071
    0x29100906081b0a0e010303080115020d20030f03100f0501050313060b04060e04050604030f0f05070204090237060e012316060b040c050c0a030507060603080d0902040507052b 76
    0xd90311341051400440a03002100030585210042c000b02603541c1d101c0401004c0303880241070840111202404141e035404a503000e240210a81c0d0391400002c0045806400300c69945542d84d29000e084e2018107840d9001c0c940c00059000400070b80b03507100d5401e6900440a02d580390b0040041c0d6a10080103120494005402c19201c0c134001030443e0400f4800c40c0b00e140030b000504403c4c40d01e0b00c1c00410043c1d281140e40188042120013201c40b40d0701070140c80c00709605540c0015200c0030750001405980b036a50100582c960b04800030740103813040b42c0e044c080171702c851b035036914000b0784030ba00c143c0b2401801e000c440c0c002a62041581143c0034a13000c869040e5010050641c0780002c006101d58941101d00000c0c3c4010b0385413502111141880c3c420400c607280a0b1a11600305409500d50f0340c0c07103180c24800901000320215049090060542c49000110f0340102c2c001d503a44d0306006618080c250002060307101e540b41c00d0015900034011401c445088107180000400744001c00c80030070040390011500b40049 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 900704568 1250 900703318 900703339
    0xa0f08040f1703090c0103110f070c0e010308041404020a14090a1505070b09060903041710020a0c1505091e011104080601052e080429100906081b 64
    0x4064200003a581c1458500d800d50324580042401c5c0390038110303901c0f503042500d41445c880c014a948002d84107406203100700b043da11b5406040500c05080d042c0c0205940030369a00c0004100610b000c020412182c000b080c86114041307001c108801c0740140038605001c80d0300c10b444040355040100c01426030319401450303200b4983d150030030070700203e0100d004000441e8000540f0001d121a080c0701c580d02101c0f000003480350f840d0080311103407030b03014602c900c00c46411040c000043e4a04203000c0f0340d5a072410200110344920607108014250900b008041e68140c10548011480d0011802103c1c0f10b6510100108018000c0d0960014201c0c2000d0010a295603520354410004070751000900050050400034810707541042c0c1000316009c801006100d00300401b014039049152030300c080c4a903060950400072002d54480c20560400c1544400503103d20080b1098800300303e14002c851809078603070200c408000394075180e0240c01c41d1110701807810554450341c50066901c038580815113a1950281510201 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 900705818 1250 900704568 900704573
    0x708010b1c1e1104111e0304031103030a0507030e03090117070905150a17092d1f06080a0b011401110a0b0601021009020120120c010501080f01020a0f08040f 69
    0x3110002508840c8214046101d60143c42c0174041c80c2108907000040500c5c1401107040f002580113507848050720b01034003000160600d4041d10b00c402003134412000b602d039a45031a400c00b40c0249000c4039540c003c2840c1001071151240d002042d91042401a1a882c07152180022030440a1034000c008604211054501240300d8550f504100d1032110602111030726803440704000341401c461402030343c00c0202c0308020040482e00c0000d0b0f031100a1252140840d14402d880710090324050550950005881140800c0308100c80001c0c910b01610a001e44c1007098980760b00b02c3d69201e01507090302600c108103a40041c04150b9501c5004030b501e05050401c0d0801c00c00e24682c2d00d04004940000740e030f002080804015076035805101040b100540c003070041001500e03c1c1d0000e4220030f0103132034100885204411050030058108034890b5007406209005427554107102c04240a07000034015141c00c3d0260030007511030021705009851021081b0344a54401d40300d01101111000c000a10554001c0c0040000030007 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 900707068 1250 900705818 900705863
    0x180807020d1410140f04150209061b0618060c0a0318021504090b151204030c4d011b080307030501140a272c0708010b1c 53
    0x81c1100e1549020403518210480d0b4030504da401401c0b00c2c031401e0f03400c04010021343e00b0790054880072150704c001a102c0042d88041000c40c021070a00700741001101160303c100c0080060070910400c0d007401c100c0035250417607840390f46031602904e40e0b40c43c040b01840f0024415000740c0000b03403401c4034a20381c1c8008005940010745013507241e01604c01c802000050a1110781c000780140360264400741c4402e4003502c014480401c441c4501c8400342e0a001c0c240b004182094030680344ca01545801c04058101c545410500001525608801410601001024a0807002030704a01c06001030725180242c2c41056480055407024894418005c0000c06021032200081200c4050b602805003580c1c0001c40e907050441080c44d01401c0d14507a403152100e00005c1200150383e0411307a4104000460340f004040b1402c01c40c42c0a0110013501801d2020000740b0364680d41955140c0c50300c1400d5020440f0242d60f601c01a01c0c1c200c0c1d0f103000085030840340920320b01002c48880351500a5251160b0031140202044848042 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 900708318 1250 900707068 900707083
    0x13121d180717010b040509040516030804230a051c060f02090a0b070b0106030f02040e0a0902091f050904080c0f0610051c0f020a0f0b0a03180807020d14 67
    0x1220905201e0500d9209a52244010a19080301090f50501684807414040c03446a107200b50041e4000500b000400d105c0b070000381c2d100c0c20284404540740c0c6820a05900580517500740022441c2c90380050010602500c01000000b4000b003002c10b04200034044040e00042c40742c542001300e02050030000301c072407103840341011131554016140c0754580b00304458038074030390710803030320030100340040c1000c0340007168820b0440b449401d000446620440240b4064041c17580001c8424a58004100329585190084211207200711104042503807812624000300e20070358040403401c52003081c24045802d250b0801b580040c02004c2c0b043c1040d00c9152583d240079454034101b035154200006200141c884840d22901074041242d0b4a50007500c0b0a0012088000b1000003030b00c140c00d142c13810001c0d9150000c030030740540344880318a00326940791802d480b407940c84404900c0c0082d10b011b0714040d80e4403105403280038050344180c5903484d0000355002c1004001240d0419a0700000ca840d00900e225801c00004 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 900709568 1250 900708318 900708349
    0x50f061e0d0501270b010908010204030f0203012007080901031104090902010f030c0212030c09030706081012031b050f0106080d11030a02060105010f020307060606030f0513121d 78
    0x30758603050711500e24107462041c0d0240002010308010341c900082d0503000c902d4030070708103d00080e14041d0000102c61000d4140c0c0150041c0d44000303808014003910741d54288116001350024001300c03840c07004080c1c0030000c550740c66001c2d5005000590006901d03800070220f0038014035000c900b603d000c480700c410591195211801e41c035a030700d01d09000c5507000484103510b80b400d410200900803503081c0113520385442c28000c0800f400000000b0300d0b5a440702082c0c804032440035049601c62900c4240103800070b00c0c1501c4015001c410198001908203040e1408484950b0641e620342c030290742c070082e0a0b18032010400403213a9010b090040c001060003442080010850750000f000320850b00c9601510003140d2000500a81d0020450012201c2e000514941118001c0c60281d06a6405d85012815801842402070426040c02e00006405e45e05401100f281c00040380208580e4071410411285501074000003052000000300d5030100030f00a094003e183e0701408012155403002d0b03c0094555010262130 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 900710818 1250 900709568 900709627
    0x6020d060603180519140601170609030c070b09061c050105040e1b0616081204110d050c0f190b1b070e041209151205090102040f050f06 60
    0x208441541801240101c03604540f4648043d041c544655407500c40d2801e55000b484041c46061041140c2d103840344850380700c041c0503500307203503150031403a2061440d001c2042c00f203120311404a072940c0804011030f0300c10799011000748600c9140107588801a0030615080390b11820500c032200c00d0755600a5020340c801155240003482e13604203070801048444140740c161960f0701c400400c3e0450250320341402c101d05002c49207a900d80c60115102100400c07030f804014142280404c01f11641c0f0410411a03000d03600c909000207842c0d50450038440141c00100018020343d1158282e140c00d42080f90680c242c404014044150703030b004404900d03641c2e410507807000e01135140005031aa004116809807080034200d5402500c2081c2c84d001c070b80e03450b44001a1018001981040d084091180109805030040c403500d40f005610b4007810202030310044c00301c8001161241400002945010180b08a4055818580081e10300b40d0604060000c09940d081c60303036400640800481c265102040105a640c0c40f03030209 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 900712068 1250 900710818 900710831
    0xe1201090516300f14011b050a02100c090503070f030b0c0f0304031b061802031006080d140d0207210c030c1506050a1e0b0403020102071e0306020d 65
    0x88000b1900daa072008209200d8051910040406843d036006101220f8044100001c0a410004000307040060000d19508030884c1c2d00b40008419000051807043c1c0b0184000d07414183e16050302c05100e003210100041e000341c1c40d4441988102c0e400b4404503082860095060b07500c1d2008a0318001082d00300300081441040d0400030405c4d0100000d13403021420081900348402c00165540d103000140c002028003c142c1f4040001419408019050507001003007401030190b01038506400b04007200702030740240240c0f824608002c0035070040c601113485140041c03511024400085400c01d00708181c1c20440f00040254420740000307800070f030a980e0300075000341254101901d410103900c12a00d05860902000c0b10201011a400c401360300300c465004410031000c401440c0c5801c0c02014582c02a56000c28881404035002c44024030b4400380d07075081da03c0d07100007503254105c0c029640600d04c8000e005a01040080c02401c4004c52441d41c80c690b0380200f140c0c040c1d00c947d2800700f40e030090142110010f94800 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 900713318 1250 900712068 900712093
    0x309080106230d02030a20030607030219080f010605210a0e0d03202b0b010906031413030210050703020703030605010305060f300a050c120d0e12010905 67
    0x202e0754064030440e41141c000c0020780c0030a0300c40c8840200a07101c0070722801030458131050542d482040010040075501c1528010300041d000b508183e00c06c0b0303035041400e8480d030f600300c1c0a000100d000ea203203040071780c22503841c01c0c030212442e41c0942c030b041d410420800210600310b90185000c0303008405002e80030800010200c80a032814110b00d4408003014102140043c0c003034078508049034003034101291700b035464905841010301000d50201011404049080034402001c1c141e00081d0107040c240d8804540c1d50780e03a5001c405440f021346040c404a8501c401083c03800032120340d0b61040511078015140006a488641400ca900803500c4c8404250002401810940d251050308050602402d0400a40c182040402c448141000b2540e00400f40d5070031124402c1041084240800140c80c6003030184409451203548460b402c100c1100c040c410100e90051034513068a1566a0070f901c1c20007010303429500391302140c0149040c2e45040e001800c2c10455450740d4401c1c01801c030098002d02c0180111051803 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 900714568 1250 900713318 900713369
    0x1f0e12060114011d01030507051605010b040608010c17060a050d0503090108010905070509040b01050c01091b171f110a050c0c090105030c4005070203070f030c0309080106 75
    0x1c0032032410003060030481d4582131901900c2034280d4400b0b10b000181591800016100da1040400e089081400c100d280307000c0100542040b800100165070900003107950310040c0d0701b0384001d136420a02003240e0003e10400da0380d50454060784501d0041c00003000c1e40c1d8610100e00700110707020341070f200754000050000665812441c402d005180c0c00008119920700558024460b000d84e4400380c0c410351b120300c009840b980c400d030180c6070804440002001440854581361280b030180c00561100940d0131040018a8400416000340c2c000c05a03010f0300d828250a80c0000b40c5011220001700b1003a034039030599800540b078034003805100d1155103502d0341e10000440e80a180110b03a1519510038040e0b54018803080d203000c28480b106a005031650340581d196000d201c030a92102542d1000b0f841c0c00016405201e500d220100210722504260420854a034104104c0e1648140d410192400c1144051980000d11810601100900038a043d155403611180c01a0075110a60b01c0900e41c1a201d4110b10a83c030050b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 900715818 1250 900714568 900714599
    0x503031e121e070504030f0807170a0216050613060c050a05011b02060f15150415020703020126010308030a090614270a03050f0c0a0506241f0e120601 66
    0x1913091140c00c0c0361665a0b00500c400344c0202c000c240a0300461280104005440c0d00c40c044042c180300f080d00c070480000001c3d03442c140e102c4500c16a0169910000b2181001d60464901100c0030480c24225070030300600355a003181002045a0500c11811f0820100d5000c0c490014401c02c00c40c00180180f42c106d00081c40c00d140a000800300c1013080d801d2096484020700551101d80050b1408141c4a84404402006008541c08030030301c560030b00003103404668040342c80d0302624400d0325650001c14418454444000148401a00031400000140040791588001c1c50b405405a04e001c140c603030480c0c0d0758005403101e2505109034400c8400501211440c00ca030000e12520794a82104811004070021990b00d81002d200074060241c0001d03041e2921180004035605250344000302e40340180d95281440d55100e040b034100541d10013a80382c801020b801d607c070780c0d01c41100050001101d6907061140315840b1117401e0340d1300c09221101c590b020701c2e501c0300c00360025464840d1014081c158075101c509480b4054 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 900717068 1250 900715818 900715831
    0xc0f100b040e1603111908030409060f06050901030b06041d010f08010e0303060d0f0c1805070306120b0c3702011803030b0f0a031103070504060503031e121e 69
    0x106034818045a0301420310355044076040400c3c181118800004200c40b03000e4500500c00c0301000d40404500b0047c0000200215003403c5400c1003d15030b40e600c21445144240540400204104000c1206d58425040840320050083c0b40c586072558403420403000c481c40101b95070354880640010040e000003c07088600400201000313000380c143e10b5455984908c8003c0c0312911440085140c1418085644014100250302c02031203517981d41c40b00c0902d00c044190740d208102c40d40c10034000481c0c00e4424024001210f80360b0f09407050001481d070740c026521100401c034040c943d1084c02440f841188006001200381e004620042d215400700101252500c2169001000d584c1890071403913071000d0034205e04001c90341525001a9900351000055107402d8580700c020741c020582d02001c400d00c00146001c3c0f0781e00380e045040b5480560b4800604c000d0316000d07c0740c80d034190810720940c81442e0b503111070200442100145507140c20000752010485a03416101460580c3c1e0003034010380100318802003141c01c440c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 900718318 1250 900717068 900717073
    0x613080f100b060409180b09030d06060903170d0f021c20120a0e0a150c022e0b190303021002030f01060c0f05010e0c0319050c060c0f100b040e 63
    0x85154003c509a8071940c4204401d41c2d507035400c2040c000208400d8062055880150f0142d01e06052003443d5a940000700d00b41c903440d10301030300014002e018040c094105c1e5840040b59a41c4d42000751070794002d0304000019401c0a0300c80c110864284031500c018028100020320302007241519072603000485100c5404c0300d04070782038031407c440d9071030802081c0d6904940038886a01603980341a0701d5400380c00b502c6d505d403450348144842141045580001c40040211150003005426040d120490340c40400030052110501090008039040c00c0a16502e0320b42c140148002c12246500408603401501500307102c00b5074480e01070b0503c1055818802041c0040d02c0e0741c0198110704199070294140c60041c800c10041c0103c0359505e40802c00501c526101d0990020000c0204d400c9011010340c4920501c91864424040c0500160780d01a2450a4903105a0054014211703d12604103200c404d6208009650880c42010700e83d0300071402c10003440114004a61020945040741000d0205840606000c0f02c600d4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 900719424 1106 900718318 900718331
    0xb03010e0a0c0804021e010e0d0b010305160609060f0c1e060e0d020a12110f0f120c0307062f03180a02100e0613080f10 53
    0x2241d00c210240501d000d0648101c401c10340440300254005072103ca20030800010400c0d0140d090f00604141100403d1080001c4240480181c1228500303030150051042100900c05c48112600a0b080851074609140c1d0244c001c03030040c00340d0170800c800300c1c89280480784030f0fa849a41c0181c00c64500e007101b000c0360761100006180d0180603103640e401c2c0380442400b00e80005591120720001c0d0302821400312140e9902c41d40e2403d03486607504110308010702c01a4400c0900400301d086182c000200708003203000880794200500c028040342a54414400140000c00100031665016131242002800c081b600000b0042940000c82e40c40c400c04004c05560b10210003074009601405c0407880180c03540441081c0c3d0703980d40100c600029081090700742440c6666008412003110b4885c0103003400d00b00841100207002030b540f5944100e125501a00d801d408091050080313108006c0d9500e000d0040 = true := by decide +kernel

theorem cover : BRFrame.Cov 900539568 900719424 := by
  have h0 := BRFrame.cov_init 900539568
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900539568 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 900539568 ≤ n) (h2 : n < 900719424) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
