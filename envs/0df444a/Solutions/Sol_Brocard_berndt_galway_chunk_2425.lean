-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2425
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:40:35.585623+00:00
-- url     : https://prove2.me/submissions/831df506-60f9-4097-8f93-8439c0b26829

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 435971223 ≤ n < 436151079 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 435972473 1250 435971223 435971251
    0x408250302090a0509010606020c18060406030503031f0905041a040206210a0b040c0f140712031517030a05130b0703110115030c210c090e010b0307051008 68
    0x81d5021070740340281a03a4460307045403120184020440d082c007840e0060401071000700802074842e0b000a164000640790380c40b500100d00040740741500d46421100196401400310b0b65641403443c1207410070380504000d07a260861084000c04c01d00810b01030345004640000400402c10840c0940941541015004a91015003004401c42010318001c824505180005490189180040819094448191a440c45145000c5142803255046080c0c025803010500d40720024000000d000c0020b40300340100a442c1010300c600780302103980c1c507401000c0000c009034111180c00e50742d04460440c11888103004001070b0010f00c5400e07841c034070035009811103081c12000c1c900c5803039640c0b11010390342d48264819000200548564083c0034003d0041d0000414001200041d607481c41d116031000d21700e240500040d51908188254000740d000d840c0200b8507070031408001b4030b555549a04030082201c0450040c5650800000345c0d035a203404581c40088505c0507145034001d440c8a401110300c00402481c41d4592451 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 435973723 1250 435972473 435972479
    0xf020c06040320190801051509010e07090b07060f0e070303140c16060c0317060901090b01020102090406060201150e010f06140409020d0c080f071e05071403120705040825 75
    0x20b140c607135103002aa55880d616541d0400e80c4250a4880003440000d45104404c2e80c201c058075842c281d01c7c11920441010348003610355400c2200d00024170f5000e101000c1d4003040302000d0045603070003104d00c014120001c11031a0074030750309251030b0a000c0c4005000302d090141d000c003185146c2c50007000012000420b946145000540c0c001e140d2180d0380010300010700090850b07040503000100300030510500c0ca00f5043c03503c0d007140001e0041c5014020112040d03110148035000703034000d406481c42380d030000f001448802d8a0f80c41c028001c2015103880400009000d00020301c8890aa40980c140d402d6004500001402d180003666080301800f02c8800762841000001454203039031001e004c0060b501c007400710340280c5a02d03004010001c040c1c00009501b88440c203008000b508003400131034540000c00780d40065203001c5000e580c5030040c000c000c1d00d4035907880740d40c0c080014040b001b481440401d007029201031f141d00d50121a640958040d04411ba07004202000040b19a580715580a0060107884c4680c1a2 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 435974973 1250 435973723 435973729
    0x1314030c1905060c16051909090c170a03031b05030a1505031203060103060605120a0c11070603060e090705030a0b0621030a020f1b04110d09120f020c06040320 70
    0x44404901c0c0c440c0e8004180304c0c10000010f030300b200024082180c00c100807c032a10300b07103030800780c030b1307104551425541d030460004003d034202d083d0000f008103444560b030002c1241e070300c0380e15071500102c1200040d1070041517840081605141c50b000400c40d0742c46504542d035041812005201103e07070380310242407010f00060030b03a0301006400003030741040c0040c9071641415000501a102c0c19048801840418400d4140080350300d61480c0d840420761034045030f06410102c0c20340707642000c02103083c401c3c02401e00100b20690950091000c55a8101c1c0d407098907540c106500f601c0308824012160b01d40c200c0750b103c1c40440c0d2900125604900000c00c19105c1c3c1200d43c025081600110482d1007041d000031401a4280341c041c004841c6021580d40640044040740c0200c4010798602d80143c0d01c40c6640702455594042c100055421b0b10b0070030081004103181c5803c111048807403902040d0005841c1012483c0c01c103101068004604002401d0070f07040c2411681c81c0490320280060940c450100e549600c04155 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 435976223 1250 435974973 435974977
    0x4110c0105090d350a060f0815060d08040e18060406060e0604060b04090e0a0f030905090c0f090405060310090b071106090303060f0307080a081314030c190506 70
    0x1200c0400144031038070000030302401d101e044001c0c0c00300406401600c04001045413810b42c1d86284064a42182ea58450f991031008002c280c04c01c02c400859510049003010000030405d8035a10b038140101c0b09c0e03995860400044181600d4003c07e68042440100a24080d1124058009500380d040140c004504a509490b0181c115419500e95440f040100103541070008210f4000b40d0a640034040c003170408171511a81d200f02e1040220541d40e4807854040c120082c8a2907144550189002011200318100184814424000e1600c1050500003085540b940c800845120f448a4500903050426040409c4028400205200d42502403001854030f9403185100b6031a14500c00c3c4400c00290520b544014104801c000d4002c09991207030041c020b1001000054039130180c8200d5443c0c240740140b0022a05000c440c0c0d000990074400e03241a20101701d06040500668078200728076520341e664502c11183d01d0480c12440c581c02d80c01c03280c8041c00a040c541500d014021220409001440d0340710042020307a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 435977473 1250 435976223 435976231
    0x180f020910091802041119110a141b01051303060506040902060307080702060705040515090612010605040303020d0c0b070c0503090d030302030a0e0a08030f0901061a07030e0301060b0904110c0105 86
    0x407540d003c1c0c1c440441c0307450710801c8030806081c0021801c2c4030802c2d0440e43e008403240c072948207014a106501000fa1810071054000079403281005004c4000101002c0d034a002c0300d03110f00c65a048008042c19594400d205a40071650070070541421180307151a09002051f01410940d00f10341c8811001002d81c440c030000f103000c1c822507502d000a5241151000b030900318003404000c100007040204205c556200c800480340c1d201210b600f10303603c91a20307000848900c519412080c90f11488000060b15507040350190040701d0094090320078100a0000c00c0f100c494414078010443c030000004240360724811000351210520410032a882c3c580580c0000e12100180b00003180081d4001042010b946018099588110300041c02844848440c0d43c5620b59070200801c41c1000750410400109142c10940042c1c00418058010018989071200c02a10703035072003000180c000c108418000081418144100d00c110b4050f64029810113014608010203440d030340c0f03514a00d01d6800d00401440703060030b100d40303801 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 435978723 1250 435977473 435977501
    0x30702120a050717031003110f2107050a030b0c0307090305011803030b0a030305030c160b04080406031a1e030f10061706071d0130180f02091009 64
    0xd03000a8504400e0301103281340500f645030030601c28000a0254898540281d9504c4040f200b802c00c4180042034061144122081d400b0381351988505810392480381405004035880c058400c6103441d54207220345170409200c02004c400401c070005e050301107220059900031003503103020144156261101d5007540d6000c100c1a00c03104004012001701a01403040101c0300703400b81d805c000c01501e191009402804010091074031032a00041c00f408000305031100070104d56200da803452050525003010409170f0001d01030003012902d40005400e84d01c02158141012004c02880a20484440b1608440fa0803046071706a401d48244c0c002a88400b10a10640001000d4084002a074901d09244c9080703440f800351114480390404024051001c1c2e00c900780d003220000c00c00390362074055500700048604840c00d016881010b0211000c40b0200900c242544a8110b504801403040e40c0d0b0079060300c2a041840000200200d00d10082c40780182410301c400703a405910809407000e00c40e070f5000780500303071038a00d007032012 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 435979973 1250 435978723 435978727
    0x111070b07180b03220507050d08040f09090b0708040c03020f03070b16170a080402061c020703030515030706020a0b07031b020f10050c07151d01050105041a030303010308030702120a05 81
    0x18150344103440d035174502641c08046140d1342000761682c50710b604440c05918041c0b9064140300051210102c2114000d003030902c400d0202b07a5466201e14020503511500b241c030041101e002c00c2885111300d6080f40101d403c840c1c9400009d19603401c01a281610640d01505030241120000e110b65042d1301a2942c2c0058000000c8643c9103031400010034841600401c5130454144603519400344d02880c615030050303064a0f22075032101c0c42e0000418890002000002090000601c030b000c05030700d40c1102c1e006121030603031603101e882d118040584488640c095007005a018032514804600049801c40e080a0b05040001c1c0500a48002c896905403840d044409680450034458840c40c04215608000d0380c000d001700010309100343c0e00041c501c10b01e20054200140c41c02010b552440c4c0750701026104040c0745204a00ea0078641d01c083c00780009100365803250345404000c4c5441e51502c0c1801080400007400707180703142c0c20366840d01a00d80000c1e09a0046218041d1010290400b54006115a410319103d00d5 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 435981223 1250 435979973 435979981
    0xa050c090106021c030903050702090c120a0b01050a08060d0b01060918020f07150b10090509010e070203270607030804052a1002011e14090111070b07180b03 69
    0x200c201401a8000002c560000c0032288140c40c684408010004040c580819020003c2c02c048039180250140a036115100d00148210041d071940101005900300302007030070f156507001c405c0c01140c010100c1c0a0108108004a01c522441011441c0e40020001c00036402401c6584030140b8000c400d0700704a01144038008140120340146880304003046c900d0304150b02d84500e104c4481541d0140030402000d00c0703e4010740404460840c3c1040407210300c0903040d082c0315000ca03240200040d080d44246170140012200104419810f0400e29101383e04a800a51400071800046e0a18800b107514a10700c03001000080ca02d0b954600c00141034881c000c0d580d8100c282010308006040070070030a40d204540c005405aa400d243c1c0d490013401c01c0800499440c16400001c401c164050031501d2000b13444130030118101c60400c41a5030000c2170030291900c0c9002c8681d2000342c018201c0c0c41030f4400b04044401400300f5400207460511a50784900980b8201000c808a00406400d8090980010400d44400300c100 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 435982473 1250 435981223 435981229
    0x201050f0906010f030b0402180a1b0c020d08210a09140d20011503050a0c0b030c0d09080c1005070f050a080c0d02040512010603060605010309051b01020c030a050c 72
    0x2403504080074501a041d194504010020701e0070180c440245132014080c001815583c1c0c0120b203822100b00090361080a141001d6900010800700c00301c1342110301071005218441d44611002001c251b40a0801d80081c50992100161604549840c078800a003118440210385109942580103940054000c9000f64481c5001d080d945a10800350307071158050441c001c03e407980501803140d01c4008240000599890009280c058540c0e0300e00d40e0400b0240031000400c1010003e004a50180258000c20782c10340c0fa64040d00092109031082d0851400c240480c4111042507813060f1030f01803040220f145071890128483e130800c08404054000103a4907004c00103540c0d0003495501c401900f5207080ca1412112207006041c10401406c01c031803008010400016004480e4100c8018110007044801c1e04420400b00c0c2c0e010702200e000c00c450752424031500103200d5009000d4080324582c40b0010709043c60070701100c5520480110045030440c440c400b106140d6850a000c91441c460143d000742200309250703030034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 435983723 1250 435982473 435982501
    0x615081614010c030e03011805071701060b03040813050d21021f020309070e0f071404120b07030914030a0e090c0306010c08040f0f0801050a151503020712020105 71
    0x48040d0418400210107026a8860301860a4540c1401c103040105102e001190041100d5005043c0d00e5450380a0041840310005100d0215141031884081186002c00614242c4030705101d404003074001880840c000039012070240560709002c05006580c84e5907240002c030318001280b801e030b524800750f1603200c4440050960141452582e800103007000c4460b0030301100900c1003106040409640031001c1781d00008180201001400080c0b40d0b400d0380c0c2080d149261200c502902d030038010a404040061105040201f6581151801c112400d0081e00f030b520b5504039400010452410150f5400c00b0200241c0d4440890820f5802c49008685410141c0b201500724601e04000511401071142000402500282102e030710600a20300710fa009441864030b0180c0d801250002e81040d44590b00100d0140e42080b0000200d400510003409541c480a0155044400c0306049101d2021109001d0000c1c04030420f49400310043d03442c0051409100d62100901c0b0003150140c000180d44800902050680c6540 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 435984973 1250 435983723 435983729
    0x21216120c08060409050a0204050a0e0706090305060a05071e02030d0c05040e04080a050c1902150c0d0f02030c100204080c090903070620070b0403020d0504080601050d06150816 78
    0x100071004000310080c150000040200b44a5511054503c007005428002408005c1c0d0140060019080401c03034031000e05281c0120407010321400d0800101b191081400b20226500000900789a8603115030300400f41500501d400300740503031500452040b904c980c6002d000c5209581c05507032580710203940d00c030580b90389425030310803c4000d07c801d00903900a158034a801540c00300707900d903854034540003d0311b00f801518030010040c0982c00a1082c0300d2034402c0003c1816100301c421200b2100045a444030b00e018200d40c10855512510318020018042d4820100b94105ca0049074140030400c00d00c0d0389043e5002d80c44140107900850200400c0904000003105041c007214030380301c00e1501c814001d03524012040301400c0301d600d6080c00200d41d4086a07029010225002881e0fa0784c140740e06260714038075802c1e034086005100c0c070001e1500462103103050340d00791903410b800b500860740b0703107000c104c400b814501054480503a11f544454045015111120080480002801c900d10f2495100707402481154 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 435986223 1250 435984973 435985007
    0x4060509070c1221021b06011d0a0513150b0a06050720011413090905011506020102031e04150915062702070f0c090207022b15021216 59
    0x1000021081206890380440364078031301001622200250321043d84480f1040040019000b008004124a40041e610451030100c0313082c0e807041030300e8070f401e801d088550403a1000034070142c0240f0400012803500c0b002d455031a03a98004101c040b4940300007006480356034829408540002144001c03c0a1440307c0030507070301d1840626440828040001e03281301100144c0408807070b0b0006448800100f4002e44070054030344080b08100903a09807816a0080806401480c00c0784100103001590324814021603218102c0b81103980d00d1400142c042c0418038101400803203490b001041007825510b110f00ca541e1055001d400c0f00d281040d0111144001c440d0240c000e00070030700c1561690681c2c1d0345504984d450724400c50034010b83e240300c503042850300c00808a030010410082250b00041d11156500034254190088405084452181d50800a040e040c0d40015000500c049440c4010804502028000c500d00c0440540340c01030045000140071340495824041507080303c40100b07600e60249125060b01640 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 435987473 1250 435986223 435986237
    0x11b081302010806150c010204090f050f010513111b03041d091c11010c02280215031306050709030c0510021b0102070b19081315050604060509070c12 66
    0x9030700001c10600c001032409014503543c4260b42125a00c4004840038150954001c54540383c0f907070ba64001074903603100f079014481c0c1041d0101e81c6c0350200844690403650001c0441c500d1401190b03104015004070b100c1d107410114144a0601c0c1701c035451413030304820308041002d95a1903007003800e809403445081ca410180c59107104204000c2420000760804840080913000451290005040794496000d0482d1004d075400c011540401940000d000c40782942d007142c2c03000d00b580f4000806001c001aa00c0301075400b0561801060b45006218011500801e0001c40c03114034a403252200c1c0c065480a0340c201000481021f000c1003401401ca1072807003d40000c590288007034400307240007940d076680c00b90b060b9040c0320324081e030881c4d90b802044000018052010919143c00030038040301c500c040021000c001145603440001d00c00340c444035206440a0307001c6403003468510817509920081200900e040d400030380d070712004500b603999841e6440c8141c0140c0d8502e044400180303014401c80f840410908180004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 435988723 1250 435987473 435987511
    0x803030408090d0f21030605030111120703021b2d0a0605090f100b040501050f01020a12030b130c2c130f06060908010e06070f08060a0503011b08 64
    0x49074084800b208400c54501100300107a0401d80c0e42e000a81d40001c0911701c4070b1142488a030440c0d007040d1404030790780e1401c01c0510b580388145401c0e203024250f02c212006080010704006403860044681007034451400504054503083c91460007008485644200d45c061b0030b015070411000800c2c040000603001e0100481c5002c0107007140d6841d4074203801000c030740d00c0300c00040300110100a0940015a90005c8076044500d4032002c1000740792403500030b0b000e1824000041030b0343c101804600360110043e40244007110f601d859001381020384541100406803516451000ba6984082c0e0500c805180c5100054100448030302915481d807040300c10900b0f4201e040f02c0a08a40040c202005030030003a5159600d0150f9402000300802c0d890921440440c0b500303030302281c0705074402c2c400d8080c0d4491000810030340b40d00b13040450380c0714411034200c000245040d50303041ea030501c9510306c1a00458041d0100e13580e01e8413240004c0c02c0d03400200000104080d5040110191a0f0280c0180d800c029010300500f02210 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 435989973 1250 435988723 435988733
    0xc140c060d0c020c030d09051c17030a09020d0305041503050c09120f0a050604020a08011e11070209090102030a061d01050103020a1205280b09150f0d06020904050108030304 76
    0xc1c419150511540c0c0d1002030070a034000d224218007207034020150748100b90400d50140c4015042c0c0501400307850844814107888400802503800680c215182101d05151421039001d0303580020a010300054840d0100030046e00c0c5d1655281805109031103541d00c0d141030021402c130701e21030b10200404141c20032044c004003005280444040c15001e441140e040c004000c4494a80407058800d640c0c0c62080b000604244840414003034001c51084819010f202c0e542c0d11020b081c0e0307500101c060100004040d8000e507402c001d41c002017089420403103007400c0601c23a800080a114003103401d050265000020000041e0091280c500035104596003640720070a10a041c00382000b050059605143d800143e21070703482d008680442034110004814480c40ca0200f446034007080307512219203205403070340d100c80418084038021855201070281000c1e0080d40c1c0c840f900c41542c101071b007a00e90825a580c162020949810745441d200d01e000302d201695a24801d000d00088460591084885820234014840019 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 435991223 1250 435989973 435989977
    0x30406170f071d0301150b0403050d0203121515070606060305100605090f061303050304030303050c04080a110111070b0c10050105090109050a02120f07030e0f0a080c030c01020a0c140c06 82
    0x305000403901c0c02043e0340d001181c0184140003e07100740c1d102101d000169410514010019640300d0420350b10302504c82c480507a81e81c000d80c202010400c003454001303050260349480061039940001e050640604041544038030590060b80156010f81d201c20b0103021158150082c55000a42104270094651070001d000b4014021055a80d01c90b4014944040c0599689c00a40d80c0702e5509006c15500b655991030041d54a84c460310045000c01d003031034005271110022000362000c45801070050050300c481c0c0d5540050090080580394107010212102c1400701600f0030094001d402411005540c2d17601d10152240703420a1010300c0f82c42c0354248030040c0000d48650401e03504584e42103002241e940c4400600300b01a005090312011610802c0d020060360381124812140214810303282004442840303103516480714032540b15100704ea403112004400243ea800020142d5841c05400c1c2c034182500d03413045900707a03408440210300041e4030f40b005c00c06000070a602e1200009103d0024900441040c010460314 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 435992473 1250 435991223 435991247
    0xb03070210051506130e0f012102030a0506090706080f090d080405030405150d0e0609070b090402070f050304051306120303020d140a0501140f03100b01090305030406170f07 76
    0x4640740c80c04034020f0541e4964040150000411240d2204902000d107110001c0500ca4a00d104144d0008103d1041d284807995050b600d1092080601c040054001090420010001c0340c15100cac4a040c100842d1090042d00e002e246d0034000351a441e850808014840500a81030914810b030141c1071003124500003030705100f203c405003842007c81d41d4508001d410740c0541c1d0700003074004104a0030300c540007d4400c010301c4409941c802c02c0000000341c2c03681581d20b000403500500242e01500c0c00f4001c0301c00c20740290103804001800075190918a50701e03000803002c00c0f0320440310f9520205040c46980f0340b03400030015000c2e42800130468030349001c0a54086650743c0b2806024103078000782558220748c098001c842e00710300d101c18180107428090918001402d0920400818481100601c3d5151400340b43d01da1644030020f00501014210307078a440000c02642e6645810b1120074000040010400c1c80540020162a129081050510080c41c03000d284000d2601d235050071a042000300f0240c120320303c9050 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 435993723 1250 435992473 435992503
    0xb03070e06010504031403040e090c1e04091b08010506060703140a030207061a040c0306120206031510020604030906030b06030406150803040308180301051e04171207090b030702 78
    0x392541c1c001039642d40b0542d000901200400d071580908640000014000c480d10020043c000765240b2040740d0301ca400800403e035000000c6094681c203162007960b1180c003c0c10040c00050041d01980e01e0014049941c6131484002c4030400c1d0400044000b0310800380c0c48502655194504825594000d0065070045c240b448886030105042003124840e6064030b07401540510308002d0481801d120302525056101c03040d1040341401018641c2030311030f0254500301d40c402c20507420b040341c0e5a401c220807a0002440701c2d08045000a40009950710b44201c0c00c14500a0f170003900440c142810000c2c4480006c1e000581407500744420b01c1020303158282200d61080c0c22600000c1c00004104514020031159444121544008280401400101c030028034400508891050342070a01405143c2a0b543c200d42d0110120245108440c10700d0344022560750045c4212452020480350703044c4200e140c0c01815030480d1417200c200c1000b0003660048141d07009444509070441c1585004800255035a04921107904 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 435994973 1250 435993723 435993749
    0xb0c011e02120406201810091d191b08010b0301120f0f0c061125060c0c0302060a0c060c080c0f1812010212100305030a030b03030d0e060109060503010b0307 69
    0x10354801540301c805c240107648045070780d480610115840311544401210722030318801d008207040070b001c0c1c40341c042110280800f8000508210b5410303280028002c000004120008809c140d0b00c7c802845604181c241544080b076110000410080c15035005070088e030300c2c1000c2040103029603a03605030001e180b00c1d0301541c0700b0304028080c80e105101c0008070000602c41008040c001c80c24a0300030f0301007a09910340e0022505041e00802030410940c0744420218000807582c4401d118587c80752401c0b12645015104081c03107a6540e0f40440c3d071a40c810030302100003c0450b03802000b00100c600921000e00c40d24500f4040d80c1c00c01181d803552602c245201091136000000b01500d1121900e1045001000014040c08208a046003014003030f5010502d511f0710091061300080075641d500e100d42041da60040c000b54200710010809a0051001200c010351502c000d100c10720212a060091b244051688800380a19524020b02c0720182c1c1c1440c2c200c24420f90402c05070381c030a51400500e444c115032164090300 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 435996223 1250 435994973 435994991
    0x6122202030c061803010e0606030d0309020d0b100b0d050109060b030f1503100204180525030525200304050d06090201170a020a0206070f08041b0b0c011e02120406 72
    0x13909031103016a4594055003007000b1440c2c50781012607000d1184c0002c2d400e50f814030362200021030441c0d1107001c00075031080803030924102180700f8808060340140361010f407110981e01c980c0c0c0304074117403c030b644988400c54031100180000d070784900419005242e203a100d94150f0410340207281480714020001c0d03141e40010207603404581c2d0100100c050144e003030402155242e0300c039848030004072024202e48208505040100701d15107601080b20403007042280440f03d83e000c4480045000c1c00f0082c0054a820300d100e03441d0005030404c008801d07000842c40c1c0342c2d8011110f1085007010081170030303817101c1401d400c1440200320702c0d140c10899a204540c801000a0398903035510068840e1558001c0e019170301c0406ea810003101092550090000380002c0c0c08690155840c0c0004407030480c200343d054000104190003080004400c0e01c49480c001580e440880001601c44031500300c250002181c00106a4513480300940c2094003034115521002210300030f620780b074030f180c003850300c6010044d01c0105200c0e600c0d1080 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 435997473 1250 435996223 435996247
    0x609120c0b070e0a051503060f06040303050d0e0312070c02120610060e030f06011e051005070311011e0c03060e01080307030c030c02041109010e0414160e06122202030c06 75
    0x134025084c01400d0388002c046070301181d0065041210300600a03041d02e4040344251034801d0940d400c030b075030603a40c003441c02d21403c412101526000008000d00e1206111703c1180310500440c0c0b40c030820143d0749100500c10a4010071500382147c042c1010150052010b0114107680000c009090f25041e0a001504998900100f49440340c0803842641d00d002d80300001c15140b00900f6040d040005041040344900d13100c504104941020405601c0410030400189000134061f49012003540c0f0b03000d00018055440050180c3e411110404c0581c04554407200c1240441d00b5104040240c5401d110f44000b56040c90a0156240704000000c3e0911404254641c205032140d40d031409080d90180041c0300340c240c0542c0001c01c0d90000714185021034103020b005807403030030706215450b040c8241d1110400b46031521110031000401300c01200041144019200806403620b03402040e0f0138100c0c07007281c81c036413804129191014030940c12410360031110200540260354005203900c00300c001100c0c805d50b242040045 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 435998723 1250 435997473 435997489
    0x30c09160507170c0706021507022d0703060c021501050a030602030c1e0403030f020613080a050c0105040f02040e0316030f0e03010e0109020a0b070503030a0207031b0609120c0b070e 80
    0x124101c0e81d40011307040801d032802140302021a0000c0c0c003120300664020070b038112081002c44d0b030100141e0040030642c01070034522010155140603c00f11041c0d140c00405003506003500c5ea0800d8600c6920380c900004c0144e810040110007941c055a21111941070100161092145200c041c0a0640100118413030225a10444086039042c01640644150240210040ea00548030580206182d4895420303028000f0401354822070314032000c403a0b194056a01e805031908009480c2c0c040050900058403240d80900c203041c09075000d4058904c1c40c0045104100c2aa5811043d804c0c4541003400441c150301404400c1012040d41410440160188524102c804440315408135078590308043c140e03e07080c64103520007104c85009030b8144400c03549404034039810703109501d0004c019601c1040091002c9030150301070300905200f440c0030700c140f142c1c0c80a90160014000800e40b005955108040200705056102e8035100445081c20840b0781c3c07007600c1e14540307248001c0680042c42303c40c00c68400c507903507444c2d2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 435999973 1250 435998723 435998753
    0x150717090909071a04140d060b0d030908010614031e12030f040b07020303090703140a0b1914040b0604090c09050703060614040b0702010513051e030c09160507 70
    0x4900951864454002c03555406184501c601c098500b0224981c000701e040201c0301a142d600784802c078031411031014085c0984c003010f004d03030750141e4941c03444129a41d02d40d0400d0445000c2d030380748240c040c01e04035a9400c45403d9804616402c00d45044012142c50116110311403140111480002c52100d0428909140300c03442d0b40c3d000090b0020400c02c032040c07481c64582c0a9409585101001e50310107000f43e130342e4802a12961155403180d00104005001c4588118004000c60103660840380c25580c0d00d8242a42030351000307014144144171002070140c0380b06030520b5260114950b4040e0074161a01601d400b40540207a0141d51651250014480d070800d043c0d0007020b828104100c0340c03a008100800074160360045074000355a01e844403e04014280c16601541d000720b6030705207445c981d03600542d40c45d8000d88401284030000c0b0000925580c5040c40c8100180b80e80751108040c0c1e40e030000305403c03c0900031115100d04070050a008421407441c81d81134030410075040c400e6460003103003014003014000d03017 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 436001223 1250 435999973 435999979
    0x61110090305070302100c080c180a03030f12060303050306040221040501020c210409240b072f04050c1201080f06071706060904230f0615071709 64
    0x229080c0c10103a2081c0203043d00b0307019a0070780e4041104100d6110641d8000104080010f1065010914044c090b01c010958414540305030000c90b040c190115200041d03592042d40400c200040b401099078022400c0d031042001000100003041c20342e50040d0082c00007800f03090282d50701084401203551628450041f00310301c02d41710400c614080c50032038041d500c40c0022030300e240039404e0340300001c0091000e114a08100549000c0c02d041c20144841e009158030785e144a030013120207100440252a4540030005400c503065800c0c0d6980301d500301903200c607401404545150302c10205410784064120039a641c1c20300c1c12070300800e290b01d4990300c03003081d4003072080401080c0c80503900004518a000420b1070920350810300b075501e5540c80b1807055030303444040c0034003a2000c402c0c0b00005556161090041020313400c0107100003280c1007503254494141c03030780d6800040031030100c0341400303412580c0e44000f95018404551010200c1a01c0005210742d02414030b005020310b020070040030031400003100703480a0303003800707 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 436002473 1250 436001223 436001231
    0x13080c010906060f0b09030604060203070219030c11060a0203070b040203120d0b1302030402061b12190206180703021e0d0b01061d01080103020108090708030c01092a061110 76
    0x2418030b1002002548540c0c6603c189442c00010b035155010300351a101c04000b0003821b696a41c40d00da00000e540000c052404602130b80c12859a40807408102c00d001c80d00070756a80344002154600081580440c0e50300c80e2180c1420300c424071465500008960360180c0c480031300113090b255480803d103007116014000c00114800f00700c0c0c0040f1034041d8410451080c085a08810f42d03804030000c0740491005984c00b80d0400703010066030318507090303404030100c051410800301c078407030881c04410088980124810048590001d14007076a1356904104580d00155100c5100319032160000d48255150003920000340501145102ea8962498482c94484030300005000480c2e256181d2501c049002002d01407103000c44c030400030300021550442c600c801c00290686070b103108c42e402d64005480c07148000300056036600c100e10f40406c100d2000c0c0701500d40000f0900000c03401018620300745030005ea4400c0208151410047d04450440074618403204a900c0360401141c180e44c030b1600c090500c4003078a40d200c000350030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 436003723 1250 436002473 436002491
    0x702120304083f3409091e2a030e0307170a0f0e0d0b15040608011a0102030f03010918050d0203040e01120c140604031a0603010e030c030313080c01 65
    0x201c0382c4140011401d46102c08503981d654111a0126000c007002c0c0c051418421010004001d04d140c91081c01041c90f01345583c503596140c9040c0c0c03e880c0d50100b800202080260050241501030140d100d2503041c0c0d14000101400b050f4003002d0001c105248401013649904644104807814403c6503641034104600303014002c10f01c0d004119650004180800154040041f4080e080c845c58000440300c100409140c00d01601d074461080c86100648204a01984e000404155940c0d03485000000c180c1c0c2000031804bc134041405001142076211002d0541d0030410610419140e040c08480c151082301e180001c2080c00c50360901d4940c04901d0300280a07206c1d003441032541c503400001800c22241d45490701101a80c03209203a070301030079050500030701c5891401028445201c0c002803041d001c090240405040681d2030303d41440d64485a81c0801213050888140560382c1000c1c021000c209100070011071510180002580d602d200c000c040c25900d000b844000c2040003001001ca800f41030005000b440300800e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 436004973 1250 436003723 436003807
    0x2030312010806090604030c20090a0f0b010c02090103060e0a020d0b160c020d020907180306020405091f0e1b030a020d0c0801080c0d05030f0a17070212030408 70
    0x100a0040300583d11078000041e401c840b0024040d403007690316a50780541850590f85611500d0300b8010000101c4d0a40726000c0d8281e190349050318410907156001041c504284c0391030a0888401c9200c40f410000c520807520056220900c18904403580b0000000702c1d08024042031b400d0800b8a44000d601c8400c25030391300188402a40001d000b86101c0300840d025501c20307007050365400c0300c6020087d0000714803000e5401501c5c1805103107030722401509140d000c455001e42c0481c0a14055001101c4240e0701107801d00c01410210441c59000c20b4840440320404140d1041f044c01228a100340740452300483d002908443c0c18800c079001c05042c101d81c95449041640400b4042e401c02114a1400d62405c9815110284100d040383c0c100d541350b002420b400003960003808040848031400b5281343c80100001c4181800000c01041450036940c0ca416610fa004002c1c03195038640903096008560180034400c1d01240f818007220703001035000b51590390f40c11076092a460960031284a070f95543d0010f00640c00804 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 436006223 1250 436004973 436005007
    0x61e1b07030f17040f08090a03080d2009150c011401060c1a0c09040207020a030503030a0501050a080c010f080601020f0a11040c210c02160612060504020306150313020303 75
    0xb03841d8a5410507200003280d0f40c0164982110701504980360300040d0404600554010020300b00007412000c441601d98952040c55480441e00980075640c800440c078070703040e454102c0c0462900c0c003414645054200700c00504008807010701d00d0001d03400001c0140b080b24007544100032400056441d006150b0395504082c100e0540080282c4a900c1010320b0b11080d0034001c1c03040ba00c940c0c10b07032024074105181c0e002840001e402c58201207800641600c00400440c42c104060340c480c91010001007441d40c14403017800344d111038542c03000a5680c810314032030071507030b8206d0049100c0c24854034081e0500d94902004174031300b501180c10000340b409002d23800750501c07140ea11480e141580654052180001c0240300b110380c40d60384400e0b5000c900301c0d0030300811614429006148807003010b104442440c000382006490851159202d03d02049951400b50034016079070140500524040303500b181980341503004904600c070121255110440000000380b0309030921544081440e401404603602d5003100c1e20400409 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 436007473 1250 436006223 436006247
    0x506160f060b0418051b0307051f0306050d030c020402071104050403030b0f0303040f0e040302071508091509030738180105040507120606090c120e061e1b0703 70
    0x3540c04d000c544c05030342d580c2580c0b0b050520760100080604400b0705400b44409582d002c80759506004a076000649540d41e8000398684046908011030303c114204030103401c03100030781c0c0500c0c0038120062845010a80095941440075015207002da6100400e00d0040640d03030400c886150700625000034071041c560315500c103500c0d01c1c106960140440304c2800405541c1d000380c1c03082d0641e2200700c0005204110501a440307820500c0ba00449034079a4540e00700c403019007802607514000038400c8003001414102007205402803124042c03880c0d0242801c5514540360300c180c450192140c01c60000d6458200204011012440c03481d120aa20019120041800184094400460b44000c40144150300c030018400c031400303a0f0340040240369082c5071800300103005c07100e403005541c460350352030340014041c8850164507845405503840700d00d4116003403800012542c0558240f0b81e01c0c3c2c0300c40200010a4221044140f55401c01d0001103a0740c0d0f241c1810781e6580715029510074070b846010410504040d045904240d40d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 436008723 1250 436007473 436007479
    0xd0207110f06090a230a03050d091d0a02031317070317010b071709040507170702071401140d090b0108070602060c0304080d180302160e0108070506160f060b 69
    0x701c505003004554040c001d10f45501c0070031010100450720004241800e1480c655240580c03a50b404030010300400340302e5100751105e070009a600112998050001005040c0112640341031a09206611000070740c0284800104d1b6400004a052000c4040c114020550b202c1100131603007007084000680c40d0840e903000c41c0461904400c1040c032140040301d81c1d05072811400f101c4c0c10540140c0301c01c0e21165501c2c400a501d143c04100265450f103880c09028404c1c14541c40c3c1414207250310850030314034540200307400115000180c082c4040003c13504800340c0c51a0920380111141e1a0494031160f0b2f2050040c0b005485250a14001c10042c3d0501114101c41c0101c00361020a03640c0d18003a03886810880310540d0b954010000140001c2e5500c016005140d106040081c144003c406010580c003640003042c0c0241c1d00481204c808441c20040c6034000c1d104c0d00301c03140d1655241c1510130b0340d1038805020341ca100e030001003484464295201c03580600c16030407480c08071140405080c1000240449508070340 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 436009973 1250 436008723 436008739
    0x121f0c230d061212320a0e011e081f080a05010c05040f0b07080417100f0c021e030913090507060903110909100903051324140d020711 59
    0x54407080314040f0ba2001900724210702070360349411000312a064006076000c850740202e95040c49111102c2d4455004440c065980f03640d45e01120342010b0200355070b007a5a0390400141c044030b207080d03c082d00800c0d03921101a045c660060380f1440500a80300010420710440c1100416002403102e500041240401c1c0c0508020000281d1000007104e981c821130140d801001e6820340d0402c00d6011000040c026280981c0d00300e8201034030f0b80440001c81180d1801200d03140d10100c4405030704865071059003100601004100680c01004030041c2d1140180c140d4503c45241052810f00100c030180b084504400005000a0380300d421031082d4001800c030030310305550b28810304034080340081c01145080c040d00d8001c6006a280003100c0c00308030016200400c240f42d180200c400c00300c46170301d00e406a608071a01c00d44807503880e00c500156450803201540c1c0000c051035400321480d500c0ca00740309544c40084409280c0491441e0780002241c00c1481002409101588001080010302510040c01c0e2186181200c1d440 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 436011223 1250 436009973 436009979
    0x30911060a02250e07050c190305031b0405010f120b0306040302100f141306060e07110f07050f090a09080f0406182303011e0b121f0c230d06 62
    0x24004068074000d26014104c5040890416801400a0503c01d11a50111610b06407016050358950900041c100c010860110074004d030752484100e140154048078070758a0038103103004002480702c43d40307401c44014000b1040d140104034425400404174000054119030b06801c6c10b241c02540c81c0710f44640704800e1840d0104c0701d801401d060103800034458080307454100715202e01c1e8070350503610b1070342e1400c80b003a03a581c00d0006070303c81502d00c0ca00c1c420030380c0c0d407501f08020020401d001c0c02c003ca04005215140c01c03120050020743c3c0c50380081701d1083c2060b207401c030320303555216103c4005000f8000060403035000400d41250044440f0020400d032403159407444450507007055070b100c039010700d07004007c000c880f01d01d207411501203000c0d4500c1a640d0001e001050300c201048900764900f40c54502c2c070b5941c1c2c1e00c03090481e6860500510300400000c902c1d0081006124035100303000e05102c405142c2039982e4648400e00c803054480c412a0580800d0301c120b54180380b000840c60021940b02c0c1d4210400780b81011000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 436012473 1250 436011223 436011283
    0x70f0906020a0b0a1b020c01180b03010306150801140411041b030c05090a1401080603030a2304090e060108061501090b030709080703050a030e090c0a030911060a02 72
    0x800300c0d10190001c2c0b010750709590300c007262500020540c001c0e0903a14265008408802c8840080080700754000e80200a00a000101800c0f001c041814004802d0601048100c8200080703030b0440f5000000042c40d500c0454407401c20090f2580082000d40c2440e5600e1403010303109d2030483c06544580220919280100306120548090b01d01c40501120509103114560303000b6004421549454a01145040c5804001900381009604402610f902d11031400d0b8195030003d0182c0d821580860046040c24000b410041000741002042c100c0d500904902c0844907084e10143c5020340400e4000b400740340da0007101540d64010034420701c3d6061080340d020910300d400c2e02401035000c070701c181d640049132400c020307031180d19a00281100c8200424200c00061501c01842080c000e5442000a00303007140807410001d25010b02001814407130702181044c003c44d41d2003041104c40610132070502243d0102a0f04001101402c103080003500008000b0301d4131441a40403840d45842020b46a08059080c05100302c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 436013723 1250 436012473 436012487
    0x50408070609020103021324090e01140307090f0218040e0c010503061c080d0608031c33030c081b0d11030d1707020a050c130f09030206070f 62
    0x500204000c0140c4000316600d60403059140c0d0060601510b440104d0503864920185640000c005a544952001c043c0c800080c0c43c00e040c600c98a021083d050400b0b030449080c500c1803007045042481c007090403c0c1034405100050040c004408201b20544e80c6001e10380280d07014002d402105002c50000300d07030901d4903110702e03000311030800d00400c402c4000c0801590a035101401040e40082580c0f400c14103400304800850f05036109544240c0c80d040c2e20300401084d54103941291a13a90003e100c40c1c00140301c0304810030100d008031000410f404402c505c102c0b040c1582d5000c059140e210b40d0000512000c400210501124481c0704030300800f03556001015141c00714600041c2c140928030040c01c40d00d01e82855441036450060f44903807401c64040c80000e28017404042e10030082400e140700070324408a4240a00d9004e803083c00588140d04040e034807070f078440402c03420240c4a0f480070a204402e0ba05164804491042c1d02d2000b0042040f150030003070350703e020440d100030002d402d00f030001c8402c0f881014 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 436014973 1250 436013723 436013731
    0x1b0c141f020622020d06090b01091103070c150903050a120204050d02090402130207030201151d01030b1504060e0103060b01050c07151e2f1009030207080601141305 72
    0x40a030120f0388440e540703007220308055025000c80740c8107116090f0259840c0312052402c0751144400041d030780580d1501407440c80c0160b0118002c0c40c034210403100140300c5401213030b60140092170405064205482d00e11034203035601b020034101c3c03403510000c1d01c02c05030400c00030319224007981c886500e0040b005210740182c2c82036005d10390b0420030300b840c0d10b0010300708030b0122070b0480d20040072a03d088800d11105405c980003000c0c10b44c01070313450740016641c5508504401019008034620f106007070310b5072007035082042018880181344c030100b4000252403480001c142454403000034421b014030340e5101c210860340b6600f80002e4940600d88198020158014002c4401c0640464041c0511034034011030307001400c20b0102c0c1802032148040e000391a43c00605e0b544d80ca03c0707543d40c44e26107400d500c4d052424030701d00e4121002c41c0c00540001c4100c0c1107100c00a1275040f54019480d005c5500d0302145012401d104440d4801e10071442071100102c0e0340901c07502c018501312b0080d105040110107081504e02a55030030b071 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 436016223 1250 436014973 436014977
    0x90504060f050312131809061803080624040905180a0309030809060918040c05010201020c21070b0117060604060b040605181003020a08090318011b0c141f 68
    0x3c0d025105148030784d0045c040e1120581074080c1c00d150307a402d55641c2d0090b00340140340c01e1944e855260040017060f10455000d10819036900c1c0450340659405000c070f03403014029622401d201c3e140c66450128281c0c5000700c40300c410044030b85407980d41b44d10b0030281c401a100c007144000a2600c030500340b400003c1c101d482c15055a654801d403450741c0c9500326142d1055280f150080820401100b0685503d1040b01d6002065410000d603890b00d0704007040381c0c0480d500a54110f9004120560040e0301c001001d000c08500c00280600310209034928444d0351194520041100c5c0ca1a00009621454051030701d40b00107070034040d207150780d5032a81040101d4410f409504182c04061005024040c07040000c0c01107508000f001c0fa00c2415500f0020f103030301511681c01c1c1c1c002900056105a095401600990420044001036040241c0506104224294040c0d008c4c10400c0050000c1100d0100910450741580c00c0034400e94455140e01e0030000aa0351100c0b000d01981c00e142100f040d90542168002139205c140d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 436017473 1250 436016223 436016233
    0xe13090809060f040e04080d150f050f010201060504140702060c090607030305060d051c0f05030f060405040f0c030f03111c0e010c08030f0a14130303051e07090504060f0503 76
    0x1800402074250050060f100e181d20041c80003046209003940d140780a03500075902c075503c0d003031081c48000c25913071350000d010b440c01d140c0d0800300002c120201e030078001c0e1501201c00700595002d090040340140ba80354010341c0e0003070503c0c03248210040003c0000d401160725500b5100c10b075583e4120040e15224900d45250802420080b00010078469404160050740003003079090703502015200e05240260300c243c0c0e508050500c61108901c503402458035a09541503042c201d045180c03010007841e500d0801401d40b40180d85070000682041705c1042c003140382e19440542c2c00131040c1c4900f0000503400041c0000c80c0810348400c0880e20b003080c001051405a01d0071074002964410752031084441c5210000307001d040c0071410035003600240d44000a14841d640001051205152580c2c1400a691543c0200b040d8800e548051020080c0d5940380150900d42504000c9090703101c90940700060001c10303540b60086030742e43e000d1103d0f09034048481c2040710710454090122a8a80e100d00080600754415680d0650003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 436018723 1250 436017473 436017487
    0xb070516110a080f060f0a0b01021b04060b0f0904050a09110f120703060e2104061803020901090207050f06150d02190b0c0f03070c051903050d0e130908 67
    0x15038600e2000030101400019007260764004284c54540744010141c8180c02510410280c621030488590b40040a01420b00080841400207515140c1c01c075100e40e24041a00002c0d0b12a4417103800580081c1001044166a10400028031240781c0003800c04a203e1400d0401142c0d0140013405034180154200c031401c500a40309104000c50700030340007103c40e04010104610a180081404404011401410003049104c41510041e0401c1d240e110205040c6102182c0564013098450681d000d88805003441603503500b56050160308a1041c2c3d04c02075100e0b0718003001141c0c1c004950054000c03144a0401c45042c80400c1000076154901161a6040c42604200c0040145007440818083d240050040009420b00204aa14415807904a203c0007c800143e41030350640c10049038171842112005103007401e1255440003154105403007558802c49108030503001c3d40e00c1009078003009503030003000c451070b80309001c0015003018104101d1921030460801030348401c1d2602d0148091031580007900c0b07450120 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 436019973 1250 436018723 436018733
    0xd0801050f090a180602160c0b0304030c0b0c16111903050c010e01181d0f07050a08070e300f0715020f01060e06210c1c0b0f040b070516 60
    0x190440d41c0d04c19040744c808020300444c1c4148024040380c0604820104400c195081041c2d480b2203d51140310203100802c200404a03074403610011403a5840102c000311741e140c41040c40c0840c0100e115484803410603400c0c80c8200013220a070710380c10001c00d8a040711034001c2410141c000c5100da200103403441d000200401a190310079041c4980704081410022020130ba0700100d00341c070048a4100b058407001c900d013041d001100140c4080d40c8000070407200642407401010051290050310410014041c00e2000300300824025075501c0c14640c406040181032602d280c880a20f01000c80031441030140c5440e481c070b03071a640e0100304c3d1260402d400c4001c041d00c80c68201010290060172041400314018483c00000000342805124004c02360910b02500c00c1c203010f820040d08402c0e041ca016400c906000300f40c441202c1c0454a0b0240040448003106003406911440c1d140c00d08111000f4243c075040c008114403109111180750203a4007448841c20b4503507a0280030354843c81514030000e42803009160b0310700010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 436021223 1250 436019973 436019981
    0x30c1805190909110103060b0319110d411b0433050c060414030c100609060905010803070602030a060f090c080604180b0907050a06020d0801050f090a 66
    0xc4041e00100074840d549026003030882e01104000c07079411075900801c0241c2e603070602601010b401c03910020303841d60411440014880951907540d610312500c40c012200580301800558003104640c1c2418810150703c484107910420f0052062656803d00c20001108400e02114402c003039900640c2006003919009600c8500d02c07410042154a00e00c1004040342e80e10035094001d03000303051100c03000d800f0300300c901154682c44401400d03201082018440801c1e00c034400103030280c10640103507a14107000a40040035083d0300c1041c220030380300e109401545028080c56403018088842c007410400c104e50b12000c040c025600280700d401440c0d44280428008580380d83d0046412011414002466582c0c404e041181c0032165480131681ca640d85108184041e00038290541c05401242d0800004060030300646c040000110302400b50742d00040000c4092604211a001810340203229244032555640c00958800c2c142954500180c1024000155420000c4915245020041010840d80d8940346010014 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 436022473 1250 436021223 436021249
    0x602030603120a05180429150414031006030506070503130c0f360c020309120c03071d040f0f020a0902091005090303070206030423010606030c1805 65
    0x50142e0609050148040801800300307500b261105a00d0700d0400c0d01c1c00907006400e030203203030043c0e041c1011300f05101e40598600c15002e8406a500d905015144003003507030710b100c0310148440d829000802150a0181c0300f1202420700d411000c4030302c40030190710480b0a4806038440142146e100101042d12540100080d5a00007100e0030014510111600d52032054101a448a403040d03400490521900e841206465003241c10614144000170550000d224180040e4001c0c0300d9007699901400c04907842442212841140100756001e035182c80e201080c0c032110140000782c404e20803624000ac00d1501d0032010003444480424407851079940c0d46a084070012940c034110307211903110456500580da401c0900020f85551000145c66a01000a0100c2000203040620030302509010412699400004440290740c4c1a030320320362a43c80e41d1800410381c03e4503000314a51141d00c406030300c514100c1584640c00720751081c1e8080c40401c0100c28181d50005000311390040180d80343b1400d120030309041d1020715107 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 436023723 1250 436022473 436022479
    0x9140115020f0601030308012105150604020424020f0d09030201080c0415030501081902031207060207080a05091f0e10091701090c050108010609301101080c040f0306020306 76
    0xc0640c10740b91540c02c20000760021000300fa01400103018010700b1109030b80700f1540f0001c0301c50001c52691501e5560b01007014a030b011a12120700000c0300c41c0c4482c0c05a41c0289801d80a003411301700f080c4401803100c0e91400100d801841508100e540c1307400001041e00804a01c0c0d00c1e000ca81a00b140c00442d5030060050019403c8074041100190043d1003c1c11901e1270205590001104e50522001c1400c001262080f0594031440000d03840250b600410300c410311440b1078540d03942d40c218601c1c24078040c2c000d13410080c0260b440802c040700c410350848000c1082200440d400202ca0340c01102c6040940807140001000030000404070b0a142025a06c06030000d195061001c021543c071901a0f004010b01c60f0fa01d0301a945801200c8200103203c1d06450141c542401c0090303d540c14600c3c018212005481041c01c0b82054840101d03502180320740103c45038201114840c03d1031554201a80c8800c1c2982003d40040c95010002c0c0108a484003035500346e4820191001c0600e1035901c500000e034101400c0c280e8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 436024973 1250 436023723 436023733
    0xb180c07170403050f0c06130e1302040203010308121015080a140c07030801090e121e03010b030910141801060506030a050403020609011a0105070501090204060803130914011502 78
    0x36a0701c0154080d00046208200800b00c0d105483d5205080c41810340350240a400b0030b100d0754911001014140064900c40c4843d4242a034510a400d08912940302e0302179002440000040f05002005009200540000790111610b40300d41e914103582c3d26951050901041042d81d141803411701c1403940c644c00070720525022038105021060740c1c0c0c002c1410381701c50b103c0d44000902c4004051300a02034034018180d02e8020015070180c400082d48403e10783c011541c11341d00c0095012103000c0666450054201040c80e210303104d60715800b010300079a10550b0082c1861059054400c0900e046000b481c0141e001414180704640b40c0d542102c60391422803000781041d5494501c08115038944401030b610601c551038011645090c141400b0341410300c003403c100b80e40e07414281400d0684011342941c2c500000203103403d90f84d8407140c0c00c209006100c480d000075402400d0900c0010542000000740c00710003d13400034400c89039a0742e100f100450b02d00131603881c00e5a1899004004007444030039860585207142c01590 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 436026223 1250 436024973 436025003
    0x2060a0e090c0d0b030102070b07140706060e060f10020a0201120f050f1006020f0703020910091505362e0f06050c031911070909060b180c07 62
    0x1510040c001c540da40080c10b004260b42141110074002c3c8a01e01000390001c6141c40f002e0386030300c55000e500800f4001400f901c003035620904580c000c101e40761260405001c11038075846114031074184000f43e44452107030000002e520000d107004808000e0349240743d0000c01c482d071000d50055a030031000c2c00b12514655520040252408014014148201e2015086502a150101d511601c91030300d074014400b154840b401506205600040000a8a4040f00e9800040d524446411500e041d25001040c29a0600170b1401c6d0070b18641010350305030b8900b25551800680700d41408101000070411100c0e901c9070310202c2080865800200703a400141c146e85001200d4481d41a00d10300601140c0b481d01c2a45003480100000e252400302d0902400291034030900e000042d0381125078a02689842c441d4505644c440103240d9401600800485c00c1c0c41e4054030409959680050010500c2c81400c1d41c00c0703414038819442621740382aa20360071b98036260100c1c41c1601c0d8546c2d4014036070031010048500e030b0051b032844 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 436027473 1250 436026223 436026229
    0x1080d141801030b121e010501180b0d020d21050c0714040e03040e01030501110a0512060f1002030d0513020d0f060f0908180d0b0105041814010e1606080402060a0e 72
    0x45d40c85604400514841402c11900341c0c0c65901c0781282200c1da40350500510038140090b0140030105000c03031000c10400b80d1680001e04802c0c14150081d07010141c555094100041126100b250085c07140c140c6401c005100c01c203690380d109000908441707804c00c0800703000140620020844400b40500001060707407089960501e554407980003000c4003c0e800004108005090190011001100c0d050504104101c08094082d0245002c3c441d059003a50000403107589036400800d40c5443c00a10b40003200c800d0880c003a4680e4040c4807081d50207410080007a2801c009600d884030040d07400f41c03101c82c410328a40c507603ca8040d4052000c0740c80f640c86241d4091480756500591080c603020b1a22036596084901400001a41c0718581501070440c0c00608400300d803d841d18241120000e0700c011404a00c0c41085454580075aa0020f080c40411080e0482811055000b4050115403204031b4915a0050b02d0b8282049414861800040c040400007401818404060b101207134050030444400d130612000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 436028723 1250 436027473 436027489
    0x32106030b091609020a0206040204091b0b1b0c091303110f07050a0e060f04020c0a08030901090309080a050a060f110d05090105010f0f031709090f01080d141801030b 73
    0x42450340b1920030540c001e143c511041004050103002149810a41e1801949031440107001a110380d80e0760501c0c0040c0880041001c3e0800031402003030003c1030700d8603081c180c5c035000401c4000c0040c04440682a01040024141c4881200206203100aa45003e00541000a21481181084103000c07404468000402c80d1031111030201001d005003a09140a001c4480032a83c0119100d402000031310403e600e4054010101c40b17000d07a00584d4901c601040340789041c1c1007000c020943c0300700004100c44400706501000317206100b03a49000c241c40e512444503a03100c044001c09040d0350403580000c0c00003075031540104140a0444004100c02c0e440b12010300503070f00090341040369641c6071410440b84940030f104590242010620304001c25080051604950000b0700005050a00d1080c94568030068001a80c075072540050500c0b00503e0044500e2020250a1040d441503100f05c0a001031120b000b05110042880b0100f02e55061200c04081944061403e50626051664a41c00e2581d26164264 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 436029973 1250 436028723 436028731
    0x1509050c1f0212040e130809100804170918040609150c0201060b0f0a052a0a050705030a03082e090b19050109030f14030d06061b032106030b 62
    0x8861040503481c800030f401d20f508030f1400011010304010a1080040304c1c0103d5030810760b4000c0c0e1840e540514501002c07940303e4010715951244420055810581e031141c407584c45144200d070850602d041100380950310303008089a1036031020003010780c9428080040f04880c2c1c0309006620100e06291191a40084c0204a202a07800c150705d411040122607024000c0800034105580707414a4210120014200e078010724290302d040040c00180304080080c66900c0b40707581c1b8103481d04184008440014159144840c10f412a0039004801000580b4540441e0308a11680c05464210b501d5491807413425081110035410b4111040c6007101060245610607120054411300c40002040f0190303001b0030005c090690301c541c203c40720b114000e011a9910550724001c41c0d80c04000f04603050694a480c01e4600d8840880390104d1001145024040000c0c0d00400c0c00c07100b6a407500b00c620b8030150840c0c80c842a8282000e07002c10f050300500702401d83c3d8403c060114070301c0c00344005400b5480ea59203280c0b404040d5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 436031223 1250 436029973 436030009
    0x150708071d0306010b0a0e0603100602100204050d06020a02010e0a050601140904050d1112160303050705090a03170912061608070e1c020301020a17060303071509050c 73
    0x4010044015041020042900c880c511042214030300c070000a66500f205001e050b07600d01003c0b0760448a04c0c041c600060141200510b1079480703162990715aa00d944062090400502c21a4181e41d144585842185e00f0b890015060340c00d002041e4541d0006903100703083c0e1804540d0f80d03451198000c1301c14040140c42d00d200f6400303003001e549880c01c4250306000040b07045100d011a6002d02000400c005240c48030f08803103081c88029090110b0400d41091950008541c8245000940f2035940f00c035200d501e1a00391090b1020001a100c000040742c550099141c596040200610240b0214401406091444051041d41490304241602090b04c3e00340c0010b000c42c540d4030800600c2036440079030107084110b10161030081254a007000009220717203a025001d03405442140d440c0700300c0c0080004aa008150050029035550703906500c004d0400042c54900c5041c3e10088002c40c1c0c07149130100c100c0d148541c020300f420380c2d240e40000c50080145480c1e00101c955200710444008141c0701d9407242e1040903440 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 436032473 1250 436031223 436031237
    0x3070c032d08061e1c0519080a0f030509210405040e060907150516050703060501030b070801150c0219030b011d0a0612030e010c06020d0603060b0a03020901030b091507 74
    0x3d100b4040740650050510300c2c1c034840c85402c94995100d00c440c104a41041c41c0b1035801c80c40403400c011b410902c04407052414100825080302c24840020014201200142d54440b45404014030880444106407119101c135041588881c4814009284008014060703006562810b507444002404485000d8404459074101c03808100058605202c10710040800482080525841d0f800050032403190384603824464400190f0f10040c080d00b00303c02c2c0081d40d44500d04001e203503102d04200300303d048215106000158600c001051180b80b404060ba030070f00c20b5460b040d80c254295400c000158820340e941c0c488103921503600001240e14501d0050080c03582d50240c0001481c8200e1140141c0001812000b40170304108080240c0041d41240070510707505841c1c07450a00c0d01c0400100e6406034410005001240007003680b40d081c046e1a84954100d80c81040d040101920381810711442c086c240c480654046101c0c0700400114860f00082c40d4008522010748030140c1f140c04103a0b503040700980c0c0040000d081 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 436033723 1250 436032473 436032481
    0x10510080c040b0612181605041b050d020a18030620090306070302070213093906030e0a08070804050f221802030a14011103070c032d08 60
    0x6018511050600b40d03410300400e078004000c80d6552251108000300b180d00200010802103080401307165840400081da9010b03000520f501e022200c05016441c8161b03d40130020b110000444501d6010340c9885e10707124244041c01281c0c0e0029004410210305101580c04150746110041842c207000e988901c40000c0c0741c0c5440d000941c0e4445140f012210038200c2044140007960b80043c0b1264804924034000d07940301e1052000c51151041003003185003490820109108210611070900c00e035000007281d50304205a03a585411407031500d04035040d044000320300c0510010b0700c41d41010007140c5a02c000c907004500c1503a9105120f0380074903001da070160008681408145402e0380b9a40482200700d1780c840f00100410100d82c02e981a0b00a000e0240f50748410360900b0700031001041c1500d0740c0040a4880e800140c0c100304400f90b4100c928040e0b0343d444d003603540b560b030b010341400d4a02540c2295204072400030955410f91303403003500307811000c26142d1194400100005849e1a021240f1281d0340d82052410 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 436034973 1250 436033723 436033739
    0xc050c04240837240509070e130b010311030313060f0f030b012c12060a0c0201020a1d0d080d0b0f060906072a06021b030a030e010c050f010510 63
    0x41d66414505840c3c040d41d820380c80b0510b2104184403042d0f00507824608180c42e0340b44002c0b0014131066143c424506280030030080c80c8010801e68100c030509480e45509560b808140411642c01d00742c0140002c3c5e980d8018000b18800b11400c0390100d00241c00c50340341032211410030040c0c40d2142d000c4400100e00304944103286500201c001690740c40c9050500a03102c034540081c001c980166000d10744110245110080c0c0c001001c218446c00c03d014200c0d80b04a8a0310345400e80b80c1408071214150300c0d00b408003412000d0b01c14404c440702000c40c0d44d50714a86c65078a0341550483c5d08109505a44240c4101e965404030f90445c0041481d07661042000a04450700c00c18081144402043c11348541004d02515640d0380700d840403140480c0c0c1c03184404c68008001400140c81e5a412001c4004034000f0440c04208660009040300b0529401c100800305c641c0203004141d5140314400340100084c19009016105500805003000c0c018464001d803482041e0814205084410440304080401e000c50000c1190300 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 436036223 1250 436034973 436035013
    0xd05101e03060b010c0c0308090d0819031a210a020913030f39050102040603051008010501060f110309031501053309060c01050406020414010c050c042408 68
    0x200085c2010101040c00b6110300191070704030b10000c0c0958200141910440c0d03214000c90a420ba8011406a00c07040304501030b4100d1580f02002101103450b0000d020459000790800441401d001006140304000d4801248010001940b045a051040c0c00e00003005070b507170000c224440c0c01f940e03c1c1022014950f080c0140007210051124003031100225000d02c4110b41d40c106c03d4160b4040040503071003829202003c445d408480703007010744035510214000c40c00d164103400c514091121000604105911403149078201c8000380704020100d040700c0c403202d00d401d008862802e103001c1100705803401c20b000b8401080c142009522440c610b04007000040c00305182c40b00916010079010070316046249140c0451100300100b1074800704440101140081e06952048200d41103103020b81c00030f01041c14280340c500084c2d0000d002c0d28a00113552800c0d0b0050307510404010100680010090090030218002d03c001810648134911b094460842c01e80c1080d1003180c4d00340010a281d4000b015000d01e0a010041e480f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 436037473 1250 436036223 436036241
    0x1404030b06150a021005090f03040807080106150905010804060605030d030c1812021c050f07180c05090906031207050307120212041a0d050a02070b01050f01050d05101e0306 76
    0x80c0605001040c01d03a40e00040f020f154a440031170008840e22448501446c060f455840601103100004001c03443c4140401d0702822101128001c2c821591240c590280304602015644e00042c480001042a58824081c468000d4000e200001c1c0c0300f61620003082c24030041c0f1216201290f01c07401000090381d40b040c0d580d202480640c0c032944155003003039a1222040364040303010340300b0406540000324410000c2c4000c04140d610900b25019148a54000d81c3c5401c01480740140720100790402c00b040d12142c0c0526000e03e81c0750342e621842c1900035020010b01c510040c1c0915050300c079441e480440001d030500100005401580110382714140b9140400b00e46256411420454000f880801801081c601c1594261640502088482420300c90080c4c1c1c0d501801a1b011465800c2c42c051104002d00d5a006005140c0540c80d900e002d030f03803500d040c84115240102e4035400644c0070009000b0744691544400c0e0070500106281d2501580c1d03241ca00440c031262802d41c41c590038140001c000b0400148100004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 436038723 1250 436037473 436037509
    0x616030905190b0d0f020307020d090602060f130309051207050901050f0d151401180c08011523041724130302010b03101a03011505101404030b06 64
    0xc1c0c00401007281c8070220b0740b48641c07003241d60007003060658101c481c0c1080c103441050060442d2a850b18560095403403a44507403000200b85441c1001c103185d03101041c01341c422000300c00c036051141c03100c05a901c00c0c0b09085000394200455450042003c0d87e83c45180940e013200100101059810030081205610701a48090b1090a0020340395a00f07451341405412020f802503100c44109a40c1d180401c0a05140c03243c1c004440300c200000702d44445450f01d045444a41b120040008500d40c1c68103840301c0c8000c4c010001b0181280d090021041d10072a2040407405100501048c0f4450060760000c2c43e800940100040250740724560007096070403c200301c4e085243c0000d16541c40000740548440078005403041c004400032064013000d041c000d40000c0d0109601500310340c1c4000c120718402c4001d089880b21410100e00c000d940c18110f00d0140141c0e200710340e104130500341103454201001054001c26002c4400c0c0705107001a08049040710740608011802000350513450720302442042801c0044a1714554 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 436039973 1250 436038723 436038739
    0x2090f0406120308100e0c0d050f040308041401020c0106180c020d0512060d0f0f11030d14030711030a091e0e0a0504110301020726030130020616030905 67
    0x44298845080541c10070781506152800d034951040407081d01c1125080424200c4041082c0074542102d40010405400036110400a54850482580800ac4161000383c0000c040c4004140410380005a40440c2590f6000041c0b80170900030115080d66640d9000c880d080b0760003030003840400c09601880c00004694406000c2c40300c0e040310701410340e00440c0e102e00002840c007400100c05454120324201180d401801c004422030f010f2034a50260b080901c4100c1e000041202c0e940c4041c03c0018203868180144d40b03921710003590b030005d100d009400003030007401000b80280d000f2400d450140001c106122040da0360b04045070030200408504030411000d401e11058000d000c02100072240880d64114401140c01700303440d1900d061084604042002140c0e04d03510000d2844100500d000c0480d00750a10055111044940c00b40ca00d203890009100341506540c4500c0a820088000c101644007078040c100821b06140c0d141d000301d9455002280b0381200e07452984284003c0c1504200c84400600f0121342e010 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 436041223 1250 436039973 436039979
    0x4050603030c16171c08092a010e0901050f0d050109020a030804030308090303060a03150b03030d0b040b09150108250f08060a03080f0d06122d021e01020f06010902090f0406 76
    0x4000c41c103140d0030b4004011219001c501c201034103200c41e414000041301c482481c50480460b0452341039814082501050081a00611504201d03c2960486400500e90404054107909029160b80801d10440f2655a1040c46a00598441d0281f6010314002c0501039141c500f1450094681c42029204801c103601c14410001680c2d2551001e03815643d010841008a0001e088044c0c00390400c0e284440d4140400b1451400d0301e091940590f074624421a0f05021071301000e0144880c115080e11762258a000c0b1062810342540100511500488110801426041200c80b4540c294014081142c00904403c000c60b12141e445810160050b10840c0c003102014075640d2001e90921484541004010022649407c0611303140e00100042075800c003043c030864038500d00b0300000740c200107803003501d901140b5000903000c110030402c2401c0d56018040b0700400904159211100d4008001241188195415822030a405000300d50090980703840240e211000d00040040c0a034a0040c01c9024525100b410 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 436042473 1250 436041223 436041253
    0x6020303090d0c110d05210d06090b0a0b09061e03040605010e0f0f0705090904140601290f04090e0a050c06090619050705150405072304050603030c1617 67
    0x2001e21310608983c0349050341124541681010101c048411090105203011000f520000300280541d08061004200c0c03140c88096110071a1460900c141d00031215460500c5202c0080e0b0080800e1a80140f4643c10325915000140d850050102d882404840120512081044502905001d4901e01c42c4071030040c54500c42035203041d14010000741180303040d0004100201d004000310b4205c600050304214191400d8149480c200e07001061401c0e040c400c1000000720092100182c00e100d0f5010410a451041042000c007075907000300c16018070080e020440007c0790720240c4200d0a0200001b0085c0003d500c00e420304500741034102c140705010b4a000c01c00c0807166990201260700e142c03115200d80d058461030000c222414001c0c100000d02a00c50801030000a80c030354030038240709510402c03c88030441d8441045d103420b040c0412069103449008005444140b8254100c290702c40e0b00030301141d0a0184010400e45003501c00441801d00304c81c511028441040400c9628141c01140001040c0d00540b405403 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 436043723 1250 436042473 436042493
    0xc011e0c1707110a0305270307090e0114010905060906010905060d05100806010e161e0f020115140414090a0f03210506100c0305030c160501050106020303090d0c 71
    0x40e03081034607000c0c000120703440d00920440540100c00001c0318040c003124a000380c0203500042006510011014207043d245071200498440d280c0003074050b000203490190f40c60003802c140707a1400769a5407224144c031004044030420328004c04003402e02260500f00300c000c2c4402002e020303241c00c0c10070262a0041c0000d4591404071401003030b2102c1f000072507a441a00c0d8004402098100c8a21402044000901d6605a000c0a03000c1d000440050401001e40642503c1c4c4401e840000010702140c681d034141c540307000e2230400c0d4002500e13000200f29030b404215441c150180503001054840383c0910795112504141c4034032130741c3d50500110001c1a09060078010707070380c080c6000004c0c0000006d410417810184200e0311803184000b4640040207035003410350709a001d06070441d41d00780a07000d803250060003540301c0d440c0703c02180d41540740c2034555141c8011142095010b881d4074443c003003c080905000840034869140241030302da01951700c03410324140b881d0400300f0005100c030400400070485804907220401c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 436044973 1250 436043723 436043747
    0x30e01110f07060902030d05030402010f0207060c0201031e0608010c030b09010f030f0f060207050706320c010e1c0806061806030411130e0c150306060f0f0c011e0c 72
    0x14501c1d02d07244686400d00142000c184029054080c0034441da9a50b500300c40518080c52003600c84160a40c5002d108a0b5944014410500054442e07400980994066448100300001d100306071006400400880c406880260344040d0031695228500e2506960611515078012012540301c00306524244a140c030049443c040504231088400703101c404c0044101c40e050700d496219100b9921507840d82013090704c4040611816010800c0c410320b164140e084501c820f10400001e41e0400c11000300f4510840d00780e0800241803103150768400b84012086e004000300344414501955020010003121802031007048064101070103160300384803901a0700b00c44880c00c000d480b4282c45050303c86e0b585042c5072015088a035446c50700008803030385078007041c0415080348010300150380c00c9030401030108050100d0b244900100d829284002c0c0082421440e00000504000c11807424407418003521041e2030100f64003601986006a54443c014510701c1407096164900f038030000303410400103031308a401402d000d000c00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 436046223 1250 436044973 436044997
    0x91407140307210b01030b01031101050403081207020708030f1e0403150f0b091807080c060703140403020306160f0306050a05040209130e031b0d0f05030709081c030e0111 75
    0x42d0340e48420a60400c568980f40c1e0421101c06465a407420b00c1b049030035081c00260380600f21200926034950044048600701d0342d120100900e413001d24034111034011030180c100421809007520009a2401c1040601900c0d401c0d2035250b665407405441b4406d4142c1494441100700c80c0c107001c20004641880c00d0504140180380022860785910284880106203007000e45034000c1c180001d00031074650303009a250f401107041d8100c0784055250030313845688840100d2040c0d4080c1c4104001c50020740700c2c1d0560380e50082c55081007420705449600190034404100c0b00829a0142e2000340030003a5031284518407184101d080c104039642c1444c0c0402c6268038107004250180f900010f08650b1502c401a01d004003060307201c4104205c0c00292000c9440380d226030f403422140760320301c0710324030400f500410804480340f1207880d521503d6040c504c041d035481d00014060002d2203201200062800b5050004242c034400c5000203440070410190003404655003064a52410b83c589142581a050a5011190030141c10 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 436047473 1250 436046223 436046249
    0x60303171504020301031505061e19030b040f1209030f03080c0d0e03040f0e010e0f090f060a0b01090603090b1504060b070b1515040302060901030f091407140307 71
    0x7034005095030141078000c1904548000000000d100c0d404000c60110840b8030070a102d0b58980008101001e074198807030207041c816501501c0e5507440c5c03041e2006400110a107104294035640d0301c4542c040c10741107030f082d2011081a06064100302c20100c00d654208041d04290030564115210313210310f4650020000d09000d442d201081071404944251004030030085010703c4140f1010340f0464894005d44036032203880d2120000424103d0001c0e0286050750120b8100380c1031944c403041c80c00c120510280610042d805403840ea440031032414444184143c03800040841e40b5420280010040003250340048105844e0115010000341c1d003081650b0070903048840f2500951030440050001c0c2083c1d80500c1460310001900c000704061100f6039403040700d00b0000001c20552039024444d580011169281d40810104024001850840d001d0640d28006150024842080000000442d43c81000c1a07608101c0200d170100b450804100d807001404141c642d4440903114400440c0d0f4030069070080c070310300c1c04403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 436048723 1250 436047473 436047481
    0x80d050a121e09060501050609011d0616060209130e03270604060801170f150c0d0c0206090c1e01080402041b09061112070209060d060f140a06030317 66
    0x700d4002c40320b03210703651424010040000c2d03044401881d10700720484000341000d00003c2e442c03500c102982c0040c001a100d100c2c42c08560806403100c00b40034481c1540c2304105010070301002005041462b40316200d01c0740140d0f60050754080019014110a000c00700ca800c165180c20a610048280d03001c1106003043c280900c84d440c450100744540d0081002d8100101107000201c0503480781495040f0b079809034003505031501412110703440d401d1202c055079040d8031080500000803803081c80c05070b1103100c2540b4603003007071194040c3d40c0584604244540042c0e1007c014811100320500808080c04d10844001040340e1a08501c809168800030205040c071804030300060a5441c1e54000c001102c0c241e0981d8038010118000141c422881070080c0d000003000380038000c0e0602c07000a4001139000c14502c250b800e1856607404c2000b4014010000d54000620005407000240f05024411010b240311074041348400e8602e403400c1001754024001d411040c01d0200070000300ea04055840031070340c0910241c19043d0740b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 436049973 1250 436048723 436048757
    0x80d0b01090510020304030303150503072d03120219211202040f030c06080702030301052101050f0a0f090c09090302150702030d050a0525020c03030d15080d050a 71
    0x2c0c0e21240c2c010f598407600b211060303404401042130f00d201c0e4404024a02c400180300601e00d440d402840d402d5070002c0c1040c800c00002050f0402c080301e46c2421741d0b45e0861000b110490b07a40c2554811146081078815112103250180107078000d1790080d400c01c002c051040d4554010420b8000089014603483d104161080c0d4801d070148220303070851850543d9650303038440344298075000611080c0c403008510702c40802c83c030f841080000c1c000d008a500039400c59003408100076080c0042069040c0142c502444246120028000d02e481401c226114180c10321b4080c6094042d04c5d15450412560f620301f00c804400640900600300554613140e0000614200e217140c01da1401111088005801ca00901001080341c0d00200a00090541460030f1000391164000003040e42d00a4401403c04d800940200e40e0044080c0c0045108126503c11580040400d0703020900b154000d402c01030300b01c1d81384c0350400704c116040000040100407100003405038551b0301d03000512a0240d905a1800c000d80c00b00030340070700c0e1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 436051223 1250 436049973 436049987
    0xa0903020a0f06020d08040b01030209060a030f03030e240408090d0b0a05090d0f0f0f03021b0c03010b0d230a021002060601090f120f170301150813080d0b01 69
    0x25034003810781034000c0d07141c503a1000400801d2003600d0040c403921050324481c40c811003d45d4050b60740242c1e503861607400c560030800310300e03402841c031500601144c02c000702080b41401c3c0c0c582d00740e019450014950400030082070a2030007200b901050602c400442c000703145201f101955029801403401500c64111100041040d02441c5001d4030b000090024408403034080d07801140101400401c40320450070601c0c054500100c0c4000640208800384911075115000d4170204031071045034500189000034060400d01303541d40e00d01d11740815a006008020399424248942440c40c40100c9603a10545aa540c8070148500380ea850f0384404445503e9990341c0500400c0124a00765009200f250040a031803c000d5841408860030390001d0308204e0002456112032002e5401d80d0070240786441002d485454071a5001003000048800c085038541c828074556844000e10b01810000d009414606a031060042c91400302500c010400b45607006c051000039940d00c100ea013801c0e4102c90218046100c0340040c5d9080c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 436052473 1250 436051223 436051229
    0x605012609010e0a0317010e0c0a03330f12110d0809030706050901030506041a01030903120908040518010e1902120f011719020f0a12030201050106030e1f020a09 71
    0x1842002c651104254101c01100da0071b20b81c07288aa285030780d990a0740d2004220640b1605081f01080120b0307000d403031290b040801c022202c0010380f601c060000c2284107072070a45041552080080200500079481580160300050000d07080700c2c0507003002ca8036110504041035400d0b44c82611058071101c1000300460980300c40d0840241581c3d456a91b54501030101c1c0d0290181e64006844c06c40000c10519252240c2d00c41001c4880104040764826401540100b5100074290b041c0008008a168004000e01a820300341d841140c595464a14020620506284881e031554103001d14400502c20f940c1050082d0381e020307469a03013a401c10707200e40d00410300a2150000004441c0003810400210700000c490590480d80843c410b4041c0c04010300141c0e40360b00890f029420182c02071030401c070262404402c1200d00030002042411901d82d5503522402481409004070b01503511840100070790b03509485402d03140d11401020b050040b0300030403649110508031140840d008e0703022070348034102b41c8641400405 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 436053723 1250 436052473 436052501
    0x22a1909050403030b09010602010903020c131103040c08190302150c0403210e01030908120406021315081b0306010c05010f0e0102071502212809020301060501260901 73
    0x703030070907060050181c41c64200c6140150034600001a0681c0305100c2c0121498040c0c0c0900802c0c0c0307800f01000741c1081c4400141e0344013611a05426040c00e003440085011b280700c1d030180b20201d890241061300f0a02a11046845900c2c00c0c00004082038012844076008900c0080c1c2400940c2c940f07000d01e006000e90780014103140d034105800440c04803011140601d481032074036000d84c0b45d4486001141070f142c403820b0051252105003c0e00110440480029411074402e40c0d01504000f4100c10130245902c0940c0005d990345217800207000303035070307002800c3d81c0d0002010310012a800b1082d425003285448040e180c0d03410491641150300a10200390700078810416110030500041841d078036841d0203500501016242074420002d421010421032084695a540707580000011100310780c1b070a1140c6070010b01d40f40510154650304409445d1208403954040301441c400211002d4500605003100c1080c2c0045041c490000c607040007507003408820601c1c0e4900a00c0d0500141d032070101c0c0754090052403100c035039 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 436054973 1250 436053723 436053731
    0x207170403050c01181d04020328170301060807080a0617330c0a090807230d110609031c050705160f090e160305010c022a1909 56
    0x10401101003030340d0303001403c00d0303968501c100a100008002001144960b1020202c46100b107194040c030500015800350004064a007003014088103200d80714183d2049825104003a0501c2c0c04018441440780c2c90450701008003408c0d5810900c000d030074440702600f81420300c031000c0001146c0c00c0d00c42c0c1051000e084403001c0425481c2402c64045d6480e8844c00341207120072141c0505141d00c2624028515070403002e82e5140702c1540350002943c20a0b4400080201006620440807407030300c6003000404000c10b44004c1c0d0f062040e80c0c490501401040e4864224170030301c0c2110501d404240c4101060069100455056680c1c40360080020b01e0b00c03c400a002c0c0c101030581d004022640d4112024103c0a030184027600d501d1000c0303a0620303801034006e0146020005614500f400040c0c8568801041d10b0300c0001210781803030610141044031907003a4403c0b80c441c3c5d11000f104031403550521001402c81d40900401c8250104a0942d500700384030a5803a07400f8000a103001c0001031040301481008128110f0100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 436056223 1250 436054973 436054979
    0x15080d050423330711060319020a12271b260c03060f0f0a14040609050f0c010e1002010b060a1215051806040b040c03050a2301060302071704 62
    0xa200c4280f20b00c2c0303940341000d60340000344000316500d0858480350344c440b80303a46480100b0810000300d40c2001c1c003505021501101c000c9440085803004040c41007841d20b4041d03118200e010000203481c0d01031581095075100c1d84042505000e50f030350705004654482d00c1c10403851908032810001041030361040d00703034050040074078000740800029804803c4c500c4080d00c0d204c4443c03505140e130300c4605844221800b41520001105400c601002d103401c0701440201044140911205045e0240107a50a55a0a1380c1c1c06070a42008010000030a000c85424041c016107001c80c1d00182240c1c06880115004102601c50920701c10b00c00e41c000380d5280001007000fa1102c0034900014248036010b1283d2403000e00d80445207030381c0c10a04108104483c0002c4c07804414400d00441454900c00c0907082ca5006629846000c890b9035079030080f00008559642d0014540c030301040403209032141100c1070028880c1340f0250328824420000454103640e6103090150382d82d0701a1814110781c00e0100c00d002c1c85000080307004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 436057473 1250 436056223 436056259
    0x60f030106062006010e010e0a0b040e060603011a010509060d090b0f040507120b1906080706110705120c090408070b0c0a0305060f092208030a15080d050423 69
    0x4003d202e07400032a4100c0d504414100d03141c0d2020217000b03400030282024010086510780d01d45103948000d0b103020110b0210000c00104090750008002c0c40c5554000804210290400340304903014020044107080340706103020000f070b14078030851074502d00500c00002d8a22900e915600480103155100303c814616243c074041c0301d000070809980031566402083c1c00010038140004020a100d40c20000440070350721010350701c9003500090101c04016a803a5100007440d0300040c0030700c030000e0a6607201d00f146100950700f5181011081d03040640304140e08440d00041242c001000d40c0c03036400556031441c00741c859081c2108140201c0400400a040442c10000310403410005880036a415403000d001603111601000b03100003142c1c11036074004a00100042011214240315541f02c00c1028411034402c07819190103009500c126400318800f0384a0306c0403c00c4050b41074405d401400d154019145c4501d0a541c01810340c41103109402e28101c003242c002402c02601098808a03001c01006591421111303009 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 436058723 1250 436057473 436057487
    0xf0c260a18051809161e052b050f0109150e03030415050a061d010f0803040e012610140a090807060e0c0a0f080c04020c0312060f03010606 61
    0x15000020703241607020581c00e2032441d01d150a440000340a20b150750000301200540b41401007104043d03100320500040e00104034511400903080001044000310b443d414849680d8095034040da000300403581c0003030a4140000100c501c410514040c8179a600d03103038144549000840d040c0ca04495282c030042408016a00f041004503071605002400000300091245480c1c2c0421640540907a4000010700490020340d80540d9100c48100740004206031944882d9410280401458801605420052010811000d002c02c01044154025032409060050290301d1b408180b0038108500d40035450382288004840c031656503020240308980d00144402c11f41c101401840c0d070003c02da410417401096640c0110300a5152480d00422001c1c54000340d56201002001c06038843d4a45021394442000c2076600d43d51410000e101400c030b0b1380d014a090060341c40c00c3c4160808894800c0b44108000000248080300307031644580000030140443d501e8901181050103000005030b80741d482c002000c074403690000d41d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 436059973 1250 436058723 436058737
    0x31e070303060f080618030f0a050702152104020312030a020d0b010e010c0b1b0310150e0108011215050c0a030501080a030207032d0804080c0108070f0c26 68
    0x750500c0340e55514488110702c44035a001e00c1c05541c0150001071108056843c0310345a062040c1d003128640382d8582c280c180c2c0c07034004008680020310002402e0007545007100c03041c030403a49084e00852400b001c882c26403911b89a43ca01c501015000c031780015042d90341c2400b02d040c0b21030714580c040344c2c0c2389404c200520080d4000b4a519182510b4400c00341400d5100750781c110342c0c82c003068482d00407004450f140c9105084000300350368400c046000c0460b40381031607070001c1c502441d00f194842c140b15041c11001c43d9450f030240420001c05c81030185030b0341c07160303880403500f41194901d110031480c0c041c50341000c03c0d4401003c407541202d0703420f01e4203205900303c0e080000c01000340c05a07404c10050340ca46844540750180e000c00034005a00902081c0302042420510b03a1031818410320086102c2200b80d80c00480711205082a41d0034000880c0c104001c450500c030f50300001609103040072451503c0a000741040c180b015580d010030501491110070042b07d100307007840225607103001701076851944c0c08206407640800 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 436061223 1250 436059973 436059977
    0x608070b190306060225050307141e0604030803130b04050309011404030206040e190603031d040516030e010b0303031302010e0303071203150b071104060515030402060903031e0703 79
    0x500100720b1080c0700d032109564903903000e4202d800c007503d50312465072201c40400403108500340000806507420807030840104540c503040c080b020303641010004406100e52082803000d0495507404040d554120840c0e09583e27003c15500e880303442d03d468510550b119148020f06500c01902800203000f000005040105401d913190070960941541d03a500c203000d140302c0250408400d00c4240414910b0b6144240cac400101c0090b0f4070101e20300c214000542c0e0055200b6000b141c18030745025648607018282c880226425102070005080c030081c4101c540c54070000c4c8404041c1e803030746001200c8a0a410034281c40b00d004045035102d040842d2140e850030350512040b4041100c0c00784240e0a0700b00402528080354205040b0389100c5c2d040101640078103406030300d078080d000c6001c4000c103981643d040940343d1140078254501d540602ea10501c412240a074010320720a41d50a1408900d8005480c1207075445035050300c07100d442e000500c01080c0b81d40513807580308082075010b0403d49607620101e001f5200d42e901907 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 436062473 1250 436061223 436061257
    0x3081b031c0c0c020d080307031b030509010506040b010c0f02011b0b09010c0305070207090504080d1109011d0604031502210405010f0b0a05011b05060901060303020f0105280608070b 80
    0x3110b003510395004102c0000c0d0000310410344540868810005141e1005180c00d010030f80440c0ca1000342c0c222400b003110030b004241c3d22402e200d10b0781d40034403c030b0382d00c1070098404100200080f40060107245600740020070201c484100703d000c591040003007201c0034160b50450442102185008402c0440c200c0e0071038029881c0101901d4864400e000d407030300074240d40e009821520704102004000c0c00c0024400c1c0e07080001001003004400252041f0a941c9641c00c011f16103640c664000140400d02100a003500b8004011414220395140d0044400702da0744800c42a105221404144001c2c0c052032100c842102c00700c0f058040743c0d04060107145d01c0b46108038001c008050508603620200c85d103602100750420620402400700303501580c00c11051508003d18103080b5003075561601e10b4114211161281c0340d4680300e080003055010890344221010200081c07190340741c850b5440500840d00c481c16044046070440410302d482403540141c019110200607140302c55100c0c66080595484080e4440780082c0c1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 436063723 1250 436062473 436062491
    0x90b06040b0403020d0f0b18010513031215080a0b01051005030112031409041514060f030a09080c030d0515031506090a060e0f07020607140403081b031c 67
    0x41401210162041c100a460900741140c00340031545130740000854044d0149075501011070890840d0a00c5000b032521003040e07140c00f100c1035500b50f5001515948090701c0392010040025000703155888101c240b824000f5074003480e00d01d5107645030380540c007240190060250100600c944a00e506045e0390301600c4201805011103801c039442d201c00d1040c01074040d1045c031003000292040354501c1d000d02009400724201180040001c1c1102c840207920311560800c000c00300b00070404220f1b0307003420305d500701c80360350500134880d004580380d02c4010810349942d0b95402e040b0017000030101c01d030780010100c0002c913501c0d0642c481c20b40c801844191010f0341d0061015100500307500e8005900c80410380d69810007101c9803a158140104864042c20114032591903010100700c00b4440140c861003804400704079845030510b110003908011003c0d080404000c0955040003100ca03d8008590881e1762110300e071507440c421007201c04403c00f0722040785030243c0400201020108007046404420ba0880001040907600e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 436064973 1250 436063723 436063729
    0xb1812070f08160f0b0406030902040f1d060a1802090915010902090102120a0512190f0b04050601050c07030f0f0c180b01030203060a0509090a02040c170a05010b070212070f0f090b 79
    0x1044e481403488001c4208014404148290400c2d0046440030f0400310340c10540140300010f6421001e0300c130003005101d18002412030000c11009821501c1c00314100000d504d0044104005801000040d008043c035101140d25103004000c0c1c130044a010f6a050b495950f100c2103040c020398000c00d42540148580017000d1540c40348582240c0130310301103840786440d01d9004c0500500307101c0020420b0360204600c014a0304401014042c0c1960850175081c0080d0801d07201d030410040f02c87c058191410400240521044c2c41c04c0003c507102541d412281d031800185a52410002800d0010303030060441c079003072038000340301c261040005400d0004605d0034001c17001d066004404902084900690004502c0010030507030400070401038021a0781c009541c2c00d006260003080550305107080800020b840b20071079201d1000c0d20b1021a80010101d54107218070b5140c64081c0d4010301540c40c019200e001001c03950017183d6800c00243c00105000ca844003061507540c1020300b07407084a803080c0d1609a04000454603249 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 436066223 1250 436064973 436064999
    0x10b0a050d1113150603050c0304020a0608090a0206130e0f0c031501021c020607090905040506010e18010501030c05031513030c020d0c030b040c0b1812070f0816 71
    0x810241c40314070041038645900e80200541590582c1140d0201c60490340d00441c1d000f4241c40d03000d60906441050f140520003021140c00a01030105030707000b030060000503580c00c0000421210946030dd0142915052500c9041460103e0003c1d84200c00044440300d241c0d01c038030003004071400075940c1001503517290501860000100e81c5510f01c040c041000030000c141d1400406041b110610464482c0c2412088034030380c00610043c08000360784070504119495510000f0718003d000c2091090115040c90b548059840006020341a04102070b50001a00b4010600d000b2007848201e000a201e41e580d64203004900d4a083e000d003030300a00921240d50900d401482c0542d02800740342c04415154901d41e1002c880e000001e400c120313406519542200003207205680003401a602812040803070b800c003480c2801d00648079a01502c0c243d101440051a45036000280d0084000180e44079020641110011410828250880c1c8040444101e000c12560f400050700038004e1040868002190b8940c00849080 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 436067473 1250 436066223 436066229
    0x31b210201051603180203030408011d07080c042a03062420120a02010c18081e011b0c06050106080603031b1207050c01080609070c0204090807170309010b0a 69
    0xb01418003c3d0000c4a203e94405450000000044514414a030380060b055074080e80c05410345039150201c1031442910840035405000d4204000e0038440d1402c44d010b41c40d143d05101c42c1b132042d990380c02c0c0c0d034030b0101d0346074940304030701d81d6405105a02c00ba5004000d4014156805070034090300185590000c0e0b6500444d40756140710b1142c40700041c1d80c01165004924245200e5900d082c0e02840702e81c40c00f01c0a8a030041e1444800b1a00080307940c800d80e0200810500c0c5000414204d0301210108011140010908200c002c68014002d00e9404030f05209034090180b14a00c2020b04078403040c29610300c1d0303012071305002e020f00c01c4105100a0740da91100701c0f0040d4007960000d6140d0000c110b192a002ca010f02d1700680703482c0310400e44040e5540014800c5160300040026202e580081d0714405d107d42e4400141a440b0204459418450400d180014403138241d17078200a018903510000e000038000d03808240e9400d5a80400b80d0646203c40d00310b100500c0d04107448415156090840758100e41c5001011070040e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 436068723 1250 436067473 436067491
    0xb090d11150919030c0b0a05070827030a03091104061508040c0e0705040801050702071a1e041215050601020a06090201180306020a020f28031b21020105 67
    0x21801d92600c022411180103007440903144180e03410010085a407030b44126525019807152222440c482c1000818803000408005429240008111901d03400c10b0b5042c0d0808001e58812801084201645090f0402c2c541000d10f2807001042000d134480e4180c2005458500c10780f044100c0e182e04800713002c01c4d10020302807001282c0c08030130001a0144107141c4103a03c203014900c6150950380e1080408100c6405a4041002440004052001c20720901680e50012941d1000349031040c54401014a242194100f1140e007540000300c4403090700183c843c0d03111242d0390038a0296070301e41d95540d03100201c00c1c000c0700701c500c00c4112014405608844c4107042c070408061b0080c125058030b5984200c021300b9a44422414031a26844080102d04c44c014003001031803142a0040c0d4640f5603d401914160788045122440e42c81500c0222000c6e11403074009178036416001b92400c1d908014a019215164083d00403403003544102044c00600c44043c1c4680300742942e015a080e40e01e01c1e2801c08034240c4e5001c551b800b030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 436069973 1250 436068723 436068733
    0x20708030c06160912030f1b0c0501050d060819060b030d02070315020c06091e010618020a090b070c0f09061d04020a090c08060f030705100e030313030b090d11 70
    0xe071420a90404211964918044200c1905c8100701341c40075203025001d9001444ea44c0091804680210700d071081c0e1500c0c0030b200d80031050a42c0d940303200760145014003070421401141c10341c07082c14507800c4003014110440503250f46911302043c0310141d1840480c203030303200c80c02c2c405080c030281004100c40c1046092a4040d20030385045440700d4006180b002008884a5801c209544002c0c1b8140505805140502c0180c10715540351f50000f5003501400341a41c0c000c2e40750150820849070384c0003a481c41000c680101584072980c4660550f0109815440804072040011790101084511804031050324031521740300442d2511030f05000201c903a24065803015400300304100c480c5205e84440180e100303100900390000745403540210816240c0c00c000507000315901d4402d200e01d030301c1c02a4880315600025002091102e20742400601c0c0000800700c010709000704807529041c40e403424800c9905208229101090055032441c04031044181194114428000c0031003054005100e04081c0180140c0c060041c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 436071223 1250 436069973 436069981
    0xf030f0907050604080a03140307020c12030c0a15060605120601031802061c0b060a05071401060b0703050d0c020f031e0d151805060108010608041109100501020708030c06 75
    0x1008040040c01034032081c03180103000141a900c800040c4064a9000c01610700ca64140c500034200c44200c010a09402c10284104142658002415049000101d0351541c0100c0c002e00114114032925000054034081c09204100303000c450402d40c00380100c2ca41e010413600da50340c1c004030341c1c50103100141042c40f2900740206065600c682c22001d07680d00ca00c01008030505ca983c2c00910b06a00000302c4800c02d901100040c0c1040c000d130702c240e440780c2406031034041c03403c044140001d0961103840401040c030034140d082d207442e04000354046000707009001c1034503580c1e08450a0240031a0000040c07030b61801e082100104d131207880420041c41b5102090020343c02c1201d5030b0345040c2c8182040107041c000312003c0c00651007092450241240b1143e456070303002a0070342001007406200c894401e00304651820071041c004aa64032900741d0b411110b003442e140300c181d144ca1401c40321201d0858912a03001c0004c00901c04008540703009442100c6090302100c0706280d41d49074480c0c9a0007580300d01707076031a0481d40c001 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 436072473 1250 436071223 436071241
    0x7030902010c11031005010632070212151e011d010501050a02010f0f02071110051204020a030212100507110318010306080f0a1502030426161113020f03 67
    0x3c51a00382c001010f0324220181050020b044480903030004002429450043d500c0c00f640725120800300c501d00c0d00713404201404102c0050140701c3e442e0000d0040800c00c908040380c00c03080c4090410480340e40b000303406c28100360500c5644c52b240303405c4220448a90100000e003541010a4100d4441d0b0a1100342803181e19010040d50544c200c034030454190b540703589801504000c180309050805c0301d41000180c5440da41e0030a000c15038441030040f4020603c0340515800c00340c000095500300a240c0080800c0d80e030f501c2c0701282c1c440038254002504501542d034801400040407030305214008040b4820401783d9502c0c0402c40c1e0303800707052622004513042081000307481e4184259040d8481010304012070f2169880d0849454241d1035624002e468008004110410514004901c2d40107592a429400d60816448180031040d980032901c00f07a150300c900305d06c20509124140c40c440c198220001403079006c20b040404200904000c1184601010003104800454600c00d49007001c0e0f01040050442e81d8100d11 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 436073723 1250 436072473 436072493
    0x20703180810090c0f1d07210b0103090b070806090a06050d11030118050307110607031202030a0b150a170c040e0408040b0f0415031b050f070c03060902030607030902010c 75
    0x41901c01c0c41304c0708004034082040001035402482ca40b10380c0c1c0359141064440710040e0b0805001e80003042040403c07141940d0284008042d1403141080008070a0120f0340181c0c0107064024001f03101d4104c000c100054079801c1140f142c4100c1c410b42d00c0600c140d66a03a140d90440d0f540380540b030341c00321002404e000450420040450b19038805000060486650744208a80051100003110281d00008080080001600c241c800c290301c19940f490806e1075030f40d0007a05800111400204d074950101c0050180c040ca41c102c05080c0d42c010740030122035000420001032550080d07114601054900c4541504040000c0200d8803600a02c0c0f14181001d050001100d0000300149c000c0c0c07540081800082011400d120040111180d803500b12565140303002c040c10000f98640300020305161501c83c01414241c007074030164180310982c0c6030450303903210200c3c00c0107018040d0901c081d00e8444228004800c00c01a0790141d0a158000c408640c40c5542d034070022010707103401000007030005500502e62000a021054 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 436074973 1250 436073723 436073741
    0x90609140d02040e0c010f030e030d050a1d0309010e090c0702060a050d0203130b01061b0611070501020c06091612030c11090a150503070f0e1b0706020703180810 71
    0xc9190a841c899800080540e40851000b40f101c2d0440c039034844066801c1591903000301c40c1814140b0000501c01c80c01a2a4058449603c1c0500d8079040040d44c440c980c4d500422000f82d25480c40182016803141c0b46030399410000e04240883c800d42102034013803802442c02d9206060344500d00d89001010b609116403608881c41c26800c1c000140100c041d581c0082c00074621031810142c4202c10302e0343d00d09000e140940103074018410300c02c601151030200000400740414544d0003800228814884100001c201d2080300805070440d4070100f54403000310f00c04600070f80243c40365170454003440160800b1801d03005443c4101c0c000d0790b6800600b0000240244107042540e0301401d40390082c1030405011540000040742d05101c440d0395490400300080b541b110040152109500600d44a41007454044d2101c903640200180946030381c0001d80820110f1138154501ca4014099984450382803401c4400303034100e1003040307000ca00000102004034180f030303186001310b500800040803100702142070740c402403400744 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 436076223 1250 436074973 436074979
    0x201020421050a12031a0a05100c05071505040e01060908031c11120405061807030b130204020a1d010e0f04020310050306162606010521071e09060914 66
    0x2410030012500310700ea840d609113066200828201d1242924644941e510f541c1c0341d110300d081c00070a100d0b507151192861490810b50800c1d2507030880030306100d8940b0006600206056008203017820000350703c03801400031209078610100b056600d03100107550307600c000d0103040400d50041c4070a0031a0000c114400142110007000061040e04580c6003c2c10380d4002040300a1101c081c00c14401003103410008164001443ca6802e034401ca15803803002d80340c0c25184009080740400030081000c683d08a0b6503d1405a4010304c215900c07241e050001d45007400d0407070721104001461042100f55400b5054140d4408001040c10840e50307401d00822000b5040a010100c5030303002d11201090301d4404006075130080d80c00f210405440340b0081c07402003941050700d102c0c0007141c20b07040704504405001c425a6400020908006e0348030500d0035507400c80d08882c22143d402090310001480351568100c1c80420484003004000c2e0030343c3d00e00c01e034107844480d41449002c1c005010180c00300646140d10100a003504801 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 436077473 1250 436076223 436076233
    0x150f040b1503060406060510020d1407080912010902010206011e0e090a02030709021e13050d020312030703051008060f06060c01020c0111120609010303050304120c210f020102042105 80
    0x1c804a86008000c075022502d9a54605090101349040400501d0802084c070060021301e84a5500608418062111007680c0c440070800804101140082d100c01810140c00f500107621101c4226001e0b00549400342e01600824001041300c0380c00e0300000040030000c0d801c5080e82c5180200c901c1440c24002c1c4101502e0003602140c00040c1d40c14002180140300e2008c0168031343d040300a1601c00e020085d00101c685040401407010180b01e0000c1c0f050844404035110000044140003003405c0140460340f40000d00030000c2000b0b121a0146d0005004071320042d1410805625400802d40e030721802e0ba10316007070050000000e80c0c603103040e8005050b1550403000143c10600106480340c01d542d548042500e9122002c82d02d401100c2101d44055400041110b101c50039500d540c40103091403002500c0588449075950f0a00c100d1802680e549030320079070100e40c0000303100c402490420842070071201c202c0010600502008110f10500030781d01a90150709507002e0700d2080c590068035008148908585c64011 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 436078723 1250 436077473 436077511
    0x5090a030f03020a0b0a093c081810052703030c0708060703061212090b1602011706032e02030c07030908060408070330020903150f040b 60
    0x505003640401c2442a0020003140050345000a040c84000302195510751404000c200818058840030741c0403581d814015030070113030580442001c081e0805681317020b03000c0d00503460204010072005044044240300d0346041d0030a02c5040101c490001900c82000541c14030401e1050070900c090030f580518501411071468a14201007415a04400b1001c0815081210108005141400303042d42c0f1184501d02002080e082c40c0300c0e050b41d104d8110024003083c0d03100c0214541e01d4002c008410192400100f503649980300f20503006409185050100d002645065243c00d0112440e24043d00840c0002d000d4a400102c0c012580250f0850b62500b201d1440090482495058030b840114054a110001144d0324280360a001c0e044c00c00036401103299911480170400421102d005841605a00d0310300200c2100c00050440c5112400340c4c2c01c010501442ca003090040c4066074004d04c4c1d070b03c5050741074600184440d1030015002008603040c4580500c1800010000341041d03107a544e0140050701040e0301464 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 436079973 1250 436078723 436078733
    0x20f031c0e070305120a18080307031d15090102010b0405090c010c020f09090109020909070b090105030a0207050d2f03070b040c030501140417030907050415050402030a0605121c05090a03 82
    0x30038100580000c100c001800c2c02260f9201440140102116687c915210314100c0080d40e20700c203240d07000d02000044c00003503160006406054030b0401d001860f01c550901150300c040501c5d4405411640950310782142c00420b81818015244a1400003024189030303101340d0019981049a001c0481e40700c4c60a03c10444150303503a101c0e60307000e10020000001e94513124410304c040700801902c01d001c1644698805c11409042c44112590030a0a10385036459403501c47c0b00101900a00700002d05d43d000e4804c000041c5a4401d44e0082d04c45200411869140c00420310030582003c031214480c074540040000d5004520030682c9583c1040c80b45070301001055580d115582120301b8a039481c00610304a00c04d02040c001700b0100d101003e08074241c05d510390704051581965a02c41d910840380980e49a0300000d1448490310b17040320003032a000e001036640340741888031036008080c03a0003440d2181035120a02e40800a001408804103200254170500301c1b04d0b9110300387c4554005070360607940501e0600d03000c00021 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 436081223 1250 436079973 436079983
    0x30e0103061d01061103070b0105010e011e0216050f060f031518090c09061c0c0b281103040603050405010f06030506071d0d020d1a070c03020f031c0e070305 69
    0xb040559103015154113084000b0a00c4021100600c1d0300d6109201c00c1d008144540710290445400b424400e5071808180010b981610b0a8010390b03011130649404900e009401060750100140c421039100c0310141c40d44204400940021051034200301c0510a0910700b041c4500115006001a000115201c1c0310b90001841c80a061b09a942100c410b441445a0000c0c1009500150303201114403600c2490f103040812010750019510032402c08a0380361a03814803803014800800f0700030540c2080d9452030700c0f82c10720012151a1080140700e000e400340c0c00e2403031803040401d1360103151428081c41c80c051a01c071080f400361401410541c2c0ca5581d60300d4090350052584160742c01036101c1e80181c01d003071508d54805004060040f42c0c0041541401c404180d0642d00d42d03404c404010b0703044441c45039259040c1820300c81d80400850340c03028800c0c49410701c119582c03c044040c40c264400d0782114698440009600e0301c070700580030480c15001d4800f08030342a10119800c4080c206640341308450b10b441d1340780c035014640 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 436082473 1250 436081223 436081259
    0x703081c0c0f090608010b0921070618090608070b070c1203031d07030b0106050a050c1501050306090f03160501020c07090b04180506073f0e0f0703030e010306 70
    0x2c030310b502d800b03800d0160300112a4001001075080110302580350498188043c41000e100c18807a85001e034902a2002c0c0000e02e051481c1ca1a4003154000f90300c444028007a803070428651185008044e000003410000307801040280c0c8c0c1d651018044881c82c001d601802c0390042c120848200c2039091000c0b45d1250001c1224a0312030007a17402080d038604a092440f08109900c0d44c0b19600d030802e40082c03000c6145c81b903005045469500d4803640d03945003020210350900450402c140c850051003042ca50400314008040d050f95400c5090340d999403581003070a96038000301c004924541d04140b049522040341e6040c100406405100003604d001003d900700c0303041455942143c480180d0300c0b0703403020050078030b071240d04907a650400d0b0f1640102d0711902c405948250040028040020807a64091944400d2602c6e040c000711502d41e81d0b43c80f9800c03d8060603510345d0f000c0301d50007851512060107140e402c0042d002441604e00e0000c2c011031401e58600b1a2113501100b51117042c144c46100010f0111242d1031584070b1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 436083723 1250 436082473 436082477
    0xc0d170c0c0f0d0308040b0601030f09060608250608060a091506120207020306011a0f07050607030c090b09090a060b0d0b102102160605070302090907110703081c0c 72
    0x60140707000c10001c41d80c200c08100c50045403403411400000380c1050a140d0081d80000c006106550340c900100d010344001c5c5001ca00660601c01c02d4020054540c01000c1660900816110400c881e54420034600903c000c1d12034050900c04003c100050248100c903801c00740c05413203c041a034807031071040d00352150005142d80c00589070804001080d030110b01c0c03003040c85030144c0641c640140b07900040ea817444107000c0c0c40c08001c034035002801c040f0000c0c0e00b207d017a104801d851780e80b511924103002c5d0300d41604807200310110f41002518220a4403403a90a025a4191b03c3e800307040c803514900b0300401b0724008000c00d420716030710034002c900c1c200094040c03c20101003483c08a03900344400140290648800d040c0d00520150b103081c441c00400c52254149060703110304005032125a0341e420071103010680301e005051a4500b01c24031164582c10740003019848416200709445032101201141c103844100040901900018070500001d841c0c503005080000f41c903101011400f011118200441d5041072030200 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 436084973 1250 436083723 436083733
    0xd0c1203120509060f242e0c030e0303070b190b09010f092712170406051509060303091201110a03050106020f03160b0c1b0601050a080a050c0d170c 65
    0x62201004c1c031420f5400b201100c09126070120101c000720640c46000d0140c1d100d014401510040f611001d031414207c540045809100249102005040445401c4080d00015101c002c0d4403000d060000071110050b910680700001d60352a5000c00da100c1d51824880d0511035142c0d80b90503099030790711030071034003130131600b16200080303460081118101d49001030311541015102c068a00e00c0b180d03900f80c000b070703880d00000d810404440c900000c4070070740e030340400100f050174640061009100302070717010314881e500c4209000e42100c034110070400555001c8440c0e0342d01d68810084022903042a0400111b6072002c0d170000700d28803004965140e03541d0489404200065524401000610740c1001007a03c0f2003801809503180c2803a000184103001148200509000002404640d0b100f40003000c5507109603904c209070717900902d1440e50a072552401e01c58030b0300c61a10351001056194000c9071908601d0707030110003072500005440a00c0014224010282c031101d1a20042c000d00b015018010034101c80004c010701 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 436086223 1250 436084973 436084981
    0x1106070e13110d110430020904050f0106140a09050f0711150406050901150305070510120c0c05100b09061c081309051302091f0b0c06060f0d0c120312050906 69
    0x40d2903100040101b02c0c6d8130140c40c0c0c0c811100c2c5009000d403c52150103403406040c41c2d88500304a803810300c504010340010745c40c000c0d00088585002080d0341c01c01c042110307401e4642d0307541c1c1485c006462041d101c00c0c214841c4000420804c5004030102400749001105558074516401a104040c9070b04403403e46d100ad84070780810260035001c0c851740f0070100030005a110002d0031511240c3d540da00f41d01501b8080c642c1e1011004015000b0200584003581d0418140b0400d110000c00800101443c1350403103281c4a910000405051540106d0403122005024140b4980d9043c003004801e010541000700960030460804000c5102c0100415501e01c4595441c09002c0c54480c2d001c080340c00c0100780521041141940c640103a035a030b01c1c0541c2101d5901d6030102c01c2e11540382d00d03004000c104ea1200c4074a59000941491070100402e207144100011104040b29020b007000348401c18604001c000c04004c0000028070100400703a400b4101e042c040d1a103280f0740ca0f405a4107900311601500c004c88250701080400c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 436087473 1250 436086223 436086239
    0xc0507020414040c14010219230102190e0609060a081008031603202a030c10081308030a05091c1e1107061106070e13110d1104 56
    0x142c0564140c00c01c211142c0c58251944072402949028048481e14082c2d0045041d07882000000350030050040c80e00d4010002e4a400c40900701c0201c0b0300c1e00500e800300c941d00c44807a0103100342d03a40640e0895202c46801401181254110902d07048180e21600c1401101915220b21000c0c00450035aa1035950300b43c102480b101c01c4000c0950700071406a8400c220384100030410082c1885260381c03504051000b94400f160b5080402032050907403885220b94081c0ea07102c000300142e00c903081403510b80506401030041081c180c8650090360301c142c104515540401e0224861030a284d408112602078450780c4540f5582e442181d4410384112800e980c0784c1c400d006020405020318058141c28007240383c0c14040c82c4102a00040e4500e048542c1891403031a0349043c80d0040c1c80f068100c0c012101503408680e1115006442e10007490701c0b04042d88505400144194014a070b01442d1403001450000c441901e69524006842e0302c0d00d015283c0c51050100302c0c03002c2281d001e40010f1700040d8103411b4443d070505c058 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 436088723 1250 436087473 436087481
    0x9060613170622050c010c02040f0f0c0314040809090717090102040311010302070c0b030a14090a0c0503060903040b0d23010302010206130b04110303090904120e0a03080a081503010c05070204 84
    0x803014400c0c54203c0342400160001520400c0ca280a00701056020754a000141c0100a00320a50340c3d410300b070801048480806500c00300c12120a40c500300051601c1c5514541074a0040380c000304603040400c81111181340038903182d944210540b60414034001c004c1049410701c4025144840207a401003000e108000840070403c035003050038a0308504015141d151071084030380f01d200384503d62000002007000018907800c4a04089143c503501425814460010b03560b8080000b4180d60350319031001c000c500d500c0c0c0464400e0042180f01c00a605190a00c070740c55202c1d03800b00c041c0502c0e041d5281101c2003a03001d812840b001e50b0599240c002070541c51800003a040440007450010301c02411260400007032400e560075504950407940e4040c2c81d032501000300f45907105c3c0002075580310007414200700412001ca0702c001c075030b50801d59540c010364440708240100318070b171f9020060000300e060024140b5a40701701d43d01035200400c42c481c1101340c090000400d08440380040c04500203980029024294202805 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 436089973 1250 436088723 436088761
    0x1091703010302240a030b120102042705191a09090609011406011d0f090408030403021b010801030f030e060408010b01021903093305030402030105090a02090606131706 74
    0x601c840b24140d444c0c01490940c4501d856103400c1c55a914007039201ea44070700c40f4170340030314007003000071940c0d00d8031006403140c2011860110713000b04031445140c1e920340f0311238049c480c02035465100001300412420b9801d03024001e0340350048044038020780ba541c80c523540e5003000350142728031034050682c80c00d06a07003103401d41d90b895084000d10542c4205012481c0d0703202024000c01c2c400300030341d8103000141e000013031000e01c0b1450450b41c0c000249400e21081c445081d00a41c081d44c465001c44e000b5507681c10440e400c0c0307285030800a0125800707100400100d94080f00e8090500e101e443d00b0702c0042501c400180c1c1c0ea400a03003104509a6480303c0c0907400b9601002030307211500881d410117085064958000701091903a01800c980c0280c4c0704c1a401510200e00d002c201083d035004d6800100d81d030620ba004150703800445080e8801d600f4500820f0541c0030100d43c02554035009061441603580b00d8042c4100c6a20100295030789407000e90002034030f050780c2c0100350110740c01e801c0031700b00a062001d284503034039100350 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 436091223 1250 436089973 436090009
    0x180601150f1e0c03050c0a03030c0914010c0210030f0f050a0b031f0b010c0602070b04020a090e0a0803070c0516030b071403220602121f0e0606090301091703010302 72
    0x1246010905400700305145100c0992602542c1d4a480303280481d0317980a0a092030200c2c0c4619002d200c205a00340d01b00b1000d65800303550303031445035944007a00300d207404600c00300c1804190203421102c0541040c5a00c2d5012800c2d0303003004182014a4010303402265592801001165a40c070141304040d00940241d44601e1411001801c0ba00400e022400321802106940701c0525a64582caa032180d0080100c280055040001191615198103080080e0101103070100d210b1200c8180c086403114051041004042c3c0c094001c1c0880c2205690b00401c590000c3d01403810701400001000001d1820028280e9030b12010300304020a925600e409021060081c1039070090042503d000c0e04810203030000d80ba84a00c982c00c810104030380d152885015611000301c040c2a06000003081400c000c5040005030292003c410110901d541c002842a10050759004a030310302c0d0024804600549080800340101041c020000104c0b915641e8a10080f012080d40b6003482d64004001041986012150025a41e10701d03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 436092473 1250 436091223 436091237
    0x3170603030a080604091a0f01090b010309081c1d010608060a0516080c0417030c1b06070609021912150c0c0f0c0b0c0a110f0d020108180601150f 64
    0x1030b20003030302c2d07441c0041085000342d9550b40c198080c81241c0c006c41004401c0f5680805403802d08c02c910107880d00b000d000d48001c060400300440c0255100e8480d00c002c1c16004406c66081010700100080b00c01c2440086001542e00d644d160b95186400248809107402c14000001e4680d151441050400d04000e007103070031480c500340c00c2204004940080c41e008030300700d190914085d80d45900401c0c4a0240d60001c00040c54842c190001d1014004018900e01000c0c8044807001030301c003030000c8500d04610100030340008003408000c00041c035541003c14802d200600c0c052003000081c03400c0c0102d880540c040c0702038500c005c2101e41031142402106150351084801071203581261207001c1c0141d40311030002820320006413210b00a0140344174003880a4200f003860141d6907104080c601d036948940290903a240c26891141500c5841c040e82814100c107005444400300b02c4940d0010359111030020318603a10000d00d5010360a900300c007442928042c20b405030284030740c041d54100041102c032030501c0e494240004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 436093723 1250 436092473 436092487
    0x516060905031204032a0b12061f0210020f0409020a020c1504050d0f030201090c0801050702070801060e01050d0c080f0604030311090108010519030b0c091f12270317060303 76
    0x7113a103002409010106d0340e580c001d560342c42006001c16030395010496200d40810140842c00720444140e0091a04032041c003004904410100d80c1d0424404917180568001e8001c501c219038107402505c5003000c00c071091410259201ca42400fa6800310403481c0c01600000400b81e49031400a10380f0074022001e264080c101820940400c000050040f400b5294246c00d002c080300b054401d40145c00455031040401c013a80e55606002c60203002c040d038407203015004582001c02d400c0da0501c43d01080390030304800c0010a0b4078102c2848a00e075401002541d8000d0b0406011030300380c400304035000b00401d0140080038986850704000f01150006a1401003d00040081d03c81983c0d004d0300b00e0303043d903130103e0740c0d00c685400e181414003501001e070380018650040b100800c00000d03400701c09489100e030b090350f05445009103d000701c00303050380c0e11080c4004505c1030b202a0102c000310340d110a00c221040d0301d00d42884040800942c40184030100e0031000100405038040c400700b820044203801490607001581800711b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 436094973 1250 436093723 436093733
    0x605160609020a03020d0f050c031f050603150c090901050604140f01111e060a0b0a120503041d070e09071202070812071205060f010f0309051606090503120403 70
    0x1812020140026840304030707160035907640d01d080340b00559000700600181d02d42c61812162009050a0a8850b8026a440c209a41c2001310f074a20261800e28015490200302011135801804040d000c80c0c0c00d48142900100e40021220a05004000d002c52690310307010490200601800705800890003100184800c00c95030900e40070007401c60030120b40e002c5c945246040125010320f0203e4610342c0c90320880782c0c10704250413560030115109041d030054132841c0d40e8804ca90004d59041d204540d40010254004101c2403000c0343c0104220761080e42540c0c071300380e0780d0f11400c2010781c03048140b0004101040f0038000d040f500102e1f0752082c5103068800107002d02e482d8a0103072002c41141c0764031880b030340c000a203241009070324012a42d1140c02c00140d0003003030802200041604d42103051240ca11481c1c400030501f50720301103070703e5a40d40005079180e061520701410120003810707141c2c1044072107104034500410480c1e07810203420003030569603440c8013520b49000308051034400640c10002c5030750302c200418000300d5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 436096223 1250 436094973 436095007
    0xf0207121206121a070e06131404090b04121107150f030603110402070302010204050a0f1806080601060e030319021c180605130305190b09010209030a0b060301140406060f0605 77
    0x301c0c40104891465a50803001c6c0c450400c800d040c95409400000d04402441c034114003881550071021030540b80c0360101003032108440c0a10b43c00317040c401100c40064001408a0502005d0503c640383c09a032000c04085424a0211aa04041e00c8407070700c010040c0c0758035440180c201003000c03140360a000709451925104070240c405071143c0d00464000030a00c05241c001d4045500804c009450340514a50780c03000d0400301143e500402105040410f95685641d101c0d00071602500c150a02801043e403030104103540c00202601c0c0e55405010074040101075440b001000740c071411035500a802d440713440e1400d042e02d440c90148010f050002c48080300542800403604001038890a051907aa03c107600d66020001c00300952009040784110101c440501c2485c2d26902207003403054040200988800003045d00340e004200e480e80c1c1503072040c940d6402003001d00a0b2503800120281c00000c205890044d40032580404071010350703e09031104000c00104102c0c0d03032040024802483c140d820070b820a0700000c482c0c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 436097473 1250 436096223 436096253
    0x10209010c0624080102030f01080304080c010513120f030f11070b090103150603090204060b12041104020408010e150f01030c0303080a06091b140313060f020712120612 74
    0x70356495070180b009081d0080c2c0d07454070704074404141c6400f99641c0c1d0440e001c1d60044407041000104640002034101001013914261034402c001b500d2515501001160160000108030800c961078050019904a01d08040c001c518003501072402c1020982c10301070002100b900271074040001c5c00121500c0c03113002003482c400ba035040d40d00c0316030345140c2da8004802070680e861281007140c2c0c141000164407a0154801710540d442a9800c1c405030b5620503000714035000f4401c4c0d80f03842c803255500050025400c48460001128000c10040c1040d0b140c1503924215211420b03a484158000e8200d100b026001502d81c0f81d0000745451821340d2903055541d1445190000d10000b81407200200c0482c3c0c42d0702c42604110702030310051038100110840980145060002c04001d007000c12540d20000c115160040201e91284e4011801c41c10540c0f41a0b9030385004100450004a070f1950901184c07002803850314040c1a586141d0707886c0019080000c10040850389554846541d10380308c2c0401e4400184481491002 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 436098723 1250 436097473 436097483
    0x11010e03120d0b090906011517180f0601121509080910111b010f0e09010b090103020705010501090504151e02090d0f0b10080601180903090e0a0c0e03010209010c 71
    0x40e40380c0600b242000d030914600041d4003000183c2004981400080d2003812110300702c641c418401d00c0404180c070000280d2a140121000407000200308100310094052060340f28022200300031041c00030780b41800d400382c00441103643c400300038030180712051b42a112100d105070030820024201e6550000d2601c00d4a181d507000b016071f41c0208880a0052040200c400d20303900036550080d4140c94100c9042d88050101404900c07004040d0103000c1c41541d402405800140c4034180303590030702d84400c0030390700507104d1281050740800ca10300c0000c0302030082c1c0e8000c2c092124081404d04091900200744075103134842e150300c245028825010203403e040705844c00c2c0d0720340000503928200c000202e030b44541c00f0b010282550b84610f01260030050a100c15a1140100c41c030651b65072502d84010070384440082c41003a17107050601c50582c3c02c60100398800c12038180700b410310b006420381e1840c00808000c07080300d817080106e580b13000c0c0811264001000e03240b0010220002c600d403100d07400010b4101250151b01070300e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 436099973 1250 436098723 436098727
    0x703150b0d0b0a0b0d021b0a0203060601050d021b0d020c010c120503062b020915011e05041509080d050702090f0a020c010905060103050c150423130911010e0312 71
    0x10b00f0b482d120091405405008043da030390f40a81ca40b407501030351188003200c034815001e002601281e440424003003c0107034001c010703100c0c3d40c0700c00004540175040810b81d00c103410703402c01c689640e8840034000c200484440e80c0142030b48004054000e803d000c143e04c03007a818050404038880000d800411101280780080c14480d1b240c0d1519000f042a148400500c2260000d0002d8400040c0c60300084c04809244200c61080346603032185481c03450b6103004010f03a404200d0b0454114581030b840c3c000c04140e041589000303400d10b60380d180c04503030040d025020303c0003181c035410052141c4a001d1111564001d0f0740d0030b02c0b901d004440d1303002c1001100010102c05002000102007a16640c0c1501100c110344150300091043c0085410f003180c40762003c0c03108070340c14454540040c1043c2000c0e0016001c0034000701c0301c0b90a00b4a0039012458103001b80301403030240e598401d4190420356800b04411010030403900e0004020041c3d02c0c0083c041ca1130340c028036041c03180b441d070981400d650019100d018900803110b041d03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 436101223 1250 436099973 436099991
    0x1a030f0106110c18042f010c060b2808011b210c05180d02010c08160503070f051006050604060c060b040603080901120903020c09250302030703150b0d 66
    0x1506001803040741590040d131035006046411a60050a8091070180303502e0914469021244010b0a8000404e60310b0ba01d40443c50100170740c080c80d80320b9a0380d4014440800c05005090002d441204414036090441001c0e05c4896903a410b1101e00c5d00c0907100800003003015824030000540d2070701c5100003e40401072011210140c1c001c40d10900c4160500d43c1a007030060300c0c84401d000d0140d070004a2012090380c1c1050100406151050300760110b5601038485106e0a100c94079145d2842d4007904000e00d020310b0000c510400550100000c0a4850081c0079045403043d02c2d251290500300c5007440300803ca03081c21010720903992660300312000ca40882c2482001c07030b0094170300180908a100051076000e4134103c000001d1040103402000307d01c0f0240d0b42c0c41c0d51200c1703002d490001c450f00b809001d0700680c01f650101d020342c1000c0c2d4145400c101c42c61a5500c4403918201440c01c14901c0444402c0000d4000c400d01010395014061842010302d946001c1103018288102030040e402640d500b50b0841c0e072070301d0301c40c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 436102473 1250 436101223 436101257
    0xa0809010c0b01080304150905130b1903060b040506030d08070807030f110901020c0109030c090c090e042d0f1502190f02070b031302010804060e010608071a030f0106 73
    0x240741e51281c9011281d40c3c1d039078500d03500d0b908144508440202a0078501808503c43c401d51400e07203000034440340030401c0300480c59000700460031910381c100d461140310290f03007003241d12040c000714070540000ca882070291b424801555005082c1500961007032400341e5106d500704200c0ca0784501c03a4a03100300a966003110031400f603d0031650340c2030704620b008101c01c0c415202000a02d0785150a0302200c000424441c01180d21300d24610015205074807100d007d10501100e6009020700143c2482e100d80c0c0c9039115021102ea40300140c80484800d0500306151940f5002130180c1d140c14203001801184222044c3c941d00c0180d51401d10040041e030882c107511482c401564103441c8400d0120343c10900e440202c0f84040c1142170008203a501520031480b00144101c2d900c01141d115240d0703143c1d204070f001441d6005498000c4080d00072145075445a5015007000400d204070f200500c6050024a010780c580182498801b4101041c110212030030010020544000000325046a081c0d10b00400c01c80088106 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 436103723 1250 436102473 436102487
    0x30d080619030302060f010b04060c1704050405010e1503010203061003050a1103130b0606180d030e042f03040f020d080403020303040f06120e0712030905031501150c050a080901 78
    0x3440040501140307000c0249a40010b03014480c004c03a140000943c0d0301e0b884502002e010b984503c4d4002040c0100e100d0015818590b0000ea401c0300840041c1440d48660004003550002d0b001141c0c246040d108101d000c560340342c54071003440001d80c021403550514501040701e500c0340240c1c0009054450b0049240088942d010981450004180b15101d05062040324058500c16030b003074402c1d0380c0c29404982107280107803c95000c0041440b04513822040107040c04007001c8861800ea092041d4035040c4900e5841b1030003015020483d10a078040010a17407c20411041d0701000000000001441080005602001c00340080354040b54010100003141c0381091151042d900000d415000204001400d42c0240300b00405440c1f01761035a41e0450300c40403080f011603003460858202613118035420031030b00001d180941d00d0365000e450500c003080e85a8001c00c2c94441344002c1140c8032000400104503200344e070101c2a107000190f10309199040141e03214240d03900c504c044054460300c00001e11420701d80c0600741c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 436104973 1250 436103723 436103749
    0x32e0e0304030f060213080d0f0827240c121306020f04030204050108030703080a0c050705191208010f06081e071d010302040812070206070c0e01090f050402030d0806 73
    0xe032442840800e03184c0f001c040d40000d11515122031140710041147c0314082080140d04429958581e0f010100d5281111280c6000c2e1810000e0700c00c61801c1007071003c1100c400c41181e46483c0c024009410900c01420010282013040c40b041c45c0c1d100203120040b150070b82152400c6001d4004100d145d12001c11100703c038480c0e40c1c4020100c0d40b0000d400b0314013841d428040c10441b402143d0400103a81e8440b00ca548034411801d005000a42140004d4406015640030070064001c901e46141050ba0319680c03070703180028402c0440400e884641c030120030070038140c11661403030880d0710b40380045501d040b01f41d0304500c1c020700420b000c0c0228440011004034091142c0001c1001a504000185c00c0003240501703401222005210702100804408030725500a0080310304507850140100f0301281e00001d030f10000c1d001040300701d0f80401c0421240c130118501544101c081d00308210300441952428400b241154845000390049034103041c01c02000d0b80e4049076140042c01c080c2400c46c0d8a83d034039800211000710440e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 436106223 1250 436104973 436104983
    0xf121506051e031209280824010819030f05070b040f06060e070905190521070503120403032105011205060f06150708120f06032e0e030403 61
    0xc4041503070780104400c95103203142c040c1c05642000c040319000181502c91140c00603040905803110a40510b1724502a050049004e40c00589440d16039010742c0c2408804286201515a9400c074100c00710141d08c0300e42d0040400c50b008008010402003038026a20240c2d2000e810301c48002c4007a5482c85c010ba046801059020030380585601e02131521200e00d011000007580e0451901d000440c1d02e4022a05041c00f62003252141071401703142100b00804115507a2855022a00c40c41001a05880c0e011600d584264000c405800c8441482e1003240780402030350009102e0b600504948001e80c0d0b034001154140d94062402400340c07858290710011040f0300d02d103450138451600000061591200380c5440c0c3c100e10900c241e50329034070b44d0780c4003400d009821744205034444100f0090448407041a0300901d6501e11400d912802c03c408284081210b92044414040b85d84101e070070414546000e00107144246c1c0d80c20b01581036000001c1081c1204002c1a44000800b640c1e00c141e404409002c00c113031001142d2003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 436107473 1250 436106223 436106239
    0xa03030e060c010219051b010c05040b1c09030c031d06030c0313050708160e0c0307111507020a12020105150105180607080703140a27090510030b010f12150605 70
    0x405c00041c00341d807195207441c4101521003041d0881d400d060184412481503682c0300c5083c107052004d1b003689988440c4607411055000144a00a54620b00510205a0081d182c1c10314142407401c0c00384c040c02075284492040303181e6130a12001d0355140710913243c01003600c00115480f5558a400c00c00c0c51001088013410740d10070200e001914a900081d40e40f100d485090384182aa6560b0340020012882601c001390402010f100103126035200345080500c0040c81c0c030855041100003086000704280588a800058025a40110511190225241a180080c030003003240d440d15a02d5042000700d12180c69041010008185130902120100c21000b5100180456910303c1140f4000c0030b10f51180c001180071554200c0480d038864040001d0703c010100a8562005440b0b0300c888d480303020583c110381c0d0203001c8044c66010842c06013500c6454401d4005111030140c070350640c00d00c81c81c5503005038032000310503041e2403003404110307204800c5001241d0311031900c01c03c000c0c00c1141d841c040c5c049500560f40100740c1e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 436108723 1250 436107473 436107517
    0xf153a0b1f09020a0c020603090c130603030311180d03020c03150a0c090503061909150b0325030b060d0b100f0602011109120705060f180a03030e060c0102 68
    0x1849451000040d03030308030940c003102e0780d4040c1e40c8140d0189a46100104076240c41c14005801c007640116446061402603c1ca024000320004041c1e04040308520003040e82c8075814810107030103104091201c5400a0300c1414999501c040c0700b0040e9105008502550401c0010400c05008100000380c584d130050036240e201d03009c011801d2500c2011181d04ea0190304040c24000954010100c003405e54802034080d20740707036548031102c005020064403200d140b40d6590f10003c020484070141205000310750b4a011a28100c130703c04051404005060114203248203001c07400391001400070b04011a9801003c0010300d6980305d0000300346403c0000042d02c0003200200700101d2952085184060340c0501c006144401e4860000b2400c8486c100b20f200f00c031041c00c001030701e880e107002c0c040e0381c546601c40c100b10342a40d80c40d00c021844541200c2005504d1010115450030b2000102084c64054802601c402c100d80e0303e5074800508407002d844030300b07015010000b00824585001c3d0100c0715102d0650030b500c000801 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 436109973 1250 436108723 436108741
    0x1a060904060b1c0614100f0c05030a09050f041103070e032505091f06050f0c07030c05040e12070227040b040308090d0e0f0a05090f153a0b 61
    0x251084000f82003514042010038041d136400103151002001034090304040c4040c600070b40394416242003d030244240c2041400000b00100000c1c0301c5e8020303507980d0b402100e142100380104003e2844c03c045c413032800c08506c0b40b51514041c05403588016203144c134103451031242c40030908091901c0d018038601e0166540701da216603500340d005000c0316401ea40032501e69456450180c0d1090301c1201c0a403940d0394420040103694030603809070580f030b61042d040c9403605211000340380c0b42c900194002c460007000500100b0952400e44070744101c22584030050010f000709440350f004c1c075104002c0b000b03100d00c010b01c00f008292041040740c5510b80440d60018400c6042900301044c3c401c00c00c4034101c1c00500d030600042c0f010a0041500c060340c0352140c845207000c640c17410401c100c4442d10080190401e5400030f0000311903460f80b14041c06507800f030540405c54201492007d0003001c50035055402207489140681c256144c03044d100d0140e051511a09402c0907404602c0001096510006404d40d0507140c280b0003001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 436111223 1250 436109973 436110007
    0x20f070c12170705031207140c0f1e03041203410a1e11030a050405040b0402040b0f07060906020301060f030c080c0706050c0f0408150a1a060904060b 66
    0x50041c00c404001d002c0c00c5591010510800000800396041448002c05081c3c0303282d15680c1107052801c0110341f210024690b40c50a4000810380700241d80400f0003142d03041e005004030a00d01d55240d4150b0505909240840d03502e2040c1d1084400100c9400140801d06104036803009400c102c030b80324110b0b0607615803406181d40002d0402e51280c800c45440c111030300c2004200300c0301400c4442d192080301540150f260309441451068002c00d10440b40c1c040d4000c010300340001c02040e0055111280c4440c180014803003103441c4241918001d0b80304200c14045240b1000c01e85011041d0105890342d100c1051a100d000380184813802407082c2d00200001c1181c9400180c0a40c0e444407541c1c0400c407400e07044c1300c00c89000d203050314015034644040154002040c519044107038071100d00c5030458a420180e411341d20440c8d00540c030040e550380140354000300140c141d10000f50800f00c5010280200d8170804d030041010040c48649030f00c034120018102289840f644c01090042500301030807901c51200b40400c003160 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 436112473 1250 436111223 436111259
    0xa05031e03040f03030c0309021017060306040b011a160803010513090804062d0c0218070813021309030305060a05030a0503030c030603070b030403020106030b07020105130303020f070c 81
    0x190316100340000c80e0888110940307105030b401001090340080e040d14140e00810703900200307a01701134413a0300b01c101589410b83d004910300c85a40c0e4180f04900a00010f003259400541064841e400c4a002d00000c035882021640c191038400085010403481c000e11049180f10780309000ca12062544001410300090002641c101c174001d403000006031072007483e51400c8800c141d00c0200403035403c0c00305000f0321b8460b0154551030605070038600c2c11207c0c0012075000c9809034540900c00242003070707480d00441c00c2c0020ba42071410240003c036074150030590006401c1c1032000b4000001862111070302d0042d56a000b82496540165082c00c0009400307a060007405468125101802401e14290005541c00c0c0002c0030309141d60044003460464641c203480d01d0b030680c40030b0900e60341072007482008a90b00c850303400191b004610030f40001601c0c0b89035107810021000020b0000c0300b5a403608003004440c105100380b0a2050343e1510340140d407400b40324500104c5015402002d02120000400403500c031000d09208005 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 436113723 1250 436112473 436112497
    0x406110d090c050a150906030213050406080a050c0909070e060a030803090d02190812060307030b01080a050606041e0f1506030e01050105040b060d110d1803090501080603120c010e0a0503 82
    0x303605d500d800c400400b002c100c07544c009803d0784020800c862080d0f000d02503074858481025a43ca540f000014261005034014803155085a95280c04010040000001504003510752003250301d040990107440c3d15043c030500184040700400101d456907190501805160b104d4001a1282002e480300703669900d030300390041d0143c13107058031450b0000b12032400d1009040d03018281a10b00204081158071500018012641500c140c4c000032000401c044400ca000c1d0034100700901a81d0003506115140c00005840365010300e14000620501004c0c14103800b51855548802050b0882030070307000ba00401c0138101410f0b4008410380007044640e416008006100f0049000b401166252020402280e0032013440c0c903032040003007214076080f5880750000e1400707102d4465090f0a18608d441080299100340281000b01e444480c0c052080541002c1ea07100179110a1811441c41d00e45880801c2d500e1040c2d10303005120100225110500340f1003500078001500403801a54102e007038518005599400c803140c8000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 436114973 1250 436113723 436113739
    0xd120203251b0819060b060406080a0f050f01091a041b080c03060d1e0605010308030a0e0106050f191802130b07032c1f020f0609060406110d090c05 65
    0x4942c2e9019100c1040d10203c0001d010402c1c010f81030760a6810744180704564440d150021844290f0f603650140004020380c0e11999034a181041c8032750215440c0d01c00143c9a10303c1c1c038047c00120400c00c012503065443c0b885c40010809800e85501c50711458803081c46500074200b15180d441002210980c402148994580510035150307201c80144c1400100c6071190018000701641740819040802d201800a03c290b08104411103600d5920030780300240c0094981c0c01c0d0000610a103d01c1520448101c0f152540007000014100000201e8540020790070030b2098a6445480c403001004d064070000034000c02e01c409903004102d1080c10040d400202c0f001d540c0350110640014000340c210100d48502e80d260b501d08017421040c1b000b0100305c0050860300c1d2090003240e01d601078140c9a040c40402c07000c00e00c00080c95203801c12103000303181042c0e200144215800810038400d00c03a0f40018202e4003c0d500410204030048c4080495002e40aa15003030749145040907020f10a000306461036009481003660001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 436116223 1250 436114973 436115003
    0x30115060f05071101051e0d06150c050a0303050903120a0c080105030d050904023108010b01030903091a16030c110907200c060d05090c010c020d12020325 68
    0xb88450040800103000f8003000e095040c0d5641c0b040c0000c001c01102008107410f8000c1111103840c840e0070941410710312035920308043c03110780100d14000100d061140f0b004084640d07141e40300d60729201d5900300282411f4444002c914440c00c14400e03505a104a4424003486207006004000031704072103540c1c0300100d80b18034004281e0b400c000c20011f80c00489515a80d00c0c0c02264014070000350b00151101c40f101030a10010740e090121440202c40200d40005901a0701d801c02180c00d00f1109005441414035142440110002c3c0d00004010308440540d4030700f00141c0e182202c4100d9601c103100c0c040382200c24107180d18082541101e5640344045c01007404c440040ea0348002d121031100c05459032401b05501c40c85647c2d0030340300c0c6103a52569080c0c1409032a54804c08d140030500315081342203542e501d9611202000001c1c1c80421000c11a082d007440d051017044807540100e54102c0d01c02c1c0000c3d02000500080d401010b000308126846c000b4500b6001800401d981c552002000c2152070880d03103440e0844000e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 436117473 1250 436116223 436116227
    0x1a0304020f0f10050d06030b040f0605090705010e1c02031e060a0c120504020102010902150c010f06120b0903120c0403030f0f122004080106052103030609040f02030115060f 76
    0x25031841d070242618907201d03c803c03010b8840e6000204241e01d01c070303120000400011000040d845c040c4d4400c9200c1c44a00c02c1d149002401d86000804110160f406070904201681c1e00515194036610140c0c1c50001e0500c4041e64403d10841c14003000e505489900c044003a2440800030141900d400c0d10161040d0341c83c0d150302c0c0001e895a100250000aa00004003082002c043c0d1045070024814000001c0c1c901c0d180e17000c0744001651a910035800340002c28041c007050400e026410300c0001083c0b0800800781070202c094110044c168010340210300c0c2d440000c070155000c0048601c1c4001c405040d514500d414000038981d50700c04c0c04202c0008860140c1d10403440d01801c1c0640b81c4030825100d071a5a000c0000d0f09000070240344510403100d0302c0240220b001000040c00410250101c40008640d4a040205100314134191070030681c10b48240413600080b441000c8196034116a0071900002d00e074440d400c00052442200704065859460000344117a0903a40c680c00408641140e120752051103102507003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 436118723 1250 436117473 436117489
    0x21020a021c02070f05130e010f05060102070e0c030f1b03150a0b2704090f1419030804030f2d0201061e141519090905010b090114041a0304020f 63
    0x945144c40b003a10f4418880351800c03000b0360102602c103110004001d110f00201c80d095544c007442d00d8800311780d07070300a0103000e503814080c40010301446403a442c443c0c24843e010b840a881700030a003203900040c100100358a00c0c0d501c03000c10b180318040c2005580b01d00740312006080114020b000070344140200080024846038100540d440006034032428481180d52481f02d00083c2241100291301c1560b6105400008440302c14034152103000d200880015103403070380c00034946107540d01419824040e00031320400003031344841c826034401d50510340702d2540640c01c001a03032807608500c0c11801c0200c00301c9013100d8107206403149225030009a4003c0c80350640d100140b400c0707001c0d2503402351402c03601180c06001094569000451801003e0305141d842d01d08082c0d03000c055000004149030380c0501c00d820205035540040c41c68054401c9260802142d45080000d11051058400b4241485110800e191304140d60b503050764020504d4046c01000c1c100c000d540e0001c507500c100c0d022403085000d600092030034146249 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 436119973 1250 436118723 436118729
    0x2070e0c030703090503041d010306060614070809011b030302120c03011a03090a06060b070b0c090a031103070f0602010e0f01060b04030201210c030603140609060721020a021c0207 79
    0xe0414a96121120200c024150f545030949451008100014032441607842204450890900681c0a541140707042c00507901b066205004000e00c0c1504030409207031807012101d09551124051b03a40d0b01a490050794181e01000000d1801c40c00008c511060540540040190024107005103072682e4840c06220801c0c0028000c4100f961411400b42c1c0036401140002c42e04002503008403009c00c11165180804d80c1c082d508200c040620200d404030401c0401030358a5003141030422a282005603031008100125110f200142c4689103688141d0310707a0310240b101c50050701c10540919106a20758101074045c003450748c2e000d03480c0e02c940b03c00c00304042d40600c13655041e00c10b00b002092030189035800464070100c1e0900d40d4581e4405200d07050045245500c65240642080d85010400301c0c6942044a42ca248628941d1590380100707082000c0548046860740e0322040c1402c28402d000307c07600b0380341c001c2100750360340e542034605c006a04541c11390000354602c481c0114038070503020000361010898031011144 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 436121223 1250 436119973 436119991
    0xc05060703021e07080903160b030a05180a0b161b0327060201090b130f02090a090b09010b240a0305040206090d0309030201090b0a12090c030b150102070e 68
    0x80104400c00d110b900100740641c2e9050b4565a0b410100f1009400e50380801001c0755100000211055a82420b0003c0e0400c417a9050081c44d0480c5030050b65405440014403842d440340c0e841c400a141800341020004900640000702e5a8200651410f00385485013a07a01c2e1111b80c2c0c0740b6104901042c401c01101ca1038844151001c620440f4583d01900c002c2901c0e18401100b00200c0d4900c5801d042082c240310081005900224122005090414003290050900707554141212040c3c40408d1f949040c5c940240d078140d900002503680c0d14207183c010124110300900c03d070340c1c400900403400d005400080c0505011221119140c10302c5078000ea04e8100c044103e20440c80c180600f40c0703040c1c004c0e880720b503004d400a0044c6140140200014042c06003506c0200d005c10f00c00340b030600035568030154442c0a005401683d030b2402d0703981c400103000040e1140040032410f0b15680c50508010301c1c0074080300116440001e0032041c4c2031254040310b079108000300d10b034014070661000241c0185c0c0400d0b5035000e80344c85 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 436122473 1250 436121223 436121233
    0xa0b04060b0a08030708030907030b0f0703050c04081c090f080601080615011b08090d08030a0515030a0b150402030f0108122a0f030c0f071719170301090e0d0c05 71
    0x159464014a80008102008c80d000d411000008102d40b94102c030302c41d85c0744910301041850000780140807030b400540801e08010007403000748040100007507580d44508035502940d58404940d4400c40d1000e101c0c1d0060180d1004990780010004000a0000e040c0c03404c01007603035080d950302c050b5090f02e04244140b03940050740c24000007015070511481c8000e554003585125252125642c00708454640120342241c0a510010401a210400e489402d03040a003540041c95540751040020b580c944c50352a014103074200420120b1900c1c060101c0300f000140000c0d009544a00d0031001510f03441100f445601d0b1710b402800b00b8220603020f050101c41d5000000704a103501400780f07020144800040d14800b036443d214100c04000031703a5041000c3e0101c94900c0c4002e06904600038403850a1000d540d00c4030300c420795103540308143d8001c00b00c0e2040540141c81510404464181814000d001c596460810003400000011070b0004554100101404c200710884810030b180042c02c40340c8030030200303001c0c0c070795009 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 436123723 1250 436122473 436122487
    0xc0f061e19180308010512120f0c160603061a030c0406080c0d140711030c15040f060603030203031b0316050903070f0f030204140106090b07140a0b04060b0a0803 71
    0x842200c207401e80107960002402e481d8429002844601c41c04250041540403004100c986801d100664400f03d59102a0000e13a01da012445040d0194082801c075400001c150121900c10410150f458032820790b1000b007100d0390b030301c07400340040c44240681d100d0800342103451402000d02d04100c3c1e0040c00d0b01c40c582864a45000021a090b14000d0002d02121004100c900d80495032400b49c000851440c9052074040e040c01007000d000d200d4840717000111a0000e21176401e40300c0300480c4900102e4480c1440500300e039110300d015040640707c2640144141d291510100501d0380c00005103200c0c0030030200c482110000e081e942201404202e0321542d4900d1030359030002249204001520102601030f040710300294480700083c20220140e0002d0109100c040410405d6151500582c603c030324000303840c1a215418003600a004a50768020743d2076401e00001c000c000c02020003a41301784440c0d0f0b003055683d07501e100d141c150b000440075a010303104541815940d42d80c900c4d040501c113041f503104c80001c2d071400790 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 436124973 1250 436123723 436123741
    0x8070b0306060d09150b19050904080702030706020309011b0b04020f04180807110d121b08040e1905090a020d080412050a1202060c041206060503030c0f061e 69
    0x20004100390b070440e405000841900e88107025100c0114031a5000a4010340d414180804543d2000c84040c0b082c0d040640d000306200c250f0000b032007994016034420681d50344605280e07201d88640d0a00a4152140c0c200004038a41d000c000381110384803d030f842c00700b041d00346076800240014120703010345164803c3c2d0204c0d0052900c0c0c12500c24540025101159100c81c0000100855011032000c0d54041d10000da8036003080300900304601095000c41c1e503070f490681561600401412441d02c0002403240d56481c40866104c1da00070b08040542c0300008035562078541d40b00f44c0d610481507a0401c0029200740ca035520104250055074400d001c1400202a00c03407040e000c004544540c0d0380166035102d030822002c9a0000e0800b41b41c52034500075801408192120300d0503c030301c041800e80100854012100348000700405408a40845000d202400b070321138524200701008203883d501c0180e05120000d4a0071300c800d00441c06848135500d00c025180590744811507100c0252006002d5004003000300001f1701d0f061 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 436126223 1250 436124973 436124977
    0xa08070207082a0a030c0906060311120103030c05100903030606021006030506161202070c0f0801090215090f18010914220305071b090507051204030e0102010b03150a060b0408070b 79
    0xca00100b140030038645d81e84070041064440e8102e00b80765031700d40005124498250040c51a0803503200c0c0c0d900d16002140302c0030801014103010050030040c944c4407000500000308103803142c5500b01d4400708484009440c010b00142000c0c030030000580620004c140310120103100d041c0071250041c010304a603907035805120205450b41450341d014001d00b00c2c5407020502c02440034200445c0b0418699041a003004283c00d41c6001e90750081916130304052007000103032182d4140b03480300384d0b241400075141d26043d00040c007462207004259410280f03603041c406c4141c5056810504a4040d00010810500382c11414807101e54122032104016502407040681201c6041c3c0032414103000340b0b801400c00003140c0d60410703a075208104826103149003190074001640107201c2c880d005681420110718010301110780d080328590080005c1c0a002030000441c810744d00030740200c1071940d0f00030190f400c00c20700c1081301845c0c030744240e40040c0703124a09203022808169040444081c0e03200c683c0200001c0b4a04a0324829079 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 436127473 1250 436126223 436126303
    0x1a040c05090f011a07051b030f240705070209070c06050c07020d0807081e031005060702130b030f0109061a090601080c210c0d140c0405040b0301110a0807020708 71
    0x504401c22400c401b042c428804000c0d400b400402c88001804042c00301880c0906071005080e40b0303040051a0001030300d0300304040b10703184031003002140c0c2c03940c0b034800c00d5070b29001c0c405019401c00c0096082004460348501e05540b00c82c0306035410040e9842e000e840c1c00c180e0117894802500007500420601c0403400c0840903284061003030184918210040749013011100350042101e07901c900101c10300401c402d803040040081d00003540e0785030030960b0701d03000980c000710b0105a000e520b41e07564583c000ca07a1020f01c030340d5004400600090004144601d00300c0018400031180444100e9815014802c034030b080f07825580202c10580d60958252112140840603a00c1032061074410006030684011030f0702101052841420404103582d25440329680b0941561030b6000d200041c0b258600c208100300729035401340c8050751400d13140000c2d2030f0011800309005089403292203141c440c002c6604c1c0520783e4090035562003840c15609590610f5030311014181d444e1407a41000381b2000020040114a11031451700c0614 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 436128723 1250 436127473 436127519
    0xa11040b03130804120506010b030c090d020d05061303030f061d0a020d090305030103030f0e010206070c0302031608190503010302130e0a020a060206100608060609010c050304031a040c05090f01 85
    0x5024410f40d03503411203610030380c006032160001a02c102c081c40744c2440040e004104507880b240c80c5103441001c92603244204400e1510925480350418155225149000000c503804011690103040a0f1501030502803032030f40c2100001d091801c005610012800f91100300d512260300d054030a04513200803110014010185810140e080c4a0003a02c5a01c0c3c0c00341101041c000d8484966035415070a00038402d912070481c010070320103105841482079a0004102d0342c0030407a440e0025414080f4075049095204502c58550412640303a070a4062001110051860100703112003150110f0b1825002e541a002c24400070754800195521841e04280a402c0764021402043c1510002c645039030001d00f9242d442d400402c01648080100480410b4440c403150150000d0f052880c41460704000203903da2040e00012410030401c88179400410800b00140c41c0603503401016a040808801d0103a0f45459048405460b480806c69001a503424020040ca0058800101200184e07081c020034180c003503408022900 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 436129973 1250 436128723 436128751
    0x40f05040b060c0102040f05013209010504180204061106011220062a0a0803010504020d110a110d0e06090405060303090312090f0a0e070e0d0c140103050a11040b03 72
    0x19010f10070310040025040340741440c0c00ea24180b1000618040c020b018000b4240e003c1003140400031040351520881800601400b41e64203800c00048070680219441041c030f0151a4000203500c8503c0e40141080e220a555100700c0002415200f9a90303507028821022070b08620501003000c1658187c00d01c01d048461080da00c0c9800e03001021a03039640c44410110400301040a0030749082c10b600c0b100c1d500b2020390b40700400d513465a545a905240c401849002c1c0f10700c1d400280b030083c01c40c003508011805441d032664a510f6120080000d490302003400b039084000d002d000302c0c03062010b003d40000c401e0254054041401c01c41e40c00184001003901528503a81880140034a07445550100720214819001541c0943c13955a4a424402d4140d01d04081c1485200d0100040c00010350511026502101902d840750f441c64422020801c0b41d9040c0ca4098014404584003003a00340701f206505821240a0380d04126070b0303503501d03040c204499110329100d442c0001080100b10322680304002d1a003204050300500 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 436131223 1250 436129973 436129987
    0x171609171c1d031b060903010b0312070506090316080703030b210111250f050d030203010e0a1b0f031104030b0105090f07200f0d2003040f05040b06 65
    0x21040c00c249041d104002000c0800e0701158441809014070b09501c01d60003003d121120640c0040582e001d169824005d601c041440043e40c2d900750402c03001e440000d800d6a04010004062450700c1c1d01000056825100300d07004513081020020442d145410000075031003241030690307a0340783c0b1a485807070103408150310750311802c2055884050401d10301c0409044030400003803c0c050103094544050180d1f00c854400d20480701011014640c060306850240c1740c41e030201076580340a074a48400b40001621501c44c40a000b002190140e0017181690781010b64400c90740d45800e044801c0e0b070480656004100c029100c000d801500411105030010402e003004a5840a050720440968126600a96840020300b004110700d0510301c0d078042d0040e010b00d107500c0c02d600d00050098400d094041c07080c3e8108080d00c1d08070119070828040c3d903075200d0710702c3c0603681700403002c2e9802030121030070110b1005401514000c50126400001c21601125490500100040d28010400c03004020f4441d500d508410100308031 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 436132473 1250 436131223 436131253
    0xf120601080102040819020a03030c02031204031b080c032d0a060c0f0518100c1a0411030f120a20011505060412240c17160917 56
    0x250180210100060b180e07490400b00301e03e0819104941c0e1212007155030302d8805629901500000e9903050f051103244c4285900c0401d1811101004428000f40c010402004000011000f019107445041c50b805413030b03482d5a466515070800c260b0b41d55042d4492520850b4001d082a81c840d417a000c00c00c1e41000d03100e4028509418a1441031040321f50b41e0340c0e400304400c8586c01500070000705505160050811140e07040300b204030300503d01c00b90f00c204404400d112b41e1a00c40c0116141c9030764800e171040c44a40c8405140d52001c1d9050300c0458071100c0a05101c04a4140003407812400300d4440001d2410350001407007502c586d480a20f5400811402d144811402c42040c031901c0100b40c200c00001074070600541301404003000d5604400c0c49a001000b042045503100070421000300e80040d04005d01c0d00c80300b00d40c030702c0f0408500e006074142800c1003403030304d03200e60090415181d90090752140c41131aa142040200d151204040d0000032690140081c000381c4068603000314003038214021501401ca0148031 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 436133723 1250 436132473 436132483
    0x50a030b0a051003052a28080c07020406090c080603060f1905040c0e090304030302100203130212071a0c060a0b0105041a0c01290d0809040b06090a0f03050d0516020f12 74
    0xd062030700c0c140000c0c1f41c0c0c928804455281c0c260000d80904106181c0c0d8100e0086c1204005080e000700c071080070a500d800d40d5659444580144002002004903000844d0040c10120f4201c0d4228400e008174000103845148903540b8034843e41144081074900c540318a030b074500400000e070080e40c64030440c80c00428460350540085018460100046441b00c0c03035450020300e00650703404030f09040c03401442805000d500c012044403000742d0403180341d0005007c01d00f40c640340c8003199004010149a800382d10312080e03290030040c010070320351300f0585e0980c3c0d981e03c1c1e48805440745521f00d5400501c00304400c00918503818043d02651720812010751402c02c00030302d07140c2544c0c0b0765403c91045111003050300c04444800c0c0104043c040c010348907030b45140b13555190060180a01401c042c0038030340705d40f4012500e41d1100704850803020020045e41d205910384140000d2200a404101e50310700c103860100c04601e002c0e606580110411a40c0f00c1003450480e800e10100302c481c4070005402001001003180c204a06100d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 436134973 1250 436133723 436133791
    0x60f14040513151707030b0c0c0604080a02070501051206040b0111010e01021206190e060a0b21011205060408070f21142a07080706050a030b0a05100305 67
    0x404a0191020108a46000d800781e0100c4035221301800f2510401d03c02003500003c4a8100f00704242e40c0d9900703c4401228880c42c0714a801ca030284030204000c101680e00a4a18500c1c6a801c80f030215403110015103591150b9030b0154580a1420002811407400b504100a0f0740c006141144642d0481031201c0e09580c0e01c020b044078140d401146001c050040c150b841640315004a46c00d1124000510000207854a240100c54620303a65130000348080e01c400401e50002c0010000c80da50303d01e0b002c0c260200e00c0c1c40d1241c1401d407141c0511300000b413440f0802c1c1a55910350300300000d4400d64442d596400015070010744100c0391192000c0e0200082081046c40c0e01d0014801c2c206034a01320415200141b040000c820030040c2c0410a0000d80d0910002c0d00d14401c1090800e49814040e060b504242d6251100c20303401000c00d0f101c0e0100103e0003d602c00041c00414200d901c051240d405600d0802180040c10301035207401400d00c00080b030120348a90429600b000c030582d4080001d0200025460f03800c2d10303000e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 436136223 1250 436134973 436135009
    0x90f0605061504050d021e060406090e0106050309031602040f06080c0909010e190807140304061806081603060509070228050c01080a02040803030f06040b010306060f140405 76
    0x308101460610000b070070611515925003528041c10b2000103503100984c81c001a0240002001c9181c4e81598050b00c4500004001c16445c3c48955451000b002042e4602450720750303901d46000094a18064001d42c1c4c000c4010401550424040d50ba140805400c120020f0703a00c44e8649411188409540c460030020304a844080e02c0c0410103d0b0500c03418500103009400507a02d803202c10b00a0850100c0c000d6024410002000700d04411800c001c04070340220f59001d0300603d100c1079070384031031100000100200c84844c1c44421104041c001d0000609400d4880d510106990500103440d050110411156400b60340c1400100d545d1200081081c18008940800150340072031101503065202d04100c011286400e1060b1441000650f9a2600c078451722000358140080800480c4003203015030103460181210504070b03a1030b0304e866000000c1c111000d030b551a014502c1d1000582c2c00e94841c0c0500801d852064403905488001c15004507014001c2100b0a550613000388004a0315944904107424052040 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 436137473 1250 436136223 436136231
    0x5060a0f180f090b09041e0609060e030a1404060512190908040810093804030f0f17070e061204060212090313060e21070f090c09090f090f06 62
    0x20441c40300449403203c011178441c101c00020007002031034a601c101640300c0c003a0000795401045241210181018041c020086070038810345803820306000015054114880ea541c0441a14400145c40c0300e01c5507000c3c0d00e001680c1044802469034190b01115001044500c0090310740095207050300c00c80300301110031a1b0001b00080e00300305c80c0d84100034070b610070404141d08100700121130b07540040d142001c1220410300485038820b07050440c0414547ca034110030562001d0707c94034207031600415520b40c0c0301080000c1072081402c8005c080c441c00401c12158445000b0345140d45550784e0584402034038640003940140c040022181c41000c00c0368403801144588409a2207d4601039080031201c070040002000f83c0c000e004480030036800e00900000c03904642024100381000c0d030041401103800c0d1440003107000c151480429400d80001c0e050040310400c0c0c010351740b941d4039104420f00b51299800c526002650100e030620501c8036075400380c01808e13400321001030744801e607550344075008460070025248035941d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 436138723 1250 436137473 436137479
    0x2060d09030e060a0504170703080c062413091e0c0f080a05060a05060114040602030d0b01020d0c0809030307050712060c080601082208160302150105060a0f180f 71
    0x2c540050800c80044400130f0402c5682ea4005049005030700c100688a140c107000c0742c03240d100c00d01210b006507410480e01c5686050b08946a95507000a031400d4011004440003a050f1516184001000700c4000f000d00007011200a03694029004014003a1404200040745001c401640404004038610403181414850301c4c3c0032001600c0307500f0340d002c00b1554000c2d103010000960081280c55000d817112400040356115400129401001d94418132542c0c0c60005001c10032035000005481042c1070b5950500820040f034004a0311414003400da4004103100e03003010000101300101419040c0070180849040074000c2d20340e185400e01a40c040194110071b1100c000a07c00e680c0a403441d40360050415440b00d0501c400000d10640c8010001898100c140135030140054000e83e00d000200d070843c4945484e051955009840d401c15514124007503c190410009040702115456040300c2d0006c08040c28400004015075160150501d0720b0104418a101c21f80184140b0707a4807030203412a504440f42c4142 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 436139973 1250 436138723 436138727
    0x702031602060d110d06140f0a0608131208060405060f090a0c1710060809011506050d180809040614130c0504092a0305090c01030c23030a06050a030b06040b0a0302060d0903 76
    0x801c280c247c1c0d00403100011b0040080e191154118101d440900e0110016a16000341c3d000c044803008009003000380d044c52801d640c2d40c0c00f19800e800303410101e80410040e2500800c02541c8252561490742240045000910450903a0f008104110b03807070414424402807050381040c0c0c03140450300c041188607100d105000895004101c0e40d400107540000304095681e5071114140031900744600f508010313000481120360704058104a101d250504141e0980c0d140070314000c007803900a800c045029a142020000e00c40000f00c1040421010140580354615008900e80010b404104162010301c0010400010030758140e1040462031424400d4040c1252400403041c8003000404050104160811080c00303200c280109102d100704000342000107107045060025035031041402e410b5545103201510054030001c0201c0110b215200d0020304000c01f5880c0c10800800302c0351800080e02c0c07081058006440c6042942c0f003000d500800424081e50191703640d0008643d0b50150b510303008107075102d04e04842056 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 436141223 1250 436139973 436139999
    0x17010909140a0507051011012316080609072015151c020307090c05040503160b12040206072f01030e0a06090620070b0702031602060d110d06 62
    0x12080000c0d041060b803070384455a4a003010b0103141e202d0204855400d070024000d1560b113031680c020600900907142c8010784901e4104420300b07417203000707102080014954960100000702160850f21414941e40701c0c0c05c1400601c1c0030060803e002e2010060400301d18a42c5040060780440682008200f840000540d12070100409008040721007000d640d40320850780c0b14119039400941c0813081c50100b0540c0d00009152401643c004007103d494950201005540326008000b600c405800300c1c0c00c4000441d01c202031901c01c80c0306121540300103104c03544640e00d2100d0810740040c00180298241200c036150039055910b080b011361201a80a082e158241045500e80341440001342010041c0711a00010fa507220080064024009a59140c5100030805190700c5070322034904101380042a000c002c4028003076540b110505985c00100d88000591443c400800c64030002407402d890360000f20710703a09114403500b00c200400c2d00d090b10396103040d00752815800600300041013901e0205820786045c240d0344542c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 436142473 1250 436141223 436141253
    0x319020c030d0c03140a0504030c140c0f0d0503190309050706120510050306071103070b1005010210050c04090e1f020913020301080d0507170a0305070809031903050717010909 77
    0x10501706140c1203a01042010380a5201c0007503d03001c6560380e65450100c80a8504003401404170542080c4070400020018120003420815504508070010840404c560080e074000000c205900070480710301903884600440122560f141004100b181c1150385083c10702c90b80e608501c000940030103198440454074001c00d40c1090010048805c240d0800303000ca521414000c00d0107041c00b840c5008100003010800450314616000307828140a401d180c401d018000c40b20f449101d005100d030781d404142d01d0b002c52194074000d0020000e01841d061a02c000340e400340051001000d410301480343d601e0f204c1c40c0e0410506040c0c036021600143d44a402c1c10401c44140075040031400c0103803041c40184008000003880d841c4007031250030001d441c0e52991a2000b1800c4501011a82000010400390502c58143c4c0165014240f01d842e04407140d5141040c031640c03401900919420380800b0740790305c1c0d065400707a03008035040002440c2c0b4006110fa542d41030b040d890310aa1000303180c2da5852048901b4010484030801807 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 436143723 1250 436142473 436142477
    0x1030605010e100513090204030b0411121b121504020a0909020102100509030705030403111c0f150e011d0105070203090d170904090305070203070803040503120319020c030d0c 77
    0x100c001c070344002c14141c0880003c4441406400110580e2150842e442000104404401503550315140c0c50003179000202039a040b5805490802c9281131032809164080000303614000800c00c1441020011030201d1030050501d4000c400c84908400c07a041c01d1081143c1480100d920101c0d40c1072500c18049250300c254004403070a40383c07081400050786d000c40d13040e05c90740d44440007040948a1081031400c600c070f8070070001c1040c840010008104400e10740108051501160822043c01000070711150040f8582401000c1d00c2c00c0c042c5110005071006942510741020510000d420082180d80a08541c111406a000d40ca00f8410700c1d03006040901034281e00c400301d4809941440c1515010a08000703024800401c01411007000c0544104a8010344914110003030092001c42c40b0707811f01400a511021040c1d0007401511804190707000300001300c1e0119074002d001800c90b075000b91168402e5400140481951100340c8090100300c000710f00103850120005d81c0030716a541c0031203d83c4002c68450884880c1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 436144973 1250 436143723 436143737
    0x20a15020c120309040b0a120f0c0801110405010c060b030d0c050f210f0f030a0207061b0e240406080106080a110a080405031b0d030b010c120c051e03090103060501 72
    0x1042c160040156a000c40c2c0550300410b604000c100000e84403d000c1c1c20550341065101c0c0300f0310911078003050440616004140d641304658813011818242e40c000150f03902c100078100010001940b04a203541000c9000b510001002030740240024100a007009500c1e00041402400c102400380c103000c500f00d0b43c406803006080d07c8031400c401c195034102c03100c0300a0b650100030440110445040044a162054a9030000d0352450081400c134025008041c0a40d9101c0c6421440c00042600c4460f280c0d40070825103e15111500700002c000c00c19240403412000d0300b040d179a0001d994001500a0700c09081aa142e410656040c120024134044000b0400b0503801d08000300780d1000310310f0b00202c0f61151000d2400e2480c40e502c90030030394134600c60750b9100c011003549640e180031140303408100100c3c1c5500340e81d003c0c00001c51034801101c0c0240c3c11000030f0411060a845903d569000340c03403501d007492150042e2000602d520003c05851000034004428a4200003030103101980c0c1031246601500090920f15 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 436146223 1250 436144973 436144999
    0xc230301060e130c03061103181b0f130f02192a03140c0109140705130b0a0b130501030612390815010609120303020d09020a15020c 58
    0x21102c0302a058640480019044a00b07000030b191040780695013152042c041c00c03c1040c4010715660080303501c02600703222182698600fa5021900190701e0703440c5002641c880e86150304014018100308075070b44c0d00c036020054031140d0740020f024124902402c0e081c016218421500c401d4071085540d40c1810800045e0068800f20441d02c4000b86220031003e04c2c0c440399600f5515042c3c5060640c5181100102404280041d2a800542006e04020311070481e100c5455540412550b4440c82d0703026846c0e01c0464005a4048200d203a408844e800e80e0041c5241c0c1e07582ea13907900c1c40d00580c2c400d040780c80c18500c00c0041404075580600800b801440344c540ba040020405840e402800d03051100b46040e0403042014821818050b4030a5141e90702e510300f951048680e540000302e0340c41c5108040d00c43c0401c4080000035090b8051465041100c44480b054040070312940e0701200258803461594510940c1c0e801d10f040541c0300d40c9029030107040c101070001010a980f03003010340f400c400b44001500c82c500c49001c01c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 436147473 1250 436146223 436146239
    0x2090606270d14100606110a14100212180c01080402040e011b0201021e0306060a052b020901030f050606090f1f05090108180303040b04020d0c23030106 67
    0x800e4169903500c1c00e1041c00351103900000d181003032101000d8515088188003519030742c408a102200410444000c11080303580b00e00c10f4074030303003403805141c2d0440d0000245140411140c08141c11200b0500094800d43c4212000e41805c81e004000681070b03008582080041c07028000307040c0304c9105d081d08003d005081100c40020182000140000d0156031500405940700c1c1c0e0942003000440100b40e07480c04c24030032082009000f0f402c58103802c2036001e4400aa0710b02100d58004490141340041c2545161540e080d10564640d0300c80304103090780601410401c100d000503107104041270b00380c2c0f00003d81d03101000070006007601c607480c000080c0703503161005005495845c2800c441c0281026210b01d00030b580c03a0302c001900780480920300080c0c00981d000f140c0c0f0069014000b401028426220505161901c04d000d41d1010300d03180802131194400c00100d00419109920035522030710041220680403040c0d81c844142521940c8030b0f00c0c080015001c240030840a0703007002d401c0c84e80217800801c8090710b00549 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 436148723 1250 436147473 436147507
    0x1d0a0311070b040b25050f100b0306010302060f040b03042f0f150c03030f010504050907031a0c1c050405010f0b13090311190b16020c12160602060402090606 69
    0x1e1130b04c200c1c0e40002d46084001944c000c0c0442140d800c14038003485042400c6c0b031621061f00e41c00014490007442c3d45c1313054110441c8100343c60000f000d0020140c40e800c40e400e01034503034417000300b9058110041c07000003204d02000700190b00c194451048060000c0079101213103101c0c0d08101003005084220000d80700c01d512090f41e80c04001104560448032196065014081b5208400340004140000020443c500300c07140359650485104ed107041281d030f44d41d15070303064076140303d0b000050140d0310352501040404925500780d84c0000c440007649103458010304004000300800c01c0380003c01d0f0b8403001000113000302803081181002c02c00c0d8050113410400800120342c402103c05c0408804d0fa54080312060621515039290450408021140102c8500d0310010706203c141000715240ca500c440001c00d10860814000f99100c002e8005125a131858405c210203400c406074004103602c54105c1d00c0a0840c0141c07a594010306954024200e01e0509005000c3c010358010700d9540103030f2040002c1d071021025046 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 436149973 1250 436148723 436148729
    0x20c0a020d0212010903110d020c03030a0f090e0f090601050603090307170f03093004091a0a1d0a020a170408090d0809190e060d061d0a0311070b04 65
    0x20703404048001c0d42c40015412502c540c5007000942c0b910b010441099004030040f2100080e102c1240c140c403440400883e0f40b120f840100d1a09504140000800a03000b50414110301c292400e002c001d5a844924403c00c0f09005c40f801d02c11881090144444224280300036800f500c020b4641e00e18602e0500300e8240d69210304c502c002c007400441c0d03101803031a5004000303440003515403034156643c80c02d1408449640e0800342c00004811010030405c1c09030702c02c0d6800c00c00c0c550941820758030300f800c0c03414130302c0001008880442d203110468803280c3c14407550380c0042d240160501790b0220310605440c10003101d10140c010004400b1a204102500ca196004000c41c11700c01c5103002001015039952070002c1650185c3d0205940010b015003007481000901405061040c0c002d45021000c1a00c3c0301c2c061100701c4846c421a0080340101020414a007810b20694141c04c0c040e00c008503035100080c9240c021200c4801545403103400c0090b10104243d07100442c1c030300107071500000b46040c900385590f05695101303070700c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 436151079 1106 436149973 436149979
    0x1a03060a140f0c0d0903120b01090305070e070908011b0f180312030e0610031a0c0d0c091d100902040b1801020106030c2403020c0a02 59
    0x4452400710596900c0105150380711102011004100505410481101040341011550b4140102c0e045c441c42a078800c0131420094140c241150048064581006144c240402c0802c4000581e03406407818001c0c05144e03070f225107030241da454090740d201c64060f50a04200a44c111110003440c032b0318001e1600e60a120b85000c15080381d94125134a0303911b5401052a0040c00402d00003a5110001000303802c0000d0100f400f802418901201100d8110080c0301d003a8052040010031010f07500300e0040c0144850841c180490404481d0180d0070308120441da540d91449880e6100d954284020140303106041c0b911104011100f16285003120340e490040d6540000161840d40c81c400c0798115070031707640c0b0141000404c856698290716a070021604541d06c034007008c40464464012500200300303418a100302c0d1071b081804030030b40043c2c218101090510601032614088004a0f200302016412 = true := by decide +kernel

theorem cover : BRFrame.Cov 435971223 436151079 := by
  have h0 := BRFrame.cov_init 435971223
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435971223 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 435971223 ≤ n) (h2 : n < 436151079) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
