-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3277
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:11:06.621178+00:00
-- url     : https://prove2.me/submissions/6f8b69b3-10fb-455a-9e7e-8710df31e801

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 589208633 ≤ n < 589388489 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 589209883 1250 589208633 589208657
    0x603010b092403010612060b030403170415050a050609070c0803180a060615090f150c02060903060a0b12010603120e0a080601090603020f0108060114160c090c0201050f190c 76
    0x25450185018282c0e86c1e540c084d2480c01510064203c8009400075031101d4421710400000980c0b10308001003014100280c104152503a20b804191414201400c9000c03504260070090440355039400103101c0c0f002181e2010007034603080800d80b906d250134040540060700c1000011645407007465520002c0d903a40f012a141ca12040d01ea0404079180e6400c100c00352034955040e0342405a10000c00d2014189881c100720090f03242000d041400d010341007241040c002d00c80c104c6000c0d0755508007510305615010301500e0203441e2071643c01005041d00001644114103004c4103950040052003024207803a488111380d101001e5980d021703565004545c820740e0380166111004200e4140a0000d103000706a0a0300106042d2304604c1008000b030101c401890400c1280820803180b603070711803004900004420189559454200340305540b600000f60058180c507030201c0000b0740200d09134020705582c8040d50003089252a40e030513125111800f0344608941c1507800c120071a40350003e0f800b13803400141c6418001c100f40340b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 589211133 1250 589209883 589209949
    0xc0512030405180403030b010203160308060a0b0a0809060a0b0a090b0415080a12050711090711070816090501081b030106050a0b070302010c050f1e040906230603010b09 74
    0x54925421800c10080d03801340810507826008206000034240090350034110180e107801c10341c2c05020809000c100c0400c0101c0c8442c1c41c5c0c0c140d0301010b8000760081c0ea545010003030001d80183c030145c400c01e28600c03504c400a203541d807442c420120101c000034207030035109150840c0840a0000444100c5d0b00a5403441d80ba0300700b50224400700e00801501014043c070781000d05003030307034041c0d19032421f0002d00204022000028505110001c0720046c100ca480e100ea40b01c8200841d5400e074202e4680640c3c0c0f00da05c2c0041221200040c09550010078020a00c00484d11043e400c81502c000f0f106118240d07000d20408240384100c4c0840c144807038409000064010b94400000745410041d9000291100000401c0c409259081c0a031080c0c0202c14280700740b81440f100814220382c841c00102e540f0000d94003501c1c001c1c0c400d0000c22600100040c00003484a50303210511011034260600d82030b0000031842084a030b00341802401c0d40d040740c03061038003141440424810301c8240c000b401d066030341180c0c00c3c0f090f1601c406 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 589212383 1250 589211133 589211149
    0x303080a1416030c03050c3007090f0f080c0607110604060f030c020a0b0c0a20060117011802060c030d060e1e010338310c0512030405 59
    0x1100007070000b940c86840a1000d0111104400c1d20010541840f003008260300c004022100e072070f4104240d045403090084603444110032004002d411407140301e400d10800f16807010a1009680d50014222201c5950b8503140c91129080d1103941259089001c1501c501d00d8a24041e1061074090440040c1d0450903600207880d6030b000c0d0300a003012504c0031001d104502d505224141a100082c00102800c480300d444000400343c0083c0403000c0c00000040140f020b603c24901e111041000c06803d0204e44404c141c01e60716441c0134051070f040c041e02c3d9100b21411410500030070411003500206003100221036002d0240c1e0303a028040c220140d110410082080e802e03148202401084000b4500b81c060410002c4d4070409815820380e0f000c50391100700140302003100c29414100c01c00420b5454011864001e035101401c290200840540b0b1102c0000c00090420003c10300e504020100103903410b4080480304030a4002810001500301c0b1440801032155040c000308400b0208107240480303081c40c1d03841000030150 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 589213633 1250 589212383 589212391
    0x31009110f0a0c150e070b0c0f070e04020312120c0702012a020411120c07030309050d0801081e0a03121e020d0c0905060703080a1d1b030f070303080a14 67
    0xf82840e0640000e00c54514101c01c46a0018034080c040c8440901c42155144180c1c01405c4da007900008842460001c01c0040d205030700e000c9020740d915540d40d500c18078050f00d011581a03000e8010610001c0780c0030b26203001c036056294100c500c502903445004940b061900f2141d0224103000c0344c000088007031500d0402c84040001e40052609104d410392050000b6070750001540800c00c2d8080c0003648510450940007a4000912440c03203441d0645800c0803000303002aa00047c0c01400f0b203403141805964401c100d641605d0651084803a441d210204a090301546645c0c642190b4200c4040400000d1181c00340104244020300f02040603422a400e129041070b03500c1e52503490a0740080c181c52019490300071403000d1240c60038000703c528a004080341d0640303e508801020401c00500103882c680e515807204140716146e200203102f2034000380c41c091740c8480f820341c05a001110402c0101030340c41c00203401c0f040081d041010307044482c5584d5054070760301030160801002030b072900c07282d0131414110382c44144a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 589214883 1250 589213633 589213637
    0x70c06050423011e06050303070605040609060c081503030901080103151d0c1201050106080402010c1506031a060d030203270402030702010225080f1b0604060507020d05031009110f0a 80
    0x540c130701d0501d644816082140d625010b550404404200c1998040180c98401c0e81112000c0f17070307603603882c078100300100b20300c1c2002010389152030b01c5220100ea0140c0110320804281c00f541c3c8402580408169803030062031071840c00546071000510028034101c1c90480910341c014000b1134007070035210a0306d80705524601c0c030115540c04040002035919100805045050b9448000c01440d410090700400c03842d401800a8103104014041d4402c22035a0703081210103403005502040b08680b28500000c02c0e0304440c0283c1c03507001d070301000301c0c1da50320340955110320075076054004510302001200c0d02c00581d541d85409000703041e420003082259461358001188102d503142c0c001039507a100b00c2110080000806007644150403881d090000203800307501192100805210102d0300d03540700141c0e0b160303e9042c5c01c0710782c0214040ca5060104000803508200d00400181d000e58031000110b14044a040c00700711480101c1104001c401c119104071759101d900152300c0b0b501441e190072038091340284998841d03042c03000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 589216133 1250 589214883 589214891
    0x120106140a0608191503150b09010b032e030203060103080d0c020706050a052803090227040b0402040b09010b04091a0f10020304050a0b0702030114070c0605042301 72
    0x80c40c64120340050161066081088a0381000b43c0030980d241c884000c061241030f6640c030380045220341e600300a4029640a61400a404c40708a03409014048c00e050340e0f07000b08814400800c2018000d81603034460302452045900004d4500031182c408213031442c082c900c803038110341e0100144c0c42c14460140a14002c0001a0703036031218414141c100e8a0130044001150055a418048142e05c5012034862a4081c600151070701102071002c8042c5c9410703080344d1000f10342540164992600354121741c02090003224003c041c0e00c0e030000c0e6401038041c071425602003100940c0000e07001130300b01001c1a4000b0300140002860031260400700b0480740c001c2c1c1091400c9107001c1030403c030440351f81c0110b040100760100c40c020021905004a28003403030020226200708a0030751003d150510070803c0c4c0d070082c1401080040722b80c2c0c0d03440d002121503101001c280d00079402c01c43e0100e0074103144154240100381603903036480410480d4403000000c00c00640102c40f0118a181071204010041c1060f40320502034200001d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 589217383 1250 589216133 589216169
    0x30106090203150102010608060c0919090c020c010302190809070306020408060405060702150402040e0c061812070b0417010b03060c030a05070c020a091109060a020a0203070603020702060d0b120106 87
    0x44440f014a102440c1160705000c01800200320118985800208a40c100c0c4c1d2a010030308006500c40d08003e11044140c4a8900c001850403107070f07080002408200d409603000100d11100446c140c0c81100224130301c50480500c0c100c1c180b0701ca000031903408801d2106880f22151a549c0f103a05aa01961041486510600c14001803120030720516812280c14001020765080b92003048107811070060010381724a41c1c03554070b020b08900c14004260501c1c001004a40c4c1c4030310901588049203500c8010364024001c00b041130701495000189503041d1080000720342d043c50b1506078200041000f405880c08203540b80c01940010341c808008284c014915041d03090b03124a0b10b91100c10031240c0050104c0c00300881c968818003d0b0322400d4402069a54641001c40c440758140c00d0781c000c6e07100e101e80c916089000000c02d880c01d980e002c034168a0f82803081b8180c03450709075a40012030590080074030195000c94101301d021549480b40d4040f521102000e4100031545205d03000560071184180d00c5020f00140344c500070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 589218633 1250 589217383 589217401
    0xf0b07080f0403021905030c0d021e030c0a02120709110d05062d010c15020318120a21020c0a020a120f0f080702030601060e0102010606030902030c1e030106090203 72
    0x403503070080c01540344035458038103a100296a0b900d80118109030b0b030000703450b000c103110302442229036404403d01201d19000c00b030b410081d0303900f88052f48161504a41d40807911010008400c441c5034284400c000c002810041d000c100c1141924115210141700d4000001004032070703801160600404246115102c143c00a010426140010003141c841c54558408803411251401f03902420032581440d882e9040a100058421801c0013a003c2c0000034040c0c291500044960000c40c803502c80e000d00e001092a04501031603403070600c1c8144c06031040741448484c42040c421800405a010520980b601000c074411041049a10004820010790018403060003541032100e001d1000708954918aa041c0c8070780e480e8241c2040001100800700c90044009805208030b0800380d81100c1d0300202501c06a507520003016100400414085026500f0818009101c0d40688110240c2540180150444800441c10450380440a070b00101000b05200700100d05a00c00344181c80142410b030000582d241814006 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 589219883 1250 589218633 589218647
    0x71407030524040f0c0810020c010f06051822032c061b070806130605010e04080409052502031317150901110a030504031b2001020a0f0b07 61
    0x159040b4581400c28031104441d881e40740950180c1c02c02c02c0c110700840285001d0350303c0300050303008460900c07400742905082c2c601580148003100400000b0440c0000103604c0e00151039003840b8059005030186d2040c0c1d44400040c000c150b0141e0402c401e142c3c0c5038403070000011a0700c0c5904003030740002c0c07601481c441c402a0460440401e8241080010201c0c1052400500c4601c541c0d4402d45c03061441298020510100300890302c023801e6032000303940c00745c50304035030480e444410103400b0f0311154201000081e40400c02c02e03180b070007550092092031a00b401c18504001070003020f4246005030901d114402041e40c0104c00884100a10383d024650741c61118400004403040ca4000e030941005240c03080981c0d8400060b8421065552401d0000356903039000b240d40104165604801c2ca6100011403085c46a419402607100e07034440e0f22110303500c14029017168007010701e000004108003103424941e1026900e0f40c0b81044100c00c14811100c8600542e07880d10740618502c001110540414006c0c0080c1c250000c2c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 589221133 1250 589219883 589219903
    0x1302060f031801091a09060f160e060a1710350a200402190804080706150f09020a0f140c0f0705011425060b042c19021003020714070305 60
    0x4001c001604040c1c1000c4910123001e0f0507100d0b07504a81c0007121007240522400400315030014400c40c5c50359891803000e04241a02206500c504c0f9803007001900110884441e1002c0e00c9905221090b0090403491140e28210b9076071152011024484060101e44000c00280000a1184c0104c8006140d040b02484ca40c0700710241072032103140180520348141c107c56102394140f007c2443c6c6994151102c1c14014003520465801914990401d22070b44160301140900a040b0f9002c02280440544d80e201d03c03400f20701840c180c52000500d409100176410340314000c2800500700e04124103242a148402652400b4a01d41c942c03901a0400038040000b980c128819258010100220500d490030700c0f0b070322a288032040205c221100c54442e01020901006600c5805c3c1000301504c100540e040711960030840490200401c80218086400c080c66418085440515007102c48481c41222103643d0030070503680008541241016401e101348000700b2648103503240c0c400100c0000e80300007425424240d00741201c00d4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 589222383 1250 589221133 589221151
    0x10e04060e0a090809100c020109090c08040f05100f061e030206071401020415081504110405150c010617150114060307030f0614091302060f031801091a 67
    0x84010080303200c00760420395010a603881c002410f0340039480c100c41140901d440c0107401c14aa041b6410416400c003403104107580c000d80721545c0c029078843d549800e540b040384c3c00000103180200441c0c0002c60b2141c242d46020702c1282a1051a1034400040f000c89254000700070400b601c541040140b110302c8441c88101c04504072074500005d0458002c250144a8500c004100342e10010468035888020740c1542e020b0704c00d02a162640400300c1d000200040c00540b520410f100b46652000707120702c0c152042104100314840098209850201042180b12078418401c000600420040c0d070800c2e402e118408c09012a40c01c1c444413512000941c900d4090109035030b01d20442e54800500032403405101451254a044030180d6407903441c8001107000e0f0003003096008446042c2500800d40340070402071000c00756015200060b00e95101d82d40ca0745040070781400690040000c00100403000d04c00e4004550207030209040c141100d0708070900c5403c6038898082610500c041c0bd000c01d8a00d124200602e400401c03403 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 589223633 1250 589222383 589222391
    0x123060a0b1909030f0308011d1504020d0b0a030f0311030309100e030712030c0f0327020d0f0303051e07090b0d061d01030c27050a1e0b010e04 63
    0xa2500d11035105007140c1a071003280790481003100b2407140b29980d02441c0d104990b081010800d1070003410022080c0541204103da8415510344480d10b0560030740b142102c1d6600d00305040218007480000e600000c0d00001c45900d030b88821800c1d880d17000032400254880c1403400050701660500504c040b1114000d800309400400a001001c400082c00c003072891010800011b2911507040418554405c0000c020160341000500c0c40039280c0582c00041c2444154846204908001800700d08550400310340d080006660214601d66400c2880c1c18602d2900c080e00824914445d03444420541615a40c03c500203511002000500d50282e004e80d10180e50f900b203800d0b42c030f050514015210440502079000b1903c8085040507a0a400750403160080c401841d8050021624540c4140740751000d000545117105079480c0010760164070004000f041c441c261861040503414118a0090480a8509840b05031121045d40c007140c11801104201d4094210010b01c0b1b0400c41c0c00941002c0000c0b944920503890 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 589224883 1250 589223633 589223639
    0xf160815040c2709120f020d090e18100f110f1608090a03060b180f010b030a1b0e211b27010303030f06060e0d03020705030123060a 58
    0x1a0052030082e03c00c1e004850030409101c070b0400e9a460802c1c0c000b02e06490404083d50240130022610881101300f5030b84101d5801c02a0f001a41e440d5440e02e0302c00c2c000380c000c0604115a44c2c15410a942102500e5094006104814010392902038540100070b222030f55101504c6c1223022900c10081040c4801100c141400d140d00d2500c01d050040e8440342030340c010480f0743c00d400c21910408482c1c51200052401c040b49442c0d041c0314004001240035180100e6000340b2800c4004d003800803061241d07500c0216101c02c1da08100c8500e0003500043c08a416007911699010008491000d9541d9901299034810403000c098130b042003201148184400c0500c6610000c82c0503403400401c11140340603641c0901a070603880c031404940b45a07460501103c0103e510011455143d500b5060135048900035501402404200d00400d4207c6400d8407400e00411142c8500e110780342401d010302d0103014001d0060711455a130b907101107802c4d1001c513048014040a00c10100c030040b00c000a07003d4014000761500012242 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 589226133 1250 589224883 589224893
    0x406110c0a0315021c05010b0d2019090929010c120c020d0c060507120206090a1728020d0c05031b0a0f03020312070e010c02040e0f16081504 62
    0x69039462183c400d4000031403503240b504800c0c0c0d0740242616000200800d40c1d4403070b01c20030650040401c4500240c2030030560b03c805d01c050f88460703101d0b10f414030f90b8514106444000891070581040840f0520802500c0001c2501083c400c2010142c0d69948040019000e0380c10078201c0c000000da42d40c1405444522480400c6147c0c0c82c0401c240c0007402d24448180c01c90000410811003c007000f00010f003102004518541e00c64003402220b07100c0e80940c0d51646090a00f40e0f10340e0421596440c00f58410240c2c0804a00520114804217030030010f0b00c1e03d440c1502002508044141c0042c00c03146540341c3c6014090f030380c100b0141c868000c0c90300d441210448207039185520f0748503990070600e0240324040305689081c410300012010035402000842240528a006900c076000315450f0284200c01d040001d100304d00a000b10003a0f08816034405440c18815403c01004222400d010400c52244111401e01c200d000c02c003910109030840d00c0945d1043c074042801d880c02002100169900322140c05101c0051 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 589227383 1250 589226133 589226153
    0x2010305091903030c0504050a08010f0b090c0706090212030309060601091712090109170c010306090b01020a030c05030c0a050c150a02060a020a03020904140604050108010e0c01051e0406110c0a03 86
    0x160f0b00d0700e004107000141d03020071103441c000c90b00045d80c010f515085c0017030010015071044907051140351041c007581105000300082010121001d400508d000c112000c0081d80c25804008403e100410003046021100445440c41d001128540c002d035201d9002e1000544c0c0010814005008402d01c0c1030720403100440c81a15a0701107078030601031000c042a40d0a50340e002d12101f0028203005181d1115482d103000b4990b9441c240b480a050100b4a41980400e0115041c095103030030340b1068000300ba401e40359907011203068240c6030080e01c00340002e00c80c90103101020f000810180303004e500101a054409010400d2a03c1003172401548204200aa2a00d050f0040380e010303480880c0311b100503202e000b407810640280c4100982e1543c0a1f150502d1840d11803d0100340902451080d242081180c0c5c88500e15070072102e4808052040c2e41c40994920499845040200781ea01c0101c046518440400f90700820141c001e50009008642c1c8a40503041944c81000102c001d240e00300c0300304c0b09091554440c1b00c041 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 589228633 1250 589227383 589227433
    0x702090123040515030109051621022e0e010206100e011e03080d02031e0c09040b13050c03090d0c0309050d110307080304170a0206091021090201030509 67
    0xa5a11800011010b625140b07642c0e92420000c1c0c002e0101c1c2c040c03490059110305604034274287c207102128000c00c0000c18003841a804481c1c0054030400010580c081091201540041c1c8801c0c9080c03102c44540c0b000908410305182e01c19031079812032481d00d01c1c006800e120009008013030315000d0170303000c100f40300c00030600070b044410000c2030300b103074203c00c0108000c40100c6400180c01514009000041c408159008503c0340039903c0151245590a802c0b1584426003502c200c03042071018051300003d031030a82d2200d042448000c1540401d901c01c030407148281c4108442c0380601c0d1a0110403c0000c10042c020046091180e2405e0030540c8480c0c2d9016100c0201c07401414090030300480f0170030030001081c801d0128100d0040880d000c441d40c619086582e5400b0340207103038601c561084d041c00101e07800917201c1d80d80d43c0e0081840b0f00704407125062051005d1316114030307000c0020300203455070355400b01840184200409103020950f09000d00000d0301740da0000e000a0619403102d503040038461545a514400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 589229883 1250 589228633 589228639
    0x14070c060f02030c010212010608250e040e0111250f08090402041211030f0f03090d020303210a0507080c121b0a02070f05030313090e100906020702090123 68
    0xc1c0108200100c0c41c0d0f000b4114a40002c0d1320004618101581c40c00110b41212210b0342e91403501d558800034080c0302c200e0003030601c5000e00c0c030560707446025000b50052100520f02410000d0b00031003c1001c142500d40b420760a95075144001130700b0018049000804038103102520800e00121559a900c90145244620281a528000c0740c00c80c1d4555031601100c00401014110744551092800d101074204200302205210348203885c0030f8001800c2c046108000c3c40344141c0550f00b05072101e424040014003070030040340c0c117000030003070004240d0a520390810060ac4c000740c010403071b1401d146258110b400140040050110100800141c031302108122000310a40034810784050703c0341e000303070380c1041c488101d4002014000714403208159400a008011942d0120400a0080c0e6600c00e2648038800d1040007030304600f13808801d00000786079402c880c1d0a40e40100854034100b000c0d60b050000c6400c4007000702e440c41d40018601c415468140c1c1d0890142c40c1c00c0640714078154241301c040150b008800d880e940 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 589231133 1250 589229883 589229897
    0x8030123031506010c08030405011d0c010c0f0c09020309030a020d0309020901120c080d0c0c0e010e0c070804050a060e030105061914060c0a06060e0c0a0815060c100c14070c06 77
    0x11980c1d110f240c008201c10390141b80c0703d0302d03070070f00e80b40143c040c00c8040841002c5c4d40891030005080c140014081c170801c281a11884800c00b460740313908601d102209810740788182642000290340c0110300c0210b200364252030256450340c80a0000038182800c900d000ea00705410119802d0160741e41600550440d08101c0c40f44142030018034101001010726404030b00603000350240d1500c1c13190071043c10b81e5114800da1140310b400f0b4540003d01c1030003c082c00b8041e41c2c4005140010701c0c0c1e64812006200d840d00404040c0c0c24241e5541c0040c0b0304c05200d80040000804030313100e0740d011342130034050385422800484e0105514030311029a00042d2145116800a42c90506100303001a11100304982c4c841d040310094070079560050504201604540c45244100c003d140000344009400d28103448540da80c80ea20312245450744456030201070b11200c4001c1c0d00200c100000c0d00350f03c50800c280b40580c40c00139008598200008005403c1f100c648503c016080c1d400c2002e0400074901e50600801e50f0906c2c10502 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 589232383 1250 589231133 589231141
    0xe09070215010303031a030601120f03020319090329040215040302060304060219141602040b120a060e070b12100e01030c0810090302030d05090f0a080301230315 71
    0x1d192031103501c001a608105600048107140d0b258124500e00740146800c80900380381c180505694840903c56540490300003030120000a074400c0f90703401014002e00c100c905000e0115601c45c0340e540384481c26008107036800700c00c104201c0c0c510a0584001e8402c2200c40044d19410100035440c00f004000034440c00000d00c40042c880c01c401c090302c010b0f58000d440c09443c2c0c6014641403009501c020b402001d0840040907003110b0612582120143e0580b00740c085050441d4020108a07d904181c02260301c9600c0c2c044a114035141c0721000d805c0d40c0b41480081c000b040180c1485004c88100144030f4400b07400003101409021030391011110052070341840c0c074045945a002e0194148c10641107451141d624400000501110048600686601100b91034903081009218070486184100040c056002070044460440c4680d0046034801c8240042c0c40060a5104015040c036000842c2201e0143e03010005100c1c020442c2444003007103070505140400c00d040072000a540e6034214818500440c01e80d8001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 589233633 1250 589232383 589232387
    0x501080607050304052e0204120501140702033c0306041506091a16030210050105240c0a140106060206102d2718080a0c1a04050d0807030603030e0907 66
    0x120f08462214031045403201c1d20707400b00ca103840c020031070f09a44940c20b00822032132801c01c00d01c0540c042c1501e030300150301e400651402c95405001140e0a0080344000da2241c0e601d5042a880d041600280862140c0e5249040b200300002c40d0326414d060350800d00c680307405011982e00600394030107a404e016482c0c41490340b03200e41103006c6e21640c011221400c100c03000d40020103800052035810210380c50000d10030342c0c1c4c07580c00740090400c85052005490305200051622048101c00610664a40000b5104100b0040d02c03041c005016500440006030b42d80c900402906506100da0381d00f00d50401100e1014034074241c1c100303007481e11030200d405001455200c0040142c00c803600400c0100701c06020b07240c6c2840340003009007851003414403c61901e1f00380760200011404003140201c0342c40d400701c2400d061017407a9004445540404904403210031805c3c000c04501d50360000e03460310171b074400d0004251807002c035030004140c048082d2440050500f131080600019410402c2e0350b0000740103449800d203d56a182d41 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 589234883 1250 589233633 589233703
    0x1050c03190b10051c090b090d030e03090607020402120f18010501080303063106170c030a060b01021002130302010f1b0f020a120c0e010812031f050307060201050108060705030405 79
    0x100d017101807900e141c450405c100750941034481d40c012000e0f11301e4075425001c10307001e540303642d51602c0d10341e00100b00c91842031420300d015104141c000341c001810b01340103200000315420f06441600701c040486007008201000703e02e0404928403000c0091010394903000c07a0f07903682e0101800a511801d902440c2c121010400e055802500002645140c08d200b0300c1084000180090301904112500b208003511070604c0000725009000400f138000e203000c2c0e400d0740340d603070003070030440b640c0e0b81140105032100301c40d8101c600107411207040140025a00034958030002d410320440110003401e01c1030f4160284844096961880b140c183c010040401e9081701e48005102148140c00440503030100e41c043c40c052042003401ea03015075041405048150340c85440055541d244880c0301928603034100700042d8030215404511460f80c80c3d00c0385c9150340e07d484100080c1081543e400c100c0040c8e5650300104400841042510340018003400c04030b00cac505003910354030b4950b000c0c0d00c0c03e04903842164580940c01031400030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 589236133 1250 589234883 589234927
    0xa0212160e0603061e0f0a110c0f16061707020106171006060816120204030804181514010e0d02101106060a0e0f070c020301050c03190b1005 62
    0x110480d10940c8906442111090555a0038001d02c55600003c2865060702c459003440440740c90790b032115980700c011100c01400010200700c0380640350002200d1800c2000c0250122040e104050004120518003142c9045154454410303a102c0a01d01040b00c1c941101001d006240c400210320310707030b43d0307190301c01da001d0a01396203c0c40c488039442c070340540e40391800301e40d8807400351581109009465031108200d0f03a420080d103442864000400082c0300e00c80c01080d2034501e90400c800054201a903980b20501c103a00154440d40080f032640013401c2840b0f01a110f40e03466942144880d03106a81032410b0031203060b003010b440e00d042c40038901090b01543c1c1c50030140d09800e0f0f4000e00e040600342454000414042d601011094070b071140c6c0c400f00301e05241207a032020540e82d141d0218441566aa160070b001e02c403003d40800280b0880049440168034280202d130700c02c00e60b030003101c5d03982e04004401d88179045691100340780c20751420540844070340e01c0b48070070f0f94000503620b8403039204d50244d00c400d02c40d5a0408 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 589237383 1250 589236133 589236163
    0x2040b070b0103060e010b011209021c0321020301060c08030a020d0501140f1c03140c060406150b09240c07030b04030e0102070f05010c08120a050105150c0a0212 71
    0x100c0c280040104108032141a644180c4040c00390000042420b42600c110070890750108100c69545090101e140e4000b045040c0010040c038031295041d08a00501858104103900051031180c4d4104200100b403060865092007002c00c510355850054002c1c0700ca40c9130b4034000d103090b00000100f0602c142d10380550781007005044e001c00030355a540e4814907004480306442c901408500407a0f030768510300311144101d14240d00149002041c0300d43e400322000f1142041c01c010310032050211141900d0200685403040e407061000003101d012a07011000055500c0d40400030340b000800103004640c5545800041c0b03a018078030400c0454129109c0c0e08544e009000c00d100581c0318912002017445045110781c0d0240303001c3c3d2503015a45032400012a2a59580d00600f10121003045042185500c1800500c0c00c9a001e0241541814000129820003060940701084050346560060101c0d141100f841502080301e001e09074981810f6200c0c585e01d48054140180c0300700c0c01d400f51204031403014003011500313a07429 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 589238633 1250 589237383 589237387
    0x10e0a030507291801030b01020309090f070c081309050f042307051e0f1903081612020a0c09021306030e0f0a050a03030e01180206030612070b220b160602040b 70
    0x218103111584c1c1a108001c41c0003e0130264090340c1da50000c0100d4071610001f401080a694079800c604202c07a5000d0640e004010f00c140b007200200b0329080242800000c0b2003d0021060b18180d908015614040d1100c0c144030311010a21000504034441c03103518086e8503070181c20701003000202c141030580399400b90b504203c01c0b4122284c000c251480c04802608102d8016001214031024069414000c0004500b03641d1100428000300d00244d024000704000400e044450a849684030000307100c0703000c400d2025a1100085200f0003100d0600240170b040d00410031410140104d0b01c40d046850503100712010305640d96201c041d4200b0900c5400e400e45480070031a0b100d041b280c9003040d40d4016514013035000038036000c0114038801040c011510900d518810a011302c5003140c08004055001621b9198481100b075440680300e801440000000c00540503141e03110303480c11200c40c0441403055445002103171264414402d070040c40c82507668406c0c2604950b880949075140c50320080c807482d04600403080d80 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 589239883 1250 589238633 589238647
    0x20d0212010f0f0504030c02090a02071e02040e0a02030c12070f08060f090a0302060109020d021209010203011a090d0f0f1416060201140f190f0506010e0a03050729 72
    0x15001050190b141d80010405182400d280702d0441e8800d0320f00900141d40d2002a00241c034014140c175401c4201c0075401843c00308507076034103242c0340f014801000441c20503c842c5020b620745445440542c00903403016002504469000941740ea64188119101e40581120300306d01000402060002c0d0181e00c4401c100c041d00e40030841c0da155030484040c0f800350382620001e15020004a035442600d68590010b0006074240203080e4082c0d04052100041180d003403061442681010041e00d024181d1240010f07a2541021310700b1025400341c540c00304081e5810014982262103420f02210f0203030308100e41d42c4c060441172900100c10110080081c1840c03d000c400b941c2c03a0784010036134030512590702580c072140f25a41c2005a007607603070381d000c07102615500c84001603040000381542503100c01002c1c044090510025503060440302c108a80142456036403040060300d50b0821014803143c1c004603400380c902480d643d0b0f0165118800d00407071903007541120820000b8000c2c80b4a8140034021298165101c000d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 589241133 1250 589239883 589239919
    0xb130e03120c0c160e010b2b141503030912120a0306080d110316060b10021605030307050a0f031806021524010c14030a050403050705011e0c020d02 65
    0x3243c00120001e000716650b103041188885000d80840e207615844808681c45e00c1704d1048150072600307007468184051510a42840c060b150f031201e440e255020000348030b0310503c2400c080d004004141c20030484101c8207162055a0010541c5c00c600c8040703c510380c0c141c203040003081c24001c202d10086900740020034290440e903010b800607402c1c0ca0321001201c20040c030000049500402078002000030381c00800000414110703440b140040c4a000381c00100d0355510000105a04d0100d0603401c00050b008000d0a002128518513a0300042030210011030411005446107601c944664070018800080c00d072f18001058055403c00d0f2081108a185a00b010303174409019482d45084d00c4030750102000000050b01d1050603c448006011504040358203006103180150b55101b03040c24184d600402c0384074000c845680801c014181c00380180d0f9910f132514610314060b80390080ca500128140280082042c02104c04143da1600c0f1004038602184418410300102d5040b03a07103010042e401044901e4540c0b4082 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 589242383 1250 589241133 589241137
    0x31803010b0d081c050f0402100c050d03060602011802030d200105010b0a030f1a0d0201140f04150c0b070509130e03190306140108090304080307051608010b130e03120c 74
    0x1464803515071007013550f0b40c80407411140121101c0000311800c40c0814050f040030415202600310a0400283c00b1056840309407030903110300b9a9000190700c85d441848140e0703080c00f0b2001c000c054034440740510501c540c0040c2d01c40c244401180e0800402c0b95000e403013034101d2081203e0704803031200200318039611040031135816440f031103031000484d0414207600350000340d501c01c000031440b02c021003800d0102805c0402c02c42c9100c00e601a4100405100040c051602c0301e0000e1070290843c51040e96074a161500348051559002d40c2001804144c8000b071021404400500e94064114980140e80d01040e00c0000e1884c40b40403a00c8000c1881c00c1e1600500000000042482580000e1040c240c003c000c8030450035502c0a00412505400b42c840c080060b502400356190000c500409480c00e10ba00c6809041c03950b005540c05583d1a400500c074000c0402c4003818801c060000d84000b84294860345012403520404001e8181e0704541d0b68100c440844010300a841c0008100b1008903c14203100c03114074815 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 589243633 1250 589242383 589242397
    0xe07020316060f050606391504050c0105180103180b090709050606070c0b0307110d020a031805060306010f1b0b0105040b01090302030d0804020a1a030f0106030608031803010b0d08 79
    0x4503190030089545032406d1340556036002a83c03194822090040740c0700c003050020070000c090b4041198041200400c0040c001d02000c20813640045051340b03070a0510a142c20240f505040c144142001104850b500407007a40c0c04809003804c012801c04141600340f00e8601100c071000d0454000d41e03040c400c0d075030001300e174a000703c078135103041800103458150803c0110312a452006280220481c41000122820800b950b440b42c1c09003400c20402050031000b6040c1410b1101e00d10050300000e040d0300030183c01010702c0c0b40b4003042640f80d8201c2824400480d80910000e4074841c14010850600114240324560041e40a8080c1d00303032418104052500072007243c401e014162003281001010364265118032003003000c8a4000b8014644d84140d0582035943d0000540305030b8001e640b050012920b4948007100221243d100700c4a580d0724580001503401c02c00c81030f0441380425040400822032071070004107440c0406401b4074440d040c20030102c0002e0043c01089281901b01a981401105001140c0054852 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 589244883 1250 589243633 589243661
    0x31212020d051b13030605040f08041d07020c0108040b06041104080109020a050d051203092b0e0f060d020a050d060b0c060106020703030c12020a020918070509100e0702031606 77
    0x20b480c141c43c030311802e90b00800c1003031001c2034110602000419020340010b9041401000358424062454032602d41c02d5105401946600000d90603c030410100c20301ca856000e83c3c0c5202609403c4a0380000030705a4a001d0405060247c0d070b000452a1943c86901c0342e8044401501200d643c2c50355401c4482c040e0006507000c1c5e1040b0092100000c071800d103c414900b035194410007400300e8400c48101c4402076000900716100c98820090000e2aa0082e0561421140050070110803c0d1244400003406440e14003040d60040b00001030042851322684c065401d80c0f003507003001603100c0c904120211450b001e1003030320020709414804000f500c0314244000384080546c600c1070350758903038803a44142d0f5585103d110003000104900d140101040ca500203491183c42c041c07043c0c0d400d02d0321a030000745852509a4119031807011800703050041c80c1e81009a1401410103031140741c40ca203440d258910400010b440744099030324009000824180c401e008441440c084c1042c4516003031200e080c20b000800d100f1041c058 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 589246133 1250 589244883 589244911
    0xc0a0c0f09020c0d110a1e0c08031c020d0e0a0f051203092e0507110d030e0a060b0f030703051f020705031e0d0e01021305010507020901031212020d05 66
    0x1070035030114000c8520306041c01008100e40d02d0424000c0314050440500d420307041c0036005581e40000c0c005083d9040315404016000c003540058108505104d40c0d81e030010400f83c1c010480e9521620031a02207a02c207158480700141c80d42554030036075016294060b044c12450003525818401c00001000141d8558080c004541341014110204001c600c01a100c2c584541c2c0490501d680000a80102281a2500c82c02c0d00301e030001105990407d84105031400b20214107142030354500c40300204060f010380611494107101240d01000626182d00e52510082c120340e49548440c01c02d500ca0214400f179004014003110829603803818803586855002c0580e021056035101c88084103001c41c02510045900702c0081e528046080500148941c1d02902240402d00181b00040320881d0034800c0e501c0c0d02c10044d00150350b5002d8110500d80801035500180d040c48010711403070000d6280d5400c601c0c10f40e580031080ca100e0220ba2181901d110050b0029002c0103030002504050100c51034018501505035821085 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 589247383 1250 589246133 589246139
    0x7060504140106030c1203090f080604110328050705030f060403030f0b0f0409061407020708280b090319090e06100519090f0308031e040c0902090103020c0a0c0f 71
    0x1d400c0c0c480c1880054401540201c060011442c45a48a022984030341030205c0120395030709021028140350b6007c801d00f1340104c03042005100b8000d6184c010b00310218003801c0b00008101c1807401102030085003210300098040450100310040018401501d0000c046800c2e0b40e0142400c070baa141401c0b00c04400007401e214904600c0b801034041d044421000400c642c14921554040c2700c018015414160764681d02e4064072844103504c8250640266140d502a00c04141000b04461401740425441080e08000c140745042003080c003239109070125070000c1a554140c4402c14407600c0c1d40104080070b108a24140251040c0c0c2d50054040021100300006241d002e969010402801d0100c0c420000007142040091814980711400d00010461081c01d040b000e8a40341d02d50b0009031895508104c5045000105000703201818081410000c8044049000346140a907203520340d5600c944a810041500412030541d01c3c1e000750180d500c1d0401c088100c44103c0f0321818006c03050a030900c40c07800721400c004008 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 589248633 1250 589247383 589247423
    0x1020a2006070c020f040c0e0126010b1b072c090a08090109030b0907030c0e190207020604051c0b09160e06030309060301030b0619060c0201080c0d0207060504 70
    0x30200194090141115550301c00c4280ca04420501049038082e400c0100c0c45610340d100e1043c0b200f060b41540d00e100e200103208001400700d0394502100c5401e04500300302d40700c806284a844a0641d0588244251280f00726110403280101408030659507004081c0b002c5100c1c50100d481b42e0028120207600500c00c0e007a0501c041e54040d040d100980e07607400c4040d0140c04102c419005200d00300e81850034020090340d035150f0f40c24444095071812410f4100c0c50081083c846190b81c080301403e001d10041d2580c4c1004081c6900c12410340d0701c41c941041d00443c0110079582c0e440306540c018500a0f0504078110b450300418012121607410131519400d980c80070401c110400942101074040105c602d50340c05042c0546405004001408541d01d48005c11150460b40c0794200594001d51180c94a9680d50800c102040035048000d810204042200c9900b0800da0798808c0300e811007140c080c2081030700c58a940e44240028858800c040310701500014080d000c000d80b030349c4040e110350f024294148407408080e480c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 589249883 1250 589248633 589248677
    0x30f0f07170403021c02061c0b0405010e071e1202030c0c0d020304050a03060b0d051204080c01140f0309010f0e03090a1a12090109021323010303081b07080c01020a 72
    0xc1d4104026a12000c40c07640001d17101c40c0d40a000034612400c0c00c2208604076506101c0901810407035445401e102c1c03003800c15001c1d007405009900011111450a40c10040032a4084002825950400c0340080c216600500301c004a10361900b000b55078a2415140300c0625601207940c129952058042d4490141d1010013038400f5a003005144103203584c84d51301da400c05003440051840c0e200f03804001d5100014420800c000c50240c920510944a89c6010881c0c0d0400c81c1d1601c03040c1c180300000c6404550a05039104442d12080c1d44d00361640c43c1d0711092540c1e40144440c00141d445a0701e04607600007660b40c0000038000138401110740688890320303080032845a01050b110f14810300003c1c030411510000920003643e000004000001e8140c940d500002d0600c00c184100501c0c0c2c540d1185145021281c048550607070300e45402c1c0d480002d52440d90700070060500200f00c1440030700c0c001c0040c8035001d80d000444240d181c00420741a107415100c0c0c2094001e6024100c1040171074518810b420354200d141c04 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 589251133 1250 589249883 589249889
    0xb04060f0801060f03020a270320100813050a05062e0302060a17040c0e06030102122809060e0708070303020a0b0604020403051e0c0a08120c030f0f071704 68
    0x651301940840948054010b90401440c0030213012000c0d940c00c5d620512500040c008018141c8600a09480d40c20913803000c94070720014000c040030402e0a41d0040d200c0201da00d202c00010320b840805a80e40380305076018115a803000610328019810340c60188003001500c81d005119008003286400310b101024400301c0181610020420700036a001c001614166000e03202c6071a1504100120541100080346d000b42d04075030403950740241d404240154400114015031009003034008625088100760556a00c01c6d0040018050b182e507003089948075005008002d601c0c8210050034041c28030300b468100c01810440d2485d002030310920f900001c03c0038000408404480d0550042d04e0011440d4890351000c0c40000e1000f6006038007048000002030003081018100044213100451080b04c80700c00500b00301445c610244144a8640140140040882c9101241c003042400c07694640385803015038114051140f812400d00c2021402030103c0b0541c0c4010107403a84241c4524103c040301c0c0c90040000d000b240 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 589252383 1250 589251133 589251137
    0x11a0a05100909110c03030a02180405011202090c0c0d08010801050f1e0a1508150601093f0c0806070f090b030a0e07090c080901060b070f031106010b04060f080106 72
    0x240701000001404d601c045510100700d6007a900d804481d1060307900c1c1d035200340c9032440c440368001804d03030341d800400c003110002441c212014001da52400d001c06124851a242c041c1c851110840460880130464003101c0585200e42e09481c86441060005801840c00344102e440b1f550034070b0000f40d8a141e0144809110f08015030188006070b454002800307403814020001404207903a90b008401400c1059a440002e04416000b8059440b05802d51030151402a01c03090521031582020701076050300781c0200c8000c5404002c90707016001c0001503c442c4440e0044001000c0da0030f03244220500000c0340c1004141c486080c212003c030740710900101c80d12914507c0b134038001241050180140c83c96000110b4201c2030502001c18400c5808068078101152588850000d41e40c841c07982a0050f00401202da2026005000700003041c0b43c07411441462140801c001c0c2120508078404041500901d2010380314000001103d55940e110030316211550f00c00e004001c00f05500c8001141b903648204c0605050b03800039 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 589253633 1250 589252383 589252397
    0x7030e060919120903080d2901020c120c0a0b130602030f0a08151807030c050708070210050c07030602090f040209012f011503020117040506070e0f03011a0a0510 71
    0x10307449412040d0301c520103400400c0700c4d1003000004900440041c051a0045041c00150b241d0000010f0004802a0015606841e440342011460340e03008030380c01d841c900c8290b40100f40039060b100c1c1c0c142003942c0c009280c2d41c0132044100c0400da400b400b030040d044c074905800c0e07480e407800d850700c0050380c2d00e01a20542c164013500400c05452a02e205070442c58001c0089a0080c03c01041c2c840042ea02006011030b01000b40040c0341009426a858050040c2180c010b00b8020700d44981c0d9250a0035601c117900c00a0b004403242841e0703a1000340302e04100d803410302611080e1650f850b01c07841c1510103503000d01c102078030400c001040d8044a01e00781c801c54243d1641611120a415120060341c0004543c40c00d900940c0d007820501080314040a0240701041407031101c0300e0403410704520015103101980c02020124034200d00402001030000100142c0100c080d0810885800c081400904004140107045403d5400c1424000345032104030150b21280208841d00180b00341c40e1028803007078030001e034036a4000800c1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 589254883 1250 589253633 589253683
    0x1f02151302040b3f01020307030b0103050709080615030a0807080405031002032404021b16060201020a0807050c0a060c080406050c130603092108040b09120d0b01020106080607030e0609 81
    0x32440d6021000b4110144c901e189880503800d581c00c9801c200c8880c40403d8441646005541e410711855511103520b00b0000a80c40c00d005841c2c0c5c0e290002841d800034601c8050941800d44e808125017205140c1c001c42855071411145010b003129003180c030515000e4810300040b00000d00690003528490708903101c2015480c0c14030100e448031122a06030341ca405c0743d420000000e804024041c070100e51280f0030b00030414014070788070085080c2455845101164414410000310550002880d6000811031034007549a12032406228100080f40b00003c206500d015403c00720143c000c480c0b288180c0c01030104100541c1c0e1444041d615114501892594085001d0300f441440e002c0d0380001e01c01d9005058009a5030b000c402c108019540c510141808504003408200820112224140d4032104440140ca40303001d034801e105080f8014004030454143c0c0707c90140169074400d520030001000c0341003c641e0641420000a002030000390040019405030303000055444000007007115078450340300e5140010140d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 589256133 1250 589254883 589254949
    0x105070903110d151b0e0d050a0201110c0402031e07020a032f010c030605030f0106080c062803200405060d0902061c0515030c1f02151302040b 63
    0x4012004c50f10360f018079880d038030a8075144c031501410303e12103070b4414411110b180010f1702c050f404c02041840f840040703131400c00007030b80480c001001d1942820060310007061224464200b44c29200c24179000303031002c01041020f0007802d080040c0320401415500e52510780d0001203071600143c55016000c100e601141c1c020544603621280b240400d81c56042040290071000c83d42911031803034039500000c0e01e0b03002c00e1100d0300c1c0601442a00c000000d008200c070711f1030001c81c180c981c4900014030740b0810010a1862041409102d500c400d5240d8446140d100ca01c0c010000d130041015021140008a040039844032866102c012a4162140107001c5400d1240e03a0302c942e4090301ca0310340e0490b0400030078044062002c201d10648000140c204e00c007c942c42c03505c2414408460b9074080300c20b10a51104491a4a46e2034450098506c0c95002c5200d40d21a1406601a4071b000c94107031012100801c0c1c2410443e9a45007a115400c0342c0b442120207000780035012040050040e444c6000182401201d01036040401c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 589257383 1250 589256133 589256149
    0x801080d090b2a0337080408120403020105150103020f040506070f0209151302040e060f040615020307050d18150c020d0f0204060f0b0d02070c05031905010507090311 73
    0xb410343c00880c80e404141d82c800c2007409090021512070303400404d100d003088030b140d0700010141081c00001160225442e81c0440409400d00d420700a0008400114042c00030a008554100b07480c1e608201c41c07405c1515009000307102c1141c01c1810900c141c50702401070341c400e0080314503081da148121820182080100040d03a4401c0d03408840ca00c4404254000684030607903400c0c81400304082c0c20b0b0440e28480700b400140c1e10100341c485200c40c8108014030000a0002126401c45c40603070304031410148500c042002010b0300c0c0c00c800c5002043c0381c0740c003041c1c0c0d070b00000800c6454410402d4614502540788155454944408079035815828410144848803822500705044480761070045c1e400440ca402141041309901000e452a400140c400000d50804c0c0c01450300800c020740c6107690301450072611032043c0c01100c800701c1c0d020760001034200c07d10a40481c110003a14009003501d662840070707411003400e423400d401b00b107915500308000035800900446901044907080450310800101c5802007140c4070b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 589258633 1250 589257383 589257397
    0x40b100318050607081b0901120c03110d0b03120301120201050c160905041b06080a0e0c030d020a14190623070e040e0c0a052e0f0801080d090b 63
    0x20501e40d61500c00420810000c0d540680b50780d4603440303210b040c001414503119100540c1d41e01c0c900c0c420040324116903402100301c0c408140344d00d03002485500f21041100900144102d10404200124560340b1896a0703911410004200703c085440706030101d0390f40e00280c0401d11411085000300302c003020165008200a0201c1c0c1d903500241c46001e84422041d03a0740808e03541106e0003841e42ca80401c0100008049010000c0c001c1c0c4404c1d0020b1407401600821030361000f054030359407946401c000581e507203040003003945400c2e004095886601c11010020741e2405101426500428080d40300e8107079403070200310b241010601041c4107842251903120b80303021340029410928082001c4851402c0043c0c5d4000550251041c0c0d607a843d2400c031040c0c10031080d103966403038151545d00400d0201d17405a58081e200d0048450603103192080710030200242034080e5110b100e40c0200560388900d0082568015041011811980c540340380f541d880705030381641e803502900c0c4040440d0030f650003030001c02408000384c900 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 589259883 1250 589258633 589258661
    0xf02031201030c030c0b03040b06010e040906050a02030a0b0a03030203070215070516150f0801030609030207050d06021207080609060108150a0618050f0612092d01050105040b1003 79
    0x40e0014010000d020300800364001d580460070301a05104110010140c2c0000301029a4400d083d424544c4a4000020014080349e042c041a801401d1654640d600036182c00f64014104000c0c1c1d1508030000d0b00603500c11074401100900e8112107200d28030703001181409407070309075000b542015099400e00c03a46039804000781c1e580950a000250003e2010170010482c01c2c1100030002c4083d16211031400310250302160f603428001d40c3c50503124020791010b88941160703040080072034120a1810141d08042c010b41200d0781041506040c4014401c0c250000c102003080080200e04681d0f40480890307103c0d0082d98201c0c5d000554001061181d03201d0f103211500007450380d201540403000c020015880c0c8440e0703400400812031114414951440841426000300700c107031022072125031004000744452080e140b16540c800c020101042c0f0241e010410316010708131100060322070301c49040702d4811a000031510040590700b044004906400e250044480300c4901500700c0b010700186520950240c4030a44200b16 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 589261133 1250 589259883 589259887
    0x140a0c050423011e0f260316031407061401060e0406051005031b04180f0b01020303060d03030f090303021210420c0c17070b0a030b10031b0e03030306010f0203 70
    0x100c0308017240c2d402e8000c06d11b41484081c8200c010908800d0f00c00617030382c1441c980c1c2081c85905e083d0381150030321050b42503051900007120410a549141f8034066548007804062403c20746a01c0f003214560050305039912078450310300c0109414204015162240500740c4c01003100c51a44405501440184d0782040120800f0510185050700b12507040e0000c1d0b0290b00901c410b128400071301e0850b84070700c0c2d540083c800c0007400204240d600107540c0b848090140c50080701c40461443c1810f100c1d83c000803000d04101d0f000c0c860b014007400c00501079000380da5103981c100583d00c081841d140182c4281400c84585a5503035946411300513400b0400407101202c80b03840c02031a002080340a0420030780d40c54030021a15082c514000f141400362003026250081c0308c1083c0d4000050214040c005002d1007280ca01d844c5296460740f0400c0e04601038084d00d41d9481d00328000e04083c0c00c4003a00340c3c001e84007002c4001061200320078500f008407041c03100c010015030103400400106502c1d51080311702408001c400c0c0100c034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 589262383 1250 589261133 589261139
    0x1617120c0f150601090b091807091d040b0a0e0a14030d05010308180a180207061113030303050c0f0d110f04090207060f1a0904140a0c050423011e 64
    0x24182615142da00c03071003100700c5040040030f68111800402901224075014100422440411510250740c20b00d9112181118002000d292181d5400c10141184040b020b0f181c400e840001c03880e00100391000c1707684c01079060015002d0071941c402d6a2905403428014070866909884d402c04804412903180ca1901081003044d00f141000e0040b18001c40c42503040b20381c3c0e4840c040b1180d4205190f01c0103207204e01c0d2405020820000c503c038034408007094282d00181d561196281090040c080d120f00c998822001003010b464841c0002d404108907402a202400b19a8800464030898801d080c90b82800320010320807030741500055480300e4000442d0540652078984841c0e000380b0641c02550103030144035000038000d81000507600a52030740714402070081c8034265801301800007401c550a00c15000d1440c500004e0305000740e01044040003801c540a07680408107504080642090340c1c05194022070425032189400f080c00900300368603d101801c0300140c1d0b4200f00d0842c3d240100b0761120079070550941408 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 589263633 1250 589262383 589262413
    0x130f060e07080606120105010305070e0a14160e0906130f0b030604080403170a1b15051009060506040b07121412040506060a03021309030c0605091617120c 68
    0x404040d22150005040720314100e000c00c20000c81c100d00c402151b034100401000052400106c0c0415035404824058060369034250050040c05a603600020243c40d2200784001e40441015500170900340e9607803903203240c2c905800c4c8651400d0603500c0301e0300b1540d1100c850f0301c242d085130300c51048a140b40c0030214000b00140b0000745851000d44003a1042c0c00e000408108000d0441d040283c00b20701d0f05c46050030320000100181c108196203510711032290144403070034108104410385208941140c08100504d00b40f4031501048960f1030b01504d60024a091808229890300c00c00759070032128004981440d001d40340c0c0d6400010980a40b120003441a55260840010303442c902500540000303c082c180c0d07510b01428194a8020090810303030003007240c0d45080c40961140c5a103d141e80140160110314481549411284802c000130054190350bd06420f10007016030110b0380b800744800c03410340990425100d40d04d8480c8480c9414110501d80d01c00d01140001c102742002502e50890258141c9402d08601004 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 589264883 1250 589263633 589263643
    0x1c0c2015060f060c010c1106160f050d0b0405040c0f0b0906093a1e03140a0905090c09090601110303070813120201060603052a0d18030c020315130f060e 67
    0x200c0e8007003071f451805568507503030403c0210341c04500c18100191071082d03204060b2031500200384100420500040040d41c04040c0d0304041030702c25000d070040010385042d0606d10000301c501d000d1a8440d01007220002860f040701c4050342c0860500a281d01d15000f004020000130404440c80c1d11200c000b1004201030800c0d811501e03220303c448c802c060350080c10041c40c0004260b00d18030200005900002201c0c00401c0c0d01c61213801c00e070300c07401740595518845280241c501407455402107510100080401010440e40300150116050903992024103407036240065038030100e184d00c1c10015510038030010303160342c2c030400b08035410521010080000c040b8580710904240c01000798000941e4482d03500300840c60b458032556a002c011901240c582c80194049a441c000d82d80741032551a14020a004418200c02d5204c4213660301d0307044200700c0300d42c05850b0262040d54644001d03031280c040d214800070b02d82101e007a66481080c0710305403c0c004129076503400303091428140d01a1181c3d5910500e000c442601041 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 589266133 1250 589264883 589264901
    0x5040f0b22060509270715031e0b0603040609020a150c030f110d08060a0b1209070b120403050a020a0b0117061b03010b1c0c2015060f060c01 62
    0x910900c0140403045030805403901030f0701003400342000204010540107820002c0e00b002c49880409103440c10881601854400660040140d0740604040c1a00c1242c15511100302a0806502041c9a400401e100c9045030110501107070040c07010400600010700c141c0c41401c182d480140401440c584440c4450b45254a122003800443d0f600700c0c80f8070603d80c1100e25800b9004c414649445806c500e24052031301c5800550303040c0b0a01c4880b03004103c042e0b5690040801810411040c0c075215850b1000e18881a03d05444003280e501441d100491b6070300010049640d1031043c01809082e50b2540da4045880e0f612200703100085010320116140056842d410003030003001c443c01a20f452940c008612800d0110107800301003c54031240b50315120b4443d01e01581d045800e4105042d444001051080384264400010125542c1c41e2a0f22810080e4100b03030041d2524a82804480d02c0808100031142c2d80c1c071100700048042001c83c2c00103500c40c0750508000c480d103a00609541e0070000040051070035100194 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 589267383 1250 589266133 589266169
    0xc010e0118060b091909021f02010507140703020d08090115030503030709091b030b0312030a021206120703060b040905011d01050903480c101805040f0b 67
    0x1101e070074184689806640106403080300d003000542003290301c90341074100024240e1302050302c030110b00c015507503818900c4180385000401204c103008030300402402081c00700d68000219084030307044103011044005035440203502d90001c0805d00e96a030ba060f201c0c0c41008104410964841010074901ea04d0203e0b0140198414401140c983c10860342c06041941c007078118030101d03450f01c004405000d42c281da00c515410a1400e001030f9240000c00400d0425260b40201c80160100005003c1c0f09502036004001601041c1c07070007070103070311681e00700248001442c40340362180e80300b14010300c0801c0543d4403400c2a58001000041c10b038403182da131142503840109030724140082c00781c80515005000c1c05110303441699040614500f03402c4a52017031b62070100000c5100c1582420745503420b180c1c40c006141c80105918009086444d0810707424581ea40700e0324200900032031800040c0c1001501807056901d0404603205004030040c18070040c440104000c070401c40c61684c642c5020f1480341c54502c015041c0d68480 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 589268633 1250 589267383 589267421
    0xf04080f070f0501051c0914120702211e0c10020105040203010c0302040e0106050913050123010f050d02130e0c0409050609011401050703020703202b080c010e01 71
    0x1c000c2c10b41c180300307580c04181030142c10850700405840c2e0b041d803150f2142032a4400185108182801c030b990625400c0c050007207120701400d042c0014501d2016203016407003200c02c003c1c20b05416501030100302a6240c2d8420503842034813110b04001c245000304001000f03090849402d00703000320000c1c4440e03944d0a07625025035514818002541001c0c014089001d449040c00d510302841d044580c20240c1051241d101000342c0411700308042d039030385200030342c00c1c4441c1e0f1014802941c64a05c07521107090709075104c1051500029281200c1e50140d240808860055105d0504007200c00241300045cad804a401000344208080c0041122041d00310b1680c01144030368030458880c0c0c00d0880400c126040a4800c621441001004010320100c3d4250584010801e103030454940d4281e20f801c2c0e15203030454000401c1c0746855031811002d100b00340880110a40b0803904640750035225031000c02440700c0c80f001540315501c42c6201c2e00c00728008000420000c440c0900005a0441c21141a42103441010b04040d0354841c1e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 589269883 1250 589268633 589268639
    0x120f090f0f030e0918070e0c1603031113060e09361006170111030402061602040f20041406070212061f08030909010302010e060f03010b070203160f0302060f04080f07 73
    0x1085020090007441400d4030103030803c1e0901481c18045c9810101016440d14048410544a600040c0c40480c0c5074060648030040c019030090319903c0341c02840d0014030f01540c0c6c6113f03454034071840c0b400f5800313681401c1c05c0200440c40c5031141100704140b02d030035503001107400c91803240c04000e5001c4000a10300e00213281ca0410319446035100303101c406214243c5c1018044a8800030b5601201d411a81c11552107640340a0000700700b03040304000401a40c080e01d4240c141020442a0300072503041c02c03602d0300402c0700306218044c004880c003903030080e82c42c1c070481940c0c01e00f801d0904500401105000030701102407142c00741c144e6403422034100c50300743c8480c1c0a10440c0a0000c0920002001340010002a41c02d05c42c0d000003040b80c2d180144030181c100b206c0039a405001e510341d0f800b1120001030301c00520340d0b40d68441100c000d2662210340c04900a10039022a01c0440d8544e4070082e0590304c580e29005092450b5808004168004ea000d15503440800c01000400107410400c401c18414a80c0c082c2c140189 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 589271133 1250 589269883 589269931
    0x90e0925090606050f1801090305030a0e151602060304030c08030403030903091a0316140c07030b0a09051005070504090e060a0e031602041d030a120f090f0f030e09 72
    0x300c503070155081c03020a1001c03048a0541d43c080d50010700030400e1b8030040e034001c0c20040300d25012540c0003408500000440000882d40300380040341c02402690031031100244807003246034178454400004540182c0e106480010f1401030001c5030068000c4c540200801c0301c503180c02c0315981c0155000c6000c01d60300d103544c01c20150002070080042101004107184000301ca694500c107880005c014070380001200c40d902c222540598060311800106807180d03911001c0001c01140d640d2003a001c196200042040007508000040c081d400802c1d0b4004050301c00d54107081c041d000a071501410600178448180808600004103215445a00180300020459401e049840b00b04880041044140d990001c03ca580c00e4103034889405031100e607050300d0000315050502c1c1006c145886189030718501c0c0c0000503003d06551740c400c2e071007514068800820886005103403440e504860420800528144411514034013140480d4400c0d400b5074000e04000f0a030005010004040c1e010464015102401d07051101c03951074 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 589272383 1250 589271133 589271141
    0x60f02130603060b0a050306120a080a020d0206090307080909101a1213050c01141201090b150406020604020f132901080103080403142518020901090e092509 69
    0x4984074610314500170001c2d1004003d48030041036140540307490f58035084038180800c003100c506a002207115032260201400292210b100034582001449040023084c00b428002c0201d4840c80c0d40112017503e448001424030800d10801801c0c001c8405001c1c40c00034800550101c400520700c28003400c42c2e83c400d0350903e2206840f01c040c10405818810001c0c0c140001d00000d6051200402401c08113840160003000e1001c501c50b06e460303258000104000020b00340c0306070704042201442243c0121805c19200d002c484203001e10f128603c016840300c008100941450b0300307a2128001c1c058030310b002d0f644420512505135000556010f500b02001003441500641c07010b02508061000d05e4404850751544c0c40d071036480e0140d4000688060b030a1802000381c4101003000890340500030310784103080c48407900e0b9410760015600c294564066010340c04040780002d4801c03030791600d030140c40d00c0c01a142411603841e8881c10060170803070725204000204400100d00f030a045580d0303000900b00c07042e4a05141e00c0200380e03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 589273633 1250 589272383 589272389
    0x121e050a12021912180506010e180319030b0910030209010b0906030a020c19030c0308010b090913030909020d0e07090516050d0b06030901150b0c0a020d060f0213060306 74
    0x1803052000742208084001c0c2a12940d4892806502a14162008000134907131001c00300c0c1075000d05c00054040003030114980d41242c801003010004d0350382d46111450781e82060014441c59030010820080c000c0328290702801c000344240f03000990701d480480801d28510055400610101c42d4160800c118502820314a016008041c4280d0410301e80b03101080ea140400b130b044039030040e00864504c01d0b010007000030365000390350a112150740d10290306025091b128a80c070709900040300304d400410480c00303500c1101c80445025000c4804c82e503ca24a50226140b010011020804440c00004001c00d8900140040c200d203c0c80009103c2d41e014901b500d8180c00303511011000f41443e04008024000d446044011034080c2030459031217005000307880003030014045580d800f24002c014046007400561041000ca644000e603600d0f03942d00c6050009050098981c0e6000d02e0b0f10a108403001030615204414845100f0380000c550001250040303801d98001e41884c050407134151030100035140c0d0600416000f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 589274883 1250 589273633 589273667
    0x2090307090e030708030a09170301090c0801051c021203030916090b06030402060f130303050309010c0903020306060103090c050907180e040f080c031b010209180108030403121e050a 80
    0x804010b2041d03a880b4010008060f1142c2c20200000340000400c1d00041003640c0e0000440c01d8040b120503100b6a19002070054846442c5483c0305158800c1c020303000c0300c0c183c3e08010940c14185a206212810110007101e040340c0120510200003511103040001d5401001c0c180013420182c01c0c8250302e41c01110351907110000d404d047c00300f00d4180d92a905c00f1260003d4065a007e41e48165512410480c1e00c904014212940d0000030000241a03014003d5801000954001d010280c00c0e414100c1d130703410035404043d52681014000c900070358080d90010140074403d050701d8200c15502c0c0c0020b80d100d1400c80d081404190340300c83c40031010000844040160030780c0f410100040c10152a4480e01111a1a008080d02c50000d030381e9002503400c1040d0b80c01c001350b19100c070050b10fa16241850103034020031101805541900c1e0403420908003010340134162081103000318209032031500c822020308400c07001c00342881400401c0c10204a0403450b1400c0c0b002d01c5480c0c580d0b5845403034a000b0064041000c0b8064 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 589276133 1250 589274883 589274891
    0x70906140612010504020f120901050601030e01090213050a090f0b090105010806010812090a030204050a1d010207111c0b070c030f0e0105120613090b090c191a09060309010209030709 80
    0x40d0702c1c0720a091541c1500c1040e24010380345d4440c04c80e000114807524224030040d107443c20070040c1440c415004203104200a0340d09002d514864545c541c01c0e80c0e0400e600079401402d00400031107000d8150701c920390103110341c0804580303591983c9a2604030f1090013002d8400a14020070481106024003400d401800d558005001035803511207880e8846943c1d59004180d107400045090455440d40c2c41c00000c0c5400138000c100c64188900b55a0061280d81e600b003506800b1800240810881803003071f01e0394250000c40307411380070040308104442c520045001c604070007100d102c03900c080303046441c005202e8040d9407074804d180e99003820040d000c0801d42180d40200710b8042c00502d5a40d0f8000141d400c48101c4598407501e80d01c8042c00184007103007598400c0b0703919107444440c40c140492240010300036290b09042c2c411030001c2d1014004540c240e050700465003071400804002a8078440300c42030403c55840c03007480c00c000040d400284554415107901041d6034000c51610706500e42845207500900c41c00c0c80404c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 589277383 1250 589276133 589276147
    0x510020a0b0c0d201c0c0509010c30032007030c0c090c17150d080304050c030318033a0c0c0e0403080a0e030906030405030c0709061406 60
    0xd0050004142c40c000100100340b200d501100d0b500f10808030300308010003800d48a41480d0489090b000840304412003804100c000c0507141451041d0172a821090b607869280c10040d900669044030b5507076045840908510080d410003c1d4220f0300340c80390105c05084034203401680303002000c0d2966010030092103510402a220011340715822220082d501d81404001c07408903040481e40908075a00400010b82010f144200c0b1544c0000d0080a080a0012410240c0c4542d052400c05a000140941d0015031001100010540580246510a1286044420b5072110340040385c15038008148040030101030164a01311458188007145590188201c200000060810211300c40350030041c1d4561004410300d60785181c0707481344421001c0039410840d0409460794078030a507204007004890590015070f074140840c42c80243d501560405568000c020b50501e084070040100e40d0f400608101e0360381c403003000032649051040c0036040081c411804c4c0011918604000102016500c140d0316104600c100855 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 589278633 1250 589277383 589277393
    0xc150506010813030c17041a030606030103020d02060403050709150603020702010f0815090f0901060501020601180b0d02090906071d03100c020f06150a0909150b0609040e0102040510020a 82
    0x142da8400420800450203904600f0140d5480c0d900322000350410018140354800360190710018422501d0344140010603441080302889180019070742c40d40e1101e000c000401c0503140c00460341035400d00040c0308a240603030300d940b4107103400010340c405c1041d1a260b8950841031551022680014500d9082c190b150180fa50b0008090000d4010340105000600c0d0105a0340300421600d04006600035020b660a403c00e07214011100808581241207582441b0010405500c0410801e040340c040c8101d00040e4181010a00c1c0a0400d404e00281c10440e0300c1281c602694680c6c40d0240103100e00405003003682480d4100a0034006404003c2007408101e46000020b901c000039119000d4000d5800043c402000420413410100040005034141c8180028801c524940200004150708203e0703010802c01e0f9281c048200740da92004015042c00e03c2c2c5080700000c2c8416030030190380200000d003070318a4102d001c80003500302c0d6044410040710f41e41c00b16081c419424030400300d02c4c041103140020402d10090343d90f8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 589279883 1250 589278633 589278647
    0xe040e03070201081018050f0718060507030509060a03090b011413050a0209180a0e070f0b03060d0c06090303020c0909120711100f0e0114181f0c15050601 68
    0x70090400c02108009002803108011481c05044065640c004440300341ea82d038000b910050354912a00203010000c50081402181d0040a01941152045003540381c11400d0794190407404050f4148001080030803a01e0b03aa16009021028041d1400111030307409050410304248141c01420300002c0c2c091004002d6a0381309285000040800c001195680d075204280b00640201c80d00305800c500650040940001100920342c0324001009003000b00ba00ba881d12690388011520401da034040000100380007a0407044002c47d8494805004240425a03542d100c14980085502000004a41c42018020036030b0520510782030300030132218141182040d202280c1c50304103600080d081c40100203050420090070110042c03030036200814001c420101404050b01000c040182d1038000344035000403100f50340c040da109480f030511081c459410b000410400d414010340750242c140e80003610080030603da0702d004141d201e02541e00c0d50713800c8500e8003910303041104e40104526035802e00d041001b000202c1e40d00ca60 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 589281133 1250 589279883 589279897
    0x5060f091e1b01020c04050a02091c080706180506180f010506030d03051902070f02120a0b071b020628051207050708090306070e0906030c090606070305120a09030e040e03 75
    0x3242c0503010304850050380703025005410550040d0805007000500d4640d079015050582090380da810000c805a05080c9840740796600c02000c0f901c0038001440802c0c0c4680c41124060350340010300c1c0c440c040c1d0340c4510f841e01404031741c00c0c40b1072401c10003164451481404580300910700c460003480281002030000b603d030708154100307104040d9a60002115020a000c103504d40e03d0400c4d00442d62800542410302c00341844400590042000c4041600068000246500d00b40d0708194100001e8880000444001c6400069203a001d40e202d041c29016988405c01060000d0a0303408404000c035480404021500034582c0c4031040c04018002c0d01900001c464000b9440b09051404554030780701450101880c1c0140f0802c690184156810014a160858001e420744402118081c41a03912101010f039520001c0e060590403c41c404003143c428240383c405854a1486810300500b00503000e08041100c080171602e060245481ea042e160a05400525a181421b02074a00340003074100b10380c03e11b50f2485408 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 589282383 1250 589281133 589281163
    0xc060b2b060e010c080a240b1917060d050f013b0d0503101a03060306010e011a18030607170f0411090714030712060f05031207030c05060f091e 63
    0x607030014019400c20303968506030708010002e5481c07161500c07854003089d007040c058143c4011022500c1e01200380201d211320849510000c1450076a66180c06003c6103c1c4407503000c9440340714901582500e01028007a844088074070a04060407003440d00000c00e81c03841c1542d640d11a20700c10342c20980002c1c0300401c0e050040322840c10450f0362503c030683d01d00c17103203100307940607400e0514029841040e1399942d070025401441c0403002c540290740c842c8a00c00e500007080c4240c140000012031b40c90030796828070707000d80501010038224110584210300800d041440854503100000d02000b500c11840d000030079080e401420400c2e01d05210710f0555203141d1811013681c2c7c540c0c4900561000220034a11421310f407507a40100c4284a5101e0501041c041c0501c41003411f042c248900300003000c0f80c26010610030104440006005044850f111600e640743c1d9030111801340d00304510401404c001c243d0400901e030044021018201da5450075061542c10900b00c4443d040c549800f02c0440700c0f01c420002001c0c1c071506500c3d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 589283633 1250 589282383 589282391
    0xb0a030b150316081008060117011506120e0304180504140307020906041109041407020c0f150318010612060c18140a0e0a020304060b0a03030c060b2b060e010c080a 72
    0x20170000c4501500e0b40005880d2080000100781b10403842a124040e8401000900c19002c41c07110505507001103004800002c0e5000d480c0215224064020010007840305080d2840e09440d031030100b2040015030000303028a42c0702c500f44400c028032072100308640b03100c5001850a01030ba0368009100050042e00062040b038aa0f03c55030022040c45040b2084000000c10030043c44200c8001142ca00e4001c0312003401500410a210b40b44c1c0c18810030a0803800e0008000c803101034125032444026402c0030340300d100080c1e0043c2403d07001407001d124103800f4202046142900c03801c1c038a0f0440580e80c13880d005404000d0802c250790f810102c6011514161003074001080340d005a01c00116030303000311f16440241083c01e04024094041703410342c019402240100811312141224505000c08400c06201c01400541c5220440000c00c44943c00b004981030700401328505c1e60078260700c85640b180b10760400400404410404400c10441c1d11800040400a800a00481001000143c64800014901c88d886519 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 589284883 1250 589283633 589283641
    0x20f0303190f2931020d021b1b010e06030412051917070206010b040614071a100801061a0f0408070f08013b070b0a030b15031608 57
    0x541c201c901d0110707941500c0604140020103c600c104540e958081c060182252441041c07811200b002610180003003800010700c5000e00300100039400860003a0740541d00380041900402c40011002202c2c20300001054080da81c00403414480440c000914180300300c0c151012403544805003a05e030b001d504110349100c0785843c0d0070241c03480d00c151107005071a02c101c110b890900d240c0001489064040c0c081904a039692004402d9a48080c01c1c029240c00000078802045900d1145407640365410340d25440c1410069141e49030500e02400e070318842000350042c000c0000480700c2d01103400c028111500240f16640c6440c12000314501c000724000344110b00040d452100403602c10454005003406405c07103c203da81c803078080c0c2caa00b0041c02942d4080d4240000800c00044100203c54038600f04500b418144082c032240b21842405120390f20054003c90700300240751009240902040ca500380c4011562103400d80400c8441c0b202e403950700d4001c100a0041c0b00e04000788481c42104000307a8200800c46841d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 589286133 1250 589284883 589284911
    0x204060e1c06051006030b030f0717030d0221060a06050423030f06010513090b070e0409171b16030206070c09060b09040e0c03063106020901020f030319 67
    0x407150406048203003000b0901041246200c010001c58405039006c0203400002c00c109501c0361140340d18216540d0190000380084680000203080040a8400312072402c0004121340003a604008400c2510300c40c0c000c6428048039440c2d89250b0300c10400c4804040060078580090721724012401003540560b0468503169007a205602c0558600900404a86810003410005a940e031024014680a480090341d02c01c8200d0b0140550901036603ca8440c490a50754080704071100d83c90554241d81c01510380310410081142c5650312140c0343c60060744595294507520600031030704842c82c20384072982e006e000c15800a101059907801520f45c11034002c1daa0380c02e94109143c6050903500011110751400f040002d091002d0300c0101000310003914140407120880805580b107501c4041c0d03803901500500000380d00e007215181400ea100d1200e40301c8615010300b503c000216800007920445480d80d0000307444c1a00e40c4c041014940042a65000710301c0c501e060344000030321144056441c0503c40d11481d00e000382d50 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 589287383 1250 589286133 589286179
    0x4111c020906160507030519050606130b04020d0516020a080d050a110301080307030e0f01120c120e0c0306010b04050105180a2d0503060106050f03220c15030204060e 73
    0x2e088141c80100601c981c10322644480c3c0038882160244900350f0702318401c4039640568215190000007400c3c082d5250740c1444112000340d400c0307584899850158103020f554901c042d0035405200316002444e03161031094880101804d42c0450159441010f000340011004011200c018a0030040801d00b0b480301604400581003085812800510200001c95440d0000000c2d25001d402507499021010030b44c4240148007807140d01317860004009862910f02051580c015803070b00d17021880d2410204082c408050200c0d006110344000c2600040002c1c12580380420901d800341c44020a49460203144c18001f0700180302d100100090303036862104543c1f142d42c0d003880880061003072207034600024a070008510404ca0072000c825101882802c80403403203080c006601410b0307800755100d070b5180540207803044040741c000602c803428400038899600c080031410090202c0307183c4a85046030516080512000110840c040002c04241c41880100006ca600816410b1041020384217007021641c2c07408840e41e54 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 589288633 1250 589287383 589287397
    0x30c2703032b140109051302040501120b0c0910080406060305060a050403030c090305061306020c0d03020c0f0f100f20040609050d0b0103080f04081b04111c020906 72
    0x980004500700300c1540050059030b490000c1c40780c01c0740d5515070902c5240203c2c0d81c20260500c41e18074800060004150315409160402c4400000d00c0c1f50468941c00034081d240309030401420001c082d214042040420b40c2d059407c642182c000c2400d0003980741c0405e54103154040d07900c0130045408040f506005071648a840915048800d41c2c40314500b03992a42e0182100f560100c001030301c0c00c05a048810320401900e020b03294094003401c040e48903580e449000303000100096440d55806c02100c5140c40b02000005001c412544000d41c55070403960055090000c542e1084d0555001501d42013000600030404205145500100080c034141e00c20b901c03c002d14010000034003003001407109108040c040300c06042160155a240941d26403039400f80060400701d08002081c0009503070062001546c031b10042c00e03c0075417204034142403650b251a010b00d851131800e6a20520307000040c1181280c1442d008140e460900f5251251602202400300c10308058207201d1030003065400710740e816080e59101c3c1105c1607 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 589289883 1250 589288633 589288639
    0x2060705010614010e061c230415200304020423090c031c2109081809060103090b0a09051c031506020c0d031d0402030a050405070605030c27 62
    0x500c1d83c55a0200400f881081c11060103d0030754031158244d0302c0c000044842d8100c9401040f000b06050326802d001900c500358800d25000c09654130820307071010110300a171040c2c1c029410303c0c284c1024240e8690840380e00141c203040703217070511840040f449151800c503500607a054500040c0072781d1808024804280068030100c40d614842d05001101200041d035003420f503401c5080d07030034481440c40c01c1c17180e000c0400302c400d001c0745890b007040b0b40740720300010f200310a11207401e00400c5140c0c0a64070700f00e99500001003c0000c0c0c04504502800c1d04141d021994800800c1c02c0400241a03161100d511210300201030300801600d80359030f101000710500800c060210303070000d10442039101c118040e0183c6500590444c100e03502c0b100000700d07548002500b090010f805450031036008095102100c1c1041725040708010301c1c51244100c1030316111480214400e2603012000180d5042511f03016080c01000d5000e0342c01c101060083c01184451801210301c80401d562107018603a10700e030f4400048000c1c404403268 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 589291133 1250 589289883 589289891
    0x612060f0c12070f020606060c0a030e03070815070207050105091e0f04020f0d0f110f0c030415090e07020a20030a14012016030e030307021908010609050c070b040206070501 76
    0xc40c480d0060000307404c141198080d64501c3d174039881803040902070203000b42020780c0708403585000302c0d0190214030040e41026082d42d81c0680c81e00e5100d4a814070701600104c3c0c0740300704001c0060031342d4144140d6018107400d29000b45070911843c0050003500000f0079000100b001000781141076075807003070006c0c6000070140042d5151115807141d41c0081e0041358074207024504202d4400307042d0b03555100700128402000c030031070f040c05159001c907170050300160208080740c801000302003030b501d20801481049000d550740d1400300c141041451114204050440360542d0b01c189840e20002c1c0a0b042042d06403000d00402c100000c00c003100091501000180c003a100c00344400100e540010103400031400a100070b04844d9040c80f011030035a449100e500600500307030100c81003440001e403242c0c0c0d00081c2240000d0440f41010780b95000903240c44c9038120001e1b04048281c404000d01c12080c040d02004080760704c001c10003803406510080c054415040001c010203c1a0300007003c40d42d620099030110f94100700200 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 589292383 1250 589291133 589291141
    0xa02070e150d150f020301120f140f06161107210204020f030f0f072703080c2b050f0a03020708130e1302030a0209060a0b1804050612060f0c12 63
    0x2040420f42c0080c1166001e05003180141c43c0c00f0036000302da040300e501601210041c1c03090744132014004100d400890b0803a4440c51400104401080424018110341019003480e090101c640c11240c3c03141000d03003040c801001040080d461300418020b003116105014280401003404680040042912000b58414408121001500101d4000c1d5100f01074150030f809aa494021004098a1040320030900060322840e0301200d0f40782d42e0040000207080040107080c52900c9540300041600482402078080c1c0c04040152070901101c0200c0c4c0c10500c070380311841105d000030000205144615084460b0a0b05d00054030080d0324400d5045038010303a0080c04e000c0d280c03100001c010464a0862145070311040c842c801060b0780c281015500011a9170042c01005100480e60034008107010040c40607070302082042d000904039100c030005041074203d4555081e01c5610400800045400203072816004044000b66020403500000c0c025800c02c1c000c140300030f50703035840d04400c8456101d014988015044801e080c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 589293633 1250 589292383 589292393
    0x306080d0c0c1205060a0213090c0305091e070e150409080a0809011a090a061502030702010221071e0606030602070b130c0506090303070615050102060c0a02070e150d 73
    0x80e8541c2403196001c498000c1e614030290500f580b0076540980250001c10200c1c1c804049980180081c80e0050800312410b40d4909501c0100c807601d0000d1340200c2e486104201c3c000c0c4c3d060013000d403484c6072444040d000c03081607260255514810701400400706815404036121086d00c5851040d00c110041080c4028402440d001c50140c000c500301e98041a0b00780089005808180550080720014880483c409800c1004014250f8000742c403004072555900804500e4140d00c2040b111b10079981d80086a0300c2075503200082ca4004c030a40103101c00c0d00a200d810074400e481d1000c440f0360b1500800e030200b0200502d011580f00944a10000b0302a40c6459400420003c1c00d07005040c21038000c40c01d4400566809490880351301d6041001402880d10340000e20151510b48007070510354801408032803c06140b5550802207e4446510b0b20347c0c8145504108201d46e8104003940d40986040300590409906040281da51083e900544d03d10440d49070010320001c00004000c80d00100042ca03080741d1034424148 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 589294883 1250 589293633 589293647
    0xb1807120902042c12030403030b042414010905030607081e190b040507090b0d02090a23011b0f03051908010e22110f090c2502011e0306080d 62
    0x40c4c1282c00d80d540710500d45102013802030010401e66103a5165603601c2d80c04800910020310110b91056940f258044c00c00c3d10610514018032002d407800c00703c0c0d804c0003605120001842c1440341004800e031402d0116403404210075401c00c44900b00395919407500e075425070b10714490a43c04d500708005a0100205000b01404c18040d000c4254010000d60085800780000d5035800c0b00c0700c00119905920400008020000914282c4489a00107060507200c400040e200d40d4035600c4952960a542c05000d00b1290400c8074014150007401c080405c036500003c2c0d42c000b6010040041d0544510910140505015408441c000b44144100d4903510035520f2018098480138094008108602d5001030500b20700404241c0c1803a00648d41c05506c03400703550b601a007420b10310600c030b0b80102003018000581c0d104c40c54074601030390309221031607141d04503402e10820f0080400c07035104170700d01c40048000160b41c2000c001103100e40f07618807070004129070020079401f4280b15804880c0a105040d482c0043d90b6000d49 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 589296133 1250 589294883 589294931
    0x2010b0103050708010b1218071e05010f0c06020904140a020714032b0204050406030f0506100506070b062206051801060801051c0501020d0204090b180712090204 71
    0xc1c204441e4942da2000c640c0914240180783c000c0d1b03410031900700c0e4903600051203580603144464240461034544101820200b40e5400360143d081501c080001c0c1d50384414094015000038030780a40301550703911004011111002002d4401359000501c50080e48840d0810949890701c03081488103030070121411002940031060036030318504c408038404c010003000300844503090307210b01c400d0100e412080d40b008264081c1504981a89508110014075502c1c0d50080600950046003042107800a40c103106003800c20003810406900c21584082c029580c4407001c0d1744029420842c040c8070381e40d80d440803501b036050302d021030144013032029140d080030110380e0411400d40304142d0300102c040140020010700c42070b0a0060102141e0104010b00503820b00300c4900000514815114040c1d44094480900b264041e0164294464000a09102c0000603000381120f80c40103560b1890040049000000a032401420072801c00c90b0509081502d01310a401030421a03400400401445c001e00c082030f220008004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 589297383 1250 589296133 589296137
    0x20c060f0f090601062a0507090615020d0909020a120905011e15030f020604090c020c0f010c020a21060509011d07032d410a020d140d02010b01 63
    0x400000c01c40d41c0b02080e8541200c00d9a1915410003c040c204000720302540c400c44042014082c2100011800410180f0002e0a041400240135418140c1c42c03144c1503613207503006055600c032210002c80ca540c8442980700300c506840005850301802d01c3e0481340b0716003210442921504201900c010f200c010360104245824451041000c1e1101d92071280a503150a0828411a2072028040003c40c0005400c0840148000c00182c0303040c1e22420007008940c449851840140d01c41d20403030751a403c081c804c001c10440c0900740f030000e45007070f0350000352140400c0c021203641690303c10a90300b41310f41c03140c080250f59034040c4042c42103140a2100900a0100002c1c002071109412001e2401c4040400c40d0000e1781e4006651540318580402d10038001e0520001c07411140030b40c0062100401c0c1000449810000070b2140210303000d42410369040440c00302d207251521081021445110961b002508040565056070400e407089400e05105081201c07014014110b03010303140100d4a2207906610102d41c00c4026 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 589298633 1250 589297383 589297411
    0x3032d0c09050411191407030806040612230106170f2b08060d020904140c06030702031204020a03240509060114040b12121e160312020c060f 62
    0x9401004182c644085000740c1c6403004101100c03070401c17020308142c0440001c0c18003112111082d09401d1040d07121810547c00100c1060a1064900c0c0901030380300141f08904034001e481401d43c440595a21109440707030040c41c0112000364440340d081d08500000c00c18612000007510726001102c0c0c648001203100d052a0040d9807840451488101c404c14030181d1072080051f4130252141e054034600409446070398000c240c106c170800107030b8a0302074641c4514803070003030340d001180e8100c806841d09000e441d000348152010301c2003006882d800010360300380d808080c0b048035542d192030000c103908024580020740503141c140100c0150744042c0c010702c00d00810200003002565219200542c64440a02840180442e00c4446050603d4150803689650600619600d2401540c0c0c40e2035142203107090714100d9500003c00c15842d88040c40c0c24004a84d200300780914500f60b1103480c0c0840318801a5001418040215180c0c40310b600d00d68160703400d006034a000c0301d007141480003d01c007100302d084680d1030004510b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 589299883 1250 589298633 589298639
    0x50703080c150f010602120703030b060d0b210322090905010506120304030819120603030f120203011406130e0c0304060e0f060f0a3b0d050703032d0c09 67
    0x84400f0060480c0e406501800c1c100e442204000156800481d0039010135440d1701f007010486d52a007004010010b2a19400a5400655810301064150303140601508009030344020700031007408000c640220303101500e44c09040001a00c6010f00c102c0d01d40240310700d10311382400036040210540c401d50060702c04644101c01d84071058485075a034420380c00300401d160001d00015141900c0701129000303042c8182040d5284140911008044440d240c0c0190b0010703000d580341400e8580c111107501c96031a070255083d807840d03050040f209010304036960a5409040001005603c232181114144090202c40c9200d584506250500b82e0090b0010713642520510720701620900b02080000726034056042c0303e0058416503503510100c4d04881c030300030146d0b0b002c25201c040701200355a40c0395591440c00007254486040d0046213000c2800c6801250b00b800907503003c40c900c0004145c0290035610850341c9440c02103100c2180016140d21858078403000c01343ca00f03190300b801d40c0c1d85005420031842207032030740e907a000c540c1d035 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 589301133 1250 589299883 589299901
    0x15090a0618050702121309050703021903050402190e0f09010207021801050f010504031505041104060b0706050c040509040f0f060903021e0706090b0f0f13030c052407050703080c15 79
    0x803501d40600141861b20600300314086032500903603440261405c0041c01c01d4130703000709001d61058907640380c00060750b51020441140303010a0f01d15400e2b078a102980b401f5034200134444c1611701000c1d00c9404141551000103203180b41c04d40491740c1d160707806440412080301002d81c40c14411000c1c018644200b0301e0070f0b51000710354032035401c1c0d0b821a600511880c18000209c0c00c0800100742c042e00c04ea5265030031020440064945006403002420b04100740c43c1d0b00c3c4032031308000c41241c0c03003c0c08010099108000800c045d82e40c088000c2d80003500403120000003499460410074030036014100811480c1408080c2c014150080780c40150f940656440b01c10000a42c1500c0d500c41202e0300444012603140341041c80200c0e01c1d14054001c2141ca039401c00d00d032407081446100280c00082c41840c0094030703140d0038003c00454012030b0004000569060701a54072010b82c2d00001c0c03c00786070010348201c0200d900414032030704100000c02190041c014035a5000c418245688507425000040d400040360380100d40515 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 589302383 1250 589301133 589301137
    0xb06030402090a090507050a0f06030b1009060f1b0b04050c010c0b070c020d050124080309150c031c050702070608060306010308071416031202030315090a061805070212 74
    0x40d50080c0301c06002da8469100f5002060419401c0c2e40f64800d07040c0100d02130711003004450190000104040b1720901c0c1c82001410b85640842c071600425400c2254111640c00c010035809450f07417410038007580590103400320f5051410860603503c3c00d80030000041845148030302e850203107004a041e80c0c1c0c91101c1100640e614940040004d18110030038000032200c032b00c6400300d00311280c0b00901c11420302c1da50303072189070a44884c0703600e150740342d10f42c0b80c0354604a0300c480c80840024040d2001840c2852010740c0007401c100f076031444e16601c600e8001944408480180100d4005144050800020390b4010101c8401003804032a00d81c05841025000f03d1040d00071040c4a100c1c041c001c1c018201d0785e08659525050b43c02c500c0e801c640510b6100010b1025190500c413112850103881c540d03421140c654282014003d4a2030101801d6400400a0003626484da40c400d901d158400d54007280305490381800500100700560110300c42a14040c8407010303044190700014020401642121008010040703696214 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 589303633 1250 589302383 589302391
    0x11b0807030f2c0409020406090608070e0c091519030b0418020604050607030207050d050f0601061706040c090b04030309030203010b0105040b0a180b030c030a0c03110703030f0617030a030b0603 85
    0xd01d080e20b0041c3d9071403141002d000c4402e6030143c00451242c51700e50114068420030b80001210684440040c45406010491000100b0189072407084a0a165600220f2841610482c60080700740c15565603182c03007107504544a8100c85a108500c0b01900b400041c001e007444290a8856030078407000038031803082c03041545c0142c0c0d0010701081c0f07014500820404594450100cc81c198054420300080550b1810080004180510050030700084084141420120140c00c41021706c085203228112540d00c94107950707808036080e0740021f203040a40301d080da0b401036603a000e6600b5003000907010040681c00702c202030484c0d100398002c0c8800c0340f0139401942d03980198040c4402000080c802d0840300ca03c00c001400c404040031001460180c0c80300050901c40d40304480e21510324000000348500b00380180b24080b000e09061408001d1103914111112081c41440005010161500c41e0304040340c219074086401081c0000700790b41c51035400c1020f0360322030304030a0b0000c0102c2e141c0035026510f800d0220440348a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 589304883 1250 589303633 589303667
    0x6030d02120d02032509150810060e2206030311060609040b0a02132d140436050607020a0c3302070f060e130506011b0807030f 56
    0xb0003008560400c001d4000502500e04016400c24080e28001d019520b80c454a515690f14600303a402d0100900d250302d41c00600d10200300410b010818084466070942c07094410702c1c0f52034582c417031040001926030140b060300c0d0108000344040b0956103044581c003642c2109e1094483c09190700107007030700640303e03013044400e00e8118815070001000161801c0105a200d205001c005040400c0010103c0034059250450380200e144550598650171400140584410203d40f16400c22810030341310541c0b148132056800e0250307441e031300e022942c164400142008556602805607242095034403070103414508034015116401200c010400c02480412602d0314a42c0003101c0d40003051030051242c00041e0641c8200c40c107400492517807900c8a50210342001d01804541c02044114201f05809c00c284000d90300074014410044200f04e41394030f40f600e242d00644aa200c002510f41d0f144801a10040c11590100300b1502d0812559400c02030180c0c05072010301e01035510550804440b030340507a42d6011003500491 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 589306133 1250 589304883 589304887
    0x10f0503010608280b0f150409020d031b14070620060105010c03030b1003090b06030c0f0f190b0d060b0c03070b04080f0c0a02030606010309031709070e0c0306030d0212 74
    0x22500360407920011300410801001008022540c88030301041e0f5040e90921081c13014041401012981228145250142104c0070800a06036500089204907404001814804260010011110001c1c3c01c0c9c487c02d904030903d1300c104111580c1441c1c80e854280200c102040600b07078400e044198042e440310180744042c000304036a900300001900d102800e5a0101c0401d030300ea000c400c025444030742d0b00031454191500c4c0484c20a04a2600311500c40b00140214029800400c110000703135a440d080315070070035081d9814220703401130390003082c0c2c00c0901d031a00c280c0d4401075150015212800340011b0010291003603040120f40d46440381144d1071b11841c0305c441e1055100740141c0313021031a01420580c00038490720060380b500b010300041620079003001d510340b01c031904001007000079070070309102465100d002480c00304200d860340d5401501b20b21181040e04a00146000002c1c0500401c1100a01500e0310200c1c002241c5072004040c41558021102e4134000d0144055400e049400041c848000110f8035458034 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 589307383 1250 589306133 589306153
    0x6050c0703021e0106090c0c050c01020d0c11060403020307030834030503090709050703020901090801050132060f0a17060105192006041a0615070311070608010f0503010608 76
    0x81c0203012985440f0030103550782c2c40c0004c2c4408070303440350801e002c2c6c0076101c8071801da14a0a15500700703000c85110328103540000340705402a5a203e600c40302ea85a00c80c580300700d071880310004104503016940000390140b04003031011040c4400c501c003070309c842008100030003a400d054251050740745a2814155200c4c880c200c0c0000c0000e03000d18003450703100800d40116074800e660740c02000182d880680b00040483d9001850001c15640503148001600c082c40080c050380d490310b5100725003001405100451003215980311781c19071040700502c0905002c000c2c45991201410113070040c1644c022581a00411100c41e83d07820342d9041c1e802e40364480d6005840d058207081e56440b44000108800170a00108103101d07180840d481d0700118422070201c0110010800c600d0140341079003010204180c40380c18a000101007005540d14921280101400840c14a03100e80d41450143c64412141715481c07980d026202003c68007503031101040d4101e91171100d01500c03481d81c0d0000d250803075a441c0541750365138100705660 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 589308633 1250 589307383 589307413
    0x20f0d14012102040506040b040c0e01021b030a1103121305040605031506010f030b060705010203010f050306160c0c051e041d031605070f030302010501060e0a06021b0609060c0a06050c070302 84
    0x1091b4040400782012039101d542c0c100040880e10000f0b651030209559061031155968104501401d4144440308502c10a608400082d070755840391100a00a0880c4400b40c1c2e16601c1c00d00c022607040c09800f2025450301200c2400001c2083e282c00740340c0c00340b881c02030700042c07c7c60000741c4102a6584690451800e440f0040111381885481d1801010300d80c64064500003901c40c0001800c9176030080c800180c403941001108171074101580c6c401c038409e600c00000d2090100e1441868018000d40341090341c6101e0351841c1c07141d2480083c1d404668840c10348250380007003d40d405410b801064084a04001c81d501c0c0b03080480101030f0078088000990300602000300240d010b1143d600001e07000348111590f290342ca45036030f208904980c000703d0060751941e00401443d50040d00408000c0c0341211410f400ba810200001e41d07440d44880000130541c1c0616401c845600d501c012100064030140000f07a035030000e403462170b0741c2d100a0002121454581000541040c0301e40060307852080c1c1c594041c28000c510100c01c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 589309883 1250 589308633 589308641
    0x10c030902091f1502030706051008030a12110304050a06110f04050d020a05060f07170f0d1503080f1c0e070b0a020f011b080609101206020f0d1401210204 68
    0x30103070790f800401c8002c1001841910b100005181039402503550750801c1c9017140695602509140c1112007080e0b05011940000c000c1d2100040e652500341400d595000c0382002506172510350600c2c0340000024002400000f140a00445010794401d000c6400c1084607000c2034170807a444c0b849141c8040c0420f00880c40c003c008102510b00003004443c072181c0b03990000b1080d900141346038201400000e221300c00c01c03100c00003040d084580041d1190a02c0142c0c0c2407803d4501c11309080d2f0145a13921080e40d1440380d410340ba084040c540091949803640407070824854254003007016924428001441001040c2c45401681800e00060000e0082603251000304a82034010070844400c0d4001c296554403005824442c0e141034444410043d00e00e604c401001920044000d4446400780d007d02e020000741200034001075049030345450a214244140c0d0a1440090180c41d40b0380f018124001982c91210301203030420880907000044180c6140d0f42c62012512501c6188108903e040e80200088054602940 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 589311133 1250 589309883 589309921
    0x130e0102070b010e04050d170402090702010e0601060503150405090c0105090a0306090b060405070c230f01060f06110714060703110a03120507020106060c1101090b03010609030302010c03090209 85
    0x1508041c455a03540d074803402d00340c0181c128000f8620405c0240801040318007100000381c1003035038a240c40e080c081c00c640d01c001000a80607407103010102c0d00e51803007584646202c0e06800c00fa1802540c48030001002c0341d00550f202c1511095240c54050285818410305006900000040c00f00c14031050065911f90000c0c0e0307032194032043d082000004602c880c02442c542c01d11a036291070051415008000480b5805000e99003004107803010180043e411080e141c003683e100300d0040f12141030600f03202e403901001250b20200f039400c05000042c014440440038081e502c8075118030111840b035020055a40006108400c01c0101d13895603500035060510080c1480c5000349441030907011100091440c1012803181140020014012608041c1c02441566000a920700c003d005041c41d0502c010700d41c00c45002c014021135201071030410a42e0045d43ea07403005000c6001c4650b01d035a590040030b0401c00481c401500594248001d0030301c4a80302e0300c80c0024081d401020030301182c85031650710f450210071803 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 589312383 1250 589311133 589311161
    0xe0a0803030f07171501140306130f0e10060e0705070210050d0609020a1d1e040b0409060504030f02070b0f040608070c1e1109010803040509070207050418060c020c13 73
    0x210001d81290b089181d131500c40c184000b10350032900e1541e400104000440720b520403c04070240b00384940f070398444694911010503c80e011440c01020010700c4020020041c0e406201c2c491040f000401c0c0785550025000c958842c8400d00542d40c400205032011300c101c0c200254003690598a80706458000c07005400c0000307642c400080d020351030701c3c041d030200c2c0d01114541c0082000640e414030540700559555108440079034080c80000500c1c0740705480a40809000c5200d9900c80b02d81c014117072a07541c0900382454000704140480e00b400d080c06812018940020401405004000705102d600002228520091000103a181903c0d1080031104000c000d4186c82c2040040c1c0308c8000032403084101d01c0403c9006504480284000380703040a8a503c0c0046001d002d10303016401004000d00c04420742d4101e400950341d20040d60f440a030107c3c11300c001c1da000f41e82e02a00e08207201d02c0d201440d083e4148000d03c5034104121119003041c09990b10702d081c4440c141e000e0700c425442010f604072030b00200e145000d84 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 589313633 1250 589312383 589312397
    0x70c0507050f090c0703030b0a030606180c09090903270f170c040b19031110021b06070317130b071701050111010906110c1509190c030b070e010e0a0803030f07 70
    0x1500009d048020160300a4801c9603d40c0c1052008180d402c0c904c0c8402d00d01d07603004000066a021020303000310324500c01c900707000341e6845001052601480c1c11a8000101112012164640038a4210580c850303014942890012002c040b524250036502c010355000c41000400306041b84208100180c030f041c210503508104284001c515882840d10f4180145201c0d02c18034004d14810000c6c49a146520011a4115230000e0f1000c1c1c10505030f50303110007016000f03a034010359840d118102511241a800c4200c1d0f042c50304a0100442c445030500503411252288000e40e845840d0510100d408964012007145550102001003015601586484542d048040300100340d00200703488080464400c11003114001c50002400306002205114018640180ba09048001d0500b101826900c13141c08010520580e000306d1104140001c100c2803030011030340050303143c00030b203800c1034018500f020000c03105022618400c200fa042d4036101016070284c0714030340f0085096588004040306156005800c580c2403141c5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 589314883 1250 589313633 589313651
    0xe0607020a03020d26040e0a02031b0c0610060908100518071409130b0a0b130606051809071b081201170d020721140303070c0507050f090c070303 64
    0x1e060b0b1070b201303664040c1000c50144980d0b140c14944c182d403407900f8542000c008200900040c205100c0300380d00201664001603c030b60368060480988544030480410651b000b1032446446600040d00b6840742540d200181070042c0e44e900159036104190003524207a40051003c59030b1b52841d580140d601540c041da0031002420f1841d11a42003a040c0d4014120890f141d944003917490410415458100031452032010b01110161544102d02001070258000913441d151072182681d01d02d000c06911714044032040007402d558503006820342e4891100c02407058070b41d140301c0c0501e103010440c15109000304d0311844071078810b1241c05001c116014100f19020030f0180000702000d001c16403014041e01c02090010b21903480170a80500c6d01c64054003070001c641c00001d091042c10a03400710300f4010f091416018403010081c0c030b09040001c0d84120150690b110210402048940c02045d100c0403900070360580f080503840c0c1d802d1000310311701d220080b40c0003d4407402240c221149800140340c802c0c068500010320f030803 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 589316133 1250 589314883 589314889
    0x90402031b13030b090c0612040f080a080109050a0908031f09020a0809120c191410021e07051e16030317061c03120213151803030e0607020a0302 64
    0x101840d100c0e0680d11803c0c400c01440343d5205810600090091006280c11000111307148104400b81c0e10b41c210078000b180400a00c180310038152648052150384652520000905000c001d218003410700d03062102141039807046108e9256130341e401c2503c1d80d10715901d81c01301d9040c0140d00700046024101860000a50300c01c6840a0403540409644404281c00d00311400d92400725111b00544074507800700090521110005200c603090a95511005031030b10031804c1003030341180e990351014010300802c5111544c0600690003422210200300b0850340d0801000b82c3c5541c5401214002001031f0f1000181d05404901111528a20b180380b00c00c40d81071030141c00410150100d02e620480100b582000e5441c0107141a1141c5940710f0300980e0703481c15038169880000886565024040c05018000c01c0c10700d9040882d40480701d1391032007104001c0080c3d136242c11400101d90318860480c001042a1200c03128a142407401d80c0441e90559102c00c40000041c081295981c02000101c0e03120030303402c5000006032 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 589317383 1250 589316133 589316137
    0x30f11030706140c040e04020d03030216050a0203070807061704050705120a1502070f140c03070308040e070e0603011a040e0a02070b07020f0a140a08030f16030908090402031b 77
    0x81c0c801c0502084801c1503614a5103c050050b1208000850511003402120003181060364030a804444840f00440c1d40d00f8207400070301c0703201d10240040307241180c00020311000142d8a030030a031094046500305903844a030503442d0415070250301c0c0050306444a1a0203010304081d0190005d003c1d40c00c0c0c660072660703000001c2104250b04e910140341c0c1c020408400c1400901c0c5100305202c1140c19095107040c1c0140d40305403095440c1c2c80000c00d0b9100403a88082c2c11a82040080964000502114505904d238140110350340c01600c1070801c8020003400046170144990544842c0c100051b00301415039003008602c00100d0144a00d45441140c24000020840c5000c00c40f14061140e40d2030040c2d5810b094140b41c800d000004140f64155840310072540c0407840700007144554190403030280c50104140c004600c0c2031905801001c0c0c8242404002e02c0007000b000d04541d8054901707907540c98841181b0f110242d00381c60030004061300c420b00900c601111030402d0b030000c56000403000b00c01240c15400303036440c514070b07 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 589318633 1250 589317383 589317397
    0x1c0e0d020a05030115090605010f09050d03170903070b0a02340818040c030c08010605090402040306090605061009030317090c0904050c040605090f0c0906120406020307200703030f1103 81
    0x42c0919174104541c07012072290402a00080c60007843e00c91610301d001d45000c400340701e501d010b00c4100441c0028103100c0d00940e074008500301c2940d1007078101840c81c682c0d240c12001c0d017a10b03c4031a01010504517030b034038070842e005109210820202007181100e002684064601d840341c19041031041702c000a1003100c010074403d10802500c5460f210644140710840f0f1519428005051400007140800d0f60408013003411104107250032980d90320507502113800380c0951b40c40101140d060005e04c0c0100607541e000075100d1300d82075603c6141c50b0b151031000c560018840c840a000b01d0064205008100b20341c50311545d2005001e002c44075098546000704070008411501a2865085598605454901805410010501110210a203047c8900d0303800c4c05c9200500748901014000445800c01e495883c107840c401c0c80700380b010800d58503240c1042c4c4060750003200c902002411060f41c2064403204200c400e0043c6842030003c0c2030190841d0f40544296a66a4020007440f20702108070f010350000300010300701 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 589319883 1250 589318633 589318661
    0x10809030c0f060f06031f020d020d1505240f0706061e050301110f09190f090e060f010324110a0c0507081c0813080f0c1c0e0d020a050301 61
    0x96440c0001040b04c03074120113860640300340c0022026040103080e821801c11f02e4101c0c500300583c1c0e81c22480c5104000d20035200012511f60030030103180c17400c1d0b0005c9240c1c0301b01c0d1010b40d9181504a0030305031030003007180c800e51344032a144001e02212800c0b00146018000013031240c900080c8864036490110564451756000d000c04060041c07080c4401c1c00c00f80220b0314079585c0c0b04151400c0064000c1540c8540c0201c00d10540590002c10002004442e002107000080086108060000d40c0b0b48542074003404659025032403d22031000402c000c0128818646c1c12a40c200c60142c05003003038445d038840c06086182d00466400c0c0c881c02c4034600e440302440208410307081500c03101071006862810603703180d43c5502c4848941c208840d4a04070081c0500c480c0c14161051030500e40c2c40c1d40d08140040910b00500000c3c017550700c04607201454004501c020702410303113041c0886400034030b00010a1030740444180c10100041124203203032640d04000d8800845688001c041041c0581ca8a0209003103403150f21401403 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 589321133 1250 589319883 589319893
    0x120709151d0a050403031401150f2a1506060503070207050306010302130f0b04061e1202030c090a180807060e0d20030c060c030708010b030105010503010b0f1b030a0201060b070b06010809030c0f 85
    0x2042b0b0f0030500321040d032119410b044c0340344410140316050511100c40403410804d01d805400d010440e0091306011a030301c503003c1c100303d01611541c00a11a80044a0000140c810090045064a40001c00c1d60407130f0340c01000243c0d0148085d03400c102822043c00d140c1441900c440c034000302942c49003d960041c214206405801e181e090b07003501c3c900000c1703030b100d1510040747c01108000340e103010a0518200505680407031094503030075040c20040c030101c8411401d06202026442c20400104018900c541c0038590500100c0f0800924940303c604e000902804500c0141503416602003807501c1d504407413214410349003040480700340c040c00c000040b10318400500d000410010216007001c1401d0140c040b152001d402e541c10100003030064881802080103035007000c9224198038203010212200300d0003003800c07a603500003400705c03050340c0b0b40041203548050b50a040f80468214014020b4070f016039000b0601e58250b45840f001518181700240034501c09010410040c24191001c02503225000c145000a00c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 589322383 1250 589321133 589321169
    0x6020c01270311031c0e01030f050906070f0507020306040b010314030319091716051b03100e01060b07050a050c01210b120709151d0a050403031401 65
    0x108201107500d0811005203800d14510100584141000c0640b54042400a88207103140b00182c503040c009030b2000d1151130804403406203194010020309261000f0380b014400d482c0180c20403000d89501f111400000e40c05400058401031151881c84600011401d102e86407a0703c580210f81440d0080340c00f03560040d2464010010440c060700b10315440d4032503c000d141542414080d840014415001d01d0440302c2d1680111030922844080905a0381c0181c620b2035614860400740c001e844850701d170141c50b85e000d0480d0f00b40303080410039094034003aa0001d010b402075160316800c6100516080008280644d660500071444440c000000c0000c80d000310010072004549203401441c03d1601c410f494104076a412030040110307100340460344144408400880c4042d02040428001d980c140e00c02003ca21480c0ca002440040310b9011005000c1e0382010801c030a502d51000414145035900c040e40d10200100005110800c1d591210343c1140c460720313022510505440b8020a5020b0a0300701800a641c3ca10b102 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 589323633 1250 589322383 589322387
    0xb06012708160501030207050a0f05070b0703080604050708010803070201050c3a0509130507020c03061603050c1e0a1206060e10030506030304050f121b090711060a18050706020c01 79
    0x40d500620091801b54613001148c1e68031900c0300101d500040820b0303075a407584010060144425009400d600319441c0d11421f40d4200145400015a56180141d281c0030128904500c47c031130b454140d6503400e0007145451195801140c80b9405000480b060340a962034085034801d02ca01a018800c0900300c2e400c81c2c6c07031031000c000040d80c0100c50700c61301440010080c00202c0d1f1181324000c10f843d9620030740040c1c0b5503101390050b41049050140641d040c080c203030400400c509003545444519001d59800c010039a0781c40c5c91030156105080d04903600110101217071400c450340c5001071852281034546002a20034032a0343c0f0b03040c1e440720f402100100c0d00b2500e40620b2401d04a02e0941c1e9060586802c1c03001d4103140b00860b80381c0c8698001c460044090405003175984d292903030303903841c0310a6050407550400d11346100f4100e00c00325914400e100340300080124110758400c0d0010300840c00503a0203811943c540d000c0700001840d1600031220000c0703014200101141c5d082c050305004000f03540241c030400c0116400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 589324883 1250 589323633 589323673
    0x50f09151c0216060e0c0a0303092309130c0b030a0c030e06040f2909010213050102030c0304050925020f0c030708030702060703031d010b19030b06012708 68
    0x14000c0c1c0c544140701c1001c9212079544502c40d80d82c3c0003500000d1440c1c000f00d4860512030543c001c5600074603c0c103000070170158082460403c9039482e0801d20040d100c81e648114603000d03e004443d522044e0380f804902c1b0404100c0c842034000344500901a4540d642d2030812915800841d00400000d0b580c14441001b031740c16004540703a0a080c000076002034a81542c4400c10004400d10150000c400c00c8103000000e0706050110b10829400d010203240c0d0304e0150134445c040d5002030302441000404007000a11940000255500316207028051070030a4201418007901c882c0c02010942ca0031074406050411402d0b00f10140310615441c2d01505400b030910182510b03020a4002d040d0081d44008420003e1844c048203603940142c0c122621a50740c84142821030103803046009800005480c0071030078212620540c0215103074071060342c1a02703c0d007551211191826019200203450318050f44006134030b03580300d280c18191800f40714120503d051001e8003142035840142c2c10a511961159028490f01c41804074 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 589326133 1250 589324883 589324927
    0x1f030b101212031a031e01060b03010b030c0306031207060b010306270b0a0504290f152115090c04081c09030512040303120b0603010501050f0915 64
    0x200e222403941039070b5a907007240c001c20540004256680b4084051045803000c2986010f00013800c0b45d20100da600001014544a0055402c6035880d206c40010448202e41c240c90407525010726803410b581e2840249002e0341d100401d00b60b4907010f9851400c0f8002c031000301800c034030b9000e50000a0600203040015080f00c24640040803807000d00b42e00b40d10201d00b842c032070483e03203036030148042680c100031070124203540d04039045a54040d0800c403202681f80c0070100c00c5030422481c540b02c0070621403c1e200341301440320741400c100d4001c15401810a40c40c5c0306a002840880304240d45e6188601d0102092501e018050754013450500e154135280f203042c500841c60942082101200500d00384c645440d140c0d481c1c80d085a03100703a40340b261085030300c11809564020000d64106007501c101c1d083c03c03444030000d5406404200c000c00c00341c413003c14000380180b14000b000b48016003010714603428000107482542000401e2400d00c90304200140080e1030304008041070090034404551140010004c0110005040d8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 589327383 1250 589326133 589326149
    0x11130207120c020f12010b09010611060f040206090f030c041e0c05130323030c0c012619060b0c06060411030f1b0f031003030e0a03020f091f030b10 65
    0x180c804409641d41c4020000381c1c41044404080300717600f4018250250903510b065980c0015a440001380a43c1c009900b485082680f0080d070b0400d5903030208a6071801030503180039412540034047d541060901c03004110071500d004044865948803080018160f50801041ca0700384010036078a01a461010300490004104a00304581040201400f00320354074910710000e006d28160105000105c602c2988a0503803841101c160386d03440080b9a601175550241814807800280c0c0845000381d1840e40c208a50013590b014410806151103500d1540c0c3c080d04d4168042039000d954001c000f900d02c00c0340004000006079030014120601e000000c020480b82030f028951240a0300b00f0030410001d80042d8802da01c045084c070b0400580d85c003600014014095030545071701c0b80000105000807440c0c3d10b44010104d80c0300b41eaa90038003094280500c03c52100310f100007034004400130510110b500d401d1700203580c000c01103407070030388501c98800d50800c003245603a1040e0b8001c016902070118142c0c801000d280a40360355 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 589328633 1250 589327383 589327397
    0x3020d05090f0d03110f030c0f070812150105070b09160906050901060e03060403110a0c24140d11130b0a0e040506060d02070609021f021e0a0f1113020712 68
    0x40d4144032040c407506c2e0100807506800000200e010070701509541d89203a01c403450b140c50384114034080440f540803041000041e800c5d40c0c00603d942d4110983c9920715501a9601d030b007024401d5550804510700600b07070500074010754441610754949081c811303000307250920000c40c2440c40c090034050860340c10307080542088180301414009840c0001e0194000742c1c10328000d07280c48500c240640c1400d4501c0c1004207965003520000540b004003081c10f920300c1c00c41d11070002e6114102401501e100612507002ca080180a0000140440950740003480d4124036840d540c1c41e104020042c3c1c0182100b81d00410800d860200c0d020201c5035120300c100c1c4020031709030703400c000701d041903c001405030240c1c0d0b44406603544c0006c3c208082203101c0d0411880b803640686107404036610300c0746c00c080800c50005628014400e40c4040c0e40c5940d40c6408042401030700d8400788c40c6032850307515600c1c80d01000e0030040d04d0095001849104645401038520020f0704103000042e10b56402e4074000c0090031602000d8401c02c504 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 589329883 1250 589328633 589328651
    0x5031614060403120f0525020906031501051e040c1121070b04030c150c18030b070f0512160e04090201020d030b0307030c0902090301050702160302060a03020d05090f0d03 75
    0x566062813409140700d003401003009602e94000c42e114403c0b4a11180ca404a18054042d00b8040c2001c05400c00d00c02c40d09403001d42e0f030381750a1613a270303010600c901c1d910030851100401460070700d62444220b0a0408c0a032029040c03403007022a041d030354074058840004100d84d14941d5401410f2008085400e078001c43c40d48421810107071455507000e40b41000d030081111f01d01003010980070f0007840c2503595004044020040406185000401e188202e0a02040443d0405500d00c81e003034070300c3d03030681e94001e00324000380e05c03502d8040b1142584100020180130003045000a000000c0c607038035110321300843d840e410040b842c2c1c030010010041c1400e0302c1d0013139081588860060380c0100301d2104106107480d00103000c102034030000b0f00e0300303050f64009401c21107004004507150300103030020003d1284c180c000b4095502d0b006004c0303075100c0ca41d80e0443c0034506e10032001c2c070061410100410300040315240160405000501040840d601690000e8181d8040e00c0d902c4900c070008e22034480b503901385080c20410209 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 589331133 1250 589329883 589329893
    0x608040b07030209030f0d0807050c06013606060905060f18010e04090c030c0f2103052b060603060612150b1b0f01050402100f0905031614060403 64
    0x50402000036405000044070544668190780311241c0050131258691013a000080e101c81400001c1800160300707000082e40d103030080c800c031840c580b40040140060b13843c01c4900038030803686800e10b440020500115085034094101590410309904034000b411a19201025219014543c0034030b008103801d200e5507500d400c00d6801e48102c4001901c100300d0005503040101c0d064a0304c6078102d940705e031401d95103d0501c85c2054035401900e208002242c00c2c540c45558030107090000d40b086c84070714800e1440240d000d4048040700c03404540b1900b44281000714105001000d080600352072190482c83e20b5001c1001c11003805410014410303810100040d904007a4000c0110040c4036520050585540000f00f8031200c1466040003406400d810795110f00c0701036001c985a1410f40c1103009103110301844c0186604c0107100d21402030358004c149200801080206542c030406040d003071428000d07003410000d0f07a51024081e0112406a1030394003810141030108020110040b44980d9000d0329050100b400012 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 589332383 1250 589331133 589331147
    0x15071b0f0b0a0f020c09060f030a06020c070f0f140d03171302030606010e03070b280305060310050601050307111c02032203080412170c010b042915040b1803010c080106 74
    0x691f068903181102c04032400400c3c5054090350b03000340340c6440040c1e907040f014004901101035405000700480d1036039031904d040d5514022401403a41c0800c0c1d00340140100e140c003000d00740b0080d10a0401c0518040c1b0071b84684903c6000720b991030800ca251000032400c502d41031051603031203002400c06041d109800c00100b59115154091030410b51030010344111544a81c1008030000d00800c026600c0c24069148002c0180005490b07241c000d11440310890708030342d402d001b054401c520603943c143c00d40d40c1d8208115984006145001e009001c4e1804050251100d0010701904c40c040390001c59880c0e000703048500304410350410300300301420b42d0107091002548440440b002c542000c0c51407a40341b2a18280442c004000c0e01c6014818030380090228044c640640060040d89401c607130401001624504414143d40e407440f58050100c5003d40e40362031858000b0034089103086413a416400d25445c1c040f400d0203540880c031041200070300d03000582400e19003401144c507445218585a521035140010241c00c030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 589333633 1250 589332383 589332391
    0x50906041205090301180506060d030e0d06020c0d0207051e01080103150b0d0c0801060f0e060111031c0209130603083f1515071b0f0b0a0f020c09 64
    0xc001c07078000300240d11510a40342110300c0100200302c0c222010007001ca216100710811545d42c01404006140303032824088980c20741c0d42680714003040030001c00c10014284030113102103400700e600b440f45070802e100400016010310032a0700207140050a00d8100004508010000034004040d07441d400c1c1a640e2104030036045035802000384100003c00300041c0c001d0300e1222002a04801c10075110014414103c03100300c200c8000c403008000741c80c1c441c0c000c00136141490040f0123600e030600e0302003921544a102c87d202d00b9030309842900d041030f1002d032240ad0210380d44568402495004501c0c4c100074607054104107a6146605000c001d514610f0707031040f4a6000d140c101c0f4001010404050041035144415000c40786600a200d2040c4088028108861207064072041c10884004a41119500702502d110000070a008111400e19480ba500c00d01c45c1d040c03140301401003480814001034040611016074010b040c164030a252140c03880c01009141e651115404011940018040703002e076268541c0090304 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 589334883 1250 589333633 589333643
    0x60d02070807080f041404050f060603090f030d060501030f020717070c03050d050a0314060913081c0615030203040b011404140a0b041d10180f0303050708010905090604 74
    0x31010a810000c0c80c034021010040c001240002e80750101d207190400500c2034606e012039201054207188140412101300716041a00307016800e020a00c4d529019001e90780c4202d030384045400b2909100800c07401d58021420f00c20000d500c03404144450b617094011f01c0c0c2c0c9101e001c035007182021007e8840009030f0507684201031100e00002203c50038094045452009150030004441d200b007201d02c0003c000d54411528140007038034140c50075641d00704e03101296000f040014840d004035202e0301c000100604d00c8120444141501f0030a9203041c00500d02055040e52104900150461a0a00f8008804158041041010b1041003000000b6520b6200c15041d9200710120340812010b180200d0300810760544580c1c62192500e04001100031140c11242d00c0341c00580c1c2c1408050a458071050305c2c1c5420140546031600031403000d2100303101c0c40c1d010300c90300301c8207c0000040711081e842e00c00301e0201d151015000283c41d4010040c0c1242c001200354010710391a00204060320b850b000b002e840c1d0101500081c2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 589336133 1250 589334883 589334887
    0x12d0e1002031314100e0a0c0e060105070606120c2106021c090b0108010b04020a08041b03020d0302030c120f0715061805150301020a0816051e1803030405060d02 71
    0x81102c400c810403c2558002011401e105024025640c2c80e264010040310301400c01a1440a4101c0405c0584d881684031031010780c0c240c10304040900e0444c0c000c20007810000144403070404a000c50043d5001010b80c84040001281581000d051080d00c41e0010741d099041c042d400301d0004070401d1520722036a0440c03801600e41015040070b00c80d6030304d210704a0f104c070790520000ea4180115101140c0c1200c3c0d0240081204102d03400500c8240d000b80c106407070102d034030400064040350341034a200c0310111180c6441c901d080d4036580050000c055006040e4010383c404101c1036003880e0100100f00500344868201c84c1488807080748d8046511030204d008180f6a1000b003840d9219501d034011102500010807003072140c1901440c203034028041218101c2c17418520385104101030606108441442c01207696842103580c3c1d101c40000d0ad81507900d240000c0180401a00c2224401c460f242ea03169009605c61656503840a640c0340c40514800c442c16103e60402c100801095030b82c40100c030080c2e03490200150b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 589337383 1250 589336133 589336141
    0x906010219080a051219060905090a063b010e210a030f1107020a0e040f0b041a1e150915060409020c070e0c0304080406080c0c012d0e100203 62
    0x71811702801d4105140c220900c0c1c24440d0551003210110021204c44d40f00708400c41d90340301e00c0000c1d03800c2925441c44507003014003d1404986950001c40301100b03550007a29010407a035811a030000340040720740c0032560412000c1c500c10502809402a000c0b042001001004454603592005034149009110318040025000400c58042d41181303402248520f41008255001180020207600c401c208a20a03d06180081201c4040001c03180c05241c0080071401c26841d107950300c00044402400940d1440a02c44104154107210903403203204142c0003003607410f001d03605a16982e80b0840a04042480d01740c001009100717403030381c0410a038061a001c510825649440000c44d096200c2d503040814441c0c000540d03005140d0002429008542078104079148035a5401c003541202d001c04d076002401800100300801106100d0101389800c40d05042d0303c3e034034040a51000900310f88100105022140000000d5510325919408501c04100d5525013840040841c1019940b40ca404451b09040d480e4040041 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 589338633 1250 589337383 589337387
    0x1082508060f0402010e04050c031006080c0307050a0c080f1b0c030c0f0f030a0b070906020d1407330612151503050a110a0f320a030305090906010219080a 68
    0x1000113907030140080088e81031400001074590b204480d410207041100314009905485401c42c0751103004110b0303109086443e191004c88050744103005003000c0121546003540131951f100300420705a070184187c5991000b51190103450718031100200704c1c0c00d800c1a641010f8540303000c13401901c100c00c11150740501d805d44a000400241a84d00d0841d0944100c071714110412180c0c594041c010340c159298040d0039540c92030300b2603503004c0c0da020740c1c000a5144101e0400e200812400303480010b22a01c640402400c8198001c80c0c0c45500000b0688400418101032490742414440e000c084c01d881100012400c2c0992649507262140c1d4100b07009e203a56480c47c0e11181ca01d15903065010719400010b65640313503514200b01d142540c9200031544501c1e052000004e1031015041f07030344111404d18002e1046040c00c2e0219103110242943c40e11030321584903c4030325003640c418012101452194541c40e4030380100405114a050340241010305541c41411104500c840347c03800e0110060380109003c0c1d8903424078400b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 589339883 1250 589338633 589338647
    0x190b0c030327031b1c05180f030a1502040b03071d0a140613030f050a0515010609091e0c120f06030b0609190204034e0309050601082508060f040201 65
    0xca50389500419810001c000c6d8007600030038880b03a40030158140c049180c800c0040682d20711084070790550002396080c001407034035002060400c400348030041c20123590b081121a80d40c001c50301030001461240c184003401c2008400d4414200b819254100c80500344003040b10b60840981e1a68420100442e415032096024013180c1c0156900145500b480b200500e003583d42d4442900040f2990701440d5080c400f03101035203100c241240e80a540c2d866020b80f500301032900078254810180b0300c241c441d11005441c0a07650092440c181455503032110a1294003084008440c60010401d1201d030410400b0004961014034503608120f04036407001540e1113070003032821001c00002e10354950500100380003080c4408040c118600e480b10b0151323504c14410652803440b00743c02107511a42c00c403905000e409651040e840300131000c045c090800051a00403074641d64502a002da0090481d5404082c1d0700a9000154104901402c690749840b01c440e800d00c0d0000c0d444800c0240300c0803400d60040300240540e031043c40 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 589341133 1250 589339883 589339903
    0x1051c08040519080601171e0f072c06061e120420060c1020041401030605010c0302060609040f1506051c020a05190b0c030327031b 58
    0xe01c00c0c1d014500c410380e0300d4051031441248203d004410000401401100208001c840400c0143c003022011a40d142540c44a80080240034440c1b10f49c6110440c00030030903540030f440c2e6110070254034405803091602c281200e800e0009803000e000c06101180c0c03030300d106442e0180305c2c28086040344c48400c0d6440a050103030bc0c2140c88600c0105007440203000581120b03007015407801200110032071100d02440254484c410f00758907180e0040310114010406980240d10b078800d40440742c0ca10080d800540d41d403e80240e00803880b203204880e10100990380611a07100204020700340508403015a46002c0d464140c002c12042c0034082c0140020104800c461706807603d198016031424210f40c90082c0100204524000c0324042d10100040c0500f11420300540580c1caa40202003007402030800092101d000005e001300341c030404610b4000300f00c0d030310040054840b20300154019501c9103440180f883d000384c800d011894641403510b83c2000490004000c0302c0e10f83e20410440b40c00890515526845c0c110030003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 589342383 1250 589341133 589341139
    0x90609070215070e04180803060d030905061810020f070e07020705040603081206010302040b0a11030d05041a0a271103061f05040e0c010f0302120c0903060f01051c080405 75
    0xb804106102c0e8028980c100c4146055800300079002d00000b00c40200041c2d007001414504003840090b207076203007104c1e210044a05c04c1c03802e025982e944d1404282aa000f140500c004090980750703d80c5e0600b4285100084200c0d144000e00441c4151881d040c1c680160380218008030202200184411b4001c010f0107000784000f0b0320821030325603a81031605145d0880c040012101c41c401c001300d800d41d13109000b5201030381c400c0c0e0105032515804100c2a03030700140c41c1036441000e00080c0070118203600ca503c00e4130b00c40c2e80560054500406001d202c041440340040c40300011520300120f0005240c04150001c0f05121903289485030000a070900c030341594800e01c255a4944240c20030401611203c00315042e6004480c0a01d407000750b101c1c401c1000f540d040c0c0082c07040c0e40d40f00380182d0546600c00c685001d411200750500610744101c03201c2807042c445084503400404400081c81070780504040042592000410140c9030545d4109130000f0051141a90b20006000000c580d20043c04194812500107103801 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 589343633 1250 589342383 589342423
    0xe0d03021f05010305060f010317070203150903030f0a020a05040e1e0403110d1115070504080a0b0f060102160b090103110309070306140115030f09060203070305160c020906090702 79
    0x202441c0a000300b404121110300484010802d456421080755040c8c1e5808480d8030b01c0c8101610b00c48000341c00801c400c0e64113108040c04500c1410741101c181c1d010380c507840c0241d6078910300109007561141c00075207550b0183d0310421082108550200030380702a104440604500e075201e565009161500c21041d0031a41d2120806100415402100c505c0240d44400c09840205c500000e06468211050142c1d451541042c0a20407207802c481c1070744c0e03a2000b61414031900749a11082158a480b0608400304e40d00c03038005c02808107100d2004542580b10000f4401000300c0d500c1400d0705101a403980c4104002040c01203114961030380660408010003198090054480c5028a4401d0391565244401d481152400740000c5141c1c40040340107050701c00e00e4004400d251a001d208800504198020300c24083d91400d01d40000740c480d00045001340380564000c02c081c100001c066415051000c451424041d0a4241400507220340c030050b644410111501245503031a40c0c41170381400d0707921998880c40018 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 589344883 1250 589343633 589343683
    0x3031d180a09020a060207030b0a2a050a09090612150e0f3016080d02040308091801060f0c06060f0305030c010c09050d060c170a0b0306160e0d0302 65
    0x75503801000d4150003103403a108011341e61030b0103076201c121900014108840c804000b554a40181d0000460b540c4045801d50380140c005004032006240c040100b8000794001900005456009003680c01030311030248100501450315620b40505019104010010a0817600d10907069506170b0064111a884009031482020201066901e440c0c1108450301c40801c94a102021000c00c54031060540441518075450425000d400c203081001c404022035100d101000b650ba0055150300241c00118170030400705807108800c90810061008982c680000d2848c081c00402c1903690240c2e2524000c11241405140b1004900300200a40302a4205400411080c0d80c0001000b2000004140800152000f0095010302c01c40480344072840d4440c00d0f5210102c8851311010030010b0744408075643d190308000010001180040d40d4420f0308941c9c40c61055521640c0144034142441006d0748039410300c0f8011120307041288054941c00700d00c400f0500801c42000500e01b010300800c1410300408107060300ca0b100200c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 589346133 1250 589344883 589344901
    0x10b042303010914010c031a0f241c05090d120b01050c0304120311060105030d2d0e0f010e060f031905090604140109170c1002041d0105010903031d18 66
    0xf0700109000006848e007070404041c003403c03120a400b00302c0010031a050f220307481000c001c2c18030844800902c01b8405040d12070741a000740303c0202410032210303450fa900078400002c44801c40e0700043c1071081c51381110290441d0198450000d00c504d82001c00f0010f01c600342200100d986000d07450f6010700030301c000100403611420144890100610035624040c580c00b004d81400c5c0c0b220300c00c3c400e103a0540e00a03a1401034140c081c640200c090044205803020301c082514504138041d01000520000c02d07a2444078074620f08200c80e030000c090100b82030500a2a0405020a1581c4030344626502e1240004c4081103440c00f030016001184003200009001900740800b02c2034542c0070564044074072201030340c4946c05105c81070260324030580d04071003100789908001881e500680d0008181c00324502490184c022400d5892025001509966242403665441000d403840000410b0700314a06000e103942d02040001da2000c070a0583c00114103680d20703592030754004075464428800328030383c460501c02d0420015030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 589347383 1250 589346133 589346141
    0x50307180f090b0a15030203061f030504031b0b01140a080d0f031a220621060c09050d110d12080f0a05060303090913080301120b010b04230301091401 66
    0x6800070310800c040048141080132000a0344140054014542c0700d00d50030300d020307501666001101a10b81c2a01d0b08080c0c3c00000200400c0c61520b0219503148244010301d98052030504920198030b4000c0304400694960304841d00c8141b00e600d022641d03100c00d642c00390301d44c0f900840c010a2071500301d40b0200500070020b452569003041d1100041d15100c0c0c84501030540002039260104007a0074640880005408480f280301e602e8004041181c07141d078009034010500302006a070388482c42c8005540800d41c0303003542c2030f07411640105c0c1c1009038102003400107941d04080c090000b0792240c5400c41041c1c00703a01007540105407520103028407603918030b040251a04005010b00c194030708102d00225659041450b8201c0304141c44560f055402070055a01c9403e001c083e5a400c229030f1381807045000780c955030300d4140390700903004101028940000503040010322030405000d0255404210300345030400c0494850b00d600c82e6140c03c01c021900ca00c5640720344080d40545c0e07200d90440142040d0300e0007403552138068 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 589348633 1250 589347383 589347389
    0xa0e042f040b03091f06060804061d16080c1f12090c0906090c091a0c013908040b06010f0e0a150f08042001054e0403050307180f 57
    0x1e828a96458283d805c50300c100c03010b80c5c465854044141d1280d8942100a045042c01012001601c41000e010b406081025000c0c3d52403d41c1070704030440c20140520304200310400e14601925002040d41038225a50104109040c0789160000004491109041c060400301101502c442c407450400308107200f11b46c0025040d1050181c0c14080003a10400848100c0f520348500b01c0c0e060f4204098509000c0000001c05c42c2c054541d0000c41c0d40050280c000c0f0503420464041c01803411a0500062298800d14080d6103899060400072140c1c41c043d00d80318102100200394604210b84c0301e003283c0300fa60103101c41601414002d004684816142c04d0543d00b5000110b00c072001150401c024060124031034060300348680e41c043e1852485001041500411240d090241c41c1800030a0041076829001010503900340e8905153780e5100404426180e0745031041c00c440c04100641e00c1442d0700102c4c0c00d210303809411607414038140d0750340d540d41c17441216200207114203801c010800880000740001c182840b20300b5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 589349883 1250 589348633 589348663
    0x1140301120b0f09070618030204060b0405090c0301030b04030e01030608150a1109030c06090d02030a0f0c06050a050a1124010905090102040303021c031409030a0e042f040b0309 78
    0x1e0780d103c0e414503102d01c1c041210b204c1c501d64400e81060040c24070800540d40b009030301d2207461001d0307034403580040c0c1a604035400101500b100407400f00400d2a0050700c482d081408480d4680c510350568854904181d001031001d02407082c0300140f0040d07a440f0f54440e00085c41c9100a407024000100a51052003106440c030f103907001c0c20910811030601c1d400b81112600ca60060092000c0b1000c1d04c1804440e41003120001ea10614901ca80005030300c3c24444402020310400e03010070380c090b280c602840040b5a6030482c404000040c0310020565820104540409110381031580c0f03203403c032840d894500364001244c00c0c0c0c00081300003140e01e00c0c0c00c00074420b0b040c2c1d40d141e501840a60780700b1550500301d0041d4030010380164441f4056a0040300c103103510150b0f218240c5000700d007010000300f504600340d40a56095441e075000040d604109a40941c0c00d000c0c0010854091000c140c0b85050403000703203070f40590307884502c240c0225003150148040480d0018100c3d400890307100d00d00048e1301034903000300d00c140745a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 589351133 1250 589349883 589349903
    0x3b0703050609090c0906150f04030326040f0f0c062105070e090709050910030312090804090f180305250c090b12070b040602191109060114030112 64
    0x1c900e00e03001c1a040c1c41103444000804080c08070004001c1c074200302400c0542c000744081c940c0401150410018103444031b8032240c9950319031442c40d0040250165020070b4011a660f500c4541c142040707604080e8005400c82c8101c0c1c00d000311400d040104414400002b00316030240c0c400000d0f03482c2c100034803240c172161041d015608038640d4000e410655108031800c0002441d90505106580f41c44101c03940c101704e07140740200041d40c50320f0100700624004d440c00e0106010b0007804104040c0d001418541e0341500910510030215265515078040c0558041c6008482d282c0f841e102001c01780385d00c12944a1107024a0a1046156040150065200c1450301e1032014401705007105154920081c072890a03840210000c0d120320342403041c0020001e480d102580800903908500111008100500180440488403a5203c0ca4264041c0c58180d507001c0d0314403101c0b6541005000720315640000301c000f0b8019503044070181c2c1d80d40b0041311001c1d07440c41c800c240030740048000714881c185496040003c92160707000c40 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 589352383 1250 589351133 589351141
    0x106050a05030606063f010f06020c0108072012120105030f0a0f03030e030c1f06051c0305070c12020f01110a020127060315090b0a3b070305 62
    0x143e1200001c4520b10b0700700741c00300301c45840242040420002410401b540e01005400307011050340383d00e8108468181c290f400300040c4000c0c42c1c608504401401c1c0c43c0002c00c0c004158100280c0640340007003442c001c1c007111400b010108680c0e400b91100c1ea4845209a07070340191982c1c14440c0507041000303000d060389031880012407a0704002414104428540c0e0052400403503507030315041c2c0d50190101c00c41c100751701d40c051004160803c002505100350b4900140000c40b040603400c04540d01c0703259280c1c60460a0a00070400fa4844100000e03048400c800d1400c266607103030400340c4e01c2c0c0c443c00c2001000c2004000c000146942102200b02e90700b4808c81e900c03005000d20b44011612100e04500302c4000d0340180d5582e400560040040c1007108540030030b18100340b20607440d85280e40a103503001d0000309131640300c220000540008490040c1585000800c9140082c2001c2013403048240030780c001c2449041409503204c0c4800d1076a859103038040003504803e42c080d00070039031403000582e80c10020904000c081 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 589353633 1250 589352383 589352389
    0x90606180f12080708091003021206010f0905060310050d03110f03091507031110020703030501050303040605120c09030d0309060b0108012412060e0106020d0f080f040809120106050a05 81
    0x10400c45031140300342c10007400240c480350b5166010f00c10031a48003d04100107078290315240c00039080a850703030b00d0042e214808198081220310009182c581041a0354010b0000380d500071103400d054820903100b1a840f55038080d0f40d4441d060641d00160383c848880c8505a042503441a66001504c882c8816260700001c1d0401b02c40e0390f030141e4a8610342c0a40d03c10020004060000050450706000745881840300c26070505281c00c107200100c2c0c94081c1500001e50006060301070250740d0041a0550046207404c0ca010300081c001e0040781c0c070145c1d010703103204045544101c01c201a203108d11402000d41d11510841030020300103207040c81040b1206404c0200101066005011550488103007400c1547d03a060300d804c03e450354105151000090004e80003000040212720301c035a4000c5d046602545245504001c0c008e40780c4103d4807602c20030007044956040e0f6560b4840b00300c0790030658460003003c03079869078a81038025008852242c0d410200e80105032000c180305410042c100c9205a4150212a0300d65080c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 589354883 1250 589353633 589353659
    0x1180302160602031801050904151a0306090609130b2d1306020306011404030b0402010912050c0904030e0d12030b18040b250801090b06040e1f09060618 67
    0x1e80b00541c10a200b440d01c0301d190505030305400001450174502e409184000542184c54085442d1006c58002c40c040c84810342607100c151328a07013544a140d0070347c6410030018140d841c006007054000c80c43c0ba00030843c02c21603d80c10601141e07014050348102e00d042d44d020700031106411558040404248801807040500c40c103000c0c0944c00c11011203006d140b09460303401c0a94005006070341001500d01c1401030501e00c1c1c1d0090701c051441006e40e042981420b000041031070a103900507420b82a40d50000e0070020b8800039900040e101c0a0b134540c500740c0d55a04059a1454100d610682c125800c030b00b2034000c0000305244800c984105483c100041168802840540600402076007401c480c01008a00401e40301741d03409510a60070448442d106000c071140100200c1200c1c1c421021072160b100501940145003e20074010070199112810705c0d2030080c00d4400544090000b02d003040c1064019800501c201c82d0080117840b6031a01400800e070f58101c0284030b0003243c069402d0034203090802056018940706 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 589356133 1250 589354883 589354889
    0xa030216050a0509041b050a03050102040306050c09060412080702090c1306020d02254704030f0303090c0609050901150534060501050108090609030d0c030605030118030216 76
    0x8010342c120b0b505e554909903c2040403001040360b500200e80054142d548034891400b451280c00007580300d900e5450080150303075010340b208400e084113010071311554503001e060328211402c44205a800a140342810f00c81e9104144c00650041015030401c854065581c0003000a80241c226403d0310545e10303101203807104031001c0b044005801c0480b21a0340f400b001d4181c030310842070b0741c06000f00c900e50311a0304c4070030642c400c82c0322045600d070300c3e45c107220564401d10b481e80b510050004805802c000448103200314071950000030181c000b101680310a041c401d9205074403890380521005e030702ca503c1d406c01624115081c1714082c419408800040b80280620306405403020581d02c1d22428050100c140891481c8500d110081000010701011004041030401c81211801424005582e50400d000104400001484418582c0c0000103120b55007000104880002e000d40c4800103040328501e80407409040315620841c0c0c9503080c13140221020a2000811461501c250216260f0009a8005030103c4060384 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 589357383 1250 589356133 589356139
    0x311041407030b040e060702060906012103050c01020d0905031806070503030601080910060324090b07121508060702150f040f020a170106140103020f1c0e0a030216050a05 75
    0x3804200614040d40001d181d0322030007400465a2201c0c1d015003481c00d00102c420780b00581c010740a1141c55481400345501426046e05410300e400e9000114089c0c0200b400340080410200160b40703400e03d5020741c10f03104c600c0302d400c000f400580d841d0f05106541c0d402502c00301c604207020361840e25051038014215204164800c0c095819a9154001919a07400003003403100540121101c03409030049521480300518031070b18206621040d205044d80215244815418500d4070f05001000424002140654003900768a4100a4014401408009071a440444c4142030b5406800481d0b02e10b0049081841208641e08803948904260a00244070800303032480d41111641d030000c075011612201c820380c20389002030079028400740da454403a580100800310584240c1d540321030600062288140c54012520240f90540c00c1800c60340e1980c555114141d07108000c1c1703a036480d148034201d50b82d4111000f10108801070710b0030340103207080103921140b41c10750a450707081120b0b40104152815041c09002e031031000d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 589358633 1250 589357383 589357421
    0x7171b1c0e060703030917070303050c0a0203120a0e190b131a061512070206060303031006030b03070f0608040b0906040c09020702031e0f10020412020607080d05010e01031104 77
    0x181c400d2044603031040e1000c1d0201600d400141e00800c010358003612030703007070701240c2180e44980a0900a0480d0707005080b44a11940801900740c1c0d031a4000144d8480744000c10903903956448581841e0003c0500c03100104d0103016400d207400000d903114855801c1d5900484400c44140da40c002291125080480010008500c0c2c8568514821415024650001014066480020700c0d4560701c030311504502c02d545c205501b64000c0200e01e50b8140070b4190006000d500131400c5007081c166100c005501405203208060761080c840715140e03410003058005008020100d00c505445613001425480202c60556112001c13a02185d20752038006541c40c8219000710000c56618103008504000c0d603c1a030f4260b902d0b200b00720840c802220054816100c0400404c010a84e40e2022500281000f808800110340603105110411001884400c0d40010300d60490f400d559980e610706c0c00a01d20f0082105a44100e46018008104041c0c50719000d4140c03801804505100203c600800007551740103640d11394a2024 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 589359883 1250 589358633 589358657
    0x14060408120d020d1803030b010e0616030507061a010f180324050a200301051f02030c2e05100506030606040801050a02070b1f030807171b1c 62
    0x550310241603142210340300036107400c0480c400d0405175880c000c003a050419038070090404042d00f5100340d00c680368080c2031100180a096000400c030b4043c0180a04916640050303c0007058401c004407142c0c0c1d0b038041d10410101c10f40d080e000110490107815140030822100700c241c0720750302464a90010340703512801e00d440f00307007940d4505c2da0034011144c1c00c8444221682040941c45010700403240b0132020040002143c400c03002541304d00c40c101e410001640c0700100700502260702c41d041d0503182505006507861100740000c1e8124590f1141c1d106040c4980980e0722217403e88021021549200d1840d00301c071000080950b841c0d48211101a204100c00a0790110304100c00d0601a01440d44139000610310750400e5901c158075429035504507040e42d917456000440380d08100c0180066600803440c0c0361600642e103092000400c00d40f4235400080d0a513580841d0343e60810000803e030440d81c0a40b03a19964844099004e40400056030030800c0405020785031081440111b00b00c1c41c8034464650742d980002580b8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 589361133 1250 589359883 589359913
    0x10818030d020d06090f090302010f0605030601150c23070e070806010c081b25061706030c1f021b01021905010b060a120c031a1c050d030614060408 65
    0x200903041021030381c1d02c076a400900f5203424400c03032070156042d00c030114a64100303123070090031100c00e503944c4a002440d04078180556100020610b042d138040d108004440c900c03516058646440f4208010048040c5003000c0e10700c0304402c4080c44903c1203803c2102c4402e07841d480c5051110008544c1c1200003038410001079441d40c82410742c20500c40c024000940340000464506100300b08441c190503c07a071054007000c0e03140c08400a6100262000070300d440d00503013045030042c00009020046144e00500c44c0c04600c4c5030390103001c0d00120381002004035503012000e9698490350301804e0220405406421030840041030340f0520f1305c0f0601c005a01a10441c0314100d101c5141644483c4161965907903800c50740c24a49604000307140300d442c0c9131a072038000074550f200300e0b0640d03403450007280425080c40b001c075040740030320640d6118210b401c071051840c005a9298182c56607403516000380180c4619901d200392a50594859410b680308202e80c40e604107084414021a449180b00c0c0300270650120a038595050 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 589362383 1250 589361133 589361137
    0xc0714060a0813082106030309012f100c0813050c12120307030504020a0f1a03091032132a0b090117040c030215040504050c0405010818030d02 63
    0x91441041c4011050a0311000c1403508000306405c50391a04c0c007482d030840780c01101c2056000900320001e42c0342c0307184440028917a15040d1500d0000c034003100a0140600500d0700c190b0f90f42e000b00380868940040c44e00102e400780000c12000e1001c02c1400d400718115085600326615003c0e00030009000030390980c1d081c4905801c540d030102c08107004401c1910762400c80400254003a80307003903402140d07a081c0b60040010f029815806588400082a010400e13004241c00c50814211000c0e51a5140d03070f140340780d0a080001d188031036014145415101c1c05c115600300d00c000c02800d00088102a09400c90588440348441a26007000e2a4807448c034503400102c1004510b250903840c031611001451465858041800543c2c100003941c1070f0104110034503580c04004401950010101081141419260389038000f40c28040a40681002c147c2c0d82080ca013480101c0e401804054010091458000c0e0f20034001d0704180205400500c0700e602043d80091451149240c210314140a1842c003013940312070308025 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 589363633 1250 589362383 589362391
    0x402090c070219031707030801050907030e030c1b060702010c02040c0306030515040b07050f0910020111040f1d04030816030b0d0b19020309030a030e0705060f0c0714060a08 76
    0xe4841001280016143d4845848040f1032100b403103c426402c610b884c0d21064075408581200800a0106102007607102d480f841c1100c2d000e0b07405c0c401d40c0d100c4201c101d002e007007180b610200b18400003400c070500d1000082c008000003820681d60310100070540c10403200c1d00c01c08001900003000d244000c8003514282d4850041250a0705002404560f40d507181418010032030007081c4610300740400c01c41844410b14203203034081c034249425440e114120800c44490300070050154001c8400104100d2402c0c002d500505401c030f40702001c43c1e03e4655550301c4c200b4044036030040c110440104031413151082051a0b985000300e601d520303054030a40d10010008400c01d00ca4100030704168407440103c0458864803554800305001d031610340002c0c68420000040b0040844c036140440780b04008201d40485c021090360441d04242c81d000c11030071403903ca15441c00c2d025400a550007100003e010a059184500070030203041498181c0700701ca55160015019a00b0020110b90060002c00140404510540c2a181c1c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 589364883 1250 589363633 589363651
    0x51c05150306010b0a020f06010e0c03130b0c091203040e04140106090204031101020c030a0506181c0e10080609060625030909110403050d053a05010501080f040209 72
    0x400c03480361000070300e00403007030381300154000c400160040b03a1030341030005613400c0702d9060041200c0d501d81240e6103541040140120090705c0040046092420701d030560302191500300200d503905040444488440f540a0700040c4d110300309155031910914000b01c29102198003410390b83c80c4030b03030301c50710703484000307002d800020300b2656070368070080741c00d1002d880900051402183e0003030003806a10700180c503080048051f1403003a84444030a20002d01c0c00103031b01d80e2000f0190b401005800c03011000600d00b0300040001908020b004200804041d4004e507100b5000381c0072506418004090401a03619110603a0805d030801580310014000e410440c00801c50340c200120440c5200028020340c030303a07184040301e0071800104440000c00c000300c1907000380032001d440715200c0c620309451961010b540300c00811070034040c090003003210032910341e040d0a403855818402443d4060071f81e42c881107150b450419840810b907a440e082c000f103259481500d41501c03d118030642d82407543c80d60b0f0200160303100c0042549903 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 589366133 1250 589364883 589364911
    0x90b19110f030903040305010e0102090108010b090325210c17030403030311090d03080a0506030c060904270609230c090a11040f030203010f0b01171003081b010507051c05 75
    0x47c800b44140da60f083c0c0001c2c001a21031140c540010040a0180e2010742284024401852213507000700b88006401c1d2a11075598060310401c4000d8001d002507440344e490000e402d01d82c80034070411003400e090704a00c07440102071025256070903800b01e24850303113100026034070602c010310000f0b019501002c8170b4090b15034401c0c2030103400e03400103184800c480d604600160fa09400d10213606254080e064104500b2005805c0e10a4000c02040740c2d070048a0303140b8400c03900e815960482210310040c020a0655000f81210060064100b45000c2c054030001120120b80d24a045049030074254a0640080d00301030103002c614528204001011070050001541199075201d103802c4180400000c1c4000c1c616062214541071039401054211004080418085810301000320034581c0e01c10050081040c101081846940b128052410142c1150304028544180003172800b05003803001c0358040c82e0b03e041c10021b100341d0740c858400300c450380606805541e660075528544281d1540d0303600681d510140001ca290 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 589367383 1250 589366133 589366139
    0x724060f06050706062303010e0c010c0206030a021204050a05210412061506090807080318090c0706090b04060e150106030b01020a1a010f120203070e040510090b19110f03090304 78
    0x59001814001c9629880e41701940c03001980c1000c0c060b2600002e044409000c001d000d0078008cc1c04d56400080007407040c01c000001400701c035040d9043c0c4504445011038900795103018600301d0307581d6940110031759032849098040610421140e03079000c02e200f510080705040c05c0c6880410590104060310840d80f42d62500c104002030060200384034000c203441d41e110740ba00c1d841c1c5500b150420b031481d003100c4d10700e40080010359583c15000d030001d118800d00f5222861199250300b900303003243c012003400410396800c01a071a01841642d0064a02990040c0f1040042da11245400c0d55940b502495020140750b901004000c810301a82c4954200201030042e00e6411806a80342112196030070342e40c0554644210050200c008a2003400c0c4c00ba08051075040d81c1c1c0050350300020b075079014510400301c0b211000000501040b17000d2081c03a07141aa00c88061054140d03519000c0c0340820b00300e03030070103e01076200703498060303a52240102c100303082c0c80342400c1d4038140202c9100c0c020f90384010001c0d403580c40100800 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 589368633 1250 589367383 589367399
    0x1050d0602250302060601230f1b1b040b030a020d0605060315090a060e0d140a03060b070f02030c0d0b13140706031b111903030b060724060f0605070606 67
    0x25000103210354080d2840f0b24000d1b00141414401c080d0b114102d20701780c0c984480c2d0140303180844001d0044541019180d0113080d942d4810040042d80594060251001040082080d114808418007084505104001054080c55642d000c1900b0103903225034001c0000011417081d0780001e800c1b0074080c003507400da80d902d001c021151442c10390f1498000c0d8055516002803150b5403040b00c0d2a501d801019001126081c0d40c000c082080075041908410000100c40800600a40c00354008003030040034242c42d81042c0c00c202a001003501401d034002e004481c141d0b4410300d0101c180146003944500311224680310b80c00500c0500c4000c0108032003440e10700c031241106602c108103190050105950114912502000a02110051810b00c8081c0603034000ca42c05891004601180d4064003400010122941c608086010305a0140e4040e0459030014000c404e00090402c9042e604100740700e10408e010021845004665007481500554000641c0030700039107100784000c10039240210300101d0130546070214 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 589369883 1250 589368633 589368697
    0xc0c01021803010b011403040308070909092003011e020c01060b1b010c1407081602040c121109100f030b060d090203060718090c0201150b070c0e01050d0602 69
    0x409540c107881103030302121490240111800c108003840c00841040c0d002e206040a800040d100409101c002000118101d03c215040802081440d5092065140758180052241002804a0504070820030401140d00301402a900c02c800f04c1007010204400c0300d01401c0083d04003c0f000100ca54941e038000526400500140100e0480c12001e20f109025592403030382114050030307010040c0020101000c1a1400450540385e8441d01b01d1107041d610401802e10f004090002c850095100c0d00c0c0c1801012300507481301203e07945000000b002c10007407510941ca4602400b0f83d0340900e40c40f017210542c0690031882910782c01c3c00c1320b003d0b0a000c5070142880c03001819540180c0040c4a4180d030fa070910340c0641c90100300441e004080f030300300600c00070294070072112245181c0c09010041926441800e00403407003540001c0d40089005458200543c0700d0b00041010b42c00040c0a5503984000e1030040b410010103904141254001060b10201c601c4d40c0e03a54a02a400900419044140b0501580d02c80418001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 589371133 1250 589369883 589369897
    0x10b0a2307150c122021090a110d051e031305030604021e06070f05030703030f0b0102060f09120f04050102120a080601030b27010e071b080c030f1c23040303050c0c0102 74
    0x40400c0300042085141c0d212030b04000c240c5a9240c0c022350400011844284584c906158241c03404104020389040261409a06102ca40901c1d41c8040504c1d1121030040064907400c0d8002826a1084d65107504240e5108410b890180d0301c40351400c07541200050100000e05480c00217002c2d07a042080303c2e10b4841445280403401c0d20960800244002090380c1071043c01c205e1b4451480410070046200c000075a1600700038000e00020307441c2400f2807040076003004003040c42c0d0403d04d02c003680ca5000c2d005070000d84d0880e1207014050700c41e04500c0384004140d04107a50380868507a1781c0e0f035881d03a10640110060041d00c1d0090350402421900003000341d04a13525840f00d51f003c8d20080150754505160910000e50042c04001001518401c0c051101c044005c0d032220190001880c540f194280c030a201c2c1940b01d100d2010813824800103003002d4498130700a140708a0341d4100c030204082102c1034404032580400103020607890011a0020700000d0280e0700494004106014840c1048c0e11102d04600f240e100740 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 589372383 1250 589371133 589371157
    0x1b060302040305061321120903090f050303030408032e03060b090601030e0c01080405030904020c070f0911030c160803150a1d010b0a2307150c1220 65
    0x1c0900c1440010000c0c030b50401820a440040e4101c83c4d00c8410703602a1703601b04054500ea20034103402c0c1646c1b0490300348521199021040294030454580944482068420341c0142d940d011030001d05840c01100740c07031107240c1010401e440c654400f4074024404580400d448850410500241c01c41c0310041d4032070000c0d40c030442000030448492810003100c0000204020304042c24415240001100419100719070344081c00c041030941c9446c41c00c14258040d0324200c0360010b00c0403c2c5081480800900b10f070880e90800c5001c000e6940f62a161010b540c0c8501c65064000802c10106a82070007440040080c05014050075030320b40059030320170700150b006840c0b600c00c110744001030709000d04d45841250010041080c4010155103512000c003070103181480b40120600e0b000c2500107096001f0b940c00e07641c00007141c0f40701241440c01240780714550001c80382500c2880c2254000080443c8601c14050880400c0c0c4502800e41960000c010260400c000034200b1010100c0a030903008203c00040d2105440c07030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 589373633 1250 589372383 589372387
    0x30d050c150106110f0c010207060f0201021b0a02120a08090f011709010c0207080f060114010903080d05010e06010e0315070302040810020703020c0303040b0418021b010e0f0f191b060302 82
    0x18140924002180741800c0294102c08071000d421fa03000200e1508880761410045041d0810100c1a4020b025680e01c1d02c020507045ca030f03044025440450481003140c803c40b00b02246102100d41190b69a4a48000500e1900c0401800000b8a0318004400a642052500404000c2c00c034405401131002074880800980d19007009114083c0c040c00b03001c0107071011200418207900d444104540c0c4030018402d0030600c1c0d003141036070b9620b40d106a0765000a1a08914016521070022441070002c4c0b400344606085541c1c1503010461a611860500c008180014010540d210f0104103950b5452405811072003416820000000d400f041480b2652040140f00001030311410107081c007a040900e0001212321a410800040c030074441d042d4141e030155500c011003549603410391301030540280f080e59460607d0845100402c11045c105412541401c0070820a03142c40a4038480703840d9a031001c090900e00709402c106018450041103180d00e4401600456840e0b60b01c0302e50f100380c18a030200641040b000a600 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 589374883 1250 589373633 589373657
    0x12030705060f1b030103060b0105130e071404080309130f18051603050613020112020426030c0705060c030706111306080f160306030209010906090b03030702030d050c150106 76
    0x500c101c150f61040f04503451240040c0e88282d0a9102c1c4014040140304580e40ca985125903485801070b1110000c1c0301441c80b8855480d140c040408441c200c032218002400c1c0000701c0b049030702030015a0f04580001000b9428105800200911000c84000c0a00b200c0e5482c241c00c004082c1a01034003901c4240c904110144250b20304040c1e0428a000304604803028405d4010800690009015039006550810262a012480c4012940408104924580c160002c00c02040318010655580c61303042603d10311035940c0a401c000940ca0b4080d200c082201900020020861403d080005019612021003600e1a0803c01d070b94000841c5c03000709091034258000710702d1024400300014540064422402c02e0005850305240301410002d008248a1030f01d00c0c034028103c03545001c0d03041072014517030040450010350703105c0304001c00a20346841010203e90520720303100000e041c0441124903868000c1c0c060800d80070018004c0d035045d400b6482c481000d12520703242070010b811800c0094041c05081e5142100381c05 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 589376133 1250 589374883 589374901
    0x4090506030a020109060c0311060103141b130902060f1303141c0f0c1502180607050d0503040213020c16470301090905160e060d021203070506 63
    0x21005000c10300a900102c4902c015070f0b00300004400b00c40d860b10300310703015150b24541202c051008102c0403810f03105000000c0100891100c0e21150303c4a240c1c01c95070f01903040c6000082421080302d006030064900516804511002d41042c90181d0020b0110b902d0700c0c09990001d00507902c80d00c840c80852011600c2881004040e4401d03188501002005001804119071150b2070303100519412405c5c89021040184018054a45079106a0308029501e112450000b12440654095003182c940d40c804041d9110403441c202050b01c0c500d1b508040140010f40b1000c0702900c90743c0c00500f0990b0320114a40e081241004240028082c0c90302800c090101009058803106484000d50001a40341a83c80c4070107019401c90f480d0244009040400c5005036461400305910301c0251250203025244004000b0495050703a41148031007511600c2201c80260498258103540da00c030b8001c00e0403240b8401e001c10742c82e01e0719941d00c40c903590004010102c810702020009207075920050088401c3d400160070411202 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 589377383 1250 589376133 589376141
    0x203040b061f0e1503090a030f020304210302030f0f121008150c0c0a03180e0f150a0b0d05090601060807050a08041a010f0e0108030a091215050c0409 66
    0x703400b40c075001c403224011500810440d40c001844010040241958036a03603481c40c000440c15420010515943d04200032015143c0700c1c01142900403900564503000d04602c004111002c4810030000143c1d00038003035500f0261092004030503811440706020300140a0a580c00400e80300344a812681c1c0e5410100400e403151640013028140c0c1d101204008008018004c076919070003040c45040c1041c5a51110803030740e4a4000c082c59440369104901010003010780024a0200740407258032400b000c541e40b091005003a08080314840d000704c4020006c01c14014016284d801d000900501018030301380c1b16903020900350494000000302640307031001d101001005202003030140c00b452409003291f03e084500601b89200d1140d0354401c0100c2d440c00203043c880d4021100d031064904080341c008550b540c40d10503044001034082ea002400c16240001000c001c00001c68075045003545414200d545402105030001c2e10004080e106061b00c8041840c40c4519445000c0c0714001c840034040d251400c0ca45084201c03 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 589378633 1250 589377383 589377391
    0xd0c1d0315061020010204080c0a1d07051e0405120105070509130609020f0a0807030606090306090812190b0a0b031f0e070801030201140909270a060203040b 69
    0x94004200324079001d1500400c0d241d000000391106030916201c1c0004039210440b100c0d4120041c003000b8008420007006400620440700e00c80110340d82c07040c0d10310422121015070322503941d06520420409281c107821a60655004419091080c00c2c9000f654408600d401d43c03000c201c15000c80010b040c0060300e42054121701449512000b0080b0303103030440d4058202d10561140d10721175144041d50007940000c030303040b41006c0d007500a0155103916103601122190380100710402c004c9481c0e600040c1e1258400d200d588210381c26561003044441c55616900700400706800f00b43d4440004001502000d154000e6040c040e602c1900d141c400386003420800001c403000078070414458038a8003020401001d4400a894108110342c82088420003d0b004403610210154030007024652440c0400031210707081a000ca040324001e880f041c5014211100d200901d03c56907014030340c040c10314404140c281c2424103400b800b846195801095220a40046510b00359858a040300d0182c1c001040008100d4808991500 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 589379883 1250 589378633 589378639
    0x1212030a0c111c030e0c19030303051806132f0909160315090f14070b0c0d27170d020303010312030203060a0315051b130306110d0c1d 59
    0x46a030459441000b803425800c1c1007050b81702c010b40500c0d02810700076150110300c02460550390104401650205604071320017540864030b01400034204041c1355142d00c07000112207000d81903a5030342a00d41404624011001d8030350480b050242080d13601e0031840403442aa0640c1180340c202070314010001d25440043c400b4200d80c000488840e1803100c0c207034500003580c0c2d100b000200000440040c11004180e00c0d4405020100c1d14144003050102641101d46105d804a0940310580d03140d16030f94101d40704600d0b051441d5803003c01000c08007481022a0700d42a100204050091900c10520a002d4035046d0000d20284180c5450034aa2020420401554003030b640042c505640c95510740745d100c12143c0650105042d00000011219540c10f0603080c00385a215055118000840c5c120800803c000c4400a0b0081071017400036810100c403000307070f920031701c000c03920084100e00307542c2c940c0c0280801d840c100601c07400038060f52000400500405034102400d03960706481e180703c0340140843c41720700601c10380 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 589381133 1250 589379883 589379893
    0x160c09051e150f01050c030c070e0a0c0309080301050f03010e01050711010b150910020f0316030210060506030a0f06050d080c1e060103060e0c0a060e13020c06061212030a0c11 77
    0x1046072101e00302c000d00c3c150242001da0319155640811401d40c8030703100c041e4040d401800c201041d500c2450103014040c3c05032620400c8004141602a0200e49040b000600714807014030040090749031400c0c0100c05d8020290010860f030294a10f0b1300e007502c03026614040495114030310b404416100b4495484200011a0861840b070307030310041e441c0e0501ca0b0075070850040700c0b81d40041030001d000b040255401c540400450f070350783ca00500c0010303d8a4014100301c00600441d01071000040781800394009550009001c0c520710346503803c4800c020300418113074400b401c0d164100040c055031042d141d0060203008813079a981e80e401c120082410f215017000d52154100d202c400310b58250303800040e083c1c19a43c4c80800040d018120802c1c0d0391610460100c6a98041d11080c800708469611050314010801c00303440810140ca00c40e0741e1607042c0c1c060480d5070303100d0794403000000d02185030034881086094090b0301543c401c1602100d032107103a98011035001c094991074051480380150302084641410b003003100540 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 589382383 1250 589381133 589381171
    0x411070b0604230403020601030308011401120c031808090f010504060219030c0f151d0307120c080d02070b0c0c061302061908160309020105160c09051e 67
    0x5420326801816880c0241d0340e500e103507001c00e40301005503107107015180d50b01041454a40785c02503456500f40012000260940000641c07c1c1058090044009058540300800081c04601c04020704001d05a00101500c40320145a17003800540001c800d00c1c06451016603034011b52080c17101c1071000411150400034100010448154041440e0b04008104140c2880b06001400c2c1213031004901180071705000d001295210401c09141403c0c82e0580301d0380024810003180001170010803080f81146003494200704201c0000410881841c3d5003480c650620400381580b548035800f07142c2000c1002240954001000381c11b02c04c01e1842c0950240000c0c07a09450004030303040190311281c0c0985900c445040a090200c110340c2d5032025181c1d4051003000080e081550414002e00d0f920042d030f00d80055030074540314049198030070b0003040c0f800d9030182c407040d180c26680c00840100b812001c0003514050f1a150002c240001c860007000d001d02c21405400c030200101c0e10940e0b80b5000081c140810388400c8103040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 589383633 1250 589382383 589382393
    0x41e09140c07060b060d020d050411010807091a0c06310c0510020c03030a020705180105090c0307090515181807031e0504030c150606020c040203131a0105041107 71
    0x40307014550080000c04c4e07101d44200410f071203009034a6082c0e8001d0010680d502441c0c5140d0019200710f004141e612800d08030f280055800b0042030b100c0000051119030300b8800c0181c6140d031581d56050602e005031500c0040c144250030400180d50300ca11000c0300b06412101c610131071741955494080c0300c82d541025446903540425100d402c0c403da60280c1e00d04100080340f11b00034400c1074840b0102800341e079901d41c2941c02c029200c03071980c010303184a074030b0380d030107500e040e48001c0740c0c0c24145e540181440000c2d403506550f1300444d80004041000300f01814a000c00c103a211211f00502c0e08000e2200c0c1c540b1041c207913001c0040d116040810b80c1c0030f80c134a004441400741e0440012034200c522402d0000303030542c02a40c1c141c81081c10114a0002c2814441800101948904503444184c01824150102d521031002c000585100d4498500180d202544c99000351a056006682121031200d8400f100b0110380d81e03004040d4210311f464100c44040200410a40c00c0c207018445104402e0f6496501e02112a524 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 589384883 1250 589383633 589383637
    0x30c0617060409080903060f060a081b010809070b0f0a0e040b0d020112060905090307030311031014210c0a06030b1302031807080a02010e01030216031103041e09140c 73
    0x140c2c8110340707420100c400d100810013211003408025042d80e0725490244222044464261905e50141c0c9909100250000c004103459280ca188410010080e0300345800444800c0000b91414a80380039840000660103003d00c014400e800790059415198800010080c0010f090241c42500940c1407010100960f40c44200702d0314410360900b0108107035103111240c4e070014131503a00f020481610705400e00c04000e90001c0580b900a219507000d0008100c4441a100107000c2526113030009107000d64103008440f0114031450303101901404d41100d1a140110b00d0300300c0c00d00342078011001c1c2c10818107507249050084a19001e000103040602500e0803030408103200360f444203050070060341d001c00800c95032000c10707100c9071a01245000300c40151703440d80d080e0350701c4000d4034004038046178068003085019400303802036070290800080ba120905009403001d03100d00c400e0b10641c40c40c80c00204000b03c1c100b1b451550a0044c4181b11034a184031508101484044555880101c0c2c010307540c1600700411400c5041c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 589386133 1250 589384883 589384891
    0x4060507110a0204091b140f03030a0804060507050712030b0f0a0501020d2d0810090605060301060509040b040f150803032e03020907030b040f0c08060409140a0c030c0617 75
    0x144c002002c003a00e041040058031180b41c100c02e0740d0f40e080d0000954401c1e20345091040901201c43c40d4189502c0020140e0764400e45a004020a00d10700005010490660219502c0070145c208145029040c0e034640c0c08070a0206101008295a110801c01504201020300301440d01a54003030611818480040c0d5500c009030360f44400c001031840080718070000c803a10030309100b10006114550749882e4070050180c01003158058203c20310010001080b1565004003c101c80c4d016210b00e14503402e0240880325584150741c2103420a8885100b11403a441d288528040041c0d80070b0b00017402da022414049503c82549d000075120fa02c18400e010b902c008032640464910343d02c03800c40d034007003106d024034120021990780b01952004440007007040e0b03103415030030601103c14111410000c4400703100c0c80b14102c64502c00701000048003100012500d04043c0d00400030103025000310a43e01e641c0e804900c4c5003000c0300327808423190f003c40102001001700811461000d0314107801d222040c1c0500c0c1203071200d0400014 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 589387383 1250 589386133 589386139
    0x260106120c031a0f1f030510050f0a02090a031e02131d010506060d0509070f0303021605060c070b030a18060f0e150402010f0c0501020d06030314070b1305160e04060507110a02 77
    0x1d101540780075032003400174001c40c0d101301511807203070808101c03034000c00003128801c440c40c503004005a4050818405c45541c5e81001300786603041421034882002c41400014086004a03044c404032000d80d551450f5120304400ea9031011500c200f49252001920001801d03802c0c10fa8140001e03c14a603590500760344592448a5000407240c1da0102014548029580080a02003064401000345540441d0b24141c055000300003607100c1d0f9891041c4407040c8903500109019420501c001d2118240b540000c60b00200503140c0454244201c0040315450781ca0240d084070402c2c0d50b04408443c440c0d46024101030078184c0c0c8050114074500b07a5003a24031240040c4024100701100205101d158010801300c86a2604200219254400001180e008000301d00059000c100150400d41c1108582c05c1107660003a404031403504151a0340d41a4040180c030400115414002c01a90b945080c5101034280010811000c05076420304060403e0021500054000d4003080910100340b04070b4140080d010302d0190b419 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 589388489 1106 589387383 589387411
    0x507261b070302030c060702032d07060207080d030e060a051f1e0905010b0906070f120203041805010e070e01020708060915010807260106120c031a0f 66
    0x87d000258140e100039407401c80c10080700703c44640440c203141c644110304403c020303036410044150000c02c01a0b00a410030000060300b0071140521409500301040640c8040582c584c03030718401001041c83c0364030f07800400c9014000c0030251000b6090b41d000100c5a40e10780401983c0f81c4030206848103d0341803a0340100710a00c00c0d2150504940c24022524540107617a02885030b281c100c0f00e01030710f600440f0361151002c9100460902d00728420340d40510307034540c2820003404041c40f030701c10400c00e03a0345460700511510f0892680943c11000c50700f410188280c0201c0102d24101d990b81101a09024039130901c80e12000018100c00c0031900603014910a0f81c9402281e82d48628920401c5000c2d040b150080300c1e080c481ea059030340f41c50850000802c032981c90341d0b41403002903550b078412100e000c42e0741c0e4200280040c0b4885040c0000350f03000c010305d00341005a58540e1045006c0c00456a1000c5 = true := by decide +kernel

theorem cover : BRFrame.Cov 589208633 589388489 := by
  have h0 := BRFrame.cov_init 589208633
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589208633 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 589208633 ≤ n) (h2 : n < 589388489) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
