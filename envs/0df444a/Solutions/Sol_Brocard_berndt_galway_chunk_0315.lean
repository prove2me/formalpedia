-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0315
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:09:42.765851+00:00
-- url     : https://prove2.me/submissions/b269eb58-2c79-4efa-889f-cc78cbfa49bf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 56474823 ≤ n < 56654679 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 56476073 1250 56474823 56474827
    0x15221a0324030f0708010f0b0604090b04021201091406060f041701090b0907030314071a09010605090705040503060114010c140321040b06030d0806060702041107030908070e0408 78
    0x61181000a20044140c40441000c40c0c01c0810356101000a400c2503040c54005202e2a0318101c2406e081d6115004a45e03042420000e20303d02580350841580c050350b22401010a40d2820b400204000340a01d015074076100d07204400006030316156900c10321045180c481c1940607581d0b003c013840140d120f0f441d00280c441c4010407040000700d0306141a0000311a4010011590b00d0304d03078031642a046000e42d40e14013107402005081040541010a0081c5044804101410160710b034842c03d55001d440482ca00d500300c034640000c0e0f1030210a52014001e400028500b600c1820504001405500b042c0501c50080c82070b400003082c0d02c510f0300300c94a28907105940d03591060981d942d8032030703191000e066808014841484246050812549401341d011003500405601e8645401d01090140d005003219020303402500c55400e500ea0712105440d80080c050707a001d9603440310fa2001c500204007480c01003c0000d00403408104169000c401c0d5011244104200e50b941c3d511800c21040070f00060310300820303446c01 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 56477323 1250 56476073 56476081
    0x6180a090203070e04081209070303050405010f030f1a03010e210f0408010501060503220512031905130201020705150901030c050d050a090303050901090803010b0915221a03 76
    0x10903040010364900c080d081e10074040d615203035908200e40c1520215039401c0c01140645405039050041640300c01c40c1c5c001803560324031310344001c0c0c00740c4200d000755410030001c000d408040900a4210164909521104009905001c510741908500100206101c0d500b0503040c0c2144800c000340510b80c082c4803254200c403108005410024075804aa0380402c109800d00000614100c2882618000d0140d034680648e02c2c58200e01e412094280519000300c0312500c1061180400c030001a1081c1ba04c0100c41030f161341e84c80b01c40c47d504908040f451010100da00340700800c0081039135015a0003402d0700c00c2e000c4a11542d00c600800006c03800b00d400468440c1d60a0200c0c5103158400d4000c25105081e81c10720b22702c0d068500100030b0549208a0309200640d40729003400c8201a81403094950140c43e00000704030440c43c03556140410311061191041e00240400e88d000301d41d466110090515400e0100240d554a40880d0710400c0180ca0045500f6110709900015809160b00c02040304045545d03006403656031 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 56478573 1250 56477323 56477341
    0x6030c06042103020f0a0b0405060c0a05270d0c090b030601120b040213090b0712060501050a0c02040f05070903050105090c010e040e0a0503041e09201813020702090618 74
    0x103000d900360210b10441e6117080740d401e403c0c4a201c400d18042d039034140303161506050072450f101d4054840d4800d0003040010300c02040d804010307580000d40f110982c0c041036107001210b407809a828012150f00001c0c00c0300c06401c010070f140c5030604907501e1610922a81945000b05a01d403402440ba02980c9484400d5917000194409201a44030b80b0003031812542c612034201000860344a804100e070500010810701840f1a0041c1008444091800c014040c16042000007006800382c54401001d00110400403800c41d03456401121400075030b11401c000701c5c9000070307000302007580710b01c02912039529090104528980109070136400391030685826000714200c006010007000306125103440ca0081041450009005000400c010101d11061101c095403c0b41e518410020960000050034030307012407444a6040801100300060090304080e03101d0240c1c02c0380b00420f04290b0003260703029007000302c80e401c505520380c0079044550003030b690b00c2c203941d0310001808000e5846d40d00004602022000140d0f44803 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 56479823 1250 56478573 56478629
    0x501030b0d0816030c15020414030601141201140901020306010f03090b01050904080730030b100c030203040b03010906150201091703070c15020712050a0504030b1008030a020606030c0604 82
    0x81c80703460010b04c030350301c030340c880c1c51481003480c00080c4507d40014041000f034014500c42e4403111012806070403030354034005c1461046800105224001c4030304070001c6d0107041080d404005038007841030b011401407034200c0d10756000f075104460b02404a1070b004aa00040ea10a1040300c00850f80070200180c1c5902380001c2203200700000344211f99644041044000141400c180c01080d2041c50500325420039203c0c1944494002d03403548a000c0510f13041a001c110750745c444041c01030811034142002004000d08041f401c0d807040b0b4204882c84900007000240041445d8010000c40721030300581a403a84500c201242070300c824650203820042060785000c0d4031000c65000b95005802d5060200d84055141c0c3c0b0604000701c00d04441107400d0307020911106001c00044010801d80342e500d801c5150054050028120b030040d03001c00b0f4500c0340000001000300d100042c4200c054403400c8110b036140d5a117100001d60f21401200c0e1140640101e00c0540b5643c10704109403401d84102d071490300268a2804901500c0c1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 56481073 1250 56479823 56479867
    0x1203020d0c15020703020a020f060901080109090c0f082b05090111010e01060e04060605030c13050703140c071502091c08041d0702060705033601020c03040501030b0d08 74
    0xc0d82846841c0700d0b0351492072000b8a0500d101e600a80000215801008195075071b48112500829040045c4402c40c1e0340400464155990390074001064010b604001003940780303c2d0003a20400c480910046614400000c190b4110100d0030104080c403a1160360b242400c04010595901082d02804004000e6024400c0f4a022000b2000002480c1c40540010744c250380c5030360b20900d0045030050a000c144100e500036680505410b60050522030045404503518803100450700d0841c907a150301142d496031207500039210b0020011140c1c070345401c6c0890000700c590300c521070403510078402c5120a104105640259059858024000c00500079000b000140354040642c041701c0c850300811011840c90b0b115981e01205807002c0b01030580030b1601e0000030b0701c0c001000c0c1c10301c070502c4418070070014003c41d2000c1d18540b04c030854980140c02c1142d900280050b41c00700090f8240365001061207a007954000000d0011108240da041c00014805c5042c40043d401442003c6c0400004100e4281810031045e085c01d00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 56482323 1250 56481073 56481083
    0x601022d0f010501061d06030912030901090f060c08160503130309080a03050c0d02120304020409080d09080c12040e0103031107090603030503010302010807030e06010311030f0f0609071203020d0c 86
    0x71403528180603900712282608414040703200310016441080d0660b40103240300405131040d51039414a101081e94503400070305040f0010400000107080c503082900181c2619900c01c0d6402c04511883c604040078210244184000440c03036000a0844c016000b24803605003a6929494655201c1032400b1028400c2d1040036014480240400101b6132002c01580c07407801d0080c0c0c2c03625190708440f000f0714140f03d035813243c010865000c0074007130b49241d124908681d08240e04070b1700011103d01318600341c010350061500e41c0c0600707854200150144181c90000b0000d008000d02a81d035050380010035010a80603c3c02451103880c46a00180300003405440380200b2150118212500790b07540724480c2c41030761280e400072000100e004c8010000c42d40c100301c0161300b209a904083c000f84644801c4181e07a00014800500f8101c0c4030152010162414000e10400b1074001c4107031060a2221140c183e42c580040d01d4a00561065100c0082c0381c0011040d8220016456030213443c03285030901d81181c071714115038400d40f9 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 56483573 1250 56482323 56482333
    0x80a090512060f010f080601120c08010c030905100e15060a031b06020118110d020a0504020c0c0a0501030c02071e15080702010c051c020f09030601030f0b0601022d 72
    0x5407596042504400300e05000c1c0201040d24080c1410303502804103034080d1320004840c54003405040c201203459411340d08003800045c040645030420804541e0039601c0398120b9440c213181011200e9240c0c001c941454014030803140e01c207040400443c11507404544c1c1d038085800448510340401c03100704201d134004c0c0300100700000302605c079141d04042d500e03020946030602c0690501003002076028015150650701d00040d64a41d90084c0c1c40e04200e603040c4107170a900c0b9054000320300c42150791f007454001c0030700f8015004540b60340c2455400f40e5581d01c0039180f507110345034800d000a03c0d50300c640105500460180d01074001d0a00c4c2c480b180e0309110018206884601d000c030300104101c12101500800d07244560748001182c01c101c03c02034212680701c1050010403104102c5c03042400da0740c0d803104a5140e203400006a40c2c10204488421030f0080b081d00f01c2d8103008600c000003d007c03010f900c804a10f4010410580c0a840300b600590303441c1088030a01030009900c02500d203203800007800a030074200304242991 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 56484823 1250 56483573 56483579
    0x6060c03030106020d0815010804020105030907080709060e060402070809090c0904050403030209042004140301060306090605040309060e0a05090c070b07030c1803050c040c02030d0603080304060b031504080a09 92
    0x5040d0340098100d580180c0c03007180c072200400e0340130072096000718019480c1c804d043d9000700020958940140043d05004001002c0740059800700712140090100d102a44c1c26503885413045c84c0034124900c43c0101c00c078200f1002c582c00e460a0302c02c4641d082e074080f503610300d480441024400800401070146400304000e120b0101e458607140a124843d074429076005a0f100d071048104021035045505d40c408841c2550400940080e4800440d0207580752810b00e40c2c0e54448000009002d443c1035040205800d040aa0301020094070750030084c06035220341c4480d03c0722501d41c0030032583d0992442e0b110794801d4a0610070441e5061400007260400310b88800c607803811aa40d00c884e80c80440c15140780000a6481040d8903076141d10034018581d814160401340c3d111403541d1541d44e0f072204503910540c4102d82e65411051200d008000b00d0301020000c07081440041c0d0b0303078107100707101c2d400485042d0741d402c3c00d01d940050340341340100e40c0c1d0340301210191101c180f0f5211503d40204640245203112300b4404000004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 56486073 1250 56484823 56484847
    0x30b0d0510060302090f040f110301150308030a050106020f0705100507060e07050307140a05120a020d0b0906100b07030f050d0617011401050904140304090f020711060a020706080606 80
    0x88807081981c0c0c0c0300403610034550b206002128100410407400c501212092000103003541c60603507c055008840d00c00c000070084002801042803507585000c04994080000812100b41d003e0b510405040208001c540c0e40e60605a0302c52542e002a14206d0300720742d000344143d10341000490100c02151400900b04001d40c1e0f5240c0803034121004400003a800002c00300100e00e4108402d01c041c00d4118004000300c6408008105808010b00580e4402c0e602c0103000b154005d4104202025181c000b08505107080480c00c101031401000e4525038058065240021411224a010601214400c0d2500f0b403410a958070211044400580490708000d820415040c01d9071980c01400c0103000e50030300f00454940d02d0340c0c0d1b2500710786205400001e100d4941c001004150754092007113901c2600000400072526010001904500c40e54010f2210180f0704160400080415406030110a1140c88a401b55180a1007080340c01c0c054541d458005a02060050100b07610410071143c10120180c045402c0051030340d02 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 56487323 1250 56486073 56486083
    0x810050a0b0c0c030c0d02041a0607151407080117070b0c010204091d07030b0a02090319030f080c0a0c17070501020a1404050105040303080606120103030e010f0302030603030703030b0d05 82
    0x401840d01041d02c101d41c071010b01c0b00268603402107000f41801c030305030404541c81c2000301c2ca01a100e150380d031001201c0c01910521003519040024843c0c3d039248c03003d1900284002d114070700410351528001031959411710b0711129900804d600e40394001c0580c40c1c40080340300107204050785c03a070131b004108001601c0c0d901c29014003002ca204800140c0c556041c00715810460303041302d0b101550b800940c0980e0489620124a080c1a250041c4c0505110303911500fa44019116802005806d44075245203980c0d0514000f07800b00c01030b031180d665040782d07007a5040300b1600150150f52400007910100000a1154051507910700224480d4400035658844151404c0c0d031a04810400e580e96500052403034030144e40403040003008c000294a11f41018200750009001d0b001e0f60000400740040c42d004030b50300f0313500c3c0000d50740a43c3d440c00704a400e43da140c2c50000e0411100707400c0140031a400500a2050900078001c1d40e10488000e40150f080030300c941c070200c0250100a005039003043c03e041020740400c20a00c8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 56488573 1250 56487323 56487329
    0x3010b0a08061504020702130c1b08030708060f210708030304060203090c060406021506040204050301050403020f0d02150f0402150f1317031c180302100b09160810050a 74
    0xc041c081601d40f0020f84a840c0c64049841031140303104021400041c3e41313521070074041c9200e103600026a400c040c4020740d081408841490301d2198900408002c102644000b1032041000e40d07900d10761622a00c0a2092100140b452142d01c10400444405041421007404504600030421105040d41e50610b482c1103620555094404640010401c014a40200201002c81c902922402c0c070b06458452300075141c0401010505120164001060060341c0300d405803405810014000c000b03038102850040d542d01182e2500351490b0095560311030070f075400480c2c00400c68000c0000455141e40e900d07540c81c45c0c9c0311300800c00c03680011400300100e0100702c0f00300034100c51502c400c1e21983d6000041d0b0307507000e04d48a9034052001504511500c12032004003005490b456001c00164102c40103107000084085e08108511000c204e040d002c402c01403543c000740403038444c142e01100b00305103202c000034400900021500380717140c803034420150300c0d4191242c46e006504c0406014480c4101d80c071030b0001042d0310312540c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 56489823 1250 56488573 56488589
    0xc0f08040b0c06091c140309070b0f0d0501090605130917040f030302070e040c06030203090a0611091e0d0201050d2a030f0c08060d03050904090c030b1605030402040203040203010b0a 80
    0x6420408500420440c5903a000c1c00417084640d10451881c00038015448241070b280840408000702e05082d10400c4240c1c05001e00c5a030f015101c000340b892910310384d040700880d040c0312410100001018401e0f8401c40050301c401420140b002e118600004000d0701110000302d596007000c14089074403c608502600c003030404000d4180c2014030354103000b886c040450304004078468500c02030200090040c0382c030808072010350401680380d603100b940d1a8180382c40900d000e403142d4208103200c401038090700700800300202c0845200c444054128205080c83d0710200c001604202415201e002640c020740141c030510025100114002d0b141c131040304481910700e61660100d02038641040112500360141d00c40c440a0140100411244a074005004030400b511443c05103000400c00d80a0502c200115607034041e0151040c0850301a91404c160340c2003180c401500c0c000c0b809030124008800d81070b07210741d0b0754509640d0181503844503020032000f5400900200d901d0740d039541d000c40c40c64660702490002402c100b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 56491073 1250 56489823 56489833
    0x901080c04020a180e10090c020c0d110a0b090307060306030809091012050d080604090b070e0a030501020f0a0e03060108030301030215120403020f0d110a0602072d020f100c0f08040b0c 81
    0x58000404070407007540151f82d40c40c0c144107003010741c1c0b43e000502c10103028003200c0c900003042040c10203a2030580c8803845c60350441010359010440da42c00f800240881c40c01542120a51680c4690444c200c52107400014000b00f0100401d4145240c0318032001c0d0480e41d45140702c2c03996a940e04903000c103001c403000c01300ca07a50000c4041c07040c0703180c0003006240c2c0301c1c005807410f124600b007036581d81d48608401415001440b5903501600c0e201c0d1648014807000c0e55100c4000c660319003000c800740d500c079004401503074001491003030b4101e01c60401048040c12244020011411642181e0800c462003000d01404103520394144180c0c0700c10040d40070030030701450294018119842c81c5480780707810151740401940603c580b819188003400d00c0003400000c01900581c0c01a1139100b04e1a00240c4c003010348015000d00781c2450301a400c11500401c5007820284216161541c11940b40180021001c0720403a41011502003540342010032220544550101d10991603c1d2506440b1807031703180180c00c0340f003060b041d99000c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 56492323 1250 56491073 56491081
    0x140102030421110105040302060304030c060f060e04020f03030a021e030d020a210510050409080c062d0c0901050d060e100e09060c03041e08040b07050c0901080c04020a180e 76
    0x30060075940384441c01c0c179003a49840d0664010611790700c0081d10080c1084880c1c6c14040612207142d0080c440801078440a110315503960b448003074501d2007640c00780c1c414141d424807038120313142c0041107440d030803066000f5251800c1540705030301070b80341d5020301e8401500040081c0750b8800781c142300505800da40c030707101c402c1c40e1a003103104168501481421042c819292005100412407030030042c7c01111800c490208002d225071619103014000c200c1c050861780309207400d11411400040054050514401009085c4810400d40c03940340e28040c0c58400c2c580d00704004221007548600d00030000100f0141000c55860340e1014030006205044a04591181511b0000e1040c03112121100c2e40112170480140b0180c100070748000c1e11480702420003000220410343d40c01c1070414520079055407d41121005440c1e55031400c400c0389a50000c10201c0b031a008800c075036001c628001c20400e0580e070700000203000201801d400c2c03000a40c030402a600500ca24000c5181580c004402c5440242103903804452440c10 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 56493573 1250 56492323 56492333
    0x9020f0a02010c110601091d0312040213140103080a0c1709030c0d0503090d17030901050f09061003030302030a0f050108030405040e03030403080a0f110c0d11070b04140102030421 79
    0x1031030f40844080081001d1101d1180e040010b40a05589482d00c0000d49035119200c1a400c000e840341c05110039020106020203560b405a14a0744698000d07181803a0401c1840c020104898408031742c0780001c4001030050010881040207000003a5060400c1c18081003141ca07280d1105d60307400400f500910f1b00040b9050a03003400d02425103406020307214501c1c2c860150b07540c1c540364025090614041e003044d00418050109081280700104030100314140e407802d2032401c3c54003901c41206c24482600c82d81c0c0200c2c011000014042d841618060140c580e01070070351b03408401a52020300002030325900d4104041440305584a046e00074484e0000441c2c0e01d501d003805210581e00c030110400703602d41081c000c00010070380020005038083d902c034200140c0030400810203002400d1000300d000b40507001081d5840506c00001e5076413490400340e1690040c150942111690703a40050080300b440c48028881040801e0b520003003c5042c01e0140141c9040c9910360568002e00182d05124221068540c99031340c0a201c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 56494823 1250 56493573 56493581
    0x301090b0624090621040507091802010e19050307060909110c0d03150b0301030f02150a0507021c02060a08010f05040b01300203090705030709020705061b0409020f0a0201 75
    0x9a0481080b03410001e5151030b1450b0144482c40c038062030b40002d407000100004440e40c0c1a9071955210312240741018100b40395511201e015041e01c940c5481e456070700c6011300342540c4000550594420310030354000814801a2416a10310110b04c40f41d008010a10f99018802c60340036006c02d540d5000054905081c0f0002d80c0d000c424885040c0800f040417440d0142c002c101101c0300707112410040782c2c0e52000c01010251142c640e1120315100c1f00071002200304000f041d1142441b60084506011002c0e0140751000c203840351001040102d8000c105003401070401c406100318080402d00c0c00d48000c0000d8020405a501403403095000501010050010114000708040903150940e020402683c1400000c0c0140507031360310131186200d035000f2440114500325020450810983c1c029512400d05030042d56940340d5a000d5144240140c810100c2c2e801a54800c0d145100d4003c4010032140e03d41044041182e1801d042200840d00c0800010a03500420300040c0714040025042a82c0d03102c0e0404000d08407 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 56496073 1250 56494823 56494849
    0x6050c0c040501060e1207090f020d1505011b02060702060c06100602010b060307050f1303110a0515030c03061315140f030a03050a020712291b0702010e0301090b06 72
    0x107180781900501032103a204080001540c001ea0b01d500007055a0076816107440d04641c0140115420123400c44080002c40d0007905d26011488001e1106260005280480120303600400303000513040701e0303007241c1d02d8400e11b0703110101d60014096a00e061a1900403039029130007400c9015080d0300000900520103445545d040040c41039200130040c1802c000300085da00d01c0060803503010810003190039504c03060300c20708544c44520200400201d0540d80d291003014a9001c3d8115481030040480c00038040c24206d0000310320403c602c4010349190b4131150b100c111500f01500782c0303030050700c5000c049429019520420110726000d4401001d411314150044548200c1006002d010b4588441000125100000d843c103516506050454990109003412854451036034051500200c03030103c081c003842200445803408070001d601161036000950344001845000361510000c01048190100e50000c0c2e01015081e01c610500d841640c40404d980003a0940d040401e003a0389281158091003070b80d1805450000038 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 56497323 1250 56496073 56496079
    0x90c09091006112803110105090706020f16090c020102090306040f0506071d090402040b0a09020309010507030908040306020304021309060b010915090509040203161d09030f180a0302030706050c0c 86
    0x1408480080c0c85500201d000700c1300300a240800582c08060250480c1507035441c0b0803000700100e2602c41e4000b40c7d81d03546c0f8429035000d40120144040c1c0c01401280c13a442e0800c0881c4a10f054914044510300100146001e05085540c00d00010000b9a005c0c44014011400755207841c0c01d8a00318101542441e0001d0f00b01d000b4082e0002441c030b10b000310044103801002041f40d8420b01603030340d0b0001c40e01400031550242d92100d4a200086104a0158080c46c080c404950007000180c1da90907040e005c486072400090421042030100700000394030768000350342c03240c0b0140c004091070b14119129001d0303480c0107408861440d151040030440f564090201402004200d003107808880309524054010b001e40d014050003459201c00241c150344007080803403d04044030100090441d9940003111001101c500c0e020400bc13818004154102c0c0c0000958038003001d144012440d00e00c2c00814104441c68141300c45800c80303170080c400005694140140001405182c5403903980d02c41d03c044060a10340f0190003148 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 56498573 1250 56497323 56497333
    0xf0307091809030c030809070302030d030c03051b070807060b09010603020903010f0c0909020d091406060109060509030d201605100c0c050402070201270f08030c0c090c0909100611 79
    0xf2990004000c45065050304003000700f5215060183e0400c6c20540020707400d80320341a010600d031981903200070380c14480d540c0c081115860b07900b540d07071444186805854420b0424010540070a250350010001c43c3d224150002e40f02080c81c01040740307028242c0c008004a5030100b00d584841c1030a0058480b0f0300b059420420004d0341110010340b00b43d086000c1d01c618a940481c41081c9140c440c1d110340d600c030b90401019240e00302e240c41c0b1550340d40720407500540001d24240740001e0150080e000d4035014480203002d0954002d90030f804030382d89080700000701100c6050300031038481085c092054401e4101d1514449a50504010500004104845500003008041400303a408103003440e01c40810b4803400c03100980d690105000484a01c0080030480220034841d907100e10782c3c080c0d03640b03940c03003203508205050303951554968446440307001d04a20740c03810f5004010409050b00e0810700042e803186030a00b200d401c140d141404569101c20440300341000c401c1d005010320480e900310100d014030406141c0241 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 56499823 1250 56498573 56498591
    0x270c090108060f04060b040e01090b04060605060705060609040c0302190303030507090b04090b040915060603050615030f09100608030c330606070b0705070204050703020408070311060f03070918 85
    0x900f0329400802c0070344202c2d83c600c102c440d990343d0303078010400410100000b0700c0070000c0b50522008040040e603048030158600000040c160410009490b44030340c0020203820b0b00e80d0740c4401d01882d0000240b0458410105060210060340c44011b800794860000e4961000c842c00d6280260440d10064820f0b010f10454407020420781540c081100d040e1120040081080d190110200703001c0d02201c4030040132914014141c034041c2c41c1c2584503508640031503a0600c159100c420911102c070341100381c5640d40aa042000411030024020910341190011088840069243c465001103841030b0300014015040010360202940d03040040b0b40e00100340e41c0c50882941c00988140c40507154030403001d0031000305d817000911a0ba0b25641a03a011a8001083c2041490b00700d10061240d40300e00b404901c03a85c60304012946c124464030070788060790812030040012034250b48810300c0710514504074650008041040b0125040090302550040c2e4494035101003807030420268008601902a05d0b002c0246000d94503 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 56501073 1250 56499823 56499841
    0x30d03110403230f06010f03141e030d0c03091703100302030d0c05060c190f020f03040e0103230c01030e01150306090c060302030412030903030b0307030c050a0b04050907030203270c09010806 84
    0x1c00c2c1101d0380b00c1180e0240d0424945440d003480001d842b540c0c220b41290400c0c050015020000b000b40c17a082c000100440802070000360125000660f01410703408089106c200c030204031800440c0c011440c0ea10b542c039001d580e91700182ca814041c1441d940090017590020003003000401050382c001070801c4010f03080410581c1d0003a0b8440300402aa0200f0000c814400c2442e8001c3c41059840894502580e688545071164490f0f2420288012504895202d5502094201d150540f518250244000c0c2c070351244c160300110040c1044007a041c289542c0c0310080100c400c043d901e20750040d485030001050340165070074040104501d1b0b5001c201494010000c10000500d00210300008208505000442805504045000b0070b4144c81035a0140702e0700e040170061081c41c1502e0344c110340702114164040d90315103040e400307980914850282c0215903000818207482c002c0d00950390085072000703100070019510300014026164107000e0051744e00000c1c3c1007210b40c1801915503000d4030f121002400b850070035070340c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 56502323 1250 56501073 56501099
    0x221160f060e0907030b0d0803042f01020a030509221505090f010302042c07051e01120f020f040608160e090f0402032a10020c030d03110403230f0601 66
    0x704500700341d510b0b031540150303544000080d80703a0b230707003003110b05460346064a86107803100b40c14444840d80c4841c01c454440100649081e458002e207060b40540415551035800b941c5503003100c442030f40d000e807808000428840300100c03a000f000e20401004a0090034501c5011050065034000500841c010410403107620301e05d00c0003504582e41900c0000d81d912400e2141035501403c000f5804000010401d58240b40c800000d044045d200304650404c0d82500961104c1c1841544e0f1034424013040d035075458841d070103945030301c5100d13050401303140507181010303451000c0210b078480d41100000c02c041c00d05004501c0d8402482c042c00c005641000f541e0407505c040041d6141400a0002c800c1d070048c400000c0031074070240086803060540c0d18010071400d40314181084016861303000303a8021411013800516452000030140000240a00030300b0011202c400114083c0c0b5011402040c024410400000010070442107203084030740d20300e0031240100402c04c01900340400b0780101842d940c440381c010322910103e40a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 56503573 1250 56502323 56502331
    0x20011d030304020a0e04030512040303050a05060906101409030f06220b0a020c0a0b270109080f0c03040e0106030603060e070503070b1303050106060804021008070c0221160f060e09 79
    0x82c070500341c4e620b1074100c800d441408040178000e1640e4007030ac070415030181c100500403840d401090040d45e0f510303030601400800441d4142c0d8018180e00f06013051740d000b2030a08001d402c80d5034005241880c3d0703c000c02d02c1c2503003000344284c0c0b551050b070400c401d00000c40850801c803400c010240a1110041e1111542c160b4040e1021081070360005078613202820070054000004e600c40c140b09854500800c00304030850252518400c0606881115208168113105820003140e000ca13000d410a4043c0f442000c1c5034200781c0f1b4507201c601c0100000310300700b00b014174202c4c0201069500400e0035402c500d80340c810750b4060008094180d1168a061015a402181d0381090702c00e2403940301e89802030118600d200d21160351000d04a5440c001c400300d000c0341e10200c0716104038002d4071b2550400c41d44040c12100316804444402c00510b03107542c4600146072501d1400c3e28202000490001840b2960646c0c0c148890460261000b4001ca6010031683c412400e142004108504040c0b0107800c1c80004612103000c010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 56504823 1250 56503573 56503589
    0xb04150201020c0c060a0c020a0b1903090c060810080a05031804020c0601090f02070b0103080703170708010311061c1e020c070504020d09080f0a030f05071e20011d030304020a 77
    0x100762007a009107d440000d074455001040c58403140e655000741c0d5040c1d4400280200e0821144107071008090180c000c1d411856407042c2c11000c5545044001c803440c020203050042c0000b80b41c1000105140100040161240500061941c0b034901e0662180c0070405040c0c40c40c0a00e00601210b07400d004c01144050444250040c04640d08061318281002441850303001070607250301c1c000210038044080094281681300c0e84078508c0e410500c40c1400d0105804a5588001644820040c0002064200a41c21813400500000d00300012a8190514514840d050000160b61992070250300d6109010b2400249d041c00320840c038004014140e5611404240030701c501076500050404410200355110b51140c6403c0034030a6114541c201e200407071684594541390009092038a40800000507101e01c80c0540f0060300e0f24810907400c00c90766240505040c2680051200300404002140642ca81283c03045420300000a0303405d00450007842c0c106542030304000309603c14800c000058031084607403801c2c0c032861 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 56506073 1250 56504823 56504827
    0x150503040605090c03010f02130905040c06050903120403050d1205010f0e1008031903110a08010e06010c0b01120201091703040b0c030405180a0e0f060a0209010212040b04150201020c0c06 82
    0xf40c2d407100d00c0c0850343c04a1035019803801b104c1030641803241d406060740110800780042960b985854160658400f40e5020340f2003103010000704030180c0114014060701c8000b03410303120243d0060300404500e070081e074010741c0c02e500001b01003950158048d40c2d0768a40f1101030b608005550602e50940d60b000020b0081c2c000d4032502c40081858a0800a10f000017002d0300c40881380d5030003010b0703441101d41c4090022000032904143d107088501e01c900c41511000301d1141d0f01d10599130310b4581d411000c820042e01040c107200450aa09022034a80300480340a80500760010000700290f1000400301c41c2241c6c000e000b21050241d0042560740080205d50403200a400c0c2d49844545148045056100e42e61049a00100c0300c01c01c07020300301c4564101403003460072a40410041c403102c50f03841c0c2c6951981e84c802021390420400900304803155805801c106038103204071061150400400c0700240d2060b00010046200440c00b0008000f840c0883c1e100590244000d40c10003030300902d41c40e641d40101d402d9034461640 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 56507323 1250 56506073 56506081
    0x7090e030c010e070503061806040b04080d05072102070b0103030c050f010e100b01080702070b0c0a021309050c01091a030415021c15060905040506010c0b0718150503040605 76
    0x410015581c0444024008000d00b581e000109940e401d400d21900d8028050200003d01e031313100d65910520a11300d060301800c10386d551541c810f100c2050003030040b02e0034a400c0c050801e5040c3c0502c282845601c094403212021190030f0f11a103e0001c910b403041a0040c0104251000a80510306c41030441c0c0d07142c105130131a21f506190040c01c00c1820304601905603e031410a064407000041c40c0700001c501407204100b000194801161240c1c400c44040000d40d00000d403c001d01e200322402000c0b0348000400f9036160020030360008074804003580d0044000358540e08010300780403050100c0d0090500908103200a14070345540c007850020700311040042c200300400000c040c0211911400364405110700d04540e241140a022802d6080420f00c0402d10342c030304400914850703030182075981900c810f03840c0c0b403410600e89801c02001d882c1c001c10380303030420250092210004d88a0b030300460080d2280c1c6c4842c10903040c80305e03541c0450b00c40303035100c2c071203017855124185103140c3c000c404c603a001500614041001d6903 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 56508573 1250 56507323 56507351
    0x3120402191d060105070b040b0609010609081b0a0503010c02060a05060607120f02010f091212050907170106030f030909050702030301061b02030f0303090106140618060703090b1c0b01110709 84
    0x40c280054090b203101d07c01c10040081d503000040c41900110340d0101d459032180b01c02c0b5118900e500440340035a100b280d55500c28842031040c1111000020040458a034030742001c00d094815410742e04d005a84090f052001c08601d50240b1540309030280d800a04000154803110f542c00c038808000800e0121052824031014800c0d0004080c4210000f810300c02e101072403400200154601e0458800075051164140c2c200c002401110b0161580c18004d29105041032000903d0421070188400c4a49d6a9000007002501e0904034020303403402a22451401c03480d09240c601901c0340104003404540080005109290300140d0207450740030f0107030040c0001410340c03020038a0610002c00d0148148004800c002070520150010010f5038401c01f1090a103500e0203040c8542400740507044540c40e4a6801080041c0c20305c030001d400d0b43da00034a4460a0b882e81c6440691007a846800c912600e520160341540418885001c0c2d841036060030310b01002003500c0941ea56464450781c0c003c0780760060701c600d200c01940e2 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 56509823 1250 56508573 56508577
    0x40807121a1e0f01050102060f1b09041d0606030d03020403020a0b0c1f0f0606020105040b01060f021207060230041b0b0c010507030b03060c040608130503120402191d060105 76
    0x403000550b029454100000000e401580034422580181711311400110b00301d44481d071180c014040c1d0300550440180501111900e5046048034a811541da03c045003541c10010041403980380000c4098030141c100364041c14286495014080289801004100010f07142c64101e54102c54012002e580c50b0f0a10304001400c100380d003a52141100540d81020100c004103071f0021100c4400c420040040559800d010b17402c2e24800c6801800000d94803004100310390007083c01d203c0b200c050348107a801118519400d0b2185800003041501c04070b41c0032440e200910708414482e1400f031801881c02d040780e80c001640c542803110040c0000e10004805010060001c40d012004c400751190200030750b1500009411603000b000f085608400207800d01e40700340c0460a0200b1100e0003140c200c0c02c181d15090406205455001018101d00da4105000d001000402d5050010301814031525100003031a06060040022a4089500c00302500c0c549500400c60a000c0700107114000c0021200d0b000b0307a079075441c0103031214 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 56511073 1250 56509823 56509861
    0x3060d0305041e0e0105040e03090609060c06041a0106050306030d0e060d0f09021c03080f070903021005030405010501080d02030d050405030909010b0c1b0a030b090c1005040807121a 80
    0x400b40303100c3c0c402001c14030b840302105031043d2450b004126039a13202040141d0340005501d400e1608200219030090a004006210598014089910b07000d1103614007071a01c48115000c3c2c60044e40c80c901c1340300080a2040c0180104407a00d0841c0c1981000c000280c3c4503400d00c0210814404505881042c40c5c8444081c2d940c0032256130710820400d40d00940c160041c120000080740704401a01115010044802120103c6078041c2c0d02d100320380c0c2e2003001000d0382110141071681070107998880003005907100715168a1550055544640300d00f42841c0040c203651068000011940141481c03030078403940003003034441c490b003803d8010606403118101103007140f040c00103080d00802054000b00c2c0b000f84d00c5004000ea65401012501c0303460701041c400d0000d40c1c6078001d00b503118826003010004200540415908002c00a0545089200074400910840c0c030f551030070004200c002c6820000c1c2c1d1021b0018400900c2100300740d0746614103a03615224505c0703c680411542d1440311002c5418848050041d0080d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 56512323 1250 56511073 56511089
    0x9060c03030932070e0408030907330c05030d151806030b10050f0f01030e0a05070512030f0d1508030a09030627030509190f0f0509090303060d030504 66
    0x980c1c0d461031040301c0d80c040b80c4035070384007004018940c1480c2400013810b20300321850100055104d8446a94035840d6510103001c03c6c1b0203109090020400c80c90342014248501000d11011000c842a0094008001c5014406800380a4083c0030840403030700100807184180c0c102140000d0030300008407823040094082d04822448120031039507540d40c08483e8003101c1524081c1d54000c58642d101a150741da50b0045015641c2c07c0000c1d18080013850900704020710040320705040c08104034000041c03241c50921610803d03211070344103850401860a20510020140c407580024510307107407443c0c0310a8a61b00c24194400c40035903a844a2000000c034251150014180203026290755080d144001441c400302c0340801d503502403a10700031180d48400702c0030340c9005a00460303000784204003e071419640740d04001c210a4101030608424048018032000b950040e01d41102e49402c0c99003402c00300c00c94001c55030031103030013002c001003800a41c0400000782c80e07000d2030450b502c0001401d00e15080780d40d0300031a840140 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 56513573 1250 56512323 56512343
    0xa081b0d090b0702120a020a080a050c0a030314070314160903020307031a1302010c0201030c0912050303010e090109080304110f060301080303090d0914090c040506030907090e010c09060c030309 85
    0x1041046088005004100e142c0c00c5403107400111172241c06070303c40c5a40b00005a880400311100190300744000d084620101c0c00e14609041140034514240681404200c000035a030b80c1803043c90031300b0218074a03000340c09881d040040710729148805100c10f401600074440200044d200403c51032142800030051a800307020343d074080b5940d1400e91603d20301099010702400990700040e2131440c1c01141d031345100340c059550040a41e1240c00640080908a0020301040601e940200b1004407064040841c5031007103004541d02c0d0302d0709400d909040d0001d00340d040564140003440003c60079074000c1d00d0700035400000d036a114076500c0001401c9216400700054020038003000004420802102440c03048540350251000080d55000c1115800342900902520031900d81101c3c6550804018640c0c0c842c545903651448c1c41c3c0c60710b0020305160401c0344c60825641c49020284225034040c021407a82152080090244100240b405412902c4501030034040110030200349080c1840394002680070b80e00514182 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 56514823 1250 56513573 56513591
    0x80408040506070b0a05090c011707031418060603010203070e12011404060e0f07151b170a120b0906010e01030b1806010f09031a10030b0c09010e04020a081b0d 70
    0x448040101d03000c1940511b0000081c1da40f03000401c010544900c165210490703410020907900d501032000d4000c0d802c042d42c4d0121703038402c049040495401009107580c480035120800050300c0c42d02c5001010b2074081c0c0d0051041c400032a0300010503118001d01191425003d0083d009070300d004244490650b204409203009100a020707850f03000010084080041c1d902c443d4808404607940c2e40c107886010340c0b401d55081010b1990313114007403000f10824000b55009a603000c0c0d454446101c050010300c88800000003e418103401d070859043c80460810700000c0c002a408140020b42000c0024140b5042c40742e01100502a40e1003980448102d0000511043c41140f000001c106012011540c09001c541c142242c0710401d4021000042220340c0400581039403001c24049000c03801014041ca401c28a10301c501200040c14880011b10030038000010a840d403a80c10001010b403100710f8645070185104008080e2146c2d8041e10141c1c1c07210303113007520599420001c41d000310300348242104000f285107050702c01 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 56516073 1250 56514823 56514833
    0x406021b190210020102030405060604201306020d110d0804030309020409050a030f0c020d02040e07050306090607030b010e030309010c03050405030d031a030c090f090a06020409020a0f02060c04030308040804050607 94
    0x1e028180265050080ea0b9a1120140d00301e104c2600c0140040e0b10a8000828900c0e147d0050441500b0154210035801c000034110401c5421031084c41c0c0180040c04400d01016904000380320301d4510038908406000c1e03c030030901d034641c00c041a8220070028071800041c180350080e006451002e9020f80304101080c15810440d4480c541184110001466040c8000256101d00e27100c4101c030750005d0220340c45522a81c2000002c201800c52810030380101d440002e8155814004203109220800c0540014609440020100c0e104800180d05100c000307030319010162400810350f805050282004481c030019400e01b901c503805036500c4a13505109488030b9a1080b58143c205403081c1041c01160142c40060208258031481c40841c0290010812070008004a4800c4907194008019505a854094003600d80d8800d0342d2190b042014025000928405000c0c4d03c40d03040b4103140070900c0502540e04214824103800c1c440c91201404100542c00861306102012003114028000101030559903e480c1c641 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 56517323 1250 56516073 56516113
    0xa050909040f02030607080121051002120a060b04030f12030f1503050714030c0904060213060915211508011505091003080307050a030e010507080604110906030406021b 74
    0x4124005e0140e0300c00308600500581c24603040e074020203400c42940642d010a900c030900185025580f03403107041d08a010410580c030080807641a0a1004922454000b00a209495003540682100401084100041984044a00f50155100081003402c0303d07002c4084000e04804032040742c4051426070039143c88a011502142180d1185e0241c074000c55a0b0b9840030102c5404c52500c9400d90030081100340140342140301d840d0b015114050040c1402c2d103040201a001809400c00302c08200001018450346c1c0482480c0008142c052600b01c1c80030314200303822003441c109404035140007501c5007501900d404001c0e80b00d00182c07409500810000c80003400512041c507203442824012403291000c951110301da05460400d40b07400c50111451519040c0d01269a648a01c0d02281015a142c00315035143d1000c0c0619070040040d50f4440c8079500740b120401084990901c4038803107125040040b00074a0b1596821380742c0c0a50050030043c4c55030f001d200a03e540100d000340c0b4010902404d140b100c401000314070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 56518573 1250 56517323 56517353
    0x50d12020c0306091e281a0f10080303070909150302061201060f0207080a020d0303060504090b0609100e0c0d1d0303010602100203040201171005060715050603210a05090904 76
    0x305d56801e048000c00c003a0340310b81000e40e1460080d844c18801910170700b9081e115004041c8506096070b40342c41604e54205100780d06807607150060408800380407110b0346184505001c0c040e918044c3d4558109141c014081207000c0c403d072208180c50701c3c1030700c20b04134108054a00a503005414580e440d08030050b03800c40c1d00001d01507403020950802d620312065100007200819101800c0040003400b14036000c01a400300c410108800b015125203001c100e94a0701e00072501e5062007000b00c01d6050801e04100010b008000306500b480d540103000800804210901d000c0d003042001030f4a55455008801840140c01010303000f5120080c0d1001c04820410300100640c100d4610750300780e0740f032080500500d0040e440242c0340039001035007000891030a50341790740040303070803440c0d821018500070360320000b04401da0820a0180c8014a51001c0c80c000025039000c0c10f0b07840300084018144018901074401c550041d000da081d510b2813004941400014003a1040303902800c00100314040a203454036202d40c41050b00e0b0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 56519823 1250 56518573 56518603
    0xa0b060714060f060112050a180609020f120d3e0c0414070806040e07080c040b040603080319150e090d090f0515090907081e01050d12020c030609 64
    0x2d000641d8501c5818056010b15016501e26044c015140c81241c0a05409400000c2c8540da802d0a0704101c914030009111961080d0404200344c000c5004021201102100d807600a081c08500c095201d200441e01c5458020682485100700111a99840b40005200c003070111032124028080d0747e0076801c214800941030f039142200d4443c1d01c0c1e20305010a840c4108400ca984400840c04a0703112405510500e61040c4060030015030b00c061624214a480c8040c1d0064007103800501440f0107504040c003a00e081c10406445c244400ca00d195149130302c42c07200600e404228039071200c404032841240e820001c034902007100603400483e1554a035284610b016240c1144a10660b01e1401401d80180c2001003122103000103810300e2440c00d000e005018407414a2003405134010490b1021360b0385e6a42485021f0341d030540d182c0c055460040d80c1c4000014844007060704044042c1e0041000d03642d510000381840307a10248030b80041c04500020383c500030701c00c2e40b10396060060340e0800802c64000207560031408001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 56521073 1250 56519823 56519833
    0x80d0e0102040f09020a020a020f01020f0a030e03010b04020f0405190b0304030201020d0507030e070510020102040902030a020a0f020f0c01030f021204140601050a05010c0209041b030303021314010806090a0b060714 94
    0x103000d410102d202e0305c00006c015800107840200903107002c141d00e103006441070042d90b0401c8039003151300c0d003001442c040072030200c1d22a045064142c1001d00c1004a0000306980031407070301607040d070101d8560090f0705c112441052070f010301c45a200d803c00020001058000402c80d164101440d000c0e000c0c0d0010228105001d24000005040a1007401025001c15102e4050f1980c14205401d0001310001d8050b0007083d59002c1000054486092004510990100c100140c49a844050090940d0080300c3d003c011540440605009032201081c40b8680d50007d003000241c0c1c00c2c583d41560040d015010900040221503410007050040c003070760808488501c201600e45e03130fa80355020080880e9050160724002a001d008040050610422084d001402000b40c40d5400d0200419140760550580084000a401181601d80c01102c00c80c0940a0080c0015881244054100091081034000c117021700c503200d90000b00d040081190310403004100e001c0c101c2503641d012420404444c45a1011210140c811 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 56522323 1250 56521073 56521079
    0x4020f1b010b0904020913031110060807080106210201020a020904030305060406090c020c0105030a06030606030807050d02031c09060f020a0302040e010e090c010c140a030314060d0210030207080d0e0102040f 91
    0x60010103200300e03802403400911b80c0341d00b04840e50580e8440011009c1c000c0d002c442d680c580c0320070403050b82581c040b681d001c540c0034241101242000001c0d03015100c0350381041d5040c4400134900341984550304020420b0340100441e400100d1401c5102d1030017035040301d2107001f84020b06505420040c800d5105031401e0040ca0b030b40304801c100300d4410a240d400180c01c8042c114007150304c1903000b036802160709407002c80c1142e00c03034440004558aa0740111b417018000280402007000c20f02901e154043c06001440c140103411180c8944010340d000d1205d100d41d03940c0070034000c1003100e82c000d40741e81c0d070880703411034490900c2c9001800a52260040c0b601079140388000150001d851030302e42e032041c1082c0014142c245015001951004407001c8122003581403441000b4580104110903403400e4026900490b00c03c0301c06002c03081e079440203400f450103100075034020f034013684900800b0100100385140041c2d6030001c0b030601c1c0d202801040b0b6114101800c010001d040410150080e005844ca0b030f0f030b10414150f503 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 56523573 1250 56522323 56522329
    0x3031d07050102030306060d140c03060316030507120201170a050108010605031f0e0a06020a05120601020d0c0311070801060b04050a0b130b2a0609060c04050603011404020f1b010b 79
    0x305038403505005900820020705542406000350144942c60742000c1124074420044141d1610100c0e04145217480100800400c0d2604010400001080d201124403060640c2c41e0203440d094103005000030700c44c2d40200791045911030b001d094031000e009071034038040d030801c40c03806c4c00600028400d80c400e03507081100c08240d80c50702140c0003204400643d4180d04e00341005200101524440912642a005180141021407250b000401c6c0d02c96482d500c45680d000c0c002000c0c1004200502054115030005180721005504191540080e541504021200d001e00c40c0f00340c0e1070300a45030050b0302154208400000c045084070050070945d03a00321035240c2d066841b22400301590142c160342110081c20000100b00b51441c020060801802500011404010b031135005d4061080c1888456191380c0030300c040180c0000d041c07150b02d8210045c14200c81c60f02d407800e8000b5901d4007040c0919070000700180811a000d5480f0b60443d0392070010402074603150340f040e0403d581201000041d40c041035003000c4070280ca500d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 56524823 1250 56523573 56523583
    0x3030908012304020a0f0609050112020a02100e070801060e01080d0513090f02120f0603010e120d151208070c050409031b110a0b040305010b040203040317130b0403031d 74
    0xc903411403408001540140d40c00d80284000d00180e8200f1401c00e808203260132030407160b1b00500115201c09000a26040005092a5440306103060540c4103000901d400c990110702030300c0e20809c1000200da402c60098032181090a140d01166566280880c0040c87c80d620450481c1210401804e03508051490380080d0340c00d204403402e90312003042c000018418413040350b000304400c5940e880018100000b1780c1140340d480c54142d4034940401ca80342c007000f44500c0e0902032800400d05040140050503080b204e580e8407405008142c10000d621426895610540c22010341c1c0180300040245e00800c009051400d01b980c071002d030650f1a450f503030f40040385505142c0500c02c01668583c0e0b40d402d043c00e5120309445450104982190901705209100001d80d0310403c280700a44144040700307907201d14502c1c241c0d00711047c080c03903140100c1c014403c1201107500443e0070390006200100317140c200c6d901c0d45074001d88428070040051208410000f44002d05516600c940b40000401620403070081c0c00b064999603131 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 56526073 1250 56524823 56524841
    0x29040806040f05150f06030d14030a091401020a11060106030507020604060c05090307030606050f011d0f0303160b01050a050d120e060c070308120f01082a040203040501060303090801 80
    0x2640000d01090001e038840441d19011805601a02d810402c03521034110344240030b440314010820505c0900000d483c05201c505054446410106c0c46113540101528550000a01000b45240c2e2a200c0209110003200c01210b0038180c1802155604071441c0058504620080041c0d064424000007103604c5029200c1c483c01050300381c00030112940d032075403902e018150302009a0304106c810301881070903480030084000518400d10002c1005420702c810b108807004170103049070400146c2044026008000e0748000341c015400d84801c4943e29814010078034610070f07a8407081a079200311301c2c080180302d809408641070f03420840d03c8580e444c4c2e49504010f51011b021030003031300300b40340e84c82d000c0d04441c002e210b401c0b440307840603250700d090110003200c003410021180d20a8030001c1c0c001404600c24680c070022560b0005207440000c0155040010035039454207007080c042042502c1d90b03540c48034240110051115000010015541ca02c0c092400b64043c116910003200462031441012406002c10b006480302 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 56527323 1250 56526073 56526089
    0xe0423100903030207120206180706050702061e030c09040f0606023a110c04020a0f050c0c0a03050a0b06010f05090915040615110a031b0215042904 65
    0x94061a4039a4005140005040342416400c101541c0002ca0100c0f044040310610340150455192203582d00c42d4501c15868074000c0c0d50410b14090040540000985004540560b56161512040308623280c0f49500d5465400b101d9101200300450b00d4000030041c03c0044083c0c07011701c0300d0705140e81c2d5417003a11898003611001d80c201181c50009005008036148152980d110310700140b40c40407941c0300051104121800c0000d060f0002174a83d51800c000040300d1031400c0c0c804500c0c0211409004000424000e18141081000500e98400fa0710800107170070343c50402085400e50b00d80e20b1174640d41d42c4216200484407422103c000800e61b40c040d0302c00d083c143ca21622018030303001416003005450b00d0001d0003c1106107120f00240400d440340d102d440050000382032000440110035001504181d0b0820340c604496122801c074200180d0301c184114203420100c542c00000310400d03c0014001f00070040105c0140601040c00651180c000784004196400c010f0190410744408503410443d00c0340d8010120 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 56528573 1250 56527323 56527333
    0x7110a030c080c0c060d0b040b030a021c0503042303010f05010605090d0c030b070906021b0a0303110a0609080409061202060909130606080604030801090e070b1e03010e0423 76
    0x7002c00c0b0801c004242992031001552940f010000001c0d0f07071504040d5100c000142e40d58903100450030184100d40e4000c400710700401e400c1d40c55a0014a010a0302101411880d0145003c2030401c0341c03c100380e8000d40241e8a15954101c4941c2911402e8000c81400300d00c65030804070000d551010030320400d81603c14554075146090080030034089054800c94003107800500500c00080403500c90360082e4098000c554400c14001e241140091a100d540c0c4441002081031a03588200f5660300d1008078210390340760a150000c0307110b0b040514202007003580044c1c0220300300f0407104208401c035001803040c0c1d030a12000300481d50b144c80382066040c4918000030f4100d14204914403051508080c05136001a2652016500c0301d07171542e07810b05507200b036446103859610445c10f00c4105900300d0fa00b0340c090041610204040b00703680004681c1e5000c00e01c41d001d00e18000007094804101844102d524620080c1c160319500d507520008100e141008890035210045c03202144230300030500009103652030b060540141 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 56529823 1250 56528573 56528597
    0x302030f0601320706050708130209060a05060a080f010b0c0a11060403021306050114030906070e0619110105060d0b0c0d02090a09020309010b01020606011b021809030307110a03 78
    0x141d4241001d5401038040042c01c0c0f00a00f1810f0b080d42c4810b952940a00307966100c030a0382c0b9203c01034035405000041842607000401c41c90b252400303081e03a1860380484180c1e00c580c0b282004140c24101039041243c1014000070841000e582001541e8014184003520b0907042c0c1c1c3c1c61135400018041c0c8411011550404820701010421042d482c680c204001440980b900d40c1c0e95000803101b10148171009110703521070100300004e68000301444c84006038046002c4c690718201c4902e5481d444000c3c5900305225840c01c060032161250401e035488600903004110014000040103020b040c5000d0700d0014560a041c0050294100b00030040c080036400512a1120b489aa1075400150401803c5070302241c0e091102a0642c0c1e10002e1082c0100880c0a005940f818248000d6003075400c4500c086040d540800e0034048a41da02410602c0784020424040000d4042c1d4800501103820409906003081c440c0400d000c00120080000e5000e04010b1701e0315125410703480b103015150100713180c000d03010541002001d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 56531073 1250 56529823 56529827
    0x815150706051506040807090c1d1e0312040924060807020f2e0522030c02030a0b091e06010509070e0301090b07030f0209060306040207030903060e0a060c0302030f0601 74
    0x910f070000742415000c640d00c0c0303886011890310b40244d030090080d54030500080020340d0031071144403584140b030f20300700c1d81c0c7c0c00d13070070a110742103940303080803140905012050100b0040298010202d0454000c080d0340440311403400b02d65043d000380c041c0c00404c91910481c10700c16100100c1ca20a941000781c80d900c03e070391500205031010303e80146084194020716415000c6800103101d651416070044080031317a0030030801c0c1c00440900f05007402c10455441c0c98140100d2050102c0100f40300e07080795076044151171151070110b4440042900c0250544a005079807000c00c600c540400d403182c00304104079108009088411950016490103a6a142d00002c0040c03020f81420b590655001e1102c4c20030b10502c18602001c0303070031903008101c10791710310741d00b413040c00701e0154140203100701c8407040328003507050a600780c00003103e40c1700140c10584680c0d03001500340205030194201d2070040d40c001408101103a18011659250103400804850b601c0c80e055074810320600030310940e030080b80d0260800e250b6603141001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 56532323 1250 56531073 56531081
    0x7050d0515041407060807030c050304030e040b0402160503030106020f0a0305041a2802010b03030a05190c0b040501090b0c03071704061523040605090403080c040f060815150706 78
    0x10580f40075080103604020349408100902c000c3c01c0310394642c0040e10781000700404841041e0003040030004104248408640e000c0f030071102c0750504840c001015890f202c0060700a1040e445114694003809100d0014000048041c5040311505e4003582e561542000c0d07881e80715201004004d02103502408244481601000c00044c00c1400d01a20341c43c2c1003003008903260105c40d202e6032210f400500a43e03076024650a00a200340728100f0b034015414819001c1d0b020303180b030081d000362410b4828480e403142c28036440340000e00003107074100111542074100342c140680a0401210240c076500140404900c0c04400042220b00c60305290f610381c1041d403c411b00700d03a010f841c00382041d584a80c84951403a02d001d0300340d60040c000d1032034120b10407110350303030100c03469000d001e40320201d02ca41c0c41d0800403c0b0503141c0160013588141d051620002c240d5a20010400501450700901d880f18040c00d400300e403da0300540038038005c3c603081d0054403500c2900d104000a031044044a001d1500040c403000e4002081d90b00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 56533573 1250 56532323 56532331
    0x301031a040203010204050d050105100f0f18020409060b030901060b03040b130201140a0e0306011211060a0314070e091503070b1305030d080609070503060a14041e0501050307050d0515 81
    0x400175290654440c0018611503400c181514035035541c1c014040501c41c40001c1ca001000c003110030310311f15482d02d6056621060b0f94031408240303155a8101207180540c030703030440d00a09a1440100101900c48050b6495a0000c42d05c5c01455882d02c40c000c27400c5407401040d0b0384266401602c00346259203800e00d0b42450211940c00b281032010901c14400100c00031340c05401150740b5590f814a410424008251900f40103030302c100030009050344c202e404183c001030902400481610751030740d00c1c0b0781a501100244507245103500600a0791050006e0386600c04200c622020781150099000d80b40e40f50180812040308803011762507407100b00d040100412074809400c00c101161503c1c0050b41d1b4070008281401039140000c40020402c2c1c042196a1901100d0b01d0b0704038441d132071b00908620b40300c40403c00c0030002c0c0c014a00729841c0b40754a00480d40c0c3d503800c2600302c40c201a9014500e540000325010144c84203000791072290080010100300c0333082ca9008042c0c9181c1290080100c4055820080c803e00e02c054 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 56534823 1250 56533573 56533579
    0x1e030c030305090d1403032202030d08060a09020309070e06040b0102070311010516080a020118050d050306040f020a02010b10030212040f0c05100c02010e01030b0303090415090903020703020310020301031a0402 92
    0x821031800304084480b4174044000480c06180c0c2c910b044c0581c4514002d80f0418600c495040c81c012502684001800c513074443c02e141040715003500c3c4d843c00555022210350224110a00010030014460300200c0d400c8116420001c8441050325918100829a815104603d005074081070781000031034038081501803e1035045c1052894003103001400100008080700c2650040c03000a10364407102c1d42403144040c10500c0c0b184002c000a269030f42d860700e0b1883ca4281d00c0400c580800030030301765a1070b40e01502100104042c119620104200003034043e1007090b0320360f4030600015101d502070702d0183c021030b0025084940841e4a40d0303140d40c1c421010001e402029100c501d10100c0c082159250f05d114a07510000c140c48210084403a44001402ca254150110f4105401c008a0a0050301d001041d2801d044080781e0105195404840b072400c48201c40c0e010300512800c1c03112035014903801164640036a4001c2c1c044e54214004818000309034030080c840144581010000680d12514511495402074070003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 56536073 1250 56534823 56534839
    0xb060708071b0f03110a0b0c03040303050309100c020a0b070206090c12010b0312030a0501081603020d050a0219060909140103030c080d0c11010c080105060306040e07120305041e030c03030509 84
    0x20481d860160585801c1142c5e410800300c40e0240d40d1600500c5c0c3c00051100d41011460074401c070310250b489004600c402814404040081508070009000780c0703c1e607003c1c80d242005074010040d00250303103412452054680105020104403483e01c040f69962050049400900340c07443d1840034030036002e21560120300a550782d43d65000c02590141700384002c607403003404829182c1c00d010490f80222581070b804443c0c10303030000400740c028130b5000c4031142c12241c0444242810f034403581461070420180d04402988a40921103e400d05030440c5102800c2e00d02c10760f030b0748003121b0300c44072030030100c07010040c000c00c01140c02e03001080001d02c03500364220074501c45d020780c07402d01c418402d00c00c0a0319800d0841c2c0b03002c05c40112480003451000d1140c1801035019140031a4a03501d04000306031584405040356018036203507800e0b621811070801401c0300034001340c5900b00c400651400d0040054000c1d0094070705000f24414807045210b0310b5098542500c1d089245502054a0369409455a074800010303190046a0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 56537323 1250 56536073 56536079
    0x1b0f0602040f0e011502061b090d05011a04020c30040b040311060712230f0304020a0816051011030c01092109090b0102010615020109060b060708071b 66
    0x6140050300040c046109120b4030742c0d061088642c3c5040f81600301600065800040d001c0d04c5500050b102e80088141075444c1d0143c0015889110701d01c104941642c1100290f41000d04000c81507101d041c00026243d08507044031020010041a07205541c0d590806501480c45070f0b41c803400c10401d00341d442c2014413030b0484107145003c00030781c0c94000c1d901c4450b071048041010024403911081c1842011400c460041c40c041040e60f803211140440c0f0401e1041104c0c501040b10058488120a00c0d513128000d02551030303a02284403e8030760b5004440c205d0291a41c51400280083e001902c00e0801d19a24044440703d42011701b400a480008001d100801c00c03085000c56010805200a0180004541c004505044107040036070207014003400c10442c480403c4c603c0300340c4580c4107001400b0b80300425404150a11044e004078050031080e00300c1d91034a00700c2e0101080c219015800042060300c101c17024044030036103070208229401100c00241070880c00700040f40005145480500c010484a42211050341d1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 56538573 1250 56537323 56537333
    0x51f0311030114040c080618030a030f1808071b0503030403080f040312052106010e060c0106030204020307120606030b09061002010608030309100501051e19091104090b01030c1b0f 79
    0xf4003920144c89840441c1c80620540c0e0b401d020955111040da020308800c0c1622005150707030381c46040c083c001050341d28040880402c0b180e820a18030b14400b520103400c0e01880d03080100840e13002c5141218981541e040300e1015001d03e01504044503002000356050500d5502d914210390301c042010b4104400800010002801228406c2c12284496a0342ea8542001c900300b0210888505054444200507104000043e070f8003103000000f081e016940c0c2903c4101c01586107000d4440c60300002e500034000300030080d406501c1194a0f05000c4204414080a681d0380c409904540c10b80030030320781000c1c1d2400000c42a04150000d40401006440005030040d903502c485421038006403065000b5800070190090300380303064081d02d0b02401d012070321803900c071a05000220782040d0900078a802003107800440b038884107407084c00d00018602040c0520070f10000403c90031041d4000d014440c01203140c0304104100b54440c2c03048070000d90043d01c171110141000405189000c250722421035a0646001d20080028 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 56539823 1250 56538573 56538611
    0x30c041e030203010c1812020112020307030b0112060510080408090a060518030c0906040e030c1207021e0114090402070f050105040b010e09060714160f06051f03110301 74
    0xa40046039688000303045104060a4420304807005007000303188001602d00401075040c81c0100c5003042e0b01c415a4213260710050301c00d40030300781c00c15008a101108002031a50980c00c0308842410907612090302624816240089034054050107800c0781c040705844c100c0a003d14061500180149c000728140b41c042030000e03081103010782000000441c040342800c0d02d80ea403184500c40440c0304a014000b07010140012540140008002a00c41c80c0c5600580621010610844511103418020340b224801c9202e52608907510810049024801550a400c0418550340590b07080c42d40581d1b40400502d580d085c44d0a1b03642003000c856074402c4c1c2c200904400124026083c03440644a0030000c202441c0078107104400c0c80b0141d10070008105904104a05400c010a8032540b01c4081d0910104002000305552058011900180181000034009100f400405030400048070310400e0140030035070f5103607040941c007402a080c0d0340c19000c014a0620000e41100071000155202030000940d5007140c5046c25004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 56541073 1250 56539823 56539859
    0x60a051008160f1505092803050303040c090507050a0309020411040306060509010602030301180f141305010e01021306030e0c0d12020f15060904031418090108070e0408030c04 77
    0x40c0b000c0040403c00507002490b80401080135841c070790f10005041201401600c40c0489140c0310301001640703018112041c0000d1030034101990400f0b05043c2e16072409070350301e80c000c0d0740070340e1000380c2070030005218401d41c01030034490b40c103d9a0b00303414894103000a9024002881d4120392054881076041801e204a40140c0019130040720041010381c40c3c10280004c0e0007060b00114210f40003000180490044254240e8014000860010b9804010701c5600010701c004040300c59000b200009001d082c142240501c5200d6010310700030490390090359003207401c030301c184207100d00111461a07040003598081e40c001200c2807024070030b403810a210000000e964801180b01295129690007800f0340b02d5604114540f4260b0440c0010715080880c04075150300d5020041000344195000b0002034201489944810100f0301c01401c11500c4080d02209500710718010302c1d203a400740725601c000260301d51000400d20112180c100c15004151925160f801403075000606800c9190390401c0006a1000301040c24248 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 56542323 1250 56541073 56541103
    0x316050a022b0e03030405010806010c08040308041502010c02070f0b0c010f0e070e07140706020f070b04031d06070f1103031c02190c020a230604150906090602060a051008 75
    0xb05152080c09440d400820494a01950080c4030521860740c00c40e040c640c200409003072000c502c1c4c0341407038401e03101d00ca2504010b00c030b80c501040010f01c1c402e50f5010044440d0068000b4080240002d600f01d82d541401d10840b0304845111004000c10000d890050120341c06010001c541c1c03003202030301c19003950400c00400401d540001c3c000c00c000304800d41e249411201701d14202d102c1c000403c403000c0c1a07028404019003c0d0f980011820320340c0e5900c600f00c0d40c2d4590710200c140c100b0702e418207000d00410b0719040303021046070b56000c46045625208048503402a8418108008020b60b42c0f41c003111501900c5841e0303014070040202d40f10040074401c20001340018a40003594410718100c402c40034080e03034462007017071001c0c0301f0034100107036241c80080f0151440214003a21103810403104115914401000d503401c01d00c0082c000c101c2441041c040031000c2d000c0c7d12000c14081e91020b0440f122050380c81000c0041e08050301007554031882d40c00140e0407842d002201c1c89410340b1414bc80d8100291441580d403 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 56543573 1250 56542323 56542393
    0xe030409061502030403060c09260705060c0604060f060b0f03040c052d0a05040f0504020306090d0219020f040f020c101802011b0f0b0405120316050a02 67
    0x5400345500a1101400448aa107640b2100c40ba1002e543e90040d808020300311130712007640d00e4440d442800301c0c5000308904603102102501400091101e0080e03450210154041c600c0e0201d0303a41404006c0356542c140b8880107081c25500c640360031000703080702c3c00482c2c01075440c0c9900107200341480015002400718139804e107540e410580b4040107001300741d40c0b205004581191410b501c030380c00d031000c1181c4925804000d880d020600301c00075050704040e400c0190b015180190b082080740c01540483d10841c800c2e0201c48480d01d402064640d42d440300c000160041e403002c070724203050200e181040d0000d14130240c80e585101c0707580000142910b031216200e0a150b0307401f141e21081f540c02000000000e24060350200840b2030714841c0201c004134101c3d0064188100c02004c42c0500010405421400342c0101d5140004165403601042c0174006940a82c1d6134860030b0b808120481112044178011b5400d040790020000107080103450340c0d00a5100b560648c007903001e140a001800791001001c2003c5440d03860 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 56544823 1250 56543573 56543579
    0x80c010f06170105090a0809060307030605090a061d010f1205010e1c08060a060210110705100b0a0605030606040611010207061b020f03130512070b071b080c03070303030f020903010e0304 82
    0x508590380140750045c181c1c0302070040310120ba10075017150002c88040e00c0071540c99031580c030280e000e030070346a100749e40103100081000301d1240c141e8070103c2542e1102e19403a510003600300280424110070b02602d690507032022002c00a60440b44298001644a0070020940c4407180011764100fa1000320060301581140e00507030451035204203a95030044040f00c8040e441c03410040002e5903004a410b0741051260350340c12100d10340c0e0200d81039500480e0702400b00c1d4001c181c01d100c48009016000b820501410013018041280360041081c0e911814000d00024145480c00e442200c2414130808500d4647d50308000c0031001c22602e025141e00203081c150348581c10001c1c3c050082c07800c0b0000000a07203036081402184002c03641400e1b201d080f82e40c02c03906650b18225488205007004e030540e005580e070100c0010540108521040407810718803200080030780c850390350800640ca0b40003020900b58103410a40c018400a4001e40c42000300344c545500060074a103200000c6400c4a80e13400c0381075040e03071001c6410 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 56546073 1250 56544823 56544869
    0xc09061c0204090605040b0418020616050a080a0314040503070b040f06180210020307020f04050603030f040602010e0d0c020d121407080415030204030c0e04030c0605010b22080307080c010f06 84
    0x2012000750030f523403c0005000000c2e03040707002000200001e20850001407522034040307411508000c100c1c0c010341550303100007444c0362968640e84424101c201090404a00001c01d42c403901645220316000000f8616000190b80e8440d29154010030465184085a0502010a01c3da00c070b101209111594841101c20306030042201007003c01112900719132003000030b0001610303101c40ca60b1803440305441c041a10746079100001d0540c010480e01d8090454041000540740754150000c10103247c0600035901302c1020350700c0460340310300d0801010390004043c800e100005000008500710701101d9140c08103c03003240c0300e100d04060f800207600b600c0807540800c09100745145c0c009100346400903401c003149050f01c2c50b56101d1650b40e03244200c5d00040302d0440007400780f5010324a000c0350103a0003142045a0b6071a8030454070315030048403e60b41c0359a0b9110280d120203044981c0c4105584c414001541400b20710340d40c06080c0d900007a244803140d5281d009803515460302d4010403000e05071010205e11032041059107 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 56547323 1250 56546073 56546081
    0x60108040f1a040302300f0c010603060509070f050a230103060b180102190506041403070b070815090403050405040b0105090402030a060501141606020f0909070908150c09061c020409060504 83
    0x3e46501403120613042c002c6d40741884211411a64454202034603501450581c03401031100e44d10207854039040c80d0400400030000300f0403006550042d580300311010b07140c00600a11103c0c60040c01800000100408184407210f03c9506d48c142c414900842c200c0d803204010501078200c0344070300000d4840344030b08011640c4c050007079482103030382440d441034100d26a443d43c55a07201701030006004400346040d5403201c2407082c01101e11580c3c100560140d1820101001400114200c58405001d224104000000c3c81c01c05192800fa9030503640311401c2500340003c101c001d000500704281440300410008540d6111400514490310704964005454ae14040000d00780b10b003004925408072a040007440c0030079148007a000140b0303411020060b2030391200c500b00c0080d44192050707507601041075810801d401d41d014400b0015614240c042d0b42c0c6442d406200c51007290000d4520401c0a1070500c85400345060140250901862b210505d16002081003448030490b402030308010b50f032545601e02441241881c7c0a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 56548573 1250 56547323 56547373
    0x70e071205100302010e0117090c10020102070507090c0507050708030d0c170a0203040c03060213060e030a05150408070b0a0207020a050a06080402010c1704180b01020105060108040f1a040302 84
    0x180074425450440001030b448641408001d041c05400314508080764806e401a25a000501105d50303114203088201594030030400d61150322a0042d513000c218094070600a558079244e0100090800394141601c03070000c0d00c2c03d8284e010804c0000d00a1710b001c548208420001440002c01650f6580e4101505e1800c0c1c07a00039610b00d0600640100c80c41d229000041520341c13082130030340c1c010703260f407a18680211141a40d500c00381030745002003440f0020450004070003003110207584503400920030b824103140c0c546505a1003c3c00c0e03900420041110b000c0c04a0b4245e9002d0710545c000340c9001110f54481054070000c0d2040c004031075001c210403045090000c5094080c000840300e0b800400e02c3c06900074041140100020b04000034164020100324403616603012a40041403410740f200c0d2201c010b04c1e400c82d80f02c103404800c61b05007500e01b000c950061050030f010700300680d42c94925554035101c022800003080380454050a02401d00e0135004080491140510301c298042c00080c0c41010000c1e03004000c4003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 56549823 1250 56548573 56548607
    0x901050d03080705030603160305030a0e1c110319050601060e090f0c0c15070309030801090204030503030c0a02070806041211060709171501030602071203090f0b1305070e07 76
    0x164040c400320342c1000e03071550700048900d001562680d0f00c00109040102122480055149003540441000340210151420303208555030482241f55600404c0f02c52154455084648500a4514008030b03241c0d00801407010006000c407951001c100581c1000310301060415150341d0888001817000c1a404100c44042101c01c036850300d080c0c00c002d11800e01204000d00700c40c506000004110031101d00c140030891306041508088211454241c2001d0054010600d080f00095031420002c02d8251152090310140d82e000340080d42140d44484649045900540c103182c11751007070442c0011540c1007046401d100e07d02c62182c51102207007510010b0800010015001c520390084403c10107074681c44440c85d8201c50100d01796419890301c2d492000e0401c0d1158500c0a00e5070000340c00482405807680041a030544035030a900702d60381c2c2103141107007103614100d401000403407524400c101180011610f04d402486940c009001021070340c4e18946800c10300c0c0c3c40001e801154500f0018401e030024040c06001c1508 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 56551073 1250 56549823 56549839
    0x50f0109050712050618150f010203040b040302010c030504030b13060b09091513051b0f0904030909110904020307110105010618090e070509090a05121c0c14070303050402090105 78
    0x5042c050301002503480300700382d1150b80b100002e00c01e58540c02507455201e05c2011041003401c2494a0b44142203848503114060148aa10f80581c0c0d44000200c4c0c003141c0000031010b0525055900440d204505e00c00c056080000500000c404905a422214091030401140c5441450035140c2001510b00fa1583d01c0d105610000c2080703c84d21000c1441000340000300311400041c0d84511020b0000e021400c1c1c050410300c01c911150001d82c1030b0754140e02c10860101d44091141d4400c4c003c102545804442c024009001448100540040d0340c204000042d100d003c40c13401c1c07003000c0021600b240c2045035030000003003401c40b031191403840c28810306001d4034451131b240940440b1400300d402401424440c02910707542d240e484615400050180320301901c801081e65440382444d0701e03919070f11045907070203544a00070b819124080842e58000c42e600700b09244892050040314034403001c004d200201c20201031205020301c45806034030420040040a00c00d44000400b814680180680b506c01604681d00540034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 56552323 1250 56551073 56551081
    0x61309050a09051b060d0e0105101a0f13030807060203060a050301020306030304030b1306091b08010b2b0c120c0503010608190f02030709020304030e0a0b09040f1e050f010905 77
    0x2040c600748203c1000d1300780c5100140d100100b041842440300d80000789107001c0d540d18034420107402103400b992003080e000c40125201c0c841c0040c02408104a0321201d80108002062010300d279000e070240a00c562106407110755a81c4446510381e110407012640254008200105890900d1050001c1c2109800842c19442c04801090b500d20840c08081c00a06265002407042c41038031249044030381d400f000512450300146400201240c5031780e000c4641c0303003802d00b000c161100140300e03480e8041c800801504200741c0c840c20000290084042180e0b00c503002008050100c1d88034034192008050311071385029030100ca820314860090303d64000d188245d040000802c0044030000748958030080a0508402030f001c189811555a511044025058000d6240001e141281d40d0701551155000e034840c10b2a60110702c0800c1482d007558064841050003c1c0481011418254880a1969640640043c0c0503a178501d1802031030507035100c900360760381c0c45104002c80d0203183c489082c018004c101c428441d50074 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 56553573 1250 56552323 56552333
    0x80106110d08010b090409080a050c06130201140c100c0503010504110c0a030806060408071503050f0702060103030311041a0a0e0d03170a0609091112070810050603010902061309050a09 81
    0x42c89254940b1343d000c00c0c1030209540717030740c4401040c03680b10044a07525124880d010340150003107584d5148a0048030001600302050324075858041d64140d403030010010000b000c00c6400d4010f021408910302c41c8410700c480c11410340c40f580110001a8440315240d600d024100410703103480340003140401c1c40c184a480444000018169010390307050801030310035520f61700030555501480c2c1c804262442640c0c4000b9801100880c40300c4603400b55502842113503504020006034550541349240168040001080403902c20381c01340522500c20390b0118900b607501e50000b000748040c580810301c100c8000801c141039a42208945007c40c0080d079076403903c4a0b05031405855200c0c0c14450060301114800014900091a80701c607015182545003040300c0705882c181202c0020103580128010300e6010050034010100095940455511700b0090a011410303101c030002406010f8103054041d921800400016500c03640038045c000b80c0c401071303500c14a16290209041d40c00180078100d15510304050000410 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 56554823 1250 56553573 56553587
    0x70204180b0f010f0f0e131b0e0a06090506210f0a0b0f09010608070b09010c0804060519050c1f0e03070b07020c060f09010807020a06021602040f050c070311150106080106110d 77
    0x248914071f40e4194541030080c00b405020b860507202000c1038202103042c00410341d100b400f400c40c40e04204680c503100c00b43e04044600668899a01070401c440e6020070f4035038200d8000bc0c4101500565241c04440f01c1250329000004100b1680e0011031400c101d20381003c00034155121f01900000d2010310718125000343c540c019406803182c6010005040b44813039005894034000c295010950341c0e81c03503030f43c2c810007801ca4000c81d00260400036203005031007d40d44918107850a092040340a0405030350303102411007015401c0c1407108943d40c1c03178160a1260038010700140030607034000c4d4601103580c50204e400a0400c021107507214402d040600c02c4a181020007402d4a40d8101c0c00e082c4081d41d901c4161003a864000700910051403d80000f99250004030312101a2008a100342c03814000348410307402040c140c0b10100c856451000017030001101103880341415000a885100a5504d20078020028003010350003604071801003000da500410009034400e02c50221004c4203405083e4a4140080082c482 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 56556073 1250 56554823 56554831
    0x60509030f1c120207051207021008010608070324080d0801170601030f140607031b0206010b120705071a0103020a050906090f180304080604031b08070204180b0f010f0f0e 75
    0xf008400700c42410300d00d504403400036400404440302c0f0003070080302510f184c0c060700089024100c42d0f2400a441c1c0e000758401030580f0100d440e041c02d90303907030f075203044006241e208440c003024840d4481c031400c1c1c404082c1140c0c1c09040304001600264006100c040c02000044c0e201c0480c2d0a900d821404024501198480c19681d21a441441e0314401341040c1d800f8142d0b240311071665009400500680942540c04015801c070111a140742080c4075500c00c0e83c90f400244148010780710200581e8255400c5520100e0780300400d81055414155076865103003000e0000907000d1880610000148250702d071034040d40e401044225000e140500e04440454107000001d0450000e424484000c01c2d0000c0e1102c84904070001c640c3d003140c2d1a142ea8a481540c0c81c801070710140c0c0070071004a8211140e0710060703905a041070300082d6031352910100e44d003031000800c1d01e841c6c4201082c40506c0428001028006482e015105051404c007055050480140f102c110991042d0234400c0e03c0242082800803a00000b940 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 56557323 1250 56556073 56556077
    0x80a02040f02041508010602011112010b0c030c03070b04020301140103081c0b0607150605010c05031210050901030807030809030c10090206090603040507090507030605010801050405060d0c060509030f1c 89
    0x929030181c401ca8001c0e0280d600302c00b08a84d010409020305550120390f00703040b00c0440d8002d11031900c011007081520320845400200c241b12a400510642c070290004042414001e411a480c3c0300d0100301e0b1038115001350001721003141140d018801546000d0150003640d07600c9403a10b030703a15455951954040e1060442a215000c1c100c10140d1085025500002035801e001d400180d07200100d14207030350100303185203d00079070b00d26102e4086441d51160b000300500c103621000961500540c507150f2019424010014080406500d80101e20b98403101d502c06c1c02103110700100e503115072803032078050030802c1e0003050700d521640180f1001c01e0026002421108500303441f040061108510700200d00188604540c0300d4004000000b48020040700050010440720b10010810442e1030340c42007181681c2d51031040c40d0005010783d0040c0300629103030b4011600160001e02140d007044040c0d03210440d03081540d00000200c0d1000c078910450303041c10701010544640e0800078241040401000041d80d2000300c81441c2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 56558573 1250 56557323 56557331
    0x105090108091f090605091506060d0f0204060c03020c0f1309050a0204050709050a08070f03080306030a0f060e0d05090a06030b1c051c18050402030c0706060906090b0a080a0204 78
    0x84800d400340f0a851400c40c042d0100e42030007015803411005008202c00403100d05160070001032207a00045408144522a40c140f4a201e4032842d04111540d04082081290b9a580b80007000b904246071004100504803134a481e80c440c40e290030084c0c03c0141440034640240d1603181052500e6441c070444001401d10040c3c001350007182410054502107038654000c3d0485d103890300380984690008202411628100c41444d44e807600c65904580368403030f0b4440c0040441404205000194040000c0d540c40b02c005411a102d219480d01d405200d4131842c0c0040c1c3c1e101e59600c0351450ec0b07490034010b00c00c04075054101300740381c81d2612010400c454440d205200405542d00084240e50340c0b41d03e001212441031203140201060a400e00544400d90100310140d00c40c6140384a4050a010722450107890041d80360ba0581d0320702d00401c1c88040d500c0240000481034041220000041881c45524041e1005880c00100641040d441a08507840380c080385100b03500e984420010f041001515511099050320042 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 56559823 1250 56558573 56558581
    0xb1614030c060c090a05030a03020303070806041803090911040609090e0312040b0703050106030b0603070c0309080111030901060909080d1a060315040b09090706140705010509061608060105090108 86
    0x40c1140106032031441180101024005110070000152503d410100c660032100da60754800c160783c512005400802580007400054a494000c0d91002d511103009040802d40c0c0ca940c041c1d001c58003c80030340860210344d01041c00c0c40404140d120f001030b00c06040e0400c0385040d040200103001c4889504c1103c0006444a0540504030028000e44080211550402a25090900d8030003000002124804002464200009000c5100e40102001c0344800781100d45148c440e014111a046428003082c4d041c001d0b5101e0009101d102440f450340210402d5451584a080070320030340d401c1d100700b0780c886861241002151700c045003521045a0540c1d41d100300014254000020320b4181100f250b1429a01c16004401c102c100440f505031100c100b4400c5a007040b1041c202d0040001d000002c0d503a051042c3d1004000340000350007800c03c1c14500c180c2e145601d050002640d00e550940300b0847d45602d00d50000c400348140040b0022200242000c00c0c2032401d1140f0f04100000c010f03000e90803403d030410503654081 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 56561073 1250 56559823 56559863
    0xf050601050423060304030c03020609060705070f0218090c1c051f0e01020708070201020120030105060702040f02130302010210060b0a030b0f10051e0304020f06220815010b16 77
    0x7032a00700c10080d20305900c07440d1506000d060703000300201c20b2740580603880000702000004101c4511a0500340c45a50404407642c48501035004036502c22a004401401c21500d1034581c210300d64801d5042c1c000805400000c0010300100139090300010180c4504140c08800140c1e0104d911200d00a50f424510039201a030b001d43d20291140c81501d000f07951000901d901032100b0b49000307000e818001e030000c3c80700c0007021003c5201000142c0200c064803800388010f0106161080041c0300150000b0800320790f04580345040400c07644200201001208584000c000f1075030140030503075521300f0030300040140c45d151031155100b40c07046281010426540c1d40d2168070a40d208844d001d505000601010346c55007902c1c0010382568040000452100c0c48954000000080c420469102e22380c003600419020f04a0402e220300f9422a4416020b690f10668288031580b0310603030014001c1c40712200508a801e807200030380c144010181c0150b0821310303042000214044000e0b5200800c2503210055000c500e500f0401 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 56562323 1250 56561073 56561129
    0x306181606050d0b010206060f0f0301090c0f030c0602030c0a020415091401080705040b0f0d0204060b0712031d15071806110705040507080a11070b0403030c030f0506010504 76
    0x1026264403405400420300c103078008090b181d040c007482c90401200801c07800590380d0f00806c03558560300c50101d00b0141e416060500d82c0c500e03c004003030004100100c0954802010007010b4000741c00ca000486c10400a000f20355562400416003400a503190407079100c0d03138035215142c40074040c2c040c64446c040b0400d800780c0e600d6040010b201000c03042040000c0704603605582c210078801da900710b105009001c6007030319180c400d00c61040d800400f0307503c2032804401030081140d07940005a03485541c1d6200000c441a0260007000f025125400b0800c0020040201078100c0d013000308500220a201c4030304c6900714000003254001040c1c04811184181d4644500b281c2508000100c0c0c1940c4221010004441d0f0700404500c404101550030341e48110780f42d80600c01119011280e00c80052a4440401d03490080e0b9400a18900d610520b501d150403034036107074501a4003040e18202d001a0785c0314112400d41c1d906104610803501c13032010502950130140c0000384140140d0081c410043c2c1d80c3c0c0303091040c0e0700781403003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 56563573 1250 56562323 56562343
    0x5060313150207060b040e07050102071e033003110a03050405010e01060f050906090702030901050304080403080a050306090a05040506070f020a0c0e101512020d0f050a0b03010b06030402030618 85
    0x5000c2d503444260f4588103014045814145000d182000e0f154045882c0200d01c210940390182d00a2030307442d203005c09180304001030707003040700a01c0d0313140801101082d080300b1a00e8038103050b107240d0505550050050190503020704441e6081600e020846c641e0031210004803805915117103004181030711141013541c010071800d2035240241d032030140002082540c15000b1000c0b07420450301550300c0e540d654244101c45404849190050700b00308100d09956004101643e007280c026003d50382441c5e1a690f45100651040550b00042800402003000e14a0401c0600c0e5200c0a0f8142c180b009090540d1030983d5404060700c3c174410701c070080d02d01d0b5540510800082042070341140d10208450717030711800301d04c845101740e41c000041c401c2607402045d0f81c60403007441500c0ba42140e0310114031042400b0b4a20003034200701e0b500d5640c00d44518000e04115400e00031a405a10300820020f01c0754105001c00d802c545180b441c250040e00c05200b0080566800701d1501e5200a0014890301003004800c6403030b0410b00111 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 56564823 1250 56563573 56563613
    0x70507060c0516050c0301060801050609010302010804080408030a03060e180706050a0e090a1406120706050f0705060727030f0b0406020f04030803220503090d05030d0c0309020f0a05060313 83
    0x2c2c3da00c1e81801070020f5040301c0e10328250700030070010391140011800e803003040b501d241d0040b0515004000552040c0111680580901c0c0d0140c101a1500c00681c10f60740500c8414000a0301da04c000d00004480340307a01508901c0c604080181c0f80300d01d92440c2e868a40ca0304c6004203014002c0364110610703008207110b80707805000a1000c520b600e00700c2c0c0003500510f480c1e400784901d210f07658001a071508024a2400d80e070345240c0c00500c940c07890083c04444aa100701c480500c0700b80280403080010707400308001e900649180d111810300c43c40c43c04001da00760415581e92000e4403115181003010501c0f4841001006401ca484c1c01b109541e1402c1c0038002e44540701c00030907118800540002070010b000040c5000e810070f401c1c00140228402e41d80c94600d190300c84090034a420400c840042d03486c0010008602c40e102d80c0507241000c1c1ca29844500b2110220f0302072020944850018007146000c0341000c01107602140e004070ba090400001c2035041c00002c080a59001102d1002014494404402c9191030300c46 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 56566073 1250 56564823 56564857
    0x406110d020f040305150c1623153117190915050405040207020a03141501150801150c0b040602040e061203030a02091503010305030c070e070507060c05 67
    0xa405944001e030b100d0301c030645d4180030740d04207605100052101140154070300c40a160921884004456014100c0c1c481283e0140c0902d2550b40716000b080140448940070501404420f01c0b4142803140071000101f00c8020000203070a40190110b43c40c0e8032926106202840401d001240c1c5450613003188058000402c0e0b100101c0c20000e68200b86032604010001940e0700800d03503503a00354200b4008100c5010001003801880305110600b441e03406803102c540001c20700315800755262110300550041104956a40c1c10000e021450b1074217128020740100b103c07a480401c1003a600b41d00403c0d0240600510300d542c0c88216101c200300f44190004103080340c010ba08007045042910301103001b54010300c1001940494180050041e1a00f60320058074940700740080d510f541c0c0e8000303015000790701900300160301041c843c2c0443c1c4045c013440051400381d441540190b9030b80340725020642ca002e9540e4840b4441e0105203040201d03040e40001910546e5a1020022901d03101600c41a81d440c05121400040e031220 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 56567323 1250 56566073 56566087
    0x903200c0310050106020f0f03091c0c0902040501020d020705090c0309030f0409090c08010c020703030809071d0618010305030405010302031b0a02070e1506071b1205010903080c030f0406110d02 85
    0xb45500140c100c450b40c0d000c41d103050f008071381c0c076680700c5c003160254555580050044003000d081400d146c0091800c0c80241c4100f601c82d540d11841240c1c7c0680068403150b601140901c51540c04011000b0f00b81040e00040804e40e240400042090400402000c081880400450781080040003034605000c480e222180e2942d494014040003420006410b03500c5c2558910300040e210018410214103000310350140c48080c0c2540c17016607184d100940a041e0030b10826074006816850382c1d08501d4a42892514424941460410030900b0b04460044401005c8440c0040000400000465040741c4d02803c2c0581c40b6500da500320340c1c2d100e84250001d24091000a040099668003103008400d0300c82210480295031541c0e000200d03e0401c40303c0c116002901082550003090500d001d103208a10b209844000c0191140507440000422200c102c038a691209140010107422140403030744000b2014640303007545080c4a212681040240c000380441d030342e49503c0340d0b0403203000d405c035810311458200035995410 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 56568573 1250 56567323 56567353
    0x30a0f020a0b040b0d0908130e010f080f060712021e0d0e190303090212010c05030f0c091305090c0613060e0603040c030b07210204051002010903200c03 67
    0x4001004034425020300c0d101181c0003400b00c0a4030281d9050420f4981030806000e9544000c103521399064606d0072041c0000b821310940c8a2101020300540c0221402035490040c3c0c4404640326500140c5c1c40f50410601c5900c00c0c04c00042c10340e40000d0074980245410034248044ac003e12480e0a08501d07c2c80c02400004a003051600402e5044070b000030800004c2030394018580ca03641001c0c4039003a404dc1e0b407410000821311075000669400d00041c035003034148641590050846042c1c40c3d5680c04a02c022040102030190425901d9000403182d1420f0710b030031007500c00207081c0046c1c08441c0c01000d5480c0041780c0000410002c10100540c003801055481601e0000b00011011500c207030700000b02508420402e40c24600296405a988040e401070164250799800210150041c000004c21030002a1034036085040b05989070742e1061000300580d150305203014001035038103101d403203800c1da818140c88400090b8071000f84d200000c00c11100c0f600701d070341c902d0700c1505003a02604502e80c903109100e00203101034 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 56569823 1250 56568573 56568593
    0xd0b04020a030e370804080114010f0602030c0c040f15060518041e020309030c0a0f0308060f0d060b0102070801020c0102180d0305030a110405030d02010c03060504020702060405130209030a 83
    0x60300c44084440812013490319000080342407408210012803201c612061280300b2041d404507510030038004d400c00e9283c241850844501e944803540c10380f2103030010040103154043d40380c09030010388061840c1042c007050f510755980c0c0d8450b009000b81d43e100c2c03081c9403070105540070b1110f120400f030038003850542d2010014250f400c54611980b8a906000c43c60f02c10340341600c02c00034900700c0300040c5030441005030060b10007504001d041c00d440f40810454502d0b551014402055000d2041c003801140c00b0351030600401e0780d9401882036001c1c9041c03c0c1d40008a960705648407d401d64040404607040306c000300100d0a00c00f82e0340c0410029800400d08011113070301900505501c041c0302c0d80d00201c01541204110380d04580301c0015011500c104082010800a50032a0000c2400301d680c8501c1d15540c0c0010a203481c101c00004c40042c2d545540403030500e40d03d030081d00002c00301103800390700300001d0350001140791040b4401c1c00e12401d80001d001b01c10031025010368000c035030300030700ba6a900d8a16003000c000c21 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 56571073 1250 56569823 56569841
    0x21009090b040e0a020904020d14241320060a170709061d03070e040302010515150d090c0f0e04060b060f0304060c0e1002030903010e031204080d0b04020a03 69
    0x900705000360100c0d00702407103009824a4010f008281500a50302800b285150240c003d98010354a0342071100404c420020b5400d00c558031400501b44040d4000411000a00e21200b070ba680c0401c41c020720104141b103907a21007034180c025041e680a00c149640082c5000b003e051b00340d0b00904080360014200385c00c40e500c034a0a1208145c1c440481e5141102220031034094000c180220360230b950b011038804080350000b004100b001d011247c0c415103800d15041c080c0001c44080b00181e4498081200406000010301040e48081e900f0501c41c0d024a610200a40949104001c0780c591b02c0328003e091089011011006208915003048020380300c0b980300030008801c440a031b440504054104040b402d003142150711064540c0032150543e221543d0f0728003d0480d2081000400c540105e00b4451640c600541d095018055002569591903050915082d01e58400c00364a191300f003402001100350030a0a040c1d4805e9102050950f121070f46d40310180100710f011782d03e41c7c011f403010400c443d8464040c0c2c012004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 56572323 1250 56571073 56571089
    0x60314010207020103060f0305060c03090f0a21080c03070c0503040f0602010c081b04120f0611180303041d060111010c09090b0d020a0e0a09050609060402090f010f0e06060403021009 80
    0x1079287d8807000c0c002c040781e100c020140da001d44005120030b80e48002658000100074182c0e010001040132030703460a049081c2c00c0d01e21202a200394907480c404081c8505000c0e240d0b080c00b0040749081005201c072400000c14180911400000c4e520800805100303d40141c906510035419107900c9040090003070080c0c000700e03000b103030b442c0380400c1000594020602041d000340028615181c00c00800d0307110003200183c07c8410035200d440b40400078005010b0036854400030440b5503102c0c528002c00f20b044200c1011040e0094204220600a80c02960407c8441c0407058503881e81507143d4100486020f80b00701c4d00c00009518000b0b9001045500803078610440311a01002d206240c601420404420804003009511500c0e4200c100090280820003503803246800400007a45407494488070b003000300807101d80d95507030801420002145051032007246c000c05c850080300c04640c10b24840e800e00020b18040d9803001c1d00f8a0001690682e075660803500515400b520b4903103100011840030382100c3c039901415007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 56573573 1250 56572323 56572331
    0xb0109060b0c0604110d2a0f0806040f0218010b070314033702040b09270711030418020a031d0a0206130504020f07050d020601030f0213060314010207020103 69
    0x161100c00e030426100c260705000c0c00360006465a654000400300000c8485401c50381c4c00c0d60b54000721b50048140581b03500baa4513498403881c0c444a201c10303103008076001a920f02070823443c14452010f00040e41c030350056101603004400c011070700015200003581039103040c90410000000c40e81501200c0a0841540b00b61152101d030807101c500d44c00c7d90b00084a15001034502415024203412109016812507140709880c01e2114801c014100280d030b12a42041710044e500051005039030401e141c900030521004d284100038803011528403400c2000191044041083c1d0040664198005008079070041800182da000d45880c158400300c06500300f00f200c400071a180c0802c2e188c2d2403081c0313401c80764016080f1029000740300c6036608100d2590482690094031100c11000800c281d22548000e00c520001800b1003070300e656042c40c04510b454440c0420008640100740104001805c40d0b00b00d46949604582086103920301c00820b01c020704640e4000b03820010101d59569034000198003e182e414000c4c0d90a00c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 56574823 1250 56573573 56573579
    0x140316031b02190812090a032c01080a0e0102040603020702030c030d1e0e1314060315010b0c100204080708070b07020f040e0a0b01061e030501150305090a05030c010501180b090604020310030c030b010906 89
    0x81d440302252110700c8058801c1000c283c1034ad845458031940c0035442c0000000c10b801c000010345d08a80140d00724502090340010302200750310701045440c1e15840110010404181d205038010319011a50651017400c40100342a80041400340d0400060380740b01600d440020565428082c0241004005003c284a0424080f80003800d010482490340c11004138006151303480c0c000241c0d22035006071000d01c00760007012141c1c10215024002080203007441c50040003840c0c2000849814010b03191b10000603018204102e10050719040740c1c08e0b010441c03c842c0043c134107070103107507860400e0100305004100d01a8403001040b440d80240340c1c284100c140c0d0041414041d5803001c203074101d540a0040c0451840d0104100c0402d91081c0c200ba6803001c41a000d5a00d0a031080c3da44514540043d800c007042070351200d0042c0321f103c14900410900c40198034091100080b210045101c1d04d4021341098002d540020000d200494002580c5006541c45100c0c001001d03170300e06182100c0f0300203000703c000740c41c1000000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 56576073 1250 56574823 56574857
    0x3051f0e010c0c03180b0309030a020c010206090705060304020d150608070512100908191d060f090103050a0b030a0c030b060405090d0c03140316031b02190812090a03 73
    0x307410b40200940320101d500307842e03480507668500700182e41504070010368001304030040324101460144141c2030080d6214420076070060b0800e400c80c035800e411540303d4403c104c6210320010f210700c2100e005403010b9644c0e803640e00114440c0000c01d100940500c2c0010483c07440702059501000c101c41a004c29501d02c0b03030329201084400c840a000440c0150311961510b0724403442c551003061807034400c1c4034075482e11503401048000288104990404150040b00b180d560f240d20010400c1040d80407146a80b0700302c208003152440d40218954181010ba0356000a412810198041ca00101004040350844040c03072a000000364100e0004991020351900498068141070103084d02404041026009a20280d00200c1c0c60b01c9132600d05504005000c42d101c500f04181340000e40c002c0054038070921a0524412010301961420412448440103429203a50040ea011490f82c04212880fa00c0f54250354140c140404140280a0703945203c3d5590020b00003503100c0000ca40005502c69150f5600c060703500294 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 56577323 1250 56576073 56576081
    0x302130b0c0601140a090b060702033f0720120a0312060807030222050103060b010f0f0806010507080706140f090303010803070201080702030c1b010917030d1503051f0e01 75
    0x134035508518810018040740f84290451800d440d0040c00d02820600d01d03030002440c160702c0210340d4150991441d850081c1c01080c4a280054060b00000317058800660b10b2241528441c90700302520161607051511015107820346c045828075070080c0004200b010031442d2a86582d04a20308801189011180d0409020035000d8202124111405440354525503005c0c0416000500150b040c01000b6a0b003605130328201d88185400b030340c0034140015688000d03400160050401404c040c05020005580f4411a54882401e40e071050b005c3c83c1c502c0d00c4030030030300e03040c1e00300c0c010014000d09081c1404407521510041d072029512a219922210791180c80701958580c03248401c1c020011690003c214402c00355009141d0541c00c20b0041c0b04a03481c2c10844100c5904054250340d0031034140304400d000c030300b003580d00c407281d034028009010362130440012000c4417503a6889420050000d0a454110310034418170503004102c0151b40040075a41240d00301000c446c0300c888515030648000d450700302c80c030407140350503c9 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 56578573 1250 56577323 56577359
    0x108070501030b010c060501080a03110303060a0501030c05040f0305012a050702040504021807020105010504110a0836030702040c03060305030702090603160308070209010e060d080a0302130b0c0601 87
    0x190100905100046001d004000d0400d410300c00440c504000241d401d1003824002c1540b24080c1030b040340e540c0b40043c0307000402048890580d00a20500195999441d46501100e400342000505210800c0d400e0301d00740195800301c03d2a481c514000028804190001c2d038102003100c0c0d03410000102001e00382000c0410031181d4002901c02d124407801030401d5400940c00600040081c1c2e070321004da20306000c04038011551880141d44441c01041582840e0240540390400b1a60882c1804500c3c0c6004280c0304004000c068000158441c2c1400403200d005240840c0705000391b000d0f2018551040540d507984131070000c0780920314007070002a207648244070340000d880d03000025520f4039074140c080291815014241a906015481810428440d101e40c4013000b18450144c09803a0000c6004000d40054140d0007218282142002c03c1900c0d0703243ca49030755145521501150300d541c2c1506040f0000c0c0503e40784086940400d1030041840c03c4900c1c003030031400c8a07900c2158903981e250809131028006c800 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 56579823 1250 56578573 56578589
    0x2031f030b07051305040204090e0d0801120303050a090209130c0501081603090611031017010b060703050d0e060f060405070f08070309051014040209100b0a0507061503030801080d0801 81
    0x503000c510098031800c02002413450142c0703032004441c0c86900003801c980c0203038450540c803070fa11030340d4070035150303041c4120903408c3d285050000aa601d0802020703002e06085200404041c1d0342c10005401d4107140c2c2c401d0803241d40141c07000d141450400c02c04c100c545200e0b0303c142c9040c0071040c400121981b2800d032003885881e4540805030070912640090b07010704a081c204803141d83d211218600805c000358081c43c07040407603125040b2210324006e064070000500c10350122169040c800301305203030748501086401c496894a06950b61b0038100000000038809200d41c0322a80c003842080c02401d14040a00798007e40c402c5904003d84d4031000c2080e10400505603e000c0030230400000251110300070307406041c6c9a801001034880c52040310601c0c00855840c800c0c3d5102c0c002140042c441075050103e401d136802a04041c20200d0581426006000c03405a128410304202c0e0018580d0204501500001c004030541150707008842c2d140c2c6806068242c0074000c081c401e00c504500401d07903920401e1107034100c5402c2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 56581073 1250 56579823 56579843
    0x61f0504060c05031e13120203060c0702060c0a0c05010f0c0201080609060a0801020309030c15071b060905011409100903081906080f030a020607080f06040c031d0102031f03 76
    0xc0020b9508610264054802d80414041c80b4030034a03040018500c0708402011050340d60612880c605c1203000d140d049075108030340300141c003001a2400200d481e00810391004540e1602000d00c0007415602c07a40c2d0311818140255910700040003640b0341650180d90098940e100030003210041110700390100302c0003a00240340c1d200425024103041203480d0b00100b000c5c0c030701013189440711880c41c01d980c010b070743c241842e6100151074203108206110724600040e6405507101c0c6400d240c2d1005280d2201021104004240c02140804200180c0d001d8020b25500c04001e020380c1c4030303003281c103590004111603442c0c00f4090045a844c880d8214465140002e606450704c0ba00358803090745405103403c80c00c2000c0f011035510b01c000300304000200040300e01300404400459403045002c0d0004d00f8140c1c0600400107020b00300701800305400c03e5425560f8401400d5070000340b901281b480407000392404001403c10ac0018143c980034509040d00194820441120802d03110f04040305103042c01e4503507200181c95801d178 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 56582323 1250 56581073 56581079
    0x9020d1202010e031b06100303080106050a05090a03060b1305060a060513050d0804081002030c07060902011806121109150c0106150917070302031e0102040306090605061f0504 77
    0xe034800180c4490321500c0001490362452101a15552041681d65600316080404085843c41085070941c014858040c0c2c6245d2840c59402800e4240306000f030300240000803e1610210b4442c4064491400c0000c004940300d90b03490a10000419120310722500a100b00d03070681d080b07405076018150241d0809003029120910f0080d040f10309030000c841030010502c05201c00541030380c1d1000d1041c0e0650140340d045a8952134040d00314503100d12080d1b04000e0500510800c2403140c0c50b00305817501d49801003004070300c1e9192440100d550408503800d90080b90240310340070520681c05400c0d00441602d0f81c1c000c00031a5004000340400f80504d40b01a0740c0f02544c20480d030b00d203c12030405080507025180c008143e450703c45004140e5514441001c60008411803000c00c40b20741140c1d1000445110700c4040d02c03050703007140c0100e80c540101410f0310481907460903035100300310000d41c1181d0042d40c01040801000c89586401400b41c8000d443c12845080d0400307096012000c01500055803091584541c1c0c60240307 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 56583573 1250 56582323 56582333
    0x302100c1b0501020306090a090308010b22061d0402030103080406110703080a0c030e0f0d06050c041e050103060e010e01210b09010b090c0708040317040302030316060c0309020d 78
    0x62980362204210085141800c600345044403695240e1251001507200c4c0781c00018480d91100c0180728400250800074041c0200303130081c9031070b41501d068048942e6074074030a00c4c01411700c00f011a480f0000450321407000860a40c8140f01c2c52411040d4038000c100030690000300410381c0028000984400002c00003008568068806d40c24600b04da142a41c000c680c1d030381c1340c0000c40e400948851000c2103904000c403003050750180c03072003520311022982100601c4040d004581e101409107001000c00f40d681380460224a04082603800801010408054121442080d5030010101d0f1041a010038144000840c6103400c03030f521641600c2c1c040c00c41c542140e180c8071a44040c03003c181007199000d14444a09404070b0380c00212a0311a001410002c111188071600340964040c00070440c0012110900c5a04001000c800c1140c049a801803000c1c9201410260b03889650311031588021b604d40b00000340040301e0400a01d59200c0240142003c200300005202c0640641c1c040c8031009500c00203000c202e5001507 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 56584823 1250 56583573 56583581
    0x30702070602060c070c1421030703080a0504110904140106060e040c0f05031302191d07050f0a080a06051206041101052113020901271401170309091510020109030210 73
    0x3c0d42c014a0500206034623240c19680600926000038103410014a1105250700280c4e402d40061081c1002c12007807030b142e251101e1920358010f0282c800c0c005c0350046014019401c0f000130601c1b401000800c002661071001902c001c10003441c480c00b030307400d110090000d03a001e001e14085070041c50301d03418a95501c1e20b8020990480f0194102c0c0d102b140194180781e4a11650f500344040c2407500c141e04840a50070b6003000401600a01540c2008010460f210002d204482601e820700c000d420b2568168035042542c0014000980005410241c0103888050b206400a2034074010360184034140d48000b42000111868403c1800388010084421940e608040c4840c5134140d1145501480643e1502198006900c2c1c14080c2e000e00c09240d00d60b20940d1004000800031a0007402507c0100541d40c10342f480074088400511030030803007581502039290720389000c0c411a000000b0081107000c0c00d20345440401c50b0302042c140c05ca4007503144641d0b0300c101c55005201d0300840d01d401d1340060050640c0c000c4484090 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 56586073 1250 56584823 56584859
    0x50a1d1e011806030b01090509010f1104050609040e030d0c08070f02061303050d0e100b0604030f02041104030501020a021501050d0b0c0c0c040f060914132006030702070602060c070c 80
    0x309030f032804000085188620010301900080c5000300d010b0421000c202c0c00d540900842c0d61040385005030140582d801c0e1320403182141e005650003a1a9000d1400041c018800c01182d0b424a010000b52000000a00c0c0d102000280702070b25175180c1d544ae855030881d071760009014010b026074080300c0072800e8100080d0000412a100c0c0c603080d031410903603103110419950b07580d440311340c1a4040c10000d0007000d021701441c140c40c0000c0c1d50007800d16143d5113030319079084820710002e805607a6984180b1500720230385d030446001d190003c009550398140320100a40d41d0011790702c18032240f0038010010410780383c02d8074039450181d084072800d032158a42e01c12803209030340420842d101c5403055409130300060701c0303d01500016411400c00010f40b0fa24004e40381c0c040d40c413500c801c405402500d00070401c02030340688840a8590304844003100c1c0c42d01c40c4618a4520b00c61450041c0e016002200b045081d560000d08072040d241d4540c02d54400707072201c0c1d806480901514200a10868848074184000c18200c0c1c011000c0d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 56587323 1250 56586073 56586119
    0x70315050c09030d0f080106031107060902060708030f010f06080402030a0311010b0a180b040608030a0c020406180506040e031602010e030c120f010b030705010f03090309050a1d1e01 80
    0x50030a20b440001d01d840b100705810408a03048007071400050b074000110754014030320f5040c00d020f1301e282c80d03202004900c40c44100414040d03032161101c3c190b4035000203880c61154084a91aa01e083c0a06030400502c2e0900c2b8884118000803000306166104003111402207502400504850101e640d0039607441c3c1c035610b91602d0a65a64041c020a40e5038403200c40010100400300b0340f900c800404805065490702c0480600607410f1803400c221300c1c10700208030780098043e480e2450304d401c060310009000d001281c1c000514a03801c446038000110984e0700c42d501940c001c0301c00700202a01c06c860aa202e0040c0c0f2543d070b0a42c00c1d4032184001550041d2102d082042c402015034414864907000550300c682d0302e03076420b016640320031100985640f00340307d0080c4a03103084004140591500000800c401088540c0e10308042d241c24404040600801c000c070042e0a00411030101d060b152803205101070050804240242003000220300c02051303803032414070282021014611542c1c20140f0000103000a441c1c0c8100d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 56588573 1250 56587323 56587327
    0x105060d1103070302071b05060f1b01021b1b060f070501021608030609070915030e0a05100c0f030b0a05060c0a0602030114090a020a0206060405070e03030d0204090e070315050c 78
    0x705509500009610516440e100182c50789400d05190211320341c0742000d00703844200da00d0140601d50b036190070780310074040020801c2da850f50b84011400c05814681401c1500e58000f0410000c15120720003030015014141c07040300c840c4040240c11840c0c0c0500c030280240c0121003001204001c00c0510700410405000d480007601d00701c0a02050b1800e11907550050fa014000803041c000717a0700d08403800603040941e03842c081a03010305103241c145520400039200f006042d55078020b180410300901c0b840700c50541001c15600d10070745645441c40a80b0040e5040400152200002d41016001e4882c0f104e00b000003808284206007030000b1f1200703a9000400003142c0f4130a6954071800a641400111b020740295181e51310916030030018041103c0700a03000c0b15800f80180900c9d4500b90b800114503a20a804440c00724460702c0e0b424084c0d441071003407044960140000a24503408000f0398000f0000c03600c0329103003003040f072902c8450359071507400700e0000401c1d0800c9502e000d068081e43c2d0300480d80182c00f40609078 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 56589823 1250 56588573 56588591
    0x103081b06100e071d09070309120903140a08041202061b0102090103050f040b0601031d0307111516030c0309152f070303052208030c0c040209090105060d 68
    0x603280c1201151000440058200c00b44400e403620004943c00031002d007450a94507a81302e15031704a44240ca5000360044070164002503001d88240c03c5284203070f410819804a0902c2d0f8000100107440e54002650301d018404030500080320b00003801444990000c810505060500c0307050250050f484100b680e100c0000e0005c000301c0c090550701c0c1d48100c890a00010384c1d9400c11000903081d102d00601000480b1000420400894801424035030b105400b447c00160141c1c4402512105403c2410513442c6440081210410460900103070001d9100c01c483c0350003644c02c403803180403862180140141c40c200d05400c0307480c0060f0040c168011502d203e81000800580c40f540c1600700040c00c00801c0000500d02c00308000f00c1d2410010010165003030b0750001d8208001d80d507102d5500e4070103120080801c200040c041d490040703603940d83e40f4090700000c5200d07140b69441e41e1407584e03500130b0703d00c08026025114503c016403400f032088990316440584200001e070f283c42e04110740354012603c0d03550001c0d03c0300024 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 56591073 1250 56589823 56589877
    0xd0605100b0a090f050409080f070606031202150c0a02030714010b03030d0b040c1d01050c0a020a081c03020304240f0c03020a1d030c090403020f0a03120c0203030708010308 76
    0x6082403100c10380d1403a400f02c1c0b0b480004070b50025660b00c2207000b945811071010100b02280102c030303020084030f92801d50f00d01444c901140101100c1e030000d02512181008542844e42c08140100400c40030321011005880c1d0116004052003495941005a4020001c0c0300004100c10f0741c040d1790507072000001071400681c00c08a801c5602404032448016130311400b400c1c0d14600b900c2905000500c0d4900141000394141c0031800c11280800d01905114000c81c02e010152400c200482c6060344c0074003403030310722603175000129a60b18610850f05170b551240186038628510034400e881c07081c1d411840d142010b14040544850611800003900c40a50300e07100c00c3c1c40001040c0c083d0b6903101815960041ea154031041c1d00500c10301c01408524800c0807148900c02d503943d07000414205401c2c0841d0002040e03115898180e180248552240075075020b49240c1c0e50078541c004a9040740348540e64800e203ca0807610004a03101e1008840031408517890000500c00b050300d07103018050541940481114000d0b0503895 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 56592323 1250 56591073 56591077
    0x3012303150907090f0209010210020d021606051005150a0806150712080a0b0315150a0303091509060f0c05010e01060902130b1201030b090109021203030702010501080c0d0605100b 79
    0x800d5049510210f4204910f28aa20401d07000300c01c002c504504250f4003c00013500c0d000c61444000c445034002c90500c00100c1036504648602468035503440005482e40740c1000a00b00c222031003038681c640e0900005060818000000c10710103801903207442c0c109400302c25905050060406038100050389286c002c1c00c2d00b40b200510004c0e004101503960b465903c2c60051040174002c11480e4914102000c141080d00c0014150f045099480e01c0000705940b405101502c40f542c104034164405403013000041456008110b000c16504a1030014840400c1d44d002500c4640b40d510544002446840340c5144503480303180080c0341c59224400110740e01e80780e445c1d01429100180c12185040780d002440312001c044c1c400200c401030420740c02d40c50800b0711503a4605040201484060b285c07070700010015080c084213500801d04c0719801030010003403070b8055200b50740c2d0b5041107070300b01c001d5840d040001c01c60001c00908841900c2000b8000a080d07916a03076618003400000d40b1003804806951000320f148204180 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 56593573 1250 56592323 56592331
    0x3040309170c100f02120c190309060219021507020f0333091e070503070605040e090f0705010e0402090418020315060906010e120703030503010801110301230315 71
    0x80140303000000801141c244030001c00f00038886450b480d5020140c0128004d1001d500f9071107800d0b00c0300c121201d0035040c60454140e4591030b1400040100c00c164024014100340d809560031110400c4050304d01c0e00c164480c511002c0c1d0b01500c0104015000e03503ca10040410030301c06080e00800d480340401003403400f5414006078a042210001c401079840f580900041e014080000300b000900b0a4500e486d01d4280f1007806c06164242c0d9171072030100441c200642c50050902404075520641c3e50700000780700c0c0d0000d00415510301c4d003000101d50094000184000c801581c4005040e0540c90b080041d140d001c09c0380446a000b40d001d004a849542e41c2d07105051500c03505c1d6020300c0d241d20703003481014105440d00f0074080f403190300c40090149684401c100c00341d10040a09000c01c0100100000581d40d0720841d01480c194809c00d000030041540c400051412201008024011100c071500c5040480c0000d02800c501ca402e010000701121402c44690541504054140d03424840c542003140c5103c8400c031 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 56594823 1250 56593573 56593619
    0x40501030b090c03011104120c030c0306050a0b010c020f19031a06010201150806040b04020a091b110a030507110607080a0f09050103060b0706090312090c1401030216060203040309 79
    0x1400700310310b0440a210402c40120114020021000407414504080c0110b00a041d42c01d5515003901e02007050b09105a03000c2c5030030005440c861580e80c81d01d10043c1804a411031503103801d2540022003540100001c07580240d00920001e42c02c000003051000f503c003001c5001d022120411000000704080401c03c000100c800350100d4403e00d07040e000a400e540119a0305541000d522004004c44540418629081a4420f070b8101144d03c603400000d908040c9500301c0c0c44524a4840207810740b1031400884001c010780f50f11001a60f902042d04103803100d01440c40a40800d02c100882d00010b2000c288400072240024801401c01070315840710030709a0805803d180201e6254002c100265401c400140018882403805010341d606090f0342150f1805541002010f480e21100180105401030f0100c41500c00032401c05c21030b41c04141490742000c90a446001851190240c06540a5201c1d00880d54003603a044180b401c048010794441c402940024801e03800c00919000114502124a42402c0840710b070f0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 56596073 1250 56594823 56594843
    0x1207030c03020904060b0c1203010f090207030e10020105090f030c0709050c0d06150e030c06070303052715011509060c140303070504150c110d030e03060115090603060303170406090204050103 84
    0x21f0003a0a103800c1500035151074401081c0010000400004117440070740b250010301503203c051514040d59030002003001a640b045051444050999056100038483d115403c125940c58113081c40d0242c44c0e100b0f05a8030003041d00800018001002542c0185400c11002010980791040e20751681d4212840c5421840561901c051850700980d8480d020102c2e44100310003a0450001c000b00040082c41004002003c0c1038441001400f0000550700c2c84200c01e00c4128021884003100a00e981c440c0ea0a041102d0070b5085140046054205100c2c0c01e0861641520f90726840342c00c2c80400d64071300f40e4541086070001e410040403440108140051402000d00361142c81d10780c1d0401c0111100c024000d00403070100701021420b500400c10510004401c0b41060307038001006041414202c03003c1000c12600c1d501880741000004010000a0700009295129920520005e8680b00120250741c0c07144006000160103600503007541d40350314589900b282c40380800040d0361520382c3c040780540c1e8091f07000b680c00481c4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 56597323 1250 56596073 56596087
    0x4090b011503060e01090504150f0c1103040f030807140d03060302011403040f0201050d111204050d0810050603070509040510051005040e0a0203040201030902030f060a0b061207030c03020904060b 86
    0x1100a081c51035091509092101e903082c01a14200300c881441003051403511980428140700030210b81c4584940d52000500040d10208040c5014118440307107180044c00300580800c1464011064405441a14242000f02455519201a07542028500341c0b03c2440c18120243c0041c002c0044a03451441a1401f2885516500000d4024480318802200c880001c100300000120303a00201c90b0724a07424200542c0799603000b0400c10040c11003c41d4901c3e07071300001400010030000401c1942c0700e03d00c60b40464000c0421842c0071217000c4800e40b0301c004188010030741480285080c00c0610b9001d00031345455410701035200000f034240c942c25500c4800c1144010000d105a00300242d0a510304003090400300d1a091403d10b810034500c10003010901d80e10350110124045a100350051401e2540041c1203c00100c5603845c4103403114029103006003428a04150603000b410690103a40002c0f009201c6101c1c10782d41d940068015190710303241c001c1019130821403140d02d40d44a1140e14054240080d080f0b0301c0e006 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 56598573 1250 56597323 56597339
    0x304080a031401030303060f0f1401110111070b04060506040902030714010302070209010e0403110c01020709020c0a050a030909060501030507050703050702030705090901060905060405060d021909050f220201120b06070204090b01 100
    0x14941c0204055009080340ac0c4031031040103100c818590000c0c6408a08072000d4480c19004144040c1d444081c0c1c90300190b254144003000121301e004070700410042185440b038504200440b42c4000000b905604100f200b08000226000e050000c0441810007501d8400d00e80d000458040003608107510810707048090005041c0d01500301c0f2040740d64640100081d07018000080d40d950000d201d0b481101d6000159022070b050144001c948090307200003211180344072403038094a54940e600400b80e10794070300b80340018190700c240242070141e07510341c40745403a11265403011107150f400210183e81520034500001281c2c1c88464030180300e5602c07580002100e40c10440c1c828140c039006042288114103020501500c3c1c5d0703880c0c6214010b550304562905808260810020f4940c1980d8000d16101d80b81c81b0410000411400343c1c18402c445e060b526602c9200e080700c19402050b2001000f90004916440900d00b90215a1104164640040c00340d8200142c0e917002905a41c000c81044906c0e500c04001006060 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 56599823 1250 56598573 56598599
    0xc0a080406020c09010e1305100608070617010f0e090a020d03020c130605030c01030509120403030302090f01230c070801020d020a11070e070f090b070b060f060f0304080a03140103030306 82
    0x10f4030890310581c103940340c034100c9840b185014051049030303031300040b81034200304c401c0000c032500c01c090410a229150750351a0990700d4001070b00c2403c01007621501101c4503449130b15485416110001e0700d0b03940b000d00f401d0b0342038800c090081c00203400348a1084080c2c00b6076103d00c0d001e54807034403c8d8003d00c041d80940301803041c0180316505900d1014207100c0103001d15500030510224040003031900054940e50b64a551345060500039000a40d004001004000d01da8140c0041c19002011340e140703000151a6401190007003010f9024452400310100c100602e2503494004110015030302045400090b1202081da08a80c000a088080654001208081560018801420095500060840b80d0f00c0d080c0104604203000303118804001c50704161495050040c100b442c094400c0d40003058651503946070402c65514259041d078494410200040520b2800108032400d042e020422039045444a903074480040d00008004400d040e00c0e4258030301c0c082103a00c0003600840c001d81c0c011400901d401d250400203 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 56601073 1250 56599823 56599843
    0x5060f10080c010503040f020303040510020c0a140303070318080d03090605070206070804030503040f1e140102160f0203031204080301172d0c03060106110c030a0209060904080c0a08040602 83
    0x350803142c95105030303a0f00720703090780c2d41b06030481c00c40505560305200180c04c40c070403a00041d81c009214404242e40d56400120307200c1010f002d8421900315601c54104d40401303480007002a07803640c020403154001078030504051311100c0303a12070080b08440e02c4500742402c08000d49102d500180e030f20b00d8118203000c2c9500505410881600260080b4180090b000f000d50358018405000e10000001203010080702d00d160091282d08032240380e8440d44a0750020614a04902c800d540408284000905140041c421503134000c8a5421056401500759943c0200c122945010f9074540003d0140640c0c50342c0035440313144120710910003240d8075814800c0c4d0240e802c900319114076450b4400c08112a4407100d2040100d01c4885100ba01840301d1103010300da5180a000e500c0740c0b9050f00654000256494002c40f90002c000b07400c00a84026075218018159508402c150180d80f041400010420900380100f145810a0150004510b0032a600755483d20300b0b1075404003160034007170000c1c0803c0350a81c184400564 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 56602323 1250 56601073 56601089
    0x30b0315070203040e0415020f0c01150806011806080d020f0d050a080a0902040b030f01050601091e090e0a080c03030a0c0e090604020307052206090b070c06030908040305060f10 78
    0x26050000c03000350341307010b5406442142c031212400308007400f9004d204000130603407820003950380d40c140900e102c00395041000904410742c20700186510800d508400c3e00162401c42e002020940e00e08402440d08914415070301c0300040d0b9407500415440c200344140b0318111820b130000d1440041c400c0d034240c0303000c180c503549608000c020710200103030302d501c0714010350400c403209e00104490a680c00020b004042d80f4102035414403c0e01b550901281040d0030091042c1c400742ca46141482d035402207901c03580d025940030707603039200c100d1414051041617038040c0411005060407a61821425aa003008603841048500344660000c020001500d18502569218040074030300700318580c000b42c01103003140d00007030a1a07200365000301c0003c800e148514191000e8010300c0102d0341841c2c01007048d14000c540d15020303030000901411070104001190004682005d5449143c505000d490520102c00503c140c400440342070204000000103d1803c1001601407043c904104420341455450040641c00781c0d405521 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 56603573 1250 56602323 56602363
    0x70303080f070e010e01050f072319120905060a0503040c0b0403050c04050c0d110405090703110703030b0d02040504030f09081603020105090409140a0506091603080912060106030b03 80
    0x2d0030350300640c0241030b0042801d041110348446001a035050051034026203110101140f80c005114000070f00080302c100300361361800302c2c05904034110b4580030b8110a160911741c07044110000150b45240c3d00c0c015000c41d241c16000301c1e449100056035907220303a140380001800401800f040c460300c030401000512100d07519070314292560b55074503140c10792006024807599403240011006a600b201b2222140c5948104110325010740c0c100361107640150190500503c0c9070800100014040e100d454100e4030100c58560030003440d5075049024200302500250044010384c00070b001a2928001c02e800b6501c2034485c22059800b0200040241045502140e0194402418440517039072030508442600c0d028039005544407041008500517201e00c00d801070418111806100358020041070b40341d44240b1960030750f034264030391404140e40c81d44c0303910099003083c002c0181000060000e2000304051100500481c2c004090080c2c03090030b00ea4240c0c00100401e4072404546510b14003071005281050880800f00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 56604823 1250 56603573 56603581
    0x606050405040f030c05010b030111070b0603060709030f0609020603040c030308070806060f0c010603020d0c030b010b0408060a050901091203051b030c03151206040c030c080d170a1d070303080f 85
    0x940920f007646001d8103000403004c0840a000e001c0d0440c80c8900b601030024012941c102c03018007000c0c0e1000006072040c49141001c02c00c14a0081051381c020381f070641c1c5d941c0e42241151501d0143c3e0313100c403408840325503035015500010385407074010754401c900905a50010310315500780540390f00c00080442c410080c004003048001d55490040d18008003a40c1c1d1015107a02c000500d0070300400140c1c0010b540404a0000c8800b00b115507003c00046d02d109281c0c102030703640d840124107154083ca0050160942000300084e045844503844260f12924950020510b0096a02d41d00d10345101e01d0609000244c580040152102d1001410003542040200c0c492961900700c00103030113400060000d1f4204804184e20142580d02d500202c40c290551405452480c02c0515000080080e184021190b4800c42c84001030050808103010f88608400e441d0044002d4005c98244c00d0104018107114203150781d00b00344a804401d4582c540d041c500c080d40108105811414080c10704a801041c070020022400100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 56606073 1250 56604823 56604833
    0x10e0f13060c0c0506010e250203070303020307030603081902060718050d020a0b0414040b0a050105070f02121204051201020415050f040e07120c050a1b05070909050a060605040504 79
    0x421240750030107000a0903060540d0202c801c00340000380074105100380030000c00d06101c001201da001d01c00c1714054120083d01e488182c9042c5804910000160300144440c50100e8060740085030306c0340c401d00e4001841c90300c0340d07188079058126003c1c1100d440c846070501c500d0705804005170b036002407a500b824240c20a6008c0d441c000141103001d1140964540c80314002152600791102020300408485940c6481c0c5404a03420540310300300c0c842c1d00c19400e00d01d9a500e103042440c3d4490079610182d4034145460010380f2a45030000f440d090403600030030449a250f1034990184003e0b1100c00c0440c11642c1c1c0c40746842c0801c00d4022206000008a910410040101802d020846100031003103042542d101c040e120300c0941c0d64000d0354013540c224164803042114541c2d0080c062645a42c6009080040c84450903040b030315130160203100004184c0c0607801e9508518818128000d10b031241088510040d180c1c040c3d0810786811040842e00303039000d010804200036407409040003511042d941003150307140c51344038 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 56607323 1250 56606073 56606101
    0x1031406061b010b0315041b030b0103030503190e0d08100b070f050c04060f05120a0b060d05030405030109080909130c0e060303090d0b240303090103020a02070905040803010e0f 78
    0x42e03031048000503041107980d240c00e410069501c60010107035842c00e02410341c0141d002600f10390031079808808503140541d0607109210705081c0c6e44c10524401c507581c03c6503003d4a00703500140c40c858034006548809007013130505000382c1070302c5d807456005400c00b00c4803810007500b0b9100c0586404a8000200c07014820841120103039020150060400980c6861a042440c1000713404400da941050a002000c00c0c4641a400041c040710001e9852800d10070020a0440c0c582c2804040108500000404280c0d6032800c81c0e42a00c1c3c0301e0203134003030740d2034240c0d204c3c0003c3c00c441c00f810003144c2e00c1e003001c1080196864803d045a0340a41c0d0312043c20b003011030039a00c800303000130640135824032094000c000c5402e07a1810000d50f01207000203800c3c42990000760400c045002021500c003240004485180c102c444214001300c26200c00180081d41000c220500642c065042001c46134210311071040c0000e00d0200781c5c083c00d4002ea01a809140d540d504146a500280400038081d0030241080410b0024051072184 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 56608573 1250 56607323 56607337
    0x9051e07091413080307090f0905010509010815160e03010203010801060e06010c0b0a0f0204080d02060405010b0d020a050f060c03031f1d15040e1e0d0e01050a1103091309020103140606 81
    0x28030300ea5680c0d1b0710601901d1514007600052260261403102040c83c2c0002d030300245c161402202e4a01c80f80e0b07683d4190550b240503490a0080c0c0a02441c0420100040c000f00d00f03016145c141020f400c507030401700119089800907444814241c0d1910010804100120100d68000e07500b841c0c1080e271840f45445039610300030041c0c1340180703007940c07442c3e403500030744055055401600005090301d07040080000000d68070030042e682035400d1b510381041807600f0b02e450310b80c9032000b40d805003032038903024900001c1200c07024400c0140c45c7c00c5101000714801c0e41009100440c89a1201d01c0300301503105035003420444c40d913941d40101d0180115881c459102c00e488240c4c3c15401181c00f41c45034400705208021801502580c7d80b14402031044650480f84010038601c201110517520084900b802e45509007210113000520301c05000c510304021a04c80c55204a001c2c1420311038804c210f0385400300440104403594150f41c9084c0c18030b030303440c984e11085607414040e94190780b03014005400756080c100002a07081c07107600 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 56609823 1250 56608573 56608583
    0x120f030403140a06020a020f0d090f0e04080c0f210f0306100306180b120703020906090403022404050d0201140a090f060504060204051f050a0309051e07091413 70
    0x48070b50703070794101000100800b6a101c0d0302952900c1102d6000b0f0b6449880f100e02d91484c1c02440c03840941c55206103950b10481c0c1100281c044034626102c20500c5620015209503000c0c2d404102c0400148010002c201c2030070f550000428024080c003003000c450391010014000a400f003000100041d6a100003a40c1d08050111480c0440c0c60b054481903000b4802c1c0c1d40440404120a00919200281c9900c1008291000c1d0790414801c60004801da0302c0d500c01c1e010081d071204210020034a00d0514960403036226200e40103d0300f0401c2d542c00e000041270300500341c3d9840b07644000c081204120b028031010348d03035914900090000899404c1008000b00d8001e0031080850703954006401440304c51118141159000001080603090030f003000e4000c1d40c424081d040c0a011211078081014002000b42f480610069030381c1030900b98244003c40181ca0700803020360300c0380f01c1d010b160102c031b460f035490340000a14076100a0401e1480d0200010036112045507a8a07070a40b003104004400e208400e5808201c0c0d030107 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 56611073 1250 56609823 56609843
    0x80405010f050910050a020106051507030c03090906080307060b0105030708060f01051e03010305070f030c05060906091f020f0a0c03060507110703030c05060c040302130506060d0c020c120f030403 86
    0x807084400e0700039210f00380d910403074550201a40c2c0381c0050044c605002c80b5802030007101d8544040c44802da25481040d040101d040003144003080c407448960346018070078a00155496602c03200c040a84645070014882e6800c0000d4034000c101c2c0c1c81c40754504105007030034118114035003000040d0010000411080c0225194065161142c0c451403c9588650340d1140d85c007040b100d002018445078009010844e01c904c07032240701045595140c0d501c074048980c05501040420700309802d10020390401c2c00e846822a50a10007a0125515600004900501548414425030111400924014090010080c29009182c540c00401c08685207481a01c1d0880f03004600342e2102082207881c00214078a0702e141d40219940030040560111522070381c24050030450b400c0e80c0381c502101105208522000f540032041d00c1c80300c00d50007580e0b08080d600c04002001181443c1c0b41c5185a01a20085080030300140c2200c0b0b26001c0301c6c5400030300f401d00013102c04010819410303205c509603075070303c00d030301028040e0340b20 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 56612323 1250 56611073 56611097
    0x3090302030f040e010806090718020c100501090c12050105060708130503060705070b09070b07021908060c13171905010902130c080a0c050a050c0a0209040c03030f02010908040501 79
    0x81049502c22040444295682c0390b0b41e03543d9022200c0c3c00c0c01949680d014440c0401e43c0b100c0006280d43c02d880c0318651080912032001d90f036600940c000c00c00003145009074020300154516500c00d0368001c0c98054404200c03960039034001480144006c26850803645440010710041c0c840606448040f60701c00c0c001940e0340900001c05840c010158083e9615115100400130500e9000002c1c2549902c1554908031a407907151106486461171b0140450710442400030030701528140c905a11401c01c40b4004050705502d4a51341820800d017142c0903680408005010b624240340030051000a1180d8545660752081111442e42c803516031941400c1030a520501c0c0c070b001d0003002e5001c100c1079540103140500c9100040344903806001c1d03c5000f00c011980210004400d04010701800761800801e960b47d928020343c42405850303030b400000108800d84681548000182c5511824602031030149500d40402451450002e00c01100640c01c5011039040058110000381d400c001e4406480302400d1043d20128 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 56613573 1250 56612323 56612327
    0x2160303090b130e07110d02030a0816110706020705030c011701060c15020a0c020f09060d0b0c16060b04200f0913020a030c02060c0c100b010504080a0308190e0c01030903 75
    0xb241350000103009221006115016421900200d21202035509580c0200300388403013680c42e13004000c40b51001c282440000740c940141c2c1e0208115001050400441c56914601043c0c07902070742d07402a00140c1d12800052055180801111180c02000d107444e00e5250000e210079061904188980414402e640c48402c00300304031481c0d240700b00b00d2074000440d120f8403800c40003000004910b070700b03078004c1400c09900c3e030a42c10304444151152401414031604062250341e12001c50400502148034040244401d42908920703860540000b40508804603050710500200001c032070211111422842c0c0c01c0761440d510b5012441614a0720035170514464039001c414000c1030804134108a500d100038400165012403642551001003901c903180c0c00c4035a039544000c02c0043e1032241c4a0000c0e52070744034845900a103550782c2c022400e41d00301032402c103003810781d505012072070705100c035000300d001c589500108282001c010059140c00f844c0740000344540c0311120303100794070380c0c03222080c0c1c1d41010f4440000c0e006140c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 56614823 1250 56613573 56613607
    0x20610061b0c030f050a0b0117060402010c0302010b031f0606020106080d12020f030103060f0b0109120204050a14040308040b0903071e111507110405090601061d090f0702160303090b 80
    0x764014035050107026080c80c06030f865110010382218947c0e80b603800032501c406a10782a08584003c034004182c0b54480c0c0d001900c220035810003c904540d00d42250141d01d4905104a046d1a03408070b5880d28508030281a1a0070f0f650301d90004003c581c5045010411882c0c002106161414541000424005420701d00c0011780728240d121500b2900000001007080300b19400119500314404082103065601170044540c04050302c2003408a05c1c07100018405842d05611180c1c01c000071010000b40210718100901d003800044500350b000c550342100f04030a202e00390f0315903035101d1301890166180c2100c60391007030980520350162665800d0f40303007424010001540014036414400030f08080d050039054a561040b40c2c0000022168690b44c20140c000c0f038142405524046c8482c900038000c0c2e44e003040c1046480d9240950410000002518040d1a5458003040107010304c801015040d018600b0403400b038946103045c4e403a08030034409070004101007540004104155400e441c05c00d40d4540d20401150740c0c90f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 56616073 1250 56614823 56614829
    0x1d16080c0d090512072f13060e1305060f13031202130f150903020603060d051507020102120603060403020d08070507080f03010f0e040803040201030504030c05100b01020610061b0c 79
    0x251180d48440c0c4d19021a160180c400c05100d6041140ea0011a0034022490113880151520009200159850500d056107981490b03040140c0b0000c1c1c80d81d582c42c62401410000e03030314202e01305400b026032002c1c0081440000e5000e030142e20441580e040c0044030520340032003424003604200e46400300b04a0704c05540c0440e40501f011180050392951584103032480820740f880f45c00050304940703500d0b000c80c60003003e0345822282c000380031b281545d403403e09001e40082c000c2004c48a902828005485280010783c18a00804644d400180c8a140050340e01101d0b20f4080c00c0c0320b08c298402c01c10400000c1d40000c001c00117034042e00e010b0030141c49440d0140d8050203001b0000b4040e1401141d20810f00ba0300c40c010714102c60074080407400c03090340d40102403030030360080c0e801410a50013000010090b5009410036a00f09100f407500c0d0301d09002d1501d030103051188848080100c0c0791a2028400550390400141c1c2d007142c0c00b8810708804902d0448050304514925101003200d01e0000030700300034040d18102d22801 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 56617323 1250 56616073 56616083
    0x200f0711040c210606020601170a08070b01030204050705070506041b0b04062d09090e0c0901080c0a210f14060c0309070807030f03081503071d16080c0d09 68
    0x2c41c000754000d0440911101a0320f030308820300d810384a1019160240d642280c0c503a402825041c0d08028801403c104c2918000400e8424481e461002a02c084010040305025000606aa5056104010a43d14054154010404284410380201c1c0c8042449604039500010302801e0740100008800550803940c0605404040800d0000c0c1c940d80100c10382021204074241210502c11800c4000700401c001403901c0002091a40c1c14040c0c64883c0c2d0040381c50710070020884d03881c4185540012100e2509801c00d070f0164100c544422903606151038004003034401c5034081070102445184503040070301841c1024100d6903486040b8000e22030900041ca0019284405a49507440c10f908028941d034001d8a2144031072080303020015400d2004584035084d02c0d0721074040300c00c002c43c589041350200da0142c43e4481010002080800c60380c0d0070001c0500522902001c0c00c0a000e4904000708000b10090004043c1c500711281e40d003030b0030b0380071070007940c018113240c00d140d00c40e103414803004000c200c086e40042c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 56618573 1250 56617323 56617331
    0xc060e0d0204111206100906050c0c1309030e01020d0e040b0117040303020301030308010b0309030d050a0e0106060306060f1e0807110f06010e060d032001150315200f071104 76
    0x648421032070010005813210321440c20340380d103070341040c4100d2214500c1000d00051100ea824401544150010004080030800322206018404c0000d4011112100141c03002a40c40b1030b4002015041445041c180750240094101254900f0002d0034030a514101984900d580b1054042e5980c000c0340b201c5503803c05102143c0a61610740b401400030341c0213000507404604850000102d034100c940803240f084042d10003540c18505100300f064081d1002a081101180d1104984810f140b000d1003660001d000c0c907030740031036071900c0d041d0b001d800c0841480011342001034052005c58112a0405625814442c0d032030810042d0761064400c488803110f00d04d105007035009500516903840350000381141665440034203040184c540340d041151031001000001c01288226056107080c020031034001128500c810004545881c1903401039041260680040b90842108030249905014510440c0c0524080802d59200e04e25280c60400050043e14641e28a40000251720010014141c0f1000031180700900288 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 56619823 1250 56618573 56618591
    0x806161115010314060105090714070f0206130609060306080c0d050c18070909021204120203090a080312010b0c0604170706020a0302070b0906070e010e0d1208150402070c060e0d0204 80
    0x204c0c0745490864080098402c100c004205440d1866600d4050355458580a00201c9001583c0c00c041e00030301c60981c3da42100f0140800540c0710040281813400510207e8003003d030824074090252456500240101443c0c040180f088900000300c200c89403030104c40c1c03040c5200340b0341307401d600c0d210301c0403c02d0782c00c40000340401c6100d000180095000311159154800542d49a031a04004c0303005009182440342c2032100480c0c0403c0c0b140a5542c0c00d13103454410b403840c02e2060004203400d040039a1203030104d9400000c144007042c501315001c03070151181035425460040c078203c046990b000d0103440905003014110b1a0182e450b075210403034411a602040c01c0d5151003014401038001d400c611012f80303c07002c0340f1001901c50407005c07400d64807892040d150780d16001c0e00c6800440b42d41c200c01c5509034000900c401c8040c0440e440080c2e0b103a205d01f103907454a0b82031410950310780348202d01000c103d0240740180f0401c40080c1d81e6807a0041951050300d000102c108000c0d00084c0c81605801003c0d4010b480c146404e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 56621073 1250 56619823 56619833
    0x603080408010605090c040902090a05092a0708040308130510030b030d11100f02070f050c03071a0306040902010e120c04110c0c0d030504080d120608061611150103 72
    0x340007201d1040e802001016075420a10407090821141c01507410340400082c003400c0c000e40c2c0540325101001d803040c2034258a0f080860030038182601c1e481c40c0b00c01c10b030365100e00445040b0740041e8005401058542050803941d900000f50145000003411071001240f0324078141c007001d110800400c0300030a01307501e0203418070014000303003401810603000b03000c2c084c031122545004251500e034800055004100501d58100d07204000c2c4640303400e01213a103400b008210041109030074503d280d140950068040c1401207401c140c50010194002442071402a11001c040c8004005603980702c5400d68003c50840820720048a1580c020000554031841507814880c5142d00020b0f410008202503404101e11800c00002850901034140c2089184d803084a00c10b400e424614030810210b40700f03080c000d041070b413a015068204000d90130a900011583c00f880304500c3d006003e80300c000d01c03903040980010709010480c5035018401e03462030003d01010044850300610100210280d06c900b9040b00300e0341d03503104c0c500 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 56622323 1250 56621073 56621077
    0x40506180a060e0a020c0c060d020d02070507081c05030a0504031103030f01050a050102030f030103080d091e06050708091908210402040c020601080601090f11070b25171009060308 79
    0x42c400c056110400083c000343c44c1c5100b15401052440020301a0301081c0c020400240d00410740380d40710070740038001626140146d0002e40642c4d07215070041e210250410208030701c0c0070690f41820900060b4031518084a80d003240890b50045080d030004203d50703a541c03c040e950361101c200c40c0d0182c0e01c40042004440c031115000d281c181c4008a69402c03956560300012a56806030389101c40c95150204010400640c440004104000e1038800101300720b21180c65011440f8140c10100081c3e000c0c101088040111520480d90b204400b401c0c01c1c41c907418880a444c0d0b0390210140d00c030541c41c0c12800740b4000e002c07500050340c200400c00f0071030601c00d1180342c60f0103c0303000c8207841c204d005e1801d0640648c1c00c02c0c0081041c0e41624400c0008100503803800c0301c41c038003420901c0111448607583d886d010721f001c0306c2c0900515415004120100141c1030103142180b421300300b0204169000d400203140702c6201d41c4860812900b0910414003003281d180c540e442d108141559014150545c0382240c000704000c05800 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 56623573 1250 56622323 56622329
    0x3100b03040615080c062d04120303060f0e01051e0603090705031e19060f050c0703180302130b0609041802190e06061803120310080102040311040506180a06 69
    0x82900b00f51035540d01200c0d5160011040183d00030750900c912800c0e0003645207134582e04910b01d191401c0d0034420034070014041d80560404801243c003030604600f0f060b014054000101100c2e81c0c40d2111514203031a8a00e40031040c0240c03440380340c0d42c02207600020b01850480c83c0305140200901d60700e04000d4040c13992400603100d0071703001e4000d00d02d591407018108105240450004c0b80a0094100c0f000266070400342000402c440c2c00d03136200b8136044140c01c0e61050611558000401503a070b40d865050140ca8500c401c4010106035200c11800d00040e22140c2806005116092010900341c0a840000f04280901c0c0000b030b4000d440c000140041c0d410380604071011900170f9460b07001400d1000044040e10740c0d5030140850604807100810002e0030200c0080416000c1000307840701d0b6401c8200082e00309400f80c03202c814001004400d012a403582c2c62050401481040000c510746865507031200060001003400b00e200d19a6100094016119803c0440e0005220000e603003051130f0080b824401801240 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 56624823 1250 56623573 56623601
    0xc02040f0b030712020603161b0605060109050d050703080315130902040c0801030b01031e060203090a0201110304051503220f030f0806060702130f09110906010801050d0803100b030406 81
    0x1010014a5507140c007401325601d034002d08800d1841d0b881c50000040b142d087d182c0724082140700c2c1da104200081002e0300c441d4075403082501060506001000600e03242658000700c3c0300741c1341c07404e94000040c40041c000084950010010307443c1da854121031410060fa22105c15040010690556600c240c19440150824822102003084d590a06001c076840d00c1c09000c004c010107031b01001440480d0344c090322840c042103114080300d009000740d91140c00341c4c0c02c151000349003640070840440c02c5607085a9100302d8a1340e0744005608080c031740f00000342d50128440d4021607060002020809845007200342c600d00c0800c0c0b518540c100f2210f86408071086d04401000c1d030004804900904200d48600c0416016440062803e8141000e5400b0049508411500803554607924a500d94100e962405036040700307400341c1541d14400c2e00420034030440301d4008103240e040200900044c0901e0b6240540c020101c0d0700b1000796520fa43c0d80304606070351207045d034100740000394000c02003200700441500a0028100a0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 56626073 1250 56624823 56624833
    0x140910080405060f0105031509030d0903030518030c0322030204021303170f0a1b0507060908100b1c05010603020411190309020f060a03110a0c0302060708040c030f030c02040f0b03 79
    0x13490054400c00c00071b00900d0340c0740e00b01d00380e081d20030880c5e9030f021500120b03c0f006507403078404001050750880d04420021008607456004005000c2e880c4040d0b40f04001d40f000285113440f030040b00c1d5a440c1d200b40302c090400500b02c416030941003521029000c0c013959001e00215603415070601d12035a054658441103c942c42040c0089098088200542c0c0041c96600e02c2e5a04115445a0584802c1c0c040d158800c05448410a400044ac0d0104034450080c0503544680c41064100340100b0701b410104c0980402d40ca003054800d602d50b48801060321864a1f07500c0c030341103005805107407a5000d8070007540b019502c907050004041840351604010081560840440c0c50403800c03400003542030f201c0d103007000b0750f000500d051030700743c1800e040008106483d1103107400504600e90844900242d0080714194000418074040c8804041d0100061a0007070322030f0034403110504d4584c2d01c040000185001c01884103981d225244209802680d0600e80154020001c0c032800001404a40082c1ba141508a202c2c1c132034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 56627323 1250 56626073 56626081
    0x71d030114190b03060609180a03050a020f070503070e0402031005010b09040c0c03120209040209060c010504020307081c1202090306090c03070b04031502030c1209061e070f14091008040506 83
    0x202d0710490101c0980680540b421b5176a0108009a103403004149143c503411203032114509800034080c0f151175600c0381c0c8945840b4000704500030b24119051440c019940d0101d442440720359400a03441c41120006001081c060347d4510110b8140101c4040080e442800c04001080500600700942030001c0c007a035040107900d86842e400c07030f5000c00d0700c3e1000e4046080903644161240c6150010034095030050f00140c07401c200c03100450b0300356100031400d0000781d6441c020b000451406020384402002100002c0c2480701820740784110310034030010320030b05000ca80120343e0443d507541d4040c1d420b140340040030f40b00740e440c01600550300d841110380441d02c280515440070401a805400b0b42d020360740c103d1101c2c9151003030307501c01500952002d0990700e41c42a0034469050200d502080b0944922010700c044c00715800c04080c01103929582010407078100c05080d04200140d42d0002d8003442004041c50007000f0004c01201d40b03a00303072003890389464100d11042030030094603800000a43c0210f10900845400d681c2e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 56628573 1250 56627323 56627371
    0x206011a030f0a0b01031b0504051c020105030c0c0118050f0601170316020303040305062401091802031308030109141b0a230310080d030b09071d030114 67
    0x70049403a440d10201d002c001c100d4007007681d0f04c0000b581d04107040c0064512001c1014510840c00c100d030000002e03000003424400741c10419001c101600d00ca12850158041560010302035000c000c18900503c2ca0115403039410304401d420590302040e440044044940042c20003903200c0540200003511031003400b0001a0f00341c00c181d51038003802d00200c003850500982d0301c0381c8064600c25410036a4903110a000100104000b80016401400d1040f01d8000000451428011b4808890310302c074180010a0010460003807541c00305654000e1104c00107035a50341d071500c00140a442c1f84d2003c0e00882003c000800c40c240d503944502044007001c82075401075560380c40c81610a4200080360304404200707000c031480c05d80c091000310040200502008500141d50011401d0300d030405c48840c1880f1203820001c02420a080c40707020825155490180916403040c000b141400c6000b4280008100030019019001d07491001d58642d4040010f00911003824024550208034500380c0e0002244481d0144d00b1003000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 56629823 1250 56628573 56628577
    0x1030c03060e07141011060c1e09010c0303050604020c0f060a18051c050c0a0804060906031404150b090a051618090c1214010609050d050a080c0f0d0206011a 69
    0x18010070704c1030701c05144241481071105040850070203108202c0703560b20106000b400071500c501b44442c480c9444102c1c0503100c1c4c20280d50f00300a204102003c2010f4142d503684083e40c0700080e03406013004100c5807142408034000380b0507420b03140340350300801548114203980454072078015103000e070742071044000d010240c84800620a000602d560f0002002d020203050f80d02c031032810515682030240c140b0055a4959051213421141140d8640317001030240503940d004100a4040d20191408001c07540450119004a40001d04041c0c400301081c0c408030059019a04104a17070080503248505a0410a20f000040c100039580e2003410301070000c6590140c1d11400781c0a2050b4400505991501c0c6815145070041c1180360b5840104032039444848007080e20340c06020103100707803040c100d2099032504200070100302e900d80000d40700d5a58001c032100403c0c4006030001160b40c011210542d10840703205103900d8803508040e000903d001e00911000500d80105d541d604030b80b22a04d006200c1040044c22071154 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 56631073 1250 56629823 56629829
    0xa020f1503061c0b01080303040210140304030c0503130f05130908030408070f02060304141b0a0504050c1b06040302010c020607090e0702120c030c1204030f12030f0501030c03060e07 80
    0x8120900000e001c500e41005407900304049501c0f8592114016181d05034a50f81c00d03080482a03504c00410b010450030700c01380e000110102d618100c10116411919481c50f8400a0b00140030081c0051080050000520071202441c040c08181c2030525501e13107110505d0102841224411400d01c80f0768042d00b00c85000d8040a01e500030100c0b407a42d0b459a40301c007602e4022a0702580c010181c80e40102c0180c8400009600035801103034031070381015028001c2440d2420295280c0540c1c10602241003094480088400a071801224046001d03610b0303060102c40c030300803220500568a501c041e405110b0f400401c02030b00403030003a40240180f2084400c00e0384c0c1c9032000d4512000103900e800e01040070980d205216600300c0100c4c4191980f5030901f500e050059000300c00803900b150400200780364100303010081116a1400141190b09007440d64071100e10341076031250301034400c5002440100c1118802da22220840b42050707010400d65850b401c01036403844990000301e0380d4601e071a41d03441d18010700050903812 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 56632323 1250 56631073 56631109
    0x816030302100c0f08040c09060308030f10050307150201020c0105070f081b0405060705030d090c1401140d02090d0606030302010c03050a0504020a05120309090406090314040e010504020a140a020a020f 88
    0x21008281300321a00d01d001081030350203090789400820344031b009014640046004002c0203031281403651428102c842c01a0099042801c242c900300003030f84001c1103020440d9800200203070354042c240400c0c0e0282c465501242c00a529140400810540150704040c901180d41c0d0b4103070080e03031034a010f0281c082c214014090744050500040140b0300d404801040d1691260040c0d1b81072000700e0072400c5c00d4450360142200d54040401c010b10290f03c2c0380300000d1425109280c1080200809004000c0911030655850758498001410f0701094039005003044100d64003840400800340d4a0800900810191070400300003420b10003c590b40d0328140c000d0500583e00208804e410528180c00c0042d41c0700070000a40060006100314207042d81e072002e4a501c21030003140003140514203031800902554102c01e094100314824042800103030114290305042d03039026100103030f50b801d1390b460030740e00084400030000d017900001503041501030780840c440c581136100380c1d94a10030300690000c00c145040300c41c0100716 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 56633573 1250 56632323 56632337
    0x9051303031413060b0a0306092d030806041d0d02030c150103020f0d05120f03100803070f0b04031e0f0809010c1407080903030c24040b010302090a060816030302100c 73
    0xb0032a50340c020420351100030b2921b810165643e4988040d03400c100016038000042c1c07020030003622030a040800684013958102e03244c41ca95030f54080d0224001400c11401107968060009442000c84054100044200100e071002584a0802541c1ba80700741c0c40030b40c2c58052540c6624440c410707000e01c3d60590b54014903490120016005022950043e2841600c541c89544140380503118075100070184100c040e801160b580c9003c44407249003000560044500743d01c20007080000c170300100b11500c2081e521415200c0b10ba1030700d0078211840f8a251820140c400c141c402002c2c1030942040d207014036070b03c5640305c030281a500c0410071400c1340d600c5045000401e6022540d03d00c0c1102034070051050521803401c031814400342d540403034034540156031750242c10340c800024543c07046441d8141a000d0301d42100d1014441ca482d0361456110f80040c40000e000390800c001041d070306241da80146001e484610f007101c010030440c4207a2604600203200c01e8015001d01d0564110300000d60260700c1c0d5000380341c0c40b487e03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 56634823 1250 56633573 56633611
    0x10806070e0a0605120a110c010207050715050405060315090a05010e07210b0103060306020a0809060c07050c0108091e0d0905090f130201050d110403031d13020a09090513030314 78
    0x1740010700140ba001d40c20350343d404160000140707600900f90f0030342400c00060315080b075440c000f0320300440d607000156525402c040d003000d8560721500304d40c10b550007500c3d0325032603448060030150886c882014659000b10000c0130003a0428040d8001812035811001700da80700d0300e8103182901c207070150020108460103040540d011451583e08086801c03841850000303081c0750b40380ca54504a8000c00c54040006003040d050005940301007142c150800480010980341500e10f9079440c0e03a6180100c001814000111300180c2c010505010803204864061200440201c106010f075840d81c81e98442040812405500802c0f01d003469a003c030301c100004c0120300345279125012040048102d140d030032070400600f0040000540100e01481040718107980100340c49504624028060301c200c210700010211142489a03006d55440002d00c8112146110059503186880b034116000b04c01c40d0441010749003890180880c50101900314080c140c001e9604124a4642071040c0c88550810b03500000341001e140302c1c003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 56636073 1250 56634823 56634847
    0x60409050c09070c0f1b08120d0c031e0501050109140a05040902060702030304080106060305060f0906040c11030403050715020303040507031b0312030c030c0e100507020a0509010806070e0a0605 85
    0x8650001498100340902030b10780d5440705103801100e84220707605046801421b0300700100c581c0c107602400c5590094101c040050340c1214079800b070a8040d0545544820209039001d000c0e512030860050b0320410b00305c03010f030440541c03000390000f07204240c005103032100009041c42e950441401e04450050501c40c6d25032400d81080064110701c10140c0e4006005c008240050760100010401400320300004900d05142440103011a040100390b03501804002545140325070b40c40806542c0014111030006090307002c1c5008490141020903409401c0c40001030200600c480041e00008031160303a1440b03000212081c0c005c0340c907400300f070750028103d0740004401d0001980f045050103e20324403000e81d070440396407038640380d507000030a03030040d00482d030b4800003000703400d515000e85a2030010710b003020030440b413219001c124208810006481004804515a0219950501918001e1100a0102c151542c40b60030250320303410251606130104521541800140c2480c2c030001e000c40b2180d898980c1014000c600c8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 56637323 1250 56636073 56636089
    0x31f150e0f06160c1214010b060403030f03020d06090216060f0905031b030906040e01080f0a0302030417240609090a05030d0209011205090706090f05030a030f05041814060409050c 79
    0x1044501c00e141c010080307002c3c00110091103159015125806e64a4810710413107003105d0125920901030b642c1000300340082a0000f4202014416030700d80140d5404000200c54000c003100c0c0c2002042e84d00000321480f1128079000382c02d102d2402140100058041c034000c0804460741d000d80100150018001e604042c3d030b5200e040044a403a220542e03241520a030005045039220350449044403000c0340061281403003c1100001c040703d264018102b0750700c1c2d618080d5890145d032052040c180310b0101d080341880c4041c41807001d6203d40c404c10664061020343d88a503141c01c11518180140c0c00303200090488140040e12400d82c94001000d585001010400d08020f58001e0510300c2c14081c2d48488805620158070440303110b10355500c003400e003d07410400d0081080700d55070711000e00d00d4a20003042c8400d030f0b00415840a0158507081c280743c0403800b280165041d000390350042000c0d01c0c440c55840301900607500140128490950003a409694040802044900c07060340a00545d200c00510581d030308040207 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 56638573 1250 56637323 56637367
    0x4090b010318030513030605010801050103060f0902011d0109090f0b011b0b041104110705060f0606040303020c060705150c0a1205070f1d040e010e0601061103030408031f150e0f06 79
    0xc80b9174802a141d440d13000a82d10203902182281c4c1d51200101706102d120b1090b0000312106c001c05024448a47d00000d0040780e503c2106601c2d402c80e400bc8082a82c00348007840001c2c604540184044400f10f1240402869000ca8260208410811502804401d10407a580c4c8960094484403180c45a4071105090804032105e5a000382c4d8448408800351008009488414410f500502441c5411000c0c156101000380c0b18900841d000d100500009401140d500340b42c4000751541030301d031500381c20483c4c58208a4013080044000340d0b020b01910380c10440003042412000d444003022109007010035001c8a40031110311000409400048881e5481150715507101e10240c0554441d00c0300d00d030001000c95001c0805507243c4ea55500c503c25203007a050141e01e0050070b2908281411003540e0903000e45a01c402400100b2071301d40000051002d80c00105844031500081c0e00d185070003601c40b40780804230403010390b10700c000c981c140364500d14514100c0c02114042d4005003885080600d082c1c0c1031503620b0301e104 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 56639823 1250 56638573 56638597
    0xe16090c05090607060b031216060b03030d15030506070c080a0c0203010e070602070e0f010e0103020105220303050d150b040b0c0102070204021812010608030a08040f0c030302010204090b0103180305 87
    0x10003190b6644000241c034140317003c1d100005004a10b0360030107181c204c100520740c1403044284990482105980407103110250022400303e01080301000090452040d101c441105500e0108640000d401010801007075038411021901c0d0380cdc540b82c005444540c00c14000418032001040b20f41d010758403034210103506520141c00802e80e451003521240c101045a003080c40180e000e90010441d80341c0314001f10f0f400c601c048034500030325410090464101241404060705000c00041c41c83d07803001d4440c2400450030381c0c1407400c000c016220316004051360f0101100d250f0302400c106c510050559055000401c0301d1000060703505d81854542000303100c0e0407104c1000a10756080c4448805178403103000400448850b040154030004044007041186001000e13120030380e81c5400010b22102a00000312400454241040c58941d903403858001054005281d0081c080800070200104054054010f0003d5030307100c200c2400108020300c011000c0341e100d01d0125804072800620a00030070700820041000500c0a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 56641073 1250 56639823 56639827
    0x1704020f0d021503070905010c02100507080d0c020607110c1e04060801020c030d060b0304051009080706020a0c120c0206030406050c1e0c1204050618040b03010f0902040e16090c05 79
    0xd0b4002883e000340319641d90ba0845000070401820f80d50045038207010340824207018807050107a4001c01c5042d03142da0404401e2090010328101840908003d2b2601c00502c000148100b4a00310700c02501d803001038507400007149941031940707043d00d070114080d004d00d5005070809641065500703640400080840b0f9035900659203004c08502d0503028002440d0f4046840000d5584180140700b0401b198a1540700009900c410300900001443c0819024502e80e0400d8000c150a0340a04204416225241300184a503100040040910340c000a0b170303019103402064400d85030401c08405641d0541c01c008000c1d070200d000c1000400251140d4050b82d0410006107000d0f042900d010504480f04811204550700c0b040702188010740c04000300400c03404c3c06d07014222581030614100100f9280c0c003910101e03000405000c4400c030181d40383da81c002e0440010080080c4401164400d0441c014051030340280d00a81c10180307016280100014406102d9a4461080c12400c3c41d11000c90001c0000c142034008112003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 56642323 1250 56641073 56641099
    0x70509030d020105090d030c0207090b03011806051f05010e060c0304212a0308161203090218040203150702010e0307120f0c020a1e030f1109071704020f 67
    0x104901c0c418214150000078031402c1c0700c0d00f074510f400c2a10030301030105810007090214242e404203062084039011300e80400c0356400100040d026004005418a07628084036484091008503004180501130001001000c41049030071488004442d015080c0454041140d000d101c0c1405801400c000a0040035070342045c0d240c0c603012994499040c2100c64403040711300000d0603c850071445030080640040700348040744070baa100441d1820345c0d00c0003810310140807ca00d0101c500294480034010742c803c2100080b41400d18028006001440e82680246200c058003403401201d801da080c019500103004101d41440141686a640e0001301800115502e410048107001800c002a09810b4840d000300c4054004903c4000d10784150800100100002c5903086800f680714194406c080c5c0d141d4603443c0301185090355245130b490340355900081ca0104844800700c24044590b0301344240c50b508950107555911021001c44107403c2601046907001c01e02c502040042c80c00074989030b0704010160003454a500 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 56643573 1250 56642323 56642329
    0x2304020406030e0d020f060106110f06010e0106030b0102010b0f0607050a0804122d062003091501050306040b0604050402010c020603070309060b0d03200313060203130f120209070509 80
    0x305521407008203403144884001d210342805000802c0b40b6038402040140004c42c0c1ea90756507001031082505000542c0700c8010f00c52004c0c441040310301031041c201c7d4040d513998010310211080074814000007074600ba46440603503106003d41c2c080200001c0c24600700050950400481c0c0c0e0140400f2180c0b40305600c244800500084040d10080402070668004a0400d0802d084000405110020b50544100d0f070300740341c8988000b005000075007280d030000311208242303104143c02142c8042203040741e8020081018280e4009117142424000007502c8480341d84e24020700d9034401040c1c90007000c030a6a4000500642801c1c0d2045910600514103051410503e4021035a56842a194403002a0700c4148603428040c0754050401231a0083d1144140b03e5400d0b00d0040c80e90002c41184084043c080d05440a00070080060361039100fa091040b120081d03880030040c0d0b40790300c0400c060008800f00305d40060400f4550760941e04403903000e4154900d12080382c1c00c200001c00c0007000c50381030200500148100391 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 56644823 1250 56643573 56643577
    0x2031617030703021b0d0b0915010504090b1f050d080306031c020304090c0309170306090c041206090203010b03030408070e090304030c050409050106170d030f0504030c0209090304080a0c14040902060301230402 92
    0x1001230005044100026003c5042c00350058002d14003d605051351103001035a015900b66000c0c03455410225000403c141e080003080321a032000b5889031032594490b0900c8003400045005400c11011101404c1d080c4150440c80c001c04140e55015070414031003000880d9071900402c1c1642d07040d141c0007074007400994800306242c064580310100c461000c0100040c03402e002c010f141d00241800031060030545002032040e00d40f06581c000500036500c480c450000c40d1001d400c5800401d03c02420799032515140d80710789940348800e101c1c035141d40c140c40d400700b40074a401004032403d8a80000c040341c0c440741014140000303030000003001c80c1c04d590ba4400004800c0d205801c05c502e140d9105024052910034080010281c44000c030a941000d85040107101c002900b1810882c10700383d05480c80e42c015540d28807107a0840c0925880498540036100d40f1004003d88401c1280503036031011010310003910b40c00300b03000c1213801118000b0f4000c1d000301300601099484012a0020400c040c4144000318020000b1a0607a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 56646073 1250 56644823 56644831
    0xe1003061a040602010c02070b0a0c021309050f21030f1512010f06051c020405060a080102030408070309080c091f050303040f0504060506030f0403081302031617030703021b0d0b 78
    0x2218001c18140030fa0350b4280280c00128031a44001c003409424030728201214400e00241c003041c062805018000c648400d108858040c4009408003d00c440c9402c1590700c0e4000321290074040c1c015036034800d0050b55a8504619502e0103141400e017140c0c3d031003803040c0d481d210103008482c08140418501150340e48405500b8140131202001241c0414803585101c1618031540050748140c000b0b8200c0071032500c030381e0059590039404813808103c9840340d00100302d0903d0310750820b00f2154000410841846100c0009101507032090340d0f1001255030b102c1c0c405840c0c88404030300c1c603400b60003403011400917402d40100035109844802c0c100c20311035440c80020300d154016804401c045076845020001441c0c28851000104000d40c2d0851440c40c10486021107008001e10080601450002190f18084003401d003103040d5501504070b800f008060603400082402d070348564100100c520051fa0307003120002c0299003016516400420100208001658a4403c590421034111003107042480c08902001891402 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 56647323 1250 56646073 56646119
    0x10f0309021e0a06032f090d0f0b0c19030518030c070801061205210409050a0b0a05030d0516050c09040c0e01050a03020109030b0a090b0108010b010e0405010302010e100306 76
    0xe440e0542052081661080c4d10520500d0324100741540307010100701c10811b0301c080d03040000040f0401c0103180402405914038007600114072840b5601044220422000e071700303004103200c041d20359601e443e00d080c0b403003101c1c5049031250020011900d418065040642c0003040060000d50340d1101c0810140785800880b8410355503800b484080110050a04c21503016007142c014180201d02e02d912080c0c1d85034400d0302c1180941d506564048500040c020540c0c0c068251070b0310030320450408401d403001810000810521540e1032800008092500044401c540e104546030241886281d1401d20120f00714000280c0d95406a81d9807882d0b03980d2a0815148254810b50000480038100400d8000c9410141c000c54024010518140090717a0052106070480303034040d202e130b4800e0b515850444d014120724100240258581000071480c1c0f80190400355442da02aa101d01840030524100410350b842840003a02055600f54180f22038140f038404001c80b6071a80c10041002a903507079000c512258070f150300801c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 56648573 1250 56647323 56647369
    0x315180f020a080d170f0601021911060301061101050906100b0904090510022203020112050705070c0602030d0b04140a0908070506090a1a07020706110114010b0703110303090a02010f030902 83
    0x28071786003a030f046651405980d08902d440700c0042d640d94645200d403900c0065214075402005002d0450703103502070001d02415144e5039107000c09004c554007540201d20307a5080800242401d2800190340d0b00ca0110150024841854910f1105e01684444100d42e013060b110164100421410400f810003882454801079072a814400328620001145d40341004101c10708500300f002d40e030720401180c074000701b4680010301d035100c0c0841540c10b84038a110092001020041c0020055000f0018140307990094400b4014880c4080070401240c0da6607102c1c841136a11500481c200c0400c50340240340c0140b0801e00300c0d26000c620380b901450a68212076614080d4850040c0804110392800c00030540c0d4038840c03007040c0c2e43c2803610010351500e103140503100421011490350000b40c0801d400001849056107045902c41d40c60315035404059011940517808a0f000c40c0b07100b00401400003c40340700e4054040540f08060a0754011502e003500c1d071603100b040644905441d00584d8560000390911106404004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 56649823 1250 56648573 56648597
    0x90b0f09010311150301060804081312030206010906090915090305120108030a02010c0509030a0f020a050409050f011104030c06030506130203010b090909010506031e070803040605040315180f020a080d 88
    0x2c2c1a45041c3c1c01403400c04c01840100800394000000e035411135486840b01c0c1d112200d44103094214034055018a00c8460300900c08028180c0200340181a0707150300500380403813074503419410140c2d8840100201f4230f20f00c2224170813400c4115800080e0031882841c250349440400250755514442c2078000003181d410004001c0f15450702481071424880b85070500e40c2c1040c170700200103601e4000d106005402d86041420704411540c481648001070311f00180308200c000101d0a055554810082034903016601e8100c0c21030b00f040022082d20700b203a90101c4e000703005604000c030443c080e000281c28550040400c11200c2d4002c011070020710302909642c554140c0382c61603413040054401000c1c0c08040075900d0541402803940300840c030040c1c1c010034510428100c00090982c14601100741c3d1140c540b60002090110300640d0040003041140c4c05025960307111b82070600310300c040f55020882c9454048031400c1900c00203442009a642a50004014032103590366103034070b07a0404480224042c0002c004841c02 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 56651073 1250 56649823 56649829
    0x90509071e0f151206050d0609020102010f0f0c030621080d1e0b010f11060c070f080309060108070b0f040e0601030f050403091701150b03060a080d0c0c06021501090b0f09010311 78
    0x20f5074050b04e10f1401849072503d0400441c10742e0000c0100549481e40381c0c2d521209590003504001e0900c2e00c5840308100c0800c5101a420040000c4a04c0c040000e0502030f00080c0919000380004c00c3e004140480c60081603203586180c0c440d4046c0c0a10a20a619041007004010302da54140d100b004c103010020841c03984084c00105a040f01c4c0003084140090303020025102d41300000d00b00c1e404200201c0c580e50f10308041c2060003d8403818100101031320740000070441d00305c1011aa007812114900201c0f401681c6458208180e0b021f0148691a171200c140300c100300c403500384410300d80c10200605000510400001031081070f00e41c1204c0503408660001c100700007001d007128039200304c0c12014000308207410707682010703160390700030351050000042d40480030900b02e03a12502080000c0a90100722444c1c041c2c90b04020f088640c0c035110a0b1006480060001000303400030900e92000441200741043c41ea00b0860711000511350308031160342020603410180500e071140071400340654000c0c20142c00c1310440401f0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 56652323 1250 56651073 56651087
    0x612130f050303041505100608060d0602040311041d030909060f0d050c1201060b0f0a031b0206010501020d0f02190c0801061202120706020a03030e030702090a0213090509071e0f15 79
    0x1e0002811b1410080180c003100310100071090b00c015240100d42e946620740040c03d11050403101500d03281c800580001004031505499012001c00d540074800d403007040046a21403641e120858038a03030020006400946010408030b540104001d0031488a41c0e805000300da0200c030300e03880450b0340342e2107000d5000880c075040c2600d0300b5400843c0000c5c04007905004640c000307800340d40c0715004e09150100d0301c0405a4000d40001d4141200e540000300e40b180200c800075540d0200b8407560b401740c090003c5901045204440003662203820f50010f00c064141285200034400c640902607030301c18145000465508000e0143c0070080034145000c20390b10120740100324030f0b43d2030b108811940f58000b0104102c0282c0100f6807800103601400d001030344a80c0c43d41864114802d4481c000e6010702e0113410000d00e10b900c1c1d4040c080d0000d0104420800c0c1c0c0c0c44e10558012101e058400b158554040c22040000300808441c2108481000310003110032540d41400c1080f6503400d402c50102c0819503100c0d00207031940692 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 56653573 1250 56652323 56652353
    0x20114010509070f111002070317010506090a05060903010b042f0403030e01050a05070f0f0b06030604030909020c15070507200f0103020903030c1204080d0309020612130f05030304 79
    0xb4010074981450040038104c103102c034100c101401880754580d4005c0c4014045001300e40c00103131065595202a00d0000e00c00b00204020158540c2030000100d42820000e0542c0c00004001d045115007504080030004240c0001544540c55925009100b80c640c507940148583d58130a042d40f00380418112020234000c4510000b003085181c0c0034801000481d40c803c1c0c882e02c1c003003401c0c00c1a994510290700110303418031031281d002c0c001081c5e10203680c0407c090021910300c2903005230742060450b02d41008258072120241c5016000910102041c004c03900240d005100c40381510080b00c0640300500d81c544002981103541c2804204049a4141803008200c1058084003620603c10700d8000303c40002801c6c0a00c14405904155021895a0507070303d0070022996900c00c4c0d04101e0301d00302c42e000790b20342880d4418000c5c49098090103401d511064080d010b1102da465008203044d0500c91760101c09420401d000344400503008090802001185c2d09500d0362080714003502c003840d9a807819003091107080003011 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 56654679 1106 56653573 56653579
    0x80406050a030e01021912020c010e060603010e0303040c060f03060b03150f03070806010b0304050a02180f070e090a0e01020405040623010201020a0909090519030201140105 76
    0x440070385103144069400b40f15041d10701084900342d00400d800384510719181303006030304080c0c09401c00000d41104c17000010b00303180160001e107003503558107203140107680c000074188000c9003801c0c00340138440800074005501c4c2d810550b640e0290030301c45120b500300304080c00c0604400d440c842d800800c0105841c0211548a00380f9190380c0700c0c14041941c926100301c42455180c115403d001c1800b070111010038025043c0c607131816101144940c80108116558090300c0c903000c0050790f0384d030f00c4058402c6da81020311541c4e140051400082c2c80c000b42503d407d0001e0340e20036200c2c651b9100e00060b03200840c032002050350350341000d4080c003a02450b0051580503090210100d00169444a200c96140c0544560000c0380c4a11005a01b00d01c0350450010010745005414881500e55403c807801c107501c82e00803502c03000544041c0d4242d1304190102100146d4460000d0761000042807020f6000d00412 = true := by decide +kernel

theorem cover : BRFrame.Cov 56474823 56654679 := by
  have h0 := BRFrame.cov_init 56474823
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56474823 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 56474823 ≤ n) (h2 : n < 56654679) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
