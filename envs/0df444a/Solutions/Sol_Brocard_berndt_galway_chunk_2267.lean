-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2267
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:11:32.895293+00:00
-- url     : https://prove2.me/submissions/9f7c41c0-ffe0-46a7-928f-9a40ae4b87ed

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 407553956 ≤ n < 407733812 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 407555206 1250 407553956 407553973
    0xe0105010f05070525180e0d181401050705010216060f020c0a06051302030d080a1506051b010e07080a1a1003081806070f02041b051e0c0708 62
    0x681c0416980300c0416149011800c0c510310303484d810380395005449a022200c1100c1c400f800f100d1402c4090100802060212041142124900d2806003981b0f10510440340a402480440103008003880183d41100030000880301d400c1040014690800c10400b0341401010302005000070000d00040032800550850300c41102c44030700d01242941c0c0407542880a40d40103101801c0d0310500000c0201256400c19400300300d544405904648041400300080d406006d40388164400f00d4210f03038150700031400e56004004184006018055808407402070800142040080760380c00c144030076502c041e1803400350002842102014600d031a0441d141e01030110740c1c003d501220180606034a482d16102130321210b281403440d1801440070500940e020060850310082425545107514000c0d06802c104050121a558503040c01c02002c84510580120300c9517061071b4041a10966401d1003036a1005c1c591101030a100021241011a0400c408942d2100d007080c010904c5602007004520000d0901360058030044 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 407556456 1250 407555206 407555209
    0xc06151403120307050d09080f031006170402010c08030a0608070f0503011a010207030f060b04092d02090a0c2601080d05030919110a09020a030f0e0c0108130c0e0105 73
    0x20806403401c0c00b0405104200003160402c1c100c0e80c010826000014464003989403180e094050540070980d4040c0210811281c0600640f41c4070a462140d11041d031040c500002d0220103041c02c40d402800a144560001d0000303a982e8003464010000300e03008902241c941c07210502e8400030b54060440100c070710304100514202803060094044200c40e5800c0d014101c2c80020b50342c0c6040340b10007414400300d50203840030701540342d22200154400400a02c804800c5040042c0e991206101402002c111810500e42400305648a46a043d5000e03082403002d82e2038120303a40c010111041d0090601141c0184074034050390082070141c0102c0c1c141d5000c04554100a000d46ca04a02d00d0f8000c418031000f0000c1c0603503414002005c00c80301034039110402d0185d42c5441c0c1840701421207814503803c82d61400010801034101d4025040c074070110b54081191221100c0280d064440c80c10001065400c02e40003050315500c9001c50a500101c401001c0f4400d150b20780e1200c00020050340001031550403030300180040d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 407557706 1250 407556456 407556463
    0x303020c1204090f05360327010c0b0f190222080d02060103080f0405060a02100c02030f03060405130b130b0708040203031b1e07080607110d0c06151403 67
    0x48548001d800c000d2450660306c10001203400c0b03140411046090341c412004c40c0c446104651201c12604152904d60a60b08a400c40d003031240607444d0802c2542120101d004c0d482030305d00c90040c40d048410507800e51071b0a1181c000700320015060f204855065817500e1003d03440c6000402c108090360584030700080c41143d42103600c0495070452000c54002c0e0380840c0005a00196480c1034a4006591551f43c8901805c0300da0640b28903402581c00090110714500c440c1e03008101881d0300d662961080c072a080501c58201d882e4800c07003841e03002d004001e0002ca40f09080607030015030310002448403192402080d1320340d03043c015401c507002d400320701280c180700042209861500380c03c548942490401820261300003502c0303004000c01d407005128810680c183c040710811240382c6501022000c0d4401502c00308071992078441e0390165030114425200070400382e61143c850401c8402c01d00300604402401180b00715009100b83c107003501c40a48503400d401200c01c480f000c40004080ea8262010500261130070300d800c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 407558956 1250 407557706 407557721
    0x411100905130b0604030b090114070f18060212090a032a05150f031512070906050603060a030210121508101b1b0f230c010c06090303020c120409 64
    0x1181443c52000d038585603001658192035100d080703004941d4410442600500281500302c204940c0c034014010f210790800c980b5480500310783e88440e0110b0103409507414900007449644010b0348480c5060382204101c101038030224500500903225a95a6111100c01d2462080742a010b82c0e010308420136203000302254500102419a5131307240b8004035402c112003e019081c10300e01c00305800070000e0711044000070129203180d0024017074075454140e83c174101d13074078005030040c1300c9500d03d00f1501007a01c0c5000b1081e40c0c8140b100400c01c182c040c3c1558280b04e071850103100001c0c14040c105004858118041c0503010201e002c07080701c02d03005894100701c186130101c4050b0400720b4030320b08440441d41e6502640c101400c000d03d401e2007489059900484200850750080c041c145008581c90a01001003400340b07410700056403039031040c5c0c4490704221562664080c0c0d18035130201e040416801d002540e150400c180c40c030b0003400c0060620008005c0d183c20605001d04984481d540043e09010303405103403280a4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 407560206 1250 407558956 407558989
    0xb0c010b130c051c0b0901090b01173d0909030e09131b0e040507060206010b0c060109111c05041e020f2b05010b1003051e0411100905 59
    0x1c04001c8028010f490707442080c2d0200a000300000410550304030b550802c104004c005032640842d5a502e403442d000414440c40303011f0003e0b201d4921804040ca102c02c0c0107014210140da42e10303c629413010b56815411104403840342d54081200507510b04404024864005c2080c1c1d60003088440036460000c00f9900b00014030707071007119841d01f8094094101c201d01c9200c6580112000340100807521054124a0300d50b008030301c1000c40004100c2040804542001128402e4080350ba581e40ca48122034441c3c0685c2d1031819265004100400c40c400300384d000703041500310030b1500d40d04d00241143d2002c00d02c2c440f4007008482c21307194018001000480c1d1050b089446440d4852410100c0c1d580c00140c602c1004455184140d070080c42844c4800318540301c0c80510030154910030a08249417800ca40600050640b903403040c11052807458845010303001c0c661040001508020205083ca201901d01d0200500217456a208a0000c2c5241e6182c5801d8460410841e4413030004181c80c02c4200301d01190303900000d4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 407561456 1250 407560206 407560211
    0xe04110a06090e04060c0509040908180a0509161701080f0d02010b030d0309060b0d0b0a06060e0906100c06061d16080f1e070302030403030f05010e130203070b0c010b13 74
    0x20800e08809400e200c1e08107520030360214140c1c1106e078040300c060095240d0581e21500e000400d00812400340010581ca502041d008107003901c090741040f00f41240343c454280c000c201d15000620003801901070051001c41e60a01c104000e640d0580d15000000c02d800c0841964062541c02d15101020003030400c00b41d0030791009201501c49003003c203850b180c0107000c035001d240e01ca980c60409c000d025081448848406012660149464142188440c006503030b00d5580900e000008583d030f620600c070800c07911002400c40c50722912848280302000a6000e80201000402e0207268009101400340d8401031040b40700501000100c07202c038156103180980705160082402185404544e00f00340b185a02c202895084500741c0d0303900040340d184404402c892004000c1c81030411848681580c040c60091b40207650400000f4600d21000e01200d0003030040003071140c1e440d800124945a8825090381c114400b03001e4402003a075405891103641c0110780c840c80305035103914000007242000807200c0050000c8cc00705 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 407562706 1250 407561456 407561459
    0x11d010f0608030406030c090e04062009010804021c0204050c0409060503150c0318010f0225051e030c030313120504180203041416061d010207140a0e04110a0609 71
    0x3283c3d503c0c4550b02c98003040c192113241c3c100724140034086041c010110a06017403058074152034018001c01a041a0381070600040302983e070090300b20b030140c449586040e190010540c44a40030440c1190340c10022800e2601060180801170b140e50003058000c8045c00d120381e4503903050400b0082900c0158000c18000d074080500460a00d0106240c690030511654145903281c0390a1188441d0343c461703a04021656003840c3c00c821010400794028000458514500b40305200c0c5100c48074040c0700c0f0a800501194000034a030205403801254501c9540241400c0b40e19260f0f01045550558008840d86030520084003a44414090039500816030760010380341c000c1c5824105600c0a203401040c0110520740c2c2e501000080807c000c4500c0001058135100441c5c148040c8204080c16080b00e038007822000845801c09400020148a200050082e05030040c1030082d040128000d001030901c01a00d0b84150001000104000203100c824050760085100c20b2800e10803600307210419001354448810481000e40 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 407563956 1250 407562706 407562719
    0x21612170d06082109090a1103040f060c0806132c0c12010504020a0303030c020a06050a15050a050d0204020d020f04030804090c0203130b0a020f0f030418020403080a120905011d010f06 81
    0x1110703080102111b00c02c0a5850390700c20600140400c0344d01d2041c0350b0001091209200352004060501841390f08148144001003000701d642007010344115402c116517010941d0b504d0400d0704898a00e000015202e500c0301070302c0c01c07000d215220000e02542030743c0100c50340c0c102e582000c4c008084511840c10090012b402c05c0d901080a40d00944005000c2591f00c1740041405482480520a0150095020710180c01d00c03400043c024860348410500309a90000000745c2810840d0300380b011103000038110802e400c9190280006584000c42c0810800c0d400c07c0300310825850080074001550040b0740306903d507410140e119040324840400326044d0f40c000d000c0c080c10310b041c107211042035510340490142c1b1a00c036010180c0c42d01441e0104c4460034000d000103829800d44c0040600101c501c1081001c110910b035103c420100d101d14000034103440010441030748200e0184045540c2c065010100091602d040d86030f440c21642047c03a00f50620300c100c1c600c0303200c0e42424010b9580d03848000b4010000b0500d80748 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 407565206 1250 407563956 407564023
    0x9020108040f030207091a010e09070203030c0901031d010c090603050606190314150a051806060714060903030403030b03010c08010501030c020a061104060f021612170d0608 76
    0x100020061200c0181190400d48280700420041a00b081c06010b594410384860038000c07c4088903d000624891100e2050315000800134000da0090f00554550744030080c0000715035000c0d0380140c0c18151102c240e00d65040081c4034500701040d01c54000600d015501d0001010000c9541c464000c0504200911000c0c1c0d0340e445c106c075104001101e241a003621f02400c150082d101e016a00415010518100300d103a0703044005205e9010400c544510070b05480b58100801009032800b0748040c108010005101410124000c108041c060003004501529008000c0e25100c4100c401c2081da40012051004250300350140042c02e0750124020b07c0104401c48000b80613441c14810941090f480d03040c0350800c14020301500400e6071f00a1340921000500402c00344040d48203100f29000200e8003c170442c0c10328030101d80002c91280340c280b40785482d4501080e144be5030ba104103040d5140c20020341c800d660444540300900c0e582c0701c500b0380810164130b4144920300f4111507402c01800410b12201030b41a07000c044 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 407566456 1250 407565206 407565211
    0xa05011415011b1a01060e03010e070509060102150c0a030c030902130f1d0304150309020a170102190e030c0102070f26010603140d0f080106111c030605011209020108 73
    0xc0c600707280e030040c1c0304083d07031070301070703044074040c02c480342021115541d2070211050328144d60b203a8480810355100f65040c10300700d4100c8004680c072504640b03814001407411500e002c0d00998144104d880d48066000c141e81c0d110025280081a032000040a02c0c8858060203816128040d5007820000c40300700d6000301c0c180200c0202c80c00e186550720030fa0389240f886d05502400ca540200020740002c40c100c4035455a0303a500c6409801507000e45070440340e850500c0f9024032070002e5400303411060500d02e40306050550170008109200d10f55002d11081884174400400000c40c081256219040440342c02c0038103040000402c442d50440d00710500c14400065108940c0d000c03284c41d050061003a04604441c3e5a65070b10a09150950354201640001441424080d42c0c82012072601511400e04142405917011200940780340080380b507100c010800c0c503010701201a40900c1010996100012148030300c500d0541170050301c00425070303841c4203001d5541d00c820488200090690104000b080c030703400180812000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 407567706 1250 407566456 407566459
    0xd05070b090a08162003030a110102070501051314010c0815030a0f03020c0a0909050c01050703022103181f0b03030c06130210052a1e0a05011415 64
    0x5a0106062040c10090345402c1034010385225110032405180c680501031030b5005946170009440b40303000c0c0f4113900710000032200d07004004601d003c0103000c040c0c0e008100d0305c6030301140d55420310412022480a0050030300c240075550150402c01014544514000980001c25000340e00d0b250300c0b1040c80340c101500c81d40040c210203517600c058200c400040c0c9845440d2030010451240c200540c002c041d00000d21044564046810009040e15042410101c82c6002d10151199000b01c1c811401540a4002091100d0080c41500d0540d500780314940079009400d10460380c14100002004403d5030740f04d00c0030404041d8040a0f20303184030307561289109004002001102141c2e00c0c0700900446d5410011124048008400d0f10f10514110701d200c446102000c800b81e0140300400e0841020901c15800c5a501016158180604103850802c02c041c800c1050003009880c821b42124603002020850303d0051440c00c0030082c144841c25107400e82c01d60741c5003100180039856402c240003002c1e5002412956040c070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 407568956 1250 407567706 407567723
    0xb07020d06050c070206040f0e07050705070b0a09030605250903020102151e0703230408031305120f031501080903031807090906021e0405060414060c01020a120606020d0507 76
    0x43e0903003150f080c0d20911600075030202c2c00282c00a039030032a03140640110b49a01c3c0150300340e6a54508140c41620451000510f1600000414803d0001d04400b03003009004074980340071402c0e182d0b0380cde043c101c0e04140e80648262030180240454042d200e8400c80350100a407078205d282a1459001039a00c81c4a002401c1c20320446600283d49106100207600c001014881e60480d5410310700c402500500c5e0045041ca00411101c5a10307040d070802d0105603014650100d9102e2460361954a28480e0b880d42c0003044400d03001e8440142d6200c8150f8010380002501c6075070541d40c03420000000400699000402c5040c40703002410070542500100c240e13503009110325000e040c400c4016515604044464101003001071810100206000076503000e070a4112750f1054000445000402010749400340c0d114456012008110621050700c1241c000350001c1800380002e0b06042200780c1160983e04100c640780001303480900e200200c0c0850b8001e01005007801c2c0082c0c44480b59105004002d0322486030054031003207 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 407570206 1250 407568956 407568961
    0x3050c1e21010e060f0403120204180209010908010c0905012712031b080d0c18170703150509060705090d0b07020a05060a05340e2701030605010b07020d0605 69
    0x100a400c2102e51283c2c0b50282d4002c0c1ca407450250316411380983d03094000695100e02c0480d001a40c2c400c407016603001c4401c0182c202c03003c8200f440a50312202843c1d0411602c0c280c0000c00840900800150210039200c0307a4200341000c00041c940c0b4080c00d0745040da20240158030042080b814602e1081c4c40100b440e14003d000942816600b4401c49891104080340f119181c4051107200d0b006050445801325080c000d008040504035a800d5518402031010850b04104001c041040d01040e0b010386074080580d82525643e89030b0f08580844c0c80e6003940c40c04d03140c100b013100d0101c050000d09d03800726503070505509140c24a0041043c0401e041e000802240032000420610313802042413441069020048540790b00d0b014044002400381520840421111860889082007074020011610041c1d0803200c0030100c0d0139541100c01d40d255020032508818031020070a00d1849006074099021024400705107954918540079088030030583c021040c0303644c18082d0f4401a8ac4140d400e041e100d4010385d0104458 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 407571456 1250 407570206 407570269
    0x708040b030108010204060f0c021f0215090601080120032202030604031106070201060810050a11042c070507020f13180606050603010803120a060f03050c1e 69
    0x284100c0e08803605120012000065080e4150020b006488007070fa526169046010703400e40b808180108000d6201210003116100e0000c40c00e1540d138101001d104499000060710801d1507e004203480500c2c1d56040803006000102d0700340034500d80300d0101c800a4119503c5182c00d20313800d0002406a030030380300c0e0300c158004050071046800b250a5800801752003e604042c500505000510950040b00380502c80000d0f04090044c07081074129500c807000350802007c00c03550351006040c010900015650744102c01400f640c00c0301c000d40080c018007180c042100360714103450380310407826a500c11023400844041017a501d030300c481130368003056040c1e0f040742c00c2c005030310300003800b1242200d4000042840d11790f106501d2780c012929410b4190144100300a8240c48200f448020300c824020941c9541c000c000b900400c0e8925000307183e0058502d40c00268650b00c4055400707102c00290302c1aa03840d845141c2402c4c1030b1030050303030001421094000b460b20103a01d45020601ca001c8100c523841078407100910030f00386d1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 407572706 1250 407571456 407571473
    0x61303090b070201180909020906041104141201090b09010509060112080c012009090108070803122e06030b010c0302071a07020904080a1704083c3001030807 69
    0x5d40c00240f40d038075120394480300c00c04000c3c0490102a445400030354042780c2d03070341040d11880c80314031810100309140c00c1c00d0103500c0801c0c41c469000c09400c10b01108000711815428421441d14034402c2200b1405810160310403429603002906604250304404010017240c8070050310005415888036180e5202d031124080180100103252800c2d04682d2205154144207156100604002604907040c40e00c03030340c1303c0600c11303a5000140030b0103030164400c00c5110042100318200325801007030707a4105201c6104101c980120f00510071220301c0202000c4e03c09100040d018000d07941f411000b8a130200043d030084c0c400a40d2010503100382c42c100c010075602c501105000108807011070350041d006804a0400b403904045503408011140009042040184c000c100b04100b03880c021a04034500d17508214101c00c3d030380c0d000340c4c4201c031420240c18429041c90110700c0e4803d0b0030548561480b032581d00c0740c60003440c000700c40c12140748141da056002039210728038400e01d4820360305403034000b40c90a855042625210b0b41c0d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 407573956 1250 407572706 407572727
    0x503070314030c010501080c120601030b040b090a0f051006050f0a0b0a2a14070308030f1504090b0403140c060415020913060303090b0f0702010e011b14061303090b070201 75
    0x21a54241030001c6140b800c0023490900828040d141c0140c1c06040070394141d126031084c000241813003590004180418081d40900760040183d006a4100540d1507aa1000107510460210350713075081038032162591f60140c856207000740401d44803004562030003400141c4800c00780c000e007600540c001c194101001d10400e03c0665414a21409403a031000021042c07038002c2c0112402c0700c0640700324041c030422050211f4128202d80d440b01c401d505540b220740200400800040455202c544d5803c5c141d0541d40e034078005c0940307450240314030351001d081c941001407504030b4103410103420100801c1450090703c40091040d80c8140c00c1542d05240340c0342c54012001910071040700c00d030300062999031906240c103241e00240459110307485c0e1010a0303581d440072144c04d028602e545c240c02c0e10300303025400155001c1c0740003c800b000c0502d402c001c0c1100c1a20f95503800480b05c00d017a910210407050310712403200b0402481c0c1d00400b44500f0909500d80320780d0010300000039401080da0821010600a00710f9000740c04018 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 407575206 1250 407573956 407573977
    0x9030417030405190b04141801121101030204180b0d02090f16021605061c060b0406110c0d030c1b03030305090d0e090703180210050a0f09050307031403 67
    0x145800e10204415941e42c100303014032442541c4052841d4140040202488101c03070b0b0000d410b07814a0f2074008500d5940c070404100c3d54102c0c900b40d407a02003070306188401d10302800310305190a00f00301050074030200314528440301c24141841000184104522510308442c0300e440396601054000c0e205000c40c2c0d07011007010000350000080c0301401178404645640e148601420100d841e010807220340200c5e079418a51448007048102000180a241042c1c001040e1003589184c219480000c4a004c203c1180c0e0194410300340e0703910128040c0545684283d00301d2800901c140181251801600001c20100480030000c0a10940c9030502041100780800300c0021189030340d01c400f481e903480c1406000382108a80154550054114880e0310700c0c000c10340e42e00e554600ae0580029540c61034400d40080c1012880c41003900c040d186900010703562001040d15901c1d569139015200c1307658980140514030f80c1e94104e0180701d20103000b800b4548000500804403604402000d940c100905015800c40c490043d540 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 407576456 1250 407575206 407575229
    0x806120f011b0f0207030305090103090305090d0804150302070c090e150c0d0c0c0302060412020c030307110103050f0114061b03030906040201091205070b030a1b02070302040b04140f090304 83
    0x440400740341d07842c0c0030400640380c89140404600182c100c2c0c90700840d02009010507420f1051984079440b03070f400700101d00e10038100b55107002001000a452281d00c000700704c51069000070180702018035080440080b6446080950501040d0780d5024a2100b481c02a10f407020340d075118090260b0f104101d607440604c00501140514100b00104401c2503200300c100d8400582000703020703518140720310400411541c2560280c005a01c60b0303a241c071080140c42032071400718861070f0681d03600f070f550030b200502c0b11610984035094070165910001d01645c01c0100307401441040075004105280d031400d90021409400c0750000c1e900c07103441844181d1403959201440300c0f4071012007003100b40380b00015924001c5000b40c0301ca0140d2035031a04021510031000d40020895086843e080100a44903005142c01c0354403504d001c40d0306031401500c1d00042c1c40b8880440d005901415040056040502c6090400c40c1305a90610580c0b11382040341031a10005050920410031020010b9240c041c00d00c1524080d10a51085 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 407577706 1250 407576456 407576471
    0xc1203190801140105030601020c010c29150f0102100e120301170606091006031a12101b0c080a11010e01202b06090609061401090302010806120f01 65
    0x107003110424015640340c04100c50440d02198080c1c400d9038841c0a0580c0104640031258004607987c00d464a4102c4990b481e10b6090031148400d0249124100f210400100ca03074a88024510b40c40b58041031214080c0036400740008a59a0115000703140c0101c910b40450002e500c40b00180c6021500481c1d098115404800480d9042c1c0c4000201c00d2980ca00089512039151030007000601082581c0b00d02600412030001c0000b24000e410a421400600711150b94aa00d00360118070b0030010101d05070041c2d04040c041403291403051081603516a8007070000d1542d040c030001d0240c0114001c4a020340000000703e61000c1c410311030140c212100720044000c5c40088500110140a0002248451003907030846000398600a806415696807074140c00005d00310000400c225503006200a0401000315195040400ca18015001d9100203108030400003403100e260140000c82076640f0084241004007100081002d0f0303030b00400c510b0700724000312001000341c01c9100f500e030f20301031017600301c3d440075402d1040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 407578956 1250 407577706 407577757
    0x50103050c01050f1921052401050409020705060f0f0c2505070801020c010b090408090f1503040c0609061107090f1806020a030617100203040807140d021e0c1203 71
    0x1c40c01441a040c1010030703d006c01c403120000a41d5003c03200585c00b10366003050b00310036560701030189030300e02410704020703240035260000c10050f41e028450944442c2e00c900107001407103030b45180151348159007041508960402c2c03038242c906803040103404a400940f5400d0210b0f4481e0b2130100701a61507100088070700c510b5030355520902035040403c1c901c425500c0c0c01642d560b1801e0008085101303540c001e01c2240f4020b421420050b04428006090740c00c9510b00582c01c0900c60003800641c0218010070940c81014501400204030303454039004601000584c03c001c00d04068001307410307411b90303110800100c0c4582d24654010010003503540c2c1140044510241d400500c8032541c02040c848005940030300c0555180d900884409114000300b101c60781c40070054000348001d540c017464005118070700032840c00803241c072050724003000782840217015000181c07010b02031a01000389102c007540503040a05c040003c514400d80fa0320b05039607694061054402d40d02a459001d100f201c8102d000c1100c0001d00003030f07081 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 407580206 1250 407578956 407578967
    0x10c03121a062b11040e0c070f11030712030507200a1d060f100f03060308040303080a0e1b0913210e0409020603040204091703012304050103050c01050f19 68
    0x8011031021203464222110f460180901102c461001006901e0240341c011503900e48440100403203ca01c206010401c005481c2580121005000b400750b2459103540f241018280383c066030201040c40c44650184000903007003416904865040603a0300b040d0712000012030601c04050400c0b40d03021003c00008201d5203003c00043c40f80c42c0c0300b145c00b418a40c1c2c51400f070150705e054210746594010400710a80031454421050841c0003143d600d0301081259503591018256000b5400880200d030b800c100300054038403d8840c0520405010000f018210740c906034030b20102508810640c0141d04800018000a074014007005c8500e50100748040714940031040a100c44166014010000361382c00324180b450726042c0154600c198008024038519110703179013008024640254201c4c0e00c40503c040700780650710008c010b0750003400106403040d0340072000700c0c0c4c441e40210140034062150b4500401030011a00000301c00903a4042030a2190340d4000903010301e00d45006400005048241421000a5050b07214 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 407581456 1250 407580206 407580247
    0x12012306130e0603030f07170910080601020615060d020922090b160f0305070e03010c0225030c031b17030409050a0e2104030c0b03060f010c03121a06 66
    0x7166070909070b00c3c0c09041603164483d2200400c0600001e018660204445e84100c180312284c4c000118900800c0001080c011a1120395000c0801c0000c0308202c8696010702046d9400b0107444410304107604140b0008840d401243c031406003062f40030504410903101c04429800800060420030300184048003088040d240e00c002c1207505004a4001c1860300210000ea03204001158403450003041c6c1d614030413001010300610640400482c1501000f09441c03e00c00c00706640d1f5a94040c0481c03021101c003480c405100141960440042c40c08108049181c0480e079078241c0e03500144c1c1084911080340441d4030000503800162001d665440c00c2d18a088000005004071400d41000b4008c645d10b041d8400215680c0911a2030160401010740350900c4e46200b841400c900a000e00c0c0d03003003549a8803402060400c1da00706590341007000050000915006103010312881d02442c0803280c0c3c0d8201d41e0000c0c411030040f03070308010306521119010010601e03102d440c05000005041c4d00d07121050409503480340c0142 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 407582706 1250 407581456 407581469
    0x3060b0102120a030917310315050a020708040801020712050c0a0f03020f0f01051512301801030608070b07140f031c0e031201230613 59
    0x10451059025400851850141c0351581946424541c881c801a009001c03050021181001c00740469140d940005c000340a03c8034107294050b03200f02e42e0785070b103c0d1040e0b070301c0002c500000d610010402c000791002c1482e50200003100d801040c02d0312080c030010041d010361a40280350003030104000c2583c010550281040c07030300030845600400c8207480296020312416089030300b40d40100c041d0310041400083c0107542548a0720446101c58442254030f4100030840512010a0351a00d0a0019406075024082545041100c2038120380b403042d0381c03040c0d540c1d841180c204aa01d850000e00d40390b40100c1d071011814144421541c1b9590340c1d5200041400c184290480c90120340342c00300110783c00c1000a500c1094030440c40000b0f113828859103076001003280f040c4001c0c039a40315401000b91240390501c0509a951944285002880c1740c181040081e00c0184140960390b510600030201d6183c1c090b4403060446207514018082d00c1072245001450081e00b21402d6080316000510020307003a076808032142166107 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 407583956 1250 407582706 407582711
    0x20307050d0302040506030117100e1b120c120f030703080105011205040203060c09040e12030105100806132327011404020118030b0a050a0f0504030c080a0309020a09060306 76
    0x300224141c2c1240260b004044d0000001d100500c00001d00030410b80d07140011008031003003e0010000c2ca01590500a071541c02d9800402407035032501c624009545003004200c1d0066484642c41000a41e917a9200442c80e10407413401d4844105940248031b0b054038000c007201074039603500f203608018141800c288511400146c3ca1b0040c1010450f10f40b0466000d964010003604540e00c40070003082c03280c0c001c20102940706a030fa10041001450030014482d0940715020115265803410f41042030b002000c0d41300c582406512820010b042c0e80700c6650020903114050001455025040e400c48980b030b2007003204c011242d094082c881102c1000520070b220701c000c1180b030306081c034204136894280c41030a610503098200920100300190300844c2004070413180000f400000c1980c0c0e840303024030080f05407084c40300150760b01d081c03180c002080e020b1604080f81000c0d0a203c1d41c1003075070f801030000c41802c10140c8420b4000c00c01c0c03142c0a01ca900150101c0e0740040600c0782941d15024240010207207840f04542292 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 407585206 1250 407583956 407583973
    0xf040c080307030203090a05240f040b030109050a0c0f09120305040b030a060504110901020307020d080c100207020102010b011137030e030601050f0604090203091903050912070b04061b1202030705 86
    0x103170030342400701c3c0c0f150000589c00e0b50300740d00c03010303803105400c030f128180c409042c240000300e40c0c01500400385009006001020510b400c04038907140403110150740d1a420044540c4400003003503008207444044800d803000c0f004121800703040448441c000e81d0441001540d00009100c03d540094000009842003100d04004100600400444070310644d404240582c00c280442c00240c40d00e140082001809014030f28940403a4000c190b060904002241d500b503903000c80c580095590920540b00e55000030700304041c0c20102003da43c0c2d501c2494090074800600c5090325034251003030560b07180410301e030048100c035581700701c03450301506c40204441c043e4000d2040500000b01d5140c0b40a204198450181ca82842c041c14055103401a50001308080107d11a1240b2400c3e400d110010340004c00d4081d64807203842d07a407540300700001c444000000441c40e41c024101800b500f0052030444084400c40e0400c1c12070300c00690584007080c401200d000d000504241e95250041c0e4020000b4000c0a1082045d034032841c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 407586456 1250 407585206 407585209
    0x412020c0102061e040f02030114011701060b09060703030f0c020706030f0216030c061401030f02132c1c1806050301120f060906050c0a02010b03150f040c080307030203090a05 77
    0x1000c044610400f1455081c2d9100c0c481400e8228064015002e01e00d03640fa0406c85402107403d448405080f110f2401c4a48010044076416481c040040206030000f4000c1c14989000d41000b4001c1c61a0a44940c50000c0c5403003c00d80607070700c91417684032941400d0107411824030002c1d407200e4003031080c100403904000118012440705e200b05c031a0034008031007d130841c100035141100c075001101011a2115036030b003c00c0500305950f080480c020340c0f0030640c19000c400c1d9841840190350b0b40c1005055850308003003030002c462804d80001c1d0031040144d02502817100842c10720301e1518000702c80780390091a1003203410030926840741d05206440092209210010b560f40011210740c07209200380400e100101501000150784a03100b0009907001e2040402c080155072510340c1110070946100e21510000581e0284654081c0265503400c10110058110002a0482c44a4008005003003c3c075000004001504200d05250f09002502160040740d854450525019651341e00c010712403407081c4869000051309 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 407587706 1250 407586456 407586463
    0x1201062301091203050304050307050708010504151404030809030706020c0f0c03120307121e0605240316020319110111041518080d350408160b0412020c0102 69
    0x219640344484020183c0e403610100c40d1504084c0c021100381c08100540c0380801c008020305800382c09000f00015090034075103030030000304104464a400250070010700c210b4028408444070760103609420416042e941d030100e40790441c801c0c0d0000130001480402c140702c40110002e400e49640030031600303ca018412a004040d540c0a07094885c80f049141040040d80c4e01e44118042c1c0e0031040000c40104031581494482042943c80c00c40000b14990380e80c50030800d51411a040c1000300c64054010101c078076400c00416440d2200805c03090181c0c42d0806501380c414070030402c480d1440010040d90040d0080b01c18000d245200c2c00300c0b001c4041d1300b00030300520001210000c42e412958180c0140029a82c0b45d1025039884500e07102c230180304030244c0c80006085409010721038400b405036603020803010300b803510907600c0d035903450f031090641040c03900424011304610b610540082d04031184588980101060200708602c0d114028044808103040c0700030800e00340521540c0d88032503000c0d51001e1547c0c0004994 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 407588956 1250 407587706 407587709
    0x90504080316030b041802010201110c0a0f050304050a1d0c090907030c090e130c0b070201090302011d0a1508060306040506130203030c070609080f070b0315120106230109 75
    0x811601003021aa056441c4a420510b080351400c0100f15903090078002801c40790320041e000c140300c0c0c01071420b030110342e13082c46402c41c1c0544080403070707051011040c402695422a10b0b00113041c410213540c03c200340001041a5801000300409505100f9215256071055840e04400090540c0024000c141260070200990f51038080250a10041d0b959159088001e414003203d000103200e07600e4000f10740f204c010313400c0350310610701071601100300b50b014070384410000040d51005500c200140301e0200140e0f4410a103c003240e40920781003541d401070040d641020302d000b029265004c001c06000048014019003002c408000c1521341d909a0756541050507210a0201c1e402011608803800240480c1e405265505505001400300c4c1c0c03c081040086500d0040307503401410108200c0c0c2c5040141038410045c8540300b0b80d07210060311240d85001e42080890201030070040b01955000c4034003200362200f18003041030188840003404141c0c1d8542c0500d07520b4084c0b0300240207007101041e040038a0750246a040c030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 407590206 1250 407588956 407588963
    0x40f090e0c1e030607030c09090905030d020f0d090c05040c0201090309090f020c0109420b010531090b0607110303090627040c020c0f130e03090a090504 67
    0x111a0008011200d03840c2d1460600c5808889844041500c08000c02442100310f603c0010300700b070400a024103d03020f07076440b5014041c108200440042d00100a8605004882001503100ca05260081415025056aa821861030410000180b1108014020442d6000e44007003100f14281c1c8400c07420703606050005004683c1c40c01c01000900c51950005c069000c210600500f0014880c60f6039080d41d11411055440052101d00c298212600891000c1412028000da1900c0c0c00007032204064003242c21465140349a940002c450700b030340034034201c8400d1081e41da0010790076107450505c0c0078002c100d481c8514151518010100c1c03070285902c2440d400c4a4018099424540b00b07665040407440d4a141d45905070100b4006400c00303480d61380181450f0551892021b19091002e1440e248610503400050f02c40c5041c40c55072080b0300d0300810002003100b415900605540902004078031610103052040500e14640745208004050100c09060180d01c11900744541540d10f0b1080d030281d49040d076028 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 407591456 1250 407590206 407590213
    0x230c030a0515091b040803040608150a0303020613030c0222050723030a020403060207050a0b1501120b011710080c0f03070605030a15030b250e010f0507080301080102040f090e 77
    0x9441100d515400b110301c07a0340c2c07150130741c94a41c9807001341c1e045030000c0e4005804200c41c1c1d070501800f1813900c0101c50381c409046e5211401146181ca00950701c036005002980903040302c4040350285441814450002c54000d010010b81c0520b01002c0c9540c45840b40544681c28503280100b1030452040c40c2003480e4514041103d000c21200b0070400c4010343c005054030507415800c100000010f10743d400a0040302d030044018040c4082e0b02e0174a120b81c171a00030620b03c00340d1300d139031003404160703800441081e80440c40c06000200c0d81c91ba9401655a012000800480b030801c20040019240e25181910192107000003600c44092b42502440211064002159415042200d05200c201d20a40240da8491040358000c140c182100c006030501411907007080c1d60310800c000410015201c403810504200f0043e0000410480030300074010308400c0d0340b9070203504104d10b9101111380326100e0015203100c00d4105402030342d1395a45502941c001d622520400100e400f240c0c000203441040e500c11000c000300c603000074 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 407592706 1250 407591456 407591461
    0x90111030a1505041104061202040b1c0207061b020c03070b07080a090308070308040b1509010302010509220c080f0411010f05270a080d0c06230c030a051509 69
    0x102001d05182000e10366140901200000c03d03503501e014040e01d80c84010303c030a42d910f00b8072800070102a05196202246070042000b0410084e00804031502d400019500707200b80c246541051000e84600c210182010b420400d06942c0088501e00f800154040358088840d0005000189915840c49220700b032510501803000c403001c00c2c2c10b00014281c1044624050340c042d5100d548203550ba0300580d0b0140c1c0001c200c5010131080008010095400c82c1700742c800c401c0080c46002c00156183d10502000b4100000400c400c4a40e480d424000714101c0c040f40c8054030144d4200c201480100a40c100c4040098181004110b4858034031011902907600304a41e549000388131001074420110307829410080046c00c2000280300489240944020f5450000740041b1140c02c1d0300b0041c40c02803580040c4001d803c45140400b003940c111a4101303803143d000c040820740c4a1b2008800141c010103a0129070f48041d01400c1260006662001754400c0b14180410400b5845940d4802c0b08811010342d06504140400301 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 407593956 1250 407592706 407592721
    0x30806090615180414070519091412121209010b010c05071a04031520130603090f021c03080f0609040222060902040f05090411010507080f0f03070809011103 69
    0x1c3d03103800040040c201040c000c0c0031030102c2c41031180403100340700001c80110b66445d19a407400740c3c03d08071500380e19086c0f0310a402e001c410100c4460032011188070303100300070700b03007604d00b00c14040003483d944040c0040c0d4607081032051102d20100c0403585500340707502e881c2075141190301844805d04400d41140c010241642410150041c20300a03c24100c000e030018080007000852034501181c03051640c2002080b05a8195040340c4104200340400042600030301c030f054101d2800340e81d00342c05c4600c2d0349030104540c020b03070800e40c024610f04507029410540b26020500e50421f8968124401d0344a50780701180d03a03595103a58440040305661480c3c0c4000c81d00042409031421040b202810745c101071400f610b102182708081e007200d089a2182e40b01c2500840c0c1000b0031300c014640c48000348011b07218100c0c6458544d8070205411b01300040d55051010215811051240c80c01c1030300c80e01d02100c0c103819039500000401e503100703800c101c51050006644000282089006024103512071410b140e0280c119140c4a1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 407595206 1250 407593956 407593987
    0x608070e0103231207060b19030b0705180607080301030b010603111e16050706021002040f1a0708030406090611090f09071701030b10080d020706050a030612030806090615 75
    0x101c0c4a610f101e0b1303c880d611641e11084c0140303200780c454035001640550311014403011200e000e81e800c1c103201c14043d003080483c0c0d0440c10250b1010b290f10785159500c0c2017601040007840d10407030041d04030324042000001c101d0b07084000c5069a000d00c0c1c0c4414a40ea031240f044065403200e254032048624280001e034604040700e0244124841000613990400180e10340d50209107103030104c00d0300c4030b40c0003810030040660180711117000e02103001d00c2985841c0c101000e480220704980309181e5260007985003aa604200c55007179a2265500c14200ca5581c2003a041c460080c0640100650340d5914125018080142140440d101b500015000140380321022080110384c40004001c001030011891380c0018540c0342401c841d018520034040252241001c20b00c1e0058110703142c200340f020360300000c5210305040d00090102c00316989442c0c00703940d0300303040310044000c0c00701c1d0340c00694103014040380c200c20160403a409a210362001d0b01e60900c3e554403402004410380c240c100c503420f615000c000f4105c0349840c15 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 407596456 1250 407595206 407595263
    0x907031101030f0b271b0702091308030408030105091302030c090c090a06020a11030d1b03050f04060305041a06130504051504080a0801092d06080601090608070e0103 73
    0x50f00042c0e810504011402410948501c01c0200d2010f4400c1044800310700055134202c02c003080161240358100041e00c80070300c03801102038031903a1000001050074829000b44082c103a0300c02c51164517030802e032030290f403250801c0c021280f1542203030340003407081e00000703030119881500100100040c401e030b041403000c0d0b003c0180c240424800100280c07595504c81d105040c001300f406600400d410741160030140003003002150442c0c840d80001a07084542d942c01010f5000b50340500d2007001140c0802d140c280c0303c030311940c1600d220308000030400103030f6103070103505c054819402840d00d00b2000c2c6003081620b400b07000032100d642c3d019228040c0300c2e28000007944032075409481041250244603004181180030181141c1c200c445c40400200c401550754044480c900400d011a810b01c140c50280903011403417000070118a4880c5e55050080d0211842500904002c0410109440031035031910903001c007400850181000f0343c0325610300050705400400015049903041480404c0c04003000d500a01030100c3d1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 407597706 1250 407596456 407596481
    0x90c0201060305010c1205011403060106050f1315020f0703050d1b08070602030615030103020d12030213060801050102010c0e030c0d0309080304180c050a0f0809120f03010e090703110103 82
    0x7100c40120001d4000d100705101d80c070041d241c030200d58000c0038032001a600143c2140040701c14a460700f040c1c6450028210f4191081c908100c1d0b101ea5501803018494066008860101409040c0006150284007801c0700f002c4020f40c00c0d210b5042e1440c2065030380740c40c507103c001d1441d8099250030109031300c42c0b10210900888a8968400001152501d81341508035407020b036001640003042c42014a00385000060000620910134110762440d000a05e0005c5031000207001c0051500c1c40304403280c030036411502c02d03d090203000f400c80c0d1388031203005000c0f0100b4018540950700c2e0051000000d03003d0a9000c1c0001401030042241034084c8d814041101c903450300403002d000091401190b214400c0c000751018101c3c21480d0301101ea0110980801e4405201107081841801c001254400f80e0042100d0107102070350402402c15220103201c28a810394010008010100c085540c2640014402c0158102e89000c241c008041d110840031940700d00b179030320004120340842800e00c00b055001c3d400116140d083d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 407598956 1250 407597706 407597711
    0x405130c0e0f010e0d060509070f030f06050a090233040e0103261605150c07060902120106030f060c02060903030f09010b0d05010c0216271d0d0207080c010504090c0201 74
    0x2150b401702c3c05004240c0801c48043c0d0f04e44003000f030190030400803a8001c10002c040740c1d200314595100d04030600006640900501c1c0c440000920b80d1242e41c000411a45c5e028002c1c105019081174008081060f4015981c00101c4406011032000c0c2500c05071004d9800144c000d05007079213150380d01e1002c460700d80c41c44031501d045017400d0901000720002410524580d8600042000301030f18109040a00900b04404000d0700301050003081000c0c08103a030380d000c0d40003400044401550001900e0001f1101c01410258200b41700401081b00f85880701c080640321314410b0043c1c0c464914180e0311000300b1546000683e01c103000103810f01c4180303115281c0000c41c110001440304900b8003c902800071200003507403e03a446669000303006a0400a80068a490046c0d180c845400d00d688540351260110400c440702c0c403041c0d58800c15601c15480021002884e4084440c0e428200c000951109969410300025003d02840062249000715a035419080e05035955403401d401d225a01e00288400c1010740110b65 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 407600206 1250 407598956 407598977
    0x100603020906180f060c06160221071b0801021b03040501080f0717042102011104050d0501020405100e0310020405030a0b04050a0b0a06091d0c09091f020405130c0e0f01 74
    0x4603441d000300000d241006c007624540c6841c0840380d9556105a0807101154065420900c807050268096096212000240b41c0c0d01d011078148400120080d0503000d49450000e00001070790181540101041c48130030188000744480b0039480d64076809103100c0d0728049001400006e801d0f02480c3d4a20380d02000704d04248500604a458a41303205204640c1201c102140080103101c00c910302c03010301c6001142e403009000c2a10120440c0b4400e0180b80b00307040c0140100c4601e40208030080d0150b5001d4100540340c1e600001c0f8401c40144102c0c981001103000340a064a611240f0049008036401c0d0fa0b409401800500c2a5544006c0854401041900d5500840c0360910015000200d258007070509a0f6003c134146050a845d0300484029001700940b251881e240344142d64030107d8200c00348501155400c05a68031520031030b05180a040f000a0380600200000152000c1076014001b9035505071001984101480d41403811a08103402060200c1c0300c0080c1d680f502e00c0c00b642880455441854800002d1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 407601456 1250 407600206 407600209
    0x90e2104031505011403010902100e060408010203100311090c09060706110a03050906070e09010e1005130905070f0303051222230307150c020102041706100603020906180f 75
    0x201e000c2c601410301940c89000400c030f0700c880f0444110701001c044008114070380300b5a0001d41c24078900c00740741060115000c0c13402d50603640c010945000385000030080d5070780e18143c114010403541900080f40c4206111107181110b0070141040c03480780c039001c41000d15249a9030100b00c042d411a0401b15070841c2c41c2d8100481a074204005841c0301c12880e2404190383c24090350b03090030940010112402c0140c00700d0b80025036131341c083c03685044a00c1c481c0e0b41c1d200ca4a6521215400700f01d1a040140c00c8410310703080103500b50740f55101840060052007601e00b041c2c0c80f00d03020218003880748800707000180306101d800b1900d120136104d40d4000340196040d00c4c03003481e44011142003105102040c1c0d18040c1d034000c0024103001e00311031003442081e00302c040e47c5001480d80e034603415a080e240070740b80c00e90307500c0400d002501e001b58111400390000c40281685610700240f80c603591341b021501585090045031001030100d000b80240d441e2580700401150500f10b2031510f50032036070310302207400341c0c080d130040c0740100503 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 407602706 1250 407601456 407601473
    0x91f0b1806040e0402090a11040b03040615060f03050916031e150f0f021e07050a02031204150f120c0c0f0c0617070207050d1b0806070306090e210403 66
    0x3c010200c690165450a401000121400100f0340740760a07017001c0075283c8081e928000c4070b081e104401600d0752641c8442c10a80000d19803004468680c4480362400301e0790542014400180e9a044e550910466990303101060f20356401c1007410010a4210388140001802010085100403000385240201c0166841e91101c0240039102040c5140d51001000d000c040180604a0101c00d81e00301540b8101d04002e0440c0e00d000000c032031307248481000c02d584082140600041e20034a40080840368a80d82c0c00758034232002e034800c1c070030b0580782014002051081c60080050008a4800307855070881c1c1b041c3c0d802084003504002201c68100122680204c00040c200150712041900490b100040907040034800b51103a40c0c80c4000101e00c4c1a140304104e01c0690004080003526010782e400b1041244920f0401e42c4840314080700e1020008280c00480e0301000091818801c2a81395001d01c0255074400d5034004540f81040e016150742c000c802c200c00400c030249a0844602d08890849140540d20740300c1049 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 407603956 1250 407602706 407602709
    0x20c280c181503050c22060b2a060106050a0509030f03040305010b01090e061009030b130201020106050a18020c1f0b0315011d15030f0c091f0b180604 66
    0x101d8511a03403400c04000d180d032140c0c0c8600c1c2c0c003800103481103900315252603030780301051401240301c0c1030400306001e0709408001c0c1c0d1180324058903030140441ca494280080140d004251f04810000010401b09901c034040006078030110790880190900e6400c000086509902210229081c40b508000701e00d202c0c1c80c00c0041c1140c1c1c01100029617152819460400c1c25620681211410800c18080500c280d41600070340e560004006c4644411050b60b10009980b402606ea20181202c52138034100316802302c0401d0800e07a2140300340d00030416141c50b8820480309143c50300441c80a078030303020420800c1008130b50080c00c0614003107049840389403402c0120441d120a08540c1040c1c5501c038240000282000c001d510000320f00a007202030250b041610340320401c141030302c2101440900001140700c0100c031048166001101405940036110414030050380c4080d26100b0a010340303001800030701484218800c2241024803200c550030700a10b020240010381d04008600c0c8442240b4842909240d6a072100a00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 407605206 1250 407603956 407603969
    0x91b18190e0a0f1b03151211030f122706070804090f0c0c0206090a0b0f0a12020a05160c120b0f060409020105090d0f1b051003020c280c 60
    0x10110300d0b01002c018166540d40c2da000d0b6086042c85040e40c5a64034046002c0080c40341c910b400900364442040d01c0c0c01100c2ca6500c08494451104910010702c003d480c84408004019800c541e071014941e0140c0d60390302e880000caa9288081409020301a810100c3c04450450441c10804000d00742e0500041c000d90155a085910010000b01000b5664060046410b101700c004010000078400880103030040c10a0000244a100c0000702131030150780e91229100503011422446440c0e10005401410552180c0401c0010419059160000d00b6260088804101803951084d007007000204002e01a200701c1002210b10416501001c101c0303540329031020028900620100c0c04908000d003418000c000003038070721741c02141440200340150b60070108030343c010b20054603150003401c813908000c80f400100d8400203100d178030301c89202404074105030440c42c15107500b200c0107200b150300c0031419022032003021076810540d04900d40d100000349541130300c003800c0948611514100c880940e0b0301104217a5540244 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 407606456 1250 407605206 407605229
    0x30c090a0c09080619020304050316060606020708061510110a03020313051f0e030a050106030c0801060f21020103020d0e01140c1804020a0c0f030c02091b1819 70
    0x1e01c8001e0303000c041c00300240740c020050010b80c10030f404e003004d03003880040d01e00e400690008045000c01208008590f420a0a100e82503142e04081c50001c01034003191240c0c40052080d8900881c1e491008601540240e03a1041e01d418210f44000501c01e14446240d40344042c0b150501d0414007a101c14010340210503c00e078081e5030340c0d40030180c008601c2e105a4004034010700301e910b0481402c6007502e14401031003d1900b400604007030788000003450320340745040082181d4200f5400108200e2241a00401c3d40c405400a00030356842d00e2803c00003114a20440080160711a00c21010050810319a0f40441c010303d005480d0600d00c949000544080503038451540e036407580c410469205410407a40c0041d00741c00003604e01540b81001c0d942c640041d0103031130b20403980050f0a004540c010b0740008802e0b5444001451058900d041c054900303081460182e000e80b03c86000a044d44401c14000005a8050580d40f4104408c40ca44041942c0e18952402e400c2044c2018400c81d80d52440d51003001020240d506 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 407607706 1250 407606456 407606471
    0x601060801180603021809190b010e070201020c15070311160b010e0705180a1703041701090305030412030e100911090402100f020307061a04140601090b09030c090a 72
    0x10080b603544000000b0b441032802c03c0034401a40c0d101c0784c00011907600783c91140c02d17440e144a800e040c07120800030b1803402400650a0401c000700b0b01e40c080d04850200604500b95030303c1080a909038418184115103a800189540c240343c4803804209030030203034502e000640d0f005036031804c1c184c0d544a800c4035517860501c00c420300100840e8002e0325000d00080100d90750b9600b0b103a01c02030f2090103585c180300c100146e103401d0069140c0b58414000020140306504024800c0b5888407141c40f0346c0280205800441020080446038005000d5101029415507529296903990b454015019801525032001c0603140d0000500e20401000780c241108034142000036404150310700190b00012040342940a266114200805a5a03e020521100166050034002207020403003c03400d40c81400c4009001d46d2400d00c030b01400e816101c014803601241a1010041d54001800306d0100d4001250041d000600303a0303a0500c0490980c1c0c01910344544040c081b102c0c1e0030413441c0000d0081d9011542004015525a10b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 407608956 1250 407607706 407607719
    0x11130100e070f0525080703050702030f0a020901060809030c0709060f060903050606010305041a280218010e010507020603090607090e070c200405180f0705091306020c0601060801 79
    0x41c54100d2194203000030030912003000584039010b07400d20304054000b402456001e090007640551412540601407071b80e0390380207290207081604004010380c041c0c450741040b11008100007544003121a00240700050b1a882c0102c110342a00740104078508500007401a80b02600c4200401b0000c5c0015002c08200ca83c01c2c000b40100c41ca411350302440c1001408102000402d0001c240316402460071b180100da55590340c18982e0640f4130221451101d1090704081001c0200442285d010307511040c912803c1d4802000e404000387d0040d0848011b160321400c102e0210f642c0a41032001c1005010f0400504040035900003a050303030411110307a20680c2010040055080d0f020081030301030400ca07010318038a402c08581c018540c1d80c4c220001440c10f290b402000c4d1544040000da079509050091060041d03150035020095003c28a01d1740141c90711031215003880c411800700d204411340e1401741040c40255034034400d8585d007684012080e43e51aa0030803045042010a1010034040c0140c0c0d11100d5582d49001c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 407610206 1250 407608956 407608979
    0x1d2b0606080f120f0a03091a04110d050312040203070801140f0105150430060e0606010e150f1e0705071409010306020c0f191401113010 60
    0x4207070102a0004460700300c0802d40a4181d038040c0c8001010645c880485c00740a034028400030f00040c0083d1080314540d1104ca240c183c080f07210b14480c011350001300030314606108100e018094000c0094005000d800c170300c608641700745039000d80028110b54019984010103401c4581d11f00700300c11100090300c100f06540f040c0845881c0140f000b50b0340d518a034012a000300055000702c0c051041c030407075204030342840700703924841c45880a20700244400e1301e07051911301480104503002c1c0400351800340500040e100e601500542c100c40101604080000700c0c0b00740c0c0c8400d5940407104115a00c00b0500150114132414684601c1c448040c1100990f2211581081481d20400307a00c01c01200c01d036219801400c0d1600d40700641140e45c0310a0140e203c1a00200d9070741006201004082c80340b0814105581c03c502880100d8078081c040c8004044480c50307400141d0903290740e60484194204104042411002c5031503202002c40701081407003030707094400e007590001e8a07002c0d1030394400c00b80500e40c184811110b45 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 407611456 1250 407610206 407610223
    0x60c0a02030c0901030803190f0f0b100801030b130f060501060801030506250e01030b1503060a0e06031b0105040305010e10110c060103060b0301020c0102071b061d2b060608 76
    0x11220f1107119031455503840c03014480100115042100000c8a00e40c0a40036040264840702440080c4a80d459010100f4024074a0010381032080500c40424885e507806607042c207050740e800202009c0c0f0390b0354190f002401c0500c01c50044604102c51800c034000b0500a01c180e5019000ea0754a038401da52540c00d21070724203140038090110138902000500000c0c0c0280340c91003104000303404d1140222941e07000581c001c00c0c64500b896002414090140d214002400055100c6c40d4111200aa40e030b48a40308802c050104441141d0507610a10140c0c2c803035071030607814102501c4140b40040c03906460b81d50780350a481c3c0800d010360701c2d40d02070071000c901d5505900035840c25038a1001060300340150150195901c9006110107803d00d0b0391128855550b40b020b4040300caa4000d00704c000c0d996010245018620034500d4078110600c18000040881e030300b4800c05503100070010703810810820800780e5003000742c1c0341070b204c1c04072070891400c070210000c130800b01e0700c440c070000d028030400505145400034903030810b4080c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 407612706 1250 407611456 407611459
    0x190e0906160503061011011a10050a0210092f04050604180308180f07030c0f0608070809010b0907050c0c0109080304030f14070b190305072c060c0a02030c 68
    0x88121201c0150751010550713510000403a08460350301d51001d0140c40d0804d211180748115428401080220b81c120703811700180c050290740361084e040c254001150b450248460303000c0160083e051802c0207031695004000d600380100a0801400311002030400958141082900b44181070849a119440d203803084030b03481101a80c0038000e508500d1106002103403007600c02020f01c000c14000c950242c0092400d07400085000c0100c406000400e41c0d025a100414071088840c400b12110204016000ba0740b00130484103141c1b5080c0c030585507840f00f03440d0420000c0004100350b5030b40300461102c0c0c0c0d17801006805904152241c07a954a00c005895040c800300c1c80c541410310009002c108016a00001203400302c98022031580a40300fa07034038150f500035802500c00074032841280c1c808100068004001e100c4a074005d5507030f07500d900003141c051b03007512401c42d6000f0225084220b10984544110003041c0301d40b03449000600c03285000300004030180c101600591060380305040e0b010441c182040b10a00c7c0540 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 407613956 1250 407612706 407612731
    0x18030f011508010c090e0705031807120209100812070609020d120e03010c350f060907030b030307030509010210060609050a0f030b0a0b0111030d090327050906190e0906 74
    0x34003c00d00306c0e8040103415002081800000600c81070803074131281c45150600710690703003425035070240c2c1c503081481c003201613204c2e10951020600840c05021110304442c9007201500074070303509410110300f40c2c020307420507542c035503c4040c1d070001a503805d0403210003e4071882249629144144000308480030b25101c15000b80c1c0f60801c1090107980012461000800e41d59201005406440d8060b412910324220070303518508040520070000e80c41e80d817082c0700d80702c10348035440d096444205c03c030700765046c484242d03400d904200001c00200e8800c0004001d45101030045403910f00c0d9488080040383c515030312800c00501c40c00703002d03ca00e20f1300e034860300000c140b4864034003041800c603143e00203444000b03462400916a0b414614030310364040c2524800c554481030969071030354091108170019186542c011000601c01e103005140d0041c404503825004607078010940704c81d030305010600404060151819510401c1003156804c8920303a10129000340c000c080e240289c504103d40202d1804c00003514100c9c0445 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 407615206 1250 407613956 407613959
    0x207090e03120a18021c060f0b030c031b1923040e120f0c07080f060618041109101205070312090303080a09111c0309080f0318030f011508010c09 64
    0x9072548041343c1000d804490511100301240121100350102c2c010061500d410031030f48950700c007010780c404e5144100035020f6903040f407140000c064482e0243c990082600304004840841410700801c01c4c1ca442c5103240800a6554580c113040e2a8983c9454422084004107444680c15041078043c824040d5480c0e00202009204055529120f00070355a6290110030041515141c6103410442080200100802d0301d032507035800050b540d116901120a94060810702045004035803074107150a10441c0c111850403600c0703030014100f091102e0050400240d80c0414030340400c0d4140825410708200c1c1c424402000a9031841ca002498402a1401030080c030220620800c00309030030007805c07540201030300000203411079585031042864004408980d01703c5d030000c11402d0401c98108000c02a24082e40310400003a41c0d0780500781e038a04007640300c0c0c41c0c90340042c46505a0303005035049800c2841030003826514000e4400700f5003400c40b1182c000d44103050f1801c82c01008034040a11070705608000034940b002085 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 407616456 1250 407615206 407615231
    0x9051e1c0804081308060a0608060c0702010c1a0c09180106020303011701020f070609140703021e1203030405010507090602060705040b0f070f0b060f2209030207090e03120a 76
    0x2803204528400c1481480e40c00a01000007040443d101c0000300388180100c0382d01c03000c0003659004129038072030a0303e103088000308800f040050664802c0001c03000c15441d00300c981d4011606820061011510321102e20f0203056a0382c0a9005507114404a020071078071464800b08003c10704d400701c415070700c0000c0e010006100e41c9502004a0f4190380c000711410b80b020001c0d203030103030080c031a9001030f224507034001c1910003c00555401c140da040740100c001c00d110641145200b07484400a1000a52101c10602a2400f081340448600b9020a00078002401c00901c1004541580c3c001c9074101e4480e5076450400103c1500400a540517100c21320050001e460101c40140c030f244100e00904074040d00110700444900b0b00c10046481695100c0c151a40c21080d919040380050b00a81d50680300d000c41c56800c01d154105444c0c030300385181e10003010b04d420411499078030001b407460000503011402212800f05022046001d024421103101d4000d550b5011115503034400701e00007401c030300c40e103c0c103001c10700102c0c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 407617706 1250 407616456 407616493
    0x1080d14030906180328090b1201060e06090a0b090a0e0c03070525030e1f051605010b03030a11013e2703070f080703030f0309020409051e 61
    0xa1030a04c0c00c1c0446118403009103035005000d00c4d40b1100075040301010f46002c0341542400c04020a4540410060301c0c0c02c01e242190182841c101c9828000c1c2d001005010320071071003003420340e070050110340c03074071030710101003152061030380c100d07845080700000c00d4507407030501ea10000010145016400c1d01410703d41200d41c0c3c5d07071001800c06010031030003040c6031246540b400094950b802001e529082c042000780350140004001644c914810f00310803a20b0740780381061803088594589269612454042c250550030100e802098040d13540d07660701c5881e100c03030351030400042c0803c40c0c594403054080003004001c2c03400e40f81e000040003640e021030f003d81c14050181c030004240c1c0b4034400804503a48601c0403d103605d2401117600a21001c04044140034080c00e010701003403032100080e001c0c1e56070203449901000c00000c03a4460111568810102080400d00c564405c5585c20740901d00400c404100c1e03000501640c449071404d541640115900f02d215002034502c0072200550034018251345101806101c10 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 407618956 1250 407617706 407617711
    0x6051f060f0f0207090617120306031213211709060910140d090c1205070b070c090501030b01060e090c0d090312050a0b0a12050703060f020d0501080d14030906 70
    0x520050111540d150b03802881480d01401c2040c60800031599a0200c0b81c81440703020400d0b02550281420b0003180542c10f600300c910480c0044c1c0240709040c1095030402143c1c1c8400c0b0303106411041c484c1c010803201e06240c0c40d0224110088004096001241014040c51420200e540b840c2d20080181d0451911094140d401c001011143c030700da610400b0506035040c0000000f400b56a80b40043c081e460024141d020702c0c60709000301c9480145a850b091005d03a5135144c050046e1203a8401c0208014280c502d038001d00c846449070003400140c56489075450180c3e0000e03001100e06079500801440244c0c0d01401c2045080c508641c0000c0b18100b0701d034150030920410720109112600d401ca8001454090210103c4540d440b00f0308101d245040c00d4040018085102d149100755401900091081580b07450503624540050141071132919503954400105910750420008540a010544c080a11031091b98028108030f000791041e40e4082100a09001c0042c1148a03191001d0040c031078044000120980e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 407620206 1250 407618956 407618987
    0x30e1209010f0e10050702030a05011b0908150a0905070b0703020d030507031e05090a0b090109120212030c0d0902180708060a0b070206091809160603050c090103110f0706051f06 78
    0x10746d60402400820300f400c0103080701800f65030030700b41c03080384070711611a0300d02d203414241d66644055501c0c1c1d0342044e200e1914400175016410742c4404602c11580580c009240c07a440f0381c003290041c40d668092405650894141070300503800c032410700f00400d070705400343d0780d40301080b86020400c0720b1168040b001d0001d200080030790b940d540c0d1000104a0202001135410803608400000c05a01e0f100c041a4040c11550004031441c064206a001401d400010718410310654806098210356a041581c0c205810007110f1a10b80c58a460382c000240e1943d035070b00301c0160000c18460f011413074948806400f0010240c0154024000b2201c1080340a46a10517603421503070441e1129521080c0c80005494404040c01800201380880140b01c081c401c005880403000701900c4804507404d590b250280c04444040358551000c4404200032507031ba42c402ea01800d41c482d03440c0c0f0740d50306040c6944254007640c1c10499007142c285176910306002203e018403261142c440c045c02c2c2206c960a003000c0380240f40501c07401560 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 407621456 1250 407620206 407620217
    0x60310090303060801020f04031202010203010e0429040503310b1c020309030a09060e0109090b0a152d0e06181903110d120f030e1209010f0e10 63
    0x400070903100b904450b0040400c01d000f5903d410000d2120b41d42c642c040c1c407088900032176100f80c00740c0300f82c01802503074102c0b0b0385160380c4102c5540d42d85130002403440040000da6024218000151541c0454001c01c1c0114003c40080d912104640e00700c100415580074408480054003d031210b0402d0350b50316034800d441c020440300c2d4131824800361401d11616804400800740d800401003010f11540003001e0264040039a60b140c0c00155285002d4848d081f102e101e550000300f0381c4505100104450300070074022880542410701c00c40c1c0c5d0b484180380290007034412100051405801d150740e0281000d10307400c20940c8061921004020f01d80c050084035114681900035440802c0000340307141e8403800c25288500c05460850081101074030340f860b801550100310313000700380400d19602c50304000034010b24456000c20480c024082080c829a4070140c5041110200341c1c40d004102d48002d000d006519409025a403002e484840c0c12002410f015800740c141c0c4100b10b010041c9030016540d40004554070107203801d09 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 407622706 1250 407621456 407621471
    0x100509070611011103070323011a0a050d091b08070503031b0a0606090207020a060503060307030204021803100b270622090302100b0a12020405060d21080c03060310 72
    0x2e0901500c030552480c3e00004020040144603900740e00140519224081200104980c510100e6a800800c0c0030303480c04503d0481a08010901c924002c003d291005d00b015410001d50707140000c140c481a54080b10a00bc4050307001001030481581100034000da07602814400742402c01099583c0a880002c590584000036079036240c000a200814002e50031800c2400700341e032210b180da030181d4410841280214801c2c0000038129100d681038a00801d070007070140448524607001c00010f90440300c500b44448a00300b051001c203660800400384203d030030400104035640380b84200203800e000075141c800e407410780c2c3c01d010b0300800a201daa107512510443d0300815005560444048c1800144a049030b224549100c48080c15000144032030b401807888814070450041d841444070308030461045c51055114402c80800529081d0040c591100000c0c2145080c0c403415101d8410541ca001401c4000c0d41d4152201c0c039449038000b280e0ba130b210004102d0b842c03640c00e0074000310b03544001e51444105040d03035400c030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 407623956 1250 407622706 407622737
    0x507021915091e051e01020c040f1a04090308160507020d1b0801060b0703210507170a05040f08070213050106020c1c0b18030d050a0e1005090706 64
    0x250140c89441c0a21645100c1c05002500d0140503000e10300c9140207944605591042d0442c2d00b509407000580494002c030349008000d002070700181415070541c000d003170000310a5102c0340f18842c0700122101010844201040300c0021a01c03503020000d000314100b4143d5030201b90000e103600d070490314036444180c40410b0604122010300030084000d5010361036880b0f0b1014020300c001070307006010079000d001110030f0b914450f150881d2042d224454034038a09000e40350101e405403007034169007101c0300c4d20302c0c06002c441300715401254800c54080740468072883c010117011089450003a40411340440400050915071580d680708c2981240041080303000080366421905c92001600d46210600d41c144100d5071a804060344600c0d1422071180aa041d05800200c6000340e44601c1c0c0c0320741e4000f5141c0e0500d48032440c0010351081009030841d5580b0040080b0a00d4400305c0c4500f501c075010620340001c014106158071410000c1d41403d01030124205800c0c488070400201c1c2c40411140c050909501d0301c5200c25 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 407625206 1250 407623956 407623999
    0xa180506092d06030a050618010f06050901050d06090501060f0518040c031409010605030f011103010909170d020406110f0706080603150112050f031206010e0a09020304110a06030c050702 82
    0x10a0036001000131007403001001aa400c218014102125840400d03000e0000314401c0d108248100d9518811200c0100100c60051004240800042c58940d203407080c46403170082610100d40c0034590070759840f0300400032103602c40031140c1d100d00f041c50828540020f21070790207086492203080c64420390340c5240c00a00c0b0b41c02a800b04920030351104403512585444100c1c00d0003482940304440c043d0041ea03502e070400d03080612901e2400354079002c0140c00c507420550018020042290101c402c40c04891000341d44284400c0a03204000c00131601603a01c50400000414003c03224000c01a11351000c010300500c200042151010341d041c514085030203540d04000603240203c00910f03a41189d0083c1c00102e00a2581c0305040350b0743e40034070b08440852031007400300380c0c2d64400e003d0a414084a80008a081c541c401c8a040b0381001000303202e001c4403a180c009031401c99005035412564004c12149914250503c06461001000e60341010014a0180d40d4084c0180c071407560000d102380d008012295448980d00d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 407626456 1250 407625206 407625289
    0x1104020d021605060421050714150c030a11091003050a1113151b1212020a020307111c0b0a0204090c02060a0605091504050415020a18050609 62
    0x114000c0b40800c89401c180d0b403103503002d0380c040e1104d03000d64566102c92050039003a08604401540c585107400c0342c540b2020000c82c1e003428180464020304080300240c00704400f11b03034000e843c40c1d40040e40d24100302403c203003210441070b21110f40c5c00003404400f10666801820030b005aa103401d0101d4540c0d03821070898014448000b121006034000f141040343c217090400d174034042d598000100c0d140e01e8404041503401c2211030012101111442e034007140040c4c0c1d143ca910701b200c4518200118400b101c40400300c03c2e6007121030000b0040c0d10124050007070046490303868400c4102543d0074110300e10b10700d1461080c010014005403030685008041129050241d04441c002d00300e4081c1000030088212001b502d610041e2020b8280a0800c0004910b41c0313410240c050145030b510982c481c02021b42d07800c0c03201a060040007903c141d0b041010012100010740001d02480711150b0340c0e07007100d04800b0501e00300c1184a40007180501400e12900b00661101130b484007240b018081145421280d080c5800c403146c900 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 407627706 1250 407626456 407626477
    0x6162601091805030a09060318020a150203130617060123070503091c02090907060e0103240e1006020105010b0304020105070516060c0209070509010c060203101d010e0709031104020d02 81
    0x145c01aa400c0c0e005103110f0581e00c45580920602400009085c00c908040002940c03007540450204042e0106a52a506e02d2201d801030320b007401c651032503003a26460254042c3d0040741242c2e00c03540314407540c00000d50b8085400d007041810007512030004101002c9590750300514050018030082403000400c151100740344010042c184202c422440340442504139003040380507603240b00c04105180070109200c01920090b99a803c40c424480380118090039490300003005c0117001c41d050044081020ba401e0010b0165280740750f20074104040c070340180d44003c1e8840011645040014802d101d500b0007184d8000741c0900e042c1c0e45400550408500b047c03080303403101040114000c4000f42842d005581d02a0b1170780222401c000507610504140c1d214402d186003540050401e0600c0340c001150f907800b440d04051022142c295951700e1f000d100072114813072404080102c1c040350040064122104503e82d0010452030184085851651810320803034000304000d11032034011640000201c0c860b415503030348054 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 407628956 1250 407627706 407627713
    0xd2f1905300d0306380d02030901050601110a0b1602120313031202070206030703050405070510020606090a060e012903070512010b130902030903040806162601091805 73
    0x14448100b50740c1c0c0036440015000ca400c10100213008801078080c50070b020000100d1489040d03000180302c110200d01034405851010601488001d01c41900c0954861a110800020f150401000141900d481030b0000c0a40d580304c00d01000c000381c0d5456607980c001060310140441d201d019141a402c01d100182c5040445001104005102d0b1803e0b4086101a000e0307102d4801c40000790f41c0b214142c0c0f08a650107904640c0c204041010b49100758003042e84180100259020140c543d4005508c0050040c800001a40a01c0500510f8507100c104c3c0307a0848a1084100400380ca481c4d41541d60400500c544601d050f03451305049100001e100e0818104015250265a00d03e41084090501d0304031040c00d43c49010032400100e9406500001c8890312080c90104035541440c0903a540040d5000a000d07000c0c9000a100004200d03070700b00036180c0104c820440c070709081010418010520385809014590f40303072034414030b401d428411841d4641174030b088900101d800c910400c2c0001f00d007411140010704620 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 407630206 1250 407628956 407629039
    0x3081015030905030d09230321180f0109020f0405070801181b09031203050105010815040902100503180303061e0f1f03060e1902090d2f1905 62
    0x7c1e121458603000c0b1103585180130245079600366a4010018001c43c207081c2d803094940d401a04076116540110a00b066403c0068900d00300307405d216031851600a81e0b03440c0c1007881c00f14505841034a49180c07041d941044a8541010010004941845280c0000c3d440740c207400111500c80d04520608403c0c40c03142d0600301800c200003420b41030203100a540792801c3c10b8552000300c1c03290107000c0c101c80050b5030340c1070140c66a01983c2d05141d403610304290f000360785020100050f00d0b107003000a4044843d866503512450700e0003034905414659081c107201c03600104200301e100d56030310880d2010100300f4525201202460004691340f1240c4800d407586c840381840d10020400030f40405865082642d503002e1240e103075034184c0320078182c00c140c0701a00507074049a80410585850750241001d01f4000301802e0020382c2a0b12407a414214a04080441c403000f4680c15440c1020901c105507a070005640912402d19440c1c1707410540c1c556406018401c4107195008411040b5503440084400d24548c140003400 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 407631456 1250 407630206 407630213
    0xc03071214070c05010e0607020a0311010207031a0103030905090103030f03020d0b060c0a0201090f1202060c01110c01150b030c07060f1d0a0b0705040303081f03170703081015030905030d09 83
    0x400c0f0320712482d40003038072a102c20869424008103689001e50701408070304c09a811665a50007400380501000d0461003194030000116080d09a25102541c1c1081c00403802e50541c00e00a1207050580c2003036000390b1100300100000381e480300910710341c591280340040e251070030b20401c03c01503c1019000c640c0200c0118071042180e1001c40d84c005024800d8a40074455035403048000300e01c0301140b1811018905960380314015050040081800c2900ca000000340500450310115a6401c150481c0d030b11607648105c140c590584400c4284080d000c1161440e00f14640540981594481c502000340b0098560701d01c0345d076244c0da5400102414016a40c101088122410300e107581304a0b407003040c3d40030b0764200040303030310716000701e04850a407601540d440b01165205107940c0c42100e4840494661041c00c0c007000400700d46100780103200b441070021065a524050b0600800c00c0b100070307241a18503054110100301100d142d01c94088001d90b142008581040141001070960060403094001c2c2e03800d001e40030b401c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 407632706 1250 407631456 407631473
    0x405190602120c0d0f0605030d1101020706060b0301080106140603061c050718050105042a020f0327041b030f02040902030903130603291903030f03060503030c0307121407 75
    0x20b0b08415042080030051105d11141a10454810305405810401c00d41d50aa0321408401c2c158018070b40000d4a0603000766034200449003d584190f58050021006016085003030144600070321000441c50407080140380050624130000d8034580c412181960085100c1080c07400f0104066003090940d24003d0341c45c0351441101120010005801c0c1c5400000b0071076180c20300c81d119001106040c90707040040404007500914103490505420751180c50081618004100010203601c03c0d0260b45d03111403207210120380920b140d2981e07001c0c41f640c02c1501c3c04c02c401b0040c10306101202203a16010480301c05e0303110400d00a11031508103a0080d80004200104070000100514142426000704a800c941c1c8540480c21111001d0307081004252404501030300440c13105010071042001002c0c9114203502200c1070780200200d51044002c10a448100c03e01d003034051281800a120a402440c0703400b000c19800c0c0d4480c401c04000400ca842801c1d0b4204482c2e2080704410200f00d071540d03210780e03075074042c2c00c24502 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 407633956 1250 407632706 407632717
    0xe030903010b0a080303060607020a0b0a0e010905031f0519060b04141c0221030706050103061d2d0f0f061003020916110316020a0605030405190602120c 67
    0x25820400c0c40c0d107840c01c000c641c0c8070413030b40303c1400b035401d507100d4500b0005107610800080c1da000d0030036080420300f0002c01c402840020f005450f28a040403d200c00900082002c0c0e106034841d42101038011314004000300000b0b0100c01303030100001c20341d070740c421462204444402022150391900b41c1c0810900d000700000d04c1030b02c000e000b410011021110412440307081c0c00911610326051586c1810060805a400c40c1c00130400c0500c20f0348150041d03805614503040741c00165a4551560010400e21441d40310354000007001b030740c60841000c0d100074810b94580360102880b404295001d640c420090001d20320030030f402140400c0d1120340b01000005652407840d842840000e00510005c03c82841f8683d1503a01140d60107041440280c0c2c1d02841c040d0341d6820f0764044401c2c020404200700e071340c9a00b440140081b074403400c203102d90020f040c01170100e6040203800080605c1420003d1201040e0005008910440510a03410151130300c3d19003280607001d002d03810b100c80e06880046c8112940304001428 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 407635206 1250 407633956 407633959
    0x11040302061e300f060105070602070302031623010c2c0a0608040b060301090201090506030a0f021c0b06070506130302031615051b040b1803070e190e0618100e0309 72
    0x380d0ba41c032031003800c01d007000c1300341d03401408600308008500005031250060107c0034040e0060f00d00705030f81d269030380b610f5808c0020225100c08228070000107105062400b0804961400001c0040700b550800c050300b04003282071050345c84980301c0c80504e03080c40c400ca2104c2410f400600260001c590340d04000d410b1203029202228400350b2035000403220301f014450f4165498050350b810000300d260109118041d44060508044c8503262a028059400365000508100081d0380103002c03154010a4542c08454210840d50f120304000c01c00c42d404640002010740d003001400320030711411200780c42c3c00d030701d584180201e080f02809410745820602c050703444030040985404d4404c0c0310950352016108001b01245074610100e10b000d000501410294a01070000302c000d1010440d1303003588920009140c04e4460b0720884100c2e40301e0301080940752001c1900e240c0007007482c00c24044080240c00300b03a00d40348000e1a0044050f841414900460300c01c1000d00442c40e9001410800000f2544a2640700c0d40000d40c0035 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 407636456 1250 407635206 407635297
    0x90507080106020c090f190c0e030f160b0a200c0a0b07030f030506060d060f140a08030403020418021801030b100b1e0408060f04020411040302061e 65
    0x801500104d100c05601c0d100619600c01e41d40d840ea00e9110240c0c01030019a0a084e90241507020681c140c800c0b00100c124544410700c0904208040600d440e410001000c201e4203c1d01d8550301d10720700040500c06a0307031210744882d103960030307203034220f030404a00c0c141480c0c2c208050b10584040c0c0c6000c00c40c044182c00584681c1d07203603912004210603604c11858014000b4010881820941d8429802039802001c002d111902d445061074194042c1d03a02d40d0442c14000c9038004042040080910300a54001019621804001d103000f13480c0307489018a100107130003181c590400011041c403884c94681003aa004001601d50100950040142202404200c0e241034009001c60802888a07100320102d44e540d800e070074504401d400701d200c444020041c4032162a42c081c040031604c04c5040c03000718030841103100525242d140c503004000c181c4512946110040310200414000358407201c1c03c4501510041000e10440c2c1010216486144074065840d1480b4004451350008078460005048000c0c0340101c02 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 407637706 1250 407636456 407636459
    0x102190c1d0106020a020d0c05030d1106070906090e101a030403090501021207230111030f0a0b150702180a200a091802070503040906090c020a0302030412020a0801060905070801 78
    0x1c02184401c00c0c024074015a1240f2420401883c008243c141310b030740324020f401e103110394800c0428a00104402540041142e0340740c4c88095203405c04c180c9601100900c4c160007102e1a141024000b02c0c040c0c01801884041c20300010310003405d40101c4401880041030810310240d541c0c01c0702d4070395041524110b0015142000006896100080003c00202041d2800f490820035980b048220074180303111100070303803040c0c0300804046800c1c80b0b00300d24480c00d079568558a00c3c11000071860032400601c4401c04614100d0040081d032207080e011405d2041c440e0305503030342d840b0720f0000504016030314640e00c5a41102508126600455412500101c0d03420720000304203210b030320b960309510b0003400c10420008551080c100001000d54400d90180903025a0061030611652103190070756001d81c002e50f1a55895a01c10808840d0078841e0010715034403880a803000c0d003d01e0b50020b44a203d14812061207400c0b040c0c00c0400d558a0a2525008260880080005076980c80119010700380c122290b4000c030380f51030300 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 407638956 1250 407637706 407637749
    0xb090a05010b090607050f03070602121f0e181f0c05030906070e060706090605040c05060c10050912040e01140a08060c0711040e060118020f030a0b0102190c 69
    0x40d19040c0d611412105080000d0362007400390581154405484074490400100c48180781800246081030080c100545c1d180e041501c0c0391041c00014081444c2c21281440c13442c0c81e01c9800783ca1200b510300b000d18030281921030001148440c03240c11100391940c0124000703c000c010b02010824440d100011050245641d450000d41d000d000455405441d80c01040002d980c03148243d1074440b008a00078040380c14802291100003c03a10354074801c40da5256208240424000007582c450002e103012508c5625141010403501d0700c07007012240303500d40c96840d40081446854140920958900d000b2103654807580d0391006400e00e0340c0c0c2889022721010701d91449054605200c41c0217030507101c04200800c802c1d11788d18070a0320316900042c0c06a884a4441c101c85031070369070354060a20034140b5000107200d01d506101e0b07000301518020400e003200703a01c10020300004000c1c4a054942c811940311001501d03107441001030b8245040d00c034244060030340400c607801c10020014890f2003600d50a00d031006031501c0140 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 407640206 1250 407638956 407638961
    0x1205010b0a0512060315010b03071715310f0c050703020613030516030e010305100522060e090a030e01140409090507080d0c0b0901090f0f1707060b090a 67
    0x21056800039400304a0304041e43e05076003025800450160032544032000302c0c1042c51340490280c200c9070080300000188003100d035100e000240b130300e14442d903030710964240500c1000700c0c406a43c484034042c801448014403440c0c011a8203240400114503029030049180d401080202048606d101c5050f14003203080b140d4500c620309884240b507141d00200120f840d204642091200904070803010072000f00b04d46a10001400507003800c2c0381c400c2c2c03101c18a03c3c4000002505032080113100310004011010100171582d914820f07a4040103440c0ca4020400f080c43c03142074041c1c0540d401a100210009090229040c00003070040f05032b40c080d41d00c4405082000c401180c425604071041010140705100520100b2080e900000105100e00c04a4001581e00c142e03d506041001c2d50f184081081c445c0941d09010101d000154400c0880000700329042d541c1d95070103480c11840c003018081000100c0e4a1040103940c0750016090007d00c01c482d512050180307440006000c0e815481c601a0380a003005c102100081d0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 407641456 1250 407640206 407640217
    0xf0605120a0b0123030d0e01030c111c020c030a050706120204030b0105061c0f061419210b0108070f0801051510090f030b0604060b0f09060a030e0d1205010b 69
    0x5003034260f64600304000c080707a890106600090008098501c1c40c1d07603802c0140b403082c60002e4039010202ca51001c009400c40380203800740070034818080d142d50202240800c01c2496451800100f0940c8800700d041240380000c0811034a405200d141a048240000010300804554071030791051800c040c40d04940023680298400100b00e2403000740140041d190000181c000301141c0055403a038100a55408806e0740d0600b540b041003e0390303039103051000c803c0c0d071241c100c040fa4080e2100f5000341e1b04640342c3d5060400e01e10400040e2030040078411040102402d814803400c0c0c108074111100d5071241241030300d6803841e2040c4508040d80800006005c4011700456103e801c400140f014101e030b40b0400d01480d54001301100003000400c0001003518280199148003a40c0603c09410070351a0140500c012034100360002c4211090500c01102c074a1180d20440c1d83d00d00080e103c10303031605c1c207100d01500a41002d68400e41c40b800348048081150307612852a0840b00010a0140656680e450b402d0030310b032146 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 407642706 1250 407641456 407641463
    0x706020a03050405100c060218011103070206070b13020603010f08010b0a060c0b0a0e030a03060807060e0a03061e050a0b010f0e03030d0e03120108030a0f0203120406050612010f0605120a 82
    0x6103c1040180342038840d424040c2c004e424400d00070748145d40d0381e9049a2004024011311080c0804040c11941c0c030144141e400c1c546140210b16001c501d03000140b141c0602140184459510310018030000002100e29402903400b03001d2580b69619400c54180c40b00590041040c0c039031902c40000381528100e0800b004942131506c50105448003629009584c800080185215548038024139080300c03c100300030310f00e8966903070b030020b03016080c541c0311401e09000d41d01440410401c01c0b20b030000c0d9550042c8038000c80f80d000b0400580c040340035041042421f00710041852091800d400c01c0b14001031a0041c0b01c9036a800da80f90580d4000c504001e95106100d60034143d01a807040c0014500e451082c0e000c2901c9024040841e810f240304907141c0d629801090b04010910b40001c14441340c203c0d08843c2c0b01c05880942d0029505100c0703074040110402d4002400a44500c8d2a200403480c103403503030a1030784070003500d236802441101082d04080001d400648117150082040b2071004609000109020041650 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 407643956 1250 407642706 407642717
    0x801030b07050915220b03010605030f0a110304030309021c0302070513020c0607020f1006210303090b0c092b030f2105040b070513031704090e0703050706020a03 71
    0x7201a01112542c01a45407190071444090000d0100500080a031100500021032011003402c0b501d60360032000c0403503210300d52401c414001880102d8021045d240d1080c104040400d0f03680c0d031000903402a0420448640c11901e00000348414958550400b000075030003038901a002002ca503d00e0f40b8075141c00000030380160000081804180380c00074114045c00c4d90110302600740200221910304140c0240d8045016a01200314002c0b00c00042c00302120585486004200040c503020a142140a030028001056011800c40008040c02940824900da03084001c0352030b50f00d0400b414601c5540204a000d1040310f107604020f03a003504130050700b451180100f82d80c003110a00c5a8007541c0c0c04030441911401d00c5001104162110740d80741c100c0d4070254854034041103508080c2029040a04041c041204010702041440c5414070041c5143c03080341c3d400751101d038404810b0454400e15006d580c001c00e0340c49003056210075410a0020307a40051b00d0180c0c0950340c00c203a44030300507a511440b885c0000c0c00300780c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 407645206 1250 407643956 407643961
    0x10e01080a020a0507020603010b07110604032604090e100f0e1207210f1d01020309120c0607143310030f1202070e01050607150e0307080c0606010801030b 68
    0x1060703074003d4001d5440500b4490300380701480d0b000030b050750401d8004c8883e003400482d210051080c1d60500c450340c85804e0320b41d149000d00b1600c0b1411050680401c03d43c1041048811551540000e0125002020400230410001c2c8100c0034181d100c4550740c0d00c800c0300c54200300700b620352110070703209007103030001480b0040030400c13154400c08030507401c68001a00e40d0b000a0071904210005080b003100c50302c0180d0b413200340c0341c41e0149000d8195910b542c007295215944800400450340c0020031542e503100202c035512200d0700c02c40c0e09a80b8007200c2c800c0c81c0340c0011020549404020381404003078000d10f00101a901b9120414541612105079000c80c4140f20f107000303020506182c00d8140c1c1603000440b000034050500c0d140d40b40c00301100014182100c2c0700360601c1da0721031010b07818451800945010241005194500000540a40500f40015001e030003215a41c6080f281c9940c1f00641c2c08550005603a107410007424140e0198102682010907801550f0000e20300f58842d4190b0350691b40d00959944054 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 407646456 1250 407645206 407645221
    0xc030729090105010b160609020a0e101a18032d070905060d03110c0d0f02030105070e01080c13030c061110021312030509151801020c0d11130507030501050f010e0108 73
    0x8070300b14003068640075503031888c10300542c9030360440001400b080f2501c030314142000c028030342050820703500c00f1070703c2074008512000c890583c1741190350600721810040700017014040002d007081c1d100b0398404403074200349200301c1d43c64280c290405205c00100e0280c030041d80d900c002c0e61007511003c89207260f020402015036000280113180308c0380f1054450040354440141c4c01d02198001403510825111800b40080c08030861409000e03c551100c294039064000c4801d82d00007030700350359001d80341c203040711000302e18041d800c400700c041880259040410507020942d00c807030142150307e20307002501190044401624445c1c41c18000c039961007030345488404816181c082540700454001d00c084041000c100080e01069643c00e10481e007601d21001030342c0c1d840195084440d6440d078a4042c2c981550003031110b0410b00d682e000c8110540716003042144644084007000140300b005050000c00c0c44508c0c100902c00700c550f050b8070040c180d80c1d082e40c9a110400a440041d02d0035400c10004900103859180001c581 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 407647706 1250 407646456 407646487
    0xf18090506061c06050c030604061d0a020d020c100c03050f100303080403090b0307021c0e0d0b060402041701050403020c06042412020f0918011a0c030729090105010b 73
    0x9540001201e043d2200e40ba5600010703201c0548000a0660000c002c0c0400c41c030300741c800d02e4000e2011b00a00040e00c1000391021701500300c010100003150340e011a1244002c0300940480740c41d0b801c00415940e00c0c001d50010071000b07103520500080024682400100f141c1c07605440070b40035206164201d01c000d491640c0c21690100000c004504205400c0000a20210703854041c50141c3c41d01e030044d20404411030030610556000c0003000041010515603619603072035224484950a80000031480e490f61100045004be101e07561000c00d040260100d5140784010651101c1d011b00d00c664251040302e507900c01000b106000354000e00101068800d400c44100444080703800c0841224145880c014a0f201c40e000101d80004490740101c2800207850000c51900310805d0308680161241c5203201e5044c0440114980b03002c00e86602041c80021f40403506120400640320500c0e4481c2060f00c02c242154101008508c805103041155050403002c03459446041c0a076a040e55540d0030f01c541030101d42c1c980c42d01c6 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 407648956 1250 407647706 407647729
    0x501091812020309121024030201030902040e0d080121080d180c0b0c10020403110907020304032f09040b06042003040c0e0912030c0906130f1809050606 67
    0x42d4031040101e0740f03040d1584403903c00304c0701540000c0c01052104100ca98141c440c0ea16107405040300740f9030408542406004590252070302840d00042e135110520102d0010b0000c0401110326210315003064016560001c5098141c82040003600d40685c46000030900e500e0258400900591050000389507442855108508044611440760a40c9c0d0040e02c6981744600c080d00800100040014040d4130f003042002070078403030f452941c411450580780d42c8a1010519085119138031610001d00031481441c401c10680b4081c6400c0f80b100001d19162510301d140101c607180e0700300794a0300c1c002000b00d45c0345444c40f4050312540c3c1250130421941c1c0e42c0c5c01000010480d1076200151010f1a111801c0501680b00245204030720418100d004941401290b10803c01e0046c04a5169441100001d13601c00c210300c10b40b600098044c903140e40f00d002c0d20002610500800a6803080440440c000090101210302c03060100c60320345502550446503e40b0002c1900c103551070207004c40d8003040c0071443c0d6080c40c1030b102d813 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 407650206 1250 407648956 407648993
    0x1150215090a03080a420503250b190305010504020a081b04030b09030a090e040f0b070918060e10050a031502070c031113020a020d030504020f2205010918 68
    0xd0040d000c61030146059450181c103008074448920041e41c4114500700300c00020020071180c07070340b50b41380100080d0707203c0a0444111501c3d41c1210419040112100c00e90003408ad0030f00c6542d00c91403969140c60341e031140c0c40c00d1304001074242000064be5041500c00c0320350f0404c0d15640c05483d5500e550904500c40c143d40c080710100d4400b04000004204500031413400385111380c010f541c3c1d51840700d50051804d11150030620002d2b04010a0000240b5407403945514507510208010440d91140301c141c4030340303042c0e40c80000d00030b04030000850b40d0040f50344040280e481c000310310381c1c107070325952100c4611b51064001e6540041205400f4030100300c0d08202810b05800c17251003d490111180c1e01d241d04807040380e1045818150500f19000175180c5103981400f1404100001c50400710a02d0340295240f031495000414165140046030944d22021001d1704841c1024118400300309209a0b40404031032003c0321444501c0c5028000710b45101980200182c4110b4000604909032654a659413044068249079 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 407651456 1250 407650206 407650211
    0x90f12050a1e0f141c090b010609050303070b04020d0c090203040b011512091502040f0608010b03160c020f03030c0c030c03030708040312052205040b0306010302240409020301150215090a03080a 85
    0x12107020480581c82c4400c0c140300d5008220700c0240d140ca0b824487c0181c00001c10b00a130020140f2844e1400015a074505811401400c1940c45a0001c550364a0081001400040702070702d01250302c00d8550000c600452181d001c0790700682c0c0e100d880b8034101135184c1144000400b5011114400c00c01500301401c11070080340a95000e45d903043c00a0100c0e84554849012101000300400c240b907007106500b401000280025459440e0040c5840302106200f0b03005018000408110019921801c528081178840a0126035507000c110310029542c0740701c1c000c3d481c420b104a00d00d40e002400d0220030b40300c03c20340c06030751541050b007560780341c00844110f0340e91a0100b00b401c2c00982100380d01401c0c6900c103040c1c2e060004240508141c180019521094461400f90f8000740040005131150400035021144a20840300e098030b0010341c0e40c07114131035580400c074154004000803510306060b58034021800c54a030202e0707610043d04000c9001140040703130806c500380c000002101c0400e005850f480c0d40310b0b0199800 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 407652706 1250 407651456 407651467
    0x50604141e0906013c0f03091707110312030a0605180f130611132103050a26060307050d080301090b060c0615041a060706090f12050a1e0f14 62
    0x103c401701400d544003000c911410441c8202c03654103c207801410020924091103640310070f484072090054845001800c0030030004148041c0043c1811103001c0c010300801b955249000c502e26103109410640b410944980b41c4a0001024503080703038000e4003940e4440e03000c0200d0b92402140e01c24568003c2410b8030751440b404240000880502c117146d214500303c1032490b19613420000c102d070300450b1030700300001406035250240054007842c0e1032501240e506191032aa0b07079080502c101c0b201d5004da80c820180300840d180e0703111f2805100810718852030095040320380c1d50399a2010020030642d043c4000d005550108014408400d050308500310b1141c001d464240b902600c80c100c54544070303085450b1000004000000c01aa180c18000ca10b01c004002c01c0c0c03000925111000200b10784a584401454107644030140d100b00500e11000010300d076001100d04014000d980400f80040d402005840300007078603400074007140503481c0814400250280d8450501090f17200302610320610b501110390f031001041c80b9 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 407653956 1250 407652706 407652767
    0xb090f0403020c030f03030f0c030c09090c040b0403050a1a10030f052b03050a0c0f08130b04031112041a0913020309070602100b03030a0513050604141e090601 70
    0x160703405d041068002d50b601c6ca811104c1d8401d8440260141000b000104240b1500e03954090980728280021206c0d02c03070586901510720075a1203654449034910a02203030000c01e01c440811648000340c09000e030003000018440164880f2038044600481301c000144090010861014410108038030641c12654244400b000203c0c8400700040c0003238411800c0710307000b8900c66060180681206500200f405050000315020700203440d40c034103003020000a18002040c00a60755010701391640c0010040850f400d146c01d00800c807191f112080c5209108444054400c00c0086080f40c0465001103800e02c1800304220074402c20b50f018800d210b0340b0072000302c200703030040001c0d20045005405800c000c0040d1440c224002c0d05020540c0b44840f8641c0c40c00301c01004944000c030442e18411000d10f4529034400070523600c8582c040044d040240c204a000c80e010601030a00034482402c0701080f61640110b02034009080e0011040403d0300d600500c540020801c1c55029000211400b5401d00703030000203882800d03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 407655206 1250 407653956 407653963
    0x6080f01050d20060f03090115060519020712050106031b03050601050607030e181506031006030b03030403050105190e010e07051e1203071202070b070f0f020910080705040b090f0403020c03 83
    0x312540c010317110010030321480c030009100b880c0e00301e41c40c01207032009140740c014090028000c5056480c11220f1345500110420f109100d000040c2c240404050f0310000c10b82801c034001e100d540012202c20880560344020019561496402c4a5001f8010030047c0c0c208002c3c01640d402c500c200301c0501030340c5480c0010710f8ad00c0c844c0b550b08010002440000c2803600b800d42041307056100c90114001c240410038041e500d01801da91105640c110f04002c030b100a204000710745035100b0351f800501294039080500080041c1420304640846940005000e95064400300130300700d80c21071506101c03642c003c4100304444d0404582c00b04804040301006a000890103012403108898400301b2822900700080e003d04021260007410040d030350510003071240f581850b42070f00840c40350501c081c008042005816041210a20844480310f5000d008503450781000c0401880b1440180100c81040c010f010010540c3e00b080e1081c0380075050001c12040440d1078030480c1c050152030142c0294118000d219458409031400c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 407656456 1250 407655206 407655217
    0x60f06051e0a05120f0919030210090c03050604121d060a08070e1503041a0f072d0201020c0106081605010c0f061103040b010503010c0903060c2706080f01050d2006 72
    0x502002c06919206c640d40c0e00b0030340d00410940c0100b91815500c00031a40c0000c44050002c5503000000740784c03101d42861030840c0300541c0003c100344220010401048502180704440300c2e90340e111114044414046044414449280c9a80081c014418403496520620f4095004041c0742480b900c2400030340301182001c00d6403c0102a059400820b10041080340c580928100068500c9a0200d090181e5200442203018100324208107105c81c4010002084007008500d0792404810312410740d45001000c0e01035044a91000071a5107400d00000b6044c001040960b0041d09242800015600f810b00549100d4450340d0309482d030071081030004002450358415000c100b10710075035a584a19251604000c990720503000b03140070f42d04000e9510aa00c0c1c0254041c425640d00400c0455401c114140c101c4421103070b003092440010440a8003d03040d42000084400c5d6102c239581c902c4195074942c45e4814125003817040b07a030009034103100040440c0c41015034150790707640b1016502d04400700b60001100b54005 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 407657706 1250 407656456 407656471
    0x2f1c0203190e03090102101a0d05010b040c0e10020a0b060103020a0207030503040b13080307050604081602040c120e01110a111906060e06010305040f060f09050709060f06051e0a0512 80
    0x141d030004c0c541e01046120800540e0703041c01c0c828040707010906d05603203040c507025038091a03081c2107040c00c00000390401520904054020400c11080110052004220320700143c09401402d554011741032001c6200382010760403030003d07031031601c4180044000350b0168140d1800c5005e00900440002c10a0000700000c09041d5003458a41c02051003400c0010b883d540252003a0344200f0812000802c08508181e00542141110340c44241c181042c41d803410387c40f00000d51180c0b40086440845412010103101401c200340d04001035400206141e0881d050342d10201d42500d400e001280308640b19010b00d82c00070030104180ea0001030007502024031801445400c60302c0c1e6460f46403c0c403d05000d0322509900c03090901e02030182d800c0c207866031101403d604602911450321081d00200008898000d00355541d40320302140c90103562400b000d17000300464040c90024100c2c0315000101540300e081542e140c0c2d0030f080462003210600503000e4400b940103400070001d00406000e0035911244400520f4800c0341e4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 407658956 1250 407657706 407657713
    0x1005160e1005070c14280b07110907020a230718090804060e100905010e0d0c051008041101080903121902040303030b040c14090f040608012f1c0203190e 67
    0x42c600400070355000e82003c020103d880320880224002030107111b04116000d03094896580c540301d0030700850600080c800550031640840a00003919400280d41012a00480c80060060740984014404010121145405602c642001c0c080d00c4489203003c8140c4814420001d0843c1c11a56041e0282d00107510a9000c40c9c4041701441c494100b00d40402c00c21011450404401030070900040d003841609043d080c05100785000980400911071800006441d005007203402c10304205a00030521481142c1c2280d0640d00981810310550081c46040d00071003182010b542005800d0aa001038200020400000820700d440d0100603005944001c001a501a5802140502100e4244010b40c0c0d50320100700704125805c2c2c108004402c0e078800340d484050b021205251400c1404000030043d00240d0002280341d440c2141c69180c1c2501c11a12114a0802c6030710510b1030707201c0b041001c805005003d031001d41c1e80055029000441c406900566000c150782941400c5a04d80c030140204840c040c010442e520750 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 407660206 1250 407658956 407658989
    0x90c06020a03091d0c03090a02030601080a0309080309030307080f0d05101d01060207180209040606090e010803212212090b040b07030c231005160e1005070c 69
    0x141d10540003c0a0200b4100f01c0c0c0041c009443c52490525006003049140e550203c0420b034800000d1080d070040c00d400400721707401540c4561040c0e8448144201c118003140203608001103401022090b180c0800e40100a0750601c149a244c00c2c40c80d40c08003205c125908000c01448941ca0709500c102806404281040780b901400d005201c1c1440e0244941154424244c800401049600144003419a00300510030804c0d404103501c07104c0a40a00352a041d40141032440100b20160302040e2103003190b8048014050301d076a9114440d84030f100d00080d10114501011106030224112581c007a08015088a014684d40e5041c4e44248496501003086465101004000e80215441400c02025007410380720300340f802e49400300004e00340c80b03038103402018421121480c60038042e4a18202c5410382000f250300610940280c1c004d0b4480840c0043c50210354904004510341074900d040d5034158480c40d440d22a8101e0a41703040000b10250038810000700700c0100140750001d0803107452400209242c480000b03048 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 407661456 1250 407660206 407660213
    0xc030601090f080c04050c160210030609020d0504020a0e010b0a20010c0804031107050d02040c02010e03070507030314090d152012010b0a0807110120030a0f0614040e01090c06020a 79
    0x1240b000d4017601b81f40c60b00f4810340c0050490034030301800240d07040303401c1249140100c40a8018050f6580181d04041c4081009a090505e070f03040b5521079442116000300303c54176129008640341084c05200391000081c00f0081d152800303071082c189041d031031100001c0110102040d180c2036071543c0401c0400141403006010415811240108504200348040c000550130100800e8074056003240182c82a62207618502c800d9000794448403c01c4c01120a0301d94521960403e19034480c4544422000108010f8462850b203113400142c41d40014010405003010007140c540078070410350f07111006d0807990b846e40740100002e820300501c807504411180032511065181c03054000d6050580c0825458a001c1140000e0b595001c80781c0b5502c9842800d100105012000c00030340149140c5500761b0cd0542006000440c8010003000346105480001051058220003100b00003564074911420b204400320b0b8540034064a010f800c060040100040000744840d200d4980ca54500c01d10b502c68405a000742c1042801d0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 407662706 1250 407661456 407661461
    0xa031104060801020a020d08060d120c0b0f01050109060e03330c040501020a1b1a04140f0102031602130203150a150e040902010219030905010210140c030601090f080c04 74
    0x100942d0000318180401c645010707441d007035006240000c0280000c0003440729500c070b2403004c5440d41c000031040f1800103060000340c04070080c0902070700e032013105500080a80c42d111202034140c50060351103240c1076141a0303040c0c031101d0b40701107180e03894099030140b42d6505003050f034440e465011350681950112201480c030007075050080c1c110070a1010401c01480f0780d0341c001800014859110000181401c0d510355228032580c02c035088031380c003000d20a244041e80400070300a401907494004415444001940811106101e00d00603540543c109200780c6001c01041e0b012303911010b0000d032140c6405c140c0500c044c41240e00440b2800700612507001ca504903405c05580000c080d2040d01101c00071031840f4070000c0d00241d07810420f944580e132155400002c592003070100c071112803e20301d200395044006240103420003035180241c0703005101f1b41900e100700301d000c0d000e00c200309580b040c1d4009407170300d503078090718482c1c0d00040600c0d05000c1603250014860038601300342c0005108070380151101d03081d0f1034200400d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 407663956 1250 407662706 407662709
    0x10e0102060903090108131203090b0609071e140c010f05070f0804020603040602091c02010305091f0203060f0a0803040302090112050c010e010e12150c031612020403020a03110406 79
    0x441d4000410410400d400200315080700f01c090800d681a9a14003003800e4011010f204020500c184282d4068855601500301c2001280710700b03411081e9035030391403e100c00740504440c03100005440c0d0f001c161111034034040d241d40318001407818a12560301b4001d1500550f102e0104400320741c2d1f42c1c3c1403420481c01c4a11506400102030719000081e4806994000c1c460343d030140c006071250f100000800c1c03c1144035812034002c11070280c007000540600f42c082e0000c0600c12030041c1d0200e401e01000416112001c6402d08404083c1a051400040c000300d050000b500010400c54010281c444101155920300740e400c17000f00801d400940e500d60851041c0017075800117070f1002108030982e148580c0058408038105810150a1900d20340d90086800100d90314640200300b1500001007120b40070002501141c003155021484412102503100d0440a0300703248812218a00318070000d1948070b00e090303c12505c23000304178040000541440c0d01d0b900000c00812440c0e10454030800d000c4405252810320b03024480 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 407665206 1250 407663956 407663959
    0x70609051306060c11010e090a15080c060706023001090605041e18020603093306010f2114160e04020906070b0109091401020a0e130219030209010e 65
    0xc0518051010744108411a13006240c1400070034003020136445410800401c00000700007110340d0800c203004900070001c2003070f0505244c00300710300807600c02c40010309040d018401900c8545004065100d510094009000d040c46c41e0001c00480d401d901a2541190942028403201410a51601d8804011250140c2c4500c2c022411311081070441408600001e482c903006501c0803445007401901501146200f200081d071040012045c40500310000481d00c3c21012a2104802581d0507494030f1881c040000c2009000c031005900062a00d51140c00c107034050038603d0030102c541485040722260001015008001031035904c150400200400c000c000d508420548200d4586601c0d82d100201800104014107004a40009200c0c00170f4841400311510281c105c0c040c1a11542c44400e010040c2003881c8080d10100115140f0f4008184113100b114107442958840c2403801012400f80401c4001c3c171509651355a5090100c200b01d11100c50755140e50400c0e0f580c0043c0ea543e50503002510007034000c42202d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 407666456 1250 407665206 407665211
    0x151514070614090625030c1206080f010605010c0809060a090801050705071101180e060a050402180306010b0c0307060b1804030929040b0304020319080310050d0506060d02120706090513 81
    0x804400c1702004441500c00c01c0c038075000c43c007262545029900701e03008034001c0041a00d003200008508101084140703140c40c2407002030041c5030b030307402c0119483d941d07840e07001d071000508020b02c405038600040181511142410101c40c0141c0d0f0700000d03070840e6021298007011940004244040001c1c49180d4200b581c82424000c48605408900c5200322000340144d01c90380c42e107400403c400f42d85040301c1c1801040024410755035040311040c01c44107400c1d0035900b103000e4420768001003070f019000401d80b550100c61100031801c018071038072520003070041d00200c0358000c9010000c1882c600510401c01d8810350094036a070340c60714a0403a00000c851141c0007940002d0588070096961520007408403011929a41c036030640300d0b212800000d06100c0d04054140070070000c48120420840000059489940215003860750f580d41c030824032440d010480002840707500031a00140c00d900e00b205042a00700d001424010412000c0c010140c03800c140c580114020031201c40d0300b004145068800c0d82c00c0601020010b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 407667706 1250 407666456 407666491
    0x7030b0a06300605040501110d061e050607080310050607050c01170903070b0c0c150f010501020111070f032307020f06040f0501050a1106130203011515140706140906 73
    0x2018031564000504180d00c4d4004541408001d402940c4000fa4100d00155100000810640203118034441d481ca80c0c0b207140d00540c68890085488c10494002600a5140820702d64940d80140d000400058070829000070129090f12070300f0182600320711410003040c0117462640050215152081000c01b04110340080040d0300300c011064942942d071003502402c0719202d101c2c0c484e009000e4202d1064031441000454260480e0003140c07280140d80301c0320f40c40c1d40303640c03290012801d07100702082c0f086d00554100950800941d0807856111258028034004503103001d5480c0c0d85100034115005e0000d4000e01188075002d61901c81991203240d103007102c403240781600d040034420f1150707202e00c0f03900d05108001ca03c0d80402ca0090358400804c0c4100701c262240c900e4142c80c0700b000e10319150300603400f0398a00045d0840c030401c601084400e42c1c40601d03000d91440780c60ba000f10f44c120300022001e14408014400b40f000519103000c1c2d41040341c440c8415074250303c2c200c03075494a009030003014425683d140010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 407668956 1250 407667706 407667779
    0xd1a0f0d031b02060408010c03050f09061303050d0e0718060605030609040b0403050f12041101020a051018020d110906030d0f050306010e0306090a0c1706150307030b0a06 75
    0x41e0341441c0b42c400c00c02c0346541d40030f000003203441c001c56101640e15401c20300c841d002c1c40c1e4158406441035060502c0d0043c1c47d102c103507044c2c1d503c4070100e581100c982880440c0a0110740104042c0180d45c0702004041010182c00e01c50606204071580005858280410700b2000c10310203018004c0942620f1401c6400d52401c40c000414544000c0c0c03020b001014800042000e045c071a804a8504076007100c042036566a414000c030030b90070b504840a860403040b00305003984a61001c03d2810080b40c00800801080020754407100040c49031488a10000207a007a818006889008502040902456108903d81d8800301440403081009126038800e800201e480c41505401c1542c151a9039a20320b002a240d0b510400140e98046003125150b0b8103215140805c030b810140098015502c41c4174400c04120315599020034060045580340c41d20b9950400c0c000600c8011040c9030002c8141d100a0480340c05940c0d0b5100d0b0101c43e00c0607507018901f0390321441c0034002085200c00c8122100d68800f5080900b41c0c5907079 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 407670206 1250 407668956 407668967
    0x8010e010b0a1e02012702010201060e06011e09080d030e0d110304120c09110901021506010212030a15060914010e01120e120f07050c030d050a11030d1a0f0d03 70
    0x281030740040300c2220f1282030320035880340c03404450303051700f1841c2e68200068550b000103018504a00560800d580460080885480c0ba4080ca40603140d0038401d030820907801d014281c41d051284104030001d0340001c1c01c0f6008103c60800d04c2c1e415240000c40c0000140900c1c10942c101914806000c078103c600040180c000080320110380f00e08041100c55512840c0600d00c002d203e43c40103940c141481c0b0094501030101005041d501ca00340c084481c004000110000b0000b01101d4580c0941c03c000203d400c1d80035614025903120186070000240030080c100d1074035003500250403130800212091414001219910300f401c0b002103003420a402c135a102400020240c3c00c400a00c007410307a0303d4000450f1081070420081148510b01c41c00b070780c1c4800c0340720304481503504418020340791442440e48101c250304002c5154141100d080c1e8074944bd04048220542d61011840f9280745184002c0065242c8200503208250f00306070010380c000e2241c007005042191101220a050340702c1c0e11421101c50010f82c101 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 407671456 1250 407670206 407670227
    0x221a0304080a020307050706030c02211c020d050907061b050309041a090129031e07020312090c09150a03060e032703060c03040f020915030a0308010e010b0a 69
    0x10084580e62150102c08034194041d01c0001070030780c89901c0000c900396030150403401f1803000aa003210a00081083c0c11005280c140100c502d014508008007509001500d425070000443da1001619149002481da011944100c1d840009a0060581404003603800051081c0107200680e1000e00c545040d1605600c031710852183c584243d40d171b481c844a28a0b045a520700a042006180f00c00c40d6030348500d00c6200010b1165102101800c003c42024584842c1c01541e0048001070380041e0543c0416134aa80500405401c0d18154403090050045250214010903c2003010b44041c00f07107080d54405108000b40c0180440030103c1100c0c03220342607501c0c1c00c210101100d420203408680e00d00226091821071040c91b401c03020880c00c1c2112400a81541e60494040789801d80843d905a40c94000c072610500080c2d8004200000c8140310f00003501d00040307003682090400e10300d08500717818680064600804180b0032000b25030b007440100171824030050790500520b06566600d10f010740c0a100145100990b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 407672706 1250 407671456 407671463
    0xf040b0705150f012304050a06090c0309080f0304021504150201050c04231212031f0b0d0f0605060705010b0f10020709020d1103010623161214221a0304 67
    0x31101540103940341c0094005c000c50f0280080285060200705200a040c16000303411029040500d1400120704c207124180036140c000d240541000c04c4011101c02170b40c0081c1059912040907520078507650f41c0000104010b043d03403141e83c02d009515540103400d550b0000c000755044035041c00100840e03030004a03901044562401f18001c608160030000711191034094000e0060701c40d01e01c1c0309401d01c1ca6500154040c0c40c42010602c1c1e49594211105211076141c09444940c69040c00603480390441ca0300441903049150001003512500d40002c03c0da250082181a41c1c9603454406c1400281024280d8100c0d10006450003081c180601001075500c00c0c0520a036041c2d10342c0040d09600288003a0320140380e40c03e001c20020fa40e035035074030030080c40d0191101142c04290303142c1020340e0343c2c0ca05807021101c01426502c04200584030725201d000b42407150101100502424514406013104440d000704139141c200c4a00c410300c444a032074034080c0340c0c41d140c00c540407071411180705914003659141500d031301c03a62 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 407673956 1250 407672706 407672729
    0x801150810090e0111130503191e030302072004050a050103030e1002011503050619140606070f050a0308090d0206060d060504021c030801030b150a060f0201020f040b0705150f01 78
    0x6000f601c58014503000b80340306801076010507081c080013100c1655004680048045411600b05d6003031469000c84210030083c110101c402282ea40040050342800846000c1d04005090410940360b2041004d48440c4500c00b10300c00c60815441490a48180c5801241c4084108030541c15568094242003c0385c04103803260034101c0141300042d200350406042410001017245601c0ea6138500a0340c2c9140940b80080b400321010012100e91341148070740068041200c0d40007525880d410b080c01a2a03115640c141d41c0314082000c4e60010403000c03c04050000d100c1d50f1009071901d8405045800c0910902c03c0e80300319045042845020b5035403480c20340119030051000907890f10303644002134844100e0005104014081c40900c401d154000003113034100c0c0e00030419503503603568140e6000300c0000c0c90000b01f0390004c1c0002e07003403080c01e04c51011440300004d540001490182d880c2c05071503454001d40d01540181200140040030404248a41080d40711194400729103403d04003020a42100e05018080c004030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 407675206 1250 407673956 407673971
    0x100309052109041a0f1008041b031211010f020403030c230d11011503020d0b0c0f0d1b05090a090b01090e040302160509090d030b03030705030406080115081009 70
    0x2000381d400c403410312400074020014089800a64025044150882482112446030807460b6050400c204000d10a09507648116944c0355990850074140242200c02020302c43c1d0008000150302c00071020030700600b500c4100c0501e11492200c1c1c02e441388402040360450041c002040020f030014541110749a010010b06042201c401e1140702c1c444031030354649424400d81011074081c0e50440c00244000000c8c000a0020341c40c0c011102442c4e4500b844000d420491030130105010402e00c2d85840d4201c103001100c10f24011641042c1d0f006900300c802803058003541c1d24400c0b030340c008280510903511045c5051040c02d042402d800281e490180b482500000c5448081c1014160303c80d8041c00007030f010b07002e030030f000341e08150034020750b154104840c0303509910607200081141e04c1c009910038822045000280010323080c1d28021805000c0c40901d540d09840140705d0000003a00c00e00290010340700554900b01c66601d060454040003401c1052041885803030801d109203071103081124000c0d61140040402c030034 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 407676456 1250 407675206 407675263
    0x71e061b091a1c02070f0b09010c0e04050a06090c0e0a090513120909140f0a050408180d020a0305030703020d1409040504113309060d1104030b04030e10030905 70
    0x41c0703c040c400c1c2e845610004140041001c810011070340306e80602003a80b01682c038a280c5a0880c2c40702c54200c4042202c11074101c445103440d4104c00d0703101200a0000c03d007641d07202c43d454140c404800e510800b0034840450140e10b428980000f070024400d256081c030107810b05882144100b503450102411f00004a000d00781c6031401a18924020000c0b060200100006524142d414800036500c0380700070b54090300407400d041d0007409554010758100c61240c0c5000110003100d10300c2c9903030350300e540d03041091446004090f03551000410000c600442c0950341c0c7c0c0c1d0640c1340003803c0c5070141460031700340402c1c41e4496508007250001e4802c00e801c140d03800580ca80f03070340c00e0602038030007019451903101d0760071140d0400340c842207111002c42c0e10300d00c030307500140040300899800c0324040c2004003a04440c05224a140c00943c030740000780d004a100c24542d01c2c2c941c4036101c0307640388036003104c042d80414102103802c1c10604100c410031041c0c03101450204503483c52551007035116030306080303000f01c180080c00300c20116 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 407677706 1250 407676456 407676487
    0xf0c011e18080d0e5e0b0102060702060f0106051c0c0309030e06070b0406020a1e0302120c1611010207050a0306050402150702030307030302071e061b091a 68
    0x1d0a81070301110b1503c09030b010f008001c42480304841d07006074401c0b202c0071018090003501c03c40189401001004901807a216026450669056200d901003200010060340d10a07454604000c9800540400c107174100100180c030f061005420141158441020040402e580900c024150744c400d150150340c0e403010420002480401d040f483c006c441c03403e81440f1800e03815601c4540c1c002d1081e102c1c05009800d41c0700300400b6021f10324014081101c03000003c0c00284041d80108102021401d00351002035001174805039a000004442c0c01107580040d044001c0b17a00d005c06150b100710602500761034814242c01600c418140583e004114040c600010a5144e000f8403161000d4100507041182480e071b01e0030729801030300c802d0718181e000c0c0e41007254815400380d416088610f0303150090000c2d85081c10315038007140250710681d070030744540d801d400750001c0e036041c0380c47e00c03140141c05044c002c140030520030880e481a88a400c0340d0301c10b02142d42c2c03081205840c6000c0350710300100e50035000c90f100c1c20301240700c008 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 407678956 1250 407677706 407677709
    0xb1c020706050f0a1d0a030c020604031a010e0114130b01140a020d0e1e0108091f020703030e1f0c050c01020309030408100c0516140f0f0c011e18 64
    0x545040c0010840c05400e000840f503c600c0c00440d040c440001c07203030030707003044c0c01030003103000506401605012010034001d0a640e0001d610142401e45400c2d41c98032080340c1103145002100c1d0055010300100003000010700c41f68003418840c00f00120032440e1400182c04401c1f42c240480340c0341c3c4c0300e4a081a40368029012103407030601089c140c5a49030301c018802500c6051302c91400010451a000020030360600c0610300305102071000107a507910f112440159101140108085540e104143e004c2441115185140107004241440507131107a000c3d1030082e06440d81c946480321240d00099020600c44440e0741030508084405000240307000e158075044400e0310540c12000e04542c000414090929030020080c01183c55140c2606c2d404620f440c0d040702234919045450b400a9002d100340d0030310a00b42c4a00c071001601c11020840d00846081d001810448035030300000e00d982104107002040d100901c22040200d0b02481d10340080540d403010044540c0e001c400b00c0c402c001e800d44455a40c1c03003045043e00b0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 407680206 1250 407678956 407678963
    0x604031707151b0e030a0c08011e231807030f0c05030606011403100308070c030b0f070206010e060103020d0e0c011202090d140a080705010506270f06010e0a0f1403070b1c0207 77
    0x1f00c5054481d1400c40c06003040f5041d030009c07011701149400304058644540051001c2c041001800310b0f04042c00c000995134050410113082450b101c2d02c0b84c007808200660340040d0322030341581805400070f04084491003100e40c022030080d08104d04002300c580c0e02c07403c901090b21400000b251240c503102400c5510406039040144403c4000131a0030a00040c80c00c2402100d2040d06000b1980da54040d0309103001909950100c0540d1100c0014850380c45000b50241e4040b0043c540141008880c404080c00d032410015004c0b500d420100c859451968800d11015000302030100651504d0b50032400b050300f440040b4005003016030700780358112a2080c248181060300760880c0d1a144c45100d0b40c18610f008100c10394555100f107401c41c40b0801500508840070744144c52032440d401c055030f90f00028a640c035000500d941d04110f010110070b0307215510708450f403003d8032030781d189174140c9030404800700000f201d0034542902c6a808074208101c001c6032001160501142c1441e1100030f600305080080190080b20b00c0203 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 407681456 1250 407680206 407680223
    0x15020d03050106052b0204181a010509011706030109021503040c0602010513110307091e050916141807020c0406120c0b0f040504090308070807111b0604031707151b0e030a 75
    0x140200388c0250080d13684002902844021240801e0064401744107609200f80410a00c6c0c1540001c110180c00566202401400100780340343c640c0e0000d082c885805014909100c0080103100a2211140310300c0082d100310b0000304000d06100006078014103050000a001410980450341640c0303081c07112400074552144188400011151001040c01c44000c03200c0c0c202d454080041d641900000e00c1401c00f050403086482e40604041801ca90307048005481d0390444607521280c0c0e0140e203003d2042d4803900340e550180c01044180d404000030340b442680000e0b80204942c591501040c07034022070104494150103919034070044400b411200340620f03405941d20a00c0c0140d00700a02d0f40100610344201031959560300380c0d54030b0810689469403940d04040131640038004441c0050407142c41c0b041c01c2c1e000140002e09040d40c0307507203241a14110001d1413441c0c000200301413040142c69070000c0318445050b1400e00c8008501304070741d400909100040400c0010301408040325031400c1c0046030b446600903802 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 407682706 1250 407681456 407681489
    0x7030b2e03030c021903020123070b0f09010c05030130052b1719093203030c0901081801020a082403030301090c050415020d03050106052b0204 63
    0x103403d0701c86480342a80141c42d50307a02210102075002ca803400380c1b40d05840780d084100303080303188480d00e00c00310443e490780d04400c07c00c0b0300c04168500c0c03a4511404c030743e001541084c5041c0880c0b42c01e48000030864000d000080c4018000e030041500f405101e00c8023000501d0995401001051484881c24000b810500030741c08080d80003424012020743c070000c8107200c00300e201c03543c140440760070306040403811a21306402c2c0421400c1c143d201c000e03141c0c0c0403501e40c013190301005030b20f078440d90034166210440d01c90029224038011007d440034042c1ca91248001a50640c0303800d4010b05124490b0a10315030400c0048800101411b0380c51007600d00c4105a00001c5454100e42a00500301d41029901c00146c1d001c088110b120380c40012442e06156500900514110307442c0c180c041019209551142c802d1000500022512184004a10200e80d00d540e000305183e140e81ca0014040703c0040e00b00500304081040501904c000418603464441c0780d00c414121a201c1340300d5140000c0c0166082501d484116004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 407683956 1250 407682706 407682713
    0x31519030507080c0f0f0d02061b01020417010e03030403080601023903010e12031e04081903020921010608160906080d0212031e0f07020d0207030b2e03 67
    0x70794800f40c92450b81103c1d840001681044003140382e40d10710301d510190304925030b403407424259404200c59201a04185c01c00340c13090b51400e1441102e20a07041315070b41c0440c080295860803c02d01e080c041c3c0303001c02006040b400c0c00da429100d2200030406410301c010000032400750b03417080080c504554400b40c03400c50501a000c440d040381c00000750301652905440c0010034003d28061154603106d1031998020318404501901d040c125400042c8561403048a9880c2d40750003220078228035101c1c602c0746d142150303a03149104003252188026140c80b002c05105012000c00c40d1a1003040250324007070615070110030070000442c0c0e40904030541010790140101510713410020701220b460020f882e801c450500095031204095a0340341c83d0201002c0040c5c1c01070158a03507485444e00110b0b0440076240302d6034081500682d00003d000c000b6500c18880501840802c400554180018040c4172294030241802c140355480b84002c402000c3c10948081d00b14100b2180300c2c04c2c80d140c00c1c80c440f0054050311190141d8904 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 407685206 1250 407683956 407683963
    0x4050411190501020601090b1507050f061305031b030d0f0e10091203200705030403030305010e1b0919080d11150a0911031009020f0a06050315190305 66
    0x68894060726024140c01c4048544514000980310180e00a00c0310343e291514200c040c003a1002d4a07604480b01c10250002002104018460f4500a00042c40e4400d80f0b9040742c2e24000c030040c0b10341c205009000c2c4100014002000302c803e04241009000e00b55101103100078114480c031040210081d00e803205820701d00c0d020380c0014204c05075100c15a50307186030580c016401d445038081c000b0120144501c211007060b006e03912001c0300043c13080c450300c0d00c2010014106241d03400072000341c4055101140400416a00d801100d0240c00c0e403090500250801c003842074071901c039481d982031090328041110f40311501d400c01100100d490300d022903020290341c0c18140351240d600120790400a49051456815800c00050340076400040f06850384140d95480c5851000b01001c0f4070449084039282c90316110360340c0030481c0c946040480d9000143e4002c5a20401c0500d41c1c2e80f4100d0350007600408020400c80742c10400360f0b40e10118000c600940350b490300001036110075004c00390f110302070182d1308044140312000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 407686456 1250 407685206 407685233
    0xb13091a01030b01020307150504080c060a0e0c060703020c04050408090d0f11010f1704050a080f0306100905060d0207050709060b0a0e09040804121103010f0b04151202120705040504 80
    0x70b0300c0411015106a0049850784525a0094810814400d40300c417811920b90041d948035001c0c0340c00c9401c00c6038544015007400741c243d50030300700c060f15280701e40590074060224140246e0212113541c44c02207144c1d406034a840307248500d28810381da160300003000e009001e81211400d070801814050300080a207030044954030528001d80300c030080300100b0170041d400385241c041511601e840301c194400041c0c00c001c41c00c15004008031340901a40305071800184524002e03084201c282d41c0100d03180e1074075000b4040301d501c1c00280c480810414560410090b283c9004550101e001c0407005031741d4814508000d0b25001d1103a000054062401e0380c000f070320030307011000750614540d00c0e640e03035054000400411200c03000545000d014550208030130411010781032800c41c0454443c843c1c0e0002c00006030002400c4580b90310002c034400da12007080042c1071a0074411441250f07400160001118141a0407640300c400c5c0301c50080c0145100d0000040d116020442640101002041400903143c24a041c2e800758810 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 407687706 1250 407686456 407686459
    0x2010c0806040501030f02120a0204060e04020111010908031801020f03040f1e020a0b0c0a050d0f12140c0c03040f180b0420030a1e06080f03040308040b13091a 70
    0xc85012891500e840c1c024a4126900b000b032040a80c0766603000c1099600408140640d01d1148645010060b00d990280400600c014003140446d4074241c000506810704040c180302050b45001400000030305100300f6039030410403440740c040510703610403881030080c0710300c80c402d503000000481000200964041001034940c0710f00c00c080500d8001790511002ca00079076030000d500a0f0050001d022170542440036000d11000c82040301c00d03405850315207a003403040d05c003690b20024006111110499802405c0071800085452080240000301ca14440d03000300c018010700c1c0d481d000042c1146441c01e04105890141c00ca9070840d00c01d0655480b000b01800c03110741c1140f22007500b0860f0b103c00e90314080c031844a010304115404210a42100c0188a1541c001032081034001e540b446025990901100f6200361100200b800003023850405501030302c0e14400c0200d080c1c047c0e100700f0061001420003010381d41200e0000034020b89a440742c9030100c040c40ba0070382242d15a145810305c02c401500305031031100e2882c0350 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 407688956 1250 407687706 407687717
    0x30a0506030c03030f0706150b030915060102150411010c12030f0606111504051f0905061b1c0609050411120303060f2403040812100f0311030c1002010c 67
    0x1668107040c0c903406014a03005c2e510030180820004214182c2104600c002d401000b14501500c41e10810189d401c04d99500300d070341e03105504480d4000703424030185030011b03824001000301c0c2d1554149a110034800800081190b81154015903059019500700002d1b954021403160300001e40d048000c1c020315500210996150400800240e06030180da400111000740c90054240d902014410a21464025008032414810483c4801001030b15001c0b040400150b13070341c0842c7c85002c03810f002d45400350240079140c0400c0000e05805510887c5002c13940d40d02c0c010024240842500316800f00148010703409010002c3c00d010401040040078013420307a0401c021200c4131900300251101540c1d80c007045078555044214404100514501580701c0b00107043c61b201d446000780300c1c0d4280b07800d443d0810b03641107a003c400443d0310f00151000000d120390000c9610009000b0501e0100701e2450b8055520024111038104410850345407003d01840704040c101500344958804000402030080c1103a04031580040e8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 407690206 1250 407688956 407688973
    0x3030117070f150c030e0901062102030601021911030a0b0702010f0509032203051905060c0306030604020609040b0d150b0a0f0b2d07150b0109060f05090303030a050603 74
    0x4402d42e606905982c15034982c1c80d0050310522055a003503160400c103a080c0402c4906081a9684000c4040c5c02780203e43e4030004104e10288403000440307004804042d02c14014420070040c0d981c0010700c40082c1c001d0506007101c01c402030074110790601c15128115003500a080c402030621400c62801401041d00764001c014107911540420200e0f041030320728800a400420a540b81c0c1d00d0802c1c1c1394004030308560801e210310f0340c1d41c0c0d07503245c50f06d000c168044500c0c801c09507440c414850300380a0340754000e40c0701e00e031149580390060001e915610018002480703150701042c02c1d2140d0b210345d030050140200182c40520000c10605083c000b07584812140c03d1820300b0070020403414101400014101e13500380c500103c00c20300b005031440460700700d004083e41038410244813101c5140024001031103100c804210940c0d92402e4100711a07101d21715520900c0c0242042900030b0700d40d81c4250802c0480306180b070010088202c01508079803038895100350340d600d80720101c10320aa20140d5448036018403070450071286101c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 407691456 1250 407690206 407690219
    0x200307030c030e0f090f0a1e0c1106040510020711030d320306060f09060a0504060206102411010e070510090302010c06150906060c06050c13051509030303011707 71
    0x188035904e2a540104001d000b0443c0c034090200c1d041c0d00458005004500304031032120781c40d44d14502e00702d600e0a650f201e50080c1541500300401c8001c150140e4043d01071351800784c5480341d680292018111189600080c5a400c1c80481204400c40400050560300c20b011101c00c0200301c3c2e00c0255400b035003840342014003024038070000781c0308100260103680c22f415555048108403c80d00544000340c050042001210034507a5044014910500d482e03d41a49460178410002d10300310700140130010403410154188156981d1412a54440f0900d0301d48440d808001d80c4102d814010079408041958202290140c4640011804500303585054a0603640090381c204100c402459520020b40441c080050200209040e900b00c41640c1c0410701d101d0030807507a20780c41038089907100d0740000c0024041d00740c1c0b03104201c0740d40510340d004100c3d6082181402c200f01350812010180380301d110b2007124009040c880540480c1c05803441c018000741500c1d01d960f9a850000d0170280c3d12046a640fa000711500441ca5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 407692706 1250 407691456 407691469
    0x4205130b13030b0a0204030f050a050f0102040e0a0e0a0c0f0503060c280309020d0b071106150103020c070e0f01050109060206070c0f02030f06040311010e03160201200307030c030e 79
    0x1a00d65848401c00501d140da100d102507038401a00c0c0c40030b865001c00c40400810517142300d9890492048004000a0b00f040c2080c5003400b00c111040007541e401000108003181c010b00c1d0705038001010100005d190346403140c00910b890f9140d60000c0412002c941c000804080e220700002c1118801e0b401c1da200c0c0d82e031b440c00b02c02c9207210b00407141c41822a00654000faa20400b0b00819120b007003800d00080340d04a0390002242800801301c1210101d00143c208104150320072900544a0140d0009080305e040403100c42c0b2141c6041d0400b41d04042d0302107010044820104041c800514010030f1811041c20907802c005900007090056a0100d01e0301500041c4281c800a0f2540c81070720160f4803400d02c4509a41d501c01c0342080080e040c1d0307052284041c1c01c65440c40c1402458050b5102c0d49900380071002c0030008900307545149056450702c1c0c00c01d00080f40d15803103007a2248151942480c2090b0088a198421580b501101c03005070281e10010070344901301500100010181402912100e00d6880d00300c080041 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 407693956 1250 407692706 407692717
    0x80603010c0311030f041e0b1608040308040b10170d0305010518191d01050105010e1210020c0708031803010f0e0a0b15041401050a0902044205130b 65
    0x820900410010b24030303000f807502c0740342c02a01c0b84081010347e40701c3c0409100030b0824820240c50303281041041c0020001a820780c01c0346149c8600b440c0c1700f04d00c0c00f0f4a01400c0407100900242903240910700041001c02820011005040410045401d2102440c1182e03690007444c04228042407a1900100795031902c02d41d11001031500d043c0f8103145030f9500380c400075403000307640d405040d10361285407017103000700500c3c6041448007800000007481e61601000412140b43d41c5000380c0242c410b81e006200c061800701e6408a990780c503800140e80d9a0a201d9480c0c90029998400e0060b07002c041040d43c501e0b0240b00041205140860085c092043c820b2070b21801c5450200100030745a000e0440340700040e450f03d80d055032100454203917802d07d11140c0c020a0039101e50800143c00d10030248014001460041d201e503001e005e50700001c505150070140b50310588501c002c0e0700700080450000440e00014240041b9085003078a5104200f41c0710800700140c0250000e8034405507a084415001c01d0980a44003030381d4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 407695206 1250 407693956 407693981
    0x1203071a1012020102011506030b1e010c11031207080301030b070306120f0312060b0904110a0504031b09150509070f0e0103020a120509060708160917010219080603010c03 75
    0x45440e10703000c0340c002c0445280c40124195522400956001780d01000d12100400340703510b000c10200100020413400600010441131400116100c40c040799900c0f4040c0059160322510014004140c1400a440c1c00105400616a01e800061003020009620059070481344605130900b1a91205401a07080d1075a50083c880c181941c9480b030b0010650f05862800c1301e81c02401c104000b03407218070324001920b00c0f54018000b0b0000008200d4881e003003038404d03102e415100348101030038a80301010082035842540f001030201500c090301807001e082d515205100030800c02d00100840790180d000030300d1940003413042c548109208400203222900440f0b408818010383d43d109829a00d41c200107500071f40088810b001080201c0512035101e62203441003e000b081000d0084c416441d02010007061561b0041000e61312400304043d50100076000105402552440300d400d41c06103070084609030082c05900300660502160741920070300b03140c120207420b0040b50160024028120040301c1501a640c6e41d0280a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 407696456 1250 407695206 407695231
    0x20603040f03030b030106170f07051c0212010903020d080f16050c0c0411131706010b0306060f031e0703020c030913090213050f150d030c030203091203071a 69
    0x250000d000300d041090310740c0c803074140000e40c8030b180c0d00424215001904001040b01004042c042e4410081184480500c070440041c40800d0030320011445c0341c0c1d00c0d015200c440c0c0c4104580c0800f10343d03c0380c00c8140507100b01c8000b00924446810000d640d8147c0142a10100d01d0380000301d586e02041c1908c1920078034400303030603c100c1912004111460350100710740c3c51b51409101080c00866807240500f614595402240c00d445040007070550305103402e19072104108a03801e4130b40000c003200100c1c81504503015080c9164581d1b9402d00807640500c02c003011070054180000030030621180140d510701c00c0c1a8914503a41070356640300400d84c00c0707203e44194603901d0b6109101120329445d10781d6458022460f6031320045030484407540032881c142c00381b030040c0c44034a4848080040020f5010741407a404220504071b0070801d8455404030307503034100504000c1c0070025070304481d40605008100302e031154103010700000070307501d808044a0340741d80142e0300880b09000e1407030482c2c08010902ca107007800b03003d010340e45 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 407697706 1250 407696456 407696461
    0x1030507021b04060807060c12030207030c1202070f09020a03380f060a121116121716020f07051c030314072114071206030f12110604020603 62
    0x206254810182d00c5a200e512030801190301ca03001c1c00203100a140a807550601d242c1d06103050600c0005040c001400c0501c14044031000c280d01c01501610341e90000c41c00f40c5001c49101c5c0407820070b40c1542008407519162980080c00c0c1e00c841d4024510440942d408202c01310190a07044910645109006200902c2c6602146406a56600b2004200b00203100c101c85089802c042000c940000282901141d105218a45000040e002d8402030741d0544868501e0700d180100c103074901401e074040203042e101c19411402800b501036403008080c3c050303120361098145401c180c000840c400100c4000018000c1c00030010007440000b84001c1907820090803210402100119000751410303a1409908141c3c40b000540e00001c0041101c82c0204d031165141c140342c0062050804011041d524404c07409440d1402540c0422058103c4c60341002031071602d800071769840c2c00540c02514030303074002400c00100320031104100180c240c02c64401c0080d42c3c458900c000148000941c40780b904a40194100204000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 407698956 1250 407697706 407697733
    0x316120b130e01021207170f070f0e0d06060915140d12020a1209050f03030720010207090e0717070b0a0c080d0905060603100209060403230607051201050103050702 72
    0x10000b186510400181000c403002600803c1c3c4900b604c0c0400803807600490b07044031401491009a019540d160400310608003040000c2c03006a0110080c0b0800504040649039a034070401002e0300c42d0b40000c0280042511440d850b0000d140b00784810750409400c84000501800d05405000c03042c6006003200d1600b6402d480d00d038100c1c1401c5a40c081107000358130790000061658544103100c1c50865503003410705400c203400e01442020710130040d03101342c1c401d2004100007084014803a2161b0724030340c03030842e02c0300b00c600040c2d10f045130a400c5110b049061000507102104005054000c035405c800c00c000d80d80d425040d2030342e182c54084c0a00d900601080250900c103074090307030301d0030b280300d1045404921b002c010014080803150520070881b134540043c004d0040c545010000d04581c8908004114640006140021014810740c0b000030213440c006c2c55584036904100c22520301c55a45642564a94030b0100001040c592111002110000040d0004203403540320b40702c0e0502c00d41d203503001403156900050 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 407700206 1250 407698956 407698961
    0xc020f1c0318050a03081b030610090b0c150604090201120506061c0b040b01180608090114090a060c0212030403110a0c080a02090112020906010f020708030316120b13 73
    0xd0400a00d0b4031401100d040b405803810b80c9840a003d0b401a2140c07002500d801130050030003030243c84103189081200e41728006180704407500024101ca5511244d200100c0645d01c02c861a0b20110b03114402007101c4801c4000492440c4150900c40420101991543d04010445035140700181c001044107560710300391099a0b00607904503d005000340d042091008100b8946c1c250061072100e03060b100c2c0c0410740e40b8100741c06041483ca00900300303c50f4440e000d01540c0b0800e54640318900070411504003242641000394011001c0c401c0c11b007960320031f40c43e1800c0a1580c440c00c00c20121250303071400713a100c05007074804101c503061940001c040c40d285440c1c0d51801c44002050714954602809800001c90015044046103002060740390058046075280e401000b0800d00140d00000916440098007c0103944d8a10307069844070090800148210000c0c1082307140c2125034105000612000003841400c84140d00c1c4095100025070303030b16081000318a40c00c01035a082c0403030f241d040307501401071031645039158 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 407701456 1250 407700206 407700253
    0xa0503120709180e0d08150621151311031311040c0906090801090c050d0510051f080312060f040f06090e12030106021504031709060a0c020f 62
    0xd01d001d50b001c585440d06541031502c5108410071242d924001c0300340c0d0303000034040342091201c9410048142e181c000e100c6480e0650400a6511603071001070180c105040081d12007100e10340400c1d4500c010320703010000b0f1301078400340d050082c802c42241005040303c122a014500014204c2001e40c3d003140c503000010740c1c451222180c00ca54144204802c420540c4961041c48616032160307039856080c500d0802c02a0404002d070b00221f515905064028001c80c22003a1f00600300c0c0e60941d01c50f15642030505059061101c0400c0e280a02d60501d0f090214158a0b140402c0c003040c00310320302502803986c0310140e554a100359001092a98507610014140d0f203060140380304020703809480418150640d21204085454a070000f43c42176a03940e4030a58504810000c0b0400b100d01505003500c3c65040c00c80182d600c408804441c5040810307000001c04041c0300300e8400c05210f140e5942000ca07414420144ad8980008885040c410f070714101910840c81c1c40011442009a0f0b008041c007108541c041840c07503c04003a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 407702706 1250 407701456 407701471
    0x90403050702010e010e1e0f011805060f0c15040201030b0a120b0a1d0115050603010b0f0d090609030309030f090f06050304140f0703031d06040e060d0b07020a02040e0a050312 77
    0x4506d004c55403620b9110556641403160340d003003242100004c02c046100f15401243c10049500390820410400d050f044007503801c21265142c0f51010304a41400c03074401c1c1c1661042070302910600d1941581c94546550241c1d00c00d80341070181020380028003001010300e110300e42040800e00312000105081c010000d802c540c09030f1010400110b03105a5861110701342d0342c0100c0d503079551741c500b07183c881d07820501da400f0300707800c6400502d1549840308614142c000d492111140100000340021160401e501c4210002d034020418410b8103000e04002d00184406001035022845040341404850b100309601070564480c040005001400e183c01151242c00051048605030025441d0003005a0300704800b540000b0103000900345c1504619000b070601c001d0400a000041c210641034049a499000384c80a5851316401b00031141e551030001280c0e5400d4401c00340690301424244000f89602181c541c500c18000d5030207200144200141d00c0c2d8480e0031020191998005020134a90141301d20511908501c1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 407703956 1250 407702706 407702717
    0x1031a0303040f030b0108060c0306060d0b130606030f140a0b0d05160f0e011202011115042306190507090308030901020414040c120209030a080324090403050702010e01 74
    0x44440481d1540d401904030342811500c4407010410400c42003c1d941c050401c01016040d030b414049801880d034040600b160384a0030001c10210701861080e40a114980002040410598858401d0000800781805220b0010b0300304980d203124002170b8086c001040d206c5200b20282c95980c11460001050180c804540c00000d01f030003030000c58002c110340e140b00608000020486480c01d0200240c1c2220f6a0041c0c155143d60001003001c015200440e1541a80a090482c070841084103120b0510300d06907001c0990040210174482480031414031a07411a001c03042d003048008226036490f075502c400b110341d441e100c003280c00c0c034070030709031464028603001041428a8049142c0326a21203069400403a2004000c0e0b40c0458200010020f40031140c5000e0010b031000c20980c0860b074001000d19011401e04110560005035201068504114071075089400414240e100e080800d410002069412400c0070300d1504803000035114a0040c141e50f0003280d050304c0780e80c94120541d0041d12010280d0544505100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 407705206 1250 407703956 407704001
    0x90c06031e020f040e10080a0b1008061618081b040b03060901020304060614060307030507051306050c0d0305061c0302100e010c0807050f04090f020c011d0106140f0103 74
    0x5880b030018100001003c140142c41c1d50504030301e650381000090185002030440f1408104030343c000301d100c0c0c01494220b250700baa281d40e0802d1114070541940d210081034881c03042008071050102e605200011010b55401d64800f045480310141840c0d240556541604000c109200300c3c81481081c012910740608003090420038500000e003802d10441348101c9070394001003040104449482058050102030100d40c0e4240c021002040883c0001010070040c156903802095a8a00034015a10405102d00a039000d40c0e48031540140540c0045000b1a0f0f98411a82c990520038024000c980c402c3c000a1324600b44480d1340141c07075000071407403074055065014140000c044c031142c0d40a0345403c6400070300049005041034a005211040c010516810048248442145000c6c2181100e04544060001017080c2030070320740c1c2d01c009100740c4903c00e94030b40c41c00003a41b00c0d20f0030140c04043d8400c2d000c0300802005a40b0043d1488200341103200e070b5070251600e00142041d42c040d600c0180c2900c108000c13491242e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 407706456 1250 407705206 407705261
    0x2010e0d050f1c1803080406050f0709060e010e041d15011a21040602042c070507051f090c090603020a18180b090708010207051c020a060f02030708060301090c0603 72
    0x13040701c007000750001481582000140001401281c1e000f0300359646102c402d1400410080c1002031600600003004201117142c03501340e10a1001ca1b9040350020401c000b25043d4188170300300081c0d50140d41c0c40c10b0203005d001511240d020340c00e880c125000410003650106141046170346a038400070740800d0002140452115155074685441c0c07080f8481e160041e036a41c01c0c118441000150340c1d000031585100f00700501e485413030b51010301e43c209203181421500c6800c50301e0190700b04045000c1008060070b10484a804101403600028a418094880c60300c1454a9482c1c60091701d0701d41c007010750010760b040b01c00c1100103601801041e05d103019a000085e542005950304c3c0c424100c010041e40c1018015007407000340b242c1440002c000b003d05500840c50205250b030b8040d10744d0015480d80f58030135184644800d4043c002e00001180b5075000c081000b008030b030620350000a42003614a00001015034000945a04051140d03034052134028000c046180e1402c074085002e440e83d0303400301032819074440415142c03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 407707706 1250 407706456 407706491
    0x9090c1c060803091c0c05010818011a10020613020105030c0f0316030b030307020d150b0613031a0408030a0b01052101090b06030c030c03040f0b0702010e0d050f1c 72
    0x14100c040d018503540c0813241c0801002c04c00e5040700b450440d400403d5000040d9601010700e084510031f080103030f2070369510075983d480300307000c0c050b54855942400000400d00c0130f0003c0c41c501d0300c68101c541c11f00700c081200040380d40d01400c0b207003204040c200e41402c1c405580110040d6034040c04c5203940078500001c810040c0460b030025117000ca0505103c5504c180600d415000d107462a0350180e004504010b95900011100d654400c0301078141d01c042400320081d45455000304440c1e5201520b4a0355a220001d80110030000c0c1c1c0c44281c1e401c40700103010801d00c00844000703034081c0303401880f50360950b180c19250341c00a1000146050502208016040d100020181249085600e1049900b402d6241c107100c241560320041b2414802d0f0740400800070255180d80a60340c118910031011078595071180352130700c100e4501e04006031090b04450304100001d50305410805c4c05100070400d503401d038002110181c0759405030021041954805224030601c444003015106001d2040740e00c00320710310070386480c1c000b070307 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 407708956 1250 407707706 407707709
    0x50c030d060305030c010f05070210090c0911041505090f090a0e100c1206030507030f0611040b04180c09060e030a021e01020f12040e13050d02011a0609090c1c06 71
    0x10303d600081a82d030a0b0308000e1050809070100740d2400c3c1319034507205400035101c4821020000b03c0340c7d0380b407041d801442806501d12003c0e14403e482000700c1c06d144180d280f4950002d01c40d40c0041c482e5105a140741c41d2046003580c0c0040c0d00038010395990450107040000d450310050030640826034a00c103d04881031700b040030fa00764483c120400285444400c02c001c1080600501d42c0350894202001080000d00000748101100d41008a91342002c0c201c0c13410038080d201c8400d194001003000315010410080800c000c1c82240c502401101d180d400d40788000081d6042002000041880c0f00780400c420b42c011001c5003070041c0c0003810360b9071103184c9500191105203a4030b0b40307032612541c4d20016051540c040000c802e1802140000301040804401142c0e420f214600030f40413a9028803001c108a1140b40700e205041070340c04402e81e0004580498024024120b400c0b580c0003218401d088098107040000c00c03107840543c00b81c8100e50f0765036000d80700045648407004c4499070070b1410444540300b0109101d490b0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 407710206 1250 407708956 407708963
    0x3030f02070c03060f060f050306070302130e0115030e0d080604020a09030813030c0b0403170d11070308040b13021e0d0507080f062401030b010203040510050714030304030f050c030d0603 82
    0x40d81d0f0507050045d00c00caa8140d04900501e90030080d0034805075400103405684409942b801596405006003003100781c0f0410b80c095450900700c0d80010508000d80b100c0c60b03070740b072995580c200140403c0643d2142c0c0e4407080028a40401e2030358005ca01c41c1d08103a00100b000320740c80d007400810300d0340d03950303400e40c0380d900500c101641d1450b1a04148200102c0010110051070161115401d041c01c6454200c00c885a0707441220740b030712000401c08488822500520150503400349216200d0314a810080d2005400b26000c40c0d6402405000942036404a41480204c9401800541d450064031045503111412480019400490403044100150742080807201803c5014082c3c50008100841d96241480c003a007152124404010b40e11015100b01c01d41604219091a01140d480410b90060381035120307541040345c005081d581000f03001a0801c006000440c4240c45a01f103851030740301c403292240020f03a401000515079818000702c1510a0018280781c0119800ba02d2400300c0851840b021501c0503070045 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 407711456 1250 407710206 407710211
    0xe0909070542181c060f11030702120307030603140a03030605042c013305010309030e01031e0203090c0a091122050405240108162d031e061203030f02070c0306 70
    0x1555034111b00d02405a0303603030051040d40c0c154103096001a44582c040d608d0000d01c05030210000c4e00c007a1003508034000850300308866050115000740c090741c94181407901500400e0800c180010070381014401c0300c0813040c0c10075031010070503482c00e10302c48006036246180515641b24544200c01450110024040042004144010003101244801060750b0703a409a41030515040304040400e400040070340b9600c1003403170001500302e0314840c003031070103c1022032405806201000700301824100154850340b41034216002d0800a036103520b440c0c251124804050252001030040b62050300a00c1c0500a07503030416443d03840e000e0f45610102e42140c00884101000c1e5404200b488100003000394200c2c0200d2080c40c00522900c0c000f6041801c0c0703082c14141004202d400710080647c2ca4482c00102c0e25601c94000480c40c1310005000103000e0100d400307075080c2c03c011400c0041c216150520a10044070b055000440c4d22200507207051b0002c00e1101d69051005800f008514000307056040d4402c0a0351258000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 407712706 1250 407711456 407711471
    0x40801020a090806010801020f040b1b010f0507030e0c060706051017010506040605010c05120a0c1a040210180e060d050607090f14010e0909070542181c06 68
    0x444c60084184e2107020035910420454000f0301d8020200d400b554002c01d40c26a656501d84200d00302c400c50b0310f844130425440c14a4006941d88a5001140104e48a5609100059250b0a01515a40001d05c1c02da8040d500b0040000001c0c03854010315400a0b9410507403d200d5a034509066940d8000307002c0d0856a5940c1040145070318061103081e029040a10746001031904582d40c0750741d40c04000c90076060140e00881c40f00d84031481464810000da07480100340d803070300003400d00e0740d103088005075800c03841199400c43c0c4034501481102c44d81d035003808405145812901e80742400e28801c401070a203a0300301181140741d5000c26010040c00780611001c2c0c0e540e4402d1031a146202940c1220b41c3c004800e1200462000340031b90ba032103c60184440000c45003d15992281e000491404160341c0c8129040200d48075000100c42019500c0394102c1c94005845c800306080780744490442e03076180d0303100010020502c034a00f215020154000e5900c000a00400b0814810781000d00640d80c0d000c80071140315884002 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 407713956 1250 407712706 407712719
    0x705060a081006140a0c051911040605010e090708130b01031a0114060d0f09020d12081303140a03061e0501020f0d081308190c14060f01090f02040801020a09 69
    0x41e02c028000c600c0c000c2c000c8015907000503064403d030000c0b201004500030703400c01440824000c0c41000c40c150074a01151524928000700180107090707429115500c2c2c400c0002ea01d50041c1c2140101c400001c2009056944002c8243da2070704000e42691400c4240c0d0760310b01c002132401140709020394000d1a181030711040001280d41c0c4002d050300590040d00c4a842c1c1580306440d414140e1322018102d40c0003048003082c1030300b01d8000704042c0802960000358001da56003886100c4203018070941441c3e03034203070032a41c80641203280040e810340d000b0002a01d80f6904079441d0741503002780c800d01843d49004200c0f9a5685401400007071380314803454200c2c8c2d00010401c010741e01080b1080d68050040701420704c0c0f01c1d0200d03003d410090020030f0002c114040e4040181000007070000c4414407601c00005850721284400000c0524100d960202e4078039031140c507980406100051100d1050441b0400c9502d540e081040580141026500016405400b444081081c16083c00542046c403ca65204882c8902d05403 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 407715206 1250 407713956 407713981
    0x4051203210f180714030c0a090e1e06040204021c09200d11010f1125050405040203101503050105092b050702060f0904020310090b01090e04060506030705060a08 71
    0xc2c405800c00250910565441801213202070499681c4000221400c040801003401c0c0b004030030505a00042038003001c60074050540c0718000c0700c00c684044491401c58840d00e80c0ba400000703807404801d03070300c003100050041c54150024030452140441d00701507004010842c40603190700c4242114101c00301c00b20440910880018a81501002c542001840c0500c0e240d00e100f0740045082c803410094911031340e5040d180140041007154007118201d81c404200c8485000228240c144c002d5200c00c0c07207110000f403500d401d0140c54040d0750024050700d03400c0005084440240070606020141c03040e4014000f0111b6000c0c4181842500104094800d0101502c0e10f08076580e280e01c491070091035031010030495a0740c008140c42c4e01c9d540c107642c241d070b4450071650040d90f02d005441281c0d038014000404c01130380c04001c2c800748085555601080c030200450a0064500842c0f0b030066010340c8030326800140201d0126040940c2007a80942500c841a4850000c2501c60344420b10780c40100b9450400c2c00000c0300c200c1d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 407716456 1250 407715206 407715211
    0x911030609030a120b010e060408030306030613050c0436050c0603130807021908010b0f03010e0c06090a171605030607050304030c051006060c0c0506030103030504051203210f 77
    0xc4000c2d40c80c05a0a42d409044505041c03040660255034542800003a4050030b04008410740c000c1c411354a035980e5600c155aa40d1040712594060f018800114981c1c40400d24460720555114001d070120307481007030034400202220340c40d0049140e031555903042110502040410302103181c0880c0c404003450b42c10101c0ca07200b6240141801003008004120002121410b040701650b4880c22560b035070700d41400002c44055100c00100c031070101c2c5440001e90180154001032180c4001c0c3d661717011440b44103080508a540c20b507554001a000070b0801101032900a000b02804900207002100f032940314150040048900c2c486651a0340c00080643c08010000760400001d04045000f04840e103405d00b401410780c00003400c01010b10000c1080310003000024000e0615040000000b004400d50710f043c0104102040781c3c0c1602c0d03c4422000200d80740c01c09000310307810f881d050b448482c6000d00d0310080c01181d6200b4082114240810310101c81c4400011126001c0c0d19402e044002c410300305a8440c80381407102 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 407717706 1250 407716456 407716471
    0x106030611182707080403081e01050607022103090a090c140a030e0a0c090c0e0603010611072c01080a030c02011211040b03040632150409110306 64
    0x602450702d25115801a40c5949181070329002c814014410950030900f1602c2d211803440d211140c100701e0616841501e00d40300d54001d5442c1d0b4007680391822541e100101400380031172400750b0307007005015509140b001000c11a00c0a0101410300711038202d0311013070380c0781c481d503014681e040090028003603e0040822406852600c104008102d07110324040c089a00095410400800200701c444515029a000000881d05002550704000e42e0b0302e040202a0082d0103015165860940303a09401072058042c0090000c01800091459003005070907030b9059500c01e681d10140c4555840400c00016190161504207070200680038110030010025030b00790381c16040085d00d5800001e580000c1b940c00902480c1858080c00d01d0f44c09201460344010180000000fa8005802c1c00100085c6968000004522440c0211000c110400710382c03001806155407200c101103400c000e00c82220105108505058001101d140b1760f1507056a1000424155104840182c40da035030030303109404160400344291580400d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 407718956 1250 407717706 407717741
    0x61e050a0e040f020411030703050a051e0f0619060806040c030209010e0f040e0304180b030a020105030106110115060c0c06051c050a02070203010516090b040b03190f0c0201060306 79
    0x10240c0500d070003040104090808120141c1c140255240c5601004605030030480882c3e4034070704031030060081c03c005c0e01d005028034a0300002522001c0f00c10301044991035000308008003074441504544a660000d072001d50700500d00b01d0014074482c002d0780004014099034496407030f989010010082210150168030f818140104007440c0240c0e800042035400740d408035040c800484008010400422080754002081c0c880094081070710303030503100000c41e04416400e040c0444074407101071684407a64082d000380801c20038401800000d00428951213200c0818000094016401d041241e03e45030f940c1c0710030046181a0050300511084201070800307040c507810b02e1894401000cad40f901e58680004401d1340803555690104a0540ca160125040c040e0000c00900040c105101c02140828801031401b02080c2c43d080b00080c40202c6005490441d022000000d081d0b684a50301000e10400151002500070b03510902e40a665030103200314440740b0341d1540006041c034114a0070800302e802c5502c080501c46c6 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 407720206 1250 407718956 407718959
    0x17031b03191d19140d0e060a020a121809060e0417130f0513060b090d0809030115081b03280f05011a031204050123040306050f010e0f011710061e050a 66
    0x46d082050080d80318825142c0980da6003030030364202e0401d180058010002020140085d0440390b0050140079481b2802e41d20b05803156076184803104440181c80b812070b0841445000a000c6410140003071070b00480f9125040c46e040c40f44003245140d141d160010036451248080500007070400141102400001103002c202450400d05540407038022484a58070600304580f01d50301b042003c0083e030f561417034058000c3c00400101400d22440b5070560142c0c134010320032075000c00720905401c45d10401c00e03a006805401c6e203000380e141c042c109001d245400b041c0802d25882d0200081d0320107040c0341a0074040c00000030a40100c03c92004d0900c0c14814043c840e6008841950001c0c20803411502195424204a0346481141010442d502c40b094041c83c82c8040c003003000024440540c100c1e6100c1c3c0e40c40091501980c1e01c402d07444061000c191411281482c5038001880b8111404c9410003101103450115843c450342041c01809580c405e4004c0f141200e0001003400540c074002c240070014000c1262401e0145 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 407721456 1250 407720206 407720233
    0x60103151a0f01030e33190902120316020a08070302151b240a060b0304061508031303050106080d050a030507030917031b03191d1914 59
    0x84448181c18440c00e00a100100310380c0c080d030b001659080e4581c0545002442002c00c100750501030074449072104144030610843c00d0080e64205106040c00118601080d50b00d9815070700034001e00d0402c0381c0099040d032140c00c104004002506070003660400b0000b00420b0f42c81800260b2903039500629542c0c2c8010300600040e518241000e25140c48006020348503510510441210f110100e9125071900541c040e08411100000d05201030aa00008210642c1c0381c1c0400101101d2440c401c4020f014418404640080e09980024036090310a0305190b06050300c8034846800d42d40045109030f10310200e094100104502800740c00010010312029000c03247c41c03450003402038800c0000607000c2603500c0c000180c60398065480600344c1d6401100751509100a2410004198415100b00c856494030400042c40342d860b03002100e10800034100103a287e07110802c00c4401601821010f40c100c0741e20344d000701c14030380000c1202003007901888200c5a100c08a42c203104030703184e0064406506580254010102c2c2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 407722706 1250 407721456 407721491
    0xa080d0c0b0603030409090c031b050f0f0d08031005040e0f0a0f060e060c0a030e0a03020c04110f13061e020601061110050702161d130201110f06010315 67
    0x111a008481e60240d07507a84000a07040d440b0760740104000034a00810b02040c0910a008501580c3c42a1600c6d05242d01c00101082e01618511403e0345c0403142d966540250308100000b40108038014110f02c1d07074101c0e955101070399600201d07224680070446040804c107a203014018030800b0318907000500b41e840541202c00380c98100820015111070080501070701000038981c0080e260b81b6518040e2005d5052142140700741d540b1040c03502001904102ca000c001200c0800c2215407190301d40c000b03201e850501014800075040c01c054039030341c4100500c4020110b01c1807030300400c28090f4803000c2d0700c03c1c5414040d01030456000400140c0c511004c240340400100e40008001d419504113081c140405444400c0851511510790160540c00342000b0502040c02c2e00050042c8140c0d00e03929042030841d4807000300c401c1e50f0380795501c450b1407101500046100501c508000f10741c00390041c0340002c05600301c079407194030f003c50000140e00795501c100010002d0014440480000440010342803201c1c541d135004070a803 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 407723956 1250 407722706 407722727
    0xf0312050702130f0c1e09092d0902040e060f131518060516020a08180d03051c0b0303070b0a0b040f0902030c1002030307050306060f0d02090a080d 65
    0x90060001d0910199928256000410306800d8010700200031030304c00000203070103240ca105000c10051032080101030341c500c5034070800011503a00c204030585807689000c050301c2d500700540c0d48800f02c4403c0c0420b504108141d000722100700c20700400c0080c40d510502003102c0c0e00004050f079a0300401d0600402520103403000b42c00c81c0c8180c21003107902000f2704120b00218503042401c04003500d405001140480951a5000303514095541004117648007018890740054644080d40140c10031110500001c2c2e0000142c841400c40040300e4541868641c0400d0000284210a4001c40d00105032000815010300c1d0890500711710050900403141c244010a940340201c420050030700d200e00001030b8401050703034001801004020002c3c072075071440f1070300f1400130400c4c500240e0281c01410414441c07800c244041140840c5980d0055145a903111000c540c150800780255510003420445600c4040c1c01c2009058090504100165030b02c50b100e04001c0498980e81c001040e5820031004802481d42010f285072 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 407725206 1250 407723956 407723993
    0x1c0e070e1801060e0a110409060914010803040513020705120f070501050a020f09010e0f090c04030506150a03030c0c0905010b0424021f0e0601091d0a0b06010c15051f0f03 75
    0x1441b02c0340c0e6160007060b000d260856500c051605400180b0054160040411000c00007406000d598131000029107074400ca004c0c0c203421445010303031089404000d50080c1007490041c0250382c4001c0c10000b8114499010341e41c03181040343c010550009006080c4a01c03038000b1a03e490851800c1c4803e900700120780140c0c80c3c800d050110010203061030346c41d001f1421800d260010b00484140c546418484440e80007804140c2d400d00c2440300091065095411398015640000c5c090000c0303c1c0b03075a9044445121080080383e803480012400181d0182c0b40c080c443c00303024020301d02034480b824010264180305645844444601c002c104409886801140102c40e80700e051580400310145811854050402c1b80780402440c4a01c20000505126030303480908200903503084d103a150b100300d14400750b95402c01b0402404001008000c102c0ca98091050ba495180c420700d540e83c2d280d41300000c924116101114482c98450b80c9000038407040b02080b10141c0038164000c00d602d034050070f5840e2905003905560110 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 407726456 1250 407725206 407725211
    0x70512030d052503090209010e060a0b070f12081b1620010f090b04061b08071406010902070b0c030a020c030301081b12031c0e070e1801060e0a 63
    0x64421041802240c4406008440612003070518407510030780c810316108005003420101e148591194864002d1030b2213030b60010241001c5900740b42e60400e811001412840d4800c09400e17000a00c1ca40d0040507241e014094008100c02c2501400c00c1020800301c2c40388803040000407001c00141da21090201070205d540e66003019250700020700e4544c1c80c088600006013481c0743c0c1d48070600210605003010f0040d04000c3e43c40050411882200b9600c2900700c0c0142c0314007030310501083c019548641041c0010144810780b003880c04846480e0200d0395030201409407409029811068500c41c4104403450040c64030010442c5446181e444030f204000015000c080c80003400030104006180313a805541051303c05106030399580d40e40351107c41d03642e26122030300482c0240c1400b001d602894061003468651858401440ca041d2807442640980c1da48040c09205461b80d41880c205110740c01c00070750000c2d104011030030046041000d0398861480654002900d1603061000070301407105a001745581107562400003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 407727706 1250 407726456 407726479
    0x30b031216030c170d021804150603090206120a051005010e030d1b0c08030a020c0d0b040210030905010c09080609011b050f190905010e0301090803071d0603010b03090d0c050705 78
    0x100d41c2040b07403001038800000042040c038100301c174a5006045591900c0f9488030200000f609100076180c03c03244c1c101641081080c2041000d000781c1080c401144001e00c01d500d40201e080043c0082c5006840d900040c2d545c4208101c03903242d407240c5d0b4202038902420481006802200001d507604480c4954508000000900c3c031080e2680070362556685910004241c2c0c00740d1a00c8207141c1da501b045030b104c00103110b048540401030500000031444540c0080581c0b209541e1038003400181000002e07070100309942e410422010460a21030034a040c2034607658030700b940385040701007460704d07401034110031850345002403800c440d0026025000040f1a41c2c18400d4981c0004403e100050059100021605201852841102d07501098a0096460076250851440507110500d8229084034200a10039441003010032802405a034001071148601d0700c0c0c04807542011008100a07030000e91103650090b03008018030103008001e000503a2800410724041421004a4503041c1d52080303075201d0540100400020b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 407728956 1250 407727706 407727713
    0x20d08062b050a0311070b0403050d0e0f19140f060301030f1a09070e0702010c02100e03040506131a0c0c1c0609050f0708010c0507120e090403030b031216030c 70
    0x1c040d03007030581110694540c496541800b401200445c0f203071501034017070740e44082500903040c800d580640703401000804899407182c8040d00c0205440c4e007901e0784a01d03415050100e81d5580c2442701031035151180303d51034107071500b402c0401ca5040b1054562240200c10a50100c0303889850640b41141c2e008000c0901e902d0082c02c1c1000b00304140351202d06000283c1d000c01241500019a0b407080314449100d40030242e5584104a0880e550001c40ca001a000130f1840001c401c4623402032079803d14100f041e039240641d00d900086c2c4030b5002d00c03c58041140312600402c1550280441800320100e02c8400310310304012681c040780c48010462180348224542c8601540c107001c62040d100380241d014500300602611b9040c8596154441441c80000740b0270780ca00401c1d40841030040014440a5132102410b0044668401c42e124803200c4401003000490021000f099541607801345c0164026140080d00c500300109160801d6a450181c1361040c02c2000780328141940340c090f5400868052801e1080341c0002e29 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 407730206 1250 407728956 407729029
    0x10c0816080c06040507050607211803030801180c050304120e06070506093f07061d1c080f06030a02130218040b09010b0a05090406030f03020d0806 65
    0x300003819215000c20407810301c5800140c0349008038029400c03110400c0e541c02c10040c80b44248c06000b0900d901c203039810b1154031160303a030845030404141044084041122030066203441e20b903109a0004285200400c00d84d40481e40703108ce08001010203014003032071510040c000b8400a000180045000800d504400b84a800b030f1514444000300030316941c8005050860b03441c1c0c402d030f803400f90500403800084861040141c9402d101c512050811158500d004060310f000302c000001c1601c00074040207000c00003070f0584101c240c80024000700e00030b5a02d44800044c80c03d815080050011000003035000800c6030050f12103507226001c0300c001c00e8a680c03080d001c03c0c00c100034030400a402010031000d08810f00c1c115000350624411152408414003107500400c0305451492240d150800c9008005001e80c1e0408801802d0381d0280e414a80c1c80c042c00d5402023000c50700701d0b600a8501d05034250010342055410b205103007940c1c40c82e140c020f41a00303003440003804940c00b503c1d2001e140034000454500070100a23 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 407731456 1250 407730206 407730247
    0x3040e0a09150b010e010305090c0d050a0206040306050708010b03041e08280e2202030c13060917010c0e100e130b0405010e010b070303020310150f110705010c08 71
    0x3180251100482d6030a0042d2440043c0c2a01260040003040c889501c81c0c403543e4401d504080c0280722045084c003d01c0310404012209807428080d03400d1000158941d500180000c61041c80005410300c1c0c110360003086850107170050b01110008106000204581c4268800250706070b01c030071a0401c0c407601d44901280b00d860402c225001111403120401001e9800c000d000d0911621102244ca4060080210b1006c541094002d101650329001d5141c0400e54041c1d40e01443d03900400c0c2c50031060823040784182c01158444000100f40f40014040f03042d10003412000c0c1c2c80d60343e00078021204561030142c0713503454101081d0b02070a0740d500c0407980709108201c02d809060b0b0103400040c0400c81c00e104c0c0805424940040d81c01a81004000503650703045401c3d0a0403a441984005c0c180026903801b1400703584060102c8201120202e0082842c1580304400152078069403242480b00d9185103019144400d940030490880e001020100400d0741c12942d40c2c815154040012035441c81c0c030481010121109 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 407732706 1250 407731456 407731463
    0x723030a0c050405310b011209030903050a0803070315030506130c1d06100207151214010b0a09050114221203090602070b0405150912030d0b0a0b0c03040e0a09 70
    0x42d0781c540c1d1a0000001a40c4006000c1d840c20005c90b842e604100081d1104401c46500141000004002401040c0d000200c11403182c85e05c2104965240c03101362400150b55800c2d42d00b55000000d00030a280c2600c00ca510322211081341403066842c5072203258403007600401124503030341c00115400030000c4844104015090a08603c55014049081481340311002c440c00e9000b581c40c012180010303800060031030204c6046216136220003000030001c591411a40119055442e15200030b4041c1207103812030a4040d04440d0b1007143c85007003044c0010500e5040d5400541802005058000c844101c081142c080d110031396a01103000701c0c05180400304100d90751003840b0902c5007282007810998000307159411a01d1540c220b80b8125102e0710307a510b0511507071007401d9000d901011815084115071002d40503407030000b400355502100201c100c4d411a800031105001e06075864580c211346143c505400009071800700207580c01c0208407200b0641c0ca03c154003070a4087c02c42d001c0010031012454100d0080e00e42d1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 407733812 1106 407732706 407732719
    0x408160e150904212615010c1e03050711100801050f0a150206042a1a090301090647030703050a03050d06080607090e07090506030408030723030a0c050405 68
    0x2100d20003101c08003d4180c0b0203058240d0300b6034541c1118025243c80d03650309000d1404078800c0a01020161058041d44030700453b040e070140405041d200165682006040c24400003044190795070300200060004101405003260301094042c0500c0c403a0340c07503c10400b4602600c2c005020780d440c07030804617020a6020400403a800c0c20340d00c80d021003172414600e00801c5401290030f6519604040e078a032912000010000c0fa003060010200420a0032000c0b00320329500740c0d007000210b4188081240035119002a82195024400c0100559008045490700f50b0b031132501804c160040001c10402d5442d2480004000ba00403502610500c4940c1c2d80e00c0e01581032601030420544090240820002143d001240039190300380110300803070250030b03070b41d40341e1811440003003001d0140c190200f48007a59004400002503914280c03600f02003403600c04681c9401c05402154180280da01c01c680c00f80 = true := by decide +kernel

theorem cover : BRFrame.Cov 407553956 407733812 := by
  have h0 := BRFrame.cov_init 407553956
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407553956 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 407553956 ≤ n) (h2 : n < 407733812) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
