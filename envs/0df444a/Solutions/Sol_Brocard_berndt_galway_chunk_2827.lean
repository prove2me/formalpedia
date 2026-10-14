-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2827
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:51:51.149182+00:00
-- url     : https://prove2.me/submissions/2fd1968a-e4bb-4a9f-9654-4a6584b2aa7a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 508273381 ≤ n < 508453237 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 508274631 1250 508273381 508273391
    0x10e070602032d070c1212033b1b12120313060204052205060d12030e0c1206010f0602030c1c02010b090f0907060815060c0a080a18060206091f 63
    0x1e00d4030105005660400c40d04421503400500070080c0c2e01043c0725451f035891508004803180c150402251501440007040c55980c10210204501d10181c2c80003240912002159070008181c1440100c4c00491005580309008210400710142004074107981011942d400350b17440d541d18144071601d01d510000068440300d60a11003c15075443d4000c00003510908100d0700e2611402c44040c1505407980180201d014141c44401c2c140050510a042c0c407132030240341004100e55801140841c64941070903281c0c2d5000350000354010007424003255042c181c80380300c5004094652160000c3e69a403282480907001130740b08103002041c9840d46400c541004026200100314580002c000403e030b82c10a40303503010f081c1814420304c91200420803413100100b605042032405407404540741c014021141058030701a0900044050324028144592100c0c0c6510403407070754a901004030020f10751018500000c034102004070021856600000e8801e1003021582c0041503040f5803000000011811070952000080c7c540e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 508275881 1250 508274631 508274633
    0x40905070905040b16030c090302040f0b0607080c0c060c07030b0604020d0e0d0f140f030c040302100201020c011505090412122d050103030c1209090c02010e070602032d07 75
    0x16014a078000ca0041d03420b9407103414410705040903805c11031240c100b4180707099103071070313a040e0003c401030100c81c0c04890000c2e00301c018000704005044c04603407180c5d100000144003400c2040400190449900903011a02c4a0a18070305011042c4a07040500308a42d10002040001509207074001e54098800f91016050030468001c05d0165040350a6580a580060a001d00501ea118801c032661100501d401a000380c40041400064803e4a050307070440000040003640f012001304c11900210f6014006288824450b28000d000b5007242c2d03c068919420b24010b442005d007500000d1082d190010141c1903140c64981e6010700846001c02d071345042c0300d91904800c01401c0d440c8034400d007000c010716861104d500c0550096050401440003000d85501d0b100062022a501c200d56620442d8085002c2520082400b4142c48286481c0c0c001d002d500e0420344c90801c0c440e4103400c00d404c01c45000c03040b110125103400c0e09036101e0140005091098002c0d0010003404007202c150031450300c0d01c1a0702f1926048507 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 508277131 1250 508275881 508275899
    0x711031c0515152803091103300f0307020a1a060906010302072f0301140702120a0908030d24080d0c030e120307140a030504050d24150b030f010504090507 68
    0x100800b804c0210b03964410700018050519400c046503402103020700500140c030314070322030800b0910f0060f12440648000407010807440c9012148061030000e030682d2686480800295100c40c88038040324448004032450780c0c00c0700380707007015409403100070001d09903692010011170003500100801e442c01000c100f050480d000d0100c0100000000341c03d01a420802c5400505003906c5072807009980e40d15901041040580d80402c407000100c20828031f260380c6110f1181c08544400290700485168080001c2c0341d08401c4581d0700080c100e0300303456219244003010500680c000051403207495100d810608012540720311031200304140c50301ca814406640002c1001042000e00761140740310301a800001c0c24000e00812a140c03140440d6528005c28210003540d130300400300c0c021403084074050a40410014200405584246c0c4003018203081130990320300011615010380680e08011a41144105005c034104120030100ca12440410750300007281c0e480d140c140401031841400c11340d0b060003540000315803110 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 508278381 1250 508277131 508277197
    0x60509220c020d050301080c0d020d12180e0609011e0902030c1b120d02030a06180c0f05040f15140f070b06060403020306040b0711031c051515 63
    0x11100d40010309007a1000040d01d00080c048080c0d051041c00d00040098060020f03041c05001d070291026000c410031480492200d6020100c001e0004501c148a076088581c01310070480758014001006d1045a41c602070300c68101070176145640c110001d100140091000c020054030b9114420100f0000181d84009400890304261900d0031b08140010740f030a058941d02030565004074014000d000a501ea2484501943c86020394009580fa00400016000314a66000500400e5111640c4e006020f8884180340140740d0300c44100c001c01c1d142501c100c500ba12940c152000e94403074811141c8503d0422a0f80c0b503450801900c000c0400c410341800400e00340ca040c0261801000e880150f5440d1704c910300c1d10382c4040c2c200400a0707004020911080001d6a400a501d603085600030030341c0541074480b85801c0710704c006580240c1a09100005886580800e6444080b10140e4610742c100555180d80c3c8010869007042c0c1e803400e87c000d91112a8044108031000200f42c0080f0181c06015803441070009400c80720 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 508279631 1250 508278381 508278439
    0x1e09100902071a0c0a09140d1205030402040c0302030105030309240417010507020a080f0a111e0c090606070b0709051e04180b150307030501020d05180a0507060509 72
    0x3500203a0380424480c034203502c3c00d810280c070041e100d0070401800c40080c008045803290a01c450302c82822040c0584400f40c807000d9454000590101150107004043c00b41d62045d20701301d00947c0b6159540d01018809d100340e87c10381d44028069858a10f500301007103004e00718050400220a100c0d00c0c0e00790380d030011030010001010030040e24a4100e40c480c0d2007a003101c50003008517007503402003055180010b004d40200c4140e10b0cc1c01110a07203a080180b0211a803440190208105200d00716201c100403100c00f080760f42c50702d0036900322518961a142400541074090345c100d0342000f82402420009039010101075800344041c41c0101000340c2e520005403020b1490708440c80400101d208005441c10701c0c0c06842c5248800011240503440c680e03613407c0c07a40d1002420142070b4501e410b809801c582d401c0c010172009503000402507480f00c4078468060024401030f9088a6142010307440303000140c4012840401040d0400301070807500b0301d840030503074050b0700c890381960f40106125048101c2c40045540c44c1513039 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 508280881 1250 508279631 508279643
    0x3021507110f01050115031d25080c240c0601090c09140a0306020903030c160f081606030c110d021c1b1e05060106021b1e0910090207 59
    0x201d05411242818031001800d4040700d0303414000144802c034108550b14010603550315002455049210018140604a0b00c5014041c02004244140c2a1103102000e0450b5104004211241e0b03031200c02c0707991a202c00380c4460704101c11103d41a5600c0182c120003411f4008406100d15100640346400e040031001d070000b55102d50f41e003402c1c00754982c3c0301800c06e01800004070745081380c104c1c8000080c07400d000c034400102030580008000f583d07500c1c188140c1e508000420112180342a083c400e019001c1141e020340384568002160000c0c0c00280000c400c500ca08500c0b500509907820701c1811000b4201105c082400d00403441c602c0800e85604200416400401e9800b4088881c0c0410364800403100044081080010400f02c40c0702c0d183c0001d014102d042e900c202e4855030f008032144070b468200c1e200e42002d05076004c1c0c2800011425004a425aa04462085440480c800e103c080108078281d0b20b0b0010f50210304907a01d44054100309104a41050060035035103001359480c500b902c00da0380b142900b1100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 508282131 1250 508280881 508280897
    0x30604080406030c08012304060506040621020313060225030201051006050a1710030b040f0c090c0e0d02030f030409020d0501080a0f031d130515101b03021507 70
    0x1000d035044c814001a074400d80350011080d4901384d07680141500c49200d002034190700c02e107080e440781d42d1984044000c04020f00980c0d11346075220005016020740101c0c903072407404903e5640a100019108585c4a400317401001c0d0803804e91070f180c0d40c00940001300002244141d002000c0810300009180300c00b5140300707034004111481d101e400b85180107040e83c4a030301441000e208001d0381c0c50308103240c0b01e0211206131084071580d40b18032082c2c22076040f5900107408000c0c40001c0c8401d1085040041201b98014030f80b04e200a503035071032a501224a00490100081d0445140c44518130703150303000c1d52031180010100c1e0fa00e050550306940c1540d00550156221030b0740062a030b60701c00140e0152600500c07010000d000c01c000a134407a4a2007041d011402010070081e0070501c0d42003150320100004104015000d8083c2003407035400f40e0f00a1805441c400c13145031001c840e0b15140d01e05205e402c150591680d071000c44150900c41c1c0500a22041542103065001c0c0d076041003881d8018026240c80f0703202a07602c00711 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 508283381 1250 508282131 508282139
    0x150e0d0c020a4506180f1401051527030d0804200105120a05060102010c081e0939120c0906010c0b040c0e0609010815070912030309110613030f060b0306040804 70
    0x100700c503804c2240c00070342170400c80c02d80c150704540320030141110000d0340d9030400f04144240d60901c41c07054042f034078009005484044c0c80f00340720f0380d490580d000041e07003203807038170030500b6820b0b10706030412203000340502e10401c0104c0003079075083c601c0055514103040c40c42c24003408405091540c00100c1d8081041e50f601c004224080d80d090013045219641030034041907074100031a00040d455064101004000c40200100d09000420014400510002d503200112145a04411144208580c566400c6e24010091603003c601d03100105001c00c0c008040180a101c1203d414000100002003d007418001080014008103081660300c0344190f00c01c00e290b035040760514100342502c080203028a0b01603540000140081c04c00001c03406445180707200080d91f2039694410880ba68020f07500482410321080146e20704064164005180281c460040d441ca011a1841030060328041c80300c1551241c01c503000104082a12001081c00b0b95006090104114140d18042072a0010031b0790222182880050204 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 508284631 1250 508283381 508283429
    0x10507031b0e0d0b0615120a1a1e0102030405120717010c0512060a051f0206010911070303020d090503030c0307080a09020a03150e0d0c020a4506 64
    0xca81c2224140440c000041d0008560a40c00c42d000080c50340d44c4080103d41181c0d19052a042c0401c4030800c150343d40c122000e1010f664003401c1d10407d48a03420828003074002441c06840c0c0c80c0b0b44802501400c50f00858a0f601d18400c200c11591a055001c00c00002c02e40da02c1d4405170701d08420016004141007807508020340440c49200d0403403000d07a40340188070110f29600c0000c403040050a0b802c0101d464940300005014010680d10455100c00311000310300c0a41394214282e0312910307140d02510030903030b41c403894070041d516500c200307a0a1070401c200c40b2002900960241c030401a80110002d14220fa940e121480c50b0f00681d44c0c110031300300100030881a50791206005074070500c9104180143c1701c0f1a4003245403014140001130101c1e22403404031031444081c0d8040b000590b101411a140b052941e00090403c000504007070303000b11701d4214003140b03800300c480a59042030554410070850840c101e003c0042149500503542405c600220011407103400c2d405004040e04203404c0000d400240f8484803 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 508285881 1250 508284631 508284671
    0x90207050c090c0306120f0d0e1017010b0c0a0501020c0a0c0f120b0a0905100b0316030c09050921030106080603010b03060703020f0405090c03010905010f08061902040801050703 78
    0x1103481800d49070108003200900c1025a80c100505450700521002d840d40590304000c02034140240611076403140100c45507110000480784070382641c1c440d13000080d01c3c1c0f0456010144282f5100310500c00320041001d916071a00038130643d240501a2110000310360303115404d9074400060048540d000d82240010301285e096000000d21075000200c490302d00e0701c4001802d15042d800064840d1620f0720000e0500d4200f900440d04650f402070a0321401c2c3d038080c610790020007139010304034003c0c85a0300c50141d0300d96000b09401c003070725006541c40f0707081450000850090300d0b00600c82441401908415010303c001110352200c83c500481e1550b4581d0304241c0300071f00400004210a101e0b0b81498a40c43d0142ca000c100e00390882441e14015a5800c140d01260b03040d44a103901850b0400410020403c094450030051810ba070352051050055980c0c8180341021008180100d03a40303600448007241600c03100c00c4184505201c41d00c4e0140c2082e079512601030840f44100c035200b0220303480d041140103480c12040c04e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 508287131 1250 508285881 508285903
    0x191211131d04150506041d0105010f151d030a1a010501140f09191206060e070203090102121c180201270b0c0a051c17040812180709020705 61
    0x1062090b02e400d0b150040b108000c81e80010b500e43d6110041032036030301e40340c000804c51300c0d4030f412903404582404007e6000704400d2062844684444101141d070511944a6220303084480d50303800e60780610700d14524404404416003e0b8513114594801d40020391a031001c20f4014117047e4140c045600d420009411405c0b802e1005012403010000c04501c0c20301c52091301c00d5100240c2d00090402d4010004d10207682c04c41c2c022021407207841540c4c1c0708106880d04401c040d02c0c00c030710940c40980c41d10f0708240c1ea240280d6210034051f03005040c0301c04080000202610006c0020b45100c0410306400d01001c0883d1649015401402544010346003907581050b031210020780f081200d0035041a03071600b11134110705c0d039000710250100c002403070042ca5042000f1100000d900300c01510740b554064044400d64803951500d410224541b944402c46800b4012411482190420549407920143c6d07200900c0e960720003021714500b030302c6104081241d000200240b84c041e0042d110010398030143d50409a1800c114032031 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 508288381 1250 508287131 508287179
    0xc06040b04120f0903080904060306020c0106060e0f03030412030e040912020c0315060423090a03080108010e06011815030c08010609050613110c0303040818010519121113 75
    0xf0703042040b079501c0b2000710202d03900b001c0c0c135a480d8142100000e01030503450303101600c900d00100b99808148410360080c0c0495905840780a6410465000c3c0310201515455403541368000788010070007805230b20448041709219152003d007503031700751001800311008608142c45c4950844c000142e0b40d50104820740c0012011030003003070f9164040ca801249040002d0045000b0794492003100c00001500200340c420088101e0101c00b240b0300501710742d658160310700c003d6001650a40001035803100600c03810315100c100d840604034a80c20005040c181c2c00d14500650901d60b590034010040d0703400c261000c00514811504000380320329101030035003525160b0308400d040c54038040c103009060f5104a49000c14910741e00001c00c00100424032841e40c0e004084c00207480d0301002003007204100400c4010078183c403001e244502c0100c0c078000116894040c070151044404008071081d80040d0080a40741c40c52090100040f5040348448900400383e048000c00000b84400c207041801503444503c1c02305000c445103d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 508289631 1250 508288381 508288397
    0x180b0f04110d02030607180902030108060a151a031003020d03080f1e130c0e010b07021f080a051f080f0f011b050a0e1c030305011a070206030604020c06040b0412 71
    0xe000030717031a820301902d40010b1026441c00005107564005400000702001c54045440b503075205440741c1c5030741d012105084413504e8008003407100340103600c01d5020b0b50f5104580b00750611250300c0b90b41407940054440e01c6034100350100040160b464600030245140b20b41d84000242c00c0c44840b40e100b081d0701900400081a0001650303c569a8143c0741da41e02103002c08507088111518200150412419004014a11507007000407484014407070081c046940300b034031240502c0002c45070646120160b6058803001488207000304440d05403540020742c00034000209105a03940b8021a030120000a80c00280f05400008502141c42e80c2030198203c013080e402d000b40108003100100d0807003074100c1011174061007004a81c24a1091240e03c0740b5a0100c0090100a405000300a00d01c1081007030103000c40010f802c05001281510340710181e0034401941c1d808003800d00d0615801c008540d0401070070107801c683d0038001d114000c58200b104d5801076005050f03403103c0d802c0a00f03007100742000b01c04482051005074 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 508290881 1250 508289631 508289633
    0x5041a090328150f06170c01081605091203181f0f051308071d0709080601060c1a010e01150905060306011b170c0106050102070b0d180b0f04110d 64
    0x110300a01d000d142d01100b6559040003d04030900241141c8211031801e0345400e1001c2082d40300c5004820f950b5202c142103070420081c82c4c004542508003115034158009890b40507501da140180e014000c40d12000f040e0000e841c1c0008410f6165820401c8619440c006e6541000c41c14100200107500144150150811122589401400a846100380d49003004000030300c0c82101d080c000c03926000b0b45000303030560308896620070704c1c00414038010000c90003d401c0702c0045004a8058030900c001c03150108060b05490b8600041030b42c03008425a8195071030305103085500800d4112070034a9020f0b00c02200d23544040d50429010b640021011300c4950140034000c0401e204a03980c190940790310010900c0e03c44c0ba0811001d0640e1558a12540c000b48003402009408413030115030b20260481c2a0b1a07002000f106a90307200480c2c3e5607004c0e02c43c00b1208101003040d40500c88054000b40c5000e0b03000010541000e40796035a400c2d1440007201c0e0b0100c90008041480b04101c1603629814202030b00321a072071040300c11 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 508292131 1250 508290881 508290943
    0x30207110d03170118180f080a02030403050609010614030a0507140604032310180b070e0306090a02010810180e010b100201050a0501120b010306050705041a0903 71
    0x18412466200d480041d1018007098454441101018541c02100e203055a68203040028900b90f00084101301e4103241c02c0300340102c0110100402c1580082e080c80026020f91901035155110011003800c40c0030400020001c100200115030107610b060b00006042e5180000340007218a90b0842c03c2e00c01d4019010750808101c0c001419001d90f0440220210544481d04c00110948511352000306560800300c03890010590804070080d609403100266103800c040f0048000c1107030348150030180042c0e8181288804181c0030120700f0340c0704650f82408800c10301410300080c58103400f21100e045c254440c0c1410b1b070855034003101a41e003100841c1d0780e6070b07403441c208546908020451600d00304041c1d0364402520310601f00b50440c8204410180003024180c19012000b4080c02c0c0071201420942d00b4640001041241001d050746015000341702c03480940d0031990361802510005e080481045414840841d24844070301c49081055016820580d0319001c040615080c42814000c4810003501d200595140400c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 508293381 1250 508292131 508292153
    0xd090b101509090b060d0e010b01200a030e030f07180c05160609020109090f1d0a081c1e0504050f0d021b04020d090807050f0105060a0e150d05060115030207 69
    0x8000f107008968281c41a002c9880c9000d000966445103052010070400c0c66010346c00348248031000c1ea18410303049200030394000685940303003000041e903010450000c04284103003a440b0380c0b540002c06444100401e0703000c0c40d19048035900440a00101400c1d031900c0c601052181130555550717400c00a0400c0c10006030321090f842e007440044e110342e0300e801000046a12400040c0041c2042207030030004e40c0000901d0000520010442c442c0707011410301c1070900d29200080e003010043e4050b40312854449114810090141884860075400d51070382503940040701c60000c03103c01d10355402000119454a03062039403800032541d1300405c86401100903005e000354040364968981d0407649000d550440e401020500070300c101d44c03109481914203020322081281a034000c140490140040383d02e182003010b50b0900700e0380c042c2c500c00e920800c41c00042100d407a842c0e0009a000c002401042c1d401041e0101162101148480441c3c140c1c0140b00140319142e1581d4421a14021600d021814031040c0e40d9140e0f00d4074 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 508294631 1250 508293381 508293389
    0xf09060729070c03360e15010201050606040902130e07020a060c110706052d071103030a0801210510090c060912200d08120604020c060609060301020d090b101509 71
    0x142c802844030158030751302080c4090321510740245d121980d03640b03803a000300450581d03050b5400040080e008015620500a403406420014095803503c0d01d0b00300d000d802540003039500c0c240e80590000024031144081202031040c0300b50740290060801d640b40c0681212030700c4501c4020f0028041d94440d01aa000400305d0903106603060007a41c9030000d9582c504034183c0c258640c442c2198010916025458240c0030f0808948596508602140b0314400c054403400f4200140380090304100c0104a000d80201001401004180c0101c044412684810b0306115a151090a50540394056201003000f0a860b6030020142450310140003800c051032060171401e5690003a00d84903410841004141c0500300100d0303041e80c0140040b108418500d82140c2c590000500d0a081186074070010744039041074021100d0921560019201e50380e2018100004c01001400154041d9400d0200034a102160320401588901800f01c0d1281858034100502031003165030060403800320940c0325050143d0300a10040169 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 508295881 1250 508294631 508294667
    0x10091a0f0703091e1109180d030b180109021305060f07030c110a180b0303311a2d071712070302120603010606050f09060729070c03 58
    0x4000c05042079540070051364107062003800702495000420000090a41c8958002d44403e98142d5400c040c1600e03441d0102e401c0e1015412010314120014440d03402107024120050030380d031015000d0000d00c849944240c0200a070b00398001427240201c505100310700010002120f12525002180808907128000c000f0010309210350150100c0c100401450411682c200c090244000c2647e00c4201800d10f1070b905420318203651a211810745141000300443e002480000110890042005600950401030040a4921002082d008140d02e414004008040e0007181d08050315407546646070303c503480486500c1300c1e0042841100c090313030032040300981e0300841d00184000d8015600a00d4010030b481400694001001c08000f0005083c4d00b6a010704524501c5082d074441075544d010525003250341074002c21011800502010603628010700c014410268080e00c014145020b07540e03400c20011203000003450604c001300c000c0c2810455074bc8040c0d480440c070702c2d11101d500c0b4580c802403ca041284400001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 508297131 1250 508295881 508295891
    0x8190204020f1603080901090f3005091e0d080a020f030307020105010f0e1e0712090501060501031404110d060b091311040204140d060e10091a0f0703 66
    0x1555240c0e0706940300e600d02428203540d80c40c900f034501400c03c44031841c120040b9840401045c10054148120080e07260700c03060091032514680c860b161b201c845200102a4500d07407084501c03402d880364090300941c0306d0303e40714146c4810110041010f43d5040c03080d855000b41446034040140d50315103810410b155040b00c42e5551b01d2203825022400d2041e19210700c10180300c0081408a080c0d41503100b1412500041640100d540c1c9071a00310301582c0013030325100e02c207007004900310701e01440d02c4031a0740e001040d904008108003e0b8000c01016a00300902c10760f00f40e59190301c104003950b0113000c0e48060030b03c03089503408103192590740c1d0001170399440003003809004441d100d0f90400000340d0000748080c000030302400291402d41c0d41c09014045860048403c1e00481d0182942030030180280c0d410703101241c1c4001c4070f040c240300c2409900120518192001902e444180d49400c10900202000c1c401035107011a058029041c8144c034211031068000e403412180080064500051041c1504140c89160200b4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 508298381 1250 508297131 508297133
    0x41403070305150a1b020607030b040b150316020d020712031b1103010b0909100e0c061207030501050a050a151e05070303110a020606060a051e0306040b0a0819 70
    0x114200c0507801c010000e1180302404107242d10342c903001a116014948080c000310315011500c035540076811001201503070007007000c68034060003904070344641d09005d40006100002480002c10100c20100d180040140020a210f21410500e00c101041d042d180001d028415440000035a1820280b01e42d80c2e220311886442420588102c2c0415100701c080018200012258200400d04009001195101c1c1d864050a1411741c00e09036001441032941e42e0181c61217540b4403146001501d640e618400381400742062032003044d510380b0b004c1d01c446400300810f4105881e102401908444040e0003d078443c400c1c103001040a903803448800070903240c400080151109506030291003c0884d210b0482580383c000c0c502200080d803160142540e98083d907424001e88040c0380423808180300b0079841d41e0041c0c00403400503e035420080010f202c185107920f03101d45413083d03070b46401d06455403844884002900001c00e100da649001d0240c5030301c50600702c81180500e4a0101312540c0c50128905054002000074100340c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 508299631 1250 508298381 508298383
    0x1b030507200301050a020a0f0e0906040e1005040b0103020901060905061e1c050601170103020a050d0215130e0901050708070f0302210f010b1e03151207030210020d05041403 76
    0x42405035010b0000d2200c1e040011195005c1e4000d01c1e03681000a40742040c80030301a100d11804031074014094041e440c140c603904140000713020045541c45003841800b09000c050001403017a80c0c4942c0c02611100b0080d41035104000b4030301c0040e4072040400c00300d1201440b0030303030b00c8808480c02e1744002800200f032041407650f03000b21402912880a03156550180540d02141d1a8108a2180000b43d9a0061000941c01c00c501c07241e9007030001075040700340708000f40311509201c1d41050fa900d0004258042c40f41100000d00d0740340d400000d0044c003003400340004004a98451030307010707003000461000340150303d04001c00610b0784000410702410031003060901800710303000394100c800e000341402d1841600e5510303040842e000e10084e02c1d0000000e000c007000041c0d500242c0d09843c1045003881d45a0409840c0c1504041d01d80c10207072101c2c12100202910520071360340c02000e86114815500600301072851401040768a07400ca28028003550841d01401030200da00c501101c080d1425420f02c0080c40c00762101203 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 508300881 1250 508299631 508299683
    0x3120403110d02010911100c0821040f06050115020a0b061906020114010603060f090908040506040e040b0a0c200106350a0c0608090c0616031b030507 66
    0xc42824042c1c180030801c181d6040d042040701d18010741a070100c000c54007081c030544000032042030000a503170b0341d1032800268030318004020000840c0d4900c00308090f042c048170301d015403d031000c89040c6030300d03521a01045040d028141c0100400c44840d035241c4141480039482c6c0561035401090a10a000014502c1e40c4050b80c404461010007044030b01a80c507048040e0003020b010bc16440641482000012450321038064801902c140f60700c1e0404092030f082810b40540050070084414002c1800041102c2d281c4002402c010070a05807d006e46042a05100103a000040c000718251420201c0d542002070300144182c000c10040c02040680c3e010022070580144501e8000040c841401224480780f0546105d4090049050515480c03030083d825a003940e40b034146500007008046a0001085a03078024036031580d0100325401a00d9a2403d40d100240055000c85c0c66a0307220002140300f0801d040d0711480c12000420812150a961005920043e0481c012418010150b22403621b0640400f51000e00c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 508302131 1250 508300881 508300907
    0x30a0504030c0b070f02060f0c0a0f030b03030d0506130b060405011d0d030905030d05031e04081303150e0613020904140a0821160e030a0c030b060405070507030203120403 75
    0x2042e00c2800c28040c010300b86401110172000611400e40803941100c030040405011f45c4400c05658030f88568220191000070004403180f0034980d0319880d01402e6182400284001403031008000b51902d850000c00410f8412400c104802e149410903c0c03009844010484050316000d080500b48024001c40c05054007000d480c0003074111000c40000c20800d80c1151507001603403011000c3e100c2c81900d4420450302400115403140007080c2030382c00c6e14090b9094203080c1d600180240039603449d20031610200d012001349640304441400c070114076004841100c1c03042401c0d00c540c5202401d018148000420110040514081d00c524160b00126081000744407141c080750741c0d4881920600d01090030721b400603412680b40c8014489400c11890000424015518800d4804100c907885100040b60103c8600802c0008a605442494010008107040d82d120b0303001144501e6100c01c00d46043d000340310503214050000c20034444140030103800a500402614111040304820000d541e1711410b0448180d1480c2031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 508303381 1250 508302131 508302143
    0x90c10120b040f05040b1f030609030c0f12030b030309150a11060106080601080601360b0c0105010f05010c03050a0c060f0204090f0e0c01020307240e0708010509010203010b030a0504030c 82
    0x4030791003405243c0d40009108501510b4511074a03900d05200e21045071200a01a209200c500000d00004a4540c0011210340c02880c22000010081c0d0700c000791442140815901c0c1c0864106102e101a0325004994a074802580039604028040020a0561441418010f40044040b41600380b071807007001c000c010400134a04a0b1103a5943c0c41c13019050302c4055540c00c0c00035074000d0008030613500480c0b41c030480e64907046407000141c2802b2001d5082e0301444510840fa203100002c001284e40c24200030380ba05a0003400001100c0d4584034440180b0301495010710705120406000c0c80200c2c0e0041c0540310350103100d06081d010515545802c070018500c05162200b29440407801144130300c007550042281d034140203801c200788030740342c3d0300300e83d85402c02c11004e40164000c000c42000a40d0040c0c03a100f40d00224ac84a800201c80910204140c52800d018125a0b61218204000ba00024018160030580141c001c500c0c550410311010410322004008015841d00ca030b01103810184505410108150818 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 508304631 1250 508303381 508303391
    0xf060209280b0d200307080a110405040b01350906070f0507050a02040510140f0a05060903010e0a030e18100303030c0c050d030203010807170604111503091005090c10120b04 76
    0x50084d10294000756011000034540b1030005000760300074841c100c1c0c6521000d080c6410146000d08020251043c0b0800758100314501d503030340045001c0f03000700d4203050150300c100c0e10500f1441c1d0806594800e00030b01011031580407000340a11240c2003801030403501d0f05440d044d5520182814902c2c07411080000c000c0d0820b25120412007644c0803801d514040e9001645000388010701c1c54200000003642e0300c08540c1c42510104200035a02e0400024140208094000310b44046009c45490070075560540550116004880741d12442c40d0400c07030361340448076514400382d5034203021508203079404e15400018280340e85c81d08200c48140c0a04071400742c5592100817a074544007002e20080180d0000e1190196500c00c047c3d0100c0c0354040024950f02200742540242019680c0d92038500141003200041600540e9108000d0a4494611300070341c4140e00802c001c2200c0c04d40112008115a0002c107150210b4100417011400c5646400034103003140d1031440e00d50149881c08502c2402000f841031100c1d84207141c5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 508305881 1250 508304631 508304681
    0x3080a0e0109090e0c040c090801020c0a03031409060c1303050d020a060b010507080d0207060b06070303020a1206081f0f022701050403031403090a0f060209280b0d 72
    0x4001040200042070b6070700a506a5078560035030a460700d11a16120503007281c80070410906140e0302c1640003408914280821f682da40790350f2422640710620305204d5420100c041c006160b0140101c3c07000403000c03407011a55141c0307140519142c0501501d40c01d000c490000d030b4001c00240c440c028001442d00501030751800f0030034580117542e80400b454210349550421510101c650b000e0f0f400c4ea090190050700f69803402d0310010b800e00080d4000305040f56001d88d9000c02c3d01c066201c260251101b80d209840060b80d4119001001e0051800d076042c12061030b080202c244a00600800c03200e41b06981c0d0810552082c1200401d18090031a0114007072110784040385005040d03954000c1c0607120303c044190070600c548800011505842607010240c0440c0f0144180b0b04000b9803040295444a035150545000e80b007540e850313901002e014070041c0c80f0143c000c5400225450075000f417080d10a80c0c8245407200c04100d2801d1844812240301d0341141d901d0200300c2c01040c2000e1f8110700341030092009a8440c020340 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 508307131 1250 508305881 508305887
    0x901080606030d030203010f050108090114190506040c1b0c03120224010602190f0b01030c0e0f041106090117011d0906070509100e0a09230f01031b03080a 68
    0x1210704920a1184080480c4850700901c202d9045c0c0e40044542d009050420005580b0030801600f500749079035039030108524517040c0365906401000740705103c0140090300505c0c84203541000e85494400d0340741c0f41c400b81002d504040018088680b2007025000b122407400e045d07442e05a95840513100a80300c481d842c0c00c1a80c08a04e144004200030078201c10010340d07008140b1514801d010790700c003580c0081d10038014204020b0007003040f18450b0011900683c2c2c981c2d207940e204142a801103444d007244020500c030768000c0404407a40200074410764140c500e020348940c03503520b00104442c0d00558000490300e8069104a000744043c2c626800c1c10042c5581d507019104001a9128028040840c1c1001107030010002254484c06481385944c1c503418450203004000209800c1c00c7e0180c14800d900000a0707243e01e508007202e00800300000c0006482000c40e4003495400030000300308045100401c02c00c519072540c80400350659800c0f01e20713480e08035450302810a2110094001a0107400081145490517038 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 508308381 1250 508307131 508307143
    0x2060f13150507121503080f0f0d0603110301140703052208090f03070614180d03090510090b0304110a080303150109060c0f0b0702120a0216290f09090108 68
    0xe125550742d0301c0200811503440c01c90344070204202d817040b18004100040b4440c2130261074404114181540362011000c981c7c94242c0c0003060082c00306c0d885d0750042050084135010028000307030650090007441381209045c0b001d407400070004010b042e5104046441c030441c40794602c60342009000007448440c5103080c49001034100420a03481070025092001050070017080800c12502641c8502d00c45d140b5040356590540c02c121000880074400019050700390340ca441c0083c40c1c1c14026150355a07818106420b11072060f01581200040c4880000704000380d44c01c5d9001c49030b026811441012034035101e10002607048800745c2c0031054511000c0144500541c2002114040c04801d0320307446c00c01c035502d443c20f5400c0300c00300e44c0140c402c840c40d400ca50b0203e0144803042c2d502100a00c141d40081c9a44210a52103401041010005a201841702c9030807030b000c1c40401010700407200300c0300d24412094481d00c03d08030701c01c0a1540809400700c1c0740210740c0c07891025114404002080c031a415038603444420340e1741c6 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 508309631 1250 508308381 508308391
    0x50f030a091a0703050706231303111f0b040204030611040f0f1a030703060e07091403120f0c2b1706100e0f040903020c09011502060f131505 62
    0x8180040d00c2c0e02c00003a50849210a525880e10f80c14190345488910081200421002c040c1d4900c039030740c144850203030190902c0b450503c42d148407032030024100201031681f040f008891035401600380d60600c03c241c02c4040d41100034400042000700c030900100c1c0c0a0300039644028a45c905001003250800c1140c0302a1040c1e41152a60900265541c044600d11540c5481401c3c0500100d80c12440010001001075a204895080201d2080d80e203a101c04080e20049401000140d10351600703000f5000c0540002c108020300314001c0c8000404c45640801c2071180c50b980c2c441120000420740304400082c0280e0a112208151849907074420f184006a05184c640604000500b41e0040013069100040228090303130300604000421000100281c8045041070780d03840d40441011240d41c0c40e0342d01e0780960080b951080d40078044046882c020700c60501d8060b04040541c04888800740516540014095400881d10122a8090b1902c40c54103942c4290900c003e001104003845070300001041303810141c003031 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 508310881 1250 508309631 508309649
    0x9270303090616030b09060f04140106050309010e060108030f07050f010606030b120a0c092c0f0f0a05061b09041805060c0c0303060d06290f10020316050f030a09 71
    0x3d00191422422a80d0150000b540510b44174042409402d2150f5880802c4402900008508240181c00300201e40300b41d1003080029000020082c4100c401c1c0101e84c02859a5001802ca95040c0000c558580c002c40d401d0420b50040800e5480034001c0401010f184001c08100070420251a15001805041c001100034058070b140079400720140700c00034a41001d01d13004401030400034144001c031405480580c88840001e4040c03040d59500c3c1522005443c03e4110400040c43c800100c1038000381044140b0001c1c01d00d64001140303900220b200803407000e91007040c03980c030b07030741d10603502d0178a5002401003a5000350494540b113009405042c440040c0f0310700d40e00400c212129540d820301144103620849002c0d2040390003d0011800500b400030409400034400c28000c5400174402180031015403030800303050340110303a070b1800c0c200c20b0074a10040e1400040c01d4481144004020340080c3d134a104075001146294070000800d070501c035042c4030b030200985522040d240c4d00d038401c0100405040041c0115111 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 508312131 1250 508310881 508310911
    0x2040e07210b0c042426060301050606090607060e0a08040602030a020c04020a12020c070321110a020d260d0b0913110108101d090c0d02092703030906 66
    0x1a0000308070907641100c500c05c5003040e900800c04070380d0070b60b80300003203202061240f502c0d0550041001400008000503000d0000c0b051441e10f4010182510000340105005010400400c0320b2034852404803240c07513800c484045800d90b100d0403010f20306580144d0180c01ca60010801180940c0d0110040c20320450030342c00c50310f60400c0201040124880c03007290381c0226200c0328000701c18060f0394000d0300312034031001c040d20403465494880103c0c034400c01074a102e844590504801c24503800503890044004070030010100d080299000c60241c411a01000c0e00c408020042000c030b85020b00002c00d20207a580700410b03200d100001c0000003034002e03400603d210341071000014030002400306801c441039400200443c510b402e00c0340191103254000e01002e516040d1140042414800a418029488201d9000320900d107042c1d65180e062a40c00c1507042e200c0d0003601446c0001da56514903641d0005074a456182c4c1c022030329550007854125040b203046140c00003100b000901040428035a20442c024407175616 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 508313381 1250 508312131 508312141
    0x609100f1206050f10050d0305040506040b0a0f020304050d0609051c0909142703130308040f0902031003111c1a09030a02070b030606070b1302210a02040e07210b 71
    0x156040040360039405d0703d05000c00c1045540f501c581e9036101c0d42c0c040d09029241548030404586a41d00035000402241000201c000719a5031010103c44410351502c09107041038141400034883c030b1780c0580e01404075512a00040e0030f00105002551141450113400d1000b46002c180180034451148181480b00d440d0046070b050001602c13010311310401040014a006540780754041400c00c1e146440344840d4030050141e104a2040d103403181c0091402424201c1e12649000d8040d60001459041400d400d4018014401079480d005911003c1d6070340702e250128080141c00100d0b0700c1e50b6840c5003806044541003010700034000c0b186007608403844802108902070303079000348050340c0340b00c1c1c1e091040040c1e000c410704000c11142c0300090341e00310000410141c039041d00e54940c01c580910a40d0070b98200c40d8140d03100e008500c0c02901c0e13000300c000e07041c881c030454400f64003e890304c40d0b030342160290059880342c0201d806902e05000040c045d000310207000596000703c610300300f6010541d0b5070482c4c240894201040b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 508314631 1250 508313381 508313401
    0x305090c040903080c0309190602130f03080922090b1b0909040b0402130c1706012111040504090804080c061801050c0a0512070213050106080609100f120605 69
    0x30641d40e8141c0c0700c4c0815505e40580c1c08829501c010302c00c0c45c00707001c0da00c41d01002036448074004410500072103001d619a1004031301d50302014040e9000b1281e01c803e045040000405010a441e900c41086034040e01c01240304d4854207100c0303d0317800143d072080d141903810410407007402e103a180078001284d241596909124580b0850341300300414a0780c860350540004000441000140d54414800340c050f500840142c500401940e0076081c046010412082c48044203420880b001b0b603009109180c1412001c600c4003c605060004030500c1c0c040b47c1d102c070181d1203e294080c040ba801041c01400401c00340d516803c0c940542d030054007c003405405110780781039240c5480c4003900d840740040304c005203426070440010341d0542c2c0030741c001c00f178107000f0868907a000c03031000d01c00252000b100860442d95100944108030700750442c90221603074a0314103401440b005a01a0305168411380640e61001291642418004015407a5005004000c64102c0210b0b0043c0c001d028008000e00ca404d06000f143c407040003d03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 508315881 1250 508314631 508314641
    0x105010f030f03021216111f030f0e0703050705011d09012d0e010611010e0d050a1707030606080906090c27100609060207120305130b0a0305090c04 65
    0x40090022440003803000c6001414880400c503c00c1c0129030381d81406034003a05e0340b0381080c8403207807031a191401c1d1b5a080c044a4580b0040955003241c05002c031000d45900c1304003040381110701c5020507980d0619500086100e5100050001d0803404403500555603180c265030307400c0c0d10b000d41400643c0c6082400d01ca2000041d0045101c000202141081d0307081c5041131561360b0100910540e041101170910b40c102c800040e4004c00390010504000c00ba604142c3c0141070040071a02c461b82c541c0c5401072003d621600410300e00012000c51804555070609404200d030751140d1402020044403440c014444c607103405500c00c04c1254450384501c0540c0d6545d40b03c440e200d400480743c00544c0c1e0020303000d41d20585000003001c0700c0c03100c180100c3c44038245038046d81d0143c80402c8034080386104c17042400380b141c181c210409400414045c8020120141400c50440c6a0071000b50b004003809400301c1e400240c8001d8180f59800b5010810344030b41c4520303d058006014210035909140c090040b5202c105250030b041c010 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 508317131 1250 508315881 508315889
    0x20d020316020d080d140103060501080f071403070503070f08191101300f05090102090a1809060c021006140a030b13020d0b252016170f010501 63
    0x84000345040c59020f01c040010346510480c0c0480e4204a007003042005d900c41c140c584111002e030a1000d60641c60708004507201a0030141c40f42e0f008075419a02500300041d14804d8a2110400c0c440e105900d03400b00e032a052a580000350715004120002c5083e4103140c0244c1e080713404501c1100e80b014080d000030039001c16090000b51503029a038440c1142c55010b4403855002500c41c401011605508291510b140e80d440c0502000d4580c80f0003a05080c42d0b0140600781c0c00c001100700031858000e405000030150b0b8958850b6501d92040d0781c0d10602d542d100b0b0b0341314034072064004400f44680c000e2184001e4407038105041c207001c81881e190000c52032107074904402e180c00c18081c2500404900b140c8803a42c50788001002942e10400004440c00180c03940c60f03405580038400c14111100341001c3c0c250a5501d0240b205065503000413801c41d100d181e910442c001e82e20780b2803103141d8450048a41485080c0000c20f06203c0c85660502d5001401a00c044e100307038201c0003280252010010186980c609848007849 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 508318381 1250 508317131 508317157
    0xa320406050a020708030a020f25030b0408070f0b090618030f090a05030f0102031b03070804020f0102010f09120306140d2406030803040611070203100c020c0619020d0203 75
    0x200910809000304010302c000c0e21103004407480140d03140310091071944074030303000e00042e00441c040c1102002c00300004034140f08980220404c5000680341e65002425030302c000341101c038070007000ca018014542c0032107080da50000c81181441030b00e400e24002044064640035101d225110002c3c0c0410400c00e02c0030080d05c00400914500f10302441c050900d03800821070142e000b40130140001e40e943d0100407807100041040c00260b00c1346010080811511101e611401952004104001105901c5545035920640c100d03119180710382d100c80102c3c010a10504075002007440c040000007448040590303031010740c2c03050f40c0901c540c0342c50303088008411440001d45c58000396141a0f090000342440b19101a007048542d90501c18189494508150703000d5a00550ba0207800200340002e1105d02c0c0190030500400303c03d03d52074140c1c00e6011030398601010b041c1040d115540d040b40008184207001020521000a10054540301a1009158111912850300015115000c0029591400441662900d0321021 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 508319631 1250 508318381 508318387
    0x12060415050c0c010609060501020105072105190e070905070c020307030b07030213171b0f120309060d0b0406090501060c03050705070e0117010b03010510050d02040209060a32 77
    0x1140c4180901806400904491800d21211500d40024031440001b821a81b1000c1001803410001a08640c00644100208500c43d40440c1c4070540f4001134906c030b480040d0000030781f941c0d111500ba042c0543c2440b5800486c0c00c2070b0704403818081c00100354080d1140350004124648a01c40140c4016282e84070094154018240030804a0001d042c0c00380d2020b400c0c14090320b0300d602c441c0303201c2d90748120740c000024024031144140400395040100700308890000883c204001d80d010001445401c694284600c100f0103070950802412040c810340e0342d00000540444e440b0010005194003508103895407a00039480d00000240ba0b051f01d0003554100e4005480d403040e403030487e8500b1600c3c0c0d44001c0341a142c5221705d580018070201480b078618000c1110307400032803001054510203425141d64281d01c0b80f20703038107002c02c3c0300e810b513105c403c80c40c2200c1080f141100188038500c0482c01a02512221b141e003c000030440e200c005800c5408140c0c26080d244040350764007010181400d0f23044007419504403089040c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 508320881 1250 508319631 508319663
    0xc09012c010e01050c0d030e030f04060c03090909031b1502040f050f040b060f0a05070210050c1c050301090b150d050402090901110a0e0102010e070303120c0519050a05070b010311120604 82
    0x9612190704481e8000079070345412041800280d44d940140e21078cc0004900307210350000c4c13590091500b00274000c0c0786030500100d580c50301c2c020030a00851a4600580c05d4030740300e0604200c1401c0f801d80300072541410664a07641c1c0c5200c04501440030740701b61401190740d030068070700ba403400e8420140000c04c0109014100340014840c8111074102c80109002e000040200b02c0c05a681e1640740e444206043d5511580d450381c4440301420082a08c074283c0c1f014010101495905030014287d80c1036802d01c1030000b030900f00c0f0800090350007480c0c1d61000060b00d0f0005506811600030382040784103600039203c0e05050380b07035008624201c640c2050117018400d403c0c40441c01d514840c407070100e001d5030148000b0074401d0303960510700d00b00b0310154402c07400306006080d03250482d810303401140c11000e0581081814070740c9001c00e11651544060205003000b00016103c0c00c510f0189040d0b03400d894110400184a40e12440d143c00b400000e19004c503c49c0e10451801d618003c40028400d10555110301d07052028041 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 508322131 1250 508320881 508320887
    0x304030804020d06060b34080903030d0e0106030311060f060105090d1202060919020102070b03220302070e0f01061b15090303050a0605030c03060c09012c010e01050c0d 74
    0x103030040707074464441030790040452582d0168601515890b43d01d1b40e61a0542440c44860200d6940c40c401d01c284816088504100c61134020f902c0785821148040c1d441c2c1d42d840c0042e007103109012622401500c0c1041d0313049522815400003050b40d10a1b215122151174507a411a6120701c05c9800f4100755a61400145481d44100c0113031525400103048400030b02d01590700c5000030b80320000104010390051081003001034003045007404203448041c402c10100b0260300005d489000c0c90045492012000001c55542d21000100c20b080c3c44041c00c2c9502c600340300303180c020340303034003503403085101032000c017008980348051030050f96040711815120108030b2111600b15402040d420003080e51000c4c640380201c004210280a1408202d02c00d5500041501d040b0301010221042c0750403950003a8880191100a610001007990f002401801104e8a0794121001240e040386086046803032500300c10703884c10000d01860000c00701e080003600c501c143d0882e180c00445550041c544000d0301070b840000010310b0140 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 508323381 1250 508322131 508322147
    0x3c190e070c020f0a0312090e0c0901080c040e0c030405150121050106080105070e0901080c0121091a040b0a111605071e0e010e09030403020918070311190803030403 72
    0x40b01034007000b08042c04600180c81000c0c190300a03a49004d1101000d003180f60f0004903e0080c1410040186042c100a880c2c111140108080ea5041c085018081440510f6950666001b05074011590600c0d261090707030404990002d58045034284540c000054900b11709010781e9040c0c545e8469034002c0d402d2209410b030303074506400409555a543e640b10104a0640038011284112100d80350f2903c11034101083c02a443d80c144e1000c2900d030042450840660392112911081022a152648018092540a00060652003c000c00e4994991020500404007001c8980310b01c0c0a00302490142d5101d8450105680403045004040308041005246c0007180036101020b15005030100c0d1040707901c0d1441d00030b0700800d85c0b0b205195058451010041d003034210014a015080b455036680340b40c180100c031141e40c0e000302d000083c0300301c1250001072281c840c16462440e4044105088444166881c00c00303400060300c1901241c01400d4942e01c417500e422014420104848105000394a16a03c0780c5040ba01a8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 508324631 1250 508323381 508323383
    0x6040201083c060117060307260303040308060901120201210f050112110d030504181b0c03020106050f130b060415050309060615093c190e070c 63
    0x690301d0360703002062009200c0c1002d11000206a448030700b810800035180c8080e90101c020321241c15400c001454138049244012140c008409000c0d003800c2c900c800359684926480c0c503645100202c10407040c1907000d1200b074050f05058840c0000c42c3d0f00c4683c0311070031007011000a808203245459111218850a0303401140301902c0e2000209440f500101800380c54003a402000b001d01203000d404180030301004a0800030108035410f1080f11510741d00604280503910071419581d0f00c442d100d00442e10346800c80140710038480200709a10550101c003605201642c002940198644103000c83c40341404541d200d01200c2c003c0160300c40c1100742600c80c0180c0310111501b03802c28818040000c14040c0e081950070001ca1f01d40301c05d6140e1403c080c8a5142c818010711071071042e96001c0c20300c80f9404400c0105d40340c60009848484110700799900c11040840d188031348086010180d00e2612511000c1d20801480310b004440806501d841c101c1d0380c03d2200254003540301e0401161000c152900d010b0018040c3e01 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 508325881 1250 508324631 508324681
    0x7030c0b060310090c090e010e0703060e0a15020d0c14071511030709060806010804020d0f0335011e05010c110a09020a12060803040b090a18020c06090604020108 71
    0x6140f65282c0301c01501d0701c80f24101c4800d0b22801c17060104210358000c2c5080f590f110b034001c12072890510710b000d03680c20141c40044c00c43c60b51403c0d40203240c0ca06221682e1000d40281050100d039004800e10720007540855103404020340340803013042c200c510500b1200c080a9290404a0406100e07031201d2032207004040340003100550340c0e07030301082d500100405944580d11584402a00034075100d4054400e00c0c00030031290411050000b04001651405280180d468001d9050180e80c1c0c02c40c50241c406212402040f460700e00b260741d10307080407889180c1c8407000726020406402a66a40c43d0040359014150300d11401402a003001808154403d90b850343e01c890054160a04140a081c0420780145c215040602c069400051400c80940c00500300164412070450400c0040d203045103d580303a008034080e0a1403824002a07050842e51000c1d00d19000e8010b5009001094014070300d00e500950100d4080b11a60180c000010624103003c0748840c4102c3e01a102ea50480c0d40d940c400a40308502e1000c40302007 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 508327131 1250 508325881 508325893
    0x615150e061b0120091801050901060c0303020c0f010b011101050c030609060105120f04020108010602061608191503050114041208071101051611070f09050703020417012007030c0b0603 81
    0x101003940c02c0303121058010b603d02150342d02005c405100241c4010300a540115000c60300402240c0c565004103411100c441ca060782040009160890180c45000b140d11030304d20a20401e070509420640c000c91138450240ca40254040203441818281c4104a550108904060001418905101102907808881450206e1405250004503c04441c0545520650450b120b00300811560412801400b5010a0008110364580550240f050320411080c2808001054001c0ba00358914407841d50503418145809000e0703010000c4905020071114802542c0660900d0040c1b0111503118100900948c1c00c081c6007081d000001c0010748002202400140070001c1060103504800020302c05c0744d00900d15040c5c00c1c05441e6180d103004000182011a0f10404c0d0880c50041100800c48440c050494614050105081d0b43e4140103070000d010380d510210030706405c03251310101c0040650004200d062406140c80c01d044d038850031b45150380100c0070010003080b00035060720301140241c01d01d264440401411104 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 508328381 1250 508327131 508327151
    0xe06190903021011071a16030323090d0f020d0f021905030705060702012c03121608010906060c0f11100f122c0a0615150e061b01 57
    0x52903a140008003c00111000c80c4c02007600742c01d014280041040c01c20803894014103e419182e00c0c401c103c8458078162042c1403003010036010b03802c007845d2524044010421001c08c1301710540210421600c2e03441030b01131111000220781c0034100859254005038000d02041070400c2091350310314480769040e001d51052580c403040281c180803001e2110351085018603225005031500a14100024000a00790790520740e800103281e850941c0307a603107035621140c0c2e0003400c491080014250310030141540c1c10128600100580240004010300c00180180d90340c0740b450baa41d07441c54045440d079010701000200240c68100124100000070300149004030f4a5070460304c802c80000342c09561001d4008040b4444284040040d074001c07006400c5006e80740800d00420740c0c00385000c1118240321030103052a0f0b4003082411540c9000b00204258140d0000c0100551681040280c8202140740308000015040210352410307584101301202000a02500c401d0912407002444180008949c0c003410b407035942ca050800e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 508329631 1250 508328381 508328389
    0x321030c03071b080c0c011403280c0e0114041a09031006151b0b040201140c0109060501030b011d010608060303070602040e060a150c08070c05032b0e0619090302 71
    0x2c000c3c80d1040d2003680c1c0c0c0f452440310203400c0032502160581840403295482c00289050401c4961011004001d1080151111064084521901002180107281084c0341e00200c0d0840c03c00d0350314039000d0300da409000c00c52400f60240c92045025040304031100b03070bc0e0191404a444054111410b004041c1c0342c51140802c034210841d40103600000c8610f002c2403540e480c49802c4007400084080c10110310902c2442038417550210355005d04028100818840c00b440000b000000b600e207213003d00c90013802040480d00b0310304050b000c00e02040e564070003080000299203810034055620000c0e00c1076610220f0380fa0440968000200629194240c0000c010b0307100081e60724030040000d801c0504020740b0701e0500c00e0521200300c0f143e4010175070465050342c40b03c00150304100408807140e8031490807a0388030708514040d00d05441c0b80c0d10264151190641c6500e451150081c0001c01e452849055103542004440c00c40d00040b41980303058001400700305a1803050924440c68001c4003450800c6d154150340c0364046 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 508330881 1250 508329631 508329677
    0xb1b180406030b10090606030e1c0c020d05010207030801150206040f030207080f10240e1b1207020624010c05070b0a05030a06140f01050306040e010606030b0321030c0307 75
    0x985072913583da400f40810b030424425100a02124541084aa41660441d0b6500c4125100c00d140030600d071450195614400c8041a00c000e40c09804030803095840d2030114042d42244004401280000001241d01040018200c400304510703402401d0980340e41d15442442080030034141c046005410000c12800010020300301c858036800e0051103c04e440c1d0b0340710340c1200d218514080c2200300010166007045500514401990ba26103450500e64895084000d01981c0d601002c2c002e07042c01060b01d20000c1080c040c1f5500c100344580903a00c05a0b1441d4080042d02c281c4140c80326104080700606016501c41c50315a0002442a0100d070005a260548404c01ea000b0652210020300c001080090000d454041c40f4020034260440c1800351196800090820803045400e40c10040d020001035003941d030f185c0084402001202c001c10a40d030f11031800601900c107120b210703030103485200303495250320350958a0305117a0b07030702c0841003411030311501d4445106a2001d80054108001d0a80e41c0140118140d44 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 508332131 1250 508330881 508330891
    0x603010905030316021b030601170f0109060504060b040b090c1608070521210a020d06081b030304180903200601091d0616030608060f040b1b180406030b 67
    0x36114a082d14540c000f45424511142070840c8101046d0400064070005100e07410340322040220949680c2000701e140c600700d56021400295820420101e0902c41c0d10344c00705000e035000304410b02c0000c0400060106440c1c003080701a801400c0ca5001505e2203070300d00f01502609118000050390601a46c45000d01a0003000d41505e15400030714000706005141c554941c070356a207080807503080102003501d1300c181c9400110500340400c203103000202c01d4012541180c03001d07826868100b0140f0703104c0c0714a0780e490443d0051440750f2022948460340d6450000300355800c03904030900c0342c0b15648859200070003070900c00c07504600740041c0303915806420004000e0240300c0041100204200e41c5400c881c201a42c00441841a140c12101c554214490002c0362059011a548071000c5400541550440052015030700207203141c0104401d0203288503400c4091030103130307000380003440b4682c4aaa8180b4410340041e110070560b114208042030946030342110340380400900400c00518140e90b601c07069007421084407 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 508333381 1250 508332131 508332151
    0x80c01090c0311091605040905130203030d050a0c11061b0c07030311060f390406020a051e071a040b03091509010c020a060207081603020a12050711040506030109050303 74
    0xd403d540c60b04280e10b030a54003990381c100312900c0300401400074120384074902034482c0e100d03144c0c4005030340d042c0300c042e1141c81a6406822681d860107520301c0e01d0f00030700044d62003c3c241d41c10a05400302141c410100c0743d1140d40000d000d0040c80d26004515022542c09400b08561128140b0403600c0405041c40410001d50294850038a400003100c030b1541412001004a0f04020350b42c028880c603121000d014198039202c0d20090b140030a202e9109031040c44880c60090750b00600080e001c11322580c0441c824010078810400c440c0e40d40070182042c0760010200d00c00c0000343d80100340801244022182c640220000c2c2510940760589800998000f82e0088809401903407004e40e0107000200340409056201d45000e0007005040c0d42244000c0d02c0d12003540001d0300c25600030070307c0c42c1480080411100d4a0401c00a1070304810454034000c0d440c0e20704c03030400f540e103e62080300c0c082c0d1181c0034000302e03603c465016940c40404504c10013000010100584502e4040d075960302100d0000d80c00700000e501a8108903 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 508334631 1250 508333381 508333403
    0x80d1b08040e090c0d0c050d0515150a090515011803051c0e030f060c1b0a140f030c030d1802030a081309020405030c01230a030f0b0d0f080c01090c03 66
    0xf01074a00c1c0c036411800302c6024001c800f11100105116060541c00d0307613030441e50840421f0490819038680030001c0002406600c10030103024424003020100c805102c0700b503d040350b100e56645911800c5680c200c0f2980d801954450b0802c20541c811a09101c1c0c0400d408194009a5100d4844500d0081024a51074680705080590003c007908083d881c034982c1001ca004104982c40c0100460311944050140720b02c86001045a0143c144201e52114400fa00542115000d08680c01d0141c001040035103041d42e94010040e400c400d1050100c12506807200c0c00004615143c1d181403844018452929020111741d055110714006076418440c81c0c0d142400382000d1502c0783d254030080030084046900c001241c44c41080200002e481c00b243c00d28101c142400c1600340050b4070b944150700c119207158102d000c0f40001803d00381082c1c040c0c0c0001802424144100b216090714010303c51158078030350000d0403840030102c411001910501c014182c0754400c2c000400d000d0030503510480007004a40086440c45016 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 508335881 1250 508334631 508334641
    0x1c051b0411071a15030105040c0501111c200105070c0c0f0e040f110306010b030403030c08040201120f0b120307020301201c02041a0901080f01080d1b08040e 69
    0x25014281404085500e12441c10782c0c1d0b552045001d0001c5805580c00e8010303480080c105609003101e0342e540c180007500910886c80c05282c00c244014180c01100d010a0045440c4c4180040000d10715000400104400400c0086408280c54074612025102ca41c03000c400841c0104080c280a00750044804e0b80b580c40b90041c03103150a074822441070b00070a40e89001140700b003020f03207444c00b0010380003600720381030009400c0341d420000850f0490051858040c402d140001030003040d200000c52240d40265010800100ea100045503071010a86019000565003240103806040503403000c0603010314803030000f40380032156001c18001048400c660b00301c0e4201007500c00642c1003c0c014050345081211703141c1080000075018282c1400350014a50324030556405c25601d4030015412a0302401451405400e80707046012160195440041601e0005e95060302003019134050008241c11381d030040b00a03100701002610201d445040c551440c070000c0c1641d581000c0072036143e80040c0003800703494581402610f41 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 508337131 1250 508335881 508335889
    0xa030b1f081605120c01030b030102071703071404030309060503090a120207031a1314070e01030b040203010c0c121206030f0b010e01060905060901050a18080f07140604051c051b 78
    0x20310380c00b842c0544c0403000030407000c1d04003107200314848009081c000b4480d07880e0400319009004110004100b40401c4e07050b884054010344c0614454015a640c105074100182541501d03401144070060101d50012000d2080a01900c06140c1c00100041158800d02040e2542582e100000b061030000d60130000d0140284000104180d01d41c2120006805280c00c1802c04180404400f90026001c01464002420302d00028070860008100d000c4000d159561a811b004150f20000d6804074825864007900324041303030040107404401c94100c40303000201449907809840014103075650100c560398400022001441060140340d1071802030390348012640c10401000811001a0401d6045c010f000e98200311941c0d4520884000c81001c1c42c2c081d481c0e100415040d5011211800c060b8034014403800c1c00f041e03404000406000840800e0100c40b681592120440f00c41034804280d00c1d000041084103203c24104103005400018440c864021900c1032910743c4d50401d521404100401c007441e0a02c1003613454 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 508338381 1250 508337131 508337173
    0x10c02040504060b04110c1209030a06020408100e0a0c030605090307080d09030813080f0a210b0312040501050f07030e03100603050606010f0203180103021905040519050a030b1f08 79
    0x21b070902d5910b290030503400805aa031041c00724051a041000030310603000d505d0a20042d061545e00000640d281e54413420b19070b44070400802c104205601d8888040c104900028102425036004412425800d0544d103c8501422000304000b80d80d2000300035090000b010b240c000c0000380b04180c2c00040c140030a1a00600c460009450344040b030a09200c00d201180385c510441d150000c00186c119a0b803100510140c0b0700ea12000240d400c5070080c241c0100c0074450070303000422021022010364030744031004e07881010903003d10b002e85c0b8001807090140c1e4000e145804000c1103a94024201740038012040000a031a02c0b0582c1c2e16804032940b1454100308021041194541200003401e000042d003450100c0255603005048040f410f070400c4800c081400d0b4000c0d4110f5561000182e4003012000040c140a003259000340304540c000c408000c00c484007100140c50540585000508541000380307580c8841e20403a00207030402c0c1d038881196030307031421040210610100400d801000341a12103203031210011850 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 508339631 1250 508338381 508338401
    0x702090a050f0a0506030a06110c06010b0f07170702030a0c1701021224060406170901061a0f25060f050402030606012601031109010b0c1b010c02040504060b04 70
    0xa400c1000b032000da002550200c41e4003101d003050005190b035a44c000a890321480b020094281c618103050010480300e2031000300300800840e021514640d0340e0300111989489100301114800384207001403400903540160200c1c0305104200110308007040754000034209007110300c0c200d5440714516810000340140d00009118120308000860170701c0f00340c041c09400181c000b400842541c2848005500004412a440b280e560001e40394036211510b030400686403902d01140c14102d00c117202c00003803000c40140a0703072003501d078900c00b03d458482c1c804040340e203140c02002c45000f4001d010300c03031f12986280c21807564031044030100358000d007845182003010484088070030701000c0d281058204805610002030f41508032400b8a03040c0c440c558914800c0030411900c403442c00c0920805030001060000ad0140ca884849044900b5400c030f99031803a0381c00e454403400c0a51202d0b500a15040b182d030042000400a40100604003425a410b0980c001401c90f101120101c840340d660b05051040b5040a00c1954085 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 508340881 1250 508339631 508339651
    0x105100806130b031504110a120c06111e01091103010513080d0905120408070e25051c0c0206060a030b0a0905161508070c200103060f0605070209 64
    0x941001d1020a045240d01072000c020705071581c50450f10380c0c404215948014440a0b420019401c0a2601c090201501184503200300c40000002c514000001241149254030000c0b142a65107454410b42d40e40e00b012094030740500501e0000030400c1d404502031f0100c04400e90002070200aa8a000c84e0142844541103000380c2c500020000c900003043c3c0d803c60020f400240d085d803138a07040381d1040c01900c1c03240c1d40208140203202c012031884d9080005071090300d0105098076401d40e168112120a640c0c1220400315201004080d034075040301c0d6a1a0b20030110007443d25601d480ca99480d000004002c410f0001149961500460203441e03060212540040003202e841c120301386584c031550800030014181d41007055448449000304942008034004621445240a40032a43c5044091440c1c2c2220560400704014400148807140706501c10143c090340000b5140d000014842da0007d0000e0306505981403568441c2e01159211b40000e10303100409c0da6503141590b40041e881400b001c1840074180000c4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 508342131 1250 508340881 508340897
    0x150a0e0a0c0509130e0f01090b160e060d020a090e01080604050106060212070618020d0516060e091303020f1c030f020a02070e0c09130b030d1728020a08010510 70
    0x4907640d02c003048884c42244200c0440c026010303040941c284824011840c00940c40c01d1050303810400d0742c4400034805d9141948007480802900426100c0c3d605a07880c890f4480400c00c503010580c01d240d409002d5810301407600541d210b0b2103450203031040d042030b0403010241d0f00c000100401c00109005290160a01e880034003200540000108220b0151a40c000c00042d16961004a078162a040500001d6001440d01e415482203041c01034450307025224900451501d810301080c80d901410341c40305d4000010f0124030880e6101e6184503054a245030b070403002c602840c0000d44564400b00250000410244000d4028401000c2e000c0c04a8001c07007204280380d03005012410003107802250b4401103400c04054a0030566485000d410b89120301d0700c00070380c002d03040003181c50f641032140e210201000099040711428402c07040d09403002c80b614000e588202c1c0310480020119a803401c0700740380340c00081e2200380f000ca07690384009003aa08162440d4000070400070040100d4030344580c2044d910b16031400d1400c6 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 508343381 1250 508342131 508342147
    0xc0607020a051c110d09030b0112150e030903060f01050a1a0d0e1c050306040606080405120901030f02030a320f1803030723090117150a0e0a0c05 64
    0x1e00e9582c10030032485107007205401000c0f010302640151281c141d984c07040d00d500880440c0003404800c12404160303000c0400400216154920344000c82c4816048003030341080150300da01e800050f04c81d0901402942c04180441100c544040203164002d4010320780c0300580b5170509007070098000c0c407584034205c80d00640a0070b41101a404c0e0888584d503405000201d2044070b14003041d85050901c00b05c1d0b920080755000f02615075580303e006140108000c4a003400495600c5074121180700050390041d05d16000080840780c61280c0c41d004042200042c100855580b000300c445500302d800498600c9201e50b20340101e030000742e01d484540b14100400141c02da0200200180088001c00000e08842201c51011301040c03004011074107491a660740b8500700e0b07aaa14190200511505200d06803142c40c160380c090f005503c1810350280c0703d5107503043e951005d1660703221070003511104020b81810030307007650880c0c0c54100f0340b20012804081c1420b5507201186007840100c10084815071340c00b04003009010b020141d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 508344631 1250 508343381 508343383
    0xe0c1008040206090a05030a0f1101030b1309061d03040518041a090a020409060c081b3103030c03110721050f1605030f010606090608090703020a030303020c0607020a05 74
    0x290070075010764005480d0303207800010451220301c60304100d91501c2404c01300c60802031402c0b043c40e4500e2080b6110208520004c0054003940d844040d0b9035031001d45015000a5140145c0c0a500c6850082c0d102003080c2c0c00c40480007440807000c00c4643c04030381001506000f1800c0c41450803801c102807070b00703c00091820741c0f151001000b846440000749003031840810014001048025440781e0010020884001d29141c807000402000c2c0540c000701d5113400000f8820104641310304803600d10100414681028040c00c5001c800c00b4a44609070a03a29090312412005d4404925015611a4403031007161170341801c2c05002090b00402c0c546480d40000f20030300c2034040280c2c0140381003070750b41c050300d85c809c05030f1034400d040844485004110f4403511401c094141540c2810500703c64040d0f042c0c4864103198030a25090394a240603150104890041c104103480c46245907561000b1804203035181540c8039400a22500130300d60003900002e402140d0800d000c0014400b60790070a0f4540020301c1c0d50580b5966803 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 508345881 1250 508344631 508344647
    0x7140a031b06020705010c0c02031e0615010908032d0906091c050f160506070812060d06150e090c090606090103090204061d180307060c0e03060403030e0c10 69
    0x400141c5940469090400140ea01903440302035100c00240440034000c0360040250304409403d030b1292103841030b01c0001342c0444a50001d00043c1002510040d61109810404030100d8003500341007040e40100061106028009003500002054034240c5216402020840805005000181c40f07002001020744507078403082141c44214068481a00b4078003551801c0100c0308100300c003c4d1603400303040400703424100040350521001c0c40401d095915183c0701e1050080c1b5004480006040070403c00007603d8203004403090311750003a80203060525101d02a0b990f50143c400540d10001007080809042c8040110300ca4088c0d0710058550090500721490f0001505562028003d14002c1200083d08903259100390018010b0715000743c01803081c540d49140d2180c03026420070f8842c2d502a200300219915800c0f0844440c0c580790043c0065061005686508000b440c1c845802e030103006c220464060039031014031059115078000d46000824580750b41d00e10b42000d00441c5464801c0761006040c1740015002144 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 508347131 1250 508345881 508345907
    0x60a020a030c0816060f050109090804050f0a1e0807060e100807140a020307020f0a030506160302040323010606050307050f031e160f0216030602130905090307140a03 73
    0x201a0700b901880c01c000049102d0342d62110318402c5040382c0c40003400800e402014041d0428041006542c1e6103000103001c50f400040018089942000104500c1c501103009840c0c0f200024071079240240c2d83d076417040c440598011704511207060304004101c185000d0128100078221420082c600d20000c5000940c0e0f00b03d4070200e0418001c01390301180302c00303114108107120715070150a030b5503403240d16a40181d50f94003c458102d12484000905284a00b031603044182226800310041c08580c4402400d184140e0402c00f0b400101a0300b8800000454072050780a1804050810b151951025203030019007074a94541103282401010828042c549034003008841812145400e8070b81c494548240d8a0503000b91080000a864014001c0c803840440c9402400f1045e1070700c1d250f811600e0110441270343c8405045d2103942c07105104031410400308419400070081c03e54042010f00078603072a82c9032880bc458059030184003562000c81c60340100401342a200c03d40c20241c6000f480e9100003960300404a080a00c1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 508348381 1250 508347131 508347137
    0x304030f09031e0501110712140c01020301030b04031206080d052508130e010f090c021e1e0c060301061808030d0209130c0e041a131a060a020a03 64
    0x424504010300c26107000015541c85989002c42143e80f403103046040401007410344481d440c3c800d0001115850b0303002c0f508180d81c03252801150a54091003a280781030820760780302d00d07190708201c1c08500060a2000314041d511440300701c070280c00c0a041c020805d038081c9070744e4038516141880600c0015400240700b403010441c3d1905603540e03425219403c881d1104107140021052210724250200318400000c1c0c0f080b00318402d0301c041c44a5642108103a0700c0000c1c8202007850194040920608000e40c00aa910809600407a00e002c1208031001040ca80184140704240c0c0003888554100c011004403013a100350000001d0200a4000380041d00911041c4502424042c48171646e03600000601c4488004000d5403040d203407510508200640a0751040108510800c4540034450f10082c952161802c509015503420003921882814040200494035061040051164680205548228422040401044002c209201941d00301503903001800c80640c0300c0c400c1484502c924950009001d00f09a17003600d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 508349631 1250 508348381 508348397
    0x61509060a0e0709091416140405090406020c19140f1902030a0c091b08040b1b04090f09060b01030e06160509060d0b0108061c0219051009091a06030403 67
    0x81c07055440d441c640e484881d4a03800c11b501254008801020a8420100509400d06d8542100d40440750205102c0c10300359494000c0c0410b00c810309281101d84c0e405440b6190041c50031407070342c2501d8540400f645d8441002028440e6200030010b0310f42d1450240c07140f600003402c0c540480c00002c2c2d100e005010030803042c0f0414455440541d0303800c0080480a90300400320300803807030315001c0d914007070f00210207a002c01039136078407041003100e03c151962441150450541035803500c60205403141e2415100144104280500c00071455900e548101c01c10880b000b000000c450700940f07840c105907071000c0303a00c0381418540307089032400030700c0490059400101b8501c0c1a043e0907140c082601c0900030000e2040e0071403408074024a0300340d402d9110004090003608d0300240340e034071042008501c03c8588a0400f0344d5031003080840050400188404141c5d44078000e040f005610b98001c50030691000b0100c01c00140e80d4182004607001e240f28203801d910182c444182c0c40c0440d000070800c0da1101801c020200403041c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 508350881 1250 508349631 508349641
    0x10080c040918060c0801060806010f0806011101091e020a0807030302030a0521040804051305070906110a0203010906050105090c040b091c1b090c0504050a050f0a090e061509060a0e 79
    0x102c070340c030380b03182d50b009000b0410014003040007000c1680034000c8038003043d201004541550b00440b000c542c0940d559442d05810356903000115640390020202e14865034850310440300050028501c84050321492000b00c0341600b00e80104804e56040c0e40c0042030642201d60300740082980801121001445801c02da541c13020081400e8003040c17030001010304408451020302041000800090080f1801103a00c0c0d0310035403182c4036a80845030152020408104551000c200d11405080728100b404008000d651901c03900381c0200f82910342012049400607603070001400f07585025a82c080d0031170349001500d8207041c01d140b00211103206450107684034a40a25091140f032032440c400c0e503d240c1d803121000048a5400350915640e0107607001e0380c4c601c00c1c241003421554601c0b51050754201c0e4401062000e0b07642c03a100c00e2000d90380502e014070760014100080440c0005a42c010074186000002c02000c452501000003117001140101d064402c0400c1e009001e05a900e55001c00c0907203445400350240368a1f4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 508352131 1250 508350881 508350911
    0x11805090105091f090b090c0c0d0806010302130806100e070c1e020414161b020603091203070507030311030112021201020c1b0f0904021012110c0c10080c0409 70
    0xc18040c0c26041103100041017804180d00803030080541030b07480d0704868071815940382c4180180d10601003542c1c8000f000c107428a1283c800d80b5000032041c100103140245082c0d03110b1519215030480c8540d94030880c10711103420010b458110081c0340c2c00202c0e000c107081c04800107081028003400500342101c03520004031604d1880000d401c0490b0300400030851103019003000c003d4480111480c4c2210411031084c02c80c0c640c000c9500c1c401c2e021000100e0002c205244e0b003002443c0e000541010558071038402c113800403c0b070020080d4000c0b54161180d98075152586401030644040034104c5110080510041007285026410140c4895040b10560040100f07164903034028094980071180c0f5108804002e904c4401c1d40111510803102500d180359460060001d00c0714410301501e009400c4081f60bc0d040012a204854802c00d440e43c180020070341e942e0000481800ba00f000d8003c90294004000450851405010400c16074000341005003007482c0145980f40d06000364891141002d440e0300e982c513490704c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 508353381 1250 508352131 508352161
    0x308011415030108100b060f0708070c030f0c08120405010801060c051005130b0c031b0c0a080f03010905061207050607030302040f0b0301080d1e030c1e020c01180509010509 76
    0x5541d801c566120341c3d4036103d5543c2e6054001107895490b150009441140c00c120302101e02c0d013403000000c28905005a540e10030035034410202921044120400840080c240c4141c5520480c0182200c4640c1401d048a4034102000f03001c0c071650301c0c4c400300020004d60360480409411146241007000c074807540c60406c1402c04401456098a4902d414100045c041c180281414881c2c00781c4d05600c0c6543e0303481e07084030036032009a035071000313004072400301c0c0615030081d80c020034032203045009481e00040943ea03900d9881d0008a800329113185c021006124683c070900c101c1c0d80c070030411074809030f84000b1151419150704203405001e004500002e0000305040c000e40480300100f80c50581d9181190340c0c0d0701c100605800a00a2030304c1c6000b2a00d11403800380c41103d00300107035100c201d05200f03420f1341c00c60700b50005c140c40b4112209100a0398100401108009841140c44980d9009841008001c1000501148640f0a01c5a035580349130410b005c1a2038068402c1c6c10740303801ba580076040b500c4220300b24100075 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 508354631 1250 508353381 508353409
    0x5030613060803040f0501170606130f0b070b220212070e0108011406180a0c030e0a050a030e010c050a150b060d091b050d0308331c03080114 62
    0x1500308100000c9030b040c0000204111070328622a280010b0300c500045800c1d0482c1d08200d00e100901c203000c900945007481c01402c4070449031081e003003619510341000c0480d107403a41c8083c141100108481007800304641041e0340c0803051400349400300d200280d940348609003d01002e80100c8071a1316011f8401030812482c4094810704001301900e40c0c0d1511403c3c0030b01604098107500e4009440407902a04190f40c2402c0d141100080700e02c2d1590302d620042000b814504002c00070192114004654071405005103a4940d006102070811a01c450901a00c2d4070603649803641003000501e035180100780003181c500d0040703901c0720840040c521102c03840b001409480d03402d203521103c001030240d44c5841560001e0561441280300521040e500454000139032098803d06800051b0030810f0ba000911039404d4680c01545990321062000e1211840807210b80c1c2180c00d01e260117000c9540000d00e151044059000d0302d00807a20302601400795030300030207000040c0300c3d60f00c1c004425151030445554116500f0044 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 508355881 1250 508354631 508354669
    0x539030d080c0c0a080c0f03030112030507020103020909070c0b0f010506161109012705040309060828090204050112030f0c03020f03030f01050f0d0b0c1e040801020702181303050306 80
    0x800300909041700d56500c50380b22440e03984504042601c9030100841680c3c107d6205401c2e600183d2180d0f00c0584942d4011a812810140d081100710010b0f9030702082140101070340e0380d030122900d40038030341282014400b0b4003022203151300300c004001030b0341d800c0110b2380d00300c060104007480c1c58101d01d00720401c419260300503503105641c8400454400c004515614581c62802030103141c1014a00c40d4a007101d2051f0760142c00501c2441081c08468002e40c102608200c0d04280000800300c0b1100c19400301c1c205588403a0070f00d85907005801035103002e020301800f4110001e8000c0c10014903070b4015200d40601d42a88060101404ca04018540240a8a080d14101c501542da891402c5900c101a0500034010a0700c594040400c203a07090030403140c2c068046a22141c040003640f0358032a210504e030806c60401a40420160400e5040400a000703440140204000541c85000e02d10400502e45031408074031010081c003004010100045000406070301d030701400e110780da0352582c2001c10200c1c1c6149a800c005 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 508357131 1250 508355881 508355893
    0xe031e030d1d0607030e07030f03110706030c0f17152101052401020d050d060f17010c05030f0f06010c0b1f06110304050609010c0539030d080c0c 64
    0x82240ba0342100200b0400c00400e494041d5079500e019011910140001e504a610420061001548140b407202d5002d0103410004190001e001ca8a40703400c10b11340040c00065254518440d0b85504000b2505040c1103a0404610a282140302d5404480004005c81130309481c0080780b070440e03158103a44074811200800054030400080c03a40034040c00e410b946110490009044e0300b8911920902c802e55650b40507030242008000c118001c86a54203c4960362a460f9074841d0001092000b0500003c001d20001d203080c2990401109800e007160305c08000401849410020071140e4130045041c0c80d0310640102941060b9110140120381c00c80101c1ca00504401d11181845090f00407640a0b40030b80d0007250040000d542c950b00100c5162000407841400d95005010504c440c2c601000a04240201894504070601d459200e0b2450040003d50040c801c205411852008025603c0d40c0300c941601410440420780e0503801196445d0283c3d4010380c1002401004036001d110034108583e0315000c0c032012100c07 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 508358381 1250 508357131 508357151
    0x27241b02041104030609050705040c0507020f041e050901050903040308120c0403020901030b0a0e0319030908071a0907090b0a0306051816210201080c070c0b0423010e031e030d 77
    0x8000e11b80c01009403aa4842c101d00001e1924050148584c20755451307035207909280aa60034451840d581c070b014140d00070f49a40c5014a064202d55500745116180321002c10981088504c150071150081c0454490f038200f000300b4004500401d048031010300721481c900e6190380e10041d00f400c517030107181c0001358420020b500000c1446050904540610402c4408200c5502da000c1035681c1c1c0d00c11503c3d50140250041034402403580603900048400d8051920546821060b541c0c00d140070381c411600813071518100301480000130f030410050015000c00d441c100820138a10000030304018181c84010241900c0b02c2c0041c115240d48401004040d00d084119403160354452071141044441e8042d0f03000c045140c019001a200c51002801b43c1d030f070740685070300d9015110003844080300c1d0301c40c0405030780300854404e0006541d103400008000900c1c032007904a01c00741e041e02c46c40c50640ca9840c516810442c0407900c0203541c0da40403c40c0c2e00c5102c07100d10010009100088800d04500900c1c100310401d074070b4010204 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 508359631 1250 508358381 508358393
    0x60c05010f0609140f01050f0f03120d020403051905101a0a08010c1409060403062a0207050901171c0909050c04032d030f27241b0204110403 62
    0x111003000d10304d9448541d21005940ca041d036092103003603070080c4e8070b06620700c5604152840d60b107d080040e0645041c0d9404180c148207990043c00080d80145d03002408000303005041c00180c47c08a0b680031000c14250340354640541c1c54940101e0034421581e2480041d0300084203046c004611640034046902c99660303810400d0080075440425404507044d40da1f8500c40101d07003000c490a9800007072581d414076040d81c0381d8000500c00b1602083c50311580ca00c00008450102a60301105ca005600034400c50f8148401d02c145040184d02400c403103869190010f10b8000040b44558000c3e401c4044205002103c0c2070440c0d100145034051402c052800040c00945c65442c2c0040c0156806445a0b0b014003810584000a4840f002d1039800e40302d504041c3d0200192140744002c60320341003807030302d01c1e01000c0c4610151204000f4140c840550441503400b0403058240f03032403202144640402c0640d010b0441c40b07010b050307065940511854120754402007405c540d2180c4c0110380991a500382d00d5103851300c0f45494 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 508360881 1250 508359631 508359641
    0xd061203030501180c170606040b030103081e0f1b0712050f0601050d080706020a14030c0d0f0501081504060f0203090703050f011a011209050f0d0e090402060301060c05010f0609 78
    0x80400703030b03544c00701560004046004441440216550300c0c59145400403e108410030082d19030b542c0100100000a40302c0c401c08050b5010314001c1c0d1074203a480304d0b402c0041c1e86154a280c0026044a0300b071182168400700c0c0f9003560310350f180000c005c0c83c0e11100b0b20080d03403c0002c50f03000f003000608503c900308184200024140c880b212004100e60a80c0d8807001044040008090010704507074003041501d00140d480d8001d00510211402c1210325031040060014240d0412074000080803070100d0160b864200500850700c06204080e000c1102d54106040f80c0d03252500c1604030401c080031040030400b041034079840f0f0281469586000c540786d0410b0791403a0b44407080703803005490600c0f0b4800f081100c1c010601c201c258186682e100903603c40021340054a01400c03118108481666481d2110042101440301e0404001c0d40005046001008100580020748043c6083d0043c11f00c0e40c100401a196481164152078481c140b0b035000380f519240c21800752985550700291141070900c0010305101c95002 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 508362131 1250 508360881 508360889
    0x30618090c031533100507050c0d02060a0507111e010f0206010f090b011b0b01050118030b010306020f071403041a0901140a2f0c120604020103020d061203030501 71
    0x1510022401d10b110325400d1030044d2000c40b4000d0000944218011040c2880d48034000600000c0300494a2900000d10b4249040c22000c003203207001420004215052040d0740c0c0300c01d0200e1381c5500012803034000c150345001d82c201c0c040500c4800100d000600c5180b40501940c500004d010303428203102c2c900134100174200c1421190100740b2880c54418203074008580541600c02c4045d0048038a031600000360040d02d015084c0380d051001c1010700e0070303000021802c04a080f6000758070007103c80d49404001040911414601050704240b4074050000a1220108504490f04600c0258541106607000b81d6248181d000007048081000302c8030b02400c0c0c010010380111003080d8603032a0007030008030b1000200c1c070a1401c80d0f800103400389580c3c440055441d014046103c071500c8d1030310300303220520701c88280c680a41c0206480040e000100411200082040c1e90091500b40c40682c04030071000603581ea102000703800281815004103034014040c4260b0b02040091800744182c070200d841078107000d40104400e002e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 508363381 1250 508362131 508362133
    0x120f1615050601020307110f0607023001020c06160905180402040b0103140f0c0f040b22120f0f0b0a0b01020f0d0203070b040809190f0501020c0a0506030618090c03 72
    0x10b6119030002c02a58840740c0c02c00c2540000140841c104031181110400c90340c0e000005000650268484601d54840c0a2800303180c121000c1030546024000c2e9100c41c0160a56801003083c205032040100380107406c2030320402c084240300c1d903001d030654499056400070350300085c1c850030031202c103103d41421500076402030b1004c2210210400c0111309481507800101d01403295000031a0a441c10000c079a41d0040c0f0541e85241001c140050301421035006034051050220082900e8407000b112610311640001c042c030010050324908039141e00b01c0040041c1c090440c01840358004180803881c42c411000035403155500102e4544042c0d2100100f250140ca540141b00300002da01c1d00d804001405441e00300160011424810241d503800050240103000b2140050b00b4040c11015888804100006070400e0211480107400e0100c41ea001c00c0e9198001070440d44040ca5072041c980743c0c45807000a84406444044c0d40b0345d81da0000c200c190303241041c6038010512000800580c242e000c40c07901d0040c2e500310 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 508364631 1250 508363381 508363391
    0x130305150f010e010f050d060f062903070e060a0e180109050f070503190902042c01020a08010b09190303030f151a2508180102060405120f1615 63
    0x454003000100034000d00c0b2507417179540b0040c020381c1392410000100c14070514000ca400c181d04d0702ca50381515200c1c0d0000341c201c00c2600e4510b000000c220307030080c0d10541100403e800d600d4480c0c80100540500070b2514083d003c0000c9000b075040c4200300908160b8070140120164180f000c040c031006480911400d00f04525103400306a4040711140d80e140240c1d4035a032010700b507031503000d4601c800000d103040c401045681d50502c0f0f401a215401003c44aa0307801094154440000894100402d049130701410795034810403041089541045525065880f94624035803602030407808104001b01741c13450000c3c1804040400810076030305400c2810040c298540c2030082d000c0340d0929401e844c03124016615001001d010140034040940e01500304002ca510214500c0345640c000030640562010007601c0d00040005e040c1350381c050706018113400000c288010801480d0580354141c440c12241002c002c8003000181d03d841c203400790f4054855151641c00d40024410640c039255201a01038041005c0075411303c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 508365881 1250 508364631 508364639
    0x120c080102033301090303030c120603080301060201140708070c02040f1d16031502030406020712020a050601050d050316140f34090506030120090405100b0f130305150f01 75
    0x1141d0000c101441a107818117114211b56051307002c0c065001c1590b0410103004141c061042c80740c061080118000d00c1034651380d50401500900792562040d458403200688001c0c0040d01d5400f201241c1e00c0b0b103091034803041155044c4000740140c034414110180b03c9040148403c400301000328240a0a40e4460072030300701020403000e001d1800c0561001800c0c1c66540c401304a40c0e0ac1d147e800031903000303220780001458041659502c10310700072402c40c4200140e1140748120100b200030091640907160803985000000320030750383c01d69684111020f00c54141c41c0343c052942041111903000d809041c1e41402d50344014824400550346800c080050703680c40c400c040440821603050b0b40607400e4051860500c0008904001040b00601405403071036405650305d06401800340e16080c2c0c0100b403000200e582560300c550000070007095a030301500ba16480c2d0700c0114200111401d0504070f645000c415800b90f505c80f00d40d0200040100c0d0700750701c064000c3c0590f04420340103610260085104545852680045980b1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 508367131 1250 508365881 508365961
    0x15160302010906061412011e150305120a030e01020301050a0302061803061303031a061912110304050105100b0912070b030c0c120405060a0503061c0c090f0e0304120c08010203 77
    0xa00d0164000e080c09610f920010000f081d08020400b03400d0003a030b40613050f4ae95442070710f042c2a5088070b200c039800200b1688c080507858080c7d03c4074814204000d40c01c44d410900040c0c40300e00b4500c4001c3c40b07280000303134039130808003d054120720b2110001c041d2802841d2460400b03980344c2000b0310480019160020390380ca5002840128004541c01070041400d0102c80d11000310050003610400b000d20030006030316052100c090041d46640e0352503998140c0c032810149070071400d40310f003d010714400c2c21400b0400e11a405021050b1414070358200e500404200100d030009040080310b80149501510000070000003120840c01043c624424908881000d51203407400c10541c013580c01040c0d072101003008502200ea10031030185400c503000400301c415010507202c10070307074a017409001115202c1c42400200003400c0144110101058561020f1000c110a03000780da441c2c0c82140180ca00d058982d0031842c0034403413070354001c10250005500840d40c85c100059000588075040284000c0c04401130b82c00862280 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 508368381 1250 508367131 508367141
    0x2e0f030b04090512130801060603091505070f0e1201021206092815090906151a03041b03050d050304120906170a0e030a0903111516030201090606141201 67
    0x2801401921012400c0c0c981c40c8215440780300c140e401012041d10106d203812080c89200020110b54400080700011480c0070aa82ea803104030040b030441c54441001f0203d40c0000410700303580080d2030044034084a440005201107400801004103610100d44601104075001a4501900c01220740c071a9a6075030181c06400c100446264628011450383c60b035806620540112110304090302100d03820f5074440c115030303044501a41d070640c0e200d82c0ba0740001136144580b45034040641000011300e03c0d954603481e10031036244000b50009003000307100c5810301001e503003a041030b002440e4420241d50500c103002070010403075001940c041c0ea68068503800c104240f0b00900104041f90442d8480042102c20720340400481c81c4020700c0c0701c8400e80c481d56084490f020520048c0049021b039120100228190708200070307890014104507008013403400c1d090743e12a004a06a0741c04140a0805610f0700c04e00380303002c901500d801c0000900550034200085400b075000132208000710f1040e9a0810080e4904282030b0a0303070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 508369631 1250 508368381 508368383
    0x40819020a0b09010c061503021c0c060503090304052701030c030605090604320304060908070b0301300c03110102010b0103090308160e031c020f030405030c2e0f030b0409 75
    0x70301750249500c00034101d5007280f804c5c41d000510580410380d480d008107041c0c41c90580c5035580031031551070b07440400030301d0a40e0340043c0541e403400034114030307001c4007042d90b074407031b40c011030744504d8411140c0300580050180d610b9000400c03400702c14440d41d603460090710305d1016001c12500b07981050300113240b80300001361561040b508544442d2b600e9205085500b004000c034401010005c00e211a0552122010002000101190703034404c0380140c544007400313090820a80009095100c100010880904508000130681d001403014038141d40c2c240340c01c030315070117078028000300b00a00c0c0040000502078820044004050203030000d001c1c0c845418011400c685100340d0040200b120304010403106e4001903226a024041350420312140400c14000038545850140304120352040c8410000810360f05202e007011140d602e400460801c3d05120009031100000d0758034074050465a455003a00745114540c005405c0c3d501c150b200d240186131403006017544c280031844000b00b07040070400000c50403d48103801240b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 508370881 1250 508369631 508369637
    0x90613060f061808010e1509010f06140f010306030b0a050702030d1503120f0c11041d03190807020706140d0e060f0c0705060406200c011a0604060807030b0402040819020a0b0901 78
    0x658080210344807407c4060710030700482d0368540a28080c41c095120b90780290560005550000d00c0540810100c1c84810204a0425040180400000700c0074146a0740000d00d2480c0402d85964060080b46103002d0803801150039400c041d107009402130341e441d68009890107910f200c0e0180681120540b0700b0301013000c22800250580340d0301303404181c03200b205107107002c0000c10215040406c00380b000f041004018a49095420000d0960305005241038070a00040c41030600405520304008041d40707c00d0720303201d158144040d403a18042e1101d1041c04030f5001105e620700070841c2c40c9243c04103581d140011618041d0204505022540703100302e17003041e505115800320003081e0607507596031040c0c0a0045841b100c840d60049401d01107854040d1006094868080343c000603900c09243c02069400c02c01c4e2010074029030080209100b450303030000c0b04940c00700040c01c02141603101000480d00a104941c80950140181d03d5114016503085481c03003841402210b840e0482e5807100d9149641d44501c200880c08 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 508372131 1250 508370881 508370893
    0x8300f060d0201030929010509010503070e07030507090e0c07030906030b0d02121e03070b0609190911030709020d1a0a060f0311030c0702040c0c02090613060f061808010e 75
    0x198401c0d040f44803100e1145041d00401403c04250f4110703c0071030003c1c06c003100064001840340d400d19050090051600b00c1c010115a464011002520007001e000d1030101500d9200258032203002e0346d1f545c8020010541d421045e4a07040003019281d0300320b91802c50010b0b50510300010742c4e0744240107000c400100107100c1104850765900700a030f0381e40c0400c01c0042034014282d0013407800c1c40c03249030f00e040c0e10194400b4551b5100507280103459290300800940c403d103030240c184200b24117080010741030030b0f0003400c00081d40882c6040189100340c041c82801d0381407080710343c00b08012802c0d0f00600368101890000b480a040c412113131014031041000c20039080480d4030307000c009207407148109048120582c00c000500c280e50300c01c40304041c0d2084440388841400051082c00310b051500c80d000f0f08954030f280102a03c00e0640c00600c9400d0007500b11031155040345045d50310350329540d105400811000741244011555090060883c1280d034010101c51036100381e00290904060081141007004d86000d410 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 508373381 1250 508372131 508372133
    0x1206011701090c141810020a0f080928090c0804170f0c0304120201171b0c0c0612100806011a130b070501090b18030d02030408300f060d 60
    0x2c000d201001140b400c0004c114644000e2506007001803d070000710b103188000d0740d4a02d0f002e00c950304124840050442d031004188001041d00c80d520040283d0b800810340382d5a030400390010382d588602003001c4500030000c111216001e0302c1d1250101c2110100c9005020300d603d03000c0300340d42007601290050109070342007241007a100711040042444460b41380003103090205010089245801c1500080c122040c40c000c1401590f810032100c196129940d108071440e860301c40e10b074011801c054a0f11034070a8030b020504500348042030101c0f8504401c068200c640f1034010814251040d031b8207030790159200140e0340c1d0100b01c0c0b410100c3c9050680b01c04031900e00f5422116030840c00e03903920103844041030540a11000c29554a0174004001c2503029500100f1204298103104002c07860103000ca0000401c03d80c80c4a08010f40070083c0c441184071034800603140d42e240d0900030320502c076841058403140ca045412091303540c00d8107001c01c52a00c200d0a909240c1d50303146a5030300102002c1d908107500044154982c4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 508374631 1250 508373381 508373399
    0x1060e010c020f0109120609150c1709030409021204060609020f071103070302040e06160302180f061b03030403020606030c01090513111317030301050612150607081206011701 77
    0x2040340d00189041035403c0c0d0750320006c14100b107807038000725005901d50307800505124202a041c10311a84c0f20074204901c02d281d500107030409928a1000080081850005881c42428800d40d4001d10b01c0c2d903000d660fa42070061140104030f41c100c908441d414640f10002c501070007d4400c0d00e0820030244004d6240400e1a229401000854000d4036414811000c000c0010b072983d0061102001140300100308900b01484607202c0b42000355100d00816205211160020700b0110f54100141c20603100b040040d0b0400c404507265102c2c803031300c0b01c03440004c0b64107414041100000440c8aa4000e9081d0745203a2650406c260301c0301c02e405801d900013001901d050140d4500081146512041554001442d00383c0e0502800c00c2c1c1c00a01c0081c461010621007008188402080500d406a041018503d1907040000081071405440100d03c1c070030f00d072803002492031140c8000c00b07603030a0b000a0015480c2c501c1460040ca16610071615040c41168850104080394083d0f10348506050417503246026685c00c01d40c200c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 508375881 1250 508374631 508374649
    0xc0207092705070302030d120b01140418020706060e01030215040833010602010e0c010c050601091805030301032018041e020a0810061a070f020103062c01060e010c02 73
    0x50b1081c0c016041c0010050391b003082120030000d2131341c603140680ea5203900c8450441d0303d1445914140581110300e0000000884200c5099450080e030a18885483c91030b403000a0080000062115103007500214245011031701c0c09040364030858a16031144603014a104460082e0f102e03111050f03110020300301d68011010803800b020042240419502501c841000502a200b030f0b001d040907035956017200380d49450034010a0031600d0b081c28903141c502001e03580c007940c4890500c41d6144659550020b00340d449401c410407100780c0e802c030081340e40300d586030b040583e0044c0c002981000316000ca40303035108060903c1c00361141001c600950b5140645e5480c0ca44040d03005804d00f034444502d807400c0840300142e4442c4407003809000c194005044000070300400104480c1c0da504602c0c8041103151401442e003042d141103c5000b5400102c40c000204039100580c05045a508043ca0100321405120305070310804411003035142d20090249600c0e660b4150030350700c0b801050542030000d01064280170140c1400468 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 508377131 1250 508375881 508375883
    0x1103040909060f1a03011b08040b0403020f0303010e0709090b03030d1e020d0609150807120819030504030212090a030807110a080a061a010c0f05011e0c02070927 71
    0x86142503801880d00c045422062014224141328144020182002d12400c030340c00c03800d112028180681404064244080100000d150800740c00008040610920602c0d00c00c820350f03400c0360380781d50f114504400d94010456002000400e110f03000a11a00c01e40150313001c5023405409145820047c0c810305014014000703885580441000c10050482e109100030700d2450170a07800052482d0422504100780e6031941000035030303000c10400038460200d020038841c0445421000450564509242407800c60160f0383c085400c1048200c00030300500d4060700510711580c4030747c3c243c030309104a000301170b4101c2c0a05200709810202010080c4005445180109000e50103011039540ca5503500d0001818080990007000090f000301d0640410812a03024141e20000070304140d4203000c9803000000c1c10f60400034009070058118030301d10014004298041c030500b00103450b0001782c0300c010b1444400580031048540005201c0c00f140028203003014407175226a03c9100300f20422005c4541c040c407013a4415900 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 508378381 1250 508377131 508377143
    0x4030f150902030316150218090a09050105040309060e030105010612021c050c040e0112030f030b04023a02030c0f07051213030c120f060e0a050a0f11011103040909 72
    0x21400c4050390f420000380501c5040780022130036a050780e140400400300502c100011690050160000720007900058505404003545c40030740c5a500d050314000500301204003e0309079484c19080c0828150300c00b00360015a0400d0300d82403040a0b121051500b00ca400344110030015008442041c40118581c00030311035401041c2800c1c4440078650700302c0f800c41c1c1c030903075a8a0159000013001c001402c05062a40d0041110340c030340e0001c1480d2a10701038154075050f00f105d000c15655038024000703a6507541c141e450b034030300c46c02c0304022100802e840400d0140b0002e01c508064101003012034801e90a0307008807413150303030100c0d00c1030f007428107401c41111180c101c50340807101070140140c0d1402c0007082d1f101510b01d210807149080102451418110040929504520756452520912401045910302d000b00e149502240000b09400c8802c0d2a605181d0b0411009040d4000c00720b84100f801400e050580a050081d410081000c00840041d1a41d03000380680c68629002800100000700d076a52140d04910b00544e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 508379631 1250 508378381 508378391
    0x90302041104051e0a0503030c060606091f030608010b041512170c01060614090f0910080f0c09011d010e0a020f0307180905010b1206030709020c031e04030f15 70
    0xc000900304044560440e84d0140820410542d1843c12100c1c404c000c050075406145014104000c01e5114003005024070b028940002e1051461340f03481c03001e03200508101580b02c5014a00600040180032984140031f440d6003821079100480c601840395601124581401c2d0490300c0c41c04803041c00499601e142030f035585201c070324121648204903000704a0581c6080000551a09050002e004510700340b13803202c80442e0602c60700107c0e0300c440183e8190804225039201865a40702c6100300520a6a00054610700480d854000091000685035410721011140c2e82480c1e03885401c0a0846001255004490102d150040140c49109088141c1003240030b28094602030080220100540c026511b400001d5044040510f124880301492405404214170511807949041402c1889000300603101d07806402c03044c040b502c07540d4200092002029000015502da502e801c07100c544075008811b02c440a41a00c602442820405c0302c22101920384c40302c25210b12051903181e02d41c2c103441819018160540c0c0d4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 508380881 1250 508379631 508379639
    0x5072a02130507090f080601182f1e13030f0302070e01060c020915060405010e0402040f03060603021905060f03040201020f06040b090106050d020a09020c0a1403090901080a03090302041104 83
    0x81c05440d100e8445138440150040c5411203120404c0c050391300284081e0003110050054001c01c59054008000d01000400d80c3e0100f480300804003051094038007560000c0d000a4035120b0034000103044414040380366004a41c071300c0000100103101c0c100c0c849941e00c490300418130011f248a41d4025000e0702a10444440c039445500142c20080203030080301c0030802c1c00c40282c0451400b044055441061030304108a50030408000c00e02a020394003c49040c41090021154692682c1c0c1c15a001001c001f620000c540e9624105000140102c2c0001d80c01072441005e604501011501502c04440d80a13000b5468000416506d031001d40005d0700480c11030007003809130341074000304000f4540164040d424011180c10880406421241a41d210600614034510a000583d0311102400200d0f0a05030025a407051207440c160300707001781400c00a1580f4100b91a21240c0c241c0000a0420b00c503045d07841e00102c0e621480025503030f0808620040000d29014418401070900b50090610081c010f07620900b4144c136 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 508382131 1250 508380881 508380919
    0x90b0a06051e0403111f080402060a0234120b280504060c0e03010b010e240f0a120513060f060b071a0606031306151502030c0105072a02 60
    0x9a402600c91843d00c1010303141c585001b0001d410040c0701c078100c0e4046841d0100015018050003800030380b00302c4000c1203520b03055000b40007812242c101d498000d400c26000c1820811640c1544900c8240c50742a00c401054007003100c0000140c01d508068008042e984080301e0b00401d50b00d8108844d21285031000102004817035001ea240640d100b0718002c2101c10f117948004000400c03141660344030381c1c141400d10103d40d801c4070480304d07880f9042c1c44044601c02000b102c940768400d176901841b001000058800064501c80b800341c806820b850350750b02d8a4100d004515425a0001e070f40b541302c3c1030300290441000440039400204403042040000c03840710b5988040800175005181c064891610042041c40035044001109138007003400c982403411030500101c10010300202050003080d00b0741d18402c0070440d40361032004100402e4101000d003003440481100070b45135080303800114015030801d80480d020030b0040c40c02e441c0c814031110710410f83d5100c904003082e8a03548010300380d8006041a0610f249841 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 508383381 1250 508382131 508382137
    0xf060f0405090d03110a05040501120e07120b01090c09060f021606120b041a060c152502070503030904150906030b0609090609070e04080d05040501060f090b0a06051e 73
    0x410b100241c11510603042c805000d85a043d900440a04400c20107101d8098106041d181910001c2c6007002c80d1a00d01c5502c1c00060051040f01c007610301c550600045d020905488409140d03100758107071161a6650351206007542e030701050720340214115010601942c1d2040b080398048080a104546d109000300d140510211441d402040002c1c60303144103010004528080c0b205501410b450401020034840340b681c0e04122580d204601c0703210005001845000e00700b20300410a81d080c0d8002040e41400042c55070302e50111840b5002c03030200b406012180034008a1080700700d9801030081c5161400f074404100c010300c404082219400075403580031031101400d10076640078521a0b10032427000d0800004100804d4002403440321a580003104004081d030b008180700381203c40c0c0041d011807a481b1843c03d00307000d014554000380c410f4584400c010074010705400460885403034420790400b00c0d0300c1e0500101624004424207400c203038a07440c10402c0c54803a5004015446c0784880f000340d001041180461a64 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 508384631 1250 508383381 508383391
    0x70f0c1406090c09010506090409150509030a03050901090c150908010501030c08070b0f16082b051302090f09010605031506090f041509030e0307060c050c030a05060f060f0405 77
    0x241c446000c0100d650810800144003140440d50130095600d4a00082c1c124401e00340301e2405262600342c1c400400a14421608078420048414803880c6860ac1c0c4641e9a80c00c280d00a4000038140000700c0c00c000380c18498070207030780d41142c003804481c5d0402c3c0c1da01c030410315051203c00401c505030380002030300341c03080c403486019511542211810b0762401c04038030301d007840e660031041c81020108140708003a64002c0443c2d0210581c1c0b254a40180b01c0c83c10010034500803002607030b8a102010076900f000020b50103012010790039550081207241c90385081b204000d8202072000b500f00050740701064000c401141800d034040a22400800e1480c1ca480100c2e04104c030b5094041e41003400d000c18410b03949080c0c014598445040d500414152034282c640003464400c0410401c02c1a03070b510250000c0c1403184840e179600078406000c4071007555582c0c100074181d482028064a170f60241c0b003024500361401040c071441c010340040040015403503503140d5401c1c942e0017402c0f05071711030310030703076144000d41c49038001c1c28820 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 508385881 1250 508384631 508384633
    0x2010e120a210831020d1b06020303061503040c0819031704020604090b0a0b1605010e150612101508010510032018010e180303040b070f0c14 62
    0x404809102c0d1000801000c00d10414002c91208222038a52072a07482d00003c19003030790804c0c0034441082c000140f1090f20001a4000302c0e551a10001d00510300c07000e2551403030f07401140071642d80d6240201e8407400182c8a860b0700080074411021036403d07003806190080d0140c4000c0d01303020760b1050034925103280c02d2150701c10bc01031a4003c005040d000014140300c0b2204900400c2507180c10342c0001c1d000c0c4258001da89444c8d40c0c0b440281c4030f54694510402c00342c110500c074140e450744800c401412681904908440c0b0b9805c0c0f003e2081d91aa001c40d154106a034810714101d06622038104000810045617100c0c00c041c40340c21450321080780140140d40c1c0c5001c88010010220307007441c00960941d440200700c5c400c11005807000300000741095200020700f2a0360040b07603130006046000201202c0b050754054544040c0e140000c107565015070b440d94010500d14407040c88000700300d03c5054590004480c00f800b0060500c0004a20034040d03a15490200090b24003001104480c0ea00c0d43d000720100700d10070b0b2403 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 508387131 1250 508385881 508385903
    0xc020c030637053d030609060e060106020f070b12060d020303070615261002090a03060f0c02010c091505090d1b03020f060c030d020d23190e0a02010e120a 68
    0x100300c0701c240c040400740c00d280c1340700e020381d24482411900c0052a488001c0ca00c0b0340e544100300911900b9400b02c41440f20074000d480c00c41d40e540350300035036424080750700c0d14650107000c80014107005001c0460300c08034442c0080c26500e507205010000d18082e0490240d816000070071446e0001030403403185251048142010134000c07414207102c4a500f6004030803c030541100144142018540090180503071190054007596688450f004108407a600350702c000c01040c14000b030304002d0109504a00c000c88226402041210400e0f8006c5804c2070301c0d0b100d800802c000043c4000e40c40f0703105100070848481c000e45484c20440c0c8990f00c41e0b0110900317900c3e0010110400f201802140382c001d04414141d00100d4106041180c155006601c034480c21110843c82c980c00611500c40c14050b400003280c003905140c080650500383c0d9201c1c0410704c03044842001e0400d01d50424005400644610103000041500800400f0502da00551b80c000502035516808a810107a64024000070010000310714490005a0b40c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 508388381 1250 508387131 508387171
    0xe0604090305250b01051206040f06060f2c040305070b04030201020403140105040c0602031314130504120306060f17070e0603100e06030a0b0403050d020c100c020c03063705 76
    0x1484e0001a0811071155860415047c02c42d04001100c60f0419002030304252400010b20381080244501e512900b00c141280200103890310701906c1e86140c00002c9170380c1d45e80440c0030180c1c40e804071804540c02008200d0a020510102d005503001c41d50141c0309000040c0380ca504c1e91266550340000000024450703458070304000c00c00c04508610b200519050001318180340068000c0040c0042034041c0d81140001c3d512201c0c40ba039103103c0248903c05180d0300400032400c040c10132000742841c6864010100f03007002c01c00918035224004040309001c460796404064244800e01103280000a00741404102b0800d01d00c201c2980c400300114000d51441070705600c0e881c501409074100c2500141128865004800f140c4003251030b1100d0590700950611785943d030780004460b504020b001e4401030b04607c1c8103071a0301000e404696408500915065001c95002800711420569030360001c4651411204084e5140d0320708041100d0340030703100c0c0c0c01e0103039003940185200320040440c1c004561b50a0300301d40c5c40441c54 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 508389631 1250 508388381 508388393
    0x1002040302030c0414150f0603070305100b0a1403130c0b03100902040305070308070311070608061507051f020f032a040807261609150e060409030525 66
    0x103e0510001d59041c000283c89031196402810000c0411424000e04100003019603aa110400e40408000380229140e0400c41d800800a00c1c04544201c42001003c4001c0768488110050301d10760002c5984030b00c4240d1684800c441c03183c00c041c00d88010407108000f00d0000031442c01c402c4001e4094062425128909080f04180e046010360015640760f00c10401440410300c049400000c4d01c1d04501101da07903580d6441c045030058488020380d00903010b1101c0104080ba40500a11700403002181d1600d008000d440641c800362180da0802401540a8080e1034108402076910101d60800b010700182019034110041842c0d42c4102c0740100c420450000d42c45d2200504907541a202d2551091242090b0501030900d030b80703044c280541a413540540c003110303141d03541540410360115000c0c41a01d07501c002c5501c418014480c14022a41018180792030001141c0c1c0b2000361008a0700410040d51a94032540309000c01040070711000d90800c04104200c408043c0e08000541c7e18000500700d0380c1a02c40360741000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 508390881 1250 508389631 508389643
    0x160f0b0f060a080703060509070b0c0c040615020a11060d020d060504201c020712170f1003110303040807151b0305090f1f02250602060c0c0f100204030203 68
    0x400d00c0380c0b04941e4140600007001980b18156030b4029400070700c989071b03030030300074541021030b4400f070480c8900143d02925494003103409413010000b0740e4244215610750742e841c140c010f035070314042005900a039480c00204000030410700801c40040c160714a04044040b10b40c1c26a032090015801c0076031030f44403c01c41410248122042d800d07030403000400140c14400185414840c41140201e84e40340c07555000400c10855040341c10166002c3c1c504010101c134150054000d40140b0606030044001200040c90308000d00c0134544994140214800c1142c01d544c0c907410b00c003160030107243c2c15100c10b001c007092015040000c4006041c40354405000542d0000004221070040c102e007056104242141030000394108060b00c030640e0f8100d658070070400b40b50001c509074400300d80c02440304400912605100750340104845080040c2c0c0c95060032105040006098000c0c1c0511a4800603845400010440316000300030b081c6e4040202c2c180c90300074100300382e8945040300c43ca048008181d4000303030400440c6410888 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 508392131 1250 508390881 508390891
    0x70f050d090611060601020d14040b040906230f061c06060305160f1707110a030509131407210504030e010f02060f0a0b0301020c0624060f0f160f0b0f 66
    0x4c100c9441d02c400001e45482c0141000001d10655017031724002c81c88002c0580c0d024064186500351a20f641d0780713001c1e01070500c034070514041c2101c6280d01c9000111030030300b8040c40e5001034681103460b201d0f00144065a030144402a8001d0220b81d0300805d0b03031800c0d0244200420482d58080f4440c00d25040e41d0541e0002000c9007818416019050f694554111388110b081402d130a001104640c2c071900c05842198114001944034001c200d02e0b0300c20150020080d12402c41d00391190081c1d86122000d4404482d04501d121a80009020000d100782d44a5407124090180c1c0c24601d80441c00050b80500a4800550702140410405903c20416580c0942100026001c910003061302e0300740003180340440c0101403c007442c265243c015480b010303102501182c420980c100e040b108113282080c00381003000340100e20003010f2113040070810b0080c600030307007980d4140f245a42641d14125010740c042072664030a000c90072071119106090030200382c00a191611541c01800c100507907140c01307610b60103d03000c0284 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 508393381 1250 508392131 508392133
    0x9090106031e030845101509020d060b040308030901110301030b180708121c0b0108130519080304031106070909021b0102040609030611030615070f050d090611 70
    0x800002090b400a00a030300f00c1c051000031076960808a140e10104c0080c42140000c5007205040752a080c0080ca60780c0142d8030300705090b99210120800b17120141d481c244003c0c441c1f90061401403200240b1a030080c40321a420380e60001c1e410b607a805205100360400da20035074005402104001d501c60081c0070f40c0366188044590b01d03203958107541ea144078123000580356952003d80d401d1031501c01c41c81080402c0150080108039003080c0800811305069074007140d20302d21f2511010604414104140c0a000240c480c140c40304da2055460800811200d40003a00552b41c900ca8440d0b100308107900d00140e0602c20b4000c5140a40c1c0745424103000e0206100124240c140d503100c8010808140d502090322403d0b02c07000100980e560a05007a1410100940d40400e40294800200001c4054019602804807031084500340000c03e460071504906000840f00c0075009000c5141c0030744042c02a000600c252803103141c405034a0b400a0b2502d03480c00381400700d03032400f1607100002844540e0304010980c1c40428050 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 508394631 1250 508393381 508393433
    0x60c03020c09160e1302030114010e0d2102010b0607030302030109050f16110f010e060415140a02090402071524031703060a12120e0102191e020909010603 68
    0x42c0075501043e8490350000b04015079055858440c0c0d0790344440c11240c0030b190b1070554036561646030304040d000050480d5804200e5481024207a030a06524001609800130300200180e942c4200094030204400500d00031550703103068600da036030b56100250240a000b51740040e102d60501b0003400c21128003900300310581e0003540401000342c0d01c00c1c06102182540d40380040501450008207880d00317620500080465003850311424859100055440c4144d00685201030006004c100310022a10003814640103546410000745a0302c00680042260b5440a0001403030709600f40c84000001e1b141010f0b10410946030038600a19030800d61444800c3c8856400048480e403440d620702150a01340c21110011007800720006006658207003141c1c004044107003040c3c00560781490024480f071041901100400c44074076140d44954400211240000ca0f00742040350400c4050300d503030041d013204858090950141001ca0710046c0c6516031414001c10090f000807460b941540342414410452071200b461b00c078465 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 508395881 1250 508394631 508394641
    0x1401030213260a050d0f1b03050a2c0a05060a020309040e0109050618070f0803070b1801020f1305010206041a070c021c020a05120304031b03020307060c03020c09 71
    0x544030080c00c071030384610b10b001c0910b48100b0b5100154101e1040d18514014003941e84103118000c5603150580000e5503a5038842020002c0645284d90741c1005c00180700c40c2c403004040028010001000610070604251420b070402d084203030004200d03250f051400115884001c0401d04003510901c0c0903000c00c507603ca0a00408060081d628043d03d00081e20032a2612a043c01031031083d44a07404213a0848142e9441e441c0410070001100002d51549081c0d1107a2000021561800060302c81942c00780c0001d5840d022392501c0d103000102d00030701280401c4141c0c040301c8000303900074402002250804400a900d41c01c103071142802c1c40510740d00075415500f0400411001400c007094a446900206800d00c4951315200ca08445402456500940144120400b05800c031300030181000090b00c00c8400e89d500584503010b2024484002e0361180c1c40713034800e000a100244030b120001980c0352003810409907148d50ba80000c0e14040c1168044408562404020005e059042c042188440015540c9208030f00348 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 508397131 1250 508395881 508395907
    0x12011d07140d15030204020708030f060609090a020306010210150e01090b010c120905060a0e040b0f0102060a0903170f10150504150c02040e0d1205060307030b07090f0801050114010302 81
    0x1d10703031008103803950328400703c00d400b058144820041e58000e4400c5440d03040504e06041c02e03500981f041910811404c2c00140907140c802d044512858015100900d40e0b100e448006000c0d4001510540c19405042c0411140030040d00c11032900c5030800c120341181c07503d1700c1d803d011881c1c4103030041c966440c189408861283d812101491003151700003198090b01840c00c030304480e0310fa01d54100d0303640044002806144640d000c0b20308404038008650420901140c01d041044003015040800e002d6008440000c03150102540301000309800782c2000d4501115151120281c0c0c070b411075081e401c041c03000c024083d01004000402c000f03050000c0c11030359008108000075080d40100d00c1103101c0044052141081c052050311640c20301d40d0701400c1440f0b1081d1850b6003607182c4003000c54030000101c0c4100ca0410b01c184030300903540100d0340900500a45030440e100c4800181c0000c01100038004801400a0b00012448008000301504c00000459504080c4000c0465800d07910b602d0406006100079140104 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 508398381 1250 508397131 508397137
    0x1207051c0e0a03081e07080a06050d150b0301060f032114040b030c0c03070c1518170309120105061e3d05040e0c03010e04060c0512011d0714 62
    0x50581880502c2e40d54803000f400302d00340000605d064600c1c003d01400303c6243c100d241e00380100c224850a0150710f4844040c00b4000c0c0d4550b101801b400c207081c0c03800e10703c1002c943c81070a50160190000c42e07083c0d21f462011526500c9030340f0071a0154410b18007600d407410100b0b8916115484c1b440e05501e00c0281000c200598092800b80700003040b40000425840d1524400f00c0c0d08140352101a280c0b07a080600308081d03000d9182c421030300d010114602c2c88040b24411090b032040e03208103101488116042a03140b0420307000418800d480741c4001c000c0e40d41c40d1381d180020350b40000960000482c0074940310060101c4180b405241100025030140c0d00707000e540c0c1e02581d48100c0c0c0317007140c2d030402410f0003000b4040c0148102c900e02c0c5486a60042c00341c1a0b154010020700580b0b0040381c00b00c00d00c4d1104c03079010341184402d01c5100100500600450000f9003940c0000240f0102c03440e000341131640301041207068040a9020000c3d01d03a0441d5001c1e50465024031503035000207541000524401d001d5841a0144 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 508399631 1250 508398381 508398383
    0x22803081c0504080c15010b0d090c050d1b120803060f01020c120312131106070c33030b03071512020a020303010503100605060d0c051207051c0e0a 65
    0x104034140280d49080d00c01e0003020301c01006100900341400c110005a00060b0b12001e607010f01100b6403001804490352604950020b04818500110000d6410003481502c1040f200302420100001d2181d441c011070a41d4540641040c410300c8200c504002070025640e070182d4295080100d0a2001c2000101a40c4e8001e1040e0b0350001c0c1085031500403818010348840d1903a221058180c940460000000a410000c3c2018402c14268070307501523001c000101f102e001000104030014561050a100c009803914521802007414450340398000c0340e1510444000c00342803410b005048042218501c0c0b02659160105e040130084551000301281d110030550007040501603401680340c0f040c62247c0c4e45100d803e080c0940454a92500f46402516a4801c1c13195603c01d10a0031044032002c40c00d842402c080341c000503d1203181101044400001d00034021004040c010244504000e04103403000e480c3c8a10125039506a075000110601c4448016032002140454508072805515620004040c4512 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 508400881 1250 508399631 508399643
    0x503070608090d0804021807030516091a1c050901021c0c1409060d05040b0601091d07030c0c06021b010f020f09120a1b0807120b060d061b020604022803 67
    0x1945d450000c0740503950100000c0d00d042003034104002289034168010740c0a005400d01c0080c1031405660201c40d0820307075000b52064002046d841920a070f0540004100c4200e641c2c4000c0b041140c20160b03003045403011200411240d40000c0c42212048120400c2c03403150102d03900070010100d017400002d000c1d10070090440d00300d1000207284248c03542c6034030665810f20f5501505100c64070b028602186000302c103071425030200b64000c001045010807200d40d401559500c003107001050b03485113800c42c0a080e084c90340505000c241001c500114800b030000345600807c0350256614000c1140e1075a0860b1415101000c0c6c0300e20500c07030603480c40c0340442218152201200c030110741c04015100c1c01d091550107080200b55403407040c2440385101c00126180c0840301080250f61074143c2d12522141c04515000c002440a680103000a0140c50007460011a05018440001d62064078600c40c110a0030342e00328003409640107030200001c51a004240c4041802b00d101540311808000680d59030a0b50b16000c02010 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 508402131 1250 508400881 508400897
    0x61f09020c0c1504151106070807050a0e0a0f080f33040213090c031412070204090c0503010f0b09061c170f0307080402090a090201080c0901020f0102130503070608090d 74
    0x1c0004802e0a0b18042c00e0551691400500d5183c0050000002031850304101e0090400081156010340c15071441844c032ba4491501c1e2000c007c50456912a204200651041880101140c00c40590384900c010b08245001068019114107456190040707000e035852000c1000801c070800081e070045100e0303410f841e00c00c0c00740746602d42c0d10004040c40d0107088a4040140b8149008045c080045461001c40e030040d08072012094010307001d01d03216090b014840380840f10400c569001801d26a21020503a030089104807119034071100001e095075580d128020901d903c800c40c500951038500c1035507030407180480700680c0c030b03041c07240d81c102001f030300d002c0058480c1c1c0c2441d600d415411a000201d422404120406580d07c1c50564009000c0780f60a071400d07030082405900040200c4240d04c01c4c0785940f50142c42d0042150b580380c21500a50380701018140c1140518280c885824600b4000b8044054000140344840703810601803519044d02a4007820800c26290140545080702040310084124a442c140c2c0c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 508403381 1250 508402131 508402159
    0x1c02010e0105070c090e0d080705030103320a06050106030c0c0210050309070f0303050a08061806060a0e0901080138040b0d0212061902040323070503061f09020c0c 72
    0x32020144d503001050541c1850610000f103400440c600030440c40310f88402005445400d01101d40740001d0100500e615180403907000c160400c0b006100804001017040c500012100c88003e060a1140c6002c4500729250401445010740501443c05580798920340144a003000750001941d40c421403c4140c10322000202041501000b4000340c1c0180c9100705101c25041d41c0d0b460f0041880c0c4c403152502d40064540d10118a580c030b04032070759181460300000584e407580c980d4030801480d80d101c001610140510a40c0351840c5484240b0b041c2e00034085803000240e54501d0028481080d50100d20a07401c400320366806001c420208074003644007103c240c0300000ea80c0200d6000c50070f058000240694415007100c1900340301040001d2241c42012440d0420341941c101c0c074024010f84c041c600000341498190602e4005a00481c109a8427900c0000200c2310615900c1010a043c48401c2e66046150b4043c85110011401008029030040000c20411482c2c410b020070f035641c84042d12104203106030f82100b0042 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 508404631 1250 508403381 508403393
    0x1115031501090b0f0403111002030717131403010509060f3105100608070b0702041e0501031a0709030b0c0c0f01050a020c011a0604050d0f05060705091c02010e010507 73
    0x1e44002c1508071364550f40d07108008026007191004598050041d4682c01c01828040150380d081c4280c2c1c0c0045003010800e0b6500e484542401313004007131481041c04076a4400480340e103084000d060610400030300ca0881c505260a548008012118542c801c1d0148030483d41d007405081e90040d104a050048010018010304004213201940c4d0040b015101e0301009104000c100a01040403540e8204807140e40d440ca140d4482c1310721b00c40e040000b14148050f00c09030501707402107030400110103403035410032040007441c01c00c4440c02c1e0410b560b001d0040800b05400002080059044141e504029000910350354035404010f600806040070204081181e049402e0308028020060ba0321070000d009610f0039a500350001e41110703a039135859608110300307070801040a125585901102501c0343d03282c14201750901c040d42c102e60204858000c00c8201d0000418018080f44c0d002c1c0c0542e584550341d9098440c20003811090100e100c101d101c0700341d090400181c1c1c000c804011443c1d400c1c00c0c0705442d5484c40c1048 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 508405881 1250 508404631 508404647
    0x20105071709100306170c150f0412030e01090905010e071b1406070912200d0605010303120e061510230a140310030602090607050102161115031501 65
    0x1483e00215880658201c03036406030422002da0b0020881d401d04240240742c3c00703945076104400346030013010107130f14500510f2081d80104a42c0c40d24201c07440c6003942e00c03c0200c07010022900c0c194001901c0c1e040200a03981d02103240301c01015203e0051100b541441c0d1200030400014000209024040742e254141c05120303040744160a0f0003882040d5a40701031a1207d071140300440d041c130009001e0050100d59a241104d1640002c2e4204220f0180110100d030a0b00201d105902c1c050781c003400b00f150160019003540103c1d4041c40c40390751030701011020010303e0419600e404c842031341c054002004100d00c1600500308029512821a10755810329010f06081c1d071900c410f81d225811901c0003543d428071041102c001400c001d15241d64000e0510840003100c0c207607000a07240b407820070f240100c081022503440e4014085c8058003c2495141c80b505a0702e203400ca0707204401c1102e124613038818a000340160414501d0074488183c8500e40e02c2c03d016007400d4018132009084405094203110240016407040d054 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 508407131 1250 508405881 508405897
    0xf01030c0e04170d062108040509040f0b0408091509031b150d050105191a0304051203010e07020f1212040611030c1305030a0201120f15060903060f0203040201050717 73
    0x440c070741d50301c500c803013040241409001d042c50794020300c0c0740700300c076022804411103030550488807450820341030400304034949a0180003550700714541201903011600c0503004034001d81c881c80356965503400d040113128040d8609102000d00d14418420300d052a02c0110707030215003000c808071815014402c1400904640c0440c56601c0a030362020441c0c1c7d01c000300d5a0b200c24140c0d003044444a03c026070b004140100d21046006903c410070680e882240c00202d044050b54102e44118162076040c42645402e042e00d0f00309070b218003104102c040030300909d01d40600c480b8540740202c8014000c0c003060000070034911f02c18640c200a03488890350000c2c0c1480401d5210719484c04c400414143d41e81804420310360300d0341000c003140021055844000806181c001068000039906845550315030581d402e001d40141341d01c4580394205078551605012a1001d6050320001c0d00860320b812545030301b1410f0074012103140c03000345180c80c2c0c0b0400502c40940e800c40142c9407c56448441c942c00d050004203006603a01a04d40 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 508408381 1250 508407131 508407173
    0x609160e130e070602070b09061603030b040212061c050d05161e03080a0603121b02040c050307020106060207050a0b0903030708041d070c12030513080c01090b0f01030c0e04 76
    0x615079100d400483c0c03a10455105608682e0000d4480c0b81000942c0b045201042c2e20007410402c000403070507030910b00100503020f0304000591440880114090303901442000070880340801c10042c0b1841c00c5981e081d60103c0d401d1701d000000899664007a030b102e001c051568180600410100090003014a5884031164026829150800f90114100c540307205403a080740480e40031070014a56149500ca500201d0707410414158080843c5001034601c9007040c100910032030b140f04821000368445004940c00e140e00340d50740e0799403442d20700002800c40b1950380000c800c54216050821590303541d414900240c401d10710103d80c4d182c682400082c69031041c200b009001140210340010041c035440051002c034540302011080a94440c40e0071210340342c2c0d0030350003090114a00c0b84080318501c03a84c04241e003c0082d81c1c428004000d9511101102c0c0c0000c103001d2060381d1901603074020040c209101d80d4001d000112080c50380e5046544c2c8030120340b0785000b0700c00d60002800000d424000100883c008036010b1030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 508409631 1250 508408381 508408391
    0x317070c0902181804020d0f080715050604140c1308070f06020705010305070c231b030d0206070f03090c0f17010501060f09090b1f05070b0609160e13 66
    0x195200c1c007940012000c140200380800f03868034103080100b4100b66803070894039a580c01d42e48039400c10103880003051003a1510100303892030740300207065040245495030182c641718009a04266104056400044c030490003141007402550b00c0841c404009504070f6598029183c0310010540c84409001c003513480486684078460000401e041181550002d4404503803e441c05c0d81c1d00c910055055510036a200b03c0020b0034507101380040b50085070303070366180218140d140295a05688110740381000b00e030a66543c1004190940c0740c10305c0c00704074064009000e40080d120618242c45c0c0540304014816100003415259180300342080380e401c14401c05802a041601003654590160869030044170380e800c403c5600c1c001c00400e15074003440c00c1d0095a100703640d541d6101414000040041d001c034a28454005601c0303442e51b0015914080c501000e01d80d15035485881e42e4840c03c242d8002c1c44007400d001c0c01a0241070a10002e08500e016403031078818541000f210441c86880850b50882c0f914840d100e619140c8 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 508410881 1250 508409631 508409639
    0x4080c061e070815010e0409120e12060402010e0607320d090b041a160602031902030613240e16020c031c09030c03050709180201090317070c 62
    0x10070107904289901d084507180d5680d642000d94450703a043d9058483c605682c42603d003a0740c0b0032040b91144080281001c0780c62840d0303a4514015020040c0c040303001c04c00e400100c80700303400c014000b152004402001450380d8140742e00060079955000b41d615001e000700056070418045d08100003a00c1202427800c16154050130340e00c04842840d49a044040c038002c08109201513841410020241c444041c6070906e0316103440303150440080c41c0c801c22051340d0f0051101c0c403001d400c8071054645060003410050703a02d00c1c01d40f6001c44035901219004e0354482c8140280b1a0075140c10203a603503010285203001450003144074103104030482000703c10a210201100200b401d28036480500c3c0107000b45a01d44205107034170030013682c68100c01100190180d000403240d82c603118401810348020001030074040c042070b07203070b4a810154070100c0d001500c1543c8080010006c00c1c071144074410360045500405070442500f036000800380c1281e03220207000d23140b042a134112408070314000c58100a5000503003050050366 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 508412131 1250 508410881 508410901
    0x20612090d03140405060105090a1409030a23040605030a0e010c11280206030c040f03060e060a110d0509120703090302030601080a03090e220317100b090904080c06 72
    0x80d1400c1d0340000d04010050783d0a81e020000c160082d0f6004015010b103a081001b0702103d0382004054a0300f841d11007000984e02c0840c0c00700700780141c0850010b10b0b0303213003400400500710138000d4450b002c006402c1e00c4404840d80400003503030252102440d06a54030780310341400b40045c000c000380c0c904083d440d014020310b4a0740c001d0001640300911074250340700c03164034000e100b403101401200109100708022036040149000801107512602e071860440c14552604e820107941d11840d00100c842036501d039a4042c0c0c0740400c1101640c0600c0c0c249007804004400182c0912a01400e001000300e07644610100c0c82c440303814081c5000325200340b060103468071041c1c2402011813030300d4071003a8002d000c2c540021400c0c42010505100171501512010a8245085008410814000d00020302c0e0b015011005641006440d28aa08240640e0307a0000e1075140350440504200042d00c2c40300d002c60040340c20000d5580010554032404012900010503503a50309001c00d05203e0314440d1801c034021602081901c4131 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 508413381 1250 508412131 508412143
    0xe01020901030b09060102120d200a170106300f02040f05040203150108041704170c030106210c2d080a03080412020f0604140c030a080403020d02061209 67
    0x400342c1c0d090103844800d030144801201c0139140341c0d0040c0c0151140210440c00c0d0350003007100300040c0c440041d4461b2040d0181c619500d1103002460032a10011b44ca4440b01da0200781c020a41585444d8001c1c25407400c84e01901211141d1203040812904c0100c010703510000940c207084144031524144480c401d5003d050009500a010344112143c040d6400300b4541824402e80b44600908030481c180c181c0240019074504000030002c881084003040e6001200840c603015000400b0004c44c400300c042c05a40006080c000d212119078080c0c0e07d0704808000d4188481c94002d144a107010010840d40090304010a2030485078000f03c00814070140107007540e06120365540002d0b90046042c0c000252900c0180c3d40342c2c085484041c002450210204020070b4800308426405410340c01104c2e103403804a102c10b401d01e142210b0503921450b271482c5502c51203c0500941800d020210080c00e10400103940760110307802203000203401240078030614421901c0305c104890b21140d41e06000c885a103040b000c2259116 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 508414631 1250 508413381 508413397
    0x11401151701091d070b250c090b04140709150e030f100c090f0302130f230c04270b030304090609060f050612070203090a0e010305161805190e0102 65
    0x912484900042d41c10b02045c400d00382c44505064916011250006c40c0808540d00c4403404021801c80d1060009169004050002d02548801103001a480410401182e28a440150300202d1003010000843e070300c84010400d80307000c1c0ca00d0103d074050900045640c01e00c4080f20540601c1180105084900001039641414580c02c0c1e00303200103408003504407444803d074810b031082000f10710001e2005140900840445002005002a089030102e036400240ca11400c11504001c402e06109203802404000907548070031504c133041d2416180c90751184d0b8141c03030b035a116522044840040f80506145402805001c0001000c072038455440340c41035070003405a1702c9102c425518044001a074280e40082d41d104031603004113101e04020107181c00000780c0c40001c201108500040120301c0040d0b070380da644a80600305400b8507a55035810b500e0801c1c07810a03115103292910920801c1040544400b00d00900101609400840c003034540c1c511107a030b1109000c3c500da54540c100503003902910320550240a82c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 508415881 1250 508414631 508414661
    0x1a07081b10061d0a0c1e030209090a020306041a100c0f080307090815041104020313021314010504020c060103021023030f0a0e062a04151101140115170109 68
    0x41c0c9840400030122005000030401140301410000c411b13482480c101e140001d1b00742400340c074000f0420700203001000100d680000065010003840240d09080c0f00b10070746840e504039604041e0f000709000030038456840c4244400c0000116103c0204504202c501544d035520070305550b180e09140c1c201500401c40c40c000c0f511035105520480e619080380c200c055000313541100c505d070340c600041c1060101a5000400e80c1e1a064281489100140c80d0004030610030042c0040c001816034040200180d00401a8030403171080c1d00500c1418552071000c180396044941c101d8251141003198003065a1000000015400c01403908485800320b02408004503c20012911400055980e5050440889141c00501e10040d8000e40018508040784402c41d031140400c100c0c0c041c0c074890590300d40c01890340036411260720740f1940c000c0321110a0f0800208202420078034000d204200342c1154220903d0414880c0c092101448261110380394043c13031030148a0b803107001903811990384905c8070102801d8078505040507 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 508417131 1250 508415881 508415939
    0x30b01122609061b070b130504050135010c0f0807050a090306050c09060c070f05120a0602070215030403030b010905040c050f0304020f030a06061a07081b1006 70
    0xd40740000d80c040090000d841903604002400b02404a950044485000b19030b0901060040e6803070100150070081c040030309880e0746c46800010700041c08040360300c203078002d42c104001440004403c510b001d00a40c0c07a8113001341076100c0950210002e202c50711313402a1035460324803c5291540e00c250503030620040c80d11641c00c540c95a89040b140d500c180512800000c7d8088800c0c40010499000150085191600306061400c0c010010741294032805c000c4a942e800f980b000c01030500840d01c04402804200d4545200304070b030031800b039140e0841450040c2284c2e0300042600855580c0102c4210660715940100d80324a420f2802a000300700194109012807640d1000250601d413901880301c0140b0981e42c1c807800d1034404180c420013908050404c81e40100ca15000f4407030b54034200040c4020500415021508501d008050000c0c1d5401c8c0110441c440803c00ca6200480c078420b00303d40384401070b1140c0d80f0080c1401188682031040c01d900b001c3e501428510000313001e901110704888110403803d02c3e150 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 508418381 1250 508417131 508417163
    0x90c041401052809080708160e01030812070909020301170c040e0d030e030c0610060f0c020616030909050106021e0114060d0f06052d0105011b0c030b0112 68
    0x1a40d00602c840103a003c5506010201c6140c401180d96012a9990800109460711880003608100858000302c1c0c10341c3c00803010b190f28000341c80d00a0020605034103207421550454850308458800d0198441d5400c05240c0803179985803148030258002d0854001c115100c0d43c55544012024011084154036441200d56101243c40c05104102141b0020720007040c5100310706038194040d09a0000c1080540021b1010304446a0b040c40b0141c0700391641925403000f01c0c1002009401e8101c4030201000b000003a04007800140c0300c0030110340b6800743c00c0444425885492504840d030600b6a013001011070305140000400b56000a0301e03c507001c0034006440311280790603c24500b00d504070301542110740500780220b0668140507022011305401090720010b1581e5070348600c82980d40075240c005c5100400010894000146040f07608101c00042c1d0680d900e51405000800c20b4400412107400a07501c8402d00c0e04010b242c184100045600c005111000d6a5907200c6030480030045601350b42034002d07980000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 508419631 1250 508418381 508418387
    0x12020405061909090602190c0209010f0503030d11130605041d0609010509070c05010c08070905030a210c17040914010e01120c050405151011030702040e0309090c041401 74
    0x1c04440342c0d8440001e91a25501a024007441a03003680c401ea402c000b2191560400c80301e44048480984960080070300610502c05c420005a02c00c112921601d00180700355900070023100d80f891406000030400c1206884080d1151203008242010031801402c00600b07190410085d008a900c440c0d0754010000710750200d560350050440b206070303100c0c001100602951821000030707038000d059490404032801c06540d07001e0845d4130084000f070200d81180c0c00c00c286d099100e92810040e00055001d000301c8030181d511040003049001c107a00c0000f014120324480349101e14207034205550011203d491b240815401b19007a039003c0d01410942d982021500d80350b00680444441c1200d01204046007603a02c0e02c0c008405195040f0400c40c1c52621046001400c1d6a0341e0143d94050b40540c1045540700c0300da2020000c07407846480412090140340c0b811650050400310640d084075806450201d41c1004540401d401c6110740800700e5400078041003802403815469019000396284400350840d0305443e00019 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 508420881 1250 508419631 508419649
    0x10e0703050c040905030918060f01050708031b0d060f090510080d0c060b060301060f2d080426030703060603110304030e0a0503070801020d1a030d051803071202040506 74
    0x1401c590b0002200d50a1403c00d40d0214032114058019030f800c1072050000102070499200380d41c040c0025410500200d450003c00c0f8102030003090034014904030156035150114007000300f011030781d010700b682183ea9040583c0300b1a034124817040c00801c0650740328489d074941a0b5060045880c074500e0480014003c801c070b0000355040d00e54100003041c01c0c1c880400c0403540010840011105141c03181c04a0341961a40c201641c00780c80c003911018444400180c0080244840c0a141800da0507a1110b002403e4600e000340403074644103191501c05591541030649083c1d4071f81045900c07038149a910100030341c6030440030f1030041c841950148040c940d110012000e030b909002e2910b110380d60820106000a019000202d5039034800340c100f4107525540d100081c1020741d240d00a0304241d4001a808600e1007044c4109140080c0311110843c03000480000310750740c1c030196103490050181c0080c030b1081c00c0042130324200003880c3c02400c440c1d00c26281c05102c003142c80c0d00038040307001d9400c00c0c0c0030905034a0201c2c04 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 508422131 1250 508420881 508420883
    0x30f070317040602070e100308120103022806050f0f0a020601030c062307050c04060e0a0f0e100c09090c0203040603050a02120c13030b010b031e1504020a0306081c02010e0703 77
    0x404d40b0900381495180300e2400944040603101c41f9140000002e80701d44040c01403100d144414210f69851801400032803018240160300d101000e9030351036060407002c83d101040e6039a516049031521181d2034491040d02c2091505402c50b400841c0d401c6415a0016149050b01e104090b04444180d07039900541e010700c1c44540400c2034140844002072840380c3c890280440b18060411220588c10040c0071034201c54540c1c0010b20070a06200c20810804021b0241004d00c0c00c5182003007001000d9180619110040c0051011900e500d8500c1404401d21800020002d00002c2c0300030406600b030311074042d58940c46403154034046405c15000900ca6680c070700c240d0b100b43e03112000c0012103a48622400003507030b10002c24107022410131000800842c0103095a207010700b6110f21420b503282443c103003180d031940c540200c40c4404140c5008002c1c07080295062114000010341e405601ca001e491410b41c00380586402010081c4502410101c0c1d10311000180310100606400802c90309980080d0203803a0711142c00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 508423381 1250 508422131 508422133
    0xa061b0908190b1b070309150e090118110409050103021504140108100b04080a140304050d0f060b041103060922030810151205010909030e060c0c030f070317040602 72
    0x500700410115140c3c6584140400c0503043c4540c078032071000c0c0341c41e0026201900040c04107581408943e11000d54500d1400840c10704407560003290000801d900414080e84030300c4170300d85410700c100d50035a80101e69188510103c0d1030b122a01d51403a0001440240b205a100e0b0080da10b02d894480034070005c403030540380120084502014076600650b00400c010f0203602d031602d050040011150404409007001d00440400307062075846905084088140d0152402c100e6001080708101550350300384031700d030030b1944282213100801715400c1c03da0003044014481d41e0032600308135030013406950380302c0110b214240403982d4001907100c22400c08800070a005081c0042a40081c0c6400400d00607460f4a07403040c0080246520b8648900400c5219483c244140b008128000500381c80c294840c082c25000d004621020484480d40c0d460081c0300703041c90644180114400900c1302c82c854401d004030700c1000c1000e01181c1d121035083c44c2c495030f159594401030f1000c03078070242c1642040542070200c5003102c0c0254 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 508424631 1250 508423381 508423423
    0x50a0f090207020d080a0e010908010e07050d060e030a09060809060c160f0c0b04031703060307060f0c0b0c04210506270a050a0c05011b140a061b0908 66
    0x108060003584028010381c2e1150b982d411346800103a0200c010805200e141ea2076090440d54140007400f0040c80341c00005941e411f24104403100710002030b0960460b001160380000c00415030400304010041d11800500d0f500000555042c031a411901c40822203413a03076035201856448600c46500c81400b5907140158400400c1010a0800b00d0b55440300038500601e800d81c40005651b035507083c081031035031100d4801c02020900b0403d00954515540f90700d50469400c901e54903180001a0702c42120b0b002d20130074003600d440c0d80c00c1541d21076071107850581d90000d250602030810200032005908144613822007100c0e45200903030b410701002815600268008000c2c112a220303241040091011000d42002c1c4100e040c000ba942c01c0020020f90554500039805892103581070305000340c0502a03500404c2c1407001d441c00010808130344105107071415402c01c6840f0880030501c1d80e6035060501601e0702905c12801d0414042c1c4d900351804a003401ca0308a40c95004050395a10b0f101520750f644010340600e400500c0f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 508425881 1250 508424631 508424639
    0x60402090f0418050d021501120609150e0c0102010b1e0301110d09030905010e0d020d151109090609040b040605060a090903030b03160515160507170106050a0f 70
    0x260060005404010448500040d41002140480d405104061280001c20303a4810501c88144000800780d009440940210540b84001c40d40e19a410300c20b88072101d04414480040c03241c2d61b413082d028154082074030075001541404a4000c1c0c01003502d40d00c80c40c020b08811807079640c0140f02c1e4103103d803400381c446481c0510ba1480101140d1790181d04507055500c4d0100841d41d225000024010707160049000220b01c2a41c0c03c009001455540005041c842051500e44481c1d507019a4407040c5076048401a1107040103186c42420903c10019004015041c46c203030500009040000d0880d550040d21008580c0d510a01001103d02d17054801404812030500442d000c20b070716030071071035100380c01078401c2c02004d40e02d241c030100b282e20f0000c045d40040d545d50041903203850240700585404403030b80060f00e07003582004001922803c400388048003c03003001501c5a1584180c0380d0386a200ca80040c02c0d03506140d82e0700003103012404291840c20203546407040100d203d14000340040f05480c031035501c0007c07160070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 508427131 1250 508425881 508425889
    0xf060322020d0203010c0c0b0c03010f182901260103080708040f0e04150902010509010e0301060b04030605090712030c0f0203030d110c0f0105060d031817011d1506 72
    0x100303090707801c894015100400360f00c090003841d0310b4503415900c04028030042d0501140702280502421344c084d00400c010408007245900400070388072140740d003d03030012a0154003402080680040c50482c81091004a1203441c010788c540f490130420b0f00c0e00c0740c00c644802c3c4d12034040044400c080d88294040401480429090b03405032041a04c159249807606848074120109580c00e9804400055050700070401003001220340341c10340510f122010310824003d40e00103001806150501410852011900784807a41c094004200400b5a0726955960340c5d1681484d001030041181e8100c560702c142c0744009800c01214050411070b5406d5a2510414011680c441011080608060b603140c4014040e43c80303040c005115401401c00c0303030011240d4a01ca0484520305000c04a002050140d241500b0800c80d5240c4441503900f155041c80c0c60380005001c2c14041b582c0c0419a040000b103803020b860414080141503100150030310000160200c00c90b50540000c2c2ea400c901318407103403c4207059000ca441030070 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 508428381 1250 508427131 508427191
    0x1030b010b1c020f13320604050d050c01020f061603020d0e0303090d0f020309090a090c1d0f06060f07140309040c0801030b070c24020d02070f020f0603 67
    0xc10b8040840c400e6450310254141e0304844042c4503c10b8000803042d2400380002c84d400001c0c2944001840100020000344800c0012000e56500651488182c1805541c1d04400c480c003030b01d00185900484038803410301725a42d000b406105409440348180501c01c00300c0c00070312148511302f1003450700d1342410900c100f2001794119911000d05c141e1509109180c0705005d00c00b45105010100080c4010750010304014840181400c40d0000c2d5003040000381c100791944c0c0401584605027200110301c00603640362410f056401544082501109480031068000050300100e0085001007049070240c0c5586c010015280709103400030f161008200441c400040340201040100300c2d13120250307424001ca0710045010b541885814034001220302c17005008209401c9000c68005102d03203840418048181c0d9050422003100758915540c1001020310480c0c0541501103d40c8012000300640d00d410a41c07401d41161064400220f105982800c4100d185003405400e491082e000c261910181070006c001e5000804 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 508429631 1250 508428381 508428397
    0x8070f031103031b0a0c060807020d0e0f030114041209061d041508100e0102040f1802040308120711060603300f120a29180114040e0601030b010b 64
    0x2010522501e85820780140400c290800004d024040c000c0301841d1000002480da0810780c24400c80d5818410815030000e00111001058101742100b901800c001801d020400c0102e981c2c03560800d116145106015a1410b004520a0b105e51441c6020810103440c0d110042c081c4000048200c8000b112030f901c10000e0741e082d0344010300000b5140711540d16500c00b1035001e4015941c1075010a0507510301c0c01562003103000e000c504c00021410541000c00c040d83c1810148920b00401003001d495503094005a81128000d65010742820b80c1c4a40c1ca42000090000440c1d48d0004140b0700050700013544000318500303100380c400030040c1400a0001c101c46d0441100c6811380c0116100c40200c4035603003052072000b02070b4911a03404103601d0355072800c42c481032514010450503a06040c84c0700c1c5500e021803140181c4100066084001d15440c000d000720b40400030300078004003c54003002c0001000d1070038030401010101d040c1c3e8240045e602d4102075a545da01d0030b110003495840d10070f00401c000c2856201404005c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 508430881 1250 508429631 508429633
    0x20304053a020606030c01030e0304050111030d1802040e0105060904060c0905060c06011403151909120806040c032322050123091005060103020c070603021308070f031103 75
    0x140d00c1841aa0310401c544503001000d80d0001d4248a9180340c00c01030405414070900e0300b44041400c024a55807030b8011880b0780740c1804072a447c0c41d80801d07028815071b001c118020701d0801241001c400e01544d4043c2005007a406186010b8440d54241010301403580b058201503c80541030300c990b510f52004228600601d41001880000491030341d40d003000420703511059100801003941040c00001c000d6511074140c6109038040040b02090029030340c107281c1c0c1700d441e610729600d0b00b101803005440507000002c0010081099080c0b0041100d4000030b070280100016501042806014a0705400300c9074900085c0642d01035010030080700d02c80c0d4421560b400f58400d2000c1c0f501400c0c070000e035180d5080c0c1103021200c0765155143d65082c0000640580c1500080700f000546a042025001b51190300c0044c6640c112a00c81d00044c4499001c1c3c1c044a07440702590045070120350351280002d00030f4108403140301a020f1440030001d2803803000603104045e40c0b10002d400b88007601d180c1d40c0400494000f1005601 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 508432131 1250 508430881 508430953
    0x906060d020a091a040501080a02030d0507060b060705011506020102180402030a02090405180d08040c092004080706021c05120a061a0403060b090106020705010e010c051c110102030405 81
    0x44480207002d00c1003013110011400f10007900301070801c0180e42e0140c1128115030701c809610300240ea4000380d19031020380c4a05180d50313600d6141c200038000c0c003010504990024000100c0c07030300f0041e05500c10384054400c3e9407425009512084200e00b81d2182402c020380c001c105421b40d401a14240e40103540007a0107800061504040e1808038043c2c0700100c1c1c0340d64a51012000302e4090030010300c95401c030400280b5082155250550300d03c00d42e1030340c50003038000300369481c541c1006443c20444841c8900f50049080c9807156507885146039100054000c3c840140541d401e9020b5055481081307080441c0f050319034038240044542403041d8ac0710b0080071401c0345a251100020382c854a881c481c02c210460120301c43d51181103003810410780d900886203a0080416000400c5007560101c0c101054450034a03261000c0400100101d40c0e0000c2c82c50701808070700072425600d241c0181c1c048004a072007801d85650f1409111500604e00300d020486028040d030300100034010401014507440301003c02d1448072000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 508433381 1250 508432131 508432139
    0xe01092402010b03060a0c02060c0702062a010e07050a05090f04110a090c02060132060d02120a14161d120303040f030905030a0c03060b01031d0303011d0906060d020a 73
    0x728140f01660307035940c007d65644440e805698144816076002403142495490404994003090b1203125013800c0c05501c4511a00100e14200d1071813100c28007c8006009100c12088024080d031190182e206045c450180315a00180500784034894034807d00c0304082d50800c1b5507480d1903003508018100045980907907940310101c0c180300d10344500d440111aa50060040b58100003901d036400d02c3e450010342c0340d4591690100b0b1140681e901980c149082603820945605190481d01c029000307003040c800d4001751482c1001400140c030740c8105903441240c5600203442c0c0719080c221404082141e6140c0004003800000c5006414002004140c0c400140c0304813800d00c801d02105040d5001a00c084401603c90700078502032580c0424140080c100860140c26161811342d01c0125082c560f00c0300031f0446880324105141680a98065071600481c41415190024001c1826480c1da0090080d00040300e807a403036402d102c64140c00e80340c1c810940305005083d1521180c0410100c414a41e2040340d100a68034000b05d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 508434631 1250 508433381 508433383
    0x3170918010b0307080f01081b040b0409081c140708090703060617010b120a17040f0e01080f0d0804020f030709020f0d060b07050c0d0c0509070f0e01092402010b03 72
    0x180c000d080800702c01d500c9091048005250b1791000c2c0181914541540060005030400300d05a24164600d50740d00855540810110303000c0c20300001d000350f001d89001030710014401087c00424084010a2400904603100c0700020201e540710352039040202502c50000300640e000d0381c003540e0400705000480d154181c3d6591a502559500d0f00720300e40c110000b000c40701c4194400d000e040074801c003c99002141a6203507030300300ea41e94028200500707400e0300c10904030240154402100c001e000f044111400003a2115885d05a0302c00c2846031059030320814115911005022801f50124551942d6055141e03c40d0340801c00507070000481c5a82c940519000064045110b02c000c080c0203505d100d52030f458044c1c000c0c88800b1544d590340000031400c020028100043c1d4042400129811b04651007451200d8500385012202c0c1c03070f80c110784c0d041080c02060bca0034079008820780440729101e949480a21038405c00455040340b5034444d01c41245246078803c03000020b082c1103d0414400340c4000900502468006 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 508435881 1250 508434631 508434679
    0xf091a1015030e03072a06080a020d0f0f02030601121107140c0901170c1203030c160804080a0c1403060601122003040b160f03110f07061401050a031709 67
    0x11141010010407100b1580440c607840001b404c8040d01480e00949170580140541c4070003068241c8240e80001d417a8960380720750b07020083d003e50103030701081240c442003400c000951080e5201070100e0f10485040a003244507005090441c0c40e044032840c1007608940c0c44200340099000d982e030903030050110310350103615540315060003000064a901ca524001a0321103040c1b0f22030702d40c1741c4d002c1c41011090030340750ba8000040300c1c1c01025900c1400d03503d200007140040307400403000005110000000d000500100c0000d6480186030168622a0750a5666501450f80d480000d1145030140c00c40c8000408641c00394070504410f407070100022a4824204c5e000313060301c82400394056440103011040c0310502210210003a0321903a80c400107150041251005007140d089070050200700f607180c03409001071507a0300703090b1a4844036142e01e01e61522564900280500a4840c05205800d2003038000211858501f00b44400c03646c1080271542008145100307616180d1000c0341c0a0f800007040250101644200062 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 508437131 1250 508435881 508435883
    0x30c090e0916050303091f0c08070506010e010b0a0c02041505031203011503092006070c0e2a0901050f040509040317090109330f091a1015030e0307 65
    0x41d01540611884402000baa0740c1c00440c002e0f442072050100c1600c5030101d0688000c1040d0041c1a03d615102046400e00c80382c540c01400007002141c50010000002070444c16074090500460a50380c890088a0803030082620344000500300b40c00c13000150074a0340c09200b08005110450006035165000709140040d40d0f04c104080d20400001000035070001c000800381c8020700c0c5000d00c90b100e400e4030381d01058440d040001c5506482c0c0c106400061340c44208480000d5441400c02007802e07510141c90614900443da144031440c01c0c000d40e0791810201d5401c0700d112441043c1000e0500d5504030044a5540025120104162080101055070b0759194800c6218921036520120111440b4030301152050700134102c24507682c10f00301e07030200203035a031044c8241001d846420aa1103282021400720101b446540c1c000b50a4a00245924041c40d50380102030072500840e9a41c544800c0361881e41201c0d1812505001c020b041160103000040c0d060491401d00e00b0249008510002c00318025400c41d401000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 508438381 1250 508437131 508437133
    0x30a0e010b041e150f0510030b0a091d0a03050406031d01050a05011a0c0303040206030a0b0406170114091b030f030406120f020909190e0a060204030303050f041101030c090e09 77
    0x2400410840b15009613a5008410044084424640913041c00b01c0d810901440b84200403035402021454072990028601020042280c00800c1d621026000106128a451030614030303038542c5201429000036107042503940c16558940341ca0314000301140281280501d4232844074084200f02c402c030000b4050300c6c1c050707003020500149951504007407080c0c4c3c52540c19007020b42e0100307200c4044405008002e40340e1050301600c0c210355940e0342200c0c007070043c007036074107540e41c46850701001260721144640980111140c080013049441a1402c610410450840d0b81c110580e01201c0001c20300001540e018030f02a4000c0c00f00d45d4240f805454a5045812907000b01000849003088820000841e00640441c8010800c04500d40148c500100d00081c600400c80410940c0c1501500705400666001e208410295030940321618064a00303600658071921007a000241040c0c0821030b0314601c00b50a6009035440710300a1048000000150058680d0300000030900c440c1140008001128142c058480c002d104 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 508439631 1250 508438381 508438421
    0x2315041401300506490308060f0f0907020f100603020922210207090506010203030f0910020711090f0705040909032102130e060a0b18030d0207030b090d05030a0e010b04 74
    0x9181d52515402c04542e090f20305e00710040c001c0843c1e0440e4045e508403000b903940081c0030300c1e0813000c120411224030005070442e80110401c180240d0221341c102350a0b02090940300503580030f83c03c0d03906803021404003035401100000442c2e444680701d0703c50b280711040c80c000b03000c4030440d6403202e0300005c04210024078411882c00030b0410ba1941405184007510840d00108101e0a0081c0000e650f070000034101d02c042d0303180d03001003041c94004100310050088555425956604d4a240c040213002c0310580c107a014003060404601d040e41a15240e51140034540d0701d0a0a041c81c269000c006070194a1050f014400c02c01d40c8918a50340f400c8221006140e0f0f0140540d45043c002c41003003042d00b00341d001000d140300b00c00510409540d01d41c02c0d14101e9010081e0300c4e03211080c00d4924040b5803640303900180e26100d14022413aa0310340100748203040b24052070201040d0313a0b400180716125400c0161301400103030f0800000f405030a16501c840c802c07250700c800000c1c2c041031702d80124049a1003411548c1c0090110307 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 508440881 1250 508439631 508439719
    0x2041b080f10060c020f090c0a030513020904031b0203060403080108061e060f03191a0c0a0503070c03170108010e12042315041401300506 61
    0x31009540e004081c41016054514144440340529021409020100a900c41c488001c1d50b44000700036283c50070007480c0302098148002024083d038026071f016008242040b00085100000e50450400d4075000382100a803030752996821205544002c00d81c2c0240210250b92030050b840401c040e6119074440d4481096550424003540d02e03000c0000c21403500800d42030050701e400d560b0004600d0b004002034403901424011080000e00300b407048484c4080ea2051004000c4c2404400070001c1c0c20b0350701d80c4081c10500e40301c215881c001445000800ca0219804101240c401c43c441e541c00c4008a010385046038081c0c0d4815880b88241e1002ea00001d1a69160007100456040c14815001c942c0e54218207a0f140a2405104411481950450000f940c08004070701400e91504d400e00a030240440403015500e41d15800024102800c05940c203001842c030000031008030300c0d21280c0148410614803080180025000a140070301401031030560400c1207004140c0c42d400466103242c5412280d03001d04201000c81c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 508442131 1250 508440881 508440887
    0xc16090506120d0f0917010506040c0207030c030221150f090f0a0b0c0c100e2a0415081e1212010306020a0302040308040e040201080a020309031204050a02041b 70
    0x40c0806101d119a07061000c0c0c84500082d40f0040f0110f03c0c02c22140c000c0c400362040d104000c0940c040802c0202d403201040d07120406500c6284184000c403410060014641c004030b955600e1408004c04030000250140050320303040a001480d48401250185022590b003d102e00b0303d00444150320040e4854014000000e803c00d890a611140000c0100401c400d0405403075611818150068101c1d00c4000118840d0402e4404440e0a0103c42c0200c40035424202c0344a00100110500d03242c150203910524131044100b0006122601e65040d402d2124180c224100002007a50030500844078080d0580010f069070140000185162244611341002d00309049181c1488224460075503d000100102008c4180107460641941d13040200161202d6503044141c0007840380e9000500b030b800c0003040000b0381d100a0790031a4400c1c0e20030303680c4d15410b0b1201c0d941c200c10303070105079151103003600148580da08a40c26040c05c19880b6004508640352040b0039000300301151019420003081d81c04040c207801c89070350 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 508443381 1250 508442131 508442141
    0x9090a18020108130b010b070b25120902040c1701090209090403121107230601081e070b0430030512070507120905010909022107050c1609 61
    0x11060140402606102915800600824001d05020306030b808900c05104c0301c9084900d8075880807244065503110b491540058005450840e0520622800900342d200c107810240800036000c80164510000120160394100c079551281d02c0a81d03444c2000800b60340d580c01611000c8a00741c4030041c024800302d108016035401604102c030110700400a085054840300d141651158051410062544000d07111102500340b0f01d203c01c542010104081e024000d005202000c2900e008640303003070500d40c0d1054135407500c009111301c9070240c04c400c600210001441d0200f50380c07401180e0595025070384542043c40070750401d41240c041141490321401000c425031703550304407008541c0548503072003009a400030528403c804194076401441408240018000d40603203905952001c00f1448000302403000410b4a6560711602d4006070104400140c084139a100712801440061044551801901d5210042010190402c8100041005201c02d5040c1c1403028030700850801450b9108a403802d070094003519 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 508444631 1250 508443381 508443391
    0xf051c0306081009050a060b0d0606141f02121c0204090b0901081b0f060d020a020a2109032006040b030907271d01062c070f03020f0d0606050909 64
    0x80d04d004401000306800003088091168010f4020642c0c161803030114002d401041070040c6054244100405c40103c055450300d4074000648020f0001d00b500481c40e020b42c0412000d100143c0c116110500010b0304440007000800020b0a0070210403180c070800c2012603205500590b10b8503583d124846c01031400480c401d00410a900003440409403401c1100c40c010f8079800380c1481507002071880d103c90349812007a29106c042c20441103469043d54007000c5d4841412902c1150b079002e11004e4000703510b141480c440d101c0b4645555800b03001d0306540d01c44c00b81004681114503c1d581001044a103940d421004002800c5081c16035074a034100320101d50314040040e0804c8441c0c500402c040303100c806941451416020850002043c0a00c0104104892030843d8200805075401c0002c0030641030b0902803866202e00301400010985c10001d40100014441507540344000307004180845c464600c03030b40182c0a840481480b46260003200304414080342c070700340d0080c400715102140703a04039840c00440c1c0307580c01 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 508445881 1250 508444631 508444663
    0x4061407050313030e0603010e150303041d0a0e030403050d11060705090d0c05040f020a021002070803040201180b03040c0501080709030803060d030302090409062004050109030f051c030608 83
    0x5040695028016020041c0f81d09020003403040100c040c90f210b070b5400548400003911059481d41c40d0b000320f40c52a4011181c84030700d5003030800081903d0034000126002c0b11200b41c80f0001e01c00000d131401d2123000018100003002070300c80046000c0c3c5142030000b800111312038001420441d4501f07030041d002e076a130455079800b66000388040102064100c42110150030040f0303080d0f408902a0300d4240c1c04202c1c940c010310f4001c0c0c078210046008401d01c0d4000d02010a1580072a42c3c02216001c1c0042a407060300e00041000a051010800550081c0c01881859050b803201e000d406841d0300100489401c2110159907a4000c000200b180796045402c0716048203286c40c1c03200219055413203424844c031005c0c00403802124000d071624145413283d03040e20b0b40110014800c0c090f074005401c145004c0c04c4400012045000440c0340880e5809010048504554041e111182610b2841e21114101c0318462000d88850140c80e880c03542c0c0ca030814000d003907256500d803000540b440c10081000c3c03801c0807658641c818 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 508447131 1250 508445881 508445921
    0xf03040521041a07211b0f060f0213150e150f0f0f0304030f080f040c030b0a09022e0c2004020d09030f02120a0801140a030c03030e0f040501031a150a0303080406 71
    0x400c46d02829240f21f183c01c44d1020540030b040d01043d00091050320410400c040480d5008a000f4a41d01045c40d12038966503100380f40740001204000c00040803a00c5007880801c200f0000001075a154098a04003850130523190600d030141102d220242e00c100c9084000a001030b0904880540000200340c01401d42c02074500b16140503602da1a21010780d010280c640044900058100f5034907401c041f64140d07020f441e541b00d281001d10b000d80004842401103800001c2c10350064078051007080e0341e034103103508024110380c01501e00d601590505141110039411030303003c022041000300c3c1400b40b01c142c1480b035951401d2400316002c00a007003101102180e80d180d40c040000d01c109690208d0098191002c440102c0300d1060300c140010aa00316607440284002228440002030580040c1e03070601e240400d482e0700b880000b14400b0802115024040285030907114100480e6110841d0035143d40040c9280300001000041e1000900704044d540c000ca00040c030003001c00c02001010700407610708902c051a5654 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 508448381 1250 508447131 508447133
    0xf0e01051c05010605030304120c06031107030302130b031807061806031109030a1a0601020304060f0807120f0c0e030105011d040303110f03040521041a07211b 70
    0x4828880c49160241da10210440d9105002082d03114000408008044a94032541d1780c00c8100714040c84e8a0903680c00582c8a0009804c0d0f000c1c0c002d820001564a084a10b049115074080d8025040b805150200c0807084c9000304969141c80000c600071030661701c00c540310407002c6042c04d2038a84190010070030098803a40442030b808000c02040191a450b09000c15000c0c00700d40041510b00914128a038103202d00783c440d105200354014000321803156400941c2c450342e50040103980c0c074031552243c1c000280c1070440005501e4480da00e00c68008032a403502d505440d07040c840c4030050b11110355103890f4407540c604040c84100d0700490b103031241300c100750300074005989842d2a49200d4145c1c20b4001c807803020b440c0005000c151207648020b030802d2100d040e85882c1d81c8032903102e10302a00200c404072407901c00d00200395100340482c2c40e10f24400001404241c6454246800d003600001449191003000009000100c00185017103e8640d01d0118103164100c2004144002800b00c00b40368200c01400500080c0a0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 508449631 1250 508448381 508448389
    0x3250f050d0f0b030607030c23042102030f0d020106120203060411120a0c1503050f150109032a1706070305071101090309090e031201031709060a090f0e0105 69
    0x64000701210000286034160000104041d240307042035180d050052104102d1410f42640c007540038a800c60340c1c0c002c1e0544256804000389450050b01400c2e00c88288010421400449210798803000740315114280c103060760380031a140050001515080f60003030214040c42ca036091180b04001c000b100040514003816030003094699501030005030000380d60300c42547c17107601c03100c0d03c001111140008031902050030303040080c40341e0603e0040c070a0340c1c0385090300340e24628481e00800d4080c0e502440d1030106601d800d480c001d5040b20000c01d013814889501c500001080784040003e010192000e02120300e0050b2442714100040741d600f0504205100a1200f5407070f0320001075080d4045024100001c907a15a0704041c0c8a00c44040700d4440741d0342c24841744804050b40050340703808882d251001880321240781c044140d203034024101c24155142d0b010b4010408640d0324a000110220400e203414134103868500410781a43c0540761210108500003c10841441400d400c40000d04504c03507819a15410310f0002 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 508450881 1250 508449631 508449637
    0x60905030d0f2009270c040302100e060d050402150a05090a0602010c02030a080a060905130218160509040f05090708070603060b0d0209040e01061403010e06090a030804031403250f05 80
    0x13039001c3c00c80045400b414001c1e9121007140c00d4960309004a091038681800f100340c1d4094002203006410045030b85e103ca43c0280f020369260107005000074281400c1040001c01484010401d90b4480d9682c4280003c61107000c0041444420a541d080d075620f00315802e000d19018036500c45421680340c51404804030313502000352400c4880b030386002d0080703440d5649484d015100e40d801100f83d00c0e1521050094500b6000c2d81004424400c1c0c1d10000d0101000c000404400d50894000e90600d082c074203401c0340507114030010403007104020b03c00203035086030b080200c040300d41c2155191040c0e4000c0340140300440040141700000d02052a040c04583c1c02c0c410103201c039000e540c44131000541c01180c00307238265030703180c020f040d050f21000c0081002e5540c66072501d65074600010454029444c065400414000124071103214100180042030042090307541100e95044c0100142e0410242c0c104140c40080703c0c4004600030401008814080034040410100c04d036681701c01d4406121400c02c03030320b640c071307401c0019 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 508452131 1250 508450881 508450897
    0x807050909070b1c110d05150a0b0702030307151409030a0f030b1c060b120c0f010c0305040e0906060901080c010c351b07140d060905030d0f20 63
    0x81d15803103242a095144003c080304a1603d015400d000c5840c44d00b500c144080d1481b00c000b00030511543c3c0342c44c0300e10440542001151034000400d454144400460240141052807001e400c50745030130307a82c0d01d070340200e110510440600191221683d541c01c4030084c0343c10b90010842e4000d5460010840d20290940130044c51020515481c2d47c80004a5a500025200d00109400d54904000040e15000d4020084582d505214a00181403241030000000f0000f8114801900c541070034800c20300151040340c0d80314070850030011f0030080030407040400000180200400c000a00140c1000300410240f500160031a4042d40c0c00009007a02c240e0b8448000c00e0321940201599400c5462030b0740c48401002101c41903010810000141554001c12000401d4a440d070104689502c440c4003200382d442d00c0b2184100c0e4412603090340c0300c2000746010414074600324450740f030000b00382180b039440a040d50800360409900c95a110304450101400b0b002e0b40a9480d02d4070b10f040648a05d542c012290390044100c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 508453237 1106 508452131 508452149
    0xd030e0607050c030919081204050f01030c08162303010f0609121103030403150219081b13080f07080106080c0d060b0a0519080705090907 61
    0xa41c1e516410f840061442c240001c0d042006c164040155840d00302c0031114000740f132a20420140c1103c104104045860790b18110800460f01c03014031081d4140740c2411500401c60b9031100740c859000c030701115068981070100208440d0921000681c518140703500b02442003283c80900554129928000041c0000e81c6619040b48c80c91464032030001040481c5103d0400503000d036017502401c000c06403c4074207142c2d9039194481d950194240c00201503a00080226402e42c550108036058002c07410952424109031030304c0c00e20180508200c11910202041da410701d0b1000d900181c00900d1018201c0d02041303150107005880389210300c00c004a5600c0d2502c00140190049240c002e0840000c0502d003206843e80c41d6007014111001140340e200c2c8400c00c3c08101c66490403010540c05c82703000d0114070700c1410a400c09103405041d0300140d01c034150140c20455860f00c0025141c0554140301c0e = true := by decide +kernel

theorem cover : BRFrame.Cov 508273381 508453237 := by
  have h0 := BRFrame.cov_init 508273381
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508273381 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 508273381 ≤ n) (h2 : n < 508453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
