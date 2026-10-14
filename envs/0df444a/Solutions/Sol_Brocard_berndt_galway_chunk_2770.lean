-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2770
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:41:06.872827+00:00
-- url     : https://prove2.me/submissions/24a6fc98-e8dd-4b95-9654-be42162af06b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 498021582 ≤ n < 498201438 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 498022832 1250 498021582 498021617
    0x302040b240301031208010e13050a02040507090305161401110106350a02150a051c060302091305060402210a1103010f090b01050d0317010b0d0b030307030905060307 73
    0x3107081c1e000281a541e4a40c11403410711000601c4450f02d0003404640c40052120007883c03441c565110020402018950703003142072151800225040c040e41041c5001c00703101ea0b055018a00000b82d0740150101e90446a5054040009460a220710b50703d4540d50294010103600c91207511008681c070700001304a807500c4107240320860800003140d427a2100c2120300d4681c0d0100c002c0c07000100c50b0200010300110351154000c500c4030682540344141031500000c920640c0d500840c20b0f14460703035502d007603100c2d020035085441005040780e0100307920500391900003406a21f0210284a0582d5010000d0b1000d80c82d45d070309202c01503c1c4512403000c02801d440c001001e402e81003042a81d6103018594608210100c4410f140c00c540c2900400344841c1c0c00c05c4840008103100002150441e28107a4111082c04054201241c8140042094100d14a10710300005030414400340a400c240203009010458410f11000701030b500d00c5095002400301c0c0011000304900c2c81c1c042c018560007403090030001c4103054441c010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 498024082 1250 498022832 498022879
    0x818150313060e01050f0103060c031e0c0e0306040804090b151324200f0a05070302030c0a140409021512090f060106080f0705040302041a280302040b 66
    0x10600044950201c000501425000c0c1900d41d09000c4001c110604084c40718049400050001401407a19030362500440b5100e6840000071012490402c2001c102a04141001d010145c000000088600304540b0691030041040d50103950300580003841c140c40c040740c800181c8110592180d100c003110092a41d08803030300c4000c0003002c424101200750b070307814904140d1800c49801c1048801c00c0444100055007900142100d620503030440407011070b0340c88076000d07500e40050205040003030f0045110728000c100d400200703902501e100f101a0f07000d01c2c2030b0a00f84519000503204030601200e0b50000000c15042c60392000c010540050080188507000c1000110703154802503040381c08131450020072800140900071080791581000103040d1951601100070902c503400350200c0e030144046008928154007034801c580055138094001e220804a520480342c8020060240e035014021044985401d00003503000a0240d00d0f06241c986e140900310b4080c00010301605440c150060040054150f00000c038220 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 498025332 1250 498024082 498024091
    0x20402030103080c1b0d06052205030304170a1e140313050f010b0f01081e0f070e0f1c080403060f0603120f0c141014060a0803040308181503 62
    0x440c0d680c0d06462400514100d1075114a801190802c1710f00400303907894424061007141c1182020860f5103409002580c0340b02c204482c0380340c0c1d00b840407802003088404009140710702e0203402c0b00d88030000391105101c1c043c81128007420024042002501c000034044801544030308880c601901c1002c0648103402c09030380161030b21200300002a00017000c0040402c2800400c80d0704c0c000900c00314038440082032a242500749054180003046002a08510f244081c0380b02e07105420031940564149000452203000056442c04000f401c10620315544e4200101d0751070400001600c008860226054007144456802004940012080200001040217070141c6080d00c804139000140081c40c6181c91000304203410380385400d101d1800314000500c0d40000b0000c0104e03405c041e01044079515404054200912016958080c5240001d2616644240007055101302000c0d20541452922011500c4c1c0e40c0c0510300c0014102c03031082101c02c000149400702034000c0c42003d807028115888003110008560421103 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 498026582 1250 498025332 498025343
    0x24011403091905010f0e120301050d151404030e0f03060103110a120c0509072d0c050102130501091710020a180306020d05010e01050609040c02030417070515091c05010603020402030103 81
    0x1000c035401e02d1203600c20a901c01b2031410080c40b0300346001c0811421030005201c1d540c07103410700786034440c148001048035030302c0355200d410204400c410030051108000000c0e1000d030001150380d44000d402c1c0c10159401010744400500034901c1e80c0c6141c0d9114101115020880d80002000c070000503c0195803035020941d0b44030359091a00b40781040103100715402c0c028001c50400c60782e54524101c40c4150601d03465021030498250300d226034408026100800648401480c0e58400100c00c1240c6e41c03054a610b0903103100f61384100c0303015591480c60002c0380005518400350340040148805148030b40d07005000c2248181040c07020301606540307180f2404015401902d072503070006810003c00c0301c41d214880c058880035642c41480d504120129500b402a50304c5070f40900d55411481210600030820703140105076076082c422030a030550702403075100d401c030341b203046d008030790315501f52015205000c00d031400c4040252416440555240c2c2403440080401c00c2030700d46550703030034021000d42c545c2c2c0025400b96002c1c4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 498027832 1250 498026582 498026591
    0x100e10020303160503060a060809070e1f0501030519090c0b070b16050a050d0504141b0415060e09250504170606130e030c0a06052401140309190501 65
    0x10f981024a2203c250050402074104104411aa6482d1100302610380e24a815040c40c0c1c0d420700840c2c0752420071b0304400200c42d403500c2004000244801007c1010131308490700f8406540d144019416564281e90800b64403060880c462011582c3e40d000418440c014124140050303a1418130744c0c515440b00c0400d4441c50500810850740580a0000d00c3c0402182d03c0d0803443c08024010042903805401403c10007161200007150034400454900c55080c146d0109640d80b58042c800040c603040b0446000c1c41c00341d400d10002d142003800c1c0d541490b0840c0c4560b11080582808041004242c41d0024012003840143c0010146d0b05907003c04000c2c0b88401d03541f12039580381c0c20807102e40904030b8041c15941c2c0302d5103c0800c114080c1c42c0c0c0070301c010380ea244941340400c20320b40080d1042d0560049402c2c9551764494040d402c000d018054102a000d1400c4002c8e1001800112600d410030388081080c05022802c10310403000484c0140c0c005683c400711032019103806481200c41daa44001c072060082e5403aa464 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 498029082 1250 498027832 498027841
    0x4090b01090f0b090a05012301140d1b031509060302061206060d0213060e0d030e060c0106030f0b040201140414060708070614010509010b0414061b0d0c05120703050702100e10020303 80
    0x44240483e0408c6000e010740030a80181000241100c0d85105800550780001c10034035484034864010340d100b0450651044400000c1400017001030000a00540d1105440940000e140b030003445003030140c0307802500061078506a13450b4550702c1c00c0094a075603007001007013001d0004115030b88041e22000d034420ba1400c0455160220040c5039407c600311141c49030903c4401c03400002d030401880210b5900540d8020f4841c003800820a006015130b60014101d40304c103004050400c11401310144c8668806d8a03a110608aa20113064880c0101d000d0780d005140c5140440d01645005009000168420083d1910f0b10986d6030311a0295060f45850503038291341c00d801400b040c94440c1038240906007100703c0c2c1c0d00b41494540a00e0030310300c091504034025100000c00e41540608000e10340d507078030704c850111035110701510b4000300303511402032090705c260281e900d1402c0c1c0102c0b03020480d00d03441c0c2c0580d58907003003440c5502000007200740c40040c40140714402c03400138000c1d100c2d01a40711400c2500d8028503140d180 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 498030332 1250 498029082 498029099
    0xf030204051608060d030e060403230a03020304030b060f040609020a030b041a0906130509030a091410032a110f1c2303180c04090b01090f0b090a0501 66
    0xc0d2500c0407500341d00e0b40040c01e01d580001c6556008004880795180c0b18417509043d00d12401c02c5601c55040500003801105014442c144501c490106584001c540060303240c04d0340d1621000480100181c008000420209a403071480e10b41141000f008075136402e010900240c03c480c2644c0c009064241c001c92010300340d40d01403244040b9180700740c40501c50009001c14040c9501c01d004c2243d4491307614040440d4003600c909c0111001c0616003d020031441c282080015940d0300440ca0b2800081e48454003c940580341503880070800002410809800d20400300a802905d40b4408a8102440c400d220b800308166403041d039481ca50081d00c9110400107115035260400b15003000b1030b1203980c825221925030a0401d42140e088009514240c400c041d900c0c40b000d09064080d1400300c00c0b080b408414000c89505060305a01425000400c96928403032000c01c2c0000d551303404101501c800c4600004002d070342020340140c0b00d846090500001e0100c0c6070800100e06000540741003a04543d00d00041c031440c003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 498031582 1250 498030332 498030341
    0x204080709050a0c030b0f010f02010b060c0115060903050303060f18010605040614162a1d092b030e070b0904110c1914030d050709050d020307032009010f030204 71
    0x84d480d1a00b4058010400c02048803a00070344000c1d8100f241d8540040c1b5014400e40c068004110700504590355030001c10b4055019080d490002d82001500302c0d80001c245008802900469610001541c219502c4004010345407240700801900910f070341484082e54411400354038042d104503128180c0399810000b00401111a1800c40f10900e070080110080302c51140104001d140d9000b0000c0031040901001d03a41007104601090750342000800011a40110f450b00c0c40e03401c400b01c21200c0c08a55989081c1540c1c0b00c0c0c541c000f80061400000108100d1403a01d181412441240e013404038001842d01e00c0c00c0d04c2e100c42e66100c802000404622101a854a405207602d13024550000d542040c0c801510183c440d5400d910148003031501d88500341c104000c410b001c42405e8441400d40e1b440f42d4001d1000300103040c0444003000000d5850794003049501d82031100e0260b540e0090024000113046585405911010a245130016290200ba000680d610070310540d020300400002c5c20f400e680b13540305000644 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 498032832 1250 498031582 498031601
    0x215010906050303070609020604080d0807030c080403080f07020123060a0510050421020d060509010b0306010f0e091513030f03091104230a090b010b070503030c0d0204080709050a 79
    0x6410030307204110030b0b0b5000007902c002e150400400620044540700040d05880740358001c000d1030090044200140e81c02c4204584280c41ca0386040c0890031411034120f0300041c0032100100031811000100b079010014111840c0d000e80036000000d81950484080c0d14a03440b01c141c01a029007840b002c0200a007400340c1120000c000903500300030340070701d0054044e01c0390045020700500340d0801a149000c501124801c179000c1c40d0080c124041031902410704c030020340740444444829600b442c207004044d00700021a58100c2c2c0c02031340040c0c406828651400e90000300038100303100c40c3c8100d080010704c00108520041c00751049a5000185420364503010f461160030901c1c03a40be01d49000054400303c0d504500591010364200ca00280d001407082480510f28108458a0031400400341001201d818aa02c5000380c40e000b5040e4800c1c0b680e071103e43c0e010307034030800400420130b03002400440c02c540203103400341040202401c2c000d820181c596a0322440c0518551005000702c3e242c000780309443c2407511502100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 498034082 1250 498032832 498032849
    0xc042918150406091203050f07080306090610091e0807271104050609180c0405030c0402030c0a0509240a03050a29060d0230040b130c030210021501 65
    0x101450442c014200d1306081c4507101000c07446500c42010548100e088425000c50340b1551030310355680d030601903d5a04115020781c091043c0030040303611890041d240600300f00c1d4aa5901e5006410081c3c4410300100607801c05420034000300006c110703110b06010310805040000f0342e00000c0b680c1c9003d00c0481c041404141488245441240c0c1070305242d050448054500031b840d40740d03492141e400401c04c031420b000c2281c010320026209204076080101e0080003225800c401322115000050104000c901c402d441d95001c1c0b20040001c0c031522801007014140016004200600f2100c0c200300e41e4101094440c625041e48000040c0003021503090b100c1c007604030713408540c10455142241e44e42c00042c540c0510b010190041081c4903000d81d03407042c0881d06410020402551a4036881500040c0c40c01206100d003410a564000c4e01413107402c03440d556210780c1e0041406042a1103050380d203030038400d4412040c1c03a0105940b1000c0050303140c03807880c02071250160340240030084149808a03090241078210240 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 498035332 1250 498034082 498034087
    0xb09130b0411060c030c1c0219060f0209060c010b04062309040c090207150c050901050304141507020c0108010b03060a06111c09060f080c04291815 65
    0x2240840384603503070081d0b210003400e2480c9200000502280030300300990b0054480050003c030717003410104080d41146050047c104020b441810245c0e200d960910304203004c1410071000d030340440c50603001250321030b0b040c020051808040102044e959841300b545644181c0d181c000000302c0341440e2040e04014030004590840d59580c82182031111849070704400e01c180040c102260034044031001410040420350b000715074649440c909105440c880680c1d00d02c0d85440c2c21500320016006000311450150141c0d1154555070b039903642c61701a41e0420780c0d18025446030b00002030403c40b902c2041802100b45e60010401c40040c07200040003040140c0007240e8460f0180107100c1c9980300d584241068030b0080c1003080c0a0386140c40c4c12460700350442c0086004000007440401c005800c001c9410070f40e0700c140c1d10890045181038095802c0002555601c8022008010411180f18030a1424842c1c0780103540d4002c075074061180307114035604004508240340c19101d540f103149140017100c0382c10060820758800d0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 498036582 1250 498035332 498035371
    0x4060801140607082a210a020606010507110d08040905070908030a0e010c050304060804050f0309033f0a090515030105010804260307110114071d03100b09 68
    0x1000c0d4040c209000707200100109002d50036040104020b1000e061240c5c21140c0024042c10700c56848040da24401c41480d04400d042654400c03540c1110a00e040c0c9400500064961200448043d880140180c1e00048040000c081540d100204420200c1c007449820740c4613801c0c030103640b04a84028201c4024492030b11010007544101100707413040c0000750b090020101040c040184c0d103d92500707900811601001601042e80c54210001c240141c1c050340c12150804001c82c581035170f0b44641d081c440d6140c0d00c0b4840040c00101200d0202c1c0381c2071000035456400110648030324006202172403030100700c0080415540881070348030392030100401e800c985204540c0307462401030006202c180109030403c12070a00080034000c010500051342c1d50a007085004410195822074a0344e00180e5032240052034000c010081002c050044201d914401b4114402c6500e40301c2047c0d848888102c219071f284d4440420341c05003a0340c03d0000341c10792281c0402c081400c030701520401034880b0f4001d00e10502e08054581c0b01 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 498037832 1250 498036582 498036589
    0x70c050d02031b060409050f0907080d0804080d0e0609011e021602040f020f070602070308011a0a030c0228060f02040305030418020f1b060606042904030c08030406080114 75
    0x403e04005007008220304404420101c0c0c00d9115641003142d034141000d050140450071104014810002d603003d4402903500c5000d5961a84a2170062000107110320300800c01140d07a000003030800302d88010317000607003c40c0c8500c110300b000c2d4100e410701c009175944c242c0c102c4c018420708039841c585810240304514040c03c1400c1c440072058848806400780390b68151a0395210041d0741100c0800458a03c19a02c5402c42c0c80c1c11006580a071200b1800030742e212000044180300219824174081519003982e0420606d240110000e1845940802c03c43c4075074030300d40c0b2420784011603480102d550920f04c402c00240302d091500c1070701c079200400300701d2510420041010520100c25901034503100310720b031100701d0400b40b03015000e07002d00202c0802c0c01a000840b84000d84030791803144007200091064404560343c036810090b403030140344150405107100110780314189688005002030345000410550034544c07241c4036414030071980c0d084040380d82e0000a0a00c000b6400034101801401e0a071074465600c1060000f0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 498039082 1250 498037832 498037843
    0x1020a06020d09020a0e0a0b0604060804030c111f0e03070503330a020c010e06060a06030e030d020304060c12020a12090305070b041110050306031915020f070c050d0203 74
    0x1609441c1e010580089061064002da942203400a00c0040c003162a490003049241d400c1e1141c071060340c5030080e0b144072801c100003690700311200c54940354944d40d00c0d03840540f540743c101a021200320101d8480d21040790394001285407a140d00b40c0c444414448030810181c001f01122203c68401d5201c3d000c108815030340040c803c0141000261542100c0322014030085050741c8442c0c0b42440e10250100300044001241d01030b000c405000402441032541c0c8660107074a4107400d40e6580d400000340201072110600a0304044800107a02c42264a0300001800c1c003401c98206440480e410360f1503042c281c1e03016601441d0700b071201043c08402c5191079072012018121045034426491100c1d00c400301da509141c000c0c02a00c10168001206100034a0b07d440c280f045041d03c00e0a031807048040c2d641070b245451107001640c1c130508000c0c0060041821316050302100030031542c8202e0f0030f05caa04d56044d01d1081076001610000d4601500f16482e07100910f010801c2d1150303508154025207c051088002d42d1b8001032 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 498040332 1250 498039082 498039103
    0x1c0c03030f05120a090c05010c0201090b0c030912010504050c090106171503030d060623040e06031228080727050d030905190602150c040306061202010206090c0102 72
    0x8150003205000c081c181c03090700030500000a1240d801d01045080521500040d141c68840c44d442c4039059101d400541d080e140c48180a0300040482c2418000d100d240801085464000d904590414000d540041c044801102840182da5144c80c24801009010010140c015408461110142d1304060740207220340c21204007000303230b04402c4021860807141d0500483c907407240601580e070303164046002e2802070700441c80f51800040040d40e20130104103503581c0c81250074041120700c91905203080010920420042e001030b604d8000c02c44000c0006103c0c0b002042603071008501d50604a0000070003068a040c2c5664101c180000802081984c5610080c58131044002c0f1019810000350f02100d9142c8900a400c00c90700150030021801c14141c02020001c100d600889101424011070040c003600e0b07048511840015a0103248203808004940041e00c0d4488490b080d07040c1025500c0d120310080d41c1c00c1e5400103500d00c1c03116a40c0c2e01556414090315501501030300c010a81040c0d80d100003991f81c007080c3c4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 498041582 1250 498040332 498040337
    0x1b0504140420060403030810091104170705120706020708060403080f070c060507091404020703050702060703270302011b1112071e08160b0d110706090503091c0c0303 73
    0x1644401d90b10307699460500c4081c07000d041c81d80ca441e240d103009401000242c035000141034042500082d448114000c0009400002e403c0f10300701454181000407030f04c038402c100e00882c05041004110742e110700294586109603a07004001d018500b460203400d0890700d403c09106908038504002c080ba4000501ea60003402050074032802c1e40c2c2d009001c0b2a072510340720000f0141800c19007840b8020358051500801c0d035900384050040303110110100300c100e01c174942d80240030030001d01c050000340ca440c10151076003901038204800305481c5044c4ca50b510929460b441c15803d09200f8061065503807002c050107980c2001d95842d000203410b81c41d1020117840c3c1440d02071040080360203070a2602000c1c4500001048050848a1048604000034a809c2d03154003e00b5418412624108080400003030b0420031503c04500151612108083c0b46000c0d140e40e56000d851000100907007000143c0e070b8072603001c0c013500600c0a541c40e8101c1100704010880c0402d4140303490165440008041007000b0781c8481100d0f03150 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 498042832 1250 498041582 498041603
    0x309090f07020a02030a11040b01050909040803070c08070602132102220e0105041218060c0204091410050a09020a05040903020c12100f02040b1e0c0a1b05041404 71
    0x2860120b03d0b0079041c0724002d4241c01210030b0304081011003622102c0000d03040747c0c02c0c01544120702c01107880740291140c107503000d509480483c0204150200650f004265440c2010784482d81c1c3e11840c5507940800000ca4446a0000b0103564002c5405e48040141006117000c0340b0088002c0c0c0c51070140407014601038410046602241609800080102c185208144090244c2e0541141036402040708440c01d64010000c08403890b0030502ca400040450380c61119800c030b1890900343c0442d141c0c1c03002101283c02c11343d644055004913407000d9000d101c065604e001021190a8081010281d44001c0d00d0220001e04220413a00142c0e540070326070f4146c0f03400355000203480d81d4500701240760012004502e90010b01c8103180f042c06d00400700f01c4040c1b08038a0a002d201d42008003c001040380324610a00302c03081c2c02408004a04075100541015941c006102a400c00b42c000c8030701c50418007980030850340121a2102c3c01040383c1803500940050034115820860b0400d21803410501d820003c00c010241c1803038 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 498044082 1250 498042832 498042841
    0x5031b0403020d1416080a0b070c0804170a0804030803090d0f02150c121305150618060a030b070905130506010c0b040c0b1b01050907051507080c01111b0309090f 71
    0x40003200ca91500200d045d220082c1c1c0c074071800f52101031807201500d50241d001d001607902400b85012a128a40c00340da07851400d443e2002005404031048043c3c0400c0c0121190384000c03545000c003600c00746000e02826640d86c10050800742c58000300e2822a01030004441056000c10b07004a0941c0c1c014101e1a1110a5a507854a4100c00c3d40f1840d551690180ca124040c0050581600d0311448a107118100301c610009035520070020f04241120510750000c0c0c00102c05003030000080b00560044406464242129100c0e03481d000c0d640c0301110043d000840d00b003002c1010340b9047c5102103804510b44810406c80c109500020032003030036500003400b800d42c50300200f020000400c00410013015840096a2075000c20040d00d00850b03132406900c0d0856080c1004260049000326540b03085a00040408101d240c201c1903010b00c40d04003600640348020140819518204203000b0b0410a5010907a01566074000c04102998281c850445d41c1055000b8002c880f10782d02d8983c202c3d50800501d5030010000d5a4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 498045332 1250 498044082 498044123
    0x19110d1206050a090e1b0d0f053d0e3003010305030706060803090f011101230402120615010509040b13050a06050d050604080a1e05031b0403020d 64
    0x780e11007500030800500024094446031700c5000c4601341e08060b40c2e503070700c007075003c0d601c119150520156011041ea0360810024040c070321a100c46503c100c00b55500700c1d2205100401801004004003000f01360641d6007050b1a000c950b402c0d081c0304505904001000841070f07520342e00c02081c00d50000540525144840304100343c45c8000300242944420b540e030750303124603042d03440707801200c4219956820520085070002010040e40d03001900640318241880d4034500441e03c8000c2580f181c40d11b5580e070080c0120090031072041800c1680250222130803420b00303105025200207240b580c40c1300e03900b044082c02050115952402e260303110901e0065210300070240000c00074800049241d070701c14035022462081d1015608558410701f2201c10802c0216038500034402f6413410f0f0034006245402145c001400902540007502100074686000c1201c106401c48200c0f007100e407001c0e4580498400300c1040001071581c414002450040c00086003094615030200d0440c283e001383c01400341e68030104c4042d070b0741d2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 498046582 1250 498045332 498045341
    0x14180c01050f0d09170c0f0c04110306150d06080624031b0105210a060806090304050103112b05130819021c0c0302011104050901050d03030902030109030519110d12 72
    0x1814400c1895030740300d1005103150f841c847c89010a5241c003442c0c0f22031106203418460080540500c540407071941e0f90790703800c10144640d41103d16082c4c0405110609405400f8400c0d00003401000b401030030706090a0140b503549000c028407000c0d020f02004030f001031644002c00e5800403585000070b8a00c00103c0680140c80d50701074071402d03040404000c02180081c0050400081c0074103400e400c10040d6503110b0300220380b0383e1011600c044295204010401c85540b081d44050b5130800c9601410707082291200d820031041100c1000c0040038403400c0014903103180c20b0301c5525000344200c003001c0020003259640c0000f9001e40848851039080c81921501214000d0040003480441000000808203201c0009001c5800c01c11003580198641030016031007100d42e0341268281e401c02840c045550f86030404000303d101150104a0805440b07102031001a01d0034000c0a141c0f80c402d48030103840b560400c1c142138040f10b01c1c0c0480c500304095052515151100411280d0449903240340401511024050203005070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 498047832 1250 498046582 498046613
    0xc06080c0c0d20070f050d080712051b0c010c0308071205100602070f0506030c07031707050405040f020304031d0f06120109061509050d020414180c01050f0d09 70
    0x10300402a840800381d81c00504003c00c00f041c4421a18100d1629261980d14080340c080d80a050b00c2c4620240b10f68034000c030901c00030030300c01c441c114501001c1d55507004003801141c0502012840c00b050300b000da580c2000d5001c24020340c03200204441100c0a00003400440c8030640501406601c00c04251018858122000c484031003040c24461403d0012065000b0f4056106090040c020820301188114503081c000081ba5001070207281151035140d08484607034407240c0214207100c84400d0700d130203815541680500c50030241e1103160710f0f90b281c103061205590810314030240041c41041008002600080291207000d44a88212180c00e042c2010440e400ea0090302981d00010100e1841c684810300c50403d0b040c0c8803002400d000580d6206400d045103c0c4811005006c111100824040307410281610424140010b2022a25903940300180d0031414060311000050380c498609038030031030000c005032620704400b8640329103400a001415041d038015090207400f507584071101c210620540e81d2500b1840e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 498049082 1250 498047832 498047857
    0x405040201140a0906080a0b0d1502270a05011403180f33090a1203020d111209161404020c0d050d05090d05040e18010609061a070c06080c 61
    0x1141c41c003c0000c0c2c802d410622410000440030380005142c541140591500d824018100c03104c000001e507108514400882c03001044150b00b40242030700c1030b004044c0402e40c2082c003c0c0c2e00303003d50504070a1040129480d00501e0501401000760020494803d048070342c42500951142c034050702c8118014244000f1010414280c400c1020b10ba03858820703500000c2841244200e10748910702c4a221440d80d0f28012218001d0350b412808100d0080b13540c0700c100c180d4098103440d0040c5411132038640c580403600c04e0303081d0b84907281003c40c101d00c051700755017103d50b00030309090000c05040505c5510f541c910743e414013801c604810740f0f004105142d22250107603042c8040c1107064542c0c04030001c03030080c8150016000c040d41c441c200800700742d191030003048204d444400781c0d8031186440d05240300c602c81c6030009400c110110907251403070203100c0800e00c50500907011220012400520700348846150341c0c40900414000d180801c610000582c0940c0ca10302101c215080414050b600c05500b5105405030b00c510184 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 498050332 1250 498049082 498049087
    0x5090102100c0f1205041e0c0302031518010506151809042103090206030703020a26180c0a090b0a03150c1d01080a0b030304080f0c010201060b1602040504020114 71
    0x25480d030410031a40d026486984c0f510601948007a405003510340544000d0400340c03034400e015109019000502c40d00c64003440d0010480c6d6544c0e80424a4031b68140c1c1a0300450303003140240100102c200550340319545c5c07404002d0000b030800c0d4001a0401e142642030b210280381c00a80c25850200300c945c0484482030040c11001d0a2604c1c1c18103c1c1107815040c84c4414400951040f50080d84c000d01c28414100c0d006000d49040d40e460703040a8000358003104800b414450b03c030803901010004281404d0307424002c0f4442c1420350801c5044a110700d40261155500d903000340030001c0090322540402c00884020001c0426503041300804505e01d6900d0750009044002441807a0032082019040a0484081a55400d00072070403141d28186900070b18142500240c0c08001003011461140c001518212008040e80d14050b55070021b185400a650051252078000ea0588180c640e0280700c0c040040400c0c10381c2c9031901c1d18403c00e1943da010000c1c0021700c12552030010800307691050a441c201c800c03c02d07071010ba = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 498051582 1250 498050332 498050351
    0x503060111120d1103090d030510081009020102191e0602130803090108010501091413020f0a031a030a150c0203070204020d020702040506061905160203011b0809060114010509010210 80
    0x2d01580c08244140c1c0f0326418041284180ca00d5901203e200307075580d0000d40b01118410300e080b405000042c0810070f0140c0a03001c0454400014480d1640342c40c150070f4000390049043c400039040422215071880d40e03c0852214001103082d1b8001718107806810380322655940c8481c60000028017171000040c00f0b00115600210700c200c0000002c0050340f009803503c0009a80e50001141d4400c500d00411030b2040001b046803039103082c1244401c00c0400d65140140c02c009000034410040d410010740000041e88441c001c644412600c0b49a01900704180d0241482e04480c3c1c5601c40c003010b00100004110760384592461040b1710138400e407200f05034014000e6607699030131800f1901039000790405034803861400d00031904c1c1d45030100440b1070030548040059806054000706484640152300c0e462500d071040f6851500607a004e105080071040d1200380030708030030b00c0303141c00802ca9040180300c1c10b07040e8800c000501c20703d4401911901110b00034a0580d5480b240200100c0c02e044c61180484406401c005854 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 498052832 1250 498051582 498051613
    0xc07141908040314010b0d0213090204020f040302040509120a0507060618050f060301090309051302043828050d09060c0f021504021c0b090a030806180105010503060111 74
    0xc0c000c0b40d00441d4402860460304056030b00300c84200e40340c11f90100fa90308800c2d0040c1020b440d00840b142040c1130006000a058000c81e050380d10002200e10502c40005040c0110f15083c4142c0da04507403150010064115105001c009c00c2c801d01d29500103010002c500c07e0104150741d00048094a040c1c0d1310f00862107004039081d006054141c40d040d4001c84014006001814144100f0b8550382e00f5a6906010502d004180701032ba20304182d0580c0200c1e000c200104a075104d144c0090300350349a4100014581810740d07a01d1807011780180c2120035024041161081000c0d046e0360101044e0b1101400c455441d02c0e40c4000d40d881d200c1d40b1092441c076400c00180310300381300d0945d020f46c40e081c4040d180c2407540304442004980385c0d06074074004020340c0c26281c0800c0160030900e50416280c1d014070802c0d40f0300ca00940780d00220003011030308005158418100d03070040660040740603400220640e0010820444041007590b1450705020b41d80c10040c0120016010740c1c4188124400000c00c0320944e110b20b100c21046 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 498054082 1250 498052832 498052837
    0x170408101407021c03060806190501050315010905130f0b060a080a0c0b0d2003010503070e06090a050903090d060b1008070906140f0301060c14060c07141908 69
    0x9a2a8403803501c00c07010400488081c400d4807800300c43d0b015005035140c01d24020911280e440c1e48900701a03945001040542080004034001c1030a205240c07a51440c031035241064039816046103000f9007000c40c5072104c44072200314050555804504c013150303a41d2444055a60403201e00e00c09005400b11280d1102030140001d0382600a10055071200710780c03903c40800d159a41403851000305400c20300d400401402001d0405020112903c2d24041a480008003001100812f40c0c60343c100380c0340c400401000300307140400007130008000c035421010041c42c200c000a0805100100301c3c002d0141c803000004da42c82c2007441103070380e4044010494032101c226802c09900400d000b880e5940200007003d01c0e00039990052203528410242ca594880d061410321608490f04a8146c41c00441d0758418080a0a11130103403001d140680410303613901820303600b5400c2103240e81740c80e00344c0600d840e0460300c00d01c418070201408544600f50002d00b28114281130341d848078900703151000c5890888412000003010454075100 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 498055332 1250 498054082 498054103
    0x902010e181e070f0c1403070311010608060103030c240e01060608060402090906010c2906030c1002030f280e03060a0c091202120708010b04140c030c0304170408 71
    0x200c01d41c0401e41c000200900150560f01600800c0070110841d010350b100b5490706203090700c02c001031403041d1702182c80309207541c200c03800807008901c452b02810701e444024441d050040c0011002130801e54950780340908001ea14803c090711401e44070700b40440801c20b0144601e2420708281d0104290301d070f14156140205054001c002c00641e0800201d88030b4a024001c4e41c6450000520040158448030b006640350080107008951210404410079405413030030981141e114801d400d40351280c6000d0301011300b00070012000501c9820fa42560409080d0f000040e00c507550005948260f803a1130340700f50f40b00c15031003905c50a0141444070000c0da94055100c03450708409001502100d600d13031522000f11007501c3e104948100002c2841c5000c01548000e2101c003404140080c120b0b04105800807021800e0003c103402101a0380c2d12010381c42c0035070505115040c0f540d0100340c41e051241c03d01c150340345507511020700066240b10000c0045028464444201e00300000f143d6221581c59607203c0c40d40d915103041c001e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 498056582 1250 498055332 498055351
    0x504020a210614010c3f0e2701031416080703060c090803070809060c031204022d04050601171003060b06030705071202070801060e1008070e0a0902010e18 68
    0x8078494015405602c0c1d444000e41d115009102101142c0c80141b1481d0410307044040d0b0a421200200c80d01c1221442080040d030659102e0b2503001d228400c0c131030b64400c08481c01c2100d080600300c40300c43c1821000d03c681502d501200000c0034014000c100742c500849081444a03d6000d0707100000c00d0200021800c0881380f06050030f100440030040140c0303041036244500c1581360020046c4c64000b403410030062200300c000511503070900e42000b900518607002010109410b2100c442880158034284a01c8008540e00724002240704804007203c0700c9602e80445001e000d1038460020039400c0e03000300c0d001d01c081480d075800c0d050b80d071074555014401082c503072209a0300c0342c2c80c00340004454200142100d124102d40c1d00c4032441c004165880c0c0442c83c03005800c2c182180503001d4082142c0e1030070300071000104150340f04a01141850451030304c11541c036610510381170303010f040100141d46003041403950108480c000080c15803428001601c401d103142002c1035000d04403102822040740c00998443c094140399 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 498057832 1250 498056582 498056609
    0x70b0408061503030a0305040309030c0801020307080906070e0d020307030609030503071215181506050a35250804060b04060e0a0917030906190b0603010504020a2106 73
    0x210302d0070745604040c50704560180c01c00c02c13820213450700030340120b41c11510a142400f0490b9507038a9034040c403400c50304010400e94000003480250365001a03a940c100d00000041c004038140154040d000c81154409107004418482c1c1150035580c003404240c0065410040901c1080c480b13143c02445070b40116080004030b03010b03168882640e40d09204042240c982d481d40d0031401424000c9507544c0c4140003143c0131055444000c07100c5c0400032441c0f1040144920345805440c5d00c40581302134409100307040600c806070020129100b142d0700005c0030b20180c160500202c003558454038001089800b00c07002910b0020203507250130154590040985100d140286410001040906c0800040e540306c0d20800c0703102d042d0000800c941c22031652010b061544203410f1040c8d130b5440c5085010454108480300c0045400040c20490040702c0c0070b00303e2503024290001080013155402c006000d40c0418001c49004c0e0340d000c0303501040c1a000e44100d20000b00b0f403e031400c440001c500c01480150405d8005d10b402c81300b41 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 498059082 1250 498057832 498057841
    0xf1e0f060b120402190303020a0b130212070503010b041e05090f01090308010617190213091406120706050304201e03010606030c020a110a0e010e0603061006020a150e070b040806 78
    0x45c0903d45c0c05890f4940e02500002c01c00b0b846072440300070041c040d40d4a80a030340610400607610310907603001031004400030b04001c510f420b04050031503031036034a040d00550034910704100f602103040c0c10800031350080341c000555464081d041441c5c480000602c416640c6000212424190000480d5048824659a4115046815602410101c01503600700064000100c19103d040c066070090156680c8100032800b0303040d070b50360999054617031081c3c41181000d0708905025050400310440c2840c1c0700c152006100845c40c2540c010220310000300050002d880c55980062980e0411100c40051400140301043e0008441c540000c80d90941110740e101c0c0d8a01035000807490300900454541c00c6041e005841e2403107080d201d0401410580c1c850315484000424007203030b2042c0400d00d0a000c0d05610b0b0411020703140c4203052514105001d05281c4454003040340402185a0001d07514081d03130350041341804c3c5401c60701d0581000c1c217088080706845000da00701c0411018040400b0384115490141150469140c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 498060332 1250 498059082 498059119
    0x8011b050a051615020d02040f120807240516030b1903110a150f030e0c1e0f101206090e06010303050a0207080d0306090f1e0f060b120402 61
    0x60040350710301050040c44a070125600680110103401c1c02079014590034640030b6111001c03a80080c070959007084c1d0100e000d1001d0108202844044c0200703040440f2405001d41f101d0040340203940e00203015890212024180b0828801221101861400180104e0030a01c044c41d0301484000113101c0024070340170344503405161044200280700c401c4040f00c84003070f0964841120703808156004580001405000040c0303250156203d048848041c1d5035003032200c2c15848010180c6031000454112603000048940b0b0640d80d07070b4000c0c40209110340c1c01214980f400750200d00c9040c0c0c000c107a42d44c022040c1034200525034020001f0300d99404205070400c005038031000124100c9409d030b141002c6a511800041c00028010b00081c510241640110744486da0381c0c0806501d4a0950240000001c2d290f00c002c02280c03216000e0341c03442c0358510f5000d111034030074100c01861030305400c1c00d80c007040303502d0b840c441c04003040c20390000000d0030404882e0b0b0342e24441e13032050304040c4400703035000c85c0502c103131450b90318441c03c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 498061582 1250 498060332 498060337
    0xa030305040b060901050f210a0b04020a0902070308010909021201090c09150e04020108060d06110d141302100e09131704080d0c1109071206231e090108011b05 70
    0x204014160804107640c60144a20850f8004042906002031079401d23588180410002d1300a41c8203030102149807074588184201c0e050346601811600307006210450009402c01340c3c8d9030651b810940c0016030b0b10b0440c00068181c0c48121b130280c0055280258072030511400010403400e841c00c1440601c03a600f075091003510101064444d4220449808000c2001588540c00041e0046c030010140321020403183c54060440314070f030740303d001049000280004503030003a000e00441c4c543c0000c000c92141c5003042102c0441c100c8000000d101d404241c2c106403c00b805092030740649400580014581d24128035070b98810142100181c1d40718910156030f180b0302d42040c1c2241c060722a070714080e00c00450b5400040c2e0743d021140504641400548000090741e8958103082845007221342d81d541484040032070400b04644540e0000e0401250807001c244211480d210a00301090050303410000c1b003100d01e6440e60241c542c504056a01c0032a030400000c150505420107015003907988040060031400000c1501d052 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 498062832 1250 498061582 498061589
    0x70b0105091f090c090509010e04060510060f080601050c070b03010f14060a03110d0c020303040605060306070507022205270a02011b060b210609030a08011809050a030305040b060901 80
    0x30b0305000b40c24000c0440e02e4002001c84038081c00d120b01129280c0c80040d54051098000303007550340c40b81c0100014400710f0f015060b0040f58004000303021500b0142d008094104404541d0240002c44021881c607900c60001c451030b40302003c00362803074261102103c0d00c0ea0781c028414103101d00c02401c4003041c240c0340f560140c0218032008101070702d06480b04030141d0250210141d4a088401c2c20b000040d8000c1460184078952082a0f02031036403454035161010445030050032150180c0c3c00303942000580743e08602201d00b032503012929000d43e204500b40d15110024504400a40c842c20401072041b8200a003504512000008002030a421100075050380d0700d51008101a00080c1d58040180108203804a41042d4034042c5c1e4010450945500c00b1a04c0e100c0004250242010f501c078464400040a015640d000000c1001031071900d060040d000b0031264060180525142d0102d2501e001f500007030380a060807d07030020030780d14126400e00f400380080c8001ca50559180d10030310001115450302c0f00da200c3c142c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 498064082 1250 498062832 498062881
    0xa06061e05060c0319110109231c030e0106051503011d071e030912121406030a030e031c05070b15010903170f0c07080d080705040911040b070b010509 66
    0x82102c0345e05041501801154030105020a00398007024180d000c3c0205044903004144040c099442c60300c144d50201e00030882d19075190041c907000d15030100141344601e80c3d1812440c0101c2c440e0901d0310039038010300055028a900c060141030321601c0b4131000001d1030480c4d110700c00a45418040c18620468407800f2251480068000d490b08c1c894903030001042d6000c0c91484c03900203400740321039485000540c4590505004a40300c600b5000c050b1215000f220110418140c01c0403084c100207001c00c0d624036003e40c004081c0a204c0f218118940c41c2008428840c0c070340c02c880718540b40702240e006880c42e48800d50980b8964403c0300010785080d0030040824580d041030351020b158620310740b62040382d0502c80c52130030100041000640ca9003041326000d030004252304805171121500d040001b0b49024010200e0205010280003003000c40ca0b040026034089844030b44001c0b921040000c04602244a81d03000341d0044d4102088141c14071440003400e50590f10140d813120304035224400368419842e03811040018 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 498065332 1250 498064082 498064087
    0x51c11060408060606030a020c0d02011a0a080a0b0a020f0301030602120711190302070b0c011b0e09040b27010b0906030c03101a04020c39010807020a06061e05060c03 73
    0x1030381080001981e002c7c0c60f80d10b006043c0843c2017641c5062120910000006079101c20024030004286a600c00b8080401c42c3c10300751451911911985030401c881029100c401c00d4800a515004240c048502840340c038800f00d41d49603100d00e0403800030b400080c2007004405902002809e854064102240081c0040b0000d010311459254560b2411040404c00c030218003c2d0000011079a070030760b01910741000340c08000b24030500640d4160540e0f1040407403003001c00109806c0e0080384e80301c0c940072740c1d00306070803043d8140380d503481d02c00701013071003006242030965500c0040140b80c8814041d0701408500f541251803981e80c0e22480708040c0d488880440b0180d0581103a100c014000c0d4640c2e00881c51031070459a44041e404201d000907007240c0113075040711800c0d00540144d41b912100710465416050400346024002c0c5042c170700311304012000c003031100e050104170b0700804c8250b8000c01c19040400c0d403101c014400345445110034500014425060707615581003402c04522890014141d51206121600650 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 498066582 1250 498065332 498065341
    0x303180b030f2202030d0504061101020301120f03030e070b0d0c080402010e01050d090209010306020403050f0106030c06030b0d2103200d0507050c0d0e10020307021810051c1106040806 81
    0x41e98038240c000c0c482c070540006075101c0f0060b2402d200e001c0104e030003511965100c61400d400500034000d4902d1088559204100500901182008540f026900034140f651130150780c0c502a0010020016500100c1c41408000691070500000070700c0c40003040e07081031060310b200c0081581d4200c01920000d000c246c1c0308205202c2540305070003a1100b070900c2d070008201901a5004203010b01400c1c3c0007999101d80000b0280203000c0f007045031a010b218108020000c451942e2a1840d042106001c0e98007015142d111020030f07559250115441c0c150000000002210326910000060100e60000004641061b01c55000c2c020f001118280e542803115200b80382c44441d4a4000003888028400c0c81804000c1c441d40120038000c101035604041182c8502c80f010001c401003004500c1c004081c8411903100300170078001a103c4109146292210322180403580c4c036040000042600c0c07a4001d10380203040303298043c104140c0d169610001c940200c8a07a140c041034001440054421030080141c0c55000b40c0104 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 498067832 1250 498066582 498066601
    0x20f0118061421040c051c0b04080405061603030c09211403030c0a080c2b020c0a0503071e350d0c08060102210d090c0303180b030f 58
    0x19008040d4860b04586040444a40034000c41400341d0704481076110541008204003042100f40c000e00806c486003000d0603801441c2c07150f0b81c1e02c0813030014804020364000c1810401c100090b58042c0100811058840440a0701581e0540c541001a03000ac0c0c02c0c032002d00c00160080754060b00342c0d0903500f210030740b101c00d072604090400c07030345c000c05c80f20546207494008040e00148082d6024484500300b03141d90303c44000005000c83c00c054134030f4807816001c102101c1c25025913100360700800c1800140401080e03103c6a420700031700500002c034100340180d088810400901200030305005100329440e410401c1d0440e9240b0100e28411001044091407000c40405c820a04404103102404d102c1c00d2a40e49049901c0340085802c00340000c41d03403079118058034600176086812941d011a00b072004010120b910158a18959250422550040400102048212003035044078449075008003003d0b945554a02d8003c01c1050002901c0582c02c0ba00f1001003140c0f041c4400701d90086003d0580b2110a0312900b024 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 498069082 1250 498067832 498067847
    0xb011502060f09071406071205031506090907030e071a04172404062403150504020303031f03060204032102010207050601030b061f0203190801030228081504020f011806 74
    0x1c42c0e4401424000d4400140d800700d00d0443c0c08d4200d985064903401c009280180400c3c3e0741054074410031082c80f260119480d0149010303884541d40c076001c0381c0c49070380c48000e60414095401c9081c221020540040304413100b50001c0044500000d41d80c1d0002101382030094544002502414100200054000c02110301c0e1202d180c2180c0a18000507030780c0e5403045d02048810f41c0c5003054180c0380900d4410800d124040c0c024858010080c0400d1080b49016400a51640701c02400b500e0950480c2e0a0015142e42c2e4074400409946c0c445021991940c49082c602c020258003008a80107401c010215001c20341306000f511440d40e801801400d040c0d0039541d0b04860118024032036504200400060b120001111000802c0e17580d090b005159102401030213950707a00340c2c0300e1062041c050304400401c01600d0b03480440f4000b02d1003a10b06030402c0d012100d851142412640448161300c1a0000c030a00d0709030803021280540d00c00c5071005e501420a00042d0764521000a803194480d226050820006024400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 498070332 1250 498069082 498069119
    0x5060409091a1005040501050603040308010b030c04121b08120703050d020c1b09070e15090118061d09010e07030c09170307110303040b07060b0604030b011502060f0907 74
    0x70304250741c403034501c9058440483c2c407000d20450700306042000741080e201703180c0034010a440c11807440c0341030785028081c0e42d41031242020300400000051941008a400d03900030701035008040c550700c00241480843c1050341206520145940100010040300021341c0440d00c2c14550300f286c0c10020161000d64840d0080c100c43d4174401e03020098900c1c0d800c0c082c000c5800d40251120030702c44448001040c402050320050140e810301156041d0340c03800d5900c00d5032425a82c40100545c40d40d030381c0c48000407502401c0b0003402000d0301100e00c401003000390301f1184c404c60000c102d0082401c403050b164200a05c08000b8458840800c940e02c000c151494440c1c0c0000030040d4950030415511a55903030064041c02c11010030261a810200b031a00c104000b800c00320b140c1c040220011130402d800c00b02d5018081c42850001880c866803a4862015900e881c1c003920002c540200c410700141d0ba6409002d02d103603610911000060082400113050f905072002c800c0c0c00307000040003c03c03c20b428001502100b20310102c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 498071582 1250 498070332 498070343
    0x60c03090807050d0906032c0a02060318010513030c0209040f20010306050d020f0d0f0c060f020f01092a09050a0b310207080c0109080a02160506040909 67
    0x514080200d44070a0041940c00c1c480d9000780f000403040702006120fa1501e80096003014205503019020007010040f945481800c03034001203200c0400091070749010034040b0000e401003004410059902c00c3c2c4e952138001040c1a40090085507100500d50604052240000700468000c4200324054141226640e600c580705485804950a40b034680703014010005441501c54414100c2e0703130700340e541d00d401034100415080c0e0300d00a00c42c600f0385c00100309a0b071303011206001d1881150250b05020382201000c00c013039008540c40b54615110000108001002403402d0058800c4482000904d4014880c00c1c090325002040d500340c03400409954000417030603420100007407500c90408240f8007180d22420380511003c2c0000110034040009200203801c003400c5035503900c12016101610074000e03886040040e501035030016580c0c0d406d450701400c80d004054644242c0d43c80c10140508001e40c1c2c5000344803d01c09902243d09801518440d07e0150603c2d0180c1600001c0901041100e03171003d8100406491081 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 498072832 1250 498071582 498071591
    0x617040809030604050c04150f1a190806091503100c02030d0f0c08010f0e0112020103090f0501061a040617130b070909150501020604120e0a0303200a050a060c03 71
    0x7000a40780c0042613a060340c1c1900014065061032606102d0380050030029442c05060320329000070640403caa502c01e60000941a4540e100c1113a40b4408462a6842d500392101181282038001000038508071181400740c0c0d1540e021809450129603110a0014010001e150f28042c0c001c4043c041d090074001030066201c01e010300180090b40b4040c2d606079000760340d000900144005002421702806034052041007c8010050040c0451411074905691780704144440501241c80100c00604a2840150070058429142000c101c0190410000c40303002c14a400490041e0025030b902511651003070a001c07a14040c02030500401000d0344a5204440200b0112908419214103401000c21035000000032020641805098100c7c0307d000088a01201950400b80c20000080e640301c602600c09070105100c04592032442c0d110b003660490b00c0a015240c2d010207a660f2130003920365100c000c0401080d500d10b061071101c03103200040107551a03400400500d9810030390b464200081c0315600c111010513071503 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 498074082 1250 498072832 498072847
    0xf07020420040305010906141618030209040516360f0921020102090a06050705010f06060507051e1504082b1404020f011d0307080309120706170408 65
    0x4140c082c0009600400011441004a1416001b00c1e00319022407a441d219520600c4203a8a0010601707008509030b0405c0c1c03298200909016000d00c2069100a602640c900100810031201054910714a1134420000d55050f0300c41d4280d44107905e007151100701c44d101441074000448801e10003400580080300300080c3c0d4036200300225060340c4904405682040c2030145540f009601c541007041003500510086092244c484002041508c4a01c100010404013290890500c00290b0001e580700c00510010041680c5c1d03071801400b00d8018a5007610180607185a00322485041071100000f00220405840d4281003422600ba540320003603c181d811410078810503040b41d14a4100100c03211340500c4c000d14070700d6800c1113407080da108289940390040c004020701005840c0d07541c19640c01e0f282403c0040881d112540350440103862040d1060b410320030303000c00042001010006000441041e9155106c2c0030a051016a4070500c41c407412001030050240405803158040c1001d8010b07204044a9103130040c0c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 498075332 1250 498074082 498074141
    0x100e220e01020a02060f0c0c0705090c0c0f0609071a04090c02070b0408031c02070b07050a0201140c0901090f080304090c140307030f06090603030206190605060a020105070e060f070204 81
    0x40707103c0000f503803296040c400d0b1824040c2c00703294020f0041c1d20706440c003090401d445854070440e11446020b07000c03070b102051503181c0b50000c0d1042c0303d103804100d95101c0804429559103040a80300e001841c043e810340810b02e070514000c0905400301c00002c0e107241a02d8841005e0052016000e0f543c218040c01201007110f50740030000b0002084002c1c01141c8502d04041c03070000c6051070211020580c5e2040000c0e1002901d60f10303009601c0440d505015849040e03070f400a07409802e0390030f000346803507003900100501c0b50003e102070b00c0300e203070207980c1d1346d0303044d5101c030307845403014406000341034041e4030a22042040d0300c21a00b0403010038032345240c80c990895885004d40500d8000b40c400d140820340b1480300c80702899042c41884000c0c000300d0800e020207841c5850103503c0e080d0181420780d0340680358030100382c45409508044010705001d80b00d0b541e207401010700207009001c19194100000c01c152040003035440c0c00700a80c0da82e015550324031850700c0c82540c00c20000b042c0c071401d607a8150300b140c1c03921044030f00e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 498076582 1250 498075332 498075337
    0x9120414012102030105100327020a120303021c0203090a080306030304260d0e0d03050d090c06021506010801140909120a02010204030c0e040308040818060711100e220e0102 76
    0xb03003004003603102e505000400c00e55060014209040603d0310790003001c0000001401d802d01004d22400070a08012030010490614250300010300d0215103405103001c055059006120b10701c54020509250390124441c80168403090381d0600566200c00310380000b0654440c0110b070404001012640740c255240e8103918550000340c108422900044060300e0a40c40038880025120690720b000b0600750310303d40c0090000130403040042c0800c400480c0e18200d481d07035580004400394010000003040c5070b941d80025610503000c017801c2005001c0310b021901c01d50003484a5416180503002ca0070200d01540203100a940e00101501b88501c030300815042e08420503030041c8001e002960002da83d45007517040248260065070312007400d5194400410021a901c814016000380d40328800c10355490500c05080c2c1110310024003143d00c41000520501000860511700f5004107060b116043e8048082070251a0304480c0005541c00804195105192440c4140301680b50020280000744140445000c0e6003241c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 498077832 1250 498076582 498076637
    0x2215080901090f0c06020c01020f030d02070c030b0a0903180501080406020703021c08270303010308160b0a090209070507050c04050916091505030313230607060b01080912041401 78
    0x607a400a03062082c1981070007d0509100203000038612982c0749011996280726211007080030540c0030403210200300c03102806400460700000e50545605001000e000140b15560084002c264104080000342000344940812180140c5509405980300c2d203070130010390312401084085008013410020494401004049100c50704e0f940e120706864400080c1021126002040b205001401840500d400000080b0b0303040d03a60200d8140d480c1d03000701c950038010048848005121041a00c104207185507035500020712a40210f8868006440c0c1900c01d4441d8402c005c005004c940180d10500814241500090703084400301003100d0b4070400c02c140e22400140642c002542c650380321002c0f4001803400c1110280a490101e01451400041d0f420740080c108051003400142204220750403481c00d441d0a510001c00c1c8050206070780c8804c61b1500000070411103481e140407461038408108031002c0010100a09194040441d1901d03041644803506000c071580c256041210f40c13018200c0c0200c04a14801d0345 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 498079082 1250 498077832 498077843
    0xd050a0c060f020a0b0103080c2a030d050333060a03020d0c020d020d1d0a260d2304090908030106030506031219091a2215080901090f 59
    0x250303410200020645055290040215405a403041010401d0408a141181c3e8070142c405d58503544d031b84203181401e00410009020500024245100700c0c1001d00d082264102141070341c0c0f44618903107054600d07000545254030303c083c1001910f50001d065440025991440554004100c540c6800166156000b00003010010b40c0201c0c0c64107040141d4020550b5142650000e440380b21150603000359180310f080948002c1050b44a4100085202008590048000900400400c0f5103c00d880d001d071081ca000b40d2402210a99030380414804c0225564030b410340c165642d071000700c1030341d46565021040c440c03005440c1481004000703145003044c880c00d0107503445140300710f849624011015007111002444140260020750b20403480c440500708a60003030091200e200040d01101c0c1080b1540045500304221020304520f031729a02e6030241c0064104200381a00160000c14928400203c4290386c1c4140107050000041c5095203601402490f81d00400220001880303000689540c08680c0601205459 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 498080332 1250 498079082 498079103
    0x1112030726010b0a0c14010c0905030609010c020304050103110d0c0905090a05010303050a030f15080f07060e180c0f07080301050112050f0105040c0e04020f120105010c030906030b0d050a 82
    0x800c590704070041c1a840e0340030300d2030500da6140c8030b0b074000d01c3c1c0724090000040220300402d030381c104020301d411011103401280c020008103d1880010781825001d009462081c4a0900001c400181c14090746020550a502544c1080d10740801580502000206440358030b0061000b801441d2140c4520118440299201c0d414a450042400803130140a841043c51500307210060000c207410000311120b01d0342c280390020740020780300020b07401000544c207603038401125104005924a03001818100102500701039420442c1d0301d010071341e0580c030134a02c0f8036004056070380c5e6180416000400c1c254042c0030719010611b483c9208441c003240703038090300703045529890100c0188403d50b801100001c03440b400540c00c00c41420b020404290004051040910071a03c03043c0c88000d00f40300e02070050210001510a64807031030120742006032600000b0b0000300001036600002103541c803a91042030565016260580258100070040b400741982c8040e070703030b0481d0525100c800003510400c00325030103501880d407403035 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 498081582 1250 498080332 498080357
    0x102040e0901090c1d011206060314060916050a0512010605060409140a0b3f10050606130315060b0a0c050601050a08120304020f090f100e1611120307 66
    0x900f000134a03000f1410000400380361841715800301c9442d605443e0314250418180c4480d19007103010700b4035500014031084152030220400c1c080061100d003d1034001e0141d855500142d115079141007918420305074042c21a040c2001981001782c030f0005204912000030174025180c070040f4a0982c03080e0301005006035101480c3c86034a010790740e0300d43c0003c0c3d108018820300c800c2200040c80c1c50121740404a8102000c20001c051034507455080c28101b81081210141d100c1044186071101c0060407504030407820b1074000ba0390b42c6807a074102d030440311888092401d04c1d070440e1903042041d5210041c03524200c0c0e4443c0302007a46001b0402400000182d5030b90781001516a00e031890800750183c0c0500e0140500010611040e40081440451800d2040082c2e45a543d01d0000801408506007080c2d0804001c4c8240310f98906202e0b1094802c41210105082569a85042c00040101150307940343d4412104140e4000600c1a16074200688400e82113031b00107807600e410620298010780301040480c25040c0e00302e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 498082832 1250 498081582 498081593
    0xc050309060a060e011806150e090112020306160212030406020703320708040f0807050a06020d1b03120c080712020405150a090905010306060501030b10090b0c0102040e090109 77
    0x190302c91030070542440001d01e400049901d0603010b00681c0c0318a01d80940513240006640e22030401040d5850341145035841c805006800552100051401603011100100c0d000002c401c00052580d4080c0092609039286030402e0b01d191005410f040450045c40b000303505084401000c2c6028a006000c016502e500e07a14000d07040741090702145610300221083c0081268a0040d100b00302e103034407000e541d034440051801c01c18034805ea41010300c50204012010890150020b4044295402602c6448071036860b400280d0ba42d124440048001603101901c142e0700301d160b0f00138a0304281c03182c2844c5140c0c20300002c4800984498003105e100245009040040c0e031303540145112024429007000714a041d00300070100d80b400300810f00d0f2813859140016a0548103101d4003003d402060501d10410240d40c40e46820006070210707214050001e41022015115843c00c041001800da015841d510941890302003d9500794100c4104e1019a5500340310028103181c4551440b0311420111000040b0880b162624 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 498084082 1250 498082832 498082843
    0x7030b04051f06030f020c01060305072c041b031a07260c09010504030c06091a0408191110030615050c03030a2406051b0d02030702040914010c050309 66
    0x8540c490150180b14070301d0b51101c1c1e4603000781c0c0c405107004a024800d07000054003a2107007810302015036180220000c01c3c40b2010940c4000d8401d4030210a1621622030040300006003800480c81e00d045101000c6400601070040001d103071101c04014040e00360ba00e44881f02d4120008182803c0f0403036400030014000c1e884451540d002d6586a5026040140d00488844459000300007024005001508645a038007840541d4000d540c01541114203a44031040101a01d001d40b090204d014500303a0b01d802c0000710301094609481249000f0721701c0e81c04580100d98035410f42d4600341e9200e07010305200355458452014403010203550b520046402d81c50542c901400c00e9240040c9001c100701408208503072400801105d8103c4500e0300d0104d44000c0b511580e0085066a42c00c41d0616100c5a00004110382c120015000400f513403450140f80410020303000380c40d030502c48008001600304002e461300500d0a6841030400034003510f80728030180035070788000342121a0003882801184002c4200208110f04008 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 498085332 1250 498084082 498084091
    0xa0f0f0f090210050a14090307030203071206051003080d0507120218090105121c05130f05190f09020703031e2901231c05060f0306041a06120607030b0405 68
    0x10500d00d40035401500500013440c0000c1030415060007d0100400c1d903041009030042c54008083d11341741e507907034a403502c151205464101c1e1b680b030820001030103100301d0b00d041404036604080106c1c5000100100310008040003401507040c4014420034001240720fa2000d40074884c040b180e402003610700241004a1660140c0c4000c0c032840da00d00580801902c003060362a1031002414610304941030140c0e05680c1d07402003124281c048a607078940010885170030b42e4000115070055544189554101186070b9000e08580a804022803000c1c0f02040032804582c0104080c502030b01c0c001a4034209141c1040f8050101500000c0c00ca403210004000682c00410303006a142e00c2c0e00f822060415040006488180401810020383c440300c26100c0c0c10001d91030464650030b202e6918070b00200342a0040000074007082d00d15500400402f000d00d001418001200c901558011350b40b02c2d04003d070841c1e0001048402401160828000c42044030403681c00c00480d4000d4140c1e40300451003003001c50520003111030050 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 498086582 1250 498085332 498085337
    0x103110d050c040f08060c0724050a0b150c210d061d18060103111305090f060c040b160201210f0f02071505070e030d021c080f0a0f0f0f090210 63
    0xd052001c000105c504480552740e00c000f04142d0488100303400c050b600c1c0c4400303108030b00034148005c0144c40c08075580030100380141203910a580500100000c20b050081c48250000c80d400101d0030030202074900c000d2202c10032000182031070040c518508030141ca0035948403c0c3d41c0c102e071707102c0d928001490110040c0d0000d01d1501180c5001e00460240c1d80d82c0c10107220150407400d8014045219803503020250030200340456061056003001911503580c1e541a1403006a240114000f1030650040102120100d40c0c00042c01030800e10880c200301003810040e64100d040c003110f01420302500c8003029880c00f071104000170000c0c1c11481d40d402101501d401f130202c030f80301a2040001000061004074940e03001454010f0025040c0e0b5296002c3c2c80c4001401101a814070503c04c04951036540010105402c41c416010912081411101940d00c6882540c6040d840c18030600002c14028066001d01070100c420b02e00031030060419101001125110180389030040d032102945801e5080100c809a40e240c01403 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 498087832 1250 498086582 498086593
    0x1030b06010e100c032607140c0a142104060207050a05060d0c0e060d020c10020a0804020105130306060e0601020114040b060f0607080f0a08070309110103110d050c040f08 75
    0x540001c20f844844422030050010f0700f2190b1084c0b611400030080c651740000340c0014000d60080e40001042400c8860030300046216001031786070104103040c4e0f143c2c5045400100490400c0303640b9a855246070310170038503c80c071580d10b801001000240001071101c3e0ba00c03071000d17621402d10340020304002094001c0d5005440408040140e07172201001c46044240100d000210650320102c03c4170040203039405c40740d208401040c0302c0450a003543c0202a0910840106ca41c4641505c01c1c00050740115003444020804050002d03015500500040c154100103411603030040381c4966812003210701d907070800c46490351141b0401107a56024815a01c80b008040071803407076450103654003214104004d100c540103100c1100813180325200c46003a0782060b030b03102480c6601c07080d05003203800c0c403a0000c001b800c00203442100855040b60085c8134081d0701c203401c0a11510241e04690055019100480300201940d03000c001038112044940f00d9035000b0101d5450300c80d50ba62424008100441098221801c1d68021 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 498089082 1250 498087832 498087857
    0x703020d06050a09020a08280206030610021203010e041203051005040b0d021507111206040215070609050703050d02070608190204030b010e0618090309010305150607030801030b0601 80
    0xea0400d080559441070000c2550754a8886950181c0350800000390080386080001c95043c0e00400c0c001000c908a14400d03000010494540c40c50500d0707100060340143c01000819064201040001052007107401101c1d40581c000040080d00d6109034855400400794805001c2009016a003201c0a16030500d003c2c0014101040c81402d100c10701c3c400c10748500e50318980114182c40d40c00719810055001001d94007008180e04a022141d171144004075040100c001d94080c99260850b6828506840301008210541e80c1d68280403103d940070780781401d003400500c01c2400143c418003a00a030184600c0240481d40d1440c50300d039181ca4036213080a42507411040d418010706900449043d4441c4100d880e4500e003540090b000402481550070240100d00c10400120300000399045407070260f48280c51100c0300d00c1888040c8a030b0818160b0740e480180c2c00403c60310030507601c01e420035500300190440081c50b040107040020b81980c401541203011442c0007004105000740c10180c1c50f0300c50001c4c24840c42501e00d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 498090332 1250 498089082 498089089
    0x70302130506040605061c0b12010c0206012408130201090e0a140705090f0108040204060305120c301305040e0a020f04110f0703030605040612020f0409020913060b1e030f070302 78
    0x103c1510903d09554402015032300d41d540a1039011110180002002640c0b03d4040007502c518090140c1401400015800c009400d005502c2514212056607582c0310340d114010510400350707401d48140e04100e610f1501086850030b006030b02d402221025000290348044001490440304014944014481c0a102d000456159101c1021039410709280a004aa8446c80010024a16a00060094071030000001451402c0d04002c0080d0f4511070101c800503e100d15103c401c10021400d0003e82d1030414941c0c0b85c00e25515400f4103e450558041e9030310b40791311000454201c0d491a00017202d41c0d4000c2180c0001e50511100f4004410002d80c1c0c00e0010182e4005102d18500c20200b014424110000c0c43d0400d25110f036000030083c000c01001406195640c0141d44036240c11040c0c10380c40703144e1019500010b0300d040e216502c0c45550151541d803041e81c400004045403100d0070000d592082d00c40301d4958841c5e940c4907180c00c000410708424002503404005240c54514076a086000592103103400303002595 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 498091582 1250 498090332 498090367
    0xc0d0e191e02100c170a03092604060806040b030a0303052205060402060304030c1b0e0f0f0103060f0e10060f21020409020f100f27030b040507030213050604060506 72
    0xc0d410000e51034640341c0b821030707408005909070300303c5c20802207086000e00d0340c5030b00030028841c0603807045902408100b511144054013400704600d0b40400300810400c280c00b980d40d0580c00840140002801020880440e0810034504403c4000903a58410840711070700700501110500a20b000d00e44a40920380e840541e5944040c0020344940d10104c006401c0510990410700c40d541e000b240416a0050000d0203810350100740200e48014480000084c50380d294049002d21456040d0105201a4a542c48800080c40301282c0c072071401e038946401d010501010000000480901c042c00101c81703203410401e64001d2415000040641240e54609002d644195240442d80341c0407200010980d6a070310000e161202003161113504400d00302d442c4640c868100c108241c01032126114007204607030b120001c60400c100c2220002e1600004503041c00440da815003465445445102100c1c081601d9400141500c401c00400106550f210700c1080a40c0c00e15001f000000e00781910585c3c18000b1100c0942240ca = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 498092832 1250 498091582 498091609
    0x61a09310c1e080d020714091e100f0b0403110a03022809050a02030a06051f11030c120c0c01021f020306040603021e03011103060303030c0d0e191e02 66
    0x4803108541091521122502003006101882c2200c90203013003980003a488102c507104030580f0440e00300030500c450500e034000511a07505422081041d90f181c41c0b242c810b00d0070151640080c0d101561002c240211042c1c0b08901408081c16526150303880c500e81b20060f135005031070140c0180e105040030401a01c0e220303086150b0310301c101803070aa0301f40d00b8249511244107a030300840c42d080c02d010511441801380d600030b50084c0002c000c140003840c2c503030041c00820419050b440b01c10b20401c0003150740162184000c40300c0c140200040c0c03031030568284261407402c061162108900080090f20f550b0201040294401d52003081c000b40009903414210541800380c60200c06060702d800000082d2150340d0f0341d118202460780104110050000c1d10141907501080c00c401600179860701c0800110b00b2248019213201c4d00303005000310710396a00c03681c0c036444941107007488407040f036103c2c9000a22003006000c1c43c0000c103244d03406144072407154140441c2d5000000c11460f008400f8010020250f158051203680d070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 498094082 1250 498092832 498092849
    0xf051c12021e0f0f012d09150b011d061918030b0601091d011403010212010b0904060509010e0c0901020a080301060807080c0703020705061602040515010e011b061a09310c 75
    0x100c20000c120340e0090030903030300002c00b900c00800210b223500c5201e0f80310101810003070782c5540980350200701d444040c0c1c915141c490341c411000e2009002c0005800c2043c42d40d40541d191482d00580700000040854100c0d4008803840e5000c07000704003a41d680042c0e59801450b008140c040881c4c00540d61405048040c0103100ca0120044804000c503202501250600c5c01585107209175582d42d450165140d82010010b41d116904110740080e8903d00204d80a040c0e60722401b0310040e43c0c441e08407015040e80040c170242c0c15400742010301804240e10b18081d5001306103940700c1d0640c91400440007000908010300502c4c09050a11545c800310f036001500005031102500c4803541d40e030036185842600c1920840c003d52140c00c045c00c000000c01d1301c1e120180004005c1e00c0350880c0d0122640195080112000d820b41c0c40700c031050079000466565084001d031a104604401085203982000c00c2054508035180b1010360710300845040701210784030317104a100d40050508030490019030b40780300450149100c0d0282 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 498095332 1250 498094082 498094151
    0x11a0102070e040308180d09051e0102060604020d1104060f03063312110c0d081902031509040303090b090706120e1014010f051c12021e0f0f01 63
    0xc00d50150f4606c00a158000801ca44440072103c03801031461079940541030090f88450000c0c0300c250401c0c00c6030340c1003102c140c01801c50355903000203000094000410007092951550201d4200c984035600403c0030304a00e030307260122203024080103416510107900950030324010310f120010360074012801402c14402c0c56083c81c03460220b04000c452151403c05c119103054a405103143d1089040b00c010100ba122000648810344a410000d84082c041210083d4100c040301507401c0c80001701b54000c40d484aa244242c100504191020901c1c080c0b01301c4085000c6992408100180b01111124a85c004620320040c180c20381072400040c0307483c401d044c0e00c441041e00c5c0c07446a401c12101b8000c5400384503405008228245902030840c0c100b010030300c00c2d9000162040c10115040c24286803800201ca0a4031070140d11026903914010785180b405800310840c09001c0a07002d0840701d0055001c0c42100002c014400211000b03400c0b800c1100b51099001d990385481d41c0a00d07040404107401185609000032007a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 498096582 1250 498095332 498095341
    0x9020306012706110c061603090b0a090519260a0218010f08070b0a0e0102031b0607030f0506090610090e0a060f14090f1905010305011a0102070e040308 67
    0x7107609900c01d2102810001207005240740310304840e082000c50b16141d84d6091510020700d401a00d601c1e8040e1003e8000302c08100c4c140e0803048520314204042e100b0300e000d540c115601d040d50801c42c0c00c800b80660014004001c2003000c3d00d40303c0046880072001902e91b610091418000046035401350856510101000c00c0c489041101400040d104940103010224020424001594910303024083e4501c220940750001c140340360300003031210a599003040050714090b8440c0f070503109030386605c0c0000d0441c8010020720035a0580d00c810b40480e038150390700401140c184054081d055550744000c49004c1e510b000300300300696944c1c01d12070390407075401d8681d580c1c00032030305400701e5603c90317160040c0c86500c03000342c240000385109a1040782220700c07425000620b51740319800c268000903040078950f40300c200000440c86044085061580003202c458003000410b071780f01045400d480090b4015901a59258440e043c0070310300c600c3c400c2c60041c00b440545a010708094400700030220260001c1c042054900016 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 498097832 1250 498096582 498096587
    0x140f0c06060414160e0627030d09060207051e0409030314070f05071214130e01060c02030a230706090806010b070b01120203011d010b011e02151f0308070c0806100902030601 76
    0x200d0f14441070080c1c7c102c82c0c83c9212003900a84016900d164000d1044040794a042d9124401c0c01007620001d6018041ca0b500d020100030254903c111103110f41040140c219074299524405d000b40c0d02d04c243c40100d000d00c00400e010090351801840b22052081148c96401d010754080d0480d00007541c8400043d041e01e00740c0e0011a60030107192032a072900311700016109106a02200c840044035001511240580c1e05c482c0c00b01c0340003c0c4205c00030f4150780210201d10018070080001c0d02d1a0700d445610364a156910b42c189854040d290340200c01003a0051401c1c80701078403c1c840070340581401c009007454001266507602c44104144541480441086185021503500707401400401040e000c584107004d1080e40510300800d17804400714003041b1a0f0382810340c0090190840042000c1c2900905140040b1b010031120441c030041481313031401208a00c0702e0700300240380d0082c405113005810b207a132600c070b041c0740514801c0402d0700500700c2980f041041091549012440301c007030b9140c40e840075071a41c070b451005 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 498099082 1250 498097832 498097837
    0xa1209081011160f05060105040b0105120a0b0613260a1707062316120b0a05030706020c03120705060103060903120606020d1202030f010501140f0c06060414160e06 72
    0x943c14074070452088001441151958000e042e4000c1050311003503642c03034040000320703400660002d0200b0800c4c01004007806411402030f034401c200c07400c00b06400c2c10b43c000080b22a808a00388844052071036800b030201115000711800d02505041c900b88040b1004c081d4140d540311a500c00424038440d9035406e0100501c208180c40420740c6c0498140701021504003d02d5921000740d00c114600e085c50400a500740300f0030745030103209404986605e0400c404030080d0700301400f18a8426a00039519140c0094540c404000c1030004181c2640a05403d4011108140c180040342c00000c0790340105110000108501282850450780d02a900080b650320074981590465800d81c1d19100043c50618005003203a000728841505003500c2e9170f05070701107101070111000c03408152603003140c0d078400000500940d405881100f410305802c19100c0d0500110310074080b0203900c0103034400340c01e401c07800500406047c94003e0400b070b5000304a130f503d19454460100340040c800741c00074a0400540b40308204076500c62108 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 498100332 1250 498099082 498099097
    0xc010f0e24040b07021513020f0907090302240d05090106050a270b060a120b041802150c06090d08010611060a091407080304031106030f07030b040f09050a1209081011 73
    0x3441410f511f0401e04240c401100c0990580c024088001440c10f50b1070501e490b1032088540d900c95003142030440d024064600c065001c030300c030251310014400d0000424900540701600c0300ca200420b43d441c1043c405801c0d503601c0e5112a0044091207400e00010282d20700240181035000000b010030303100c0001040191903020f00054102100141002d442580461618500d1402960038084450031100380011035406101c04007903150900c44000c01480e010324000302c040e590100707481c02c04021102c224100303641035480c59680e60145000d84200c3e60410702c014014012401c101e1034101c03080a101c1d44414004040d605540d07070302c503150350402648803407140041c500310088903085030700c81518554a5106000a44070a4806100300310f803490508100c038821035040481240c651104001074000d4144001025409a190350107000341d07203482c0c811500514014001016060010f05140c070040024061813000c00546040500c000fa400044141e1003136103581000a005c200b850140b00540110326 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 498101582 1250 498100332 498100363
    0x708090715020a0302010c1407031d120607020606010302090607060504150509031206100f121b2007050a060c1403030106050301030215030105030703170c010f0e24040b0702 76
    0x30904401e940043ca40c40264800c0c3c00800600e50489000e540000850411004e910020004200064400c0103c1200d92017014850403820024600048401405009002d40d60b40710070200194a030b0704100c0290020030a090461030550710901003015446104405418191140b02290401582c11248642c50f45200c804001038180a03540f20303240e5009131041c00d400740c20b28000c00c83e1407800c01074101031142261500381e840ba51054055620320309500c100013112381c1c0c52880c428480050741c4d020095a501d55114003000002f0742c40c050070303140344d000750115640c0040c20a12442d100c1d11200401d80d441403c000c410509646030060784800d40c400410343e940000b10000482e2034121002c0c5060ba403080311541c102800075400031425000922419605502181c810000300e80b43c91401150024407002091034440009031072401e4809440000c40e20b141d503082d956118801c240a03940d43e90070440c2000401c3e403c0c0440c104083c0b0409400580320320144000300c0c5401b4000c0050360023030700c50704 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 498102832 1250 498101582 498101609
    0x1090b030f120a020d0905100807090f060906030c32070c080105070908030717090f180106080c0a051e0915040303032d110c0709150f060807080907 65
    0x2ea100d02d07203e40000310f0002c0540b0502c55103514580c0604010b03004d83c1c001406452610f5001e40c0111541a00980342c07034140316100cad5001c02c00c601c150319101c01038903151b290401c01500d0039600804981c5012901810008109040d1880c1e0345004003241d490b008015070f40c030a26941da1480e4440740f04181c0010100381c0316110004200030103404c80e5108440c50b8071000b0100381e0311080d69803244a4003800409500300a0024030000c00031201621020401903c9080940789010100344907544041720200e2210300d0130010000a81d00a40d656405004010f5043c104013204002410501900c0c0312062981e070194002e4501c0945d02056a00c0110010602020b1020301000b40201d0b40c8a4081a80040c2c20074110401c0251100035500d20442c20070002030380c1d241c41070541001061140e88921280408000184d0044002c0081c0c2028280200d0b0001e501a10741da03e07210200c2c519030107901c0141d00c00c40104200ca4000f0b2096501c04000c2c00c10294a41d04d2000d0b0504040b41e60700a2031542100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 498104082 1250 498102832 498102853
    0x120e0a0506040f0e0f090a140c0901031406060102010204120b040602070c0e04030e060307140703091a3004030c0c030503070602030a0506091b070602131e09021201090b030f 76
    0x4842d8884100c6116140c030340d6040e102e0036045c000000044802c81d0195000070809400181e20748980035a41d0460000c2e95440b911031000a034140b030080e4000ea41d000810450202411020301c1041e401c240240000c516292401009806540319a20007800c1601d801c8006801e2001680442c0c5443c0c3e80090a0804251039000d11134074110f068806800249081c1401e120900346001100d02551858a400c2c894518126110181d54032030b06c0100c0c20480c280714000398058407035914a4102c00d103142e0003a2640c00c100c440c0741c60b211204401032400801c0000716134510b0130500e50203401680600e410307191010641000700c80600958001011448001900c3e024004030754051030080383c42c460144415101c000c10130541e11402d403000d070000b40442011600e0952050010a0f85500c17074030001d03080802e450340206c55a11a9032250700151403220f40c0302c0c8400f283c5031410015140101085003421401c41e01034103144014081c06101c25030714811481660360400040c00013420050807125030624 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 498105332 1250 498104082 498104099
    0x30815120d03020c060a1e0207050a20150f0301151b050109030305090109020f040e010b15030109050106140307050a05040b13030506090706021f090210031a010903120e0a050604 78
    0x1c558800b84d40a090082062800e59010700100117159031204200301d0b160f1a00c0d10003d40c80000116180d110300c000f014000317140c40003e072010502c0a009011044003c505000d48444030340b08481e6103138020400d1015030f40e10b8000342c0b415100f031418140319501e140001030ba504010851079616403c0307400056020060150840d100d01e0b0301c070b50307001d200985070304050f07509841c0c480000940c0040031600605071809c056202c081402d07400400881c0244902012900c0c01c803250840362511180000184030040c002d0150318014a802d14146482100a034803465042c0005040a81004000a070070060749220710142c2d005001c048200c82d41e82c1c03c00035091159041148801c6405000b00d600003101e8541c041200c504950701a0040d0980020032030120741102c81030b04444030016507a42d10300000d41c88071684180d00148e076850004200c000b6280030030740691251070040c100044048140005400f8407a00415078041c3d04140711b41043c0400040d00304401038005031340280000c940015610f0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 498106582 1250 498105332 498105337
    0x20a170f030f071805180402131a031b0d03260901020910140a0305060a080d200c010c0305210c040512210a030b03060c0c0118030815120d0302 63
    0x100c6a813240e00c041c0080240940000c07111344580e65100580b000c01e894072405407207601d07600c14030080450303206285699501003121440c44400c0914201109640c0326410200a42050607113522800c0c04505610000140341b444030002c000d00700070801030034980061140003a501d40426010140200f8582180110b000350403610b020b9115100b40d860303c00c4042d010700300c0449041298251a49040c03000341c0d0540240c18050140c6804c000326600000700c00d0703804c0c4030701e07008800349070340e443d62840d003005004c0c07042c800313040c1c200391542c1285903500802da81201c107140c0101c0d81400e000d515503480340d0001226a40030140c030401190f14404020380210ba100083c81610011100848440858400c0c1a0b0300d070130910f28000c81d044400404141a0800000b03006965160301e004070b01e8a85640110b0f0408400b030340d03200034507113020030080e0010034203015507002020210171054680b0500e8030028608a0b0240100361000c08403103289426480356100901902641c42c00c803806c128410300028005e5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 498107832 1250 498106582 498106591
    0xf0712080624040519030c030b0f01081b011d0927060603070302061b15040606061e11070b031305120a050d27121e020a170f030f 57
    0x3080c0750000000c041045162114840b60b9400202c1e040908280030322040548079440740000740146100000010901008000138501c64039110b040da007072440c8070054564043e00304c40400d070041c50000346c01c95040c00100d848014240381000c2e45c14816004283c41b51a240c1000741c10425a03001c010f000c046a80103034110404840349a00d40540d000801616510103440d00e030ba064200c40020005881d02c84058441c405030310401c0202d200780c4050641c98940c5140100b0950a075450421007840303154425600184801e08180ca0b42050521142201d102848240c0301401890314040c40034031804c210840c0a4080300e802e207a40d13410303e4580c60081221204003101e15216159180500c11b03000c0041d2610341481d911600c1c20500b9220b2982e01030801e200400000a1003074210704402d1100c20114035040303001e01c150018030b081c0d081c0014a0085501d0f4000d2001e02c003840c0444440c2e82c0013400d524225007210144103002c080703440240c036600c40c00200c060381c00c1003c014020035035500c801c840c0c0038 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 498109082 1250 498107832 498107839
    0x30d0e0f010c030c0210020f06091f0504080306010825030e060604090503030c030411090c0705010b1c0803061305040c08010506030a120f0903140c240703050f07120806 74
    0x202900d04011260360900a01c001c00040d1818a4000117050184500c0b0201505006940c50b0b00c0c0010303217042c50038104031111011a80941001e0380ca9114070307800704000e10030002040c011031a040c0c440240511020b4200c0d030400081600040c1d2901101c140500c4080c028449503140301e40014004000d400800c2940b5003901546012442a1030700d80319001b8540e51140185066070380d214414601034100074000d490404290b0a440416607170806140d100d00020088039445000e00e0800c039007142c1a8502441c0214801600d80c030210280301038200e510303580003c035035540b0381e98100868a65290760786d03e030356841d08120900c010060b011000760183c1e44500020006503562001b0565a0b4040325409040ba031548548450351601c1205102c01e00d0586007001c8560325500d40c0c84d944c4581400c2d4040030107030424240301d9100d14122880d200b0f520341c640107804101080c091f050800e40300c1c440c001800e02c03400180e05100200c2100036101255045100d04040004096024055a208503a020310 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 498110332 1250 498109082 498109099
    0x2102190806040c0e060d061d01030302060901050708011401050c0604140f0307080711010309051e07081c030207050a0b0a091101021606031107050102070819020d0f1805030d0e 77
    0x1075007094803840043e09803036a110b2525029640034000954852034180c0032131a00e171384000c9809151a40fa158122058800700041d0b5132440c00e0090610b0009009059664107100921a10b19071004070203041d20701c402c010701d01803c070741801070f40c45100d181e5002c00280162003c00041c04010262861081164400e507960f1480008880e5161300c59102c1c000c1120406010210128180f07454410070200107060007c3c0d000b209495035441c0c2072040440312144180d01103019a82c400c2404180b000b001040020302c550301c165690780303c2c80f54603400100c0405501041b04004d0060400c1600c4d4526000350f13000350641007803640785d8058840381c1000d440040b016402d0390065440012401507101082c4030240016060002c100c000c0c040c0c41445d002010400e111040c0071403c02e01c020301a5610507882d141d5500003010720184001e03038074800002950081600d12140e140c01c0441e01c0c0030020780c0c1c60200c16036048c4032550782441100d0780050b41c041c4100340b0160030b002d8004c01c40821080c4211002030313 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 498111582 1250 498110332 498110341
    0x9020a09050d03050d15080a060b030d09050a0302060c12030702070f0609050d021306082a0603060d1104060306060303020c01030f06050315130b071808030307050a21021908 76
    0x31100ba0058001800200100005031920310f066000700d140a1201451304103066a604030f091078411501c0003a24082da488030201c0321454200210301d803900050401c80c1c0300c0e03445c140c000b41c3d4108903440044d01841000a80012512042c0418401442d000d49196164100071a0083d034a5180d4051070810780c4100c3d8022860178000c4000c502100c0c4010403203c1407480d0f0313034203002086003c030500d00126925103102185da4041030180040d102403d07051086100300002000b4004090390300c3c1c1d43e0250340d08006004040d1284650f40d01080e801404a290410840010400070149035002074115441c244010080503400b0034000c8110000b641c0c24032540006420180484150f031040707560642c080744a0f40d03c0158130700340103603008582410060b004001ca440702c20040d501140d03c5800120b40c14508142580c0e402440005008070320002d5085203898080a4041e103d42d49412048c800c400e040040311104680c180840508255010341d00c1d91040496280001440d2030b582001c07a10000029 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 498112832 1250 498111582 498111589
    0x7030c02060c0904020c070b0d0905060f0f070f170a0606111b011b08070602040e0a09050a17130b1e0c070303030b0a03080c060117010b01090509070c0b0109020a0905 73
    0x7401802c607405003030700e4900c6480412000398000034403000540145d0100050101c1c000000e003192640650700403850600c0c070301d403e038240382004000841d5070000c8001c1c400503010342c001e41079110501e0b080020003000079110070b4800c80031180324401c6550408040184e031801c01e0700210201d40c12622030741ca0700f06d49014880d498800c0c04400c41e1501e0410ba8290701c070340d8030031241140c04002d0305e4041c85110207603840310740840c6d02c2450143d984039000107003007203040da03030789402507011a1002040100740702c03665545403180c04d282e0b0060065080000381c5001000420b045640c240400c810440c0903e0765400740700e0540d0000000c503807001051550300089105c4030000c64040c503054030060140c843c00c56030150020b1a04941e0315070424030800010002402403c0100910118040242800c0d890300851140001182c411001c42e41d050807610409660040101c600b0703280300300d07440303e1240c2d50340710b00712640020380304042c0507204440c00014504025a005102a15072640c40200d840d0311202030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 498114082 1250 498112832 498112843
    0x30d0203040f02120c1003050a060f03060b010f1704020f042301080708070e01150203042c15060a0c02040209060414090603010e030406030e0c0d11040614030304060c0f0204110307030c02 82
    0x41d80000b46449038091b038a20030f030b010310382c40000c08900164968540501b0f8103500415042116090398440c04003220350381081010045248915040c1c5902241d04c250510341390001d48024007a628161003042140c2d580c0d0080807035541e2030b02d1800040c44da0031242c450780340421b00c2034904038081d200c1c6c0420003c102146a000350b554201c0310707604507403a121185407180c850002d03c50440c003040c132011950004001d102803084084a00700387d8040b002843c04c1350078400c00f41c960039404c0310101064429880c2d4a0903600800d18508103c1011a01800401d02034400c21145590140000a000c0790404101004080b4404160707102895559020149401c841c40040089481d030302c1840104603445c0709400000d12014035005480c0044080c0e0007141c0c0c0090040c104075507440100890103158200b600c6050000c041030170b99504105040d00c0030036201c1c8901d0040c5410070800c400c0c00740c140205101182150360380039008100584e0001c124034080d40041e41c486001909007040703c540c02d03100240 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 498115332 1250 498114082 498114103
    0x4050a0207060e010e0d12110a020a0515060d140a060e030d1107260c0a060605010305070201150501050a030b030d080601020f0f3316090b1c0905030d0203040f0212 72
    0x10011b01050b6003081c0c1d100c40030314071300b4203034940c90702c02c03403481c0c07504150141c41100455001818125800c0c83e1050400d1891100c10344014004001c0201070343e1520b02c50700180b50450384404100c000b80d00c0e26400e02c090320300050812806e05e4004100d0750f600000034070a01703c02c200104181d00c9202440352003403203014400b5001d40906010f415244280310022070590b41e03450780107403410386c042c9111400c01c20400402d0310b44955509081140c3e503050f0140b03545c490321034402040f02040c1c4c14a51603011449020f940c1c100200401c1c120b545902980c040040b10100504903410140748541c0249290b0342140c1440c01801402c8101c1c4d8805400100e80544044440180951482c5c000e6007142d8014110f4544c001550312508003e044030b0b1100c1154050704080788051045c14100320041c15040c003139401024161030400c0150900c150003510705054001c80040407131a1206414054a980140f005000c00745100109000400401c540758001013403007542c0d03a0708a0114044001c0c0c40d01e24840 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 498116582 1250 498115332 498115361
    0x708011401090506010c06050a0c0f0219080c01110c010609061d06010e2701030512070818040213181407170405071203020609060f06010f03110904050a0207060e01 72
    0x14072207028990000c507400f0006141c1b10320141059143c80313040d5003058841c95106680c510501840640c030890640d80e1442c14002002050041801d0280c0e801125602800c2d07d400411b0390301954000b90410159907002d20b0041e1f03140c505010041e40204000e04c19508000d2515030700048214114420f07420f04044028280d90540d908401540c001d2801100d00ea032180b5141d041a0401c00391100030780c40340c001c1c00032000703581d070440c80d04d9894280c0c821200200d1791014071821002801410403104858081b01c40303685d041c414040450068051510f4005421081e0319011a0010001e03885401c8802c2998040c0603c8004142c8110107020a031481000034000d1000b01704e005520301c95490300544070304116400956a0322a810356038500c003408400681014060021160003042030940100c80001461201c0c280a000641040e01c061041010b050319084550440c076100400d4400604020b00180940d10b819020000290700416080b54034030324004240829502c14880c03042112841d1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 498117832 1250 498116582 498116621
    0xf060602030d0203040503090402120411060f250609053d02070c0512030c060a14010e04080c010f0204262802040612030801080d0206040803091e0f070801 68
    0x1d040748000f0b98802001929244402c201d0481d00e07459901c0201010000d01e80807400c0c9050602e4000000062108000d100c1c00050084142c4203186404841940845400c0074400700c030f1a00c4d41028968003814060080c614000b8070318103204012a52000c1034002000d180521071520b540316144402d03084850389042d02c01034500030f0300407243d4010103015000b9180306c00125500d0300040c825003101c0500351040d070400719420801d29020031200c0d42040400c01c082c000541c0d0101c07a00400c2c074051284d980780380c084034049400d0008090031185400392403002880101399001d1004080c0d0700c603201c0c0201706007806d0000d1404042c41d001d05511585100c000d41070303181e44011b2884c0300700802a201c2d00c0c0e9041c1d8068800040c5e98611804005040036281001650080e04014084101c140d21a02c06600600c20407000340354086007080d4081d501c410f08136102c0d00d0300c0f00110716040c0003407240c41a000382003c02d80b516080000c0c420703841c1071864040312034054584491500703817181280c0c00706102605 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 498119082 1250 498117832 498117847
    0x90a0806090a0209071803031b120504050a171519020c1f1419020d06030b01140603010602030d1104050d0309320d06110d0b04050601030b0112051b070b0108010f06060203 75
    0x500c0c270130210140340d840b4814490303101e44a07441d84c1c0c584400581c0108400040800007800d20f28140030081c01c15583c100c1c00005244480c603104d03d0108000c0b540c12a004000540c000010404599138004d40003003191600401504e2994868078081d040d01d1252400c260004061400d0288020060148408910589072940e0001245003804220400c854080c00340c40c3c0f04013454840d880c011340c00369020507520f51408020720102850f928806001e20800c0006021854000048030710a8034103a0300003501d00ea0b03200c00044a07005981007164042d80b042d64000a0640c845826000d6844100000c00c1011078108507208003417000085613655a0003040b004414608026a2003105010340c1c0d002c41c940f070440b20f20100550105d1901011030781e0703469140d51a0f080c81d128081d4852400e0a080003500c61000010304181603e00241031101c1e22200007645881c040382031204203a403c000800e44820b0b1610b0300d0b518405007406211855864500d4481c407000090140508450b81a000346140058 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 498120332 1250 498119082 498119087
    0x8190e0f030a030c0221010f0b0103020f190504150e150406170a02040f06080405010c020601030b0402041a060c0d171e0a0b030703150c0f080606090a0806090a020907180303 76
    0x1500d11059a20480f10224038006c0c0345006c03002c06001d0444000014040800381000048507406241c15040510501184007651105022030740c0516610441c00201011507208442030700c5241c1126072451041c0e040c5401c40e540100c5100f140041c00c40d2290286114654103203200d000710312a100024015480180c1b0240d40c0c40b80d0b1541040c9002d20140c900ba80f02e6007503d17800300079580301800003084142007006000c002e1141120780c2020f403001d000360f0b525540300d01040c0b840103007000e0f1250381d9501d0300c48c2c1c03003404400e007034946a0400f814080c0c58883c000c0c852030315240d5405411001c90068a440c0b108828401d529500c43c0d5089446044880840034001800d04d00040030041d103903545280364405030740c00700071000055204400c1c680052001d00300030382c1610300b4940e41d0000d101e0b8645004040d203402c40c02c942d900c082d09461030358681e6940d800003605681c4c91751041145024101c2405141d001c0851040b0140b402504e00c548281c880e110225880f481c941c5643c1401103008009200291 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 498121582 1250 498120332 498120347
    0x3060c03180717061828050105040b060a0608040308010b0c0c0306012d05060a1b0506280b0f040b040f181406010b03040204150302030f06040320030708130308190e0f030a03 76
    0x2865984040d4440021fa50f50340c21500b0030b440596071018881c04001e518a0412101d9000e00340038581605507040039a0094a08601809844200000810700c3d81d40c0c1b1100704080c9808000c001c00f02c42c25940d540e4510910180602e2603201080d040040c1740d081e02c0c0c500500c030401c68030050702203450802c1c46076040303030710300400105001a2401364502d107010034010810140075112500d11401c4442900390301040d4524030350402c5841d2402d00e81c3d000e0b6240c0d50f65010310b407914801c1e07030046007103001c140001d001408011500c1c0c855070303d0400407841c400d040c07004210b040c80c4281d4074920070042e602c403060b640e542e003407080303540f1540c00f000003a0041c00c15411002c0d030760701e90200700c920150702e81d0300080c103100760402100516031001e4100004d01d60b20074079010301409501068840501e40d045041e85a104201000d0408180000c0c24a240081c0058240041d500400080c0c0c5400c0021018010901d41e401c801340000d9800381826814a0000360390342c201d000c001c3c02003986041c59501a01c030427 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 498122832 1250 498121582 498121633
    0x309111009120c0602100504030f08063c01020a120302130b0d1415010e06070c0503010c17010603140a05040606150e1207030203060c031807170618 65
    0x800385120005540480d4400030030b155210f1144050a9414410001d2821304050840780e581130034001400007103904408840004055440d1038500c17540e96101141040040382d005180f134154090f20f0708104d0070b803000002a4855141a07142c08034170804012a80c80201c403c0c081d00d03500e2501a2100445c0c041d41c001c1280c402a644010881a51241d0f841d0651300b000c02000b2003961507558034a5001800d1021550000304402d201c2c2c1510b1825000070151010044100c0c0983c10014810b81402440c103d000c00600d8001c0c0244041c482400000705072845101c0e040c0c82c007000110000c58a1806801103480c1c6110252031074103140d94540051026001c090400d40e4402c1c0e0ba0b04001c1a104c00001c000c41140c8040c0c1c4550701d5045040082c8000c40d150f66110400315001201c0602c016170b404540913411546002c410358a80c1c5451000200a0b1307410001a101c4e4441c0e1030b0001501e00101c21a00c1c3c0c40c0da600b00c182c488030340e00c80d80c18084900444511070310b15000040c0d440224048985200d404 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 498124082 1250 498122832 498122837
    0x4170d0b0a080123040f050106030f0209060a2403020c0f0a0b0903030f04031409090f091207150e07211109070c0303020d090209190b060a0f030b0105190e040b0103091110 75
    0x26451f501d611b800c480c3e850700300380e68100e8091400710130341c140706803178913008a0300b500c07420900342c50141c65200b219131100041d0030350381c102c50110021600c250140d5043e5401030b07040d11480318403083e00c00d0303488489203400c4031880002400a0401400401582d21800c850102410141d5070303940d003250050a02c7d10503202883e010301042d00c1c90303100c401107144542031031341d00c078501400d00c2e2141e14600345210f010f00700240b504014807000244611501201e090f0329a04c080381600f0180d24041c20700c40c02e42c125241c40c1040c047e403041e84042074040365007002c1c092503100f10507412030760510104100440c0e12101048884042d01c000a1107940207210f65450900f001460741003da0002d0071104003a0364018800c41c10700c4415109502c10b02c1000342d0644110390052a248010768042c00040c4500c8001d018180c0d244064601a40a03004a6010383d249843e6880401c01c01c25001e421700468540c1140910b2a050300d88078507500078415401c44581011401c20312003004010060700841c507160b007204 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 498125332 1250 498124082 498124103
    0x20d06090605150a050a08030706050402240a12060e1b0f04030c050906010504180f0212130303140105030a080f07061508150408030a0504170d0b0a08012304 69
    0x12500c1d61040500440840d04240c00c019508070803c0342000d0341740c00041c40386c002001c040106010010403507034026400305021507a03036106c2c000206500c5550741184842641404001d6501c14100002e002c400180c2e02d589540b00080702d680b030b003110b080340207400d401400319011038800c0a01c40c0202c121201882c41c4503291441c600f040598540050380101c0e08880c130070701309221a01d4540c10560b841030702071a2560a041c60311200600c0320a036624007002c0c20740c0d00d005070f0300c0d00c0082d42c04603660032190450f024100d04121400001d034501c1d41d4429070000c2e02d4640300c044400bc040b03410ba812120014020300030075005444600c1c413540101c4120342e24010402c1103000248840c06101d00652031021100388140c0741090751401d00d04107000010305c41210200700000100e6240030751390015078a83c0c00040d80c0c0e07181c0c030384501e5000700c0700e500c800c4404021030700600020143c0c007c6009484107450012000766180720790340c00d1f207400c54082a2990001c14000500d22890000c035a03029009088002 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 498126582 1250 498125332 498125351
    0x11031e3601110d02030712050c0105070914090103170c01150f06080a0b031507050715060807080a05101815060905060d020915011701240507030903020d06 68
    0x80d0000c55020094084602010055681090362103800e480900058140325045581c02900c92240c3c25009000325071621004d016103101d10242c0780c91400310300c020040c1d4200703043d0207042009a4483d069500010111152050402845060489601c440c40403114841d294050341e1541021000394165960f8100801c103243c0c0b0051010300410f401229a0901414030a00500d4030000400030380b03a03281421242407030317500c0024a405624200d0b410203941600c41d440100d0b101d201304100034141203220844240030002580c000000c4548103401c42d0070083c3e03255220390b180c1e80d440c40c3c054820382020034600c018000b5a08450a0044c09045041c001c04166650030f07009040c4c0b600301c400050b500c4c8802c1c480e5464070300c07441d80c00c458202c5074400b40c410315030b00048035800d0041c507541c0d500b080e00041d100607074043c1070074000c1c003850503c0c403c0725580c448036004907165800a051204101c0d01074200140c9000c2e0048594503501691100300d41c03400c507001c1c4a6042502601190915035031100103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 498127832 1250 498126582 498126637
    0xd060506161e061d0606090c0a080a060510023d020a02120a082403030703030e120703031a0a0b041a0d1b0216081009020f04020c0d11031e 61
    0x1800c4903074802c40b50280700003c0c1040c1171070014000c014074012560802841250118041070700c40f1080b030b0b0724010798561b9a540d04d6002900302944420740010304515040919030700801c180030702303910008c0c202c454050b40c5404910040781c1d5100c4032013210030364201070075007608580052060301403600403a00200b61080040003503900007003126001a0054040c8800307003041c181b040c5420944480203076680345051002940f288076454000b404d05030b80e88904281618248864068000e0460311140c6441c014280540500048441c5184a4051401003440d0b460302c1d881c07040c15240c51151460400d410f02e44441e41c2601407101d8030b00c0c258410b10100080040c540a114070308890039038541203800d01a00c0291501207183e0002d6104001e041c004d005401000513110900034044401050000190020646404114150343d0b002400001d0b803c00d4100d000880e82201c0c110b40c0c0c3d40781c0354608030040440e140c0c003543d000003030b0039900c1c071608280601c03050020301154104400318850800075500355 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 498129082 1250 498127832 498127841
    0x5060f040905090a24110d0906150609030b07030204050d120f0206310503041707060c020d290f01090b031507110a06020c01020d060506161e06 63
    0x1002400200080601080391203004050704100308200804494005941e00c00701260400c2c00c0d02c0041001c0710303500b045801660010454010460781c101c0c0d4880340034401c10050155104141d401c42e040c02180740d00e100341050380d44111a02656901001811a616880195000781500c3e040580a000200c0d640e07031003448a42c00c0764402c50018591600501c009049400c42114001c02d540051042021845c100d4841810410b0350203240d1205031807009800e45010380e10070019001c0c2c4004900400c440808074001c1c0d0382000d83d0003c40b000c459803120121003108030508020f4020b130107a0301e40000110385031007514423144244100c0c0e00e6481d43d42c04e07003055960304441280740d202160004220f1104184143c0c454228160b001e8400d005401e00004200712000c1c05010401c03855050714412840f050154162441d8440c205640c0c4071901c0c2042ca0107904484a005070307440c0790503800107003460300004894a1080000c0c0307000040405485d8440c0200c000c5c0801010500d4001d00f00000400c50301c00c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 498130332 1250 498129082 498129097
    0xa0903141809090d090b0d06090908090a0b070309060f0507051c12020f04120203011e051006050a20160803130906120f06090605091c0504060f0311040506 68
    0xa00301590100c41c100030440d0405050228250800341c00c120b241d507440790300c4005a460900d085983c800702031035088001c0146900c1814040e203001d10348020800054020300240008407016000c542e19060f926a29101e03085009000c114104820002d4a0240c928032005c0807840c21b00c6420310140c0d807502ea0800700c1552103000c552032120725034800507400c891080e800045001c000c50401c0060724048210384901d0043d0303007400c2d122101b66421940d09404c00c600714040240310000180203920590040d107000e444600400c9910403000c920f05108605032100d0380c400341da842403001c1820302da82c006100340d03410b1224180034901c61252002038590340040100708501c021a0307a100a05402c0c00364154640003900c441d030070f18030100f1014101900540c0000d40042c0420414129460000014a06041e00401182c1804200940c0d103001180303080c040840c20010600814040030304480d03500c680d000d008041550391510001da80d100b0fa103e402201000076001e845d103912640020704540200d103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 498131582 1250 498130332 498130357
    0x30f060f0c0c121e0c120906020d11031e040303020c04020310150c0501110901030b0f0108160c050a0308040201081806011701061a041d04020a060c02040f140a06050d0b0a090314 78
    0x25a05c3c08000350000300114100292409281d01070a20324000d4440034111140c81c00c111180e202ea102038503080c4200d56055840e24000380f4110f168050200207600700744401d4025000303092000c051401c280c000c0324444c030342c03407440b10b08114241a9841c00080d1010440010068280e20f007000090091003a6140d80a4030030702a6261203c90300010181c5e880340a005000f03181c4a80341e0b081990f082040143c001c070341102c43c0c203030041c0d00c450101c1d10651482005031541c4a10b000300018181c02c0420075000718000e0b42c46400c966500b094041d00c20145043c2102c00340c0c4100010071080002d0803d00b96000310807000031442c02d640e40162951a40c0b010203070360260100080821421601c030405040035003200c0400242450660000380000410b449500180300b0140e00a07011035846520016541c18118010005101424000072600760103ea950900c149003d001258900d00f42903d071030050b600042c040001e54480c50303150054641840104d043c000c01d10b000c9e40e0f2110000d40500410001d80 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 498132832 1250 498131582 498131597
    0x215090d0c1a0c060703051b0a080604290f0103090b0a0b180124030b09041203110c030f0a090e0106020c09010902040810110f04030f060f0c0c121e 65
    0x20300040e40000b21180c180d903020804212580701c4003004075203642c4c0300101e070a00140d1603580310a0b14810407880328001f08035610010ba880c80054101901d18005c1605490400032004a00310829a1281c81e4056080b81d101540540d281c0e850121100149074606241c00700c2e4a0055070ba5940b00f0520643c0c03c1c804040e02d4403007002903414401880d0ba1551404100503080d5450006461005480c0c400b4444c65819401035a468060094100b00a00b900160040c3e406183c2410400c1d180076207058a1000641003a84800144d41207000741c0e54941e03007400246240000c800c104a8059110f04042c02c11302200c4031300080e206000441c1c403802000345802402800e8011420068111416004190320038170500042c0001400001d20940580a40900061070a018a51071601d4000c171000e031079116500041c048100303d070841001d191944251414000350045d135481c00140c80095074008000345803030100704040340900e0301c0c25614104908041c05202c0511000041400300d07000b1440205894 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 498134082 1250 498132832 498132839
    0xb04030606030204112814070b07080108030f12060d060e030403050105160f1b06060909020f030a03050a0819020301060309021e090c0c1005090d0206090109020d0215090d0c 76
    0x4d4007038071000540c0c041403140341c144810020711940300300d04d0303962066042c0001d4250005006154521000240c1c221064071800c45141c1825600002c8a000c0b001840080001410600c0042999102140d980c000c0741402041100c00ca00140b0081c40241d200b502020ba540c080707a114403400054501e8135020f181d0312811821300340c0c00e46801900446040310303000c0000050540c060822807c0c90a54500b0346a1503010400079655000e0034180584502c0c41c040c00054150455408540d0b814801c1d58000b10b610030b01d03420552104c0b03500c3c0c0094085001007040c0445644100701c820340c48441319091121410030f00d0003000481e00240c02140102c0d607181701c14411740c5070641c0c110b00c09106082c01100d9807a0403c3c085443ea40c00074010340d00c903d8011510403042a0f013486103040005149404100b10300d000e802a998403c1401e154801500030407001c00e404200c18080c00c0c6c8c4007078001d0070501d441b03105c0781d0a0061641d05101e56000040c0d052045071400d40e200040c1448542c0296603c1481605 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 498135332 1250 498134082 498134089
    0x90204060f05040b030106050c010e2505060c1506030a06021207080108061306050901020705010e0705091e04030e060705030d05160c021c0201020705190906050a05011e05040b040306060302 83
    0x21042903603001d008050101304140400308040724151381182c5881600c0e82e501d00c203010f01506081d41408058000d8011070840c1080c10441d1803191001070040c20003080da260148045446904141c00440d0803001c101c107507000750300c0c07503407500703c9006000c403281070302c0c40e80f200c008130f030000c0e0300300307031001034100180079007150302240e00c40c01742508501800c1d107401c0c0b0304000c448104c10b1040c0201541d4640001440452080d4103440d5910b40100080c4070f020340f89001940c540245024103481000c616010800210030101c466810403c0100d94007a01e0f122601c05945006400c002c01e0340c40368080201c000000c0040c03015000d42c00c08214042940e04102010354401d0320b540030007408106101c0601b5001d60380e403811010000c58020414201c80906000403401c014240c4c201523004039041030389a10380d070505510341d401c660540390300300300d8540c03140200400812684101d81c0020307010f102c0d10b2010031010062041018650405d585843e64840c840b210a8200d540b0984081c0d6459504109505 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 498136582 1250 498135332 498135347
    0x1a09090106030e030703081b0c01052401020d1103041d0a061e050108090a0b130b060f0f04020a11060106030c0e0a030215070804083c0607030b060d0609020406 70
    0xc50341014800f040e8200e0545940c2d010b101c0d005010050041c001c1055036410b0204030b400c6402c806001c650b138141c01030205000c1e040990b04030401c4000c0c029801848000080c040d540800140e001d0541400c1443c03088480899848180205010070440000c41e40b8100b2a0820000d200c0c0c1c80c20f0030140382c0403164104039900703a448a00c1080709a445844441c007805480c10a641007400d141413681c07240305015160244000c8000d12021000b4140081204018140780d00c00b48981c04195480d0740b501c09100e40701651400b00b50300408140010400780c40c168014046402c0203140048030300b90103080007450b012003a80043e000c203640d9242141600e500000b0411f030b045050388c2c80502e1602c0c660105129038100203050000840201e10700081240c080102c03402482c0020894140a159205100c00803410b180b0301c51800e40119440c0100a500803284521544482c02408203941c0c1c0304003d4000c0c04840352020f9009108100804410310f4030f11405004e840e6820340180c4131414404050b001a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 498137832 1250 498136582 498136589
    0x120c05014d19080c030f3c22030207050d051005040515010f03030906080c0c011b180b0403061136040e0a060213032301050705180103092906010f0c1110091a090901 72
    0x241a508c0951002c0b03900000d0300703001c558040d550507580038242d0070b11a040c02d000100712590749003424244020300400248240e00203202305020811030b603272546100001d8402d44801000724802c180104059401959903a5100e40020259803078417605000321800c40e0542480031910f8065924017010b000ea10500c0c2e49040d203900100110f00c2405e04481418602507840000c2510351240024000c0c0032207034095a030480c21059144200e00c0c90401c0342034125a0074040165420809644040c45103031a000b0000c6003100c0f40c02030030030290395071030b094040c1d8800d11042040c00800c410020005001e02c0c94810178030040f011181c4040109210982951405082c1c002007140174846203003050007081041c00c513a80242030004040301c0e985081d01807138050300c440c0170070808514043c07180582101e1000e80702d030320300b60303229040302281e0401522440030050000c2c0024218075502e600c1401d007035254506820590801e401c4541d56007085c1e000d980a64185942000c001003680c805d141048408240036 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 498139082 1250 498137832 498137881
    0x504060f0c170c09010c08030a110f03010317040b0313060608031c06060c0c0e15060d02070302010e010510030b13120c05014d19080c030f3c 62
    0x4c000b5404002458030141c0390010380329034000070124a0303044555124244505c04a08580d81351601c2220b031a07020f420902c0706542280c01001d113040310201c03810441781030b204105200703400d5448850400410983c841000c0394210b41d502400300385402d0820241c401e0070241503050383c1d6035050010030410344680c0e51200702400304194400c0300095501d4503000c02e0310030500d20b190f0942d59007460980e0401d00750001c41e030007210000d036101c54004150001c2c000b1138000d4000b8010003840301d0030700f4220b0b44215010403041030b00d1801400090803181c138598200d140b101c818240c0b1407241c2c444514503411030110714041040405d002c0c007040400e00030035020b0010b9200003064001c101c20001c40d0a600290f1500e0200303600300020014640700940b04080120b0345e00860340350110f41028403d60801e0080c54004a080c0000180190302c080381203d104081200510040e5201c0c480d1851900d0748410b00980c00c000c4c80158100c1c0d0b560304c100700c904070040000c8051914104141e0701d48040b25100340400c2c1c03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 498140332 1250 498139082 498139087
    0x60f050a050105070b0a061a0309160f050d0501060b160515060d030522080f010e0a080f130306050a0207060e0604020f090601201b0102070f090504060f0c170c 70
    0x2d80e045810b0f10380c001d81068a5101a07610914054020246e03904040d14884030705a801601d0005000a90b00c149034480407690040040d210300100e00107107119034954401c0030301050005042501100d042c4922450005c690340780c4a40c40380f5403a40065401228041c170032000c1a050290412900e2113580396036a4045075420103102040104150300700203000d001c000130710300301803140c10300354a004804004980d41c0401e0f12a41903503222016034806540d03d600305401c032002c6000209081d500c19078030454003450480507200010003504041410550400e0001002011400601a032403041070603800040c1e545901d031401c0c004841c2186403012141c1d112004000c0184c84145580d0200d14040301e0f40b03415551540e004071146c09000003d207110500c1d1070584110300000045081404800c006050344806803c0012a6140207600c1a01c0440b00303041070400050303200e80d0019820600691700072400c0120309410000317a51400902d007001548005490500140b04003080f034003c0003c015007031 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 498141582 1250 498140332 498140339
    0x106260d05070b01060302070c050301090f03081b27090a0603021c02010813140f0a02030f0c0607030f0c0f0b040309060305271e0a122318090901060f050a 68
    0x800c3d4001c140150824141c1c00601c00d0148508020000000d002c002c0082c03009030450714241c1960080204201c01181540e000b050118124116907440288000c1d0034600780036062220380c801500381826958172800542001105071120000180700f40100007000c5991851441803000486501040920510400301614010303071340038808a0708180c5441c0c030800c07450160b003400220581c0c8020010460310841c10401041100441c4009010307008a00b0341d031b0102d0500c100070b1340f202014207149520007401c20107200003034002c010380005200e25107042c040c50382090f541d21114100d0381405803094420003040208255100903000c01601d09840c00340401d0600d6041803400003910080c81e4040614601c00e60f40f8024104403084000304403150b80703580301140c0b1903150f490b01c41502065a40703502c10710504805038003038000e0f61a4010b040146145049a4800400d515046254001100003010507030707020564070310051134003400191000203403031844c007140401c4040e401d50120b07005080030007081 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 498142832 1250 498141582 498141593
    0x21f181b1706041401020306011b03031104060917070302030606241c0e010b0102210f0d0e0609060702030405101106101715060d020604080105160f110604080c0106260d0507 76
    0x602020400e1480400f81152483c041d0701374a01030121070445000424001060f0382c2c05180001242e50603103d82407000c86648555807a07000354040a0740507400385000c900f06003000140c6000f0b02462008003642d0103040c200c42c214643c0214100c0114500c2c920058001c01c007244a1502000c88600081000c0c40f0300b0030000c0d45403151042c1e0400090713140c0c8128400c056929049942e01460440200d40d07895003244220002c0940307400c2c55030244140300000d440c1c01000250705016540e03e800540c10280f030041040881080780c05443c0030011010782c003051000c010010180104001400c00322250b0070010806070004412007800020341c490b4a1039072091510031581a04010306540d01e480443d41400810b44a100c4d903403151400350303e45020481407205005112160b00419a6010b03400403d00b042280ea0200e01d00d2050a6600441c1c081000a0740e4903000386103800990b4004035034a40e42d0174038a40614440901c49200e110a40442c1c40040c10503c8034800503140c9081c070505281c60364454 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 498144082 1250 498142832 498142847
    0x30406050a090f0822080307050111040f0e070c0807060504020111070e01090e07050604180b090105060d0c0e03011d1014010e0421021f181b170604140102030601 71
    0x1362084500255480400c15103008071411001e0b51460155440d60741d100b106d03541d5110450030344d00c0d9407a005054441115850880b41103481c003080c0404020f00706200c42c199050098480014440113454032000280440081c007200d40c041c42c000951171410380005803806c0d4050001c1c0480c0e411083c010701451007007081490548000f40000030f06441811111881c2031220b81149500c5803010078005486544040c0c04c0180c5424000203111f114801c400b440340303894080c02420760200c802d21440d0410030503a4042c0d0105442403038081c00b101d03000c1010900715105108520a11008408981c40c005000c010403102506082c00c2000146070400381c1926a14060045820411040d80410140800e00741e0155801000784110f0541441c80007010355284104601c075000a0242003840f0f0707800019120300040841000f107900d6009209588038003000d0901e0700b90020719910301c08041501e682400b24210b04038500b40c020585802c0604140f444000311416480d03041e0700400400c602a617102c0324 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 498145332 1250 498144082 498144113
    0x10b061c022a0d2307020603040c0302040501091508030a0203040e04080c070e0f0601090f0501030f1d0c19051c020607050d030507111b0108090a17030406050a09 71
    0x200580324120544084440310b2240d2070040601281d4000202c5898040303051014204141c031080c40422180050280392120310000e5821580e080c4840c0015040000080d94130500c42d420642c04a034403503000404440e000e8102080342982c41c00395448000c52820882d02401034000214101801180000e43d2481140100c3c2e00303603131000003c1410812200c00f41c03002c110200e8240c62107561611700e120400c0000700e41900300703c8164000300f1415402000d54070282c8803040c48a0103004e08120054010341301c20580000b103d50b4407072024055500d0f14299005004050340506241c8485d03208015011030411008007443e40580300030003003a511015814403404c03144020901104103400061020700401502a100d8020a03103c881c17111303819441284580e03c0c903101d0f120300250034041a99120504014284442c100d401001008d41c0030f2481c0c00d0344044114119100034405a4842601c9696070b07007140f4107010080148400c00135540242540580c8046040181c0c01568881c011041c24242 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 498146582 1250 498145332 498145387
    0xb0301032112050a020304110108040b07181205030a0806060c0a0201030c1419081308030a021e0c061b0703020c040504080904110c070902040806160507150e010b06 72
    0x41024911402500600c40b40b80084100b00401d14010418101a40c0101c804496402040b010140d0070360084000b0750181d900504150304a1362138500c1500c101c500359014100c8510040c03000681c5007811940e26841a200b00059500c034403800074050714201000e40010b10503c001e0298203060710000035440c1e15640c0900c0d000c45c00240c06002910146802030411010b80f40000d040c40810741700648002000980f55600c12150703450000e01c07078150248200081c007840c010400b0411050240d0003400c1951125140c400d020a071a070f5420045610610050744190050400c00c5080c0851200c1803042da0290403005282462942c0e00a40b500c18240443d8400e50755040840c0034042c041082d0b030740c4844050020400d17039500b0809081e00360018000000c05100703000d00400e40480314001c0d02e0494903200000c141c1a20b0703014020918504400148040103418401c0724003050000c08103c1d007510541c500000d66145000342d050a6841c2c8203229400b40c0c2e0104044c40318042c2c406a511105441c20 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 498147832 1250 498146582 498146633
    0x617121602120a15180f020f2107081209010503130b01141912150f0c05030124020d031e060e24010c150e010f0c02070b030103 56
    0x1808403044010314900c040d4110308403560081a2440000e01d0030700c0140200058803413a1101c1c01d4071805e4500b910400c0c0ca00d480003c0d04c120004200042c040d9030030384000e000d0b8031100c640b003011441c045011002c02c0803003182402020411071040c1301300c6000d04942000b8001d04070041250701d16a215503442036041110002c0000c000020f4515100d00b10b40c2c0c080b00a80035540e480b4540440300d2030307404c0035074820020240b90701d00c030340c0c0580034140413200f040c0044240f0240e2525031604580054010a604036190310740482401e00902c074582160400380c0f1803a4582d41005020714201081d030105141582242c420200102d400140c00035101483d4900814007404540c5060a031300140b6014642040c10440702040b1205168500c41c46401c83c00c003960301c0901c45404049440f14500d1080d4045440c00610401084141c081c070500c1c2d03807a104021400c541c20b150040c1c2110000503c42c5000d41c3d54240b0244000d605002d0340c8024a001c01e82d42c0d00f1035041d610340040c8142111903001c1d20a905 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 498149082 1250 498147832 498147847
    0x9090718030b0a0207050a060222180c11030304050a0b0a09032102130906031a04150203060a0e16030c210e0a0f06060f050405070815040e031606061712 67
    0x250101e17840d80343e00400755841c121183c45c0030b20103500120b02607201c4105020740b800440c00f20360401e60486100b4070440800322a2121810010008984044c0400070b40b0301001441e06070070001140505c0c070400c0100280000c40c2003203c640200600705041750b6050036544c1e4086a88030080050015256450740b15282c00b91a00c200203110740914034031248020b80001900494540c40101140c1c0203681e0181e40b01649408406104005c46008045a41c030042e0034211010360345c0510361150015214088454480303907450150041290041680c80d007a2111022580e4036008400b406461828038000c0c14030720342c2d100c191403010440010100c80e5120408403500301e08012401c01b150708600c00410a10042c100031003e4841401880b81c500c9401c0000541820584116072042031340e50b07140b10141d142c5507000143d201d10414203503449600d0b40c0c841c80000c2e105000410309002c0040d82c114041003d0310713100d000c0d640c0c82d13441703180405a0441030989241c0c01081084940740001e04003580c9103032 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 498150332 1250 498149082 498149101
    0x30c080f060f0a081501050f0901090c03060504020403050c130b032814030d1802060909040c0801020414040605151b03130b070501051f15030e0307030509090718030b 73
    0x4030300700d07540e407201c00310a000408440c08500d03030512203e845c241039680d030389074414004c00145c000310658110f0106001044008059400030401c11094600864440e90b07541c0020242c4c0c029400039941500101e80307411081ca0508410954021868424020501d4160010785c40d0306070b8520392009826404c1030a007505d40014450705103282e2000c1c040d603070030040e810741c00d950b40c010704052144245000300840541075200f034a4618242d00500c240d181101500a0002c5c900002d402102c1c010511b54011881d041d0a001a1000e80800c0610803911a142030030001601d11592280c0d0047c0322284d04d0303916051808080320306031152a01340708003090002c1c180500c0c61050801e9101d43d107802203004140c10400d40024441c00b80528000e1080703480e41a040018000d80300000040f03c40400c200f007182d095040c514500e1050036090000d2810316440078182150311842c004c8001410006030305650380341c505445034004140d460440101800d03c0200c5041820f2404081e03d44010200000c0240380c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 498151582 1250 498150332 498150349
    0x131a0d0b161b030309050f030c0706110a0b0108210c03040626040f020a24110a0602030f0f070c0f150e03070308091213232806030c080f06 61
    0xb21803800d44100340b1060300f002001490b984000f101d4178083d8988814503001d00200380c414000031032020b410032074540ac1c030694074001000403802c071034003480d605400441c14000c4164024866600079040342403a1f00d00501541c0d00c40042d4400c591014404406007a000205540070b483d039509010781180b04850340c06010916890100b84200701c25070400003003000760203187c80c14610984100071000c1c0c9400c0c2e6031000b0040d1202017100c244a0800c0a41181e104070006c11a4810344c80a4078924a21503c0d080c0a07640201d44001076000c0072070610140d042440440c41d40300706030740b909054480c070036070710413000040000d0054940110505560307858982d95008440c01291b400031295111880c1c174001c0c0c01a081111406805e00522010310565020941190840c079541c441d0195264240091036210340a0042c000d0b080560980c3c40c00d00030f480e00c008070700180b02c030030b8001e4061000e1070380c600c2058410340e040031080605008240b194142c2003020701c0c0d00501d40c41003d0b4425541c0740040b4044070b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 498152832 1250 498151582 498151607
    0x70f02040e0a08041e03240e160311010203130b03060301060b0a0206060a0918020d1109011d0112030504030b150301020a11061008121602131a0d0b16 66
    0x14040d40814004110a00f40100700b200d0045c0003020540c0000c241060f070001e05844040c20b0203000b502905100e09140320b41b5081c2d01440d9400140c1c818100e4500c51415600501a880d400542a814818014038034050030145509200840c644580019401340f81e12882c031841100c24008404a2010340d070a411440180402001d55034580c1c4140c10000c2d52114141c89043c0560714035440414400303224080c8400c02a24584a880e0a028079400e210115400354001d603007030321343c1e810040310659030403003a14000c0542800352901594882e212a070020010380c403000d9810008a485400070b5005019102120b4115040203042d40e905210f4005401d145d0041c250305520018069162030b41140b4484810728018003140c6d0243d0301c2038180300408002c1d02401c5200e41c0301d00201d10141c594100200a5002840e2560f11103404690228400300ca0718265910310540f500ca8038400d0780049140040384040459144000c503483ea11042c44444020f4100c2e001801100b441c407005a0180c184205c24 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 498154082 1250 498152832 498152861
    0x3020705060d0b091e06060912010e0d0f0801050a030206160605010905090c120c1009080a0305030703050a0b0120010207021305010e06150412020a050603071e05070305070f0204 78
    0x32803608544100c02040002c00d07141c807601500000c2080303a1003600c41d004005c11a104000c00e951101820004503400c0507100c50350207681207610101c107140c00e0044800f014071900080507460403104000c1c11002400311150100b25003000104000c0da2202d2640d022a50140d5440c2e41d200003400c2e12000b0440c040c034014189604140000907a00d02c42c6e8809446000444250780030700301c0d940104a000d000042429400d58040c002810f12841c1800d40301c0280c030310609044035450b136100c01c911b0a08a02050590205002104002076140c241c081c4c41d601c05141e03007082040e03e1013440060308078003030131545044c89082c0d42003055044000b58100e4003860303002000303022403160301c20b24407010f00b00900071803a18800e250b001c1030307860505035050b40c0082c40c030b0f40d03041c1d0134a800c2c00503003a800038450b0340599000118440018030b0391515001035001e0f000681d1104422000004888040f99080b641c103003c1050401445012035885800d80d80c1042c1c3c4807151140034101400000c02038501031803038003007 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 498155332 1250 498154082 498154087
    0xd060e030a0f1101022b060810020309010f05040510051008071715040b0a02030a0216030201020a0810060207030b091204240c17030403020f0106061d101b0302070506 73
    0x1001030700310040203003160071943c41c142070391442c400c210700f82d02484a9203081c02d000251484221118400b0241048550704000178207550780b181414502006c5410b2569803a6000003404070303921080c0554480e20040c0c4a0620043c205a0ba9055942402580440c0440e5032200132984143c2c0c041e219030024030348c40d0100d605c215100d451040c01035200b04140708940c030a82000c0c541180000e0400f9220b140c009554603030981e00c0301c081d1030103036100502004200da800c10807241c0c501001146400c005004e90b00042c0c88074401c443c05021540c1c05403041d5014484404200b007050350014044041d82c0d03001c1d03001c24160702d640d00910b01d088012600080075180100e404140b07001c1c880348280d0840540c0300e11004095001c02c080d0f4186410150241040b61440718403610350703030154001c680007407203881114107002c40184440d08490562300510001049018407801035000817082a110071400c40c5c00c054100d101d00d401a0640c455049614444070031180851305045c000e2101c4801040080d10065 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 498156582 1250 498155332 498155347
    0x10b060409090f21030609050f040201140702060d020301051305010b090112060308030115080f100b0307171812160210050720010f0201020702010c030e1203040308190f09050d060e03 80
    0x1030a06010600d050f00007860407500113200701c1d1f58001c8602484c00c018144945031215001101c0481e01212100481d000800030031006880c2e90000786072890710340d000180c5039418101080100300382013864000c110304000040c095060702d0400c032a110b007824200b4043c900d0b410200000a07044c9540003034100c64010000083c0bc400c614035a45240900d44d5401c102c44e641d40c2740b8031603814412350301d09409240f543c1c0140007411111000b1a003180380d0f4107003080e4643c031146552411807400c4803080c00c0c0c1c200240c0ea1a4a01c081000a040d0304060b00c071280c0c2c00d000049000e00301d840e0f08050b02a00c66507040c1c600c02c1165000e0f5080311152500489803114000107002d00162100d403003000203000400310285c090140388113200b45c618095059550802006051710100c2c0ca0b00f09800380e66501c10442003001d00c080740c3c02c1004200031442480a180c44880c43c43e1200380701e00204c0141d00c28400c03c100e0500d21903902035101421b4540072141c440d006002401e202004206001400100748000100075 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 498157832 1250 498156582 498156623
    0x5161b0501050c0d05070c03020601030201050a031d0c1518210a030203030702070501050f0d050c2218060b0307110a06022a0d020309120a020303030f01060908010b060409090f 77
    0x2090881e080000901c03454841b010700303c0d400c0328100006001600300308010300056100d2402099280444e00d408514117600c0d1000c6c5214a820031149401c0e5406540b00403900c0c00c14840400d8984294002d450402c100d88802108402011101c140700b420010b09071100301c00c800c0c20740c4c0f03481454801252000142481c1c080e680340d20a8500701c5c058810218000742d6984075204071007041200141e05070a00c1a06050310010300005000c0503280d0606100440c81400313004412031041400d00042c421440c0703040c02d0b20b4401007002c0700c0c5207045414010141f2041d5184411227801804030702d0907010141c0100e0a00b4282001080002c0c00c1a0000441d540c3c05842c0d490340409a6000f5010301c12902100c0800542c1c81e184000d2400150f0030a21850180745059018100e2a8041d1400c0c7d0340c80550660019080d540200c0d0320100c19005c00d0018810b4540c003107141c0c030181008030020005400303144005a0079020394840d10410903110300e0301604000a0b0403100801580c003000d003ca401380303082c500 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 498159082 1250 498157832 498157837
    0x203040803010807050604030f06090528142d0c0406151b030f0e06040f060305090f0304060c1e1209170316121e0c12020105161b0501050c 61
    0xa006292003413400102d4a80b078200102d50489511207a003c0e0003403915500c0350f0207040d00300e00c140c50900503540004419031144504403107800900f000422908103c0c54406c0038881080b586101d954405504190440c400034903202c005d0301c821110f6040020750103070007031a140140e4800c98001e0304180c00043c01e060a0440c051940c403980d1200d400700c41c8046040000001d070300d01c000d00001c102808600d40c55006551007840c140c0c0140003503280c1030300c0c0c070040540358401e07a204200180e62070041040041042c88401e0080c150040503600d020700d4003030000d0051058440140c0040728192040c10701d4040d22041010865010703154140c0030b40d5940c1e01504d105600d10541401440c10300d40c20441180102c126000180402d20080b203020594407140e4074000d4200448080c018540d825a4000c0c41d82243d0071204900d6582e2982d000400f46000348038a41081415019a8100b0042c080080000e010803800c0c80004d20b005542d908d42c007040500b001c01c00d580041c100d541792005100030f01102200 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 498160332 1250 498159082 498159089
    0xf0605091303080a0b06091207030507080d02060f1003050d02060105100513090c030209030a0c08100c200102040518040b090319030c0c0b0f090106080304080a021909020304080301 79
    0x211424290741d00c0c44021149041004010005060900054041951688003181c1070b00e028200b5800d0040490201d166007511200300c401c2a1702c079810400070400100079500c050b00b8450050448000f0244003c1d54421018141402c0054881c2c00101003c40c080a014000d540007411101881c1d600030003c0c1d16558207010b176a00071040c281e4004456405402103c00c4001c40b40904140c40340b500c8a401c008100d2070b28140e042607000c01ca40b10503950100310002d0118001c110200080e481d12618074505001410f1100096040503929804d054011007045070310010301d0018108004000344c074034024400c3e900542c0c2d05c40d074000c4d0301c1516040280240d6100354030078107501100c0d842d48500c00759203000c0c2d00b10381d444147c1c0e00002e8a04980c40f035004148580712908080003220721942c2c41045810044800d41e000c40c02000402c04202024002c00004221501c00345140038107101c80c158403200d17a00c10190080d000c0740066400c0301e0748507080c04010068000c003151603041602d407220b2158002c0c030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 498161582 1250 498160332 498160339
    0x14030406021c0b0a14030316151b0504050d030c050f0c010210020f041e03060204060c02040f060302030712081c1508010209010206190b030601170d023d0f0605 70
    0x210380240e80000b03200354807451070020035240c0341e140340c4a82d01c0406017042c5201905400240301552080903c240ba1480091103107010405014040c07408808541c2081810051200300303802c0c1480c04d176048012182942c100760303000717049814a810280c0b851008260001c00c1031280030110082108041020600640f00f41e00707440c030700c1c1c188805007400d90043e04000c54402e070302000204141d04080a425601e0101c90400241d01c03a07494a4580480c2c1003030b408503001c80c00320741c80d50086140502c50b07050b03421503a020070088d40c2e0071600846d13542d5401c0d00941c6401d0a038030b10100284009803043c0c030303110441c580150f03001c84048107806000d00582d15000c40b2208000601042c3c841b01130087c0e03010380300e0690040005503541002c1021030207400040f06e004581d990344100050b103051108034040c1c984440d80e4510b00a002a03124500001c0d41c590100b150806103401d14000000c0070580821060204000b00094202c100c102550317050394a0803800078600a559021703950181c026100301d90045 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 498162832 1250 498161582 498161617
    0x10e0a030806101103041502190501060e0105061911010f06031202150103080f25030c230709020708090901030f0210170a09061107140d03090b070f1403040602 70
    0x3d0b801a01e111410b010001c1c06600284010b102030704151a0400350603103103204554003103400904c0344503600081003043c0c0b01d0340d4640308140400003e41407020b0040030150b070101e150201c0724000800d00c9c0b1601108004000d00b042104402d010250013510b1107814890b42000f0480d528500741f02c2500140d0060800350140a480220325004154014100c0c0e0300480002d1800004400c009060750100c1216424400c0d0b2503d5540b0021a4024030041130b0710a80b03034040c003800d140c18100321401813522845002d1002c0c4200b415101d03000701d9190f0840b0301440e800350b210202c1c1e140041d1180a8030401541015214000109002c4000c103010701030750003907a0707005403101160421210640c00c070240105000d03d000100d04500b209500020000c1e011f5207001131154041d20fa016500e920440040d1a10021404203103030068043c4410301c566020342c10f08000400c0309a50b20049176400500715410302c8002490030b8592401240800364140051042d07594074a85440c00c04025000b140e03580c590030f24503 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 498164082 1250 498162832 498162859
    0x1416080403030209040e0601080d05161101020a140115050402091509040f021315020304051f12151d06030705090c07050703080715140a090c0b0304060e0d08040b0105060a02010e0a030806 82
    0x40b404c4510469003480d010b33240401d039840c1e200d20469a5660f1504620900d080364001c9041548044040050a800848e005002e4504040804442e4000c10304c2203104101d40a92070340c40c440342c002031800c12910036864064900000d4010329080840420b482d00003c0c0640c0181c444d4800b550503a07000e0355560710403c50601c001c07aa00c1c0070303a0160381e80001e4210710300741d8600c2420006d5840c10b1050700e0a11f40b04000c80c03401500340c4900c0407068140482c901750902128032501c18130700741d51200300100c460307a1030300d4000282c1c1d40c4444d00c501e602500d40345001c1426400458100d5405980081c01c840c00d0716660320341082c80ea4442d44058030614505030704008130003040d01414806c024414040c228907111158140300030000303080120f44605005000250a81c87c22014500c283c2c0100c5002590700c80048003242085400c022400411a46208020016180840903410740c4d40503127005407901182801a4014504900e2440c13992040400c21400c0540c00402d43e882141c040c3d404e030400490 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 498165332 1250 498164082 498164087
    0x1b0c100201020a121a0103050a09060603030216060c1a040c080f0a2a03030e01050c06150a06020d0519141b0106050f06091c14010905011416080403030209040e0601080d 74
    0x661038020711001545c040300e511598400d030403458100e1900d0384000340c0c00d940b80c0c0d05c00003110400c2c0d0080b00942c103c0c2052050700038042070145c0007008181031201f23404c5401e03a140b44071b14603500f002501c0e4140180206050080407403848014041040407281c01d445e50784a0b1039907500880da0104c0e03d040744450030030751101c43d08582a40903144d03c0d1100b061103045503401e80b40443c9044034281003020900541c40800d10420510b40640d01d250ba010080c03034415800e10104006641048080d035100400394046540e01c1011a1040306c4840310280701107040c10b40465445001ca40388401d0090701040407080b000103c03039000541303080000200101d40c0d8036014030420329a50040c40354007031418000ea48440c1019034a1880da050000420801d58409541b22943c4000750031440c0c56683d034602081040010034818411100d5404c2058503807880e103d00700717000b413014040c0000100407110300800c0c1014040d4061303c0020800030310620030300307107210503036603480100740f0551101d84606603068006c41d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 498166582 1250 498165332 498165341
    0x3070e1b0a0e0405250e0906010e01020a08070302070b040e060f030c01120b041116031704080d09060b060a171f1e0e0a060303021b01051b0c100201020a12 68
    0x48946680380b940005104100082900420003561081100c103500f0045403045e0614403d90a1a00c510780407404a03014003c2501000788101e052021941004505c0e0380c0000b5017250065100c540103546100601d422820520b055100480440e400310b4045202d2100f458003074804e242c150740703081c0321101901c00c0569807000c55030414089000700c030000504004681240c024860054001b1a03111214207504089030f2165410b81c0300700b05841d450f202010b0380900e8194059400ca0079a030885d0420741c4540056100c0d10003c10310043d0b8410742d00c0c1c01c2015941042501c84402030040b604c3c0c815030080548900c040b01001303e600c0003035030000b400403020742250700f240c5140102280307401810400c085c0301920090040c074800420b00000040c0f642000b0f0300e058800e5083c0b150115485145150180c51322250f091410044080074800e500b03580da00c041551406011101c9800d8400c940c103100705e05001031029495080000c4078030f5002d40d03980540083c900c40100f9507a104907104410124000c84 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 498167832 1250 498166582 498166597
    0x1101080106050409020f0909012c0103020112020306030a1a2d010909020303040906091a04052e0515070308010e010b0a0f0917070905150d0b0903070203070e1b 70
    0x2c070248001d11007820b10743c0c080d00742036070404a441c3c035041c3e42c10700044410300c090f40003017000c0100c59824045070380701d064a0719080b520f1140d58685941180d00180035035100f82d600e4144030384d002c0000f8200341e1b0108400c81030250480180403208815070b26820701e07041c0403207401241c04021080c04084210440c0d04120f000c0408245c0246a4285516040906480c1d40b090364140b00502c40803c00b175410f07104000051401c6070700010900f100361b0141d1030540c1c0450180f03204901d4002046160050074041c081c403138801d034000d205481c0701032018010305c8600307030800341d000326034283e52080f209100401084118080d403542c2c441030383da032400d580d902d9509004090085205001c180906405011489409000707420f18680d0140c40d52221130046c24005035140303007980700c0e0134108040b45c05071203440d4000007200410301e044001c0b100412061000c410000300b4104003040041c514003c18000d4a42c0c0325030003804e640a15907204034000a0030804d8800c00321308090052501041c11491080302d460 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 498169082 1250 498167832 498167837
    0x50102061305070b030c04050102010606050403080a081b07030c0c0509090d1101021e18061608030a0617060702010e1c11070302040c030c14041202091f060c1101080106 74
    0x380d5181090441100003101c0119038600c642d100100789a00314601840c0f00d650200360013911189444002825501d0980c441410b002d002c00091012070607090440c0c2c00303a0003504004041d9114072100e50001c2c21450246840c1000102e032840415600c0b01d04121083d004503031080c0760b907880340100070f102c44040d51100003551050b131810020034041c05801e00803040707400c001803c03c1041c5421700c2482da071340004020030305800075403a8000c550700c0304610303141c24090324010b04061f106414400324601400014040803004000500108400d40241014080e043d107130381420706490543c1580d442c41550120051b50a1501d00e400d08030000400d40c081001c410580f210414a02500307481081c0940e280070000d008032000070000d030300c4e58000c08110f84955a80096010f8080600804528038518229100c0030108810003a4448800700009404d804445150464880102401c800351000c0007d5201911001001a82c681c1003004041c0b05400380300c43e0840a0603420044880800900901d0302 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 498170332 1250 498169082 498169093
    0xc03050603060907121e0c05130c021b120102040e060a080303070e060706140403180e040f0209060105070c030614060303090a090b0112060e0702120f0307030504291f050102 76
    0x643c1c10740e40724a01d40c913009045c0b500411100c0c5c0050700c21021b040354191441814018104070781d0602302d040c5015000168004c020b0701c07995010094a43ca20300d0700358480c6c07442c60062a11240c0c1c61802103c11003407104000c5580c1d55403800b0f90300205804984c400d00c2411501c0d400a8640c50100c00c9902c1031200b90b44480c00b1a850070100106500002000d882c05541d5180e01641400700da40550302450080e1914103080b1701c5900c04042c5081540c0112559030008000e110000305d0070705003d4082541160110015960000100e8041c02010005883c101403042c0000900000b90b00016643e4010340780c1d0031a03961001c06159480c402c0c02c8017030380c214081c0402004442c085031702441a008051420040042c010400324058070401d0b0012000072490707a0a008910780c0410a0038401c445400d030941c240104502c90015500008014005040e1500009020040742500d4280c08407050502c03000c1c2902694039904e043c41c412540e411544501d41002c02690480d000c413201101c00581c020070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 498171582 1250 498170332 498170339
    0x90106082d040f110a080c040c1701140102070b180d0507050301110424050403080f040b0408060a05060909070302130f02120f1f050f010207080607030c03050603060907 74
    0x9114011240c450030503001191608003014032801c4000d40990301454403441440c05500700b5000710800007007401d00c5032444d070404211820021580421000c0100c400180d8030881d94020749040352a5011341d5100d87e0352200118100050388808182c0440a90850b41069100c420300f40c10391191561850f80210382070720200c220b240c10030180704105d1184055640180c1e45502290965058100031881c43c02c002c5418090f800440c40310a07500c00d00174249520760414124081e241c1e104901000e41102e00c0054140c5801080000f124010029040810b948660f11040541c66100036074801014070704102c01b251319880e00ca010f06000f002a6000742c02c005203181d08014498200900c41c801751a04c1c3c44180720700c0c00c10f17031029001d603000b540194481d038500b91076041c000200081148015410441d00d0406030421081d0b00c0301038130300548948003807056840c0142d28050f119480b114040c860325041140f0158542c100e40c254140c1910180708035100c800801d03494100481da0b500c410fa01688082 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 498172832 1250 498171582 498171601
    0x10306091b1202090a060e071d0a15111b06090112050a02030106120911010309030c0f0804090c0302040e040215120c121f030318180b01030b09010608 66
    0x105031449444032800c034841e60a60036419840941c024266803501090150960911301c000c690301c46590f5004211507801c0006201d15a00701504800820a0b90f07040744104d003c00003d022021580144140c000c243d41e19841114041c0300d0b65010700103440c1c00f02d42070000300000340700c107440301001c2c180b0455542020140211600820308013410003602c001c04880c2c0d0314803807007006c2c0100d14104001d82d407981011000b8026041d480d09926005107400c0f0410003245810b80310420501c000d00c0c011540203500c1c1030032100c0710040c06001d0003810314010320900b0492054010001c0b1466881c00380f1480d8020706c001c0d005c0f400350303200e65500441c0c21000540145011290b1000c68001c1040450030445041c6140aa8890449403030345041c9000031100715244694044540c0a581d003054145426a0f9002c1789824014600c001028030400000f03818540402c031060001400789200203011080d24610782030040c2821208240c00f01e46021880d050300e040079082e55060362a10380700c10085444483c00c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 498174082 1250 498172832 498172841
    0x2090406020a02101a0102060603150f0408040503190303050106050f12090f150402010201060b0f0909090f0a05010504212001020702040207030e0f030105130b061f0c031214010306 79
    0xb4801c500600481114891052090f940c00c4001101020010348042d00068503004010b00081c0c480ea2007540c0103004100750082035544148000400e5556484e103142005480c00345402455060182456480244d11405503400000c0c2c0651341c2400540d0340d0700425070712071180e0101e1611a50040cc0702411120380300348010742004224040741c2d8009440071119090007518101c22500207440c20070301080d981e0901800000d01200803645141076006030684056208101c02c8600031540b403400650020b03000d01400400a21a00694603800d003549413582c002c01c3c00300c40032201d050f801840405982406403034401d43c80100e03100c0c04140d00c890302c8009602d05c04010075009564082000380c006845a00190603868869100c07281840c3c2c110041006c0d0b00075208080c2d000e68500310410482154901000d030803560448610382060301c4010100390201828011010507000a4004030005d50b48401e0000d42036000769140762810101800e840203640031100c0c8201c40381002d034010b0000c12002d520 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 498175332 1250 498174082 498174097
    0xd0f050c0a0f110c0d03020d2a02040b0d14070807091103180f030a080105010807020c01050328231e041410050a05010807050a080a030c02210615030a0209040602 71
    0x441d183d09051800044854843c4d1801b24016000110008125608401f1260603100d1100041b480c1c4000f000307000580758100b0b00044e00c110b03100c810800c8a0b84805014203c403507044040101140817404181c0c0c0d8941c0a0704c982812841540c0001486480920030b080e060850718449030701d152103074160f400301034203844006c00b1180200400d00f1800001040203040e655842e49890b107580d80b4210001d03001c2c01c8010050000d542001036543c01c1a03070f2004c1203071f03803264044003804210024040da04002d41181c03804500300074901310100003003c80d891502c0c101107119421415440c2c0e26400300381401d941902c240105c0c42640360200f80050704100348445030141000c00c07244035616007007030441520001d46d20400500d5841c2c005220750a81400300c500981820748921040c640703802c4a403903484540381805410413803428100811965155040c8600c0c841c005e4000c2021801c071a241070712002d0a40742c000d000b02100d0022680ca00b0045603848595400070020341c016526500ca40b4040d6000c0711 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 498176582 1250 498175332 498175367
    0x90d0606050f04150e370606080f0115051c05041b080a0611120a0c0e030a0c1401050705030a05090f0406050d0b0711150f07080907090f09080d0f050c0a0f 68
    0x881c00003046c030b220030140c1d010401e903128030040d459a114002100c1c01604800104030054080006101c0842040d5044428448452001240d6450116001e003d2515075812a0401c1c007136540002046400c114002e50041244030402d40c071040e600b03000008544940c1095030050035158004c2035095100203502c06c0810f071420f00e4000c10749507035184c00c0c0c02201c0c2c45102d00c1e030f41c09004c0b8030380360320500752602002d040e00100100354072601d940340d06503501c0c42500d10005500d5030400290b4403a205855005921004a030746403152100041c002da00884403250003030081c01424005482e05000307002c1111400f9121807008952a19511000740b0300030070036824040d20b8a0182c508820401c030117403944a100e00c0344c000604010100500c0b28402615200402c9841001c1c8001d001c00401c0c0c2d20f08403561a0f1001601c4401d26404201602c0c1481020b407000d54003040c6244601d105800109a1044d4004100700326581e487c20f441d040d0154101c550005203541144045960041000400c011040e0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 498177832 1250 498176582 498176611
    0x1060e07120c230717160f0203030c070b04061409090708070306033302090901050108100801020325020601060e010309080408070603090308180d080c090d0606050f04150e 75
    0xc400100f80415201d0030410340344000038000090000d00704400c0c00001c07003032840c5480c001c0e0030520170100c0000740e1000352215240c41d880c902190740410072160341e20b0049041e00c1c00103039035035113202c0c1940243c45030700041502040c41c01005107949048170540a8020111095030711040d008032458040202818181541d89c00c1c0800070400340b07800920702c02c85c1c85824400800030111616444040164540080340c0188003144465403502c1c441410342e902884d000c1e1403507949412000c0d00c94065880252194070010610035003c200d030310214a041c44240500221201460040740d640c0310034404c0304001ba0b9001350442056209401000c0c4280c00741002ca410135850345103082c249146076010301e002c42e940d50300d2642050303081840c55521000d220182c1c3d0342c0441403481c43d034541004036028003c1150b0000003901c0c40c502401500d103640c03000b80240c07404114a15000c2d00402080c0652403150800c120203038090301c2c0c2070050840d004103085403440d5552600c04038808a050192000c00841c522 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 498179082 1250 498177832 498177857
    0xf030f0902130222140904020d0804061808030c0c10051b010510080d0e06070c2607150c08070f0503070f060513030f0f021c05030901060e07120c 64
    0x2e0800c10381c10449014001680d485060380c0307003224240512050008200390781003c004044465942c121880c43c260f4035200590b45034800202108600c030001494034202080c00708046a012001c2c5d029001d0201040329483c0d11400c825a0f24001c0020400d856440546480e42c02d040c5055400000c485500b8103034103250b0303c0d64094a06003101d816519031695940204509000e80c19000d03802445004d000d09094002101e004000c4412819110300034034000440700204940c4103603580003805030050252006420000a410b440c9080b009070707016109894001c10750350f81e100c0e0311340d80c1c0c0b20f019140c00342d140e02e15599541c06a00800410303140300705074a80d89000300e2400d000500c1002d22071140118100202c0c40c3c24011280007070b0094400c40c418401c2c81f00002c4d0802c103404c1c051707a2641040088881c2c2484101d1800312040342400c0140d0500780400410341e0442c0155004a82c410001e1000c1e0391501c036200c000d04000c446202c00a941064403407880070075588100e06801040c178000d200d0400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 498180332 1250 498179082 498179089
    0x90613050c18090115060807080c09040e0c01030e072603071b1701060f03021c0c12020f1e01050310080d0906020d080105011d0102030912030403210f030f0902 70
    0x40b06020421504040104109400213111742c072602d0400414061600e130620703030014003103200201038109025a41d00480d091282110503180101380003801400f01e00b100043c03d50311840141c0325140443c3c02c01d88a140d1602001c40c055059454800c0030348000d540011440c8038000d00c101101489010400900317001c2002922040e50710103002ca003540c22585800c918919040b9064413418040c4d2400d5070510141d000c035405101160340456201114840321050390507103510b0b5210003031080e640004000b82c100f40c00071410302c656000b2146404c1c85058003081c0151422081000043e484100901e41a1036008a01070b42d04000c0c18010100042d031600e0103d4600542604080c001c150007038403c0280f0703a8100540c0445429501d0026901d514080020303000c006608119008000c03203425500481c0d10030000d4070605440280208001000c200f80395443e07601c00d000c2605c0d0b410066828a010201040c00000c50713078481e940c0c05c040c400d4101e1044005011051084149030740315810040980d0b07 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 498181582 1250 498180332 498180349
    0x50a060e0c07150e0604050f030c06011202061603180b1c0c17100f090e07031103010207081602040c05070506040f020d0b04060c030b0111070302060717031806010e090613050c 77
    0xd4134140288030390300740340c00d00034680549000310308240e5004002041c41c3c2d0801042040c1107451042e280803901050307100060050048031181d40060a1000b020b80606501022070310703200400740116001031381c558144040a20882c12040c182a554120712008030391164072580b003840f980d2609829044201d2401c0400742c8094600004e14401210b040c40046c26003082c1100600d00c00d6000c10902c1c0011210a85400c2c1510003d49002c10140001065480c2901214007540c0c0c49034109548241a040d41c02a80b00c00100036809985000c8264000502a100300e60942d5000001404c90340c0e41c5613148c85900c02009000ca0304a2601c01d02040007507400001e15004900c100c10101d0f0040d91000020202d07a0011400e50401174440202c00302c445c000301d406c10a4a8058480c41c2d91144035082180c00041c1d48074003400401070020030030800c207004001858070020f1443c19502140d80e5000006070248040c0c500003102d800040c0031030032449102040c0056588610207484011100c88009800d11 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 498182832 1250 498181582 498181601
    0xf0d020708130911121303200f1605011403150d03110c030d0516300207090c05090607410f120a05070c0f09050a060e0c0715 55
    0x310801c000903c240b6416014604003207440403002800d0042c900200e001d004006002540e0046580b04540c00b03051190000f00d040240d1030300c81c98034002408688640c1d40c0c0e103c007106501d0b8001e4201a02c0d104101c54180d40031690140c1d01c801700c008200842c681d0640c0050136801c52140c900b172043c0c1d0140c40b01591817441c58003d840b40c042c0d060313040038594140a15481d00d5486074000044500901da04101952103510810303241c001e900106c6e2500c03440d41800b1007480d0099410b110304500c1004000c41c4160b01242c02e681c29109043d545640d0b42080d40c9800300d150000c20420b10281c0f955080c00390181c0600c80c051486182d07098120018549402e4400c2c0e8010052610040700d5007124855002d00303450b100710307400249040d20710301070034a03191a070301e501c00080c246002034940307100d520408c00e50b45680d4125a40d00940c5070b44280c42485201d0500c14200111b04280002d07a46540b40e2043c44110f84110701c03041038660762100c03240b649070700c80d500446549190140c07007c1d41e0403d512a0741100c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 498184082 1250 498182832 498182857
    0x41b080a02043c0305060727140a080303011406180409140f0601030f030c02120601120b0c090f0906061201030f0201140c07030605061302030a151403030f0d020708 72
    0x860030f11842900c106005100500c101d084801c0d0800c0040c0c0001003131680f02004c1c0c54051411480381340d01840460b15680b046081d4410340e1404900484110b01c04550304a080300c02205841d528405607840c1d010901c200e242c40c040c2d050010a4a080200080c01100c4400b00185089202c00700081c013281e030700c900c0595900030300201e43c1c08038090070003009005c0c075160801030030a0b601d140c1e40e034000a000f100c0000d04100c24801d8801c11916100140007031014140b040d941e9a41e162644040b029101020594200901e000410120100141202e41656015080c4ac54501084c3c1c02c0c8001b40c9805000c103604110200429035803d8090502203029601c180403005030500c590000600498854000501054081007060144070700000c0100407241d00440c046000d503076a038006030340801c050740c048019078000020040d11426541c0114000010321703036280c1c0c6658888608012100800c281d03250954410400100c4103401907004e010030400d019030152038030106582e07002003504802e500e10038 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 498185332 1250 498184082 498184139
    0x1030603200109091518020403021f090905160c110301020a11010b06250f060e030703080f06030d110a050f061905040b010e180304060e01020606041b080a0204 70
    0x181580c0c401416801001c40013001d002d042015451203c2c0c10f4041e10800080550190048041905c0f0782c040e1001503400400440c02a00296029481d03000d5020962000a00ca40e2020a00e20300707500c212801a040310030340340c40141c400001610800d01d10030717058841091040448059940074002010281041c1ea24403d15149100002e429601c1d580c3c0c00301e22400341401a9804801d44603142c441d00b14000104000300e00f42810f000031032041b07100010780301d141071020594526070000000d0200d28800d40d101d00580e0b50314518050020000e40380c1e2681a080021850702c1c4a205001c59000a8034a0087c4c1e292180c05543d25842c001607400c048103103421081c00c100090b9809283e502c2e82d803014141c144514686503441c07030a00e0b070741401420281000540421401002d00c900d003440e0121345001c4a80e030744e485900141188006020041c014441d001c001400f80c241401051415001c4280f40a00c10b80100000d8401000062120308015030034000003c600d00030884841a01c0804d821045 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 498186582 1250 498185332 498185393
    0xd0f1202162c073002030403170610050307030b03071d220203030901050a1b081b0f0613081318063611030f07080907031a040201030603 60
    0x1158001200340d42c0c124202181004080c03a0001c00d6143c0d2071800018038400620200c0000c041203c40500c1c0d00340d000c1c404000c01c001c168000300340100c81c0c01d019030200d417607540725810030103c2080c40c0d03144000610300344049501d031802030f00602107450b00202500c098a481f102c030715240208000b13103405211100400e00c00403400a55020b00445080500950060206c1d00425540c0c81b501680604000340000c032200402e00c5040ca00002c2804400340d808148400e082200003500905036074010714890820422602000003030080d24459002d0140610765501503003440d44c4202040e055880d003000304100a1101c19480558000e4a02120785401c0700c03c0b007003200e4044541540140c00135080381c0d00300c414241140c0b05401030f00080000c00c00f4440182c05004d0015240021030030708900c3c8003009100c00580d040d40e00d00c3c8120010b581d108021341d1400d01455850700036201c0900422075528031f9007181051035481550144c010b05001c00c502e940c0e50f03600703282070708059176881450400d402c620 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 498187832 1250 498186582 498186629
    0x6081002090f01081b03180a0f060e0703021f03090b07051e091e01030b0301090602030415050f040f0201020a0b07020114060109060207050112060e01060f0e0d0f120216 74
    0x3003203011000e20b400b03d1103141c03611084038000050403091058070320100004860702c04400002c034062030444240c0c0c01c101114074207522740707034a070100443d0f20f00d0034413541c3c02629000150203011260000d100304910901086021000c02001d4049010180c40341d440201084019007060b005140c01d46e41c040e580e1360324410300c103801c0031a62a0351402039010426002c040e82c64a1180c4043c0c0c0c1c00d40b94403890000038800607401011529187c2d605542020740381404e0125990256100300d0141002e90451040304010004807501140e0300c40c800d10b8204041404601c8100b9251f86092042c0120342c1c6001c1c054a4517021040200d070b440340141c0d1680c01604500943d40242c1d504820282071440201f418448040d44444207070140d18100702901365581d4030742c00d150300240014500d6416540103543c403100010840713111080c2900209455a05107007603402c01d03e240c0002ea5400900c0382503000c0040c0c0d25007001c00854804882184a41000c07140c0709048030301c0108c010410018031840c1402e40c42c850 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 498189082 1250 498187832 498187849
    0x20c24040b1e0408031302150717030601210f1104061b032a1a012c0c0702040b09010f06020f010b0d030e06190207090b12070b0d0608100209 62
    0xc0225070440302c06404200c0001c41604a980001202e4980ea5404002032410b8290000a036109034542803841c280d0020360000c0408502448500760351038124842c00b18a0f02c030584145000900905c9030310598808205201e070040c0003000f0202c0d400721200078000940e940da4151507004200003800700640c2d604010080c1c0d42d04525512a010b65407180c070042c064410f20a10240c045d6415a160742d00e2100d91408994600d80c8200a05855405c081500191907002d000748019255101c1c1d0100700d003074206540030885904411840c040b5640c60922546541145000f281c105440f100f140d030700d658801c500c2078040c0030042c0321100c4061030304400902d0220582c030986181d0745010b103917000c1c036102d21038041003803600350601d406805240c0010894a20560160f100b6020007007483c440340e5036000c20050f00f00c039120101844920148410004440c0c1c01e000c0c4600d065005040030072440c07400f1000380c55003442e1102c0004109540f4149182065007640509040aa001070710844d5442c06404 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 498190332 1250 498189082 498189091
    0x4050f010c020d0b07090b070c1e080604061505120105060f0402180d02010512040c08150f1f08010e0102070b0109020a050d0207150e1e010b0a0504020c24040b 70
    0x1c1940c14585103070003203000c0081e41c8001a12042c846400108034138050071440c802800c50f031008650f50a103d080040200915004440403140c000710800748540d0b01440ea1020360f69601c000c2c25154903076a4071100105604125400818622400051180e0f200100d049691500340300120340c91504c40200004641c011480c00d110768814081a00e0130040c506041d8103110b070a95619200805030f00042c0c0700742c007484164060b9074001000308800c01ca0780303030700010071602400116003400c00030480c9900080d008850321140205d54030700050315032102d1156440c00e000800c20321b01c020f030f49907000107094070105612a210ba87d00001c80d5000c00400007102401040080411030402c000801d0003007040c494680005100c540204402c010300051401e000c18018000c1c508100020010340074940300d20b03820701001d403145464101c1c03480d190010b005c0c04c2d20702000208015896400c050400c80290004120540c9a00c6410058403d10706892480300d8900d483d041c00706e603140b401e46060805050001d2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 498191582 1250 498190332 498190337
    0xb09070819050c0d0509100513050c100e0d170a030c1e1418030a0605040203060f010e011e03081303020a06020d05030604020c0309130507030c08010e06121c0504050f01 74
    0x4100140d124804094815071800b40e000820f1545404008614100507813004880461410080c46068400f00214427050351181041e209101e143d00c0030014128480035060001c6050100f0300b903881d161541c00401c441d031141d00503120000e481840807141d070b0032403911031010079a5903c40601c25134000c000e002100540740303000490300c041180f006003007241c8545401001007011a99881b001c64450480001c000050102d990084003030901001410090b2816070180c0134040120700b01ca480c0a0000c0d0607a0580900b801d03041c0d00e17010044d200d0700144a003803248101329103800310014040c40000e001c201ca801502040c600d08500400c500e81c4000d46c80407046d0b42c005004001201c0d00841034941c44102160700503103075505c401c40d030750541c030510003c554441c6847c4e0340444090580c0d80601d0248003603603420043c80d0300c180d0055503031241c03e0003903460152606001502d28030f480c04021940d0501041942c40449903e80ba0030701400c40c208808011440200c0c0600003801d0540d1210392202092 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 498192832 1250 498191582 498191591
    0x120e03060108150c0f0703020307060b01030506030c060315090a1a01051c0b0406030219230d110105071a06090a050c09190f0f1a0423040b09070819 65
    0x95842d603031620301c1d00340380c0d03a0003181000051030801e103201640e1740c10039010070f031507074814a03890002d40300d6002c104111005850451048001c0d4400c0c402c25100d21009401020100b5003801000760341e0b0401440403c0c80075840c0c000d520a03445d01c004250141415a50204d10201c2034055410f400a9009400b410413000348a90b1581c4000d1403240f501c06114040001064943c1c6000310700a44800e03003003c5d4210301615030685855520085010440d131041c82050141002900c4500c0e40c041c071500d138203501c0041c403031840e000b04030300a2052440301014149030745805019139031b03007000750039803070342a1401854030040003e2410503488540d40481c0c003040801071443d01840c0c074071045c0200c01180e8014000c03c101510001501c082220141141e260a0480d06940708a030303c4944246000320400e01c101c4204038a140305411090340c0a852264031a1401009004100c84520164038552580941c403402030070700e5521881540390090b81300e6a03480c6212b01d0200d40e00038664604200908010380f50 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 498194082 1250 498192832 498192839
    0x80d0b0306060607060b060d050403081006020d0207030204020313050d08041a0103030c030503040302070f080c041a0102030a05071104050c0d150f06110c1017090a1e1e120e030601 79
    0x2004211080168805c0c00020a00d0612001c0f400c54083c081c035034040945440c081c001030541104d101d5104001080081c0d10b440d403191001c07030b1a9000904120b0141e030081009200501d4035401459010390308148a54490340d250315140e1602108600c10004a03009400740024803103201c040803004441001440103030751546e54001c0c0196010480a4108040800403604240c800e020020007800b129110a1449450350800c0d9254043c0080d45e41c816850308180c00000d0282041900e20100160055410b11b44105001e83d4281d104035170448080c41c040d40109441e580b107210713003406500b80f04240c54a410503200c20608480003016140c030356040134001040300c1844055150240c030010b1400d01074a040042da01494044002c0f10350ba4059011030346d00e80c85a034042401801154008003900c4030740c445c542c0c03494075a0541c04025000346040418000c0d80d905a00e0f0351a9100c0c0710342c0302e03542c7c1c00c01c241c104c040b4140e031514802c40b0901c1c02a2280d14405030f0204d13088100f200100d0107404154035 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 498195332 1250 498194082 498194089
    0xf0105060f03070e0a15090503010515040c2705130b1005130806010b0c12160f11041401080c030d0804020d020a15080a0c0f02100522080d0b030606 65
    0x7907101d1004101000000080c4890304c40e0340c5000e80c01070068001c118607600c1c1d600006240e8200c0f01d00741c0014040503070004e498501400344030f0144a62980d6008203210710801d03c07020385007100c9440c09004540304112106034446000150040c21159001035180c10002008154540d6001111141f0305080030907485540e10b0340280380031020303418400d03a0351510488200c0c0009440d803140e002402200000916400000010070340d4405003020380381e649141c114500a0b9024442c90b0702c0fa00e840c11512880020112a00c01e08280d009809066445804600180c00d03964041100704510840c1c0340104021b080401c00e6911001046010b8031104a10080081c0050001800039108141d10348002042d52188181800507205c0501e8124400e02c22040243c8030303c0c8155503488040307181c803044c043c0c00b520030303c03e00c080319000c2d40c0900703e5100201c2c0312001401d0040e0048141801c800c1d018070070548880194001180b10307014a64071400d061600d00112421207840500030f400400400015a9 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 498196582 1250 498195332 498195337
    0xb01080f04061803020703060c0507050d320a03061721070b09060f07020601141207181a04050105010903140106090513021c0b161206030f0302060f010506 68
    0x280c24903060800c0d07a2a0b0418401900d0400201d514035403580803403209140e40803500d035056074001c880500c04100c41103811115032180880c050090742003201e19102d0f40344a0312030380444c2078007503126040140c4650081101c6c0e0030790740f02d44103524200103507000803d605405410300405c0308040120303070025001d40e0035455091800f070924402504102202002c903030401900d171969000618510f2924000c051940d603080c0c20788948a84281140009991500c0001c185040c0c8100390000c1c400481070405201180700e1000c1e1000182c06a00b10104486030b00305854100c2c2000060301040100041088100300c2d518801c01a010350705000040c03080b41d8001d40e00c841121761002c15001d590701c240b401d0a00403c495000a1011420f240910510309031308004103a01a000310341180d06202d0080c0880300554000000800c03000c14000003840c0600c000d1a600303802e10803820102040c040c044291022a107094008a54174142e45051070145641000000c0e84018141843e81c2d155040100144450 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 498197832 1250 498196582 498196591
    0x61018090509060a11090d0f0b04050c090a090302030a0e060d050f0a0c020c0a0b160507120b0108150a1a03030705010905070b0708120604110705010f0e0127020f03030406021f0b0108 80
    0x26150602010108520b00c2d4042c16232a0308002d80c1081828a07241482d00d85441080407440303403580c07601281580c50203205519105525400651528001150076600540c8004601368800b200b40400761406000b401010301c100c0080740c3c111041d2419402e0081103401038052601107500a000203091600e42070f200b00191184000030f551a4992403100029604007004001c14074002c601001030846050020300800074410340d929551b40c3cbe00d0344a9940d5602603000100c0452001c0c5010803140388040d406031640d1051800450702e03010200700030a10350b80c4220703401c603201e039901d400351002c1c024240000e070094821030900500d08000340d140c66015014184500714041446000328070980d41f00d038000e1070b00b00104462191501040d040190081c030103110031410560804401d41e107a00d00c1803082c00d003480001e201c01d059180400391f40c200c0e055081481207802c8118103c0410380341d0ba081010348010501030740200f4400c103082c003071000345a03a20911711001604080440d100c50f82c00842e140d034030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 498199082 1250 498197832 498197839
    0xd030f1103160f17160203070603020f030a05090102040807030311060609040203100e101b02070f06120b030f03030c0403060b0a0f15020c150403020a0e01030b061018090509060a1109 80
    0x218080b0742040400b200700413003410000000050107213046440c00024000300350089003030340c1e043c90780d030a41135050744110034040d01c030030304100000744095a040d8031054100d1540c0f400141044c0d100c0c03030050b16042c0c140d0025400724811074104508d448040221a90000c0140da07060300e0f40c01d165003ca0795039040080c44007906610b030500b915903000100040bc6000126070028030091508000c10385002071700180b1103005000328a03012a0340b4491402e84001c480c0190b4031044040a206031080040a003a01015450b00801307040710f44a440410155004072038501d103040d40e0700d1943c50210100c03088584194007c030a01142001207800190200d4111303940014ad41401209110080b42010301c0380742d4140d4801007081000b560f0160071009002a24401c2c0c80e04407401c1c4e265019154062401d2100030300b480101c0c400240301e400c0041106004181390b00303040c0c0702080b9071603d600399810260003880391187c0da0004c0110281c0700f04071454120381c082100300400d11101c00c1c0c91110740308030f00610b1302 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 498200332 1250 498199082 498199103
    0x43c240e090109060c12050703050603060c0a090906141011030f18100503091209060a0e010207030804030b0a0b040b010806040b120102030a0609060f0f0501030b010e0d030f110316 79
    0x907528429000b01c2d40140c1d00510400c00c225150201418244d038005403c1c040600d04400181c545005e0700c2007900520f401401022030782e94201c1c80807440c0c0c2c09800240100324403c40c00040068150081001400f50b00d2031955503420050140500654014a8a01002511682400c0e0900084101c81007542000b590320f6885040b05000200c1d0402440c15a400001400515074140d03444000f40d806040b2100c150780c00800b034441c01865500500c864182c0c1b2040400c00c0102c110300030000714009172418010f480c1a15542c1d02c40d49960b030050b50003901e5400c03201003000181041d5100d1544c400904980c208811618000002c000d42d40082096005507540c5008026507954000d104039803c2d0118000d540c0c03840d10080c203070041d107417a10480f64414105000860898080b40c44070741516008065141500e01d001c0044000e0021009954103110740c003108101951520032440c01c00500030744505088142c0c0e008000c0805400440b1007030590030600c6240318203214042860b00301a006200d666 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 498201438 1106 498200332 498200341
    0x40203010c02340e0103050c030105160806041e0e0a05160305060c1c18030905190e15090108070f050a14043c240e 51
    0x1440140e003150000d01d900f4500d860602c94100d41c0008407025624114140c144c0c6082e00151001d80003c0c5040c002402c2c00d005039508200484603510300280060002400b142c4090b110b02e01c07454844d44200c41241e0345040c440d1002007040410064195081101940c4400480044980b409582020078480113904542002c81e178014029085503a901c1035101c40b070f0390000090300184882d0321107a6a907070f0040c1c828081541468000340003092400c0c10064801166030703010a114204802204003400038558890b011182150000132040d00ca1081e00c0d0743d21300312458408c6e00142e6610000540c4400026254100c41440e2500d4130f01540316001c1c030081b1090b900464100f8200864101d075030b41000d034800c01c11541000b44208441803c480503100b070040c0c1c10380f0041900c0c8034041142080c481c0c2c2c0b041c4204102945202d06819850300c00c07120700c803240c2c0c2c13245550b040d15040029 = true := by decide +kernel

theorem cover : BRFrame.Cov 498021582 498201438 := by
  have h0 := BRFrame.cov_init 498021582
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498021582 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 498021582 ≤ n) (h2 : n < 498201438) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
