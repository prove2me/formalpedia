-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2666
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:22:57.263981+00:00
-- url     : https://prove2.me/submissions/f08a63da-742e-4026-b32a-f9c486bda0e0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 479316546 ≤ n < 479496402 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 479317796 1250 479316546 479316559
    0x1308010504020d110a210b0903030f01090b010e120304030303050112050a03030f140405010c080105040c1e0c0f05070302040516021c0905031f0e0319030c020106050405040605040c060e 81
    0x143ea440e06011081041542c66014818680200d00d902e25104d259184014181c8944110a800c2c07400c0d56060354042d0802c00180e1050003040074070343e003001c00d6a0548280c04400308140128a0058030790410840d012039101e106260b00b0015544004003030000c40c1d000c0d81e424051079a840a140e440c04082d00e9001c1d049820011303003140442c1c0030750441401d040c00c20b400012001c480d100080140341080e60704442d41e075142c000b10110a82e00c0040c0710701400003210100040410300e05c025142c900c00ea4505c81400304050f03109035041e8040c04003006003540241c41c1072161441490100d45800090108138406ca15100200f1074564444035801a5425642c0050414401511500300c400151010b10b000700440220b000c500d070f03201444004052070b080000c015090f418030030104195804500c410b20154404d00001b00300c1d00444160300c0c82d0700d400d81000a0901c058034402c03030140c085600320329002400c200074041000060307440742d40718034001e0640714141030316404216914865000102c0c0c1c0a403 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 479319046 1250 479317796 479317819
    0xc1506030304150203040b04080a06140c0a0c02060d060806090d090f0605090d061e0e16030b131b050f092e09090506070807030507080c0f1b0102130801050402 70
    0x40b01143c01e9218001240116030409948000c8844c240e8881c0d0000d0100750403c8441c40108400380c050710241c4000341807149014034040180e01054055005014200007078044202c041d501c4440c2101c40100d0b41c48411710106031a48041503840401740c4070349010384501c90009030414410300044003540c5ca050000daa8040c41c2c001c00b00c8150b04103c804507800902034000d000080c9541c0b00d40b12010000c1403d03101210030701c1529100301d607640586460310340c01c01540c1e0300031700c3c0c803000d5a00d040e2030f4850840c407990349525002c07000c20060b014008040020501104e440519210104003c0350800c6904014401c0c0c130380d0502c181b5040c1519554507690744000801486440f6210150841808034041a08540e039040c405080d254429810f440942024090254580c1d00c03811603030344100e0364201030003030b8100080000c011035001045010901c00200d1109603100c18042241c1141c03940c0104290320350120a1014000d5100301d99520304800c050b03500040040043c02030912882d0010202c10502 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 479320296 1250 479319046 479319059
    0x4030906020f030708030603033f150909030f0408013309020a0201020702030307080901140708071704410609060c07030b18070f030506072a080c1506030304 69
    0x542024200c940c2c1400140078540780d207800c40c032b884100c1e01c010041c01e405407940c1e9903512b081500c08003c1c00d04028030203030030004d0125110740c82c0c2170340030f00544810440d41c0e40d034400309065001b43e10181d4145003000400007030a081c1500103000e000000000702e9078440c44030350003a5010281808034292941e00041c100f081c102603a02601c0001c00e0343c000076141003180c0d4002070650340071010458010001082248955a0000c801e4200ea44201c00c0e440c5042e6480d12080124000c1041c0240180718824400405c480c00c2d006440080071075141c400140100d01c4030003111944c605000c400440000b0780c50041030032251220900b0700d40094481458020750800b0700005500c1004140342078400e000b0000005040c0040300780c45180a01c11003040340022005503401d296031a0f0002d240340850071001e101080011802580103c16404c0401001e038043d002044041c122080f92aa1090410308d03403010300c02000028000f00912906a4401d00c100c61003911007a10240c400a8043d8818081070016 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 479321546 1250 479320296 479320313
    0x1212010305060a090b040609030e15030109150308030a09030302120106030207030201050c2b09050d051903060e0c070204060b16020a09140712020405031e1b06030c0901050c120304030906020f0307 86
    0x40e13002b81b8028801e4803519001c00c240e0045420741d0f18400d680080100b200000300d101c0c655103e01094003031582980386460f000351710300002c0c061500381d50f030f1160036504042c003aa0440301458150042615a0742e91810f014000327420003541500907508001c00a0703e0112403404032038030020346082200c0e0390241c0311070b03000c84260820402c441950f0303100d4011000c03a1081208074044e1085035a400c0c4d540d4580050003030701100854442042c141002014020400510400c940c014540784213181c54160600004020f42360765030040302c65040014000c10b450540a28a506260003503400040302944c86410380201d51491000400000c055004102510302c40d903c5c46001c821040701c05401d1a40302c400084c2800010104400c48245d00c000b904941481030103d0040c4411426234049041c0c500300112703001e480024800c0b0444100010856020f0780120b0540f405500940111000403031960704080e515441500d00b0b50200c0d14802e4000340e114400512581c0340c0c11707000d01a5040ca80c0981e01d4090 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 479322796 1250 479321546 479321561
    0x30c090c02010212012606040b010603050c070c0b091e0f06030907230108010914040305160503040b0c0106080706050f07061d010615050702010219051212010305060a090b0406 77
    0x8554013002030341486501c04100c030340030300b514903402d171512129000000780652141071910b40940001c0f04100100d21108596411036407141000715150b91100c903003d000748580070008000101e138040100d00500c0c80c0c005004420000d0f40e000031004404206a44481c0a80d03000542c0203c603420440308508044000c0d641205e014011948059100c6003411501403c0103030498942c004440c0409003582d000b0b103658014510000f04014032049148880e184200041c0041c0500600140044441c020b090003000c00b2508501920780361900c4910600d00c1d03502030b01c0f1040b00d66003060302c0403804140c00f08441080710100c1e140c035860600c48000d401641e8001450070b036907207a990320a994034a4203549509004c08154000015001c3c10110030b00810f01c1055820410810b042c0481e00040c0d07000030722161401d0f10b00101500310413043c40c00c240f80100c1e250604000c5c15000c10050198078140b2900c60580f803084043d070300c541e81c03000240f10440f440002c2c05441720101c0d5020a01169003544142d0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 479324046 1250 479322796 479322821
    0x90804050409030e060403080d05220339060e0303090d11120a0c03030f0501061742010203072a090e10140702032502040903080108010b0a030c09 64
    0x140001200006017071900300354001d941400b400a0241060b41062160960055026082d40c0300c41c0380120f040d200d00341c450100102800401c030004103a11105c204c0d1492075200701c005440c6051040340460300c0e4980e450000b282c0150400c58071200780e02011081d00c3c03254002c4002003038074600780101251046542400b40215009191100b9101c40c42c140c010020381e11140c441e4a0030001a10740182200c405980050341d442c0341800500c129070740100c210b503035400103003080481d81e1a050071107d4038030b59501440005600d0410f6800c0016510180d00540d500742d14220048a4001001a61684941d40d0003c00c5042c0c141c00f5101006170406000c2c040366056500c080340b0644a4403200d044807004400b5042a620055031070300303150542e014054500a2010700c806c450300f4214800ba50700d000d41c40f54000c0198000c1c20480314400c0d0b40140000d00303600104240542c90031410701403d844c10a0041850350b50900c2404d08850803d01c0700441240d1744100501d041c0303858010358500401c0c2450485 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 479325296 1250 479324046 479324057
    0x5060414011d030118111503061302040e04260301180e1005010906080c0f1c0f051f06140d02040c020304030b01030602120609090a06050c070f14010506010309080405040903 76
    0x2802e500c0034842c00c003a041c05000031000380c54a0381020188004003843c2c0c284900241c0d440d81ca81c00c00f900066980080044c0d480798510381210f04050080e02480c1c01c03c1007040743d050200710078000000ea401c00914407401000c20140b0a402d280440c1e48000d0203844001e0740c40a5203402d0710560361380000d40d60118041582c0098440c0750b545400e4820a90151524039100c240521649d02c05210100a00300100e80210b17240882c080418000c00340f0b001c86070300d991078410006080c4441410f030500226848415100280d440d1804105a1501c00d00741c00b420300d01d801c50101e51908041480c20003164002d0407121004825401c11018001011440b000c41c04244400030000300c800d445580a58801c000c003507181e03003221002141d002d500402c1544a0f001c20028000c40700004256125100e40084000c10030b1b41e12000c503041144104440100b51015600d0300b902882032214420315045a40c40090145484000045056500c0e20304c0107002610308200400203403815a0054008601c01d0604 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 479326546 1250 479325296 479325347
    0x608070e0a15020a020102010c050c070b0306040905030a02060403023c1c02030712051e07030915020d08070f0906181203081504020f040306090314130305070506041401 74
    0x5107000380152514030003d03078010340c1803808640c2c082c09448030740e040301d1410b2810301c0814031350700340e030740c4507900c6500d030300410020108140c1d40311a04000421500070f01103a54584046600039902d120448040d0014024a600c0c41c1040c445500c0c803c8a124840501c944450b0402030024005006804441c07028400c040e078220540d0300c0e6198100c0c070303080160003964440c441810700c240704290441d01d04040000030480104419003070740c841c142c1c3c50070325040540c84404da460259010015078026503600040204c4000650750b0009281010010356640c41038503440d03102d42540d81c100010a100007140a0503c00d05c107261182c4100b40d01268850002c030141c0313a640d000980c400c0d107880070a1700001c0305842005520700e4200080741d9207071800d9030300714541616402d101c1d803140a21b000c024003041c0ca0388035450030b0520500300b01501d01404045540d4904070825603102c7c0c80251f11085400e0300440c04005110301d407071016101180d05003201d8141880080004403900203080c0842621518403899 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 479327796 1250 479326546 479326559
    0x50907080109150f06020c0a0816060507081c0209040f050403120e01110307050703090b03011d0402194214070f0501051503010c1d0d02220b0108010608070e0a 70
    0x1a900300070201d86e000703403580315442d038180064881503801c9403885501c422010b4044440c02c860810071a04e040c9003540d200c0942d8134060003544203000694400740360001d03c4000d0001143d0081400c01c00444042202d07030030140b141d000792141120090041507070725140c0c039074800c056040075400c94102000004c000340c0c5110b1405aa0b042580d60310000758001c9805c078105504034081d90042c00d84004011301790761400a0480500c0c01d002110500056840041021502d8a1480c46910718000c41e02e4a03510391038506c0b240003030284001d00e040300f00c94404400900c40280100501b1201505044541e5041c5584141c451803496540e081090030104544408250288a107180d418403500020544c0d0410031003030300d144440041c545100364506000d080c2a0741c0c1254008600490a007c5000d0302d0b81c0042c0042c01c52841080080d4108503003036080816401d900d071080140207680354041205051a10044603000c10900422022980c420b0200318040d0158141e25050003004184c1c80b1440e49608 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 479329046 1250 479327796 479327819
    0xf0e060114040e07031e1103031803060604020403110d03090e040f03081005060a230a030203010e010902210c070f03030e0c0303030c0a0c1b031203050105090708010915 74
    0x207004445400d540300c190061071800d03020304000c032550300b0003c05145081d5200c1501900d512480345000c0300c4061840342c104210718122504002005040e83d844241d00c010f0075241200304802c6510a0013404000b0300503103058030a4406586d040010740886402c013074184a00c0c0040303c1016000d0040b50351002a1032400b1a966500c150302c50480d08843c0301d400e01c3c0c040c10805014150f8205c01406403420702c0303183c65a030181c8540c16514034002940b00c0d066000c0c0b04041c0c15040341030050f2180020442c1c042c68240d0000c41c101c031800c903c003003030503aa6403208100303c1c0500c0d244402c9284040981c3c02c41e0f60612480150040401804945040c0d1640d4603019640034621045002c40c0e202c40d03120b06441d9050150081203001a8061891498207648a03102071143ca186d010600101141200501010140041c1243c0b400c0d540c09001d252641031048103c00c4c40c1c211200003074104030000c00c8a05014003c54001c450545a8240c0782e42012051800740c45111060032030b540341c0c00d02c000b44024848 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 479330296 1250 479329046 479329049
    0x150b0906090d1b03110409170d1b110624102d08070206040b011502030c01050414060c0f04030b04030507020406090e16080607051b011a040c020c090a0f0e0601 70
    0x5921400f10b9a1652406a403150901c000803442680742004150218039a031300740100c1a0b040701c1085a551065040090041c40c0340d40026221060120760030a0042e000050209030b002000212401e075542d001c171401d541d044014528801c5030f110080d222007800c010b60700d4142040c0c642048610510030035015182c80031400448181c54030b0490200c0040c42d042085c41d07410a82d144050100d130324054a9a84c0404018412822018074040702510725920a1040d5208025010001d010380e0626080c610000e00750b00c000100c45004003408a0001501002120706116150021508140ca1521480318080005100b9000d1050405c046801691180310702409030440a800068041007421a5460100d41d141044112243d0a005000010001904030b034440100e00d0400c2c1c0d10502210381c0000d24043c0c00e4801105c0d82001d0a00e14120010b90700c800954005036000c1001406802007240c0d5800d847e24681d07042009400805c1e00c81d06c0380e401c810050342031030318007240300445000c61520b0a40d09 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 479331546 1250 479330296 479330333
    0x102190f080a090b0c01020a3e0304031509020102060919170412030306030506071103120901020c0f0a12081911190507111005030a0e0c100e0103150b0906090d 70
    0x5890080c41c0c0c10005450203c0207280c013144090701271101c2c4030640f09030041001f07244c02d00ca881c0f9800c4000c0400845018648c444010342c3d4407480d642c149130203080c500400302d015010b104000f9400070300016000d002040b6030112424022035a8640c06441008060500f00d5035404101c0428141004034148264a10a5500044151031403c165040c1b480152101042003003040009050b903a00009030703490001c181d080320f01541c4880010398024816040390190306e0040b412031240c040b6021500c001101c0c0650311000c0030b0401340004840d81081168104058900e0700f80042ca180340c20b600c0024420307042a03016103401d49880004602c1210b001c04280010000543c190420030000560100c0032020f855504a0a00c0d1403005003c5020003089107000c180c0e00c10740d12019441c100300d0280500030240046603119024000280615030240c1c090f80400d00341118410504140202c3d00304079400800041e081500480400c40035511140209511480300000540407946964640d00031341038 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 479332796 1250 479331546 479331551
    0x10e09010806090c030d140d0f11130509160c030c020306090c0a09060305030702130f02031e070c0506190f0c03021b010c0f03111c0b0102190f080a090b0c01 69
    0x14242265840c4c00514440580207070040310070010401e420162103602d101b50000b07141d48803602070135110000d00709440306050380c3d4101101c1d5030300046500c3c01800400010f507008840c0d543c9503014040c280002307542951000c0f20759600305039a14401c00c240000613209140c880c01e40c51482d000685840300a54140059410100300c0402903c1c0c40800d9000a00c0c68410901060749542ca40039241c1c018610041e0040f224040041841007196001a0b1000640c640440d26402c03c11020440582d0905040c40d05002460120720f480b4020f440e4400c40e10350041c02400c0e15500c1550700c2500e41400a00501d0305903c1e800e140c1103501d124051011a0062030707800503102c3d80900b200710344250305014043e0090340b41c400e03025086980080c440c103c40c9045e003008200b107500704501c0708440c41080345030305500b1044681d1090305403281d000100307803400903400c480ca02c40e500380c200160500e481c84020403c0508040d41000603011001604034000e43d4148940203a03a1803402036240d41c800031003101c03d47d5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 479334046 1250 479332796 479332801
    0x504050f01110a030e2407061107051f05060d0b04060209060d0203150316241413060e0f0d02100201060f030302061006031107172b05010b031b0702010e09010806 71
    0x100080300742120048203c10702c03d06c0d010303900c40a09a00c614a00580039036202c031020078146014408682d940d60740101103c00c06000510796545482c03420500c081c1460a003000b188c25864501a80485d181e04075400b010991259604c10000390321007a0b149070800c0d000c2c0108141749a0b50b10145104a550f101c084d11160703001c80c105130030b003842c80c00c008807004a0008107010107c41c01d02403841d10503480e040e8240d99100044250750f41d0520b14810841c0800c0041e90141101c945a01041110300d55180c4e4040700d0b1000d8100711981d0f58045d14540c01c0405880b03510050710f0503188425815a9600000401e961500c030f1008501034030340c0040d0b0241e40000c00b4401160500742c0714100401c110318040114000807840380c500c51040c02d40107005805a4020350420000359801c980d2380e5100303020703002c0c1703540c10b40342e03807041061030000c43d110166140400009108450004880c03158850001d03242440810210006464114080580c100b05400d25044d2064403001510350180008400030007903031 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 479335296 1250 479334046 479334049
    0xe010b130209090606121803040302120c10020f0d0e120607020703030f0c2004110d1d0c0a17070e0c030402040e0c01080106211506140306010504050f01110a030e 71
    0xb00743c0908058040c0d00100f000394501c034440807419070441c1090071090b1135500c1d0340002034610700841e00065404030991604100d180000502490840411b6410341e004042403141681c50344a88000d080380740e0406d2190000300c600c1410396820000b80180020700d030f00e02500321180b82c01d00442d84203015921448080c41807540220140d106c442062403c2032045c241942c411403814804100345000d00303004a080c0030944e4aa4001200707407005210170b40d03207843d4140e000c00050010200500311015403541c42c0710040b04003149201000314068051000c0a140c81151041c6104110790300195009042d004a81c460003504500e016080304500282c41c0d0605004100803a0316050f000074096204c0c80c900c01d07003070360003140c8641102c1081c141060702100d940c04034907400390681030303e55000d494914a810344400221708c0380c0590301c265680c604211083e03c1d01d40010b203c1681c140c1d020400a0000300724034030b40340e84080000034040c5030002d600785540000e18900080c0600840200b0000d10211000703 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 479336546 1250 479335296 479335309
    0x12120a050103020604051c050d030b13060e0c0306130515040e0d0f0318050718140f06040207060902031f0b0a0e040602180306010806072d030e010b130209 68
    0x4464058000c100a524550016003248240e00c5402d0080c400f13402c2c0c0c804182c01076041c2c909081e40050a030f07030240248020040091507050120741c860380d1203010410304030500d0b204103000c0d10743c0c04840c030425403241c11000d039140d00300805103075201240788021100c0f284130b4020035006020184815000164402c200820303a81ca4812880305039202c201601e0a4542c0211070b84003030380040c240010701000504200344018030110300a45144102500020044140501c01d100701500600c00c20110981c0c502d611106001a582440c0c60b02030700780030a5240c40c00d9401014090301c40c26000504500640c0443e08016201c1002003d42020100381d411070000f500401c2003009045500b24020350400c04910120040904003402d0a03501040c2e5800400c0c92107401c60010900074100c07080c943c4d450042ca580c81d4401c44440000036540e0784c42c0031904040010b0042807034405501c541d20b50400e42d5040340108800600e004156407903442e0070455445001003034202c900c1a0070056514030b0800288a207 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 479337796 1250 479336546 479336551
    0x71a131403070b1903051b0a1e0504030b0f060303130b091f140d14010803071101020d05030a051902033d03020d06090b0a090203190506150a03051212 66
    0x3042d0100300029800960207405911486829080c0003490b5111100f444101000201c0c07d414000300c0060320440d102e801004010404090183d00460612101001c4506001d0381c407004085044a2011907411050217103520350103040a0112410030503a90b17100c00102c0520f030300c40361041c2c00001d100401c0382031001150761940c50b61030410b15403141c0103200401541815852a642801c00b0800002400c455007000d8214000c1034108041941c5420284d82c0300d5000403412540001d035044103094a500205580442e501a070b142e50b0b0542ea600342054000d820010050503118100414242140b441da1003d103015030a605103202d12001925080c182c1c8080c1058024014005c060001e41041130050104040e05e038113855400d54094030313240c203001602c1c0021004103c88104010400014130035400044201d00890444030100c469042a02a90361171040c003900907003154002a10f04988110082d001410241403c8903051b6a40c03500c82c2030001d4001503605c021070004103110204044c040454 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 479339046 1250 479337796 479337809
    0x901090504111f120b060c1e01090210140910120608064b1b030708040803130f06050a0501061409090403030f020c0601030c120203071a13140307 64
    0x103031010007803151000f4071046003a03000100002c0360000c81d80b41895070041240110b02800141e05c0c0ca04408490740c4031000c909011420900840c02c242c51280c050040c281d946402a040c0350103103d04000466807141c141c051a0306803681009804e507980c88020070101030010781d0307489030f40c0541d8040e254001e07204181c0c06516994000d4040c4003503004c1d0b1500117281841c03e400110407a140301c0e031000301240c59541d0002e070101e02c0d6684180c5010018003190f44500b00c55075010521118550818409003c207a51650010b201c0400050008010100035034004021801541c05034105507545502d8401c900c0c82112243c0d01c5030144214980e0314061a800b4180d01d0070708c9204580c014180541e540204030b030705886052424041070900d80a9031003c0321443e140107084d9a0fa8255a01d03055031071000780b20803070384810003400002d0101d43c442188050310f0b0f401406411000c0c40c0462509220855100f44c0111090800c80f410160300302c024080000c2000c48150340812015504040c1040101c2d4000b1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 479340296 1250 479339046 479339059
    0x601081903081317030703020901020d050a05072a260601080a06110405100e1005180d15241d0f19060b0d11040f0b07060b090109050411 60
    0x18002a04030040642c04240320a0303030540b4010b41d003002c02203142c9400074403403901000011b12024a505030000c0483c90401e03000c50304481a00c2d40200e0700b5114550a6000207a0140200d00004a01101984c52045481c1829106040d50002d440c102e0b0240e500003c049440c41c2c00001064201c0004000c50784030102c080d04d19503140001181d210f00015000610131035071120410510000c030740544002c5d010107044241484240c2d20080e090450a03a400d502c034114880d85d408007644640210748068150300c0b00702d200703003803000300380855030b200f6803400c880301881e0314500f180907042c501c6a149441c0c1d41a2600c010300040814030300310540c403900040307102880c16000c2c1d5081c5406121581d0414600e03694840d60355106000100c0925081c1c40e1014814108480001c488948078083d1005085103001001441e558425a502034415889484240c011a170003c00202d0b0104004e0300500c0d01918000c106030090500154419009801002100b5564814042481400c00ba0b01c0030b12181034409 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 479341546 1250 479340296 479340343
    0xa03060f12140a0b010e0916180906020408150121050a02010c02010e1f1701050a05010804020d0609080403060f0b210f0111030619030809040903030b12060108 70
    0x18080311030010400b0300000c00250808140500401c00f81e0071440d042024a942540c440796501e82c610b0040c0c80d07000d002e01c100132006852420200b914003c6480e08203682040d241460609009042c0741013040d50344590a22000903040010b01c2840040300590340075241b1507050400b07451030b0451a05005c1c841c005203100e00e40004070006540758010390242010f54204069100480b044c1203c046070a8100100c18891940003640d001100d400b408540c40344d5805001150800f51121004d1140d56400f40710301604125550159290f65002400a0810502d210b0340d030f02c03a4019903100000807600b45500203410014000c03d8412040d480c2101d0b0b000748010301d00c10b40000e000d1390014a005ca1105d0205090981c003107000c0083d000c00045a4000380a280402448560076401c119001402405c1c07245075503a00951075038841c800c0da03030b00100c1d05051503404428000100130070801102456035408440c00d00c0d039101d180300c00094407410001e141a40c1001d80040c00c205140101c0b920b013803640240c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 479342796 1250 479341546 479341559
    0x13121e05060112020f1003050709060e01020a0204050a1b0e0f0604181a030d0306050a06050a0801061404120b100b03130b0405030906071a06011806050d0b030706050a03060f 76
    0xd009045900f10301c12a1141c640ea40000745070202d040c90f0541c1c2c0035a40450039101c440e095040144078110700e450b40714005940d00707801c0d1a804811012280182c001c010f020005107056885907400a2509400281c20080703442c203200e4421900c0c00c14400310b040654a00f040c1c2c5401044c0300e0440c84283d41903401d00c3d01c0e10b0310131480392007444001d00d0041e889841c052006240c400c174080c01c03520000c0465038a0304403498090010b0200d806428098050603901007825409501103076421007540d90703503030700c26868504211034030084006030800c900c03020800010b9112030b901c5244c00c520301580c1181a14100340c1070140c0700079810350140031810024000c105800300c0d900007860030035403c0724498015540780d290250461007407804955000001007200424401814100041c004054001410030748171003005640030354400800c59250003500105000c114896800b070729500342120390100b45800390781c001034249409a00705000051000c40e506007142e0f0704d80200c41c01070107000880610a406d226 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 479344046 1250 479342796 479342803
    0x312020f071509060e03280606050f100813050d0809010513050309121f0b030d020f1c18090507020706140a08070504030605010303080105100206270313121e05 70
    0xc14135061141c01181e040c0c1c9514144121540800e02e00d50711100304100c0c404007045c018a125094802a00c2d1480205a84c24083c00b100001c0c0e40003130045051002d040c030101c40540005240886041e5014040b60010b8070422102c03000d03040701c6d1100c107500c2c40c003818401c3c2190802081640380d012038030004000b086011045502e0f50030b00b175a0307003101c440c000140185040101903001d0143c0da0720009490011000ba030081103d01d10485c280c0302c0d03510301d0500072a6a111104e040c01510382001c00c17040e00210195220b2104c1d18170070b081440c940d0809480301e804022083c5d000569143e01c5404008800d5030510590001e090b41d414a403240501d9440000301170302a48040009000410340480d00190090056400843e0301903400e0029686a150041c940394081c80b585001d501c040350324483e581c1c004104148159851010440d1005c400c0901c61000010340d000480180420031280380c1c101d4040140750003900c00d1001446142903246041c14031322442d5600c040c25040203849503030002c0d00c0030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 479345296 1250 479344046 479344049
    0x41509020f01050d0b0909010f0501050306190b150c100608070b0304060e0109080d06030507050103061d250c2a0e0c04090504030f110f030904150312020f071509 71
    0xa1920315203640c48441113a00400042c0c150301d600100200401c0340c02841508680300c441c031040b03000d1046903a6441456510601500d0042c81c07075880401d114074021003036200e0140460000c0c12240d4224220040740341d5640321141854030f603007000c0d01440c84024a8015840100410702c024034045142100c0c145460201070300052544c0e46602c07800c030000340c09400100c90550070020341baa40301e004105900041645100c225103030701824000103081d40c0244981401c03074200c0305c020782040c14003c10800552400401045d848070b004544806a102c00e4030f052249090f20781c5031a00c07800c825003016010340c10051b8103019141c040da0724598808c2c0c226400302c0125a144248aa45916402c50030306942c020364000071310b40e9203070000b00800c0c1584244005415021038a0710348811800c4121503031941e540e0301d050030890340200007004030740c149503000f1505014192401a5060340300d075140b8041c5803480c2c04082c01640103141d090345042040c0701c28401007010300900010401000b83c0580307551002d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 479346546 1250 479345296 479345299
    0x30e010204090c08100501091805042904030905090121020a091503050c0d0f1202031e12070311030c1606060609061701050307060f03240602150603120714060f041509020f 75
    0x4420220b802c0010080c59130582104108051331200540842d04809040495040d0005001000c0024260501300e113580e043e140c1d00a504002d881d031680a1700c0e0540315030641242c00c003201c40400a82482a82306040904c000007001000c0070789181000c0b441e242140d0041c0e80b04690718150980014902009910a00d82c005200b8510110b0b070070081c0e086000c0c070211240b802481003107032030b85880020010084c1c5081700d18458095110544102c1c102c2e155400d01c1110a80c00308040f4000e489006d002c2c08032030602204e905402d40d15944d800041d50041c0d4004000719065407420721041c4e17000780d1929900103221548110a6151000183e81d4107154407070181401881030140414911030303082001580110340c026050040e4805036901c8103001d0384188001405514002e1803820108074005014483c000d0060821f5203042c0300180d5582d000701c0089800c60b200030b001c12440f403c2031241901c190440c4114029602d494107101030000b10000001c145903107000b0741007005a5410f00030982c803110 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 479347796 1250 479346546 479346551
    0x906030a11190207060f020c0306070509030106030615050f181302010302070614100b07030203180102070302030a060504110a1d150a0e0103140304060807030e010204090c081005010918 81
    0x2140c401c0100144240d220309048a1029655140c8040e000920001201c5084d136524070510710982040707844460410a165050704840c01090b8500d22520241048a90040c000601642e49640e800100c511700b440c0111903944c00e020810451030030a41d020801d0030180c50b02903840344a420040340e0904006c103c90b0f01c03030129030121002d6901c01e0781994010303a4010340800c5010501150344080749c40c110f5101301e030910b039540081808032445d025105420781c541c0080d410901c100604054001d13031090340504500c588000000540d030100150080c030b41c040e40b0002507500b4181000c069100c090303003032280609038a010070000c030035940c82d400c004400d0f00c0020b8034460303c920000300ca4900080f0000740d0b201c01441d00c041202a9507034045412a840350000740c1c0714040c0035070706a03101d009503c41d420101d4070602c00215a02d000c1d401100b07506003404001442c080c3c07603101c140101d9000c40e079858002503c9804011668000c00e4038100501400d0070709081071b52410340b481104041c403501da542c0c101e8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 479349046 1250 479347796 479347811
    0xc08070c0515030603060a1811061204150506010c030e0418061a0315060901150207240e041401060c14010930020d0305150907051e0906030a 62
    0x1100c00381030005018024182070622000402d00a640d40050351024460700859020943d0b1020f030303103c1c0340780301c0c10842c000d00c480d5841e980356954000d0300300103000e0300000100b10940104c51708405440c0320b244500c0181c1e2812031070013031407801c44900403d040e0600000c1c00c04040826044240300126010840d404a8400c103102c00524070040745c280000c1c03d0340d040c0080da01180404c3d12021050000a8040300d000814998035511070b600140c7c0c50607002009400140403101d1000d140d03014096190045584059036102c04a820700403405002d01c0524224084d1400c19900c07442c1c0b0365003102d040b50103001c4503540c1d481184003008184608170511264035003030410000c882080118518002c00200718140c0107003081d2450040002c10000070f50361803081c03003001e80b481219608002ca0154000c040c1001c0301c910507401058003070900c2742c8084039951500b50301d50380c944000784a42e40d680d55042e2142c02c40d5168940d80c2590342111401084c00f03202a4056488050680c0d9202c51322500108400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 479350296 1250 479349046 479349053
    0xf1b0b0c102a020606030c06071101030903050f0c0a020a0801200a020c0a0807141c02010e0112090c03060e01110327060a060513110304060e070f030309090b03060402010c0807 77
    0xc10109008246000c0b24040600050300400c180c0e20861080e4181c52489044c1002c0010300d2141c030304020a281d40c414190301255100343c0c00310500510909181c3c0c6404081c1c1440f142a4010540586165010006443c11414122110383c02080110003e0048000c50443c001d000c8003032488010920354042080541e4070b100b00550a4100d0014000c407080c951140e480c0340d25a05107001d10f09001401c060f5240f00c03402d1041340d2011282044010b580b403a07140394011180d18912801c0f550401c51803640c12400e81d62280310b815a171601c60020801518a145811815203500044890740c0b6450070190084d403680c401d0840b54090b5042c80300000100c6008142d004588040a001c00c2900c154020411002816440081912821984d45410b0000d8441d0340b0103407103030050703070045806080c0041400074005030030502c0b4044140d000d84080c1e0742c480d030001403404800d50081c1d00080880e2400c02a03175425100d1040b040f04181e01402151405400207030201021000051405400013a40c8062 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 479351546 1250 479350296 479350331
    0x503091c1a062404050306070207030807171902030307021e071802070501050106180f060c0605090109051b1e010206010509070e03061320090c0702010302070f1b0b0c10 74
    0x140100c0b485800c0000702c10546503500c2d80090060a000b40301c1d07000401e5046000080ad802282d90040c0d0542c90300102d50742c3c0000c1c072a085071002041040510084600748003401c03401d0f1448006a00454807442c2c085030017468459103410340745c1030a021214103840048040f130b410302a90380b0fa80a000c0124400d48c3c0301d20083c441c0c10b402501d15403900300042500b6500100000001007030b806022061600c030f1030f260f00055001d01c61100803c03104080000002c285800040c3e005a11500010351036040761143c9041c004090b0b40c049600b404400502498a07007020000d901c007410012400120b1a042c001075650b50040c020144540300302000a42c8c024861040a1801c0c40080e00741c80050400640d015680c1c0780400044842c600400310903d4a1100c5000040c8541c00040c0200f025442c0c0f80c2c1c10070b5150340020700c140c6c1055000c22864000c5104480392406d1944114052440c22075080391b8680e1a140365000f40621400402c0200058000060300345100c15140400141018004c91075101 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 479352796 1250 479351546 479351569
    0xf010b0a03020a110601080a230613020f0301060905180c130926030402011d0102060103030e150313110306010303050d2a03051009020a0915020a020d0503091c1a06 72
    0x400d4814170002054180d0080b40c8004454826040090080040301c500104010300c0f40050215900410004000903c4559031803109800541503c8103c0901c201013800d4a6080c0c10107940592a070701031081041c0c0c0642d880800703004401c090100c1201c1c40f00010080d0483c10100c1001c0ca45607130b600f00a04c005048000b024494003107004a2030120010301981c80e400803141603010809444101340091010342848010040c140c0c0075022580c25981c081c0c5480300701c07515058005003075448881105080c580118041c03400c1405e580c262034820701d00780c40301180280301d0034001e401130001080082d0b0884151424507400100c045049101030360844058444528031480d0b110120360203500d2a80c160b88554004c040c2c02c10510030080d114100c11069200301000b103000111120805c2224503180381e550703402080188162003814031a40c00050b80307030541040c1035a00350400200304181d4a00043c9031b42c4803440343d070f41080c0c45032401c3d00d4803113048e101d070941180011a01d000080d2907035603d00361200c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 479354046 1250 479352796 479352827
    0x406091403031302011d0319080d0606270513050604150902120603010b030a03050c07050901060f0305010905070518030c100908190b011a0c011b0201050f010b0a03020a 74
    0x292203250100d0700c0c0b81030a10f5400c0030781c0413650740740341140e0303a0201e821041042c0c40060002c0c801001030152035101c4130140b40b03080d00d040005200e1030505110034002d110041c51580c0d00c0c1c042030000e90706000903603248103d0625019101074010409500d510001603802d004010b80060070ba500c007004140a80840720f03803011b003901da1100c00b0503440c01d10350190160800d0b1903c064000d030b8581d000d041c00c0b0340c1c050081319850340c40010814002032181000300302c4899210107992403982d868011400c024004e030042d80104040c0b403900c40c1259411b00c0b0f013600501d80d1241c01d05c00c508000a01500603c110a007109800c80001151030068a0400c880d450310500981188051859410010900001703400360640b00d00600c1420070000703e0b445001e801403a048400ea40003a440c05012160501800b145100144400d0221036080d590a100d50407070f038011041c0308500d000031000024211040100300c3d040001a00e001840743c081d500c0c00303485410540e800c0040e40c1e04c02102041d0b8a4030180b48102 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 479355296 1250 479354046 479354053
    0x70c060606030f0f0c2007090e07051f0504090f2301051206090c01030504050a050a060f05250e0a0b0c030a170705220b070516060504080604060914 65
    0x9105602d903001c00c00200030050300300070b4800c10482c59030540c3c1515540780b00061010003001e041d08802c0080c11000303582e02089500c1c2035a41c0780700c0780584241903565000c80c1c1103a4010462401c0c02503000c0f1901403203c8801c00b050980c91006012800f450060340b0394240d40c0e000f01444c001e603070350202ca64071a11410350400083d0a210000a1503024012240220f03240c2c0d880707a4114500194950052070b0141c007500c0c201440900442c010300c0014400e44280c824080c140c008a0f42c10700c1590f94060086001080441200724441d094400240030b12242e800d000164070350181d451085058891b8451814403241c0b0100b50009101002c5a00316018000e000250510980000001001151001c0d00d37510880d09840c442e0720811141100d010340030620402c03c244483c2d810046800f80b11412681c0e001e10a9140c00509440b034200e0001201c07258482d00803401c1411055004000900301840c003d46000c2c01c1440762511100c010340b00902480d129200581084408a0096480c2030420300301c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 479356546 1250 479355296 479355299
    0x16030519030c1e02030106050103150902030c090904050d170f060415051c02040c020a0c1503020f030c09041406030a0b090f031923030f040302100218010e03060702060f070c0606 78
    0x10f040c0c4019400200d101c1d40c64680b0005a5502900130f8030720b44c5103500e1407905140d14001d0000085d40c00205141240f9404211082d03040d40e5992450380124060002411031600030a0050101c490303018076607840d0f505040402030104046030025038400e10594001c6404228011011f484c5605500015403045901e03142203143c020302704030000d407513000701d40c244000c02d207145050761281c80e00c0d40003900312242c45405214509101c01c04010281480c80e0040ca44074101c1d07141d05c80c54005541b0317104060030010300441342d46480e0007403140301d003a4042e1310200b5042410002ea83c80000f41001054851020001414140184080c0500d1a80d40c0c081d295200718441842d403c02800380041400b140034414203005c190701c04100300701c001103d5680245943c4030354420259040004104500b10721031b203440c4192804003030000d041c03d1300f42c7d5180c085810110000250448141506042c0268005401c02440035800074282da005400c0103804821900c9035141200d8034005144064429800c0060 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 479357796 1250 479356546 479356583
    0x7020d050d0203091302131a0903010504082125090e01151416060b191401030e06130f080c0313091802030a060c12150816030519030c 59
    0xb88250407049600701080c001c041c52200407801a1f03250400680480001846009000b21258451110009916041a43c440c3c002807e50380200c5080324105c0c004107000c050703a41403041a010300815031a91520782d141484050300d001c180b14004140390b0714800301780a141400b81000d41c003e0003100383c2804440da190168003d4030068841900c1c000750454900301b403405920801c1d03440345503400c3d441d10843d14407502c2e5100a0000001140d91040300711661082d050514506000100048000e445c0e8900101001500304c1d440351000410039003080c410030a100e040310207000c3e800c1e68415043c0c1d00c40c68003400c101801d03014104125145100020390801c0300320000c55840704450440400340036882e00c9905500445c910100004e4040e840b40c200c0400103041070300302c00b05001c1c80b8034003030030411020150582a5101500b000b0904010354805202501c0f0034009a142d0620030303c0c68800c4e00d0b00d10741c0e40f03680d251401c003550150085564000420188918000360005800c070760f103007818005009 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 479359046 1250 479357796 479357803
    0x5010609020c16080705090c040510021b0d03080a020f040b0a090305210304140f0109030306031b050d0f03140a270b04120c1703030f100f0b07020d050d02 68
    0x2c1c281d00e41e0301c10164014910802e1080c80002c3c0c9055001509143d8607000910080c4180580801c41004040c031011510780ca59a0700003c20311610ba0041c090907c030640a12007030361100301e0306802007940e0201e207000700b82c00c0340c508d680042c0941001070740e4940c100007100160081d0740002207d000000f4203505120303230011091007680d0140c41607400e10301222804049204e041c06007840526000d00026002c28801c101d040c40710000c8100782d910300425915042d08403210040200c010035601c0000b402403103034542c040f82e16010510f0348504281d090000003200e4001900004005000c485101803c0502c11250035501c0c0c4000011143c448800d0300000d03203103d00b28642c194414032540c0c181111104020303545c60071039103440e030361629141c101070540c07400640300c2d40c003582c80390108170000881c4001c0b41c02064a507008040a0760722410043c20001030380358003600e003400440da21101407103164a0710004800719026640e4031079035401617101080d0521290080944a4003400400c0403100b40c010 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 479360296 1250 479359046 479359057
    0x50a0c06022a0c040504020f01030b04060314101d1c0509061315030b010f03110408060c09010206012c15030706080108010e07081504080f0c011509051b0d02070501060902 75
    0x1081d28101d1000f030092104449040b20b029601030000942000c80d540a81c1c0300c401000c802403c003107401600c03074442c407003c0303000001030100c03540c40b8180c80352482c02644509107200380d1031815900100103821036541e644070786200001142010250780c028081c0120201c600700e80000d006585c4981d918030b0350300180c0e00d1921a24003100c140104100038127105c0e01ca421000c2c10142c403030610b5507240c0001200140380c03018136900410010800443e0122040100a02ca10908092640d403131010324002814403106a00c1410b44030090b644800341415130303207a0340404d10111604151a940e807002404240c0f858000c905406000380d00020481580c8100f03800d0590340483c00030310802c0c01030344480355079541a206101ca0307a0031481c2d950302e404000009864025010321411400c19000c94000c08140e442a0603215984e9590720143d0500c44d15510284000d000046007000b2a00e0500218a906000d03c01d10411411000900c201064a1541515800c40d00040200f10f0070f0307182e80e0900000e40c8207 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 479361546 1250 479360296 479360377
    0x21070b040f0605160803151809010e0d140a1b050706020d0c08030109110708040e0609010608041214130f030b01090209030709020c070302100c060c050901050a0c0602 73
    0x90003004964940220200c0b024290548215034400044d41c41301d65a40d00003500345a2980211030004c0320a80e68160f040d112040c06501640150404a020508440104c0d880e00f070b540d001004210780755904059484e80e894441017a1035522680d196080fa0b0320003480101c820215403d4002a051120006058094030700603001c60743c40c004a24000c0e141090740c420700811000c4100010f10000c6a603400150000c4900c4c000e80341860800c7d03031003616a4105030450000e02d0f07502d4007001050300e007101d0054014001030400b89802d04260312407091000100984030103200d20018201d454243c2c0301300f144c04840070360905c2a012074841041c5408100f1510055540320780d50000898100502e20032124080d030000e0040c0910741c542820400030b5008020158647d001d130410000158071120201007606460f680c40418101c8649400c20464208540010401c4810702624405980100c12103134400f5441c1080c480040301e9281100c080d1113003418204501c2c05034203010500200e121420700c0469203 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 479362796 1250 479361546 479361569
    0x31509051902030c041806031a040605070516020415090c270b030726040f0201020613020102120c10110304150b010203090922150b01090305070521070b04 68
    0x30049004002c0c2e00082e511040a20400c02080116034040084c050031071044040103e50346a507a144c0c910806000752043c480d2000304000c02c4200035051083e282e00c0b0456041031824501642c04c801c21428072001c0007401540e41c3d041c01c3c10707030030220740400c001054425828041c2e03c0c54844002c00007208039401014000402500c06210341030340004505507800404281d08694450714211144402c1d0700c0303501c0d10019040d00c82032842840504080c8124050131050700c0050f2a403000a20b042002400d00320400070103903603030f00180c1e8041280f400300b802c11211191030f010320040c003034106901c0486800c4900c0c9400740c0e0107403a001000c050f61040b8000c84000c2e65901a000d88841904c50507106c080c01030300b0400c10a4007914200080c41e4000ca00b000029410540594141a01c50007191040d90300320300c1000841c8400d81103014058203482e081c42e00460003851641d5407035850010b0f0240a20400c00c2c80b00080c52129090940c02001d0001411600e1069580c00c101009511a005076181ca51 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 479364046 1250 479362796 479362831
    0x207060e0603060303030417070609060b010f05130501110c030f0a0311030c060f100816140d0506040b0a090209040b070807050a0f0c020f04020f19020607170703150905 74
    0x50401d09983c81090090061031959489507140f04441c550701968107865641400048041081d07480391910030ae108450000b8190000070001d450241d0607ca9001080010401740064a81d4140321600320b0320282080701d14a07444024440c10040f401c503130710b85c141c0b2403004582c852000020301e45032028001d403142d00c41040782d24100d940300e100324030500400742e00880101d10a5440814155400204104840304103901d0b90703007950a14034408054144101050003d02c40b544180a1201e484c80b003c89254032281480d50341c8580f0342c10000d00c00b40c4031080740c10000d04078402c83d800400c15140e0041c43d419680c90980351a1a898009681200000781d402c4000361442d400741084072030103003103522941d4018402c040c0484a10b01030352000c98200d4005030742001b10303856600107005001c4101c141980c0f21541d010034182500281c4510004542c0300030181700106812007003021100301c180c1900c4590b0390b541c0906801809441003058030001040c10001170400142e8001c034020021a016041d209 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 479365296 1250 479364046 479364049
    0x40914061c030813020102120403261305130e0708030a110a0b0613200405010e03031326070605030402040e0d050901030e0114040f0b010b18210105070207060e 70
    0x20000307184014007242c46100850030309100d41c00441d0550b80305104480c01c00081c0306030072804d5007142d4000c58a04a4032881614104910228160010280c1c1d911a04000e41e002c0400b807011130f14810207002300c40c060342522548009402003019210301030704940c4c2581d5910b030700302d03035950000088e20002004042000d49440c40421314800480e00300c0090fa60076180e03107041103004190250b80701203080d0b5611040400c059405000d00641000c1c110380c60b100c903e844005400040c060040074401d4000704100350480e80d2a01c0e807603003626050072450000174014041000308000310300c80c0c82078030300c00c0d120b00040b819403000086200380c1c400c1c2c400303000d01a610b10206907180c9100001002042090008011a510981c8891001a00310002060703203070b5002c3c3d2038000d0710429182601d800c1da220711a0400e0051540c0303c18010b00c56000ca403890183d08224014000540b52426442070040c213491940b4002e6024102d281810b2001c020015414054006075030b60034180b0580380460808080d100d0386 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 479366546 1250 479365296 479365339
    0x71e09062405030907031202010e101d01050f0705030603190507090b09040b04080a020a0c030507060f0206091f0603081317010209010822080403030302180a120b040804091406 77
    0x941d20301070017003111600350f0b0344000d0300d800c03070243d03130f0741150360300c2d82d50980c101010492031215400d00d54002403805c419514a003200c140c0244050800d0381890140b0a07807210021246a11201d0740c5441c0b600c030b0303c0340c100090030114140b01401070101e603030710b6520602c000408c0000450f403505c1410001440d8990501030310078002c803400350020421400040124110718010000f00a462054400d5041c07070303503203441c201c0e8180d401c15607880d13002c000184085c3da0840e5500701d09610305e000400040c60481801d0341d840d4a0a54180d130400700c600352456900001d03070003250242d40d000ba070b0301d52113075161303540150a28000d12498030b1180c0104206002024180b08079401c002c03069480305001d65650b403000d14165950002c00910700340440c105004540d0718809480910b110340e070f001d6a1603600401040d03449903840e98491003007103580b80400110500c1006452416800400100c0c2c0382c0d42c3c0c6c01c280b040c0d0300499101120407410400070048c0c51880040e40f42c0300e950112600d4107164603031100302a0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 479367796 1250 479366546 479366551
    0xb0c0d1a0d12050c030a050c010f0605091302060409020a030c0e041a091f031a0919140708062d0c1b030403021e040506010c0302071e0906240503 64
    0x4018410110400100d08914442c8032001400d090040c5400f0030046001d01e11b90041e191800002c2020641d440400350a009045150b90244424001103086c0780c001114a00040d2104641b4404220700d0011501d03210251170040082a0045480d8444980b0107009088076030503040015200b0030040c0c420313281512a84501500700580a400c460341c05c002c1c0701d07002034054541c401060300400c52904c600100e00c1e5003030141d8425502a01055000b03480d0020300c1801911404084d008420040d54003010713850045001a00b01c400b00070074104081181d405c0400b01d40140c0110f0169030100144010b070040501d00b10440e144568014002880c89522860415180f00d0a90042081603000580c0040b100c0b803a901840c000381c1c0d192a64a600203a900c007203414039002c000c50b034500c0a18849c9417600c2950790180080c2001e1900c0207481d41d00a460b40410f0007079059189855a076100d0807142202c00d10301410444208000d00c5864603d5203a499072400ca481810700c4540110b015068800d00c1a03a0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 479369046 1250 479367796 479367799
    0x11120603190c090c0c0203030703031e0b0904030806011b050601050112060506030721060e0a0b1c060c0306051809120f160f23010f0c0c1205070b0c0d1a 67
    0x31507480c140303c840d074090700c20074201e20204881041003078096a014002419101c0c0700351070014202c1c14680003030747c54106c41c0b80041310403868000c1a40c42c0392034550496038080e80c10310f0000c0b0241e848000580e00b003a4500d10340d561200c50740040c05c0c100075000804e1410703640c0989030003d40130b21254040d0207a07030b410f008040e0081c03402c0c0081107c00340a02c12101410000c2196045201c910642100c21240079030700c0310414080400c2485403804407807003901d0740d03024144c03004c09440c50201d031540d81400315080010401d999410410156a10a600240141134002d0254420f0100410101d102c3e2001780c544d50300794060700e04903c00c8180b1132001ca920700405400c4d141e050510700500020200c034184419524044010b44210000f14428035500081d114500324050404142e00d07181d0031128040230300c2400e02c3ca031001c008680d030f4010b40803000003079108894601c40480c10800700d50700c0c042c03c1d4008161044900a02c02c4021000e005030a0408800c7c0c400c11445100c0030040112000c0c0e0307401c40c0d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 479370296 1250 479369046 479369063
    0x1b0c19030809040e0d08010306271401020d0218030609240a180812010e07120b0a03021c06150f0311150c0c010201110408030307121112060319 63
    0x10030000d01c511001d060282002880003c55400307200310181418070707181d0200d0020380d1400c0144100810351064461664a80070981c0c030010b0b00c0003154459840b40f10300a41524210703c1f1000c04501c094044561400745000705549039940640702c4402100700e1f240d41032290296400103541160300155400d858000c10b000800200000014100304680140c205201c0d181c03a80300c4240701a60390342c0280a8207219a4000c0d681d0b08050a96114008044c2c2042032800540b0060041050780040d681c9070a20700440f000940b000c01800080b60405590300081d0405030301d445444d1000b8a10079030036503c5024020a001b41d084103214070680340424051028170101482c024400302d4103807200300404580c054250b03401c10b008155031902c42c0e0010b101442c003650050724900495603080c0603003d54140002e546908190501000e10b48034000104960100403409141c510900601d820103061440f1484140303664000324584900c1c0c1110803600c4a000340304106480e18404104144e42c0e11035601312949d03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 479371546 1250 479370296 479370299
    0x1090816050a05071d15150d0f050a1d0a0b04030c03030b0d060204080d0903050c1203040906030f030f0e09040308070903140f060903070b0a05040f0501021b0c19 71
    0x180092100a81410341c0c05216030084400041c1041100b0300180451252081011100b41c45101000d580100020b0703180e449011131960700c0d01c5540c245880c14500a08140d2600d4450481c3c00c000c0203280b1641641604041c14484d0302c40302e540c40325003400043e003006001c89890360507442c0d076032040b82d80080281e17607041c2c000f50110b8031a48603030700b040c2d20a180c0400e042170301d940040d11480e101e11054507440e9000030200000f400420420800d01500d0400300520703840c2d83ca030551155070103038005024003500d541d07205850005000701c0c1e000c0e110600c8200051916401e2618044000d45001c5001c1080310610081c0280500c20030100e41000a0142d822a9180e66089540c940080d081d00140020400d000c4002203c94070221814008000244000c030016260a46000000791494806030000c100040120301002da00a0f48a0b01c203400205080d1182c1c64444548000b01d140500554404901c1600c0010030070a1204c2a8031540203d0340f000c40202d08203d0300c0001410a07902c80401c6410 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 479372796 1250 479371546 479371567
    0x4030c0603110f0712020c1813030e1003090b01050405060906040c02100c08060307141509151606060504060815180105130c0f03080f0d060506040b0912010908 70
    0x9030054a1011803403c00462402c5503841e43c011100c11640300013a00b5626070050b504002e51414104100c03440840f09a8900881440300000f90001c480031800207000b07000c1c14066080c0c034107031000182004440d0007030302400038002c040300e00049a803050200c7c0002060300c0c1c42d001d014003d8900400c48041a107510741000010081550450b056000740d086031b166101052044038101754146e04c50342d00d01d1410208060a00c0d4803034010301c60725030947c8480d2441e1b17180c060003160f0364040301070040c2d6180c07440c00c001003817650380000340d5051400020704420f5020300b002002a825100300d6081c032540303481d0b004000c09c0e00c0f4540226480c80d0b11240b03011140505820784141c1114018150b210315603050084982502c0b400c07103159503071003148111901040300820f5010002d00c040c00c0c001d804c0b5415940c85460a00c600040e1000c050b5000c1500045074031240d010b50000c1c9401840309994940c1d42d0749030400354018030030fa1032050301e04034002c460111041c09a4841c2c0d83e0f00c52980c0345009841c0b032 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 479374046 1250 479372796 479372801
    0x106091406040b030a051b21032208120a02150108100207031202030f0601020f0a0c0603092a061b0503030105060f120103060b04050601030b010903030e040f18030207060504030c0603 80
    0xc06803a071605c210b29a0074080384083c880c201c1900c185a01e040c072000ca1101c280b0900e1089511540d05030a40c4000d04e26005401005440707030f00281540d012000911220304c003d401d42c1c075030010003848c01050784545001d011034009103900860b90302540d80030818a0f2210001500c244150f40e102d800050240ca5006100c4d4010b0200c07034400c1c03c00d006107840403140601240c02c11100e03800c01c4080941800780c1c1d580c0401c4104012108a00200403a2250f681d9074052140309116240600d61610802d0040000c041c0d03030f0048105030003c4a81c600381070350300c1211141c1541c2c451200407481c040c0035581c80ca81c02d81d01200105411000440c0b459103043c043c8005c035031180150003990031090003244039803100313a10464001d502401000c1040c1d840f40007004210380000d8182810306203003604049803644c10130307950001c5a415042446e001c000100103d40604020038501c002c081c50704034044034001d0b181e5840f01c1c240340aa422981455120038044c4d4a030321a0b03010160010040e120704001d40d80c0b00740c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 479375296 1250 479374046 479374061
    0x216050d02010e060a1715011b0f0206030c0403140618030c030f2802010f0b0f03060f150d051507020609030f030a060e07050702190f0b0705070e0f09010609140604 72
    0x91505c00140e507812140e006c90701905a51503030440100c070710110001e6a10458410500e03c0580d05041c10700c0f040c1e6036607400c144604d20000e000e508080001600341e0206030a45004603040750014000031681a0301c103840314001c890010ba001c03101a00841f603203400005071450b9581404c000c620700003030740802641c4d541114110b030300150061110120082000550038200c07000300d40011800c4100342150b101643c0001c2e28044c01101c600c1c040b0744140d030300085e0306500074200b90081440c5480c0d2110b4401803907803014070302d030700914410103e500704000021300361000080c403500b100035a26288002c07603c80343e00f60703407048442c0d005004404060b4041c01c0110b400001038440090061356454615544140455244010030800b0515030290308000c01c1c0306801c0c0080c500c156540c2030810940c0300e4400301070701442e0b030003000100741c042c2004030401c9404094999040c41c0d907000d25100400f0fa04170700342129a0b600650078000001180441d9000b00d03c4450391030495546c03940d54000501c401405036 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 479376546 1250 479375296 479375317
    0x30203100314060a060501030c0c0809180c040627030b0c07060f0b0f01031b0e0112090602091305060102060610180603020d060b04030512031003050d0216050d02010e06 74
    0x2094008000b41c605002c002e0429500005040f2518140c00034004840040c0d11440c181807c009000300303007952000e442d071102544401a03589441c0c1c020003068921301e81000e00081200000207010301103038500c0140044604564400001803400401c51010f00c1c0e449014024100c1e0b09030044c00003401036040d86611600c0707810725504010554030b07008280e81d429000300e03c00c5580d425190303420b403c04404400c1650020300741803000c40c51036039945240740d000498080c204055015090110b03840784080c14601300d01b0103c24031151000d41800390081d48005c904500c40c112401010f000c1c2c040d140070701c4d8880c2105070060070965030b4210600503142450340040c2c0170442426040f070741c822140444180038203a20390700182c5401c03001c100c0004446981d049943c0e0900144010400140c0000d8010000c4a0700c0080545a80311a001142d03044d040750070092a40c082d001050010960001d2200c4595000425400240d0b80e2401400802c0380d50760030190000c0c442000c3d58110381803150040061414 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 479377796 1250 479376546 479376571
    0xf0103111801020307122303040221030f0409061409160507020609040e0606011404140d02010e030d050d050a140a0510050406060905041d030301150903060f050a0c1e030203 76
    0x16640780c55031b9182051140010030341030000c01c440540c401201a007180c443e44045032460600c0d40000790f41805101142101708000c0d40000d0a4041c140141c0d03a24181c0c602c400d0391590345031a00400a0625802680c54842e030f800e000036914908032050a00900f040d5109030702c03007902c41d88100c401d0b5200081c01d036004481008400140e0f2158442c9200341d16024000e0240390420000041415059060b0303441c07008024070007804105041d100000800360101c03124050081d55100503182800c00c09400795150240c81070f0403c9a60700400140b04001100d0000c0004d80c1d01c2491030b00880d8805080a00c0304800d403400142d0310700e0f0952100e0f0304001401c04148800c4e640e68000ba05844080e0400800503003076110400050802e4040c09149140c8084940c1c40600000d03140d56490005114a0b60300e81c843c06000034001d4082c606820156412010034003141000382c80c08000f03042d003924202ca003e40381c6100c80d1107540c458140803e21300c1204070482011503021504030084c3d00090001000000c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 479379046 1250 479377796 479377807
    0xb060f0d0b060301060e09070e100f171036020a0f06030509030a0c0206070606091d150108030d09061814070608040c03021201290f01031118010203 65
    0x252000c040003256403080c1c0c0c04421518084040c1400e43d0f03556806004407180702c1c4140500034a02060100a03079804c1c0390100c131b560b6111450751285440703650000c51883c51400d808104031803001101c403a15074061040f1880e29258450b2141152012a81c105c04c46102403007000d0310f0a5880c00b1076400b40b800e0b6000311004401d940004070400c1042d40980c8400103542410008187c140c0102a8003000e0100918101082268060440160048020300c9410001000b20801100d91301c03944c0904001d02080140300c01300b450501403001c0048030035269228100401b490305a025016074140c07243c04001c0c4d801c0589212002001c2c12912074100c400988440c02040030708080e11041103064098125005400c600105c12400c10219410500400000c00d0030003012030f1456403400c003146da050311040101314070075440e0350041000c0e000094410801802c00e1f960070310b0200200721500003c403496104000340c4801502124000c41a0000414040c400c0e80ca40d032260101c07207402c24806005503417608 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 479380296 1250 479379046 479379049
    0x3070e010e030d030204060e06160314120406060e241c050f0706080105180601120603051b1912110103060503061e01060306030b040f05160909060c08040309030b060f 73
    0xb1010b10b81c0b40b0f0002e54040390801c02c00d54000c2113030030b07901800c0d1100c500d4401039450110606401034800380038400001c610700440c00351358085440d000e01d00340a4000300c0c2010701e00000540303124411400c4490381d441c080303500c0c0d07007144005007002601c41f024140071129030414826820010f2042000000c802d20403900840c03028070480c4004100100030348140d50130840050407910068000c2c078000d0078160342d09001000d105070b210b90044c8013420000c4a55030303110043e4002d80762982000300740d4022400c081c008549400001c0da00710302c088807030501407582d10a1048040c01548292074091046081c4840840c400c1500d01c502e03c46d0601d00403400d142c0724000300385088019101407000309134400903d6046c00c0030721440c82c0504503901d000e0040340d10311345545003040c1018201510368a00c0145003400c2150401c502c58044100031904030225998001540040c11402400c0e95650b040800e081040c0c2d00c02c401c5a03200b0740d4551620b4080f2800c58845125035075005207007940000f030010303114059 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 479381546 1250 479380296 479380303
    0x9050607031106070f0909110702060a0f14032208210712050c0f03060a0509090d080f0412110322051306030209060607020f1309031404030803070e010e03 68
    0xe0003929003100c0440002c200701e1410034010040001c0141c0d000d0402c403215881104001103d00005010074800c01d10f1008030381c43e1054440003940003a0018503500a650800a4030884402079101c101820b01458405220b9220445848800044504c500c1c126204000d071002003c1d400b401100d828050301002e8289001c0041c0a04180d419800042055103a0704c407801036012580d601090006042c01034001115015025000c4135144002c00040c21580320b00b40400006c0a004080b10164184519159101d44a800304000051030103400207950360302510031140580d41c40355a4400d85007074980b08490310900101443d0103030104000980d908e010643c8001140c84410350222890b41c5440108003829403121070a0f50345038100b81040000d607488231001a0302200556100f5941c003d140300155a2900180e201035008403c012699001d1f20f03180c3c020706040b0301c45e4880c901d0100160f80900b509001e40e100080000d281000001e10891203030a00c012001c00604100c0580c210f2400080e04 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 479382796 1250 479381546 479381557
    0x91005060a062604050a02100512061005070506010303031505030a080a0809030d1104090f0b030a060e010b03060c190801210204090506070c060605011d040c051b010b04050a02190f090506 82
    0x160b6520074440c071ba056181407100b0307220704805030a01a20b080c64544030080301d5600101114801c0e5181b0074203491030750180d0110390800b5400f60603100701c1d40e160b28020b401461a80b10300c400001003520081518140051664940c94004420504180241100301d807403920080c48003c56010611810f0410013960091824444245528a8460781042250411180181103104010f0704100d008815514042046005581c10100100da0303030080d86519030141a010301010b030140700340b02c10481c041c0b0141c4003801c0b200c086101d482003d1b10614030100d46c0c00c0421301130350703041124007d52280d2105040b2108600a0300c09040441c202070581c070303150f04180040300c40c44003007a0104a035404001181c880e00001e4402401c2911101e044900c442c0000c900007040b03030b4010756035400020840c901400c26a130382003010a400881c0000341d60841d501802c0c518400b03234084c0b400c1c10007041181c04c040c0240c501651062150703080004250804541d01d00e42c400c07811044c0700303a5200200e00c90301c45000071b20 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 479384046 1250 479382796 479382803
    0xb150a030501020c06070f0c0b04230c0f010e0603012904140108010812070311070b0c1e0105130b04020f0402030c130e09030a05031902070605091005060a062604 71
    0x507113661003507180a05041c0010454410840420140c030242d0790070080e008150f5401c40310b2003a03942d036186007071603050141880100f04552041c4c0d2941441000040360304c20030740150307540403880d0301050042d2884919082060740c441400d0005003c440140e0241d02e40d9080051f40542209201c40d01803400b40d4001d411075076a144032032115803041e580009000340146140402010b041f08002c50900641c0a044001401c0100210210025100402582003c2c11246c800b20756030754425000300341d40714100d0b424002c00d0400005c03080c0760400d041c4038075071003584401445990a5510340c3d0f41550602c00400c00c0741d00c1a14038940d281e0680781d502c0a5880f400101001a548601030101e1030b03401038540c3e02040c000b541210410804060100036140c0c80b800d2802d1040c0c41e0380b207903104010240e40710340c0079070141e5101213195010300580781c021900685a03413081d606501e03000910365050301c00440d80d1a1b00955031102c10091107110f260080b1203290800f804c424202001030480c03818010a50307055 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 479385296 1250 479384046 479384051
    0xf0117190f11030609030d1d010e0a0507060e0114072405060406120503090f0121050403080702010b0f0919090b0a1113050d020d050102070b150604030c030b150a030501 74
    0x1c0c108440c1004112800808400400c3d452070041c204c00d989101e261040038190b80c55021848480115956180c022081940203104642c501b0250326683c1c00541000d036071520a2040004049004801f40000f510040c2d50701209840c1d00701000c10107606c41c034802c80741c0c82443d80700c4403020311f0180e41e010201d103041800880c2c24180481000161003a035041240c810a980c8803440000f080042224140f03030059869024801000c00140e07031400d501c00c3d043e460700011380e40c10400055154400d5100390702c01c4d200d0104540301d1220032800c03100302d6550241c010700d000e05200c01034607003100030940c0003c400341641591142c4080da5800d403686408119042e852400911040e04498000c8442d10b05074100c1c3d0500b4441d6030900083d0030031a07881480d0203648110681c0c400e40d102c0c50000c01085070403d000350b503501813a2410100820080300e001400c182010101c200610702801101d0813203400c6800841f8031403c54032950300000003c0c0c01680c040c41529214a82500e070f900c04d0000039400382000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 479386546 1250 479385296 479385323
    0x604080102030711071521060f0603020306180c03041b050301020a0c05010b0d030504090e070b0c0a020427060506040605041e0c210915050a0c11060f011719 69
    0x42d1340c5040003d07001400a8001e8000d0101c9040d03200c0030041000e50b000e070141000d5042d1800a900618290f005080c2c03d4214940c0032520b00e8040e002903024440544100304c030188d001141100c036030f1003a591381044550800105000c64426050308500000c840054032030183c1e980c00003800ca034080c40100002c512041780c00000e00c042807260b518800000d45140c1c03030000c850750700144548568042c60700c21655450103060300748810802030000d4400704000759134503000c400f100e55850709280c01c00c91040e42404a0b10020185c20508280c038103403800d5a09a405601d80c0d070320000f03030000038001da030815615000069039035500d002c0e03c51a80c004c600d81c5c04230891600c280030240e43c0b45c6081034050061380d10103560b11a01c00d000b040410b0710389940005555003a8600000c61454401e8150102030404040c40b06903001c541c8025400307500c9845a4101e4000d00d04c40c4d5440e05001c5900414261000e401000081580040d070b500709101101601c005018940c0350b10340e903040140d410740320518034161 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 479387796 1250 479386546 479386577
    0x20f0414010815090105010f060f03090f11041515030e150705040303020f010605030c060706021b010501090b03010e1c02070b041d0105030a02030d1d03100f0c090e010e0606040801020307 82
    0x801500084d00d04028052581050320040b17441189100b40c6082040660f42500e50600c0707030380700b603520a42c0041104c4440c416402c050080c0c05c00c503002c20348a81e181107030301d0140d00144152501104d001a154401038800288247d009000803401030841d409501580b41c4034050b0806990f00c20314560719025215421400e00902d801c2080010b85080d0b03250100901155400060040f1800000c446c003035620402d5240c06000b0b070140c1400b000c16852690720f02031030038406400c0941600d034030074820000d0205550415003a070b0f40f407076455203280c3c00603c1d030001000c424528a05140010b8012100364139910708070700e001030f441580840c50300701603046032170346040b444030806004200131001442c0c00c09041d00043c2d10b529056001005001602110208203003a40469441c130307080003001e039119151640300d040098180c401360603910a19008003c01801d00602012041c1c42d68914450801d80c02c1c5000485050300107130a442e071001c1e05210001c2c0c3d04201340000d5109116076600c80c0e214400100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 479389046 1250 479387796 479387833
    0x10302130621050d110723090a0b01020f12040b03060a21050d050a081609050a1d0109110f0304060b040603030f08060405070e04050a020408190b060a060804020f04140108 75
    0x120785208115503460005d42c4c5880006404082d1844900c81e070004184403003003009100650396000d900103054408001c02040f41d42d04c1000315001c00c1c3c00355902000d48401c0c454448000c0c01c41745a1007103050100f40010407064001c0c5a12210241130100c5841c0c6600b070a800e4400705681107254aa1003443d018100300d802d00056124210904009007400e15455025103c0c82c030013016108403620300d011500e001485600c5400003040007031b00d07000f030030f9455000300e03031084940080c184107924071100000341150652041c6241480e000001d1405c2c04104c80d0030745510360000e4010744905456404521031603560781304c0c1400651003a2240080e08803404400350282d40700a00061289151200b00111541c0000000064001c22980010340d5500c00001c0c0009000d560005803103032181e104030a80700454043c080100602a201808860384c030034081158101c2a030081c0c0700080e060b41e0120300141001030030304543c1d42c0010404034240c140d60b01e0303045118500740c5c03110b0010341c4040302d104840003445 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 479390296 1250 479389046 479389063
    0x10e04050705010e010c0803070915020d03140c16030306030b0114040c0e060405101e030606021c09093c0f06241815030b031501030213062105 63
    0xc1c00c040320304d4224000060141e0455840c0a0700500000002500c420f205498600c081c2900d80c02480b016540120004d5079150065180400310749843c40082e02140403110340340c03098413404d403920700c0c1c0318200d0504001d03002140401c90a00d511001c020001805242d80ba5010b80101e132003042030701650108000942741e6040f60402400400c0d900c41c03200361119402c441c1991820f5510b100c0400818004490912180990840c110300c10701d200e00a450b45500103e0484c1c0065085810581200b0704c83c5450b1840a65090702241c00b400c030412a184281e00030400590014980e4480e80007203061001c201600a0840c881d4025a44c1d48010f0031041d501c14034450310107414040111506110041c008040c1000030350016100406003d21090301c1100c03900d01008010340b03105c040940d6152030072042c84040402101181c00c4c011100003a0400040c51603e07010098201f07080d41c1d103180c0a01c01d60780c03000c40045007444d4aa40d004105113501e03c0716980c0356040562001c00e030290a04241d400c19103803 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 479391546 1250 479390296 479390299
    0xa0b012705070c0803131a0f040b0a0603140d140c19020f030714130c0e1302090d0506060906030102042303211306140d0b040e010203010e04050705 65
    0x81114405034445000c0810082030302800c0d0015958888080075503024007a440000d000d500004200440240e49011800d48140302e010058800ca03181640092591000c640c16010380d4803040024020821044400b80c100f90701020028240e901d036114040030701740440030f102043e40008401c182d555448a9400c1400b510381d050141007007040b4003410b4982e001c0820642700c6c20402c8002c10203655030313010b01124101c002404c80c0c421a503100704000210010110f80743c82118160142c045030016805007407640c1c64265600350400e0003400c10055034008071101d07080c41c0c503409d1043c40311070389480440007000c900841c000e1106140040801c0b1600f41c1c0180514003a900503c8100041481d0114131000362000d0150004c203000140042843d009030082e1901822500180c1000c0007124a002082e1819001041c0144030341c403003a060b02c06003000c800c401c004071380401c00b00c05411b1107075024645603d0000c0000c00d4903417a03a40710f02c1c00c2e82c00a8003c095085140010310040000400c031890040031f0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 479392796 1250 479391546 479391569
    0x81b06060a12050c062b0c050426010509150105040603020604150c08160b0f06150702030a051605100807050703120f050403080a0b0d050c01110f03030403020a0b01 72
    0x80c044082400034059200702e008104003142c4850400c9410301c4036001814000c0c103180e89403020f1115069820070708045a600078000d0140c06044c044250195410b0000c50b619041c1c81e0903e00340d0b18082d54403128030026680c40040d43d0490784103c080c000c0030701540f20b01d8014803041114050311030f110795041c1c0c0258401e030b01c0c0c000200016121007003664112850a00550700078082400251291204804010603a400025050b81409000d545d0500c1403400358001881540c1d034440d54490400040ea00c5651040843c283c000d5086608001001d1161015090710011283c698913039240621402500c82286e03041d080134400d40c100f01407005900000c0e85030211050500140242c018419108007908001c0c2c980100c09000301d80360040074207111086400c00940ca402c0c10000d00c40704096810021150520001070b0b600c1c03a0000d06400300942000c090180a0458001500d1030150003c01034494010300c400c030486c654041c005580701d039000b034001c2c000114580c6042d10789004141c00403c3c8401 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 479394046 1250 479392796 479392801
    0x100804050703060b01110313090605040209030709020f071b0e0705120601180308070f061506021504020d02120a06291018260609120a1803081b06 64
    0x2035001940030202da82003007000a520342c440e00101d405a211104e6280c00784400030b03040c40c86101c0c0d00e10380703070484164220812035181ca810400086c8d1244d110159032690119a05100010207035004021240d0303e20b010b140381c001541d6614803941d2480c1404c41010301960710070408805480c1c000780e4030070481c0c13a24516000011848244003080500014104940513241040701c6095030010b501031904036501c5a203510355890090050136108008880060078134030b220f00f0740aa0b01e10004251106c94001e000141580b4180d0940c01200400130380e4420503c9160f07001584690401d00407254641c1e02a00c022845410b06506464500310250304400d0815070b07489400791042c610072a12030003105c002001c1010b9038812241c4410340303c011503c007a00d10400250f12181240310350400d01103e000c1c007030500760124085840702011103010f00b154100c0b61f042d21008031000020700c081401e41c10081c2515001d062400c4043c0510b0f0001c03200c8460010710349025a880e2018008108500b000904503803 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 479395296 1250 479394046 479394053
    0x1c0b01050405190b21010e010c09060e06090d08030c030a0524060d11040609180504081b0f100507170108031b190602040f090209011e030906050a0209100804 69
    0xd08007403010b180455403640301d80034a668031840d148407080b50712000305410b0038002e170090080050550700429036103400101d80c2001d004810075001c40700940c0354041d24512980c140032103941b14400480c1e002c3d124101e218001020140610b02036031b652a40e041d241e1601820320b8080340c03c0500000135041e0405200d003503540c0221600045a1010307504251100e58103a40310b0043c04051034012518030000c180800d10b194003031140c2040b6084a9610000645544c0d6100201d44c02500d000e05054020005000110134696500d4180c15001d402c82d00b00c00ca0f00d030402810801b814820507071180d02d038000c0c0101d13998420758001181464014502803540341ca0301c040d81e01d1080c5c880603034400070050241d0140e040188820f113201c03c1340d0940c2981d00b51720340c90030348000e52141c091190640301c007290126180c2258800d42d80c0143c4182c44035100414916005481075110f00e5036282050b0b2143c19100000e0214041c82d8029441500701507210a030305401c200c0103485808102c01008000c03400c02010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 479396546 1250 479395296 479395321
    0xf03080906070201120624081006200105010e0f220201031d06090f010c050c0a02010c02040f24092d060b130f0b0f0a080c091c0b01050405 61
    0x32040440307a06550b5402480140c07a1400f144082d106640d1516138002590b64460801024202100400d80720070400c1c10030665180b40d040e00e9103030405604250600c07110340281268502c51480b06028503207554400c100c2030a6400903006240400c020b0301c1401455400c00c2c0490f900150310705030400c01160501d242408001e4100006410552076030242d0140b0a0800441310740c4a154a054684500e80b0084081c0d4034200880b150302a9031030b007142c0c02c0c0c619201d02c05942d04054050060001000d0607001107628440c8504140d901964400307150307843c02c9003889a410b0155000e48117400f1080102d5503c03050361041d0b84942c460a05110315a030858180c0c180d4400894210b01102500d08000e0031540000c0500d03402c00829a800008c001294250780070300442240e400c00044250980c65045130500e6000344600301041d00350602c60021040d000d050320540c041c0350400704c2414103c0134000103494800f0200400071440045101905000700809400c0c0034003416102400781d810300010901c079 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 479397796 1250 479396546 479396557
    0x10b0406060c0b0703021b060105030d08040b13020a180b0f10020307170d020a20071a1c020a180e0c0322060903050a0f09030203071a071b0f0f0308 65
    0x4100c25200000d0310040c086e5040c0d6040411030001042c1c03d10500c403c955850707600780502440380c45040c2030a001c15126944c103034807907944104005c0b00c50f181c4070f04070300d0b1101035050101d0b44104041804540c10010407140300740c0c0c031030404000c10501c19260a02ca80c001d006c1e01411302442804201c0c0140030f130000f046800381540a40c7d2042690f10198410b1140d02075451400c140c2800020305481e41e0380e000800b81300e0340700e030a08102c006c9020748203256a68201d521a1101e045403000003005502c07502e0300030306101e004c0700d0100c6101641143e6090200e902245e04180410502c5000101d008180c050340f0028001045000358241407201c64011a0301004004060066400c004210010790254540112a81c0f0020a200701c0c0e8491401030055000340c150800051002d1003c5504c142c840c200b120212078014025204c0302d400c0181100079148460103c81004038100b10101c00182c3c5107610312280300c00039000402c0700d0f040c042c0105a03030b4025030140740511141581800070645110403503d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 479399046 1250 479397796 479397803
    0xb100c0210140313030306080102040905040b0a090f0305090303091809010c020304120620040605031e041101110705220b0621040f06050f011503140604241502010b0406060c 76
    0x10041105845c080303000d0a0241c202141650000c2030000303140b000c0d500f0142c000c030b104049440056845c40720341d8007141d000900180c920a442c60401002c80d00510040651100150950b841c100301c61000c0ba80c3c1000d20364a42054a601c5070030000b8003d02842400c030000b440788003940c03426251100303103401c818000f940a4030090f074481e40c44400030f02d04143d01364180b00e40040305403180d641d6400034103d43c10440310307803884901c020074481d44407003d4080140b290754801e810030303420000040115498a604441c1c00428851818041441d6468940a000200804c0c0c442c580e00810340c0320780019900070000d0240910f40601a52000038169440540040040d4140d1041c0e51340c1c1e801e04020010b100390b00900000c1c41c00b000c3c48541c002045100c0d050f181001c2c917400d0610318500d4210101c41c4d18541a000c422080d00200e0000c2c030f055046a80c4009001c50096207510380c5400314902d40b0140e074020380c04c5e070b05e84583d8450243e4081c0545400518112410031001c0c2c6031200c0035000e10a03060008 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 479400296 1250 479399046 479399071
    0x70e011107050f281e0f06230c010633050d0c0210020f0a03050f0c070f050109051207050d020705060d0c020115060201140f0112030f02010b100c02101403 68
    0x130941c1c819074080107600c0714410030000300041e03614805501c0f6460344507403d07112400318803000700d55043ca80c00d030f1100704c0d0150741d1024042e0f4120310b42800c15400d00070180903030744020084141c802e5001d01883c405040c5481a800c60007010b280344401901004849040c1d600c4e41c8026841c00c4c40d080410740b0660070f030905011400c20000f14049003041c5038090000303403d61010900c29440c100e12001381c4028801501c040000e41c81c1c01c855002e252504441c644104003080020030009080454030b004814810781c0040f03003280b074035900c20342001e81d0a03030244000c01001c0f0b0500c062040820a00c8945000780c0050651641003901183c4240301c6d51504c05000c689410351245024401d6000c0841c6031442c01c0c01e0000142c0b1860000d01a03c048040c2410301100e10001c41c2400300c4c1112400e040322001c41c00821800703241d560507160346010055500942d50780c3c0058118a072110054468407030000e940b07000409241d8410810801d250300801e000700b29a06001c408900e408000b101c1d0800f0328009074 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 479401546 1250 479400296 479400319
    0x5060c070503040f030b010314010b090c0a020a0515240102030a0c111801151404060f050409240b03151c06020c030a0e0315011a0c06070e011107050f 66
    0x20700e584110740c03180c5000307070800c2400800d001d880e01d81141680d1080c89404401c004427030b00203098900c101500c0d94010b4580c030102d410540504021324003601140142c6404400640b42c69007480d00400c1c81c40001c0f4019010010500301e41489050044000d004d090420345803c40002c0d0350340205400002440b088642c0703181482402030081d00740c00c0c002400400c1d20b1000c0c060f941c010050070700c0703840e02000070b2085d6415003e02524003049060b9140d01d00031b081038503011045492400941000301481401c000214071189036002d000203841c468840c03491000d00c0302e84400c64046a8ad402180c0510b010300a000880b203201c4041c1c5c902c60001c58800b0300c6402c1d1103640d10052404510024103107440040c858071011008030103412100299115103401194110030f01d0b03110750640400e0008100c0180052007144844452000c0000803414554101299403c0f0140b82100a580703a902191108840c40c08075a44100e1204a8810240140480302d01d80b50208061003110271344180700c0d502c010103 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 479402796 1250 479401546 479401553
    0x606020319032019030b010c05030f07060e0d0306031707032c060c0609070e070816031805061506040510030908070c032901182c0106090f0905060c07 66
    0x50a0014025100c00150303229112200e107134000c1c130b2200c0f080300800e09210308a14a50f016100e5402d0090b00000918584080c56003807807103079070141d001203403140e941c0c02e005100410304201c0c603d00d41c003d6480c00129103056003407802c42074804000f84074400344100200c10010340d0050301000c0d080d413012603c1c594400324a0840050210a540a940001e030105900c032090400060301401032605209851083c0e8413540d101d00d1041d011189200442c0c80000459442c3c801032039400c0706441a4640018801c1c506502018003034440c480c150340340c0c1e03c21024010000c20300f901c44601c02008460440ca41894000840c88140350340c0b078228240b41c0d80300e1000d014851502c04030b1304d0302648489040042906c0e49000301c0d03109006a080045d9130301012100842d00d8400f6007072416144007901e0022030b030345000d04000c06448001035076901c3c00b810000044d00522400300300c0403e00300840021a82c50304105400c3c1c00c031100110700e00d41c0b150410000502080c03000c60002d402031044950566200e140d400d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 479404046 1250 479402796 479402831
    0x8040309140604140a0302100309060b0f010e120a0506042108160522030c0e0916120809040e0304060e0d0b130f1202011b0309240603050102031009060602031903 71
    0x610183d00802e66223178000185030305070300c0f2400c694801d040401c105500d03002031111003106500c0007400f181c1402400b17901440d00032004100c186403c012a11a03231001e6894605041d010f60b07048510019682c12034056212004074a00c2c25085841d140361b1500d45407241006401150085074140480081d45800c022000444802e0400f43d08600003820382e42c80c90114455011383c49000080c05101c0d021495078103020946021911000c00c8840a0030b0810341c0d404400d5095140880741404104000b100540740c83c000e00c183d4192050140d07807198645507001d8204404085200d10800c44060b4034030004070308072a4542c12181c9000c03e50605042481c1c500301ca5100d001e4080c003451101c40341c0c2262103070705402061122107091443c10440b412400141c041c2d41242c80010314904901740310b4a0760350700c03c0e0075020181c191800003240044e6a500c1c1c050032a8401c0d111310134040040380003844503034958080d500041c02070b88000c501d48880344018080580c0350745020070070192100d5028802d02e4564 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 479405296 1250 479404046 479404049
    0x702120a170103080711030a152a02010f05150a18060b070b040302071d04030c03021603110a06110706050a1806050901080123130906050708040309140604140a 70
    0x498001d44596102d0038401d0a40c0c112101c00c42c1e03030300c141c0c40102c0103a042c013049403c0c00aa001040d044600d01c000c6110000e001071a0860414070544415019004400703244841200502c2c1c0001407013504440c150810b49034002c10190b203a424101c80d40c00b603912295804812540c80080a241040c000c2141b20041e120b42d921440c01d94501245e80303c18803502e240024003441c03003a001c882c240f640e240d202c900e41c0000221500e001c0314555000a0204c2e0040c039042c00d40324032a1042e550a50034442004545885036002900c03041d44210800f601810100b04910140c0004c2c103142e05002d0304dc0c94016034401480c0220010000c0c04036000c00c0e024094200d0b0614030242001c010b03103694a03a50000c1c00e0390007201c8024002a003180002404040310b03e60310302e6404a101e90460148400421300c00e21001c3c40e4061002c04d940c07080407030040385451181d01d00512142d525051030b8181402e0040152141c0e402071000c0754a20110880284d407103504507412a004042003c0c00410460001480a88075 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 479406546 1250 479405296 479405327
    0x91203010b040602010c090609060507020d0212010c140309030702010c0c0302030a141b03030f07030528110606010801030b060103020d1103060a0e0105150702131406040608060702120a 81
    0x8000480e1030141800500b0030b41d1030302d600070450346038a40740031200003a017449000041851510300b40440c81c8110024075619001403c10307000620241e000c154201c0e80c004800146c1c0e5559a100d950059000a10700e903103001c0403841a003181422501d46899209400000f4140080910000e04001c3d1151204006540040554040c04e01604111400d007080d407111401d180213070f901041c180301c815891450f6011010b0021401c0a607924043c64442c0e0003041c0a44c1401002d0041d22603441d20300381c105d5900b458404400c0d1050103d480081c110318880c00c542d0b2aa600004100701860b49c3c88004503044070b82100725a2450b8661000581c02445214402801e50b03007070048a005280c4124001d5003d21400e8419400c40c40d80c4081d8a02c80040c04e00a29a02402510644114411100103010010300007400f45007641d03400c1c9040402c0ba000003030410381802c110020040a80342038401c0100601e032410140c181440c20740e40081d103e0f180740c4010b003444103000c00c201c41054807074521030101004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 479407796 1250 479406546 479406583
    0x61e050603010e18030d0506100c0b010b03100f030f06151404052502070e0603070b0f03040507050a030b070305100308031306061d0907061b03110c04050a0b0f120c060309 75
    0xc01c24546c002600341292540d002c0c1c050032004100305842040311203040b40c2c0104c0710100c6a4201540300c1c1c034035800034111514841ca501400300300c0300f00d505160700040d4450092a528100c1c0b44c81c0140941e2599290b04c045403146034020041010301a80c2221642c204880004180c1d46103810540b001c8003d010620b040d603ca4a8980380094001410005480e8850450503882e070300c0310f003015036815031805110442c000c18011050b80d4074a1401854000303210348240c411035911400800c51494260b40250b48182032182401303120b541600c60503401001c4144803040090071611000542d12014020466030018814220b0a2003040d40c416030240c10110400302c41031002c506000058001612003202e07074000d000b0006185401201444545d1038000c04005085981d40c0341a143d92102c95030640c480d01806600c00c800341e68070700c221780c0b1031120148009802c002e0f0000b03200306001c43c10b504a014820402c0c440e001040b0014040e090148201c5185690b542c40b5249541440c102203c0d4540600 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 479409046 1250 479407796 479407807
    0xc0102131409010e090a020411040302040c021011070f0b1b041214010605011e050d111902010b30010606050c0d03060e040b09150703061e050603010e1803 68
    0x100140c580e0404407421944070315141d880784030001e404075007502c002800e0f81c05a0640001810315030098049444440000c41c00c06503603401103415918442da4030300050b000740c4c500c51520a464481c03001100001a5070901380700d141d07560401600700d42d800290940c6c03140700006a601d001300c81c0b80a11310008082c080e45884e900d1841070b282c40c60480d0101c50501207011426010a014800d040c00c0340c04c16980c0341c4010410101c04803850307481c0c0203624100102040701c15100c2c2114000da130088a445001c0542d42c582d032801100c0c03120301030503490045904000c0703c55620b9494081003203c5038607181c00040741c6600c01e980809001c010307a603038401d1542803000c00a402500701000d0031001c100c841c140c0b0f07030b0200c0100d0308034100c03030081c003441c4516603043c004100480c10b40c14103607034015141d404603201001007205030a6603010441d442d5000a844110504c517510407004c1150084a41704030f03101100e410500042c0c001d0105010f00ba030310101040c00101025545d0407020302d2810700340c0540f603a03407 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 479410296 1250 479409046 479409059
    0x61801180b01081219051c020a02071404051009110c06090a02270103080a09031a0711010c0c02041a100302040e0610080f090c031005090c091006050c010213 69
    0x60002d109000f0f1074019058480382d0705512104417801500e08948406103000900415a0560002080f044d006d1001d42e1600c0d0901007144018a082000c580041c2006880d00a6034030a600b4400600b41c000e5040000303211040c0b440c42c0d900001c0e211440310101d03841041c040094441d004141e103201051040f8814000c40f40000302e0144c801e24025146034022084152001486190046c0d10a040400c804010800701c0c7d01c4001901d0038a001d03145c120240f603a02d46542c406c00c0e21448000c00207090050034001c6642e00045d07010507060b000402030100c80150080078019625101b0042d00654645400c2c44a8480d110f505a000100c000e20007212522002c1c001002500540100c2c4c0400e4511404103c40f450082004c6500d803509588411544d0b64030b4401c601000800b0706201100d1003021062503042c1c3d01804000d8071840e82c03900004051408030302040c40e0010b2448058041d400c10418442407554229004080d07940b03070706000da81e078189018040c1c0240b0820740c00c01da1903015004089280d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 479411546 1250 479410296 479410313
    0x803040605220b090f010e0a0803150603090f0c030106050f190f06120e0102040b03070c1b18050612030f0a090b0d06032a270f052202010206180118 65
    0x241520802ca500000b00ea144083c200c58000c98815000c1d4054010f23040050700c110019540000d9174520a0913405150300030810681040da1a2219600410055105014100710008140d0b40440017072014030300c0c090204045040c044250b80c0240080c001882000d19400494001041c0382c518a9401039519103000b000781e4184101e03a401c00c0c1c1003603550b84003400f0500960702502d03130001c0707168950b45481030256501038009100b100c000b07240304d00c1540b95150300c403c200020b104a6480e082c05c0f10984c4a0f010131198020704030b41c030031030b5481c4c1c81c0074840c00000140c400e8503140d4001350790345180402080e90885550351040904100000c1c0110071004980c0144049903c1103400c4404c00000800d01d4910550f9280c2d0b20401c00203a11003008280c0d1a02d02200c41c8800c02424440054020801c5000381d814504200100f00c3e1100e090001040039102c0d42d00c1c07114803c400d0040a1040307503000039200d14024211403000c400c88110340c07400c844207600800c205d018000b00f4407c600a541b8001d80e0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 479412796 1250 479411546 479411551
    0x50609070812040e07050913091203060f08030921011a1201020901081f18051012051510080f0d0e0f0d06090305121003060c0302070803040605220b 65
    0x1824001c402c0981c800e2606481a80e041d2801c0381c00a40159640c9103040b00c15820a1007500d40c0907200c080d5210740990300d1b00c54540c40c14010244001c000d031011201a096076180d40c88000d101001d0300d0104402040030068075a01d45040715000003032000780000e46070a08042503200600d5180c03102c403a00c800c5003590f040c0c0e1071200c2518040501109868000d00300c0c00f42000050106841e440011001520501c0304040040d203082003410040d1103040401060f20103984c00044940e0346e00500401c1c55000c0303003680040210a10f140c1e41400c00c0d81d140c540b104030143e680050800c05c039021680c0d51102103c410080c2500000b192341082c500d8000a035502c40a10344107020030346800040b4002e08225141101d00c1c0c4000e4600003829145980b504004c0040c09130603400c02c80d00340a440c40003a0041020742c001c4041c0740c141c840042c2982460421211a860000149441003004100007080c12003600d5110ba002400047d0559450705030b03003410041000c103000880804410312080004240d01d290 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 479414046 1250 479412796 479412809
    0xd0c05030f15060d0b19023f0603071a1c020901030609050907060c0c0807030c060327110a180c031104030503040b180607140c0904110402070f05060907 67
    0x9015486403414008144c4903041c0180281c1440340c00110050044d00b43e100382c904a86000524100c0341424444003800e1001096500074105c4056203008090000c107160140145e1410b40032904003d4002a644d4000c3d2094082c80c40140e5140c4400c0032030642683c481046400008a8140402288000a40c40540481d0120f45014008540311300c042c17003094414801d0000810003282000015200700d9104c041c104c0308044144030100307015005020390401035110381d40350749119080caa0043d00381e54040003110310408000c241c5c1d103c60304040042c409116002500e18070310b070340d8000c0130be102041650000342ca14051108100c0c1d500303030180c1c800b05800c1e030640e0f002c0010503010703491501d0500c15071102a0480c1d00501c818888100d55100800400f0300d200e04c20400b40c030209000c940e190300320702c105031404a6000c0090300d541e04207004000f1a658210340b0f1200910b41a9140c10b00e0002c58907810380240e41c08075103038003045442d000c0b035183c0a8118003195402d207000a0055541c81b001c2c010038 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 479415296 1250 479414046 479414083
    0x302100c062003060f03031b06070207061b080a030902150c070609030830070906112b0e04020f0403170a0509100c020607051e0304060e0d0c05030f 65
    0x188074010740401c10061210608102c145552281301c200001d004440c400c00703078140002c10031048540201c078901950784210201078845e6180100001c1d007800229070000003801000034010302900605031290300b045610411003900da1008103001c500030000240000d41010141846000502d0390034090715100303842c201180c502e1502ca007002c4601c404148801058036805101c2a01180308481e26040c894900001220307030074641d0840e4401542003601c00b0004502e141c94141302c4660321210341d0300312180e4900141013400110781120007c1d0b40814141220703220b80059480030902c110800002007074010b10540d11041c060301c006260f58400d10013181c10758003980e03a40100080c401c0c1606c0d5809002d07203466080090000600c000c001d100d905002c1000031b404403600c016502c0401400c000c0c4e00a4008007043e42c0041403402c481d660200c48030f8003a034400e10040190b0303580010800242d000c10746948080c0d00c082d180038000803001d6040268103009901240c400d280c000141c00504610f00087e0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 479416546 1250 479415296 479415311
    0xe01060602070e010e040203031309021206150702010c0c05030703060204211502280201090506090f031c0207021c121707051e0301091409010510050d03090302100c06 73
    0x5030381d00c0659100f41c19001085000401401c441e00340c125911500141c02c4d00d142c411001491010b156158200c0c1c10b41b1070340814642d41601f1581c80040d8000c070113480c030941c016407225030302d252801110b00003030420414410103000c100100c80520b00811002e401c607201c16840e03250580180d0494007800214100c0049041c040036061400c030800d00d60050742100124600394002c074042c3d4001c25030440d0a10403260603281000c42088406840d0015900008101d1018541141001d6028104d001c840d40089405d40c00c22401001702c611101d104010080b407541e12030b0b000701c082d0242d001d01940c0510400308010030301c1012425903400d40e106040444c290320ba9040d042c3c0d8800b0030040390280e00700c100340014480d1400781d4010000d0381c0c060130000ca000c0c017000341043c8060b072007608080c122a889a0b201800000b41e000d030903402c04201c4000b4466403400f811921641840f5100344d0384600054590759061501400c180d0b0051a0060f000503114031b2a2000900803000300c03402100c450b840c2050 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 479417796 1250 479416546 479416559
    0x118050609060a141201080606030106080d0c050c0d0f0b0c03010f03080f161b050909030729070810090b010c03051305030307060c030c0f09030f03050c100e0106 71
    0x1000a55800400031401c00308074406000154100152003004d00203030744183c9400841e201e001d00520902ea0841e8041503041142040c00d00002818441c02a030502909100e80c1a01154482c010700c1c0d02d01e000180000349082c10303071901c9007600006030400c644130003800c244543d45541d41d403424001c400f100c1842d01c4808480c24184001d200d129603607680d404040c000a01c102d002812514180350030b0303509144c00701820030300003209000c0c02c0302c03914032140e511120340c91982600c400819085946800900c3c220441d40c0d242e10075010000c000c10101d82c0e13a00444041078614881d100803c0303000a407186030690002e4002c18046d034060b00d054501c1d120000b6500c80e1801982110b65047c0d46d0300c48038606a0740c1c152280d0708a00301c03c82d000001c80d5004034054400f0405072a5250150344007207141c116000001d0f0403184190840410010501034442410307401441910881e58040c200c680c90700017034102101c0758041e8036001c0c40e40740100000ca03a6844003071341000184858030300003045440d99604 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 479419046 1250 479417796 479417837
    0x1021303110324010501080421020c0f0a03020609121219031103042a18020d05010b0301031e150219140a1403090f0303070203040f0f05060702040c031d0c01 69
    0x18100100f00040f005029a5103e0b6041640040c0f04900840700e03442034803551241351b2061000381d00180e0002e180140c440c03416055030400e40a0a07201f00007070605640105405114461200707008401c0c82280300d5643c5070400c40ca501001002c0d0743c01d5181e04092a01088030503514507600d00182c1000c0c2c0042c00c4584050440f40200d600c9001920450052090000541c11074a0341004084d5619400242118101308100d81c09a07602401030303907041300c45e222608880060b004418801818401800041c3d06201084000010b03280c0203c0611905d181c400c40d01c100c00c240e10007180d80082400303603100700c1d1010070f11242c10254403108105412050b118096000780d1401400003200c004100c545440300c3d50045802680078400d403146030001450741d61440e80150344190044e0b0000804014000e0950070300006031082a641000041ca80310014242e802454800f901c110355502c08004194025031199003e901d0340380020182c0d00e0751415203a181d8405030010380c08500c1c03242000c84c0407803c16 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 479420296 1250 479419046 479419093
    0x110f01020a0f0305070215010f031b050f01110a020618090a0507082a0712090909030503010306020307050702030703031e0201060305061302030a080309070f12050607050c010213031103 81
    0x42c2d40315100000140030440241101030704607020350145400c11100042c0c0b00c92100d01174510301011081092a501e01105014200c3d51511003a4441c1401031049036a1a105144045802d19240340007190010405007040b1440744000e510120004070031000300c413003080c6d2040d1240d04541b101207907514a082d404c1039070004c98596000412900024041004e428002020011000b070680000c2041c0010541c1c190301040301a100307400d180c0c2c441d10040d9030020000c40600070031a418804402c0e07039580034290703000c1804000c15450300400000e03101885041a0303802150001d04030f83c42c49607030741805410202903060107512a500b0100b50030300540140110021280d0110060540c2e0340c800a082210040b0044126454000c010000b40841c0c404806540182c040c480540000c906d00900503002c43e18592050404c810400851700203d0000f0440c140c5c4082c0604015640b00408030310140244a00e029070340c1d00008107000070052140a2406180a8006078200c90b28811102030501660190 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 479421546 1250 479420296 479420317
    0x3020c090604092d06050c040f05010c08180105070204180501060b09030601090917070b0609060928110d090c14060a0e0613120605070302181c0c06110f0102 69
    0x300e00e14003100c4d09600c00c20840c10240c0c0d07000741c0e07894984c6940385400c1e11002e440a28200b98042003d0080d210096000c40003030000742440c0101106950302c007034580c09032040c0454030300080c2c0d00300c8050343d000b5401c42c0c84e034582c010300420035001200320104c80754130440401d9400d5803900c50f001c030700301c80d20008848070000c008004051603807030042d802026002d130034800c442c0f00ea45622480394200d0300c000a04010b512901e454441490a2000d000d0b40d03100041c0304511810030303102801050716440d00315280f11401d004520200d20303001109803000d800d003c01e506030300720b900088035490001980d0007441c84503c6001c29000c820707034540a0b44008510342e20a00c0e80940c04120f80551103000358802c1c07044400282821b0305110011140c1460180c01d64070403d800c50316549807404000280c4669548010305042c1142000c0030105400d0103610007000041c040ca08144020280c0e44130406540c441c69800b1403071002494032004000c0041c02c00b24903e00451040900c441c21000d01030094804c4181e4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 479422796 1250 479421546 479421563
    0x608101703070803060a0f03291312090b0f0d0b060a02030412030c05010c050a1206060e010c0302070306050924040812040f0b0103030f1d13150f0303020c09060409 72
    0x85a8450308007913400a001c41d580030700311003000103510100c2078000e0001c50007040f160140d00c17070600c0f0212202600003101d1035081400000c00020710400501085800d41114980b4031740c03402c03001d01b030305d10a9141d0020800c070600412007214050a84c0d0007400c540e030700813a06004050400b02802075a0142005030030242c0c01c10300c42480480c80c0e146c501c010042c040c0ca071400486065850303407400c44804c012503000103840051a40799491b000304298400d00040c0c881003010030f00e0084001d00364000845103504002014105001340362003003014030040c40e00f1a03030802460421401490351012166890491984c950b00c2a41003071034080c044920964015106515082084003006061900100201c41e10017080c540031000c0b50307402002501952003a110044800e20700c05000d04100019a1800c1591000a2070a000c9485214502900ca08000c8001ca00c11201c00b028512556154015090700b44002d01c0010506500017140c4a54020580d0001c0301d5482d0407083c0b0055444011010b081c0c0003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 479424046 1250 479422796 479422807
    0xb0601090b030610080c0d0207030c021e0d060b01180f05011407030207050603130b09070303030b030c0f1504151e090803031303050904060e060301050703142409010608101703 77
    0x14018903440d940206e0513200540341804c2c00161000301d8010306800c0d8000754041030020118140400032699401f600f50555650f6001000011245c9001400c0200070310703181c82e200c8407564020410f2007510080c0459480070542c8500c140e042d40141485420f00280e00300c1000780c1d01d0380c1c03110100e421580e0150b000d444032904250a20555900142021944041507402d00340400c21404216006003291400703405071910303508006090f00c03120b071107544c0f007500100b4180c1a140c2d541031050030040c9003a0360703171a58030241c00301521860082e54030070b04c881d540c0070001c18102503020160700c4542e007251041c1c0f541544118011181d800d164091003d0644c0108081144242584000d00740c0c1440303490214078200032840890f040c1e400b580c0c4030102601c001d0007441002e182c2130007503a030b02c040ca81c0760401c0031001d459001f1a80b03032000b40c0f001e980260708a00c4203c1061410059051135034018210208950303648600821150f030480320320f0312409034540f01040001950014280c0460144011804e04 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 479425296 1250 479424046 479424079
    0xf11040f0e0d0503040308220204110c06061e2101022a010b09070e0d0503222c0c040305060f04030f021c05130e0a021b0c010503040803060315040b0601090b0306 71
    0x41d8210403145003230100643e03801c801640e640c0181c070441c205103a051919080b00032131061428501600f810b100300c104072005240c210b06075010319841d98003241e122811117440c2ca0803c00018140d0290280b950000038181c007607a041c0d40c0512a241410742c610380480442e07454081c01c1329418800300d680b00303050a000ca00729912074081c1c01020000203002d20b600144c0c036a2100c0ca1a0701414401c8034104021950806003445002500000c04c40220b05582c015000d0a9018a041c5440401c081d4055502c0100309a95010310950b409150300504a415600744009640e03480001164102c00044031035140303440541c03010a544140d03001c0319030140001610072200344d9468000b50071a076034182101c000000e0340100203500500610b4103080041ea6404541d070010450300441000c00d107241c0c4501072040c6030785d81c032104690380076400c28003d60300da072503400020f0f0500c00d883c09002544200c003401d200c14010326560380fa014040c26240d80011590750341c4070120340c1c003048078010f502901c0c541c14140c45 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 479426546 1250 479425296 479425321
    0x50312070204021614160f1a04030b090601050a091a0103020d180b01091410091e052511030906090409050709020c01110301030f0f11040f0e0d0503040308 68
    0x1101d100600140c14200140201a5070200000341601c001015508013003011800b4000115651481c5500303900490400d100002c0e403142511401e20342c1d2040e203000c0311706840740300c051754040c5a0101780e02d846401d100c00900ea882e5028000e1620441c00950005001482d5214010000c844036038000a20010f103030054000350400000d41d901552106403059407000d803880e41c01c2e4654420201e04806504011a00741150b110780b161941c03440300c84090100c80c60150090b030040f22200913000c2140c001c1112004080e182c01141c000480e814a821321100140e21001e00b020007480b890170860110355400300f20703080b8000000203000d903001004026618144880101807a000252000c41c41140c02d40e0f400f0b02d072890719400300d0003584d0301088008132050300f0b000f080c402e002407019031415941161a800105280c03040c0040c0680c019101a400304804403903454840781d0300800c100051219044c5110141c0380046840741d20b4021086108a400d000d041036a000300d0305562680d0b203996400c02904103 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 479427796 1250 479426546 479426557
    0x18060903040e0115230f0c060f070206040b010e07051315030b0f0a0501050c0309031905060105010905090a0e0c06160209060612160203070204020703090e090604030210022a0d18050312 81
    0x14142c03070800c01c1d00981d490711b038018551f80316079000a058601e40149124550113024051108540192051002081031036505a0569103d0158001c0c02d07203825100391014480c00c1c00480003400f2401d40010801c0c01c024190082d0403254405000c1040b401007000800c0213109550b562003040620f0a00c119403292020300000f10581e001c03640303802c003044002841c0c4100e10702969031b0700c50000e00d004100501480078074018602800c0400c03015080100103a92134500410f0103038615914417210003030301010850b60411400c040c100350796a40001049045d080143c4405a00500b00c032004582e05050602c119030a040709500c00744203588443c00522000f1202414403011444240002d80c00759031b07113200030f0a0083c07098072000c049600c0c100004000420080c1104050b410481c10000403d40206152000c0500c0100059507000d40507803200f07404454040641c075090301c0c1191358610100004000c810301640703488104400301d2000b22482034103601d00074550075030450303126045c041e481c1c10084d19 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 479429046 1250 479427796 479427857
    0x14011505040504050408090111031804050c070f0309050a17060a0b0310020d02040504050a1e0c030e0712060b06070807170706091a06030f1518060903040e0115 70
    0x1e107031a50301d40025003a648107550540d18000c002404049960308007212400c040c1041e8040c504001030180c3c0104c0424620f401c0e28055611240010403d891143c100d40709164008444407100040e4100100514070501519010b00d0380050041360000c180d0307010080e1007040d900240002e0ba074402600f0040d083c4600340700d0700340c13140600303007a220a098000340032002000d020050b01c90740f400d0308001c02d03543d014160404052808032140311801825543d400b01000b48000450b10340c8003101c00702c0080481c8243c0c40001d004851000c20003e07900c1d84241c090b140509400d01c0164a031608102252052600090600000b0000b40000481e451942115030030111800c42c2087e000f600d401007034441d904000c5032140d0100110a8400092501c2c464108909500814030481d51694241e92407000d00704020055641000203200035144420304000d0b02d5105050300d00c01d0800d030b48000e41c3d94002d030240d400c40204000010a0703040781d4520706080041503582c2c0d20350144030180c0407a10401c00300c1030302 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 479430296 1250 479429046 479429057
    0x71707030512071e050a0c030e0f061206030c010311030a15090c0c0201020f300d020a1d010503040b040605090c0a0f18090203060103031b120c1401140115 68
    0x2100c0001600310b0700b0700c80c510307030344070043c8000d091a52807680c508800346040a10005003c1c81e06182e40c0b203d44c0420b090340c5400e140d075a8000c010001144030055035507148e40240300140040e0001070418109000300c1094089551070b0a6000064040e9800c500c1000c00e20142413000440c01d10054100340c105000d00c000440f5100d07140c3c18044241c07403460b00000041200b1502400071540c0c10050140b640c0c444201030105952402502003a00d2000e821b50300b40c80145806001000002c1411a0311b26100c42a00315039801c14404040c0c0045800703c030458018002000b58640e95010b8001c907482a85d201e4400b410a81e42d5594500c01050060300e40c5e40317184118450001151518481580606500103007000481d10740400c684a4402c0030034043d450604050f2900d0040c1c400040c4141520b5250501034500d0b81e5a0900c1284510402d001410710721803001640765040d041028040101e01502120138203c40c952020f40c281c40da00d658628002484400400000000700d201d02030170401480c09 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 479431546 1250 479430296 479430307
    0x3040b0627100e0f06060f07060e0d03050412080c1b1c030204080f070803041202010210050a0605040606080402010f0807020a02030a110102060619121e0507090e030717070305 77
    0xa0031480341048400302165030348501c0c10712802e10440c1043d9403044400c008160545030604c08a8454000c2d0410002a5803001c03600000700200307078101004e1000b5001c226401c0141c4114001c000d014180c40a40b507440d0104401e15102d03101d20300709031141c840444158900419922040c0c0300e410014011502801001065074601c18000a42480300362940c0c2e000d41c486003010505800c00303e2030f10200900e944101d40070444044080107980483e440718240b51032116139400180e0034800b80d000c244070460314080400c0070a2405034031110030380303e05580421140d61940019920180c040d80c001e4085001c00c96603111f01c0d4810710030641c0c08140c0c5c1c41030b9060b200c007641c082881c0c0454007400710750304a440030f0b004035256410400307590720000441301c070030001d44080803801c2c0d0b0b490303a03000c0e41da0842100c95004d0184281c0181248400740481a10300c000c194500f0039541319880c81c000d41c0000da04000c4108103961002095407440394106260302c03400c0301c3d50b044d000c040d54080380c0110148070b0180039 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 479432796 1250 479431546 479431609
    0x1d1b090406050d032a020f09040804050a0f030c090902090a09031b0506090f070e070509040b061216050f0a03021803160e0c03011d04020d021302070c050603040b06 72
    0x1803004400c4c4242c54103a0682c9080140c902d030703140122840240c603101e1070179403c0941e0390a43c01079036604d13094030300685030786460504043c64410398009541001d010000040c1d048400c190354001c07030b4000c0c180252004d0703c039030408040d00c400070006540040f244010502500241c2c3c000071145100307040c605181da062400308500490622002c0e2100d4000c00708001b00c0d15018020740315804c40784070103090400c0c108014101105000303002c10003017100210350030882d906c9541c4502c0c0030075002007406454040100e45040102c004940e00f51002d42d800940b144141d0041c0e0645001c1405a0b12300b80c10420300c1101200217411000c1d0301000d00350040e86002c0303991020b01484c45c0c2c4903101d111038a940c5041500c180c80d9114082d0046240f0401000100301461a605924010014605140049807175500000e034040c1c80468000e90320500c013140580e64030764254004c004692080980710800f41d652000c220b200e000032200608060001030009403186803030220100c01201001c403007900c5c1d096821 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 479434046 1250 479432796 479432809
    0x309140a150e1012050c19270e04030f090302130f0f061719030f0f0c05010f020309281704080601030b010e06100905010f271d1b09040605 61
    0x341070001245081c605043d04c8611030043c0e5510074102c407103052510a0000e4581500304e42d0030641e03820003062903e80c902903140b00c500800e10000000c03031015501d072192250f0036040030a5a0850208400c100311000c1c003030164484100702c80e0001c16501022040c02b86580c0a82020400100301030344d81c00c0c080c90311400303d1003200090500c002d031105c0000038219045240021208108203033403618008607001a80c405040c3d294070384903180201c0070440328101951480d451140c014519402d28880002d905415405036100f1518981101c1003451300718200c5d241da1100305851180300f0005003030310000c10008062110b44551075040f0303c0c580f41d0f0310070a035810b0610a0f00111615010313200100a0452150f001e190407040c115082c500c261a0f088015044002d11b07c40c10f418882c1c2d03c1e0441c1c1f106800388045080311280388075148004400e0108100146c80c890158100b050707030120707401b41a054026440340c401c0f110111400b00c44050f6a66072400c540080d0199907210751210800304480d25000d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 479435296 1250 479434046 479434069
    0x30b1512010903030c140904020901051204060e06011a0f03060d0206040608010f06030e0c040b040e01020403032001020c1009080d09080a0e031b01050904090c080a0309140a150e 78
    0x400004188a20b45001400d645c8444c4104081107082d400017540d107030030030044441100007210011303038410180380140d0701d40c02101507218440305080108001c0c40460380001c04140e07813840550b8a030b6a21142800052070344e100c05c0320308680f410700c1000303290b4504070f0007103400c03101c001c0c41588030000d10f40c000303051070340560003120003d4079a01c01040b00842c2004500301504d80d9043c240040600c01003c99a00c4901003070f094400d0351155000840390315554844070140807800300a40da9107441c0d09015000801c440d402200d015840da0103a01540700600c00c1e2405d9080c06005481940d80019100e400381080310740aa5111004205191140c100d43c894908007620600545c0c3e203400d42500090000305c030100c0396600030780002002e200c0403484214601803450090800301d84a0452401040007003460440003402202180d8020030400e40c0060f14604441c0300755a44049140c4800400310810320100200360415947d6900b4041c1111403005c0c5070340801e1500e080407990b0b003040d00181625200 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 479436546 1250 479435296 479435329
    0x309060902061306092907060902150913020909061905030102131e14060706091b031b03111003140f070f02010b0303031803040b0307051201080115030b15 68
    0xc0e24000c004c09034100b12682c0007041c180c151500d01c4070240b50040c0e08400f4504103038000010014000b03041044e113034024050280c001e0040b0389059103454642c0b945a001aa900d417080c0b03840252a120070049008603402d081001d0007181c85521a0001e100c40d5080d91000c1a54040300d041021800da00d00744080c00882041e9901070b034000e450074811041c00710800c0030303e80c1c618030181e00038420f84441e2040101450419101982e0b506a18148000146001d0100800c4c6041c1545043d02c0c1c40740c40325151050703d002e880214040d00c400e800c80c600f07210803840020180d5030400b0014500386001144210f0040c0242404201480500c0d00c1803c540c0301100c4252140980e181071040c071641c0701d400c4c0500d2012a0008200a46030000003d0741c078040140b501d4118114103071580501041402a01c0007081540201602c90800e2000230b885a0400b4002425510380c2c0c000004072b007241409031803c484403004c0044041421511401041c2100520740d20145880300440d1400d40c1365100b00d01c906149 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 479437796 1250 479436546 479436577
    0x402060f0c0601091b172706010e0f01080a0209040f0b0403080411040c02030f090607020616021f08060f04180302071d060a0902300f0c0c0c01030906090206 69
    0x18180c259085030034001005407480c590001040170250401003c8807105035200e640c0d07405544a561030541040285840034509060b003c11000e01c4000054141c1682c2c5000d0600c5142da56040d0010309240091240d412103600c6408d81d078015007010040b20341c01902404d0304d0400c040007602c0f0030a00420070344007280010111010082845003200184401c000300b260180181c2c120014025506d0103509490344808200080fa110103030ba900d012160410f601610150301c0d000303011940c50403400c1d910b1040e0700034007032502c4a80c4051080c0320502240b400701c3c0c640441030344070075080c0446860704240329034105940d16001818410354601c03034405c19109500402101c0c0c00c2c1112520403103a030f40d0070011980400e03028000715603134030228803080c0ca0400b540144c40d000d1030a65440e09040504014240d08102054032120107140c1561501c20801c0f400c2c24089030326604011802d0f0b22903100c03540d880c0c1e000218691034940c8a0703000180418000da07000328100c2d035a0340000b1a0350317011700c24210200d01e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 479439046 1250 479437796 479437799
    0xe0703050108010c020d0e030307020907050414030a0f03050a0c0506130203011a180406091209060f0e0a060c0206070c0b0a020f010b011209051c0504080111040f030b0402060f0c0601 80
    0x9615000381805481c503140280035805201340c001e540c170350110f58002c061160083c01c05c030041d1800c0064401741c54005001e104c072410300181c0545954010701526901d0790501c050510141000507a2941803948140160003400b09a00c0440e06908940594400c21104021280201c0e0382000014000c1c941c04800400c0f0a071684101802c585409404a0003007030320318544007a1355240c0c0e6400b9a90b0802ca00e6608e0030b6503d51420500034401c0207801014000740121030500c8a60040b0350b90207440c0c85466801c41d4011076202924051080780c0c40b6940084500428401c0d54072614104100610207408541055510703903850794180307041c5e0000d070000d003030108051844036410842d103492014644001c000d0552840c2c00200000c80d0b600603414803603102c4c18200e041040c10082d01514481100c41078481b6000d4520082160703020b40300d68000c0b90300301044803c090710f0720400ca0303045604c8031880e01c081c90320310f170b5510800e00002001a40d200700c0c140700340d21107801c40200800c0b1004403d40079000c02c0d03 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 479440296 1250 479439046 479439061
    0x91103010c030501030b0703320609180615030a14210418050705070b040c2c06040908070503030f060a060c020306040605060301060807080a0c1502030a0e06040e010e 73
    0x1121650700720030800d41420010000b18090400302c5030480214500070800181a0300c2a117424080c40c8070300101d44030711403a41c46101c01280380550081c2011551207819031070b400c460181201081c40310100b142c0000c00031812495000c160390071803002c081d0654100c040c4c691036429101107888201c440d02e401c5400c20384821481702920f91801241220b50a00b0f2500f003c0d9942e58110b41c141c80d06454964600200d440280641c0c2510700150303009000004500d800d103003110580010b07200b900030001c003d02c1006810441c3d0080c1c2480c44200030403240f15903449400f0400580507030340050f1003140c0704120032008030764144001d5106449a140c3c451580c00c000b018030140340c8250384598204a003441880380143d40125030560025081200810180c0314480080c2c010f0071964460340383c52181c4200095844804282c4110132030040c41198002580d4100000258000a0005005070003c00c440c0001d54091512040032071409080541402d03260043c00317160b110282c0009490490740c00030450750 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 479441546 1250 479440296 479440301
    0x19060204090e030403030801060309031e0c050c0402091819020406081905070c020402210a09050c0405070e061309060b04171204090e0f12040608090c010f11010f09110301 75
    0x110008500151300c1d10b0318540b0001d2260700107000b00c1d810142c482d01c25205040c46020b103002c02c1c02d0070300d0842c2e84e01009840c0c060141140d00f8011105400342c400049030b6480c0c140300b9100c00010151010b011510348201c81c494460300200300b10104645807105503030300e242c1c5202070b0024080c140c44000300d5003452401050b1a004a0041e00102400e000411010351f60005180080d60b505990160b10b50032100b00c062001c20302c0c022044a21032500c0c0402c43c006c51907400c604400c50040c015a680c108030780c018003042d00d0044804c0b00110b007100e40440031500b0310f00020f00c11040c02440380155103442d400c00c036040c1c0b62a940714800d44c08000c103042c00022480314060310f6181071200202890781483c80552058010b503c80c20404950300c0c040c441d40820b00f881558444204038060b00d03503410034080100348542060040d0000500c000c00001c03040305002030300380035402050f1146074002c00508011140041d0151002c2c03100d5484542114907005640110505a44150903040039903600c5002c0c5401c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 479442796 1250 479441546 479441561
    0xf0a0209010b04140402090402091f110106030f03140c0105090d03050c09030615010e090a060305070605120c0a030e030d0e1b010519170c0405030d0804080d09051906020409 76
    0x7410208000c10080303212880e0141c0381c4c22000345c5d805a00c0e02a804000340007401865240f0b90803803040b008044d540300c0070302038a25000e4079685a4807142c814000009003200d14a002c010214803c0d01461408240240381300500c03060030250b0a0f141541e030381c0c415403c0d100252004c0074140e00c00712803643c43e2a018007800e580000003121041c140803144000a41d01d40c4082c060f102c84151183c8555001d034843c04408a5813034024003043c01b941000701240008110f184015940c50180b0f40000c103100d07100c2d004481e400007801000003420b840340c0d200c91306541d1041d600740703051690b00c6202c080850070910140c410041ca2840004900039134141d86428240c1c0c41c1d10890b610080b08406085a070703007000030b40c0c0704180d5000740e070301d102c0320b5155007607810b000e031050203005200e5140d04022100d0100001002555010b0307045d10402d451101e01907440c65810f40e0b0090001c542401004c200740115070080c2015409507003182e00c0764917015444043c001d81e4079402e98006400080502151400703008000303 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 479444046 1250 479442796 479442809
    0x30f04030317160804050708030a0905040b271504050c030a05010608060607030810260106050603100909020a0504051f080c01081801150b09030d110607110f0f0a020901 74
    0x70b5240c0008520f4042020786030110a2002d040c002c85c042c03000c00c00805028241286c22680d80f40c0c0c4e031076400b405c0d0b10f5031446051703c80c5040c14100c0d24030f401c2818210071800462501d690088440e444885680c1c0401002d9600000074030005460550345e034000c0f1400b0361010070710103a81c0c0c00c01c40072850540e40c050f0020028030032a0300c10b001c6151640c0e07086415450300361502050640350b0310f4a10649841d6540702d00c01c409151007034620040005c240e00810b101402000700251540c40090060034041142c01030b0b00c40b20312410130010060036400c1500c00520044c000c41d03c40c0e440e04009000c8407001e5824410505c045964640341c0c030703550740c210005084000300500355240d010000a00c0440d008008035400080c4141d43c030a00d003800d400c48140840f0b40c0b00c00d52240740e01d902c2e003a410340e005400024480e11854004251b1113004000b4000040351010182006640c0c404007518081d604c4c10300c500c0d141c1708440c0c0c030790061030301409001d84c0701c001800580a403143d5801000340154041c0c0010 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 479445296 1250 479444046 479444087
    0x702270604091502090f090c2101051f030f1409070e250c1403070b010603051303031104030c080d08330f1809010608240612030f040303 60
    0x1000f160150b849000076194940000d80c0c0c41d0401004500c2c80c441128029400128a00034414050740390405031094030030030002c454402c148100340c800c00c89020f00c00c2540143c051040e0030500ba444c200d00210b09525428046090640300c0101801c4a0b560446580811203070810701c0102c2c1414444280140760b41d45c45505c1e01d04046410301e03541c005d102a8118078180e00c02000c3c140ea03009459140b040c03904403000100c1c508070150080d850398440b40b0100c07001d910700000410814001c0c451217008464000d610219005a56002e4004207104513100b00980002d00c0700000007904a4295000307880d0020203003076940e20002001c2d1504101030000f1150820b0340c1818460162105002030071004140341050b06030f500c0802280c040711103d001180c002813151491801000f418010328026031203000204840da640d00d03d50b0703071200e1154a824202e02d0340092106030407c0ca044c0f007242c11160041c180b03580d81c1c050948440c82c41e440010141070812010904105241d04045203204490055810 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 479446546 1250 479445296 479445311
    0x81206040f271a090102120112030f0c03050f040906291602151803061027020f191d060412030e061809060613050105030403050702270604 61
    0x440812035034110030010708056665501401000003039444440c8008022141d513040010180d8080d510250446500b1a528800000c0c0100c0310030290100640540e1070300c0e000c000c400e500b100c0d003150301502a400c00109002c2d0340c1c441d1003150f00400007000d07000400a82c02c1d2074441c01c200c1401c2c880b418010540615000d50039110314803011130b25103480c5040000340e81001c0d8070015201100d5603200700d5078a41c0100d80b480c2e034005000e00a800580c0c00b2012107019981d07802104071584040c0c043c0b1005c1c0b0300110070b4580800340c82044101410400326000d800c2002e01a00718040c2d802224250703082044603201441c1e0650410795207116181c10340b1502c1d540001d4407010030343d0f500c900d01c180c40d0400c480400100602d8416461100311000051190ba500c4140807000007128545003078881c0305540100c08181140380100c200c4244660b0b20309503c8e481440c03c0010b4a00781c100800035024400200220001070b030760f103010403c0d6200c10070810300482d10810305d540d9603228000d00301406180b41944 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 479447796 1250 479446546 479446571
    0x1c0c0e15040b07140312040f0b0a06051003090f14150a1802090a0b0909030903010c0201050f13152313050a1506080a0b01090b010816080a0603081206040f 68
    0x44861003600211307036100444440803820f24506c00e6101e15035a28030300740188801c01410001d40200140070b0f042465246e02c5640c3c41c130003100c502d440340e07a6100c05030000c0710001a01079000b04410b28001c0c202c900028200d40c0f01d4012411051401504c9038004640700300b28103082c1d018581d008003c2c414100000c1401048035180110400800303480303041d40d4400030720b04800350340003000f0082c0003400002d05030402942681e900e0704a001c07a184203500b003040c1d0f1203500e40705201d0355100b40380003002101a030301c62080c0d400c01c3e100807503026150100300079419036002d50140902d840241d4550014103000300d130304000012405010b04105050800740c2d0b10300340410000a0000741031500510000302445500242030000c0042e50b100c0c0c51907001d5040404140039503440194125a0818401d2240c81d10b428011a80c4280440b002005007807141202d1100e24801c40a0f0380d4030905006002580685a8407005101e81180c01c0340103160344484200111810a400781134481e0020200a100e1541d40b8030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 479449046 1250 479447796 479447819
    0x90a02030717100213080a060f050a0c17040201090506030c03011d010806070305060609120102040e06240d09150e0c030714040b060d051314160b1c0c0e1504 69
    0x3043c807168660041500c00c039800c1858511002000020100c0b2052102c03840d1074005003203110f01201c0090b24200c00904c0b50355141c020034200764000e80e229101007408902e1041101c01c05407042c1d0400c0664540402c00717172a907500440c040c00300810b88948940c03600c555000c01180030b002c2111100c1e80c010041010110001c1d03196000300e12420080390a40c2c405c0e02040040c080e1215542d031100f4100c00560301800107500500903184101c8002c07056030703614014001c3c0300221300e40150020251500141d09041580081e01d00a980c0c45004941394081d42c070340c48a0700c14101030504403680d03582001c944154042100c0381040340164090312103e80740c04a0300d48040030a030364280c021526003204104580e100301c121a85196690420459030510584c1030340c515440c94000c941c08014018159071801c8006480c5018410b00d2012007191803c00c9580001d0750000301105200c802540c460764071501050280490080c45992283c05950039a4100000051214440140e150013084117100c01c40288 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 479450296 1250 479449046 479449063
    0x8010e0d14030a1418010e010b01020a02060304050c0627040e0c1212340503070f0201030f1d012403030e030708060a0b0112230915090a02030717 64
    0x41d042903842e40d032486080005880071490400c0d03e1000c00701001000d0040100350310760b0401c440020060405140000c170700720380c10040c04602690040c4000380051402a00455005220b8019214800410f2002c5000c5070008044101001c24060f00100c0100801d410550035041c22a000e1100401c80140c003a108d415070000240120075816521003014000c011504000702021881ca54601b40c2c14043d42d445c0b4620350760131034540001c80c01c607c103082041c100240501c1c0c021010710314000e103030760340d0000080610204a0606131074034200c0202c0070a510840794000002c00d854a14425401c1d103a500315102c685080f140304c410040d03043c80003a40021101d080e6541420000050350001e800245406030b2075000c000706100318420400c5210581c0c00c485a1158280c8440c000c0680a50741d40050b20046101c000d6443c265003c1e050030164452580354000f4510000d88010903c441d000130b03a000002c440280482d8000f1030814214202000f0740c03001400d19101500d442103090f4456625441c00c03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 479451546 1250 479450296 479450327
    0x10809060f0c0327030d05070c05060a0203070908010f050708060d050c2e0207240519031509020405090c0901091413060303020606100914060d090501060f08010e0d 72
    0x203c00a865058001c2c03445444411000c800260840c414021603038951107082c5610501c3c0c182404520f030140074201c080c0c1641e5204d4007501e100d036240d40f003c0b0002d400042811080100001000a50003070a1080341004d09034001c01060030300e040c007000752015601404140c05107030301c00341300b01c041030010441e400300080c119240184c9540c00c0a0002c91445010503c41c8454080340b803101d4400d8001a4030800c03900500340d02d00c424000c00480c2554418880056004200b041010790b001c1c81c00c000900c07008444c2d50600003051300c080842c0404a141540143d00142d90005050241d03182c0620070380d07030241c00c0d400308a1812683d1000245541c0d01c52140c90a4808051030303a503c02d0b500e80c40f0f0704000303404082040114540e01d00f0700030764460040d02d095000b006034400c0144014030640c1c0600507500c2c0552605040e4601406001c01d5a1100c0703540180166140c41010010ba002e01a1304028468900c41041043c10080502e00b1210b524003441d0040e805135241030901900400d000035a05207 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 479452796 1250 479451546 479451571
    0xa1b0e0d0b1f0e0a0e010c0507030f211415010e1e0904060518070f05060702060f04063f020f13150306170307020d031107090605010809060f 62
    0x1c4428103a0b00b03107520b064881c0d0101803003042c0420002e100308a079a2107101c841c0c1051040c00b5034200030364200d64820080c5800070304200080404240181c4000e81080c0c01494944400041c1c1451003075810200c41c20310140e0b5441e003008006001031b06661940010b08889081460100302e00041c2207404010849801028100c44000c0201440c4044044404000d880500b0300c2c81c1c00c0c604a001804c04841600710086240c0c280725207850005191401e07507523581503004450b8107040411001d9084410100da00c00001c0140041950b4202c0190006003d15143c04120880c3e126400e41c06603551030001c0c540c000f5206032144643e07000d0780740707112701c2e143c420300140d4510340c0801c520300c14804c00e040409104603441c00080e00007140401c03c91090f140355420044c42d51240112a102002c102c0e0090745940305121087c098541304007000b8a072882030170400d141552001c40641840c100790b221101c06651510104a103580008c0520751100d014005040e45103465280700001c950044c0c00c1d00360259 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 479454046 1250 479452796 479452801
    0x10212090a0e190207030305040c06051c05190212040308010e07051602060403080c0607090801020a0903060b010c02090f04051c0219020102070504020f09240d020a03140a1b0e0d0b 79
    0x990180f0703c00c0c48140141c40641d9650380038240600a0802510100c0e48604800c0d03000035a05e00c54420f0380e200c501c2080e00031105840f00c000c401f028100c054201558501099200300380340c0d0651004000d44e0030b00da5805200c1d4605400c0113002c8070300580c0300506805881040100c0550300000300c40001d103005c4281c400703400c82400072038104d010710f4000034024000002c0041d8080c000044152040d00f91343d0b104000310b40c803140014282d0189110f000c021a074414400d00c00124240c1001100040c10700d003003080101c090300000c540c09016104444031195800501090080900002c01e42c424084294000303a03a100300000d41d13901012402c00c01080444910300c04681c420300104000b0a4010410f5450740500c107540c18070f9600410682d48204150840c0e240c1051020b0740c0e80040d030700c4402c090f60901d540b40c05040081d5000c402c1c14010150b8401c0c0c099080001448610300034040348800003502d0702c64070340407405e000c0c91998103010310000000842842e9100150b03c0c600d02c0d8051103140454 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 479455296 1250 479454046 479454061
    0x507060c051c0e1002010b04150501050703120b0d080c0111070b160c0501050c0418050601050a0809101e1a09061e040c1e080c0414030a120806010212090a0e 69
    0xa000b105407030b13030100c41030074580c041c0c070b5054001001d19103080310b0420046498807514080f914551007410b011030b10900c6400d010074020214014510018a0023083c2d000071100001d1610369442d42c115800340011a0114000800b4400c1c1d1a4812100c101e8614000d2240c48600c200c540007045a10714500700c0f00c1c0402d009114031066402240e10030002d0240b810072072091540341d0000c0c00b40d040418400c420b022035404482c011140903a1041c0c442925000c000c1c08111036071040101104420711644403070120903031b03581c42010b2015400707440c0003201c200c00c0542001540e180315000701115009282c0805943d0300d0101c0b0941050003152030189545522541e8000c5011185030b0a90142c076081308030309190f411500e00004200840894211003600745016241644103403120000c84005000038001c01440316801141090300408903091039a4907510a10900c545080714400aa005e4040c44003e5030100309001e0800380c042c0c0e0b42c0e82132100181c04200c3c0000e4901c0f071030131011003036008035061 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 479456546 1250 479455296 479455307
    0xb090f040905010e072702040f06050307180e1503010b01140a0207031b0515160602130810090204110c0c0f041d0604170418091704090501030507060c051c 68
    0x7076546400c15174410680d03860f12000c1c4958a21454110108446003001601c00684221404d840100240c03100d00c07410000c0448060300f0092040d401d004900300c041c450003041d072914600900c42400034030841d2410501d03126241030030702d56060203681089142a6140c3c0c00000c00041c18000f941c169803590031100d0b04900e0168994400360116031404005810011a13420000544101f44c0700002d20240a1460200c1231080c2c5840b8106d171040780180368009010380d0002c0c0303902d108810790600034540b01c007490b9081c0940e028090120382d0b5655130170000c504242c000ca05545205014140c00d0200f45411183c4440d00050b440340308981c008020b51096031a41c0c80b07619103411036800300c0b0b01d0310201c1c0707013040d900c1c58141c0781138484030041e002d070080082e118011a07040e180540c0001020f00ca100044001522845008850f840400c00011800c511a24042d00040503900401b046030b5140d414090b0504021b030304070f1b004118195032003802044002582842c0c00c4c4860405551407003040f08111403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 479457796 1250 479456546 479456561
    0xf050a0e19090204140f01020703031706010504030c08030a0906180e04080408010c0807030e010b010c1209050411090a0f06050306060c010e0316030f170a0b04090203030a0306060206010b090f04090501 88
    0x40483c4085004a84414218400c04902405480f0b01c0c012080c100010f90380c880d0140700c0100061b9002000f0041d126060b40160780006040c1841402d094681e6554032420040d0b40040b4455400810b0300b10100e5402148071000709050b00301014006610750010100c0ba0b90f0707026403603401546c0c2e0302140800c103100e4100c4006000b510020060819401c000802c440c1c1e00391039800029003044401484000c06215003800804140c440e402c00400d6507540da860000c0c070800758000c2c010004800540d544450042180c14a40d21004035941c501480c104060002d1581215160710307c001d100740300c00c5420000301c07900300104640c01034855980b491401d000d00301c080a5500e0501004c1003260303505091042544950707100b0f80300c82841d2507001c801201d00c032a034402611300c00700c0c4110200b078402c50540c0c07210f91400805000811080d2460700440d00d1903100100d280002541c40b01c040021a80c180400c9d0701504d0103003405844d0480110010b0f20700000040380b18840d41d5a03200d01c50801c0400d520101 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 479459046 1250 479457796 479457809
    0x21280b0109320604111e0a180608011a07020d08040810200f130e0a05060409020114090307080f0a1b29121317130e0702070e0a0506010f050a0e19 64
    0x501c1007698040e45051b58000d5141c980115012081c0142032200d50074900081e61307016039030800542c0ca060411050b1500000740ba00f4038420400a07040940c40704600225503e002da1700c000d542d01d2030180c400d031030306020981010f0414a0610444c480e00c50310741d101e03801d40082d00020b0391500003400301402d240c41a0100361100039426400003800c00540c0740300e9031090f445550f041100b0368650081c0400c0d6240c0c80380090001c2e0402c40000c10b801202c10142040c00406000c99583c2c54a580040c1d18080c10030b41160a03d40c040091541000030300410007845034107403201402d00a150400c00c200711145204104c20320b0400d0a101d080030f252007002d845003800c03485548241070500c0e1070030410144c018002555000c588412041100581d402161241d04900203890400c7e0b1034510301000c4280041c24072800c6002e40300c1c00040c0210b0b40a500350003114805400602424040d002400320303c1d4100b84101405014403480403e160861f03000d214100041d12880c1d5040070040c806005a9103580040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 479460296 1250 479459046 479459077
    0xa0204170a03020d0302041d0c04180b090a0b060406080a02130909030e01050a0905041a03150a0e0c0112020a0e0a090b21280b010932060411 62
    0x54221200051001d040718000d400359038110340d80c19011000d03031045004a01112016151000c0c034480341c0048543c0c8545200d160506194407240d000400c031150f411011552a110300514040b840d00d2a142d50700203192220030068040220041a25400369104540c144154080069a03030034181d0129a4002070f05041a002203807240f0300d02c1c1c01003009044c117400103241e010b40300d40c0d41d50090080740c040c1026034403145c100c039141004200c06403922480e850071014040a17842496102000402c0d03802891540b0124035180c51074428040300c01407032800840394052000c201c560390b0800c01d14403550360800005a40c1f00c94004043e00e42c3e10304100041d4014462840008401c51325601800c0582422103200c2c1c4500b104075280c2c0b0070300301d1800e0790115542102284074248001c038606030400101580d403451904c40e0350380360115204000d81c00300b00b002c0d403944501900c801146082c50a50300800c441210005100c001d8125410300081000f03002d00d580b404150709801c220019aa100c01c030300081c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 479461546 1250 479460296 479460329
    0x2060307050d150608070809070b09031207060e0f0105010308300c030a0b0303043b0c070606080a03020604030305060607050a1a0106050c030708070311162102090105090a0204 77
    0x80c050600c0f01d209034000104200c01044545210b440324a001d04c94420041144609100c1c80a45a0340201c06495143c40346c0c0d0030740d80303180301c1c000003810025000c1c40f0005081031101c070074942003036401503580c02c0503450040140700103400311003500c00c0a0590040544050009840e204881400d0624415050341400c1040305801801c4011403141102c03080500c9280c0f81c40050690b0303400b5030300a250b41c4525072064000b40005500312080111001d00d010320204000101d0803140480940e106d02c00c01f00002031020030f00c80d507400381d80b004044040041c0b42c0354140307413402500c0706400b80c00141050340361008034229564207001d407505940c0000c26651850501c3c9054001003c00d043c0003e421404800000380b8a80110306444100c07150b41c001d1494030106581d20305259220000c11003d101205860205c059020440c222281c500c540c0000312050400450110380d441c10580d82a0002c81400040016212000c0980c11104260f1342480c0b1074540c0d01190001c0c1c081e64001c07458542d6002c20 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 479462796 1250 479461546 479461571
    0x60d0b0405011d01181b0b131a16060b0102100c08090c09010b03151311030703060b040f030830040308011508010b0a020f01110d11070f02060307050d 66
    0x4407550f020159542000030b54503600b800d84890b182c0d1140205072040424000c0350843c0100545031455010f01400d01d600d90045041c0b030b802007120f103a540c1140d01824010014004c0740c1d2500400304030764850030704040511342a03440207070748001800641c58040300d01d1140d00801c0054195440741c01c01340510001840010319010045850700b03c244900308400000e030400a030114140e5481500045c90756071344107a02d100d055a8981126003041c81081511003032403403071140c4179426264404091345c9040842e0024140e8805030000300001108020411216481c40080b004076980400c1c01a114003120401881140170180d240000c4a5025552011840700c9825240300d03600c240c880421990321240700c0119250071303001560100e0400001407103103824181c0030703012904140c070480c2d1042001181d940e09654a6102d0085003480101d03964a1500403400303066440c60101000c90304100080d11600c00226170020042d00401001010404481c891003c40f4074070010b07c3c0c400d0040034001003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 479464046 1250 479462796 479462801
    0x1214010b250506041b080a030c030201290f010e060403080406080a050f040f081303060f0b0609090601080c070b0c0301140f010e060f1c0609141e060d0b040501 70
    0x1c8500aa0380c0e00620380d101c0461500e40e034041e0750003400030002980d591791405820200317820905041007841000064146040000120b520311039038800010514600d006402c0d105041c100b03842110f200340941ca151015002020034056007100d014200680c0da000584905940c0b07015140c0118000802000f84940300000b84100c61895803200f01c80e43c2c4501b0381504980c0d0584103c0400084100881c0200b0884000c1d8004a8002e950481c07400c201080d0300c014804d040d5000715200c0703882d10002c400e13001c41c038418445104000d0340c1c094540003220740010005040201007605004610f0082000c40c2d000b1402c3d5107442e507111201c20340c0d03801c0c4200b82d614560000d00c507c08000780c801400540508001121514101c0181c480c4a6103400d800304104a44d0008490690207500620079004040707003002202c20800d24800d00003c00c2c40c100031120041c0c46811748980007a140e010140584000000c1815100d00a51911218192202ca0001320040302c0303110013400104030b08003480140f20066 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 479465296 1250 479464046 479464057
    0xc0d06230a1a010504030c03121b1104060807060207230a08060415090809040c11150121030207090c031503080901030506120309120316050a03080109060b03071214010b 74
    0xb6400c190403030a100c011070315072013103000081c032a02c5c02800410005155000c0d280c06840d45007051000c3c0741c0307a503403001c2e0b1504030100700b40c8101c03071030300103050440c04c141c49150041c08006010306159410710340702a5682d00e03140301e400c0607000b5032075400c2e018850b070b02c41c002c1d603010005201100d8659241400e43e40d6243c10394056940e40c0f6a4441e482d060180f510810803651340c0700d96810b0400540c08100402808807030600018000030300b08051407414240000c03281c941000440700f0941d410104107038035aa40e85082003000c4003800403840003085d0001081c4044030036506000c01e0302c60341781d4401c0b8040c00c401d02c16204407140900000c0f00300403c0c039000d030500c02000c1e40c04029680e9a0301c10001d03800c04400b03021b1400d4000b08241652800c0046d1164071080003401140d2400d4101e8008042860441000b511907400400d0103204042d48070724080d0060002000c240036650a00d0700958a0f880068071400a02c068404c1c424510741c20b42c0c025091404a1314131b1324115603510388035a8001e5200 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 479466546 1250 479465296 479465321
    0x50a1b051218030c0d03110a0c0f0201140c0a0302070b030601092102040903080a0c02011b031802030d0504052d010c050a0605090303070f1d04050c0408030406030209090106020c0d06230a 82
    0x5040c42044d01030000c47c16150303603001642d030b41c02440d00661101d00c107080203800203034108003815041c440c4c0100d468000f41601424000102036100742130030000d0400f80aa00072071442d440800038031031a030b81c1c40074828050ba0b50700030402d5081e0400b514540740840504a000790464144007051040c0368200c000544a217109060038071216848040807400c94070503400300448190007116152005200b5070006c0c078071540c01030311002c80c1310064001a05c0c1002e40035400303002030700024040c012810314042e40c0b552000300c0440e16448511300d5049c0c0110240b03c1c0720080c1080341003001d402c14800c0402c40221201c3c0c20010820090400001c0581c89600131212000030485510010414902c108051030b44207407007000b180600b016403020003000c4c003800340171103541040c1880007143e60407007840280010a0316407030060741d650307080c0c06000700c0520582c1f0000642d00a02c03070005103a201d40400c05036441d071109000501d8510043d0030100141d600c002c201141805508100036018aa801684950003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 479467796 1250 479466546 479466551
    0x40606030209070c0b0a0c0201020c07120c0509090316030c080304211812030203120112060b041806050a02310e0c19030f020d050a1b051218030c0d03 66
    0x890f0901982c25841c0d004004001c800f00d00005281c1000c1d90303000c465000094400135203080e114415407403408021b6008010802201c440b9130f0204098202c0070401048140c3e030002003860000745040e1607010b02075a85c0300c450180005441014442c1c406544216480040f1540383d003054100020354003014a5000580f128201c5e8512901d4040c050020a500103c404020182e0410720440204c0708851303001c40031761006001030f5111070718240d81035010b0064a141c08919402c40e003000e03001d880b00c00300c0b400d015030b15120000d0701c030120040844000d140c1054011a1540710b66032244000c0c0b14140300c455220481000b01c0d11001600c0b081c070b1849101704150071170188d40f50501c80e40741e1740b4243c41004860108000d00c02c0203910351002680d148a55080c0001c46c2c03016500600140d030f1100a0b60342c0d00c2e56031041000403480c490302c00c088059080001100e00c490902c400034009101d030300c0d80c2000000d602c80c00141089080030400c161a50082d040d25214000e0211300c0d03644116165525011a0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 479469046 1250 479467796 479467801
    0x90f07170714030304050405070503160507030507060b12010203010b04180507090501080a06080114090d0c050309060d0902031207120305060a0b03041a0c09030c010e06030f0618040606030209 84
    0x1140c851502494a5048041d01d4a64640b10020550007046034200f90140020300002074555103c2c41400d200b0f110070340343d6907524034184540020503000b95800100303120040c00401d0104c1e0b40b0a003610141a809130b0002410102c030000034500010403500b85200e50700000c000708004072904060401c0b908110200f802d1051801c2c00c02003903c004490420024400c000204010b603c5213600300d4000ca030902001481d641c54400c142d0944a0f510004000c000c0a8001c1c0310860741e00b0003803c001c81034540f410364100000d43d62419101c1c07041d0b085c0d1710310404000ca0000e0402146612980d090f683c010110742649401105c0004180c200c14400da4800740d00c4001000360b28040d01982c0d00ca000c005141900b4035040c9001d40040340c0001c1c0043d10700c049901c00700900582a040f00c3c90055607090940794541c04080205890140300c40b00380350410000c101410f0490315840142c80c0c2054001d03210701007554071800030030409071004108082c81c24001061005014081e400401030340d0080e2990031042d03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 479470296 1250 479469046 479469059
    0x603020a14040320011809060312110607051c09121b0f03140408010e06040209010b0a0903020d03021f02030a0b0d0f02130618060f060c02150901020a0605090f07 71
    0x50242d880040e01d419181c6807410a848141041a4481e29050600d10302450700810746a5903e05142c02540e566503550009006100c491403000307815000700d00d000f035102000004100c1e01c454014154109000010902b00c201c1611144069000150005c0401805465082203040c045803440f40801050381400d107806540180044407000300e80200382800546032599003140c02504a05000030b16540900c00420010700a00031a200b140d540e10043c4000c2c180360041082803d01a44120000300f420403480c0001c541200c1c21504480d012103824404c1019414264201000ba000a18040201641e04014040c49601640c00b45000b04020051316501d6028800c1d0215100c03070103020b555110200900519002002c04259820220701150300c5940c0c4812800b4106c1440a0510f05912408280411116003018030020580da14286207012040c0e00490030061000014003013489000031121300a9008100c030301700803540901c0410007460801d076a0360701c480414210000ac1d005c3c8480c0051035 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 479471546 1250 479470296 479470337
    0xc02030c0a081e0a02030313030903080304062408070b07050312011e0f0506121021020306061903020607060e06070c02040b031f1a030d030506150f0319020c070603020a 74
    0x144844e90300214039540b10000e911020007030785d0000b10b0420101200200c0040e800d40d014500035440342001242e017040c110610807525420443d603200e07401249104025411000030a00c08482c1c84c1c1c55003e94503c0386042c02da003507110304c1400c4501640014000100042201200f10303c2c211000c1c90b16156544802e95074400c11078621602c1d42c0a441401829811031080c078406401008036a00011450380c0c4002c070107608030b40301c200d04a00d2100d41e80c415066080600c18554044400c0321310106198503030400713501200d00ca000282c010503020410030304101c4c0c50b90140a60b695228202c800501e4451802030003000340240480c003d03414401c100d14070303044c00030305031001520000c403200105421030030800042444480c80714141c05c4510091886480502c464400801d180c1d0b8003203503515008062003000301080b4107140404401304056110990010203894001c52802c4210040c54a901c2801d000b90040d44981c4180d030080e60030000352241c050b4001c00c240c09498607604405440300f6036a554 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 479472796 1250 479471546 479471557
    0x31c0f020d05120127091217010503060c070c0e0f0a0617120d20030603060f01150507140d110d020102070203150417070609260d0c02030c0a081e 64
    0x3c4015078800107200301d1007a0441440300c403002400d031082018800c0c01c10000d40d0f0f92088150741030001c41040c885504c1d8001c4a5582030081030325810742c55403400c008030340c1c0d54000600d8800c01c9500400c40000f0400c462358450002c1c07039403c0400c202270400031802090f0f040c00b612801c00143c6000c1d40003030321131480103812114001b010302074000790070070b07503010300d06035100c020711070107099581040080301b500b9003c45a040e860200050798891502c80705051030498040c011203059034501004000c0400d484851181c003e0140c0f9203242c950405151201c910700880c10342e180f180c000e40407442c2d03001e90f000c52149100c0040c54103c40000495a0050f0f00300c3c45071090203501600010100d00000c00c9040d1a1600144181c0c00c64044c043d2048007240690001d2a00304c4e00765480b0020081408a48101c002103030044400804046a602440c002c0903c1400c2031000140d80703d220070b410340d034024819105200345403000c1c1c54101c1c24624104180d9403207540700f50403054031084951585403c4106541 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 479474046 1250 479472796 479472817
    0x90b011704030807030608031308010b011803030c0204020f0a08040209070807020c0d1403040323061003020f0f03011104030b16022a150301030204050f160c02031c0f020d05 76
    0x840d50380740c54a04580c1c1020060140081c5626100000f40341c1324100f00074015901d1000703003101400d050020850a45240c000d0b454100f102041d2520f14490040c00d5000480350301d400c190031120540e2010030041c0c0a804200c114130800820824500ca03044051f1520651088132a041395658048080d00c40c104181c4852005921000c103900050070a40107083c42d40740100840f035616050b84440910f5503205070011a122040b294050804401d01040584011603e0004d490f00e07160810406040240d14803001e4880c8080a0491010b81c6400f425000c034080090024030412043c2c1405600552142c40201e92504201c4d000900c1c80c0c0d08000601c0300d16120358094103070811591014511404c51480701c0c00310219005511b401644d8440d1825502c0920b1500745031a0340c5140100b004070b990051024103054411004c1088019030204d08034601d0010b410948078040e09030011a24005134118100b18000300504907160030703904925683c590388007036822a0070b6003941c002c00f101d8a000d584d2200 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 479475296 1250 479474046 479474087
    0xe0307150507060b0301050c0a020d08070c1113152c070c0302070e0109050a0f15030b07050f030907030605180606010c02060712030c0311120408030709030b01030c090b01 75
    0x104418801c500410304640100c401068000c0f64034001303402c45c0c0080e58803018a8100080c80e6882e03e40500c0000c240131807508007400c907442c1c030307807030207441f0f00c1d03140b032000f80322165081c210703101c603070b11560031f00148200010704006001100526207000002070141c41d1280011040303081d041c88110000910004035815003503000d071602030b410341d03101c024204210198010b4100c0441c002001c808201e0080552044c00704443c20180782c010102c0d441c03900c0100c070050800d054002504007a284003400c032688100301d88066651000115603034020981038008101c1c002062101542000a00c841070780d00500c42040b058981042480b545094130b54030644c10b03081203000484660007a05100407960010303280340e02c0c02c101c6aa0340000103501020500100c0c2e929810b01c0c0382c1e1545485402c41c00540c03461060304d0484003d001c10308500004100030720001c80000040d1580f80b003105450025907102031030b0703450b42d40c580c41c040c80090070341c1c050100301c680b0300004040c4940c86400c10b1450000003c445 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 479476546 1250 479475296 479475329
    0x20109090f060b030c0322020102031e130b21060112020f040504020309030c0705092406041a0a0206101508060f120d080a06030c15140a03020405010e0307 68
    0xc04000e0400403809041650351000300280308100200198850000c08184542c2d034030b0b200302580e004102c808540d1080c50211440300d40180d80002c00c44001ca0a04030b00c010030407488015480451042c4070a01403440030507034000600d1814000038205000c003051825200000c0b034201e07007485100440320140002d581b2541d030320074401e00e40e0042015142c0c1880c07940c50107031190042401c0c0c0e802030f14071450315070000985405500007801401c5c09800c0458500b2054180502148131041c0b0a030081310031044440440c0c2c3d40c9640d0b28049070005d082c49240000c030818107104a406941002071204054012140042c1c0c40c81300340b01e900d1058a03460003200712501486101258194001403e05030440c80448890030290307588800418112072440040482c10f101c1e0300c0080a040000d400b0701c60030390034004280001030130f540c44042076500250007880254090704080320008209001014222000901c03584903640c03507001042038400a0b00ea900000301048281640c03410144a50034202803502e04 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 479477796 1250 479476546 479476559
    0x30f120a08370204031208090c09070e0f0a120812010905071b050102130902090a050118060c05030f040905070e030a0c15260414060f1302010504150306031e020109 72
    0x2e50b050688403440c0040c01c043d140e0355560038070b00b0901584400310350390008000d101d5900300725800f403001c81070f54610a0340c10401d10140400014001040c030038805402001d01030303280c0d00540001041e150410081d0003240b07027000d10403030340002c15400c01c241c1d950b00041b4005400d40100ea000702c040342d60300c0b88141e8892130003003135600d0851021100781d5020052071203c14822414040034080305e400050307a9004a00c2004141081e80d80850305010b40302d011080d9203480d0040b04001c54105060580030f029581c90a1400d611501d00c1c12070301c44030049008130301c80c1400d511080c4604030940300c0c0c02e00a51780402300f41e0780b8841d1386801041541d80003014001440000c540c0054400c140c00c02c5a44020b10b40c10141c41080000c0740e040c000d4044600f0003003071040c0b1112031000307490550f02621090504075154a10040d00410f081070513428150700c9800c40e407040c01218001c00302000040c2c107030012198001d010741458030090740d0145201401c1e900e0b6001c2042810052607051b100d0318103617460501c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 479479046 1250 479477796 479477881
    0x5030a0f11030907050102010b19050616081204020f0f100e010e0303070501051509010806150d02060406020d0e031b041802120706120501050907030b030f120a08 71
    0x1640c01200586581c80a294203000101441c001c01c00701010b0004a810034000900319020340b15420f1082da500e00413660140401c2040d030741980e0040c0c0340740c0e0b66036403a00c2007403000100c1e8000c010500d41d80021051210050215a240070f103108540c9101d012003002e0030864241a580c0c5060780c003800300702c088601140680211001101c06041003503005600030002425900301d080291a41d075150020000035036002d00103000c07a0b03002141c0311005541407120780c65460100500d41c00d07030343c21086081c424959500d01044030706940180941d5466880d850000d40310320000b039481e80400d00c5e1800c83d010a03d004035000b901205001d0f1007a0000c1540020440600214072404c9001d07404490720101503120904006406c648910060000707501e040745c028000b0054685d5002c2140c54900140115031b40c00c5003c0d174100c40700703260203d0784420340c40000703090020305080c249041c820042d14104401358200507005010054070f48940f0ba507154401ca21142d0039400600f8804512800d9000714440420b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 479480296 1250 479479046 479479061
    0x20304140d0f0546020d0611040f050907110303060103110f030a020a02070f080705040504080d05101d312a09020c0606062d09040506030d05030a 64
    0xc0036402202042a02c8190908043c5103c0e8607544501512000011801c0b22603e51841071418051310160b6031200d1144c00c0988516009110310303100e028140901c9041d4010070080c42440010955403035503140900594a407030320400340071742400340001d1421030103031201d02845903208020b1407540c0e036440011801060b054201d401a414140001843c040c20b080c0598480c05811900581c1c0d0392100703c0103032601d0083d50110030107020704482404441008107601d0200c64013601c1c0890962568a806101d82c052414050186440d083c2080850040705c2011030850700d1609c82800740c1c051202a9240c059400c8030400c0540c0c2004e01e119400140880b00700308545400340030703c1402d24440e41c50b045201307401c51142601c1c00341c000050f40b912003842130340e500030545402c045141003e040340c480d0f2212401015a4401d95000c104000b0510440840803116400c0e001341900a4004800ca0441c9402403440c050050740703440e00080c0c090800141011540f1140d454032341c11560f030300b1884030141c11034 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 479481546 1250 479480296 479480303
    0x90f02070b0606030a1e0606090506040812031b070b0115030228020c031608060f04150f0b03070b0403290a020d021603200105010f030f0602071e050d020304140d 71
    0x21022806c603d16401c140c261070795400e0401c046030482c949600149021280d0f0030040c031a11040000300441d000002d00303036061400051209881342e8840f0f40410078201c2c1d4108503444404006451400c0108610305541030b11050449040c40c4440c580c8110308030f000702a80c141581030910380700c0710003000d0108814002c40580c41181c6280b0a10705c0130030300744070784071042004204e51010140281c08051100d2030340100c4040341051185016111087e103101320381d41083c1841e03078410a40540c45504d07040a815070001400720b42d407507a600e00000265a100303204c25104030442100010015501d100300c2c1c07003240c0c00510611095243c0c3da25101c000d601240c81508800d03420002d0303403982c042c506070b50f00c1e40c0e80c001d450b01159444c80700311407000b806040010f00c1d03169241c1300c0184014132101c20000150b94101c42404001c03210351615400a01c00c00b035002c0d2031043c0b04014604900c03142d45146a03418880c0c000c2e66205062201c0c00d9a4a008070f003d0f00a521545400302400c07070505042d64540c0a02 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 479482796 1250 479481546 479481551
    0xe0111070b04030f06050603060606042d0f080c030102070515070e3a031b0507090203131202010203090703110414070f0306050906030705010c05070b030709090f02070b0606030a 78
    0x1d5910180c18107030b109510840304468600a41803d1161034445c4a6000c039080e0007500e42450481c0002e80248600e0107101c80c14941c1111400707140c8a0000c5201c011440c4a25016000d03441c1c040c2180040c101b0310808031180306031000c285841c00e06000360317946a54010000d14071128400202442130500800030380400c82c580102c4102a0344034103c0040b001c01034610f812002c00c0360200c0c0180c816201d00c418035460400c051000000b5440180c0100072078003812007204500c8076180050501010f64807800c401c43c0003005100c001580119001e540314456a408800406454016400d0780000c444003c1c2c180c220000c00c00104000f114071040e5a40000e00c0081c0711414020104081c0005488400000c3daa8080e202038480d00340c4101e00144c0400c0fa2100f02c54600310000942c1c40d595800340a04210440740408204070341001148054881c035410680c5918103508000e141c18554481e4194540c1841d814900703001262017190911900070741c100030140c0d500030a005c0705500142c080440650f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 479484046 1250 479482796 479482799
    0x60906070305092704170c070311060903060103140c03060403020709050c0f0a080105010905030f07090e0f060403111011072334050d0f030207050a0303050c0f010c0e011107 76
    0x400c0021081040c104613804401820542000f01000320740ea410040703104801c21424161001c0001c0400c210395200c2036440c0e00c104403201140071401069403554142c0b08000c000320400c8121903601904c9440482200c1d423035040e0604160356040241d4024025070001042072240b400301c1d8000940c00300d60070b848545800c001c0103003170880d070f0b101c400e14000054218005004035a0700001c40d0307008020850050000701da000c0041900c0d4400385c80341182c200da9035959691182020302910360581074040545265280609028041046440050060b4061410148010b243ca445804130903001000318605050789030781c40c80e0700380403501c41c7d45515503c1e00664020640d010400410000d40800c0d550a45030303407506002c9617064455102a103240a46a02445a522480700102250741c0080e51015411004d04040e402d20409030000c03a0441c1803004080141500b01d00189103041000d021500d007610780c1501c80382215460034100c0005a03065038001e502d580700d0001d800350100000165085c25 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 479485296 1250 479484046 479484079
    0x3050403021503070908070506040e18120c100216080c0f160320060a081902070f1a060a12060204180608060106090f05060a03140414010b06090607030509 68
    0x1405100e542ea040d018000040003100c13680030803480b00134203086000300324050600c40011400c0c00f80b03008100504281d1400035004a852064444c080a80d01d010f95400a0700e0440001e40399103c10482107503445021030042d000542c0c0e10071201d110308269222020360000740d851004030f0740001580100c2e0310807000b50304000c0400340700240c10001402c0500c0c400f5850b42c81c01c1c0c1c0c0c0d05806882100c0700c0c600e01001554170b45d26900215a8aa981440c200c40f0a13500e14400040312800c6103040c02520b407000c5020003c0040c01d03e4584c00b041c0c0900704054282d030b41e00741d240d08040f078200c850ba6003082c1d00000420815146111141e0342e20700c204005814603854901d0740c1784030000b5051120116440782800c02c02ca0106000440c05007810303103801100a0308002c9051620201441464040c510004410451600c44d601c071100c440c1106266902900f4282040e400080c02804e203244103500e8600c246045103400f01c100c0e1109007020305080d0608100f43c606555540017000707081d802c03620350300310a0b511 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 479486546 1250 479485296 479485309
    0x506180d0c0f1a030405070501050a0c05010c08040309080303061302030a06090905060421050301051009030618050d050a0e0d0204110f0d051b1806091504090b0301090317040305040302 81
    0x20b815403030303507242100f442c103000c1041082d5601c00d40c80d9000c00400078000401c0340802d200c0243c4c0d00a080490340d4889c0d2031000c840700c884030310000e8000d500e04240c892005504c608143d0040d4083d6031101941a01d45441503100d02c0180c48007a884881241b0300e4201411039005107501c100c01500c0050403d0396100020240e03000001d04a071a80c010710104410400b40081c42c400d2000148115601d50754450400340c0b082c80107004e01d0f4854020100342501052207090840f0146501a03000d03c8401c1151000005009480c0d0080311540910281d03010580d1284081c0c500030394841d62041c4800300d030f10003840b4001e80e5855060fa046916100401d202c84030701001046440c80b40019650340e103202003401c100b141c0010b030144020302204c001e030119021511301600c503840140341401c3c050001c044001800c1c3e1260401103908280c0d80c60354601c3e00c100c2080500100d072500700042c09a103055108140c2215200d030b4009012405403014014503076030000403640e10612034148680343c0741c1c0303c1c2c0000e940c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 479487796 1250 479486546 479486549
    0x10e0f04020c0127030801031e080d1a0103110d050c07020d030816080402310c021609180b0703060b030c0918040819020102041203020609060f010506180d0c 69
    0x2a6691a0880d2004c1c20604c070400b8000c100014003032118003045a80c000b011010107110161050f454510703500210744041c0000c0c1c200640c00940f066540003101040806042601d038003040009040044800c254000e0040c0c0740360b40780f80c0079154070b411002480e9200418000d04610003000382802444010780b2a0600460390500a881d17400d09072030180c800c031140c00c1c0c12a21000400c50200148801600c0f54207904552002001480d40403a80854280c420440c400c054101e0380e5050603c9c003030205070040380d8000d00200c000c0024030495217600380d20040e1a009240d03161071a1800c09080d0104129190302500044e4900e4080b07070041c0c1e21748000000e60001d50301da0f1903410001a82190500c1d081c0810942c1c3c05003a60218010f141036242c40c05203004444c0070029100c1ca00b010b00750b4241c401e40c11540030f0417000c0400c00121040f824020740e1810704640c000c0c1e480c440d071400700c0c4c4c0003c0c600209504955000b0b003090700d80801d15074520091410502c0c201c0e00700110060030701c0061065402c150 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 479489046 1250 479487796 479487817
    0x280f0602030f0f09010b030703110f090c030709090203131112250806091e070315060f05120304060e010912060b031c0e0409140303070f0206070e0f010e0f0402 70
    0x1810304140d20f1032200500040d08007103040e854030040603c2034070041685c078100c1c1c0e00034a980000c948501c01207001d01210101d1130380d000f0010400c020401507483d0141d401120142c2d0360035515038940c03480204034071040e1040080c1a09a1201c800042c02c88242c4601111028090a1809011240380c601d0003ca030049403205607459481c407220601102c1440004140e10b9008100da800e1046005032201260010480b1941e00030103502c00340700003084501c0040d54800c180b15014580161f0400c01441280201000c10b00948000581d6103070008415440004400c041c61616203420310a9881c1d21101840ca4148005501c00150120070b402610040303901400c0c0119001503108105802d151950005e51800001c40050040955001b10207040c520002e5a0004450b2607908203404246400090420703244070020400941941c082010b40d03482c0d80c01c2d000c80c0c4490b01d9908064404000c00300841b0b0300488001e1030b00b941588503014251042c07901030141010090900045405da0b400342c0c4200 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 479490296 1250 479489046 479489071
    0x1409030d150b030708040804051003021308120f03092a0118230a0812040305070f062a06060f050a0506040e0612010e01050406140702280f060203 64
    0x1542108000d026091039605140a07806180707042014a0129010143c480c500308041140040c08000717102c01110b01820004202d2000d45e5003003880100a5400440e90284101e04008005400540040d48002650404a03070b541403003c0301d500150300703810040880c1c2282c4031b0030031030410b5296002e60000d03c9540c1007801c028513120000000d0070241c1c04061207000802c03905000c1001c54011902210041c0000e442d518401002a0000f2640c0c4140d4000175418001e40b100d181242d10b41c100104102c07482482030b03a4000b5550000410540a140318441c0801c00c031111102d200f0850600b00c04c2c80f10b600214085c1c8410107606da500440e07240d500000e1414600f03100c14840c624207260850010401140c1c454505403c061004008000180c001c070b00035185850484805c980a400c05e02c4844820300c0204594a014145100644002c200d0340c080100c01c40d000c100f40c14404610a1090300b10700f00c102c3c41d0310321000c0a101c030000d4202404d842c44054510400c00060b11400114042c07180031013071 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 479491546 1250 479490296 479490307
    0x6050304120206070f050a1e03020c0f01090206030403030b120d02030414040509030a05070507030b040b0a0b06130302010e06090a09060812161205070f060618200d140903 75
    0x511045205522800150341c0710908000e003c5512440082117042207182c00ea850390400c4c4002c1d2100a442040d02c941741844c0c1400681d038692583c0504485949041203a180b0380d50f110710035088841c042c00c00f03900940100000340101c0e000350003114807040d01400c86003515440440c0c40d414080140403110060f00700107020058040142c40d07528a80d03004480410260030840c1c0b41945d40c0c89103a1121060110108003d010721405000d410011038101f1041440342c50710703190910644800301d50215401c0d00c0c241c0c0852040c1000c40540724004410402603400300c1c250f40044d070300111101540caa00160421140016803601d800c00401460b20751030100301107040c841d25a0401c0c840d0701000c4a18041401b000601340301101c48403003071030b800002d100c0c1c2808020307070b04840070700c9211009071242c100205004c0130448940d128008403261282a4401c40401405141c01c0c2c404984c0e0701a00c03100300c41d151115605c03128000342104094004001480642c40140c2543c82e14212884440c1d90408100e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 479492796 1250 479491546 479491553
    0x1409041b0f0f0e0d030e0a0602070303031a2206170a0203010612020907140405121b0910090509010b1f0206011508070c06090206030c0a030e0a020d0b0a0b0a06050304 73
    0x10000c801d5401c900302800280310840004084040b2001030b9449078860860301c006250003080495003680c0c014000007110f54440303001a5030380c003041c0b2088000034030b462401003d01310a4442a1241e690040c110000d4070084151405822985541c42004555801001544421103007054408024003805805031400d240101400c4541c01d6000740b441d103440700311100050303030340a1030300d070b400f1055007841d064800010403040194001d641103070760040071303402602100e4940041c40c008070500f0521245c00030000ca6013409840e181c1600e00003d01040d032013040c808080c079070700542e070701c04003650000450f405202e0004032440c10b920341e025044c600e0441c02440081e0305100d4107025100c215110394140c9034001004012550052400d41002688200c0c032007000b0458010344c801580003440305481c1c0c240a610f440159001d09041e0010920f0700c0b103541c010102c04101c0d24a41c9070010300e400f16010940e00c0d510803800b801001e104181e903903480c4000c165510205070038050b021568400743c80b460140b6 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 479494046 1250 479492796 479492807
    0xf16030c05041406060a0e10030509010b0111030904020f0d02120f15090f04032309010201180b040204150306052502032d2107170103080a1409041b 65
    0x200600d010710300300329a034601c070f02d0f2040c90700d600403009541c125521604040c04598a5001704107042c0d01101a141203100b9a52507009036010382c2100c0b0007042440000001500c2c00030034800d40560380d410911401c000751a080d8083c0000d42c2d4900080c030300c0c004c807120740e550499010450000c0040c502405000c141c0380c0c8002155444041d076103402d500c03030601000041c20080c0c001c2c19000400508c0c8009810507101d030305200880100740303070035003803030a00c110f00c07400e5075040910014010740c60200d0b60300b90038030810024007005030070006140442d101d0360203000181c042c1e00041b070444141d6090000014083c0d11490b44140f01ca41d0600d90380004ca40d556944626001035104d0455001f40041c0d80701b8508203600000c0d1441d607000f440070204a24800905500651118212800c0c0c00c000c941200941170444074480c4603075685c1d00c1c09580200c5500b504040080c000603080d5074042c051401d840d07014060249082122209090500c16000000780075a0703900994285001d084884110301c003030b00035 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 479495296 1250 479494046 479494049
    0xf1e090309210606091e04020103060b0a02060106030507022d0c0607030f080109020f090f0f21060601090602100b0d0f0f0201080a0c0509131808040305070807060804080a020f16030c 80
    0x225a03004142c14940000000300c9082000400446d0035140880c0440e03029902690081c4540781790f154861000381c8020392540300901c544030200381003c0c00900110b2022400318880c00f0200100f4041e103650109100c070b4915a2119209284200300c155045561071602078140c10b442a1395040b820084d02c00300800c041d01c11f0303101090582c01401404031020b652010344040000a42c0da80585903040b41c0080c0c101910300b482c05030044150303d401c600445601102800140803081111241c1d150f9500440706183d81e072103080016000700750450629030707040d002030301e038031070021b1070b10000bd09140c48100b041c0018440440d00301b041c006600e0215604180c5599000180d16004c0046a8120130040e20034420402a00d02c100490185404401110b45c41810008121030503240c3c001c01520302a2025449404240da00707100f040000980408009080010b85245617586032a03911a540c40d900d80c0d4200010306070644c011014880026041000100f602500100955191340d10f103081041030182daa = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 479496402 1106 479495296 479495299
    0x3130305071716140a21020f1005090d03110301180e01020d0903020f0106031101080408070501050a02180a0803030f3304050f1e090309210606 63
    0x103215109001d144120740c2c1c0c13070041c4605440503035100307003c61009003004001c0511142c03441e190f068140d01008140100c0f03005e100d0f54130b1528242500116846800d42e034907c01c004400c0c40820014440400c41e0408010104200c51814082c0c03005004500040403844001c940c10b1280340c0c001000000807400031034072000001d03918400344c10205000e40051061802c03030403103041e061240e081103070752044001441b003002c00019100890000e0013030312644018014040415400c3c05154070800b20403000603030728910400c480d10400c03130b103030030050191310307013040600082000008503a0081e9a01d800940c2c50b581d41e01ca6444081c2c18908040307010780580040f0280604002c07900c0344181030807201030046d0b40d01e608520800100450380d488801c2031244080f100507049908440c0c020302d000301501d15184100001c20001050302c240102e010b8202d0b5400300e40100e041c00b140d50030120 = true := by decide +kernel

theorem cover : BRFrame.Cov 479316546 479496402 := by
  have h0 := BRFrame.cov_init 479316546
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479316546 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 479316546 ≤ n) (h2 : n < 479496402) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
