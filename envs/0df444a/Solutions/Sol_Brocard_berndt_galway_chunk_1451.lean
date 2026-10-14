-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1451
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:03:02.651221+00:00
-- url     : https://prove2.me/submissions/b1ada7a4-188d-4993-8b14-da3bbb5a78d4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 260791366 ≤ n < 260971223 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 260792616 1250 260791366 260791439
    0x10302060403030806030717030c01320709080a0303090510060b0f0a0c020904060905070f06020607080c07120207051507080306090601021203042003010c141b03070606050406 77
    0x1d413008002c41d40602c41c100c80480c1e41940d150406031100509402140d8a10b402c50b2505d081d1f50426104259000206004600f035a11141106114020240302e10302c25070f8401c002140d50180399400885180580b80d81e410a05a140d0814640603008030112440c51407104406812156039100b1a464044240100d11641000f00020a400a040e2604510582c1d6a80001e4519082a40e0031210f01d5506e078600010020705000703880c001c024030b013201400c452070003401944502000b03140c1c60401101c103000880d56200e500559003400c2d04500c0840a4041217000a075807070301103000311840303810040340e840030f004180400c990219500c90f003000d05649820303050203035031200500800d06501072491901a500600c001440c40745005000d04020b0100408400076845075012007980280d040c8a00c5600554122100c5804100b00d016080d645002c0c0300821006c01e118000ca114050000050040521409800580a40e02c040314100300c2d031550382c0c02a0043c1c01c4100d00d0001030304c46841c41038000b0b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 260793866 1250 260792616 260792627
    0x50c060103080904020705160e0610050d09060e0a03180512070302040b04110f0d051303170403050c01020c0114061c060c1202070302011a01050a14031321020f0601030206040303 78
    0x34054050409801d01e01d079962412305151500080d420407004000040005100c9881800c0d00710303500791140048407080940c01013281c4104800c040c20703641c07140d940f00d08004c250361101074452000c030280c414600d5246001800c1598101850041200c102030108003072070701c408102c03001c1803498004d180991840e1b0170301001d010381c0012107a03c01c0d42c44040c1c0d4407011444d401403051100030304001e95100c00360b5069100702c03070000d422129008001d20503d80029001a5142415451242d80b1040e6642e2031034222000c3c410a800750400354004104028010415005001e80107224002c84030030382d035003100340700c4035100024056004080e114a44004100c495000d0100b0210b58036011403000c03144001d540982e07101048c00c4006070f54a06880000e81e200007940c00b025038092821915001e61004014004184004240005900000414500070703019249541055000345100c03c0b03070341110420203242501404610141c052005605c13038091000c1134031416260700a0001e41403e0458800b106e4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 260795116 1250 260793866 260793877
    0x9040c050405040c0602100c080613061a0408010b09070507080a050708190806041a0103020c1006121403070803070309031b08041d090606061317031207050c06010308 73
    0x48010500401180e030352aa4042c09100d10300980003001401d2400c44002d142c018001104491189041c2c021040c81b540305020941041e03003100c090008002940401d8010541e544c0203200120719184c80c10304641310040903000719107008000304407a0188800340301ca406400c4070352800054040084400045004016011102031480c0040c102207860381e0b0100a07901420004500418845c02662501c2d0300800c0183c0c81b0000f0350f001d00c44d440c04240701402000f076055413a0705150300030800d1701c1642401c203c030421041440c281406402d80d80c42c0442500b0b048580281c40680c40400140c0801c44004200c4e0700440d800722119146640b140000c90090007080381c110100100c40c0c80200d54003003000c0e90303c41c2d46030148002964903032800d0821341034a114a0f09117091060510204194031101103031a603405a02911000d648803008004409692072581015070300144c281c0c1c80a420020010142c10307030340c07070150f04003905446505054070795000d4030031140b00d1580050018400145c210b00070300b8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 260796366 1250 260795116 260795123
    0x70e0a1118190f180b030a0210050c0c06130503061806011a0706050a06171506040b040b0303070303020304060c05030103050c210318040c0c0b150a0b0c01090210090b07020904 77
    0x140890f40f030300c80e540c503030705465070001000380103010041c0e140769200e100b040d0111500320700803c6110750590103e01c41242d1000180240403003c5070045c0f2900c0c1c1030104c140920300080c040d81d80d1b10398070b004c5c0d40c035212200e0013000d000e449100c0004940c0314480c4020903ea0b4100303001080141e2030300300e00341c0030902c2401907001010b0042c0410310000344680aa40c0c040c3d1402c0c400410303c85d0070b0101440040c0c014850700c43e01903100e42e01007880444e100c1c100e1a00082c4c2a40c02041060004006c01c02608051ba001c035018440040e510341410b61641c065405588680c00c20f10103002e03800b408588501083c04054900c1d0401d2202c0700561030266441892100e0750740b10850301105107061141107070441080d82c000618000400c146502d1b0601c5010300500c00ca060051761000b17551100c49400d01d00500085416805041841d43c0e43d44060742c48000b44005c2401d15503902c040400203001c0c1c161800c0c00c034068541044410001e50058007041c00f0f0311040000d050170b00049400300041e000f400352056 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 260797616 1250 260796366 260796409
    0xa020c0a061a0411130303080c0405030d210219051c0c090806010e0c0a0f11071805090607020606060702040906090305070b01082107020111070e0a1118 67
    0x14400642a40100c1690801003042c600007004803409010a8032200b400c0030108038000c01c12000f0b00c0390f90032078607000c1c0d940614280d120f030350707845e00e00302c46501c641d401450341031203200300b805886944000c4607070582d18449200085017040c08078400680c0904004070b0300011003c8070b0220424410009407002e140042c664914040d000c034030000880d0034240354070340014003244050280800810080380100ba100c00405220300e0900c02300511809000383c80d4041100000700f00650510610703103102440c220100745e45200303588503445064003e2007014440c0302810140000c2c0f0703410000c540c1d13034800c14030b80c1c024042c1075441e2002c01115034001c3c3e0040b640660b44060600206401c1c0c4510f5400f1407003912038a6403840f0340d05110082000503840b05400723074000f0640c080840090016250f1043e10109038075281e542903c0142c038214032004000b8150b100c1c12130001114030040c22040d00869150344100b00d60305001c2042e00c00c52043d100549460040c64509140e2410724108242c045606e00c10310 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 260798866 1250 260797616 260797633
    0x603120e030c0d060b030111032a04170d11010b090a05070c1b080f0601060e0108181b1002030a0801030816051e010501050406120b040312020a09030b010b030f0a020c 73
    0x125100c030b10b56000d13106242c0d07800c01c241c0741d418244035400c500d9020541d005d0075890400b0749421458001d0701c00032140c0c02d000032004000c00f6a1002d071800b07851000e0b4620f0003d03403500405030703864118103541c50010719800304100340c0100622030706801400280040d040d40c0d880c80091400b51802030314100401100103d00c10101d80e03401d0401254032800c3c8a5503801e5440c0442451a0812410384540d241c2c02c66401041041d0300b003445c18050a4080c240035100da0b6800b00c1a82542c803c54120b1500f030302850150300c071404008a40301c01c50301000c5038649860900305008a0f5240103900c90a004141a10700501c041006400a00311003c0203030340c141d030283c00315034407141490482803408680d0341c07a03a224107041400a000e50344c00346c50f0603038003041a20301c3d00c6e02d21081c4125804c0090402e0a8440100e01410711805007940c444180140640d034448070204004c0080b99103220039203007105c540c800480e01c65440800c9902640300712a040c0c11684900356040002c1d4450043d62000e841a07048 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 260800116 1250 260798866 260798869
    0x90105070f0308090c2d1f0806030d11030403170d0606030c120623030a0c06050301030b0c1207081008060c090102240412230405041503080d020901090b0c030406120603120e030c 78
    0x40031104180700d623440710b0303042c00d010062614003105d200201c018482e1640c0340501030000081601c1c00c407908819405a02075114147c42c2041c4140b41c0b0751074500d810305001045480e0160042178030540c0c0b80d603135201d01d415144200011076101340203400c0b55040301248100c603107020220031511010000c09a9025140700e5580000100c501e60190021420110040040c09590414958800d00110b80c903894000400344e5030701d885200410480c244600d441c042000920700740080c81c081d04506003141ca640c01e01c04804030198000b00340340383c014441c3e1880d40c0c2c0001c21380340081420b141d124048050703548841d51100c3d50088204070b08410060380da041010b81209016000c514010902c24050740c035403d007000d00c4292011150018a00040b100f81080011500001c5420701c43c941d800c01a1144410070048440560640c0004910301303002c101441300c103801000410841c1c0207600c80034107030f50405010b8004e4032564803000d00048903041c01c082109004240f41708405400400355070004503241c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 260801366 1250 260800116 260800159
    0x7031e090c050a060e0a030b04030c0b090309120f0712020102150a0606090503010c09030201030b04020f040306020c19030905010507060f09050703030e0303180402090105070f0308090c2d 82
    0x10340956601040180070803090070807202c5000a4400743c03a221440396084804152090101c0c40004c0840880c400020305052080c101c0301e840c0b03a4010747c034114034103000c0204ea030303250485001a4030442a00100701e100d407074009994001400040054640c1034501901008a20500e400aa040d0b00405010010300c4a03a401d82500c603560410700003130800e0030008001c0640c0b0a40c2c01460081c1c1c54140c51690094001c00c0c00e01c1141d0782480c010900c4110040428042d00600c615a440204041000300401000c0d070041c04002e0f00c4101194101e030a14100c112041c0d034802e80c0600803c54810f01400742c3d5103e03500500d0403034021800800c1056007427100740202c3c0c141410543c1c1c2d54110300014130806600405800c05901c0c1100203609141c2034075a884064202210a00d10031a4001029034050b4003520a803440c076900014540303041c2c025800e01426080c2c0403515a030241c02104800700309031800304008002c40c2c0c4054141e010a0141d1301260301c02120300c42110f948000312040c06c2040b0315884 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 260802616 1250 260801366 260801381
    0x302030c21060108061909200109080304032609011b1a07050706060b0c030f0c0123010f06080103080702061605031303061104080307080d0902040f1b02060403020607031e 75
    0x3003001740720602c0d1001004185404c0c0250042c05582003070201800b09104644008507052200e8014004000c1040141c070f910344250b1000805001c042800814440351820322000455007100d08040001c2c0d030030b020355240c07040701616030106070614a8200c17050390f1003103049042407107080308503c419003001c40c01d080d840040b00e01d440003800018441c4108842400788400802031091120700300307111030f0b039020b84034003414517285032514010501003041242500b1040d4008000e10302c05449181c14105950510401d00902212900542e0001010751085d11482d040308d800044540c2031040c40d9081026662000e510607810a000c0c004810110368240000e06908000b009105c0440d0700d540342150030395000e03255104000c04180401c1103020000300445505942c0101e200342d40b0241d10021000600407080003940007481d00b030340e41101d0704455003e038aa84001c0d052050b6501d032012070481e0745041c102c8008005070841c0c00455002800390300300c1410080b4280d00c4184084070080350b40100d60b0003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 260803866 1250 260802616 260802629
    0xc060c0c010b040504240f0e1c081005090c090a0603020307110106050f04020c030d06090204030c14010e060f040b070b0708010e0108060106210c0e13060302030c210601 74
    0x25000d080000074461440c0c2842c2c155800c0c002490661900300e09420311181000203c030804148405041c00d940c0544900d100e040070820444802c4855180d41d101390000c9c2614010803458521821805a01c8162042c04c0050b45455884d081c0360030700030421030240c925604001c040c03042e080c0940c2c50300d121601820b080d5400580380c1c5094040100b12181481040c81c850749000818481515451a00555484142d401590391070040e07048038598802e00400c030410030314040000c264541250000c000f100c0c021170402c1c5405803030340101035201d101011158040b03511060407030944e09100303029200070080700344080d0a00380d072141c072002140d0110008461000d880350810800c1a08607030418050009003d4006440d070501d03101d10780c1ca44040c06000c0922610100c9283c003e40d040041784028501e0400601032856400006458012140010780c4250821900c0c10340c41800e900c0f5040c122a0002c0041c01e03010300316400e102c484411400007d07504030b01140c2c1140010810000705008001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 260805116 1250 260803866 260803891
    0x303030f04030306050f06031501200c03070b190e010315090914030c030a03020c010921030507030e0d030e01153c0302120709060b040503070b070b07050304080c06 72
    0x4192030b0080c201c3d20743e0f804c841d00c15142400c00d000325440b0f00d002c3d2a0b0010081c103441503662050001031300c503000300500900201c100f105000c3c0c035101010420842c2200250304480320030f500e40180c0c0c0142d004240d01120b104d4034020701100b400b4072840014040b210107040c00604100396100d908a01c02d05a0005840300e070b1190f40d10010031100d04656031121514001941c03d0402146e80d440d140c1c400e10052104040e000b10310358010000a51064803000c0d40040c800c442d280700300201c4002d1000f20407200c004245080001441c0a0007070044410364812103001d0031807410f1001c01a0010119442c85840310f40d6034000e246260741003481408080c0c881c0320005010340c00c07541c02c070406a03102040080312030b16a248904c4141030109005d0403c0d6039044030b504103202c8130498180d06c6e01c61039500c40304115082100001e915150705c0700070025a1401c3d03081d1900a61100d5180190b48200a0000c00300c64008001900e050300c558069a00981b10340d201c0c900c3d111181d60707024600300301034a80002000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 260806366 1250 260805116 260805121
    0x3060e01021e03070c0206030c0903010501150f0905030304060f14160c0902070209010306022d0c240a1d071e0e09060411040f060f050a050a0e01060f09050303030f 72
    0x20070441c1403070001107402d9416071562419400007800006801002405502c0110214035422407a03800d803004444040c008016a6a40300318402c5960180152600400c6079642801d9125200f04005c005035030b0003a00962400e0b00c0c0180403039400409804003010802441c0804950040716030090009000d0440d49061000d02c5060036400c4d04059032140c1400762040000400580f1200d410504403a040703007005848270841011101c1c0d41d14a589000c04040f054081060480705443c00f43c00c00c85400d90468007085d03581d40ca602081003544070f41000e080b12046c009140340303102e500030200d50b00017160b1114040c2600020380b0700d084441d070000046012184140820000300b1107040c0014401c000054000f4203280c20038a817240306c043d10242c2140420380c03045a142c0c9564100c13085140b0001c10070404aa41c1755410707403021038540582c0703110307401780f2200264901d00a88110141ea5040c000e11311903920340740042c1e4000e00f00c0c0740510180700f02c000002405c0c7e81c003070010b1071003110b50140c010b6051 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 260807616 1250 260806366 260806387
    0x40b1c03140414130e030d060e0603030f0d0b03070807090507032d0c180314010507111b030a02060d0509060912040306020d18050a052803051303060e0102 68
    0x59150400d05a0801c05100420148040311a0403403108429a01d1400d140d02d80701e180300140c04800c2003180503100000d111081d90781280d02c00412629000c1841085440d9001010340f28465043c0d40c0c2d40c50b0030701b4488503a8800c4103900c03030600b00800a0858005c142d5901c40c031420070302e50782e1220b03020759641c5041040480c0c060007480c04070850001c41540e82c2d01070a90788407001c5607407501c03144110b50310040030650502800f0000741c459000b0420b41c900d165a4a4005010403000340928215420003003c02d403d40e0040345900019208a0007404020b95101d1603145544115040140c0c5480340c03013032400c0981ca494008000e40007900038049250300d44000c6491800703102501d00e400c5503016201c1c078030240713100400761402c0d070b030740130300003503513030102c02840c04040c0c020451681c01000b5110701c01010040001070155502d440f4000751600802c41c084000b010403102100c1e11194403c401500c0c000a00c00c01c01041c00c410590343c954281503d9031940d41c116200d8524984080c2c1d030000b40100003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 260808866 1250 260807616 260807627
    0x503060415060618091a040f0915020a050405120703060f050a0b01020a12030b06090a1d0f060a03120516030207081e10021308030d06090501081b0f040b1c03 69
    0x900f460b4103100b5004044000d001e40c5480b054441e8850880d40c03407207030209248584480c4c1c0f42106000700144007201310407241400404603114115611841c102c05070104014a009441c21080030741c0340c0e07a0401c0d241005206090528000310306940c0201c210202c001203072440760100d60101000c00048174a0b00700b01e910201d176180c00d1030070f040d03501c11428100080e610300701c1c40383d0041c62841e02080c000701c2d903808100c0e00e000312070b425980913405210200d466520f860503569510a20030383d060554659000f1001610342c140e9205030083c880d90400d10206180350310b420040301c880d203045032500301c603524a9007240303401d50000c500581159404000d4000c08109503201d40c0340d0300c240d500c04c043c030b070401b00c9950b003c50000300f01401d41c02060b0980b80c00c481064200c004d007020000d999407110301c01e11040040440d070003020b620170729000021401a200040b21401400380b010491004492035007007040d05640c00200d04d0380580c5890703240c4460b0712845100300800070b10030380b034401c1071407545805844c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 260810116 1250 260808866 260808869
    0x10308160609061d060906040212190803091504030c02040908071a0105130b06090f0a03020d121805011b020604050402040b03040203190534060c0317010501020307110307050306041506 81
    0x40e171344a00306004200c18041441504103034101c0d180040340000c10740c00d84c2021842c06450b1b203040c2040e0254814486100c00a44c410000002506c0c601c0345100c0548401910960300a000a0000c40300c0f0001410142d1084412031701a440315402c01c13042d2754414404103002031100c4124400d00004201c5801c2107481301e400e1120042d41404841c0300140800d0b072034081c90b1072552007580c0c0302d0a21413043e1200c01ca1180a5a0090314544040c0c0b0307282403e07040c3d48002020400041d952101c0c50807001c41e014068000d070303401651220400502c2200020881140301c04c140c1c1d021900300000a482d03555072000700b000344203007945c185d00c80c42c150040505012420004421004400d2500e90008901090300c4010b100814000220900c954183c003000400c03a070717100349400c50a000d02041540d00803041310101840383e540e01141c140c01440710f0040080a00c81e15025900611039030000800c000f9102001002c09411203007901d03540c10000f441d10100383c4054502d000c0c0403021035112600c80c0500b80 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 260811366 1250 260810116 260810171
    0x3120c1e03011a1305120a05150412120b1905090a02040b03010605250b090c0d050309011b0506070305010302190b0403110f040903050c0d1701030816060906 69
    0x50079507140100d260100401d102d1242c80c0c910000518490101d0403040c0c0101a00e80a00f2207500500c06801c601d540d584e68a00a850a100e44409010440310007007542e44182d41c88080c41440d0080740d141a102c0480d2040030b1240d654070b0341d0810b00342d9250342e84144100080800b04e810003e2030f140a219503841c01410410b11640100b10a0080c030b0591400c41e41194451f181a9235507070b0042099112000b840800001507000d98a1103000384088528040d006452000643d003070790003490100194180192b100030400d40050120407483d41c06125401ca01d01d20251440c443c1d48195a2800d080410850341d141c0444e540308018030960800e64440c890269007030540e01841400c1c0003030740303010f401a440010040000484101d00c44d8503040c02c043e01b4694068018002c042c082c0c90060003940213490760005034810003010854040c03003034180142a5554540c100007590039a1608181d95109101c0ca008884611b45d21100180382482520750540c01000b00080400b865886252800300c01113215 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 260812616 1250 260811366 260811427
    0xe010302060a050a0212040801090213090b070f020304050306011806150c02040507110109060e16120206030a1e020403020307051f0c110a03051608011407030e03120c 73
    0x1440181c989504590240c0760301e0410380e480c0c1148481c200d15100810701c40b204a10000300c1c0c00a00402d05400481440e4400c890b5030044500206032070040300c2583c0009412003e80f4400300714114043c4131301250740f134520710580b46016142d102085c50640c0a034422200000c4a103d149421486403240038003038400d9203040010304e40100801001d807061200040d100c0c0366202d011420850081a692181c0101600284501211424a84020400c4035000210b60091004c202e8215018409200c181e0740f0300901c80d642c1a506809121464200030480300c0100e0342c410b031000400040c03040c0701e0114149903002603621030541c810300d03050010a80c4854054480030881103051074645440d43d00384111403038048003c0d103642c00e003e4620126450344980103d4241008801d0000c04916000d49205500c030503030b500c560b40c0d200c00303089800d441a4102200c504201045500d4480c0e0043c03111855140126420b08102ca11805d5007108191501c1c901c410001a0050144000d10000c070351011100009 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 260813866 1250 260812616 260812619
    0xb040e0a0b070c0201020a0b0a0609060b03060102060708061e03010b0303130f05091e04020d2108090f031204050f0607051c0501051e060408070909020a14060f0a1707180e01 76
    0x80d47d504e00365180101901c52250010b001a0720a50041c4020001200c05020850f9110214481a40b040e5142401402264002100c4501810b1403600600001d0003c0384005144a95450038685200d4025455501e400000110ba0307070410142c10003600c00000c09006603e0040d0725003015249a02680c015007000e0108100c0c00040d814010300c00c8481c1d0b000c280291f58620002e0703850f103c5e8190090100e078025076480c0e82d401690714076880c2448e490b201d4410a844201a03203a4914280c1080305040d481008680280401ca01c03159070030910890480d401343c00070890b001e040400441b42c000c0000e50205114040b009905084106181c5941d070070809035041101250001000702c81064142e480340e042d601c07050703c500c01220024100d400903134500907111190381010300701c20741e4143c0c0b04050400707010071801c0b4151803e10307121400a0059250031390440000009800442e1001d09000f0408080002200e518100c14481c8400345d48106078051080a50140da9541d138220283c8202c50f80300 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 260815116 1250 260813866 260813869
    0x1903170901150608061c1b0905060111010204030503090f010504090905010b1503040c05010e01120e0f010b10081b0904091401061211212a0603190f0b040e0a0b070c02 73
    0x4401d424800342e003118000c141c416003441f00d819401e4911a48501ea8203000020303d09400e1307880760740204001d076540481e80c3c14200c580b038240c2c0030b00c5c040584590410001d80e82c05240c81d29054480200605040d0706003030b9108114000c80ea600303d401e88a030303510b610202e101417400d10440d20180c0d010310b19040c11030405844051507030685004d114144841c0360803009403030b8060104080c207511f603403000780325400319018482d481c4c01242074071004035802c2082e41940341c079000d1030922001465640d45850f81c1c2d614889007240c040320382d0b0307805644142008121560746070b602940b4142405010001000e4580490150841c2c000740c3c040c00030805c200e002040095000341201c1a141e004803590305103501d4044c84800b4820752030001c251607100c1c1da20400d5106c8451000e980b00c0d000035085099030000070600b40711380d0340b10883d5a0103001c601341e4001d1010410660000102da180c00d24000740849466012400b1510038010a00e0a1340c02454074104100300b001269074000f5440ca008480c0d0341c0e0703550 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 260816366 1250 260815116 260815129
    0x1b01020712150905011506021e01090317040c0506040e150301022a010204171e0c060714010b04051504050901020f090909010e0601030309030b090f190317090115060806 74
    0x484084240d207500403c02070082c2500501c1c403850480041011031540c0e004060f5035030030950400441c40d182640340320384540c0c041c0f14070480141c05480c0d48040703e044101c100130180000b4800c41c0d480b40c01c480701241b0707911790038041d001034042c0810107511030030201e1300038800c04000c80c0641d04c02d80c010814105a10844004a4031000600b4904840310300a00400ca001e400f6a40120f192403e007200300e004807250010710b2111000510025041101000100948a50513031402940098040000c880002c04100715003526002031000060b0000900c1e0024068410646004218030303102c0041803030918161080070380201c40784000310728010724804003803114014a56540c0c45452000001004c0c01829000000d0f1300260405440c1c0c00d40e168540946002d210b40010341d40d2a000000240c252031380080d007a0341d1450300350010508803520a8070312041000c3e003481101040400c00b0400c920000c140076060140c43e581001040310500b548041070341c0e0030658003002c10084e8a5042c40515254071 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 260817616 1250 260816366 260816393
    0x11073203070b1303080d050f0a0b18070201020d050f010602070602010e07060318080c062706160302090603270a080f0703031407200d020601091505031b01020712 71
    0x8a60107521201c00070f60800034201d4941c0041c10072000004c80ca030306c003100d982c0a144100070300329900d00c850700c40f02d2000d0202e500389440c1c01c1e0001c0c20046e0002d184c2400f8004142c1c84441c910002d403620035401c0c0864195401910010030b039039100c4005021840e01400381c40302400c0e407440200084000311690341d580742c40720300c5424107041d59028002c0b44644542407803580b864000c09101d0707030784103141d000316074509040300d01000940d88496100c1151900962000e03100031440000c001c2e50712030f061501400c4000460364400c5c90b60070406843c4030f0700c601c00994890b83c05a400d0f500701c40c0529241d00c01ca010b079010107070015000400a50009465902a65001800358200c16141c1050b49004c2d0300034003030340082d0030603404010100031005610603010112001c00074600401c2c81c2c1e041595554480500801c0409a00420018003000f421944070b90b0303d290380621003003116682c2d000171074202032040740c00b601c648008142000c00395804100c0a0003e201450303a9006800003030303c600709002481d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 260818866 1250 260817616 260817629
    0x7031101050a091707030c08060105040b09070e010f030b03011503050d090b0a03020a0512180c010207050114090301180309030c0e010f0303050702010e12010e100203100509071107320307 82
    0x50142c4c8800441c4104040d20103184d01c40c240c01e0100752200344030f507a00c0030244503242c86a820260386100a04001007050302a5071161180d160502c1114019140d07491190b015a00b0107544050300c80445d6400d006a618040316864a88051421400d20768100000c410040040c0001c0c0041040701c5c1e2058000c0b5501450380307280050b100c81d46030000312054415040302c07a1003a8070210904c080070442601c080c0840417400111105080d00d10016070b168211032181c0317404903c0101c44981e20241200c0184480b55008000003100341030102c00c81130040b42840146c00180e1142024810800c90003400b0300a0710000300d8450140d807609003100500000c9001c014100b000115884046900400403117181a0004001da0070200b41c1890003802000803040c5518148540d8000074282922407080301d02030380e0040e180410050a102c140400e01c9000741052040021000320300040c00010700801c00a400803402c6110300d07000da03204d0211401016144058034a0711442c1010899400007800c0301151003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 260820116 1250 260818866 260818889
    0x30a02091f08100204150305040203060c0705070803030c19080103020f010c03021908190512041407031509031d0d12020102041703030703060611030a050915070507031101050a09 78
    0x844070301422a11007a60100849209a01008246080580140066418000c0004c0001451050450a86034156400b942507001b81d008240d02804440062001c0d501070002c807180b050b43c48040c185107500844445854850216100601500c09041c3c3d00034007900d803810090b030394150b400040c40041d0a182150500488805980425000740031452404542064414020f101420503a009a0040ca0110310b100c01c8a0b04548400d800362054039820000308101c82e25070380e03e0b0b41d5902c1d000c1096141c10321041c80b0f1420000005040c0c4444440342c41d0f0305802c0801c1400141c0f0380602448003901e040e007a52041d80032070f0b04030303903c0b500960042107401000c40a5020f1050364141d0082c481d82c0c1001503400008011120600c60000c02035010740e00d203a030104031055070f400d4211546884680e80c1c032200e81040041400c01441003000d00203039503005154104004113280512255407015004a0302c0b50000c0d00c04205100900001011802c000e08040340780038842e0000030070204650080d840c50301c4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 260821366 1250 260820116 260820151
    0x191503090f0210081605040609031704030b07030f0510030b0a0c11190b01090c02031c02121305070e09101d160e010605040f26060106030903020c030a0209 68
    0x15000c81825040c0d50050f02d205510450103400801c080c208541000d207800002c1c082c0c5501c41e10404c12141107407132540d14115808e0450b51083c0541001450f14525454180b0010010030001e40718a8054034a640300081c624054010f15829034000802d0110041301005080001c06d41c02892985e200c40108800141c2000c82c00d410744126500805400c058458024121b83e00c202080c002080f1901601065130310346e0341d80010304151040d200c94500103820a00407441407a000b81200c1082c42c80e488409410a441c002050112000c102c440d500781208400e140800e1241c18400140038000440c0d885d480391815220403955000313000c81010007a50350b100491000180c004002051a5404042c2c1b09102c1c032200030341c46018070502405605080c0c4900006038a4080c1c4d0460b000ca561040c80d03030101030b10348684410003800301210707001400844003020100310810b00245010f0406d5450000725505c450030024034003600b00f0f0a40c0d01a601c0685100c2c0503940303481110350700000241404c00005d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 260822616 1250 260821366 260821373
    0x3040806192906130906120320190302030f0d091412040b0a11030a0c050f06071d01021e030a020d1805060c100e1e0a030905040506060f0705060619150309 68
    0x41c81c680c0c401d45171940740c84004100b1142d0040103021044c060355420070f15042e00380e40303005081c4881c010041ca541c494a1962454500b14007150a201e02900540b8240060b8152400d01c0341d104508030003126aa5490000400011450036403810104000030103c98501000b0101640700e1806080b903121004101080628850003003010100d106109880c1c403800001c1c0050b041402c0740c04103c40c82c1c0184602440d14800005020744102802e43e50407002e680001e408407070054500f0852070450180c280442c003209100c051082136190007100540c1d99881e0010020700b407425081c404002c01c0440d07110018000000400001511401c036002556281d51701d04052414403e40081c000d154104258900e00c1080400c2c1d01c000f000a0400c00140c001408031000e48554100c840100450b034155810f10050601d603200c294008805000d1600e80003044c502d0038000e03045a20304a88641c02502000214200703814a01116041800075550b22030500000b00340f261081200710081541d29201001032 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 260823866 1250 260822616 260822647
    0x3080d0b0d0f060605060703021005151f09050409030e060a03060e040b070f1b1b09020d1a0f1c08090a0b030403030c09151103040806192906 62
    0x40340c001072052407214240d1800490038002d80509407880c924201c400149400c2c250111000d036a030550280009080070180300380106009400102204846400c281c202c0e22168841c0032840000d03241d104840405410003840e82c19507412550149007011001000260030003002001072404a4040b922155800011802002c00d80e01c41840e44a2800c1804180542c0303280d0140100e042d5504d002030320f1400c010580b41d1128800d03142410b0b02c06420f950011070440510b40c0303c60120200c1040c2d502d07a640b00154166041070306c4210f8500e540382c0c034000d001502061f80b85070020098034220440e41039140094041c80100c0f000364126030300320400004202c0018112480c0010061141e02102d85070100300e401d6030412901100841d00d0070b9034217090719004030595812100c0c80c0e02045140445580100c40c0e080c400c8440010b90311040c0808a841c03001071107447d01c44d4031314010a08005004441420549490380d001c45600c0c1904850248401c12903d50200c1140060354081d5990302c840032160003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 260825116 1250 260823866 260823881
    0x8071416080705030a030507080a210605030105090c01021f0b06070f060534020115171905030f0703020f010e0c0a051804020111071205060708070f0903080d 69
    0x1418014034180280344081400d0880070303102040100c951035610354040c140d40c1e500000d00600031680034809000040c0754640200010301151500103c4140f0444020f400300a0301032030f608000351078020500c82810241b00d420390000a030b500400c0b41d0445400041d440e105018040c0e039042c1c5904800b02203000064100303229000c0c014212640c0c07030358036042c07480601d420709008681c007604003008500b500005000700e208440300f40e40900500001c600c101036030382c12001008000d41d501d0b0011440131559501d00d00700280b48910709000031b0707a964030203241862400a6480020301100b00c1c1c50020a2001081d99070f48091428120f544004904041e03241800e64170031103a1640c24180128203090011030384401e60b88064403035020554541003040300f0b003a038000c10300d500700d205607002a015611071041d80c6a942c07031107015200d503030b5181c1d0803401c0124141082920303240d00a1040c0f10610358002d10443e400101032420348941c640a050040c00c245d81484090461080861f101c62984216880000e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 260826366 1250 260825116 260825153
    0xd12020a05150403030b0105090f0f0f09010b04080f0d0503040b04021503070e040507050a12051e01150f030605010c14070b0c0c0a0e070903290103080c07050f0604030807 75
    0x19008955032600001c0b000c001c03102200082e0429800107102e50055080ea0311036080289072011402090040c89005604400181d0b800780355480289034a0f1150f18800307010300340719080c09036598105640d1a01d445040e42c9007035490380c0180140b014180c2d02c8800d07a6040b980c4132010920540300e90001410343c8078580d400c840d00c00000020b2001c580d0b08070103042120703d421346060105a503074cd401543d060180010781c1c40800d06202011402c481c1c0d5910050780708a49403824016074040d6100c11000b0074098000c41c2045e080c08255008142e0080b641c00042c0b200d03450148809400c20b000241000c0c40c0c00d60042c9100300d00402e002406000740070100141c43c070890126112034030907400340da854420100311401642d24010200300c4078100400301d8441c1d807035a15071107072682c40c5a40301c04001d45569603003040020034070440c407500194510000d00a60142004945400104d00d046040c16500d41c88a8410f400415200d0800d441c0c01c0701b036408998100050649401003805e011440c801d8464646 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 260827616 1250 260826366 260826373
    0xd140c060d05061206060d1523070806060f040504091a07021e071406070303020403020402040e25140a020307020405040b0118021314010c020405101508060d12020a05 73
    0x5071070304641c1c0030600c036001c200c4150510200b407014a640380d103002e660041e004071038502d0002c081110290003007403000c0d90610009a50600d400d0004c28200403030280b4400001c44401d2002c0c0301d0340440d4407034010404135040b92401c080714581c41104e20417881803030701aa85540f100e6051100c4002018004129000384020900d84402d0083d1540e00c02140101040c000b40300a504500e000540b44059400101911610031440000c00c60301d904010b400b02c04241e000c01020005031600d0005c0c10040c148000341d00c0c0359090082c0d22016516081081d80c0c5803801349400d8121150f0700c10104619401a190302c0365a508001704100d05500c0b070300303502a4205040c00c09002c10440342c4100103041b1050480c9030f1400100c0d41d0300c030000340e06c240312600d0a41440701e502404a990601c4442c6044003050410103034540306035002c142a00c1c41190f1142800440210421001e144080040d01590041c41e11102609d00000012480c19440002510000400c1d1950260700d0007003100040403034000046 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 260828866 1250 260827616 260827627
    0xa021e040f0e010609050c04030209060d17090a12030207270501030b0f0c0c1506060d053405040306020f070c0e04050c0901080a0b1f08010b030d080103020d140c06 72
    0x110301910341c81081d100190301e4800d000405d0354051051500840500800c00d241c0f524640030040506806015039a1000056035568009042019240050710401f0000d540b10031002080040071940c582c00714684615654000380003a42c04140072040e90619038488622045100d11030a8115945560060742e500c4d2000100c180203080e070b0346922800d2400081c400a90303a220940d2941e0141844113902c0341c1c804100b00030040c1100000c560711000140c055030608003c00c01c50416a0b506403640005d85610800032000c0d41819104080c211342c5207480d0204004481c0e02c01400d600c9148005003d03e42e0102d840c144035070400d01110380c4142c200314201c00d400d4884110210001c000c1e40c04880604c5030402c100b95034240741c8440c904a403203510240000c243c1d40e8a600c0c21101000345121640fa046101503a2500c03040109000500008800080e05154050a00d0314004545162800b4000a00010401070340c2c3c0c0281c0c0305400b80d01010300c45440c0240c1003004d103003a6203140d9a56011601160 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 260830116 1250 260828866 260828891
    0xf0b0307061806030e070e130f03030905060609101403030c0109030f11120d0b0d050f0d090902032205070e1518010602030f09010e0901030b041a01080a021e04 70
    0xa10003210b10b8800403034035085666003026012070f00c500c0311200d429004040d0800840000c4299a540114156000038007a241c5da07071000d8208091040c100e000c01e03070350400c0c641400400c0000307543c840f00030343d2815028200603910b02e095800310f1207a01d81a07501c400540c0c0c0161805c0c401c1c0c0d1230007441c020091181000618010341744038182100500051000d1089040380301d00010007030320340c2039066841450211107100d082c0190441d40300694111154420850004034104140340802c040c040240104400c2030307200418100c4542e01400d24580180705001021344070a110196400f18500080380070b46403407912600308244ca602480000301c5000030441011841903244040c600101c1d090301c88201034480c04040c9200078091000168428071028800d20340a00080501c00c1050602e610705040910008160380001d8008440300c40c40c0206000802c0502e942c1080f03543c0303088a40c40241d41c1010300381ca94604003c4c0b0040e21030b8508000c020280318511480c90750480010b00f09000c40b108200 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 260831366 1250 260830116 260830127
    0x504080a05070503161202060906070c0f06121b0503040201020a080f091807020c090a180501020d06060c080a050a0e060a0c02010f020307150906320f010b0d0f0b030706 74
    0x42002e009001d40c8900c44c3d0310845822010f030641b40751905240e8807204603003d00829800c0f2041058100c0c0080100710003042284207203178002c1400540301080c8030304000d40142a103002c0e00364030b5102030424001c140c626080250900c0c071100140742c902d4803070340e6900040b0b192650ba444041c2901000042c003485190a450050051a0701600d5218002c18002946800110202c0e15000140c0011280c101207241554586130880300c4054080340e0100f500c3c149101074240d04a00b2200c0369400034007148035961902607040244180e083c81c240450541e1140921442030090040411400190242c026406180b1120f080240584800d07103810b410341007e001c6880e03001041e07000c21008940b80d50780c0c40c400011030722811f9000c0d80d491035800f00e002d204d902820b0044400c030740c581c2d15040704103060080c0f401044c030018050304111b005803030000340122006001900c034074000c401c04001440124080c01c112211f950840d100050082200c0380b0789001071a17010a034940c10702540900088595012 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 260832616 1250 260831366 260831369
    0xd0602090d1b060809150703151d09010c050307030c120e030903060906190b030309030d081501020105010506070b0603070b0c0307050c0d022b0c26010506130c0504080a0507 76
    0x2003030300150b0b0948569058590002c02c494000c0146d124028100345003217605000354002e50b03907040115103004003500d050380f10281030304003080c01c1344ca0b80d41410001c0741e20940e141d0040c03039640007040504035200d801003480c4402481c8005254440002800ca02d2040f1741070b86041240030170400c040800c0c143d01c10303120707800003c843d4843c0c89400f01098100300041200340c0240103e00c0c100c0c212241540d01300001c1c2004064103030b85800241300d40002920280302030094602240d40c1c0741541d141020701074600340080c0c08a10704680c5000d006018588401e411031311903903080044580c090303488100003440c00c50b0503000701070040c4010441d410110000009000054810000e0b03030a030b40070710014000304d900040c0000e075103d04828802040e04861144100f9058003002062144954507112900400e15aa0103e48005509000c04804d00c00512905443c010120b000740070a041c00f41c00210b0114485d07140034185a07440d42e901d042140110211401800c131002640d10940303680c01c009441c1c9415 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 260833866 1250 260832616 260832653
    0x1050a14070e0109050d050a080a0206090706020f060f0901021b03030a0f180206030405030c0304150f0807080c0903030405030a1203180f060c050d020d0606031116020d0602090d 78
    0xa0100d0100790240980544080703060351540d5400c2e2810b0100f0442c10b10503a4141c91500800086c07102141080006281c0001c05400828060a080c041b0514014003580302100319002000d400e1440e03100032a065030441e00606a04619844480c0024020b114070742140004550818454080c003401101540c412701314000204110a4001611000c5d00c4d00351601455010301c21111000518203003002d16000780c0250b08503420b020034901045d2031039220703800101841e4034a81c26203d40380c0c1e0054034050b05400f940b0300b1110034104031201030a009006009014880404111020541c80c20000e40300100360040448800d0785841c01c01840c003441840b03103840060f080c8004035a040003548454851950300c001c68070081d0841e5202c0c42c0041c02034005110820008210304009002c02d0300103840c56502c2c1080014285280203c06000ca60612800e440ba580081c06048844420441c008281c507405072110303070300c600541c50100c0092003400d1000c1d611035480c4d0a80010b100c100310710501c40f1103c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 260835116 1250 260833866 260833901
    0x60d0804060e130c0c03110a1119030b011806061403130201120c030213060f020307030e030c0a03050d021c091a071703070e03122209020a020c03011104050303030f130501050a 77
    0xd00321009440b0b0812002c0527024480f010b100110f40c2c184a20400914004140105c402c1078580e503030081000030a9010000545014500d103018425500c41c139401420941002503d0380d69003201c0c0c00044c000203040e41c1d040380d50441c002080d0390042c0c1c182e4054150f414000c01c4094a0b4440181c000d403c40014000481608100450950b0207540c504000b600e581e0021410003c095034110b0310703488240b42081e0180210030a80a141e1030344980078002d107100d007000d000002d011180080c45c2914095091013030591211640c840290041d0000041d5200d03d510010181482d031380d42100f900c03c1840080c02d0415080000860520400c01b950240d0b400c0c0d070380d15100c0a8400f0426540b62400e42080d010880304005000c245100e07006021000c200100804001941d2015000102e8024440310b50140c0c015511410182c5828031458002c224500c00d568281410000481c0d0b0364040100318600e0502030101041004079404100700324990b210000380060f1410300300e68809040405030201c041310 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 260836366 1250 260835116 260835137
    0x1b011e0b0f030c060318010c171e0a020f0c03030405010204030b0901050403141b011a03012a032a260402030a031409060c060f060d0804060e130c0c03 66
    0x1401500041901c00c0050041940c0462103040040541c405801150182000b09004006202c2030056812a000a8481d42054503854801c1c5c2402c2c1001010b1003184103059404030404041542502e8000d201504016203c80002800292038410603040811070300c4084100010490150002c4c030130381c0d200e5012403072103445840c00d15090315010358004012801650761403524403400005007420000c0d280c48020a40d001c49001403c66412580c0070200c850300b800e10501c0c41c2024000c0c0b008004d020185160000340c1d200b6504c032a184250075003420180c580050703488032400c911700d00c52561f46014010f104e10a8081001e820201100c20300092801048030460141c903243e0403841c44cd80d0041c0251185200694080347c0c032880c00070900032081014000d55446403168070241c000320801c18010100d90800700916200080014000c51141100340c00d80310020310a602510102c480d18201070411081c4140041c400c008003000c1d1042d0f45242401084140743d0059a658a59029484101d2880b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 260837616 1250 260836366 260836369
    0x908030711030a02030316090914150109030314070212070905090d0302160615090906050405010b06090a03060902060d051509070f0c03260711010c030216081b011e0b 73
    0x380519440350f800742e00103000040401d40c82e102940c9040e041231400d070b9042c980700c020840c111050000c400320b0f900000004c002e61851010100c2400100908000041919651b8010300b607800c0884440c205500c007046030f00842d103440110032203484141003510740142e29030003ca00100000c490f05c2c1c0640c4034020103540c0250091080307070520710032314810005113050360b04c4403c0500541541c0c01c0c0440b60072940083d918001c2c0c0710310300c9481d01c501310119140c00c0c0743c1000c90030740342107014041c401c030300800c02d24416a40700345188003104d40c8000c011a00340b48600000700d890003120403240c0507034105802c0040b510807084e982000e00d40203c80c240b03929100c0c04422509100000d1900011414860003d00400d01030384806090420b11000030036000341d6040c3e200386d060300950704800840c03c80016500d582c5003c0c010f401000c640d5280450400c11100c1c04003000c80c000070b030080c01c03004000a40e02c2d07007000c100c00c1d503461000c3c802000303024998000321600c5240918403e03c002181c41c10703200d814039 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 260838866 1250 260837616 260837623
    0x1060501090e0718080303010b040f0906050a1715040605010e070c02060d150305010c03230603062202030a030806150301231804030507020f041515020307060908030711 74
    0x940c2c810705103450090390740f9041aa80294143e140000106880e100003d000404100a60103854144030940c5c4580c50520005010741540e088000c05c0d50a00c80240000c1c0c68062004044030481d1005000c1d1480c440b10050600d66040c0c00d2210118040c01000113000740741d080641204c54500790140140d1701e5a5046500714a107800c001d600010030400e8405043d0725411048503107009540300c00881e03599907110b41c00c540343c41c00702d030010a848840610340d0500c1003144946200a401052000345070000c006516410006d00703c1090002040350400d030880d4004854000c82d90241c2101c404900d20b08015148030011503900b40b090310480c2a00001101050541c1d0488600542900000e40c004802444075a529400c43e50020210b552780071101290003e11030045010b0748800b56103a107640180503c00300d0f00070703032207005500303144042152135400602841100c5184103403843c0504125812415407195050203002c403400d200100c4140070460b401140154001d840e90202100d4145040d510b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 260840116 1250 260838866 260838869
    0x230303030f060603070905091e07021605090a0f021b0601060c020108010504110f0a050301090f092f0604030b06180f0f0402010210060e090c150912031b06090106050109 74
    0x8548201e10046501420110003560700301c15581064041d00c0c2c3c80301c011030034500c81120310720020502d8050600b1131454030480542c0019042c030240c0305c00000b10f1038a04480c0309070321580340070341842800280440080d900c000c1c1c2c1200070020642d528460b02d01d8a446c20380a0740d001c401c2a0050900009410b401810410b9000d68181c5a581c0542e10700790070030000342407aa02d0010000c034100000445840140d008200017140f649415442e9410840b44000b280c2e1000090a4140d2505102c4070104802c3c46035001145212003100a200045881924904081044d070b00d4200b0070201c0c0110800c680700028504c01e400541c0c03040c01c20102c02c11030655080c4241c0c1c2c40c2c4050000c4c2000f18101807110707283c251f0b0060040c01140d0303041418188201c120b440590180d43c080903141d0903c03079490011b00200701c0002d07080700d966800c4220b299210300d4512802c004030784035005a14403e8180041482510103201151112111803102207840179101c1c10100c600403c80c1d448c040011807158015405c4d0300 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 260841366 1250 260840116 260840131
    0xc030606091205070306090b040c0b0301050918101a010e04050103020a06121b030504210f0c031b03180b03040809040c05120c0d06080c03100c0c0c23030303 69
    0x1a07140d8a00080010700041c18841516140140780021011400318000c0c00100b610551449901d0b03d000e04207400441407541003090080b4041004220542da00c000280c3c0241e2108442e010010924245c00e1502d82050710051150303080c484800441d0710321a0543c2c040307000a0700c80707102120101c020441251400d0000035489800a14140011031041c00a40013000900b040020700b0a01041a0840040300040040001c3c0d1114100020010301208041041ca07070502e049101c0c50484c4000703072a00d0020405202041020128070050520425419200130040c1c00065402a0503007001040841c00361400b02400c441c1c60b10006403038540c00d086900c01c075000300030142043e02c0f030030400000d82007e02d180c0c4204002481422008000b40396480d0280800581c015a035141c40000c0c00103032500c542c44001681c1014a101440d5100496800d45a10b15810005040300044006130b8a9640358040904440b0b00540040303840d281484a034403545450701400003203040c4d6103041560303921080720a203 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 260842616 1250 260841366 260841377
    0x608010c230c0a06020c1b12060402190905011706060a03080409090317090a061116140109080309010c02010f050402030c0f030f03070305030a0b030712080f04090207050d030c030606 80
    0xc0e0145507860302400040380c0c0101950f56020f0107450b000180e0300140b5110a240d00000c6080031620f541c0b0001364407104007581e5041e00941d020403007541341c042c020b0000e40611600755665402c20f980c1c0b55084081e000a000800c0fa030b5031a5890482509202c191059091040002158507842c009501000b100c4e07000b0016460141450b00030f4010f0514030f002201030020420040c40c0800d0340c4400d440c41007800070000c001c0c282d6030b41050700c2a21101d050403512400c0c2080200061603105002c10312143e000071031078621344640301601c0c1c01130101d080c01a2025001205010310850190070040241e402c640c000e003e002035144411045071030583d00294141e101e8503452002e810040030305004400300a09444180312900d21032810743e0701050302100010400020081143c205100d51207540c8011707002401c003c0d040100300802801003400c007900070b00c40030035489840c0000da01210050044201c05548501d51032415a603610365102c0c0c1d80d0046030400882e1900c0034400d00c101411500543d032034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 260843866 1250 260842616 260842667
    0xc0306010b04090b030c0a090f110f0417030f0a210204060e040c0207050310020714060f010501080a090203011505040515010522150903020a08011103220c06030608010c 74
    0x440003071030113466180e00750180c042d80004540c3e40407210b0700204000400401c1c40740d0382e031508004880451402c0c1c08100000d2000c544005c9031541524141c1d1b8604000100c4001c4c00d42c1310340d143d03000c0c1c42c01d0b000c180d4000103000b442e49644544038411410101002a00301022140c045040c0e000b54020f002c002890150447d606c2c0ca82500480d0781c0e01ca43c0e0041d21f440c00d49a40100741482035240e00905400d0700000c0620410603001c0b2641520241000a03201ca810300101c80c09030b220061042c00d040184810101d46000240d80c00010300a500800801514086032521420003440380700391840b1318a008000341c03e43c0c81c0b20300d642c1500581603499510300304040c60400140b0369401e40380d1000300c102c144040b800001e90140d065041e4801d48840c55030501e14410014042d15640142105034140004410184060750680b900131074140303d801100354600c8031070340d814201c48002600c101c40e100300004030b16800d58060410707a10140020f112000c01400c099458034142c3c003805907000741480c4e5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 260845116 1250 260843866 260843879
    0xa06081b0102151e09280809030708010c091e062a0302060103030e01231b03030a0204030c0803040303021b0f04140a060609180504050705091602010b0a180c031805010e0c0306010b04 80
    0x6e50001161140d03a1090501d100540400e10b41034042c0c001c0200c5030b5590248030b28a5800c045808001c08562110f4284420b12008030250941c0e00d104107070520400428484040316005170404414000c04081c000883d00382c100255101400c0c0700503000f040701040c20032500d5100d0031000d04c0085c1201c0c400780000c00030200c0d07403100703500400c0c110302a02d0b010380302036005907000d000850083c1911040541c5841c110308000c4c180a5440c1d00004d0154001c000400000c0c0c1c01080d01d11000d081c4030b203a55004000540030030803840742007a04581c010714050b4600c080c8039100b03043c02d01941d4200810000240c07101c0d0280c03130b07160890041e05190140742a52a9911905810180d400b510900c2522a0141c0d03035408142102070a94100d140320810303e03001260f02d5824802c00042d14022510342012515080f4042034039101a120a9030540e00e07007031141d13403981c000d0300084016240c0310040a1500c0550400600a01c40c084081c2414018194601b0240c0f80010b0918166004000c0142c501840c000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 260846366 1250 260845116 260845183
    0x2070503030411061909170303070f05070807060c0201020a11030c07030813120f030816090b0d06210204060e04020312160c031a0a06081b0102151e09 66
    0x3d10325030712040400100c4071030070780e1025180d107050300c60f00d940c202c09040c5002161000703d00346880d402c903841031082100d0968000d445100089260824035070b01c4d075940c145902c2d5440b4800000c1c1c24281403440071020381c3d07415401891541150f95501c6d0342d01c0d0213612000c0c0c40e4810040d24440175804182c040c40458441d0000704244451042c070030714043d5075551422222250030900b0340d070309003501c0b0011003416000b03101030354001c0020347c4001d90700c3c546100141c50741c2e80d01d0042c200120004228000c40711010740c0918054111081055414401c2c6448030500c0100031104900450516800103240d12050701090b0080740e004001d42500780100400c801640c114080411502625445003008a00301306900d1000e1030041076004c0d4402c01003d0110300324200a08180103052070450104400000442c64035181c081d01c5482c01c64000741032004070b00c0e1032b40b40042c40490005074814043c01c0f00c10250080c5056041621507402e65442c840080d48030241c0c800c01403001e152600183c01c2c81d56010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 260847616 1250 260846366 260846393
    0x5181e041d010603050a210207030b130c0f06030c050304050307060513080d021321031409060c0a020306060604030f0209040609050609010608010e0d090e18100618020705030304 78
    0x9050701201c4040301800e45415503c262829000340c1409018031022140b000d41032540c01c0b6525103001c92600000b560f031903880c88050481c107820000700b68224542c46a041113140c001c1d000e8806552207000a5814080703500c912804240751040b1400c0360740c0684140c80c80780340c012002c0c0d403c0c981d4a8499034041c000003007011041c2c1c0b006651030030000b000d403c060101d01450040040c2c0319100c02d11001d207400b4007608517000c03124280c0c1c03c10854400c03081c41c1000082d403510b0558026595504803800134010441d0817030740700d1808140e8100008000170180811402203045405588489081c07001a00c10340c00b014024281070044140941400006150050300c41c0328002980d1040303880b00b45c1442010385407410565160300041200c0903090080030302d00078650780609001048200090b181000c948100c0b4000001307400003c0c5491078011391100f01c5641002607800b214103030130503c070090240b4011841e0740d074811900ca0130034141520984554551200c0114070707549440d1521810340220 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 260848866 1250 260847616 260847641
    0xc0e160e060a1404081005060402070b040204090305090d030c02030d0305010612151a0904060609080c04230408070308090c01050406051e04080708150903090d0f080a05181e04 77
    0x4003d0350f1070b0032000090040c802400104060401c013500c80f80c0e044203451010b04420f1080380180302d40400b040c650011a0f800c42d504070b03800982d04440380b4055a1a0040c0c401c0c20f607026294030710030420f2607001404900800c1c0308806450003000032140c20f4085480138080d03040002e174060b80e11040605e441d03020a003d030b411901000a9513558921004114400b1080368182c003001060907101030801d401068068507260030310040e614184048103940310a540c400c00e106544178506c0035000d94040c404100b02071840380b11301d945840c050400c1c40441c0c4c002002100064030766400101c21502c04954000a00016554945081d203051811161500501c2420080b43d0170001e500d6411507005d00100010b0080ca0050030f06c291038030031b16071304000001c84110240c6421400f0030207440c07004412035910329021151049050700d98180350180200700030b001000c1600003d801d00301c441d0048042c0000030003900e6020140c91100c014460410502040e0860719040e0030401c8126181540040d03905210 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 260850116 1250 260848866 260848877
    0xd0c0f08041802090f010f050a051308120306190602060705032512060501171b0f0d0203010e1e07030e0f160305060601050309061b090303070c0e160e060a 68
    0x80b00c81490801c00c41c1d0072402180250700041c0e8001c01e0600768018130000740c0900b0502c070f040c010b840010f03081d44251100c860410000092420b900c0013902c42c060050850141106d01c640390802880e03410340d005030f603424818038800d201c1c8138404100c42c054505032030495003d01b074a0f860780803040d00d0076017004d0100c09258441c20459038814107100f404600c030aa49036100c3d01020b450b160700c00115021a04114104000c58600c0c01006114990480e0440760f08001d04017401c0e5040001012030190360010407403940c00103404119864150065410380e049001c0741d56658581c028040c030981c4450300010a021600e100180f0401d001c2d602c441e11f000f4a800039070701150140307203c1d182030022052014480d04490201401071080400c64150301200a090503895810103085940c1e40d40d900421240070078800300d18907002081440e054071540b4001a0480740c86144070b20b01080c0b141e03c1401420403801160000544d20072020b4000c5822900f20349954203060340b0002404429440303285920107204 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 260851366 1250 260850116 260850119
    0xd11070c060f0915170106030b0604030206070609021903020f090721110a110105010b0f04030f0201020a020901030b19020a0e01030e03090a1d070c150903110706020a140d0c0f0804 79
    0x68290740c05540040c40c2d1792190a040f400401026142d0b0060700180201494a19416070b59290b1030f04540a40c1d40480d00320303840705210314041d006080f066100039005601a203040705110700c641060815240300701c81c9034415440e180103100112204851741c40021308401c4499500b9607a403100300311030607803154000c604003c040d00001c16560001c03840c400091076000c03042907941420f10030380b030141102c800394174900500c4002c0e411381070203a400050001c01340740354040e086a0007008291001030303000c0c202e0700c034541e035034100f41d40d481c90101c907104000382100d0203c020301c12080c42155048c0601da110500003540390001180140600c8205e01c0d61403108002c00318080e41c91071080001841c884509051041c807002803011101c2c805810312050090100380b0030000341c000c5030001600c3e460742c0b00010314042136080840702d18401003c10000ca0050034400700d06d0341d80c00b10361005254002e4101030340c40303803080005a541e200050407400004070b41010203000a10815040b0760114019000e80d814503 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 260852616 1250 260851366 260851379
    0x9020a140a0b0301061215030c0b0c011515030c0e1315090513050d02070303050415050904060b190c0203060406180506131502030403020615030a15020d11070c060f09 73
    0x991007a0820800304084040346001e444003405420107a003c0b045087d042e55240d40e0302e4200b048000e014a244903071010408400c4203c0c25800000ca40010005000f44c090307840d03444c4141400c400a03444006400c1c80724400070326015480d155004000030380504040c81001c15603100a006164071a00e0f51510072000086402c0303d40100350148134102d565410b109006c1c6002c03450803403140040019900205420070100740c2200945044406004441241c1e4003c800c08861038403540e601541e10504e8101c2c0821107105000240100c0076018802c0484140c0c0114103503040401070344000e505900400000300011020f40040a84036480e100c60b01c1d800000d40c0d20f25080c078000b101c0315280900401010024400701c404001c428503d192411403450410f520029107541e001800401c1042000c0c0904032107032820891310303102a803c1b0402605d2070960014a41c080e51010049080543c00c00180c20044c201c1081101c200035403024003030440600d07106042c0c0d1f021210500c540c00b8002c0100000441 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 260853866 1250 260852616 260852639
    0x92403030d05060f1e04020901030e030a02100c020a080403080c0a2301180b2e14130209030a03140d050a050402090a0c0e060706110a09090f09020a140a 67
    0x8009500400706851810805020401301a60025445032030441c0b1040c1e9030700c001c005d8550000030700795009681c41141c41300583c0980b44200b05501c0c140300004103c00762981c01b2a030405101034000c01402001d04121089a842005860251807603004000c100001070744031004104a09050007514840c0000e6119980c0c40c61043d4152484031584040303610070b0010a20031203060540c10030b046810900240c54640072080c0060a9080810488091107941e0440d0162503d0980380c00b500003c01613122403401c070764082e14502c00741c051790112101d80a5444140251010410054000c000910030b985080b28940080c00d8182c20380c40c405c1040c85440310060148070302c40d040c0d410011034141464414000c04120040070310100c0c07031604852005095000350115076032901116a25141c900d1410250001c05840c0c2000038a00e400017840c01d40203030410900c40440795415000c000040840d052201940c810080084d44160304c081d0038410092040c0d1070011801020b418003800d19140c0d0800540b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 260855116 1250 260853866 260853877
    0x60d020d0b0a080f0c040908030a0b0409080a020c030601120f0803070c020301020703030204150e060406110102090d030806130c050306091906091a0f10052101030b07140909240303 79
    0xc1c90b0400b003890004c841d810001100000700c2690100461815501ea290f020700000d01441542350726282d40b4151996541c10540e480e9410940d0950303503500d041000f075900e06403a0400e034001d01444000180f050307202c0c00050300c4160480d42000b022079075503840c5c0c49070341d2005244400384400300003500c0140e01d00b440940741080c0300e40c40060781e440c10b150000501d0941441224100f084019442120380c031130005403412144241809880010079940c2207001e030050003c01500080c8051044051580c080c6406014a009841c01c1d002581d60742c0b403400545008616203800310f0000c1000c1840b50600c07446243e4000390161203500d19140d00e200c000180d0f103060741310101440d2504c45840c40365807101038420a14108840452340340c00b00720040354400103031880b00d40c180308010543d519060015a205452401e090700c0f0f9034040e40e101c0c41d1000707085500741e420200060422600c2c90300000e540c81101c510140c01060b070441c43e66410001070005504019004d00200340340240c54442d01c04002900 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 260856366 1250 260855116 260855129
    0x909120706021201171e0a0b0a0b09010605030c0304030c0f1a06010f030e060606030c090d0606140d021c140102040e150114120a2007020901050a05060d020d0b0a 71
    0x590b1103860f60307003001c41e208040e08600700901d11881403d40b842d81c001900c00d90156400000b04c1c60004001c00e103424002081e0014005540074000c2010a81180d8007207200303110121982100c2d039890314402c5034a800122900e2000d06810004100828000c04660b00da083c49144410803803940340e6a9048242c46010544c0d8660002c03505014141d0380003911051001034603d000c00c925031a6800465541c50094082402140000049414450141c04607501c65070b02800226000040345841801416240302d044200102519003100311310380301d212000c4968008120300340303c1b5134051515034280c40300d1004440881011105c4d21b2010820b0020700001d00030010441c2040c0741030b40071100180e02184049040146510060100c0800310050b2030701c8628450a2030f50650310400104000d020301c8202203a505aa20342140f40701c100180107111183c030950b5900d2040e42e0f560148a02d1003014000c280d88100d043c0111002410154007a0041c031408a602250090204020910f00100d64100a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 260857616 1250 260856366 260856371
    0x60402190c020f091e062404092301090b0d050115030506011523280e040507050417010b090405070e0106020c010903060b1810050321090909120706 65
    0x600940c0f0300b40d250110311460940f1091140d00d001c185a000d401850708485c4490b110b40c0000c10700e140c4902100c95001602c4600280608002d50460190398000e4420010b0329800c0000c02c8030424180000c120069400c10b091a4203039007440c04007006405280b0301d5940004802ca036000124400b40203074540c001b4032030345a1301c1d46400d506000341080d005800c84100c01141e101414101070b442421010110460352800481c991022a006c5282c80b41a80100500c00341200c0c00c0b41d01e000340075500d501660103803225001c54880500b0302094500440c0c404000c20000d00c42000711014640c0c4a4066074a40c2c00002900c0b013480b00000c0c981e00c01500c099686074846c02081c031280f08203640703d40c050310b0140001d213105000c071000240340c07455501000f000d298550b003142a03182c56980300490079114140090a842c80d0034461681245007901c1a60b11911850803c0c0800c0300400050101440d9010100b82c070f0311000f0014040c0c480c001030400d4042d8442d49020500101c0b038480074183c03281c42103030301 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 260858866 1250 260857616 260857637
    0xf061c0c110f1b030a05070b0d0c020c0d06050a06030501020316020607051207050703030603080a020a2d230307061a0f010f030903091505040f060801180506040219 72
    0x24440340c1c0300c100caa1101c0d4000108031458120006402a400e11906000401181d45102090400504510040c0248101c210118503a40060003801a55125590400140540c040126562100340c4105c035001420310300e8501c040341407a000701d40d10080620b40410b03030b00d60342e9071807600f26407040360051488c0c51008500c0e61526810f120183d01320a00e494200d050801d987d14150b01c0c0e26000d440e84050001c00203038802014001e8028000441c0c02c01041074a5440d1820043d4a504031a40201c1d02191221038041c00e8203007040b40c00e400030310a075503840d0f1041055030350980d40c04418542c54141c1504205806903100c01000185880c07803191f00089901c2203200d502118003a201c108092141e0b07180304a10080741da200340100242412451f000c0362046403420f0507103807040c142d00711446019003000300510306604074000300115010340d070122509550750b110490785003100b070091a0581c0601d0045c0180300741c464002a400c500001c000501d05030a9036030040c2c0c281d504480040100e29007881 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 260860116 1250 260858866 260858891
    0x60a15030f0e15150109051320030a09050c1504170a020a0f0f0b0304020906090a150602030901090801060b03010326030708091b03060735040b0106020c0303090f061c 73
    0x5940310b080c0083c203006c2d5845042c0b00006565084000f80c41003c0350f138031500803108a4081e10322100f1400c21043c0c0c01c0d0369080c402d0302500030b807030014070940c1c140c030407565242e2070307410001c054099041c021040796007006d0800c00703042c580180c030b284d10298501c2810701c07110141c3d07654103021000742590603004100e90318200c508480714406510610a4031000c1c001c000241e1599881164800b100b00e407144070540e260a4400000c00d4241071600109110810200303185800000410b4002000d89541040e503959405c01c80c00d031101401100c0312000240010400200e0441005580c044001c080202203a8440f0351401150400c8824030000380c00708040c01451401071121001060a10343d1910075440301d2400b19689200c00380284c0c040165101411f881c00d801c03a508048a450380518403c12540d1410040e46540015a02528109007910000a18234000925592980c1001d4040c5081440f41004c00c034640f22003181d900d40003c0100070b80310341206141601440825880c038005504200c1c43d9 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 260861366 1250 260860116 260860141
    0x21f0507020601061d010c060f05010303030501050315090715140a080106110102072013020d0b0f01020a030c391503060320041e0207030305060a15030f0e15 69
    0x288403a041c0000c08000e00a0f03500400b818501102c403c0c241f41254403220f150031001090b11001650b551071404d4000710030190300d41c00040c12070700f044088603980307410701143d4891040e00b90340c1c40040da07000e042c0421035000c0311401d0b80788078a403074281160800c008209100301c560160310124005a05140148105c9400c01052041002c100008508080507a50f0b030400c101a030703520307080c000100c046c4000794990320394049440000c1240e00c1903440b01400050071001d0705041d100301c1e01c60842d601e0f40c20b5180d40b00240e15942c007034050f42e40000b0107d060711408241c0180700003400c94440018020458420020300c0c18032001c0d4039500000300d00345044240d444500702c81d8904401c140c100700e010030205444540e078102400340c03c0501d41e04116440c00190090240d81c03a070b03448ac04c1c2c0f075481e000c1e035600c41a8041c1010300d010b52004e204e2036941c00c04001d03d80da028061681c11005902e541c0d640c59101e50f014540c1704803503c0700010242c10360810240b50170441031001c0c2d0402403103000c000b000c00c64003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 260862616 1250 260861366 260861369
    0x15060215010909200307180b040b0301090206070f0606090e0d02060f0705091302070f0b1006020102030606030f07020f03031f0b09010c0b0c070f1401140c0d0c021f0507020601 77
    0x50b004000c1e50040e43d41e81c010f50141826400868445032042d1012641c09011180060034070158081c031420298010170080e2030301501103807250749442d02c030010905040c0a0a00c1282c0d0060080d442c00b00d29036200029840c02000c02d85046030764940c040780c40c01c5030b031242d400d85005640c0184031001c2010030017485c0070b1006001402c203504900a00152607042020380c0c64241044a20b60300d0103940c1c2c81a00001e0140c1c010140251745040040e4090050b0f80d540d04c0c0c02822009403015031644c5608050b402c0c0d10055801d985c10090400019a09610fa0120550059120b1041d250000a19910075165400076603000c200241511110f04c0311f1040700c2801c50041544114050412100d80e00280042c544440007822460510002030710220141045070301540d8401d61001c1400340d60709040d00c5500d8050f411b0492586050210440c80407900880780c407510f4036207001840d05464030581c6015248007603075041584186103a00c1011b6400d040303580c001407500c03500000c0d0b42c07800c51070092038084103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 260863866 1250 260862616 260862629
    0x212010b010e0111010f05130203100903050409050c07141b1807030905070f08150708040b010513060302041811010f08150a090207050604031214191506021501 70
    0x418001960a036040750000034200804d00340301000c085040c1c400c0d400b500c0b1440359207508a150204005042aa07003c6c95503806000384c0445010b4554525664111200f01d003000c0d0100d807003031204204060b100d80200f0782c0102d00c100c02070b08040c0e5984ea610030010000c030040c4102d030410010415180d00d10b100c80c0500c500200d404840f1080442e82030700d414034028195000300364841881300103010040100070020700c00c001c41001602c0d5908581030321340c0c5c8004500d114170042840400c102a12410a96002d103410001e8125140d1803c0104002c1c00e0742c03158602c1519031105000005640c0b2032080c13050100c2c00d8042070142d019640b800880e26002c10400506025091046140484e4054141c0c1e03800050f01810100f0041210b00007041d07000954490442107000180040c20400003141c2c41d40121700c01d0f01c0b182d0100d000c07540511f060f0303201d69050128201542002980c190085000411841c1030484000384040100580751a450b0f00c036000036015a01102c05402c1c03004650065500400d803 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 260865116 1250 260863866 260863871
    0x120a0f060b190e0603070f0e0901050c0a020c0111070510030501051002030c12090d0f0f0c0801061206050402060d0204030507080d0212090d03020f060108100f090305031b0403170304021201 83
    0x18030550b1864212881c0149103440d201c0740001071443d01c0400c07681e80503140010200644075519005c10040203404c40e2044030650a00d00822901c0041100340d8880040940107000c150700c0100c011a1010562401d82e29580704c0c2d2100062140c59442c0c0c9410203201c9a9804580c641c14102840182d03106254039a0031540101308401d44460081605006d200d40d02c019180d076001c000000611603081c0c0304000d4804152503000c00e0400410078140c2c0c81a03440741403080403041e0360f010702508031129880b40b902c0010a10648800080090703000692007840108098140400b40c10b807101240c000e034100310703610781c030800307040c0404602044800c0141489200600c006404d940c00244103010f040f0340c9502510442c000081090700034085001840300300c100b240c140b90b9403100310300d0b61040081d10501b00b403403401c400c44c0c402ca1014040c00d038900790940c0f1041d295403a9500240640001c0c200880cac0c010000307200c04800901c03580700144031440814403064032030815004100b07150106083c045680d80c03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 260866366 1250 260865116 260865139
    0xb0a0b120a030819060b1c05090a05120a050d09050a031d0d110f120d030b091e25090e0a0209180c0702032a270402120a0f060b 56
    0x783c1c4001040d500828010545902841070000b01014207035542004000384004500400c6070040400200903148520130140302503160424020744883c800c40c00640303d031308004143c613002c03080d00c0b0052040600ea4176005151000f48500c040440b100000202c4e4107030003e0040741e00b4158021a6840c01c6811120240c581c0c960480001d5161510075000605101e5105d4078a140c994a00c030411107030382409440c000d810345002d0810749d10303901d8014051300400d240c1141c1d40083c1c03c044900070300c0341203810ba161000c0002e2614280300d002000f403d0090362031104001000070040100c0c0c40080b0084d540b98040c14a09000b17031b101886000412610802c0c0c41489070705403e60b01c1240040f0a01420a5540c00039140c10811021314492000c010790148100c440320710007800f000000103006030002190216041144c400c000440b0000c00d00b01c5d1280007501c0c0c858007051400006950014801010300c100c0441c0e0072000350030040c12140658881c043e00c3d184e2001d200042c00340c0c07800c114048541e0078110 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 260867616 1250 260866366 260866373
    0x50102060705181e09040309031202210d1e0207120c1a060609120a05100c05070b07020a0c03030e010305070f0219020f030106030506090f0c0f1009030b0a0b120a 71
    0x1e0300d88100341d0307215451519004241d0310b41c1e07003102007413164042c05d18507152070a8100540240c10500c01281c010704410b0460911502c081074142110b04a0303001d440c0c9441c3c0e0307901140600e810408219000540e1046045482407502c0e4401d06180048400980c03241c00301d0801c02024160601d0714418481c41280100c000740002c50601403402201c2c1c2c1104240c0c640301c002c40c485000e00882d0a030401c0b40181540104580061000082407064044070b02c1c031000740c20214280e610b0301c031030031011032418800c1e031000500c0c5050b41030b4041c06510480300d01c2c04507500c4100c1d01c1e000d0742d442a0041010400d00e24060b59042c01600d500c082c007800c1a602318002d801009503114000040c00d0f10080c00c00d01c07200119079468416002903240140280625501c1c4d007045501d80205580703000082c07041e9070f40d0354140c0101103046180b1150042078604a580f016060240c004100725403201000f80303581003c03000030031888000c5c0c0901703888074000846c804030400740101074100c0e40404005612074510350001 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 260868866 1250 260867616 260867647
    0xc02030c0d050a1b0f060f0e060a0c061a1503070507020301050c04091401050a060f02031308010203010e130c06030c050c0114100e27120c0c011b12270f050102060705 73
    0x31106c4500e0032030b04011040900311031501004801642c04080007480d015403942c4007060103407031405900c0c200140e80f0a903499040580c07805007016040742d14089a00000369a031000f03181d0060490615514000c10782d40043d003100d5003240c0e02000304801117014003151049119030321202c44111003034401c1d0f5040100003030501d5060311400d0104080301d058101d48034400d02c02d455001c50010107060b621611400240d010b03402c00d015500d0760220280029543c40d10524521040c5074002d034544514a00f0704c8003c80141880c0080031007401410042c00100700024860801c00061b0004206500e040c000800501100c10b60b01103940c0f500407100340300700d011040384801d294140e5092048804003d0f00380d11070a10010200e000250140881c1d150b400b82c10124000c948401c00342e0702c000044010030541044120610f1015260f0104402c101c041c680c040e041d541154a4030f200c800101d00142800c00407001e100350445003550352452020420740d43c041280907004199414600d04080e51001003006 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 260870116 1250 260868866 260868869
    0x606050d0f061802060705010501060f180b070611070c180b03030313050f12090108011a0d09031101020f04170601060c0f06060914091b030703030c02030c0d050a1b0f 73
    0x341d07980f604200c1007441c000c1640800030b0740c09800252030314441c2c10110300811091081c0b501003140003070f4968450b0720894031441e5004040682c1c0700d0050070011103010070703001544212502c907980c0b4070303020200c502c3d6005004a2441518818200f90400f0134820403040e240c09411401d5040a03d10b071302a035008000e580c5d00c130141c42c045541d00c40140c10f06514000c103428850009019224100b4000070081000346002030080c0c98200050f40c0e14082420842107044410107624000c0c0302c103590104103a001680124024940003065405441c042d50032030703201041c04058680001820020b1000a030510f00d00d403c10034014012940c54040040d102c522664030041101e140711032440f04204a981c0080042c2c20b0703283c4100700c032504008054000c8803065440000b10320918071000042a1041000081c051014000c3c0032440c0c03447c1d41c1075940044d001d804a0341030040e00b9034400b858803694480c1c1481802000185000394640c10302c621544050709950400e90013002042c068614024542030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 260871366 1250 260870116 260870123
    0x10906020118021c12020604060e122203080d06050405060409020d03080c070f060501240918090b04080426150601110106030c05120601080d0e010c0605130606050d0f 73
    0x41207148108507000304d00e051004000d02229500c0c040b01c200944c006042841640f091100304940564040701c551fa03500703a1540380310303c0303c800c00c46000000920145040a09d5441c0d40300d0350300c3d54a80c0c4d5103c14603048822100d98565031380b5400c10103441c003030240d07c0c1c1240d0300307a504000054440d000b080c0b50488031600542402514800b0a038652001e40407104199040411860880090700d40100035210a01c127141c912424140345080f0380c808554030030820541902c0300903503a031904280ca00314014207042a02590350350041103021070801c01c40148942e208190450380e45041200705034a071702d4202d010347e600005002c5501880a000902072030000280240819582d40c1c00004841c03569050075030070356a50802000008201d4840d0010b0140c0304101c1d00c0c2c040441e00c420059a40c3c0500744114481e03640301c841841d160b5800360840407550318061400c0201c3c11a04e4640a0980364103032440242600c80b65000401c1c8881803241c1070260000700d801c4000300300181c03100f100a00c06c0c40b01c084c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 260872616 1250 260871366 260871379
    0x1c080d0b040b0a2c041b090212040b1807090605030105070527040204080a060e0c061810020f1501140607020117060303160311060f01030b0103240e030901090602011802 74
    0x410380404200002c00f03090b1040c0100200305d02d042d10780b81c0f604c40c42480d050b5042c00507505000c1400e80740b0f80203403a04802d1480d820043d60365261904042d01d5000f810802d0207462250140a491405010a0002c0e1207460001f05040d8980000e15084880040007001080400d102c4450054900c0d0901607181e8610344034590f92000010002d0300074410741c0e004072020301c10500c51908210355238118801d419000b800344e0b5071696014061100303900c1940428400c984002c2c905042e81d1410300c0d21240b50100d207104940300c084a00c8845442e14030880083c0d040c03901010010081181c0964555698280c00c0d074006040c18280c0d03001900355001c1000744c2150400341d500040481d10108260b5050540864460b8008003c03814042c1106565134010710f110300903040003400700c10344aa0b016049992103402000a686541c49104069501ca080c41c52005400100c03000e80c0c0c00c1d00d000760721510b038804000e03556651806c000908900d240e64891070545e41001290020388101500300c505841c4c0659a8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 260873866 1250 260872616 260872649
    0x10503210415090b0a020d0f030e19140304080a1202030f09040509011b051b0102120c0307030204030209250315060c05030c03040f0806010b031302040b1c080d0b040b0a 74
    0xb50340111081e04090a200d0000c02d102044c5a40014131004141f00c07a00c1c1e100d06001418421800c0c0c0307181c200602c01552210200701170324020050010492800340010100020811160b5400c5610541c41700314194051410b0509011100200d1100041c01d0b00042d45401003a12244030139000d1509003610480e69000000c0c1050829000081343d103004843e07030702c950500000c1c060016000818400c0706c220340b50b000071208010510860b50504065104210340f03540d1481d54041d29031009140604064007800000f00503103480651500805192401c10001c825011480c0001582c20140740e080500300106080c1c003000b8114010141c401d20314080e82a0185420140d203107100d0b080e5184001e21001500003203d050360800c940a960f60301c403d440040c3d0742e0700d03a0f400540c042683c0309a000c514861800005182c0781d40170000400002c0c0010750500086480603d00c01c2c1400401c1c0e0b4842000100341c1c2303010555102e0b0183c3c8078021a0f040180802500200c0c0b12861140a22101320054211 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 260875116 1250 260873866 260873909
    0x2060a09021003050411100f020c1203090f0a32010203070f03080604150e040210020706020706031d0a030e0f030d090506030403050913020c01051003030503041104020915030105032104 81
    0x50141d0451b00c094900140d0002a02000f01407049000d0303010f006000700d4410030344a2800380ea09640c86946c40c4011410150340c00e040022a40c0f0000d00c4540c001019800090101c000c0ca00310000d01ea08400702c4032041d02001040501071301e400c07030b415045410070082800020111003181800036018508081c10344d4915000c1070062205050720304c007001070301000140b507507070039040241308900c25074003d0b040c000c004201740d035240340a0141c680035070850030f024001c0d11700c2580503498800f0070080100260382c0d4030a0703a03400d168030000c05600140e1103801031070072410000c5075606a1710b415401841e0b6078101c024000c0c030744581c1e40111b6120340d10010126050601c50750079251400c6004200e5a40d0054003003510000358044006440355508200c00542c1c3e1440700e080440c101e0f0b405803511461a03583d55110030442c0c071208036040d805542440600c0c1e817521402032141f490614003040391383e0395040c00308042c0340c9a04480c444000518101c4540c1c050f40c44402500c0440d802c6685220000c401004e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 260876366 1250 260875116 260875133
    0x703060b1206270103021002160b070602091f09050303030601090308070c0f080f060106050f0301090b13020a0306050a122f061603080907060905060a030908070503070302060a090210030504 83
    0x45100f8200f201c214040354403640c8101c60904884c0b08441d0030744001c4101178140e884030b006c4003081c1c8089018800400c50750042074000c288062041c14010300d4035a29a000034000280c80c580500b0b040010311700519007030b40140304034026150850055081d8508ac82c00200b00c5241404018030310280480c5110400070714100303030300c0034081c403003644000309031608103803541c41140542c141c140c0d10528000040040c01030007102c03070070000f80c1c140c20b14580c00c00790740308042c101c00300320740c0d401000303a591114100c00c4038070250081031180da402107001442c1c28208142c145154100c0c04003041c09d100080001941101a070300004000b104901e031145c0c3c035003002d40401010519140e000305001070072038000760b88144203540e405c0c030a0300d48543d1601c5480401e42d07035a409009003008241d01c0817081c0007510300340000e0003040c41035240204840d1110764542d5120b1b04010f00444947d0301c0802c1010404d9010b02c01c9a0b4040c4060408000808940e0002441341551503032100c149996140400c09000700d01 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 260877616 1250 260876366 260876389
    0x50d09050a0503030601021501030209010b070f050706030b120118110a08010f091a04051e07050301091506080d1211041212090518010b0a03060f0e040b0703060b1206 73
    0xc00351201400c5508090703889900464010340140900844c000741c42d0000001141a01d4000e80107450580c24038100486c994460501030301c0f5201c1680716032000500030001d2001403c040c0d038010600000d05014481d640c6d04440109180380d0410380200315000280c1e001d0541075070412007454484101102280c07103507003603401040c401d500b03040d0f05080c00421500321034035180c41b864081c181250248040f10085a0641e0000d00c1ca406c540d05400f0122100c18840e11100030107000d40e202180d8840001c1e0850b4003510f401c40d840d062940b8402c50f9a04544151002085100043c000c0c0b43c0c44076034010200c010048140c85096540d100041e03000c9140c6050394007034840000302d5103940b0240d05203819114000e0b00940d001400041010585040c0300cad0303508120450507041002941d080c400d0003103098105888200405656139400a40c213440e240c1c100004040b030301050451030400b8105006000d000412136001c0c54200501080000d0000c0100c0d8201d00c4202d1240072261200000034103410140e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 260878866 1250 260877616 260877623
    0x80d0c021501272c010c080112030f120e010e15090f0a060c02030d050f06091605161e0b070e0a031112070b031503100506010c030c03090b030a0519060510050d09 71
    0x135983c0111403210154000d191064254480c2c045903a61101900001c01c50004010001403400040c030422a0150840450030b07906900041220411425060b00b10388420103448180c4c0d2009482d4802d02d4262809c00750094015030242131080300b00a9000d5407032004030001025560780e911a02d04440c4244151007040401c10801d100c141003030302c1c0b5240d000c0300a41c1c2a43c840c01c0b100c0085102c1d020607402070301200109494190902295005078088401c000f0010380d041500c086048091a034605180b1302d4040c4510003923400703400e011000a0a0880c80c94016001c1c41c0312042c00d10121b20030400125031814121011450129421030841c00c040b25039100499255004c0144914508201d0701401b01c40815021038a8581f1401164020342c1d10a0f41d401d40450f0001c8506800300c1d11031014480c4040c06402c25885142d0b981e00f112409a02c1203031045651640c0300c013440060404501d01c021480c03108441440b400d810b050000d8112070700000000309020b000500700c0c410b82c11030b4022055440d003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 260880116 1250 260878866 260878931
    0x15120507030504050f07030b06010c020301020c0307060e190f200a0602010209030f03040f0306090305160b010f150207180e10142203030504080d0c02150127 69
    0x40011000c1c026000644045415004030441402c2c00c0340000f4440e821030380c0007852070489448107801074640c16105a0140c0e0195001c121b003001c1401d04100911502c0d01c66080090301c084180c4200b8289215000c0010380c100f1034407101004200c08000c850000c50300900c90000c1c0455402211411200d440b00da03030b4104a104500240242e019406031212072001c1d1b0a95800c0c460594000f030701c0b486103000d030700d4814000301001d1010910541c04440345620030704205142c20b90b80c402583d91021030f404100c0f41016242d00602038001f50901d034000400c0454101c4400001a840c06521075256009210042e0300501003104451803a4000380e0200b440002521104a083c0440101500134409403001c08040ca502140c50351206560b03001c415030340b14450050b101c42540c1d0480c00303000040c2c8240e948040074048010301c1c0f0142c0c420f010388031040d82c005251821021085500855050340040c1000401d00d028901c0840c401c05038801d0890604e0340000e080701003440c5c85035840d9407807021028020 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 260881366 1250 260880116 260880121
    0x3060109080a1a070905010914010512100f060e03030a081f0603020711030f122b0c030b090c0919090504050303091b0d0605040f1b0302010311070c151205 68
    0x14210440200040f0090000d000c030b0b035504903080e19400b80c50712071035000510a01c001c0011400e04a85960305840c1458541d160084c2941d031202880c2081c0d0f00400d0341c03078021404010600b01151010000c0c400740c141004005440000a030f00d034002c90211006000e070b142d0001d20791540c0035440243c013604102c4800401501c688004000750000b0b0012038482e02c408803036a05e1854005420b82c0c1d219503113002065160542c7c140b2082a4000c00079405903004000c0406004181a01451090100a8100040f40c0e041041c00a0940380c594034a54080d000c00d00a00841035806412034003440401da4a03180c0000b41e0245d683c1c8900156404035010500c1c080a0104202011000b940115a40c42c2203600100c1030025020a00c01407030b0820754460f05080d850030000301d240d0051940a0b0107041d6031160302c41c0c142c41d516076059a00d5002c01a101e6080024021507130035100b402842c1c0741428141e402e1a80c15644e9000401050142001440c40c4090301e140540c40380c0095180030b507000c4800d10250 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 260882616 1250 260881366 260881373
    0x180503010f020702181b1e040330120207140f06011d0c040314030c0f010605041103010506030609250c02010f030207050d1b05010501080a0308060a030c050603060109080a 75
    0xd42140030300701c2c8541070040580e4818200046100d0140703010450f5030003d10600d040e0301b200b0b640306034004040c00302d0101c0200f15900701030000c2e1004500420588400310440040c40440c4551441c454010700b0750151602ca040e944113900303045c8400807075401640c070101c60502c403144042205a55241d0301c2003005c59450080045a01790413140582500b1034030074450043e14528290481c0e0040a07440d0038442003001c42c1030381c4900100502d400701501d107850b50000c94242804100c0d88580c0160f91150000c12250030f041c80380e0516801c5116000b819541040b0020380b503444003070aa24031901c200000301d0340c04003410481c1c103000c108081010710000500c00026001c61409202a8046012011808076a6003c1c2c022509030715801006040c00c96a440d8050710262008031801c03002e03a070b918401500040c400d2203014042d0441c20001c06041020740b80041180d60b000b002c207409003c0754602003000034000014070043d05c0b001c0f98030035165558607004945501050b449045135114904c4071100b031 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 260883866 1250 260882616 260882621
    0xc1611010c02060f13050d080702210f01060602070602010605031b030c220501050f03030901030c020313060201020d0b0604080615060f160b0f07021513170c0c03010c090303180503010f 81
    0xe02c041e05d48407508079030b0b200100214005c000202600401c0108845d000500d05a1000d50040502d540c4c40c640c1c80000d1109a40303130415101c080708150f0347d200010b001c455010030503040104040e2000b803050034140300c040b0780c582c110015810410000c0f08510846960288a01a855070004d40018084000004980d00b1510040225000c0e01c0c54280042410304141c4010144d08101400030f5180201c0303100114001d08283c0110000c600082c041c01800a0700300f03000c2801031a071070707002603120700c0424100012191a45242c5105083c20003040208110101c0c40d00d6001014903000c1332400700c1000421090710a4011002e091100024111407101c1c032110001a160300a040d00d49090b501d440030207880c4281a0b8040c4090b900030400c1c000c031032590b5a03015a0001c003184c0100001081070340d98400321202240200028400440c040c00c00e42010440059150300c02c0b00284810365941201800d448840d001c09020841001038555081510741c40100080401034001c1007501400080c1100 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 260885116 1250 260883866 260883877
    0x100320160b0702010908030c03070207152309011e050405211005040803190b040603210206040b0f06010e03060906060111011103010b03040f0c03030f080c1611010c02060f 75
    0x81c152050400308070680e10511070612540c0e4407800284c69078846200e000202c0d00000c200c1c03811803140c41ca01240400c1240044c001a1175a525070005503001210f000c11805035030a0200343c0500300703201c0c0d82540d0384c0c0036503407a80901c98894851130f407056660007100c441c8a141c02c840c2e00551040c0100140c03900302040300c0300d903c84180039150302003401015a001d4610031382d00680117100c00c1c0085480310180002083c01003865980008000a1a90110f01504c1069209960403d03000c1c0c06120301d01d00200c25011840385910140200f40792641c2c2d599500100a064031017400b522000048441d0d01422502c0c2481000404480f8140703014a803047d650780c01110750b640021084000c5030003192050190a0300c4080700d0a0640c10b680c240b500600043c0c0000f041600e50b0305011010802007283c031300c0c000c1c1c007850099a80c040303400501d42000c0c02c00175000c0c05500c203c000401510a0304100d628100080300c0c2e20982500f40d524800c1e0040380e0394280b950002c0c1d07000000041002408421900510 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 260886366 1250 260885116 260885123
    0x209150433020a080a030b150406030e030c07060309030e040e0607090f05090c070204060b0a0801050f0621060a0915080f070e0c030a091406150301060510032016 71
    0x1100000700d001000680c103000708000002d80e0280f01c000340055001805007460b010203180006044e02c1010000380d1100b420081401e01c00320000f000e002d202d0341030007140c0140d1400c900451804402da00030035a903007010301c11031080550f51301540342018030850920190741c1c0300402c1840b40c011049221034039000140c1300d20000c42d5503e200005c2a06210f60441c08a4000610304901c43e550000201503a1303005100032039206580e00700100e90b0704c48540c00740200c411940e0f04e0184541c1800140044c0010345214940301d94018014000010258101c1088100100491007501d0703c442011031650302d8142c1002e04041e0802e02c0e0001141b15119002c0b084501000c2110704e070141c401011502c0360740302e01850329100d45113800035402a10b0b5100551704019100d0002807520510345072800ea6003284200d40400b500000103010405680c0130400001840450003001090310300300010300f00d20500000076050540781d46c50111151180c076403100300311002400142c3d60381c10209010400500242044 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 260887616 1250 260886366 260886419
    0x7080138280f031d0f0307060b010e06090409170a0216170d14120c030103060e0f030d0c0207050405010803070201110105091905010905070e01140108040206090402091504 75
    0x10404860200d2200000340706516100e6007100b141c08201d02620307403443c0081c40a0084420040304810800c0403250000c00d9901a43c0ca03070340c5078680a4180e0b0b04681c401c41c10880d4082410030190780305400c440203440220760004240d06c651415004d890007a25402040d80c41c08908905000d03000310f5049000390400320381002c05c68461138200903210315821102050f078001c0c02c000c1d207142e0041401c1075503208000a0a41041422888203e03607000c121810404090302000400800810f4090f002d4001d5818019107162075141c07618a5481c09092001e064281c0c40315107404003c1d00a210140242401070820b001a61b1258507156980d40112802c80c005040403450300c0100c50706200342405501804080d29010400c40100d181c640d1280030146c62039503031903250b48001802001048001c00e0441c500446561416485680101005c0c0a03907042c00301c03080070000140d40306802c80b00384807801c48005803103041c0f10012414080d4440d507030040711036000601051403c201c1c92041c400c5080701904 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 260888866 1250 260887616 260887657
    0x1104091e1508070b0c1b030316030201021c0e0c10030b060c0f06070903030c020f121015090b300a080306040c0f0e090a021c09050c060307080138 64
    0x254929845403204101494101d400c1620b071080516a41b055109801001c90f42070140d14565040045150301c8101c0244c0c0d130008407400b030480d2180e82c0310251011800204581d460740320380d441c0c03030701c01e0542c40503c18050800c807003213024000e0b03104401c0b040d0050055a1a182c01c1c40d991944c0c6d501024500400344244000514081d03c543c46210a0303c8c0d05695400d04043d055007130041c40c0c2d52011405501c203c2171003812102d040700700007a00c4c00300b00d052004a0126101caa06005004154010108560501100400c1ea48640b0603860601541118644001c40128a0081c00c54072071156054207004400500c001d1005440255000d0301d000c81e400c0054410b004016541c0961104401c2c011400101088035a45801503440e9403086500801600e00946140240342c02c1001c6207608404590b981031180c24030400300420200780005848851031810411030180c60b5420510503000540c110b114460710410702218030a001900c914180010302c00c110310000140d03000303000010349040b00b0340314 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 260890116 1250 260888866 260888879
    0x60306140c12040f0f0f020111030415080a0e01020304050601030303060b0a0c0b07233001031b05060703050909060306010e0604090f1a01080d02011104091e150807 72
    0xda00610310600c0700c03490280405186202440000c0003543d184d11504800d40104500c1810021410300c01c1c0b4800d10350315010f10001d454507440d50b00c0d4002c0742d441404180030089581585100d11551403e1031a099602d0fa140780d80270304000300c254840c0394000f00c140b108105c1e00140047c1a00c1c030944040c082c8503207900c0b4140300c900440300c41800241d0300b02c030001c02241c00c100000380c005410f440e03c08c026020038041c0c809082001c401301400d107000050682da01801c4030000007007962107403802c140303502c0340442c1d403418118043c0006482040c60640b022480b2200c9000540201000780c46a0b454a60328200602540c00407008030380200f0301000043c0c0e0514000c241181601c440c4114004552500c10500000b003912020489200b811300106001180c0390064144010583c00e44140b087e40c1880c94090038100551102800d5a04101c80496056003120030396064031a00c0a000451074112203050100602c410000b10307181e4034100740c00e400c45040d85140030580382044225510f5581c6c400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 260891366 1250 260890116 260890151
    0x50f06070501020f09270a0504060905071502010c0309051c1709010209010e0f09190906110703020c09040c0e190515040e031305041104151e080105010f08090f030c01060306 76
    0x2400400d90306e29420000f400045103501c89030b000f0f402110000390b40c180c60b5880e94907110b90b82c0c005465521a510000d080c19a090280e0000044545420702862040340d48150b55046c1c03007180b900c50202000700d612880d500c036512003442d4114502d04048142840765649000b94420703401140042d0800110002508025645006000c006002c141d03041da590800c0f20444010111041d8190385c07120b0344030f004940c01e4040c1a800f170060511326562800b0030325000e484d022404c04ca4902440c03441c001c000206121981c0d101c110b520500b42c407002030340e0307606210812440882030118840d280c4801d00204000c0207941c032020602c1550304010340c00b00340c48042d45d03d0081da0001131074886481c0c0240090b0070b02d50020b82e6800403000300709040c55107480410100071125544100050005404800b0070003209a0071409a1140e0415084a504260000300b900360012520302c2407000c07241c080741e1b44000070410030650000307050950f902d0303095410316240648120b00c82640c0080c1405116080024980b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 260892616 1250 260891366 260891419
    0xe04020708090d11040204030503090901090b0102030f03060303040f03050c090709050307061803020d240c1b03170c0a08100609061110060b0c0607030510050f06070501020f09 77
    0xc6240341c10700d05640308008107082e025601303c41510b03800c00041000d4803240060006140300f2405503071a2500001440084081680000201c42c2000c9507000d01d40d80100c00c0b03641031500703208526920b58801012901d94402d6a00044001d55801c8000080c03240102d8104401b0300110b424015903115800d00300c48101d964041c29515030007040081080900500017090280c50b0001000300f00e40d41c03900040d0081d4170b04041030301d034a2660000141e140703200010310031301c1c5029810304102d0808040390041a04030019040820640c00c402000103250103040c0c00780350300700e481c2080f44681c5061104401c60b50803a89403400443c241c440491a00360103a54090b059a00310b5503030400d5246001002c0301d61001d80080081c0307600074402c440001c0d600c280640c2000d880b10440745a82c584045a5543c60280e00502d890b080600d4030051140302c12655140e10308030703002114140b8081c1175100000710a4454102c008009610000d0441202ca030f41c10b01070100c00b0000c4a40e0318025120840300f444040c401c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 260893866 1250 260892616 260892623
    0x30b0102070b070512130f0905041104020c0a0b0103240e0c060f0408010e010c0906080f01090e03280206010509130303110403050102120411042714070905070e040207 73
    0x600420b1001c14108006001c40701e000340229000400c50110701150356211220014003240300c4070f001d202011281d50314030000e08000354100254075080d21410000e21801d500c05105540014402146403020002c0c8025135400483c1c2020b1545d59107030028541c40c030301c015a00c040390010800e0f15155444d20a5100c4403c001018140710300c0b036030080001e0f90b404148100d110700028800414002401d02c1007004c1c40700030b03200000300c4100d004400ba00081d800d07400842044016400c00405ca00c1c0b020381c0c541192248480480c0e402440300810b0b04500800048420400720f04d03d12a26003460501c504810710056020f40340d859817203070140b20200d039080741c06038940040780e40c0f9130780041e200b40e20162096286040207428181c4940c0c91a0980e40921240c00c400441c040c02d2100b4000c2455460f2203a000441e401c10042402030b860310322100050401d00c1140f15411600350a00010354042e85d000c205900580ea065902d94230400300502c000c1d0b0700b49000031041c82107091141003078421a0380304c940 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 260895116 1250 260893866 260893873
    0xb07020303120a0905150a060e01050123092d0103090519050a0803010909060b030f07031b0b0c0601140d030c020906120d200a020604060c03140301091b030b0102 71
    0x107014500001c4030704050001d9004039600d444440108000740a40e00403219030700280704075820407040348001d881103600074004e0949c850004000036030700b210080d0b4000317514ac60210704c0700c5403074501c45220f4040c9000d010f03042588600c40c0d40360301300e84485500301c005540300940d482564210044045840740c20005055520116100c0342c4414044115008544503c04507128000c3ea80d440300c03400d030001c3e4003580043ea1030f2010001000b6076405240d0409000354000c1042002401d8072541e5110907100190001014140407400000c0030050f040240464942d684e079606030282c011690355800f40f1886004002d0110341800600e002c0760380b40380c52034155907a844119859001c0001355031016180075400402020074080c0c480c41440100800c600a445d1500d408008000400c081050300e01c9840154120301803041c01030344d0380002c1d241a038565280c08441c0c01110b150503105040e1412040d4040600800002446052500282031611140c445201c00347c9002505505507801705000a01581 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 260896366 1250 260895116 260895127
    0xf090801140705070c030519021309050c0d08040e0412180308040509180d110c0a03051213080118020406170d0819090b060a060206070503010b0310030b1608010b07020303 75
    0x81c843c101610707105000c0c14100c10300d01e81d46c3c0d507800e1414071954640144543c242242200750700e094281c11090034018201400184460f41d91980c580a8201c1c403944074500c1012080d00740150441034501034590014411202d00b042d0030843c003940030000190000584a0362000e891020030440c8a0849074418811810142040b00300411204020001000300da1080c20014250804010078003456a00d5100c0e51011041c03800154100307000e41e8421405400c08510030400030380001062020240506003658461040500340c20454882d0390002c81c1350341c00c11068424042c004ce0032010024421030701040502e0361880300240c2803228405110054008142d040d500c02c1c00342c0d90140e80441c3c4640111070882e05400041701b00c0f0004102a40d80030390760020000380741451503186000d011030f030006001c00d1801003002040f52005015811500718048042424200c5000b08540603661151300321003a0b1500b080745500c264410f0301e40c000000c5032480001a02d82482e0100e4100c650054059072600 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 260897616 1250 260896366 260896381
    0x5040c150912080d0f05130219050105030a0209121f05072607020102090d080c0f0604020a0915090e010f15051005070812040b0702120315130f020a0f09080114 70
    0x144c0010040c241250703158204030000040c18801c0074841d222501c0c510180030211f0040c41440e01c1c031b20218100300d901ea001c00307004d581c1e00a019203074010146840980e69002c03030300205070580d400180c50318403841039490ac1010010744d4050b0f07411404055004024984d50b19408035980301c2032002c91010000d010460142c8801044110303640301480c1d00001d403510401402141c600c1840033400d03a40c0e4207000c509046a1b00d414030012101028040040c041c908207900011303207500c0c0a01c01c169085d9600d902d030314050407001d0310702e00042c0900c0f00e00304400c3d50981c0743d10303019003000190320044c0b91400b09180140c0b60190001e41c20341e00b0240c6131005c400c10490080e9460b900070a0140c0701e985c2d0900208028202000645102c0e9210710f10000b0306080001c40a403a005146a039250740c2e8006001304210601c0f40301f4a5180300c1c20441e0944d006c8516100c3c56001003d8505d6102c2000740005040c2011075081022526120304a6032255a65555100c4150032644409020011800300c4004151007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 260898866 1250 260897616 260897633
    0x718060503071d06030a02070c0807031106030a06080a0b040221100f0605040204060e01200607050307050702030708011505010c0b13020109090510061706030604030305090a050105040c150912 84
    0x81ca40c1070f5028103040300f01c81c0000341140c0c000b01c0c2e5032074800d5000500c0008105149512100034403145008120003400c550f10104903540d00180a4001c020100000381d13001d13015040b6000401680341500c01c8024a0304100460798002c4400b80d005080181e201c01d241100d840090b101c00d90701e1405440c03260040c81c01080071b0030019940c2017079142c44090103d20740c0e0b034510090004003015160800154130713200c0050014510403849802d25121a484000099000b0608952146491034056030300c0c2d84013841070b100c0303015600c1d02135094401d041000c200340c00b05500080c04007010200019000b0350b58030044500040c0400001d143d460240040740c032115589280010b81c038814103000c081c040e1542ca04904a4000f25180300c60444ca001042007560341102101c100003400c440c42c030046284c0040441d5880c0b101600081c01c05681d903000410100040c41501440c41d4404000e12a50038242072403500041c041c01402000507040f44404002e6004070649022a0324460b010207200d07402d5182d1100 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 260900116 1250 260898866 260898887
    0x807050a020f1005040b01060f0e1012050f0601081501020703020d1109070e1c0837020102031609050d0305030a0924060b03311a071806050307 63
    0x65102d03510091240d82e006104004030b08094000004040c40c244c1084421118107a20050a002c010b1030000501a0b00c502c1d03c1c0d001c0c040545a802c03e040300a4002c44040c0301203082c030782c105480d042c20300400d210740e0010907015540036030340c010301601d916800801101e038804a903805648a00b800304014206604c5000b01b580c0100e41c6100022071a5012603001001201d101e0b00144e01c00d82d600c4030034504403416031408078620302044640e401c9559000000e2040544081c01c10303031803031a60307440009143e0002c40307210b90025100d601c80794001c0010703010350802d4030b9804203420240c1c00c1c1182d43d44038010207801c03150003d160303491007082624141c2c0c1c4c590000e04089005510b580300c00b0041032070340800c007500c16100c403449460f1030340d4451000d00b11500d681010021107030800c03d0100c55050003055048040122429403021400700c03c806004c45040f800080c407000074020506920072402b440e03035114100a48414005c90094105040003003034902a46004c11820b00100700c816100c3d10400c003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 260901366 1250 260900116 260900137
    0xa051c0c03020d0c150507021e0409060f1401050909030f0c0a0b1e09120d02130e0705070201120504031704020f0915010306060207080712050312010e01051f080705 72
    0x403821a240c0e0041034011100301d10a0b125400710510402c1880d04600003198404d80c14a0f1440c1080400d0340021a14203000b02c000c5480d011328441280e05659540c495142568415002c1021082800000d4081d01d4032159000c0d5a40c500070000a040c105901c01601c10603101c009581342117080c4802d42425000034051210300e100d50341810000440945501c0d000300f016081845c0b84c8030001d50368084281009007100344039007004a81c200300301c40100c00e81e4a15481280007503160300c0b0000c01c8489016143c2c2c0700180c455000400c0c00300d402d80000041c440c0313600030b0f603d681807544c640f0f1305103003984c5003031f100180000c0c107548030601c190003000d04081e00f00b88010210202e494081300002d0341c50b00183e43e00082c100c0e00705015503c0d90303054031508008200364001b07031524902e06900c0a464680f00d01c610441c10401c0300d145000c1140c14002c488000c40e081015880a5071500003411094000b4011030b4003444050503501c00082840f040b61180e1015a500d5814655440724122002c0d003140c506030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 260902616 1250 260901366 260901383
    0x60f141203040e0901020417032113080304120e0a06050304022202030f0106030c1d101106012d2106062102190501020a0f0c0b0a0c0309050a051c 64
    0x1c82c0c05483c01210a004100d00000583c883e42805c51a12010160f402c030030455520410003108a0081c1484412aa4841c0c1c40b42082983e1009291076801c042e045005000c80d05c00400c00c070400100c0c40c0d110400511541d10040501d500200b4402c81c807999008240108000380300203401880c1200c102d40110814840d000f070740c00014074051069030170035503102e2a004440801844810ba1511a6014141891030019007130f040e001c00c0001c00c4003103400c3c0c03640103000b00c0b140e461103107002e80d0580105807420030885030700390382d142096010b403010034501c1e03008280b2018038008010303070702d110340303003d81e29811105400320711008401c42d00e22aa0000880391640c46440004410008401070b0341081524084651a0300b024810840c15030b028031140002414007800605c41d5990025000740e400d944486074010040b01800d0914081c00184c5c0b16803410b100010b0040101580100307140c0760755120351101c80c4070703d0b107900411442019600406410000a51494021581c0d04041c0b100460150301c19 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 260903866 1250 260902616 260902619
    0xa050705070602040b0c210d0908070c1508070815010806030a02030105090c090a0e0c010c051c090611010b0609270c0301080f060910020903010b22060f14120304 71
    0x8400c00ea812580c08081070f0440070803410300ea491b040c4164040401828101020980ca00d089441c1c18007401c00d0b08407c0030fa0700c040309010055490202c941c82c0c0d8001007008079003070740e440317041200c060001400c0001842520104089030701aa00d034900032141c000808d0a403a40c9180115a40c030001850b056062048442110150305c081c40303002d008041d000098004121010240301032454090078044401b45090384000100902184042e0b2040d0246000240c55146050540c0341c40404800d000e0185854603d62650701d40000d004400c83d01c10b0f440300d8082081140c040c1e400c0b11f09400605803c02020843c0d400103141009240070360146800702c050701032260156030485040201c4100d0300105000005001582080044d070380c0c2602444000c0420f40780003100d5584400320802203120058001c64240312a603029042054400f0014249000e503441070188c11440c00d0204016844c003520b4030f003011501c4c6c1142c4685000340e40400d002d00a400c8115410720000c40b410300e250300d132540010b100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 260905116 1250 260903866 260903873
    0x1020a060c030527030a0e061c0c0e040b150c0304080f010608070812040b0708211816231f140403021804050708010f0f110406080a05070507 62
    0xc0308400d0003150b0b4000360a180c5550242015040e040e000240d0745054456803403550340020444400c0c100c0c5181880c800c10304c0e00702140280c05501d00c0c00c9400343d012050745004074019401202d1200650b590007400b134001e0f0042c84111229000d805420078000e01c503c0c2590ba502070018092011001c088074a050b994400160a1108107246d41100c1e075110402040494020042031014000100103001030343d0b180340840032a40316521921460400c0032401106210000c010ba8010203100440240c4665003c404040c02000465070940c03101c003a00020000c583c40010403259100e80c501c2d85070000d5080c10381003640da440310004007d10b01980c445241583c0c0b40d00082000d4100105210b81d501c03602003c0140c003005010454640c0400140010130159403003008030034a224550f174141605444504006040c0450741e00454125820060354100d0b1201c0c690001ca0f000c040c19004002460f02502c55881c0c0d803043e441040c00080c040c0c800314550061a52215810085904001b4030301080c90b038 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 260906366 1250 260905116 260905121
    0x110918030a170a020c15040c09090303200a0e060c010b0301090f140c0d020607060e01020307090801060b2a070806010f060f080402060f2d040f060f0e010e01020a06 72
    0x4800500a0b00b041010004120021070300108640d8055052401c0c00b035025a58081503007608200d0900c400109090280e102c940e039001c2c103001001402080c4480c280600a030520802e0f1141104060000007046c0c0116426250a600c859850080c101c98000030003500b90400300315501c09540c1d51400400d00d5070244030314039000340300e05a0341a0518a40c01c110280f40001071003c4003a40040c51102d0f40c0342d40e51003042000c16411540e0b503031a8000780c24004002c2005810344002c541c800414800c446411041035002c0720018030003400b0f2991518a001c0c514050010100ca0b20f0302848103124110b81002c2003d0b182c1c1600310112442c0580d41ea4001d8034266003a807002400b50b114400500116601854410015205007081540b42c14903038089900c901c55048076000c00080815000d0b00c0701a0300c64400100b000300384280880c00c0300b200f0540100e034403612860320162444203001540300e010720040141c0c207080f42c8900001c840030034015207100d81c00c09541811402900300140000d040c91 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 260907616 1250 260906366 260906377
    0xb0309010e060709060903031b0b010603020405040b0f06030604050c160f06050906090c0108090c0306090f010528110904021201051c0c140109080f01020316090311091803 75
    0x80010a8590079200d00c14100799015003501c040020310941441140e4020081608582d4036240200031011044807880681070a090020000b208617000000d080b03505402038010b44100b2981080b0940342981041030f51809001c03070b603070400c4d000e200050341407829610980e48406c0d1060303594179000c007098210704e003550382c03140c101d983c15000c803a50b405000040c4900d0780e0002901d0010001400c201c0391041d95890440340d8641044003010000b034081c1c000b44004810000040c0807680b007800c085031104e4035410ba08107643d119610303290000e4168480f03240700c6201c1c0030501d540c004411709100301c183c0241c03410300008845110700700041c0030742e62035501c0200006242080e42000c07a505120030451181d041c25103001ca02d0500c0e541a00216800a07514002c9410903011f4012607070109005072561203803075128901c24019404c04503510740b8190000c41c420034526805070308100146c0003d80309000c41d4003000d000300c884800d00c1c4600d810680039094010520345903031103030107080d1001645540e212 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 260908866 1250 260907616 260907631
    0xb180c060c0601091104080c150415050c0f030a051c0b1e10110309010815060304050307050c0a0b120423150114090f0c0904050103141e03090105090a0b03 68
    0x11001001031009601c295078103030320809017035490f0a2406985944e00c10350128114130613800410649100e155040458000302584001d80d910096000da0160042c0c101c28181c40c880e004412003079448010100c110381c043c2441d078480e181481c07141c2d40c002d010b08550001d000005555000d00519a0b52040000f41c00300e0b038940c0d52948590120000c1c464005611084003084c860340904040c030160b4040280c1c0d403681420300c1d00103039558801011003040808a001544c0280c000001d01041c0711000c002030080a02a80490740c1844009003401148100e1f131240d03105080701808484104800c0c12666030700715000d205404e41050165540b140b0038a620440c00c0c030703558042020381100103020b05180d40140300c611002c80744d0108000103d251850700030003103605045950001212800c01400358cc0c0980d0018008011940e180e2404016140c2035950080051094905d0b05051403104842e001450140e070015508101c00d0303030015240e5802c42c240007580580381d00c101207860031031080a107100380e85 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 260910116 1250 260908866 260908873
    0x2040e0129121609030206180a0b120603070e010b03040303050a1b110d090308090d020112051303030e03090109030b070e040f061d040b06010804060f090b0402090105030106030b180c060c 82
    0xa04070f03401034041503a201c54809100003100100096130355142918112290400130380c00d0510585c0000f040000c40d50001408440042055a298a200b07040540301c6c0704141c00b140c14894660b1034841560000b48541c151900c01000024002481380e004075422801e22034002c20695201405902414822452000000e101c40c0074000402c200300320312001c138821420102656801c0d5101c4840b24894440030900908007a2000c90443e4411410000d44043d0050100118100000300c070910070074044007a0002410013442820f440804004c0300c2742884142c440c086094a15030311600c84200c002d003498117001a400640c40d05448a016010405403844800104282400001c0c84009480080e068504032503c0800000525a0800541040307007401d101c80184d48a1800030b001e030000c811203400d141e040140f03c104110503c0d41003409184211004c103060fa882d141410308855051001400d110b50040100c0c442c014801c281c01d12032144c00c42500c0089045001003821940622008200ea50 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 260911366 1250 260910116 260910121
    0xa030c020405010b0a14180d060203010317090d030c050115120c0f0b070308060303130801050402031e0d08150907050c010e011802010e0d14070302030c0402040e012912 74
    0x7405108450142035402c1c510b504002683d5401800144501052090740700c001500c1d8100c0c6440e90700100c00000700410540181c2014904100a900284001c030f8903446603049a01491a109003034039415800a080c0300c12548031b03914103c40d514103000007035a6a540e02e80c11036030101c441100081c00b4103503112080e010102c007850f02410900080d803102180356100001489560301c010304944007560185003146803501e0300f00c0007d055110300100801c00c0d0180060000f0741c2070041d00035900c02d9000f20305441c1c4650001045540c21044140e00701138540241d4405034480c8e010740340498004829000d03803014401c0000201c0c09030740003a0303100e5012410116140220720002d01503043d40a60040082c0000c0386611103100c907880410000034113114491809100fa5210042c07400502504640604607912400160588a890500050f4064020b40100025500303182c02180c00311040300b05242c003540c0c07034802e11496004800c94100f4045214002c1c03154042041400b07080300c2c04180340f02100f0750 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 260912616 1250 260911366 260911369
    0x9031a221b080d0801051c15020c010609060608090a02010801051014030c03090609150121020d0602180103090c06050307051306020c01082503020c030f030103050726060a0b040e0a030c02 82
    0x140d1001f0310030b1700641810044921440042d084840d80074090b44c1e2807140010f0640040c0c0201c03100d007c42c0c4d610b071000000e048001608064112500c5440707071646900d134a00e01640350300003000041d000c40c00c14401006141003d02075031501c01d90b2442d10301c0d400703600c65940c0303c001d80c41510f01036000400401403104c0c0318018410550400d1040c401080540820718001d901c0040504c02c10a41d80101d00e1100c40980f000c66011581c2540108800b10480881c03a140e0b009400100c419090304008080710340d2654020702c03503402000d0300b00040c0104c81746003042c126000e5200400000411400744981024001d1100c1e079a0040d10717039034010300b0031020924001403e00600030841090441c3d11072245003500448109054410803074a40560341d0100d4151243c2703544981d18035880c00b000000000018041c0c0802c008003540c03c00300451204040700000c4410800341200c8580035074000f44089218010103910041443c2d001400c042000303a0000c4285040110ba1101070300845c001c1c1c2a15000c5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 260913866 1250 260912616 260912627
    0x909060209100f020d08070c0503130816080a0f020a030c0f030210030c05070b0705270324010b0a0309080d0507031104060914060c070609031a221b080d 67
    0x101861450201c101074030403503000f540d60039225174610a1148600125a03401e100b10501c81c44142c1200c1201d61700c040000c4485c55481f507601c6249c006015410410b40031030020110308044424050080c490300a0a465000d050264240200c0c1d20145d09140000080d5000c0965001040740041002c5820301d940144901c900400c59442c1c101403818500245d005e4002050320035494110059160690383c8420540f01403183d05900101e072881800c0c092500082c040c84c582940340160144d07404100042000e0f816035102540910740104000c005000d100710500181200030043d00e008500e030440c03a202d095144d44022010b8a134183c42c1c80070080800d4040c014080d02c5680e24041c9468103241260042602c200f5004441d0003010b03541c2c46074201e50b03400c0151210109214141c582d250394403000034041074a03900c011501500b001c1a1102080c85c4040e070940305429150008103510080380303580760001d0105404540c110030f0140c00e50802c49001c003006010705403120007449242d59a40c0090030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 260915116 1250 260913866 260913889
    0x10b040203060d080304030e0415090e0601031a0a0f020a050a170115110f07090905060c0a0f0e0607150606140c0a12230a140309120904060909060209 66
    0x5540100207001c001d03100c80a0110340c45810584c1d16843c0e464500d81100c4442a90880d1984a403c080403403000c004107260f218201d62105408100d802421600381d80c55074030910000d001c2488650000e0103e102d8000300c01c0e4441075540c000214088416051030032608043c8403c0c00184002c0b0744400016080540c0d4001c41800011741c2c000d56240094038641c0b860722440480820601e08141c003089c081c2040074030240841501950199612500004000d248149041d80c4d14844c49000c5292403000004454070341c1e259681d04189900740c601c040da1400300c011416038010300d08110140100f40504125802e6240883c070100f0307071500c0c102c001040f81e4041141000401c01c20080803050a0f80010113403001944040c0740c0200c410480310a032140c00701201c5008100201000c038054241d07140004000c5481d0719201c3d0307920030900c10040c0e0828001106c0c1c416042c0d014407048109a04500c01400f40410010300c0070500300c0e1100c0398101074400314041100c40b282c0100e0183d680e494010001e18 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 260916366 1250 260915116 260915119
    0x80307030507060f090c090c0212030f060a1502030922050a050612070b0304060c0509030609010e19030e09091c0203070c060206060306010e1302040507120501050301050603070911090306040311010b 87
    0x2c05c0d0703041e00c48220550151188a0405035140d160042c20b500a0041862200c504150a81c0303c4c070340b00120315560031040340d485120302ca01040c00703d11141c2c440540030204106030300035400d14207035a00b4001d07010704206540f418000c0710014102111245d01415100d603504034000b24003800d10303205119090412001c48031290300010014041c4800c0d60307080d43d51040d04a60081703000c04d08400c0503103040c41103400464240c0240c008009104005420800003180000200c0312025080703030300000c0484c465803008002030305140605480f0b01e00040600d030003200e10350942d4000700c8485980712513888603005203000b60f0804141c242c2072180401054005107440e00103081da518280700029111041400755140c0c0a419002203002c0300c110607a41c0d4a115070190040103503091442028000c20300c4200c0d141c01c954108400400c0030305040c02403070b009900280c010003c590800c1402c80207402d690940030b8407000140894a8a541d0070414076011764040c0e140c10003200300740752459003560041103805 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 260917616 1250 260916366 260916371
    0x170c0904060e0d1b0b0a0f1104080c013f06090e16060905010804060e0106030303140a091509030e031501051305010501050f07020415030b060f1e19080307030507060f 73
    0x5280005403042104c0c20b91010004803959603e00d003481c01804900108040c0d245046006440320b00d1100017481a20301c1d5204a82c0c5060003040110b8401e002c0742c001c008040340140004003251704900d40000c00004600303244101481e000c44400485840b03501c0700e10510740320f0b210505092001d2090b4070350072078801003290040307041100182504215100c0d039030402415a00007400d01c103c541c0501c0d0901c411a00030b03c40380d82d9030706004011706000d0207000070f02032210300850520b02441c85014025a402409544061900741905000300781011080d42403003140e8030b1200c0544c0e000d101c103508840390b01c03032001d80075410481170010b900c1c030108030001240e142c80018402680c02c24240e40100f6000300480c0e6840c841407000c00c0140002c44d1a42d8440d8650316008010040d1000e5420f126400680724480f21052010030809912846858000303650035003502d403995030400c0700f80810303143ca808201c2518070340e880c0d040030b01d1139103e400b080d0005880400d1034000c10403d400f8507002805c5140d0103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 260918866 1250 260917616 260917637
    0x12010617190b06011b0b010e090d090317130e0f10081203060604080607030603030f1b060b040b09010e150a061e0207050a03030203040f060513170c0904060e0d 70
    0x841c50490380004090b1880e500c100000d06160320403134a4400c0d05581c04048400c0417020b1805200c1d0010a026800501030008005003030028009103403501241c0c99034030141d0f120700e15101c01007a203107100c2141c180383e4000c0103615006c0003050185001044040a450139500d05610800c9060002426a00d83d00c1042c400030024048002201001d244400e0701e03c541c3ca03241c81e000100240300e01e9001e203c1c2e500a400401441c140c06600c4042101e00a4030703560b080141c070f8a4103c03003a51035108000c4030781104c034000304080b503895406407803600e5000e817000440303945500009010120036804185521590402c2004170f2201e80000a44200c0c00d4800b1352085007401c902600806c40300182030b42c03031080d8040d00340f5203d100b002100b0080c0009020000070544a01f0025100e62042c01500000b29003210300042c0f691003441100c450f05404562646100c0c1405041d07510092800054060313403041c1090b448071640c50000d041c1c002c0740300c4c0f44c0005101d0704c00d24140b420f148c403128011043c480307101e40 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 260920116 1250 260918866 260918893
    0x9010b0402070206041404150305060603120f0d181a071103090105070201051c050c0706110903060412020f010204270c050a030e01110a0305190207050d0509060912010617 75
    0x94034140c6d00344085240c040400900407800030218030704081c210301146230001080c400c0106125005010980a031a4040c142c2944651644034090440301041e904015940080d240c0341c0c00009005865103030301c4941d43c001c2c0c660000c007004210288001070003813428842c1c1c540d00605443d1543c1c036880007541c20b0400301400078045002c0e805001c1d051001c0001c0c020440c0700c0d01e80d580c2000f05a0044200080c0c00d29050440c0b141d04000303001c48005180261400c0000c1c001c10580f140f10300000c0080042c3da4840d40c8002d1000d00c242ea1007400e6124003d4040800340081c00074202405400d104460b9aa0b001c031611100701c02d41c2e1600703440a6240c000b00e0307441180d002088910003400341c1408214841d500d4051070061041c0f00c40b0000c0c801d03001c910062280c3c0d05030080c90051280221502030741d080d0440e484201c1c41869401825680041500034905d4003900140c1a1400c0080540d401d140c01c103004075034529003030000603100d655521424090340d8070701c1030f8011028425500030f2114000d90a03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 260921366 1250 260920116 260920129
    0x121b0f0608010b0f0c0d02010f1103040b042907031a062110030519050c10080703091406070306050a060302070c38131703122d09010b04020702 63
    0xe1212403400000d1384c0c0c004c048000c4102ca541040482c00c4804282840800a008002100b160f0907942e0038455030440008480d810b032402940c12003040c0d50f0b10f45881e070b184e650b0b50b00d01d0102d05e07030843d04200c511200c0861100d20b0a100d42c03000e4501160705090400350b04000700d00002c050340b1801041c058040402d0003611217480c40384140360031a1054075031404404000348583c2c4000c000c1d200300183e41296030040341d11004078612610441b05020400c1003040060a041e56546001414450000326902c2c800d03000000703c00c0c000d002680e10900d01102c1141894000c66509011a403680801c20460801c800c9042c000c1c040ea2604500f800304503618500d081500780304100d01b090600102d01010b800c8034040b00c03041802416400d418129040c1400780f0350300050301410280180c40400203032080844104605260b2007005585031084c00c5a0404034100050207101140602c88486545002c015903061301c80d4008000c0d40003245054000d103420b407007e07001e04a028900511000006803600c4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 260922616 1250 260921366 260921369
    0x120b0a271b051e09040804080a030207031505090d05090a0302090108060405060903091309050102040f06180614070b0406060b0a120605030f070b0d090b0a0e060a0902061909121b0f060801 82
    0x216030913a0319442e2401c0c5280303140940d0700000311901580780000101a00010440c00300c0b449244155080c00d00400e82100b1101c084400c0030300e0760003281014118601c0740006259454008000c94001d940301c1e00451401c407000d8101000c00c0e403100c0140024480c04100c1c059101c020034008501c0c0070240b401183c0d0320f00c0004480041940c440b200002004020f40544020305000c1100d10301c0541c0d500401042c540001e401d001410050500105406204800310900c03050440c52540c034141a0f0740d116040200300500540312165074940208107140c489008009844040c5d49200764503003054050803c8541d994090f40c401c0c1d20985580c0022800031861400302c88107100314503202c3c0d01d18038407840a8420118001c06600c0c6200400c203480045901041500d41c5a800b01c034542c2d51020408811610107160180d44020140400c550500c140d282c4810f4042880c60075076410361f5155161170100741e10300021541c1d60380d0f2041c1020150074040d019030085c80142203265100e4a040c00c05011140103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 260923866 1250 260922616 260922619
    0x1401050f06090a1a031602011505330d06080708060711030f040f03031209030c120302090d050303040b060604030f0809010c02030316060501120b0a271b051e 69
    0xc02c420b50103665a68640005008403982e58007082080792820285034800c66a40b40c1600108030440d001910500c0364034059901550b41070100e609200421007405591130000d5482055a00c0c0410010042125002407412a00c000e58680e421015030130141c800b1900f0a00c100c1d0f06c00e5600300b2030742000140c00ba42095590808641c001440d1224500794480d11181e40105d07100042c0024269a00300f0a01c81145e0107981c1e01aa8106442600020389a0300c05010300002c080712980c0002c2a00c00311806001030950070018500107000c00070803400034924000342c03950380020080009105040020b594010343c1101c40900c2e15007550b84062440f05410b00c00752803128045400c54099025107018203109400070101c0340c40e880300b890000307000c00180408855180c03c0c10300000701025410310b48480d003580070003240801c1c5c5d500780d0403030000c2103160300c1007200800c258280401a203003034807100c100798028040e146664281014001114041d94401030087c60a155905944c0407042ca00c0344c20f0110 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 260925116 1250 260923866 260923879
    0x6090a0f36020f12070317041508010b0a0f0203210417030402010c03050904061d040c0503010c0f14070c120b16080601030b0d061e05012408070c060504080307031401050f 75
    0x10142079452034a00d280c2c100600d40d007d00340c02d5080320a00e101c0075100701e94850000e01000703000c0480c01c0322018020f102d4800025002e200c2443c506024001440c0084800e104403424042d4050103070041902c0c1c520310002c171030032210600050045040b800c0714402c818813807451031810181e0009007085071420001d000c004011441800c150380340e0b08500000d20302c003403c0d00481e601040d0740e44d0701c0d103405070360441c0d59600880d800981410180601d040a00c019220b41c400710216410a07a0001d0615601520701e4004012a00000315412002005840c42004203010310003240b40200e01190044e101c0f6114003a2646503640c481e901064440c1d1103c004c0c40d02141010450703001c01c5541c1507051009002c64203012500746402d4035500c0c03d01000e0320b00d14003882070341d0303030754a074007172414001001601d200d00c040e04403800490041240c5500b08082e0701d801242500c403a280c420888000b40e50449070b841001081c04a1aa458010405007a00c0b0707a042402c2d952420000074400d10216085600400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 260926366 1250 260925116 260925139
    0x70501081803191701181104080a080c061e04150e0604060c03110c0307030f0c081801080a0b0a090c110106030b0105090f0f06090a0f36020f 62
    0x2101ca0201e51100c07803801c4a03122a9400f1480b011041011150400901a2203240c08140702c07034034103141201c02442c030070b03540c2602058101010341031040d01e1180b002e4080000051440c01004040310150060064070748500b0741d90000c0e03091600140204889155070b8004007039204004e40c1207908540d0151600741c0b4288180c1800001d4505619101e10034003030b55007000140030841e042450710002c0341e6810005441c08106249050140c0301c42c00589602c14020840002e0064011101c812002e081908101c545a92000d0541d8801e010450241e032030760001c1182560801e081c0c03074001020240c1488403503407101c0441c0d1080a10320804802c145c860342d410580c40e01449101c0410b504107030086c0080c40d00c80c10103003013105003031048034001c900d00d00c0051035440c444104030713010350310088410901d45c079008200324500c007002c2d0a411507a642c40303185030810700c03c0748502000510446800c00b00c0b051032040840060180307215048504d0b44100c5ca690042c1d46040015907a00b0b012203107441c001d0b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 260927616 1250 260926366 260926381
    0xc05100f09180e06041b0b0f12060f0a080109110603130609112d041b03200a020c031c0f080a020922180c06120f0606050d0b0603010807050108 63
    0x1440090b5101946004030011711040c401c1d000801440000e00b03100d010601903950300701d02c000b441a001e14100f5071000b4421035070030b07c2c0040c80998011000800c00c0c00b074a41d202c07000640400d49503104241607955103a41e03800304241452503c01881c41200c0d0581540750004038447c50b0b0209900007000d0b1a90b51121904015228902c02c500e41400b900c480040300c0d010001382801820004110454007506155a8141ca0180a2206070241b03080d00000480184c13a0143d01418207518a4103100a0a035002e03000700e42540301501042c801640248509645001418100305a03518041040c1c0c00440001c8182c5030480a0756015501d2071406030440e03503400c4184402070184041095104500151154035003200e00d01440b0501400101040502d015903140600590ac2c0500244070180300e100400413280100000070005040c024049401c080c4103041c681160056006600850380100307180021000d54490480c4505081d20480d1855042050999550602e031181c503040100c64000600038 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 260928866 1250 260927616 260927621
    0x40b090f010501090b0f0405010b09060c010f0911010807020a05030a1805040c050306031b0312090f041d0c0a0308222c06030d0c02120c09040c05100f0918 68
    0x200320a2400030022561111542c4010307040d030001c6103100305111110195545814824281241c4015841500d442101d40034030a4503006042c040000e9540e8080ca000041a10b0055800a0384115454040e03242c4800003d014050b0143c118811580030168400014100100302c40054019040040d01141619100701605115802c0103410508044148442a4018020b5802076100f101920f03d02400d070905d000240101140140e4154800b90010000c0308250300140790000028003000700b25010140460290303450760481e240c01c1742c80005191a6030000f8401d110b503401080310001d807098950344443c6418000d1303541203118078591680f0602d040d0102e1042d04001c01c0040700b030f10160000216a0026003401d0304a80700d01e524000c0008586150118644130301c00115210340c001c2540540070300010304685814a1114030402d2031110080da2420a114480d80c4074018188400d4140414040c204085c443c0c103100740700c60101003954160b0000552000e5400742000c6004240c05454030102 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 260930116 1250 260928866 260928883
    0x1090327081f0b090702030403030305060d02060c070f05060c030315010c140705010906090506161b141f0206040f030201020708180a08280812010b0d1b08040b09 71
    0x107191260140e411140d00c48820403400400b0081820003401003100107000c0301c00d400f1500e48005070030810050002074001d611240e0440e5001c1c0012204a04913030105240ba803040b11101310030b07440580e041003118141c01c0c40760050300c030584046042000010440e5504c2c00082c1c03c401850541068000c2c80d81d2088005410464120407103a030400038000743d846e02c0d91050f0040900294007884040340780c81c01105460115040941404d2400018507065400c800d100c0303c08031241b0041031044040107203591821313000b03006180e9611a01099140400c80f4181601c0d10b21400c981e40c40305200700154001c644180d200d60800125130030140c5500d0100d00900c50004001d04c00700300801e2030340c42d40c0184206a01450700c03c0d43c0407a0b1560311002802c0d0342d204508200c054002e6030507882d61038031f14024410607400e4800c1a06d503007480c2c040c1c0040216100d00360846842036001261034059144e49000b4014905450b0781280030b0000f4070a4014007000380100040c04003807103200407440c140020080401e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 260931366 1250 260930116 260930129
    0x6020705030307050d1104151b080408010b01020615030307080c0a0206210a09050c040902060706060b0304150504080a050304080903010c050d140610030b0102071d1801090327 77
    0x950383d1812000c00b8015802c1400c1900761146401c05200724440304c00d00315420303100c60140c2e1002102038140d04940c0408140494050701d5000c50000000400d8040900f02806818001060341001c0c14002403800d88004d14199000e01c50a01c0d500281c1c401104032264140c00004541e50b4000d0030440928180054000a4024100081c040031441c400780000b81d2076150092892944d032550900d010030364440c8100074002e60042e15400040349442c0c0e00c8078842c41e2000d02041d0a01c0c1e8075407180405c41b141c0b80d00c41004098000200000c000310280200d4a9023100380b030401080c202603c17012601e008071a2008140a400030120b02845041420b079211040010000d120602807140018050340200c20401d80b0141007030304980000301c3d03240d5524403c0d0000f5081c01c607222241d85044000d0b000d035851850550203007181c041080c042601a40048213890303200c0040b03130309022480d240c2c0817810000050ba80d0745041860b00000360721600c8110b50040d40200060340c131003071004060f50000660b0050 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 260932616 1250 260931366 260931373
    0x61103130b0c072103031409070527040510050c0a09090b30010b04020a080c090d14030306190b03040611040906090b120a0201080a020c031303050102090a0602010c0504090906020705 80
    0x210450780900041c54130718071035035050068004540c0740441e003100c05d883c101c0c001d8115880600a0303081003280c1c039201051241aa48441010303003001c42030442d054400355030359000340304200d0078170318940180c076001808400c2883c54041c07803240c010100c041d1402624089903c618540da00c55540c84469042200354201c03860301c0600307408481d540c005001d02c0000d031039401c1200300a868540791003502c0240900e512444043d0340c81c51107041c23566010380c000d9540181c0d4403155501142014040c00c001c0341252006681e21300b03044041120b9800040c0c41d080380005540c40900c1400000001c0c6d80d0010b03400400401c04508101d120610390141d0b400204001d443d104c00011a090f41da009210300c01070503140b030a0122035803001c0588900340340001a011404600210b03000c4c0119038000c2c000700035002d00340c070b043c10404048a801004150b0040d01c042c3e401007402c100a14010400900070903650000304444980880080c107140102e1040940c03155540b818170f014000c40c1e40458100c10ba06c1401e8 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 260933866 1250 260932616 260932649
    0x203060103110f19050c030403060e1e0a050c0a061215080303102303070312030f110c06070f08071206080a061e02070f0b04030215010609061103130b0c07 68
    0x11061207803c40f0b02c10114031031070544c840d0304150048040b90b058502c2071010714541411600c070b0401912090721015801e21404200c0c4840c1155007403c00c6403180c1c420b01034400c41d207107410400c6c50001d810031518420000c100041095a42102a0041e024600c11001c1490604120380c203411909a5102c062140000010400d281c4c24001c0603030300b83d030f00e000180c080106500359008110ba00e51300c0c51603011342c800d400620100702c0f0390300c044110a0716071401103101c001070a020350650303003810004441440081000300f1500300c1402040c2d4042c1652408132500c0c4c09081004140000280289090014100c1345403545403840e0401c0005c0d115400880c2c0d140d00c00b6140110080c0300071280d0740e90740e2005115082d8440c099000301d0b0704d45c07038200c0440200e1502d903445d0980b8000000d4800c17010351082c044440d060b41c0c42e290a1a0007040c6540f0360b90f2400b071508c0d501414800880c030000780c06810070810080001c1800040800f510400034038541c6500440c00c05030316200890300144980c0c0d900005 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 260935116 1250 260933866 260933887
    0xf05010e070603090203030313141204050f010c02090606090307091103060102010608070303050304022106040308060405091609050a18060e0d03020708030f090c210601080f0d03020306010311 84
    0x250808050a008440d00203aa45800f20f0884680410007035040e001003000c102501d0040d464101c2540c0140c5651583c01c1c0b00c03070303000e0349443c061a4454008110205040010b0710f00901494550942130a2505421100394000380360768900802c07042c0303e5500814490036a403010001c0401600002001b04024000c2040c0e203911600201c0b000c074010741c2000300114081c000481c0c0382c1d04603035058030b03194256121582004403803210300051002ca0020051010f04c814010040c00380154040e032103141442c1052014003042c1e4000404906a81d031111940441800070101c0a0084410540000030283c5900c02c42c13074060300f412000103005101c2d01814400f8044154011000c0184001c2120b100300c180074401d60690040d103001400010302400065000301003030140d2a488903602c4c0a8a20b245007510000f40c9070035a01c0c0100035090000f0b050402c900c9070400c45a400b4000e81402030001d000c9880c006a5140030180b0818100360300400410301d564003d8001c01182ca01885c0a1900c4408041 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 260936366 1250 260935116 260935121
    0x162103051609080709050a0b0405010b0d06230d0203030c011d0609060105090a1a0a120c0807120305220303030e010b0a050105090d0f0b010e0403081524070f0501 71
    0x2104610000d141107402003810740203001c1481110072003005031605901c0d1409101c0205402041015582e8640541a204d9541c42c8211800b8104c0b0307108190321600c07520348a0045640d141c110302910070f241e00b11050f1940c540078589180b50f0084501c00d040107000c0c070229046028519010040390309100141d030101c3c0d455001c03014101d54100c11122565620242c081d9600020311981c0d82089040340416405400e58104000344140e03501055036110b2101e01003000d44004c0d6001e24500201c0e40241e408000200768050014100a0000c0c0101402e00703402d48144d0840044c02001c2c8880040c0d16440902030351030070400c40c03507250059110f50340d5038280a0064020f4250030200c0303501c1e0800e950654a031440e4483c05454040c0d548a040c440d0340024410840109203050b2400036001070581c002662800c0030351f0181c106044500f420b401e080c0f03005080c0100c00f81004900c800000b0400410380c1b1741601035118031054019610955100301c20441d250b01c910403001d00b007010700c01e2945041c0075054 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 260937616 1250 260936366 260936371
    0x6070507020102160501080402011412010b030a0b010305090309040b120709020d0b01020615010315050913020a1a160c030f0317011a0d0c020102090a06020d120b0616210305 76
    0xc1e000c4c3c5a1000ca64403843c20680c10b54000c82d4042081b880108015500c02d2601c104480c2d0340c2e1008518029a1440c0c001c00c914099200c102d07141000405c10809004038065164812004c0c202801103082162049880e0700425050601842e681c0140d00e1003030340d1300e02c194582c54050324295941c0d030b80c644080030041c3d0301100300040748608043c441c003510f52000480f0751051102441035891085050300440280150081ca0154034403108408101c81e5190300905004105580e0080c0e1808010310601594002c10341c04030404000003614080384140240442e05403d801c0004145001010725044120b4010740d0400340807030010f01030102c10103410030140351001e141842504210382e62500340c8079550141e01503110100b9000e20440403c800180c00500000c52203000142c00c055896000c941074001580c8400b0040e4000c141d8118080e802130b40640021000000130f0042140010124900d03101e000015542e40e6020040c020500c0200340107808400c1c001c1014200200d4880360040151009 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 260938866 1250 260937616 260937619
    0x20040801050619030515060102071d04440d0c0e1302090d020120061e0903090f01210203011706160912031b0b0117010605030606210607050702 63
    0x80b4441d0307a00d4143d420072000100c075480130080a03040c03071032040c0c0d501d44403000d0007845c198460443c000c01c114a10003c0c040944d0310144d0140100d14103410241d050042c0c038901100444501d54043c2e000041d403045c41440c1002c00402c0c4046c1e000000c140d640036116070604141c07030929107110499096030040f50302c082a80c0442e0746044444800300c207101203108054102d0f9100b61690000c0f00154060b204100000380b840300c00c0d05881d26001c02007401e068003100c03d91080000007402c140040a4100d2840d0000983d800941c01c09441502150982241000c0903052200c5e460000c1980c6040e68031412078014604019510f95a40700000c21034118640c5081c00e080c0a00310008030240402c2002c034950910980d03584e0b2140c0d2038080747c2c0040d2480e259055081068001d51f13032030075610704541c1415440c4600000c4070950326107040000c150756003191920450341021410401e580d000200160000801c441c8401051201e0205548107070400003449204d00620f000c00c4801c2c0c1e00320000d400036a00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 260940116 1250 260938866 260938879
    0x9134110080c0102010c0207061103070f0f12080c070b04150903050a0e180f0606070506070f1e0c060e0307050a0605070f111002030c091207080d0c08040504200408010506 75
    0x1c2c501c0160300b600ca4000e001001a0710030036081049500c0b518984400351222001c0e40e203020429158500c641864043c2070b20b010b2100d6100004018021521083c0d0f4200e0340303481d19980c00d0541029030280b0501002130319012007000802d040c0001000084100b02200108100a50052400ed0055004001d8200100e00d52181560031418100c2c030450042e4440403058131560b8503400740400921001d402e958220350700b0b1040302c000138020440c40c0d01030b0419850f9400d0300144004018803c0c0403504c803515500350403400c2c208030150419044030800e0761041020940c940301c108814a035010b201c0c0c001c2c04510540c21240b06210048d8407407800f59105507a00f02e10070b400c161084d900300c009030a000000741e0044d6076003442c890403503000e5a044400305191300e16100612000a10745110340f08412000d82142404001e2040200641a01c004041c1081d040086203900d40f9203240c0218881c40740580d4985480015140001c55100071b407106a0000c0340d1a5600e4090381c500a0004403038941c0141e0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 260941366 1250 260940116 260940133
    0xf1305040b06030f0c220b061305030601090e06060409060e0703060501090605060f0a0c080d02040b1c0507020712020f060705030c0c010e09010b070c050301110913411008 75
    0x140204207003190b14409440001a40540705c465654403e0308100d51102644e03542c54010f0039a556001070640c09d04080d10b03c0b650b00c2c00c16040500b02081a40038041443c541b40501d82c1c03a007800304480d50f21070001c0302c0010310300b200f504091f00500702c84580d40341c4a002e220008810070100303512007810b80305003110421060340c0740c40901c42203110701c0800000c080024450411218800c600340c0e5100b91207402c402b4180140910000280e0300281c21100798801c002ca040d001015607c2d6851131000038540003032289060200019440c0d50300d41c0507034809a85000307484801e5482e0071400711074044010b0852551034100703090540e280d402000c4032103204d00548402494640c403c000342d0748042001000d201144e46000240040c60348420011580603c1c034010000d19a5802e10407000d505095058250b039400c024000c1115210381d03412000525450580491400c80d1040c207440781e28442540001c1000390300d02e2030a488103c44692004010340420200410140301e8800d0900300c03a40c907800c840800 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 260942616 1250 260941366 260941393
    0x3180b091516090b0f040b0a050c0606040c140f1204050601030201021c020d050a1e020609010c111506011407060c09080d0e190b070503031f0b07020f1305040b0603 72
    0x10303031002c070001c00094246806220704d503c040014110f905003040010324240d40c420b0a10025045580280d01045021406100a11080c81840e0707002c0d030122030400c0f2040030550068011520f10f01440540580070503032101c081c000303d0031910241c0e010501941c1505e041e2505079914070003400124014014800d224491482002600c0c00c4400f080d00035007011012184121981d4000f54840c0080140c04007401000300205c1108400e200c1255002e04014506100e4640c250f6810448840030090302c001191031100001c500541000504808024251100e400403903505030200d000b081c101000046420800145a01204210310f00384c881d542041d544038000b6488948401c01a404211100f16000040c03810030301044034042e182c1440fa5a00c0e0300c03261540599000b02008952a51000040c01141d0000b144481641711501d0800100c40c2d01703003800e40c01b003805250002070103484201c41c0b0603130b1661004500010b400b8030714800c00c010324160400c041024010b0350354034001d025089440056 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 260943866 1250 260942616 260942641
    0x4090609021b031c0f092102060c0c03040302040906200403030e010c0f02010c0302030c0d120501050d0c06030f18111201060f0605030c0c07060f2d03180b0915 70
    0xe41040200611320304103030079078001a10460032a000c1c107503942d102d041c4c000b0314030080443c0c1185401e50040903001080d40701928094000d444164040b10030311041008c2c00000084400340da030b050ba070201c0d8410302031070150054000c010040c0401c601c00000e400d014034110b8090701c1140d0180e500d54440300c6100005507120320303810001401e2660003160200255000e0f0000922091080c411203103000b42ca120b08030708000c46c0030785020000700341ca5840300280b01c10707018144c05020202c0d203001c03228372180c0d9182c891980360303c01d1209064031144024010069603006c0c1c501c480e843c15095410641910f0b2500c184012032030b0f540d1080940c06c2100c0c0340710105101d9503080d41c0240780c01081860070000140d07081c0d04014828455a41c04008401d203900c0280300c02d800804198450f4130300c0d021052000b4244a002c080640d00032200f450400610003451308800c1e40c482d285090008003403003060300203510b07850b03049009843d003494a010b0008000000500346081c0085181062140c0c0301ca000c074501 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 260945116 1250 260943866 260943877
    0x270f15020c0f1b1e0a05060d0b030f0c101407020d08030603011815090501020c1b01140c03030a0b060909010602031c0e1b060c061608010b0c120f04090609021b03 71
    0x810101004c00350700380e00303421802541160001010850305a68480004015501945080716031070b071a202d000c405420100304404080b405040038102d082c0d1118042116041361000e20703410001c04503610741d00c1c0c82448084a581c1c0d0b401500346a0342510604001400c1da100781c0da030a02139868100081a03010036800340400c02c4c2e9000d10071044e0f4162849002c17000d0701141b2400c2d6501c0d54200801b042c044403c10130b01d0800783d90001c09800f03044c1010000341808901c0e1141801031201000010041d60001c000c0b66440440e080300080d0141c0c0c0040412450b01034403600340c0e0001e51280c000f04034590000041e0040301700502d00a454900e00391100c2c0b0541c0d011020044440e4400d800c2d1850189030a80c003a000c2043c0541002e05021030314414074030344001518107038260307442c06204101241d807040000b0301600e50302c10070600d803608603d50b03282c0e00d500c005000f5800c01c0d008200ca030a00c2d05400b007201d0050280074000d00440d500d60031040c8c0203510200304034031540401071120650b148040251007 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 260946366 1250 260945116 260945119
    0x3030201051021030305100504060e0108010e120a080c09090403090e01060c0804090b12150610090501020d0f1101020a02010e010f060815100f0810270f15020c0f1b 72
    0x2542041d541c160064000a1f099030f41c5610b4006000c01e860701d0f20320078003008280b040900440365240180e1a030850f800310b080b030700c81500030101c0465010f40c15000c4030590260740c9000c140c01c0c0c7d207903407a054060203415400303039011541e2004e0006155100741c404044e80c41032802c0000da66a00d840130343d0503ca0804009190100070b000c01c00c4440d040742c0c080f8030203001c00b41c90048840c05800d250b605100b2264035400c200c10820041c04080e0514410641c044c0703a81d410708181c0c1c52705060020303680310503a0755943c082144101c04c0e05241c6200e8400e401090104200230347d00d0300034200020340070b4140480800345943c40c1c40003490051185e4002c000460f48044040e20044407402c6040700740c507070300400c40c0d600c051341040000bc0034000103001070001c1880c08080c11143c5010110102682c1c0300780200800007004078ed00343d00316510011505591503000d40c0c481d80000c071034a4007400c04c082c3c0c003402c86042c41c0f020900845030800810445440e04c6500d056440c81726410350003136500e000801815 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 260947616 1250 260946366 260946419
    0x2130b0a051c2003010204030c06020c0405130f020f0604120201080f0721060b0a05040501030b0f0a09020702041b0203040501020706021c0e0310050a0e0114010b0f031f030302010510 80
    0x18041000d501101000c0703803c1e0906800d4461003540441d099a006900c00c807104201c0c003001304041507050041c0400e10314212010700490a2040728150703808444680030b804600300480910842d0344101180204410150040341c46135594461041c8600ea2418140c0c04600203100081c031350003040e0f20183c4240da6035220088a0b41b50103070031200b039021403280321070003994400d00450100c1e2110050084140290703203041d519030604000505640000c02c88034094100c540c1d0000c010340da141011000c1d2500c042c401a22800f1500020b4060804001c6c00240d034450403450014066001c002402900c600703808803426183d4501041f43e80342c10888401600072040c09803001803e00c20801007031403900090480300e2010611410400f151019100455442ea03105140d5440200031f000304100d00f000505000410b41c0b401e2445041445402c04d0200d62050000c0041d1494000c6401ca10541002c070700e460040039240e1402134020242078411105d5010501c000045445000c4032001c000f61040898 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 260948866 1250 260947616 260947669
    0x1f0308030727061b050307050313210213061212020c090f010510030207140609011a030309060304081b1525110c03010c0302070c06090608130f02130b0a05 68
    0xc69840610802d0134042d0850b000b00940860400c00242c403005001d04065a502e14001d003404810080540c007206244940340e407050550090b006410300320540564050120031006030103000205065086141405a00590b080c14090a41e10095030745c141c80e000c540700f0304007440410401e4801150200d178882502e030014015810202159074504500c0d040160801d06242c9ea0905032110030300811401364052070800010000034020140c440038400074002c80500c02c080420340b64800c0d540614042c24000000c60704020520040352030a587c501e44060a405089800c26261112404030692080b015404180c08034881d80d94008107075103042c82c2d0701001c001424103071410600404081401e008514902c0225242801005000700f0340303580040c0c5d202e0f55490300d540c9010190b00701004025040d80d0034400035400640c40381d041180d049100b407103203100f45402d49148105090080d0002e032015500060407909400c6079045a03021212122003a440f00144807448500394041940d00008207403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 260950116 1250 260948866 260948879
    0x8010f021213110a030303050405060106050a0e041d060c0304110901120f02030a0b09030a02100b0a031704150804050c010c0b220c031a01060507030c0602031f0308030727 75
    0x205221410f2088141c2044001d4240000f0108285a4001c0c3c000c252074038200010490107100c0c450261005060242c00c000d0126001412481509026030003107a6405007445006c50041d03248140a028800701c1d5103e207403040c24100d0f950416602151116441030b611607091400140c0d04e4103076800c00d048000c40c007426445800d035100d0504d0040ea0903001d50021140800c003c540760078882c8031110015aa42c1c450903070002d16194000f136082c00a640b4100704074442e07507a840001411280c11070300ea2415525007544160b010b1060785c0c41810000e05c0b90b450035180c107030480c14443c4601d00078415111103000400065801c40401c01c4000d000480c1d90740001d4540d807440c190f1011323022480000c0d16000c0c47c0f80d034811851750b14035041034400801c10078540d032a03e400540c0075405010780b45081400e2034001d550240c43d403031070100024002c03500803002034209200b030005c03a02410304070513110050640d64100f0380900da005440480c00120744009404020701040c00d0000603050303464200b1107880ca0401c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 260951366 1250 260950116 260950141
    0x703180303050402010c020d062007050705010f022a0f030102030f011a04170f0106080f0a031409191a0a0e06070201030e0f101823101508010f0212 65
    0x60040b8140240707046d0303080c05230700c52103102a0f044e40700f51400604050307e040084041400d0020f940604d90082254000207140810349000b110000c1c2400c00c582100718403740c0c00c1180801540194441280c200105160f40500800d00107900342c80d082880c058020a01d401e0303100c2120040d0642c4209001088550b80740c110b000d14507906800030074207041e20341802d0f90000140d14240c05a0b5445290b40d078491443c02c0c841c001c003c2240c0340003080d642c410700d00e80e941c6034114440082d0505c40b010074201c14a8405030100c03000194010011000c0300800020192088028054010608081403003110306c145500100c824401840e110043c078010f907071040100c158440c5108074101604d4030325940c065901000544a150410400341c0b000d20381400c48402295040c0d900e440c14182190300650108943d040903094000c580e40400e403400ba01d02000f28a024544180d0704c8500c1d03e0031072500248812042064141c45c003000080c0701030011071b107040d0140d0041c664200f40c10388400c800704008c0001032 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 260952616 1250 260951366 260951371
    0x106050307140c0d03020306090c07051203060d0606060c0302060109050105030703020f0607061503060c090302150310170d08010e15060706060b030103060903120507020303011a04090221070318030305 88
    0x40b0364403868480e16104160400c0e08401001d80070039008801d000341807900c0300081e40d22601401020b811700505803985540c5100301481090240c7c030001c0414515210700500501039900600d060092035139a80c3e0007054030b80325450950049c0260b00010640d190b1034007845049480c000d0060652030306540800c0001910408490b5000b40208007860014926000f004040b20013400382480217807850511000751960b00390560304019150751309100507500d10444031a1540c40d41c5000c0e403250b80d00181c900e03100240340c018591801203000c0740c603800080003c61404240c1030395514407580e40d0b54a01518801c2e0142c9008003812001c25500b00c0170304000d0040d013042c502580e030125005c0d90300d0300c200c1e159500c2a0802e51300291140d101d1414560084002c00ca0074076407010800c035901c7c0108000b902c1f4001805800e503100302d04280c18040b00a41c00c15100079041c06541150754401510001e14a02c18a41c3c100c1207900c5500d0005000c24002e100e584100c5a10310030307401c800d14030340e07a0403030060000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 260953866 1250 260952616 260952647
    0xc010f230c0d0c03140a050a11011e0b18040803040602133803103c0503070b0403031719090b010e0a060b0d0203040326040c0e0106050307 61
    0x1d01c1100304081042108245840071070300c516501d0f070fa560030000e082211042060b04404810003010103526446001c4400c05031891a01c448440007104809000d0302e40000a10002d050505414080d05540d50014515030001c0b0340c01801d100f0924080d00c0d2501044a0151651703009100160125115070002c26026040d40004c2c820f1640300c803815041380082e2200709078900201d0500054401102c3c43d0201107201904059081d4940404c800c0c0500c24540075208409030500e03480c40d1000701620081c01a005105000841140c41d1001e00880c81040d120701e900c248105a80042d00000171000c070707001d480c1c00d0b90700d0311681250440720840402c000380c82d9684d501c5605080e0341c480d00152080344801e51140030361004a515000381921281005030900810901d0040200310700440d0340211002c44020280160b129920ba04042c0d490481c503000d00d000c2c1d82d44600d01d02034003200e50380804c1d00c40d9110f91142c1070200d40f43e031561080304009006100c04510108041180d49020f07020a02c0000507 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 260955116 1250 260953866 260953937
    0x3090d0807021203031b030105060a0f02010e15060f180406022505011d16030b0901091416120f02041a030115080c030102090105040b03070905040507110c010f 70
    0x51542c0411183c814007620600d19820105c1880012035001403c80c880d44034002582d4299410803000511078890300d040d0f4018004041a8100c075075000390055041040c104042c3d589104800340c05000d41d8004503211352050652140c0c50481d0300e0100c111410b0021081e01c50091642e441c0d883c00e000b175100d24520b240c500c44850580325001100c11014004c3d5100d84004115000c030701c210070808da100d020071188240c001d0110604084151104034003103e40001d40d5185a0b1110300c0e400d4010261640003815071000c2c0f040146142c0c500142c01c901c070310540b1449060007580d0b156036840a0f10146401003d005051268101528058229000c000380c110300903915807000360002030031a40c2c212000d88881055580c10499030009101041004505500a528004010300001c00303a10072402540601c51005c00407074012031286002201a00f80a80300300a90705001001515507003040600005504c41c00020844079440b40d503c1100c03402041d00e80106101c1e40081c0741d21520031188000050b44c2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 260956366 1250 260955116 260955127
    0x10e0d0b010e0c16080705060a05090d0c030e0a0b22030c050d061d010c090e010b03040b0709080a030905151804020319090c06260a0908070b15040b040e03090d08 71
    0x18144125140103500c600316443d13544106c1c1c5019070822000802031070010749030004129070340c40c0c045141e1031122402d180010181c0071a2505071050b95013412003a821084c9003001089603c1301070000c24140200704035542c0134020b0810316400c80501c50200910004410900300120b04002e5000042c6c184540e00c0424600700b00711a240540e07000007040c00c0e07641c0d1116009a20541c000740c000d0f014148801440c0c0d0030b50f0400758480a98440a8030082042c45c050340000c984034422000301c000390902d042034031b14895103402c00401000704d90113010b1250548007000c8229940d1041121082411800030480300c1c802041004001c0d0001000d81c411070346803940401c248129441500f404510854403110034a003010001030103d030901c0401104d540c00342440116001104d40201e500204245000c80c07040418680001075005050005004034080c0d414030110410403c55000c1c168000c2e50100000c8400030104003e03561403c0344180c29403c100003484c02070920b01401d0303000d140205002c51611 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 260957616 1250 260956366 260956387
    0xf0e06070605060901060504050904022e020f100605010c020d0302070902070c1809052107020a0b090108060103110f130b03010605040608060d020a05060904060b0301060509010e0d0b010e0c 83
    0x1a805610304646480d0740d0310420490780303040c9944134050100d5140c0141464200008950380300070240001e03100b800011808070300003914000e0444203645071003c0c50483c900141c8003071354490121225541600440320102220480b03449504101d403416919000703162060b03028010000841f81c01541140039081021410302a80d000814403a849102456019890311000b61860714000115440c403508140b88030000c035800051812401900344c90700e910039225840742240700d104024009402011100c3c00082528801d000351038120820380750315020750ba980b0300440484261800584a030042400119219082c03400079004e11030140d030345001000d80700d9071000d1958200344d010302c0c001500005c05000140e40506040c1d082601a80c4200d000d410700d030b00165841c5298001c09000313002c080340016440c0e9a9030041c030001c00c7c1504941e40d49503150803000700303079901044031580070400400900106041c00000c90701d01d6600480840c000e0303420892025250303100035229403544941840002c440d0b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 260958866 1250 260957616 260957629
    0x203010803040603150321170a050103050607090b0301150201020702121c03050105030304030204020a03022214030f0d0e0622090509060f0a0c030e060f0105030715020a030f0e 77
    0x40c2025900075a01c1c0c901d45000103007a1528200e44da090030044020800000c1c908820401d00d6000004a4004a4111040c2211080310b03020002c4140c1c4501c1c018041c41d83c07426400309051368028403c0e60615940d442085e9041d41b41031052080c903040030070041108603a01c0540350fa0550692002501e0483c5070740018442d01c1344900050010780145081082c0202140ca2114202c99142000d110662404d00042d450380280c0c440a8000d42d00000c07004a418440d6040b04c285010441d80d004290001c9280300f242d1031600c0c040c00810106c040344043d0b40c0d140014080b200e6075443c100410310010301410843c5c944d0f000e0009150010004e0008506864090114162040141c01000c0c0030074135114401003682d1010742500e0081d0090300c01d100b551442600300315480403462001144500440e9001ca009200c0b2a1441c2101d0003600d05209007445d42c1251241240c4d41201142c24039a1a0a1800300760140c4050031405a40300c1c07a04000083d0282000c4040c200c0d041c18506210010003021901 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 260960116 1250 260958866 260958869
    0x7030e030706050106020c011103190306230f0117010909080f07060213060f0c020f1302040308090310020c1903052515050c041a0405030703050303090105070e0d0204020a12020301 79
    0x248580c0f20f500620006504010b2100c00401c00d10b454203105040c1003203607450b0320500022403403000c00010701500302e60080d00040c0c01002400d203030201811040b1403424040a0f07003074989125480705101c82d01c0d590310540c442003070b07440403106d000403592800707996400038000218101e59030030061105198004100010f040c145010315070240c3e96000c249132107180000da913041a4140080f00b5034080804c2c0e070010380c0e000265810303103800400307210040004801c000505011300076280001000310800004102600381e002040c0c04854000d810004d001c070903400f80794600e03411940900444440c000b03466410300410ba0207030400c03074a404540d004802e05015070444c11001c02911401080070004a00c40d814003413426003d007040103040480100980344960310404240385041b48025501c21800000c0b240103000c0101120700c0d2594a02c0c03c59203d409c12564880c55510342070020303895034014246007804c04001480d000c58029940d0800c00290840c4110000f00846000345001c0665584010b50 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 260961366 1250 260960116 260960123
    0xe100305030313060b030a03050f0d060f08071a03061807120204091d011e020a1b030903020909060405121b01110c100e0309010e150d0203040b160807050307030e0307 73
    0x1d02d03c0301c03e402c0c8582610040100c50b8083e074000000100420b45c090207031140420000711065448080140c00b001800c040d400941c2c46c0c08241100140c9403400280202c2201c005110a400d2042c484820034054003040342c5c001d802250030720b10741d280140100d402e65400281400c1600301164a00f981200303c0c2c0041e00450072155403901200d00719144102003100c44510cc200034000f50b540d001421042d1032000314041c007041c3c1c0119404500c00d00070342e1202e0561400612000401c0071900f0002c0c10038803c1d00c0141e0242c0644000320700c032140c01007142d9100c5c2d038104d4000e00420044c0e200d00c5109030301c00c401c1104e0701000104418800c0301c01b801071105040c9150420b58640ca06500c440381061404850001c0803071410b2070581c1082e0012082ea2406003090900900c4840380704040703840c1c3c0b062444000391030080044d258411a60360380c003070340c060750040c1d400c1d0303440740d40713210302d007503080200600c1007010400310000036104500c110f00459200040d490003280d01403039495084c1c40e640048000706c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 260962616 1250 260961366 260961391
    0x6050103050c0109080f0a021504090e01052205070b09180a0c0e0315160215101d010e040b04050f010e1c03180609030215041406060108060a0e1003050303 68
    0x12080c81d0b0b804070829010b040c20b40c02500100c941500341d155100e017007d90081c011264011590744082501c1e003510018070320364105224103e0212000790003400101c400f02e00082c95002140c0f800099400209006c56001e0000d011517401e0218030003081e00310340e2038250b20500c0c0c060094051000f80e56000d01807400e820001c0741400c2c003a0b1025101f00c402080f440d00a42c0a40c0313014894410201280790452085840950603501c0018102e003410320380702000100400366014440103001c000c5040c0c04403654028620031a0501e4005400481000c0c480c0180ca41950710108000c16000d0000310b812610030001c80340e0202603030038082c0c2175803191308a5500d5900004404404607814003081020a40e551038100080ca03c90303441040b00c481c0599003e13211583d50102981054002c01102c03000010ba001516a107107003618003c0e4080b0006c5500040300c1c09883e022640b19402440341e2030041c040103007200c280c0b6040c002090820390004045800c0ac0040c50400404140280010b50107200906104d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 260963866 1250 260962616 260962633
    0xc010801180902151e1303030305060607080c060f0a0606090b0c070503011e0b100f0f0c0501090b010915050913031701120506090303010506030c0730090608060609040e0304030605010305 82
    0xc5c83c0390b04072060b418803102010401000060f00070161881501c2c2e00d424000307500e8903a517020502c10701800100420440b000540030460640c0000c000381b090b0f0307514070000f03100d590b441860001d441a40c41120041500d24070240204064040a0080d1410040484089075518030000c0d080d2352070407a03140b90b04031901c82004068081400b448040d031b0015a040d0360030440e10b00e40240b2088519440104000d0b901082c0c414040c46181801440e0340c100c4000c3c00140018103000c880d40f9420b01c520032030a4501a030020310400201108400c40314001d14410340c56659004030140d90340c81000403000c1110741c400d003160000300d00c40304a01038180180034081105c1c6520f4054036048026103000c03000d620a00c0100400c0e0769a00890340d128a280400e00d4440b50a03240c07841d0340300203455000c800c4041ca40080d0100694400d401c007108440744e42c0d08403181d640c03120141c401d4a011b0300d043d60130800411055019052030b4000070140c10703013042240d140550703d48450741120302c2a00100d40c0e980041c2e10 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 260965116 1250 260963866 260963887
    0x1b071b06030c0302070209131707080306091f060f050408060a061403030304170d0b120604061802010e0d140703060b090a11120c0c0118020306090c01080118090215 72
    0x3100000091402c0462810415800003540120b000301407142300c00803214803070204403114081c040c803000c020528684441d010300e0700c0c401075082251414002c54503a000a83d0540036942c00760035a00e8006a03414101e030600314102d0b1211480c0440806100342000f001811800410180d48501c4040c007001603071504203502c2a10a41c880100240b03e98024028803004c1280701d40b800003015150002c0716940e06039840507a004e01100340d0410781c02403403c143d583e1000d1000c14220b100b51f00c80c0034100068058142c60422100c02c003140030b800502400500c17011820080b143d502e05d0b81c003501080f40d00051600c0d015103041c81c80c4c0c20466032640c40e04a958010705144000d1904020540020700030b8850618a44206000e0010080030b05250078000c2100031145004984028a9500007803010045461100400c10030542c0700701d010388110b000103050702c403004c52100800c510503500c100541c0d207486982c540c0300d503012500c105540d40d2446640c005070303501344150140d983d0380e111072611a1058007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 260966366 1250 260965116 260965121
    0x60a091d040302030a050a03060302060a080a0b1e010305040c080a1a07140304030e1302030709030c0b040e1305010b0612010e0f01152a11030607020f03031b071b0603 73
    0x540c4480c0c440580140400281c011050b207000740c0091400540700c13030b82e645084024107440d91004e0b4000a001920368542548451924420103040b101440b03403501075400d01400301c0c0c1e00b2000110008404219406a600c40c0e00120307007003402100e4140581c0e845501607420613103c240c04460701d04480c00710142c0c0b040e40c01c0c600c1d5030019883c104102c580ca40a08000482c0c44024402010400c0c007213881881d6644a10001d460f803c8402c80854603407a1021014019811714041501c2c0c1c10f520120005039650944115420f44003403026600280c0c5a00c1080303103001e860040100d6003552500301203807107074a42c2c00281c504003801c2035107800b9651410702c691084560181801d809605118018001d8545105001c4000480e503d0480d0b10f82c01c5003e489605207807681c4c00321030207601008410050040340d50007100600340860954200c1c2e298030704181c4e9200d508800f0340b4181d400c14070006184a200c00c0484d0401034054900301d1074003840b5a10010350311501c5100380400a03400800b4415030740e151 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 260967616 1250 260966366 260966399
    0x2010f03090c0e1312020c041d100b061c0207030e0f030705010f0302120a0b040b01180b0d020c10140129180a0608070311030124030b060a09 62
    0x18101001400c41c50380301c40d41c030004140640720703008a0180214454809000507a203203984c0204d90780000606040000351181d401680c440e104a00b401c1c100d00140d03010600c80705007454aa40107129501030702030194040c00c003c5003460703030281c014042c13004607940e4403d090082c8680d200d401039880d0100d19001e0000c01400c0401401260203542c060041e403800070b049c1d016140c003400c0c810240380ca40303242203000e40705004100b032001c00c850042c440c0c050402c0e0003070f210255003110700f070008031641c000468040018000d09803030102d1918003008211040b90043c1607800c40064007610b02100f00c4a520310340600c400c000b07070b9000d9440070002e003010b01b81a0018050500c0340b0301c5580f07102031000700c2c19521600d004030703005c200000a01e001017101c0201224040b40e2000d0100c0c04a56030303906001d0588641180e064010170b00303081e00d0311800e50030041264140c0b00c0e1080c0c55018441007400e0800724614050004091540d9400b010b00c195a0f24000780150704003503500e001859040c100d0804010400c0e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 260968866 1250 260967616 260967647
    0x70303060e070c030804020f120c0301200d0b01020c040612020414070f030b0f150a02190f061814010204140609010503060907051905030708100b04050d210801030201 73
    0x1402401461039000e03c010718101d0709460001403c0d2610300024255404643d803483d442207855030030030781403c0e010958040e400000c40c020000615441b0340101e040310080b440144542003002201070b407002d150b1003541c400e0410310484030030803100e0001ca8100c4440c0e411440300000084030403011440d25000d2114111440c6070754407a281000040945211580381e10b034800c0c51744804581c0015100e400c0d980b8207805009082e01140c21150745020200d5215800c6000140a541d00550b4200c4890700c02c1145164440040c0c4d8402c000780e216074000f0000d21101d0030882455203284004a40303035600002000090000041c0e0b642c0ca010760078420f4810f1500c5103070082100303103c08100b41e83c1080a82c1d031f1240c0256841c039001d41d208031044840d40300f101e6203850800119400a200c2c1648031015500c204180d0f21210019250000381d003040c1d0b5034611a00b002d1a100300010302c12400d100251341c0100348075200720005104140c800c0c030099404018060b0008400300010800e66a101d80400010f011 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 260970116 1250 260968866 260968889
    0xa1505180109080306130e061f0806190c02011407110c010201060b18130f06090c0c0b0705090102010e0106080d0201060e090a112e090503070f18020c100207030306 72
    0xe09549220343c501008050610031084d05c0c880b030b5281080c681043d0b903400d07034007001d692641c680589132000ca2030350013000400b046001e80d0042003003a00084c665020704403c11981c0743c00b8201c0341d114000380c15400c00640865481e400c4142d8140000110140200c00c0c2d91a05440b50071015840c501e803849142e03105045a0602d001000481324000441d460a140084500c91112008020551a146024000754210329026440b1010b42c41507010800f90b4465180612410080c5081241e86466410002d020015000b010819003405500188040c88042c00042812604644e01608540340c50b4003404907500300d04080c1c02c00310f50a00c920710140c5818082c2c0e0126041484a055403241c164034010015400264804419940d400401e081704240903100d0031149510340c1c805501c4e038000020040461b52200c4c01042c1403034003240b114140c440c80d0700c0800ba40d40c07400141400d082c0061005092080d8204000c96111100f44a4604001003005016a403010b1760b240003001c8a14980c0103031032280 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 260971223 1107 260970116 260970131
    0x90a03061a0f090f0901110a0809010c0207180e010204090e010b100201050c07032105090312071b080306010e09010611150702070b0307020a15051801 66
    0x1061001041460250107000c02c0850030002c096200610f10000703611480c09100c1030303501c040300400115164100e044008942c1c0e11a070304a034002580b0004100041809010b082040300303a600c010011246014407000142c0b0f60108154007807521000c000500000c25015100544403a88080280b52000480c00e4000c2004030b08a60180d070b0100d1a42c19858018071032280f09941c0030485a28100c440e0341c2c00c50791403c00c2c041c10215120103c9035691450400e11070741d84104001030085943e10716801103882c40010003000402000600741e541c00398402e222a04006041e8090541e90301d82d160480107030b540c004035880d1140c00680060001035407903071011501c1030f5035071580b0030342c0c038904078282c2c4d94010030404441a80269108000c100b25005441000f954400072502c10f0380c45160709a0340f000307045815022103040d856290f0702408486145214011071905204008001c0c04 = true := by decide +kernel

theorem cover : BRFrame.Cov 260791366 260971223 := by
  have h0 := BRFrame.cov_init 260791366
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260791366 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 260791366 ≤ n) (h2 : n < 260971223) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
