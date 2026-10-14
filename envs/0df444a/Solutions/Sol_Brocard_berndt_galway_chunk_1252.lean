-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1252
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:59:57.640793+00:00
-- url     : https://prove2.me/submissions/f16b3308-4d99-4051-a08c-6f902f7ce7d8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 225000000 ≤ n < 225179856 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 225001250 1250 225000000 225000011
    0x123090a05061b04050303040b0711040b03060a020906091017090606010c03030c020a0c062105040f0b0702160e1005060c0d030c0e040608010e1c050a030b06070501020d0c08060a0602060109 83
    0x610240410b131005850028160f960310b940c3c1e1154910507411255040e16403030081c00e19460180782c01d11071200d030044060f0141c031310381c0c2d2510105402504070001007904000e0400030045103650703151000108022540350680008518889145400e000401c01200c40e80400c007130000e03581c1c1240015200d290b05240104140500c1c8408a061402d48800101940e00c0902d02040c0d294000c8555800c0c2c1400e10007845003549000305440613103200741d5000c1d0083d2440048080451041001342d0f40c0a00f00e401210084250f08190035a840040e501410007030221400340440e8450f222540c2c1e0080c80121805400d00c181c22107401e4841034050320031014941c1e10f242c5a0080c034014401268464001841040400d9175411503602030032000c01000b03043c0c0191400303144000800d80c1070114511a42e070342c003800c10fa010031050f80140070240d41950700181c140203440008a0074001810b4103d2418000b00310000c215501134600c0a016000780d01c5030444030824032116030b00092107811181c0105001c2003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 225002500 1250 225001250 225001291
    0x4080d1106061c050f0c040f090c09050c1308030d1a090703090528050111030c07060903020c0d060c0e0906031b040204090606020a0512160308090c030123090a0506 72
    0x500d24000c84005042d400b524a0110055501182040c6d150200341e8090000581c840d2039a01269403541004000d101600e409100c1c080c0c1684c4034692200580d44014504084454000d40190380303613100c18020b0b807000420039400c40c824040c3e40c4000c0000c100040f46401c503080014842a40104080105641d403070400341400340030009000d002c11000c41103c030300f280c51002d4180034840c841d02540d8646c01c01401c910580c21541c101d03441500e0602c04070f0300781101691903802801a2000503030452203010300c03511040d501c00c0c40080f001446924001148815800054403120728050180e10030b458074003c00130b440c3c40c046501040c2c400f8107009642400d1844002600900454000e007000c00e00c0c0c0b9001140d900c0d0001103060359140142c0807500c0c04041c0c145000c0c420b100c0c2e144a42400c00305440700c4170001e4010030038240c221440400382c0e044002980042030071505800c0503125a102c0f071a0022441300c01004a194000026001504040916441d5261f858002074000070170246540381900c0d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 225003750 1250 225002500 225002539
    0x30c070210031b09030b0c03010b091215011715190b041d061801020c0a0204110d1514010309020306130f0c0308130b070c030206130e010305010204080d110606 70
    0x100d04000c404007202d0340d0f4648a4001d00f40440d50204842d50500400454a01404c0380f050303d04941983c01c1091400b0044014802c110071840040ea5061007106514900618180001e41c041c019400113441000302d100e507c83c1c60641c52144510079882d051040c0b0080c2c50302140c41008940150101145003a000b50200d0010301e60050034a40d20501280550603a45010910a004103010070b9142c0c1c007202d0040040f4200e2180e0340c1c2e0f1031410340c002e4200400509058100309015001200b4050405403000f08003000d44110f4401c031400b58a03030f0301c01408810300354181603d54903000e290811250900d5400701e541e480001c1c00d06420242c005040c201080f0a00c40c606040c581d100b900015210b980b8a017484890300810624050303190406408100304144000740c90a2070782040c061284145550240400d56004580c401c20031250850082101501428005d008512a40006079500c0c5040a807900308004035074440100018400208411032000074074036040b0f8412214000348401e00342051 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 225005000 1250 225003750 225003761
    0x30204050c04031a04060506030609100c03060b0c1c03020f3f010302030706050306180a0609061415041203210f09051c0207060806060f03040f060e0102030c07021003 73
    0x4215000c1e14444c294600320310700c80b05000300e100c0c90091025444610070161500021100c400040c0d002c410049000c0c50140c029a1017240d0b2070a00013001d40e1a8a00e0030f003594030020350700c501c0798002884051120220241860210030070b1408505143d10b0f5105030107940f00b040f09200c00c0c48031002840c80c0c0c0440c04600e071108070145400528081e44000103401342e440302480107912078022030800107801809041128480c603001401c00c243c1d80fa107042c00503c4400040e080000181e034500c0c02240d0111148503040142c6583c0c212440c039509040304000070032141c1d4020404d2040e0074041007106d201038800e40c3c890a035140c240480d280c40d134010282c0c54110303105011303180607091001c98269008150b21140905000d01c09560030070084160000b05c41d00c3c0d0042c0840142d100310310802c062071256032503d0300322074000e000da864802c00160300c080a030410b98040e5903551040501c64208a1644940c81102d40240029811403606c03c1500d000b0f4001c0e0800680a1400c628001000d41e2007548007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 225006250 1250 225005000 225005003
    0xc050f0702190e010e0108010c0f0f03200d2715140c0301060e151b030c06070207050a1203020a23062409090a03050a0203070b13060c18030204050c0403 67
    0x200da1883e0341c614003801c03003410030b00c900540c034580e12001060440c018050222090200d84413014000103c0d90b00725550f011195142d01010360301d0320658a0001000030119000c1031000e500c50306c409240c0110000c0310041c500d01800c600402440315040b0400d8400c06542d80e405c4180c9502c1d042d01448160041c01003541d001e40c074840802d0400001c0307194040a14181d503002c0c0c2c0d42e0002c039940a801d100c0a81410941580c2e6000140520050f955240d55080042d404140c00d82e4108141d942c50b5070320380360080d81c0034005030700441801d0105041541c0078200414961264141000040d24040e4072100070110191200d103106408403845841c90540031950300c3c120046490620341003056194295917008583ea01c0c101c064030349406440e002c2426030041503240c02620803070090350b03030035109540202c3c0c0000640c0418890340e0702003007085c04210f202e81c01903031005041e0181882c0c10320880e4040c8843d40c041c403040e43d15415007031481043c00400d996040d00d0005171501c036010386100c50f0203603500 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 225007500 1250 225006250 225006289
    0x4080c0d020307030809031201050f0f220e1501030809012c01020d050408060c0c12030115140c0615060c0a060209130b01020d0305130b010803030405100c050f0702 72
    0x49000c0c0305500200034201140607130f4031300784613480f040f09030f80d00c0388152003022444002901c01404607181c0781800f080800c00050600200100c00c5000c90581ca62140c0c640c80c1c0040d200b252050010340c05e00908079058030900c0079140c43d821341280b1f0048542306004c0030782120000315140100344d000d60487d002e03049110403041d16102903021450040580314003818018007410030888441402201501c09503038118005c4d00d240e0750b0355584841542c10501d40e284d00c0b841030000002d03410b1980c000550181921070100210030101e0100a404c110040c1e130744042d000001c01104c07001c4e50011074902c0d0002200784801004000715070000750107001d20806a1f106001d210324400801c102a401080080340658004440300550325254048444500d125800b50308000422001c00f0710a030712072944501c60b081c0342d001d07101c40c41d21b809040c118240c212031a02c1d40000180003d120301000101142c07600e070481806244110b81c0010900d00806c140601d11050124201c41103517110100c05814044204 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 225008750 1250 225007500 225007513
    0x1c12170901050a0b0306070203040e0408090d0c0e09060c04030308070c0804260706020712060e1005012103020c010f0c1e1b0605070f060b10120c110d030504080c 71
    0x20880380c000c1c602075034205142d900e4094516803506020a0a81c40340d1190780142d410b00b883c14032043c280c0c01000304200c5000a08101040b5566110120b421025004030450b01c1000d0902c403074500c1401010308a40317400d912510070002540c8019040f00c0640350301d0f107005d02d560f80359554203491550070f00304000e11512000c01d002c5200b20800d0000012180c000e82842c00e0032152003401511031030240074440050300080c006000c94400c11440f1240c8a1255100103205c05a10950078200022608010301c2d0303980344d00041000104030424405030582ca03558480c52007120f0754019507103141422202c1e061105031140d03e007115000d10280940303590400d2907145d002508038210340903800c001c00c0464804007a541d010404410501000c01170380c1150322021300d05203a54403403244040102400f21455605c0f1113000d030480c0c030740c4240e10000003100d0722080c0340000c40306141c0d400c2c0e5480d40420350030008505941c40300c0c540e00143c0020103405604000919444031b0810300014840c84650086a10030340 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 225010000 1250 225008750 225008761
    0x17070f1205030904050f10050603160e03030c07090204051018060e130f0b01020d0c050303130f060e0c040b060705150403020708060c0301050306180607030e0c0a0b181c1217 76
    0xc004c1c0c60b1042c0980e41151f68020f481c0c1c4100690303400243da86905040c1c03103080c040700c614000c04450542450042c1100d04205407469182c0c41d01c10990001d945654002c9000c0007103040100000305062900c0c108001444280121000000300e140f040008004201d058510182c95141c00c0301070780c1a04420074414103d0b890245000f80540195190052280300c00c00c070507985c40740c40b0a0760865440001303140b45456142d00c1030002032280360142c4286400000250001340c0714402c002c2c3c1905440d001c0c281c10301c400c104000454940306103441c0a00c20400107000001d03400310f4000792880160700821450307240d5080c120f1420141e90001c000c10310440007440300850098011754100d4004070f0440740c0e00d47e102075000c44c540c8402c4195005642c02140451a560300039041007218000c901c0c101c400c504400030001d4400700d000c0e405008020800500301b007513140c0d030f407801c5100840152006848116401080003a0b03042d850006043c00d04c240b440c10141500c0751103281d060384240140300b035090508 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 225011250 1250 225010000 225010021
    0x1902011b0b1012030c030c1502070308071d0117100b04080604140703031b150f061a0c060417120408030708090a080d020a050f0f0417070f120503090405 67
    0x103030b0301032a4001c402c0100094407214000000d25055060380d80d10070785c1c0d00580c0c003500c0492110908440364083c0703c0c1d906031500202e10181509038042c1c1c2d01c5030854102070320040e00c10038060340100310115138100d03803941c1d998000e40140f11440c0a10242d90547c0d9648428001c40c1c803264111802c05e4000040000e045c54001881707a00443c018903200300c0c04000c8401d426541c4005200090100d420712402030b2b038012401c410100740301d000d011000d00f5603500e80d845100b1190707240712840e803207a611841800340f00342200220442c91996025146443c048038203c580d00c040041009003203010315140141080008000ea6126020b5034003400d0f0300d410070780351800180c2c00c2110b00340700141d100d90010305000b00024400c441f50383c219040724a001c19110040d4043d50204401000384441009480d1005500000800200348004600c0ba01c41d403c0408010394400801c01000c002d50000b40140b0507080514040011207641040f4254580741914086065010b130300c4640ba4044c0c41d010401644c8580d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 225012500 1250 225011250 225011273
    0x904050f0106021c02011808030f070905030a02010e03100c110c040911090408040b030708011a030f01170708190507080303070801060e0103060315200a08040f0203010608031605010615021902011b 86
    0x100302d00001050740c500000b01c33208460307031040310784c0759001120b1a40503500032908001c0c003200240940364071180080901b015200405420f600044a02e40d90140449040c8840482c20306c0403202030241503415210052160002c411141c443c0070002d012a0030400c1c0320040360020030750820020780320301d042d6a01500c0444248a41610f0810b1800070b46c514940f00f9040740d02c500c10280d009d507010b034203141c15210021260010104a03101e24003001c6042042000300700300e5036040d844d000140b407000e45052800c0203807176884001e059000b442413100060b0005040d41c190389041c0380400c0c00b00704100040b07010b01019800a070000090080c03195403030311036030420500c11600300b50f4240c0c0c6003c8281c2c0c2d9021841100c6207200000c1803032011400142c8410045412031340000c0003c20216180d80320242943d022407002c00d201e81c00b00002e201000401e018003802031504c8480000300420259010b5180d2000e540d1640e004000b640e020b104581c060311050b05803165043c00d8100021961a281d400c0a8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 225013750 1250 225012500 225012511
    0x1204080a08060103091e060605190305010c031b0806010215090102031006020d0c0308131703090c041103010902130902040f140a030206120405210904050f0106021c0201180803 77
    0x10720640005005501034091201d140381c0c8007203141c8aa1890300d400c0310240f141e0300421144262030f2480000c0382c0d80c600400d02c88104101ca01d0800c181e2651030b04034210394140c0c0c08a42414141580c00d50300400d8041c0510741c12070903080070800ca40e56400101d06090300200305000e800c00d4601880106c2205602171841013440015800d03995444400a03a55111904c4c42040019200148440064860000c03184c009100054082d00c0405656920344541c40881d00c408032050301000304240410100084d0f103880c0416a020410714001c1d07140c0b408144414003884003501d400041c14928504000d1100c0c0003030646450464032103440c1d002c41203210911f4451090b940351940742003d01d83c07500100312411240d009180c20f1800f42085002c000074440200706039001d0043c1e00ca0002c015540500b1035a4117030b1491401a600c0714814100412100060560291200400c005125668001914486040443c0c98049101c65a030340102d015101080034143c0803003c0c0309001c41005000c101860252 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 225015000 1250 225013750 225013757
    0xf03120903080a140c06040308040201080c0a1b0809030a0506090111090d030c020a0f0e060406170a060e0703051002040306110c0706180302040e0a121d151204080a 72
    0x500204411144028a0301000e080018108414000c9038022840321007140c52005809003030106220001d81000001c4405802040b004030070042150f902c0184150702c50301c00003403030b410b1030f81c1c0c55401010544a81c503030b520500700000d819000e0091090546a140c500101120788641040c90f189483d402d00740c820700c100d50b00b8207100c0b843d0200c4403029110f0511014141010803d099201140c00405031481660402114100071803142c40b1610082c0203081d820a16078103074200342c002d01080351070591006404160311001200c02d0030012844c2d0b54200d801c602e0101e21101002c040c80d082000c940d00c002c3c154881c01003140a142801d400ad84101e0303024000c00c0203d08100b207006140d41c802c9a90304055034002004c10b2000c2801895201c1c15040c2150094045a840382d0214048440c10b40750080f15a11601e10f003001c00c0030010f4484007421407880d00640881003603d5076880d0301c48284520b031040e15407162442c07620340404207403180e4000c000450b180740e00301400c01d50302d45d0b84043c0100001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 225016250 1250 225015000 225015023
    0x11030105090a0f020607063917070c05070513091103070510080901140901140709140d02030f0a03111c090306020a020a02061c06050f1809010902030303010f03 70
    0x1810011401c0b0200035040140e4014080c001c1d8200a0254070914007150030f20b0381d0f09441850280605e1403901e41601a0700c0718809605c0c0082c1e03560002003502010810010a400c41801c5024012996034010500381002149161726243c00da04020668110130340046c2c594105580e00012a00f00c1102240500b00042111020b0750600d9120225401883d80003600d2401140e50345101d1100703503911043c414000215048140c200700c0c500c2e14285d94141d07079a91030b4000244442c00c600152a00300300c490409800d0700b49810252003c20740380040e91881548800140015510180903070f01f0342001c2903040d5500082c4a260180c602c01d5142032008141c842c8908900030318401511506121aa5445110809280d0390320180698410050881140250494000140c42b201c005d840d09074000c00c5c04071200e601801c003010455130194010340c820300220402c444a5100ea160310030707100006000400659440c81c2c112405002d02c0030009405100000c000035802504107a054266446031451424 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 225017500 1250 225016250 225016261
    0x213170307030e1201020706060b04030210090807210203030301060503090d030203040533070201061e050f09040c1a030601081e2205010608011a030a0c09020a050c01020711030105 79
    0x3524040c1100003070204084511a180510309403890090000d494070025242c003449076919420b484440e4400aa0380502040a100314a04055102c06100d140d1600e950302d2882e02c903c20f65504010322903000e28980c203440c9002c0f51419010f160498a030040c04680e0f8030b50750b03208000c000740d100b10742d0007201d0b00032a06440c800500c240204d034051500310000303044042c00144110a017200c01c050440d886201403001c0706841018109403807081c0c5d01900005190b501c0c11411020512084080c41c50303510341d0503000c0c44140d850105503000710720b0965800411740d0b254503051142c4c6070305402c0043d003035102d0f544600b180d040d010011840f46400b83e079246d074143c4407030081031240480400c400c084641c1620000300c0030034000f554507100410b4094444103030003982d1690b42c00c450f5145c0000d1000e0b5110904200b200707020500c880e2422030194000c08042d5419100c4c1c61100c81203001d410030140d00022008681171007102502c10107101e000c021555502c040c6850042845841d03003160080d42400300040c2c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 225018750 1250 225017500 225017503
    0xb09060421021f020604030e0a0815040201030f0b0a0b030703060509010b0d0c08070813020103021c09021f080109020309031902030c01060504060b0a03052508090c03030f0a03020913021317 83
    0x1910a0f580040c803940d02d5654007628400602004150031400303403c00050444002c00c020b00111740701c002004070b141402e00004007603c0da842070303400c0d4250810980701d102c3c0d00e824106508480550390f0003922919250802c80c06025154403566111040a0002c900c080d034040080c140500010010071120100d01030544e4800340444008001c5981000050300001d001c0350801034161052500616041e1140440310314821480d000c02c00c626950320210701141800307081c0043c0780b1045c2000400403500d031a80180024814010101703180d0300803002c5112003c0409c20b598200c803110220b24060006202c2c02592a080203180002542c20314000013001d0403e4490070058940070b5014919018005005801419002d810f41090521140360200790145050346042c07103040c0c039614070300d17075051200420345411155105584640c000708402520858074400321108041141400758070381a440c0e0014a610b1455080119064000200100810a56100442030703810148460701551810511203 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 225020000 1250 225018750 225018799
    0x8070e01061d090705160b0c0403052404031b050a080703080f0106020c0607150203090312090c01020a060509100c0810080f07030807080d1802091f0b0906042102 71
    0x81d90041000404144428882c100806d28214440321441d40e40e0b80c40c0c0ea071407120080031038911070a10b10101d414010000d0034021810892002890700105082c0d0150218003020081c20040520a0040c2c00701e2102c558604802c2d02c998100d0203465540c1b0340c03030600e0000350740718400c200c0000b020040041c1420803019240c0717044c2c5d680340d401401d210075000c0910407a6400410107441d503401900c0e4000b4591028002103100700344003070181d40c80d08040105800460405003903981d15400100203040301da47d0009103006840d81100000c120382d05d038200356508003203418409000c0303076003010b0245500c650490160b502520401d5894080e143e62000340b940c980c0011082c5411941002c0c0040001c181c5003005480700d10b01800081d071508581c41d50540485840701103404a1948098500d800d51034013403034450303008001803880010f000d07001503032038011503050003242c16150020425061940b01c10701038801400360a14151402404000039480d11040d140c001c0344a290105072584900003d051071 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 225021250 1250 225020000 225020057
    0x4030809061005090c13031109070504030f0b0a090501180c080c130b28080606060c030a0c11100905030d09061e120f0b041506050f09060408070e0106 66
    0x6420600d040c6001c1202c4481302514001202009004d6032044185507156000118841c02c6400d50110f4041d0500020b01c000604072018841d050104001261f0511a0402450390080e51704640d81d64000e511f40040046d02c201511940ca001c020090150032003850b1840740e07014000c48a1172503a00c000c001c0c0d442c460606041c0e08881071101d102c040c1e02594010441a010007084940b2030410841e030304020f8140025001402064080200210796040c01156001101039a03000c0c0750007851388a240c0c1d40d00c0f44050340020040b26284101c01d02c14403951a0220150040c201280c2c0d00100c64020101a40342c0181440390162200c2408030758080c1200d0381c1151800d444040000110080454800d00300740c03421420712a801c1910002c89003244501c540098070007400003210010700341030000310341100344040c0e81210542418003a203608601035600664018030041da590030401e000c200c542c0515440346040e1b10404002203040951545014180c1e405681c8128007550303902d901c107000c03083c62500f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 225022500 1250 225021250 225021271
    0x2120115050d020d0603020d150f020a050405060d0b06031005090c070507050904080903100e0c0d11040902040902030f010207050f0601030b0f130c06090f27050603160603050403080906 81
    0x1c8a1002c889076000f80104c01440040092040e94036004110122002070007203c3c059800c1c82c8c11810510588668158044004021402c01c2c0114401505511480c007445204040c089882c2c41000e80a82004005007409000742d502ea00b031080c080404001c0f01d0180078030a054540c0002c5044c0c1c440b20a60394a48d40210051030040c0c038141c00d200c20003001070800da564203400c101407100358608210488080001400000d091080001e05074281810843d046208460722809040401c900d200c4600400c181220001a00840307440014020440402c000350076000c4c40401c030500c00010b501500159002e4820f8a0440896070001354503048240030040c000100c14000c00d00c2c918201e80c28a80c0809485034405469159450742d6451a0107540701800048042500f441920030b1392110341c00800021041d05403080e500040140100c0785003202c58400d0744d441d40060100d5508000c10b840c000d083c004000a00e94880c1c800402901003140c00f038011907820004a8840b00b0006100ca1091660a1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 225023750 1250 225022500 225022507
    0x1060b0f070f0201121b0e010c05120a09091a042706020a0e0409061506051c0b0402130f061704150506060c0d2c0a03030c020411030403030212011505 66
    0xd882c10420000c441081c0e0400a841901d4807a801c402e1040308034440c0d02c40030140d0030302c441380401440d45001c81c14060402104814a100007480080d9003040301090482184d00c91002100807a24150141d10800c4220b040c4400c25030403042c0241800c24106055405108586000700c0340c42008680400c0c441c4500e400602e9100811407940c054001ca00d070500e00356061929803000101a1103030310f4020b89005640e1004840c8a50040541200805583c184a42440d03919001c180c1c080c07125114a2800c180c40e030f090410240c2e03407941241c207800c1611a40d020841d07260080018420118003900b8081100c0282c801c0081038000c8109204580c40540c0c26010b00700c1d00365801c00340401500c03254005105000001403200c0034424440c0c012525501c000e0300d0b410403e001d08010039010000c00b0314041c2003009400b5600d540380300300d05030f94250a1644101c0b0862010074018807400580021031803020050004040e81038000742440318109020f2016030740c032110001003552188540001146082 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 225025000 1250 225023750 225023753
    0x90912032a08090118261309050609061e01140405041b030c050f04060f09090509030c190c0b160c14040b01030501050303090d06020f0301030302030c0d020a08030f04050f01110c01060b0f07 83
    0x401c90045200e40c9005030904803a100d101f0440341d0fa5401040c0c60300d031241b080180c0c60412180003980a401100d5001c2109903585000204140440c1d0550402c8003400201101081c00c0049070020400a041000303000030482d40d0f5130005410444a0000900b4030740c51100492040c810340e42903007400b44c00035103002d2616006031000c0e04805a03003424008210740005030340240e4031869119001d000c0145540700e03074a100c414201114000c41040081d0000d405070b0214020b107410a066403c84118941c3c1c0d0404045c07600e600f00d01c035142c0140f040b81032440201d083c444000003481d030114103640c01d0112405c404015000e84509000e5150503610030f02c81680c103882d04085d085d01e414050000189407003400082000c2541c0243c00aa0141e400041c1034602024200044100c4030514030107040d000720031399240701c480c0c44003900200d045d00381c03240440d06100d0f0a2040c2c1c00318050032002002a81c0c4880c803400003541140d44c01c802a54600304000030301000c610101c0d042c80c071003488003514081c40c6 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 225026250 1250 225025000 225025043
    0x2120c15041a031906030c06030f02040f17031603020c09130b07081005030715090b0301060906051b0f0d020105010b090916030b0307180501090912032a08090118 71
    0x4d0110002c0040c00100303031140010741c0310341c8026500410350940f440e8208000501618040710500d1405441004104150b10700d6800400540b841000b85060305190590503500d10300511075111840c8000340d5814040640004040180210681c2e0030f20b0556030b54901050740c900c20600162001c100400021b03c0c05105000a0f5800140c0201d015001a16400404e1412903690818126206101e1050420315001140c000c0144441c8242500c0c1d5810600d0040600d01184101001d1003000304100d0301d130800e1203413412051807420b01140c00381c122043c1e15540c0d0781b03a074040c0d880155103001c0011511126031402c030786046074090140d280b10f880b9520710081c1080d002d60361500b01a40c3e006900000c0e901881444020144100303482140740c04640c0c104116031040e44840145440c08404000241d03c0e2401d04e403141c01181000140c02c0c9482c22100302c00031820030648046100c811200c1900e5404c01c0c202802441d1f070600030840c0c51004007201c10000180c0c50098140c00f0501e0645820225 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 225027500 1250 225026250 225026257
    0x1103060d1401020c0609070b09060f0a120c050901030b0604050a0605070f0b2406030f0703090f05010203160e0a0501020303011503060f0b0d140c09040c03020702120c15041a 76
    0x1c2800109500703501840c81c642240c100c9002030540e600880705000100d07004101d100301034910007040301c1c648030003100050007612400f4a02c0f00d61075404100688a80c0c012802c001c00c4e440c80e0340c010b00c021031803000c00400302e500c0714a110340441c0c5040c60a00b8613042031419201590000fa200c03140c032a040c40710586041d04040d204032900000c1080c000c00064a071984140101c82d20740030706200b8124080c0301c1c0703007120610b01c41e5401032700103004000202c000c2c0840a41c04c400a42000912040141001652a0708924010704690700000c18841002e0351414240c0c0c40001995030340044000507800c11114481c140b294a006070f10910051106200c0704116109440e941c0c1400507400e540c400d0300388044203495002f0740e0f045002080000c4018100d026103004210418040702e550300c1c0c4a504c1000030b0050300641c03030180d95a0143c1c0c0c1c007614081ea044418072500205840742c03460240b5007035960703002d10307091190003107000b500440e04569200041d1130a45e400c0764070290811144842c00702c2540c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 225028750 1250 225027500 225027503
    0x31503110f0607020d0b04020102120720010c0209010305031b010902030d0302210405070509161d03070f091b170402040504020d021c110a08030403060902030c090a050a050a1103060d 80
    0x9810880f02d80140d4858190601c12807207a15407a1184ca0f003800007a08001b2034101101d4114010401d8400240d000340307207028400058155419140b401c00700403a14480450402904048400d0003c81070040020181c1070030703000a81a1014003030410f400c0ea080e20301d41180250181d01a510001c1c4c0340b030181e00039069695071005426070180b03442d440c0040c5c02e00305a034140d8071303070300543c1301405241824401c160b4403c80e04208850b08201c1c3d888024500e0382c1c594901100102e912010a080ea5014040d21009101001001c82c04a464100c09001044407005c03010031b00c0b4101c48001342040c09002c202c1000000284480c801d940d4540a100103464011703c00c0f84e0109100c0311000041c2d5405070201307852030240c0340c59515a90705141c283d2030f4071315810009102d036020010802445a0000455043e0b9504c0400821400c55901c04681f500c942000740303540c40f040f9481040740d0b8040c41ea1090348a200300034004d0003661654145203007100e42d00003005410303150400025117103040405410001a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 225030000 1250 225028750 225028759
    0x20c130207020d08030402011d09150a0f06090f06031803080c04050607050c010201060603050c090d1106042304020406122a0e0a080609061603020f0d020901031503110f 74
    0x100e250b50002d00341c10043c0d8030444180c0c002105000c1035503803005280401c2c130394200b160800d41104400141c440c81004007410349402550804817255140e0f07010311001490350442d802801522210081d0a01d14140141d0f244d540c0f40d500b001400700d00c40c0c02405041d40c00303024aa40b10b00040c1d18100c905400080400d60461010030000841d900c4200041c00142d0184016102080310440028251035155100e801014180400d002c00c03c0441c104032822004c089039603001000003403031312036480700807840c280f5030054020800281c503403002907654000881e5001000443e11204082004a0045018210002e200101c445010241c1940100080c2c06442c09840d102080c00210a119000401040340050540f10704408141030090f088400f414540c0b000d02031a15104d2605907032081c0040c800310300106c1c481420090070740242d044440c01d0f43e41d12441546c42c200320103c40065488149640e002034174109840c1249042e5a80103400c1e240e11800d80100c1602d00b404024081081480541c2e02 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 225031250 1250 225030000 225030007
    0x40608010e25030f050f09120901030e0106060f11060709120f0b010323010902062a03030106090612050402011e0918050a050f0405030d110c01020d0608010c0906020c1302 75
    0x5503502125002440e42d1240e03004100100c1498102c0151007024002d2440759084030148014610081070b480001500c1c5c0c00200d4940e002c0e10b00403405040110414030b655480d00700d000c41c2c003560001001034144042d4840103943e400e1f0401195035880200c45020000b00101414440341194541a40d03600c1c2c06102071086a15003611600b0703840c8000c0c0d000300c808512443d840d010290803800a126407001c0780c0000c208014a54020030014400c000010b05040c4e030028903030303000c124408085000307a040441100d89940e150b01c030207171003800c0a00074a004074480c201040d031203403900c0c0038075403007264103940e82c4085042034440c0982002035962060140318035170001095200c2128200301c0144494640400c1c1424055288803c444000e0000100c8001c80300400001c01c100000b16400000c10040008408204280301c941e00d00503c01d428209500005d411100d400340364000390140d500700c400030407400903d44c4040d03451003414804c40000d6040b90240b115030745400c1801103021180251301625 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 225032500 1250 225031250 225031291
    0x103030804030c1a100902040308071407030c030302061e161d1005210402060f0f0d050403020303150619350405060709030b0103080c0f0f0a05060c040608010e 70
    0x207018040401c8400001d1300320421892924849202d00100b400c1c9208600d8141103481c0e00f42e030780c440c038a0043c11b000070b641d0800c003014800304032500045800400b60803200b9120b01c0c000b03454150a8840030a44504001e107148010001d040c45c2c2d00070244040c214001400020041c0c03400032240c04c00f4100d9119030802e000315501c5440c3c521050f14000c1d51200d03501c114240450000b5000901140036545c603840410005849003021105814110105940c0342c2003e281480420b03c0f1341c2454455060612041c0401c250300000a0760141d01d11079080d08a0001300002e001c55400749036080441c850384a4528583c0301d0041c901407150b4a080c15003140070120055000c040e40208003401c00000003188100030506c101804907581111082c580408981e00c1c646504403001c02c10700000d041914006028280c02d001004044003810102090703075807000b4440c0395203072518030414094030b190081c00002a91060308500321819501103888003421a42006002c14a042c030041c0204824a60366282d40c6 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 225033750 1250 225032500 225032513
    0x9030204050c0c16080a200301020a030219080610111e0d1112070303020a0203120126010b0d030e12010f05061f0f031a12010b010e0603010305060103030804030c 71
    0x40c411007400e0700720356840200d04442444d0440394000110446405241400803242c0170600024480c2c000c02c00b080c030a44c50240781140705209284c069071540c40007600c50081c1c0d030181c001c0c0c0490020300040e040d20142014085c0e0301d14008441d032039070004240c0044145240110b0325106900041811a0764000c051030040308101403880400050350b2142100044642d8040002003080d240d41000c1c0003411551107030040709000c0c8540040c00e043e00840c150101c0c83c401c200340d41104511007100411b40d40c1d1003400e190a51412030429000312444820b4080101c014018049640c4000d8107410110495072012030348a0710100c1401d900002e60040300300c000e00c00740105104000f008200254a043c00b030b04112480302d146154440800d281d80545400c141c20445030354144501c5d013408140c0082c0241089031701241300c926181d1140a00d0103504400005621680d58a8001c1c0c0b1a0b8025081c0369082140c0b5010900c070060459205000500009202c0c07e546a0054440d042c00d0194440550b0b552 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 225035000 1250 225033750 225033761
    0x10e0405131a090105060d0506010324050709061418061b060c0d0c0804020607060c09090908041d040203030d0f0213030b04021f05160c08010e030307080903040608070f09030204 78
    0x40ca0020702c018029501401c5c81000d4000500700c52003c0e100b64240c0d034103900d0301d8052101030112542c1807100c8101e603140041542e4082404801041989406080a03040c4c54071070040300005202480f9074601404d4070801c990307030284004003c40c10a0078400c10095640c0c4141c80707501004541421483c0700940402805006d0b4010010380d544518900031a40202c841d0341a4510406c803459003440701584944080703450058102c00302203135007400042c05490b10b48080d03108100c40ea00c2c00d0031110500001d000035006481e1900012805c106070b801412450507010ba401039855041040016443d8881d6480b00412a01d04031000d070500c4203503400305401c002e1170f920070340c0d003111400100300851400e6280c140120b11340014483c11503060050050041c040c110541d41800020892081440066101c443c000d0907035400074400f10248075805600c1e0341040d00c825010079010b80118102c00c001005a50589043d5900c1c0612a81c64410442c4e41208040c0510240b000310480071000d41c40f2409403 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 225036250 1250 225035000 225035033
    0x6010e0a0507050702150304050a022d100e0d0c050d060605040b09070f0309020d050a1212092414090607111b060f0c0304060207061d010e040513 64
    0x1006400d152800945056440c01440e03a8200309040040d00010ba03507145000200507000c005041e213a07903031450507514004200780040c0d4001c1410f24201e010914600c903000410031040850843d060b151020f02522014062040002c2001c40c121003d0509200d10010010f43c020200e201e404d0740c0d42c40c0450601c40c819841524500d0300e0b90014002400c06002c3d0101c442c80179103403000540742840004142090110481003090749500c5500150768400c0240e143e44d40c1c102043e550001100d10b0a108030420300003411004c030301d2160403004032008600c41c480f111138028031004810100b000c4004aa140c606240c03002c1d45981d40144081c0c1240c240c211031241d00008000e040c14240740c403002d804165039500c0c0c01d08a0780400d510101c2e4040802110707821440030780342d06488181d5031a410444d4000c20950944030b11012130000b8045034001030a90840d0b003240c880000f00e540071880800d6081c003400d03003c3e003c81d91583c0701c0303005802e10741d01041e800a2160201e4000e82500d5031180007020f4000b80 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 225037500 1250 225036250 225036269
    0x30612031e181903062310030b06030601030506041b031b0305060a06180911031902010806012f01180b0f0624090a0509070513080705030327030601 65
    0x42c801c4038110a611040303500d910888054002e00c2101a852010742840c1c00010001c984404868800c0c440c001d0540c0c0302c1250007003030f1150610f000083c0007000001f1340b0007505c1203400903010a000c0d043c0860b80c103040e80e801c81c018045d10b82d11a210700e0074900100c2081e92070203201030000400720342042c16029040c074034850f1280c1c0c00c030303d1418003a207042e00103001c2c14012464603004211540c51031312080b05d99649544041000c01c81418524031002481c40c8241d0540508002954080304040c8100200b80c400d0300c403046d03070b0344804004456804080c0300880203000c034801c0903210300711030a40300040b02c452900046010000000302805901c031001c401c03680d0754401014080c1544040744050382c0100b0658080b10001c0300c42c1011403043c91503e17003e07820541c00183c514402d448041c2c199001d400c015001e4042c03400c0030300006095501101c0d0302c400d4001262008652008081442c1089580c001e0096041103a4801e00406400d229081810b841e403140d80c258040751400e00006000b40210403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 225038750 1250 225037500 225037507
    0x80a02030714040308031504050c09010e0a05040203131214070f0c0506130801050109090c0618030204021204030206071d1c0c0602010915050f0f0a0b0301290f0303030612031e 77
    0x6045c02034003140031175608c40c50400080068503404a402d40303145041c2480c1c014403048481c800314100d0b4080d50005d68001c0d0000041003440d0340e04050144000348200d0f036941c00d094000c0c40c21600c0d4001c3c40034149050400b00003060104510300b003070016441c0200e00144003143e440b00000c035650702251620304603400411040001c450300b03115850041a01c21070500c0031059650b20403d1030038440c040c0105101618042d581c00e500014075030009154007400c11540d070480400c4c0181404000c1790110014440d210002d16054441c1c06455048025440803e002c213000ca4100245000034003a00c01d0800b41090a450100382c2040c0440020311154000140d42c9405080030003113440b034591000d00c010300384024410415110b00f5010b5128440007400c01e4107440d207680785c90251201115480d49503007001810b0808a003a04843c8101e4540a03190325461000300003441882c507d45068240d03da08240001840c0d030900d102c200d01c00c14441c0b000c2c1d91a000d0302800f00c0001d1343c159441510180d00c040f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 225040000 1250 225038750 225038761
    0x306021c0c0f0e01090b0703050a11010f0504022107090509010b1908070510050904020304060207120e1315090213030f0b010e15030c1e0409060203060a0b0a080a0203071404030803 79
    0x42907400d0003d8003840c000248500301030f0003002d1445600401400c0040004030780200c14400c000301c40049400744001e124130720895840102410701601c1c00e9105900080c001010000f43d03241e801f95803504140500700140c0340c031409800500d401088031b0400d54840020103010ba5a000c0da00096400201e1901c42c0c01d8181240e00e0b280082a400660080000d071600d040c80300c3c2c009040c0d03a14480d003194003507501c1e40c0d540341660103801410f82c001c02d140c800c1c00300380c405150040c2c60341814090035111a800e0380ca8003482002590310344000708034810704a19040c000410150010600200c0190842072a903903240da035100c605100507402d2b50550007280c018400e01042e07503017450b00401c034843c3d13005407866180e001980350707070710001490721907002380400c0109040314903c81000c05100038402c10650b0040d00385400a0350040740d0040c4164110800401c4602001c800e60b098951140c3d10821103039100d00002c002981701519101c00d000c17403231411010024844009101071803294407a0f54490904 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 225041250 1250 225040000 225040007
    0x3120e0a080c0909031329070b0f1f0801020d0e0c0a12060902030d090303020f0a02010f08060a0e0901020705010e010501120314040503010603060b0f01030501181d07060c150203100306021c0c0f 85
    0x1f090f250320004a0100075174004074074002c542e150040160b1040a0040c1c0f1084540480341c1d1600041c201032408034800080c0c070714810b40c00340280600d080e46c01d0007010b48008102c1e0300c070301031428000e511840169040c000d020b500712415440038420b00300069400702640000703107401181035040c00000e005440520805605004140c03075171100c2030086c0240300b06a80003030013003803821984400f08280840020000c3d640d403041c4030001d01c1c400b01c13a50f403181020503001c2c0c040d50000c00107031619800d05080b5026200140f00e40d0707049401c0381c18448044072040c2d404a514410080d00c00494860600c400301d5190740a00c2100001c6125030800558244600c1c02e0103070b0f29410b024458181480c0800411100d400043c0c00c811108000d2000104050502043c0c4040a50384c000c49116101c0d181e00403480a42140b030f80700301e05018038055051400082c10344016440221851103008002e0b82d03007040010442d4019100c491403000c130941c1450080503842c42118088030081c00020950040d6244a540 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 225042500 1250 225041250 225041309
    0x1082406121902091302090409060f06080d111203060d1502091f0206070f0201020c010603080307172814040b041e0203060402090a0b090103120e0a080c09090313 71
    0x100c446040d81444c402d03500052103120001c40c0d24507810f4000892055aa031a68841c030380055110f1130401c4518094a5480002e00329409a140c0b41c0c4685849150101d0286000d41d01211303042c0c0007031900940881c101c1960b50000703040700340c00000c81e134010000105103409840d000d402140380183c40e40c0b03070300b030400409480754010001103a10b042c0504101c5680824002da0124107400c01700c0d81c42410307c80883c020b1051703c40b860b249520340a03012080155800081d409200c1d00d0356000400c00341c80b200007441c80340030341d0b030134441d49120003000c074800700e19842e02d2200843ea0040042c000d20140c6043c9843c280440c0c00304c403842c45e0001040208012220b05a2604403010301e110311140305a0b001c00d50b0341d0400780019109007021030014000800c00c1c3c01a8000c114083c2c5601c42c59691381c0b50000d480d030270f107100c0e45021880c080101da5075030070003090200c101c0d80200024030b070440440c0c0c1808801d250140c502d84650008020100b690618101604000d000305810742e150680d1300c4a502c42c2000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 225043750 1250 225042500 225042541
    0x1006090e0a030c031e0809060c090a0317040f1217030114120102070c08060925030201050d1506050406031413200405040303050619050108240612 64
    0x519091844200000c00294070700e5069160520b09a0241e0b5800d040d00d030044803e810b64040c0800100c40c1305031380da01072102c43c01609484122225038582e6250712045010303000d00503400c444580410804a07031101c0c1228210704e0064425441d10703440e440f00d0a10000b581d04524031701c2e0b4000e031811341044811100d80070901181c4490030304550402d00405035981150362010f215010851010107451000c2d41160507083c1c0c00720310480d501b980da0720840e031201030403604402103018540106416810828808000412201d413440314a4150303401510703a60850030741d86400c5c13556002c0040101c0d400b4103000c4003400485d140c40781c540c0d02d0010001c1c19104c1d04541c842050390b004050119180342c05036002e80d0241e200c4401100030a044802003809c0d4142013106600134200000d01080c1505988080e000322015a80f8030002140031100074001e0006218450020b4031a2000031040d8045829803085210680a1300a000050100241007900a5500c40c000801484140221881402e10703940810 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 225045000 1250 225043750 225043769
    0x30e0904050601090e03040f080c0a0e040b06130b0d0b10090204080703080c1609090605090f1b01020a0227091207020103020d02070803240f0d0611040f081006 70
    0x1840c1603038030700d0b40b50b600c18450074900b9070b1201c48190481c3c2c01031051320301400315140100d115a9450324070591360449045118050041c6201c0031407224018203030b10307203c2c4d900603021190700d40750b8000340b00001c5001c000350710a040c0e031183e51500c5d0f030345eaa44070007500600408204045041c28100905080c1b825405080707154410002002250f1001c00c04000b220380225001e5280c2402403031b00c5e401c2c50b0481d501505130ba00050320101d034105090f44003483c03140c010340c0e0410440c4d030380300d205943d900d915000502a662041340f4079200650000c080011042e01031040c0c070308000450f03011030b542c50160201503100c002c000c401814001e02401c1201d501c881d42a00800700150820141240f074411091701904150b000038110401d0382c0e090f01126001c13640500c0060766031800003030040b00300100c0100c90b01194400e810395203080c901891412401100103190042002581da5054000d00e0f0044d40c19090041c140400150380324003401a00081020001a2010800c2010340744c04441c003c3d023202d10721 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 225046250 1250 225045000 225045019
    0x110a030207060f030b0d140109081612050406020c0906030304120605040212010c08070c03020c060a030905060f0c0405120109060213060206010b07030c03081315020d06051806060f0705060f0103030e 87
    0x341d0b07107040c0351088035900800e107542d4482040701c040c1c0c05002110400f400d441030003d0340c291250b10300d0302c2d0bc2c0c101901681800d100b07540b180004461500c0307075204500041e0303c000310f5268986400c0500581000b0001d084900d0f0aa4944540078550710101084c3d40450781d4004200550030004000001d0003d0300c8005c000c0f554140202410417840a0030400811400035403080030117008000480400400070420b9403103000684009028000d400000c030b071240115000306002c40d40003143c1a028140c800035407400d05081030184035051458040f030310b100707640300c0341c3e800040f078620701c010b10790300c0c0750240300000f100d0501c00c01a240c1041a800720311280c00400800000c682d0280d4100ba82e03992615011801e500c1c0d00d42450040c0c4551440948054038844000304231085c0b80d401043c02000344501881020790340d004014181c000c050400268150580000e061840d0100042c010210082900e500f00140c1791286071038007004450b4080d010140c00b0050042c140c000c424050925404c60f00c2c0c01e034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 225047500 1250 225046250 225046271
    0xc0203010c03150f0b040e0903130f17060910110412080408060112110409030314070329150a0512100518040f120e04020706020405041b050316110a030207060f03 71
    0x46c80303980300d8003140c92011400325100f12820310880314002d90710f0000c1100580c543c0d071801c0c0c4035041d5109003440b03a400007580458004000c82e1007031041e001c06c800303042d240150390019409031104007901e240022081101251409a10291942050244002c940c070380741030011180c9011810307004500b802c0740d91a0302c1c000055501c40c03840e00c0d05c0390039200441c0851b0580390550140c00762440c41e41e5100134100030800b400f64580e0200140b0900c2000d102482516600d500d64040020006203400c46d5000440508200c01c90000b8200e2080310704c0e05c241351555001400002c0341c000c0d10088001041d00c0c40c20843ca142c40400c1800300c00301103ea44a10b400e00c0c5d51078000c0f0000d00ca0006103140101d09000d51b080c0d000c0c41d0000134240010b0025503450440b441e01c44020f60250150038891880d080c403042421108000c3d520b210056920340620f50b1f1070305019920a880c40c44440010003960400703506481c43d050003800c0c141480b9800030400a4140303031003c2c0c0074984c0b108103e407c1615007443c0c91b8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 225048750 1250 225047500 225047519
    0x306180c07060b06091f0306120c052107080a05010501380c0f06010509090303161103070602040e04050d050c07120512070c030c09050f0c03070c0203010c03150f 71
    0x1003a55502c9032000a440071008007060550080300358081e8003009005214009408141c540306104440380e90400c0500d817a00741210761400303e54005802c400c1117400c28429800e108003d9a5102c0412908814402404600034545012034010207900e401c0001e0400c1044800d00410b405086800c0031b00d80303088044d40901c0c0c400035054001c008022080d402401c8254000c0080710b000d080180b041d030f00d6009090300e91039607460003886568010b80c040c10004101000c0481580e00070a546045a000c49080c0c040844001f040c08114820b10f000030840400011898402400141150020b0744070614040c200305003000120342010342031241c2009900c49a000108107002512040403020b294005a814090b01d42415a000d07500c00b641c0c00035014051003001d00d000030490b0f01c900b84042c0c00c5a100e0510406440058418120100b07400300412440b101400107594403052502d03015102102d103400007070075246144154004a6a9070014025809101c00100068140c3e91a0743c02140c5c50b010a01c0e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 225050000 1250 225048750 225048757
    0x30507030302010f1a10120543112404050d02070f09020c070b1b0601090c080f090f0a03080105312403030806100804051506010c0501110306180c 64
    0x584504042c06c03500c08a50301403c145903204101c86001c100c00d00e405440490404004a000000b1380e50f04401029560f5807107510240c442041e080506840101c801c00350340f0410000c0142c4000e005092a01e4508c4007062808104c00e04400d90000c81400c140c00e0103420b04070600c0110f021500311000034440500000e03480c2d03003194800b406c01a07442a61059050070140c1c00e8119440b41c000001d407844140702c00301c0110015421120980310a81d9030380b00e010044550000c2c0110109441400240e403510071460115842028402a52030307041e1820380031400c103a2104021030204040ca0010704c000d0810080d100a507040c00220406100d000500c280d4611904512001c1050785844020101c4141158101c0c844903220480d000c0e0f00341ca9241c083c1218008071a880e0203048080007000e00b15100b507002e24007458000c00505241042c504251122807001070403203052090905807100011000d1240c0e408007072404110300c0d00c0382410070800c08921140003100320b192a6003810301c42c054031020100d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 225051250 1250 225050000 225050051
    0xe06090c090a110c010204140a060c12030605090a0f11130b0c03071205040311091501030c1e0e03070b070b0c03040f120e040509030f040504090609020406030507030302010f 76
    0x1201503580e0b0804a003001c1c020f04861590706800100d403908040b14150045c20569800780700385100b0a00680070f1040c2500c01d8801d10300010391443c0c0101c0850100c01082011408910300800d95940362004209156001c1c0d0306882a01c0d50307081d4000000746d00748a0500342e0380390f1141040c0b4104043d0f00c000300c00305140c002d0b003000c00000074079810881c50410840e001030768011403070b0190508584028009421900c016030f62024040d03590407280c0f400134003a03072290301c03020700380d038105000b03000110b00900f612100c020070f000d90341080d010700000d40c002c980306c844995503522126800c1c43c0d003807501f4008260f10080034100e0901440c00001c4010b901c0320340c01580c1d8041c1640703955660030a641e003012140d03405080300140e8030f10030000d00d61005110039112070940d014007080e180c4483c1d8640d00d00c91009400a4200b062200303010505d46a0402c071542c5e401560081000907094001404480c0250301c111000d610003038082080507020f0013128643c06080c0f0080001418000600090b441040c81 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 225052500 1250 225051250 225051259
    0x601060f050315030d110105010504060515030a11031311060309030301050108090709050f250509010c03031d0705130c140703020a2a0e060a0905040212010912030e06090c 75
    0x10300c2030700b080d074280300d20f001c0014112111030800c1e69002d080c00305808505d8120b03500b0301d400866542400e00031074040b03d03000380c000c42c0e4510030f0004407001c42c0c01c054510b035100e0b500e540d082c1c85d600807005c4c0a036015640b002d03e9500912801e20b08401c1d9111a080f24500802090081042004011007503d0441f0f10a0800b00001d40d40d0483c85824804d05411040b02680341c0b40500412406000609110329401d20303c8000101914542c2150120103104030b000191040150098a5125000c144401c034842d04021804107002007010529961540b5030020035032041c202000f4a29180860018000454204211203003000700001c00030010204030000701940000c60104041c400c029903554503403c0000e5603003180032000f58484141140384000c00c0180340722000308190110b20035060187d40020034403400e0303d02c1e10400b40054500100706076801018000030070400b83d028060f194010b03100f104089000500c00401401b29003031038a0003c40c0394490b6080004040c80012051519a02220b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 225053750 1250 225052500 225052507
    0x2d140f0f060111010905070e0619090e0703050106080a110922021f020109020906060f040e07171003020a1409060103090809041406130e060c0c01020f070b180601060f05 74
    0x200140c590003c0ca000441e102d40c43c0400ea1014041e01042c544251409013021003181e4440d9810046046c0600c3c09207401c28808980030000c8804c203030710107012005041c0a0310100e83d82c07503c44608644140e07100316819004480c10342c01300b043c001e0030225880c0b421030b0590701c1400c0600075420307440b10000d03c4115101c40c10104d0702c1035550390500a440c1ca10314a000840300222100000c0c041c02d104881280900311110205010349444001d07518202c90301e82c0d026003490302e0b004040d4141d2130b002c0c00000034840d10b0a4a22010301c00822040c0c8a4170520107050901450b503c1480030140083c3e1003039400d4182400b1080c02035036040003032034104109180210780307003140d4140b000c070171b10800307800307031707446441c0c07000c50400d8800c400c20040c0700c1c40c011540c038080c8401070f4400c0802e5654403442110030390040030014080e501c02401a0280880c2d840006081a2030340a5070038540d40004801d031740f40603000c2d04215525040c0000b40b02c00b5216900a00b88551400c080a42201e907a00e40b01802d000010 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 225055000 1250 225053750 225053761
    0x60312030c09090504080c01060501110a03030b0d0203060403090609050414010b0d0e10090512090a05060f0409020a030207060c020a020109060509041131031203050a2d140f0f 77
    0xa454620250150100030061424603180c12546c03903012408500c20303542003070400a45076001d005039244075420704020f80580d02c0c15a8040b03009050564030194062002200840540c80800c2000d100300c0c400e48030980c0c1c160800b84003a004442641c802d610550400c1500c05508045806640c112520303e808643c89194480804015004c68004000c1c00e03c10340c0110305503560541c1000400c94001d1080d40c55040c030205401410f1300c030300801c1c0c64010802e24410400e90405030001c4c040502480c03640c078149502c0b015004143c2c1d010304081c80c0007030f0300460440103010709485000c04072031060004121914180e40081e200955901c00c56084c044007044260142c2c4658010000c0f0591240015948124841882008042207480e030000140300081310b40c14804590604411b5030740000705000c0211444a0031005048002c1007124596102c0d44001e0554a02d1180b44110b110320a1000e22400f44a44429085503481113580e0500030301c0301c0a121312602100d5503203401103010301142902c0d40d40e5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 225056250 1250 225055000 225055007
    0x9030f0c010b1909140903120601021204030302060f16020c190b13031406070509090403110a0f0303051005091f080307080910090b19110f030301080c0103060312030c 73
    0x1412080b904102400740003d10500c1c040c0e141c0c01a42c00d841070030040130a01440b11a00a2022503422220340e104001c0030b0358201040c94542e900160501c1160040d464050625030a43c001e580100d0140c0d1010782400f00400340c0c40016540140800503400c5550103050000b075482d9650320945018294200c011050444403c0c1d88001130480030140c01d0342c4040c07504980c40300d0251840150340d840500e40503004d5205000c01c180340210019550035042c00d091a040000101010740100d00b0b000710400142c2ca0054180031300b000560003400204030910395400d01805803000201005d59819418400380000e954403a030761500080d5078400307141550029038a85a00185c00e42103c922031001084030001c0261a070000c01a8a505940c15082c1072034020050302c0040740d43c0201d400c1c24405019030384005802003c42c3c1c5000210749449100503030781d4003500303090260f8941b0019007500000010f1040c0181040741350503066082ca410020305141d078a071400f08804842030003080644608048510a11 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 225057500 1250 225056250 225056261
    0x10509072316050c0411040b030406180204060902280c0f081e1b0a020d030e210a05010b0a08060610120203160e041a0d02040212100e0f09030f0c01 65
    0xb22201d0b80e40d40c01a0501503555101a003501340706a060804c8054042c1c440300944049400022089045407610b81d0382c94040c042d061000e03a00408500340c00000759803940100f800516101000595541201c088680c6102e4510003140c0820020300051441a81c003130070901070b40e5004101c6850a400d5440d0040e414800c000014043e403000030140082456550700526051074051b1101542184240703e150f11807141c110701035031182e01c000c00000400d0141840c051001c0000f4465aa656501d48203403408016509602f503040d030000349160308120091280d00345e1036000f1103100d489946080000d03030303440c40001c20b20b034000c0100c102d131204507500440341840b124401c01c03019074591034482041c1c0044404c01181600080e400c6420112030300b4980300d070005039003031130401e50b05421000c403e2040c44115400c049812aa00704800c1080d11b4409001500481c00460f0400f1140e00d0070840b80803001c00070b00304000d0f90658405028035001d000086461402c0c0510400b0303100c40708030004500505 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 225058750 1250 225057500 225057517
    0xb1f02030906031611070303020606100e0d08040612050405030f09011701120b1602060714071a09070b0a080a051015080403081003082d130303080105090723 69
    0xb075011050011644c036a4404807003624480e90313401c0c141c5005800166880520344400f40140e0444804541517060020040c212140981402151a4100d20100d1226500e9400c251030325a0040f030107104d00c41d4408010071020020400c14080c3d41080d444041c0c0303d02c949000041c440000042c6080164014010b0400c48140c07000494143e41c2d5800003450b001c4140c4904a503040d07004070008000c00c0a41903640b407150340550041903550380d410400d480c916041c0e00035500b0b0a0301403042c0b00005050a40080382d43d071842c1c000500b41e0601c1c4481614081560300040c00099040c4404001258031081c0c1d25404002c00201085c00e03201c0c0d000941c241501908100042c1c00b035002d01390400d035001545d45002d9440b0b55156149503903240600840c0b280e0310b0200034070b601c6c020070074040d041101300b42c19400c1e21130b11300c80f140c9950000c0d05c0460065000c2c45107400b9095003500c041080c160404501d0f401008190b4041049207843c074030050844c20741c2032400c0d0020502181204508050f20103481002 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 225060000 1250 225058750 225058759
    0x6090506070c06111602010c02060409020c0106090e010204060c110f15070506010501080106140310090510080d02241003050f07140d0218070c0204020711130b1f020309 74
    0xa040c9444020b1003988012010b940c82403c00340c1009039030308041d04550804041400c0c000501c40c0c0b035070044400000d129800daa00c8082813101040c00941da01c0113060040f146000000c1d014945803130141503403044118081d0903441440b013042034503040182c50008030790140b502625404408005a520058128219040b19401e04500318450b4a94002c0240380c0c0a001203d00d00c5c3c2c0c0c0c40300111000c241c01d000303580018208001d00c4000d600030001442d004010000d50354075a6440e03265010413104212080c8040409881d4200980c50701440b402d600c40c0b0301c0d4800341003110181e034180d00d04000501401d4640f0307040c0000040d00281382c00c200001566010003641c513411a14110581e45070803502492409880204411120b454501003610243d41e02070202c20341c0001c13560300302d906100000c00751410720041c8441200103a660f480101107103441842c1140d00c1c54449818408604274543c54489100e00c4c04071009495071720240c05404403071940360444910074091030308030b003540114842c25810 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 225061250 1250 225060000 225060013
    0x60c0303020c0a030509011b031b05031603020c0a1e14010e030d031e1a01111c0201051905150909011107060e060601051804150e0403030e0d0903021309060905 70
    0x40582c8817004108141003640c1c1c104880c40c1c01022084604440c19004010443e03802d01601c0c040001c1d80900562070042050300d04200c090031101e0011f030000c08041780180c000182440462030f116901e080901004800641e00070002e03004011803107080e00400c0b500303078104160300103c0c0e8460010351703805040250175103100104103600503000e030501d54403040520382c491140312001c1c500d1340301d10f504906044614606120f02d440064a40081c0000040100c1c014031000300070711039041c18850146d0781e940d8000601c6140038549030385c1c18142c0e06c0d1003414480c2080140449030103494001c100c1c0f0b96037196101c149803107034140580108081060034100b41000f007034410500c01168060780700c200740c4000365006a40c070b5400465552155000d62039000800b00d001d88040e0810b5403004000183d03120200032460b4943c01143d0300701204580c114000381c1c0311107003001503820600480c00d00c6002030030420012801c6900144043c00d011201c106103950b960740c414280003042e001460794035085401c0d03515 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 225062500 1250 225061250 225061253
    0xc031c140d06090f0c2613061104060203032401020307060c1119060e010207020a090c0903021203070203011103060a0b030603030729010501050909010e040f050105010f0e0f010609060c0303020c0a 86
    0x2402020000c10081041c0ca01c43d030055209081940e06e482222044c1c1d039680b560340302521202d0840c0014151030990f5101d6603102800340032030003440039116039001941c4034a4040d000c00e40c008502018a94080030014282030746980000c10785100c958400710108120603940800ca443c4070080343d0518880c8191a0303413100080c14100d14030300d03140c000c4400348070b05098421501c1c00e074400c07484001d4106003106002c00c40d16195a2159036208e090340783c02c0d10600d95030340020781d4180902c0900d41c0140c100042e038504504d0244503110f08480300348401da0a600d080800145524075504c03406110700c0001001805545e0148104e80d0100d1380f100310150321400403a041064285c1d040c5121104401d20300002ca41d543c041d90913200d030340300c00a14008850382803031464161f0f0707900a0002c843d0b4560307035944100024028001e490180048a04480c0b0440c50242c029901500240883e005881184010321106500a1190054070320790b04000c220182c1e41d24045000b840341d0f40d50410540a82c2c042d050 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 225063750 1250 225062500 225062531
    0xf0606090305150603061603091203050a0b011e0c020109030503130806010b0702030a110d0c081b06070f060507110303070333060305270c031c140d0609 67
    0x4081e01e019030300700c4080354460000c0c03400c80392095581c40d5245d880800007030000910303d0f000d00c0540905140200344521030742c4c2c0741d40080075501d1044020076218801c100c030041c524811241405c009182c00c1100345e004a20031401c0041b00042c040420510010b102d0941e402109508002c61f80306080b2603030b4182e03803180c1412508090080c4603250189100006403010038205584000350020007802c0840c00c5a500c1b80d03d052406101190460b1610360b103040842d001503080c1c4010709060001d002c2208407202400150b580c6810214818003092207081c1c0460000d44d40140b03405c0c2e00810018580e143c806d82070f580d4900d1500300710490720000080040455060308981c810440c0154401c1d0b801b00c4400b00c0c9854139a25280e1107580c1e00e540d0404010b00307440b0f0782000c1d4200c00c02900c1c0300c0200d2900724441d03004d010ba5014a24081c0d00c4448038042905080000010001c6561440418842e071541b00410f040740302e160b150380281002c0b82102d14445035501600007403480840400141941d0900f40 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 225065000 1250 225063750 225063767
    0x1080a0f200307090806150d030e060c0d080907030b150402070f03020f0105160804110f060f0c0c060f0d0e0309090106080417040f05090a0209060c16080c060403030f030f0606 77
    0x280e0011340304240c002021400019410301070b00ca07118140e2106081481440700c2c0c058062025030400c04440c49101a07511a04003c08808004c07078003920142a003440054044240500f040d80303103070311241041001c541d8511401ea000f8018010f503644041d00140003501a000300d90014256404181d8501d04141e00002d8125420784a507009002d540d42d007480d590030b2021008050800300f070502d000940003030130642d1070254502004050081207a0642c01040240d0824000f00d0025180020910341d02c070300420201c080404e00311001c0e441c082000214410601507034665030803030303501c4607012003182c08240142c0b0741081019019640c1503039103080060050f04e0545050303c1d0175003802050a59440d8003422202501d542c94540840c2510744802d02915403402040704042940c240701e1003600d40d03549401400701d19a0034000344031584a104018001c0394560303200f81c3c0f4a42c84000c0e04a016100c580681d01145c0d0507081640c5071350103101003907001c0c00707903006400703001498040c2c003043c0301d42c001020 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 225066250 1250 225065000 225065011
    0x6060b070b010b0301150302030907080609100506060703090b13090f090303050f0f01210506090717030403150b040b0901030c17062505070c06031a09040201080a0f2003 74
    0x1405010390f030341d0228a031544401c6c040c1c10126001c205100c40ea581c047e400a540180001c02241c40150ba903504190814000781c071519030300d40007d00542140c810030b00805030404000c841d1249001c01d1981d0150100c940e40c800c1c1c1f412450045400500c039001042c9004c01000f4050041c480c0b035581a02d004018030b040c1d607045001c60310b0400420303800c0032014101407258680700e95442c803a90030185c1e070001021800e8880741e1048420012900092410308c21903005160138002082d0b00c81c10000b4031849d00b60886000c6129900070700080022600528040c4654100d02c0c40014100c101c90b0041406814401903154002400d00000000c200620200e030702107610307101402441060007800f5a03100c500554140561030048803143e100d895006054040001050170704a15240c0301d50384510560460364030a401284e41c85540900d445160500c035482428120380c80f40e038501e455400a01040d4000e0000009180d1703a0b0801114000681d01407402910305032000e0110342c8195100080e0355004440 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 225067500 1250 225066250 225066263
    0x90207051f1406040b0301060803070b0103120c080409020f04080a0c0f09090c0302061b15010509070c0317100528050d0302030d020d0b0a33050406050706060306060b07 74
    0x30300301c4400468400c2d0312410b86120041c0049480c1d000400011703201090651340c2c55541c8210001d5006406c0000b001c14521581e890309480d0300d18100300d14034200c900245418001000b100000003200001200c0c182c484201d001130b00c0c0e130500200d4136210700403904401c0d074030b01c180022442400305041000c0700700d40c505203544c10603d1300ca050803010b0340d00003080180300510040707040c401480d05402525404c020440000d11180d044203000c1d103003802d080c45462840d43d9190042c002410982c201d10303884015400c00c4500c114140d500100283c9000d0050030b685016a03020504607802d241400c001880020000300c689242d04020765003010034129529074912041000254a0603c0f041d01c42c074241d0560051400c0007565011007000c0e601c4805940340d041d5684c61030100c02d6a941c0f160304003608008540381412001c0b4a1490f118444984000c0039114840c3c1c44c64125550241c2154162826031134401c0d00c4e9050340c54800c024200c40c1d00020105420142c5c00b0a540e08c1c0c1c80080c204045c000c64 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 225068750 1250 225067500 225067543
    0xf0e16030b03030f2203120f0201091e0c050a090209211c03111c050a060f0501050a02010e030c0102030403140a0206241305090c0a08070302091009020705 68
    0x4080d400c407051401c44a80582003485000248401d803005004605840f624101a040c207029202424400725042100d902d10000b03500ca920a074000c242c0c0081d21000d000801c0207800c640c803194409060b210020006950b203810000410500c0e001a030000c0c07070040c0c0403004994841003408041d400030381c501406019040140801843d017140e2003a10480d40e030000e4010300100500840301d02c405028141c0625890b200030704030448031703040180660701807003464043d84044c405501090781e00c00b17041d003044281064018086100e1041000b000c4030003d00700b140e03075901c030310030140d014040321a12151513000c08100700c000b44c070040d00154425442030340d9410606031154441c007042d0103841040c00059100c2000506080c89006060020200701020300e40d04c04044400107140c0c0050148a070800d0b0340f88c500344001420100206207070b142084604202081c104018542e80e6140da100c043d109420030f030080750a40a01440c02d0001d850a40ca0941d545c240c1400e2003a81c1e40700c1311885141042c0c004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 225070000 1250 225068750 225068791
    0x51006030b03030f0d020a110a03050702040c030b100509040b090405070f050306040c29030709090e0706021c050705060f010f0f05030619110a120e0105130b09070f0e 73
    0xc011180c0c04d200c141c102505004080e0701240003900a44480002d1052003982404652010024045000c0c030995070541e40d14840e1051100ba1207122003150207260509960540710b907940e068601c2008054600540c0700e4400c0c03000540070740019004e0a40000b0103000b032109000d008551303001030300c8864034503080d641c0d81c54080c540e6030f07042140c002d07049900360101400240e00d074240c1c0c103c0f060102400420407521415001c001c030390007030301da507408142141810060001c540c06500042d64204014001d51850214043e45492400380c0b104048940070002c414032600032403e55403240c1d00001143d40514004c2022000303c1c400b8001d5040040f01c03048002044e288107516841501c201602510846c0c4a1070f03540115070311000c06034030a02d80c841900000d020142c3c80640120150759407a12880b032900d00c141012600342451540c2c0d180d05020800150341d68802e03904240e1544008a20b8403a80e41a000c2401c0c1551908440006203480c1c0b4001980704041000c03074042c540a01c0c0b01460074064 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 225071250 1250 225070000 225070003
    0x3050c010e09042015120106180e190212070e090103030f18150201020702041104030f1b090207060e15060108070f03140a02070c0e04080f0706090501051006030b03 72
    0x204104150b001204900041c0000c04026040c3c0700d40300c0707100d030f41c1c01c10882500010311040700310b03403403983d0103180420302c180c08013559a0000d00404140c149501c2900c80302c48814030200d424011100e0555000d004207124142c1900315250b0032511b59030031920741c20a030003034210320401523603090700041c3e0000050a1929080d100705048981c5a119481015039252096451501070318007001c001821540c0000d2a403088413060700010b40c55400180d03245140d2040200300e8904030440c0110038000c1c081880020760b9844210092500100f00360070764000c0c100340e0740858500d500b06004280c008541501084501d400c00a52402140141d81000d502400844203800c81110820b0005501383c012070011030017900200d19403200c526000c10168030030042428034010544115030025800503a00d0b06000407000500302420040074064a03504081d200c2d800c10303006005401a45650008001d400c020307042c6c1c03051200d075078084000c0c003441ca06407e0700a1110b04038170030340000c2814070814149c180360 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 225072500 1250 225071250 225071267
    0x50102090a1a0711010519020606130e0c091312122a140c06010b030106020607090f050f010c05150417040501050d0c0c020d050303010614031e0702071a0403050c01 72
    0x41102018109990f0f500c1c0d55040c295440003150501c441000b0000b03502541c20f907076421800854000b021182032079000d0211010003040300030125843d001404a0030070f0301103204421554103d1707054045841741c1c0c1004004c40c0c600400204440700300141d104200790420b51080642c0c0c0000c03010000b40d00540e444883d4800c030500590100c00c1101081c150b51401000c0c022b02d040d006c60380d258141004510b22520700002078001c4140703020b0100c0104207050b810021554000c0c80c40c60000c5c5030340d2810f201031036151420701416219103030748113612089900c41da080b81d414a4000c0b0031030301109508105d001d070f43c241c256010358080420004001000007007400f19421144103a403010310b00881104140014010101c42104010a0400190140c1c0e100c80c8003107034460090010319581e500d03181000d4818500d0100c8410819001e10410440100403000100004020b0140d038120f40d8601c60200d003007004c241c1001205010760060f004107901c1d00c10140041c1ca110324103c500d02e480c0040155603205 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 225073750 1250 225072500 225072539
    0x6060402090f040c03021b0718150e091515040b01050c0d0e03030702150a09060e010806061806030108010c0306120206090d0c030b1e130b0c090303040302040207050102090a 76
    0x100c0c40c082c80815041c66407282e84401414a40107003442d88141d0740f4500d10454911403d000d6001010a0000d01003044c0241052031101c041003200354100240070381003461900c1040401c6000038000b600c110014040d092a03140d55400c1d203103141ca02504680d43c080d030601c803454000c43c40c00c511084d80d540104203c1701414801c60081c07254042d60401101e0344810450f0785034140c00240a08001a101d42c0242c006004090b03c41c1ca0715241e00001c001c000501544c0000e040010b403401c0402c0c2c6981115010383c00010a0303a045a41e0b400000c0c0340c00144c0303010700b00c3c9a00400000000282c22806501c0f181e070382404ac1c0d8040c09030a07a101c6640000107001030010f94000c03010001c840c071034030b869450325000c940305519150303030141c2d6500c940303100780c0c41102c0f01d074080f0406440f5600e403816001244c0da4026032107146800e0b8885a0b88580c1043c0b10000c2941442d4030000444c80541d42d03040050728000d5500400965889050f860101c1c007070340155001074099a000d00c2d001c1581d28940f0344082c07040 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 225075000 1250 225073750 225073759
    0xb150904111504090c0c03080a060e13020d0b040503090102070902040e01170709020d06030b06030607080403030c0903300516060b270609090f06180f0607110606040209 74
    0x1020301d1010001c48101000c10200410420880011050800d009514034290f590310340c100e00d0074680c1405000144020011b9a183d8035006051001000d8020603503040000e1140e444800840387c40841c803045641d030740c0540404ce07410100b10410030000b0080c1504075007a82502c2d42d096840f00150300f03900840c029402066070140040c00804400300040c03a100e01300d1000c4801c5a640e80441004990050b45001e170403d4882005000b4801440025a0440d0040d40100240d107041207000f440410080c0008040640310700c056201c02d0f200d040e4030400346810030400c8165050341c070201070040c84031784c200102d9000054001e840607070140f8141c0e40b03d01500161030070f062803c0d50fa0480100070046010754440001003170181c828641c1c80490040108548200800c0e04000c010003036400c0c2c0c003c0c0020721755804034801e119100b8000c60010740126100c0400c00b48159031940690605207844030082851040808001000b9807000440312070031b680300140c0301075840301c0080c070003a442584c514a802 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 225076250 1250 225075000 225075023
    0x7060f1a060c07140a030c12050115080a03110c0a1707060206060a06080a0f111b070506040e06040605090f010e0c0405180a0f02180a0b071e080d090b150904 69
    0x101802c02c1006213852000900007084076850f80d4810741d0002503500070811036040807410004001c0c0034817034041d0210100300100070303c500e4420a299140c480c900d000707040011125554030428400c1008241c2c503000203012116158503403140c200761800b01600b0245a200d039a070006840e070300100790305000f400c02920720f500b094146042900d80d00320142c06c65020075500e5690f10001402407103481204595928400c0d80e81c0208040300c102c2012004100000d50410b090400882c1d272014103c9080383e110010340c880176a50080043c00610b41a0700450b000805602044100500300c80050b047e901d00801241c91600c4030381608040380158001e01c1c0d0400d000340180c464410700c82280f25800f04148502189150080704d41800381e801102c2d031b50840e410384510304184c40c603003032816070003424031580e05505001641d200c0c00307205040745051000c41002c1e40e01c10700c00d100c01d480407200c060501d08418041c449507860501883c2c0c10803100703004000d80c245090400c0b841d2501c0928040c54000100310503 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 225077500 1250 225076250 225076259
    0x31e0513020d1518050f070f051e03060a091e020102030307080a0e0d050307020712020609010309030c06020f12160e01180905011503061203050a0f0507060f1a060c07 73
    0x5841c40025810b441412503150103001240c103a0251854046640c59000c4002c5918601145404000440001c2d187c01002040c4490300030464181c0071900d0842c0e004003001202c10807051068120110b041c3c141c01072070704000180704240c21031006240b050249251806241000020f03402001c0300090041c2c00400124162031320840005800030700090002a01c00445200c0a00d045038040b110008142d02008003c0c15980511070b4400800700f074443c40b10328140550005056200b25941c640c1403594901c140da05062040e6000100c80d50301050856854a00f4002d050840d0007848000cbc081c60112070008104024800104500685a4603200c402440d4580151541c1d02d03520115003502c50310380700009804c0741c0ca01540740200302480c64050180e030306800040980d0460342081d10202031009a0341d00003031f0f200e01203904510f0a0701e003016010f442c0d82e0007200c03680715103400641494108014084107a00c15400480301c6610f901054014002000521100b03000c1e514207600c454116070001c01 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 225078750 1250 225077500 225077509
    0x1020f15070c0c0b0a0f12110304080f0909070203190f122a0e031207020604031103010603060f2f0409050915010e040b07090b09010c060e010c031e051302 68
    0x1002c1c03840b81c242c401e8203903100c1c1c1c078040454000001c108000b80304200c0459900303030081010311600b04011018402c0d00c00c0e079513008105210240c0000e04081c4006940c2090b0728801d0145c800c01a401441c0c85403500300494025583d4000a10001c000e02d2000b01c00344c18140900100150b9020707a031511070340b00703041a1003200102500c4006941c945008403040045048003004001c0c41c440940b51005034407201000d1500d0400000c0c41c81c1c26407a0f081040001503aa84415201140d5100d400c0022581c030b20780c0864007410156000602c42030504107801e0310707001c13a03410810000703001041c403580102000c02e4140307983c5c81d0511035001c0401d04200c1480054a9604907641c44007404c0129082c60401c0b8030380f1044968264414041841060f050204111002d035038280c12501d149440c0582504000007000503120b1740841e02d051004100325203041207040d40010304a034001c080200511716074480702401801070b040840500150380103454442e14036922449014240700c103681501c2503569401d20 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 225080000 1250 225078750 225078767
    0x30c03020715120b0d1e320d031506050a0201060b030a090b1b0d1d0706050408070609290408031306080705030609040308061212040501020f1507 64
    0x1682140540803001c203030310740e80d038418003207a41441c0d58205003100d0b059500030440c0c60310b184491180c81d08400d024041203414120f0b10066000ca00c243c00302c040c00b0f10340681c4c4000c60710304140d9220f0740030b060800006603110144141c2c4c100d0304d05480103240106001ca041f188581c1ea9000e580a00c071805100b000d114a01400d82282280000114a51515000ca049030000c5403905160382d1102208810449400d410b41e4010030550b90018000d8404010f0305524010b03600344c40d18a95451082032900886101e1009907800c0e2982900c1c80c0750f403a808010940c1e4401e0103000614401c07c0e03000a441c85c0700b2000d4a00311100440302c0b215030000e0384204869a80f00c04041c0000c514140000300d407440060002305880c02e41140c0412966180580242988000805074400d008091040113a070740c81e5010980e034440c0d4186400d510729a0b4043c001a4624000c44034604030b4828080e402d09030004d110010003d0300c5c0300340c084407203140c8400c0d20716944d26280d452006018030541d0120701c2090007060074 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 225081250 1250 225080000 225080003
    0x8070201020906130906060203070b0408031e0a0b040c09030b0f1b0c030403030207090b1f050d020703170903070812070306030f0501090b060a0f05011128050d05040e04030c 76
    0xd0301c1c0c600c108000440036080710004c0c0f102c030505114100301040562050a00420142c0042c2d414507405844812041c02d00801c0907208c0b0f60000300080381c010359401d0300c4074896155542c1c50000d060072030f0680020110b400b5000d000b01c0c9840c844907a05070081041400b1a9400901e00c0308950700c0342080702d040140a006810076118003080101044c031143c01800345c08407004025600c40d8610b0034000e2412038240d0000180910300030300300c03101d51100c1d48000410801c0c000d40f142403e1108000312071510606036001c400502c0800c85104060340592107a207d0b0441d00d140032031030385600d21049e4803486002e10040a60300200500c400304400c0b0800c0070780c0b0819600300041d9280d0f407510389218841e6100e10454040c0d540b220f0180400070a10003a5800c0141030301c00901c150709100103142a003081d1b02855040c000402320481c056242000710b080b034251610104445043c0c03104c218a10b4401110b011506401820b0b5210f046901c55410b480c1120f004016400c5a521703280c0301075848a204a00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 225082500 1250 225081250 225081253
    0x1e0d020f060a05130b070f030e1302040906050a080105130308090a0b18100b0102060a090204060302100c0201080a021e0d090c0f050307050301090206030a0203060303072010080601090303080702 85
    0x210154540d100e8015007451480c07034882030fa0360f503004c09454138200702d20340020010540c03d101040114910651044c4829491305082001081c04c3c1c001550b1a0a5201c070542034600001d40428101011303080310044802c15a610007101c0d495004003403d803103040303907084030b40100380b640c02021900c1024169046080a070a880340c0c04200d840300d892288046414200921007024180e2400c10104007800f00c421142d90100300c05c1683c03100007034031640058001c08100303458892010666030b655000e040110b500501c030944225021001910510010034282d0214011000041004016008850581100388440301031103000e00c600c5c0f412600074107140154030b070b9a00b8222002580c4200042d01501c509100365103005c0c0342a003011714000e10754022501990400304003d005803240300c00d49420101c20800580c4950315800468514001e1060143c61910043c4418064103950300920003a0f0380261042401581c0203d0165284041640c41d14009100340d0400c00109104182513608100940f0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 225083750 1250 225082500 225082519
    0xb0c07021809030a0e10020d1808100c14040e070f050c0a05070305070602163c212001030608011a130e0d030903140a08060405061e0d02 60
    0x7030074a415408440c035a000c1c3d4070005901907416041003541a101a00b00d42c60100075080b050000d4581c00c0408075482480301054500c10550032807001c0e9406040781c0001c4554044031414a04003807c80d880200b000310b17500e0b0b031088d89601182011a03040d10040881541561036291080341e4100060300c480c0f00301302c024448803c0c080c4040c8221001036000300001c02606007541022801c250041d400760301590700038040c20381002028050001110510700d00c0481038a04072000108400c5a0091814444540755a0f1440164002000410740303103080b10f011810081e07001c0b42c0c0720f542410100a0035200c800d5174041103c0e1202003403805200010715000c1141c0743d5600d401806e44a50300c45d03455000310108592207640c140705c9400c4410b544010401d004001c005801a0b80724032000e03001d4010140c4440003002854065020f0200d0a01c50812182d40c030301c0c141e1001098004151007280c8a1400c00c0c000c595503242c0300465800e140203220484240d000c40004001940480c0d0404980008828 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 225085000 1250 225083750 225083779
    0x16050102041802070b071e03050c1308060a06090b15130b04080d08090102070f02090a06081225121b02060304050a12030905030307080a020c0a05011d030301030b0c0702 74
    0x180b900d00840044405601c86019140640400100070039120402401d001040d0105120415009030920b0781d060000c2e1742e0310b4200c02402680324031594a82c80813484600000e89100000c0c13418400c1c05249001c0241e80d444900c64006d44607e5018260b2090603541442d0315108030764001c10051602082c004061542c0380c01c0c41ca0030750055441303804c0b1390304400002c01e11035400640c5aa40300b44c4150003149048120b50341c2110704103084802034040c07241000010000100c50344888007500f03075541151000c2d0407000480d405940010b00304d1030307441d641882c5440c601e000c80d8203110720694000440f011507107012000b180c4051804821080341c06c4903051980150316000300450007030340101c01420a039441d9042030361035162402070050400d468580000c003c102e001c07090b07a400120500d0001055141c5603040300c00382c042e00c1d110400902a0000c40010070605510440d101c4d203000300d440d4040f0b90710075116912400700344030141c041c40c50714000800d0f165054004060062009007100041e0828 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 225086250 1250 225085000 225085019
    0x81c060602010203010915030b01090c11070905101d060f1306080a0204050c03011d070e0306150312180d1a0411090a1b0e0102010e0a0c0f14061605010204 68
    0x250301410250f503002005120030700c0c090160760201030200d11a1080d40b0b1469035203801400c01442001540d640c3d46100c03001c150301c030300000109603460500b2111f0594680525030018407007038501001c0760415103000900c0d880101c4e5084511290001d84505941c0c400f02842921004074503104d03880310710740041084180b003912902c000390100b0401408040781c40d105001c00c03101c0203000441003072000d200400c40c8110080b44203000e00384a04d00d012494440160660741408025180c1c0c0d03140c000d1000300300b403034851940f1000741c01600310101c5e1441400e402010030b8600ca0419160700040c03070b1210700306103402d1400c580000d0364801c0302c107948050000502c210710700740309030380499280c007a4500f80092843c000e00e1194010400c080304000103005c0c1d800c0d20307140032505010700061000f0000092043d078000e501624100443c0300960301d41c10803501d42085406050f020300080c0302020880420702103442540001c0e090b5002e4401c41c03400100060401ea5204003e004132038540d020000810940708 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 225087500 1250 225086250 225086261
    0x31101020d06090b0f0a0b0a0306170d12020306030a0f020d06021b012a0c0501090204020a0e0406140a0b071704030f0519020a090c030e0105070513080c030a081c 71
    0x181a4000180203060050348030540360503501d428411482603004e201c2950b07641401d401150701140c0e809a030340c8e21010007036000d0100c0c3d900c400042d407920402288000c8010960500c20205aa500d0880c200385201c01400c0303000545696825070f010200f07040000c1c035070004055801d4002454410304e0b00ea640c1d50340c0140d80c426242c001408000e0548807a141c0401d020740c0180c410900041c0c5003030300712031802d0b0300000d08500301101001090119601440000e40c042421660003410540d80c4414000001e00707030040703c046150040d8640000025842007401c4c041318000c10040069401078500744075840c1d0f80e00503440a031a166410101c8003080e0310003e00034001540300d00804403011900f07091071070a10480084920700c00c0d0b881c104a4005076a44002c200507601c0c6008005103100c40080200c0c0180f000c50342400056207403005004500f5001005840c107840c0c5050100100784d12198440e03202c284ca001c21542592000c45007a000541c3d100280211503c64100004220481112841940c9 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 225088750 1250 225087500 225087517
    0xc05030406031b0908030a0503060409060507020705150301030b010e091c1809020c0a0206180303070f050105070c03080a2706050702010b06042d05060415090e0c1603110102 76
    0x9076120b0000105510380164141407000609001310b80ca840c025144e81c491290382e80c44e10811500000050181d5110380c48a214540c120504005621741300d0310107542c0e48030074080c40388610700301035094011810003401c50307050ba0341c40049150180d1078646080760311b0a01414200c801d015001000301d412003209181d80c19060280c0e21040000041480c201e007030b44d600d40264484a004004030300790640b0005da8131001c141d050302c62b565500d00c1902806841c2c04032511aa515010005801003804000380305004802d000e078000300001d03240c0100170740d03102e4089003005003c1890800000d40e07038000b0703030300c061400c015618000d14000c0700c9000e100b180c41030346242200c2070340c2e0b80c105200c400d0358244511a88400183d80d0503141c5400d1524201381120001584816072280c51420380000840501001c010040681484d48468480c64414000f000b100503807800115a07410015084240e036a00ca4010072660b080b061500e070081ea00703540d502c1c03c090000d40038012000c1e4003000740c1109200403c0040c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 225090000 1250 225088750 225088757
    0x50303030c032202010e0d0302010204090c020f010b0303030601081302060f070624060e0d14011e0c050a080105041d1c08060907170a0605100903150614010f0c05030406 74
    0xe03d03140300d25019003140303045001d820901c00d03000480142d0308144c0e466940e07202140d244511a07201e11301240648039542291800a09001c501c4201e50b80015864040b405920020b000c843d64a41c20306580f40400c0315000e00084084000c0f4900f5800f107154100024006894180350090a141004a5034007500b011030312103a594090903884000d0455214081c81203001940d15149050001010a100301980700d1041c61540c10260400903c648402480ca030040c000303100d4498070340802c0401c040c0501649590034140303200840c40e140301d0001c5541e09034480d2034010090f42040b003440010185e40b01c45100641e40c90f502c050100404128840e4a482051a801e07143d00d075a40000b05030042c0980b0481c0907451603c00d00684980002c0b00d0719954490b410050940c2d0b0350321034160302400d85d9a000c1c5030403000d114080300b403240d401000d04064901512941d2000380f50349100c00704840c4c15100d01141250056a03c22403903200e8001c42843c0701c0e45207402c4402001507215141994001c3e0b0080001c0b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 225091250 1250 225090000 225090007
    0x170c0403060506220b0a050a030b01050907020d08370204080c0d02060a0e0d080f030a0501121101030f0605040213030303063f0803070206011a0a170a06050303030c 72
    0x10840345014071035018009032510707400900880a0155a43c1d02d00f056404c0c02601c1e000740050b5030710344201d03c800070b03c0010034841016035a8104140004000c0c01070600800b94000080d0b0514000070f0b05481600482d5120110713681c4240d81e440d038080e03840507a030b0080d0005410107821036024003040068130944400040e616464650030a24107841202c020307011700d80c003213001805680c5600540348021100c1c1860442114078100041d010040424018204240801e075414400d84010182d841540101020851641c903240d04d079100444030170300100048a40300260f00719500c2a00440710680741200081862030711980000d050380c012015484102d68242010024150306025540050580100783c0c1c1c004000c10b8860000c0940e080360904044520310011500c140b01410300300b0400d074010701e0703a079260b00308800f000b91600420701c16212060581e819a502000b403150407076100c0074454a175449103081911000c5052103006219541440e62008000b400341c405100940c030409030320303c1c20741e039 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 225092500 1250 225091250 225091253
    0xd0f0f0b030f0f03041815080309031009120f051303060e0c060906030a05070504030f080a0801080708032a0118330203040f150902130e06010b0703170c0403 69
    0x15011640c2c002c00c005a20801c40300194075008000c4800352003101c06082000b400c040e05d2407001d45201094160080a62480014401004400b07020940743c202c095610031060070410354152264590040c100001005480411034000e100c04528123420741800781c100f080d41c141212032040300c0c0c0d0041c0c81880d00d07041171041e000814001c03900034030350440340c460400e1a000701190083c04010030304200fa942d1040461201805601510001c49c1d010841c6555030030985807800168122140d1207021881481c008208030401044000c1600e9216001394105034406a10300e024828101ca0481260310301740c03070424000d00030b0098582034201500900e440c0d1216207441d018951000741810842c2e51400340c00d00480d085401e140f0445c084103000903803692910b048c441c3e8940100c00c1c2c0240000c18219651854a220b90807042c88540200c4040c10b40c81c451448400680d1142400400540c12020045c00011440405091b60a000c2e01e88517540c0c00901440c401e036076406803405030040402040400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 225093750 1250 225092500 225092503
    0x7020d03061e06050a0c05060a0212070201060302010f1d2e0e01020705040c02150a050709051e013002190507050a02060a11060c0c010506010c030c02060d0f0f0b03 72
    0x100a0007021115a600d010304112402d2010302400b8010800c107002501c4561385100d03415070440b1a40240076650203051002006c0c00a50140030007025114a040002e10f04074018070920f0122074060b11180c04800c0f1003041203420a640030402c8544100712100300d0266118245c180c80e007030405c40b00d490301018152407180442601e09001100700b080c119135180b00da980c08150401243c0c019103001c0f41003482c2070303c02d070300708015100100e42085c100c404012200318503401c400e0003020f80d03480320607a154444003403040110340510007000004031603071480c0095116030111000207a03450041c0003a006031601c00f40a0803c40c2d03103c03040043d0040354584c014642d8810b81a4a111181041072606c069951200d80f94103858030003038483c400106548a02e1802011010014074014040e03038900c2c0341c03c00031643c00b504100b0a000c1c1c15840d050006500d54081c00101c083e281d0581c03184050f40e07015508100055002e654a52100c0e5200d84091030180814010603c40d07408400d8042800e00303502d000e05 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 225095000 1250 225093750 225093761
    0xe040b0a03080d05070315060912150c090303090605160b15130f0506060a0f0f052a0c0904150f0207020907110d14041802040807030f140c0a06080604090b07020d03 72
    0x9041c17407c2c500200f00a4250020300380c008468000d8640d6000c4040d5080c0f5040600c00c4c8030303900c0c180030f080c20481220b1f190300580340015a4402d0b00c40c148031946908085480c2c1c007d50341000745070303080d0100315008204c0d9410017550100c00541c2c091646000c80c000f007984e0380d12250050100356210300030400e062a55000e074590041c3d06031916400d003811840010b00740e00ba20f040360403d0046420746100c03014800d9017190180d07580310900c2a01041c400c070400301c0301c1e94154981002409002610b00c010b150164400d03000d0b580054030601341000703241d95a8010300d140207a10144650030040790005071612207660b442460785032105900701242000481c1821803056000d030400400c044c0740750442800390281c07419038040c40300480844550b011004000e12460f0044405071060690000c1080142070380c01c000c0600c40d0003e12910008100c09c40da47d20340040b0815403041103004244141c1c0d06c124186648410000c002058504041d12034048082065601000580015810390080b42d0036000c0d4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 225096250 1250 225095000 225095021
    0x190f03060f0b0612130c0f0603050c21070314042001080907140109030b041119150f17090c100e0a030f150608031b0606010e040b0a03080d050703 64
    0x14032009000e0000280144103846900521440300c130f0100d648250482c105060782c1c3da000040081141d2100f940942c50348851095000003824040040e4040d8506401c0d00e40d15280303108810b0600340c04902d00d48080f40e00034400010150f0b12a80c64051032007100486015500401e5000324103841030408400d00c94072400c406050000c0081841251180007441004480c0164881c0c6107143c092030040303c1010003940003400c001da42c18180000e0100b21100280e80b41801c440400d4500c0070701112a01004051007054030108003a141c0c0d401060040c0e02032201d4a98600e000d0503080800100c40d100d08009070790b00c4265034041c00d540c0240b0304020305401e07808021420001d00285514001a1603400f49020080050076111001400c000b40e00d880b00d15182040030041c0901034030f4501c03981d540e80100e07001451022448660109961002c54024020481139441021700e25140e410301010b05210448203420500d5034800201280018020b46007900381c500b40491142400100113080d03400c120403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 225097500 1250 225096250 225096281
    0x1080f190203091e070e010510020307031d0402070b010e07030209030c040903020102090915010806060c0606040e0c0a080304030c050a060813020109030f050d0f05180f190f0306 78
    0x9010460110020248603030305140405641e907070360145100d0600f407124940b000444544402d50b5600080421001d00381c0300740c000560126030f43c41e0704001d046540c6d801e084000d41c00400101020901c02c10103007042c00820b102d00e1030800c410070040b5080740d00002c4252084990f60b00140308081d5540c000e540c0144a500e010350070001441d00087e150329045403404c1c421030346c810000b8100344c003e406039111200018041e400e03a2034690810b0200148072602e00780099101c500113072403450507030b0030340e0f1284000100030601582c520b400e0000915181ca1400700901c11504014590380d03c28000c040a0460b00000d1500d0702c2c81c501e400202158039401c07251180510000601016502c200c0c1103a01403c1c1a0395040d408446000680b159960360300042c01c046480141501480700024030400c0140c056a00c002d1007400d00a01203d6900420800000480800c81c0112142c48d180d5400d030306108006003101b01072580c001003401cac0b00415503c0006503050f5a00104140001446000d040158991 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 225098750 1250 225097500 225097531
    0x3150301020405031b0a0b0309030307030f1a1011010204140405241507060216021c0b060d0302120301170d05040b09040e100504050303060f0a12022704060b0108 71
    0x100041d03200d140c401d0310340400c81d4165040c40032680d92000e0810060401f81da0956890524a01aa880381d2003212460f01090070324695000d8400b00744603805150f011443c0070390b04c1c0c0c03505008001c1c0d24003140b8200360030004e011594010b0506c0a100a10041000030202200e040304181030005645c030060124400032602c400100241030380290051451030212040f91104028554081540c002c1c0c1801400b82071000c01d8002100300c40f103401c555054021203c056920214408003c80104001002030507940c02c1d0021540343e081c44048010481d2190068400c170805180100e00c054200f64000410318144400c03100d40d070b0354244030000c0036503864a400381c50642805003043e56842440078290058cd51401d0031f43c1c0705242802007862803d450300d03060240341002c0c00e001e13580e90029200e041c8070f0040400b40300c41902d0500444011500d0303000c00207204465075020440c1a1004222200c004176209541201004030168168410342c4501d0380010001c0348800018070741c3e14018589030b03468240d00d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 225100000 1250 225098750 225098759
    0x2060610090f030308060a090603080301060e120d05030901020702060705010c090611060609101e060e100c0b090a050a050a1506060806101b03030506041103011505070f120302031503010204 83
    0xb41d02e502a2030305410460391948a9002055020040b980240d00c294607196010040240d803000460483c2d907581e4403200c0c3c0150f01c0c1c0030002c0b11705141c4945e4440d54841500e07551100d001e42c0c0510b0340b0200e03150005050220540104e03a281d07000c10740490301c1c0d95503440714614581d0461210005020340d8500601c80c020705112550340e0316409015144124400310028642c60425081c10740a02203020400e040400c001511105041c05405510007103000ca00c400300c26410a5100e001031070a03184d4410150000c244c44100c40403801502e030680902588100341c1c082034081100c0d00003c0d00c200014031120780c4908001030001400210180300c6400e01c4020000306074018500d5402c01001c584000850308070500c103907003270a2101819206d094032100c1501c189a0941c0c44148111015542402001030015415015100900030104030300d541090200c200f62051005c1c100607032240d0b00c4003054886075211106000c51034028070340065000410082e90000791a214403075a2001cad4025400c082c1807 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 225101250 1250 225100000 225100019
    0x20a0506040303091104060306200a020a0b0a0605030307031d09060d08030721021b0a2a050a0909050114010303081801020f04090204050319020f060c0c100206061009 73
    0x141002d01016254401c000c14015940e10051395003a0040c000c10100e41d80f032500c5000341c039520018000c2c141950ba021480309410804689450b075990b409001a4101503481c0c3c010b07441c0103840a402d440ea50100429140c4040008012040c043d44400361903441600d00392450074810380b030060041d0910300138001d95031a081c03148a626948501c1e02c944954940400302c2d409800c204412000c0403410442142001040d401440038040c2c03001c2c1240c01c180484501541e501c0001390042c00d0850080000880d4802c0c008850105000030700c842c001f65a0303076400600008110b4101e10300507a40c800b1418101300013403007500d5050700c3e841380c01e140c0ea49c5985c4000d0001c600c010700c0c80c0182811600d20001e41c8000b94121081301c18960821030302c0e1900c070f8000e400250000d018040c0a4459a40c9d0701030b13542c0e00030501200c0c03583d00801d41c0000c03403851400e1208641248180c44454811b060040803256a400150020088503038028000b40c904103080084034500101e1442c2441024103003485245c04 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 225102500 1250 225101250 225101263
    0x30206040521071707050111061f0e04080301060908010c080f0a18150e120910050706090605060a05010504030b0c13080609061905060303090d06180501020415020a05 73
    0x20102d403021030a203120866019241000c402501c041d0040301070208030402411800a022141002102c1d0302e2a240e0005440017141182d201005a1161000901c1d0500780300c20701e0846600c00011081c055035075560420000000c0d00c0440f03001d8008801400a180d0040b0a03100815006000340f00300c80c0c0b520006011610041c10f0b00c2c010400c0c18000503240d48541c0c1205905030b080300100c031000d03005810322000410f21100541e00c00740c1480d0f00d26400c0100082c81a0b00d0700720700d078100752600144200304144620510200d60038407005108c2580070840510884207003a00461000ca040c0c81d0000800c41a1080c6800650503c5805c0c402417002c10200b01205500808502c581030b560114951702c508005d01550054442d80f040f00c0400030030660100f0304901803800c0c20100c4084261a042d0030060303a504803510741d010303030082c000c200540c0f402c8141c1072401f601580f400108140d9024501035030300081c8030243c509079000607081000d90800704203142040c903244041d140507151561666103801 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 225103750 1250 225102500 225102509
    0x15050d0f0804050d050a110109081b0a0e131b08030a0503040c0b0a0c0302060601030b1f200c130b150a020708010c0903020f0d0309090e0a050703051501090603020604 73
    0x209200d8540080200716400c640c0541002002d09003c040c00b8941503030740d440c0d80c802c115007078910000e1a01c440e50188070500296104840900303208564400b07410f1040c502d0b04d00056004140b07400014124854052544c0204c41030421034421002504107040c0c841e050340700008401c0100300081040003400f1040c1c2e8180a02d40c82c4ca6a603076100d9040c0140c10500c0703500000002c800000d4850744d140d4010350111801d51003a001e95501e691000f00643c1103c0c00b0306a11504840e483c0b40d13000c8125540c080285100d00e0500f04410301c0c202400502591034080440904182d20040310325415161000c1000e41043c0804018403000702400040303801104a80125400c1c503001003a47c41d4400c1c000c2c4500b0000d810b16000801646145120040c040b035980e01c020790203000d174001840c2d0a418054aa10603490301511080b0800c1e2070f0032281030003400150055055401240c2002000410a11001d4021405140200004100b8800c00d0f580100c06900c40d04045282c124104010380394141990b0884 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 225105000 1250 225103750 225103763
    0x34080313050a1b0302240301050126150102070807050607030302250c090b010512040803060114120a0b0a0602120f0d020705011a10021005090a0c0906080115050d 71
    0x600e1145001c51409100410040c00400c03a0100d0002d032040103580034085a00844445032116120030642000c51070844400f42110f01c1000144900c4d4010044d55214004484007800c5665102c0720040c24688291a00528070090303078036840566a04100050140c00c400000e403500d40c3ca440002107407480b4240009007459004250300b02c0007a0b24022000705072034020b841040c5014249030040c403401d141c2c0298003000386400b070b450045522a6041d62a501e0544208080903151038031140502d40000f442c00d030411074007410680c1c6040c1d0000241c001c40c2c00c200404130b02818865000b1080e140e04118050290030869000c005c955400196030840905405440d55503190031a03008445209900d100302c00140001440c00420005506c100343d1001d0f5520302c080c135010540c080041407103140b05039070f005070702461041a102800350f118a070084190f004a4840c0b030090f9894004a034503503406102c510750389607801c0000500c03e010b400031403001308d91a58051801d140006290a89950000c0c1c4072 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 225106250 1250 225105000 225105031
    0xa120e01021b06070b09030c100203090c1908010f05090c192c070203130e06130509010603020301090803070e09130303050a1512020f060702030a030c17340803 70
    0x8a445003803c488500350010001d91703040c98191003050341d03507110142c2040f0074410b02c101c0e8000c052803072095034040c0031504080c1925000c2003042040b40103004a200300c418480400001f0001310900c04d000c908000c140b00400c06160140d0b549003086584480c1ea800380c1036010380340140b00c070601d2207107003130b41d81f2071a2000428048032550501e145407402c0c5546400f01c00b2081c0604950000050814403000a4140c190315484402e1107c042c0b400340c910b1034101003c03181031040c840a5070001a4016007000000031065901d0300080d00351000c1300810741d102710740001480403841d44181805207200080c1c07070030005803c1c402511000c01500d403401030105580c40b0b021605103002d40e0401d84405100c0340344c07100c03143d44400d014003408411103022841000e4030112041e4070b040c07101c04c1d500c010f034000f00600031100d265141a11151481e00d82110303011a00307160b1425429200b00504035105103110160444d00d501c5c000c3c41d201c42c0c2034551004200751581c00240000c0c1604048035845640e55420a00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 225107500 1250 225106250 225106303
    0x63201090e04051c0819140c0c0111180909010203010b2a1c0e010c3804080403060b041401031412030c0a080610020303070e010e0904050a120e0102 65
    0xf80210300452094036122030744d064080765030108032079004010300e80103101d100003c41d0b840c0c0121840d68070441520170491002480f103840f08001341602091a50001c920350000c4540d1100e02e900403588401224031044201c0005d0402c50030445c1d0010186000310f1130340d4100a4090080e0248400c0b030000c0e2070b41000da03a00b141c1ca400410707002c0403030643c0440d480014603103414410a0581c0d2500d00004400300c00060580d8481c8a8020610350000e1005500b280c11038a00d4000c0804c58940d2880480020f41c1080c0080c0f481c00c0c01071140f8003c0303524030340f900d0441c90980169444085890b110390b007002d011080d50700541e440141140d80c40003000d40a81c800031040b074104080182c00c90344035a0003008003d0200300d140e00074561035990741d9034003900c1d13601c1008000640500c95000d00069000b840042d82007400358203070381444c1c001410900081408540004c4426104880071103807600106900010025003d00480001075141000424002c10b40300003581c50081172103028003070f580c0040490 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 225108750 1250 225107500 225107503
    0xf090e0a17130302030105070816140d050c0f0309030406020c0d21030b03030703050c06060306191a06071a0714090d020d0206130e010515041502010f063201090e0405 73
    0x1513502800911442c1780414019004590444007a4007150b886460500c0325441000d400044d50491003401e410003d05130645001040000e22030220b08404100c1ca0b511200c082d07015522421140000315562420041d0007414a681c01c1c138842d0041c0707202c4611000083c200c0c1205082046031408101004541d0f19040b8094401110b4450300343c0070001d0b010082c5030b8000c00400c80c0138481400c42c0c0140e203a02d014183c1e580012202007103c0003101c0e6074103940510540100394034240d146030380006c403080000000e01547c4100d00840b00002c009007141000302e404d64406a200340c55052810840700300100620161050002c5144940c4022140008640d1059030382c201903500603006d5038654022604501f039842c2203020303100b03280001c140000340c6841d14202060060704104603044c02c2902e0145005c2c101c023680503028042d552152031282d604046803003900010f140780140c2c0b00038280440b00710380c030401094045405601c5100c0b4112000d9030040706880031201e00c5902180c141d507403030800d103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 225110000 1250 225108750 225108787
    0x10e0606090310020414030c101b0f051507170105100c0314030901050f0c0309070306180b0901060504060b1206090408160507060f020a0201020606060a11070f090e0a17 74
    0xf000510110380840c00b000300180b02d525015081d801c50305104e82090400805c840ba1a54007000200603944003034486800449210f541d0784540540900100715a0b110350404580708507503200e06091808001c14642d221603040e038565030200c0c402d1036650400021500070001ca0b21300c0e005010400d8194002c0611440546407651040c15807141c81c0d00b0f09100c1d00b4060001a204415004140300104141032003081c00c403801014010001d00e061442c5558000140c500308511041d46c03101e10705000046042c1d51016071007035945c0c1c1c00003c0c9040c1860200002c460b1a0b4225601c150028860280c0001d6961000f1390003550440d06c01c0ca45569900c1c0c078200b41e10503490b9510002e5510f000344003c1120001d0660309444485d228403014880c5000200d0740c400f601c0074083c0c01648000046011418000000c007000710403482e04928016000c40709524151155000f00d125051103001000500098410f550028240001a015900c0342341c99100c000c9050a8007100c240800107140009070308000c050 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 225111250 1250 225110000 225110023
    0x40501150c1223070204060e0f040b04031101020d0e070b040e18190339060506011b0302060f0903120a020c1f050709050f01020a060f0609150f0905010e06060903 71
    0x628501c810b010081c0383e0b1940015004034004c5041400114180c0c405940452003850300381945461a5580d0702c0344070004001803c1502480b034080c42c000c1c03802c8400e0005002d1040c0025000c10329080d00242c2c54500302040d44191a003e02c181303c240311603030358a45000c0d08100810344144008169854581c1042d139900c41c0340f25600c003000c1418003019007002c6490070104604247c1080081c80ca2b100d14030040c001c6070100b50318084108094005074180d0300046d041403042c0341c1520030041c01d018050000020110136409680140104400c107140c500340b01d580100f01c4005142001c0c140401070012b00b4010b0b065900c0c0a03004504580107890402041400d0034281400b94110032015503140700030281651b2240014261200116060401c04440d240d00c60301a40104410b85007607c0304001401406071801d00b490f00c03480300041404107805800c80c9841d4810101d540f1501d44114609444240d034030020b601da04140040010403000c814496004a094400560715401c80b40000e0030845003112 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 225112500 1250 225111250 225111287
    0x309010b09011503051f06050a020106050406230f0a03030f140711011d060a030c170c0406020d0e010c0b0402041d010e1005060901120c0b030f06040501150c12 70
    0x291983c002d0740d52021081141c0b0204415160700d42c079040000303180368590040d0140700d0002c00c00b6034802d0000f841e5200080c800040c14584400009082e12240e5005004280e03144801d990500910b0b140c04039002d20880d06590034111000108129068500c0081e090040540c00c005105009402000e0380718004050180c4c3d61a0f545041501c0d0445042c840d8000740050105007050744002c1610b42c54100000e00b00e50520740454800c80140410f144410f0400c15030b00286100100e00c14125806034441c0030800d9260707401e051001788ad10340104035070010040400101107050760080141d48040390000e0540c0c2050b0740b00d001041c00f4180c03298500344014050704120840e00303010341c8800307400f81b401c03000d8440103080340d0100e609550341510480d41c44900c001c010003681c0c5d44100314800b40303840340d50f104034505e54034821080603807c2180d058000d01020410004076151a204940c05040184800302e003114000600809090a44030014040d01421180940d498042d110424070202101c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 225113750 1250 225112500 225112519
    0x20c030c01050915010806060d06050a0e07080715080c0a0c11030f0d0f05070c150309080a030b090612060406091412070204060f0b0a0f05120117070e0c09060309010b 73
    0x19078295207102a407a1441c4c40400c15001103601200494114054403001340840031880f2651690002810082c2c90014425520150401c2080c1c1c1440700c2c1005080060151400c0d62070301c1803a09036001a42980070811000f8420062050098003c2d10000c6a041c0341c581c0340310b407452400066858143c0d082c5070703051162045130b0940ca1000964200c6000c01551040c1540904103800c3d2840c1c00b07180e0008011030007a2005100040b13001c507031f00e00c07905400e280100e001d4132a51100800d40c3e010ac0580b44c00079490f103208683d05e00b003400691380c0200c0140c56a80c200d0500310305150301c03a50058002000b1584486882c420b02c55103940038500b455868003030715010050302c0c0304405503502042e000c83c000d0341814800503180c40c5d80d1243c00101c0d040700c007840b032911400303040448014042140c90002d101c020700503201001d04141019020b4480400344444440703c944a00d4071340740407540520503600050003044800f0340c240051b107100107019180d00e500c94031440411070142c0108001d07941c00600e50f1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 225115000 1250 225113750 225113761
    0x70609050307081803010f0203130204091104090c08070b04120803060f030105010b070b09061302060c0f03120103061d1b0d061406100c0309030f080d09080406020f010b13020c030c0105 81
    0x100c200101321030200c0c002c02c08242c48402c03000a0340000c030303819a00542e0041a010243c1020b403c500951840740b080b00c806c40400000140c21110350241c2640c0e24242080c0c00e1145160400c8000f01070b0001c0030102d41000d1901140ea2292800841c00420f81400031000c130310b0a4940107980700c0c40c440018024000d960f110303948400907805c03901003642d4944210010510000002c03c00c02c0c050060300c8422000714940740c0a0180c2c550010480b0500c0d0300c103030301c0030254480003030001d03203890032005098a038103515504000003a19030048881c804030390b40381c81c2010700200c0040c0c5901180707450340d00c42498002c20000500210f0080380058502420011200c040d00d0483d060b0521401c42103909010300c160000b401c0351201014a0018082a48504107001003902c80f00c00b8211140320f005038910340021111076600385c034100e44040790800408541408196010300c404507640311404020080070382030100190b21000e407181520013469000034198001e50f014000c90b00380b103102100034841404e11 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 225116250 1250 225115000 225115027
    0xe04170d090c03080c12180f3606010201020a1e0c140703061d0303060d021f02070312140405061b0303070c0204050a05070210050604060f060206010801050105010509010507060905030708 82
    0x10b207010080c00d0055174280c0c10202440e60030361f4100600f18801200840d0250309126001e80826a01030b071104003520640302113183c2101d8082d1004000000c454000c5605003d40b454100281c082419a4014003007a200036034401c00e1102940010758402c582c50907258402c0d11040c0009a0160244801c5001c0416a0340001102d8040701d11914040040c102c03a5056a0348011035000e142245800070004240540f4000c9036002004d4001480b041440703030400700c0110440d884c04070000258104540410512035807200104800300c0f42e050100841150326aa000c1d64400c601a0074800c010205110754014805c1000b25407505807030342120707902c0c200490054200381080ea8128841c50518000641003031040c042c06014040f00c3c0c0041229855944c9003401801d4000c2c0790603046a52014002541520880744e0300041c00d26030080c00131541040e040c00e0035140141c2180f41441801c10203040166031290444405075089080080d50b042c8070316103507046200d00c00c000303450030754045500c80c00e1240 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 225117500 1250 225116250 225116257
    0x190204080f070506120103080d020f04080c130506100c0503071208011401030c050a050c010902030706030b0418050303070f1106190c141602010905060706150e04170d090c0308 77
    0x40c5281102c1200e640d03401044002c1c4500b01d01c080c0e613103080e00d00400010301d420000d40149454001c0c09814402d0851a188482d0803651068041d580300412030412420b004564064140b40300d00144440d290000120303039812143d94400d030800042810903c10710000303200f07074cc3c94280d210110541d040c6200000500401c002e00500c148540700300e8131041a0b40c001e200d4001e0303400300c1e5210036003041d012190a0760580c0024a00c40c006540700d1842c080183e90a00c0b04a020b440d0940340012042c6110301440201d912084021494a01a04441002c2580081501d9001201d8540507442104170001240d01803e50344602d0150b225071014009092551440400b400070300c8401004820718000c0206c602002605800d81a4901004030300107110705404030180c02401810309031180c07560b810100b08a03900015058855541c0c4407940b11502017040400740c028074040c00c5d002c015050680b0364507468403100803040d2280c8800030f15654141000d401143d443d80d088107814404a540c1c0c2000d035095071 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 225118750 1250 225117500 225117523
    0x110c130501050a0e04232e0b030f121308060c1b1c030209220504050f0303011508060d0203030d0510050109180e070e13030e04111219020408 62
    0x55a031403020a613031a00c0c50300548525045215244440401c820000320790b03480d02444501401507000e400c560156400040a20781001b00c211000c1a0746a03000303008658400b0406842600075544108080c1c100203450b403211241102703526030f01e43c412000014041388a9025840303e01450041004458601c0044d0850804114041a00348100e02040c0e882c1d503c40c0200c1440c8400411405004034420f501402c08044040d2075820043c6c04030100540c0150360603400280700b034596007000308100701400300c3c07018107044c6030045065504285404080b80d2429501e041048902c00004200d5603030720b000c0480e4245c0140669546401004810380500400c603a2008021104140001c15520900c80d94040f00d4010104800c000c600d5110b00014001038400a04a0310030140081a90000e401c420340c01000ca41c80603000c00c403074629000e4000460801e40764800d40c6010071000403016004111030300001d600c1d1100b1150364811042c029803a407a06e01c56915170384041070200c0c1c0c181d4006802400c00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 225120000 1250 225118750 225118759
    0x3100c091706061f210e121b0319030b060904020c0604110307050d0204090501060504020a090305010609061805040303201815041701020408030a0e101707110c13050105 74
    0x113500c0b04e04503602e2100c0201071000042c4040c260307180b2030035000b080301506450307802c01103903800c0480c5105150010480c00c0c0003165a0018650088004c81e550780001a0242000755060075000380b1000c544003a424000c2e01816190811609660380c3c00040b100c031114000c0045440d00904800c055992000316011221016a40d40c40c803a01d2070001400340032104014a1600040e00650074840902540c2038115007543d02c2d0311012429a9032800036065442060b038900050901e103040c0982507030301c40d50102e40b55501d000000c1c88907441103014045207104910300414243c8a0349000c50007890f6407410611400e01124241d8501661a0000c2c0b01ca40e15440200024009040800c4503243d040d242d80d0141e148100002c00c00c0d400316500e44009000b03180c00050510380c1c2e842d605411039002c007406030005000e10030802c001c0c0c42c21a00b020140c0c4010301c0c240012892002e200010302230080c0c888401c0c081c40d0f8200c200c0c1c11500b0880c142c41204098103840c2d01010f800c112201514081c040c50344207 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 225121250 1250 225120000 225120019
    0x3030f050a050c1b0c0a0b03071412061203070b0408040513050c07020d0c0b0406030f0612030e04180c0308190c080306011d0301090302060a050a020903100c09170606 73
    0x11150042c14010a581400d141c9840052001d01c010030309507108001d07060040782082c088560380c00700b51800500c514444540e59103482c40005044150042c804404120b06002c4900300003d11000d60f540083c003a51018810f2a410400c80e281d4013560030024050f000308070800040003035090250003150815105008060841800101a10811141e508503051b06000400251030a6004105018090034a03c4801d5483e1540240140c0c442d41100d0013082e1100c200302000030b01c5200349001020092000f001c40813a560f40149202050044503224a4590003050f44001e81042c4e80022250300004400d2040c0c2c4d60324160700180c02c064000590a441c0080a00b601402002c061003055072000005140d0b0f5150700055a82c43c030101402d00184071000c1c580e440d01e071002d00ca0b18040d54000d400408141c079007015450300b03860004000380012401400b00100b19200010040505001020702045000205030102d84006180d4007000d9010103821101c00042008201a030007100e0580349001c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 225122500 1250 225121250 225121261
    0x1210050307050a082104080303040f110114030601030504061e0605100207030c180f020c03070b06030c130b060705070b03070e0d0c0501110c19080c03060405070b1804050403030f05 79
    0x3c100c103403407090401c00c1d0094984041c0c0c2c214400d061a080c0440101c0c0207081c80e0300d40b005146180c208690440e442e03130781070300b00d038040c03007044152002000424030704401001d19541c05c030341c010b000140c002818140c8030400304003001420380000009468000a24070709280c07100b5558090034051042600070350002461a842900c041001806e80e074010806803840341c42c00c0f102c9654000c241d014000b0340f543c1c1c0d2610988110040c001010001681c10003542ca1700414101107440a101600d20362007030340300585503002070b1100c801004001880680000702040041c003ca1110f01c204a0020064020260040750307084411001e0743c05040305a8640c480c8041d0603003404402000d85002130700001d401d440800a540c421003a01c2a51008181580c031081240d0010a40c188102d170054040c03c05003140038403d40c0e5080100c00360a2200b24010f1540d07050075180c19071642d405d4022002c541400085165551403003020f80d00c844280940100285e1406040050042c9031070058000700b141001c1c0401c0c3d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 225123750 1250 225122500 225122509
    0xc0203060c0703140a08010b07030504050d030804050c01080f1f03020d0c18020301051c152d021305040914070602030a0807050c100f0e060f0f0c070c030f0305121005030705 76
    0x40d803090796611b680607540d080c03000c1a4403642040c442102007100410021540792641c03003019031031500c25200c0c403645040a03e080c03800c0070405002d00e410002d801040240350f401d0749202c1900f2030340804002040350348070610300c0d100c08a02d07000039400055400150003044091050f130400c540200e5038200060b45c130a130414041e444284140d03039006d507480b160b08454404101041000303921a00090005048a0381c0c1c440565840c002012001c2c9400c68016a10710001c0b082e4108481c1188401c40c80c10340044c0c039a600c0b2000600849005d02da07160007010400800c2c000c085200c1c28504103c0740d000382d4510000f5035903408940441c00180300350010510782c60241054403408019400903101c200c44024140303000740210781202800540700d089024014005021880c010040c0052065161804031074401c64100d0141440c000304408016110225035414500c00541c0d921003900c0041c41c1c910f060446041c001d041402600085907014020110703400c5081008680080d410750f4a003039910030410 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 225125000 1250 225123750 225123757
    0x307060b01080709350109030e06070b04060f1d070501030612020d0b09031b0f060106090b0f030a0912030e070b030c0d0513050319031401050d02100c0203060c070314 73
    0x30008034032908000e1100340c100c007501000440d4100b414405c507410016180d40c02c60400852140143d40d980000300034542d11003034010050109403842480d00b4100e550301718284400500180c400ca60b6400400d1139a41c06402040e050208000c1c4000140328240e035064860f0003038815180032900e441400220001e0707a02d44d1001c082d4008116800449003511800401200103124510a00080145a00032100a02c903031405040b00002000700009400711145442c83c1a0010000d0108415041041541d014101e5000c60145c89800e40c880e01c42003026000b401102100a1080281140400640340c0c15805070220003420021110040e40e41ca10b28049480141e07440042c11008219492a102c041d40149802c08015061082c0b5058103407202c41c1550008106280d554800c81d42002e50705502d07004408041480d081c5501c0359502d0080090180003110700004d001e41100c07c52054400e0145640e10007140d0041c0c01c2ea4000c2c580124500103984c03009004802061407104256a510b440b002078 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 225126250 1250 225125000 225125011
    0x4020f010f1701060201021b0c0a030f110604140102061b040909150615390213140106020f03070f02212a06130306180f050307060b0108 60
    0x18611094214011a4101d03110a01541402600c011503040301048205803402801d0342e500041e2642c04103005540400c1c6401c1801505074000704010b1040e554125007041200da201d511810381c81c003d450160f02c45025030380c1581d4011000324001451001c00ca03500000204241e0030740b403132903072080c00c901110200301840d400711f01d2050005006188896001d40d660901440c20a031141100032901c0c0e055951070f40000d03454120600700503071595001460518920320542e2483d2145840c042007480c0f40100c100194619001003600c641591202144a402400020b2060081d000c40e031070016100c000c02c0c480d00c0d0044c40344158140311032801106951800c2e52050165903644060340800c0701c4a407081c0c1c6041c01500c0301d0001210200420002500d40d030400018180b82e0320344ca424190760f080252030002e8020700c0100040d070308080e40415002d0a40380e12480c00a2004903800300c480d0a441184002003016116001c00000d001c0000068490940319520512813081914011034040c4001d664 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 225127500 1250 225126250 225126259
    0x160614031e06150f0d0c0c170d020c1b0307120c0905040519031e03060312120b0a0f090608010b0d080a0c0614070207090b010e0f040e060705040f08060402 68
    0x6401003601d00807204a40094008000408503441074211007856480300c40744400401c000540072480030310a0007100140c1d400c5c0d0600352a0328039907485409915a1408000c40b45520000301e54038046181da0586011035482003c0382c2d800c1400409140000e00008406031081c8038a500019003071201c542c440c1c03400c0e984040202c3c1e0031440c0188480c0944070180080340d0314022400ea19140414018480c600203020340d44000b004621265401d00404500d40c103070b02010300f440c0d81400825105026421000658900030807020503402e484802410b1054816500c0014000f001840310180c01411054954901c01046141e03a9541024200c07020800803035040380d1582300b41000b103032010002c0c0900840b0f41c1030100070014295500d07021030b0011551036a02148820500c98055030411041011302114142008041030341000a4418018401410311407030846041b04903d0300c4a400c000c01080c400e008841c1c560409034070182c0715070814001c0800400b6141c03000100c1c18030009500d4001d540181 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 225128750 1250 225127500 225127531
    0x1605030105160c05030421060e0a030e0d1b06110c04020a02070303050304110a0f081c0e10020708070f06020f010c170402040209090108010f0c081504051816061403 72
    0x35034036840c0f0b03c441070f00c950205000c00203003454003001e5400c1004a5000004105186141c48070440c0d103c2110401c1c50b5204101e5040004d82003204141d0326541142d00650b9a0014688441900000409000400840304001940f0368128400501c01c80781001a2401c0c40150401c1c0000c900400c8084001030b44a01c5041012901500085802a014500c603d040b030a562010072459200b692050030700000c6444104401d8606121071500d416040c01c591074011000d00c0001c10000d4907500b01c034840d101d00c401d8074403094002c11900e001800264191030710300e40d0b60321a406111419115000c0076005030700d10201c2d005410300c81d090303070000b80d0b40750382c062908020400325010200410498000b80e0803c08c1c41318940d60701d0013803802011000c002081c9180c0c0b15200310140d0380408480414032049005000480c0f0388800d00325126401541d0005070f030b5803010030701030640b00e501404003024012441c1e400c10100d201034401e002d0b07401c2900c8520301da412038179030b2596510040316611015140003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 225130000 1250 225128750 225128791
    0x31506020a08040905090f03070b06010f030209030d1101020903060405010c0801050a0b03070c02150706270503070602030406140709080615100e0111030a12061202211e1605030105 79
    0x745d0106410903501800c440c003002c6c14400c034600e1a800a6810340f02d4412150030841c107913034004040c0040c0c890619065050107540380110360703240100e080e89024050a015034044600003503050304c5c8a502d00400b12a02400d15041503402400f02c60031410011b0a0940045070750708005030810100c85068819601d15601d6020445114280000c1260300c04103800400e020b50040401501000e0b0040a00080d8020310355548042d5950300d007a51500449114480c90105901100750b460140e000318000d40c0d40d03912450f1860080c030300c040c18006140025801c0c044074980c0b01c40004151040401250080d4440445d81010032341c504d04260f511100d102e91410b00c191090f9035546c040041818454003004003030b591942590031156000000820300402c4511007403290141c07800a0280c3c0715950010101ca80209000d10040c08440c0341880da081c908124544041020603a0b501110a58400041e882c90200e521404031001a510320300760407030702152078035040c49824003414601c810307008130340b42c036 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 225131250 1250 225130000 225130019
    0x6061115090a0614060a080111090d020d0204060b0a0f030b09061c050105010b090f0a0602030a1d15030406140f06010f0512090c090a050f0408070809040c031506020a0804 75
    0x800c6800903001c2ea01ca440700041543c040e41d0300d00c07a902685411140b41800c14869009401d503c00ca0031681411004400b5100e101c048800302d8500f550715056207000c42c0080b0310301070600480250840e103000c0c00096408555000b500000c00c0940d84c01e03800024400d41101074480c03001607590300c8200b2901141c09840c001d100f08070700340d03100089180841a01d40312142199001d90101c800c8103070018130480c82d0716080c020f02c882e500d42121080156070a01d0f10003075507401144c0100c0c2c14071a02c0c00e07001041c00c4050501c158803080c001c0108402031180ba4240b02543c1080c0d5084036082d04041d00031344600c14449000d845443e80c0c44100056950b280c0c011140000c003100d21100340300303007080b82d103140407036104619200f074000000800c80440c4803814402d007648000e00305050a440c000504c00e540d07000c88a0b2980258000c51030f036480d244141404002c0380f01d500980b9a1051038200c0e10924940c040d000400f01100702090031301515540c81080e1389a040811000b0000c000402050200604 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 225132500 1250 225131250 225131293
    0xc061611100e10050a050907081203070c050a060603060207110d11061803010510050108090f0303060105090a120303090c060507050a060e0f070303180501090b070201080601021f02030a060611 84
    0x80003021100f0340b5081c00029400c4900c00d860300b048460b260020002c01000420480000b0b006040c02024000308014813284503000c0505101c0800c10b0300303a108800e000003040705d8500035800800c03c11215031b4a1030484001c1d40641001c5480342d40030010100e031072401c54006030307440c0c0c0c000702400c00315124041006100d5100700d217000c000f005207503150202038800b4400c5c40c0c800e5802e025035044803818100094112500141050b003660b0000e030110451040201c140c0740c20480c01c1c20b0444d10395584900292400c44650854100d10303c4405184091650641101c00e02500800c0e0321449103868450841d00c9210300c0c0c00281c015400b0170280000614640d1118140011180955000e24000c03001c05040c852240e1065001689142c245e0300188030050002c00101000d09143c1800d80c030303100290000c0d008042001e030600203000e0000d8070990083c480031042c10055402e481e00094204800d1009400c03c0c0c87c0686c1d00c40c5400300c0400d05e82e000301110989505040000d060006600558040916 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 225133750 1250 225132500 225132521
    0xb011209020a17010905060f160c0203031b030711011d0105090a08010219091d2406031e130c03080a0201061d010311030601270608030c06161110 64
    0x2001d0030b0005980c01c0f0244021000d52481d4001041502c0746040c41d9240900183c0b20090502c0e0303010501154503600b4403801c0031040039092400da514100d000081c1076008004042213003982c2047d603c0c1103500003100a005484c8030b0402c90528600780030046650304100141414104040720071050a0b6001e040030b03051200300101008000c648644200d401da8100640100e204d000c182842c0100e1034219400d2030141c2410010001500054100c1d2508500090204001c459a0780131184089500004114800790054815a0ba0b8280710328484134100c80551070020005407800030031500036229002e80320460f0401d200b03104c01419030300c614440394440c03180403040d0340d0303101000107001d4801450740c02180c0440c03098401c40d600d5810301c0034950714110300b070b6031180d00107800511800e03199210203420140a41200c070031140c00301507071500514494100d900d1038400420080da00c2400012154800c08140c1440503447e440158180c0c0c1006041031491320f550445141c243c0100807070f5000500c06d1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 225135000 1250 225133750 225133759
    0x190b1801020c070f0f0b0a0206040b1305011a040c090b1902070305070306050f090d020a200a0b0408011b050405090703180b04030f020d1d06130e06130b01120902 71
    0x501c4064050301e01070181c0d00610700b80b643c500041255000000d18032009061b00c10315545814180351000303440d4140240300508c2900c18102140c2c9041c0568482080564800c000b003210500c1d50000403a2221003d00080c825400d003050310005510036828001201d131280016410708581401e200ea458038800c040c5002c41c072910300000040b4100f0090080218010280081e46050042c0c4a07884110014605d4105a100d0088543c2c2c06078000342c3c885117150000388460806445d40e400980c0e1012440006a000c01c5114002ca0030304540c20043c4210f40c50ba000030410740807140c254294425042203800b000c40c030103010803c0347d81461240140d001030a07207070001c0d001c192091041254818400240d91a146403003c010415400030079140341e83c4004d0000f0104500080d00042c8454400340003d080c0084201d40120952110010f035a54000d51030903003840640c980e4003076103805000b151031a1180d035003800d02070840c00b02c0381302d100e60011040c4c0d81c144082d1400c484d02006845000d000b00d030803 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 225136250 1250 225135000 225135007
    0xc0f02012609010b090103020f010e150a030506040b0405130807110d050a0c0f0b16050a0b0f150603010f0306020c0705060a0203070201200607200303041202190b180102 74
    0xa10300c1d4400707000304101c080c00c4860118145610982d0071a410800c1e0140203500b03600c01400540d840041a907940715007442d040c040c441c3c0300c1d00403d0500044409a41c0002008944482c1d000d4054008603c141015901049094500c10421080d07070001c0d9010f005001d03841d0650404030301407100902140307001b2a00043c4c40600a008a140c0d4040c112050360542c00c6003400800300100701002500030f041e859000b8001da800e150070f6540c1441041c0c015150b240c44000c3c16020014184150960b550304104403c0803403800301e18881806200b2501a402c43c0c05044142c034070791401d0006c1d281652090780880ea840d508550700c000080d40911007081c400d210301d100c00034941e510180207001045050303029584600d120710000d0100e18030641c4020f000003094a01ca4041d41002400d298402158a8400da81182069000b0460300c41060300702542d0100000300401d02900c5940000200d1055080304d50f402c51170000c1d24099041c41800402e0321104402160f044404002103942039041503000515 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 225137500 1250 225136250 225136277
    0x30301030b0c0c0a0b0c03010501170601050904020d09020a0f031401060b1902010914100c0e03030d021e070c052b030807170a0e0d0c08030a2a08010503010f0603030c0f0201 76
    0x442d00f00403031b48400282400070040c403043d41d0241004000001038200714005003400710000c0d0041c041c500d080c600960740132495000140b82d50b00141030141d0003030f1030310001e07589a29001e03104064501080d101c5255041c07134283e0304034051203560101c0b0b4070b00d00003904020303082241440d80c9500c0144082150b4840300e4900200d05400701d0950302081c200b005028502108503011b040c0c404000a00080c000020400c1c0c5054801004039110a00c0755140140d64181d261000b1460007401c1900c240c5050f0301040e11400c00a1501c00740040d170f0412a05810300c825480c00c00d00501c070500e00c13612824011010a038000a004014030398000d10f003810810031403c810000c050004408030380f941a4503440d03c092802d049000d20101038005e206280c10051040e181d102c0555500c40030301039014980c2ea400c0c0f081002c9001c01c28008107400480550b5030b60512000c002080c0308004c0c050280f0a502c2e10180d40c04075070840c401c00701202d9154441d05002e105a4648400283c2101e00903410300444002020 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 225138750 1250 225137500 225137513
    0xf050a0e150421030909090807081e0a030b0306060a0b2b0908041706040c0e1b07080c06071107030b0613060f060e01020102040303120905160b0d0e030301030b0c0c0a 73
    0x4122243c860055610321001d030400030030900080d40116540d40c64111460040344841013105e0300160413000e9240ea0b401540d044d1085224412514a20460003203018007081c6d0f13142e084041c501c0003c8044550b50b46036402048503a03c1c4a100350340000b0720401400303508080b6a500c841140401000c1082c50400041d24442a6181840103c1d805040000e043c8402ca468044049000342074800034880f40c43c00b5940c40c0f44e400f451340104400c101d071120001d03200e0000000c00010070604607080300d03110580780c544017500b90400021b0120380e010b0384000a5026101d0f1008040c401c20300c5000780245491510740401540c0d020b008190400f1450882820b150180e00801005104500c4c4214690745445070040c04850040303250342c11640100030800102c1e900981241c0040040d0000084410f158071f030040c540b4404004050f0715003030000000440d147c204021f0402c00c815540180f11a2152100c03a80e10b912090200600d40051000403e07100403006000c1d00c1e1001070b0204644201d07102d84c5a54 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 225140000 1250 225138750 225138779
    0x50112110a0e120f0c09040516090c021b0f010302070302030f04030f140105060f0f30013608070605040c0302040f0905060105060c0102040b0c0304060f050a0e1504 72
    0x12021982c65007608142d4100381caa54011642050301030006000305000b035075120404407042610a03c0c44001040c148070080c0402e169264035402c503440d503190349012400c0035065011103600540112000ba860600c2d100540c410400030052a036200c442c2c23903500640003500820030a4085120a00402c19440c190720010400785006440c1100301e810381c0d1800300304220b010034210714903905100c01d02440d91070711105285045130484101342c40d0501c81000c0790144140003080340c0e0420f4030100415951816440d0701c00340e04426802881014498482c801c01306409401e48003440711040c2d9407904c908504000c18200500c6204203a1504240b17480d106c06039030003554191240501c000d0b0400443c80c1034402c0700150200f03c134050207600c3c41a150281c41d08030501c1401d004840c00220395a41d03140a50480d00a840c40c0990b0310b445001c2d401c0301c0c640ea50061b00846d004250811030400006008401390b410031140c075030340da0b054100d008c03060100300800030744401c614800c1400045440085405203 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 225141250 1250 225140000 225140017
    0x50a02040506040b0c120f161106070c090c0905032d1c020601050103050105180603011b020106030c0e0912090102070308040902180a0f0e041a0f191505011211 70
    0x883d217560880c1c11450400711000c01c07000d40c0e210304000010000100c0401e980740210100c000070510501c2c2c0c101a034200c520301c14403e901030b2000441000300020607131850142ca9a2090400071800e804106a66001c0381c4c0c040ea96050303220080d160348220030540d9a0010826800501101d20030740c4803007924001000d9001251058968020300007150704102050040200b441c1c00d110b5545000d0100e00c03c0401e011010310f41c15550700004005880942255480c81e6a809980c22100e5100800074000d0203680011207465414900018070105030880050007144204040c114107100d80150100d40e034008442e07981540211000000402e00b040c002e00020b0803101400340c3e4410412030706541700283c00c03001e6440780381080c206000714204011110103582c00100540e40c540c8490070880760346038540100031041d80d4003c080040d4403403261a02405444035882182100b800c01d10f44c42d05544000e00d511080c61300303589040000e50b2160706408465420210002403045140780060490b034032103a034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 225142500 1250 225141250 225141269
    0x1e030503040303050a18060b031608010b091305060105010f0c0602070602030628051311070501060e151503040f12030e07060839070b040210080403090603050a0204050604 75
    0x40105050f014003561781d110440c50000c01940c100038000e0000f44030020000340826941d151500c0080d2410858450441402e103d0302501680d111040c43c060922114401c6c05036420b50003040308a40c100540010003076102018042d03503800c3c8801150a496000d001408006d41c250724000816110710040000c58058400540d403442c081c0d043c0480c15590445c80c40c001c00302010321048141c04145482d069078412a05141000205080b06010306010703041c08041f0400000c814042010550110003200d141d1080d10603e1b65404a51004400d145003c07260002140e50351400c04515060041d0703802803103500030303049007081d07a19180017114250303c4e4a40402e03912005240c241c1c404110301801007a5928118100b4607280300084100d1080c4c000c0c526042c40d030700c10840320a0100070b404d105c20034841035400d43c907500d990612030b101010075502a40200d505031550154070340b0030050b041c803543d01900e82c0c0303007400e107882c02c201c0003068024000440d11341c0c00d01c800b290703541e40c01000f48001d004a00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 225143750 1250 225142500 225142507
    0xb042304022e0e090601080c0c01060807090501050a0614070308061f0e031207031b050a0b07020714060a17041b0605040f09050919080d0507030207140303130602071e0305 75
    0x900a072240065200f418800c0070b007203040000b0742ea030015001c0d5000950340d00740c079202d0138218203441c0034020581004660303024400000c41c070100d040d4003460423074100701d8007010032070382e602000c2d00c40042001100034407500c2003080c640030034000c40342643c200304040c0c4020070350707035002c030300c0103541110264110006116125990325070301d41007041081444401504a18010040e5000342c00c0c0784140c91861046e4034071410a81c14040103100007040745400072a404007521f0451802911a04540210300e644402d509a040c154201482511820b01b49526902000c02a5406800c02154000c00072150300042081401c05103070964101c1c030040141d51200380c2c9030f500b49585c640715814240c000c172005501c1c140802c0300005001136801e400c641020382a0b107481c0c24508001d4418400d03500891141400c2006010030183c2c96402040c80030300421107004205109010541c40e071005071003040c2c103815105034110220304680d0003070400a1141a1a421a5840d070040322100886e05406801003035010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 225145000 1250 225143750 225143839
    0xe0411031602030c100e0304030210090807090204050609060d0f020f0d0b0d0b162a050c010c082b1d0d03060302060712050c0a050f010b04230402 64
    0x50121003200442c00a1401d00c1301d542020350761151980d05010901c2d440d00d0a600b85604180101c03009160003802c0c402c00d141001c00044c001402c503102d90391840c4281e20700098440f12903c25502174400041c42d003464503183c5000c0000079084201601c450769030b900d03104071200c2c05920041c003130804198021a1141100c41021040301c002ca000c0034042d070711010ba02400111502d8517950300c10f064040c10308400c070544604488102004001072488890000c021103e58100003000300031520400480e41c206c01c08100440b410324944000400a00082c8200c0c198903412020402c8014510400084842d02185140c0180e034188030580041d52126545800c52080900c4200620b203058101840410310b1079003c01c180348100c03e0058040e0310201040c40c05948140b0881c0e59405a110850f411010700d0700f072054903807206045510040d0b01c0c00f4816900c0341403e0040d003000140c025a01d81c8280411442c06940d0b000050040741c2c0714036005d011a65200c8111140320f080e50751000101d03110b8400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 225146250 1250 225145000 225145021
    0x9010e130f0b040e060109110f041e2c06060f03010f060810030302070509060a09241505030a150302060414030d05250c05030d050706050c0c0316030e041103 69
    0x40c0d241c2c07030302842c20a200100020000580141141d084c40f0000400c0d04869200701060b00400004d028085400500000c914030901018421030707500c1094005020fa0b5080c02040c00d9480c001c020726003151008184014104c0d501005074000c2e00641000c0c900110703901e1112840c1d10980111441c085181014400d455010140a900c10550b0100a41c020b0858802035551003862007480d10445d00480015440e4507000f090714011b00600b4024806100503041200f000d0740140da006200840303440740000d611a0103020b50b400030741a900c48510f0354581c000304c1d40c003410130400800b420036240c540c0040181c071600001d00c01031600e5140d9190350300d00c500c00c0608101e4102d4090f003c002040c00300289181e201d002300e029500807403440c500d005c4035034500122040781c994040d50303241c025a41e00c0b00c680340d0058010105240b04200c00c00042e0740b24140d0078001e005d480c2954102e544148034400030301c0c01c80481340300240e00074140207519004800006040e515107482031416244003100b4001c0d00320380c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 225147500 1250 225146250 225146261
    0x151f18060b0a1704020117070c050105061f14120f070201060f06140702030708030a1706030601061b03170a060302030f010b010813020604080a031710030c030809010e130f 75
    0x44030301640c2c94040e050354000e16410320300c280480c0c09000c440c049001c581c01100416640110105080054903058001134000020030f041543c0c69400c000010701c6525240305500101c0e28098505409820091411241e96651100c03294400070100440118102c0350a005481010a62041400380c03170314940007030a5407034562001e400010024801e004d0b00d0b030043c83c00005041c1d4141d8068481402d800040d00e8881c3c1e0740c3c4120010b000010b5500320a56011035400d0600e52000000300e1952150000d041d92038000f48501030020f500c401d222824a03082443c2e05220501034a020350080320b80c000410012103040c0d1b10042585ea48500410440c201486648084004900204443e100b0f0300700103402408010490b1900f9044046c501085540728000d03a80a040502c048404083c002c2c40d0140000341001400304010100300b00040341d5010351203402c01500c0c0d004162090152841e0750301c0c0b240d0340008038000e05001c6509010100c64079070001889203d00c1080c00403030b506010320702c040100e56 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 225148750 1250 225147500 225147509
    0x20c2e0309082a0601080a020a090203040b1620061e01080616090e01062303240103020d0504061d031905090109151205070306080a15060b03040803010602150603151f1806 75
    0x34013300070030000c04c03514104142d012001e0240754056505940b02107400502280301c00d410510101e80000425030006402d0f8403a0034003441c90040303071450000c2c406a42d50248540340903580b01c940081c94414140002d40509019400c007000b41c1130311564480300c0780c8000d8200718001080200b80e02128090780e2800e035034401c80441c0d418030b181004104e009040044580c84100c1c0016590a820140d1203035040711488100782070100b08074180b620707101025090914161030780b041c201020342c098402c040100c4171010100d10a01c9041c01d01d07000d0540311500220546030500005003000034644030f031858150100c485d580d46071448a482078040c50708545015000c00101840d01e0821b21508a0006035410010b81242d480c0304081c014928001c06046180c100b860b182c000030082c40308020481015505841054007543c510000c03000a04600703030300445241e68035034000b07910041207603a0101600d802c50000d00307499054409030800c4a84003000355011020340d215400800c0c009500521412001c0c1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 225150000 1250 225148750 225148769
    0x2031006060807080601050d0609020702030f0c0612150a030b0906012c0a110c03040f050907050d1806020a0509090c070807030f020c2e0309082a0601080a020a 70
    0x141c1020402009070000510b044140142d5a02140340b681c0144207884e0f40555022040c041d61307444501c0d142c0650080401207020f4401d4809804114401064041403114041c16503030401114510780e4002d00c10203005503170b035070101403103814090f2241d0740e10002440c05005402040d0505d248080d191840580c000310709007248003001c040844070b040700c0c0a03885041c51007110217501c60716030810090080070082a448240002d0700d0103c224040050411034428590b18005a559181406001102215400001401085032260f500c0165010315050019803090180628469480d03100b203030312403611a0b0118402084c40c0019250a0b1062030380080c01c1e00005080808980c0c0d0380318503006845000741441001d01c6480c0c400d91080202c42ca1850b1b00500c0081e96013100140010707441d030011200c4c010048061501d0022074060300039401c2240d4000301c040d01d030100e04d07901c0400380c13040003003e90423190784100424014074003040b025019040b24009003100103145d204000e10080150b1214446 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 225151250 1250 225150000 225150011
    0x150711030a08452e0e130e1009060609091a07020303060d060e011e0501050f010519080402010c050a030305010314010221062101020a17190c0509180901061a07020402090a081207020310 81
    0x403117001094003500d45072191000b00300707001c40e85408000b4140d00d801c20353302c45152540790400e1058000345000c4e1096064600d551700e41b1032030320880e200d20044400790342200c0094121000511554810b0100101803400029420300141c002e440000101c5203008426844000502131813420702c4900486040908009107400014803d0300210318180802009004440b4005415a401039444180300d0b9070180c00c1c0d82160a581c42c014004102c01e000990b056054401c080ea002007052080f9002004071082d00e14501d1480700030b011000070000c201c150410018441d040d03c55414030300c2c0c1c41c00c00c21644d0016032281c1d0701c400018000720180c0600d003400710040d803e102c2ca81c40401c0c41c6800e160451003010500700304201090302c83d4412181041c1e0407400c5175403d0303c0301040107182140250210f1000b8054141d48080300030350b160700a65201c660780000c1103104010718080c1d0061420030000350403011256505c2c4805404c2503c02c080c3d038414224000740c4401146402d01c5007500d0f00750418000c110 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 225152500 1250 225151250 225151271
    0x70311010e0c100e1c1a010305030c010506100c020910050319020f0a050a09020d0204241107050105120615130311150711030a08452e0e13 61
    0xa6107103c200800e000081c0b401080310a105c2c0504d9400350f1506d2440d62410996981c0c5459a03407a80222510450307546020007285aa00e081a440443c0000b650b4401412100d140c00f0070214000c0171b00001c4a081c00e0700c800060030b8805001034141c0c03520746808804664884d006100043c1d41c1852118070503907180009001c0c80c2d89021088040c0c58035410010303100c00c03501000200074881c6800c01400c1f41c0040103810f002000c15004030105480ba9590890b104a80e20700c100d41d03a00290251601060042c0510f1101800c1c0c80301c4141d010b0402446164100b0b0911110710b10b0380e024a2042d190003404200038014032409070100029010261100400c00c441168038030150301035050010030403d00800d140181e50b50030410581040d400450031980d0b50400102581d40c140d60300c61080061520304c1002240c0240c9148203140c0342c0c0d01c040e41030003811a0100308402c400e0780442c0c001c01c200c40c131305500501d200c8039981c0ca6141c1449482d030055455008042064035850f0003c08100729040a10415 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 225153750 1250 225152500 225152509
    0x15040305010e210a0207050d0b06030f0106030b06190f060309121803020607081b0d02010c02010905030d0513050a06020a081321090308030903180a1a070311010e0c100e 74
    0x42c03c0c90303102c044083d1904881101203040108507488907038405d81301d003ca802401103100e41c00c0d0141c1000c0b800c5940a866003034440342607036982d20025084400d0035000a0391070922140301c01200d010034100002d0b150f103032481039032441c0d903607003250000a9607402c1100030050100390900414456081c9240700c000518850004002c060000030f018680104050040003445015a000f000d062180003022001e0034412907030303c6c50108001e030015030070940803400c028018450312887c80c0d045000b40d4640142c0b0709020010702405030004007118200c440807400b08409100307034044a441400b0143c1d4825a0900040c00790001030700c41d42448006a816000040c141d12101c500c1c82d500c030b01c060082d004841815030708070076141d01c094075540c4d00004200c0d521001000820601070040c0c2d04a4004aa4109121826245000c2c145080c84840c0c0b1020056110b40c015001c014070901e40212a85400780f040c900b500c1c800c0900c01001d82c0f008100c00020b140154482030100710610341040500301080018 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 225155000 1250 225153750 225153793
    0xb4606051806040c12091b1d0f04030507020306070c0314090105030a112109011a0607081804141501080c0909060f03030a0c140c0a030b130215040305010e 68
    0x7520403941d80b0360084c0e03594040d4003010081d086600c01002269500d0802d40041d404414540c8600801d1005c08140300c0340f4424091503001c154241e03000303981d403600d0b80a030600c10007410540a00c90140400001a0380400c015841131040d552145680c0ca441c1c07030302404008100c4440315002c002803064050300d907400070581c1d61140c0c06c04804130304040d42c1d204040c00307807050040045c03649030880e0603e0500505124000d0240090704d00030001083c0041450000d074a01c203032681d600c02002c100e048d01042140c00900485441244c843c2400c1c40e640f00018112000402c1008405151004201485001510088000d0001e0078a50311901e80907d040341244034800803540706208482c0451015214885400004000982202c0d661038140d0005090641516000c43c0c2c407202441d02e030784117801d01088032032519001030480c0301000d086588444c10120000e00106056006850701c03401b5070345862000131450004d41260f50740d00e0440c10300e11b00307440c00110715840c04c0e484119500e04000f403e1055 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 225156250 1250 225155000 225155011
    0x9091329060d0c0e0703140c0301060903020118180b04050a090506130309080d1808070302030715050d06030c05030c030712020108060a0306020f030601030f05040b46060518 76
    0x6001c1d54031054500303909580c000390400030358a44c2807800c000b40c1c250141d00c40f40c4010440825885140d0706c04200507883e2100340035200025004280030001540100ca40503c084034000080e800c2c40d45441c1c0c07040341d00d0072148504801d2070300c84a0402003410b052084642204180300180320750021601c1c3c0c00d81c2c4c2d400150500780184000c480c280181841070307031844e0103003503004203a072200081c0032070040078400c00c041c0300d003182001c9010005444200003445c200316507000c0c010b0410149005003261030010100044c8040c04030030452088000b00c81e00c1903e020b14400c14400014600703100c241031034840030140c120301a610000090101c4c092901d0200300d465824a000d40032030b5144004100c0380c40b00341e400200418004100600c1a00300079011b944111020383e0100406241d050410b01981c0c0705882c00303054080c180004c2030301250700101004200303c01000d2660308000c561080100b5017400d400d403128001c2141d40c9034602000074010b1a004200840348440b03040c40101b807000203540094907 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 225157500 1250 225156250 225156259
    0x40803070201110c0a02011818020d0e010207030f03061d180f1504020906012f010b060c07050a0b0403080a030f06090c021e190f06020909132906 64
    0x10400c610035002808001c9503032640581315807003800801d0ba95203005070201d0104448220040801078103003940070840320443c40d4003100b0f61450300700c0d000a501440355401c0c0c440e1038481c5600e8a000074001490914460394880c0d651000440005045504542000c064841880514070340c41c10304c00900ca40004520502c070707500d0a161083c241c5030483d0180e820f0664001c4c0c2d40c144100d4a840400d0341d100e103000399040c01d900d40d41c0500449001903181c2c900740d0f2600f01040382502041700f084d0401044400704000294490003600082c038030f5000301f00c00c14804d81c41000280101d06104031090000e001010380355040a0955540c06600c0c00381100f000101543c0e080c84c1640003459400100c01081501c0c806c000040030010001d480d1560000707088010030245004125005000951449807982001911403552542d0b072150382c5e40c0c80c449800c2d5506074003400b0f038120341d56078140c2e071500440b958442d4a42d40045c514080c4050308040748003d01040c00309291882c06441c5051031a40840100d8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 225158750 1250 225157500 225157507
    0x201110703021c030f0507150b030a020405090304090f06080601051003111c0e0c090714040b03011403070e0403080c210a0b030705030a02030705060a02031204050307030806060306090408 82
    0x14446152150550000e54003043d203464181c0380403801d41c4034092081c001e9548402c50403100c5000e541e0b134495018010001c410440505500406540c4243d49152009017962241034968001400703a5000780e850310016000001d08000b4034070716104241101110000901600b8900350744140c0b26001489114001d0307004200b1204580e01c00c1c7d00034059030346c0c01401e4945551543d00c078200446c869010400b003540c6400300c6810320f25030009110390311040c01000c0c800180e50b0b4110032210b540c6039045040401304140804140f440d451030146001c1d180d80081c5203c0c4244560030185050a607a1001100000d41e0040c007012076807040113941c0c00710001c1039490b624128141d0300e00075804442b0b8180c805000c0e20043c403080060325000500e10020840484034910f894404168885170070000080d8568043d880400039801d145015000c5c14001b4010f40f130418940c1d080304070107140120760845281d003001904000700343d007000c20941c01c00000d5505ca0700f98903010002c20000300c03000e8001b401104011 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 225160000 1250 225158750 225158777
    0x2701030b070c122f032b0f050103020f0409050601032d050d1e09060509130207030807030f020405060313060b0d080309070f1521020414040b0102061b0a02070b19030608030a09030201 80
    0x204c08542c4146c401001c03c12801740e034802c41400600085c00200c1c410741c0c442c200d100151a05004812140d03070050302502071a46141d580b0b100d01c11058894103168110400030f11030300034111400c0b2007050700810207400102c014039001442c202c607009941701a1041450004100355024182a056840a0270003d9541040c640019260842c0c401d1081e0321900000300c6004141c0e120f482c481c003030040e40c2c40910000342c2ca10138a2080c1d0080b4024640c01c40740510014450a000050341c00b040f41c01000300182c0520807038003103043c0031410b0000313448007074000042c8140880100106402403c1d040001c203015420039200c1600c101d13280f00d1407020880c0d07504100c9001e8049100301e240b08070f10307a50115512a0740d00440701c900098900c980b803081d45440345003c150b50001c1252031090301c0b004003180506608101e01506a04050fa201003148502c210118996141c44000c01d40c14203542060007000c1443c0d4001820340c7c00c03035005401d56030070030721090556907040300455003605c0d4242008048503450 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 225161250 1250 225160000 225160057
    0xe0406170d0219110319080901020c01020d0f0318050a051b0406050907050a110f07030203010b0a030503030414030903011109090601031b050c0c0607030e2701030b070c122f03 77
    0x5c21036015001611405106c1080070440c0244100c80081e003e0b941a40e18840040e41c40d0b036a40102040401d45a038420807003144254024003444c01c04c403000745004440798540300d24003404803100301c0c0c155002c01c1e0303400c0300c0c00420381c0401d609680840e014030850b820000820070032640501444140710b004119110403a0250856090300c1c3e80c01e20449220b181c40004e070307555484030b034441039019510b045a442e0041c10551224015a50000c1c01185107840302c3c0e580b00550400c032a5113540d6800244a8901190303801e000343d0510300d151131485501c503c0300004100844801402d041d060502d80400c0003409600c002c03c8810200c00760034246c3d2207110061800d41031518102031254400720000c1d19100b01504900c4100e02d044003030340c1c0082c00310041540c0454020010480c001025000700041000402c150130403540800c45140500c2540070705c1e51007000d4003007104105404210011040e2410260074030148071213290b400c4503411240b00c80c5040700e45910502050307020b240400e15103110700069 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 225162500 1250 225161250 225161263
    0x12060c0c050a05010c23030c0c0304180501060305060301092112090506040b0f0108031602040e1009170a0512090106120b0f010e250e0406170d02191103 67
    0x8011040d02d1080c034141c40c140c2c0c02040001803840204001004108442e01c2c4502400b40c0200122140b038610b45420303841c4400c5420041e2802214402000042440c0645060b5118018140800401e0035418210702509079840142800d0203689004041c901181911008002c0c5229540e500803101c015003104403202404100110354180c10071821204000d00085e01c00e03c900c1c007800c48618180c0324850560200042845040e00c1c41c0c1c0f0501108803914295489098100d200400c00038500b01d5485a250400448000c800015550f170118003040c8800b00d0080200503040c01e01e19460814500d1014005004400002c840c84014000013044800258031420150054140030709081c0010314006400b40c0003200c6600c81e090b402400040e00c007200780d801c1400782c022258400829140c1c0610160b481502d8194002005401d29195015460f584038801c05880300d91342420351040d61012040c40d040d20b60700003808540c0461099080300212031007070030b1051ba01a02107e01c4003204000246080c4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 225163750 1250 225162500 225162503
    0x603042307032906010801150504030618020a0f0f03030302031506031807060e0609013902240708030c0c010218040b0901030209011a0d0603080705060f0112060c0c 72
    0x496104080240b102c500540296440c1c0100f11103d0041140101c40925409640f11800b04e0344140052105550003180258411100d280c010304007652500c40a00740d4460448513078030b03080040809410350030a1900d5a028003800c003c40050240b60103845c070382d200b030544409000c140c1e0100225074003210b2285442c807031101c02003e003074407400d2a56240440d00e505001080c0148215074000800d00c5c003642050303403000d8005100034141a001401503800b844803201014081107210420004460103821a02c080c4186043c42010410b00340305218807d0801041c1c1001070041c03900c1e07401200154030441d019946d109824945030b4490000c0b030425405030002000d510350001c6840308902d84100c3c01a600700300f00f01c4041c401141c1e89028445003400c20b001c0650001c1000005009008040c8150684554899407041c50800d0085410040b28000e40007154148000907025040c04010040d05410001c54440c0c0025940352180c40c211400402c038004086030340383c41d03240c00858000c828664416 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 225165000 1250 225163750 225163753
    0x110d02011101060603020306180c0a03020d14010b1918030201030902010212031e010e071403060a1d071e0e0d021813150c17060d08041403061506030423 67
    0x94131141c01070040c0d0000c581d03450141040071600c811590030000c0e014090302051060074500710b8400000c0300603520078045146581d44810a02e61000f10840e0503034005e040c5a9001500c0300c254a090305440e04040348a00304000d074402038101c0e031400c0c40704004100da41c2403d000965103120310041c0d0400c032803110700c0042c140c404800c1001c01c070340c071002d1700300e00c1c0020024201c1c1d00ea0700c2d1002c103403030500151a0180029a980407042c81d0602403001180c00400c0105490440c1c2c0c3c2c1c2e05006c2c5901241441c0c00303040ca020741c50230710800130742104801030390850140da444046104800028812510b4009651051600d914420b0954a07411011500d050504148444c02c1c502942203130040c040c9818201c07101450010580c4040f659441040b400700c181c0d55a172511421040701c5103104200c09400a980080c03032212010020f102c078402440100001e185120300c819920040604002d401003200d00703030b103050381c02020060f1340300c3d0b003260742c810742c08140000e4202000207d00c007041c41030000300030203 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 225166250 1250 225165000 225165011
    0x150302030c120f1501090c0807021b060d020c0a1509050316030905041b08090706090e1504053102060301030303020c0703050304090209130209090c070f12030603030f020a110d02011101 81
    0x2141004e541103050b2850340e5010300030251012005c031070901f8110340103801600840c0781501e00740344050700300c1106c41004010314140807110710003c04990054407032907000c0d44180c2d5441e040100000c000c03900400c24040400214030f55880d031680300e1042c0361040c0306059981d002c2000300b601411400b806401c02400800030300c0659501200e2988103000c402001c12a8a0001044008006441c0c03040e00d1a50359001d0510780f42144160015101810805a10000305020300044d280d52240c01e04c80c0c000381282e44a180801c0b982c0301c1d003007402c00001e2951148900c0d0700310701586840c012641101d515140040c0e031031643d001040e00307159050300020a6400002030003e4100d102c0d402030040004103d92681c040c4404440c2d6401f2445000d4003280c0010404000410403030341d40010b004182c0c000d5440c005410103c0d03891120a000c0400590007007950750105000341a40004090072403407050000300100c44c80364582c815452504c0c4100f502c103907030b1002d46804591061451458050344040207109 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 225167500 1250 225166250 225166273
    0x4050a0c0b0c0f1209010f0c06180b0109090818041b0815010302040819030507060204080d08090c010c1101020a0b0f07080702070608010b030408040312090504150302030c120f 77
    0x9140d1000c07500074400d1040f508074102459012034500400310040921929003c66900151545c4400d0b69a503000d20120301309282c0802d000c0e011303e1401186070f04008032000a286042e52340300c030040e00201640c40c989241000020107800845800021344c28070100b0403901d00b0700040c09085602e010b400882c1445085820117504000c025016030865440c014034101032400460032405941f0501d40344d80d10a000a6202c0c040c1050003014441c024a049854440c0d2600e0300800d0383d015620100c001d5200046000b40b195001c0070040d046150100035221144a400009010015140000e040000310940026050380200162207040381c0c040c038a803485203050315544403000003c0742c801020401d404001213031607102182c0e08040d1889902d501051340d081c100b071810a90001007040354810b504000c0400480c140c103a0030070041020f6a24115100c0c01c1c80e042c8030544515101c591400d6980394400d00041e40d012912040c0e0303003415070362030f80d016140c0017610b80391500903243c42149001d07003040c2c044c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 225168750 1250 225167500 225167519
    0x32508070f0201020d02012307020102042105010c0f1d06041707050a150819150806060a0b091305090a0204020406110d14030126070605070b18070e04050a0c 69
    0x248214002d03000e440b44108038170016800e0300c4070048407000540208509002c0403009070785c0282c008085100050500e5195030030003042c094184220b515000c4e400041000304403003409580203c100510f41071a031160501e1000d400320800c080c1802c0f101d003070405404d003146c5600c02130700c1c0200355400b0044040d0011651950b11902c16000381c0340a9240300e000030400c9007200020000c04da910ba514698995200c01c90800517002c0f919400e010b89071030700d00b1011119070000d00d10010f00103290251445080002c00c00c440d003c0554041208003400b400140c907990340d0051120780304240454007190543c1d030540000d0a011030b010b0025401403021502098190340312801203501070b031131700c101d60350030b0000d40080d600c1e841500a44000c2076010401030000c0c54030b82c0c0810348558101800c02d04c160888404550030180300e60003101c00518080b40714803d010f81815101c1d0441800e8021001c44100c010f40300782c441d24a801494079040140c0b003c2000c000f000c03c6501c03400358025400d503550369150540728 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 225170000 1250 225168750 225168773
    0x14030c07020a080a030f0f1b320d030209040917030f15100c080c010c08070210060312081308030a0209091e0414010e03030901020a0f1103250807 64
    0x740c1c02800a4000400d80c80400605204042d80645400700c4550310300303a00700c0300303042000c00040c208992000c1d5141036050194803100d91a10844901400014466140c81e1140301440c2c1e1805184080200040c1c9040105502d0070101e501d180c0940da51402a020401410b522a070080c4444a0055211030014014000c0c600808040801c2c0300c4507140c18191041c0c60540d0320030140d000350003008074602180a8099401d01c0ca1040028a003030003103200d032150860304c004500030042080030041040203541030100481010740508104041410343c0c44100b1141162100344061022400200d5003141c264007241c45c5803076000040c10b6691420b9606c2e040650010400f13a80103202c40c1c0003248020f0201866031401c01c20b66405810141c0d115110103840201551045c5255540c4410100070b089080c0000c502c1a1411030000d81c0c1c94140460003010402c4d0051080c0402120440060746000088100c0325030500392403c120607104081c00f010002c200d4104020401a00010b2140801c801d40c0c021 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 225171250 1250 225170000 225170003
    0x3f0712120e01050304080405040504060615110706050408150601021c09060815030a060c03020d02070303090219031703040203031c050a0f0501050d200a0305030705010501060e1f14030c07 82
    0x600307003071030031a40041d1510300068030010b01d0400140000e104038180307171b030155511500540c000b240c40da41e180501404114811231030b00c006142c0440c025000301041006070b00509480c40d006143c00e140215003600e40c5c2110000031130f4404901c012410a80c803c00410070550000c0705a0011a241e003040502181054440e00010459040c00244103039000440807030042d0000d0042c000c183c1d420340ea0f85000b0505400361605055080c031074010072008902c00780038aa8030a480000303a40080c1e004005038020001001c2a00110014050000820350090b4607001c4194448481c2c50360ac85200190a500032012200888400807441c02070b00c02140c0c00170f6008446802c41042111a01100304056800034090795070800c2020180d00001605040380102e1401050004200307100c0220000c0d1001106620aa81366440802c0d18400d101007840342c107006102e0341c20305840c0d0141070790202d11002c05c0180d042e03905101241c048101c0a0040c0b4000c03144548181c505030396850022110034842c0c10a010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 225172500 1250 225171250 225171257
    0x30a030c03050610110a150e010e1615020a0b1e070309050d2d0305040b0906100e061305090318061303060902060f04030b063f071212 59
    0x215030501d009224542c05080d0180c040e4503200a004d20a555100b0f200040d8040f9102d810f81d540301140102e08009810421300314081400f8000f04003442c256041c21141c0202034011200714104d03c00042040002c440007041941d0100e003c9071001d030b041010580c0060400480d440801c0b0500001e02519600d1003013050a15441d5100c981c0104c044030449440200541c0c080d42e2200c1c045070290904000702208207090b40c00000402c280c00c1940c03001d145100c0040380e10380c014031003000a0b0124003603004600310002e00349450326100400c51840c0c1889070a80459080c00800d2607515907101101121481e40800e1055042c2220035964940c01605550080100c02410154600c1c01c482200e1104058100b405a200d095444420040042d40c0f001c076031018081000243c05811180134000030750160300e80950601c0c0032420f021040e0801c6010841c50411410f80055128404012404d020356551502c1c0b030f006a0100d40e6483c1c503109400207100c6c1501080c2c611b0800030100703146041c505641d40e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 225173750 1250 225172500 225172511
    0x405060412052b02070c125303040507030b060402072d020d06091a041e0201050c1f0e06010b0409150e040303050f010e13080c07051002030a03 63
    0x21012a0240568004404081d20580d603d03141c2e0101ca04103100c41c0000c0041c01498881690303a000e425140e0396204020642c074010707110f01400400c00c030040b803840e4000e42c04074080d44030308441801e03021040140a550411040040b5402c403000c00d2003a101407004038560394034103181c18580e9554071244007c031200c0107845c00040031400d05009030742c1203550100818203011803d0786200c101200c0b40f0101252684041e09030b500ad070740e036190035103001c5006400010b21103c050a0000c02141c0002ca0108a1141d201c01d000c0068802c2450b05828421441100164144da100489a078820a81401d20601c204240c0d00c02000d541c000e002202440c03a24208400503120075001e4035900240700d030310084141484104941040c50b04014040301d10180e25181041d01d401884c031614105990039000240e95008000c6a0400a017256014201c1990450110b05d0142c40b120700360320f401003000f0050301021035512207511003000306201814001704402c00301007450300029903a420115695000900b0107 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 225175000 1250 225173750 225173783
    0x313080f010e010c090e0c0918010e0606070b01060e0a0b040906082b050307050c0102040b09010e1905041a06070602030f1302010e10110111040f0b180f010908010504050604 76
    0x1481080e050513040d89510303c80c1c5203082050348441400801400000d0010010300350196202d811200791141c42180c1d22090f03504061001ca513000000300311074054281005110045440860054115946807508100107036228001c2a01a9030b168005903020718042000b1444584942012040d945204111500d403030f0b061411400c0e50010b82c48003000c07100c2c0b01c0c102d026400e10920003950300038201c0c02c081d843d2429004815089a1087c1d10251107190003040700d504a41c0d200b19007000190381110107000000b400c80004160342d44500c03c0301d01c200d689a16225490060854101070408000d00c0180c8030150740c1030100103580101d0780d521103612810009212400803a80e0a410309070103a40e5045041e10210a111540c05400420020300c24604641c407103010090084083c03c41005402640b02e03490900b003003c1140341a0000c0042440521184000c0500400a540202012540102d48032031440040c0d4200020349c1103603116509200070401407200000d8494051403048081803102541d0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 225176250 1250 225175000 225175003
    0x5090103181106090319051e010c02070b0d0b030f1b030a03090501030203071205163902040e06011212080f06010f020c060c01090b100b0712020313080f010e 69
    0x400000400010150b902c0800e00e04200c40600840c01000d81102c61a4000030000c040003820102e00701d5047d03000790481072991130030341c12002000107028000c0c003407000100c4010f034485480780110190a5070104a0598006c8503800c008000e00001c2e00381c54007660340407040d40c2c0b2000c2440091200713050710140d044050500050300303d417040d0035903111b0030040d0810004401030352000c6c00d920708006041140e24602e40c10340c85068000d0043c1c0080c20480c0d11a454003a1082c3d42e4100d000e2100c42501d40c5070740502401c05d540c0c00040500c0c21041142005900c0040c0c001c020b2004280c4051003010300104000040e07400c0c070743d19503014541c901c06076810722004445200d030440d8403074100240c50740811030b030354000c455021300080c0d2801a100300b4000c0c00f010440c43e800450398400648e4440d19042d041c03010208045070042d00702c1c8400c3c4507041c00c14a0324250740c030440c94024500d00740c42200104682c400d00a03182440c0b28030f003078104001d80c0c0d1540c00d5a6050000712100c0c240d481c04695400300c040 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 225177500 1250 225176250 225176291
    0x9040c0c03050f03070e100f0809010612020d0609050106080a03030605040c0504051c08031e0901090f1514040602040303030b0102150c0a0c050d020105160f1205151005090103 77
    0x9150382d0302840c0c0a0100d610a6003070304090051001d004401c4200d9295641d2540290642403442e50b07041b042c4a80c10303200a0034504090100380c0142d16110702800302411842d10122170070740680720318841031340900e4907100414004102600d0b07035103000c0c0c010954040101d62004014042d80e81440303155280c2d000c0004a03014110058080f0307404000c10410303410243d142c041c000c0c51002c00503861106a4449854075032007240c8822113070800009900c00e412a03005400e4000340140002c20042c00f1943d01c004851108887c05000202c00764003800e4444415000044800d1219403c0c8006003014600031020303400502044022900703001c80401254400075410150001c0d10724030780b00b5030711412052079841c0c1c8100703581c0080281c001500000b24208003c5c95015141c181d00009080c5003492807003414040d01c118007010401c01418020002c0e034405c1c3c8041485900800001d41074554004100c41c40350b80380211608002d0313a43d40d0450094012019180d5503030280c03014000c2c81c0d01b03140380c03c0740b8a1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 225178750 1250 225177500 225177503
    0x3060b15030114010305090102070f08130911030114120a0c0302180f0105130b06030c03010e06011407060f0e0a0c0e0114060d0c18030602070c05010e0622051509040c0c 74
    0x114043e0791641d5611a810454100210200040c81c10713880f9203d03c10b450320741d1030094850302c00000e900210003a004c0b1071000244050a0100b000f4004c8805070f0301c0d103100c1071040541403881c0c0b00410441d581d400c8510b10040800e05d045900c0c100161a103005201441d1000380d2041c2040e81400c0745001c84103000612404901c000d41916a00b04000c100e10310740318a450142140d03031444001d0140d10f82900031130054189100300b80e102c0d890f200d903581c09801d0051100e410801c07208500c2c05d1182048080d1600140e100b0b2000ca039406082c1c1d403800003800500c00d021510700c1a0045c0400303012400301c1da141515940c0b01400390603070703d845440301c031058103052045d000350003003048101000f4103034062038030380811b842d0001c0089038070114501c0c000c40540044d03070b06980c005a84020054003500440041c4001e09200c1d840c41c4e009000100c030f500492101041c01c1007043c01000041e207007114039202a000c0100b0300072901c000312181004982000b000f0030b0065241505401149000340100924039 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 225179856 1106 225178750 225178769
    0xa0212030c0f0a023102030c0904021c0e0d09030602030405120403031d01020607080103020d0201021c170f0103020a06050f04120b1f03050622020301020403060b150301 74
    0x502d40b10303180040c43c505c000c51001048900c415603404440e081c8000603202d581e550340c203082c00c0c8101084107a10603c00913000c81d200c4403c6c2114910300011400c100b01d9142c1040340581d03100300401c80d40c0c021529180c000c000060003a001142d109200342c05139000745500011040e51504250003c074041040d5005403640040400901c4a00820034801020241850341016046500600010b40140641c850200559000304000c058161481c83c9800741d4848a0900070541050307084166807603400040811050a07500b540541030b281c0081c48103102900d441e409440c075038000ca4060b101d10a00340400150700441c0e4400800b09406140320801c0b80c540754100d00e0b4580c0b103269000c001e41031200803d10100d01c0c0011480e41c0200d00444c10800b200300d05440d0101c4181001e00254103600000d0084200b102d0b0f03800458807000705440c0440c0f812240d0042d0400781c0000d018400a0 = true := by decide +kernel

theorem cover : BRFrame.Cov 225000000 225179856 := by
  have h0 := BRFrame.cov_init 225000000
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225000000 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 225000000 ≤ n) (h2 : n < 225179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
