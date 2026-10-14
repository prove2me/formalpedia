-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3392
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:32:08.172724+00:00
-- url     : https://prove2.me/submissions/1d024a35-793a-4d7e-8532-1eb7901ee215

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 609892086 ≤ n < 610071942 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 609893336 1250 609892086 609892093
    0x1518030311060a090b0705090315040c05010f0f09090e0f010507030606111605010311160804090f02091003110717030a0b0108190b0f100305070806010207051522080f 73
    0xb080780450384290103119401100403142c0c0d603078000307054560394440d540c112781c0b600c165908103151070140403141740b08520454481101502d030400143c0b280604800080a000030341003201e0a041c2d2003080001203030303400307540450310b0703141440c269042c240c5001c8841011f5080804121030f13a40c141d0080e408a80041e5140d0481c4090080e209460b0050304801a07036072090390b0010005984aa080244802581006145421b488505a580b1a26104400ca5101002003030402580c2000d215442001c6a554019441c28150f200040c4000d803190400c02c1c10f05a0311148140d0745a00c1c0707010f8521455003c801620040d509901441040d081210440055403c000c071840c41ca501c40c0c4810b600540208042c0c200301c00010410070301400100000c96080b0307101d205c1a140d1503071100e11862084240b610002810b003000480200814402000b290541d481035908120b1034030741c141e060742551805081c9603290301400104030400300440c40380202a0503a0313a03010824507804500700c0c013079040000c101c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 609894586 1250 609893336 609893341
    0x51005060120070e04030e09160e120a03140f04230d020a120204110a0507060e011505090a060b1306020f0105150904050c03031306090b13151803031106 67
    0x5030303074540b480550300d0495500025410494035104d1151150002d202e0f0400030300b000d44210118000d5074080340e8949001401921140c159a0440310b03207207441c801034600100f101c61201455a80342c506000c000d0412007000291a46410b40d00d083d00c0e1822044400590348a50300c40d00000e000a414490b0312514582215090f4603103000d4242800c0305038041c2040349180d20340485108000b0561209981103a2a4600c0d00c0c03059100800808429886440c1c842e150607890524504903a09207850302040ea242c080300d120000001c858900464004035926041c0e41c1e24408950007500803075000c1c403000070300412619404081c0601410580ba010f5084070382c090541c1d1802e60a0b03c1054540c100d030034107010289901c40c240b5a89055200340140308407040f4188003030120f4503507480320484507010380c00307a90203022595110070b501340140b681481050500c0241c1c3c105040b18009803085d1182d031141c00f200085c01034042e01c0b8400c05090f240c45614055641c90901400d1910361113001107550251000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 609895836 1250 609894586 609894617
    0x90112181a040302122206270b090448090b04150c050a0b09010b06040b0a03270602310311150f09090603060f0a0b0d0510050601 57
    0x100d1086405500030009400000342e1420903a015140d003021b0182c0e83d038840d0080b502e00320b03a10002440f051f5580c00c8104c10980c004d02c05c10200407900e0a01c0403501100300000b0103c9020780f40401c0c411140001c00d0380e031118022140c00e01c1c0403070005420101410401c84810a070719421032030b054101848004407840c81d000c88070782c1c031079014500000340184418400c004241c000c060302102142030055202d91075495407460280d024104031220441d07007040000f685003c0c01810070590081d640142401d04280006e12540078010781002015510500c1c0b444032000710040c0c0074100e61306540c0b280c41b00c60508101000e90301c900c00c0e185622400d080818490030018420a0b40c1c20102488180a82e0441e03036408959280340c88859070100e04903400b03a0403c1540c0c00141a41450305d03010568030b01500040c410482001045688a500903a041204a41494030055400345003200c1c0000c822144100251700d510541d10040c00c070307100d031241c504100d55140e44014007d031001d880e103010003d40d004 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 609897086 1250 609895836 609895883
    0x15050f0a05120102090132092803020102190803181504060f1802030d030c03150605041a040f0e090a080c01020c1501062a0212060106030b1c0809011218 67
    0x182d031041f0b11142824034090a4100c034042d050301030380100f42e944140c400b407080000055000c0035034040708582e00010011581c041250f0400c507226502e2860245880e82c071100d0090000a0400c07201000504c07a121401d10188001201490700c41c841c00d41c10b003800d0900d040205100b101035050b052500c01e03611407049007003000d800129401401030404049108048000d002c0307044040044c5626881015081404406e40d0b0010309170f60358800b600c480c070304542041d8112041c40001c0350448108424400201240a03607401e4030031000410005845003800d00d071404960b0341014043e804046140b0001d10410740003040c02041c0d400459096890080400c551004207124a0002c80c0c0b280c000b986100840203a0000056280c10300008146c040750003041e94003468404107035840d0048001030250640610941c0d201d95800c0d99a440c10200c02d06c91007aa100c000200504003420100d500c81e00780c2c0c0320f0360b4421810807610205010440d0102103070308585405000449503450039142c21880d0b1007090 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 609898336 1250 609897086 609897137
    0x415110102030c0d0c170108160f05010f2d0509120f0303070f110f160b0315040b0316260f060105090403110604030503150415050f0a051201020901 65
    0x30b0700350362801c20504c1100d0000d003000701503c400e00052481c640000240c2920f05030081c19000042d09050042d2070725000324040f260000c034442d0024003010b0105980c801da0b410401e000a09068410344103210441c1414101080b40d8501100204c0d00700e181d5a5000c03000d4950b0800c156041810034280c08804d40d1a0003041445407000d80c001d100088026200f0295500d00d25030f0760600040b9074849003d540d051102030344003091241e200c0040c0c40d03807001c0c0c0b40107d03000805110304403500b0741c01c1078220350b08002c90400040d4411034271500f165003207070381c10700021182c400e40788a403510341030781c0d90511440741c1410140d50003a901030303000d0080f00780310200e540601c115106010b4640e40c2c1c20001041000d42c0050010380411024141d500d15054041015901640c003903240c0a0322444c0c90400c1c80f20b04170410a8641c003850625100200d0441d5594100c020b070381c41140c5082120707040c040414049002540840d50180c090340c0001024901940101840c7e0000e030385007940700c04403508222909044 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 609899586 1250 609898336 609898351
    0x30e0102071106090a090603051c09030510020310090504051c030b090c1e030a02070b15030a1101051317160b1207020a0f03020d18081e070902041511010203 69
    0xc03000c0c0c4480b1480c15030001c289010005004400e8680c0359808101141c4080c1c10454035544207000b071020700201d400c00d03001556001d00c2c1c00310b411400c0d60785031a1030364240d07404001d00710380100115185521920f07468014100f034040c1001750346014100a941e51031011114038140c810a00c030349101620034040c000d0041000f43c0142071070b440380c1c1c02c1c005103035204507890541d002c3c40c040500c18a642e4200118043c200c1c0c0306002d40c543e003071401c125040c000b010340611500104806d2003c0252800305001c44a00d4100403645940460407005a0300361080c6807002100d44d940c010040703403220b16900341101d4908400304450701d9140070001525801040e000c0c42008580522443ca01030b100320380c005601103420301c180c501425031551544e82e042146c0c1022409600038401c009802c603800034155008040d517206d00240306140054044d121007030b01854040001c8a001c680c2c0021104000400003400030030002c40d030f61a9905000c1e204414108544c1001805084074440352000500030341e07006414 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 609900836 1250 609899586 609899603
    0x1e150922020d06020f030403120e06010620120a0c06050906040807020d08120f09060601020109020619090e0411122a043b061b1e04090903030e010207 66
    0x40c25001c00c200c0103801e000c1101c5480d000c010601c0000310550145000324804d4541ca54034542c41007980c0255050308031b04c0a030b00c0d40540d004009007503010444400e40f1f816050681183c0c0c0c01c17a02c0039030800c14054162504000d0001d104400b0359031040111406074040c500030000343c0c9034101c0076921810180d9019100d41020300c8460094640041813041003480340340c0a901d400040e900590002d03008442800d40300344000104460004180f10099200c1806d100801040078035900048050041c0328146902040800440c40002d000700c044d503015102c20800700c0341d24500b52800d044900102500c10380100000c0016201d401300c000f0b0b8840c1b8000d155054001143d00948042c00349220710300780d169015890300f1810f5980c03440101210304c030340f01c82c500e4040c00c2078500078844903150b0300c6140e201035a8040780804c101d4031075245006101c400390511107541d80b0701c80074a980800c0100c22540c000c1038400a0001100354451380030002c01486600d0034454115841400c07400c0703025195014002e180d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 609902086 1250 609900836 609900901
    0x60105060405060c100608010f0f02030727030602030903030907060908060a0f020d02070f060513050c06030a02070b151003090b0610030e0f0601030b0c04080709051e1509 75
    0x1601602070041d1101d040119910450348032048000d45032247c1c0441000d9540740740031a6605481d014169101c40030400c1036180d410f004000a01c64405c959102d00d500c0101d40c06901603078a49121040250342007082507480703041511240d0b440c0d61003a64020700380d1244be000000d80c035001c0c10030f42084580f400d01420381c564032450100701403c950291102e8142e8200801d188425251002d043d0300c0e4060090708103184020f04d40501151005006444403003003042204001584c0004c50850403070054401503181e07200d00a0241c081c1c021108010018401d070420001640e581d0783c40c081c40000c08440b84000c00440030b03400d9044403020400070b4079851040000441da4100010071011144982c500050460140d22030726040244107466544160010401001070084880856801180d0303480864900341c640881540d55018a10542401a44800000c0ca080c058500150182c03600f01d4001c208502d0310650002410880c10003080c81241d0000c0828034410582c1010400c2481c90410380c220321 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 609903336 1250 609902086 609902089
    0x5030a02070f1401050a060e010b0a0c021804121209030c0b13140708060105040b06091320220e130c08010c1815050403030302090619120608060105060405 68
    0xe50001c00140c404099494900c000140310301c8003824104520800042d542c20500341a50664043d42c2c0486003c0d1484001840f4000c0c42004460505100b424218805182032020540c000b940034060881c0c10000010401070080f2401d0724410315010365103a107180c02c0005c01040c2100c1c192000a070006007040c64120016020089941c3c1180d085031540c038048084c0e640f400030720030b50b5110398106074010360130400c141001000803601404040b207041c011010502c0118900b806517021907446500183d07007003030940b4060b500402c0300741044a64541a686d01d002124017640c80321400b043c44000c5001c401c100001c40680d14415540c44264100040c2c440024244501d46082419208080100f00c0015441e80c24850030f95402c4507916015031406403008841700b0380034654010305010003d4500c520b65603a001c0211029280c1c127080042c3c407451b4400124183e40155080c2150b44180c200032603454a400c0b1003120a1000100d8040c4005500c03007050039101e04003841000e4201c078050106010720b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 609904586 1250 609903336 609903341
    0x114010e0403050c0a030905012a0b06010c080d2c06070503071704120908160510090b120a0f0204080c12011b0804021009081c11011409060609010605030a 68
    0x1d000e40f80030703400c1035180c40500b400c00900700d0084011803640e16040140e560803910241d5040c414203002c405112494260140080c80032100421190030940001e6442c1c0c01001e130700011030f0308414031a0702d860001581000400401102d524201402c00030002640b5a0040c0c0b000d03800711f044007416080c0c44000c000e642642000c0d103000103208505d6008c03107507440c110030031500c6540a079401d504200c0949801820400d02e903000505682c010322210041102044e0440c41243c41c00d0701c038181c104100d02800c44402c9142c0e0030030400c0300b0001612840d40c84001c4000e0b4020845403008111150400e060700c0100e2140e840344100b2030704581d6045207103180c008151040100420000301c0e010044507480c004040480c01c0460224810b182800150b0404402c0c08443c0b900714100b0008803410322030900d6460002d0941c009070028015100302210340314101092020740040001e2151124100c047d45845d1070460b500030300342c894140095049d1900e04515030480d00942c0750146552641000d2070003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 609905836 1250 609904586 609904591
    0x1104050610140906070c1701020309030a0e1909020307021e0c04091b0602031905180d170c1f0603121d0a12110405010506031303021002040902040e01080114010e 71
    0x12000c2c248206061611940014039095114072880b81844e800c205480c0134040f42c0d50200102607105104200d2070040000440e00080c05070709006c410301114a000841180e02035a40002000591400040702080c0d0340148d40252078903020740300000d1000001000900401031442d1459010000b056050b042980c8074844041c0540d00301c00d070780c42c5481484e000d400541d03805000103034800160b040c0b110090108509400141c0d24205240056200e120345c0c00081c2003c00a10440d42400d503c800c0012504428104944c1c1751610394803888484182604d9843d21800b500d540c01d04e41658416003501403240401780d03036000a060b2204503481400302c400080020020805001000403040b16580d407507401c01c000d011030324100c8080030141c6840c6001e80c03229002d01d4002c2d4140381c018000c590f2030344242c0b80e03c141c81502c4403a80030b419080c200d10740041c0107410002103100003000724198040390010401c2c2c6189409244142c0da80c0c024071800c0301e4a0110038410f1510310001070007030200038091140c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 609907086 1250 609905836 609905867
    0xa06080d261021020301020a050918040c0b1c060305060105030d020111030c0a0225140303070c03020108100f0b070b010f0f0b0f0c0312190e060406020c0717030301031104050610 78
    0x110f007422940400d089034024440300000c5880810010494540040500c08100c169500414142419031301e9200c08080d6020710044c5807000f2031816404440078108001c80c24000f80c1c00e0110341d50383d062060f1181c03401e0003828068050ba0030b0121106005003e09a07040340340b419414078658828078804001d40011f0003990450060080c42000c4000211400c9641640303140380c8138201d4584042034554020200d4043d0198100b0b01201c00800d40188000045a40a080000240e650303001010f00c0b8002c160003060650301c038020042100c20564001d403010b02c1c440c000c06143d40e40c175204030850203a1944102d40030035101c0c2205001d141d4840003d0061201a850264144852044004e00b9a008007141c840707180c4418007000500000c0c0760740c00e07956041030001004420783c00684aa210b01e00140068405500001d4207400c9100c20041213000385a450284021f00f0303085410951268028482a2880f08131490079034454a13103441001e00a11000b00007260341d02e4000000e0f01c864940e00e0810 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 609908336 1250 609907086 609907139
    0x100602010e0604062c0f01060f060c02040b0103180609020f0d0c14010512090109050c0109050d0303020f04050303120406050a0507080103020409140d050a23070b0a06080d2610 77
    0x3020090b1001990003020480030011b00200c4564104450840710795a220b107080810800c4100034041c0c0010311070141580603900031500161903001030b0040e211814081e508890050340202c1070144030343c08908190b10031101d4910801c10002007001b403044924029195a0303902d034040100460b1038150302180441030508508008444400c0345055204440c10482651a500c9100400c1400d010242c0004401d003001e0251a080c000400c100c2948020002d007410f1b80010b80b0741200308003e0640340101001800c881d91406c0707449008d01e42c5182504c0885d6000e08017400b08880c0080c600506100e40b1083c8d4951115a107907800300700107041031581c2501d60340c43c092224030015200b44500900600d00b516825502e02d00c0c41030052081e03c00710036240709400f00480c507240c0304000204503007006400034100c02c1c0680355110503400a00403580282d4031031103104440bc60307040c1c0140320440c1030b071010004c0021010340c181a0100640040390114041810700c41d041c0a00f0340e040d07401c5d050784007004405 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 609909586 1250 609908336 609908381
    0x90403030b030105010e012108040b0d202223010e030f03090321040306021b0a060b10020d0e01120b0a08070e06060703050f0a050708030a05100602010e060406 70
    0x200c2d007102c81c00e030005050704404000605c04231343c101e0242170600411001c595081c0030b40e51500026402203010348140c590740014a510400410340044030010042518080350040c40e04030740d055a40002c404202d1162000c1075030055203c001104001c1303071000401c861200c1c0d200315141c048091006400d6041c010b400800c0741694a04001611f082d031751010007507075074240315070030545010040c00c1110030007003013840080c3e580d016250a45044950007940941c03642c2940e01400e1560b40130a02d65411072050900940030b0000c6a017040884242c180d501842c46901034804a864600309904003021481030422902d10f9480317541c9a81850080d17000005144c8a0b0100050100c4041da00414007548149002d0240c2803249015a40010080311450301c0e040090394080c01502603a8070b0b811407403a0101d081e800c03050103074041300c0c4002e501c41c58060b0381e40350500c100402414260f1312001c0e40d070540100441d1050052040b0050140608000c20303582d6265503604002d08a45c048000c60000d4040f503 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 609910836 1250 609909586 609909589
    0x30516080c012321040b07020c0a081b061e041a0406080708041103120702120601060c0602070c0e07030e0f190809040b04090f03230d020d090503130f0e01080606090403030b 76
    0xc4071340c0602d110f0b0b280b501150070880d000a1a01c9003101d61203106a024010401003540005410001c41c990742c2e0000d14817240300070018981e80030301900c40000e050140d004085102d1184014002d58500c0ca5410200e0f180300580c20419000b580103403808a480b050104072098001d2f00034582c0a8800d09640020015002c04241040f41201c240a445900031444030308505e00000050750301480603009240c40c0d89440d000414020580e0000740c921030b40000c8074418882003c044001601503445046101d04001400800030030698602d010140149000380e000d004010a01c1e10441c1c1c1804020700000850703444003207403a40206c4006502c00c0ea40c0100c03440c0c4d51180e0090594140c0146112010301625041c080d0000043c1e01008000c0c0543d12a03894840c40c0c004141d4212041c441001601d030800141746ca0001e007483c54001c0d003644808610001c21110300402c01040e1703414070200c51a080c2d55021080d1210100780142081d41d0850701c00100c1500344448096800b901038640400c80c800b9010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 609912086 1250 609910836 609910897
    0x60c1505060310060b040609080a260c06010b040815091f0b090708090d08040506160c0209090715090b0d150f0909060c05030727030516080c0123 64
    0x40c060300c0300010120342000008e4010704a60000d01d10348000e409003d9003561481034100004801c00700403a520720140e417840c1041429281c6990b506030880d0700a5031900c400c0c20907500b0512864016101d81c20011124035801c1c030b02e9a01030081070700208502d1f510350000c800e4080c19690008010382d512050b03805180d5900c0305c0c3c06e0180700780340c96412040c01c00000443c2001c2043c0100c0301804212020303c40050000a40b0701c0e844100c1452411500e01c0800c0202c5200a00f290007a600c0820f98051101c2c0c1c8002241190445041d0000f82004807400c40e025911013480e84500c0c54181303010300003040203040036001455103860100030340700c0054480191b4403202040307800444205581c2d100a904000103803080d81580c00040c1042415441c00c01001001c000c440c80072001128820b60500c2d00d107594516a110182d80d001d01510000c0036203034044984c004861150702c0c0725104034030b0000c40701d500406081d5205000106820b03007120410310004950f83c00719804594112001301303c5140341c000c44 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 609913336 1250 609912086 609912089
    0x702010e100513090c0207062102031504330501050301090207061b0e0406140904020f1c0602030a11090a0e10030f03020610090b0f01080414150f01060c150506031006 73
    0x100750028641c0c10518000f45400e2550300004240544189a5510025040c3c403264009c103000704007507600c1e964110100d00780d40480701c40580013070030f0a090f403503c024441c4480d540b000440350707401220f1081c0740e50940302200341e2140ca400b14000300010302800b1501e07001425054040e0102003242e042d4148000641154210400d00190002d4041d01c0319107414041c40d8010809040c51030081360110340001c400c164050002445012014409001d54640410900c04070203440315042c03400086040420181d030040300e0318039160380703000454200d8164042c01d031100c5840c050401340805050607090504203002070b000d2103851014560003c002440e00d100750898520030381c00707805141040690003d02d030303006400c001d21003410440c1c06540c1d81c481101c07090b0503080900c0c3c08245034886062082d9042c188a116a00701c1c00380300400c01203000110300c024000c03811042c030310403141c0c0da0300c0b0200c483c1e01d40400011710444000214038103040341608150741042d801000d551003207207420204012207049 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 609914586 1250 609913336 609913349
    0x402210a2003071103031603092d02040e061e15100f0315140d0201090b04090507080c0f040320180601020f0307122f031902030702010e100513 63
    0x10401164640c0003c1360381c940302d0210015401d5080c43c1d40f80503203408130850781030109543c80c1e5a890901c00d1015802d018500c0caa00308240104240c0034054009200c598241e006a08200c0c3c00c0404810000701a846100c1c01c13007450007480401c1102c41c9410502603c86c02d042c203030644180c0e4180da11100c4101d015003c6450f0704400201170240a4181c07103203100e040180b54100f01080103042480030740003144c45011180e6007140e0020f440140c4040303c1c1ca8024400e0400c0c0402c1c00b240c2003100c0c0d8080c600070708294407205515900c4000d04405803040320340040440d0024841080059208403603801c0d03462481039810306504d40140411080303508986100082c54a04e41800480e58041c491078603000301c200c0c0a14541a100c0d00e0304845600000e03813000401901c040e000c030104103110001901a090240c41011020881c03510390354a400074800601c20111030300000720010300020407550b25a606071110208907000c2002c004140c40c0d40d072001c1c0c00b03121040040c2040b00036602e045a029254 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 609915836 1250 609914586 609914651
    0xc01080108063402030310141f0306090221060924040b04180303060501051218010905160501090518060f01030f2a1110110f07030f0e0402210a 63
    0xa110402c1e00c50305106074800050300c2c001540c423821030780325448510244c08412100c51003054028104400503d99070b804003050500c00f04281800310100340001c0510701300c03c5400320260300d0320300800c1101032080da102d4000f024030410300004981908440340740c041c0b0040c40002d00004c2e10003c102524452800da100e56810b0303000c1c0e2010541c0501c03130200948400e20f0f280f41400c820090b0035011541c050080c01c041c0c54151300c0d201109600b5000708071410b6000040d43c812100e401d101402c00e10305800380d01d0102d0303540c14000ca43c1d424400000c600107a0b1461001d01c55890303141c00e100356005040c1d8220304250f00ea078030070301781c01d0201d000d0440042001c03010200d2401c403139070860000b4140d02841104106802e4580c40d186540014503081041d040180083d0ba078806640404051160030107140d20700e480403c03079906250f040303040c0440852040e164103003040007402c01c000882c8581c2e80c01c2007140448000440d84c0d401c800d0540c9510006108001030014152210b02640c03d04d00744c00d1051000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 609917086 1250 609915836 609915841
    0x10306090b10060203090609190303111005070c060b210c0a051503060910030506010e0105100207030b0114010908010f0207140a050a08030601051902010c020c010801080634020303 79
    0xa6400c0c10164040154a41540380a080403c004e440e4460310a130780e03204240218241283d503a41e0b90000d60b0211806400c00d200994034a0b0180610901400d07070301c520302076140180d081540790700030507102d04416039600e0000e840550340e0b80e00a03c0900c0c84075410103107203107919000e0020f03801400001c2d07000380000d0095442c0790013040f2000304650805401403000c1c48403180031141000540350408402c41c0e0311b40c1140e03112032507000c0c054075562003d00103104100002556107154030b07075641030b6201a1015111100365400503695004140300040503c0c0740c040040103030480385450009034800500d841c1501650340e84029081d0358840e51044003032580000c64908115031a101c1d43e048400510190510000c26281d0903100d1046110103401c480c40000054400c0e88a80c0440b4402c0c80c4d210314032302120094503002802096601c3c00d001c0035100d400c902000940c02010014102c1e0a044000c00d000e0350b0342d003440100307422800841c9404036145006441c0081490900c034042d010103500554692 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 609918336 1250 609917086 609917093
    0x90e340905270109090206120a050f0903090a06030b011101060f051c0b04030309030c0203160f0b070b010504090f050f0604060b0a0803120405100c020604410a0b01030609 75
    0xc0110703121601c1140724841e091040b0780c0c1002d10050446080040008041030540003060300d034404c01c04640c5280d184242040086600e544c001802210900082452030391086412642c912482500301c2e485120280e0400c503545c840d40010010890607d4140100c0c4500c201090135241c480c0c00034402d150303c4580034019414140213000d540c80e0380303c946220748211a03d80755000d01c4007400140c1015103420303001e001e240c01482c2e0860001c0c0d0107001c6400840d01d0454002801206004580206054840c0000c2d0304803060140c1d03110641200c00528180d00c0c12007004020440310380300f114012801400200403400510482c801c101028018120500d040d1600600b00d4040d040d003903201d40d02a00041c882c124000041e12000c0030fa20070300e505a5160703400c0c41407501c05d1a80d02420000d0609088008140c3d0108049001d1807041c101c01c4890700401d001c0000e00684481d00d9010b401c2c445a1041d208030020440d001e01040c120181e0303d02520a4640c200454001d800c1a60307900d0301ca00516042 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 609919586 1250 609918336 609918349
    0x10120506090d020a021309030306051f08010512101802030106030c14061206040b150a0201020a02010b1f0f050c030a050c0f2128110706090e340905 65
    0x2d000c0b44041c00b8018015800101810001d0390500100c1c0d42da2206030041501903801170001e8a00203220301c040c40b003101185415803011f10301c2540001d0700c0a000159504000c011144003503074200103000c3c1404018422030042580c50388014a5034070021000015841c00e100d8a0041c5010703540d071034161030510600d012800d450700c94403802140d0030030440c0480a040800543c000030b040300d02280a110480c002503080004000044c181d01c80010400340c0d6640540c0141034616994009018403114181048503100310082a1100c9100b00e030060000346204400d0340d8240c0320f4601300340b4201a2129002071458000300f0b1708001040001403591748640080100c07040f40040c0c03100505007540400100050709007407004002c01c01d500424000404004402c09601c242194505555550b164110040c80c904480d1200c070a036004003900400d040348500540820703910014105001ca0300e401c58241d104550000c100700d8a000300c800d03404140c0d07004a011951000f0f2984c7c43d401194100000c0248 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 609920836 1250 609919586 609919603
    0x20f12090c011e091a0d0c0e010f110606120a0519030e09161b0b1e0f0708070507030e0d0c18150b220603020d0b0411070b1012050609 59
    0x1101c0082d0110600c45039000604c00142d600b240040c080d42a0700c50048103150003041c00c1d00d01c505041c80c0c2845000d03644824500d2903110300366200e80b0000180301040c1d4000b414a41c40e2207080c1c02034070004070f107828240b10b103401c44049541207810031742c241d4440e0780c03c02a4500d506c030840e032b00000342c80043c16409295800818001c55200c3d54506200001075000c0e559203b486042c0050700d07080241c6000c01409803500399410520303500e964507200801154040c3d90307010032207480341480007060000c2a80035455100b180c00303864842d80341e01d40c10001d0b20160480719049080100c6900a100c02c0d850745081b881085200315458050b0504044c5111100002102001c101c10700e05070112000c610070340b1082040728111007403283d0301c00d110142c501c03e079a02040b00d00d029507210f00300050142c0d031503402480c0d5158400c804020009051040000351058950f1600424006101c49008a0082c40d41c55803c1420749502420381585d5034020f140c903240075842601e560300076400708003072603406201c00d84 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 609922086 1250 609920836 609920867
    0x8010506060a02060403030c1e030605030d0f080406050c04050a090b1810050d060f0509061803130608060f030f0312090727060515040312030903050d020f12090c01 72
    0x20300b00086000c0096444d80300801c00b80030540c403034442a07580ea018200d0300d81c20191140540402292004000c1c01420b040d104d201c2c003904c50b00381480303406d030b106100c2c1d011a0452a9a4080c00d61100d44444001c2c3c14064101c1d003103107204101c0083c0d03a03641c504100e0014104520f001c40c1e0960407408100311410420503440b0880c00002c1040035122f1030207428400e40d4021116407134203101ca410080010030b07080035000d4802c0d00c0c1c0000d200d4584000900d040c440e02d2500e191038500c01c0008007003502d0780544070512200c1d1003609801c0c4800d9005064003031f40940d000d014a1860800c40d400680f4140030f0185d0402c094000143e0b02c440c3e40c42c10340740d1075409400b16004003040d624042c0c40024a0388800707a209640b075600c1410440889544e044030b0002c00b002850803000c00c0054000806035030051000300d5030302c1042d0b06180e112a0003405038020854054480c1401c152255801d1400307580b1401000003d054200715560b00e803492040400c1c02014400028006550b81c0b20014003c0008103c012 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 609923336 1250 609922086 609922099
    0x6120b030a060903022119032c070609060203030a021b01090305041e030b04060b12150f0915061e0312030f250c061b0309060b04231b04080708010506 66
    0xc62602e4006d004c8415040100700d6040410041050440c02000e004c03d224112265042d40c18206090502c02248080c5101080d1600d1641e45e25060313445081b5481601c025820500014071041140e030b000d8003101c03403420b01054000035404159400c41c2d4842100314040791000c03030f01b40180d00c0700c01d5440107500c000101180881d400c50300d039000e5540008000600b55919420405205d49507440c3d283c102d480008101d40655606041c081c01040d000c0725513400302018207001602901002881e4548085408100c800e1501c2c0c0d0303001e20909d608812443c1000c0c2094108010060f2010066024021408501241c40341400301840840e003a024221041d010080b145d61100e541c194030707045151a9890515541c06040d41c0341c200003600402c903043d105016100b03041c020380350301900f18015103072040f401080010f0416007003000f222805658001610740040703d00d150001e90041a503006661440c040d0344240600c0080ca4442c1e01c03940144100e0f401c0f80504005290090052503000f030011200d1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 609924586 1250 609923336 609923383
    0x1407031e0c090e090606040b0a0510082e081603150b13050a02070203060105030607021e12040303050403120c1a15091005010212030c0406120b030a06090302 69
    0xc80403403014240400644641c1d0301508440a0b0181e80168001c03c050380082009140040080380c88141c1158542d0003181009140c18207460503641210507213400801c80455101e10540465030898001c0204441c803500c4400c2103202c1456130643d0150b140c0070700020040e81d0a2515440c140a0000d00701c0445c0300404d8000d00019100c090f541420f2400d209000132001002800990351150940003082030914007814461045015001004031030700a400b21001030740d840c024103907140f00403103040300107030000d00c40e41120140d030200c0c0300350440490702122000383d080d1108860035032103a80118003013900041c1c100200095511210542d00301810600403c0e011500c07040f0481c4101502904103d01c440006903085001c0300c0f80240c0500050160001842c0501f15030034880700318001c49000d4484d0800c0510850302450440e440340e02042c11117410185860340965681d140e2840030301c06a5250012143c60361401c001001080d8083e2501027101c0308603040181c00c203800000401c6189580108 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 609925836 1250 609924586 609924611
    0x6080f0303100506030c0f16060e0c10050901180f26071505130e091204120602031e040303090b07020303100b0d021c02071406070c0201140d0906140703 67
    0x3850b008841065641c19601c1d51500c50442841c8141c00c4800e560740390100b04140c4543d44040081812440742d5801c00101640030360b2150387e02244000540d0000945c00d5000d0341e94407800c05041c40d18070606000409028458000b100d040300b540103c20300507859078040080ea80c0c046509085d00700c850341200301c0d442d1510741d601e88904150140004002142c1c56240300244520b0071a0641994000c980b60704a8940c0c9507030b843c4540942d0f10b42c015101d030079068204402200100c80482d122422500310303410341ca43e0703074201035080145000302400307120a0b0040814003038000c10340b01c4c9100e69000030300659a86060000310f0400b4040c0c400b190b00610402981074011240c20080e01c040452003611400c4083c41d000180c4107943d01c5850a85d01009000039109160300039006103031141684820a14440c552070740c0d1141c089030140300103481d41d0f494102550280360b074400d0400c04545100d160a40d41e40071002654114242150b2059032069a807019080ba5050240c0200031071400f030080065089 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 609927086 1250 609925836 609925861
    0x8010b03040f06050f070311040b070b04020a080304060807021e0c090a0608030705031803010209010c06050c0f03040b0a060510050406180f0806070306050603040209241306080f0303 80
    0x905801508000046030034002d01d41e11081206501c0310301400b1501d8460070310103034608242e444e01d0202c1d050844d1440c4a20748001541c00740c81d00090550705050007502d82c891048000360050382c000d40a241c0c0441c4a8400380300400107000c854032403c00b01d040c88040249402101890018100e40780d034001403460402081d0101180e400300c85043c0a902c1e9502a07000404081c1d00442c8144000035040c42000008005005800c103001c090300a034040001c01e040c00e03449007241d40350001c0e2190314200001136056012070380102c02c035122107042c003000b44030764040e59206a80c1900c0230348616040046005030f5005c1e40300601010f45020500e0041140c000e40580070318025482480a4011103401000d5000300140c01444480900c50000340d031350b14901c0c2c13500c5041c0c4042c400070303051204c00b1940d0305110341243c0c082d6601500501c45980c0d0118076030600c180103280318022240e03030034404c0c1140e5109400700081c80500580041c400d03250000d0503207852180455a1040c1c0c1003482000038855008 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 609928336 1250 609927086 609927089
    0xa1b12020a05040c030b03191b0803090d0c0e01060305011415090d0f08130807120309050f030a14010e2104030303050903070605090102040906170a0210050d050f250801 74
    0x183e902083ca00301128054010b0503140000d1905841400d86a5016085110702c0347c2c1e44c0750060030014115998103040500e158428001c840c4079500800c01c16003281003510140121502030282e48030501e40b1451551a4402c0a0340200e0019440340010321000303140c000e1207800c4240031142590000011a10501c0b14095010f40d0b034498071282940a0074400b04c03190170896142d20021013036a075075441089024040040c01503101a2086040c00720b00d400818050070741d0180c040e01c03907010302c910340030410003400001c00c42c040d0940a8440c40d1070004a014241c8500d6000c41800811500030100c1e0340c03481c10381c507404000d118181404141500200050894007900c0d00343c54003140640d03030030000c0c5103503201c0c40400415091800302000741164040d03001c1c0080e20601c03001402201d6444082d4588031080d180c54000340c3c1c011204c0700005140010141d50f2501d0681482e0742003001c039606d41c50440d0000c6032001f1245074000f04100f034028811000405400d14920311a5100f44441c070b0007030148005 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 609929586 1250 609928336 609928339
    0x7020306070e041404050d021e0c1011012d0b090a02091c03020a110d08030f0a1104090204050f04050c040314010b0901120209090f210c0a1b12020a05 66
    0x10540c20400c0d111030300681d9101e03401d080c4c000d48908046c03401a540b441c003460f00600501510200d5a64841e5218524101c0003501e0000d22200341d6840030000100110140c4500784010614600340a600a001d1032013528455403158100c00f904191494400c0c10f02204160b50702e2400b00b04103016901c0e408125041000c4180060310b40006002045051442d412085081c004000346002095400070340030950505c00c00421441da0a104248140218003040003008584e081c000034011280b603900700342d48001c50b14408201541c10a601c2d0b40d06510540041240c2900007905200a08040503001030340c82064030100001e1038104140440c5000e28007008181c1545007141310b40a11003500b101981d2000108010040d5075219001c4088252410040717024841c803d000440a00d008102034604400c42009450f038030a21140d88004505018281c151183c000e0000b400100403c11600360518403e61840f80ba106220101036031501441d0b0105480da07800c69900c000507100d040c4440c048600 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 609930836 1250 609929586 609929597
    0x1b051302070c030b040b160305010506070f0c0f060f110c0109031b030c090c110a0503031612020708030601120b06090d080915041409091915020c030301031203020702030607 76
    0x78145002e010b01941580054105000c00060005103c1505c5403540103010120302468201c0c610002501644c90034882c65030300010a1101c40046114541d2683d80a0700c15050324100e00d850310f80c10464001203800040c001020341c0081640c454004003000d40c3c0d400310380020b140d180c2c403001c0000e00c0c0400c5404028203600b242c0d0f14980380d00445583c40e80117140d00c014901100c54544480340028543c9a94203000034a200005441040c80070030110007641d0804051b520f5903540018020303242000303544803c00c1086a000e160031008040c8043c080300b80c03041c8442c0341d076401c1a00006001d101086c9002544510301000700707850b659408200c41050405440450b283d03420380c140b442c40742c003ea40b85650402c4004c0d088800c06003640b001001603403140c070b0230f0800b054214820301c03000c0f550481c0c3c1e07625540d00c40f4030314408120351607610101c01881400324040351040030314a44240d8200d100816001d51001c0014020040b03211a0070354a02664a400c40c1003c40940003c0d50720800602207409200 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 609932086 1250 609930836 609930847
    0x8060f01021b0d1502040308090103050c0a081602070503030c010e07050604080706030507050904140f130506060402091f0306030c05010507240204080f16140105180a0914041b051302 80
    0x2a54045a61340403402503000c54403a030340c9043c0440240d00800145000918000c00604041d9241042c0c40d445030041d51540c4065803044c0b0b91081c00f0300802084410361080d10700c00030309541d0070401442e100d640c1c88004030348142c43c07070480b52524040b82c011324401c060501c424080c40000140610840341c0516000c9150b407141002661706104180540d174100341021417101c0316140030581e4500a054081c180100d0786d4480c032040c80408103243c0d000300640c00c41c0c00890101d180039005051843d000900e510104664041c950200304000c50b41500840d0f100e800070000d0001a00700f440c0103020030b003081072920f0304541c0c0759031345001300a0020071031006940a404803881954140e4000c2d18207034003112203102802003006e540310740c500d683c456a00070b03a0001103025a01c02d508400c2079903040e11103504240204146800b1031186600e03c0360800c1b119000016040902d0082907091340c41c8184100c1c9604040c1050b2001003526074412000d02d450110070090382e101d110a070358546c10004001a00c50 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 609933336 1250 609932086 609932093
    0x2010f05071112010e0c042d021b060714030c03010915090f0e01050a0608030a390317040b01050607051203010e060a0e091b06130608060f01021b0d 65
    0x1400b0b0b00301e030341d50000018800340680d03040551126801c40c1c080380440b400581d80710108416903100c00e130114031010312000d924825071a5a07002c0d60500c2c40c00720016003000380340c260580824605941e600181d82c40541409070294010110b6100c5410012100d45585001d0072072000354030062261882180d40d8081d0401541e80801085024010f034150030710066840142d000b016041212070941154600780100740280e20b0361043c04110f5107800d000d182080c1c18001c00f0364407141810140b10310b1880c44d100c10120805150640220545c21103038508081c441c0d0f09005103420100c40031131401010020511000c039040f126410b04541301201c1460740c441c99840c045007800c8562a99000100340840085803541d1211181445080b040d240700c0c281d2a07a8a2041c034140d2003e0342c900c11250000f40707901180882c0b00c001840c1c2d908000e4501d0f440e00382610004003070b5800030303400345002412001c24000c4502c0d00710b0080a141400748000d020086000515040709203d0307000580c030501e2a00c1c05070041 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 609934586 1250 609933336 609933353
    0x1c030c08250b0603010c05031b03073c0e180603100203011202030c030d051603031d0a020f0d03081f08060c07051e0618161d1302010f0507 61
    0x12501c140402041c1d49080c2c07400750405071050311014403c4d420702c2400c0c192284207409070f0748151821034603014421101c4c0240201c4c0d52018211030700b001070240c00305142101c21011b00c084801e00c0d074294020302200310341c501402c0c3d0000d1002d03c2080030416424816030740c0ca0484944008031790415a081d0f41b585d02c0040e1a0556020759000c8090000c00006000a110b612204c1814020b0b41607030032800001c010540c481010b01030003804140c080c001003102c03030b2108002c1c0c52003503ca8200064918109403401c00c0c00412500c0756240ca900081c55002142480035241820080940d0030b5803000599560251818000a14488506c2e0341c90054480e0380344a480080f001300030038001c0d21040e04080c55880c085034001c0c401514180728007000c00c030782442000800b0100da011400948440d455503c40001c8100c0700c402451000e1150410b01c0043d80200320307001000b040c2802c0c4806244100140c20300d4002030003456103cac2c0030a441d540c81c0c0980d070010b035902240c0d03000b454026640d42c3d861401400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 609935836 1250 609934586 609934627
    0x403030e150412081206010c020a0905070509120f010b1c02040506061b0a0506061f08060307030b0c0405030c03060601080601080a0906020a030c080622020a020102040e151c030c08 79
    0x100f00d904502e808062110b0f400052001d41d1084125011503600c1c0c60041d1062402d0a10094118000b65410064002103030310203034002c9424034045140011980018004a9808180e0209504201c0380c102580c00b007407090005482c1c06036200d000d0546c03282014422030f41a0340300a406180c0300d40c00204650340301c5044408580c5580030418045800c1070840e552601500c1e42161107110b02c0c8040365045c900744c084029047c403d07141814022000810440d02444080c0403103815109044000c40010f03441580c10b4841c044484e59a92a51b10780001c25151540c0c01c0c039124081e410020600c01c040c0d1b4042081e6030701960a080000e0507450b007013841c00042241000c0503142e0380c80401c80115031a410303000708819210039907608555460f03070010000c0900b8145d10b11101c00c0840c0a0204099032640c001d008800114000142002d03a41c50f200d00c2c01000807200c09035802c00c1c568180003030317203400411300c001381489000c03060011200350b9026022010a10b0082d040c2c10700030900110402442c1c030841c8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 609937086 1250 609935836 609935849
    0x50a020f0304080c180c07030507050a05010c1d0a080309040c020a0b27010b180907031403040303080c040b0301091a0618090703091110020a0c030b0f010b0403030e1504 74
    0x20756543da207016160700d42c141407040c2c0e40b20742c1d403201e610404640b04550050203034031041d2001e0300d007490701d035010744031540058000c4403180103504614010440a00c10305070304114a44514651083d020a20702e909a10b0304101d5100d900c01d031005000070b0b0800419595660b2058400040d543d0000c039041e0f19100804500424541060702007003100c1622200305040103a0500c00b0085900346050381a090381c07000d0b035040d40c12072540c00350071508000f6008500d07000f00c441d0095400309a205d880b40c18100e01d001c0f419035015400001c0030020960b018102c2036020b1503109650342454102002c801d86480184518170000381c450040d1040048084410308001d44020015680c52a40801510f0b605400c1d4040b148102240e90008040c01d02034002c8000055015081d1000209080108090803954034800d0003148200640c880c0029101029071002d0742c010501c4021a1518108403000f0080507042000000d909202c2080002d07001000b00d0301c4c480044a08001c442ca01041449050099034402c8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 609938336 1250 609937086 609937093
    0x3050703020a1e092c010611060f0709050d2012070b07080d06090f1a010e0105070c050307061101050a150905070e04020f07020f0d020117090106091a0f03070b0307050a020f 76
    0x402c0c0310800702176250031122010300c0c0c48480e82c1e030b604042d0340d1340a000c4504103054100d04006103c144e0f41c103488039440203a0342000e00859441c1c4000c2403280c0b80021044440d6817000c10100b43d032520307003a4100421003084130107900020201c100c164580c04c1d0b43c4940c2d08042400b0805030101720404040e20f041da44024420403156a5950f41d0348050b0a0301d08544942528104521004401e07001d1204400c0c80103071030b28601d060064004550551201000380c030700026120300461a90b40601c400300040c116642c4001a0200500305142110b0b0090070003c80380c0e02d42a90740c3c0a45455400354001c07207000c030800259955031044240d03101501501e40b5907005200040440303c421103403001d440d003213000742c4400f5004500341c42446144012020b002c0d0206800c48030007003c45c02d82d0a81298031050f00d4002150305641c0d00d80a505452504404991081e80c080d4200e0745030400c034801d0710200400702d000f00f84080c50300300c1180303203480040c00750340c1088070001d010003105008001e000350031511241207 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 609939586 1250 609938336 609938369
    0x3070c0807030e090f04030905010f02010b03011506140403020d02092208041706060a29120a0c0f0804061d0604050601090e0304060203040e1902071203050703020a1e09 74
    0x105a58003c5682c2845080f0040100320118154000c25101c3e40c0c0c1902c4096031507050100550380840c3c5526500210364881c1880d64040c3c400303004050103072060360b0000c2c00881c1040300103080500c80104548200c0300901c41040503a07107071391150040d135030107540300c41480d140c1c40202034a9415526407608220010380500302084002002001103401c441d9a40d001e0320703036a111040d207400c001d0f0380c3c45a120520060520944800f0003d00050a5042c0101c104440c0148840d1040303030420b4440c1c040804203036007004400c04460091010351542c80c03408441500c28041c0207400c2e064040c0000d04902c0eaa81d00010041d0200c00301e05242c1d83c6a401220031740d00d09886d085036140024056581c480d4105443c84600040000980f0240c0380d0741d401441c24181030001d6039540e00b10003000031000b240f00d44a444118150780c401001114041c07418040241c1c0c40705c2c0b000d010350b0805001c2c0b00c1058810003484000d02d510040d010203424806088a44e1035046000c1106d00c03004036000011b58a106040703 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 609940836 1250 609939586 609939593
    0x7050102130303030f02090d1101031d0705011d30151501030608030406180b0d02070302010c140d09020604090e031306020706080c0d0608070f0806012903070c0807 72
    0x101d08080b41e110740d405010707403215540400142d00421484503000301a441110300021105068007400c0c0c034043c035000600c03d40700f8410080540102c00300c0c210a41000300240841e5a000310102d59045420034004045041400424107600300728000a0019000d80c03801c1c88410007076903154009100c0e4900b1594414940c500702840c8490580700301a070201d020604a00a5029000703440440700c1e010080d6040905d03100056030031000d120b4003604043c10240c0b0204a50310308502900c081e1805000050301c0b0340b807a180203400c403480c5584010a00882d2040741086417840740454a00d02040c0c1302c00304072401d2a02c0401c0b4075000e5034100d85911b50400361a407401d144004040c000d00e841303480720140300aa48135016130b141e01c017501590001588040015064141c920010501110403000001c0c9141e903032007071141040c40c0d80d042000800f0b12040100f0441404021a601401c86004000300f646541c482c00a40440300d81d05001c4c842d500400050030340ba000d01440280290051042c40c0d03901740c0c03482c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 609942086 1250 609940836 609940867
    0xf0503070e031c2a0c1e090903050301082b0c0809102708100c17010b0c3a182615010e19060b131a0d09060207050102 52
    0x1650509220001d10040c1c2190300365031440314404d90444044e9003003178285000c0c4d10348560207581e0000d107040c250303000082c00101c612503204680d00940d69261603504129070242000010001640d15661103011003c0300044101b00c05a00d0850381000c1e000c1069600c0c2814250280e0101640c0c82b6a1808604420350f800c88c003188900d02510341d03c1c0154032104169402e0002e00f5025581c4594049900310010604941c8009070440d101d00b44444a17034030488403c40601403d822407010200f000c00c0900d244481000b0303010341b809007155903807046650345140114015038004401842d81990700c010341c10354058040720701e41d00c242040c000c8520b42c40313114245905008d1203609800b0f107482c1040344d40801011884040d420804418500580d107041200603000001800500304440d40c0c4681ca8019803042c4240c0c4000d1990b00580e43d16041d100c904000000070a900c810320a4048200b60502c0c022050211001884030f00c10000305c0f40f0060a10314000c0c041c44c0030052075580300113030381440300b00c005 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 609943336 1250 609942086 609942107
    0x307140c0106060e0105030c0901030b040209060a0e01110106051f03110d0e190201120f1d07030c08150f0a0b04060305030d050a0e19020d0501090308070f0f0503070e031c 75
    0x80c0c540038a05076507130004407045d00c000c50b0080c8402400780300205d00d540c880d07004144080d50003000035080420050020300c0c164000c00b20500880c2201c620481c007960015180f0f42c001640000810010386064080342144651068400e509080c00c410500d066000e90302080e080c0510701c034076030f0b2034402c2c1e02c920310020a0303c00080001485a030307404c22660441030718100010b550603500d5180040c060b0030644043c010000c03400111985450b605901150110034403001e0900c2c0c40d000b006001d01c0c0d81007000c3c0b102c10702e820040480e04140300d040d0b549008580d034540c212071000840c281c156580306608001b8494603400342c1d44142444000070900500101400280a119000b0009601c0c1c903508038040320210f0030078030002e4121280c0841011070138408440b186001a1015003070122036071b1040d085400080c3d0480c00328030180f05000003079a0100e07034441c441e101800c240d03a80010018001c0d0441c00000d040c41c0401840480d62021a05c0520003112904030300090000b10400b140000740c12400c44 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 609944586 1250 609943336 609943349
    0x10501060f1805062203021c0204112a01090b01180e010902030c0f01050706020f070b07020d0203032d1510031107020603130f0c092f0307140c0106 65
    0x4608100701d01e051070740341e8802203071001000d061a0280d11540c58005c002c854140c0c0c1542907030b0450000158031040d910340c880801d6003c404035018124410041161900209030104c004140055002d81c640c690302c0c1088403074461600703101c910601c0b8070b69000d4903403000000e150068110001071040b26425040361141c03a1110140600500c00c00c80a08841807802c0c041e51551082d82c11088908040c2d41c41d0f02c1000341031524a0cd0720f51a41c440b0001d0341d0106101545000d0002044018041c800c00702c290000e00721302c007070001032600240083d602d00014102c015041b000c00484000182d031108103d0406588540341032551511a0464060b2440c500b1224012480001001c465038403070711492100c0034110700c016081c040e050b0240f00c8581c2006004028824024880b4000b00e4000081c1e0611584a000d00c0c6c00520309215110082d01e41e51420750310b00088d00507070203149034580300d21400080b10480c01c49891f40c0c0c1e8a44101c56420080f644402081000940074000c0b44046d0400c0e81620792 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 609945836 1250 609944586 609944597
    0x106090506010e0108040c1a1b0703030809121804020c190201022e0b01051303060209030c270a0b0d050609060108030a1b0f0b0a0906060504020c0304180e010501060f 73
    0x800401504c03585e2086030024030240c8041e205009400101204400402c00c0c200b46c1d9007810046890050710a07201803401507943c0c405901007080560042c1074a90000c5454040d001c0d01854441036899400341d060a02c032440c3c1e066400386400d441c1c907816107a0f2030342d508040764901e101901d1103003036040b0500000d900501278032828020b103030394094031915010b0303201b204c0c1e035031406100603000020100c40c00d855040100411504100694a02d0305078041c41c014040140e4401c3c00034109440c00143d0340b403ca0080e401c009141429036402408960801c3d51341d5080c0c0d509540b0008464028408218526403000c01c9000311001e1100014003148240300d080c0444e250369072514082903a80c02440c14030f100040d60b06d041c000b4905c8200600c800000c0c464110840410f10b256580d80100104540c0c2c000704a5a0f03079100003c0c02024024400101300a6600f18902001900039903181c0c0300314020101c1120806200b40301c01c0d10194480526420000020411035854040081c480300d4901401d400056 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 609947086 1250 609945836 609945857
    0xf03030e0303090a121403041805060f030f0601060215040c05040e012705010515031c1b06050a23071d090a0b01170609041416260105090307020f030f010609050601 72
    0x3040001180d0555181404100c400c2c40307144041c0d0040c3c81e004140c1da802210941074845d09407010041f123b11030400d00050704c41d96040080003460100a190a020441d007a0030a020101d01c10f801c1d00415907600382d6012480391244003915000d001c903911080c1100e200c8070300a034180d810005948072224460f5000784101d445131194011100105110703154160070094207500c1107042c400ca94000030980d8105054092125103010000c2440c004058403071544130010800d118030319200c0e049013030080040040108003c145101c11643d4010304000c18084100ca40240309000300900914503100100442d070b0a2038580f41f000b003c0c02c000c002c494040740245010701903890700c0c00900c900c5580c001d03025032f510369550380b159441e9804003503a400c40d50280f80c8400815000d02c0c0e2132480a4400307200360227407044034124200c1d00c0956001c2a6001a40350100307001d06d0500100807a84502d0b0104e0381c1003101d441c4100040e003040f1048a050105620b04000001c0c600c5581d08140c0c030524098892001c4903 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 609948336 1250 609947086 609947123
    0x209040f140126030a020703030f082e091509050601110303060904020d020301180c08013e040f090b04020a020604060c0909091b0f0f03030e0303090a12 67
    0x2285a10200c00052014800511440c20420308038107691000f00000d418201030030340a1429544075990304401a0041070b0148249a00044980c224512500e000b000910707203032100415401d40b25100032100510320784480900ca869180c2c3c0005001072203030811003e0740382840340196035518440c00136282d007848001030483d8003c90982911143c1c0001031071455a85800304403648500030710407680003034007052002c00350302d091044500394103480383d01840124007410034148001c015804812141e0501255a10040d01110030910380c4440000129040300102c6030456030501c4525008020100810006206405003001c0401c4a003240410041c4091001c240016403050055500259004c44007180000c1e038582d01a80c0c0e186490f103801102c090b2684c400b201600c000f002e0a58901000402c280c14500c90001d20000910b20314080801c058030b001c06c1041c0c0114240b00280c20f0280c00307118042c01d5207081c4112603003240300a2014400580744c44240c4002485080c0560b1801d202c1c011581d5031 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 609949586 1250 609948336 609948341
    0x3050607140f03090313090b2107051e101d03030f0f130807060e01020606030109020a06050d0e030f07290105040905010f0c020303160f0503010b0723010209040f 71
    0x1038481e10314503524090b00240140d119500c0034203040540d200030000c83c143d4444a02001d4041c02001c0c4010449031200d00802054900c1d0038000b40350907100c528070103074405002954804860055422818042004d560008810401101c0a4020084000c0fa41103558130586040009400c002c1c1440307144606420b05070f80740604009290300000c1003001c1c14070250010b002d080400044402c18990680b40c0004906000d565844403001c02c5280154484942e01445000d47c8201705400800a071905074000038000340e070341d1241c2000e000300015485207074034507600054581e903041000c4959070400c1d0117a100c01e40d88a07030010b68001c0219030200c40c1d41510f0044c04c0350146401c46101505908080800000b4800340008031203035075032251440b6011405002d0b030b40d00070300590061501d91500e001c100c0c0f0f2910844451004008480b1800307045144c0050a0301d042d1850908040e445000ca45409070740d0b030038400d00c940c440c145140c15070b9803804015001002440c0054609120130703440302034100d05 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 609950836 1250 609949586 609949607
    0x901020706090b03070e0d060603050c01031a031c0c12020d08062205070201020405041407030b0907120c0e1c031d0102060109020705120a081e070503040b1b0a0903050607 75
    0xf0b09a410008a0038a0b44240c00000040c14014a010031194040e52000f048401551040707503181c000b900000c6a943c2c061050020306103010030f0600071180a40b002a031610074099030151480c00c144481c030760441c0b181060f018066440241c2223600480d80e54040c1d40c5e150340403541000201c00e0340018243e405c207080300a0741340c0e0f401401010700c1c10034a5056009814010450340c2190350031300000400f80d8880c00740c440000c208540548050400a030000c081c0c60342020040d005000d92402e1224056024100c5404070350800000101c90207600000c460b4005824207140d030194040b0501c058404141c0d0054604500c42c0c0c541c02c0400c071459044040100300398410b540560081c2c80104080c8466400501040c1d01c030301c05503a02001c010040740b0341d40e000341d402100068056010004070b42c00004d0b44507c5c80302004084c140c24580000300602030b10004200400e190100340c0401d02103060003284d10300390701801a401d6220510444000d01400640c8420394580c0709a42c04a004180143c95008 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 609952086 1250 609950836 609950849
    0x4050129032a091b18030115061b060219050d0b010e0102070501051605190302150408090d0c08031c150e0711030903030f0c0d0906052203060e03090102070609 70
    0x81d030b401d100010400d03e84030041028183d021122512000e154464000340244814400c6001014039a201031600f10303407040c54100c051004840c03040c02515000703031400410302081126159801c000d460000042d00802840310700b00801c03e0581507206801501520007101745101c10806240000d00444d40c0e040704071002c50158202038028011075208400401c00d50100c0d0190b0341a40703c0300e41c1ca02d0315103500d5a030708000c1141c502104008141d41480340c002e13002c580380510030f840c2c24640c80c1d412491041c0b10080340f00321415000c4d20100308546c25090001e040000c1507a8846200760181510300d41c0a0000703c10861500d451080441c905031010401d07603400040c14051651511000e4510848040e06266a032106001c0700025a9041000303151a0b80c06c645030326120782200382c50a181100606031038003881010750f024001d4591001c01c2d40e280c034008201907045111340b1002d04a58001503080502104d003040200400c590f000001048000401c1e4201c482c8580d96180c212400241d600038003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 609953336 1250 609952086 609952153
    0x2120136090c0b0c101401051201091a07080109060308030109050403020a060f02030711030301030b0402042403030e010f02030901120b01030f02040b03390d06051003050a29090405012903 82
    0x14403107800c0c80342700000e080408500005d001b1820761500000f00ba0711b401c0602e40c44900108008155600820301e81c018041a242880054110364495243c2d010500031019040e5503140041c09143c800c00a14004907000340c2d00b0001c0f90314207103e85000c7c0d4400ca403243c002c9013030b8103070700700089000208980c1240e400c40075501058030f503a03007004042c0c81d0040034a01e00300344102c00503511440356484540210710035169000400e11080c000b4081000d500780e180c003503410030300184030303540d0b04200c042c21042501c00001411085a00c0140c0c02400303841c030400c40c010310128020075840c2c080c800450180043c0d510000f1143c2e0021070184072581440822104a2a0702071100e5014420f400a0812403010501c0030407880d80700e40c003180980f4001007040002a8841c8240000b0000301d200f141c4107800300000090503c42441c513610f584d0700e690140c080c090b845640004060000030f500424a04012011410000030089440805d910b0140682e81c0300380103401c5441c501d5004080641c2210380d903080c86 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 609954586 1250 609953336 609953339
    0x2107090e030f120711100204140603041e02032a0a050907090608040515072c0d031d09010303120b01050310050906010e04050a02120136090c0b0c101401 67
    0x1a41c0c95801a0001044c0300550245c1c0700051800d00141c0380c0c46444800068032145403800d02e5000500d80c0b800d1038041c450070818400407548090501c1000341154044401203049071003c240303404e000d4030080c40d4180d142000360002400300d800b000400c2004464940d0010b89800800005403816105503000c10001c603410480c01c2c1c00f86a42c154018019000d8920040c0d030140c590340107100440710400056400445181d18038940c4242d00d038440340c45c1d103608010414440102d0f030720864800c2c000e41400110441650741001c0d444034400c102d040500406aa96520b14020707101d00200116903003100c0c203006100700780707502c103005030b82c4031304e21018030100c650b80b07041c0c00e0061101c00034014074104802c65640200f25265401007034014582c1580040e03a031480f4401880d807031041a00718080c280507243c1c000c0ca441082555600200b205012124101807411803041d0040882010041c401c44280800192040c41e06c3c0191440744a01c0007a200401000d820541c12140c68518500403003070358000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 609955836 1250 609954586 609954607
    0x204060f1814011205070e07260103050c130e010c0c1716060207140114150303280207080604150c081b0c070513020a0306050d0c142107090e030f 64
    0x11304a400e01c1c01441610b00765500c80f64030b8101c400317040324000041402c00174011422803111640001c1508401155841d650540d52a982c440488000161050b030908420502980240d070082545600d100d008020b481c0000002a0070151074600607a40248010b0400040d050b011044503001c82c0020440782800d0499510003000350400c00d01a20380602c0c0650000065109124440780e1030b0441200c14000c2c90071641d0210740380100e0f50b865000360810311045200c081d20282700e00b0400003d0b13a4900f03044800c3e040403460140c0700ea208081622400b8140014020f540c13420b004d00490760300d02488180400f200075600b200050303d0103403000030345c17008800003600e05030701502030004440250742d07035560b40d0400500040c0c08074100701a410350001d035117510703e82c05218203001400c042e6890f221900c0719407500000c03c04244a001c908178514a07405030250307200340c0c20403c41d0300100d60502c02400c251038450382d5007003e8021400c082e45865403d52911200000340c440356640022007514080f4021b4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 609957086 1250 609955836 609955859
    0x90411060703050c030c06040c1a0304060e1912090e07050a27060930060905071a0a0207051f11030f160c052d010c0204060f181401 58
    0x11402d4003000410b000c408039003d01840200840922580140a50b041c641400a101141307917004030b00c14522400b000900014200c16250f016400c494006100c0481ca41058240080e800401c14180e60301042c00081024241911b201050381d5510381c0703403094907508071804448003680c1e1440400c3d4180100c2d40014807030034105040b070b0b2644004400048100c4590b07e8504550341004010508841d414861200c0844e46030f4442031004600c4204900003541028900e00c94550141913642c642200c030f41403140400c500001040e0303018072520303001c581407034050164100d03114050041c0600240081c43d45071200b010700c81c080e48a440c0c2200c07040d035008142d90001d000085500c850100b403180c044c0f45911200907080c91541d460700c80100c42d110380713010f01900e4801e4005d94030602610540d040c03c1c0e1003001c01500c80c1400c0d403d00c0c4c00e503000c83d035006803641d0050040c000d5200f070401c6800b14108408982510031a94020003685521303059502d01400d645c1e580101403000200c0300700402241d0901e4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 609958336 1250 609957086 609957097
    0x6030114040e01060305010c09081c05070f03050918090f01050f0a0207260c070806160c060b0910090e03030c190c0501061508090c0307090225050c0f09041106 70
    0x142d00008003d550380da00c603401e5460321010340d400300f21441c00c100214101030106c407071400490800c3c0c04074000d0511002c0d141d0300a010018140402016203001098000c40c201c0c2d01d00b501c0107007601c0c01b960b00c0c1c004e040d441030700c1103881e501e6600032400e024010441c14080d1134001c0341400034034511982c0d83c3c600b01d0025000310900342d41b13125950191fa4204074450001c0e0001c0441d555080d0380d81c2006141c00e5141103010780c40307a8103681c40001004601909a002c800422801c4d1400c400012803d007802d101034066a200d65038007201c468284032040032216030742001c5030a000814015185c2a500594481c0800c848002e6002010080c4030105c0e03420200140c02e05209060884205200751280e5084a0003034200100c50389140c200202015000300740c80398821040402810000e00c80d00c04245c846000744992514942c0100e10717070481c400c101906001e208403400d1450000f0203182046903864801070703a0720780100c0f090006207025041005c0c44900c90b075000000300d41c01807c00018080681e000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 609959586 1250 609958336 609958361
    0x14030a02041112090a11090903120a0b0918160b040311120a0f0314030c0d050a0f0f05010906050d02031c050708180906030106061403090f070b13050603011404 70
    0x1c001d03e40e0185429142d00340900d0003c4014905d02c600c40c42c0880c00c290703a02112034480d007204401c11410700c0d40007086a45564004034030340130b144c5a80c0d503010040d24031503031490b0f0310107402810400401040008900c51840d10011201d0040030640800c6125a280c02130084c0000304100c284082114052400c0c09030201401107503056407420303501814050104e604990703c850320010f1a0900d540105a00300b4610002d02c0c4034074508203621072505030b20a08180402c2c1948950002e003c08209a0040b201c0c8507141109100c0480c1c0c01044000030030003402060070710f5150800200f024184070200f48041980075004000142c400300900501d664a210030f079040000030030850700000c2d8140040c100d0081c008005a090001c400300f0401d10460003070442c0e010343c0c50000304001041e400302102440d29540b82c151703a0b8940314214442c0c104240e91401c08068840c0480c00600555000010315032041c41d440c1000b6126200d008104203031200380708407804201c6124917034580c1e242940c00141c3c080304 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 609960836 1250 609959586 609959621
    0x307030c080c06011805070509090612010e07060230070219030206040f03120c050c0d14070806010510090503030a0e06130303020615040204030b16050706050a02031014030a0204 78
    0x3040502c145801c0f0241c100b94060070b015a200c2d1000b440a000f515008089070034010309022a09002c16010f81300240441d10032074203030b4075608818400390f210400d401c3d06e84040d1400e02d9159a0040d640309650902280c140481d4140c28002e240b40d01d441c0c1c020049040e0415150cd01c440c0c00300001288098002c0b0400d80c01070f54000010313a50781000f071001b07100f07001c69291400d180d4104038182d11000282d0794207202e03181100c135001401c04150310443c1704d8119030a01601601e8244031340402071004030082c4030322800c0404241d80e00c001403810b04844084407603101c0034449032001c541c0b200c400e10600d90181d0043c48035464240c01008038590a003030203820300b0300b00745444900c084010565171056000da00003105120041010b12240104500d0980c0d05514040c5123698258004200414040e40c01000e10401122184280300b1140e2040d045101070190f410089054030083d4001d55404400301d80c1c0100c001408403c8108411108400070040c114030a035540901c8042c001c46908020b0f50f44 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 609962086 1250 609960836 609960847
    0x803090c0f030616200d0e03030a120c05040902031806090d210f0903080f100e0c0903010e0a0606050108161d01050913050a270f0309050d320307030c08 67
    0x144c01da801c801080700e085c0f00400790718120b060040c05026004143c14002c0c3c0040210101c01900a454003108445001c80062800c1080c242105c841c06140c00880042d4000418055800b038204408201c400302c07202514442c0c0c072210b036550f07503408003400c4500101d9604a5200800d042c803c554403420040c1d0318022504400c400040c604a0302d073310008502061000c1c0500c22190488952150302100b00800c000c82c00d800d02c10307240304c04040184a10418100040d815071107480039001680082006c000b02e80c0c1a03125031910030050441c1d40203845c0086c0c1000e0008a40002c4000b0803d40007240c0d481d9900030b100360700c902e80000c10101c4e4015040c8172080048001c0c54490356000341c08904031400c001024203102400301c0588144d442d00c071040c0070391711004000c040491a02030b14001c0d408040162401078038030342075451550f254080c80e44003035009989000e107c00070000c0c21041484182c081b813120760700f00300c440d51050030000b5002d60783e1050040d080083c0c0a0030900075424003c120040c20403 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 609963336 1250 609962086 609962117
    0x1a0c01060b03041208010f050a050f060d0908040305010b09070509040b010e1f121406010804150504030e030d0201061a0f070c06180e0105030d0323040803090c0f030616 74
    0x50340181c50880c0da4131300400c80300e4100356002205c1400b5061250800d200146810000f41c2c80d64224001d6522030340c000340082c180c07640c648007204d50700c0344840424040c2d46800d080800981c0c00610048d1155402c09424203014a441c8a52501c00d000607291703541051006400d00c00240f84422140d414014680c0180c64940d80f2a003d540800e403c0760044200798500d100000c0400c207039194180140c5041c103803501c0c0c82c1c904400c60303113a01c25001e107003107840c540d03903800c00c1d42d40c201c0c0b48402e00c83c0311403404052005059005001d40e20601d0140c044030003042d10f1a404038200c422522582c2050020011185d003a000c880000f406600c1d10540c049090041a403a000030f0078040f9032001006c0b458802c00b2603c0a01326075002001484405000305581d0b00d010080380c1c840860703040c100c0c101641e070070040d5161030850694080302c40345599403250354034191816412540c01034400c604035208101101d85c2c289000c10502d20042c2014025041d00d803aaa5546940c201e072010001080c000036402081c3c80 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 609964586 1250 609963336 609963359
    0x60711030109200a050603061503310b0105060705100203090c03100603051618050a0f18140d0e0609010203070f05210f07020f040b130b0306060a1a0c0106 68
    0x281d09081e410421503e650303001c2000c0f2041c254412401132030b0130300800040d07503500485d10180204404a91b03560b0ba94035480e003284002500f5141d8180e60122800040344214401d030303080600e10503089244540d8a440c1004001d000c2e514000b0f00541c45403203661121140c94001d140c0110ba10780890b0008101c1c000024104200d1101d542181c964415040013031110401c0b8558190a04040090a2505101d105511a0b000046801245481d0b0010410291f0180d21240b0300000003281000000030510940500c1130f2650f03010344c1c1d2119032118685043c02c01050500f0056003580740c00c062410000c050000c0c40c1c0025481c0d41c1540800d21400c40031884c000c2c1c000c0d140c1840380300a0580928141c43c2940c4040a140c0308000043c0180180c82030320fa41c0e081245c6541da0129440100070b400880002c1c00380c860210f0a83c1c2240c000c0c00040c5580445400c000d550300070031400d4414030750f02c000900120081c14460613500b4a048511103000218030401845003401c03250004c84da0359211125401c4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 609965836 1250 609964586 609964613
    0x50c3103050a0203061e0f06150c031210050303070201030b04020403080f0c0f03070c0e09010603061a030118110d1109011212030b2805030d090e01080c060711030109 73
    0x2a5600407002d004114a81400410791251900f11404c50307203c40d450301940044401040e0311a6140440045226175803210b209640002800301607a90b00c0c1d250030442034a980045010761948848078010840009209a41702d055440140003581000d81e907400440282c80503a510b00c0e0020f40c200300120203d103101c0020303c01304028164250351000a422458a404002000c1d00b840da04140703c1100010b40c406101412219004180041d54440520711801001e0503800180703894a4200d030400300300180701c031a2420318003c0700200140148118078100ca468408401803901135030b40c4050800746440000340c0c0c6807500518a0400503198030020400051003a0030160f92811045101c004001490b11114002208c615060105040e807502150b40c114040c1400c0c03d00c8001d061310707009603a040344501c03401003000030211500442d20780070260611410780a60107070340042400205640e8400545038844001c0076020728500310043d1601d070101c0740404080c540c15520b85031207001050185400700d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 609967086 1250 609965836 609965843
    0x5100e0a0f240e0a2c09060601020c0109030c150215010602070e01050f0d081c110408010c08131b092a090806150a0b0c0d12050c3103 59
    0x50110340038180484000500c242690304101010303610500f103488a5044504440c81c500c1c00c0d005800020404141840344040c114140c2e1070301404110010700002280c0f806820280c081e61038401e6400c00440711121903000c040e01641020004000b1039840c0090348002000030302c140d464100010a2205420800b84e2180005a0005405200300045107914034010b0070111a0a0304c20300c80e174030114080b20009503010f888560040b40452200b201e2000c0030701c0841006a081040f40c99150020101e0780160180b20810b41c0703040c0c40e41d030503507014907001030203070049513609210300c000756461005058441d091610006259900017541d550107005607098000030400718403841002100c004604141d01e50307040d0400010100030004680003058a5420041481560040700d0702c0d14040741100103141d0186000c2000052844151480842c0754800391020ba900c03041d036a01078982d0481076034001c2c1e8000301c00d2102084403d002d101c1d110110b5000c0040100201d02c0c8801160300b01000c0310880d0f01c00ea = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 609968336 1250 609967086 609967109
    0x1e0c060d0b04050a0b0f0405071e0903050c010306031e0c0e0a05151c0b0604090b04030527060d1e06290708071b12030c03030c0905100e0a0f 62
    0x700320b80b8081c020303103921403a00901080540c0c82e150014403001d00b00403603640980d80c0c0da070215885c540704d2030000402c4164290490080c85c500f0200a000e02041d1005132614001e800c3d01e81120740c8240a142c04a13500001401880d0101c441003d02c203d401201c11601007034154000101425540032549c45000e0b07070140001c19151240c0116800c0c8071000e81d440c030540a140000d40ca40050102d01400c0079081614141c5035034400000c2001005c4800c005890000c4001c104001c043d0701c10000c084080c19074880c141040d4074181c81e0100e510007035100c41da221a0910001d881072031a0341c004030344510024102103054400500207c1142c100f90000d05a0301208840e4031104125101c803615540341148081d403412800f40c541c00740134007441400030000791400c180c0d40004880340400201a14900a04100c4850307103181c05400c654030800210042030420b28044000c5025500820449134041d003444414800d44008841904411222650000394004081048682c1d07442c0e0101901a00b10304 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 609969586 1250 609968336 609968351
    0x11091306090605061309050d0c03031d0c121f0c030f110a0f05030c030103060b2205150405040f0b101809030810030f060504031709010c201e0c060d 65
    0x184040d400c890700048145e00e081880050000c0c0c1c001600d00800501485d20100302c0c21513141c00c80c080c0c98095541c082140040a6060841c000440d0340d081c0c1d00b40c00c07124441000c804040c0d007504c60b170700c65010400d42c403245424043c260f00940c02080c87c1184074039001408000e400302c1c1d00708480c3c0c194800051260f022908582c065040f00d4003c7c0d8024641c00c20302e0a62428139510304003407105001c014003488d03d4502d10007180d160008a4081e07041c5900020804120b41c000b080020702c01210a086c00d011134048040080c2014412903000e19000707000303c04441b510703031074034102d140000c1c1801000c041c8800001800101c604038804c681c01c0301d50408582820981001400c004024042e50040901903804000050340b180d03105110560200d40451550f485080c2030b140302800d40c1c60401800200720803c140c4d44010750004001d50349984032400c0c0d0844c103c0f09e42a1412040442200e070780d2102e0341008000c40e500000b0024107000d6821540310249140c0030074426006803100c80c80c81601c0d50070 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 609970836 1250 609969586 609969589
    0x120302010c020c04020c071806030c0b030403021b180c0408070b1305090709120c05060a1701060f14070212011508060108030f030403270b0915071109130609060506 72
    0x11030280203e00301d600750b003403030a140c514640342c00b441d01c90103004844a0726000e80b20070032500303e000255000015110010380c0c4003000001640700f164110700600881d02500701c1744c0781c2c0711400300b4241c0d400ba01002c1010b220030905a644c401c080e042441405060000090703010081007100d025009c21940079842da0001200c2c4031030305520703402c0144a1440ca50400c00301b140c2c00729441e0b01304ca50000340140f450401d82012090403a158210300c9d0032100c0025402c0c1d040e40c100520744000d01c14400c02d801035aa8810044440c020085018400103400218002003035800c00c1c068012280001c00380511a04c0f140c80180c00c44489295294403007040d5501000400800d0000c00d005002800103949802d03070714410382d40944002000141408000c0c2c0400b1003082c802c5511000568031042c070502030544500c9440300a40160940a109002032000c0b6406103502100b0f84da02c00b68000e40c41c00380e1400382c030200079504000410f000c200e03010340900040403651500440d07241c0c500a002c0000d45040150 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 609972086 1250 609970836 609970843
    0xa0312020a061508031e090a030b010e16020309010f020708100501080706090b19200601150e0d0209060105210a05130c03060510090207080408250e10120302010c02 72
    0x354480001040e003e020040b03c0000302c1295104950b9041402c2d40c22191001a003c500840030215004078050344048100950619560b060390850120078185d030792418250707500c0070310703c4400d00010b800074003000c105540940030002c020226801902c002d0364843e84400c0c60444860b1700c140445455500401110390148050400380080d071030000726030307802c11184503054400c000c440341000e072040c0400702006220b6a501007014012803041d85c00c2c000440700003035882d00d00780141002c10030a02001030b1400d0096640b8031001e10041e040f104192165004c21111803402007455042c098208000b450519070300c80840d001e488480149145401e18545582c22210010018513aa104000c2d00b036010400c1b40c034a40b0212030b840305010a81d607644d529800d501021952181200230300106483c400c0041480251054400c12030071a004602e00b01070258481d00c0d40c902c0c40031075404c031000621003880340d580c01e0b9078003a1841458044030f5681c0c000c000c00c110807040050300140d41d114280d400311039061 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 609973336 1250 609972086 609972101
    0x3040309080f0303061908061f05011805040504081b070303020709020a0e041a040f060914060a140607150c080601052104050a050d0c030801120b070507020a0312020a06 74
    0x610080010416a250050f52480050001c5124840001d0004d8031140d103095014050714500c000c0d2155401c00d50050728645102c0c600c80c84c00e1085040700440c0551140044103c0f141660340b1900800d0300e84001d1100900010700161050f0604100507043d02c01c504440017007106006005180d21440c41c01c00034100865034201050319801000950500c540c4540c40300000709007120f0005007542c0701006e409450404508564016040c030940d02042d10b000d5016908489094005010f052030003500f003a040f4404495459000750044028072401d82d80406180f0a0300010707100c44d00e00a81611149400b00040003550729481e221039165100e240e05c003600035040842070a000d81840d00145070201150003964074203d00c0c02d0b00e0741c001002c3c00000c100e2054595080b0b0b0650b03047e40028140100080703204c1c1400d0340811b80e035074000141a08544400b040722900501d5581c5541c846880854069104d41820b0740e0101c06100c000c00841d20894400c01c040000d40c0041c4244020383c80c040c401d441c40c4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 609974586 1250 609973336 609973349
    0x5040806070f0503040204020c0f01061d1003120503091912030f0b010909110d2315091b1902031e160303050414011e0f18020919050c03040309 63
    0x40d26900540b0b075000419250000e60484000d61140d541c218614a050021076030200c407582000000100c0032403041e078500000181e0306c080b4405640d00c1d2ba014050782e229100c020601c941149150200782d100f0b00c080c1da04020f20505031a460424400300d441c0001e81d0301001d403600014000c0d0512025050300c106940c0e0900b10105010b05600d44e00081c00c15089449210406601d61404000070340160b01115010340008a041104041c0ca440c01e5241c06403111300d02840071140c8001c10346015494101240d2507000900d2811940c0c2c540c1138020701003c1241c0300720001c000030b01c1030101e07010030074030b1180c11001a94015515071244070315644904541500310480010204a0340d015220100400702c540c0341c05080202c2c950301c85140035211740e9480450f0226652070042c0c16030746244105604090030000c02c20520079442400a042c0484002e1502c1000c01030a10b0940b0303005040280e10698822056011030341914002041c4070140c402c1280d054454020010812007096040300e407281c09003c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 609975836 1250 609974586 609974597
    0x4030b09011b02190201140904020301090b0415180c031b0206070e180f07020a1502040f0e0603100b03010b03160305150f07051c090303020a120b0a0911190504080607 73
    0x911494045a03160b5401904008515059004603030500089990b5101c8c041c100715903035a92001030170004c1c008806041d100390308145104044440f482c5916003512202c42a0342c042c0c602101800d0f00600d42c1c0b018141c1810b444a404860031110365807060240329064001d011107140031100104400ba00110492141c0781d440340c5024415603459100390b120448690049690f103c00b002a468190707101c0c00140f40c01030307542145014150f45c2d00548111a04070991314229610b0b40408100d40c0c50482d42c1c0d0b50141d010380c11a40000500317400c81010030a002d80001a000d1412010234203180c0542050642080b5140c400c00402000f00106050700c0b950401808440c140640300c07088404001c1d01401c00c000012a4500004c4007016800000850728802007002d40c0c1c60f0304c0e001d070107500240d00e010040703081c07224185000d49090281000c46a40140b8820703806040051f1303500104100c80100d5200c8200740466132500c0ba0074084081c00507803a8860580300d030b2a02c143c8924002000b45000100007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 609977086 1250 609975836 609975853
    0x80c01060807150815120318030c0d0f0606030b150315070207120503090303040f050418050327060c0601051002070509040809121e012306040b0604030b09011b02 71
    0x40c2141d03500400000c514011341c503a1220001c00d2a09072000641c560704c08442c20521200c4d00e8000014040350503600c0500491100d00c0e000c16032a8000407040c150070170078441506000454107031390240758600c20301c0005a440e131651901405c80b98110b401003910501c84600308c00c03500c0d080100c00840b01042200c4091072410060080d100c07140341c400c1c1c3d10040490100b5604014060043c1c03007441e000513013101c0d102c0d917866110341c007000c04a109043c015464010072145002c443c500c40d451041e04140114602002007119803907011115090400d40340e040b0510800d960307506030040102d541c0d2030300107000a505040401240710810385514080d980400420070023030701c940ea0101d034407a42100442da19215140c010803030740311070302c2c070000b140340111124203a8134410b4001440300791003510020400d05440c0a08002c40608900264001000400010303001d80f4081d00310301100c1e503003c1d20785401c20f40ea0b55107818010b90140c03001c00356a51a6a040b02288550760440c1107001810b100601418 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 609978336 1250 609977086 609977099
    0x51e1b1c0204050408041e090b19060f050c0703060c030b06070f0201050d0f1b020c030313090c200109021305010b2212050a1b1a09011704080c01060807 67
    0x10a200d65000303000b25100d41c0014107010046080e0313401088418881c4500000564601408005a006403030505284c9a08140281040d032100007141c8204101c7c140344905020081e1003040f9126142002c2180402c03801070600703014880103004501c124008143c08001d40c8015007510003c0c840140144000c3c007003440401d009074020010706d41c082c20a40e40c1c3d03590041c05180900300321a0807420003400c150003840351900c80d01410182040f40c3d400c0d602503542203003c064a900c5200c20504540210b07000c00d01c5080305952142c3c0311030191303062500c85428620f81c03001100200c1800c1c81c906035900c001d010251708100c02002100c29000703504100940c1012900361709401601c01000310b0001b2070a4403920b0841201aa0019010040d0f0302d8000040600e070607a0740d107200c440210307816159003070111b100358140c0ca280c406440c5441190707085164a1030200740c86801c000d030301d030381007000864000d2000318030381c85402e001d50300070385101c3d540300101d611a50940d4901c2d0b01004899006041c00c0000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 609979586 1250 609978336 609978379
    0x9060901091208090c041811151b03090d03120e0d0c0b04020d080c0109170307090608040c0b030709081902010e0d02060f040b03060118030b04020904051e1b 69
    0x1030b500341e801d0000711501d4038010545441c51031a40941c00c54a4420242c0030883e46905185680b4428030741058407401e4a0280801c0e03624500c0ca03200914400c0c0142c80c4000740200c02e03d0309a214460490323040c10340a0b400580920145002134001c03548554004070a000903000f42c00a03940a20f004050f00810f1000c0100b0a04040d000901190443c1c400315045503215030104603030755007201030141c0b504004030076180288a58803049498001221620031801c14a9041d04e00c10310300b54559003101071800c0015241107000820403a1200c803006400308860007090080c60013041d103a6101010207041107402c500d810424615030055552a400c005c00503030b80701c2401000c080081c0c1c0c200300030803018408151180a4042c03604505280403038040380404502000d9840352034260707120703002044003079410758130344201d8000034004805100000300582401458660050711a0040b1b800841c01a9903504040d8201020364010343c001140c45444d0510041104800503c12500c0004e4000000760882ccea = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 609980836 1250 609979586 609979613
    0x70618081e0408060711015006090402130606030b090106020307051c03021b0120070b01050904030903061e053106111305090709260c03030c060906090109 68
    0x801002c806c800802e410290000c180400300c0880c244a10920a0f10101d00c02ca041000200c04150608603d01100d03103040340603591881a0320040903c0e01d90030107018000341c00a10503a0085d05aa0003040121000d100d51002803400707075000900032011000f00021460103a202c2002c541c414848800403400c04030b8860140305044107880c41d04030070110150f0190240d00d10b17219546803803000a251002042d00500a000030001c90181d01c404002e4412000740109030001e4408a5581c005001c0f90030104407940c1c001d80242411002c0950ba5500c40c400c2d6801c00000e10400c282c68203100c9825452030140030b411080f410f2076940c0b450131400f414202d070b02007580e4103441480110302101c144203181c1d010740c0e421280100c100f039881d0200342c1000308560b06031040c2401404204001100f65118a110200740d48840c0c1f80c0c110840454407103660304004da0740703a41155000e525101d0410341c5d400c000811400d25500060020b51811030700603030034424020002009230f4105283c02c40000c10300410307000d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 609982086 1250 609980836 609980851
    0x6020c010c0e03150403020c04060b03220f08070213020c0109170313230d022505090103020f03010605061804061406120c0d09031d01020a03090506070618081e040806 73
    0x2e400f1740c0caa04041345000707407240c144e0f6007040c9050780118203400141c00461040f5401049045905030305610103a4201a4510250102a1103216030b40083d180000810216000412065070120b406006800720782c06034800070090303951141e4520400415109991600c2103c0d40010304501d40781803409880782d148103000f440000e18003124041c0311000d50048039400c20610803640a0f02c0741040103941c41d5122004540d035020305c0070004180b0480343d240c0c14251100030345500c5041c0d18580c00cbc01809600e0f20b81d110b501d5521044046040e480b01c0300506000c500c100c5c00c00b071b40208441e06100883c0c0003a000710270103c04034850050287c803504100e0300100704040c0d00004960b101032840a0600506603808030007418906100c080c07584c0b0520310300e0184891115a000d40f0303120030043e691007d07240c00003404604402d804201501c1c108015203013050242c2c3c004204034510755206d0001614131030b01104c6455001c180c044091161240000d000c0a07001c042c140b5003400d022215503074840040090 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 609983336 1250 609982086 609982123
    0x1030518190203120a03090302070b0304050c040506210601091109090411031c020705090114100e0a210c081219140a0801081b010c060b0105120406020c010c0e03 71
    0x501152020848003010180c1c01c0d013519103a02c210a8000c024007038001d82540144590f020104110010a0031a801554440300034640b040c1100140400380c000180102d50007209564914004500850031aa030308005402038007543d0305021120381200e1211107001120f1005214038102900d4072800341d9042600441d01e42191406000080d00d0104213100145110304c9280c011800250000340c0081510b404030781c0030340e56070303220b5000800d0704001e520511f0340607110038007e0a055004005407208103002a1166881c5500e031021a0502600120074029202c0008050700900c6003071411039003e8181003010703000c041c0811034901250b01888100d03060203035101c0c4002a01900a0600101080607000c1c07054603503041c0c3c0c002a046910921514040d07000340e10309017903c0507052800c042d82c4001615001c83e04035080c2c81e8000148100b12803030381030000c10444881e040031003008040c0316904c00d035005680c81810f070591a0030348400540c00814031450221202d03107a40d000c90100c4280300481d0710b1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 609984586 1250 609983336 609983383
    0x1b1803110402071e020f0618090a110406021612020306180106050a0e0f0708010b1c0b060316270e04030c0602031017030f25051005010501030518 64
    0x800070f101c0d10b0802400414030080c442290400020128911802142da500500d03010b0001d00140744200019290a8200c00240d45030f13501d40242000d07006058620f00184902c0e140494480710f0b13006400c0701c00035074040d4042212a000c420301900c0030b00501141038920050303607408a9558030f0060701c0c0180d14100c054540b4480c450952041009000050040c1401c0350303500d48007a40c404003500d400e652444a0400503250300c4c0141211412190354150051a0080520041c00d41c101000504129151100c442ca1600d543d0701c4051400740c0c03a220503120150042c110050559400300c440c5c503d0748008003402814501050300c0010840c2c203840ca2100d0f00341d0300c030302c1d0448913030418101c003c22140c40030060040e03120125500d0b100391080c590301c0b00c41205294521640d41c5c01010355001c0c10b000304000d58904007008000a403040002421a00c25404013551000d0401c139945560380402c80c5c1e96001003056603403502519800c550080ea44c0d01000940000803070301d52070f95690400170300c076140e0030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 609985836 1250 609984586 609984589
    0x4060f0f180e010914100b072f090a05160302090303092d031f0e0703050703060203040317041106090d080c0714010f080703110705010504061b180311 66
    0x400c4000380507071055140541c0c9400c84101100e80a025a208103490001d074085001d800d0b900d03541c02001814208109a0315205658203c0c0e4094941101d2000500c5c1c1440d0700507184000d401d03c0301e0700d0800110040c440007024010203580007004662aa07003410180f01d1441c014071420851441d89107400f41c4d94404a1000c42e182d8803840c4d41640d0410f00d1003a515852509440408019841c1d0781000b030030101a036400c05940e19441c1c05061010101c04100190021070381c0d1010004403515401c0c1e900f2940c1d82d4031780600700030a9030300c1541c03074030703000800c1008241e030010f02c0170320649503c0f0050360141800e171541d07000709a0441303c1c18041c000000e2902411354812000d0703440720b64400b600c65500e0750f00b03507807031900c0301141d100d840141d00841d90070152542c0281c00c00400428142da41040c00c0d82c928108901624000c103412000041c10045d100c0803540a0141d40d2042d40512404600559008400340c91088411101000c05c072560450f1032030800108013400480e5044101c102c001e01c0b1100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 609987086 1250 609985836 609985847
    0x2508060f01050715060311011103160501060506030a0905060a05090a0201080a020c0f0a0209062b210e01020c010f020a031107050a031a0a0203190e1002030a06050306090304060f0f 79
    0x801403e204640b02075950f516200745c0001068034030a2003410750741200d00c0019103111030154a1060690001d102c060b100307411504c252000c0c035018030300201ea015941d00115415038410740c1c4c441c0c0b0064980c440b21050003006c01c4040d03086090b00504025500c0d120038915211606e000c0c00a0401140d031020a807000950380650b01004000b0b0180d803440345070b420b145a52851138050032030103058040c0014082e454100422148138691085400c81c81e0b48001c0f0543c090f200a170030884030164000c5250b40c03a42d8820036440c04c1c42c2980d85403166136000751400a881e20880c00501410010030a00b0a080c040e8040b40c100903043e4075003402000400d00480c414249000c6810194008040030400028000052445401c1c0f0070402e072529040e803903901203a0281d220848610400a03803802904040c80042d9000c8914400c044099541210103017030b40800340d174002e0702c4002015840b030506002c0340c035092101680006030607005602e01880d012014054601c08200031007484410103c241d040f90185 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 609988336 1250 609987086 609987097
    0xe07050a0b0a0c0b0108030a09090e1c2102090315010305031c1107080a09080105070c0b1e0117010b030a0507051903050102072d110907050906040e2508060f0105 71
    0x11130361019980c60380e0020341d880d0421504800000d1b00c01030001600e000783d129019004c070600740034024488600c6541d040d1003904078191400c01141e6840260032078035601036529500010031004d0781c0c42240900301494801020350b2202d1843e41d500040001620000846001042d40e030541000010300c9038a540041500c1c1240c915a6540001c0d050704105400740200340030501511403004041d2a00401402c0364022120680800c0801c6501000319100b81201940484058800c00070040484040718403901c0a03844001400302807001304500400070300030100c0800302500202500c01c0340e40c840580d80c0800748505802845040051049460341840352000703180c11800035940c0340300074504402806030242504a140f007503611007100f41440c0900800056810182008016040707804005c009007018245105100c4100000300d400e0702e905010b070004015001c4070543e10f1030f00c001840390300d410382e07661403491f80502c012040304c041e001921150881c0c401d8551111a0403001c0041e20b075803280 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 609989586 1250 609988336 609988343
    0xb040f050f0403030e07030507091a130905010b06070c0b03180a030e0f0a030b1918030305041101050c0d1d090103060b1003050106050d0f0906020a120e07050a0b0a0c 73
    0x511040150380007070705001c0703405544030303a13000c00c0291500c4d611203480720000d000051680d04150002c102c9071945400200c0189481c040104012190b00d000504500c1e01d001030800080d180c1504100b806000c2c45644040101034802903e80705640c3c1ea0040d40d604580951050b000c0003102140c4c1074051011744961048140040391511401c500b0003501c60740e14102c14600c80e0625090b1000141440846107007100e520120020710394641d0091000311160003916004581d90760444400e403c0c4403610712003203031406a10002004d08040c2080b482e1042a03d0304036050102c1082000c507a0741700080c403031b00454554a04a002500c6219159000704411502542d10002c210004028016164070404101c00b00300c3e04610b200f01315090680079502c0910600b00400c1e000c0c8050245050560000c10185803183c500144c4603c0aa86100890300a10038003800a054440303a20f00184c1c051082072415221580188559403030840003602c54010741c02101400f820208503518814010201182010350 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 609990836 1250 609989586 609989591
    0x1060801110316170c0304060e03130e01050f0a150201020409020409050f0a0b130c0e04110a080702030906070609140f010e0111030603210f04090b0f10080a0b040f 72
    0x441520070099a041034400010103004094400c01203070146144144410740480405032030b80d07413074400c000141c00044c01510349944400ca0291405400d10040000080c0002c00b186102d080c01503a1b0035200d0141c0060303025418200310309040e91f480c1008041182e00d1003840681440b801941280a8084c903840b13450315900114004c00c510007103802c618841d841c080600b43c090346d943d00068041d114030a103155084001d00025800c24650780c2c02c521180702850030010120349054010404031032a070040c04011004c04036031614402d6210396207940161080c8029400c00c51948002401071140320341c018401540d0300214810815001d00384a40034894200707944044110b40c20b514040d140c0030a6100c00345d40703800c2c1c1314459202218140d07030044001500a0804451280840c0c002401020300000c3d00f450901c004c110044150008101400d045032000c0341c0e8030140010f020112741c262a0251040c0082103c81d02200d03808650254009a00180810b5603001c2c1c1010400600460400c8400d02e070 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 609992086 1250 609990836 609990851
    0x80403060915060b3c0c01180507140a030804060e0d0807030905030c0109080705060d0e0609010b1c0b060108150a0801090b0906011d04030302090a030f030f050a021e01060801 77
    0x800d00001d0302d8104180745030307800d03140342e001c41d1404101805c52103010f45469804c4000004016400036142c890407401c00011351180e0010301c810003800b903d000320350950081303006020024483d46018500030040c1c5400d148a8215aa4001240960f0160004214410034800016515002e807881c4554100020795520015820300030854440c500520303000e440740401c0a01503500c02c1402004540c0104d001c1e10b006800c00e400c101580e40403c40b49030449840d010718007640380060160a0061698100010310702d00101c0505c140115042d807242d4805810102a201081c080d0044990010b000d1078400791998490605200c0810407982e000d4211030300f00c8000c51002d0307055024609060042241440503904d44443d541e0b40c0c0000d004085e00c8071041003400410382885c0c500c1d04e410030310908000d81005008c4002c00c41510b020703402030300c100e40302c42c00c09402c2c550880740004030104140307000703071412244001c065510030300511200300c10340c401a2a0050b07800c0a40c094406092a54001d20580 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 609993336 1250 609992086 609992099
    0x70c060c1b120e190b0f0706060b18030a0f061e05071d0a030c060813021512061f1b0503160201090602030309060703051302100f030c020a08040306091506 68
    0x203184803100300442d0509250780f4142c54510100e1503e2400c50741c3e10754030395007844003402c49900b120000d00c21041040c07100a00288080c0a82c6020b8004000c1c416112f4400e00d22204409103640080c0d0b019410480900e0701040d048026071550f5604400c000c90324468000704110140200d21414220618050611406a52100450034640707a41091000719040e081c1c200503900307820784002402d402c40c9100810010340070b41da602d54800c40c0303221242c80814841e00441c206440c9000e0b00f28980e140020300300d5a8903003031880e040e000102030b00c2e8400c6800071011030701481c080c400d0f0b52200340000001e500d818098061800d0710325560003010b5079141d8003005240408240003803800c074003142d002070000c18998400000c0e00e2041350701000400940c1c480c84000c1d4001c15000c1e100c03600501c1074110000150f21034000240c2c40350b00569608075080f01c40000107044071301ca042d1a00031504504000f4020415070b006460559030020000144d241991a040c00314003282c0500c804101c0c1004c000282d030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 609994586 1250 609993336 609993353
    0x40f141b01090611071512020705100c0e030c010e040b030106090b0a17430303120626010b030609060105090a0b06071704080a06021c05070c060c1b 65
    0x1100342a200c0381041901d50205031038491006580c1143d90307200741003c000300a2071076401030f0164001e00700060901c1c1803602c81c1090f03a105104c103a030b050740321109a8800d1003251080380d00b543e4030703403030070f000355031035030000640c0360154080b805042041c0b02c81c00d40100d40d501d60200c450308074000d000f0018195213210305409400c44413802071003141140d074000303000d901170b003a40c03601c100e4002c014020364141c0c001c1d403200205103140344840d18000441600e075004c2d0b090f00501005030011040070040703407852400800c003100c05810b04140754106201040071103504103890b140400c07100841003094080c200018010409100425890310a41c000d2080d16000860487e0583ea01906c05510300c2e07981540c141c0949408881c0950071110802110000c5444100c00319019071842e642c0d14034081d0b558090510740b0a607400f0640d6441c0e030010340c1d80340903000310403550b0382c000711194280004e18045c6030290510361124009000144c480c2d00215281d031050034155604240029140958141c90814620 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 609995836 1250 609994586 609994633
    0x60e060319030f0809071a270105070206091f0c120306051818070f08011407090b03100b04090e011a090106120f051e1608040f14 57
    0x640101455904668001020340d0360868060702c807000d100e403444004903200c00005001c007495004001d8003083c407c0d103a1700b80030302000b55601a2501d0b000c1002c0e54400800924484040036101240c412125907040740075500039a4040f01d009403034001d503401089542d0507182c00b042034010300c00481400b0326000007680402d00d002d000c2000d02c0c6140d40d50203070121441c03800f496611070110f50f21090300d0003450180950101910300c0c28130145c03800e010043d01c1d0032a107030080c407034001285005001103d400d12951409104c455040e1805040000f40a880e1030b465002d92a07002400200040140350000b682d0001011185081641e666440c1c4075400103054034180c07407080d5400e121141c0700e440030f04d1001010089004240307000a9281c11000c1c0c075100d40c1140008a4070380c9a07000608003114a12807107200e0b18240c50000c94a500720810425810f4006103802d804040300c0215401c2c240d40314442650099002403030400e524035500742040080004000410244500320324104c00d08081c2c0d28500 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 609997086 1250 609995836 609995839
    0xd02010905062809060b030d0f020c0102010218040504080408030315090105061305010e03100509070f060503010f060f05120a090501050903070b0402040b01031506051206040e031204080d060e06 85
    0x18800e0312246001c00343d645994036a6201d66a0320403007040e44a140c0d500c40d60a19114040015000c6504000302e8102840110a000465411408408159018003120078050000d100840c901580141900102c100100005009542c2c0e07400050070040d940b001c42e00942048411252686080480e045c40007d04000c05806000c4c00d100025a9040140a80d550200104030f044c0c0d90754145001110144030a441e8258140b00f8040d5161601e001403092500441e03001014008040c1411201105c80c80e05078400410003c0c1040104041d001549106080d07450500c0c02e582981c02404040721180209080742c0f2140c1030000c00e210440c1e0300e0b5400480c1c031900c100d00910541c0c0c0e640b03008544034007a084c0081c01c01c42013800003c0051801e5032000724140c0c014180002d071140380c2a240d281b0070003640c00c0352002c02d1001a84080c00c045803200c8035809041204c0601866000c500c1840c0c990184a42d942900903462001c181088850b10686144c04c0b5450030400116940e4280244800400c3d1500b5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 609998336 1250 609997086 609997093
    0x1a1807020a151509180605100f0902030604111207050c0304030c060807020f030f0d020f0d380a0302130e0303090703140c010c0f080702040207110910080706030c0903050d02010905 79
    0x300c0c013000b40241d60704000054171045c075541251711400042c100090104003040c481c0d650128600001d04540b00143c020700100586034500002800111107040c6915501d14009120b10409840b81d0f0388501d0b48000f052a050f038541704659219841d50142d604001e001514070407021035840d80c0800307420f00ca9591070742118410200064603a84a208030220b8041310030301000010240300881e00148804040000ea0300c1c9410310002c40d400441d211b035a501c44222046940303103402c110501540315031b082805a4503600018401c40040d0000081e032100a0064081921034030410107154000780032062042c003501d65a2a2000d110b5840d00d12500003141c0d00414405d11828900700050040750100b07041e121404500403540f80c3e030030b8044180c0c2c011188002c080000c2c40041e00c990000e055550b100714110b00420000000f0401900402007035881d03068280ca60402410f08001021401c4503010b00340007682c84001c01b000c40b10074400d0380020b082e622a4000c40a01903070305510100d449805001035 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 609999586 1250 609998336 609998339
    0x3020316200103050c0405040c0c050f0a150c08180a120908010e030903120f13061d010815010f0207123e190314101a1807020a1515 58
    0x10f40880e030040d40d4003c94114244020300c05800d01e9072120b04844d616052103c449146075455614040360082d082845800c00311440d001c126003106001d1800d18110001e02240800b010f0007020b010004060251054594200102500c010300014070300c01d42215508600c2e034240c54000d003000d070640c400c504240d840c01481c44d00c40720010042c0d45a11400501401c02c120300d0b40d110f0304e13040d00a40d03510044500100f0581d41c405a132000644000c0c007050300e42d5100c968210700d940405142101c2c65a0501c00340c04200300d9041c500d0542c11800b150242000740000000c0c0d68100d14103201034015803141c01132044c0d01414001008405c030030340705e40715955400e50200d80910f210304100c00c074406240071256810301081c500c4c10741c0743c1e6070071021200e000440040d9681c65510f9030000d00e00410704107811000e81c020700d02d0394038001c060224280007020380112b0f4640000c00c0c92080b404044000c08800d09003c10180d51003840401581e81d044490109006045031000b00100000c0e8555015070742d64990 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 610000836 1250 609999586 609999589
    0x20c160e0604021e0d06081e0d080115121107060b1f051b0325050c03011e0203150907050417150a02031504060f0602010b09041106070302031620 64
    0x201c1390743d030101445109024807900b242c0e100d9074120030741c2c0f00e000a4848501003804032040044007044080600102c9894401007151800c0500c107030003040070441b103078006010940c10805829103190040c1b5040c0b14880a10410718018100529081d0b400c9000003804014081c450300308025a11040310310303402c0712010b08034618000600710038010105800340454006804c01200d034101d030b4400b140c140c03440d10054060843d1540c0d00e18084a800007035910408050041c104090000844207600801c4010b03840315552131284000c842260015400100189401d89100b44500d486480909022154144200040c007075070014000c540d100220800340c403a8040001400030300d282050305d00c3c4501070b05e0320071109c23000c1d502c020040e807240034004480c10901c1c0c170742e485002c0080030450607424242c1d00b8000020300352a003988060344509911000e22000c03900440c80600b0843c4220340c0310b546c602842ca0140c4c107601440d00300200d03102054503280180300e00511005e4180c004522441404a000380 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 610002086 1250 610000836 610000841
    0x1021c06140306241008071832040513120e010e060d0e0601080d020f0307051e19051f09030f110a240501060504060c020112020c160e0604 61
    0x4402652561143d40410030500200d109000350301603202000030400500c00c08a0f14132922003d4160009a402c000c00800d194001a044135042d440100304106921b0001d41c00f10207050b41e24a4407003440c414090705101c0c0200480d40b004002c016206024500e4440640010061007880550711001c9a00b9050300a81c8102c081f00480481610740b8840c0741100d41c180000780c0c201103400a002c41c1c1ea1241e00400280c10032a0b14000c2115500601c1c0c1440c4c40700000741801119801e00300320794002c0c04070200060001c5019142240c58508012032400041e03c12440c0000c101404a5035040c0d030b5070000c040c0500400d1003441b407507840c2d5080104041f0800044111003c0c6403001e000506041c200010303c500c03801c0c030305011000100448500414039190800e10480f00d1140d0350000180c030600c036242003520700409005010070f05001c2d041c285000000b07403d10340c41c078400904000480c1104451400240e056801c0d80d003007001180d00000303209100b05440102d9004200b156a68100000d0540c074213030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 610003336 1250 610002086 610002119
    0x1c120f1401093204020a05030307120e0118091112010b0c12090d060f06170303091603170306010504090c05070308100f0b090303070f050616050403031b110301021c06 73
    0x114032038400742243e403030001e14000504200d900285210b0300045a5a081001e080040c0c05601c00c01c8176a102507c01821403203800c0c5030603044c0200c10740b204480c6c2000482c00000c6403445803011a19610000309100903208801041c1c1d2400600000400c0602c021000340541c0c00c024011070307110318038110210380d490082d100742c5030340022400d119100180040e00f008488151101010032101e440b414002000c0c6462802c800840c1d001204210303040204000080c45944410042d032501030442d150b0840c40084014442003240c00003000c80c2150f44248100d400810031018200240001040001d010364440581640012010710200e020f2211500e240011126804070101d00d05280410b0003060b500807460140e4540018003081011404c00c20810240d9442100a8242480d101c00d00740200e042144030b10080100034001440044d40144800c0340d840040305100d00300301c602d4540001072010810b500c03500765001007081110b1001d0204949500b01401030103000c06500c0710304608600c0000d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 610004586 1250 610003336 610003391
    0x80d11060a0614040c170a0b0901090b0306060d0f0b0a020403050d1404060c0f08030112150506030c0405130c030b01050a230d030504080303010e010e06031c120f140109 74
    0x10403103c0343d0703181550000844029901740059000302d031984030403994000711040d20f8a1a1505414070035031504400361405484030105c1042481d010b2001b096840c600200118041c4007240c84030028400d00f0f1070f00d80003007503200c840e520f01d610b428202c4001940143c801115144510f006a5590034060b1000e001061850b50b4001d060514000c0100c905258080c411303a25202d15104140102d1440002103000c1d0041c8a8003440074141440d100d403e444540b40c0413a1300e50300d03040c20300909a40124144032414400c44005c5000e031540e2100150002d25410010176446c00b1500c0001080384110308141261001c44030841420764850603550102c0184001e42c0ea105404c6410550714038002584602550003494602d08041e2101001440e640c4203801c002c8046130400010408000c60000e1650b100809070087c0410801c3c0074015a0f080c00d004801a06201e01075003486c055680c0c550119a5031160300c03009000f407151800d1058601e030001c0c003603a00300908012000c000c005421000e004007284 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 610005836 1250 610004586 610004609
    0x20a1701120224090310060501021c090b092e020601060c030c080f0405061b07090608060a09030509030d0e09010806010303081b040e0108010c0806150405011107080d11060a06 77
    0x2207560180003000400c0c44803202c020310000c60117840802c03848040401080d00011101d00300000645820300d14119400d1400c0d6920307042e000c007644100750000300d68411540e030b900c962050300000c211a180200b0015400a01c82140c58003450170496081d00f124140c09581a50740c0340d4a007100c00e0300c0801400f030702103200904800d0000724404010184082c101c00811705294407040024a1076105c0c1d03450448407018251100041c40c2c2c117204910041104000801059250022031500c1d030b58010522a07000b507854441100b030600030300c11a11140802001e4540e0418001c4020300520018680507000c0c001610006c50102d00c0003c605068a4142d110400969110888006c129520000300408401d041c0400a5031040c602c411f01e02809425001140368003c004005048480007803c21b882100b01180b43c0c001240c5000803541503440c00e2819081d91421a003420b0300c4c0450961000300f140c811800c5841c4081d130302c09141c0c411005514141c80e6184c960b40010b40646890f4000e100d0044c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 610007086 1250 610005836 610005859
    0x70303050406050f07020d08060f030303040b0907050a0f0501080403090506160606120f021c0f12030c020a0213150f090506031002040e0f0604090605070306050a0509010b040b0913020a17011202 85
    0xb0700881c1d113a49d02100050110040b42c80c580702090031500140e408840c0c0000c1c8405200b4110003e001050240a0945000310510b103444645c80c0072420078030400703060284060104060502c1200c03080060b00d4090200c650b1482c0242c2108881d00000b08161402864005c020480e00c0d12045161400c0340c0140d41c001c55200a07400b000710b560301520720011001d011166940020b0250542280d5540c040e08124030040c2071242d0180503100410004c40c110741060074001c0c0143d50328040308002c002540da00241d407024402608110f20642d812201c10803801040018203100c26420281c400c180c20350564419243c021814011b0f40128012064000e15090000710511500408240d02010003000810b02d86003e0311018221a42900d20100203600c4280501c404c1c01e141a091000300401c0c2c0301e4201540c03404410606038080ca010306035542c0b60024042e06c0310b07a1191200e260300303120100f04641c1ca0340034070000740030300c03a03012811060300240720000120809425100090389401422031901c02 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 610008336 1250 610007086 610007113
    0x6050909041b030515070e010509030706080a091703010311180c031b030a06030311030f0423180402040b12030a110708011404050f01020f0f0a1202070303050406050f0702 75
    0x2942051a0700303550301d50b800000301040341002848000d8503400b440c2411403e040000815400500f040389040c40010032a515043e100000d04200f10358042c076140c21103884411a08010384154070001d041c610000c200c2400e0400c0043c010b6040707074855404a41c03ea6002010300c100078030805101e403140300035000050b070f404c42100001c0d54811001140c030340c41c88131025124403a07900107a8040790010f5a5807020700416411042c200d081001d024000c0d400c01e01c50051807203646c032980c02000448041ca40582803003482281d10450002001080d844800003074141c3c0d036050030030840c0d050344200d0500e01c0d900d007541403000901003094032a4018501d40100920f094860785032480f031203a224450010006040c0b0802c3c03264041c50320101042d9002801c01e810300728074140440f42e4280069204018050091100324110342601d00420001d40e00c038001410203440b1031540b12075181c00e0500002c1c51104241c0e0661000c0d00c110306c140c404101c2c944540e00c41c0b8020800894101d03016074040135403020803 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 610009586 1250 610008336 610008353
    0xf190c05030d0f06030209010b03100b03152202070503030f2505130f081b04020909040f060905060c040302010f03140105010513050307170d020a030f080a20130605090904 75
    0x944403e5001082d00c640da5800708801a50176030004100350b00c00310038800c0b200c260120240060518800f0345080d400c02540c5222881000607183c3d03c1010a010401110030a17404204200c2001c1d160854031280ca50030020303120f5008035000005c072901140010484c15a8041c01c4222b211801001c40d125024100b040e81c09030302c0744200d8641040310000004510080700e01180180c60b40b0009070440141c1070081f0004080b20306031241c40707140107100c03040d95910b59a000c2a48990030202c20002c1c9407440c108400100000d0710080c0036401000708101140150f580203004880c800e99030102c50f0b8210202c120100c031001200c0e42c844020150042101d0b40c81070b0040c01120311074080b503441d169501c400183c50180c1c81c2d44003264207924142c10b0300a403070041c44022080e414500190000c2d6815560040841201c8000f001c00d2008507030104507904c1040c0d20000c2d400b264165045010101d400704241070707412500182c200c01c00d2000000c110035100300151107614001820300c080e1912240c0c0c40421 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 610010836 1250 610009586 610009601
    0x20712060515030f030c07140907050a1701031a010806040c05040c110313060e1e010804031b030816030c120e0309150d050a141801110f190c05030d 65
    0x11803400e0b06840700041d940038400155803050308030080d55a44500b94019040480e05d9000d102a0f40d003600c0c1042d0252100401c0307681c45100c0c1d01e0318661b00c2c00b000c6020b651041c40002e41e030316581c02d184000b1003003211000c1d00c01107840c404110030000d0313a642e0b1103890755a4000c650080c0b45801d02d2a0400083c185a0460340c6000114108000342c0210041c015103190800d0740c003084070691055040001d56000301c8100d082201c00c1d152480c00742c00d20710800c9080c4070050151410400c42000247c141403142c40146d52186240c2e04082040000b414001e201160989524221031040c0841e074032241d009124000c04811292250400c10001080c1c2d0401044045130310b01d01404108801c4c42c843e522048001140400b50100c2d86c0c9888200d06048100c990080010503240e00e0700804c4c80707003881d040240540c4a100884844200340c9400303d0940909400c1201c03011080e0040340c0a010302070044003a00707401ca03a56030088411612810225026151000c01038855001009540d412801580080d40c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 610012086 1250 610010836 610010851
    0x2e090302032b0612020303071509080307110d091409190e0709150317090f060d0914070f030b04110a0306060e06010f120207050a08030c190207120605 66
    0x24100150710400c424110400682c040c00c410000282600101d91072080202500e58410300303154000c45135011940d41d110300700029107810500001406241415080800159882414a078980c00d08500203486e801011a01c069540a040d400c000800d00c01c0c0850000c032880c072120398003068010001c2c0b02d070f60007000d041e04036100355544c410050390200e401003c1490b80a03200501c0b40034076118420701210a4171001e40c01c480c440c9042000403409520044441c005642c140964982042e030005003850312159483d6081840485e27002d80d00c03100d030345c00505c0700c40c003440740c14840081c01e80b0210b440700518041c2c02e0740d02501c0e481c01d001080003c150a98003a2045981c401241f4070300001904009840d48104c5403a62205414000d00360703a40780c5190446804e0a00c1044910580e402920962007160702980440e404101d040038014100900ba00140c2c000a140c1c0d035078100181e008607190b0000b0f4104270315034404402e0007901c61000079100e084500c2800c2c0742000481c184e8900014000103810308 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 610013336 1250 610012086 610012093
    0x606181505100c1b1707240e030f03092806030b032419020c07180f02030c12100305060609063706180905100b0f03092e090302 56
    0xe000030045841803408503e59680b04d440e0a1808000010522960010341c1e55508420000c10040090b444c200ca410007030840b10804908070040203e0380f4901c04114030754148a08070302c03030614440200c0104000c840030746910058420000c81d520300180024060440c1d4404c0700700800101d48241e000203203980008050703d0302d4040079101003030841904601365031803104020902000e85900314240c1c1c60320034401c1c0190300302840e80145580380c01d40752141103200b107440508a111018640e024000c00c031039900701152642000800050305811954141c004240300f41c010031220404134a8541c06c4036401001001300d0f1741c582e002d00c0440d44010f0000342d001171000013240588003090850394259280030b5641200c41c80c0c281002102c2c09510b52003403091121101285440e00e82e4480400d040e940f0100c0301141c10340703688001140480c0503500881003c44046040c403246082100250b02a0000c40b040f01d0300c10021189220031ba03030139890180504c0f540f0300c0032143d0b5030740583c110b105a1030103801038 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 610014586 1250 610013336 610013357
    0x9010804110406030c0e01050112061d0601051e090a210f061e0203072d03020715020f040e01081204051002150702010207060e0303041205030c04030c03060618150510 73
    0x1884560100c81e00082c04444400300188503a580c41900342100c3d840e43c00c000d20000d8033300000303d031041030340524000d00b0085080016149074041d104503020030840710740094901036102500d0301d55801c15020184207008110b00060402e420034408a0151590607140158100940e03c021300090039000403201d4640b20004c00240c0024062000d50491600c403015a692421300340c020112540c0010300041c000104a00f991071104d603c030004c1c2000220308005035600d06c1410005010354464a100303404a000140300940c01400e540580110f032404000194242d80f240701268886030f083c6c04100050b5000e100030015440e0446a4603070049aa00540340003118580c504288450300325210707000741c0c0d0001450300801949114a0f520341040201450460400b652031109400e41003100c80200140480881d40c104d070140304840040d82d000042c045150f50b6450160040d0200d4828604500b41c00c94200944d201036002e140302d1303070000344607080500b8280b000304110481d000d50324000700a0320000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 610015836 1250 610014586 610014593
    0x509041208222d03020c060d020405120a021302190e040f06092f09040c1e1205090c0d170708031003060c1103032a0714060c0901080411040603 63
    0x40e0080420b01600500301803a49071180610f0b0b00b0030100c462072040441a0070440825404076001c0009001220510764034110361141102a014035002240d200b00440c001e4001c80038000303003100101e442950040502000e00090b81c089000c2d070740d0365900031020181c040d488148140e513401108080240006441e0724038140007021601c640d005030200381d6541c2c00c014200c1070015241c10165008001e51402c00d010340c41540301501400380340a0045859524401502b40651a00901d980c1780582001c040119400014000350480d804505a0391400e000304040b0200070030320008488001e05810300042e42c540c0c5403182400b0a40007004034030800d00500340003441000085001e4800ca0034808841801c500f481000c9802810703c2400348440c1d00c0c43c0c480e020304040183d9600c06a1807108015003070390801e0584070400403050811015200040c8a41000f44c04424503101401101c201d80c419500c2d903600030341a1154241d9a80800c40c1940003a000800c18005035000740c40c0544082442035680d40c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 610017086 1250 610015836 610015891
    0x106080a06150305090106082d010e030d051510020d18080a03090503010605010806011b03020a0b0921030c0f030a060503030f03070225090c0e10090f0509041208 71
    0x10b440740c000f035160400d000010400340a490044c2044070042d004144480380300c0c1c10354000e401440e2503604801103003810300c588294442d83c0b401d2514000c0d03d6a038100348280400904003262080100020041c8040c0281400e404d15015040690007e0081c1c00e9014010350b06409080143c400642000b600800c4c515420300c0005825803294840b00d0f0820300381030405080d5a60b40d0400d130f0401c110303401080520703a03000c42c601402c10719481c58562406403e05040303050150300c0101800e030030b4081c018444c00b8000024802da040303010883d0351148080030042c2d6501c40c40240c65100ca44007091200c042c00b0300c2190300450700295007080010350310390356001083c25a00116190101d1681c048204200c242d01400201503400c2c01c202184142c0004506808039581c90780100504555560100143d0b00d000f81183c00e4203040050070306030000020300e0300600c5400d4500650b81020001d4000040508140d80d40c1d9001e41e80c030284200d000a002e51040b0352031b0300000c007400c42028115458014880008 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 610018336 1250 610017086 610017119
    0x30706020d0306080606010816050706050f010510020a0302121809070f0912021005180a090e0f0307023f0c090c07052a03150a1506080106080a06 64
    0x580107080700003440030300541207940326800300c64160071403401c109641e80d200c0105648000c411658080e105281c02c801c0710365001d84600203000170b10305410310070000584207005048510480c2c0030518485428000c907295001e500d801030140c2d1040a0b0707060424030080c06010150320380068044181a20400500101015039581021864615170340810f2588001042c0280c440e1100305c4260079425404200c1300302130445400200440800c40340d401d8503001601d003d4401000341401401d03038031a14190018000c0072500c213101e00c02d0122440018002009484e030407a0000c0c4102c01212807101c028040082007015100303050b10f0b8504d44220300c0d000301035020b04800d07590010038108071103000b40b1055140150141808032000d006450002d640003032480580400740c0b100101c824200c0e0814a01070710111201940340c010003040a06001c03100442a1040300d64000c00d1156820304809030030002d0305401220b001070051401804414094490035030003c2c10000c0010303205030f032002c4024110160 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 610019586 1250 610018336 610018349
    0x32206020c011b02101a0d030e09060a03020d0206090102070e09061605041512060807060c0c050103021903050402030a020603150f04060b12040f06060308120a0501060c060216020307 80
    0x105141e22038200911410142400382d6140b0000080c0c0c10750080d540d41c4000c011141c00380d89680c0340c240d0417680102d00d2402e0440c040c06a56601e842417a029080c2031100c6c203070a0141c002e0100040c441d00c0c10042d024100d030703001f9100c10042d090540a200c45130303010030045c0d81544582800002c1a480d402c007424490707003110002c2c211a086c0b0100c3c5e000d803030092105d418100130040c0001e108001250144c7c0d071b918040c506007550130b00d00c61b4400c84058003103a0b0003244a405241000160302ea01b2940d8405402d20402c1c0b690001601c40300158100d001d02402070901c1504451410103140c003c5d4480f50f08140000c0440d218460140e00003074407640300302d803483c082151100c4d524480f41489007118860f02c404403001d0044a0600e018030781180195180301e00c61078040c0c07000c2001d1090b00c640c10004039070031100a000d070545a0030004400d5010086e00c062000301100002c0380c1b41d00a01c0751398141d80300c90303803001000d80d030075207540c00a504110080c0c2c12400c0e0280344480181d9080220300000c020 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 610020836 1250 610019586 610019591
    0x21203070c0b03150a18020c0703080408070602060a020c0a03230d061706060609150906310b180f0a08010f0c080f06012102270105070b0c032206 64
    0x6091110452040c220b844c558000e081904040c4144500007082206940241d080144c4500f00710310924035040c070035030001e03040c5140094041001c0300f0124154007a240d042d02120003a4035a44141022072082c4040d15a15810015030040040d2080c0520360f40091958080d142001d89107489016642c0444a00c5000c1070707560400304550011107503845103100d8410b0103460f8a28001000c80c0d0b152040000451080c401c40300540c0041c1c20713000035954079046c082e0465440d00c408109005040312114520744142640600340d04041c90024110000d0b180940d41081c104000d4000f912100d001383c080c210381c0f00380c0e512501949601d80c64840401046002c001007488902074240344206c1e04103048240400001008105c03180100c3c0140581190742841d1056040000103499400314540d0810005113a00000b8160a55806003d80c55a102d00c0f03000003407031990001c03005555510840e240202600034510004032180c012070080c5900c0760000c3c1c140b0030111600e00199110600004049039421b6 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 610022086 1250 610020836 610020841
    0x6090204031103011e0c052808010e07050711060f070615050d050309060f0909131e120f0e04110d060b120a020f070c0303021510060c021203070c0b03 66
    0x200020142c582050240e000700602540c0410400489819048014025880d00040300465100c0c50031038020040075190000c05520f14850900100d9100d80040006100342001140c1aa14081100d01904043d1a400d2500d5400e9651899103090301c000541c0c031510505c101181003070352100030115a4401e1900094078001420000021000381c0c00040c09912041041e40004000200701c07000d13904100d824546032101280b080e00c44c0d100320f80b070300d40c0c1101d9071100f403100700580986548120ba120b000750340001c40c000c041048001040d1480030701a02d6513011007103840c1d4001e00443c0b608000c07a14045081001c02e60200b4286c40c200140b002c480c0708002202c0500f50030901c10304016104240b1071500d440311911100707400c03440240002030402e40c0054a25040302c83e01d000c4444455102040d040c056a60f0b003006500c8450184526010340a5400000d0000d100c4080e0182919580e448403080443e8507003d11a988001c0600101c040c0300c10002c1c07001240140022170018010002496501d1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 610023336 1250 610022086 610022093
    0x50a03030c030204080a150612120e030307030509010309260c010b0f06031f05090f15012a020105040306062616090b0607060c050a030b030c0d080c100609020403 71
    0x5842080e544401c01d0f1042c0000c1c41141d1000c40c801060036004203000300417106030141c020040c0450b40c000b41000c81801c03c01d008001000c408940341d002e2039100e40340c0c601e0f1380034103142d2244120240100080c07420014008a503000754426112203010742110401c0b4641e03250b0324000a03048810ba410900030120716009520001d008148143d40c1c10350302c10290480d4039022841da80006014925484691071000343c45098503c1c82030028a80240150180c2c201201d0000060109a035600796001c0340d8841903c440d40100f940700d4082c40780750800c0301c2002030748884a001ea08201012410090704020020102d81310b0701584e0090219030b051161720020601c091008506007201c0b501154102d80510010000c2c0d01c01c0e9201250120180415059040300000d4054801d0708002041546852a200c98075a805809001084c0480c2c5081041c03400200c10180d035418403500d05035001c003811140c08001068400035000f07410b640360450b100501003941d10400d640407904003403843e9034081401c0091 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 610024586 1250 610023336 610023341
    0xa020d03091401110d0806060705011401180212010306020d02090a090506030c0d0c0504020d060801020c062202030316110a080c0406060503010806130503160c051302162904050a0303 80
    0xc440b09003001c103440c0001c440583c0e00c80c000b090302c1700c00341322031000092100d8030303054126074000d07602100030002d0390380c3e0007100301106100707010b01982404044400503520116108071032480c2c0621400c42920380c42c55981030007035480011003500c407607020701030300d106070300d50307580c00710141c9175071000482c05251600c2814640505450000c3c420712544100d1804200c0422402c003e64030140c0e000350742c0b0120682408043d01e080e9105440340d41c80040e60140301440031a045006070aa102d100060028200c005401d01c0c1e804840a0340c142c00401c4240300700d03010a5050326100344100d111180c07803607450000520500280d881002c0c0c4d80c20800404072513182612031036000c0d1205003445410340d41007180c0c90b980c441c2c0040920001c10b00790051107040c0002001a00c01070100c440841090560a00d0304080c016402d219050061071420750341d0044588a00a60394922005824004840816160103580f003451440b070065240440070320094880240d21098825406070005007540707211403400504 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 610025836 1250 610024586 610024619
    0x3020301050c091027030516060302090a0e1b04030c080f19020d060e01020d020c010b030138100e011e0e1002030904090303091b050109170a020d0309 66
    0x1440380400c25a6001d95aa1307011003841c203000e14000d00d548101d5466501d82c0c490000d039a0b000849481800405c0000009142c0511905465010510b0395141000c0d0181e024054002e032388500b0040b420310400030708211003603205000608c612501e401100050000d54010b81007900c90010f108401e100c41e8500300300f10111606503a008208040001588a04c0b407500c2d03540003480b803220303000081c080c40a1178011401103020980215550f03190054400029445020300380c1c41d40d428030034000301601d418412460142001030007078509003c03281c251401c4180c210f100360403001e518a0710a0301516a6504d44d1001103142d240c1003110700c000f00014003562a0100010100300c3e032104803082c070740d502a11806990009440c4411803a088050a0b4118054035100c035801c00d2034844200e00340369054002c2c1402034080c0340444240c24030208852a8646a4090140807648040b4100311540403001c1501150001c00181d903200040759000404945485006400181800209000b588a580c2c100346 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 610027086 1250 610025836 610025851
    0x6120c060212030906011203110609010e070e010e0a0b1305040b01091b020c0415030b1e013011270106050703080c0706110f1c050403230f070c0302030105 68
    0x3400c528104c01c43d04c0c1d1700e00b0140164000c1103046032543c01018000c613003c2c04e144400005594080c680a15500d00030882001100064443d0000c0024510100e414103816a4450020380200355210300300c03040540180c4104a0700401c9844042904801c544940c50045216085020751941750450f5013090f5811240700e0640600c0640030106400c1d000150b0781d6501c8025100444c2d01080701071140c0d401c420907403000d8642c11038a000c2281d0700c00c03c588540007150b03102411820590300d80300c00c600404031070a031540e04001c103561101a00031040b80b2000392240f2920283d40060fa28001051218035a0301c6603400d8040c0b840d0a00c00720090194403940901500d107041810640140c4000b46103141c0030b0448130561b80c0004500d001e228181d000482e0301800e19007800c1c0e40d030080000c9150250300580381ea2a19800f1714035821842c407001d00400e40156010350b82d00d5154802d148044514a4400030301001281080142c031a001d0380b02009010561300034011040c7c1c29241d80141420755030300400d80c1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 610028336 1250 610027086 610027123
    0x309011202090d03180b0a020606030d0c201f0c060b0906010e040504020a03021203070620030106180e100302030f06101a0f120103050c0a080d0e01020106120c0602 72
    0x28102a01c0300110400f0341030b094541000b400001e648034982288240d004501d11500c0003031f11a91b4039400203181d9003d54002e50407a244403c0c40301c02152240361220700145240c8844d810007640080c0a02480310281004041913041c0e01031041c00c10030b05105040035030100d524210b400b07050019612a03606030a4050310210118540f120000701085501920540320350380e50310104081d0749030501d00b8000f45901610075000703101d200140380d0b0f480c0c10254080791280d0508514101007414504949025040ea00b0b0850440c2d0030b285003a6004158071429503020703144580001610300c040141c89014a11141d100c0c8081400c6005240c20603405450051440d0b1100701401010450105c19004582030752440038040120f540300704645115240005001910200d08400403032000300005040703910880844124007000700c02d0002c03a110612480f481a0060b54020440c58003820006020039014800001c1c86a111144038100c080c0e141403ea0710441000c205010701501000100107490003040317807 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 610029586 1250 610028336 610028347
    0xb070c050c010f0c0506040303050121170906130b0a03060617070c051524010206060f010f11060c07140a050a020f151b06070f021504050a0807050309011202 69
    0x11690740d9889034504070704111040b064a441d00b84504d48851406034048190744e558101400d0007000782c05c00303024000810884c0200d0140200d0a02050f4181a5001c8580c604020750300c140881150460040107030001c408003c4440d44c0c000052410000d000110402e54a034180204000d08803a819042242805003807c0111404a203800e0550382c0480316181003980310b540c81c94458245020308020805400102c0c2c18007a03159203c40002e61141220942140c05141c044012a40c0340010b035006904501440180fa11035445a020440004158288024202400700c2114600502102c0580186402050030010000c01551003042c10b045200100301c02c0040d501d419840350720001c00284941c1002c1500ca120f0b0300c0b41d54044184440021480e5118900403190400054561903c1206400f0301000214002d000381e4410358034840301d030300600c03a140707900341c151400b05000341c0180c42ca441200d0726000010724800051420f54841c1d40a5901c491440c0e0000d40086040c50f9440d1030240103004 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 610030836 1250 610029586 610029593
    0x9040f090525080c0603130512040519030209060922110901140901180b1216060305010f0902030903070206131517041b0519050a1d16120c08040b070c 66
    0x2d8003419030744102c44171070b566101c4a0801d44c0d07100c2d00c0203004245008119801800301c1300b88d405082140c90946030b4030b0080c084014142e1340c0c00101e0000a500840c0c00c0d0200d417850401c070141544c0001003403264101004040010140703441c0446080b07030b50a6032000c081c65103041140c02c20340101444100781000c075202d000050315140050041000043c901c1c0405444c0d11103a400007188220090039070f56260100c5887c0d2078452030500b00203281000b1140000a646100b4403030b440c102c45180d020751803403070304060074800654005040c502640c4800d010000c050381d0b50a00512000c001000e02d40e060501e01614098030051440083c014895102c0d100180c144e071145c1625072050b848a00b0002c1400e1207030100190440c250001600010000903259240c415010210141c800448003501078541d50b5501768980c07024065010207901071b41c4040303604d00a81c1d82c0009403418440c142a1050a40d440c00c0307508581c805942d000010303001a09000a12007500311158101800349032003104164581c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 610032086 1250 610030836 610030843
    0xb0406080c030613080d050f06041521050c04062c01081203090f0a050106090b0a0f0303140d05100e0c07050a0b060102030f0d0501140d03080402040209040f09052508 73
    0x20301c10100100c0c0c0c05406401c0001c2c45c0100d41c074403404100100824100f00004048040b000c4502d00d00991510200d40e00c04540f100c140304c116085502c1010310325031143c04c80107a9800000c01120280700d0400d505001e40c0c0e450141c0f9000c0c05407802107590f1030000f05102201c0f2641d80240201d0196050010f210031840446d030101d1102c404650141e69403905607046d0714140d500c0007001c1c2c180c060000000104941034115108440710003a050090b103045400b0400348290341d00c0783d0300c0e041e00d4201c1e04100003400781448034850b903070380801141018a180550300130750708203c0f5032481d0034a19034401d0013442d0401c0c01e400d0300080b041c52480d08190540d0344280d030750b0100d0704019000014000000303500e030b842081196010302e4500d10243c0c64650380c18101e0054802801417800440a00c0e9150005080400d0342040080e003540d151b03441500c680c0c080c0b200030340c00701c041c45401a8a0b040c4190541d1042e0242d40d465910400c010861070f942d1041140c00850301c96038034000c40701c40e658104042c50001 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 610033336 1250 610032086 610032091
    0x16090605030112030c0c0504050915013005010e0613030206072f070503010e0109050c010f020604080f0f0703020c010206010614041824031101031e0903090b0c010b0406080c0306 78
    0x42c144805403042d01d007030428508006e0f50105900070300348010401203540104030300c1c007460003941c40407200740d880764269401000c810001e44144c104041d151044001004003010000340144000641e6420003001282445021203551104912400301e400405a04000e00c46c3e01602a150050002c920070000d2114001442400c000360301c43e1000c003101c0000240b245200525008000f004030320540104140030340f03003540c03083d00d590156404880a5502828001045080d84d40c0a0079a6036219603c001164114807800340301d160050140302408010b080040c1a224065002802015040ba00091030100160000c0c000c1206220350481c088600da001d4130255003100d08c4803c40190744521a4005001c5245c0c104240d0305c000d18885200300c98001480280d070702804112510340d60758001541600c03242400c0003240da50340511040d20035035a92010f00454800d10f00380785140c0e5074a031006100e8210309034850303e80e507449004c0c5070a803610388034031801005800042d000d6402c0803c0020b0301d03901c00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 610034586 1250 610033336 610033343
    0x120a0f05060f1501030f0e2e0c0e06030a0b060a1e021c0e03010935130317070b01090c1d03070501180b0723010b030a1113020316090605030112 63
    0x3d030441a00410b001c0d4015254142c00d03502183e52130100c0340d0f001d400c030503420b402304001004403084c0c1c0c0c104c420b621b00400300220300584400240c5010715041c82071503131000b00101001e03545e4890300b041c00d40da08802840c491000e0750700c00c000c40f06111507081d90007a0403000321301950b0182021a18900e45070903c1c10032010310f8101565072000031404a40035000c1d850008007600400d2030440040c0001c0d01690000800e603200700b00d09550040810b801500c10807041c2d0f00c494090020030000241450781d01c10b40616142d035042c1c10094542c0d11622400001e805c032181854079a1814850f042e40310001c0511140e119049425074103202020903140d090b2801081e0400460622080003403140d50001c50042181251060340d0342c0e82c0c2d08008010240120403141c020303c683c43e001c200680140905116074000402409210340c0694030562140c0d86440102e401100c83c12015641400a00c06107108001e02d520047c18a80000c200408100090b0420004d0010900051010f610803185119803140d0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 610035836 1250 610034586 610034591
    0x305240703200a0203040504051e0c2503030f05090c0906030d05071407051c0b071e0c14070905150a0e0c03040c21060b03010c0507080306120a0f05060f150103 70
    0x200c3c028228154803481d00b1903a0010b0801040c0009003554034000b912144040d44030190300e884844401c3d10320f04c00c0f02a02d0312040c008010780d100070340404802c2400f241c401d041c00202c1741400032509060b40c02c12200c404240d000703e0800d100f9802c1101e40300394414003c8024143d5034410b044090081d01549102030800350300a5800f103141881005803074081d080007000b00078050301c00c40b400d14080140c10422121100700034041540f060092f0822102600440c11741200b2032710fa078504440507070507034009640d982c17a465407098600400340b01c03400c0600561400403c9a103400042c0400009607014030030700815141700c0411400480800a64001302e05403001341e600d0b01c660405043d0840d10342c000c0010080b0580d40610403852951009211074031070320060143c000da40080601300d03031740c1d0309172400030840400030740b400907403031200460b44000e0080c1170019a842d880440d40c03a00c80b115008131150b24405280c102400010080f00e94803540c140f10b010104d03c0c0c140701c054110080f40c02ca403030601d80c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 610037086 1250 610035836 610035847
    0xb0702041b170916031b0b030c040603020a02070e100608010b03040b060108040f0b07030e06090708190614040809010809030405030703151b0e1309020901060c0c030524070320 77
    0x1081400440050300003285184001074903400c20006d04280c880d020b222074075030110000b0302490541c043c0d0344566400c1e1324460400b860418250065842940c4c44411030003003880204081080111440c020800c400040481c2407d008c1c0241c1301e0001a00b0518034540e0600801c00000c00414840390306c03000a00e001040d58540d4603200101c0302e43c500d002450b07135141c04100010f10794503034400440940c035071040340e20a846171040c840d16441c00c1e000c3e0f40441d07004803091030210302c1c8dc1c103408100c5a20860000411190100c0c416040c00d174140d4048400090015803a002076a01c5401c647e081b10414020714a441e01c2c15002940d00d031040d2100034106210143c0d5000c49106079408240c0b804034600050840c0c02480c00d00130b0003010361b01d1540d82305602e1a4a0007032180400d104a40000d90301070030b03000d40c0b40d081440541c2c000c20200c1080720407441001c40031001881c00d02c900b1340112940415559240104d04202c50354080050040e020180740800a4140e400b5600e04010380d0100d010034a039846 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 610038336 1250 610037086 610037101
    0x703080d0b060c0a1208070e0d06021b0718050106080108031206010507020618010801080a0803060f04060f090c03110c0a12120612020a0f0e0a0c0504050a0b0702041b17 74
    0x14001c004a554141c080c0140c44402d00401e5800702130610003d541c0c0041c190341f11081594401c4c8450a4180c11041c1012800000350195008155080000c241c000c40e41641c84282480c1030465080b07441c00304d41501144085901c1800303084d01400540c2040296076050400c069074078020a4220348158000d14049a02d9900900848039020b0700600001e035940310031240360344480404410180000c4220300002240240491038001c05540a003200c0d01d0341d04c3c0d4108200f11042d20708452940241d48410019000010010b0761006290309600490401c1c89079001408552400e0720340541072000b0000d1818403100403e1348a003195105415071030124140780111102d201c1402402c03440d916010f40840c144290243c544100d80c03085610000003504c42400c075000c1c0405200b42d0803103444c001d020400406241d040b5409983c0c3c94034266080a6540001034071440440e484105010b0780001d40005504003030041d0450034090165400000c6840a001003041d41002000a1044041d070040f820b030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 610039586 1250 610038336 610038349
    0x8071e0204020409091a090a1b090501082104060e0d030e0603100e06060a08040212032101170d05090409050f010c02030324090a05041a0106200703080d0b 68
    0x609801400441d1650b46900c0e2450040039503980a035010540b80c0c042108213103103000a0b1740700f420001c01510b01030701c080d0740701541e5100340c0e80307140d09088a51001040c05125446114005c0080500600307000c0028805e821802e5400380d02110410340800c410f00c0107a400103c0c803603d969080d1009508041c807800c085503043c1c01500110390219001090041075106800b04000341c40c409410100356445a504210141c0700304010600859a864001009440c2c40500804010100d41c1500c1c981100e1070ba02c030001d003560100050381034034160014040000008418848c00d40c07142d000301001d20004401074903500419070428812929280c0950400c101400b5032103020314804028083d042100070003a40780c0c1c10856114040801000800c0c1e46208000704507110400d010f4410101610340890390800f900f401003055483e00c4940b080620f1100002c81030702d009046035a9007070078010300700760f82024010b800c10703610800368080c540504c04078981104651016544d4040012541415004640e5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 610040836 1250 610039586 610039643
    0x118030b360601080c060c0a0803180601080a03080901090302071505131211100f08040606051806040509070e01120606080d17010f150e0a050a090906060e040807 71
    0x201402000e40c00040c8a200080c040e05a884d19000d80e26201c80d4903051106902401c01e07124003d90000ba4403501181540e4029a04441c0b120991041c8002409001d881d0070805e0b480383e24540c0c0064048814540e00841864101410030300030705c07035000c05442c02941c80703680d80910084101e9812600e41003d0241040311256281201c00d00c1300542d07124450720a03e00130355810b68000720407400705101454803c1c443c4526400300e41310248031140e440c40440d49a200240103d910760394800012685a448910a4a15100e044003e00c050702d050b800380010355a000c0d222000903070100c0c3d414030200041d0042141911183c03907014489a1442c10042d001d0201ea0f840b809643c065000c204101c164440300588000c03e5108840c0e14590365000c0419a0701c24902c580100200c0003040d81111a11503e401c491311700f0024120118580c0780c00c0000d11480190344030000e00c0e5030f038201100401010340601c500808044916501c00d20b090303240c0603d644200200107100c58408000c441c5407401015250b039 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 610042086 1250 610040836 610040911
    0xf04020f1906031e090c0312091a18040615230406020601140907051c0605030d02030a0206130c03030f0219111e010e0d0222020304020118030b 63
    0x4440564031480600203204808800203450040c0405013100500c900034200100e03803022041d1980c5155485040e18180c110600701e082195914001400c01d460700b48101401403401440344d91005510121035034201d13000819400b403820454104140c41e6210a080615810381c00c00c2c0c00c2c002e024002610070503481207192081c4034008140441e94a9000400c503068441d10013a401c0c08280c0c82e020002803800881c0c0e4903001030b80800c48a0303800080c41c420644034a0000d000400c40351340b00c50000c0e080040310000100140d1000c1741c803070b0203164100001038104000b003081180340e0240da2540216400075000c09410701505011401e45a48208440c00105298446c080d80340c14280c0381850010440c0e10003a072294140ca1500b40f01165008007a0303410b010142c440c4020903d490707040c44420011102c0c00d03079020300100580003c41c0c0889800b440c48810708000140d4903d424800074000c031a07104090740b82d80e09003800500c001a10299400d401c420300e14400300000062007844101a0003d0340750a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 610043336 1250 610042086 610042129
    0x90c141906121e0b09090f030a0c020609030a151103100506030c1209030d0608031602011b0b0a091703071d0409050a030807111207020d08041a09180f04020f 69
    0x76203c005903512500351841c00325200c444686840681d1503890380110721034030841d00f04028030f019050040c901c440801d4806030805090070708400c0001d080c2302c610b610a032481007244c0840c40300c0c10310910a091043c1140c501450450070000384000e08401035000301c5005201c0000841ca10341d80701410344044801d40c4002156038075280c11000d442c1c1d04094668481c49041c0500031504270400f2007a80e1b0300c10344103c0d0401e2580c0068004440c61072400f40d901c0c00c40c040000b074050114075540342e85840785550f040f01140450f082e10308060740100e031061190602d0818000c2c8000240d110041c002030350898000352100d0130380c220000b030050075002e40040062203040031130720805800941d0203205030700586a189540c070f011000280c4070300b000081101a0b103c1080100010719000c44c01c0c007283c41c011090b0604243d21100390545c07030b00e401480c0c50307184200400c0c203e01a01c2c082190348481c0c03040c0b80114002e0f080c0550f007488081c801803c000d114202c0b166980300603803a0f9460483c4882030080030f0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 610044586 1250 610043336 610043381
    0x30a03020a051203010302090712150b070c0608012105030436050105030d031d0304061805040b010806090a1b09051206040b0106110102090301090c14190612 69
    0x65550000d007002201c60b4012010388000072600a0152070407a42c02800c80005652912012500008844e065599865031440304c03222405d02811004058010181502d680e4019402c100c1100314041e4400c1c0c0403c16524014002d09036200100c01d01c2d8040b8402a200f40030092034164251300881d04240000600c1001800c09107448a0b038800c00c40804000c5180150110703009481540c009020320b0303070194400c590090403980720f0b0340540d00c0da0000344100c00c120f450b000c01060856002d58014400100f280501c0d007510820625494001d001c02c80c2e00300a290200c0b03001070034440700100041d00c9102a080051a428480e400502913002c00104058cc01d0000c0031700a851100c280c0031300e0f4002c034420221200860f030005903031030180350000c0d5002c005038a0108111b0304050202e28840d55550207114403216600c090043d4244140326208402e201410414051140481c44044a2051303c50411170103646e010340304000b09840d00f138549082c00c00c030031803503110140042401428518180180 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 610045836 1250 610044586 610044593
    0xc0504120f021806091b0406050c0106050a081507020c01080703020a030e060c040f090b03030f13030506190c050a140d0603020a08030901020706020a0305180a0308030403030e0c040e0a020904080702030a 89
    0x1090f0307110341c60403142d0400c80d4680301c40d00100d03c1039141503604500c40c100000e210083c069006800d42c20640c0c00007040281d124400304004030010f0740120b6460348480c184204802c00040059480710380d03407004040c801460b100091820402800a42c141540095003140c41c902c0b9400155464103003a00300e464a00f001d0b5014800d95000c0d2190385014001c4110200b4560668090b88091050080c020342c202401940b034801d0b036900006010114030404000000060002e00440e4810070303060a80c1049240500350050680303020844980400000700300f4910700b540c00400000640444220883d2101040d0126200408480c2c0020758030800c0c203074000520420000003011800720030303030a6036142a51080260703925120518020301041040c444070190581341b42c0c894842004c02005103603c2950703901c0e50302a651060324242e0001c4c0d1100c143e00ca2802c0104a2002c07030075819101040840e03800c1100c00d807a01d2410743c009100315040e5000c281480300c07032016030f0026600202503c075926030914 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 610047086 1250 610045836 610045879
    0x14505060709090b030d230412120207140907030c02010f0f0603050d0516080a1211090117010f090b040e030c06010905010506071e050f07090605010905040c0504120f02 74
    0x1c41c1e03410f40740c2405040306883c100440c00c00101241038035102004011029008420302c456006c0d10765003082030100040d00d501d010128249640140c0110300e280c03400c0c200c02401c040c641c0d0030158040611805944050f103c9039100f60703110449207070001c0d0303100c00e6610413070141c007041ca60340007038038103018142c881840303130380d010310103e91003281144c540d50641481511a40524413590081c6216464580045400303800102504251803501c51008200000d800007240d8000c0f800e078624900105020105582000300042e40406080010115614040a0503001500ca004042010380c881800744002d440b00c0c0c000f8241291490140d9444004440000340e132602d0901c07075841c3e41e60600c00006502d0030883d0880b61015040304c089081080d4a190310a04030900e58070807502d0f8442c1940c0040d03480002c2c004030019090b40c2c500815500e1034a40014644034084e0012885285007007090100c013500300c0c04680883d808040c141107150000d003840c07285010084400394000c0980e076404001990500e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 610048336 1250 610047086 610047089
    0x20306070e04140601020c0d11061606200313062a020d03050402150c1f020306010f0311041401050f03010e0a0c05070f0b0a0e010f0e014505060709 65
    0x42d101004030007405031001020b8002512102d01517000741103000006c1c2001c038409803001d400381010003000300b0700d47d002c074449074070414252285440040d13610080003070758080c096030031501b1003000c048180c0054070809940306c0942085540030580405404008058000c601084005108441200d0b4411078106000d40220005401401030100c0003940354000e226103401103801500104030307540780e020500c081d60f00c41d0520315a248200d00d00300c480c4012004e8007607041c5032602c03005a02d03410071000141c5094010b0707810b51305141c00c0044c0e0581c0019480252001c40b61400c0d600c00c0c1d04008a030041c0ca2612500302e41c0300244400000100e404c145d14040c0500801c03415504000804101d501155540101040140000100f0201d034001c03600d1841c800d5080102c904000035104501c2c1c3d9a182111819070549000b240c07118802c1d020b100080c440c202e01d02880301402c10071a0341c0590781c41c20554001c0b041d180701c02515000040d03102d80d086040c0120560010490b007030b900b00ba14000d0400b41c0c15 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 610049586 1250 610048336 610048339
    0x3030a050105030a110103050403050c010c020c030f2107022202121303021507050408010c02010929240d140606150f030c120c0a1101050103080909060409020306070e 73
    0x40c80000a80c904000a0101903ea00f1076518018403050354011405440c01420603001c1000510800c41c40100a2042840380610b81c0c0042c0008480034040c1400c242e250101d0030303000d403c814400c45a1548062250301c9844208070340c15920300ca58400550542140400382c40c2d403141c94840000d010605900500088614246603400799440c0480e00e403142c2100c05000f030058210340008543e5030700000107690405074504000341400d40726100a401c584025207948010703911403148005002403104602c0881091210b02c1c00004603550040d0b035191806405603406100d111003801900c6248503224400181c02860180b900c602800c3c90800040d117003030692024001c1d0400b140c903500d040c554a000c0300446d00001414900d2a9490350902d420060074014a0b41082100038260f030418010700d071150384803034840b40d2a4200c100c0000c0459031800002c0029a150030010f0010a40003002e580400c081200c0d02c041c20b55861003c100940100c4500a415204050600401503001000c02c002000c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 610050836 1250 610049586 610049591
    0x40b01030c0803090d0f020d05030a180f0605190530070810051002030c01021207020d050a0c06020702012303071713030f020f060112140606090a0e07051203030a 71
    0x100e4602050f2648160502d003036000c00e210b19507070002509000221500c0c0d000400500307481a0544526082d540000070000c00141601c1c00902030400400e01d0304040c0602400301503201c0d040c6140602103100c5c10070301100b002590038022200074414800c45072070021a0007082c1c2203c0354500340b03a1003141c00d01c200796070002c200000a5843c0b841101580d205000c01216821010b01d400b045c0038801a180a80c141180800c01c03203034140b40360900090002c0710400c500c403d154503000c08024248184002c060041000401c00340241ca503001c03544140d4190001c00040c6d03200a0f61005035502040c818000030085112800c00003030344103060186228041c0350311141090142842c803008140011500a030741007850407480c401081c42180f503420300c81d85600407a103040e4410001c0c2c0d85401800d90241ca00d50100d40d0003582003052070282e030b8007204008002042c5070304000c1c000030b8170040000c100880195480029044190702081510010076001d0401c0321103003003901c8890b131680d0040301d80383c040301d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 610052086 1250 610050836 610050839
    0x1c090905060f0906042003041a04030c081312050703380c0c06090c030705060304030f030c18121707210c020a06050a03050702030f09040b03010212040b01030c 70
    0x60054a00c5801e0061900721440045402c00240000180a698000e541d40380e690a9807402c01c901c25420303c904224442d100d14051070b20031081a884064103401c2c0d0303418000c1c08004ac0c2c001c0284448030b9407214016448901000c110b80310400039034442d00b800d20711000410203100003c28400292401074009100c0007100d0034440c0b9207104680c000300c0b5100c40c0c6c20500d1903401052054103410141009041746048007020040d07103400b0041e1000ca07100d4000140100951074200901002000140c442d5030461810342c80180c42e00c1700075240c070780c24103403680c50244c0010302c1101140748405600f00ea5101042d03d50300888652442500c089038000003284200c1c1015400100743c40d2119070040c540c0c2003062030040341542200c8946010320900c090303070210200583c2e865035404090100359480e140c032901c480030000c4c1952400360220b41503400811151450500401c101c078069402940c02203400c00341140841d009100343d07031600c05c11103918070a21040202c0030415038100c1f40902601444039 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 610053336 1250 610052086 610052099
    0x106050a080115050a270f060207050d20131d060a061a130b070303020703080a0e0d2102030a09031d030a030818060408190e0906120f1c09 61
    0x211a4040303c1d6012a50a20580b0000e03441380c180c6100b5030401410b00d04000301540d00c00712210095411045405010720014050307194100050001030000312404940016691075000040c000002d01c0c840a2203050611803940d00e4080c04801e0380e000d071030fa0422100a550130101e0011007018424005c038005c9401140c00c1c11064022041590588065081e9109207140000e0441e4440e10028040c001d1030310000071400b403400045d0045034040d450142e038824032841c004141b0b84d80280152041e91801020130300030513001a041505118a06005000e0044003000e1500328803114614104c42c0e00002c10021407609a800441c0c642c4c2c403d4466041140c144000001405070050609030103620007110240420301c43c0c407000323802c813542c0c60b0b41200350341071000440e040c04011902610481c43c00580702e00740610320300c5168000d00c4940340614039940c1c0d61002600044c00644291300ca50344480780b5001800c01440000301592040003141d1503415420402c49003003180003001004100030707440c002804c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 610054586 1250 610053336 610053359
    0x2010222031218090908030714031e090a0c0312020708070602060f06010c0b10140609091605040e040b100e0702030d090303020904060603021209030c1f140106050a0801 74
    0x81d241d20141401400381c070742404031001e1002c44000401c44500060024a92400340705103042c050081d06640da03646013440740a0308108140038030011001003002040344822003180810011280801982115119503000c240b03032003d03105c40503202e0841d804000040151031121288101e1064082d43c03815035072b41c039a6a846070640e101748005a007059000031b800d094001c04c401c0e4000814180f60528103400e031140810400c084610002e00d4950103410303c10090b0410725803410315422154580303054003440108a4a000c00341200e540c10000030078050109024009507005025081148a198505404e04d0594200160341d120000d41d1150804540680c851880368030400390394000718034107032610001c02c00802c480e21040d002c156003405042c3c025035441c0546030050009950260302c4502e060b100c040640300241c4402115402009003242443c8042869011040200045680f10142a070010040c100b050b503881021040c44001090481c0c0120181c076924246540c0c0211680c1c070f800c0303038004 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 610055836 1250 610054586 610054589
    0x13090b12031204050319050903010f061a0313020301180b070207050d080d0e030301092a090509040804030204050103080c15040b0610031415130b0604260d02010222 72
    0x841e0000c00c62000b030b5108008480d0341152092040f01d2801268810919280e2000c100004c0014400544018149424010704e00852165a0204441d6141810b142c504509516100b1054071002c030010315440e80ea42806512030b50080c0080c810141c5d0f80349900781480301c400f812685c04200300c021811030b034070001c0c01d1810b855015103150b1030041d003070300d91843d2901310a1980d4542900d81500f00b100c0c2005101850080000d007201107010310600d5000d51000041e95104843d0380301650540443c940c2c0314000e10125501900c100786a81c40301d050100d450b10031a00301a400030f0404000104000c440f1009100d00005041620040342014030258aa508240c80107170200700c100002c1384c182d144c15a07050a21080c0d030305002441d144511a8800d80c506d0031a5402c02480701244c5028050030301010a41944004da0302c1000003444840c0020f18501480c040c81265001c00140702d20b1040d060059000e00c80480340850b0309400000300004d011354084c101644080448002610a65600344801ca0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 610057086 1250 610055836 610055869
    0x10b030a0b060a120203150901181b120c0509040503071a060f060324060706091115120109091a150a0504020703080406180c0305010510060e10030903031113090b 71
    0x110480140c80b110443c40003030442301c4903541e00c45802501c1c060b41c0074000f64483c401c110303400b40c2c062910030060054960750700200b07525100c4c032032100000d008149c804060b0b8804079490280c0d900c0741c0c206146940202a8010180020140a004610f00c1c0e8000350384107240031221141540b41010034001e0f207000a031010303030444286620102030880a9108103181c040060328981c14074849403154010350301c2c000700070359510340c103c04240310605040d002c580a0041c280c0c5074500e08011010503803441c2105102c6d114440e0390f10034428080040d85140c8541a00880100c070759942020000569400401c100e110700c120004440008e1a0400d4000d5920310703a050340f5000ca1030750301c44d190314020b0500304201894500e01d81280000044d800303a007040103180034800010f040c0c50040d0400c0d5281d0345e140c005a0500c0407904020b00d541d50341a4a891500311070b840d000c94070041a103000d40c042c082001408209000108010540741d201250301070850b0002d440502018100001348400101c2080610 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 610058336 1250 610057086 610057093
    0x310090905100f1b050c0609071508040305070b070e0102010c140403110604080a1505010927050c030303010618050612010b0a1202030f041b081b03010b030a0b060a120203 75
    0x40842e07003110780c4418000f001e08040400c016903202d05121049040c00c0301ea00110304041890a8801010401c503a48020144002c1607090700700a468090f41c150700c13038000104450100000c2c109846001030350380d80c951103601d5001ca410407004c083c000d8003007448040e0041d0300c0d010b1015440c40c840e0341070501d000c0c002c0384d0403440c050071902c840004100390021103401990401c40010713030380000c11603e41c01e10700982c1d816400040c01e040100540f0010390003416040c0c100301c20070800a800141070705c0680030a0182d0b2181545526040c0d09042c0030704a15589808084000103005400441e880b95015420708402140740d150810044603003d18100f8850756254136005001c0c0540c1c0030010f00f143c0c0340c2828851666a03140d070044050340c1c41283c00e540c08103158028030007000420081c0e9030412005c0814038820b075003030400700d0395a1300c0c84207061210b034407141680000e2034400303501c80700f100340001e401d80328000b04905001f2901c420079500b56008030550751001440000c48400d02d0032080e40180035 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 610059586 1250 610058336 610058353
    0xd031104120204020c060403210903050d0e0f061501020d1803020d0c0e0726060d0809040915020703020c01050c100c0e21061e060405040c0f0305030310090905 70
    0x1a00342601d010760403604154200b00004607250f00300440c0c0d1090b84a940e809201301440e600c645603030404140110f00250a15501c07900103901312040c0c46102d2000d92002607030301c44001c141c0d4609148500d03102014003c071030a11652042180e40da5034042001c0e0202e5129002d5924201c480e400004040c01000c0b551003c10b00c0185004d684c6655a0b038040c205e00c0003d1601ca11030b1400c8160140c0d40d0f0800300d0b400f00c2d1418644c503080c503069524040d05040d0750203107282c41030208900d010714401c018015100040c40c102e807940c95500ca05406900003900c0c413141001c2c0400c0700000d6100503015000352248500c40555036115000310351103030900e032000d8031420f10031352210703005880305622260074810001c564502c242c03102c0744020a02000d102c48030001d00300c1401480d090440252610f440305140062038038001807440c980c9508800c0c06d85001400b9034460a00d054650714030f4200490541c0701c050000140300b00003025500484908244144450307880001a04841050704004c06a4008104 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 610060836 1250 610059586 610059599
    0x40303150521030c0d02010b030d0f0c02010e03031b030d0612081e19020c0a061b1e020d0506072a0305280302045904060c020d031104 59
    0x10b044000031039900480b401c00c41c1c055509820115000c00c080c0050b99180002c210030316082285075a00401402c1c0000308080d5003500410311644098043d0502c44079401440c0c2c56141001140e94012003250142d00340100c3c0301d000c0ea26503002c603801e10401410102d0200c0d089030303c0511000070690100f005894902100c0003d00d55048a402c4031015250510804880c55281c440c015040003482d030140c03141c01000c0c000c0000c0419190808030402641c045280a00c00780b44a202a40a810207000942d40700010a0f002d10911280002034008255410301000c002c00000e40602031842d50b142c1841107100e00114580c0305800482040b14541400e00080c040f80c01000202003040444036280c980305150075000309030901410741e50000a80c00a41008910b400f0101601213100c0e403643c000c00c180404110f2035140d001040b148d032034141c00200d0b0000b2100d440a410b03280c50341d00380c030a07006482c0ca410305000030104c08104c0809400b039544001041e5201c1e00c615808024030341c001c18200350038020f = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 610062086 1250 610060836 610060879
    0x30105030c0907020c271008060c07050703020612010e0f0f06040e0f060f0a2906030c1201030501020904050a0209011205090c09090705120a030206070e130f050403031505 75
    0x7031540055000d44c601c2d03442c441e03c803280e40940301140d01c64030f4169030300310322819400340d43c6c001e0141c9500d003040c0782c003448022400300e451034121050b22541c40c0c070703140c03203007403050400e400c40d80b0003540074400087d008001540605800e04844d041c903481c0f8041d44c0c490800030440340007142c4001da480b01004c00100540780a600486c004000c0c0403c682420905128491a0040c2030b112000500d841c1740c108441c1d8001c0d802004092549003030642d0812982c5801d10100460801520f88214030100015115a81c03400540f2540001940c1551495a590400600130350003050400d001da03080c5030006080300c3c070034002c45c0c2000f081030b03560f0320075081c56450700ba0003071001034101081390040524205c0319980751085907000e0000c480103881007a18240c00c105035403003803074011216904001e1112020030f07008100b85500c030724681482003c5404140000781c1d504621910150001d203801843e440745405580040d100324400c2d00c04004d0601c2d002d08601c54800301d446440e51210035400d1400b1740c8550740d0f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 610063336 1250 610062086 610062091
    0xb1c0206030c27120d0503060607050f030d020c06070503010311130e01020d0501150f05040608070212070b0601020706081b0715052e2103020a0c1811030105030c09 72
    0x100080e0703003400b014402c2100c80b1040d5101400d10110300c1c1509640b585403d904c20006501d00400500d044044c0020150140c00000d18051240c8400704034081030140c18004c801032864503c041c0d0359100d1103100c45c50001e400110329480c0030300c600c10001d900940035034102c0b8181c0e41c110b010421328100d12010000c1c90204031280c1100e854450150310420310302400606900c01242002140c0c6604049100201100c0310384038404104100b451015040e400004450541e90203141c071a2031030340c4220081c2e00c0c04500070341c5442000c2c00051540b050100b1040c00b80c0c05110260b00791b60440796540030498002d41d0035241080c0514030607c550f00624500b60080400d103200c0e070000251807860b076100e0340803180211101d41652010400042c0c03d10041d01e030019656581d103000311900707420150300565418200d480088603a8002c00ba9034107050003040781898050340070700303120300305510303082e8900e1182c1c0007003074002d44a8189181e06030103015182c01d40381a20300240c02401841082c10400c480b88070003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 610064586 1250 610063336 610063351
    0xa0c0f150206060a21021e090a11070b1b0a0302180d020109090216170403050721140319050d0e0714060304020a12050307020907030203070905091f0e01090b1c020603 73
    0x1181c000c100147c40d003c2905513680003102d41d0302c100b0035070350090202651008103c0720340e00385820360291101d41c0950030340d51101d82010a145940d42c0e9040c030342c200d9903200040800c1481022554a0145a0540081920412103090100c94482072400c1c810100d095110007030108180c440c043c071020742c440d80a0b00380305012101e02e1114003030641700c04424411a19031840810400182841031010400002e0010a140c5120b07800e01c08440e200c464040c0c4003010014101018000e00d9940340c1030410a4803070046903405c2d00074580c035002501801d00c1d0f12174107000c901c0300d0070a205694076100118100c405c4602e2108002c003e0640082000181e80c0020000c0f68002d480c0c000100b49a000e20340c42c3c42182c0d00c030b44015507a4001c04c4c010480c0c441001050030041600410821100d00d0f03101086504843c000e9900041540b2031054071000d14000c41d03981008100003c400013241000104540d0407204004c4041015200e90018020313203850b0210350b101410699504d00005040190081d50311026 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 610065836 1250 610064586 610064639
    0x1206010b03100b0705030a140a12020702040e031909120308270d050403061d0312060102280b0105030f030a080a09060c0e0405090d1b050a0c0f150206060a 68
    0x4440410f1900390f0440b2006841c40d60021524041c4e0b69000041c00243d242d10f20801410404a1840144544c206150741400e40c2e0b00410003008540795074000c0f15241041030184e079261068003102e8111884000035003400620341c0280081c09403001007001c1c1800d40c0698440c59241c0e170354800b418544442e0000c1c3e0000e0129030504102284051040b40c1c940303000c039502d0b15548e51075402c0032016503441089150b407015802d18503100d580000003c0300c1e5403421180c0f018505584030340044c0d040601001a04050002203072912209184400c1c4200380d492043c80010590b9884600f031503940d040b12200c01021354402c02060f01114081c0085903030040042c172011034555038603941d01c400d8600010011000c0360811074a41e01e03500c0c0500030719510038100002000c0340404c140c0010803a81d1604880e001442c0941516030510406000460b2055082200d6140840e0b82d803905140c80c1206205181c982046402c1300101d5600c0413520900440009210485003030605035800c005540c90718201544a0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 610067086 1250 610065836 610065839
    0x1180c110d0315050616172b091b0513111614031b0c240904020d050411030d02030405010207171f050709210f0f20040b1206010b0310 59
    0x165920000c29500720b481611184e0b8800328900381c15084c1c400403d64035009400d08c904960061624141d40e00c0182200000006101000310000181b0138044040d01042c00c00c0000110083d00712200802c9803025580c0b00c550501d1400f410301120301d003e4403899154003c2200c080011135200b003e00a150145c00c40d14408807226900b940355070b1044040e03060706581680c0151610a0900941c2e020040640300c040343c0d2034428407110752091000c100440340100200d00d5211301d80b200d5054441c0440d44080c2085103082604140380a86504000c1c0c91007403160840300b8260320b2001c0252070884034103070020400903080c0600c40511003204024814a441003141c035281000c0c1d41102410b03c0811000009003605140000406c0701410740c0000c0315031110040409034041a400c00110300503002064a03400c100c4034078180b101145500c5015040c3d0303e00f604981d0780c141c658080010600c104580400c08807a0b0b4405002015a0005017001c49401c07400040190048010080d070388403084801380401d03503 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 610068336 1250 610067086 610067089
    0xc030114011b0326060a0902030907030f06060915030c0e0402060c100504020f0a06080c090105120f070306121e020f030106030f0203060708010b04060e01051201180c110d031505 78
    0x1008810706900041c4c10803809614074060905460910b00e004444021615000001c500e003190300f44251000c061340000003c41c03d1505005a4002d5603001c3c804085d1a80b103400c100010344440c0c002c8010700c0d45060000100c0c5142e184014046a0b44214510a2540740c501d0b00d0117082001841680c00040410031443c0881083c07000f00e54400d07942e0030001e21404c150060101c824580000a03000300d4104100340503542d00252181d90000001c080350766aa42000012580b50281c1c820100d625280001440043c50800040c2c0f4890847c90f6800c0151903520b91242c240c0c15003128020b0800300041c00c64100b40e2061401001c1c0c2c2078000341c00c1180c8250b4100100c0d007150a180c1c000d0b02c012120000400442c54180700c2c0640012841c070f818855541806180c44080c401d074894a0288401404a0b07251a40154142d80c0c03140d040c441c80702c841d980d44201c4100c980c03d500d44130450951424200b82074150107000d024810920304402880403245c00002034008080501c1c0c51000b02e546000e0006d00fa = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 610069586 1250 610068336 610068377
    0x20327031903090f0305010c02070602030a02070905150d0c1a0a0503040b04140303011d090c010206010618030c0b1c11090f0a050411130608010e0a1e05040302010c020d080c03011401 80
    0x8600c1b031400003501441404002742805a01e4200c0d50031504100440408a41e002400501343c0d0007200b000115a194079904262070091000e40d16004099020042c050101146180741143c40c0300481002c0d80003020a996101d20030388030200041407052000c680071900c031500c900d52040c401c00b1a504841194a55a49140c2099015034101c4012112441c00c402c54100c0f030f1504421040018070040b440c10001030b44804050060108020004140100300c8001b104020000c54001d000407001549500c240c400c0c030340c0306001e24149015021743c0100941d1491150070f0003541560b8401e81095148801c006002da81c1c0b040f9031354003282490020450b0359031480303054184406200c41c19603030a9901440058034415500c03507030074416040300400030740c4000c1003440e0b4000e1508034009034080c102d810f01d081d0303035035941790800744245000100410940c0542c0050940340303058080303c00101030041c0480d10400202c6181e04001002d10040200083e51310707921045880504244140450303134080c1844 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 610070836 1250 610069586 610069589
    0x50307061a0a0902040501030c08010807030201082716050105070b06010e0a090203090312090607120207060608160f0b0a120e0a02062b140708101203020327031903090f 74
    0x1035544c00202040250b0305031142d14105c030102d0500c01c1e6250b140450792503d032512440041d0602c8041d00c001901103007514099000191100d680c25001e9400d10100c3c1d641c0c03140c20008203203003440004041a1580104142e07046035030f1281c080f406603600c035401100c031140110001a00319000b190082940700060000d14131032210382c0b0045407210803203011065001c81c041c00c3d0360a260803000a110003160700455403074400142c94005a07640a06281030002000a80d10540150180c1661080140c0003042e901040310300100584070415142c0146554a00c100b000c8240407a07001c0c1c00594418031240c000461201c942d40a55803050055004515542d2244500b00014141030000d000cbc20408020b01d80c1d40507040403000c0151214413001e82d2107210010b04070409100c40e040000c0c08840031501c40c50054080b0a00d080c15055407442c001c3c1d03894002c50b80103015480c00b0b0300e501620074210700ba03420304040018020400354104641900c0003580c80041a400c010000f040403902c2c3c15070311400030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 610071942 1106 610070836 610070849
    0xb040b090c130b0d0c0f030e0a0209060a09020f070302010609020313030e030f01060909050c030c010926031c05060f010504150c020d03090303020d0c050307061a0a 72
    0x140c0c2c0720140d07004003208840014040d0301941160003106081103030383c0340c2c16040f212078031050b004d40e0f56803c194003d036405801071401514100c0a40c1da041580540712205960302d03400c480c0c0c00e9a11003201422480e200141000415509109040041400314411419420038460403500c40150000141c204214810700f00260f581c00e00012007413191140081248695406944020301345030304040c2c0e1903000b8154088414200490020907024050703442508660030109034401c9800e0a01e445481e0408035051070111003020001007a070301003482a13070014412104080400e44074001e02c4c0d18001c5424000140c80c81e40c0200580d802d8139070310305182d0701d040038101c402c50750500d440300c0c06036014018400e40402e25802003404016603010354242c90100e180c0682c203640d00400c5200c01402075208110350030210300d00d41c0c0304840940c0b00d115210511082000001d4200c2044e40009 = true := by decide +kernel

theorem cover : BRFrame.Cov 609892086 610071942 := by
  have h0 := BRFrame.cov_init 609892086
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609892086 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 609892086 ≤ n) (h2 : n < 610071942) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
