-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1107
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:16:19.867325+00:00
-- url     : https://prove2.me/submissions/9a6957f4-35f7-4089-94a5-784114301687

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 198920863 ≤ n < 199100719 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 198922113 1250 198920863 198920867
    0xc07030f030c08180102041508010806072c01030618090210081506090612040506070f090608070302070201020a0203010e01020a03060e04020d03050a050c0a14010e1b01050705150a020405150708090f040912 90
    0x103641a10005400ccc0d03429580c8071002030794142c0c03c044800492070b00c000c4c000100c8807200444410545014174020405c0c07a83c55500c0c4001d00d0011311940c07a546c5d40d4901410861506680001300010581011140c45c60200e401c01074960070350390b042d03028000008003600d4654680702140c000b20b030000c41c2450f007820305050081d07407494100da0001c0402c50340c1d80e05143c428010351154048413200d65445600e55a011341c21006500710141c220306610541503440c0050f0b43c2800b4000300078000100058480d4500300004050f600c076a80040d402c60a20380c144070140c2c40340340d848041e01c1d416041c02981c40c055000200e82500c290010b000007070190144032810001051101041c500140c0021300154000e5071110341c03078410405003508080300040072a8100d50092019044a90007442642c001c0c11103a514442000800ca9900c0a510b038000b50034055850400609078800e03416200701400d1162547d248a170341c4c811030080030711429028561184555a43d0880e60035103078410072890000c5001540 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 198923363 1250 198922113 198922127
    0xc0b0c0307021b06090409050a0b01080c130e0c011407140304090b121b0102010905030d0204030c1203050702011d030d020c040501060c2312030c07030f030c081801020415 75
    0x9070060040382041c5090025000164200c0c4800a02d042d00c3d100e00b4404210041511290880e040c0c0202c00074500403032419824203000b0203440019102c05800300c002c00c02c9000b881500f40b00301c3d80c90141e5015403600001503003c00c102081c20440d01441a19044607200c1c021085e0052021980c0722900e0030b1448080041c100300c4514484c14840481800100410401c00c0000c00456a20401510b049403c0c0752403280d00ca00c0040c00001041c00c41350700e500e0305550084140701d4903250002010000c01c04d02805200040540b007400046e05060341c4d600800714820b414002c4d0407c00c031f9905544a800c1003100510b2000c00c009c00302d6081a4080c0c00c043c0d1140051176050703100300d15000000440714000d0f82c450a80b0b550280c032200b070a00b2030203054002900703881c4020713400b8460b05120aa010759050002c5009041e008a100e8070745031103290040840c215500007000300b505200c4009000f6410103001a0092140b007100b05080038245061402401940d00081c004510301e40c69400c03113074000304 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 198924613 1250 198923363 198923371
    0xd0e0a0f2001030506100e0402160c0e0901020a1706191413110403020409051509060a2703120b03071706090d0206070c03020724020c120714010c0b0c03 67
    0x1c0d1a940c061010055003144da04848694101c18152860914a0b1080c0101007800000910040c00d01d4940040c074100110355040c22600d4802d40d400c180b180c0d01144001700c1c2c0c841c0c00b81c1700940c0341c065054802014144d04139800800800d8142c0480c01e107940302503151080380072101507603501d1907031001c09218500191181300c0c00781c40ca50350100c020400d503001d20444ca80c10328042c94582461a400c2c0801003040320130607107040c001c1421101d1402007001c003080c0a02d100800a10640c1490000c0c08100c40c0c02c100c80e1600142102064140724038214a4514415018102640038465a402200260440315600c40c0c6c03600526501140800000491500012100040305c85580c1c810352070540c4c852121102c0e0700541d0111001401a601c2810090000c9110348140c511207036568110101030686452010303c4c103504803c5120140d13504001c5100d0a00003220145240e4042e50142c03034455011b40141040c40d030000d140c031042640204441581c0030341c05140b50486181c141440b840b5604107407 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 198925863 1250 198924613 198924653
    0x904090804050916020d0e150c0f0d020309030d0509060c06070504090b06130909020a0f060c02012706030203070e120c0a1a03160908010c1106090a05030d0e0a0f 71
    0x4000c2103c1408441184007a007905800401006c640018103890108200360603940c003092000308001d886000d10003520011110360000d1884091100780705080c4684000c40034210350050000d121540c0d000640580c0c200410f080499072155030300d0104081c1d108200701400148548003e00c40425800001802124800041003001c115804c3c10401d00e0710811003014040e43e5400400c0c404103207207038805280b05200030718803600165900e842038541c0d1401e03804880413440c5034264805550300b1201e1614002001c8061940010341d04c41c090051000385d0080d48100755010001601050146802c504e45900041c00e034540903100d2440f280e44e94034880700c2c040c01032100d00d000040301107554840c82060b0800c5007425095584000c111a50841d8030a0500b08001548500242100080c420045540a00da407040b8005045080c118a032040252401ca41a40407070b40d400081280401910302c0171141d00303070105d4220103480405162811001003d4014126002c100d01000004085140c1e400249 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 198927113 1250 198925863 198925879
    0x150e0c1207030809040f0b13060f09141603020c07080a0c0605160303020f13090212010623181807020105010807030809010f1713020312070c050114090409080405 71
    0xc00c00031500c40e122403100078071070041072000e40d41d00d1a090f041465180513580c00028001caa88001a1414502c076400f03002c220382d998400e0161007154800e50001c2c1038800001e200da60041c240c01a40781d440103081c40000750013820000c0e0818800d4044889020002048401c025100c0c2e05043e20b40c900d88804a40f0803850a0300014200e0040c0146d60310f150f040e8103103c642072650380707040d0041d5004000c11210b0560801041140340000140c02002e072080c801c1c0107880e14002c40da801261031040e08040140820b01c20101c903070130700c0082c054103810f00c240d08642c1c445200309040c0d0301032803a20000c40d901c044108610075a490040110502c1208507500a0056903618628035440fa5520b000141030394030200031814041d401120000401044c40c40c102d0b0b80b0018114507400d0168013071f11040d0310305100c4040102549000c0042049422404590501d030058a42d52144214000d1103880c0c18490611100d00d400c0c04031406441254401030010312205078a403030032a03841e5005004080c41400c403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 198928363 1250 198927113 198927139
    0x903030c0f050319180303200a12050408010f05060f010309051f02030403091403120a170103030504050a0905010e01090e1002030a05040c24030b0303040306060e060a0b180607150e0c 80
    0x1170039040d000301c0780c0584400e006021a031085100c001c03110944014144a04074403d00015400c460391800c034003165581c192618106400c540c20340d80d01084044504e03090038280041a03130341410031140c8090908002400130300a10300942049204181003c80002c07a0504040303c9000350015807080b486076442e4002c6a0b100c2490202e90341c3d551407095016030150b0002d110040b24080242201c18546c01e00c0b1400b1084008000c0442c00d090300110006070001c2010801800c11030900e40c054030400790140b00355030510406282c589014841c0940c0103484d8905c035051520140a201c10344800600295a2840c1c131181d204d000c2c1c4000d85048514034422000080e0042c8d203455003022096540d80c0300312904c0d06100040b000b81c1100d008165250108100010004840d0300c10940100382c60390b070302e081d03524100003013000e500c00e1513001c2900104100000403010081c4c9840116000701210590341301c01d46800c01840014910300c0d154103152500081d101440c20004524180e09000c54406011441c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 198929613 1250 198928363 198928397
    0x907050d050c190b04050405070507020d0312150503300d0e0c10051c06120b0114060405011b0c0f0b030402040b011814150a1d0301020702010903030c0f050319 70
    0x50f01d0710400d542110280802d101da89070941240790000d10602c2e280d82011007d030002084076080c2e0004801144050030400307414425405000d00c150131900c4200409450840466140ea1a00c0319041e40c860082071441300c000d01c10b5a4100d0560160900951603009002c143c078020510182c035a070440c410701090101601d000101f44040301c800746e036502d09154503600b4414813980c0e0a45c4440d0380c4d03500d440012034182d0707403030b2001c1003080c0c0520001d0016504d00500035107203243d072545941c062142000180050b0360440300402040c001030a4400040ca00703030030700c2e98280030207410040c044a800c44000600c5519180035500a90003141d0410102030f80038010b6514209602d40300300c406014180c10400480040a4802c18010142040448028207424094030340d210b600d094001c1001000d01030700b400040b5010308504075040c1d00842c0b40503a00d800207010b40f0319a210003010064820031010070403003007540d400407081c0d00c03400703c87c2c036040c12010745100300381580c1c0351800285114004aa204e5 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 198930863 1250 198929613 198929659
    0x20a0e161202030c1b0a06020c010c031404050303040b0a0e060403030f0c090e1303020111031303020d0e220b0d0501021908040c1203050c0f1c0f090e0907050d050c 72
    0x92034132080381e440d014103007000d44140d02c506103100c0703000e005560741240801c0e200d0000341307a440500c8000203403440304014050112440182d9801d040d201240810000500c00001c40c0e03002600850558a03e58070f4040800241981940c01e00d500c2c00381d13000b400101034041e00101c40c01c4201070001d005082441000311081d410611030050048011400f2500384910200b00c100d41d0b0380a48000710f04040031000c10f031819401a900400c10340c01c4c44004030241941402420109111890300c0058038032000000345060744001410404500e211202d01d1501c950366208440c444005844a00700d6005402d04034002d420440c00141c590681000c81c0c040684600c4c0c24501c50780d4042203070104036080c58000300c404c0143c068101c0500c5800c00c000015014200002c40001d6005001409075414482c1e160000e107100c1c42d0403005004291071000662074114403450280d40780c0c2c424004069455119543c0ba1030010303400550441c00f04172030329061207030108090603d0702c8161041e507404081c0601d0a001e030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 198932113 1250 198930863 198930871
    0x1011100608070929060f09030109110315041a15030609010606030507020703020102070314031c020a0201060b0a020d08060a1502010b091b1903060b04080a170301080d050304020a0e16120203 83
    0x221a25000e4081c0c01d05d090000390201012030b40d80705050120f48000b180c2100c01c1c2d080b0590304148903401c03062482c60104004040c581400c1807141a03030415507501d80103203001540c00c100505c640d00020b21440c4070f0f102e45516810009013115994100f04c03440c1d41c020150f600540001078240000907800e030f4000030702e40c000c507035040e40201461817550f11801d160b100c00c0005c0b200309000800ca01036005010300c3e05400c1c4240700500046e900c0c0c000c10001781c21600540c0c06128032240c14030941c01c1c1d0940110303076004e0300307100d0341844022550350305c0c0050031000e00d80e00700550708014500706426440c2e0541c001080341c0800d440c80c81e61502d0700e60546080514140d5500c14881e800c1007480c6a046040d44070800701d045e00d04000c16050b890b8545c1004941040d0410041a030044030707450140150141c10400d680b81c003100c0a899941480540754940ca0105045818050000081001c540320710a42c84020f041082007580c09040280c610b40d1000003040e0040c00152100d071448940700214400c41c0e000b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 198933363 1250 198932113 198932171
    0x2060106121d0a0302030a111906090c0504050a02071b0509180304080a0b060117100b0901050c070321031a1002030d0603032c10111006080709 63
    0x1ca203416811001c0500118140009a41e050800c2001c00410400c40d841c0c00503c030360040c40d01c42100c40d00003003404018510400459002c007880c3c0b19403c100c2031056050039004040429185840d050075401d0344030b9640b065030070500d01001c0200041545d40034045141c1314041c2c483c110280343c1180802d482c014040c00c0e40c000400e0b004903015101c000703e603e8001c04020196400d2941e21000103050010803c0280c1c0c4000491007017012643c1d018000c0070144011800c41e0340346040c403102c03c05083d400e500800d40d40b00f10010b4454107503070150042e40d0741e0700482c00442b01501e0f26841c00b24900c0810000c1d02c4c0c1e10f601c48419101d5040d0190240241991a04603d80c0700c218401c42002021140349100c0e00a601040003298400e250702d02400d00514066200c1800a080e010105000e0101d40c150a810f660508080b03000035580e40c20200052002d2890180403841c19440300e9814021040c0d803068115140541c001841c1070049401c02c101c42c030f03040081182c4003629040d02d004480001542103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 198934613 1250 198933363 198933377
    0x60a09050c0318070e04030306170604050c010f020c06030115020706140d0c0504050402070b100f0602060c030c19020a0b0a02030402010c03120e010e0120070503041814070302070b010602060106 85
    0x1032003a01e1408031840c141d40081360080340da601d5030880141001c0c3e07025000651074950a10411042001a0087c2e00211009110500c0d10b51240d030b03299a0b01070402410002c01208940f00300f48208a03a11015000030402ca5032940d5039101d414011b8440030050b0003600070800002413240c011510300312058040c44500e4904040c8446d20401041003a50704000d021040c000410b42c3e03281ca1021b402e20501c901d6091019080890602080741c0c807560121780110100001803003060313070101d0103a422840056040e5100d44590000641ca401103080c80001d00d1030442c000c0b605a0f50000d00854664050612109103072207e25501043e07220894020f40441c00e500d01d1500040c1c80b91030500c01101e101040081c030b8145c9500c0540c29541c030040c460260303079120141c190070f14109100540303c04024820303503460108580c0e25a5201c0c0070300e03c283c55044102c581209541d20769500210071f620800c103041c00807458010006070081d080040f007515803211150003c110a800012154180c07091074440030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 198935863 1250 198934613 198934621
    0x70c020901030b0421030e0111190509030a0512130b130b03071107080f060a0606090b2b09110301090203100b0a080d0c14060606180105090d0b060a09050c03 69
    0x480003c401920444440318115517188001030704140150050380e0b207540110340d00318440e4199080d030340b460440448040f810030881c480c258404440c1c0c502d091060420640710040200006d090142c81c0308c02a0030760207082076108800c0d004e1001084941d0601e0440584980c43e440030a2045c0202d070a50104020000000e021064204000c2c40d070004007072514002808004080c0707410450780e075002a4843c1c0c03044070750344010007041c08400d6000903c40c00c1004401c0c0b0b8140010403c1c8520703c100782a50000144601d6107414140e0703109405d40343c6851030012400c00c0d146000c010b100948058036030741841207038181c940c40d040c0a60403110f60020b005141009020108400800c00315001603407000340600c001070318180500c24418000d2451b250003c03c9551802c1050204019040c1301e4006e4002c50100200c9555071000da80c00d01c0200d0261074100744083c3d0050320709108e4120500c0d801040100c0250400540c1c1489034464181607a2070596143e48a2105040d22801c0d103004026100900000e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 198937113 1250 198935863 198935873
    0x303070605180102090d080c0c150301140114040909031202120114031b041107020a0f051203030709030f0f0b190b030102120a0e150106050310050a0b0d09030201020409061706070c02090103 83
    0x40d01200c02d40009403401482e10030f0026000080d605114201c514001c8010001c1f1100034a85c1009503500b0f003030403008020304140d08131852089000300c400007992da06a010a0621034082920340c6034800703d00f15075a404001d10319001c0318091103041c4100f40e00c05041d00c0282004652880c120b051394161031541c003600020000541100d602030b5201031000d010400140e501c0c00e01c0c69000301040d40d1304200280c106410301c0000b040e507883c0302031030350300c10030912010750341c4540301c4402c8980012600300d8500e40c80c50f0110507083c0b2050090481210078051040442c1c1090002c25441c401100401c1100a0300081c18281d000b0030a2510075080840001000c40602d5004269907182d210103441c104005d40c2010340380f1785401c0c1c100c000010320104c00c00030011005e0148001820044031100a040e1408100001c03d110341c0c195000000d840c0e0398100708060003501510701405181707070180710050b120207084440c215100c4010f40e00f446080003165003540120500898590007400e000481da08507154 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 198938363 1250 198937113 198937117
    0x6030705011727010c03060e0f1e040f0c0608060310110a0509030a12050706062310120c0221041a071b0303120b09010608240303070605180102090d08 66
    0x1841501c0c2109a20343c0340030b80b0078800d00c565120507443c0003c02c030303081103000c0850110040400c60807032081c40500582c40045503044000300c980c14640340c0d0036540e40c50010060f0308101001060700e600213102140c50340e0080400b40c412f240540c1221000f01c004403078881901d81302c030018100350304200035404c91544600010284004080d00702d8914171104d680e2112181544e481e903000003803021511404100141c01100c00800c1c1c490703031140a002c0ca01003115440c000d901203c0340301b590030f03c240c1c05250340100d07100c10340304086e01c0007000303d84192000a0340f281141000f80584441802d180390003184070f4425102900c25008400d0182c2000450024959105c48003d50350042da8410100e10041e084010102842c03013a580e91005000d91000e0b041a50713034070200c4a11404000c801030002e00e502910841d40a0642000c8d04907a840c041c3e5800d0b10b82c04400d0100d501400001a00c40070b1181d580c100f64007806942f038804002e154006801401c078022041341e01d40c421480350a41001c01c42000c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 198939613 1250 198938363 198938401
    0x240201050f07121a06041403070b09010e010507030309020a090c0323040209090a140d0e010203070b0c16140a030807020f0607030f0f0c02010b10210c09030812060307050117 76
    0x460700444c41a04000408070f8000350b0150700c0c202e5180c29446410f040502251000b400030f84a07a84c2409890030000e0801e440c0d40b040c003810400302280d58014544603810041881d80c0151170014280d444d032404402402c503802419002c40c0c20302c60350350b01e04100a10290412840710417040e01d0b940702c41c0c2c200810b0200180c49844c0e648280c9a4103000b0440d44c600400e03100441d0710003003018040071000540036184000b002c906540007401014013180b120008581d1140d400707800c040d511500003803c9111084000d00140101d22101034104100302c0005508080d940207031101004ad540d0b6000403030b42e0302c4414000c0d2800360821008076400501940051040760240e90011600f12241c070300180445040c4a840b5005070b4498200020314100902c0ca10880d8900d071034881d40c0a0190150356a1000d1309070500b440d103075950105071f141e0b507205076450350140d0340c88256260386200d5403c1c0e000e42c104043e96260700c24011404001003641c010b421206400220060040050b540c80044a405842d458 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 198940863 1250 198939613 198939641
    0x302010b0109050f090402042405010801090501060813050f120d050f01061707170c071403130b0c0a0501090f0b09030405010804030c032706080c070206070803040606240201050f0712 80
    0x41e9011a4100010141050b09c1074200b1140401e030326002c001045000180c0c00050341c5842d141c0107101380d580c4907440c240c2c800149440354921803100e16081c0c0c6040842100e5080034094143d000c452810894010320508100503414003032a15035450030b2111040030f2040c0c1002c500c00c0050300d6142141c2194003503010425042c904258401131069450b02e13001140c0f01e2a89220014503041000a030504000103440c28500540c1811b0016080000c0c4226074000c00c942e07100042807822072107038100050706502d0707071100091000410314070700001c9218030340000b01c075005079400c00a510380030300100b13031800c0303c1059540c4511030b12192420b603a10320386007030143d040181401200c01c4960000762280758025002c07003500c08180c645100100a60300241007131a152200700441801742e0340e4003007503c03061504001c0c0c145d40c94680307140c240000c211581c40031a14030412400602e207040d0100c0c44180180007a0005c6c85142e407003510400001004460305000b25010721440000d041c12644035110039070f450 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 198942113 1250 198940863 198940871
    0x30604121803030509030607031a130e030f0306150a0e010809030d0606080601020d03061a0a170a02280914010c0807080309010b03210a0e06070c030302010b0109050f09040204 77
    0x1c05216200c501d00d6400c15400b04100042c2d1030480e041c100031041d803000d07071807a0404c0003c03400030420200380e0340d5900c0140b0807400400348000c0320655501c90788040607a86d0480e90750710300c541e00e15003054001315640c9110720000d183c0350341c6000104080700c0b020710701607940709901c50b44c1100548000e000502808841e1105005000b0145014800d01010b4101500e0324942d42c680703c8002441c6c400c003104440101400d20300e08000813a408109445011120101d05417100c6900200b240c5406951070382d00c4200c19024180010715200f80c2c001c0c025454030b98415203680c540c410004040e2030800715a81c001401480c0204114089065804101c590524020320442040d44070f0070304640182c0015100400000148035401509201d10b55062000740c01a02084604c40000744001050041880003003d00090568003240704503116414a100140407030344032511030501107103004d140e002c120302544c030700040700c00301e903008091040440e8001402c20b545e9103c55014400c070810083c00032a0041d4071 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 198943363 1250 198942113 198942137
    0xc130305060f060a0b0f19020115063902040b150d0f0b1c0f050a0807050607030c050c0c060f040509010e090c09040809120c06040906080105011403060412 68
    0x2482102d010308038111042071182001c0e420444849401c1d4055001c03c201085000000c0c5154410f42c0c2080402c4a9217400c0040f00a80690141c002001859410200803c001c0394150300243c0d903001c001d0a401007165603842c060365024600d41540104e55140ca201c9c140f400c0146026046292003210203400d4034000741d40301303844c460035810001d040342949458181903d042d1250384190340e00380f402100c02c081c10b0550010704100082900c13a011304140c82c450346190134000b04102d405000365001b400c03907507101090b080c0240c40354020740d0b250380060300b80400c200031640700b07074151020100b42c0300141c01c001004ca0f0401000e40c0c046110300c109044240710010b130079074640b9401c5009003512a032003982454102c0d9503c0c00d140003407610034031404040050202241607030098400088041d10140114441090118a01461460700c0742d0702010000d40414120b0040c2c00c20802c50b00c00c10000e01c066620fa544c06c2048406240380542c05520030030002c1d01081c99102c4617803a0001c3c90502c5048420 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 198944613 1250 198943363 198943373
    0x31506160615050114070f1b050d081902060402060f0c0c03030c01140108070f03060b010509041a01170603030a0f0516060b090a0209030d050a05130e0105010206090a0b0c1303 77
    0x1544146490002c1c0541504010550700502040501008145840d15000d0155a100c90824080501605110440c084d40556004040708a000303031200502e0290f02c440300e031034407050907030020794a000c11102d0070710920816400082e0103400f99034001c1c805030801d107401d440e85405400c104401c1800784070b010079241f150785003840103004100d2504004a0030802e08030100c040c0b4241030380522210343c0300c0c040030414500d10404000659a0004000ca82c404001004031524010008555030152511407814101c0c681c3c0c03200c0007903041080c2c072100a15080039003100c0840500700c5801c2d805030000c01c04d12005610520f0030400d10281405c040e402c010503107110808095811030104d0741540d0703030740507502a8a4074010842c0c1c0080026030542c07401c5240b40c0400d4440f16040007040502038007041c0001010300a0007030342e40410008402800c8559141c076010914402880364a000d40a10390102c2e5811a0104035a41125005000c509094550880041c0e03264861001008207140541002c8001b0b0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 198945863 1250 198944613 198944621
    0x30a020a080f0f030f070809060f03070306050f01110c04050403180303120605100f11011d06100e0609040f030e0d0516062c04140702030309010c050315061606 70
    0x100d001d000500c002d0070b40000c450720301010034500101c15401404200c003000290340841c1c100c1c85e80f10110a03112103c840c04a007150084150600c0c05c080302004105125501d82d2200f812560100e076011140201030340150394506003229400301a81240c0f6030702e04281020f0b04229045480391400a1411242400d000e00013900c580045000070380000315401c4c0c90044e401504080c00040312410595284000080c00d00c040c0d0001003400e014240d80031010f82e070400e40c0003c692000c070859006030040c031503035143d8036150220340c0e001c0400014400414900c0c4004015882880051b1681110740c40c5c40c0c9814004000f0488100c04001e4950140c115949441103031600c81c1c4e05c2400144001a0b5240307500c00034486640180b0208017841010070024403405d5182c211001c0b00014070900c410010010401500525000e044400d5081045c0f20103a58004001c500c21280000208004081507000326614403003a94208007900e020604840c29103028001042d0f4800d50440070007200c002903480805407 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 198947113 1250 198945863 198945869
    0x806060405030d0f1d010e121c090f0e040206070b091002070309032307150201020c0a350301091d010e012301081915090b0a1404030914030a020a 64
    0x80d0212802e9080180c00c00d0010703000030511749000c00c1700b110a44c0003c050050711000c291061080c40c0244159950621040c01904d140510701c3c00380f8000382d80b0141c000030640c420300d0303503492072860f0018110f0300e00c0300f9542c0100d90090400d480e102540d2a4820348501c0a0701e08629400781c095451003404040c801800118484c5d104c8504035071840c1170800e85080ca0380c07501260318040308004081154003040703001c143c0e82890010444482034000482c024010340885020520852506005001314049010340c48640c2c0110403050308542d220000c62a6003100503413154910a100500400b441600b05252009000f07402c03034116800b0070380c0d00d401e49402075003404850b555444070f000c4107011060700c05002c901c600d59265855241c00403e5503500c0b07041c0303c074400810300350081d501044103440041c5400c48000d041032240e030401d810106900da80c01d840510280b40382182d01c0d40a4502c00049ca8841c1d50552034208595107448144000c20803d11b40056141c0170710006039005a80d4900c00701d001d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 198948363 1250 198947113 198947117
    0x21908031204060c0c050607051b070803130807120303020a030f0207060f05071d040b0a0b0d0f061706060904020a1205060103060f06210305120903071a070f0806060405030d 76
    0x5604003800c1440c01c4132130341d4200804001d02000c4400104000081141d0012503c2c9411036403045036172103404008407068020060390051100c0002c00c1c58002001e4100c50405481805c600c07a034503110903a69081074071905c0c0c054220003417281d0110f400b03a07028221140c442d00f408690f80208050500c100e17840320a084174901d64035402112414201c0c422036501c2800c50074104c4e04d00525040c007803207142048001c0c611507500c5602e002c04c141c4800e0345a03802462161091034886203c403032410068001c601400c0703555440c0400015001d00721040c003a0142c0d615602131300443d22401c040c04103001008000b40d0700310b030190000061701d884c1000c0380303c13550340980003038a0654150f141c030030140c812055400c404a03092400511085481380301a01a02c155506042c0b20b87c0c695140aa6032800340d00e440300a203480c98810002007060100040c401c1d1441381000c01307002070304200a062f00d940140e80000010300302c07405031440140181c0c01540c00060090200c0d09080e61000020315200d50300240c100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 198949613 1250 198948363 198948397
    0x10f0902040c02012a1b1406070503060a03060915020f03010303020f0705010914240a0e0901050303041503240311010311030a09020310051e01080703020d0210032003072006010302190803 82
    0x214501c008e00403190408001d03d05a841c50500c0000200542c80c103020180105a441c2998002c0000d50302650183c1d00e440d0700e06644031442c1c0b0b1440d00c541e0308244000c0d0058055101c40340301c1c1c000c0100e81c1c1c4081c0c030416165007215604110103e020540e8022150b5000b0001001b100040c6045103c3e418500d0a05000b00d9a2800c2c43c110080181210304000b0340a45401401030099035800700945094604a900d00d1880e9080c0f0700c0110054001c4c50303030070445070301304032071900c1e015080c04164001c1c0ca02400807510a07106800046040b0380060304081d01c5071205102156590180b6005401c1c0326000400300c5c1d5020404280c1e03c02255025512489142000300000d000d040d496000b4a0040005001a00e1007130f146801040d80594441d1000303224140880c01078070400c0c0203a120843c02411507254410440d40c0c03105140d1150b00940c2c0f0b180214040301300940c4032622400b440498a4040d00c081e1200c2d0b4603690910140c00c5514081c96142c00d071805020458290420107040d0714000858159 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 198950863 1250 198949613 198949643
    0x40803150f0d15110f0412021c050106030201030506010c0302060601110c0a09050f070518010e04021902060105040b0a1a030702011b0503100905040f030c05030c010f0902040c02012a1b 81
    0x140032a0030100c0e4004213501c05108160f001c1d00c01c4415641282c4000903012810415480050000d00140c5c3d121003000d00130f50801d44c14064158004400e480c800e032000c100c00d450b00401940c04991011005006900c92000550300354403542110621461000031541400545000944031580f140c0103082c00135031b203008016410000902c000d82120721810503500d05800300508a4843c074040f2207040c14080d48010340300c100e448035811510009441c040e092551a03040070002e46401080c42550700c140d00b400c5c991b401301d240403801d5104035152905042c540c1221050161240e03080240808159585d4a08800100c416450743c108281c04a5450b595a483c0402d100300103882141c015220345450702d02000000303105510650085605402c00520300405881d015107144541052034400d035090001e95024030701146c21406509100300c50500a80a00240c101d08a5030991030600740100c0c0031080e4001d04400300b2a60012104520f012206030001684040d024103040720116681c00481c042c030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 198952113 1250 198950863 198950903
    0x1f12080702041d030708090a051807030b09100501031107050d170a050705030601081906080a060f0c050a0c05010204052106090d05041403030d052805040803150f0d 72
    0x4440072400c2c442e00703c0388035156180e290b90701d00544400404814001541c103800f0303511080050b005050040c2441c0c5c1841b440c6e4640c0c07031100c1d015180700002c44d0900f4513003c114034054010b144100440d40f0381001080c50000110041c01c4146840e4045801c00c0150f940441c0051000ca10f55003400e455480c0c0c544090f140070000e02e50001d00000c0c8051034001030016580d8001e080741d420071801d10b068809502c40c200080b034045113408030000210710342400059050070104407210082c0c01148100120028001014140d41c160f00c0002c0c0003810400402c6440e602600b801e440c000e01074030006060940b2600862940c000300b1003034a0240314604c215808958003001441c3e03200203c0000741c5086a01004080d000d80034038001c54102102c030403000c04e800e45080040e03540741c0c501d00c1c078140221706002c6441c4424020074a00d402d03540c260710b0071030507046000d4020a80690f6110f825507240d0781d1803110300034084201c92861680403c0b11105102c103940c41000c9402014080c0f0f2082100034140300398 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 198953363 1250 198952113 198952121
    0x6070f020307030203120403020c0a08060612010e0a0206131a0904290f18010e1e04170706020c0102070614070309030c080c030c0604060b011404030b1f1208070204 72
    0x20010455204101c1c50700001d03804020395006807040701c0d049007a900c99141c00d0f4240150f1520380d030740107608101c000503002d00002d04e05010f484255082860b903200c80400b5400e0310240710805100b6802540c0507801804d14a00807c4210f5001440040450300c0d514040549118074031402c010b400007040b00740040c034041c070990000d1001161003031049408810a080ca0015020580744103800c070500d00d003081d44a800d8030411079070718800712900642e160505c2100c061025680d140820032000ca21a04012141d0b08d00d60060341c104100660011201c259099a43c0c007100045a086800b4480040400424005841124440c0c6030110321001510420307001e0300ca00038400d204160600c459007010a03002161518560341000c5403e686204100c1818039601c100c81150000740306100c10803007400301c641c1c4480740c111400d98602070ba94025542101c10350156002c003402d1002e078500801d000c3c0016000c032644481200c00400b103980d544401030007a50400310700507521240d00090200461909100e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 198954613 1250 198953363 198953387
    0x304300903061103130b09010b06040906032a12080417010903080603010c120b0a0e070504080d09060e0607140111090f10020c0603090a05060a090506060f10180b04080607 75
    0x43c4071419858845031184c00d100080300041c01d042e03000b40100303904070020b401c105500c0c18050805503803a90f494400c1d00c0209990b12040e030b91136510480302d942008222451030696102d6071100c0b8011820603200200211b068041100d0191080000250201701c010203d4220180c00d0000103200c01c0c20300340500000b000a060310b1007645004140401580c000e80c0d00d1044108000c0c0004900951001140502c407403034000b802615240b0301040102c6034040010300c103481905007610380d4a40f002c241907803d0b200c030f80182c5003c2000c0c05202952410010058452680150030581c03034907940c4002242141c40d00700c141d19400718009400e8002c0d0401110200741008141c4400a88003007070340c0d000b5120301103000c40c0da2144c603000001c00c65840041126121154001c4282d62071070401c040b5840c01005021400c4405004001c00900c02c0d141c6040c0301049088054452440100d440008543d580381302aa400c940c0d9010f08000704e507014042c4041d1020b403070104010183ca04094101403e100c00c404 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 198955863 1250 198954613 198954641
    0xf0c0309020a0b07060e01051510030b09060904030c06060b0c0c060705071a1306050d051513020d1808090a051504030213060b0a17010b0f030430090306 67
    0x1408000c01070300e400d040d4204689100c0011611030740d50b0319024014180428104520390f00780f506019150b0042d0f00500d4400804072030450100c01d40c0748003034065843c4030b8200e1394440aa940040c656092600760b080d030051103840d20704115940b66550b081103903410341206045a00100e54614500d908100c030218091080310b0b55400c01a050340c40300c0c0c0c0d80345107024462101c100c0380c1c1c240ba00a4041d00c03d40706c075010310101984015480c0d17032006010342c21902615110361300308400728030502c40d400f01c494400e880c082c08854114541c401c8000107503102088800e040c90b5582254005603481061000b542403140c03040d255124100780401141400a40190b4800c100c980090a1140c521104440c2141d6054400c00352212200c00c0c500001d00556001c100240d400051a050301644401c48000c42060b0040c2240e059890342c00c014143c5c080d1850700c0d544408100081004125001c1d02c440103000f4902032484100d003040050100c04007546d4008001c00d04603007090080240b640030f260a046a14 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 198957113 1250 198955863 198955871
    0x60912200441060d060e030a020c130203041a250e210604060902030c06040311090106020304080a03080a20041815030f050a0c080f0106240f1b03030f0c03 68
    0x2011802d022280050081c0b40300340a0742e10b819013001a5030300100e40442c07081e01602d443c1e034003a281c00703520349400c540424400e550020202a0407042e0384207481c081ea8104850341e401241daa400c4000030417000c2e110b024400d45843c03c91265176014a214074911002d541c944541c103540fa41800310641c1000c895451000024020f1a04402c00241881c0c1c05604800c020880c004603001080c1040c1c0c00a0712190800f80004000c01417160359000035181d030300150307102240c50780d0f9504200d880317010b13601604100d0303080083d418010920612840350401d07000d00001440c0000d00c0601035104980082400031008081400c002c1401d040300c445030100b005003030034003000c050b800076805440742a01000b884450300703204403401d116040102810745030b40a2260921161503c01c02ca54543d012030740c110680d0308003100468000440b01407005041030040c00001621640882a118001c00e415540c3c10415a08030407142603001142c15120b5502988000503080d00c0070402c0003e4136242e0071100241410 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 198958363 1250 198957113 198957221
    0x705010b04090209070c03031116020f01030501030506070311040b031f08070b03010e090c130b0310021602150c1603110f0307030303050601020f07030602130609122004 74
    0x190001d04d640b190503031030100c1c0c0302d514510b8268014064415000d00c80c240115a0300140d007100000444054002c40d2101c0c100c0b020f1000440541d982408002c0c03c54200c040071031101800307600b1a4080792001a420fa06080e01e9005442d80c03a0422101c100340c0d00d40d150007500e109404850100060820900940303803890070700e442c1440922061013000080d40da01400510302d01024400a0074400c0014030041060821005020140c0143c041e030350b00c00c0c021104001103d40c01c40c401c4a803005095003500d01800e681740c003044000f0407209500020054200400440c0b08020b2040702c200b503001ca81e0000500381581080540e076000d01d4402405030860705c400356400e0f0f900007120011250315150100300d95480c0c10040b400c0991203120400180310304840442045020b4028212140c40d1021005245076900c0c4100d48060340ca00c1200301c01c101000444010951502003000031031103510901584040a401080840b03130324444d00540c40204902110304182c0c03800070002d14600050011a00c3c0b81 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 198959613 1250 198958363 198958369
    0x105041b08010b090103022712030922060f030b041104052e050a0602010204140a050117130c23030622050f0f100501060203130605070309080d050705010b040902 71
    0x1c0306000b101500304011460112a82c4250129040000d140ca00010480900e146011412000100700752013415140c5194a000d04000262202c4841c02404c84203041c0d000c100003400b00c0800c0f540c1514140d104c04e000b00358004000103c000861242c8650003035071801e8103090710303249401e0031039620650405080c01707804403040d0904100648100803000003070740c155401c01d0351032042d90303c203c0c0c0009142c0d42c0015443c3d010f43c044c1084441034420b20918504074010071030160328500441d404540c202503d04160001e000c02d40c0d602407042c50b032159128030b81e0349610b0b15100b940d42c00314010304040c0220380c50500c01c141c00b0881c440c4c8141c004050b01e040001c8404d8a07100d03480b40d89955088401c0e1a0018000b080101c01180c4442c0f0055400b4070f4503c120b15910f0300071118000d11054202800066072510000c200c4001223030304c0700c0605055091004c111074640c003c0d03805800300101c1d035001180c1458140003842d0010310380d44815580c3c580524019083d5440d0044051190349450480c40c0961 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 198960863 1250 198959613 198959627
    0x91103060a030209190c050a170615070c081204140102060f180a0b250f0f030b030c12010203060307050a080705060a021002030708010311031f0c1b05060105041b 71
    0x6036040b00d10700815920b0705a40817041111030043d15604c2d00f06194036a409030400002c00a141d004d075036400c50101111112180580c00340c0e19250000405445a028001da000c041c0c1003083c41807620349281c9940c0c0d148a850038001c041c101120300d00011381048015a004942d03c2224000c0c00544600c2c60940240780c40600d00400003d0b460106403904000e08005014040c0390540c0094402c09900b00107400d0219012055030214413406042d02c100c10386809460f00c1041c0c900280d8464510201c0c0d4441100034048001d2400c1d01840342c21100d000e50369511740303c940302500c110001038a03840c11008144c07038005260312460254000c55428425414017107104402d5031408d880c150b070350380c00c0600128900500c03078200034113007131000c000c0c400d10980c0840014104c0f80102c000c0e00115620308201521040d000a0012040210000b04240860160056941e09a1609040a03221203005000450440a040880d025044030340144440d00e883c0c4110220b00040c0941e0506850344c1080c00740c43d80c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 198962113 1250 198960863 198960869
    0x10c080601051e13080606120615010e030604060f05100834030501060911030603030304030c0201090503150f070203070302100504240203040203300c070801020310091103060a 77
    0x51400c03078051290b03090054107480114501d5913019000e0035070604d12080c1c0203c1e21580505d0010030024503024402c1c1041e05401c4005d01255140c031264681d1020210401c541071082c02d000294484e50309100103482540202d10110340103044025580885800820301c0c04e80701e10600c000e000c004000100020400342150a40d80342264071501c40062010782032681e18840320040c0088100403040d0845030480300480c40c00d00415000c0e50080004d03000850307100707405510510018011a200c4da45c1c00c60440e0040c101100925281c0004c613041a01070401040c0c2c4010480c244882052003000c0c3c245e0100703042c8007850a1000300c0d80d00940710010116014900ca84540214081c0f045200d800c403901001d40151410142c01c480302c000194008071805d921174012802c11f080c07903c50043c10000158004000e00001c01c01c2a0041840741d000300030300c01103501c25000003040700d0704248011401016040c0e2242d00382c41c60308400d08242ca5454200414150702401404040c0d110000711100f6 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 198963363 1250 198962113 198962117
    0xc0f0f060c0501061208071a011a09010314070207080f0c010c03050c01060f090b091e160c0515010314030a2c0a031523180709050f07080702010c080601 67
    0x200300410b05140740134008a41045482c9850341141e4010050b051006000684c4941c02c4090041001004544010b009115040c4000c1d010f100c41c42416821000030031041c48141400151400e040b500304001401c00c0340d143e0b025900c50765003880740580c100007440030045010000c4c00a10078200000b4191030400030020140540880c10480c140800e401c080e02804280c0b440c030402d95918044400900b2904811501032807100000c43c0e2280812071344400c4c1d02000005842c1d46450700300301b652040c1e8003400407204100c050351420000400038010310000c08401034100e48154118101074050186d4200c80300b1440c0d104000c080d05298210400e4a007100b4001c05c4001c0b101c02d40000c2d0070300c40da601075000d6030101d1250070200400034094001084007105401c10004800344617450900900c0000c05c07055100040c000050744005484507044102c10701105441c041940e85000030195402960410681070081e020400b032680d00114042d0303c1000e600c028040414031038406020303000090801d41c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 198964613 1250 198963363 198963377
    0x2030a080702270a06060f020a1106090402030c0304022814010c0510060609080f100c11070308090112020702010e150f0c030d0609060506040e060301060f0801090c0f0f06 75
    0x30941d518005196a020b0310710740c3c80300040c0341d104041031540000b160b01c00200b5140c00408289240b1038000d450400e01d07143c0050011a4032030711203203c6006016030499000001f000700780385d5902c5a0014600815101030b01603242d0600313104100480360003140c40440c1c0c00081c410190481e080c0106501143c04801c1010200300c0440c004903910b81d42010302921912442c10a2101d000c996030201c0c080f1201980c074940c110782c44004d103d4030345100700c2071020594050448042d00405943c000010717480541012191101c0b20300301c0c2400c0013866401518030013000700d404211942c21401500744c85480280071442e1030740a41c0040c1003801040b074824010050115040d40214600c4126a6001280d2071520341f41c0310f80100c010340c1d90340302032441c0c4040c60620200007012420b600a8000b0345000400342801c0c20304000d080c80030341c0b80007010245e040d074803050009030110028041d000079007640400400e4a50b0b131030030301082025a036489640d840c50b12810412044000a07411303419100c85141801d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 198965863 1250 198964613 198964627
    0x50d0b0c0304151103041109070504140406030c06020f1b0a060f0c0b0a0903020c0a0806060112020f0a09031103060f01141f08101a0a0f050c120c010b03010902030a08 73
    0x94280924a000325220f81e1070300c42c80306070901201001d14440c0c1e10800034110041590310500000640c10790b503603400b140003440140700065107004404110200501b0010340036540f601d072284091070300d071301c07110242c3c02c0168140340e00801440040010040c2414089039580e9074000701c0e0b01c21030680b1420041244c214041801c1134400c5c8040140c080d08141c0806160030b254580700003c02c8010400c401601c1a0400004581851264641107d1510b80a0500c60b80da180054444030303502040d070742e002e82c0d08000504002c0c05902c06400780010607603420700190f09520313090304221031174244a880381e40b214003002507400303104003418151182c40b1310b0502424010008528070001c2500d03603400038460b840e00410040da102c0100c3d4845c00070101d98040e8195200034a5000ea4031004e002c2c0b62030401040407400c0a0300401d482d0201c5195460124038006280c0145030030302048a403407903181540090446403200c0c2c2401804050103089008008002c0c0715400641d95401d004002400789201050b40 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 198967113 1250 198965863 198965873
    0x210b01122304060b010e0306040803040b1003080a051c020c07030201030c030212010801200408070b03041a0702010915140f0a0b060408010b03010c08010501021911041113050d0b0c0304 81
    0x100c0c0c48801c01d441c044a081c101860210003918820b80d1903400190314040c0e100c650b20340080c070240515082044289152074548030714a80340d00c028041c5540c404488c00c00000100440010b00e0409032998440713848002d2140d1119181c0c1100c01c2d5074101c83e005105103100c034840450320504695090800040042c008101600a406a04030b10072b4140c0040c0000501c0c02d0040d0000300b56031020003105806042c0d03601c0020003d00490041d458290721544040c4038507010a401950054019000d8440d942000f014003869140d0449914005075121030485042040d10040c104814080b9207080c004000c8030100c00c50000d000030b011040e910a803002081101000d03a0140130a6074025004070340d80c0362209506406801070101d04c0713000e58a4501180c98280c4101e100d54107070750050340903000c3e028804d0915010703242202c000362440000300140941598a510898000260050181b5260768081c0d0300d004a106450b400701d405802c01ca1a04400900c00e1b02c00315911441403060103440341c8542c182 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 198968363 1250 198967113 198967151
    0xd080f0a050901150b070b010b1303080a05090909010b09090f0c0f1201050c0a1e051204030e040606020a0209160212162306070207050f0f030a0b07210b0112 69
    0x981320200c80b200800b2400c802c0020040090600518900f1016686c68909041a210700410058070b082d41240504c00101c54a0050589501500e015030030304400c240002c0c1958400c0c0c1d01e02ca00340c0c0d540c1403c550203041404640e40d10498603400b0b42110300c04212200e4450784030b91001882028500c2c81e0210b00da840c0103240700c3d144c008000800051500c01d40f40ca4856000300b401c00040361102080420100361983e603500c150025503502070074090004040034880001403c101d050022441c1c2c1c061b0592254803911005042c540d004040700b44442c01400b0705001c01030700d10031007004540d9811412980004005112604c80030003c0e07568601070f0103020f0090302d0800024100e43c1220890b521004814a84c2c900c2d202c0254240c58503526001000e0341e46000c144949900184881e1b07242c3d1842c60150f4202840d6040079054400080159882e00d8803110111600d8011803d459000c81035062070841d00c40d02031560000c200220442c510010701480e504107050f00c01d6a4542184500c10150801 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 198969613 1250 198968363 198968381
    0x210150801060602062a0a08041a0a1b051206010c05071509090c020102090a1e12063c050a0e010e07030b0c0a0912020604120b090d080f0a050901 64
    0xc001c200342511450300075101ea5040c1d40110440d840803041c404244d9040c48100c240c5100441000d11307203202c0100076140c4070001002a0344545640b5100c43c25000304644481c03007080030403000151105c0d6400480112110750f00070800f004000e124003415000e20408113900071009092201458615107002d0740b03080d402d500701d0680b041030201c01941681c0c000d22000d080d544e00304014040f4015508049080340209030255501001d064000c014413102030501c14080704220008021072900da428102003071110f1041103545640c2c80120a140f002c80c04135102c0d2840c600d5200c20580258204c104440718140340b0030742007052360745010583d1030b130b2076910850060505800134051680c0554240345c0b6102d072480b06440b500d0791000001c1c1d4202c29a400c80f0380d001c01d07584450950504010350081805c5511108071780110003000301088004024113040c3c1c1c0c0354458040e04615260100f12070741000807203900c103014080030100b44500d2107440034506900110015000444c2d5580319041409080560 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 198970863 1250 198969613 198969629
    0xf04091b030507030201080112050d0e011808030417060f07030509010204031e0209011a0d020c011103010b1902060112020907020c0604091409030708160c050a0b0301030218040201021015 82
    0x40c000410814040750034030032a8000d80354990142e90711000c80f6144512070030020326035040f0350140203419004a140700140d60040c500244400d1246030021945446600900700c20782c0041010051003095080740152403400300040d10b0281483d00880c0800385000d03202009060321a00002c3d110403096054900441d041440d242003401c04030307040b401e80d420700d0030164002c000b032900101d05a421004140d855400500c062841c14030200c491f54000d40013040c00030415500d448104020301c3c0c0c2500034501130b0850708183e656601030003d1813001200c81c01e00c010159040300004200c3c00c804c80101350810b50301039902411a58400ca030490405180d41c0e0825402000400c001c595201d00c1d504c104850401000f06118540b0b40c41016940e90084600080c40c45004000049031920724032242c40b0303100d110310200041c50340c80f000051420322940d00212495203001c00104250306d441081038442e040000291100e0f8206030300001e4840d90046000f1706041c1c0c41d2504011811401800040180404 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 198972113 1250 198970863 198970913
    0x10b03130503070308060103050f0420031c050a0f0f020a0f060f0c02030a02010e06040213021b030f120114010e100521040c0b040b0307032a1106150f0409 68
    0xb84c5009482480300b5075003d8002403802001400e4041d03082c0c0030324066904002c1c0154010409400411002090404903070035000d00200440160203c0b1760f1915100c2680d100c4648503c0340850040c50002c2041c13000341000040c4050001e6581c0104003c008a03400c503c4039202c062807810401d0103007901c4809908110300c1e248202c80c110740c2c040017401498803554028003801c4628014950fa4510a680180d44407003009180803148445a0007030201160070b8550345916114001018110f403c81d04d920f02201000003200c075035130645200c0443c09040700c482c03a14805074101000a0089505404c2e160068000d0300306000c13602c4c0500241c4606800c0345141000031600020031284000b010b1300c040340c025a260303030f010651001c11401d5074142d400a05080c1e00355038484100f28007801ca0145800c00900d00c24410b81d5003602d0003030000d8959049501c40d400c000113005102803170402d0081c40000200b1012060750803d03604c1c05585020001c0440300072851180ba810a80070f848054100b9403403090907 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 198973363 1250 198972113 198972127
    0x1407061404050d11030906031f050d0b0103060f0507021f061208120a05010506030c221707080601050607060b0402390102180103090c0b040906090509070e010b03130503 74
    0x60100340d4084540e500089628801c0002d5500d004861107250302c0b031303000d100041c0c8451100c103c1c5003803a1488010027266950311800f02d04030344048641901d5280c420750041c428000c250040440d200f48001c010480c618122000948902c441b0ba2010782101c0a03654030800e501c1c0300d4002d00043c1a09802c1040703030100e9803803d242c15500031000c90602d0200d01000a50f9601a031241a04071180607081c2440d60b0b0721002c59a219501c81003654400b1610764040e040341c110740c0c000341c03005000c20b04042e2401e00c0c0d0101e1078924207070f5164420f900d40c1d4000720040c070030745e2100d00654021030350120011690500d400c0015001c0c0c000c40c824090940c070407940d0302141045492041501d40e00307508044401554080c0030728244d1180100480e1880841700204030554400ea0094000314082c1c81382074665512185241103c0d48a68803001c0e02548034502441031100e5403287c6900440f101d0300420445190402da010000014402c48861030004030010b400281d02d008100d12280d880805d69a84440d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 198974613 1250 198973363 198973373
    0x5403160b07060e03030403090302010c06020f0406080703050a0911130f020316081e0f070201090f03090515031605160602040b0d0513052808040e060f010504061407061404 75
    0x4070801c2542d525090001c4000030f00008000c59004942580c1c8a0540c035007560015545a40403038001c58000368200228141c8640200c040d1000e07107140c1d43c03200d1040c180700b03500074185c8034050450b03100740307103081082e20000d43c010340c902440560690700d80100004d0b0454420007001d0a0002401960001080281e185072810641c000c080954451107019203c1c0d040000ac00c0075501d0507003611000b524041802805802d2121381c9c001c9551001050000b1b4030b98440c0400080610b0403400f29400d89000e12451030503034064081001008127442c00d525100040f840c4000d030044c614820f01c000001d21a04003030341e02e008141c1254001805564943c0c0d500040440c079440005042000741c600400b040030310415005825615030000c0003030910301130000b82601c2c4814200a48030710059441400000a103150021308000e09030300c0e501715664a8000140042d5a1500c4000c6040000811083c01399640005c00d10401c50012503081c0e4948000303107004001010304802e280c01c0121640100000c020f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 198975863 1250 198974613 198974617
    0xe07050909030a030509060702060106200a0c1502150402040903030b03120319020703050922060314060c03160806030a0602070501150f0513051504025403160b 70
    0x8070f0325a0b400c100ba07071741d002c90b91610752105a03400d00042e005a0700411105104500314110180d40d0880b005660840c003060368a0310320383e00380848042070340140070840005000c1c0402c0c03c1d000e43c0d00140c400a005290514122a00240020b101d10703918501d5405061180e480003011240203800c540d0b01d44958006552180c00072034008102d010340c10402d080740001802a201c403244d2584071a41410010000c10090880c0c008522240c06c0011241c080343d541c041c02041e00441c0210550a4401080524181080c40051046284240030401d0100024040348140b2500074180303080c40365500d8860000b4103102613540003920300c034008120503061003819401a08440411686c101007155120030615501c6142d1040380ea10020070020060038111a4000b80d80c0412240d00c4186026007031000141260408600341d210ba5a0b02c00c2518074011000030740d011944400726a852111119900320308042e012072100b444010074820030f41c0c1d80b40e2001c104030b040c8802d034048600d50880d207031040000c4c65 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 198977113 1250 198975863 198975877
    0xf0c0303050c0106150509040c111209011d06040506130e0708180633040e0d0f05030f011401050d2901090803030106080603070312050301060923040e0705090903 71
    0x80d51814400083c020305c100d41020484150b91602c07410500c0d560b082000510402c10f000c8144214001c500714000720901504103c840500812034640e10801c0005100b8100720100f00d005c688031011b482403c0d0395600640307003251012100255075000404020200801365400084401d20300002e2210b065004001d6078419030842950300704d040d003406013a564401c0d090707810f0550702d0390b016621035001c0c480d01020084400c5040501760361a20706404501141c0b11400600115001000103407079031944280d5200a043c1145003860843c20842d60301c030002c60341031003807104034a0f505800b42e015034018020354110304115001080412050504c51620003510f0f1b011030702003400c6600308060b42d800703401c494003992a41c0380150700350703828200c007910704c0c00e0b001d043c0a03850b00c108000080042e440500c0c3c81b24241696072a01d899501d40031020341641c645401c56211080c4104200044140014144010131802c035004160000c1c0c80030f48030704003038403a04660f070010042c41c01c01c102404000024415 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 198978363 1250 198977113 198977137
    0x101107060e0f03031611030703020901090c08090f15040606030b04050a0b07030e1b0307080a0503190309020d12030b192102030d14041701240b0f070f0c030305 70
    0x90082c02008060302d9104581501101c614031200c00700c0407803e42d400c2d050400d0f001408890085d44c5039000030b0b21079442680403207011034984a02458040d030000c406c03a00812513030018100301c00c9144200e5103030760718602540307040c102042c001402d01085402c07000080d03400c1040d43c1828106801c0c800d446030710710201580e908a1010214007018801d1003255000200c41019010090b01d0301d680c050942c00d0441d03078a6140c480c036800421f000c0340611000010500c280015a81c0715140001121811a034a400005140c54030040e88096240c00e402c88003140e50040c0410511401418117800806206440d640c21411441c0382080c2103140032840021717142d0b4001902c0750000c104008918a88c03001200940541168503241d404a01495811400c41c00e0400a00c2c00c054852010521051205001c8400b980d140c00709503d110b14141011080042030f43c414036003050402e8404511489a0038001905420010381102070009201d001c01c68594001d030500713103c2e50b5071f0400401a030851400520 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 198979613 1250 198978363 198978379
    0x1030b04170a0f180506091302070209160f0e010503070e0d150c0801090207020609130b040504111206040507051504080106080106030309120b06040f020706050c0310090204050f101107060e 83
    0x1c01c900d1842d400300031660000c28003847d000500b400e201490101c0c1040c000002d0302804124010798914191600c2102ca0664245000f1103040c07000b8010641000e25400b4000b0503030a56603a66806030413a035018040342000107140d100303240403583d02005420042c1200342c5d9034041c40311140180d0071000c3c95904030382d00d810190b43c8a0008904a1040308070085d0720201c10807180c20142050900e0203581544d040c000203001c0c1c20000401c0503500100c0e0225041e00b03215905111500d0481e080c540c02034103520041800345401d82d07a080d0f0303a00180c01424800d02040c4041c120351401c80b01150090b100c140e0003030100540d21940c3c42d010303048601040f80030881c0400041220f05009c4020003400e904840c610307007181c50300000e00005015a1b40a0042b0503002c12042c1c005c9215402124045d45001c50142d6503441d100d00000b800601507005091b609004010401ca195034034403917200000e200f00d500c8408464904010f0340c0c0420041c0644580d801903030b41c0050200d070055050042842e041d11124 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 198980863 1250 198979613 198979637
    0x1020c3705030307020f01090f0b0904060e040507090b0d05010615030605030a0c0b0a11030310061803020d110303040315060906090e19020f06040801020d0b1002030301030b04170a0f 80
    0xd00c10394550003660380552061107410003616103000d00c00b50340c070380c1030400c910002c3c0ca8604805003898250006100804d0000e203910050034680304002c000d00490050a191303041a03030b00c1540f9509184141c0b44243d4450101e40c21559884913030355406030b489002007190640c0c031420607460719410200080400d141c110005070a050100740b24499507480b08000c2011401c19030300f40040d4014501074020001c07980c1e001001d05004200850240d02c410402080007841c004004011014542d4444010070302d042c0204016156203001b800c20a07404914485e1006c00c0e01c01081c0741d4015a4005070142d58031140340500101c4944c003941c00d40b03030511300904c4001d031259103580640d41140c51841956004640380100502e44600581c03000e03100a2102825102480000301d29401541110903a80d600045500703a111040c4511800c2d15170a50f04580780e031041c0301000e502d80c0014400036000301000030004080018184a8901200a0200741c80c3ca0300f04464000303019071a505047c002142c401030314a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 198982113 1250 198980863 198980959
    0x501050a050117070201110a0309050601050114090108040213050f01140102120f0c0705130f1a060a140409060e160905061902011e091703010806040f0201020c 70
    0x50301500c0d0103860f00841c840711080c044034049401490041155a131b28180e0014480110080038101844c5d0342c0441c0480c0d050604508245042e0f00c01d90500a51604d4103a12019040545001e00f0003420502d51a0340d0b0783c00820410210403d901c6c0000707103418100101c0f80c008012090680348140042442002d210005903030361407280f1302c4103c500c20b0a0185c18030144442c00180600c09044040e2080555188085040c4081d4803018250058940f4114003100d25544070b1080c008845110002c040103134240070a80b00c0c810400c0c03010402c07000d8109101c03480c94401c01c580c02440040c02c100f1045665068981c1f0100003580c02c655240c1c503140d0807824040c400c0410303105840b00201800e140808800004895446c030a107220255521500144400e02d81014080300c800c408170004550f42c5c840c0d20b00306806056004d001040810203000500245100040f480d070311a80c0900b0340d140450b520f00050786490101300b0300300d50140c4044018110040c25920507100401e40080c0c881020f04a5050 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 198983363 1250 198982113 198982129
    0x6010e011a090d050c04141503150a02090a03050a03090e0a02030702121623190c090b0d080a1e0c0201271205030a020c092401050f12040501050105 65
    0x150107590818003491090745000300c483d181003403081c0102e502c0e50320307400082402c1c1c9582010b08091014808100881c4c2e201202d0540d040302012009088021040400520b0703100001d04400d658039030201c2e051078544c56554101010315008000c40b44100c043d03190082c411070b454011600090750031800f143c0614514000d0340c1c002c244039005486401c081d0030440b651500002080c00401200da50310701d0202c2d0001d500c0d03103480710303a410403940c03901055044617160008041500605403101600c44000c52804070084083d110002c0c0d01080f03503821000021418103500740d01500d50207001a201d82d6690f004101050740d01c01803c43d0400d1305d8000c0c0000c3e0f603c0e584460340a400728a28418604007404044002c2584c003080b91020905562240500003010004050444042d03000092481155070100444016404101d0f0400c03230501d005d0078400c1d2520005030341c88220070410380e51003600781e000d10103907050640059251034031528001003080c01c0d20030560b0140c2c1d43c0d520308000482d850500d03602c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 198984613 1250 198983363 198983399
    0xb0c071d04020405060303160b01080607020d09060c15020a03020310081f02090613030308190b0619020c10090302090f070203091c0506040609031205070905040c0212030906010e01 79
    0x1560000c03aa1560244405054000c2c0500d40c14042085594042c1d0a409034903001180104e05401e2a9810f01c0031251400030b01421131019503010001c200b441e154000c030000c1c00d03540c16240c0035112502500e007440c1c7e034406400c01d54211a001261481509506501941c411141c9039250310740d0f590f450380320984030b4069640103415000d00717424900c84610300b60001d011410b4054640d500c0c108860344540c01d035050a03042200002c60742002d0007240c49020300d60340741d4003d42c5002008076030031400020b0352034418001c00030aa00e104540c1040c0d00c0e402449000c03000740c406400d5203043d85100e200140a01028001240315105c110302007a1003400000915105600c00e80095241c166840104070003010041c200080700342056040c1c00004900f407120a000d2072150801084100152901602204d0022100d5003213910782400c102c00d65620220160031143c083c1c6000521704c072041003ca0a2842611502601a20000c2842801c034000107216048452007034805217180d88031080603050800c903c1c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 198985863 1250 198984613 198984659
    0x71d0d0506070f0c06051005030f03130311030f010e1e06010e04060207050708010c030504031704030807050c100203010b09030c012610080a0501050405060105010905010203220f0b0c07 81
    0x30001070503050050a039203144510134181900340342040e540d41d8050707070003c840600200c2d0401c802005130b4201006401414070092000c0d606110310041110b500a055103c043d00a001c0c0c2d001c2e143c400d440a10111600000c1c440003407100d125140d010603074503004ea1001d990300b40381c44c01c4003461910780424074a05955545844c100152203a41b00ca4000e900503241c2918540590180003032034070801d22885045102c643c0340800d4520f45802c01800c505a00d501d000d06100100342080300007580014225401519410144d03110b803012502030340303040c6001c0c0881e0305503031000002046150001010b40b040750f0f81102110100c6044000440c1c075544280c0110240d158000d040043d044c03800325070940d1040341e10a010840c01d0340d90502528010b001402034540c0d95603502030209200040c40f0050140c017081c205a402c01d8a080300003503503032180d801032a42ca1607a00b848001c0c00790900c0b91020040c00b00301031800005440b245421625400760040c204680f24488001074205840d0564041900390b903 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 198987113 1250 198985863 198985873
    0x1206060906041103130311250510050304141c120c031107030f0c06020f130609061715190e010806100308030a0603060f02070303050105031c0f0512071d0d05 69
    0x142d00c85d030248007144104405022200400382d181080c2001904c0e1600700712409101c1c8030308441c840340911140387c1c2100e0301542442d410800c1d02c50700141101c1d003180d4484402510700700e4201c4082e090414107440200014101203071440c2013039200c00740b2201207402d10700800c11040c0f124819021100281041203840006100d050003081c0503012110201c521030405040800c20796881c0400c90f40060744409640c6070210300c8640102d41181280d000d012142000203c140c2440c00240100440d14440c150090903140020541c0c904443d6903244e10101408101d911150740320390b0b0803695202d024011009210b10000554401c0009805000b4268460701c81c0c0e40c203040d074840642c80c0c1c0c4000c00d2000d440e500c504000000590605c52082580399642d070058882c41217140041c180d80041e4400303840b80d440043c1b40d45181c143ca14400c00f0785c21050400c0c00e40d500c00110103686500481009040a80d00003007009840390304155444524002c94080c3d1000c0b427445810080ca40710410b001805035444 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 198988363 1250 198987113 198987121
    0x6040c08010b030c04080d0816080601081b0c03031e09060c0702130b0a0b0a0905180a051905130611131a0405040e030c0d111b010e1206060906041103 66
    0x9020700440e04901c60345904c41ca0681c4a1803ea854150096017007000982c1c4002082000100658460801a00d03441c00c00300505184000821542015040f4840080918203221000514100325840545000c050301e48a2a2000b101c058180c4401005200f03585804000f03640d058001c194144210891503000d07080c01c90700c0d02408411910b0240900d08240e903118002a1542c1e8111a1002410b680018560360b2190110060146150303a206a0181021020b020903012900c3e030b815600001050b000140c90b914600c0340d0480102200075846114902418064212001003041824602941d420700c41c4a640500c034079420320822501c0c581e07144003220148840c040501888100c82e1020304034906054817980040e088170140a0182850707070000500c1c14480d2014031070aa82d11016007070540910105084842d01d4013a174589102c2c030480c45e0403049800303170b0041e14841c0c7c400e04050b048003444510745510ba55075010588900b032091080c2c00000d19180303414010f002040343e0030036105046880b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 198989613 1250 198988363 198988379
    0x117070303030b180f04140d140c030708070309031106090603060d1412031006030c0c06020a020a15090201120203090a140703080307120c17011e0801020406110606040c0801 76
    0x50314010203070380300c00c0d030000d4a03c4d01c2d540c0884290069541c8090131035141014946020002605c144041e115013044004020362600441501200d080b030309056956048030303c07255030842c400d503800144041c50204505050691001c07114050b2031050700c4400071940f081c000c00299014510a0f107a122004100040e1241041c0500484540c4940070801c1800c00c20000142003901014100d4124003012040011542d145046040201241d040c01c002880541d20002e00c40c000c01400640340c913400003000d504092007000391100c055004030710441107003001c00c40e82c0e0203884c000c1001d030300107a001c41c401c0c403211605200312402250301380000d0400c1030300355656007003500f01d60601c000140501100040420791640c021031045801d0380e0f8000740f07545983c1e140301c210f8120a03854400c0040e03d08070b07603400342030001146045d1008222101d81040520607400e5a80240307801580075035001103000100d1907000b5004d40d800c0c074207800c2650744c00d540b0300050004031900501d540002614550040040c00703 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 198990863 1250 198989613 198989621
    0x1e050105040e1302040e010203092a010807230406050a0e0306071e05040302130b011103040308121305010c0203040f051f030509030f0c061803030411090604022b05011707030303 78
    0x10310103030020482c0c9501b80c403000e00b243c008980d010b8281d00f020310040d0b103503290f4500d05504840e084d004401c030403031a000000c01d8070100610080c1881340080b034a40c074100a540c006100d1074000312100303560720f46469000f81130b0303002036000e81d0100303002c0111440145004a0124490241642c0d0700c90340c1800d41005441c0e4270308030705101c000d1200030000880582c452515000100020700c80c0030402d00c2606000400040302d203440814150020f1000f4000514000101d5074506161811156544c980002c00301c3c0e203010700b400040c80b942c40d02604101c01500400a030045605c20300e001285299a0800c0c00b42c2250702115105074441041c0c0894801c0c1e01a51142e900106102d080ba41001d40c1203c00f540160300500c0144566405141004540301416000c402c60301c062501a505505150350741003407880c1c8140c107243c420301d03440d0000703821521070340c0c15a109001440021850b04100b203805501030004820700301c1c1224240400410803d00a007640d00c164940342d0f0040108a00c0c58030200c1c010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 198992113 1250 198990863 198990901
    0x50a080739061a0a05090108060c0901091511010605150405090c070206070506240117041103150907050d0308011503060909050c030d083603041e050105040e 69
    0x34500345114030040342952181c0c2e02400d41490803508404034510410401184e541d000d14820000c010040c440040003051158100c0d69400f0f0311901d80c180c800040e61041c2d600c1d00120f1b03405540c0001807503942c0e0301812000002131440d000300486602c810600c00c4400c0482017181101b1802c100070000c0e0b041210000b40e1001d03a0700c0e0035504080c220350000b6100d6020307042c2640d2580c03000b8140001e4803c003017031100e0390809040d15408041a01800230300745800500036034011180350301c0003c05000200314202c00c85034008043d156403c504440d240701a1405840121052040020103c0c06061503001c0400301c58050b143c800c1c2983c07819150500d008404480c400030144c072407000090b00007181c0207404006200c1c1303014190425503c0b003032500d44280c0c98006400c00c0034078030030700050292403141901c02041409055181d109840d030168100d03c07a0200880c994440054000b6641202e507001740500f800290842a100c0e40d5640119010301a0380a094180c1c200c220116030107032900541d0b042c0c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 198993363 1250 198992113 198992207
    0x708090a06050a0e0a060918110c010204030c080303250c150605090604050114060c010e070f05010210050405030430050705010e040e0606121507050a0807 68
    0x900008040030580d145900d074403001c04103201007072001801c0d802180e030520a09080d01ca0040c26440c000005201e6141441403030b03541c0c0194120f404141c80036402030380c3c4440c403800b0348607500c2e96050071040c001e500501c001d52303010403d64000310701d035032020089030300508203004850001603090f00b80c964148030342c064036004e001040001c2d41c0001c0240380e6501c044802c244000803c10710344014000090341c010308480c412441c080041c0061102802101054041501c40544036070291b94124014505105502d1203841400c100107a007a0302c03003030b6540075944c0030b03402d840b58070041500311010390b041501c009246410602051054510b46540e844201a244c00e580366030400c8a1a07000c20b440d4018825603c0780c10065060000b560000e007040714242054600f003000900c0c0811054172584058501441002c4c00200d601d41d4540030000a4031092543c4458609800d00d00d4015110780c2c00ba050310b201283c2c1c482c00181f0b400740210059446403114000d046014441138420100c2d181c010030007565 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 198994613 1250 198993363 198993367
    0xb0a05222405040b0306220c0602100e0105130305030a150b070c0503030f071209051314070e090a0902151803240411010221040503010e01020c100f1e0902040506040506150708 77
    0x1c2511200007038020301c112b40160848a1809a140c03085d03600000c510203041c1e041c4030034014400d203d81d03c0400e04a815142a6031645c42c0c40368058080c0048502c0c244850702e0106c004941842c50f0030050144920441203850f1483ea5402490703120b0103804a440c40c000f0003488100b0100e0f46030050178602d2201403800f103816a8a48000580007240304124020f8560703102c59a0358100d54504266400c20611304014850030340d8032000074101000200000d07482901e404503c1d0031512040c820110105170010a10307250044400e010640c0344001012511038840c8002c400c113211121020074240c1200010917003800d0b552a100c88d0450010b255a80f8114403030070241c2000b40c0d0300905011642d04a01840c0c2d40d0751460241010f094424404060b00c01d64810489544251000212949440240d81010400403e44d00806004000f01e01807640da1104030070940c51452855405505010b10841342000310351240d000740800caa108445880d0400d0032944908a40c10030007018241c41403080316614 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 198995863 1250 198994613 198994681
    0x60c0403061e090602070221210c121306080f0103030c1104051509010b040602030a0c030504030c06050a08090a0209180a0c03080306010908010b0a05222405040b0306 73
    0x20b044500c2100141c2e051903011508a0840c45d05c080748000341c002c4800c8540983e100c0d903001540392902c11080000340710901d44070440400e000f2080da88880c8281c81925020407800092110303c2d4045e1204512038a01c984011030824000c1c410726004800c140c040f41c00c1e47c2e0035039030280c43c02e0440c084c06039440459207440403c0d035601c500039640f140391100803a0315850350351000c0c003d8150047e0010321522900340003c0c004194000180d646a00491411100310455401d0a85152259030005401064042408145c0340c0e08840101500920b565910459545041c0d44d60b0f16282d0801009512619800c08103186c0c07580307048030b448807000140030354012550ba551600f100081d00d030300440d150306010041003000c2d03070000000070003404e90400031300130000302e000050484891400342c18411213070140301c0c0d86182c41000202c41e54a200c02410420580d50310b904d8440151510380103049150b43d0315011495003010b0184624042028000b482c103600c0e240c109904040d240c0c0103580000e0080380c616 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 198997113 1250 198995863 198995921
    0xf1a0406050d2405040c0509030a1e080a0503060a05060703090312050f040e0406050c0703090e190f27020109090506030118110406061103030403081906090b12060c040306 75
    0x36076180a070b44060051003450002400300381e502446e03502050102c288501d0510781c5001c20441e10059102413044000d541c030011031005503070000000340c075405010070902c1901d50000e0085000e803400310340c10322665550760100b00c51441200402000146c0809080000032280c1070043c13110403450501900341000100c026456420960003400306994803401d02060100c51702c102c42d04090840d94151510000340c801800301c0b207407407180714080308007a00000c0403001c0c62112000e20712048031042c424402031000c0e204c050010751003601e2084160980c914280141011032550084d8180c4801c6071840c03402001d40700a0200a1015030595203a018404450300484d0400030100d200341100030411500e4802c0c0f004070703509500900280020017051148011000081d683d0195040c074120455547e114030460700758aa210342400e41500385000030400c404030380c006820050058030002920400007400c65a2075000b9111210101010001403001c03a14130b41052030b110803580a03440c072444401042c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 198998363 1250 198997113 198997151
    0x9030a0b040c17030301060804170c0a0b2a03040c122003030a0503040206070201020c03060c0408010f0515011b020d0303060306051e06190e0703060f1a0406050d 71
    0x125451540d65007000200319a201024001d003003441491001e000340206000d070780c0d10060040900b0720031150002401c001070100350f1403082030f64070351051722080080021036880609010888404203550001480d0700e404040300504450230b68200c0b10481c401010407031680d840588103a408010034003002c034405c46503241d800c040c1442401c2d02018895040c2041102904a0b03107640c0c4250010050761220642c803a05981c0c2061b01111016664889480141d1814807000d030b2180d058081d810401c01d08200303100181044954420003404212041c003c4c210480c2c0e01100d80602d80c080d0441901c0700f65101ea032805000042c092141101100380d500010302901c08240100c0000c2c0e02c4600500030400140125500a151045408080c841085002020f54002007140c0d00030300b290740c3d14000703150404030001d004003994191046281000d00c0020041c0c0200d0286a10b60054000d000a0005020304110a1246000001801c1c2410050201c5450348043c01880181e5101d0014008502010301 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 198999613 1250 198998363 198998383
    0xc0e030d020606030f03043f12020d09240903150b1806010e060904110705061f030b01030b0a061806080d0c020d231002130b0304020102031e0903 64
    0xa01c2e040c0381140425280c101d1026018846401c24081007200d5001c000b05200c200a0303280542001d04018440311030740004110307921101c2d81010702e46605100c0c512100301441e280b182e007030712080038800b40c090752051801c3c49026a42c1010754a450555802909603203801800c81c0303040400940d9070b4541d8240001c1c80a070701246541da50324012480d282414444954605085001c0c201d4504900068003185296000c24095240000d10188a66030390b8000c003000a200b040480c1c0320303080d03401e265680d002d044a101540040300986865214140688001169440841e8001d1760b801d42d0354400c2c441c100940b01c540b07203d84420300441e18150350300d4a01c8002004000c0000c1030791904811518200c0a0300c850400e109440c504003000d031712030170070f14030405402082c80322180c0384050700e8141c007040c031064440c00b40c003c91206100514040d0001c00302c0c012000105c0c0100d64544901c40b11130f20040c0c2e07009015a004200c010f0340e40340b0722240042d4149401c16101e00340a4000080780c20124501 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 199000863 1250 198999613 198999617
    0x2040e0c0c01090503210106080915041e030206041109060a1e030606061101050a0219051b0123070e010f030504050a081b1203010f03031809060906080f0f070501030c0e030d 76
    0x2c6e8608076100346046045c0144400e1415900b41c1c02d0046115440d00d00030b01c0d40300c8070000b0307410005050105145401e600c80c2c8004440e24104019800c00948614058400300d0b01c4a501c12001601483d0480901c2c1c040c020041c1100e113201d103030681407900c0d81d0310805041c0310b04c5100301d8004080758080c818580100032546074840c4000c2c2e81c4c0003003030854000400079401c5a10500c604941c00540c942916464035403800e00c6070307603400c00481010f0500c07080500d0b80420340c2090100f2032000b646002200912189100a18281e11282e10580c3d5500c0d00c5245140020f010b10852070400d4425082250094011800d642d4031814645551030b1175400451171050381c2d4504181c0a04a15041090440300c126008203281994180f038491041b9002c03030b2001408001662230a02401590f0555100042540200c100403250340c40b44202c01410b250f10519049000302a61136041003404104481e400350000b016011140c10400150014100c0641c09001c02440204442c0d4689040011203110078181d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 199002113 1250 199000863 199000897
    0x2003010b1b1b04050f012907060501080a02120105010b160602070506011e060806030a260301140108070201090b18010207170d0e0a081911100501060207060302040e0c0c01090503 78
    0x300050000f502c0028000460308286040104007025900024004180c0c151f200d4812100d0240c00e00d88890140c00c0b405040c140c074100c00090807040005400e81424800d682d181c0c01310381c442d9442c6013210800d01c510403085030700300011020416106010f00e81c0350b100d098014200865916814a400026041440c2d0700c0466194800500d000304000401400b061812140c5498071002007911840c81040050141005465800c0c220238500d2050403404490302800da265070b9104441e80c04108031003480d5020440d100c000c546000e206000d07941045d0380100c0700300066100c100420344049103000b031a482c0795500f84900710004204084085400810701411500e07541c0d01c0c80f4080445e01d44441440751a40601103a030005400340c0c040e03403008603070454080c0080501401c1518240c1303404d08440890b024490700c2c0d0a100ca456400541601d6580c1c1c00c8414558a90005908030300c0313640114102030841c5000288a03d04003002005a48a235200102c2c403110159540c901c1e503000a0f075142100c07468 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 199003363 1250 199002113 199002163
    0x80d0b090109061a0c0309030d0f03050703021215030705040c050304050f0307051e01060e01060215010f0602101112010e0f0a0b01080412110706122003010b1b 70
    0x140032409484905000c005241c5421400c107001c85039000c468000b01804a1104110743c018402e94805d03040184c182c0c1e0503800c98240007018060140095400b192420f40070403900c0c0e01c030b4400d4440c4502210703860881901d489501c45180200000a0350342361081120218543e100c07400307103001070352007500c0e895100c0c203146c5002ca050080100d02c0c016a54001d120745004568002203016200c94601c031018007001d03514200e9400740100ba0007007000858808000203480e64005460b041d428090040d01c412039880b401c0a0050101030322443d001603001d059070100c100c0480c4d114064101e84003843c10324100150905500c00c081c00d91105800d030100d4401c01075604010600280d01500340101000103508007000a0500000138001a0400d2075040490407041e000301054885000c412007150b0412fa91048018036011000407600410b508144001c0181c034110400100e4504540380d40c0c901316030800040b150150013100095101c86c40c1d003481401000410f02034000000e0f1044410800c0c2d0720 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 199004613 1250 199003363 199003369
    0xe1207020f0d020303070807151b1106070207090c050c0712020109090c0c1202030d1506091a0a0302090a0b0c01050105100503060d0611071a04020102060108120a0813080d0b 76
    0x408a001c180c0118400420400140e9020040f41c4545078001d813403540b250390700d04020b5180350b150341600084034600318400c58804203654140d1071001c1141d96060364074118100c5207485400546400d0003580c08100144001c40710750700508000720644c90040c0c24441e2040e9910316040559110220342d00c0001110000e5582c0240d804000e042c1e010802d000540c0340c0b1800403c51310802c4009014002c12051b004402d0780709008684801b010100144070115040400c7c3d800c00c10141710311004079450540024a540d05d9022403215010398000c40c07400c00c448120282c4c041d5001781c00042d803101e1034640100e05005550050691b0028000001a956041c1000e000b246c0718041c45000a000e024000c0048a42d1003602c10700b02c0d10b600c01408100341000483c0000b2502581d01c00910002c42c0401c41c0c03080d11652102107200718000d0b8200c0300d0310390b618070000f91201c4180350b540290401c104020300401e40904440b42d08010140002c0b055140280c603484460b4001950480c0880e803214280d000e280703 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 199005863 1250 199004613 199004629
    0x1c0c0b09040c020706020307030c03090b0d0f06050406062c1815223c0b300c0d0501050a0e010c090303030b040b0402031603051e06010c02040e120702 66
    0x2d074860005144003030805001030f5803400340384001000c1013242d9600c4401c041c41006804001d00384006410b844203621350310710010b810841038410401e40b6100d00000d442c03400d4010a011a00551240e88072005e101c840d03501300e0040d0203031544d24000c3c4c410356042d694441c07070b00d081c40d07050318054500d51318100307904c1a00020042d240110712902e0320385c43c51040b0440300c2c00451400350340c002c000548010390910f140e04045107003800e010080058143c056a402403543c2002034021500390411200107c1e100300503500062144038040b1076440075642c0803c0680c00138103848054102c0441d581070290400140c5d0903144c3d08400c80e0b05075107480a2181c1104207000702c00b0604005802800113155404009091005501c4050201520340000d508da9444590001c544483c0c040c1c030035940ca2504071303600c0c01c1816082c0154000a031600d000030f101000492084050b010900002e181c081d11003000456a642011070305aa010380c1e20714442c03102d05d4013002800c1c7d10b01e2505020721f07142c12090040100740 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 199007113 1250 199005863 199005881
    0x2070f2906040605010906030207030e030f0312010b1204171c02070b060f010f1413060e010f03020712031d0a06150801090b16021f381c0c0b0904 64
    0x1450503e8000e020582e00500004140c40740340c0740050b113410b0b19080485d0740c909102425605401011164954030001000609001d00c1e10325114890380d0b40d5151030825031191410741c100d4441d1600204001503c01b5074283c040d00004c0200c0c0d801c1c0324144503001141101e0740c1508800603070002e607100c03c00c0600c404e200c2e4002403c4400c800301604031000038003240c0700c0b104a402005941c1010058403010842900c00350140841812141600e80304040d0000780c004503020f0100756544d50303c1407924403d0003243d0001d64024608811201c1108007603010b07195050310340021240030058001802410030800040078018480840c3c1c40c00c004c6a071640301c80094210322034590404680c00e002c034481e04990b5810404c01c40f080c0000710204107040381025034000608084031103420303003c510b503007280d00403140c0200c0040c0308583c0a0100810b42404581c0b520520175161a2132260403040d01c1c2004031121304100e107003514405d1615650350f003600d40126400c50141000d020400600c6410325105003010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 199008363 1250 199007113 199007119
    0x102010212041203230405010522110a03061a0108150108150a080a03030507030b0d03021504021f0504031a0108070b0705010609050a02091e011202070f2906 69
    0x280005110018218400042c40a8458901a0f50703a440c602d200394407a0001130b18041405002450141c1e582d8400314040e1000d55140d82428042003050b103c2800740303400c942c145050000466480d6a4070141d000d542c0303101c00c1d072107110f084000011880c02d006080c046500d50840351481c003032080000d0072444c00070b030174169440d42011002005907002910a500724003206060655070100c0c100045901d40c00d80c00a800078010104160101a0960442030107950f580c0c80034001c4004903000d01951f903450080190050344042290740a011a00040380c0c1c20500180c40c0c40c0c95420800c81a80c0306c130241c0a100000188009010424080e8504085d20b0a2541030042443c41d458005115aa803106010358140d40d0701c005448000c1200035403040c0b00030300c64010180020314041071300b40c0094000c3c044c41c900912034400c1001c1000e0740341d40c40c1503940380140c40303a803409400c00307086500035004003504880d003903460200c21010411a4611031060054061941440e6030f8881c0340e0540ca840203894680 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 199009613 1250 199008363 199008367
    0x120606060504120b06030703121e02030304080f0a0309021f0314060d081b07091a0415170a060e0619020906030711030d11031008030309060a0903140d02030f0601020102 74
    0x20848005039510400300343c0001c000c41540d10342c40c0001e0700b0204e02d030b0300040c99802e404410a41e003940101111500c03a041c100c3d440f400d2b203406c1c0c10507078580c4004c0720001c00040c81007240c0900440d1000c0981912509031800107100502940407030742069104102c2d040782d0019551641005600d0301800d1120321036403482149034100a0702007a400d10500c480284002c0001c554840101c031902c02c0c41c50348030002402c407060310356280300300c60042c1500055000040c201c2488481a41001e0141d440c04a010205100d2024a4044068004e5541581c0140035000b041c11140100d0040c1c0110f080300070002001d80b800c1e0400c3e0040c0c51a400141104458040c01442111525581c10050342e500450301c2c00c1c060101920000014150302ca000c1069103542d240440c001d281c09408009188141c1c58100c02c01a40c9443c0c80350690780e13000440b000e0b4440d40c0301200141800c02d294000c1040d061080c24580500891049500b12580102140e0030540d0303070210800c201d000c040740c09213410807401c3c00214 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 199010863 1250 199009613 199009619
    0x5030c030c09060303311e030b18010e2d030306010f1b05060a360c0b03071206090c2304150509120d0203070b04150501120606060504 59
    0x280c8603000700c000140301d00042070000e285a00c0500445501141c803050201e500040950400c4800000825100b41e00031600e40110308400741100d90107a403a0702501e10404a49075a485a00c2084000c05000d142d403262110542d10420034081d1482c00300800000d0b00c40068200ca11404aa8401100c40c0d00050034406140e950400442140c0e0004401e103807a60100345419010784070078010407180c212131540e11b1600c8040c001d0204070940a4403c180e0144101d40d01641c2009034800b9080e4802100d80d000c103100009024451042c00107a80300314882210b159a4401c80350264204590308000b00e048000c10b00c8582c1d2032441602d000e420f08000070441e007200300c0c10040c0044026680c00001032480352000002d88143c000b92002440b500c481e030b65407142c82c4200103003c0d82088034824018400c400003c91022004215802000c04540c001d42c2442c6c05600c1c0c555101801030004e49120714401c03043c2060070441d000e518060903403041d428007040400e00d80b1104841041c0d114008100d070500041c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 199012113 1250 199010863 199010869
    0x6061706060d1b0b0c0102071a0115031e090b040b01050414160c02060a0504050103050a0c050a05180d0b180d0f030b030c0a1205151303050703030b03101505030c 71
    0xc20355640d040301460f0b89030598079a51000e83c40e2190807a0710f1024000c20b0540c0501015002800e0302882814825800c034046203442c086500c003070003803000c114015140c0e8140c5501c80d5100e008041540800d11007855140039403201110450403003a0b038040302e08000c20045c00b44d0040c00c0c5004040c2503c0030407203541150500b03803c0c1e640107000d42880d104401c40901d2868410030181c2c1c03019400034007a40c2c0c0c03251054005448c4c2e510034410203000c070382000e001400c400407510402c10803401d1621140d246c20ba8885080300d160f0b01030991038081c0c2d0b11002c0343c200e040c0c41d40380302d0350322130380c401c0000c1d180343d041c100c0402a00301060703e070b0000c80c3d500c078441e60b80c610b640c000d84440c0c1121a900300442d181086a00003070a03c04000051034000a00120003c0c94607003901e03002034064011015101030b00d03041801529400000c903100c0000d000701414001c0028422401040410f000c2c0c036001942c181c03080300083c1840645102c3e0364105449000c4000b03c40f080c425840e0080100f1401040e580060f1404 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 199013363 1250 199012113 199012129
    0xf0b1c0b06040c1e030e010b060702030a030c02010903050703050d270e070c08031323060c09060c010515130c08060603101203050c010c050313110609030a0606170606 73
    0x411401543c48400c15a4102d005121551040366100e2000c403240c01c0341c0d84020010081c14881030415030900c05100b1803410706404449500b900a000380070000d500d40c0b4103640f5119801c17412410403a01400c000041803007442035401451140e00505920007014900501c441c0101c0b0031a0a01e02079101c0306604040054541c400f1211500440b40c2c0359070b40c1403401c4e207002c0c00345100600300c10300000030000200c01d1641d800b00010300c19411907800900442c8594682000c2d00c040b450994080d9000c500b08052070009401038981c01800c0e20302c1c1540c000c0015082d0351080c8d9211900c02c05c00701d07075480a072415170503400021042e18410040c240e90500c00800c1d000000d0640c078040c17100000482c0b4103c0c140c00c1901c0c0900a0550313010141d00940c6402051503211410310102c5520b482001240c0910600490b8081c01c840000c094803501151603448101149070f5005034030507010411380d030843d1024082c45459500410001444a14162001d50030144000d05208250815000c024640e520140 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 199014613 1250 199013363 199013371
    0x1002070203010b0406120210030e03180901170607050d020712020604020414060604060810031406010e01060206011a0a0e0a092309060408070507180204080c0a03020120030403060f0b1c0b 82
    0x980740030611b030700401603000f018ad100d42d0352241d02000070009410105182140c040700c4003602c3d0841582e0761581140940804108100c056410080204011b10300c03030409800031400d00d100061610141d582c907410740641c003c0f42d81c401b503040a0200025440d0610803140314100881c26600c0750f01c0e15400150140c8102d01484090080d00e00202d4808501001001c000c1c540c02140387c502c021100016694400003441641042c500030b9002241039480800c640b0b040b9402454004659410341c880c0700110703004140300008100f0070752004007040d0ba60001d40401410801c600081c85000c0d0425480ca040e140311607910400d4800003440b14884c40000d03441d500a400a140c130fa00c03140c1070301d0446c0c28000154808050071403042000d441c01d1003254001e104131000c41c800c682405072500d06225040c14a880003a0105035070014546c0400900f0f04c505032800203038025645003a4682c0e8540c0101c131ba03411320303654020360b68140d0040035040c81c0100c082580c4144119a0346410f070740e41c030b100704214020 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 199015863 1250 199014613 199014619
    0x5040b241905190b0f0d0b040603060b1002030c071202190608010f0e0405070509100b12070f0c021012020c010e0d090816031211150402101b060506060c1002070203010b04061202 78
    0x44901e02c0e960107130302c1400d4404c0010009d001c42507907414040050001031443c144030f10282905c42c8081400003041710034080d03a000280c00e07464a00b080440000060132002d0b41c111030204003030411040506007071750181001d61070f003090550405070380c060142c5903508110700c051030000a000100d0000111401154412141d41641c0e030f68010241e2803c030302c681d01191543c1c42c0462590454212403800520414465403078019100300518111403880362084081c2d003003030318403010040c07640c80340ba400304000c04041405494902405005421903000071140c045681040385202400b80d0311000c0740c0d00414400d0002e01554003100d6100f00d031150f4501c4001c1130307c024034285000c1180510f2501003c1e401c090252006520b1942a048541c541110100e05ca01d880e5040c0001e42400303101c5a0004031501c4a4901030315246907118002040090304081d03200e801403042c0c3e45070050800c080301e0740a1038044050303185c0042d841411b007500c1e010900a4400d504103501031040380700a1a0b11140b00b41c040b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 199017113 1250 199015863 199015867
    0x11e050907020115090c0e0f0f210d0203070203070614030a0207060912080906010b030c12100305030403051f0209011704060f1a1305040b241905190b0f 67
    0x80c416801400005a5210540d07104d410004091405502181c1c1e00c107007a0315000035802d1001c040090003c1d5501340c0940c4200c0100d40540c65040c00c0682401c00002002120503100c90342c405c41c1c0c030b014000051000103910004001085080900003103000786403d04201c0f4225020501c41011400000d111408030b0313502084400a03c103c40d00441500c0380c00c0950454a03500744d00004055000490fa1041c2d9071160b0000003412080c20011a0304c00c02660404c2c03420300c45034042d80c00056101400742c0303804110170701001c00460020f000800c001d601c110000d140d07182d102c035911500b1500c0322000b0f2002c0c52060000c2400c031b981062500260081d441181c4c8403e42e034904c0c00c40c004088151100305540d00d0b0000da006080001e9801d004000421074511103041040c041100075110111030082c9000c0303000d00403440826824038a074006140e101c1819280207140b6010401e581d4801020b111a40075940c2c00300507a040c0950900148080c24001e104658240b4403110b645110b00e004002e108000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 199018363 1250 199017113 199017121
    0xd021201111206010e0102060114190b030901020c0d0903050a02090406180309050a050306101a0d1503060b0904030207060e0316090606020c0604030b010b1806160b011e0509 76
    0xa5001104120001c0007140d1a15140380c0c034281100b00c2100c00c3ca010407020030943c01c40d903000280c090304803251151072000b625085000d100307022409407010f00c40a043c15101003400000400a540b2a00c0380200041e150b98007085098034101540341d43d2818491503e5080c004a840480c03070204140e01034601000544662402c6402004c0362210340c0aa2903121300c0ca00304169104c68290104d840407501903c130389441e03004060310382406494040da001c0740c4031020030140c004003400d0642034140c00c2c106402c0021034001e00040e2440c0d1000c142c40303c0d4003440284100030080c401e4200d000c000351901ca51a02e4991f5000c3d50741c2044c1d024203070500070041d1a600325940c0c10481e11500c0c0700100d040780b4850390798450b190050300141c007070000513000710b801c520b420b81400c0044d00c04494001840c040e0340d9192052110351980071175800b00c0b1b0880450710700b81003603c0f540300401103800045030881d1140b4a40c14648240901a041104180207041e05d41c00181d480255980c00e45004445c80e28140d00c0d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 199019613 1250 199018363 199018399
    0x301090c0e030f0604171c0914150a0513030e280b030a06050121150317070308090105160e06041a0a02011505010503040303050a0902131e09020d02 65
    0x4429110150716218480078001201d9000c84c41500503485405c00c010341c41448a2000303014050406000f0f811001c4004c0881405100d421408a69004841c060040908002500c0c1070415a07a9002c0380a0070540c04d011003200c0b207101c0c941c1d000b45141383c80c070009190743e82c3c0204600c2a180100d07100341c040a0441004205100700d0400349580c1d0010542e40d50b6490a20403142d0304111040086985001000150b650041c0c04800c0d40c0c00484081144145039290390340001d01800703042c410f6401100c84040000b030610050311400c014006d94007511060145001009000c0051480d902c60f4104420300464000001248003400f0355800c000c211022400c1c00704400e8015944a41c0e41e07000c5203020617000c00d100b00020034860805a0003030040e1612180ca43da600509480f84900044003000084e01281c482c1d84007a0700326411080c0419004200e0700001c415241d00714082c0000c1e607031110350801060032800345d140c40c508100014801c643c1a9000207a10a15840c0040d005007244a000103000c8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 199020863 1250 199019613 199019627
    0x9060105031e071101050a1505100512180f160506070501090203030d020405100804031d13090b06130e03040b160f050105060909160504020d060b04080c04061502030301090c 76
    0x100b207400e0078a602e1070f010000504d04800005a851607510b440c010078500c4001d801a2181d414240b04003208040ca010103003c1194180d030342072410040d051100001c04030151909a001c0c40c52141c0c101141704130624880e0600758004640003c513400741c030502000c8241c0c0701d201c8080352802c8503043e4450311039040990141144d510000d40c18000028140700540c202d5016006445042c1d034081100c14040e0f0082c1d441c0f0700151001b40100d4524542501c100d0060160010030000150034203003908420b0360903209540d8034038821240521440d0402005042c180d20484501b03049100030b10942708054107860b200c0c40745009000e00b074900003030a40100f100c030a46a04c0d080da40300c130582c00602e4141c01c02900030b100a4403a640308800c1080800c3c40464005109151814504c1001d400503150100300002544070f07440300d2404584031980007409904903406840100100c401405040586500300f108950a44c2c205030500202c2d812400140f66000040d68107445080703600040131b0140304800d503891 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 199022113 1250 199020863 199020901
    0x30c0c08160c060f050919120b0703112b0204050a080705090c1c240f1a070b0a02030c07080403060c02010b0307080d0e060d05070906110304050906010503 68
    0xe040014a405401081030290a0201d0003040c462800c140c6814044440c1071145850100099040c4240c4a030f504d008084112140055811407145560300e1009035280244030710160b1301d0318031040409c19659054082c4030314410007003041030f00d40f860001071082a106409114444415285441d80c0140c8041e41110040c04005055149031580e650500c3c1d074600240c015207018608401c0803d1000700c0f20b2003038a2001c0c21410f0781c46444400414454010828040700e661000301801c401305010000380f18040c040c0c007481c0480b00c00c19060102011804150f1001c4e20346010007040844003096102c10710941100c0b130b642d0f0169481c0c4410201d01e8441c0a0048060503ca500040010400c0f4040d4010800600c2c6500280040300c1d1081c20161140759911600d84240c0207169160f0503584541a000d4102e180106050704101c560700c2c6c030a00301c8904072000e4002c83c40c107503014800384c2d0700000443e2240040707900a40c9014201004550071440c060509d605012000c0003195001e8049047c403030321 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 199023363 1250 199022113 199022123
    0x615060706050a0e06010f180c0e060304152c030a17070e0a09020415180603090602120a0603050f03030403051e0d0c0305011a0c03031807030b040503041502061303030c0c 75
    0xe507194503030300c920090300b48240722081400880914803000140275403c00032149841e10301510f6900d800f445980d5000410484602c0340074150048901c901e445242151103000d0b40c080d2031440099824196a0416100346100d54414081080780030340c403042036801400e040d12007050070b0301e4003501035400310104100340358480400c0070301040001042d40078004403000402d02c03440242188100f0794002010780c5640781030903509802405000d01a41058507245e10031803006107020301000c00031403404c2d0107545003100c042d1500010030501404001c86103807044104091451403d040e54040c00900c00e00d2a800380701004107044c1c0a08012400945a01c2503035070b002408040f201e0400100200024041d10b4030301d03106d6038000d4401e038401074140c52024031b200000f035255445d1350008a040000c082c140c1d1010384160312020000400c281105c9010b548900e000f1a2520304081450708030b40c4c18050f8100441d8850000c00c500c180421070f0380215590503050001c0c1d031100054044420030703001034010704 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 199024613 1250 199023363 199023373
    0xb0c0a020a050d0c060c111005090309060408010608060702190308100801050f0601021c140702060c0307050102090315071e03020c03040b210601050a0e04090b0c0a020615060706050a0e 81
    0x440d1304203601580c0988584000c004921300310030242c42d80140900300044031b50260381c00310003121480d071051750420341400450303060005c0100055130541c40384d000740e102030f51a030070204020390081004a0700446c9078009012180d000c285509030410403100041d08204036940490340c0050500d075100090181c0100a00052070003420502078034000b96040c5005200d0181d01e400c4100c031181449040220765510101001202d1031100c0d1150001caa0680e4040d604000e080c0a0010401c018400244280b0002d600d03500004205130800807000e07070f8900c2400401080000c0d8a512540b113112069003001c103240c82c0c4581c55803c4000f4041e446140d240352000145c0841d090902c01c02800512443c040140014050a4601c035002101901c00f41e02044090184041860084060064040c0e010300005607102d050740799071140d44000c3e83d0303414149400061006800d6410304c81168071011312000c00d100c0847c0803010481c0351040c00ea001e4001940d03032000c1a600e01c080d0300482a20506002121 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 199025863 1250 199024613 199024633
    0xf020a030b071107050109080d0e15040e0411090c1903090b073605010507060b04110a080f010305060c1c0905071d010506030114030a02040c0504090c0c0b0c0a020a05 73
    0xf522a00c4800103001840c800c00c0000101d80d842201c40f07074190b5001c00040d0010100751130054946581140b5800d501203200c2c240c5440215070640a0802042d54541d600101e041a003050643c0f40480903845000c1c400140030002001140c8080b00e41c60303450b03105074841c1c6140c20394007240186480b10006082901204c18004616400400c10918044101022010b4480001400014008100000c8402405000402c00c40d0b000e10003a01803240a030402080369507003013001608a640da034009625407000418001400c0d5401048550310450301c0c000d4000550560300e40c02c0da9100010b04171051600c1c000303040c401d035800071810500803007441b5600340f0030404185011902c805090045804141003204511081d521441d0601d04881e00a0300003442c590030074101d18a191000e04034203030180704004101c0b0050b00c691013141b0529460b80c1d90701c1d4850f8200b100034030503514012050300c1003000f0742c15000041042c038205142c00c9040141c0081e560340020348182e0400301100170103001401161104 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 199027113 1250 199025863 199025867
    0x140c0c09010b1b0109020901050d020105310605090102070e0c121501030e061e0703020c060906041401020702010905120c0a06020f0c010305040503030f040302010227040b01080c070f020a030b07 85
    0x20700b40c2d00604000b0000f441000001460880f40381240181d4401e4a00c4010880f60401500b083c01d41401890a140760100c904654048e0a542d03101b170608400e6509031040902041c0d149200280032945480d0b4680300c00e07800005c0d580c95550080704114040c18003c03880300304840040b12003034100c00c03401c036900703261800b0306200015206403014040703800c0810243d01c0c0700e008600d940c8103120f0f05c0c80907041088250312442c03800d40002c024005060b820003142403d081c080084501c141c95000c020280c07031a00740b4105200305911134031300300284e006210000040c1e0b0009009001d40748203031a0406003010100e060303858907a00c0280e00c0e03004000108003140150b80400c2d4488100320050481c1c0b42204240011022140b040300d02403c070f9002400030803445043c1c04206900180a0700c00981002c00c1b1307203000030118420b051009902d1644c16002403440c103190181825900003420320313032068034280c90f4003050b03845814002020300d005070343e000f4210750310b041c081c9000c1c5401c040c00100d02c1c9808400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 199028363 1250 199027113 199027117
    0x1050d0c05030a05060603090706030905100912120e030f130b04030f0c05030304030308010b130f06050702210c0613080a0804050405150105090f01020a0206071a100303140c0c09010b 80
    0x60649000c0c2132000058040c2421400c0300c1c0a421040e00401d0040c0c5060350440003484040c00840d03240c02680c00c20000c803581405084003141c004c0310503e49200c134460317014080072107442601030402c0c20140083d80c6c200c00801610801030200016554800103880c412400c20302c2508255121071740814040280400c604001002d00d00c140d4a043c54139480f402056981e01584c4401000101f040005004c200f8110000e000f4010341e40108045071500d5000b414144283c40e0010800140d010545505500c3d00d503d000f103603842c0304ca40b00300c8105100c084983c0c56048001c001409800006488100c2d0f0700340149080c02803083c00161421110645000035442c0d0280c03141c14481c900f8880881c0d400048101903082048058461a143c0110803052210746164072100505501640840c0340c00740c1c907140c00802200e84588010740102075150343c514449180608040d004054021f021f0000a4014282c09951007801d40004c2e25035580012251610400d040d4003038000b200b03600001001540440 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 199029613 1250 199028363 199028371
    0xf030303040c050a0609080d030c030212070e100521061906030f0b030c0306010302120a050102041e08060c1c061e050a0b070308060d0314030f01030203010506090f0406050601050d0c0503 82
    0x83c400c036815640300401c6600403001c0c02031004071b4121001e0030238400d01030b80c08007100201e982400750030449800071040341c2140c1100c00c1e030045940010b6481c80d0b072825503114014940203080550401d49032065400e51441c0d20040041d0440084001c50503035500c00e80d405e24112100601131046a854101c020041c0010404a00c4902e00b8412000140d26000c100c00a1480c006002002c0c50ba11391380070801030042900d240880e500800c0702c00e80c0070800a00080001d03084a420541c1c220483c1d03400760b1805403060384604d49940291080c064054400030444161003a0700c9500350034860382c1b01d04400100305070792000021801e031481c0c52800c820700c46070340c6d821a0421140450001d41e50040302e000c62103011002000585502c00060092800f0100d40130b80e54041c1c0751503120f401011806600316401902c41c008200042e1004000b145000d02a16134042025a0f10304024104580543d200920190004040c40d444000284040c0d1080c001d856a241c8102821301580e02c0a410103056580151 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 199030863 1250 199029613 199029619
    0x3090f0b0307021f0b040e01240302090103110f0904110109060302250602040806041506060519050c011103010b0a0801090501030302120d020d020f0408060609040b060d020f030303040c05 82
    0x420001015040081964440e51441d000307071241c596040d004151003001d104142400c1d0342d0341d40d012429602d81e40306141911b039507503000291004a0401041213105020022401c1d11100c000030300041e2960444c50b0704507a070161541c0003803100d14000840010220703128039040700e41e07441000709201d00074411015204007a02c42c0042c064450705d080701640f0800001081e41d0041d804114103414102144030003560044000600b02074481c0f0040c0d040000568040e0307042540030003a241d0241c0180320380b40050500707040080c50b0040310084404c0a00300000001c1c01d2140c00701e018a8803030020b4005c4d8005914046e06181e4968580031240c04c0354010426500009034041d0022a1000c0c0c02d204d454141c2c0e40540050400d0404120501e04942c070542d0080e21003502400015003200b036600107030054a100003481502d035410820554034054006000c0ea116540c0102884041241030110035007141c000d46a1000c3c120300343c004920a0100d282c034094061100104000510420310b003620160b4000b1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 199032113 1250 199030863 199030889
    0x60307030204140d03080c07080c030c010903020f01050714070203030909090d23071b0f0f0e0c1c0c0212030408040e1608071209120309051908030103060b0f0a030309 73
    0x145040c13182c150b400010040126003660041801917003544003a14901c1e1260f580c2924101c4080400381c15074021010138000350303459006c00400c144e0180321100322130f2900c0008002618110314014025001034100b2861440001151021354405008845080401501e406451300b400c2c00074a945d41d4032880c0c240002007200d0b41e00c4d840211409000035032840c080140e181802e0f0709445043e81c0e221248421058211000c10000345090b01880060007426000003042d5400d01d01a1034080304100141100748101d401c000720620080c20034a00c01903d07a1451001654031411303002039240200d40348401020354800b00c2040108040d0a00420a5035112a980b84182d00d03019440e2013003450541d030f00404914080009280765100f4040ba41d00da111441002c61482c0c01030302d5940c41c012205d40b90354002600d07a4030707440c00c0c040304204030100c900304511200801ca4281d1502406800b042c04010851616000311a919a0310324500c8000000024089803029659107005401d11849101d0048505a0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 199033363 1250 199032113 199032149
    0x1b0d0f022a03070302150702010e060c0403061a0618011101090602090a0f240309140105090606060a0507030305310302010e0c010903020d1506090b040b0a05031218060307030204 78
    0x100a88080f1079141d0010180c0e02900540c4c03000881340140408215940e43c0412501078200308a9140141100080c803980c80e411420400706540e038100858031142c4020298111603110101119021031103600d400105c0800d6074012a04d90f911346002000644c24031520a061050a03802804000c00440300681690354070460303800c401032030344100590844817100c05038044d0460380c80920300c110346282c005030741ea9180d540c10026244060141541e82e5544003001440703182008000e4005c0001caa100c0e0510141c038a00500303034400c1d11001420140c40705c000c00c80c3c51009203d0000302d401140150303000e15000814403003c02c41030385000d400543c01c0c00940c8070911000700798094030b504103030344e070700891415502808100342c180f260071250180030f21989201c4040701c3c45500c1c09040c5101004c035004c00d407541000162640c0c980c150b44181d550300400c100c1594001860100b0210080e40c090702e45182c80b9a6142d100d545441d07454120b0030000c104001954960b00400a5802c140400c0c059195 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 199034613 1250 199033363 199033447
    0x6060602010e010f0b0a121a01031a1302031f0e1002070c09020301051c020d020910080d0e10140415050a0f0507170d0e030408150f1b0d0f02 62
    0x440e98400740e80006042e0001c1c04000c02c2125000c05040c007406030701074401040ca02848c1c01c03400c264015100f141c44480d2519600c0c8201c00e002e900301254611051481c8084d40020342c46d25840114a404403103800c4002d10360494a4000c101c5081092080e513a407401c00c05020740281d4410310003102c51022154011035420b00a100f0f803411b81d000a40240030040c0030007007203100d0b1580703518141ea1081c01c4140100060b40c40f8541c551040b04081e0090728098549103138180341c08061583c00046c0711000107a80303415192502e007100c0d80c140c00d251407201440911040302c20f510480c0c109610390800c0c00441c00300d45400500404403100c19030358030400201c850340d00f120b85010b81d100c014041c3e00c0b40d282407801202d80d0406004c010841900004800d0340300c051807823640c0d00c25400703421581c201600b52200d011030b00809662049009a00e421580b84c000c01000021324800124040014003103030450402d0015032208440314075a06085584e010003000300c0b55003100c10341107840e61581d102c0d81890119 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 199035863 1250 199034613 199034621
    0x703030501081906021803191e08180a030206040609030b0705030705270a08011a0411040905150a240207050d080306060d0c0807080708010608040305070f06060602010e010f 76
    0x141c8288810302840c3d559120b070041e501006015803601d5255040a00940d814402000082020b1401200e40481c601d4107500b1010096002c4440460002a0314089040f2100726090704003140303242030219421100040c907154070340d000a5000100480c01050507500040901c040d60f0042c444025142d8440ea000c48440c48111803c070005070082c08a500c2030702d211a1003001040c0c91141d5001350150800128020803030962003450381c2d039100c0040c0244c5180c1c1e1820009000c10580f000d10981008040d40b002038450361249520b40365075000051501804040d44c5d01c04607a000f012103540c42c0d6a160500803400341c010311013403035442101003122500d00010b03104040321009080c000a0504036244d8020a800003051a50801c1003040b0203100c800042c072036007015102c03076190100c0c00d0800c000e00400b041c00040c0402c041c442c4403401800303003035001895030750310507032616010381e90301941d20b00780c0d050008641008203020704203080820090340641203000350a1900c0d00801c80f402c8020b074203400b51 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 199037113 1250 199035863 199035883
    0x1e0402010917070504021611041107020d050a02040207060b010e092404020403120f021605130b030a0f05010e0f15070e12060f010f0905040510050603070515070303050108 75
    0x850810041000b140040c180200c0e00401c51106981000c2c0e030300c4001c40c0503039003c503415001c0420703000860710800111040d0501400001e039003c00c0130201540040d0b1040c4100703100688075221480e44c0c00100001005031281d91035014105640360038440c0344c110080d040c210269408036040c0070f603210b11800d2a0a00700c0c0f203945501e084175006090741030081035115104c05600d07005a001c00004c004640c80d00300c184030343e01040d51104604903022900030f0510280c04600914840403810401c2640d44102015003100b50404001454120040000b071a20b0200702c8018450386440701c03540240700043d40300040c07115200080e01d040a400c6501a5280c505d00800030609013031250104080a00c2440c194002004c0508020806080a001185055000c40f03203100d1b540142001441410b0340d4003c044014800454203003d242066915a40c9500e840140d41740000d40d00c3c000100c0c1680c007006850018000504030300355111514076101d0040c2e00152081d40800d00b00800000c3c40c8000042507404 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 199038363 1250 199037113 199037117
    0x60506130b0d0210030605030708030d201e0904050a0c0906020c06180d0b0c0a090b0c0c150d02070c05040c02030918071806080a0b041e02070213060e1e040201 70
    0xa2030240f5400c01c982018203d9166041603554071000c10349071007c211940260841c00c00070350721001c841c0030038801d40f1269505064409070f106085240701035520241c035800140c5020b02141410b0300c21590411380142c003e0756038020704003c184600d00c83d442c0c1c0f0040c031041040c1e507141c02c1d050300c41c0c02c1a0703510711a4612240d000303a010060020124071304000d05110200c01080e010783d85c0301c035441d04441300c4001e403240d170584100003850040681e00400064020179180a00e40d06145031880055120313180301c00a1703800f07070403180c1c2400384040e0003004a4000c03064060003103490303400506011000401901406028514002c0f82900682c000016104104002000030083c182d45581e002c01c80d88026003080240100c0c07480c030441008003101024040c02855407010310610748580743d44140c0d006840001e02880c81d048902507100f4031070507103070b0b00c4003850200544c1e40d10b454408104113128080d483c2505614061011071a00a4905018010b806484041010032299031511240210580300240 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 199039613 1250 199038363 199038379
    0x609011a09040204141e01080c0109140f0415030618082b09060504111e06130f030507030318080709050408071704081626030d09060506130b 62
    0x4840c0c40d0501e2042c1c0e02500c081d001182c0780401443d119401c07042a5036980c02c0c0308451910a05030384160784440e00621100d4020500442a000044c0182c02140100c100b18134080340f10b441c154988a0540300541005041080103448903080101807903c207000c101c5155007030640f162244403542c081c00a01e00d4102065614150740c5900007401d40c80c4042142c12900d100050050320040e1341d200b5080c0c490301907140894180b502d803034039081304008070305a980300e01070610030070100248000c0c81e007194000c2910425aa211040313080c41400030241d00040c1510042c24000c410040d0100d00c00b0116840790703c44081d44403098030003000e452480c0c041d41080394080d8104008800c019041b1941250240c850940b805100e521078010400e40700d1440000550005400c11880e6810802002e00f0725004041d5407415081c00800822180d842496042c040d512940a0380409400d008541c62000c107000104a010401d140c514082e02c0125a910301c0303815400d190b203420109c1e5001d035560407500103007161 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 199040863 1250 199039613 199039661
    0xb0c07050102011a060901090e041118040b0103120c0b090708010501050a0806150a090c080106020c01030207170c011103070903060c08090a0f0c050d03080a0513020904030302180a0b070203060901 86
    0x440754010907055810440300b50070005803045504c0c40d1a005038082c0328800d101c4158038080c002650f5140812803da028a80104008280c00915150560340d000a618a41311da685100f15031442c0101006080c4202400c00c2c000380c40340000e01041161000d01c02401540c0c3d072041008040442d52040781026000440000c41c031580c0400984800980141113016058440e40d40800321a0717800c2c120800314a00000602071107030100903200b043e51003440d0651034010f4079900c102240150b09840c40c000f00003c00c6c10843e2010039007280f6200004002c10316107900d0010360051038000c4901c42039408600c2c0580400280c0d100e4005d45100f101004001c140d90b81a40d66020403402c911241602c1d0301d0824000859070f036940721841090503000b1740c3c500c2442d04008100104403000a42130703d0440a0b6200d041c0e005840da0407101d50f0064140c1801a1100b075084c19002d46120189030155011440b020046068524540503151a50098084900c135580340c04005d42200c4045034032584412500c0340c2c00c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 199042113 1250 199040863 199040869
    0x10609030510020f040906080d120506060702091b0a02070f0f03031403060f06031005130213050105030a0609140405011a1c02010c0c061e0906050d02031e010b0c07050102011a 77
    0x41c120144180d11300381c0f4007943c520145084400742d820402254200d10580304000c4c0c0c1c40500700340c402c268488200030750306203a0002400b40c4103481000380945040340001d440e0b011800e0340ca800300415040706990310040000029107841030350103901c02183d84842c000c28044c0c4001c100100360b0b9815101c90640241d20401045160001460b0325844054500000c245440d080007860150466980c01c0440320306000420038a500c202030444040d51040c401000d40d6490740545504980c42802c081da5242c403201c181401404564001c451514203041c1890f00c5a148c40352681d21450164000304440c0045440c6080d244032044212540200d0880c4a001040c94030841d06501a10506104149080300d56684074a00190340c0144041102c84000d10644075042070100d00301d050074a00520004d060000107000340c060252071440265001c000111035a598113502c0c2e491441c00c0c00041699a541c11107240c1036441240304004500600d82c000900754014081c140a070110460044110076000c018 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 199043363 1250 199042113 199042117
    0x60d050402030c030a06022a07090507050c06040f03030b091302060a0c1703011d0c030403030908070602180f0406030807061a090c04060305100506071727030601060903051002 77
    0x41a42d060140d040208610f079001c000e448405c520514025842d6644200c500248004800042c0c0c000d5170301c44400e0250f0700010a511094450070b6500040b60f881e011030031213250040c402640094414031040c40103010080483d020b01a20030ba03024080021407000f030120203082a14800c080c1c611950a04006151203409051202594030f0050030244040e1a0080c45407015248601403690000060202110751110700080314071105600003e030812403002856403100910243c1019520040c0e4002c000a43c421940c1e405d030042d40a6403100c0180e0a001214020302c0b00c1144a8401d840b884461410f060041301c0480740c04c580a41d04091036501d4101c00b6101140703400301c0f1403088542e40c01c0301e0340d504151301307009080e11030415840740c0c140f46000c1c0031254003030208045101e0501c010030a55480500311103c0d40d510030700c00c88001600d035118202a01071400c46c1c2c2070404402011546c01c46120f1507101d50003008a080f1411640d9890007920b80207242e000240403500240402c0e40f01c4403090300 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 199044613 1250 199043363 199043371
    0x615031113022208060a06180b0103110d14090d020a03030b040f14040b01060203090907030c0e030d030f0501050d0f080c07120807061422020609060c0601060f030b060d05 75
    0x50261078000610f40c9410324000c00900400f541884140074040188100030740703680b0070381ca504100030302424500300c40701c81358812040901087d10342e2040f0109911a41000b81103488038a007040c0c6a0b1488a801e401411000347c07528010410000000e0b02404006800310700f1600640240c1144805510100c0c06080c480e08056007258a42c5240000b0201c18442d40f01801504800c60a080c10589490000441f06a20032070840d802800300d2481d60380d800c9846d603044034882c18005109111840203858070b50011094aa240c082c8a034424005500754000001f404117040c0c1c200000c1e0789910400510300004c0030003410707801c44003d503c400106024020400b00c13161a085801d20b50303841510504141d00c82004483d2481c02180c80c80820036076020340b00032402d48929480c40c0c0c0c80c105c0c402c00c56400003c2e8890300e400717030307108980015500d48004031540020054405507a0f6420300010990341c4030700f03215520018518511100c403c91281c881d25039988c1e0001d08443c07a0040800038000a824050 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 199045863 1250 199044613 199044649
    0x10510030b07030f060b030708060310060621091401021306180504051e07170f06010e01031a030a1b06020a081c1107050c0a0602030a0824060a0305010306150311 71
    0x100003003206c0d40c1c03103000380d4420b042c19500c45070185041000d045c20419803118000110f418001e0501c4602d4110f003481c0c1103204070a14141d01c80e04600301d4403000c0d14440202030501081006190400d62040d0014401c414800a40c0c04000341c1d640d03800c442c1c540c180e070003400d4500c003814420700052a15400c00e03504403507411341805480c0c8000d1402c0f05960802c0ea0900003282d80d14012000742001c88001540c4901407003410603140c5049400a0200000400344a04143d510b45001d03051000f01c0140c003500e140c1c05021641c00c80c0c0d15181c880b4080a001c524540c10540390b50001900d240300195220181d0360010105041c034502131602c0515510f4918959211622042c0c82684c05540d60068041e0501880061014004140c24012401d0441d0000c000310b40080005400c082c0e0400c552170340044d04861001e04030740c41e00d4400440c0180596400758005000511907812030307415001141a0703409118100407421081106a030f031075886204c01050541c403980c19100d14900036100c051404024 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 199047113 1250 199045863 199045871
    0x103060510020c011d0d17040801061d18120d0b090a1d0304080a0311011103070c17030601090e040303061e0608090f0a020904050309090117010510030b07030f 70
    0x1800015560a0101d034140c0016484410000220360b480080028109a0709a40c241c0e404c6881000c15469000450058041c3c031031510504842d006010458004001c02c400030800d00343c03030340ca40c540690700c240004006484184041203000c3c030340c081c1450a164a84005282c0290300404021089d00b1682c0070340d0745243e0700d44581c0c9694a802e10b0071841807040c04e600140b9551810b21180d115a8820705450345648148014400340d440019031501c100e4150400e02c500080c15044240074104150065201c03150100c180001950060b420342203940c89111a0800c281e00070740c0480d2240401c9401c24002522400d0800c0000c0d072114241d43c1090282c94082480ae0f250409040c014002009034545852640401c0103003070307800b002050300301010300050003c50702c10000440c0c1c2c034035210201030300c50010300000c5020040e042044842c140300c090000c00c2c180da501d195a503000402e04851070003a500703100000340c1084070042e405068a92002009080703881d00d803c1140207250309801e40c2d413010b0703035 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 199048363 1250 199047113 199047119
    0x10515031f020c102310050112061203080601090e0702100504050f16170a020d061104080d1d0303030708010303080c0408030c0c0a0b070b0a020904020f0d0903090503031e09010306 79
    0xc24400b80d03a424003100404030311405d18030000f0302c000c030350b81080380c61030320105040c02041c0c25031241a50845070246016144032a50b070442d013001f0801d079441a41c4000715000c6003c1055041010a4400e4400341c1700e503071120307950390290080728030100c0720000180c200c040019a40d5000b44c0c00640c0003402171040300c01c075000c1a00018070b420f070703103150403640d250400310100b281040c5888195901381c4a46c010b4003074694181c2c04500009030f04003005150a864070707824911158118180e40080088204542c4902d04800e805007400c100c51303070034054090f4500e07515960b80c1000000c80e80203000c6644d4030103040e0304c6d50320700f120900f9000d810107032988000c0100080789001000940902e0000e007024084545240040181c0e405aa500c0021980814841000461a001d04450b030001e40c000015030359004c039600140c0203100ba0380000b0040350020402020080160b407007250228801d4071130f0303d0b0580d2a403040554a000e902109039505044079008500b5400c1c030800b40c910328406060108043d80c03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 199049613 1250 199048363 199048387
    0xc130317070615090f060f031119030f05010510050d030e042c0c03060c070b04020d06050109150b0c07030609021f050c06070f080609060d0506130302010515031f02 72
    0x40750030048910343c00007078014010f1071070301e100d1000c90500010041040c80d1070a018851542c559220180180c065a041c0b402980c4418044c64000062300c0601400f940d100c1c41d01040420310040c050300c06602c3c1500140015047c0110301e0141d4070001c00101941c240c40e41d0442c1e904000549060b0003030340b03421426400c1c54030726103450a00b058180b04141d030440e01c080200d1030b052484800314841c2c0c2c064014441c1500b9800115501c20790418083c51a5558600210305e0071111800004e011030301d00000010550ba1950051041e041e00108000d02c01390b0702d034210302e02c902402140705040c1e0842c04040000601b507512192440d80301404d8050050102503480720006903901e00d01020540000758040102c20174011681d00200ca030030140f403000f14222004044c000000d1005000c1e0503404041042e60f40c680c284016040d9000003214031a14000ca0700c0c03540182002c404801641c244404a00c50705c800e85501710f05580040c0050a20f80380342c0c401c3c07583c1c00c0005100c103490b60741d00304844507040c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 199050863 1250 199049613 199049621
    0x90708030405090c03280207050c0312040614090306040f11090709090e1f020a0809070f0b03090313060207080c0a15080414030a0914040921050f07060902090c1303170706 75
    0x150f643c001c016214408c50900174105000300b402507219070005018211040840d0702031300c0644000d850094007041e000456414144100c85007180d061180208000070840080014482d480c45104200050646002403001070301c0c058400102140f40b504040c041124a50f010384031946148040707540110303d1040c0100c5500c10001d0200b10541c0000ea2180483d07040100d181d0001c2203440100718042c500420301c1c105400d1801003e04169000020035007510082007034039051201d01c85841c0d52181c0d2910040d50303c103014821010540606e01c42c504132864411440c0089804442403d070841501c0b0400711084800140120f410700d441e500d44281a03081000580b120100c00c0d19a540b4079400e004981300d00038039603081e0314411414185d405000900114070071903006800b148404005090010030b480358080c6580c5c2282c110301c0801c84100740405600303e9407100b0300a0395031aa00d516031008618481c0708109081480301107a4000b080018601d406900d40c82c0703114008541814142c2d60307120261 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 199052113 1250 199050863 199050931
    0x20a020a14240a060501211508030307020d18060e100323061309030e0118050d0809040509120304110a030602040909110f0f15040914090708030405090c03 68
    0x2d21480c104580c500c014442c00000d41001d0901da4401e040061941501c0305101c0381420310f0949480f203555520310b0115058018081c91810749469180c5200e0095a40c68045000c3c0000b0b001c2810384407031103c4150704d49061341c01c5642d03000308101550b000d100640c07004000c1c000401d9510517282c0b2010128151468000840542c0001241444420007664180a04403900a01d01d0b1002840c0020b411203554800c03081e003801d143c42c00c00105807040903811316503804241c00c1005e01e1076a104200304c140081c0141002250100718070b403900409142c2c4e88e0300c0e90300d10b000c0540c410008240850264900ba42680e00c009000f041c855860b13071390380300503a000740d0711440d1015203d109a41c00c2001000b540e00c12110b081d68400c621210040000750800019602d8500402c00181d4041003602040100c4000d49110300d014070a24890b00b01080c44c0d000d007150f5080842c09100000300700d0000c044100d808454000b400440e003034548586000f426071004e03019500200c0034054801401c500b0071078115130 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 199053363 1250 199052113 199052173
    0x10c032003070f060c03020a090e040c05030d03020a14070807150605040903030204081b03061602010914060106020d080702060a0203090a1a0a18080708030601020a061406010909020a020a14 83
    0x410f140340020030354040c2804802814018004140d04a43c07000109040700c200510605664070345017001c2d118040907030882a01402524088440d8a41640007402d0300100b640e1031004021131a16684805d004152009058407007c100080105060001c8422200450800014031640d200002021241c0840d400c8002c650049410403802100740000e00700e0030341d802032415030b020190000039200c6000802940f00c036203000c0c120005042c400d40c003d00c18194080443c1e5a2450302004103a5280002d1142d44014403031100e0061f81c15126840290041134560000c0941d0f4070341e41c0c6844080d400090074646a40f00d80300400c1d003c514403c3e110710301c542510001520074200110302c030081d40d01401000d6803034100c0000c2c480c00950080c0407100d0140d04030180c80d071249c446c2d200407070400311015000703005907081c846046251241a0803243c0252000d0320b81c90100b0b030b501c0c406201640201030340f01c009a00a60115404a10030500700b02c114100c0c081503c42e8000701d01043c01052000640080c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 199054613 1250 199053363 199053383
    0x80304030c1416210f170d090804030209071704032a11010206060f030a0803040311030d0b0405240108060316090e010608060405060c0c0a06020a0e0f0f010c03200307 73
    0x440148110191100c401c58410708209510954880545d01d400140004001e1014403e945c903001c03100305c0c01d070f13880403c984030705018070249810407003025049804240d12620008000c1a0b03032900a2425040340400340d0032041d004e0360785440c25260190041c010441301540c0d140052128032211b880091024030801c0040c0c00300c01c100c1c000904c2c0002c003d020b940100c41c1c019200d00a50340010784844901e0b880001c40f81e9903a241d18040321410300c0074084880d240300100d00c84418513400c1d04101c501007020f80c3d0400450f40d808500c094a00d0401020906542c10784044210307a5200e20329842d0300c064060202d9198000803844031f00715641d144d0044900320f42d609280d481181c001c0c05220000d042d203c000f05490b082c00c0d2266911039802520081c0322040006500c2c0b480e0500384030b0b0400581d041201151184070004020b007100207840c840c81d20590542e42e1400191403e1101e01030180c9060351611050b01040c1d4040d1030070642c9030308403188072044d021600a2105e00700014141544a128149 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 199055863 1250 199054613 199054619
    0x1302130312170108030c07181104030302031c090b0f071e0f020709091106030702151009050a060305060714040801060803090a080118020d0f021305160903080304030c1416 75
    0x3604800381130700405101c0c0c1040100c40404140058000103440728441080c810f40303206940b170401040c0c3c200321801e0400300401e00009064000c0054812022401c070f804d0307403010100c840e1004807613a684006010103c14804104014500b514407640541c07941404c0c4034000c400488020404807000728800003403103e100c1c0170062070341440910018848503400b4080c03001c4c19920b11040101862800f40148408000030300e400e031007000106886a06c0070804c1a2740c2c2000001140c03412094000d14000070f0424000c03d1850809104241c04c0384d0700030019140548a407030b0704440500e80c0d400040d41610301880b01081e992428031a1200400b00e40000f1a130b21040c4805002e10440258450005a45000c000001c1c40080303a0090b012075904640c183d174620014a000c070440d1000ea80c010f9001000c520075112503140d41d0340082d00650b1411074244501c9240442222149138070301000b444c054040c00440c0c0024050803600081610645460300b0000002034003503e8040310402c5000c0c0e80c84150420 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 199057113 1250 199055863 199055897
    0x108010b030c0a0302040504031202040603020315030d0e1c021806090601170106142206030b03030703020309150c0f0102130504050609060d140a0609021008061302130312 75
    0x104040324066002e0b100b00c040500018901489a11020b8000c648607030010307081600c11881c0010154808604649450b01d40074020000d404c11141a41030035600301d416841450005100f000c0c03109182d69075151406420144051104001c03403030740d1502400b00c80703030780141d5440c080752210381209100341f501890003904115101c03101401e03c038144024a0b102c1c1ca114540004401c1c191001400c00c5044205003003d4000c80c0d02c110a01e5500261500c005290714491201040c2c1c1258910707a81804014145820503440b0b20a8030402005070744204034202d101d081c00c00001d41e000c0002c40c0c4450600103e02446800c160549042001695000401006003e4110703d42000790030192402c00451601c0c80c00318203a0313840032744030a124620b0350114030108080c041c400102c850b601d4060f6206403485280074006031aa0550403841040340b440c584195a104800f4207200320402044d1000d00c80c9800d05500003940040c0f0322b0224401c036510080007003a81000d0100b0024070b00d54609400c082c4429007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 199058363 1250 199057113 199057121
    0x1b02061902030f12041101081e0705070f0f02010909060b121f0f031b061407052b0201051b0f0a0507020402041205190809040b01020705090f09060f040203120f070b0c03010801 77
    0x19480c1400092000e01c003916100c000704005502ca506009c1e800c3d51105242654035003d0400c0080c0b00d82c40600b03110080040d20504540c20f00e100b81c0300d0020503620341c500d440c15191240980600c0382c105100302c0d62200b150103003503074009240c0c15813950b00c441c42ca2034445100009400c080001c9501a108004000800780c441c042c00c2500c910301c030320090a000300103002450b5400c8207a02c3d000040783c00c000f801024001002d0075840310420b16031202201d4907001044861f40c4450000d540b0f00f00015001c080c0080405540c850800341003850401072106401e10354000c480a101040000c1c03041d000103840d18802000600885402d80b180c00b00a46403591600181c0b01024010f400884c10400004800300c080e80c01d80d03072089501041501e0b0700f200417854519103a0000703600c0a507080601c00815840251503015401020684a01c2c1c6d03076403002c0e050b8010f0140e8009403d54000078840340f81003240f8000d40710f5411415411460a203582d1180302d03982006450324420401c000004125020b0240f003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 199059613 1250 199058363 199058393
    0xe010e011a070b04111e040c020a020d080705100e160902070312051e0a05060a0f06080c0703030b060a09080601080a0f08070c0513020405011b02061902030f1204 71
    0x3040807036011110440e018011000700800d42400b60300803c0400c45180f1010802e10303006014148005892884e080c1240c00d01021540a00e2402d40b081c4501032004c1420800943c000e040d0403000800d503903990788107500151040e640303800350701650484071140d03006003501d02c1321000051400103d10b440300a0800b809900c43d42c4490709c1009801c000a0b04010000d204101c0800b00144994440841c00703154441c480c40310118022290030000b074071407103510081c080c0800381c508040080c0c07602200740e5a806140923800120b10070788000356050526000901800344240340c0440c18a5551000c0750168002018000110300d011109012041e010448030340100f90b0034008104402c100d40310130b08113504044000e131641c03400140c903905100d03030641100010305010b00a0000c0b002940340300b00094200340942800907180c51400010280004011880c140d001170542c0d150400180e80c040b4942c002c2030884c025400240300c42000e6040e020042c1180107240003620b012484d0511700700e84c950b15004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 199060863 1250 199059613 199059629
    0xa0e030c09071b39090c12050a0f061403120a0c021207120b090114070e0d2406060905061303080a090b162f0409020a0504060e010e01 59
    0x820a4840c0d00c03100782081c1d180c000032028002e030b50702d013001249070411210300c0c920510b0511001c4450000c54001c60003002c20510340d03041c529210460941074481213010440000c1c0790100c001301000350b40d4031881c2c214499040011b40b450b40b698805003030324500c0d8004c0a02c6004011484114202489149000e1107003024151030041205000f6161117226130001e40200307045e1240d440f0000c002c21140000d48040c8055480029461400811150f402c80b003001e0154284914918140d40000400d80210526290403891104030030074801c0302c6981c81016103081c503d60000d040e58810f45c400c0440c40b000d00c44800300f55030307052040c0030f05110311561000d40640c03001c0140302d803060b1040180c5001c0c1c1e41d001100c07a41e20550620100c03002e941070382115080d94000030302e2801540543c40708032025841440d0702da01401d0506462a00505140d02c50801c0c8070010500412625140d07000d603816520060032111782a0b150000301d02100d005412510440300c240d80140103001c2d00500c0c2500424440c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 199062113 1250 199060863 199060879
    0x120f190504120e060417030415020606010f030b060d110c010c080c030106081e10090c02011e0e0a0803090d030509030a02030d0f061d040c05060702030309091503030a0e030c 76
    0x1542d52511028242c50411003003040c00004102503690300d5080310010160b12003818000e5460098540e160b905c54481c4103440400507400301009400480c6403441080d0503154840101d0400c4001d0300686903840da82c56120f1000c05c2861649011480f42400610341c04202036100c141c06c404090851703180c00302d100c05000c070010421401032501030440b81590050301d010401e681380c200d1a00c280c2007409541100740c2d500300003002030401040d80248212070000009100b08641c840d0140c1c01c84121380704491840104a040702046071594001e890380718003041c1268041c1e101da07224994160410340c3c8207102500100e400703484942d41402940e4204c240c20024620b01182c4900c040d542e80710304210305058a4a4824900c0d03401c400380d005400030060650103c18026052012103440302085504448042030642c000ca82d900740310060312401d55019004601c0d00c0384074802c020000500078903c1412745010021590244c40500c054039007468543c48540740d101c4440100b60520309000ba12500070300203 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 199063363 1250 199062113 199062121
    0x30b09010908031918080c0d0908030a0e03030408010c031b0201050c0a0804020103060e070201020c100c02031c0902120a11010509060426010e0705040b0f061e120f1905 74
    0x45402129013069407100e440002241030a10480517004c401e91600f0008904034840091020050003403460760007010a540742c9002d05034055580310410f0050500071780c401d00503840d10070300403069003920301c00040880e03040c60340d100000c0e800e507100b50241c000000c0d254110102018241400e00e0034200c0c6a0009000502e0402541da04070b01603904035008010b8540080307415a4046d62110b0080e20300c2500461882c0f0740403c0c064040c1d44120070110b00380c41a03000c81c540140440c820840622031650141d881c05044e040e0044c00c44c0350465140050341d80d20198040183c1e5000c501c1071940304480040c101c600d1041c00c10b002d15070700c04513009044c0a0200800f40d103581e9104122015a11041c066021640050ba007051505d0345418100071690318103001e55010100000d60340007103400440f414020740c0703a88c10030310800821301e291030303504010140b01c0320000c17a002d422204002d80d04d0744e40b014100001721184424421060b01e88010580b48041880b21006511280391030742c6044103020300c040e041c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 199064613 1250 199063363 199063373
    0x31e0a0f14130b1b03010303080402120c09011802130801140f010f030209071e09050a050a03051002031807030b0406110702090a020903011410051c080307081b13030b090109 76
    0x89001c5004040d0358035000050051081940c400c1001400503813000d40360344e140d14010b4213400c0255002c0e4854280a425400d10000008680e040c414001d4024460f41c0d1a1a25040b520001030350080e10217034080c08600044100e5501090091100754004036517000e90401011041d54003424281481048200600140c03a02046440450f40e0685074041190f450720411280d181605003003015185c0003003111040b980e40710200c5426100101c80b9032a07441e54440c1005540e0049100040c503030f4204a0300020070750541d90107964414005103000c84155025014541494450381085854141c12024402404002c0c0b14080d980c032006030072540b034103240e500012141c950040c200b01d0030a8000400c1840d5440a4106019810204410f03402070f040c1030a40072541d00d028040d940c010f04403205038960081c8158980410f0b25002100e051864440107c12500d404008004c2141803105202d50824414814010074440704e11200c0c2000440c19460010324240c40070345100001c1c0e0400c080080891 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 199065863 1250 199064613 199064641
    0x12070c0e07080408070f02090f0411030a170c0a0c08010e060a020403030c061104091401030b0609060a1202011e02102012040c080a030207060e0405150105031e0a0f14 73
    0x5070001880c4d40c0399505842c00c078152254010b0020340143c2c00c00c007840703403080055400d50300852081e12604c1784138207420141540c0301801040906039485019520418091104c0140701c00140842601d461181a807100020800700c2e03070024115030740d6594030031a8000240030054011400441c00e6142038615100200211707440700000c7d002d1541e0b10301442e0700000303a5088130010203030039074140140d0070b101c0307c0340031240001d00c4250b5800094500041d224070300035600034442c0741d0003401c41005c6424610710a9413018a15002c134140141502d050300c0c2d003015100c000c214114664001c1c130000b01030f400030000780e684601c906260312440816146000e0500d8080e00e2440308058102071865030b40d81000d02020300154402440c3d40503040789101890f90200b10341c1c0030750700692108240d801019040c8401c0381d900b110440c41740a04803011204940c841c40c011600040ca6100402da100c8811488008604058030844001c0c2d03074400c40c0c108004654004e08045840442680019280c1071080380812 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 199067113 1250 199065863 199065871
    0x506040b011e09080f011409010b060313050a051005010305150f01140301110f12130803040210030915050601180803090405100e01090903030b240f0c12070c0e0708 72
    0x11001c840504400184030741c40540c0281040c0c07041703400740c2c0841480c480c02400b03010b942c0c0001c181010001040b4150500030703c80042800f5003181d103035030348440d1800c3c10541064070440b441d000d00301c0210b0114501300f181c4103c8241c412800515549103107801d81c602030f0424141c1c01e640c007450042000c00062841600d04498594440d00050703c842400030b0300608076240c03400389024010603c0c6131036240800240400d607541034401c07241601c1b0310103078203200b00402500070310541d41000007600505094400546051181c100480c02d00c040e83e80fa80804071028001c80d50141d82d610800542e076070300c51552100607035292801010242020303009522071052111040c0074036211008981d002061840e00e0000781200c05015445d540c41e4107641014015884003a000241001a50a200d00d01b128030f2404040401103180381c5801c01550f5800d00f03030052408440d1420060207800c070b0700301c0140012141054512603075aa900018500151742400c2e54003c080d50000761410401e0b0950000c0995401c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 199068363 1250 199067113 199067147
    0x12031d09090c09091908030108060903031312050d0911010f17010909020d05070b0307080c09060304020d02010e1c0b0a0e0604080306060712020609010c030506030a020d02040b04020705100506040b01 87
    0x800c4d510403085074609040845600881c00c40400c01d4002d100d01a005181030303503120342c140e0f180c80e1582044181c0d240010303030b00344841402c2c003118080010603903026442d400c40c00d420201c0c10300381d45802d00b5085075100042502e0b040700b8024005615030380480446429401c900b843e6040344411f400c4801801c0c0c05018074001e480d80c03468503001b5540c80c0030040c50819030050488462507103d42034020103400980d49070300030510801c040390307108214a081c0e80d009880074050742d08603a01d64003000100c00b1301050036810320103084524155070301c94105402c1043c2480400645a61b69403401c60710f0010b00900c0042c2c168940741d242d50302c05102056a07034202c0d0f0040c0c0126200d40b54a0b000451601c03e803080200386100401900c08056008079081e0310801150000300b0001041220603420f603602290030b503501d904440e50b110010700d4107442c0d1580660003e400011300317860000c013003003c90b03108034400c1d11264842c045203203c5400c18050766070b218100f03450900130900c01400103000340c1c441b0210010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 199069613 1250 199068363 199068379
    0x60e06030c0c061314030403020d06020a21060303200a032003032d04051903030906020c0a0c0f1401030515031b0a06080f0a1512031d09090c 62
    0x7492400030365104010030070a5900600345040e6640070030080b0340c41220402884852100099408800d40303044075005001c00001c00c4203075481d50000e40c84998514140000200510f0301410742c1c4844161700740d101d42000407903909609019280b0104900340880c0340c82006a2000d1b495004540d2454591745801c12095040d8240031501356080400080c0e402071101100f0041212128040440e02854030401e08142250b1400e0101d42182d0448002d03040e41d00811522001400f440381d0803e41c1030082c0303000204080701e681c1d8281a0782c080c19219002d0751205012205121101c9040002800c20100407800c0a140900c10300d8841001601c8a040c5079990000488015145842c48003a171001400d5425002d10140109610100c1d0000140105500240404c90a003c0c1907020301444481c20b50307440700e1362102c0707004000c0c1c4a48020310600c56030078640000d83c0c2000360310004080c0e01c030b07845034070200c2e0800801c104034800d02c48200f44134011741c8060182d2028080341e0000c40c610240d460403 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 199070863 1250 199069613 199069621
    0xb06030c071e060207240b01020c01180b0408010b01020f0d0e09070c020d0501050412030204031e0302010603051f0c03060b070b0402040b120a2312131214011401060e0603 75
    0x10904000b1804060603280c0006402c0e0208900807100e5141240e048216503004d000030b0041c0e0003114001768600380941e0016070918001d60061080421060000e0119040b05031103c02030700c4981c02c107900c80c07000c3ea91540300211140d038050003107090364100000145850602c4a400400d0320f52000403443c062141c3c400070500700761040055548190300a0303d121f08100c0d80e403401a00808040701d041e00e44902c2c080c00280b5181c8640200d40480c2d0700b01460051002d60040c505d00340d404180411000c2d9136a80301c0c0040003507403c3c45102410441d002c0038020800000000c8030070748080c50244010145090014403407610740e0b4040e04c41c03450f0040f65120041e6280d1002c503009150000485601c06c41000d102540090005490302046114440d4002000210545101b002e0600d20803c1d1160300200040c0d1542e03000345006e071104482000c201031344696584501c41140c42c83c164181c601011400480819a00c24041c420840344500d501d01c210b980f4009000744004402e00c5d416110f60000004a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 199072113 1250 199070863 199070903
    0x901020109080a080a060501081303050c0a02030d0c03120203010308041403010b04060b210f04020d2108040303051509060f0d1e0510020721210e010b06030c07 70
    0x418000e42c0b1071030b219a03401400c6800b40180c032080310300c00c0d909802e00b100800c155104e4030b040c078040c03101500c101c00c40301c0c002d50341aa425000244075240d20b10a40e590700c0b001d680c00301f010485048058130341c0c01070392800d802e00074440401c4110000d0514010401080080c807154103c808071760800170f4200c2014510000207000d071011641c200e07442401d050340803820344030740d8000b84604040c03d580d010103420711545100380d80008960428000c0b070040005405401d00403554820342d8450b0310300440c9054a019100d0198000d4040030300003907284400c200400d80c0611035180c01ca1402204c3c00e02c402e0007100000d44240d40100141d00078907400581c0000d94039401c103c1b07103c03154410641e0f400c01000c9400c4402011219a003034401d84144000c075004803449200f00c88825412085075813020b04400c0616410840b0407981c0340030407111600c0c03005200904000072000d80d020b18000301e0008009803810342981c510f585400c0c85460300b0028004d40c60000c2044a501c40e41c00307130703119650b038014040c0c3d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 199073363 1250 199072113 199072121
    0x10f09112b0821310c030c05030d03140703050c1308030417151602010609050a020703140a0801050d020f03011e05011a0306040903032903150114040506030c0d030302091008060d0809010201 83
    0x4254035417801d00030040080503101391064441c1501200c4010030404001c0301902e94628040103144100d40100c0c501e903100340c0010341c0c400c034080782041c0fa080a4904400112006038071040d160741000c24280700ca801011529a0355012080003071610805e0160070f604821000b810b9581c06000c9554080c40313a40c000c0d0400001440300d42001c01042c9800b000b800003950004100310000b450a051007522403501105030398030700450b9601c10a0381d07806d1805018a03560040d0090b640300501c1030141407d5a42401b505114951960108003250503040314030081c3c41042c1c01c004e9012820940301d4461301401d9040d2a07002208960124100900e81005d4000741142a11102d515240d03d058000e00340c040244112561020b600310340c00c022099403040c02d059000e019960980c9072980020075989015001070b50000001001c1d188240300000000d502030041c19000c601085e00441c902c0341c545444000c20031086181e00703000c0e0ba1498020700082004040c490000c040300c80c0410711001c9039100b544 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 199074613 1250 199073363 199073461
    0xf06040b120916080106051203030405150408090402040603020901030516020c15040807030c0f08010b09010312140406090e0a0c0503060607030c08070b09010f09112b0821 75
    0x110203d0000d0b12000c0385400b0b445540602c030301900c0c11302040000701000008882c8075540102c00707441d8404c60022861003845c070240c003d851118061000613060395031403000380300801d0316880c01a42ca5880030005019114014854010301040c4c000001e5140d4000c282c038001c1c0001129480318104410814172601d008bd60003030b00d2140b20b150300110402c80a111144c007a64000c1f6020126a96504426802c3c1da0103050921381000c07100004100080b901c02c40881403054034280100c2e08030b101c2014691036003241d8440000210544810412154101c5226801c1000a042440041d180c030b0340280003880080c103044d0240000107498800e00d071040000e0754070385034000043c40e5544202e09255142403416a91030000d9440c02030b046111003658400e503648154040040980e000800081111010194101a4001481c0079010000e0345002c000452146e2150007030948031000d62490f41252003d0341c40448070f416509040c4200100c0c0310862811850920030701031016140c680f031140c1968850343e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 199075863 1250 199074613 199074643
    0x20106150e0114040b0a080c090d0807031e0305071101020304110d020604030c06081819060c030b040207120206060a0f12020609040c020c010201151805090f030c030403020f06040b1209 81
    0x4600810608102801041080c01d6030b0340b00801504c40c01002808d600c40c0d6007075245d1040c40030124000064101024107501030007800c0074906059498002100e41061095840000c0d40e0744042151660b0481035003651540e600c8000c50840c030b03207996040000401c00d401d03a4461001004814115034902c8211806968480000905280c0d80c4001600000096400f0105880d614404580e051800541e040c2c2c00840d810816420085d00d84410004000300125081050344030b03844141075031900d000a0180e60f02c28079802030900c4a5000007810700c807010f45864402c1002500c200900c001c0c41031b102c401e995401d84614807084813840042d142d8443d1007105030b04142011200751180d5004158440000c03001c2c0c00a2010601d101c0e141e60000403540510b0500c0b046140741e69071010b107260701403588044808112410088001c1400380b07550458000e140495100107410700450030301e004900100307203090f9001c1b8101070401000070500d000c1e0a054160711000d550014a02900410003012440001 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 199077113 1250 199075863 199075867
    0x160c0506040e1b1227010903020303040212030a02060115030605091806100602030a0503040c1a070309050a031509050a06110c0c1c020108100e0a0c020c01020106150e0114 75
    0x603054901d680541240d450200e00303e50501c0c103001c003040c10112200302200d492441c1095684003204000c101c01c980020f5032107906070100502c1a8801d208000c04a4085c0d0010740e2645042d20402c0700803016505030511580091007008030150b0006030190644a12004049491912210460050140e40c0c881c541c440422410b214500f819900320b500b0421a80c4291002903903000602c40b6190704034802c000050340108013202a291289002d5504103204112160b10300355100c2c0241e501c0c200004074024084400150303d402c058000031488000e14054a50540c40b07440e5448150800d04000015a90319072204250001c0180038082d00c4020390b071090301008512041100c9071515008911129a03030300c141c1a040c099887e01d031404022404c00b00d00181005005540112130748100504031034485410400c02080452452900034070400000c680002d11840300d0900a2801907440c02c200c0c10769240c41403c0c00340040c041860b503110585404d050745a2030561300101d0300100280c060088503800 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 199078363 1250 199077113 199077119
    0xe010f1e080115020a080f13050a0b09190b03070c111302040807090614060c030706181208160806030a0f05010504050706050408070e1e09011d070b160c050604 70
    0x710354034034181d400f2560860b942c800d0125040c0e03540d1404d40d8020348461002e0001001c1c2000090080c200320071803072107207141c00d556031f004900b1159480e0009040c03c0c1700480e400d00700d07080101d0540a020b4001460204980c50502042d00c2d0b4800645824108040750000f807003440748810602c0b00c1d81c1006005900d072182002c01c2c10001b50018090866540548500054040c840c0d0040f00181c942c41e00056a10850070700407c07126034080300c25441540000c3c2308a8010480c14804d18500000689941200c2001850054254107c10903001e013071051803000d2107990302d8101048600414907043c05140e0351031700e50010f40b52031040c00b001403d010309940d2803010414190015802284510700311044070b500c03040d00360394a0055010742201588218400c112031420784134099007044001211502500500f4882c1c07004840403548000c10303a4654014401c0d00200d01c0101038001120f80c041e040c641e003400440c094034407a00307507044a100c84441d4040180446e0b01e10070402048000c0c0070b156100d507 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 199079613 1250 199078363 199078367
    0x3030f1506160f03020f03180f040e030706060504050f0108031614160f06030b060d05040305070b0a020c0607051305040e0705100801080c0d120c1b06020c1f0e010f1e 73
    0x1c3e01c041140140603086520ba4580c0e4004180d85071190400505044024800b042c010410140315015900c0b6480d80d500c0a95424140700411640e806140c0c0450b003030381000d0602c03060303030009420210102e00d0768004101e40358002c001d6a0702c8401d8606d0250203054a802c2c51000821a0b038a2590700d805249444c4e180c165510527100110b1b070031130030811112669010250704850a035440769402010070012880b00f20181d5010544c03152103800c101d0308081440e11039614000701240e40d018040c1e0300007180d03291170008000c8079600140c145006460300c0c1d0301c165031584000c01445464001c9441d90680050407400b403110301c001d0007001e070070407c0e19005814003c00818081c4200c184501801c0d0620025041a004400d941c94008a010440103444181104d1a9003014800d0f00e240074121442c2950282c4201407500800302d03980102383d031007001410400304440d2000f55802d602c292014000d03101e42c00001050700800d0034203203045e44e00c080d0b80068400003040392008107024032004034007090359 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 199080863 1250 199079613 199079633
    0xb040605090a080c09010e090f030a0309030206060409150c0903080f04031211030322020d050c030106140d0204021606231f1707081c1103030f150616 66
    0x20710450b041404103503079201582d100c001d840c040b40c0e000380c8160014040702c410b80c410650800c51050844907012401300b08541103400050401d000242c6510313100d000d05604000854101d0001c0303030308020001e001c1e5542084a05000300c400803103a01c4685001100f03008022040046801251155032519051b21411881c2c2c494001150500c1e20030190b103403003034030035042c00c40c65669a9008620b992103260b000051a201c4481c000c00c0700172903500c40c0005844181c0c080540078803c400620f07080708084105801e40e80fa54205440144050200c021540e5400e0a801c09464050b1401680d036011640385010100b60002c014003518203020002c0750002ca4003141080150310101520b0144e280d072200300c3c841c0c1082401540c079120000100740030307101c0d13814441d052148880b000c580c4003540c1c81d91854100480c6420103442e41c26843c05040d00355030424450600742c10039001851440c41c250501c07135100000901607416a610004080145490f120107c4141c110580406038409000c0c1c9041a001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 199082113 1250 199080863 199080877
    0xa03080904061a0304030302031314060108190f02041a15030f06010c08120c0d0e010209040606020309060a2304030b06010210181e06060b04031a0c03010306150b040605 74
    0x1c034035040002402aa4078031203110840c442c0743e50640b9585a0b92000c9001e50030190098403104c01c0d054650f40007803a0800f04d101d1030002800030b046a98074100307909003403120180c0c126449101020419000911030107281c495264102d40009810103228940200108014070031500103200480c054000b560302ca01a501c6014114580031166403494011a1000d22440e00107100c4c200a004508925410000e01075108080051084c1025020200041035a07803c036228003103079600240d15184d500703040c051400a41107a000130352602c4403040108070248036183c40d0340100043c45907020800340304074100c06140d0103032010640d10345459040990584d2004c0d1803240c0540704e84101250301d04c1c0780740105200d404040e6aa51100146520703103080c920f401c804c03e04462007a8043d94800940d0314460b03200a400030110560b2120304500c1c0010050801148030082c2100c4c44040010000e8120116030540764401000314120704000c40443d50310080350040b54003808040b9011a0450740038004d0102 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 199083363 1250 199082113 199082119
    0x5030706121503080304060b0111250b07081911010c0e03151603090602070b01060207060206010e090303011818110a0b0304050d2607090f06080603070302130b0a030809 74
    0xd0b100c031191650705244510310000b01058070070b10000b40880c819510444800206050101c46904050402e82c1800340c1c5101d91f241c6403100d414100d2240411800100281040d4900c2503c0c14809031a034180600800b100340400320100ba24811115109038081205c0d03080d0080241300c082c0402001034052501c03a11190301a1056009248641004800ba00c0c01b40296140c004042108488220042c0c0800d65080c1c90301602005040b00188803a40745500a000542c042d180c0c05061080c0242081c00691054411219072410701030184800f100304d0f41101d00000c07400c0d0201c09254540d20160800503210034460303010f0841d040605c003054410300842402103502020180d260000d171190f900007590050510750002d1100c1c004240107003d921002002c0000c40b1111440445e4520902102111004002440381000f0003000f500286181d001d082e00c0c0c00d00b0903c524041c400300351340780e52500c03000c0e00c02e0303184080a054040030b65104140c004000307444000425200d041201035580440f06140c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 199084613 1250 199083363 199083371
    0x60a0803070c1a07030c140a0b01030803010503071205030322050f0115080109030804020402030703091b05030d03020405031c4401060503070302071109040b06090f070905060d060503070612 83
    0x3103181941c00ca844c1550700d503d4a0000303150030348032820110700c070705641030051154145180204685112890007180708004440d52503040100741420800b456125088541c0d01f5040100041c82c040701762640220100009038940c44e2030040d0b841000b000c000c01518500440c5219440c0c0c40040d041050860031003503130301d1816175031020303c90308803155201c000c0d00148201c8003040c010f1425400075038124881d4030700820100c01c542c46400c000c8403105400c05030192003440802c141c1c01c062001d910915084c0c1411402c02d4500b001103a121000400c0b80c2040e90380341e418510205000e9000b10400b541c2d00b00d06004910b41e900d42c484410100003000c4040c0f200e03254915440e8070007484156059030b046540351800c40c4c44500e401d401940181d41d044400c58440b031044c9803140c0f2400c40c1c461151740a810091810b0408405005511a020f8808400040801c003084103003a0072811110031101705076182d907554458080e90100030314168001640c1030051000c009682e5502c15107510300f060160030100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 199085863 1250 199084613 199084649
    0x212070f080106210f0906110705060a110901051b16050f1002031b030c0607030c0e030a1e1b0305030304290703020a03140c03010f0602070806040605060a0803070c 72
    0x1451644a06003132050801d1614241034240785150810881003504050100d14001140c2d110320948900c1c01c1408030006010940340c003440f03020080300e42c0180400d201080710360003001e4810700c40c2c072601e003509060180008280c6071101081945000d48840d40d001e0700c03100c0307048041442501d4014030445125107249040810b441c0741011300c0c0c00c403070190390300110320380060700c2d000c00000d902d441280001c5000138081c000c20200f050050328442c1042d80d4000444447c845c0d070180600010440e8540240d0000c501b010000d1030b4500c0300071918460044000d91200c00f032a00120b4400e00d40e40940324200240310000c00c0120010145014521030b81d801c00c100d212030340350740c090320540320f098241102c07021010511960181d401030041850b90300c0e010450045003003500c1c40108040d60040c55000000004101d03000040d0f2041002d801c5500c064100e0b24603100e402a13132404081c1c0080c110564900c0403405a0f035540d04020028503103403041d2130f02c0c0d11041c1407035100000380344945981b1a844c3c0300c0304 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 199087113 1250 199085863 199085867
    0x40603120f021506010e0a03121205070203090a140a0305010e150723070c09020c0f01060b0903070329070c0201030507030e19050f03070f110d0c031103010212070f080106 75
    0x10001540c03a03e26a40360755941c0200466800490041071174010341048000b1000c00d081c241c401c25050940d0311840d5610030b00b8640a0105d900003042d010440d0418441c510031903030740c0c603011000c1340c4e040e240741f00181050800050008505a000815940c40c24504070380204011840081d00305c00120707054200e68650304160b42081c9000c1d058200003410004450302e5448440c068903c441c02120205007290f2609019800c0780d03c07400504001c0e9000150b0303052400d000f405684e01400018803181d041c0b50005000c20f6480085020040440c155240c3c4410a03000e824807a42c031040c80b0f220b1880c6a4246000b001c2d1405a0300c3c1400ea000a041400103403400c0e00038040d44402042c0c00380100b9605400c8013100910441c004000c403964002c402d41055081b030300304003401034180180c0d0048680700c0341e840d001c41c0341c0c81c20058031401008608900404a0100743c640c0d400c9030303044100101d8600390b10000a0080c0701d0a902002c0303891040060103d040d9000d444201c41d032050751185d101698844000b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 199088363 1250 199087113 199087123
    0xc1c090506041203030f020c06151009090f090b010e1807150509120601140316060905060a0908030d0b13050f061009050307030f0312020313060c0c02040603120f02 72
    0x6400e400400030002041215400c0c902c8500f541d0003032500145803120728000c44140c0e4404080b694180d4042001c0c000940f840000e05442c8000440d11060b41600351000603107104454443c034038413140d60343c68034118000e064220b40c5016070320030420b0b203103981c5482c6510601031064816666414420104d445503410000308803065441c1c200881007000142002121180c3c0615a890380103004402c80e2260107008200c15406400070750b03c4801415009003e0618052074602050000c40091078100201ca4220864a00746c5005a0307503070b566829850420307502159240c0c8900354601c0005a440e109000b50361040d800e003034044500e2040400d44821311001d5620980304862040c4801020a03924504440056400e41250a14002d034940d180006414000340d81e0040d90000800f4159404040d80b14400050402d1100011800d6007803400d0762401000d5201c000815450740e441c08512198013450b81a918141d00800c1448419120f180c00c001c2003140a04d07403004503481d580000180360010603 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 199089613 1250 199088363 199088369
    0x806070f050712120c050c0f031623030316031a010e0112090204090b0403020f0a0317430f270b0c010c200616020709020c1c09 56
    0x41e8190a105a0b81c4a0150300c0700c42402c002c0c1032080006018060003180c1c040c04080d0700c0a911180e48031480400d20509110340d1004154683c0c008114114041c021104036604054000455051001d04410184004011500408641c0c0f0001c420001818400190b5940e0001644d0381440340300800b00c03d00c005c12844114260100e5548480000c4c19485407125150003010104040303000412030b000718044940c1c03a1401d40d24004141c0801c1301b4035030101f0086c0155480c0d00010540010f6a4400070910f00141c080d20014404100104110941030310408180700c0386807244201114a64586a40122005040c46000200311414125a0740515a59440705901e504c0d00329403225a40401100d90410015038201d40c0381e2828040b803041100009000450058800000c030300001c3ca4000c0d1904504002c400300f0702c1580c0d0700610020101141c3d00b038110641c00d0a83e15000803100080e07051000a801803075010b880491482c0600303070001160b03800b111205441121000c000e000440e070892880c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 199090863 1250 199089613 199089617
    0xc1b010f030c050a030b03032101030c0509061c0f0b16030e03030105010f0e030f010507051305030a0812090c100306060e24030a090b01171e190201050d090c0806070f 73
    0x4805413555a0080d001120814801402d482c40c01c0e02c0c03c03a240e4488094424620740985c1c41078018420404d24150030300182000f1515409240780c00400513001c030f0722516186111601c400a620200038040d803548204641c02010303000c0030701c2c0c004030510820310a4807040d0006820032504144006000c01224140c50040e550b00d4139415a028040d203a0703014020202e60140309246040c1c0d6456401e1081901440460740c0b101d5444003026894600d4240c0e58111501c00e0704403109100018086c001140c040154280c0c5001707107aa1001c24490916600a140315042104915580c00c00d80d07255002000303941680e1208103002c07807554140090742c02e144018600051007600d08607214400c50001c0d552003503400307001041c2c010265907455500c0c0380aa010000d0000c840e0140030310020180000700c080d81d5184510582e0102c01899a95205013070500c4a541c22803009296065922500c1103441420240c101441121128a800c1d005091148904511409408082040705100b00c60040720403d0395 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 199092113 1250 199090863 199090867
    0x221060d050618030c0303010b0403030f140406031d010c0201050613180204091e1115030609012705090a030f0203070b1909020d14190206030a020307050c1b010f030c05 74
    0xb2090100302c0c00c0384030440b00c180e03c41440204140c0c20104011f42c007034058007003096112461850054030300c1c600402c218061003a42d8180d240741c42902c2c2e05440813907803140b401040401c05c91810004402ca1549521619401c00c0656031250f901500818061f003000d075034000244008849000031180e45c40780110582807221405c10141c80c05420007444140100801e2520250150504085581540c400c4620001d000d030260490300e021903812410302810126140b80d480c00f100002d2861505010303d00055050b191110101c4010102110602803107200c10005e038100340c5500f640d0f42d00c2c00da100b2400140201e10181c1d68520100039220340070b506c04403480c003589036030505000c0801e038802c00385859175036401d9000c0540d8500240010f120b010386c030202900f80c0c41240f410708001c03540da0320142586590b07460b0f40c01030b25140200c992109042400685076120800e040b5840c2c881c6004c001c2c00c5114010900240540340000d40c0800c1100362a4040c03220900720096044d0b4071100414400304900b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 199093363 1250 199092113 199092121
    0x90c0f0f03030909010e010510140703031a030a0804090501050315040b0919150e03090109050111070b0c070f060c080307031d0111040905180c130209040221060d0506 73
    0x120311000d0440c0140107003960f060800c203501180041500741c6c40402e0801da5080100a9820101030388040d000c2035290031140c0440c40107c0324001d100c0e110006081641c2c034030302e5a032044404c41042207000d0000301030720f080d84081e0070020650782190040c030344c3c654581400010031f4a0000b84103d04d011120029044075500ca444600c4011002841d026041c018264108201d5120f0391404c0c00d0303944507854a104460080d10600c007299954212260f00b584100320b003d03801ea800106407421a0004d01e481c02001c40028083c600f0a51668851945810042103d41001e9000324482043e40c4540174007040490703840208030b841c0b440340000680300f2041040480d412a22982200500f42d08204000c8110004111054210f0300d000e81034113404c41006c18203001d00546c60040740e410041300d074952091010040c44194460030000041d520698208480c40d50340c0b4429016946401c8006104540b5201004650341150100154402c41d07031030120b0000d0041d25280c0d0803407203804d41040040c202965 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 199094613 1250 199093363 199093369
    0x2120112050a020a03080c0d0905130903030b04060306021909030b0a0e15090601090e0307021e22020307092909030a060203240108090303160908030a080609090c0f 72
    0x50180320a075168000d010407107016884040580005611520341e0b59900c100d0284074904001025181600300458076004202982d078080719544803802004000a00d01c0d000d1a00f039005000d01800c07039410604103140001480b00700c7d800340c0880c404074460074000100034503044038030f0031082c08010110f111010200ea00a4150381c45402400c48040c12500080e180320400180700701d00311121041a40210018400d00f88c4d2406030f00003a8400740300660800b043d581c001048107081d901e280000d6020740c154104190380b154103444464091400d90300c44668070003207002c040d42c000c46085001c2020204c0024800c081206114040e03800010110352040e100c24080269601100300c117035151080d294040080303081840154010f40e59031020701d07056088485444200c030b200520301030501c100c8108201c00c9400c04011a40d0203c3c440740d0741d59411400803010364140034180c015070150b10000c9114005507801034001e6000b90b0085403443d6143d40c40030202c1d03580d03281508503503400c140f080c4100900b9003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 199095863 1250 199094613 199094639
    0x61f0f033303052e11091804020a05060a0203071203110c1b10171b0408070509010b030403080103060c050d050f071202090f0609041409060a0b0108010f0b03130803010b0715021201 79
    0x4600a140030301c0d200d548000601f541c0002e110100800701d942d0300b84011841c21502410041000f51113041c2003803000480a92a8020200c000d00078005801030003050902c02e42c80502c0c01d806500e00c42d0f0702ca56148915595030100c0c00781d100c6082a0403c00f1110138504141c2c01000035500d42d1310041c0010000c6001c8500c048090043c04009000d00c1903111080229030241014021400013015140c1c50002000030030b08040e03200c40a03001080040c0400319030710004290549802140215450a020074111881c0c41010480e91140e071410081c030440445003542c09029131304583d03524150380b0202c64804101e214008860383d00a0324102d58410300e091101c040d004105004200188600000c8001d0410706011a12500507410000400040032454492041441c1c000c0c0b074004002d41c1820541c3c0c01c40041802907440200010002442c0c0c006800300d1881032a40c0101d242c0e4903541d4601ca03100072600401d5040340c20000e460760b0044185454800d90b024110720207150507080e468000032078102 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 199097113 1250 199095863 199095881
    0x31406090c0a091809030201110a09050909030903190201030e0c1e031009050307051e070b09040e07030506010f080102070804090e0709020a0206061f0f033303052e 72
    0xc441d4500340040e0545041d1010304100744c05600c040707800102450001c0c02c503000d22946a00c0300906111202107503500001c40c0342603c0e0103840032602912250f00c050320b10300030700c01034035418401e0700c02e81d4207454041c2c14010754aa200f0380b0b0900051802c2241d46403581c15507561140c100003c180089030500300231850700316250000c1c003503d081e5a031800d1741030f0075141c1d101c00646096000003855010040304020540000d403010034807031802c107501481c0584549191060704200040840da9025664035644000c01132010441103c000075945d02d0100d45408092060b10792259019000189900041c022200350a6215184614150414004800920140d607115040303104500c008140d400443c402041e1401480d00100810b2070880300304091010800c45402a0107240c0003001506a000345001142c0011810f02142001140540c00b40001103410440759030708100390046146041508410140c90060040e6120520300c05280d0076520709031040c2e03c0e0b61140e10b14403074a581e1050360040c400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 199098363 1250 199097113 199097117
    0xd020606100e0a031b060914010525120806010c110411040b03090115060f050d0b01050906040b070516030308040b0910020d05090f070f0302060309030705010207050a03031406090c0a 80
    0x18500e03107400462030883d019042200e0000e214480c808181d00e034041010001c080c5e034070700640c2c0581001000d50072161558201c44c18030100ac12801190f0501e41800c521000502d09070b070300b8000c40d40c244030142d6007111551001089110001c6141d03944110103456025800c102d0724182512032900744001020f902c540501580410b0101103000031105c00154080c101080c000300b1505801c01307040c20446201d90081c41480f45212400c40400d41050945a000645034000200140c3c1e040050300e05108030b45800e68010780006000c1090f0780d40790042c0c99a58001e50459003490f103400c03140c40c40d00c8039500015000c250514005000254820002c0c0e5100c5258001d4450b007100501304070082e6040756045840a546501c104540820300300480e1001114090041444514000c03040a00200501000c7d00030f0380c0000002e0803121040003103c006c1c82d48240219680c1c20300e41429620382c103440b4001ca00107410410321160110150321064014440140440300f141c5a01c2804000c6a20010780c0e042 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 199099613 1250 199098363 199098377
    0x51605070504050910050c130332032203020f1201020f040f0303121506031802100221030705030708040f0204050c0408070602060f0105011b05030301060c140d02060610 74
    0x7401e4685000d01405070300d44100a0605020600c140015180000c02a00c2d060405101c000740703038020280901c2c03c490f04042d4044081e2902c2d803100b82445007021030720458800c0010806514880080100170003200c13000000010f4280495540c41c1441d18480a940411822130b03010f62450b140c00f0f0308442c0f81280f0001850000301541e1400c20b900140c0c0720440305000404c0c00c00605820040c13a46007071100c0f40041110302c801c0c88203a000385445000d0704040541e80e0859070f40a0540070002c042294001f844601900d10b88000250741c0c03040c0324044018006298107a044a1030043e05882c012141d03138807141d046507220441100c0310400100203440d40c0545910745005a00c461003001d004407100a2625581c03401d10b00443d02c1d11445600480465200c0e03010000c410412464060664409283c1681c50b08000c0404044040820070003602c140000800014682d400030095010a03101b6000342c0014a0321100150312240031100b294003582102d4001541841c00080324154100340b030400e1a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 199100719 1106 199099613 199099619
    0x305010f0b040b0d1b05192603030402090c190c110f0109050603060301020f0d0b030d0504210836090118050903160501020901030605060a05160507 65
    0x9000e600300b081c0900070300d5000881020003400d0007072001869084840081180c149907108e0800d05014a58003101440d202c904041041d4980001940c00e656894003840f13090705000388440c010b800d00b0881e002c039404002e40d120102444956880040c1c140c10310b498050140240501407080701010b2041c05640e901690040c1580e40c01c0d034401340c80745c8421002c030703029000780105a00048070100d440f0032940880d81c41710341d440c02c044007180d4001840640a44030b83c4030f01e015a00c240c0c0001c0e2041c54012591080351140c5510522180b407030446030020b50604406203940c0b40602c5404082550500c120456040c80c110f80111007811041d45040f8001d091460801c8040c50002d840e400001c42d012824000e030ba4005141361840124401f141c50018001d40c005420a40400c1c5031040200d1030342440300549242402030745a0a140c160f401b0300990b42d540c00060200c0c0e581c801c0d101d000c = true := by decide +kernel

theorem cover : BRFrame.Cov 198920863 199100719 := by
  have h0 := BRFrame.cov_init 198920863
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198920863 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 198920863 ≤ n) (h2 : n < 199100719) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
