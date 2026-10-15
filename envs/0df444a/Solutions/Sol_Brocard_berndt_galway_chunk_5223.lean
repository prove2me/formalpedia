-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5223
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:09:16.786048+00:00
-- url     : https://prove2.me/submissions/5135ae90-feab-4ddb-8a05-41efa91a3164

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 939208633 ≤ n < 939388489 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 939209883 1250 939208633 939208649
    0x2030c0106060503091b120d0801081207030503160216151202040522060302150901030e01091515121101081e04110111070b1c060305070302010f120c0801 68
    0x1554490350100c40341c2c402502c0f171000e2644845c124105401441810181484000305116134168400d0003050511964400030704c041000c805c0104443e1005000c413040c0c44580900b41860811190740141c40e50002505030003040d40b412101805043c0200480400401c5406402c801c3c01d0780c0e4101e03031030343e0203032200008006200c146402c920526503000352000d540c0020b04e40741201c0c0100b4600d070008801191076504151f190070000001d40c035020240940b81280e00151651680f804d000942540c011443c40c0300345070b1421000e42c0200304403014055007413004450114100290444114441074030350840906180c1c10b40d008800c0016484900c1491842a00c4000c15a95582c2c024485001800c0540d80800746080c00100002d103036000d00c200710903050511250405030365140c0ca1501d04150400c0c18404400984001c00c1d60012800181c4810511014091582995174181d1980710b6440003c0c1800342c9884100030890084001400c44403100c83c0400000d0900400100001d00a1041d46a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 939211133 1250 939209883 939209891
    0xa170c0604052802180c130801090b0112030c0605060a030219060905030604030f142506051503070e060612130b0a02070b070f050d06030305030f0609060108011215090302030c01 78
    0x6a41006207588050b83e80c000308540b001402d0112402d40e000340040803c01c103850704200c00090f140a454035100540356110001461111602c6c049100c0742041c0c20250080c240050058000703075202c50000c22103944502c0228217034070745901080354042ca03508025400040f80d010151710700080c01d00001211940e5440c101030960320070900d0340364903003654081c00041e0ba44440d40d900a001d280b540c803910140071007091500603c07208140000e80d0306441003603128032007440d01c8244501030242360b80240003003400d00100b1741d2503000070341e8601c41486071950840510000400542d80c00c415507491135201da60b50152483d0a1075821001420440c04643c008180c0011a07405102031007681c1841b503000c1c580b9600c945583c44141c410f00f200000381310030401c003004664040700c7c00340201c0c00250b1094a0380c584030f00b010b1440303081c0703104024026400381208108000ca0b607a0b00495150454209040d0f02c600c42d20b01d070609818946039849910035250070300ba041000c00d40e000006111442c07000000700 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 939212383 1250 939211133 939211183
    0x9020702130b060304080c161502010605031212062106040c0b091c020f030f03040e01080118030507110d140c030c03071503020d06060e0a15020a170c060405 69
    0x100445030b410203a940c0040c0f09100040001c0c0a075001014070070449805c03584901c1a1004034401044941c020108a41c50a1220b03a2199024020a80981800c80142143c2d444242c204034560003040803001410342c0301004100903440c3d564548421140c146000c41c417103542c200381c01703680ea02c1c180e9040b00d4407408090300190510780700060b210091030041480c4840c2002e040e603444080041002641c0c440c90b920700307a00d841d5608120754100311181c180035503103c600d040139200050700140c0c091040c60741040501c201c0c0c9050405c0090380190300d8207229864168070705000842010b041e0005400a5203a0705040504c500c20308008900b030301005c112000d2405000501d6112036041d0310094159005400c24411502880301c442e8061529140060610285242c58005ea4950341d02c50008201c0340800074035681805002d60028ac00060b8200780200c510f00c40007540c44003854000750801c40c403c40396041e02c1d40148120b4401d6140c0b10200e55040c203040c1081500c0d540c0f200904e00605203555004 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 939213633 1250 939212383 939212419
    0x3020d0f0f09021f080402040228230705032d0c0705211b0d0b010312090e0103030813021203070b01050f030a0b0c28020609012a2709020702 62
    0x400030704c401694a00f8842e8440d607003404003030341150440300401210004048404c0e9811880e01d8042c10303141c0d8a004144080007031444010000c020345000d401e408012901c081200007088521400d0020618100c0020b440304604d40c001002241000c07081e40081c0000040400180d2801510801c4802c40700d4400700b0480b60ba500306c0c03004c0c203a45d81ca80140c400c14450000c0301070540410344002c0c6c5120482c490507581d100603513000b40c000300c4a140e180744261144540c0100c0c4100544050141400e1650446d200580941c1c030051000d540e0710156075080703045481720840c510035090b440003140e4641a140c54116400d41d02406a02c0c061840003030160810310b00002d080000581202019586440d80c9201c03080319400320640000311103031117024101e02051074070a0307803041120f94050001e904100c03541c01d007503406107000c000050280300300c0c40365040400701780081942c0150400b0100c200d03190704030214450340c1b481082d15501e004180004d944410360020f043c0c0c035100300d0f41c0b20582e2220b0184 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 939214883 1250 939213633 939213679
    0x8010c0903020d0b0405010b0a0308070c050d0b13050c060a03050f0a0209060403060b040e15011a0a0f0c0c03050f03041d0c07080304110901090207140c0303030703020d0f0f0902 78
    0x1019520560f031801040104000820f0950441e000d800081500103020001c25080421648200d80717000c4001101418882858024006401d084403555140f5040da100c1c3c69442001070201441810580e2603502000000c1083c1014000050000380d240c80000c98050003c020895601c03c9500d0341900003010310000e807086490140c0010681406c4c1030560300e03010010180001e419800a0355540140e96a03242048081400c1440c9480304d070142d810102151889610741d10301684800c410f015130110315030000600c41c903080707080c8ac0c40d62080703145080070f01444e000796002501602480c210300f218440040700900aa981d0385080140a0500c0c0c00c448591460844440400000c00d10040e00013a01e038400642e0854020581d0108000030100010000702c4281d0009002d01da001540c0c40801c141168072041e441043d078042d00d400403d007008070340c40b4440104134008040e40054691140c82d01940041000c01040b0700800c00f040380e001d0804010a50440c0503072152400c26404501560f1890f9 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 939216133 1250 939214883 939214889
    0x30902150318070320010c060908090a0b03062202131e0e0108060714042d08030313060b0d240e0d050a18030506040605160e150a09050a0e0108010c09 66
    0x40c51708294611840540c6189408500080c1045a082010b0000c04c459000d070845c1c03a8020614035540701400002c012010110f5401001d08a800b842000502e0380d50340c0a1000011031180007105802050100500038031504070301004450300e0607404242110b1845c00e00c202c0d49100301944d000f26031074403102d0780707007200034400c1070400c3e071002000481c058447ea0f0100c0a4400e043d002c10704081d203a0311491b04110724216840e1200e2503010b0444002c8403181e0b200001060070300d010350320310304203090900003d80442001a00740c0d0384070307021070041da1210b0f00d94400607034100300130046102d104c40e544c1010940c68580300f058a81014072044942e800495024040302c4251103c0d858809101829903411860484081c02a940410000046103047c0005842288201d000160b82d103403600c580414107071120184820411120780d80441a00c3c2c01c184060352861405004c3d8481000c1c1034112201000d50f000103411051440000902c200382c100d1450507640340358000d21040d40c1e9003000301c50000440c4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 939217383 1250 939216133 939216143
    0x1503011104050f120f0c03060627040c0801020f04030605070306060906080408073306060905011d0307060c110405061804031e02030403210e100309021503180703 71
    0xc120a240021030280ca0b058003400059003d6413084881c1e08200410201941503000302624440b5403500380889913000c2c40884012880f01c141e001d011460380311400b44249a500c819010800780180032654074024825600295030701c04004080000903049840201c4000c6c1c01c150101c0c00c0d0031b01a000d140152503036035a54010807481d015007190f850001901c1074451039001c108041c00300b000c0030381c5c9100c103c40b0b10078542d9100d4032850300356440000121004041c1490310a060203030962210242c01100d030709103030810144251050310018036018040940d814402da280004405070049401240c10780151000282c4111400600054940c01c076080780d17001e103034510280305036410307651807a40190107480d03d101490400502c4029542a0444200141c0d01c041010420045102e035280111120305010a10070480e0700c5000d00300c1d405412040c5c1c400e46c00c0181e6029510712075032204404c96001402c20901c401c2e000150b02e540d6100350354595411140004800804174000380e5103003126480 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 939218633 1250 939217383 939217387
    0x606031d0a080f0d090309170f0d180504020706390f0309020909160b040b0906091c150b0108090d11192009010f0e040f06090b15030111 60
    0x103540c903284039900c14030043c1c024a506208410408505108030181c2502c261079a00760541098480c001c444d0101070385246039401008100e020f10170109485480e449181440d25400703041000190b0700001e03540081740c00610114058090003a180c20001c803200081c26500d0b1094002d04030742d00c4c5460360304020b40080a17261200b1428a2040c6500d02078042c55280020b0b041c0120380c000341c034500c0207030307030054996118824400c5080014425030009101d2070b000e440ca0070346003164a88880c0148040c84e8401c10000c288444543c4500308a514600d0784a00944070200369898103240c050504100f80c1985440c1c045000d1103540981c4441d401080c000000b0940c070202103504503895800d801c0020420b0140e4144242c0203d01c010301030811521407408215460461403403201e00c3c042d034824851041c02070000420500700058490b409070742c0ba2400c009800e541d1070034584808512004010069483e05040d00280030170003820380e02030380d00c40c10880703058000d24040600340ca5505003481c07068282 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 939219883 1250 939218633 939218653
    0x100b12011b091d190e0d09030201180515070206040f0b0a1404060e04090213180b10030803130305040e07030b03010b0603061507020a081c02150f04080306010309150606031d 76
    0xa580782c4003ca120303460005c100c0c1114444a242400f890360160808220121010300841d03070000b0002c600001c4000780c0010452031305001464250000c40300660500d0f00061050035900e40404480203000146d03251008a41d68042c00d030a25801304444000041007107403030f5081260f040007154101c0f6500d40d50340e510104040208030003810780c0501243c2c40060241d1500c4240028083c1440c607a02d1050485500032040c14010040440200354002c40d5007181c6041c00020b81c0002030700c1d044030309079000700124811854103680501c00c5421010750607043c4d1003000007059240c0c0059900550580007801140f52140c00e0021a000507a15685d03c00912001d082288076103034050444a0700080050081c15602c6010504000444810407009030720460000401c980401c501108240d100264032150319000780101c110b0400944010402c01300003011032090381c801c2d00b000e000365412803142054205986000001080d4510405c00030a0801c224042c0203c0d51301e40018007800b034040508103a00c9 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 939221133 1250 939219883 939219901
    0x201051905090c130b0a1406030c1309050c0a0210060f0501050702060405062d0304080a08060d0b0a0c030e0307080901050901090914061c0302100b12011b091d 70
    0x700080003100c10f885044050421030b9110700600049450300c050014440903d0414441410b8803a00014400640b41c0c0407052075848240449234031000000e203103601c45180030710303807038010003203074000300d1141d04207403c2c0100c400114008000303203607154003241c0c40030b20341d680e16200340d40c507921440802c10005030b820469540074000420841d440184250725142d1250002003245d04510180c010a82c00d00d01088451000030f10501c0b110158007038034a0075031600e581c401180307215640c0b0b40c508200340c040110700701d5102c09000010040e40803070b16103533a10b0046012030080006201e42000a400d25612040c0240084221050240c0140241d4074259000c00103603459407120382d09074100061100001000a441d10070040540b1292112010900340ba00030490440d929148441e10a403c606943d00006d80001d480f21b640c50f29180041020090700300040c80c00812800100042d50070200850b40380240024031403410b041540302c030107060391280d41d02c0e0503480c071600907000425105001304403210 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 939222383 1250 939221133 939221141
    0x80d02070e1f171e07170307170f16120f0e0a030803150a0602030c0d05160212120a050904050c0f0703081003061109100809031819030b1602010519 65
    0x401c4880494021a20800c0f0081900203035a902404c190041241031064450707801c0340644a074140e0f002582080c2080d00d598942005c225400a122880000d401c41c9587c0c4200c16107445940e00031141c0c51100450901c411481c030034003400e400182020323400304451400b642c056540391002515180314641166a840c44950002e0030303a801141401c1c1004003250745051541000c2c4c4060382c050354940084422451620080d00b1a0509101d800d200c10242482c99401580710aa0100e83e0300703051030240440c090401039880c2910a2400300025001100b90300a001001c411074107032130810099840b03005180071800340c2e002d001012102080f8440c0824411900a07421005058000240079900d98844048581015001c038a4001c04282a080b0f8035004000320740355012800d1804852824181c0d1603160b01c1585070068819020340e40c0a45c0e1602ea90000442c0800200d08042646880e414030b42510041140d0b0707035024601e54440350054074410300490740504d00c0c4440f4082c041c500401c2c0d02000e0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 939223633 1250 939222383 939222419
    0x90309060d061a0d060b120601031d0111180303090303270d120e0909031603030b0a0905010314010b1309081603031a040905030919080d02070e1f 64
    0x252681c0303010404166002c420f040b03200c06940c0c8190b07980c04841c125416607400e80c3c0720705030a80d03060040c2a034109800e40d22950005092070b00003080d0140b00a0b141c010318107515142c200d980703041e40d80c0e0070310301101c001000000200c0d54082420250401050b945e4440d540f0b000d41c0603041800318109001c06a0210000c202c00781c40482c0e490204400410111601c40c5010ba5221a00e40f004855207a04031200b01000ea03000d1781e107443e091400c0752201c1c1d928815203180244244070004401c0038540300342d2103106010340c014001c0680303d907a1000040604000c0c00240d03583c504641e02e401101c01d0504c112012020058805800c0000300d2040f0001411183c906940c6c0346420424031000096001807003610900c2903c001944a0681d40c94203800745003220300a000301d203840b92280102e5070000981d0f10140c001c41c2c900c0b0312a61061684540a1842d6100303900501c50b5145184002e42c000c44c249068401046410a07250345000a00443c200301000030052024078600503c540c0500014103884 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 939224883 1250 939223633 939223657
    0xc0402041d040c03060509011a030109020d0212030904020708120105180402090c040b0a02070e01170604150b1314070306051014090d14060c0a0f1803020d06090b010504020309030906 80
    0xc544c0d0b6124901610005c030780195550b5580e5101c4036031002803180c1c1c0240083d09030000c00400380d056003c02d03ea0050b0545c040e1040c981040b5640d41c000c0c041048030031b4104040d000b0340d1182d845140941c801d4102114102c010300d00c102c00800d084c102841d103900009680702c0f0601207520f8a03004e01c1b070700c0381c8050038240d5415010000407030301000080003001e01441c6c0380e000301102c0349000c01c41c60281b80180c02407103011010410148907250006138440e0015001b5181102c400401510306d03008200400e44c49410500c1510083c652060580c0310710194040300008040d45c0d901c1c00c1044003203d805010303107036200800704102c4000343e00c14013403400414480c4c0c80c1180f4009888001450120341c2c0340b42110350b046e802100e80e4441c2000d04c42c031a000400c101c041410004440d9029200c0c0744025015410000071000114032101c503243d04400950b0060800d07840c00e00c280c18142d000d0102d07001d082d120241c03000000941070a2a00c00c413482012000d01031401c01c4108c20070013200d640041c0390461 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 939226133 1250 939224883 939224903
    0xf020102030d02030711010b0108061e120607320a03020304020307030b1609050f1c03091d010602010510320a0609080f010203070c0210020a150209030c0402041d04 72
    0x59080b203070720045008032641c1e25109180400d1451150964814100c002e040041e00801d005c06502c03881c0a41c1084210220b49002800144020641235810101c04170b04500c50001480703aa1500310250002c103240d0003003442c000c035942c840140990760719840300b800c00345400c01c41502024400d41c05503411900c01400da440040d600d45400d040c03a01c050311511003030800000300344c10b00340d00325403180c0c0140001c0d5400500d8004100000d2110f28214050006002c08440c540c03003010701c00d01d603c2018090300418072400c3c0c41d0302c5010386c0d902e4800340038080147d0701e0a00403035041c0941e40f6890089900340c3c640c400101c000c50480d040071007056044c004180c1c0c41c0080f01042c0d07560342c0190001400c00c036518035820501d4190071034034141240c0130004550b441042440002e0340c0c400030682c125a01600d03030000c401140b100403441c020900c4805132171586c17404c9402d104007200f5002015801d01c11400c940540b82144c0c2000101d100301e00c510b0702d0040c501c01c503504690b441c1c0c00100364018041c0c00401 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 939227383 1250 939226133 939226147
    0xc0f0c032d1c0f02070515070f0b0c071a060310020c0c0303161b0806040201141c1b050406051611180a0513150e1c0e0306090f0a0f02010203 62
    0x242c6050700c00451040c0c040002480310720100d07801400520340c401e1a00c014038010b031070440800c02c2d95503000c080d0080c00304000f44202c02e003c00c020708804500e070f010003588540c0c600100001900d4200b40030403244416032100c41c00459502c011040d0156100501501203001070a40c40402544800c0201c040341c0110381500803d0750f03003400a41080203c100c1041492005481c1c200003a0340307645410509004c00c184240101c040c0001c2641d809a03080c24500108089082100341c5401064200390280118845903501c051413a000070b0203002c680380904000111110095406000d40c2c0107890001e60140700d400310b5200a04080381d00749000f816407501040340c407804500700300c0d800000d24081609401c10b0001c0150248201a404500800406405411541d40b40d880c50000c2c00051210f030f85a850301403000e90309001c04030355003002c0031008a12118261014001d1690414800c3c4280107500002d8000003000c103031080d445205001418800c00c00e07660380519214840000c1c1e0452005200c44 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 939228633 1250 939227383 939227473
    0x30807110f070806090708160603020a0513031104050c18090c070204140709060c030e100921050609010c0807110703050624040e0c01030f020c060109020c0f0c03 71
    0x40d8050f05815002e010103140c40580c1c0d030b01d440826800741d00030b5481400784020700c40418504a00f5180b580c64090b0743d542d15110112182d00079000a242c0d040c8100b4800410007102001448080302d050300c00380305580d21040210140d000302162008151300c00780c900020791900051580e8001c0441040c035040070040d40201d4101d4140c141c108141c003405905000c02550465410402004c0c0c91034022040782507a07900400800344500c0303032409210740d080d11149840c05400c09e00c01a1181011888285843c0ca181d100d00000441066a460143d0000309480d000c041c040d4030700f190080c4e2241d0016440d080c004a50282000003254028014480e011000130f00611000e030043d00204408151281000c03803581003c94029817240c49030340341a542c0d0a0692000c42e80108030002401d000602180c88201e800284c1305808010066000b04000411210720b59400741101c201d100c2e0494040740e5940c0c40843c0d80700300000c05264554840009030b80122043c03443c0203a228241c0c1c001c050401140581 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 939229883 1250 939228633 939228643
    0x11031b22090b01031704271d070906090506060a230301030b1504020c0c04020a030b0303070b1e13080307110a030c02121603080c0a15060513050103030807110f 70
    0x8201e901c1d62042d8010818410000001c200e0010884010343c54281350101c06a2840e480594010000c446c910603840d41380243d41c494181d039001600d203400d40150b0b0741c29494440409000e8140f0345850031a01180301c0320588526441000064219454a0088241541d08400041c00401c40e003618a000740401e03c09100518000d41c462002207219003000513a581110014001c13442c000d501c18451444019800036004d03407403800907640140e489804101c118003611913280d1540d0140310008800081080c65000703148202000304405580420900c0c104281100607603012210588601c140c802103200c1400658004d2102d00b061100010005901070404031084010760200300c2000841d415424080601c003022011100544562034214280d441c000003180009040600c000c2044a0141c808008040783e51790005015210b103002121148060100c0e8090140503060761000c1142440044c040c00c0d050f203034036481d001020f0351440300c02c44004004440b545104e2081d02d64105010006001c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 939231133 1250 939229883 939229901
    0x507020d052b020114041a15041e0b030a0305031902070c0902070510151e0b030903030a0f0527010902060c0a03110a03090b0a03060812040311031b22 66
    0x9030803500d461540c0081d0031207401c140c110f0a80f1007400204400210303016480300341f106854070341e00e403240c4900c4e00e421401c152000314650001c0c88d100188032084080b03003801800c01411074003400041c40e0101490f40b40d03c1c0b0141c0040100754140041a9810340000c1c0403001c80d510088010305014090300c40e40881d0943c1d40c4443c030b0850780045d40c242404424049a03075a284a0501070180c8840042c0b003804503e00c9105544042d490007000486c1c242070008040e00610f0404a15a241c0c1040001c0c56142c0e070040d04d140d01789030314001503a002c0c290f4031300601d44140400018244110105410400800c0340ca5508159a55841a802005a8410024120403140c8a0080c00e44803442c1c42c019182403030614004586a20142c2100c1c00a41e00c558160203079400341070705680301c0c8001d00741035003d81050780001e84180161013282c04485038400180007228098916545080d103828103040e03e03484280b1080c5480d81e0240c0c00505107003084c0720060221100940c406440304d248050440807198048 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 939232383 1250 939231133 939231193
    0x9040609060306051e011206020f040e01150906021b01180b0a110102040506030a020906070c0e071e0207030303020f1632060a0c0c0506250f0507020d05 67
    0x44010b0040c8900c40c40740d180d00c44460304075669003460405150401d10014413605040300e18041c000701c1003206640544d03c0e4202c1081c0f140b0b46650300c0d890b01101002d403d0141700116030001622a542d82d100c0c814600854441c0d0f006040845204842440c400080754400c9050090003d42018407075400040f1000410100440396100d03038865a0003825900c03400044c00c416801803105000c0c0c0d0b40c0e410100c98000c4802d4000603514070301200400c01c1030180c4800905400c40d84000041e070190341d071142030300c102c0440d50703964000b00d2840200620352071040d81010060740101410f000003030003a4002c000d031030344a684040c10603211100d0684507051812044a044016401c245108204001c0f92000346000c00b42035041e00199100322603a07280000d061403102601c90707400a9071180241160000c2ea82c01c0025500a450150b041c15090084081a40345203500030300c07089009849500003029a80142e0ba800e85082182c0d004c00c001000c20540c1503a90b40038240d400f8015503204030090350014650 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 939233633 1250 939232383 939232391
    0x150d050d09060e040204140913081201030b070c1a040302100f0b030f0304150c0804050a031b050316062007120302010516050f0d060b030901020c010e0c0a030b0c09040609 75
    0x4a40024911990943c1d4103004d01d00501007884184802010a2120744040e286480d003507a0b120f080e51a518140f41c0050080b80b800100036400e00300280002d81078a0280081400f02c2d100c3c0c10044405004903070000c1c220044441010949a0b5480040b580203030192040350300c6010004210710459405141480490742d80d42c1c140c508070305081c844540d0078403500c006541002c1c9008890701140d4103a80310a02000204810300c02000b049000382c9001c1c210190810107560713260f240001400c0c4094040040703c1540210000f054600000c0c0c11a2800c0b0381290341803210301d0010281e80c19402d007116540350250198a0f104007a104014000c01802030b0f580c44c01400c40c407410003a0031101c000d00740d12401480e00781d0880042d40c108046400500c071242d290307540e071010303401c45030002c121a400184c00443c00000b48920018150041c000c881d29038802040500410743c0c10581e82c6544090a0340c000c1140d04003000031540c0120302d00e62001c400441146841c6480c4002130888006802103c1b0300ca540d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 939234883 1250 939233633 939233639
    0x140a05090c1c0f09230c060c0709020409060905180d0c140a0b18010204061d271609081005100806070519020309030c1005090a0b0304020f1503150d050d09 68
    0xe80754215940c45d0300c40900043c41c0c2c03c0c00c12500ea00f0044042409400d00268201031164100f000c0030080c64a000119100d5445d0910079018004c24459014514182008103000d00e54182600c8901c9451400501c84843c003118142c1e079100168400380c1c0d08441e45000c0c54520101408094040d40c813502890689240003480742d80454040e003c0c0c40c107a41c0c13043c070041c01030303940106c4402075030b02454800c0c3d02d094a00c41d0000fa014103807285082e0b540d02000e010000c201007c1c1d05020700400d00540300c6103c00d250382c4011200b07003d29100e9040541c0c40450300403003c9120394462130b000154120640000c03501c4400103450200182d4403000022400160b441e8484c6804d84099180826480075514044040c030000b0b80d244200104540f050b040c0009424042e03004800301c60640d2000307020188103503642d05032050a074008540076070282e00e001c180f65009180c0080481c0180341d8100c0c2d01401e5884110f04610840d140c01002e9800c810080040c0c0c012460400079800c91000313030340d10000c038182 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 939236133 1250 939234883 939234893
    0x90a0210020d090e0402130c030506010201060801090305040306181709030c1804140304050a0807030b070302040303201e0c011d06040905131b140a05090c1c0f09 71
    0x5019105030841d0412a03510070010341c0010050110794070f80ea10b0354819200c0b400061442c81540801017003051a01700d00e4000355802d40c0000b413003000260020800141d40d5043c041c00c1c0c4014200040019000f00310510004800782d20001a92000c45110018100ba41e40d5061280d4401da60304030084001103200303552481c2c01c02020b00124410768030320011019400e501c068a00c0702520060001250184490340083c00b0401c0d24010300c0002c2c082050241d484003003603181c042500061715100490000601c540b07020b4000c03103007102d505030344403240746d821244540782c01242c40000202e14059200400d0074030b00d00381c031503061041d00d03140074010120303a0034009015801d0060010400392481840c01038650b0700c1c0000d440440d6880000031900d42d6603200c030185181d808800040020303002c264041e05908100c003400c0305880711741c3c01400310503241004104403070050b0310401c0d6110800074009505041d00c2c60141c000c200c4481500160f00034240c9000c0260b40d91031595200145c1c1c0d607080c1d201401717 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 939237383 1250 939236133 939236149
    0x1050a150305042a17010621060e12041a0301060e1201020d090b090c0406031e020a03020901032f100311090904050d020c010e06120c0408010f0209090121060b0a0905090a02 76
    0x19048007c011092900c40c200c00485ca80307030810000c500c014030b01070080c007110340c05c1140a04988000d8545404d540c40c0d90350704c5500725004454414028400e14880c0317a40e800101d0303050fa009506d4030300d801c07900c11017000985418081e258009540a10483e8400305882c041c05085910440003540c0310b107031041e2010b260455030301c0314901c03860410500300003151540d400003480e181c0041c4080e18200a0303002040440d40b03650320080d00140c0c000c0c000014000440105c00440654052500c2c0d503500712806c0742c80c1c14190380e49035540100068000d0040302d00075404100c0029804620f207007091694000244000b5046070281e40e0742c0c0016800c601c5090b07042c86500c3c0ca4030024200019808103e00204e012070003803c8034082da05032803501240225820509a5004000d010001d001040c6003034000006900116103050284018000106441c031200002900c0d890b40d10344180568400da03156180948200b030402c1d0b801c0703c2421400700b10b0410038007400388200422402040a0f46240c418400c0c0b407 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 939238633 1250 939237383 939237419
    0xf021c080f18030a0b1503070506041e1715190c0e0102011b0806060c0a0f05010c08060d030c06050601030b031009020a0b090303041206180f0b01050a150305042a 71
    0x3500156000c60010326001e034a01e030080503070642000c50341d0011010070300e095440d800055000b0ac000c20005110300c400300030b0340c0e07041444014403050340c4e075151180c441c0c05101074030f0581c05400181881281510b41d4001552040e102c03100d0801d481c14500b80d460031101881c0481d0001003d2030f1802d0042c2d6024020000780440c0c40e961090401030300e07203000b8910000505200d11501c400103d00b00114010800e03251426001480c1d030066a01d01d2070414024a025039117007020035110307c00900c0307074a4180d02e0b02849d107400d6155200105a9955020000d01009220505269032a00c800515032410440c901c6a8803415130002403400350b0b401000f01010302d641c03001c81c0c01d5070200544009602e009c000d440807038000003d407200601e124a04040901411a500c03000c42c005400d6960a105c10500548001d9019403266512a41ca84041c000600351034004c1c1c0302015010317550714048a11039840b10358454050b0401d911016004040c100115100d1480482d81c00d080751014040056104251204 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 939239883 1250 939238633 939238639
    0x40f1107020901081902010e040b030105070810080d12180b09030a0801090b061b0102070219180e0601062a0803010608070314010302010507081b280f021c080f18 71
    0xca00784003010f24071038070942c045c024104151a050240d094403140c22240098000800074002c510300050b000740314510032a09222180c0c00200001042800030403105a00384603691002c42c41c800c01c1510030060030043c180d001202c3c2d0107214210204030410384540c0146a0500a180da40c1226200108846411780201c2c03103903803610003079518541e102c208071071441d98584610744100f610210010b00a02898102035004400c0d03120821940b80300f244850700761000e80340040c2001c104040318600300d802d5201c0c0da912940c0441c0041c410640a40c8981111400d01d520224040d250030340000130090b148002100c84403004030041c00401c6e0072040141c1d002c1c0c000d00d000c004d400b03420039041c0e6042006203c0681032020008401051104440458403070411620090390070340d184203211076840c00090304040614101c0c51060781040c0c10300c990800c1c80c0d50001a070100c8410150200700500321340940d5a100301c0c00c2c025903000001c1201018020364540a841740f9110442540c001701014a041da2643c8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 939241133 1250 939239883 939239893
    0x607030c03060e18190f0b280e0f030d1508030a0f1404050d0f1502090a03060c17090d02160b0a11031b07032a06030b040f110702090108 60
    0x40412030700142c296220380040c030304038140c0003000102800e0208600d21681e0009515501701c007440102c0d40d06c0414148070310f101c1d15256845603504400c805031aa000c107488101244804603101c004c1e00489001206442590b01000e00c013070030986591b0001d02c424071140e440c1c0c01e02c3c218000c01004030600402d29000514036000d181c10005022480503c0c2d0755080c021014001342c4842e4200040ea805400043d00b1384100d4121810520001324402904603480c414420741c0c0c44800400e402030316174846010301031850a42c02c2d60b603130101070080030340f0043c01c120150025003121026055a6402015200c000d0308001e0318800f0028203100540c0680002189089001c00c10001003004a07511020070380b40907501c850101a540e8190310454040c5a4400342103801500315100100d400e8040300d00ca6500702c0f02503011082c16407001d164290000041410204040003e54060340000d034060000400004004e1508805c0c60300321000492400d840c40750116601c2d00b1400d080c42864050068000141 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 939242383 1250 939241133 939241139
    0x3070f030807080313080703030e060a0b06090103020f070c0b04031707030e040b010c1203020d1506020c060715050703050919021c0804080d0507121110090519050607030c0306 77
    0x100081c07048101c000c20380d002c0000080c2441117540b0035041950390202c0580e9586050f800c0040161030461011052801600041b50b03890b2100d04c03c490b13100030040c0182c2e050000610065000750003030012144441d03000c00182c40061100786400000d00407115113151540d0850a00d01854001000d00190620041080001080c0c001401c0c180290b4102c40204002500b00012200c03010780c10002081049442002c05829400d500501402001e003101040301501c0c54425078641ca03502c1c80b8002c050780168584007203e0501c6c40040c40c00f203003e0300c0010038540701c1c1c000035006c80e230017200ca1b4400241c1d05d5007801802c50781400940300d4105207000340f880ca4542d0307400040d8181102d030010711900c81620380d00c004009802064078020944527042d20038480c2080405009a480413078201c9450407014031155480740500310000b07001d0520030080c00c0248110680b4402008801000c0d00c4603c80c00e03e4400c040b160034445514440c2c42070001d0400c41c104681c0143c190ba4062001c88181420180c0034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 939243633 1250 939242383 939242393
    0x2d0109150e0705271f02010e0705060414031f1505061801030f0b030303010906030b010e10060c02060744031f1505031e0f04030e0a0f030f0203070f03 66
    0x1356250404442d62070310000d16540007105154564444950404990103008101721151180e03000ca0801940081c000c2069000d8881d4440c107480c000d00354014014003081c00f20441c090046d8244850103011124a031010102580140e807072140c01c00039450300e07015025a08d4408420220050909481c65410700c018800c03203480700300780781607100d0405680707484003008009950000141c035440581900c0e9256142c44030000a04120b0105645075680c04000203000154100c41610485902d03104000031814102d08441c0007912140583c0e004000b84192008a10700000715a5080008040266048000e0360f07007014465118202d50040703100c10708003410103108401201d501034010884407000710241486d8800e1039943e9041108080d0001506444860300305000f14020130a421000c81400010b0340001898002160a9a02c1381ca00300b001c03c000070300a03101c040711000c000f40700e5802c1984609092507001100e074801c1d0745c400c0601d1407c0096050501c01c400261154901100307145065403030b4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 939244883 1250 939243633 939243637
    0xd05070b180405091c0e0418140c01020604060c090b03010e0f012301050706060305030f0a1206031130010603020112060806010b0309150a020c10060e2d0109150e0705 73
    0x100d104030900401803001040c032030302c1c01e003158003002001008600c844400b48001c61540e100211052701064581c102800c00000d100340402205a00420259031140e42c0c0300e025000b092081414440d09003000301d266016000070f180078005100210200340f902003240c032001001a4048404074050302107102c04201e0194260b038403c0420b003041959800d507440c0c030710010821030303001505a010105480100d411408000c01c1343c42040d58480420746c0d00d00d01c1540444200e80703c010b20741c80140e00d01d0311050501880b954400360414003081c41203007031845c483c1e80c08941c4100441141c5d41d900800d0046603000000d4a140c000d0a001c00c12555040c00070655039400c1c10b00403003103036050220000718900004c00c100c06030017180da0b01107100d40c02d1066150010303401009140c0c42d140030300420a110211584030b80c40c111810522000d00585400540044d003002c2c2003c4840104001c203d894100c0f911004d10314020142407800060320720503410380d001c0054183c2c000c0100341d80c0030720503c9281540070003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 939246133 1250 939244883 939244903
    0x3050d0c0b0708040b07030218040c020105070206071b02040528060821160f08070305091825020703050a110a0608070c080a0e03101506020a0f060207020d05070b18040509 75
    0x140141c1d0303028a001305118110049c486c1c0c0368041c1c14000092401c65064000b0b038080c2d180ba40840e07400e512204401c0e22086500b00118400100401c6134601501d419003000d07400c80c00c0e100703401c2180c1740e00144102c0d05c4460807402d4101c0c42c0e29814200f10400c0e040128590b41c11822103c1d04031000c10000c4010346120303681c00e401d12400302580ca401404000703200c2d04900340e4031601c0302d540c0301c16916010701590440c454251050442c2e004039042000014000c0d0b1280306541a4500d10306000845900c8124840c502d00701144030301503000c070000da000c0103042c1869005c1c040007030300300034060100328095405401802c1000041c1090019058001c0e02c1491107d034400b841c15190004900100d0744942c490050742d501d4800c407800c807502071701903501110500401d00582c00349191254400c2ea03172840c640200500c0403840001d0800410403c2d40a8540b440c40201054541c0389107440341c0d49464459089104102c80c0010760032071485203840400f0703403001c040d10700348201e00d84152040c2e00c0d250302c10 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 939247383 1250 939246133 939246137
    0x2010809012a1103070302010b0901050f1c0c080a03030203060906060c070b090312041206060608070219150207080a020105090105160f0e031b040522021002030403050d0c0b0708040b07 81
    0x1411101c0000d001d0003e0708444000001100d0304c9040d00d050017806001c0801da428001c04480c000841c40d070500727079400074801c28081c05032154841422020b0714242e0820100b80c401032810030010910b060300744003492009001c0c4e035002d40c0302d081c4002040304440c03015122a01c01d031820058000010000b04002044640750a001a1100a080003003402c009403111025078078130780010301040c5200d4681071510400e00451041003455180d00d0281c0e1600400e5400b00056840300d1054040e01d180343c3e034418001c0e0311405414140070302d00080036060781c101e80c2044032201c10104164032401d07030900c12f9a6200340190000e02080c140030715a0008005040984003c010080000940590251034412405103020f0300300c17402c6881508407010b040c0d10742175905106e18103103004103120b152019000b0200324985144100381844079400c2022440c1e11684002c2540410300c0000003055060241d0a403420b03441e00c40c501310b0310b2545402070240c0d800902510502c1407103018040450107090441e0703070012030786c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 939248633 1250 939247383 939247451
    0xe060c03091c26180a05031e04080a0302030301030b0f04030c06020f0909042102030418150312081902120406050703060512030408060f01031a1009020304050a0201080901 75
    0x1104100c80f980340701d10b200c443c9010000f02014071036200b0a1854440e103c8140c41519041069440c0d075200c0c0420780014069034401e001342840c0e500f8140d800104a0b0b0406d800038a85982c4004450070301c10010030a40160b00003200400506c103264110079844200c0119041003031400d694082d100300c1d050348014046d180c0c08100d00800700015000c0711510b250040001c02d15151501d403c01c1c40b010384040120840040100c0c9031202c0f40000140d4064582c200380710010410b500a01c040108010035030000b08014140340040420300c22182220403407071340d0380d64505600e088140045643ea400c401c1201d014810400030200b611030740c11040e00a03601c50000f145c1501d6207142103004d01645d0300405d5000c0b80c02100c041d600440040108222500881502c141c2d550f40c1c050004015070920002d068500c02c8000098079041d45200070f0351240001c00013004594070f684441d41282c00031901141d0542c402c052000a6681002c2265401019100203101c0d01e000c480398280720555216000f510300c0e0744 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 939249883 1250 939248633 939248683
    0x304060209010e120c030c03150f090a080c0106050103061401080402041509020f07050d0c02130c0302040902180406140f09040206040504140f15060f0307210e060c0309 74
    0x401c410303070800250000c01442d1380c548125111a00ca642500c1c1503403084c8689071410303450381008605036a42141c001d408184680e1141d00c1c004c14500d00805100140c01180c00060000b10030002031328200f01c040b0700000702a420040050100d480e00d40014480000c84208038606a80c0640c5042c0c1c0300d42c3c140d8000c01c0e0181c0080800d02c090006412001803640007040102843c01c00b54094139246000e1002c484119084c078401303544844c01d800b07003c2e4008071210b03210080ea0722180c1044030b050303010345001072401da82c8400c40012038004020005240b04001c0300d28815152601410b8080d10342c2044004401800000051465620181442c010181a00010199074407a41a10010407000e0400d0061100c200c40c40c1d00c0c1d440080f11100903000d20f241c089461107018040e0260030710703c064a20342c0b40a5008440d50501e82004000710f080007010070000c00d15840c0100342d211140c1350b00e00c010605800302d40c03019040102c014003d924034002801006681200013510f140502d880d11010604034003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 939251133 1250 939249883 939249887
    0x17010915090e2a1503010e070c030216060807031d060711010f020f03040203160305030909180f010e0c030604050a170d0e0a1a15101211121b030406020901 68
    0x28102d40840805401c20340207120081d640e005900324480803075107000d42130601d00100020307000c01e00409000140303c0c03000600b0f060107045c50024003406401110b2400f0201c04114103c01e45070b404c0f82d40010a10f80a03c4161909030285079001602e510000c503201004400e00350340c0e16001480c0b54200024122801441c4400794020883d40e40681c2c400c0d56101c1c841504021180c1c402e447c124064032406e03654104071005084c0b80b03802d4030343c0308001d03501c0c0c03107403440401894241c041e041008907007203803c1041014004100c0c50712400312542c00850400a80700480b410042400e607a02c0c001c2d0008001c20000410114220744056401340c45e090404032954228034884c000c005d410943e441ca448104101c011001800c81c2082d4031402001541c05c8481000c0301400c1c506072001d10842c5400700c194100c91070059200000340c001c41c0350074042ca00402c441882074801c2036800030008440050308a0502c011401402ea10001240e1000ba401142c0c03624610544002800607045960220b010082a8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 939252383 1250 939251133 939251143
    0x3070c0b07030e0303010e040c06090602030409020d0f0e06060f0f0105030a050907170f0106061409240d150f0302240f0f13091104030201030905030d0c17010915090e 73
    0x43e101012241c6960b11029403803040482680d00381e03410740c25034000099181c03207030300d407a020390300c3c0c0d90301a41c101890020031001a4100c81c002d000c409807034000c0d01480342c94034402e0180c07001d0900000c2005080480074070440d01c00c92043d59000328603400710340792981d800c170080702e4014400340700001e001c1e6035442e8028100318107a0041d0741ca12111108943d0550310002d401280100d410000f042901e43d100c406440d8103088442c82c11325a0300038004884079203010100e416103056000ba00402c040c1030026144045d40c07002410106d170321358684a01c1c41140d00c0070b44100c041c0655031060b6007143e00b56000204202004c291001c880b4076580a80a4400f200302e082d0380d0030282d0311a4050700e413000701103c0c102640110550b40700c41075086000043e90041401001e003503059003d1a50315090554004501a00a1260950b202d10040190012442151040c0407409056540301c4000d1003442025204811069000311f0080707040c010a160342c400c0d01280300f41221410358000401c9030320a2606800c5c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 939253633 1250 939252383 939252401
    0x110307170a06050109060e0403200619051302031f0b0d03120c18090b0a0308040e091504080d0b0f040f060f1d0718080d050d0f0203070c0b0703 63
    0x58110300000c04000040021040111480303201c050000e0b80c2c1340c518000c00c40300c891051000c640364103004074001c0f902902200c04a0858440161007030401c42e001c8901d008826600f010b800d200d0f1440c41b9152210f144640c54000c400f06a07280b01485290300000d64a0b481d168907200800711128444207228800d5014000303441000e03156568901c02c4d03041c0505220000083c0036149800c001c101c0080520074005c10b8000001459400e160500348660742004041041c0840e4012100e1040800400ca07940b001d00014103a41d1b04051852038882281401c040c0002c589012041c018002e02000918920944507070b40780202c00040d28074954000550031104410f000780e000303860940b0f03202481c43c213500044c0588a40600e40c42e803052782e50040c0d00c210b4644081e42203505803000003140c5414401c807410380981408450f00c00c170458460000768209002c1003214408031303500248541c0740094070700400c645401c6e080710460070352410100c040c10421519030b0060401400d40700244225020703603c902c1207 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 939254883 1250 939253633 939253649
    0x20190504030b0109050c19020102030f091504060c17090c030d050f0304150204150c02030c1203040306021602060414010e010302030112141e071a0301080d0f14070b180c010903110307 80
    0x1c0d201f110304000e8000d42c130039910707524000c840300f0001c0c21195000904418031020010390301255915600d0ba440106082d0341e00e003041003032210034007400104100445005502c100040c240700070394102014034110100e02d100050080500c0850b411210007000d0b04d5000e030b00300443c1c21812450903000c000034400c03034208210441c20102c00050305540082041a402e1082d022070300340d0a00d040810024400448142415600c00c000c10310005186802600302c000032141680c0c00b0000d20342c0001e41c0b68010360407048091016036100840303583e11502050b840a070a00b01140766504000300403a048031502e8000e0700d03102c403401040719614030402030400c504c16818440101c10b0142c00000752903d010344111000342c1a041911244081200c08603030482e1034030001016401d50740801962105580c3e1b1001c4140410980007401c2e54086100900c1e410b84141c105c0c41091038074540501150700300e901d8034209540140c00e440c1003070340c2040241043d240c000e4404451094070b040041d15008150b04030300340c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 939256133 1250 939254883 939254917
    0x160816060e0106240521180606040c050d09150e07170d05120907030215040503010c020c1c02120709050612030304050d0f0320190504030b0109050c 65
    0x2060204950003900303030245820003800b02030366644200b404801e901c2080641030300354181d502603090081c001002007000080300040b02640c0c0e6110542e000c2002c55412007900c8652002c2c40a038003003401015440074003243c0c20032100d411201c0050850280c500110166070395a40750200340285a6198035141009120a0100b49070900403551105510300c40c0d5240003064031601c1e800e9100102c3c4101c00c45096070783c0d942c10910449440d1080c03143c064920801e902030104040701585034a44d06009440f0140040340d903036032074a01450b085172411a14203046400c0b84014100c2d41e40c4070528a0302c0854120440502c0b2511030001403844441007540801134802c118000403480740c82d403c042c0c070030001140c48292000842c50906e88030f1104a82c01809508200500304c0c0050140c000c01425043c00d150010340030010141c1c1282d162201c4000794401e400106801c2c1c0102010311110062074800d1524034201b41ca9582c4031822444113000d203c40803900d4400080c500e40d03804090322000c0e0207041c0061 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 939257383 1250 939256133 939256177
    0xe04060e0f03090406080a080304060b150a08010608070c0f03050901020c03070f0e100f06052a1605060403050616110d0503150411030a2408150711031608 68
    0x2540c2c2c0d40c4500b441c6030160382481000105202d020644003143c0c0c5e041071a041ca159600e40e82e0030010075000c40c007682c0c0034012040c151180302c0200d01400e100040381d110103955504014001d450352100515000421209038041d038005101d0b403600b2000c5e0f60381800c190b910740024100603030500c85900000354051148484c0018109206031a402c21503400e240042e880b615807200e00303c0c111079140038082001d00d220303c04224403842940144480c041307200c07098800071000c8018810841080030400001da000715a05803080101064100c018501203880038a4603140d0364805450700030081896070441e2207900b0744c4451500601042030340304020001d85031520381c0410b000d4203540060f0750018505041d12042400e0341410b00c150180c24651504d4181950340301d428990150480210404001e401c1c4000d140e0505500183d09010301500800b030459002404175000510b00001e02035030410111803500c000718070020041300c40824a91759052200e00e540c1c20100340038850822180c1019103107400303071 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 939258633 1250 939257383 939257413
    0x906101815021024031b0e09100506040e300307121a1309211211190804030302070b01090b181014030c1203030f070f02070e04060e 58
    0x400c00c03040c84294100010139180c0305010142140e1149580107280e601c0052000c50181803202141c84440e0303002c00e10079a1540c8404002440541c3c0d03002c940e82c46004200d40b2040310b03000369640054184c3e07003000414004a500c40d5203692000501580d9800850440c00742c0d80119031001c9a202d06c468400d50344e091400b40180320001c5040f80001980c9002c2754a81c00c07060722901c0307800880300141844400c90303180b845400245211001118810030300202c07007801445124584420b01640d413070780c100d1500040300403011b40e42d1090b01c2c98017400c801c00c86a6452400d041100407203072860320301081155030b94035080d4000e1003850b001801483e200000002d501005420422f80e401c03083d5812140109445014600b024040e952403d42c90040d000c24801e1903c0c900444600d104001c0407188a00007040104019440501050080f030304004100102c1002c2c181010b90042400e10300317000303104203510000351545030500481400304084400305061107060740000303607015042c40035101428002020 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 939259883 1250 939258633 939258643
    0x1c020102010e010507110d080717070309150234030507050a0803130212150f1f15090b040b0a080a14130605181e011103011d0105090610181502 63
    0x10242c80c0c440c0300741010600323100d01e4040b8000c45298540d5504006540002503849800401110406690b071143c80c4c081a010145958108507000005a4644000d41c1a20907031440d28181d8801643c0b24080c00c482c4a840b0014466035030b010310344142c071240c00340b03003540c00c0c08504a07002d0207884002c000d0000989404100c1e098149c822141105d075032502d4a1115140c0b141c100421081c0e0f081c140000b01c070444405d4103180d100c00c009004a24544400f409000c96070352075000124900b1112114040840d00030034200c0291442150407400c0c1803400c0f0344030849211392010b000c00c005291001ca80740020f25001174201d110403818494861400516107031080880c0041507032064145408549800061510075050680000181c403145491610211541ca41341d0741d440b81c81d40d614042980c40e410350901a40c043c204031821500b1450703410880d40c1e042030f41a00032910941c0c1d0502440740a9561f54021200d00304030b4105050b0617840802c0005a01001e0307404841000358850b48010030311f5021034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 939261133 1250 939259883 939259907
    0x5060a09052814030a02010804140727060f03030c030905060a020606010806100926060907090b031c03090c0506030711010f0b01080606130911040509070e1c020102010e010507 77
    0x1244900081d5a4070303010f0f9480030b2480885400d604008081c0c400f40d4030070350705294414041d11040c2d03012400003005034035000090f0f0003030289040c00818494044c0c01c00c1c500301d11840304150203000c65030614018580d804102d120003818421919440c104040c000c1701c620340208802052141c6483c1d40c10000703074580400310345148c00114040c0020345146400d0b05c0c440c224040e240c0d01c0388205424050f0349800010f010211501106408806034240340302004614030540c001c07030190401600c1e124003075098903200e0b61458801c3d04149100000244802d0000903403122174580451220007074140010b440c07200e03400407600600000100721103550041107025110210100801c051202d00182008513802d80c0d1225000858110114240c1e15026002d4245603d0240502e0041681c942040d411134400607103140c058040803800308000d1501c2c040142c0c5c07101140c1483c0c42a89400000102510403258000005050f00014801564402d6201c4600c0010007030007040141043c04000d0301c101c1e5801 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 939262383 1250 939261133 939261199
    0xa0b1918091e05100501051803070611060a05010617070c02040e031e03090a080705100606020715020f1216020d0b040203010c05160f02010c081201031403040f05060a0905 75
    0x20b8110118103100d0303c00c0600c26400100d2026045060000458582c0d010705140f0300341d5019204034500c03035078060007210300901a688418405003070b1284081c0c240314004000c03002c900d03d040300401030f06410405403100400d003425080916036035410142c2d01c2440b10b09010350401d00d0703c00c0a0326810f200000034212508105070b40d000c175070034107400c0f201e20b844126441e022a40100c50101e00240520001e041a0744c402c2c420f861364080075417000745c2200c0913030344a100142e003c01030400245090159032100f81c080c52024080d82e491651000380d940b503090407084899003001030030389450000b40008400c5568010101191001281040d04c00ac1d80e0a40c1c00b03038840d519080c82d60300c402c1d0180e400c450045551103250081d44800c0d803120100402074580682c140b0100105d02e0001500100003041801e030400c065080725415400c0c140e03880d0900204800103a4020001440310b590668035050881e941101c0450b80c0da01ca008041b600d06603203030f01c03254101d0103944194160110320b03403041c40000038003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 939263633 1250 939262383 939262421
    0x18080f0106080f0f03040513111615050103030806010e03010e070906090f02090a0e090118050d0305010608151e06030112050c2b050c100513050a0b191809 68
    0x4501090300c0d00000180c3e06596401000100f07c03d0400136800d0002a1001c4c00000c1c060707440b6401000158040f10112018001560009082116020403035421003400401008590704690713002c2e0007101d02a02a505006942185500e19642504800301c540600b07029a50a686d50740011400703041c02e8019010070a08044920005d48a18400ea0700503450080100c0d001c40d1a2481d902c05605010b07000c0200c079520703900042ca1111003141e102d411f940c4947d008018071035101030001d041300c2041e000f038010408044140203030b0000c0710217403140c4007104039480180a4a800b01a540039100940b441ba000b01d00840000b840003041c5881c01103c901400648a41c42c203203000304506591070516112490b0320742e1010800720740c0010410b04019110390700710f420100c1c103140018990080d001d904800a0700006440006111004415000b010180d922100302410866481c0c4140201c5640c0440b86e0181d0001c83e601c0340c45160482c03610300112007990343c07440e00c80d60184040e01516604002c00990 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 939264883 1250 939263633 939263653
    0x31902030c030a120c17042c0105030d03020a02010209090106112107120c020a0b03011707030809010e01020a1a1605090102070608090c130c09120309050118080f010608 74
    0x81030343c2c81125032000e02c8035004c10000c0c200780c4000344001000c3d00c135000d40e0181c0b09003c014842c028800340200425190151000d01e4071043d4154210f03000d0946620500c00400840d10300040403c05a02d09040141e22039015010480c024045e210095900c4404440000b500c980c00c0300b00c1185400c101d0003a203038204518443c1304031010744906109040d18080184a0100d100040c900c1038409251602e00e0002d0340540025060b00b00031741011048400000040080302104245d05401507036050207400243d1850b11503c00380e00803c1001418862424040c1200380c1c0700b4080454030310303444941041700402d46c0d070b03a400400e20708941c2074813007420800b02c070007901d800307079060350044481640100045410420100c4801c80050301c150940e00c550740c4400300300e64a02800103852841035500241e2034070301207801030040049a026070f4852415544540109034080541002c1d50001e090120343d4849d01007045080050f503920185850103444001d80030a101034000c00700f1100024200c583e11b00b0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 939266133 1250 939264883 939264889
    0x21204141212040f02060c010f0c1107080304030f08130b0304060f4d07060c03050606030f10030b090c040c020705280302180106090b030609150f031902030c 69
    0x2c034030590702c401001d080c000900001e6181e01c182842c1e5202500d8242807960b240c901030700303441243d4941d202041d1900c03400200c40368424203640c150051240108102da181c000c643c1d450f440b0720300000c2c0800c00d003881c4007014005944211144040381d4a48030003840d030b4620303006050750402c2e00c0c100c1d4420300f03090039141041100d008082000ba24000076214840c0325850241c0650740c280c4155284030042d8525283c042c401900000c1d4841c1c2e9105110340c0c80a1a1421604548a4004103000d040c0380406004613502d41006495005040b001c41450640718902e4941c10030f0000d50000f030080c16810104480200c011030484550402540c0502034540410030690300d0380420300945400098603503801ea03804411880c452014158440d85030030381526500819051443c0c100094403100301040100070113a80f01a54800030181018003d05500b8202c0000b064000050800521f50b00c82c070741041226031364041e01e900c00110040032201c03c0b030010b0700742240310b414001c2c090b44a406810082d8074242 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 939267383 1250 939266133 939266137
    0x30f140f09010819110406080906010b0f31081504051b010c02030f011407020d020a03080703140108010f0c031817040e151c03140d0212041412 63
    0x80c00c510304aa081c04031010046992080080072006803040102820007480307004e1080c0013019070042201031352142088400303048131b440940464003c5d401140100984c260913001e64241508682900303954880101061a40c8085502203500b5060744603040720311450850030f020111402d090650b50101345002c0403240c242c50880e4040c02c2d941051040b44c4800800d00084c0d03c031510141030400070742c1c3d45500441c6c5008007059075400269503442c00c0d0480714500402207980050342e40300620903644038900082d01d5554040000303040c000c0c0d41000c500424002d0300314005000c801864440c1542e500c49481740680f0070106442111481c042101c1030b417602c00d015040b18020000840024041c5079502c2803000070700c6c44140c015801041c07001094464146900500400007101d10818140c4c2079010400c491807500096148101079000900c0041d40180444080e64400c0300340ca9280d510000100002e40724907c50040c5100c0c0000400041000304030b07580300035100c40c00841d10381d40c2c401c43c1004024 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 939268633 1250 939267383 939267397
    0xb01083901031e020f07030201200403150f05040c060f0e09040b150303030f0405190201080a0f020910021c03091a070e04090501091202010515010e0303090d030f14 72
    0x240c08940940c146a50107034110b0208010000c10b05042c550302d81629008a03003041d0000008240005014024140d09005454519080e0400d44940c90031624030711500e40b060b4030000b44154018480003090f500f440d4491903890350440802d20481c5800e01c0c186682c0d10141c0034075008603c034030004864661040b51340f0f1076040d40c0509000003544590300d42d0100c3c11342c000c181440700d080703031100080142c40500145025440c0010800e0035804d05143c0709040c500303000300c440c1c80c00048070344070740250307921075000c0d03420040c1036030000340440c010040d1300042d100b4400c04640004141290ba520582c0c0025554105224040c05004503035104000310705a80c0300c01800f8000520f003200f1450019032519000703400c6042d0b414642140100000803c0c140e403540e95068403d40d548042d04030500550798940c0b1026415403000308110318003402c83c3d8a4000c80001d00c0350402c06090304142c0140c6081086840e40701004201c0c520b02c003101d1038000d00c1301c0c0105000f00005070030044a00d0043c281d40e4107840341 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 939269883 1250 939268633 939268723
    0x3070c080319051e072603060117060411130617010b1b10110a0807020c130c0905040e030310140307150c0c03061a090108071505070b0108 61
    0x220b50396004201d8043d0400304607507404c45404580c1d55039492145006001d018811030060010481c2e841011030001c1d2400b503411400b5100b0010001d00303a0b03000300c0c01c05000e104404c00c0012a128540881c00800180701c0c17895920100041040807280b80b410440c080702d006643d54002c280e80c13807d00d060000402e200c3c0a591902c18458180d014040070b034444040702c059001c03140780308400c56100d015150040c10b01e030b2040c03000040c4810342d0b030360254401d80e2003100e900040201440450101e0000754401d2141c40c00241d60b0805459841c1c0325144c4070700106001001072244081d1000c4540d1a0780c82030310b844501c845403160009212881000d40083c100d0001d004e420020301d071609101205403542a007004201c4105504000111060420070203180124400106114034100c012124040408242c0c440c40000c3c004004101d4005181c50940340c241c89410a030340844501550140500c1500405002c016000403401ca100020000e090b14100d1411900401d05400c1c0c40220b800d40c0c80c01c01079 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 939271133 1250 939269883 939269917
    0xb190c050a030c24060f140f060318010213053309040612030c0b06040e0c0f01020c03031206030607050406023706090b061207180213060203070c0803 66
    0x10a01803099048400c0c050502c400d030281442e04462424007480320711108030707545c407041808072120481180b0090102e9401d0742d12000420720004003142da0b02030030648184400030000b8082060111204140d250380c000039502c83c03803040550f0342040c1080c05001e00541d12451044030004401c95a000c884034000044542c0c2d50916201c0c032010340c0140102604a91035540000c0e020b00300003c030043c0f03c0e0080c0c0d150303480304101d0700e88000c44a00142c841c5102c1d604040450792202d00c0403c000c91a90320844404130302c8404180140d090901c450001d03913242c04042078081d40c0d207918050a43c4241030072002d40c0c456940d50354041c1c902d8000d9000b22401a0700c20341c14a1126089240200c0d2086000d5000c10640365907815a200c0c0d10210060440381c454480340464200038410b00c00c1500854221100801c0000c51900150744040a12030803071452034003491038440a10960440d1150044807416040c902d444400113580c82d0700900c0100c440c0824640009900403001c8203881c0d0703249108017001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 939272383 1250 939271133 939271153
    0x203150f0a0207020103060e040f03030507030c02100b030a021507050c041118120706030c39060b03070b03011404050708011406040f0603060302030f011a120c04060b190c05 76
    0x10300a40100c3c000320b040c142e960001140042107aa0074a125034840c43c0074400c8032860345401019030f030000e00b40341e050500340261250303403940208207020b50302c80403500020910745120001e45090102c03103010f9080540240030900307040442c0b00411815000702c0440f0700450440b001c0c441118400705645121038400d11003088807902100c001c0041c800010301c49a04070300d1200c3d160f0f0500d101d81c0e010001103982d640034034070103070340105810044044a1100002c107240c1d82c003605260b0b1a007808004c1c107054516444a040022903809182c5455000d42140c0d91643c46140c08031a0b0347c828000d48c0400c003983e05440b0380300d00d000c1c001c0034415803c5a440b80041c0c0d1918112158040351050481e070700400070311000c81d0030805994614000c254955010a0702861030051600f17000c08285a0003640c2d04104100a280c41c1ca000c2500d04c1c0340c1c00341c1d4400c0310105c0d03061185050200036105246c2c02400c10b000020b5805500006e004541c0030640c042c490516401030503500340e00e02400046c8180c20285000d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 939273633 1250 939272383 939272401
    0x30302130602120702060706092a0e1e0907120c09050a0b0f040c030b030a2d050607052107030f1d07330f09230d050c13090203150f 58
    0x24007c414407424000c144070744507555005054003400214201000051394981e0889000040c45000300030100803030780c4a081906035444440710300b580c2000444962004a45170040030040369005000c44180b001e51300d007280c40c0c551450704062141107101d5003805e021032081011446402c205900060440c02c0080c1803005200c0900300100741d010030315035100314181140c1c40510440f220284103410204c00c0118072860100d10000c3e10b0300b145034803801c0010f4940040c00001e04a0b80040302030400c05d85402e4a800711a11004101114050600c58502170150361f40d05504209030100006000748404040c071040320400040066240d401544428020854800502043c5011600188003070000380c081101e01040c100d900004400014050100d115286901c4540e071005400040c2805170200c1462003c1c00000402d01503041c89041452200c00801004010307100d41020b028244001070101c0c82e88640c000c01828205a010f40503d10b8403060322100d80351407070300c10106401a1201a10b60400c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 939274883 1250 939273633 939273637
    0x40f1b090204082b0e1314040b0a090305120603031e0c06010b0f250506040503030f07091d070c0606090603110402030c070308090709021b1506030d05070c1203030213060212070206 79
    0x20361030f080035001680c0c0c0b004032190700801f9011908003546501d5400c0501c0c20710707280c440050540440500d00841000003d0340a003c5130688148124400c449450300c0340041d0841c4103022001c020450311446104491880101610140c4204c80a0703c42c0380c0c0e80c4000c064264420411403a10350801001502250382d00091000100e807900b044000d07080c2443d64581d440d200301950180d41641c404020032211404c8070003000d0303124505240a41d60356151200d40300c0702580e1580d07071421101d043d800141c1c085104840e40074402c1d81005090011554452402c00180324601041c0e80c50381c440425460345e0304090007102c0c098400312010900d02042910102c46400d07016082d80c0c21805052030004d680a8240094030307a0b540c802d8118001e1f176413031040711854100c4200c2c1c442903002c042810000c9564003c80e110820359a80d0030440c0e59150700d4074101c104070010380c120101045c5050094400e0603455800381c60064840040000c207103407244402d0380d41d94039032003100c80d01d41e004102d010010300780000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 939276133 1250 939274883 939274907
    0x130203071e0f081515060307050706090f1209060215060603071704030e01080a051605090301060f08070503070609080c101202030403180506090603040f1b090204082b 73
    0x1451290558440b180c1c0b894600141c1d1110010703600ca00a115041a8071402d400d401028406904151a0307404000c034156000003842d030003d0103004203011050003080e40129121a40c03000c1100e1381c0040c07601c3c4c00440e00d41da518900700015072a40b008141980000341320941d5018a0044415561b680010042da1342e000400d0b036010010541c080000f20b00394000698041c074440d8070361039010514040010304c0e804006260700c5641e801c0c131060084000920315590303501607192421607a11003a15012a0240c0400d901840f40115420300018040303174082080419a04101c05407840713160b5956085410f010140070b65403040d0445252614a0b15104241c400c030b04d046030400d1811024001075407022600110f501343c0209510b9801c551301c0d107199100000140c80f0485001d42040c1000d4082881400000d20051955100551a5041c01904e62440c0701142080c1c140c10a100d444801603006074010703225070302051145007418560026001508080560b0311030030000c40b041c0a100440f81412491 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 939277383 1250 939276133 939276179
    0xf060801061e14010207170f0c0616061116081c200715061205100c0c060207050a05010e031309110304020103020a09170115090c170c040e040c090513020307 69
    0x2074001060030711005001f4030194403070054400020400070f2241400c0e018912617108007800c101003041c01c40041c0e000404031350019000601c0c1d41d4400c060720030358840c040100401e80000e040311410170122100622505207aa4140306c00d208001640200351420260031800c000c090100d5038031602d40c83c601070600d141c041c00041413420b04010100c01140c20a8001051040c0d109d180641803280401c040d40031804c0143e0200040a81c080c8021311130301583c48001c00f49600011010700303004040103d1980c07075030010020082c5070712000200765203911080e07501c07a41e03a82c0c0e540001001140343c0319090300c51160100c2149103550b0340c0e004400951001101000b400046440810300e000e02001d104025400c140000882102c100c0a02c000c15100d41e1064840d0f6090140003d0f00300e034040e05600040d8018003500c01907888403200700c6414040c5812107104181990304201c10701180b01c40f00011100d00d220200401e0f10341d40200c542c407480e4800d01941503071218108200f66400040c034400c002100b0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 939278633 1250 939277383 939277393
    0x2040306060f0e180c04020d0e0c0306270a0c0617150109030b060409060507020606120309100302090102033016080c03130209040b010f06110a150f0f060801061e140102 74
    0x4400086c00b00e8000750220340d003444d980e81d07420182c40802c01064610841c11002402c840c80c1c681c141140d640084410030301209a040d41c913001501040140580c016405590450300d00d440b520300030f01d81102d284030032a01f00c15220101d0a540381400320301410605c10781d90394803064216111440b400001800c00c58001c1d03031b80c512420102e8441e10034076000d085298042c104506240d41001001056031003400403d17001003160b00c0b5140e035110340345a418902404e0160320342400030010307400d5005010300c0c82c05c0e030038402030403000b41d0040c840c4004010b410a41c16140549681666220340c8142811800200300c4030008116201c00c1c49000d558410080390f01c41c0c081d07031540e0f8042401e104050b102142d20a058000600141b001400072201601c80f51070944503540c0c498800942e10b43d441600a131680000c201c152102c080d44c1e42064882d074a4101c0d09121030018030aa280081249224180855280c0750011540c0c100081c041101c100d0480030481c1003030f003170210300c5c058030b203021f541141544a0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 939279883 1250 939278633 939278653
    0xe0a1805072c040b061518120718060807210f05070f060c2a060c051501180b0a260c18150616080c1006080102040306060f0e18 56
    0x8100b8045108603c103e000c10010304101c001d11920200344542020a00000d000748005034042c82c5400000ca041100d1007040404440c072080c0c240071194101c1d50004950314407000c0c0400341070b000a4100c50941d400c8070402992840c11003c4c0400001d40323081114019046003020401c4802400d49050281d4151404107944446c051151810780c0d000c03002080300603828006101000c00c03034000802e20204561042022000d4280c3d02500ca40941401c3c08400c2d049801440820094022502d58211400080c1c0d6142c0801100c148012560403c410741484a45c8031103040c00654541124036110b0000c00c003022445660055046440d0146034034801c040d0142e0065076001505107200c07203070004102003402c2810f040d021152245480f40c0c000c0208000c0401003a00c4100041c01e80307908071101e1602c0d403464180081c2058822180032039a9406d201c804103c207071041d802481201d00c50101003160580d2030200e604000800c0c03261904035200580000e25034404500c4d86940450742c03400351840100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 939281133 1250 939279883 939279959
    0xb2d0a0f0f0c0e1201060608010b16120e0909120d1e02070f02120604020f0d1b0e090c0103050603030a14070803041212181704050405010e0a180507 65
    0x2004070b0541c000340c2d914285440e10f081604041010001c9070700203000850802d0f10281043c0810305c0b98107219080010411405060010a0040720f580400d1004442415910041880f40300d011380e039208024510200e08040700c00140c0c03580054086084030700b401d4401c0d43c143d0040ca41c50300c0d00340740c04600b000f074946100d2040c401864004c2c0b16440c2c00d00c20384118014040c08900c1503002c0c0859038451070500025075241d0407813441d0100d04803035041004c1071a2030328118455250a200c405107280d42c40110f880030007001c02c903101300354100854105c9007c190045056420580da426007540080020234055031040003072606c6880e18a0410b80740440719618250316070310881341695009502e00d01c84030203da108030791505811a03400203000921120b0010b4040c06980c2000409201d013a0484000c0e080d20981514010440240700b00a1581d4481d07010750386003412112040802c1c504045000b00070282c0c01580307652074215004115050410f05010050f52003200e2000c40c0402e00041440801 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 939282383 1250 939281133 939281141
    0x50303010920130918060e061501030603030c0b0c0c06010f080d0e180417122d040303050a06171f23130606030b2d0a0f0f 54
    0x4080200154510324a005182c00075a0300040300000e070801c114010480106051681c192095a000001c42110700d42810b10340d00070b80100240b5890410755820101d0310302040c0544074000c005c8000070324861401c011000c559403030000801080c8064610000700307003801c80d00741d440400034140c240b8106103040400e140c998268807624035500121418401c089051141108c0d04d071860501c00c2c030034201e040010b28184c41c0340f048800185802c60000702807000c16425a07080c15543e18030250786402e181880740440f00103c03442d811400101c0b411003540908014903200745c800c800440001f940b210f550403005003101a01190510341c55003000306a10003110340f1940e0302e0307d000000f0240781c559071008500f111042c21441440382d142080d0103c5108030000a0021501c884031025601c0d50340c1000e04d072030f00c1e00146014099915150000c000c01c03412000d881d00a1481e0000c0f6241815440902e101c0c03191f0758000c903085204c524000c9029980c840d04540041e00704548007040d00d1094401700c60031a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 939283633 1250 939282383 939282389
    0x703030b0f1f02390d060c09050306150603040f140d0504091d210f1206090c070f0201081306050703060906060c1101080c12010f0e0603031e0904020705030301 70
    0x807902402c00740d048281c04126a403004644807044e8250355507000b035280b40303894080080042a01402e02051200da40c0d448018030480d5000900304840703840e4940c018200710050003200c0c0030740f2407800403c44500e1070f051902d641c840001c211610f1603581d80d9806001c440c3c07032101140c8401d400c045000c18440c5c28000d04201c2070541e038489445618120280c801d48149295041240d000c048403c3c11390240460760a220f00013016a0303051540d03500c100141c0d00d01c01e0b03200d8100e29940215070b103601c0e0300131100030f00d015031000c507412021034850307014a84040c82020342c02048008407086010041d400341150951107030421071503510300001a101d11b4103543e403c40311800026510001800b04410b14420000680543c2c5810300541d0b019030744040816902058403410b0000c40f000040080b0740300300407110b00c004260f00c2941c0301d59480d41c60903055403490181e07034400c03a0391318000340003403c0001c1035400310050f585424070701840c6135010340c0c0c560740644102078002e42c003042041301042c000c02c011402 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 939284883 1250 939283633 939283669
    0x40e010902030f0f060a0303050a0225091401060804122a030206282d090203010f0e1c11011a0306090f0d181206020306040615050703030b0f 62
    0x242e40b07042051041143c01c01010343d4080501e09050082c03640762083c815081c0c03a4141002c40c0d4507000c045040c1e140235004c80719404059040d00d0503084882d8107894980403540e80c404148080c4000c40e5501c0e115003001d009410000391402d00080224140094036880c522250512052010541d011a0589441c2034a4000c0210a81e0070301000c00d81c1c1001415402055900108100040c1d4008074007131904612092400c0382d120103e41d800d5403518040340251003007a0081d4440c403220b9000e1140501005501a8032135480c1c4111900c054041d17002d241c1e00c61003800050003414030798003c003d20745051408000108180c2d141d0581801000f4402c8080c2e0100d00e00500321030181100c02c05107007950092080450f03412007190340d2004500046c00c50071220150070115400c2c03504c0e003402c0c1c0d00d9041d0b50b4002100090245000000c2c8211940258000e00d0700741e9060004036107e8000c0d0b544030344011503800c0041c40811984d400709100ba0310000401e04001c0081d101c4050b440c00050f911541081791101d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 939286133 1250 939284883 939284887
    0xd03030b0105091305060f0f0d020108090c100c030e0d020604120501060b04080f0f030f0a0f17040c05010305070c0503040902220b04150e0d0b071214060a0512060a0908040e010902 79
    0x31592030034007e580c0341020101c0303658200301913240100f06680d80b01b80000f0b0510550034081419548140500184580c0c0907082c2c0c1040b2281c0f08004104801d1800181c01007003040e40321070068203140010004003900640341529051520421504036000317004155002d5688490218003109990700030b02c024101e41005004101141a005051415805040205500420000340303141006020f5442c204024200050000703008902a100b040010801d24081c0751000d04000402c650b804090081e200c1c03ea80400041d541d101068981c3c01c1400405040e641c0248001c00c80d40d2030640003003040d144038800170442c048110030f889640041d00e0300400030306d48002c0b400380107006a0340ca18000d40d01c15072500e11032072044140850308a045880c800361403806c002c00040d080c24003a0900310503501980c4010860180c076403040c1500d40794203480c80c600c00c4803c0c00d070004c0da07803419042ca0064403103c034001e45601d4841161090003802e403540c0c111000c8805000003e618a20007841c44d0090a502001503 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 939287383 1250 939286133 939286141
    0x6060d1b08100608031303020f12010e16170a0b0a1d07090b0a0f06120b060a180f061b230106090b270406062c0903090d03030b0105091305 61
    0x420f46803a0b800c60203c0358405d000e81800542c0d03400e10b50040300e4041d80c100c80120a0400440c0c840f080c0400c8110685d0300781071242c000b4000001d612000c00000070018076030f554130340d40d03203126020058040042c5c83c2d1040400c40c001c1094500041e81080300c4510001d20340e102c241c803804c006141c20144c407016803c141da042082545074011414440c0342190190b42007130820a0410f03415006008000410070b561000d1b00010207590300a01c2e8801e001402c454803002d480d0002000c0140e1400303003116046865000240c4500c001c000041560a079480f0000842031040101c00c43d24914101512951600540c040c05040c5d84031508130381441e494004244d0030b0400d14580c040c2ea07648960380d802010b008100214003c0094001c203030115034051040c0c0c040d1160308020000d06901c1c0c100402210565a540b006120b003020110510020500345980f00d0f074800f4005501d90050f580602d030400c00030350b440000a40b107070340090101c0c0e130141021410a680340c0301080241001a400c0c3e50120b075070300e00780 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 939288633 1250 939287383 939287413
    0x5180a062403200102070b03090105041101050906070b0c1603080108061b070f0c090501090b041805150a1401091d0705010e041509091a0f0103030206060d1b08 70
    0x40c82501c6070320314007801c00525641c1e803074a00542c450480440c002c90b0b1203002c4400d80c8240460401000d00205203602d03800c021a0b030500a00040c3c0f000c076507040100a942c0244e5015405a40c0c900e203000f4071582c02e000c010b856403184e40300d008000b03901c0b07080d080080d400c00e01c0741480c2d0015840d001c1e0399107084560400d50030b1490000b02505044032800c8400b46000d43e0000c075001c0350000fa6010014032946800382c81c02c80980707121a0031035100c2a050100204103501158040904560122010301921100f034081c0100350800174130180c6140c004c40800724040315000d0f41c09401c420a0701002440c1008400c0100900c40c081e001482c480d0b450b02808034030070800520798051502180040c3c0f201501d4038002030200d030715411409000369220300444110011000310440200710101080c400550310340f824119070190019561030b44803141c008a001008201e50982c141c980c540c00070302c1d4540b144000c2004034144500d0481d24041e418070240030007581b1200b40001804044018543d0304110000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 939289883 1250 939288633 939288671
    0x1d101d0309300d0513140306060d0201170702330106030b04060308220b032e030f03020f0105071d040f14040305040305060c090306040605180a06 64
    0x20101a550041c4032a60071556088910101030b0000c82c1c0102e8500c000c0088080d80c0c08141c90b80c41120301030240c00e0991550404000d00140c00140d800e4103405031204000001c0c43c0c0c00444103a090340c0041c2c0094a070f410324900703030000d150050404080c4c9082c16032402200440c01c07aa0000141c2108040c06c2c0f0300400280c0e5081041e02103054446000001071503c900c40c2e00521070f9070f04054895150040c1500c0b55070040b00919040488a80c2e109016210254039030a046c017091021416160006450141601a40d0052420882c1604984002c94819944d0130042c0710050352500800c90000000c0e40c51442034140c03610a401410380d40e1600501c142c21644010301d0034082c0840c0751000c9a503074200c1c4044019400d0200c0b4005207810807041d04400607e130440404048441480030710082c590024003500c01c99100b030048840c4c660b502e044007042d0b4041c00c403019800d58004400f00b80050601d42045600406101180f0440300f41c02c0c10803464200034440558885544070b45e016281882142 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 939291133 1250 939289883 939289931
    0x2090d11130209010e041109060c03130504060e0406240e15030106060e0d05071e0f05060f0307050702030109080301090f0b0306090a29070f0807020d09091d10 70
    0xd402c6082c2484080082c020402048640d0302c955601c2c401510035000c49000c1c1c8203a50000f50515440e80d031808001556a03001c402154030030200900d000480b0314181c0140010b807002080100c03210b031100c4d0b48400140240c5041c1e020180351000a1074107401d040b542e92001021400c0482c4650300300300304901158a4504c083c0b5010380d061480034070200b900006c10002c4000e00303030342200301380c9064141381e400c00d030640e0000604403c816001144800c03184403802d0650751026040300003582d952007003140307901c146234031900c02070700a000085070340d8050000380c40a140050004115400e1a680d0719a131540242c1001172034542e9001d04004c030308158071450592180079001070400f07041c859281a983d0aa0010007441c034a00189a550780f4401c0356002071002091560300704950034038000280900d02c810510b103000500900000d10001c2c400200c9841c0d1983d0303625140b003903e04004400b4041c000031090001c90a50f0f5051110310490104070029455011000c001524101540e8030031680c2002b107 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 939292383 1250 939291133 939291169
    0x41a0f150f090d0b010e070f020105041505040201120510140a080715020f07081c03180210091802190801080c04022b06030302010b0d05031b0102090d11 67
    0x211003a8005100104480300e4404214400e074503121400c00282e142642154000d00b0801a4000000d001c0c00d1054664010402c9440d0b03204203000c0c0400c204e00700c4100305c5020b000240b00c40b2082c05c0d51681584040e40190041c580302d545110b07500d200c3d105499054924034004440900c0821000700d4419035919070b100c00300e64000b100c80c503200000d03640300007a008203080704801e90f42840c41d030350080000c5484140e201041d41d1a02d503403003c800c0c0d1512208541782d4603940c821000440081c0c400d00c60306c0c4a00481000041a024141c0c0070700c0300c0c2d002d0300c5d8002010300c52290804200f440f40300e1188200c03004001005a500ca540540c8500242000b19040c1e003446046001804a0b03e40840c4100c2e1090301543c00586980c0005040c0700320403680302005860000c09180c2104094a9421000c26280250006d2003e088090300340040e20807020b9028203550001c1c05400c50030070081a131115560a401c0008d800c0c8406140010020000120100c541041d01200700000b0706044103a030405c0c032030312 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 939293633 1250 939292383 939292399
    0xc0705030c100903082b05061005030919030201020c072301050a021f2003090f0c10050d0b060a091701090308010308090102070e100e102909041a0f 65
    0xe00241821503140130060000a02003a400400704407030420325524009840401d0002108216600007450142e896034000c903042540d503d0554016001c8138040c02644000308460342d044040d1031300420003050214119502041340040700901040104003401030710700d0060501d030103070b01d400487e880c0c4603d1031810f00c030b0f0a001c4998195008145d241c01d01d040c50031049a010700c08199500180b000c242c400d006015800481e840030702c04180a1481750b000704e0121841303088501d9100d03688594207280d10b54003246401502c1842ca201740c2c0a8503803001c982001040300512080001e69030341003030180c0e100040b02020f0400c048008648010080c4403100d0080028898a44004158000500000c4c0505000003042161039108010140c01001c80c0d10a544060a04041c844020f880303520030345031b500d07000340c010134100400c17031290100b00e071020f010300c100120030f4140070100700c440c06409420b00542809110900d494500450039094031268200165034a0081000039000038030749901d01034540 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 939294883 1250 939293633 939293659
    0xf1205031c020903011a09090109200604030204111c020a020c12030d0c110f19060507090b0d090b070201051509150d0c171207110a030203030c0705030c 67
    0x1011080380c00405180c086144401c4548103540d010303220b0581915010343c0390192001e01d40800c1043c0011041e42143c5482c0941c503480f90352070a803106400040e2041084010051006004c1c00e0002031a82000c0c003400d0402d1783c0ca8000401300c441414824040c0138001801d44001c82d038082c42101114244103045040120041000f5500e9807222042402003c100c01154101c100c100140d400032000c40c0703014455440031900c0200038450104402c003052080c040380d1010070300040f030584112a00c590350074440d8500e13501d8807806080050a000140405850007090a09001c0001d00300200d503140040799074902485c154400c0c50307004001c1030031039140c007051003500082e019000750414022a19129aa16005102040700c00c1c40c000d980c2d403000c0110400d200f00152080c50000301c0381080c60100084484400c4e280d22207000703107403d851012080008800081e02100d5810b920440940b000510545039804030303165a101d110307070800c07962144200300854038007000744005400c000c3c1d03062814420 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 939296133 1250 939294883 939294893
    0x30615060c1106120a09030f17060402160f211713030909090615060819150902071a180d0809120712030f05040b010b0a0c0c0602070f12 60
    0x100741e1000800780c0c0309040502180d42c0d03580c030540e1204404080d03a07229904200d0040b030020072607800b04a0200380030842128410380220500e12440c02c121980d1f48031641c445013088000d50100c441d610210301c0b0700700c0300000f0640110350b003a4090b20441c0811054111014202ca03400c0f1024100e4041000340041d18002844104040340c210000301c0f00c141240400745400e480c030070346682049103040d02d4110741d00c05002807504413050201078044003414007501d0b45400c0740c2d070780c4085800075a25140c0c2135076400302008a17804207490812071810500c21903100d000c040c0a9178000b4070280d502528011081000c007640403515074000d00d11040540c0228003040d406516203003c0301449007801040e50009921040900059944021996103030365517130264a001107000313107a190408002440e0007030188440f0114400c0d00e000c0c940160b02c01002d6071a02e41c0010090313100101d040c04000f901c0014000195041a1302005011030381c000c0d241d03041c1080c40b090784800555000c014503c2c2200d1311280032503 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 939297383 1250 939296133 939296147
    0xc070c0e190e07170d030e0c0d0f030c0204020a08060414010501020c0f0a1d0f010f031509020d0c0305030c2505010c0507080709020306130c142b02030103061506 71
    0x401c0789080894104808010182014003550207420301c0e42001c01c80710890200422170303038070041c080c1d00d04208503114981620340d141001e00c50103400c04422966080403482c0e20240d48001e62180c9408030b1814000c0d07010400b81d810500842d170218121806018031441d040c010201d481e079403440c00c410190302d0500001c0d982c0c004640384600030840d05c0d440061a40350800c03000c0140208120050412200a0090000020417581c000400e41c0b075000106034071590060083c2242c0e042810810408bc9884840006141040d8102c0c1d200581419060006040819040c000c6028602079910b4110f08251030b41820b02272426403c0005004000c1c1111241c0c000000007501c000b0320740803280840b40d00d07045203007040d141c021300d02c1071050110018038a0754a070001c0d442040241d07654658460702075520401c0c1c0b40c0005952000c95040d100f10085d901c0c20070b01a1910040603107005140c3d4031140241e90380c42c2c9140d19540d003504e40010041c410700c29940120444074258078151a042490102d0040000c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 939298633 1250 939297383 939297421
    0xc0216170c04270b09011407090e10080a0c0e0603030703050d0203090c0909061b070302101a04150f0b0403020612090c10031b180e130b0c070c0e 64
    0x4940d546040d00c03d1010b81482c1860740e0302501c03441c03488220a42056096000211242c004a60819070710040482c1001030717041c042d00c60368444c26485d50401586800e1105d004081e0417210164880c0000e64101c01c0054140043c050300702c0a860500340300206124080c0145464000e510400114000903031000484900744d4001b14016200c0e02d03407508040c1021020008940d2088102c4280008003001185803030280c01403a0309118642da403040090307854000c421010700560000030300284e0030100358000201121020204400031090b600000b0121041c25100000301400c41c901800382054504142000d07100c410a62070909186d980050300c2031080c0b41c0c58520110054010805054040002d0844250020031218807a40d403040020020b0140904012100c0303554540b410045020b1140500303400d42c120080a0342c40d050662a1039001c0c0f01500b14074001030110782c1c07040890366032041c0038011814040150b03520412420001034500850b00300c0851022240140f0080c81100c403199101 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 939299883 1250 939298633 939298639
    0x2a0909070f0b0c0a02040606120b0a060e06070f080d020703021902060726030c12071d0409030216090501051f0203030109050703090c180e1605120a060c0216170c 71
    0xa0f5415001c4614140311040b4402034101c1e085c03500101c2c078560451088000220343ca0400c201c000100801c01060844034810000414648900b40b440c41c10410001c04810b07004420a000c4540903a0741c03002543d020fa114020310540c04500002016410303c4081d0440c3e00c95070010701d01c03090540005185206400006205001d410001e0000b4587c640041000116040c070013900ca04e011402136107658080351203580700041000c0040e044500660081034902c0301780d01b480d03010703894a0003804005c02110500740c003584968004100980000d04131070000e41458900070501c0d500d00760900448025685140400d0020b200104c00340680c00001d03681120701910021803d44c03514041900201030b4840003074240740b02c0304004540c0600d0768407402c1c0384040510342044088a8190441d40b20100c000c2e1f600e039a2910030104008500c1d0055000700604846000d035210b0101c0c40c1d9401d011100e00d151848090b070041003220380c0a4030914900c200070840e00040220386066a4119078071241c15010040c4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 939301133 1250 939299883 939299887
    0x90c030c2707090906060306090c0f120b03190c05030c0105070b0403050f09030d0c052517010b06030403080f06100f08150a0e01031514070503092a0909070f0b 70
    0x9140b901c01d0100300000c00843c1010002c0d562a010f005015200d130340541c4100c1802c0007614890148070744140c0b0f66004091351400241d5000009880192410f002943d51610405901501c102e8103107896819044c400c8908048051605003030508110600d440f041c144401480b034100440c1d54900c507180e105a140c0780c465507800706400204c40a008000b5200c1c0c0512428144a0364641c020040b41e013030502850488501d400803081d101c05010802c1e09402803105a00303c01c00075005011b580c0002424030100102e010002400420a50b8001712000d50000d24918184885c00c0c010201c42034100c002030312040306801e000030003d800481d00e071900c0130401514500060801c141da80d000300303c0520043c121000305503940c442070040c84003800240c40b90100300f812201c9600d103500c00d01e0325001c544240094640c0e0b03090000c1ea41034100405c3e8509500031036140c40d00c0e226828500607801365802d0314030740c2501503420034400711200c01404111355034030201c0113000000d422281c036000c40701410109a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 939302383 1250 939301133 939301141
    0xf05190b0a0c260304150c0c08161b1505030601090608100504051801050105030c09130303180c151713020d06020309010204080d030501060807031d06090c030c27 71
    0x9200f00007a11141c01c0c04280588041c0e251580d80000c0d80514020130f120300e14030002a9403141214015001c0c00c01080c40d20201c18001001d1401602401482e20001260003030036482ea5003587c490144440f4080703144a8041c003011050915844540f0316078901035055160100c006410700b940750041c181400301da0800240c071600001101e801400b4050010302403401d10100c1c003055220540b040d12030315400d140020a060500203402d000a44005080d82040c0c0c032103031003480400020b884160704149e00c5108204118103a40503903440a8031680c0800130445c82d21511800c0b800c082e0180c0001c00100f4514101130010010b8019003000c0c000c035024a0191807880007814a680c000030003850b0038004000c1000244065024100b10381c0044280c0d481100c0c2d05200b01d04a42c001d00404002c6a9018041b850841c80b81d0b00c86181442e24002d1f2400000d04c180100d4a03011007243d444401c0d5000061920140c1010301c500d2110010580308924030700f5140c10500d50341135040800c0020641c0c0d40b8005 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 939303633 1250 939302383 939302393
    0x30c35090109062c06130b06120a15111207031a0d0507050a050114042c041b091107020f03150c1917071101150f05190b0a0c 55
    0x100c09450f0720542c100544404d0300141c2c40d01507400c4240d8035030f002040c5540182000d010964620580341c1001c00f05c00501a9902d5800c0f0000180116030000d81810010a50302410008460014000c1c2400300342c0b5481c10000d401078032031001401c1d400d907405000b001490951013107900d411803114280480d51091880060403004010401e160b0300c200c00b000c01409000c0e012440700c0680d10160303060380c0080e444800540b15807000c41003603000003108120030007001210100210744104802c045003901c0e2100c2035000c0e03140105413401e0b10111580c80000f81c10184445400c0b00906e1ba1404c14130460b600302031050f041d4052020064011000c42040503041d40d414403c104031100105030744942810640128800c5400000d015690484612550b04001c1e00070303041e0249203014500d8044455480100c1210b000810700c2240c2035541d00c1d0f00380007002c17081006508014003844414268a81d20300000c02005059003120701c000041c54590a0084000c1070741110140c040758102401c08810900e0a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 939304883 1250 939303633 939303641
    0x120c0f010516060f05060117010312050403022805120307032601152a030c14060c09030115050d030c05030d0212040b070e1c03020c10030c350901 64
    0x900a00074603850340410800640d54014000d00d1041d071410815982e131b031001552034a0146850200129541c401000002c0c0c80c08000d400d0920107180c5241410754990100314844440040000c05040c03600b41c2a298080043d1858001c3c00102c9402007540b00f04240a0307102c0c0704010300074081000c81c21944210a04040d8a03c0b50311021000c80c403825a503905040c1080d13040d880b880c8000428600350503c180d036140c211514a580c1748030303942c0d904800650f405d4039514001c0d8012a561520ba0790307011204002440342d9440392041141080c1e03a601c2c00c40825084600281000140e021030050034003044e00e4a11a0382402641800e04641200880c24070340c1c514000d0401082c00a40006514507054612412203401a4440e100b5411252200502900e440034107400240d004802e4014400c070b000d4154074454041070090040e149005040404542a42c41410340803020940b95074400c100141d111602001202c00d54172454001138100f68000300702c824401918068441c004041003407540ccc00c2d80 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 939306133 1250 939304883 939304897
    0x1a15060d0e121813110307051b0a2126040c0e0103050a0c1d07030203100e042a080607030b063105060c060a020a14041e05120c0f0105 59
    0xb000da40c8800c0741c0c401241e6038071190902c05001d100713085545140034449006181711122503144003030070350303941c00c0044690b9000381072184085203005065110b00740c4144501a0400e010381201c1a00301b0b51002140004103588000303000300145624144095403407002d0075180d00c00400e000d205e03241c6a81c1007a80b0008155000030070134014140000040000001d0049400c41c461400e07a4601030740c85126921100c40808410004101c250004614078442e50007103034030450400020856507200c0c500d100040c6822102150100022550b80d04103558210400401c080c07108500c000d0740307041c040394944030a0064001c0040c140c8801e420b0a041d602c0d4003c0c0c8240382d920054016450110764444501d144d6600403a82102e0181000030986091071003c890304151010000c0000e5160818640c000b50700c48901d010810446c2915008500c58900052004003669169010703403600b104c5603160b10285990046119802008980700380410104040002003012504032001040b50001a141e03807107992 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 939307383 1250 939306133 939306163
    0x140109050d050a080c070e0c19030c051b01021c020c280b09010203070e0a12020f030114090607080709050906040e120a05070b0a05041106030709030209041a15060d0e 73
    0x71070088440840000c000044400c081c200c07d070151181240d5200f98030444000c65000645800b0340c81c00c140c000e80084140c9d0200d031905614042024000144d0380041580d070b4042c99400203124031503455520701d81058104050b004600e030030401040c0554400ca4940b007240c5440b04400d4070000000c0b840c2d6241c4a10790481194149032070005001e034004d502c00c480e0700021681c1d0310076035086402c1c20900c14050382c1080c01c82d9044000c4c0e0740c0030860401411442e00764199280e0000000f015040d152141c01151628001c20b0390707080440700a07103288001040c09003040116002000035a0b0703002110398100105560000703940400040807810220f0301e044401b0580c100281040d162580f01c0018400da90080001440c0741e00d80200e02c109540d400e84d0050304182a290440c0900e1070240d000390342220090a0013410142e41c0d40c0071844500c01180d040d01e50505030b04c480100503007800f905503444084601c0541a8003103130b400103509400750014880d04156101030610038441c0800c11100e03078601103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 939308633 1250 939307383 939307387
    0x3160c0f050706080106170403020d120216030903141504020402030402010c020904080a1202030c04090e1911040f02070b0f1f17010b01020a08070210091d010609140109050d050a08 79
    0x50b03d0050111070081c400e000008012540341d80384004007025481c001c0b0b51503805031500c880600c504854021f600c1d540f07904020b40c2000441050490002141c18031803003602c0d200340799442c2d410b10442c0008880b4801515800c0301d07846541a9003455662940141e04035001a241c0d1600e00040381d220740301410007500100e0140030310052161000142407d03640603503035160103001c0040307a1016030100b521610300942003803100707001d00c4156422103000000780c1c000f20350b03984c4416100c0000c00b044e091815030300d40d140c41e003142410741810300ac1c14a10980920080d8605401a5101160480024103480c410701e2010003060368040d558501c0c154078034a1800d61868541c84280385150f600d80940202c402e5868204d00040321350020491038030080c5c201100f03d08022541e002e100844241100c1a0208200100045a5982034880c48201c0e100b0790300b40742d4515030504901906540f0035400c0b0403200f17900581e0354402603030701c40c120800b50b410507250816410700c6490168078004548030010040c80380 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 939309883 1250 939308633 939308639
    0x5030a1b030e01181703070201020f0417101835091c0305030a0c1218021203033612120121061503080d060906050603160c0f0507 57
    0x4550400c0003000b100c0c5008200710030b040600d42d403007540390703040c0245520300040d40c000e15170424502460307011900f400054a001101d00629040383d1141e040445d80b200d800c001060703d40c1d000c0250b2075000714051410030841072503079401206001c14600040c10700c9a80001000581404490b2050f001306c2c0c4540c1ca024108120100010b5402c0141c41c240a80003000e00c02100c0c4142c09504100c654043d12181d1664440e0080d14024080008041c42403041c03100c0c80c1e04203008148a1203082c0c3d102c09084440400d214810004440720305020720500c1e500a10600ca4010b0f81c1c0c1c500c482d685c00c05a0301c00c1e450b0500d002039854a61008e83c000c01c0041c02007188851115080e00c000b40b0044898105c0b04140f40c3e2180070043e030920f1030300104140c800b50a1201d20001c2d10075400f11512001c40079a09070b20230b5aa80e1003131010351004800004040d2a24000c004242c0d450003271101070142211010300350310704135660120800c40440020304021816202c03105010f0465955050f00c0d030807009585140752 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 939311133 1250 939309883 939309887
    0x60e0303010b0a0305060603270a021005041e0e0112020432100339181401080c0d08070609050703020f0f0d0308190f051819020105030a1b 61
    0x1c80300f8194040ba05050000703d40d072400004403071080c040d01072400342013003012074200059103070f2040b414050312840758107102594400ba200ca010045540c1e440740d4450030300d501e0011040c0501020300800b50300d0b4005010750144004902e0648440c030906640c010280c1c00041c02410b000454403243c2d005a002d0780c0c0007800c020008510243d4000803240998682c0316081001e1421351001a00207000b4452600a400c02c0c02c6090000307481d4004030403926200d035140a0501189a40461144101d120304444441c3d410b001c0c0d0001c02c041c260514a4961421a205440d200403680191251080c00f14500c03c0100e00c50594914540091b000c0001804901e4400e540c5e001034003041c2d11440801daa50342c00da260255107049450000f505004588603d582c1c1a17070603c0000c1c00340c0d40d42d001c0181c1882428040c0e442511604480018080f035181081044030701500040806c1a0b496040501042750745036040414904117603081c07801958a03642e00e03a01800178101c48080741d5030300481035a003480d05031f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 939312383 1250 939311133 939311137
    0x80a03110f1306170402060904110d050f0106090602071203211a15090906040e0a03030f0c14030c0d06030812060a05120c040902040f0501060915050403110d060e0303010b 75
    0x154549560304002d499031404e13511082185042a498001040000d005007098005071030413030740107030000c100c1103d55010401690810201100e440e03680301c2c1084141112400710074010800350038541c00c25410554000c0d2070f1007ca00aa041c0c6d1021081440105442804040340d4850303410fa600ca10301003214041c5c0040d080840d0040750a4030310100990740340c0361101860390040d220555561810501c0d0080c441c820200408156115641d8044581503803070610407a562070307101e59000148503040a18490490343c003451101c0401c0305840060321074684040442e41c0010000c180c0b80d455002220100c0050801c90f040104544000700c2e031000444510440d80f401503008443e01d8003c2e545642c00c1c480d1512686050b1030b8694084d2030030080d541041d5000210003070000d040030901c000c07080341d000160f030b000382c1c0301e8400960405810003000400500c10780e50384000385001450a4916122011101041050700c0d01c546224840070041100070760055940300000c2c01600d03100e681d0740d1200300c915 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 939313633 1250 939312383 939312397
    0x3030804050f0106050109050d0c0305030f0409060909050a0312180309080f0a020619020a08040e09060703020306090615160b0a0c05040506031b0f041412010203040f080a03110f 78
    0x600c00c1e9103245041c2c000c1030099009031601a901c2456040c50402000780d030410752001074666021800d808030108a051000b043d1001d500a902559149030883e0001107900a6100c641c11034035005502002500100e0717500d91458041c6840c4504003c00c0c9880b90080400e91a482c03c2001c0b049204410141c0110b1414100c2c0c03042e2069408150131004a15112800400b0081d44000704000e1001c0c0f0081c0895140071040c45881120054001542d03203035025030042d01b08140708028082000f0321003200b04040d03584060285019411418110b0108901a0020b0038641c407030003072451000d08c1003000d481580c110002010304031000c1002c0b4104000e408809030381c0c00249a040807042d40000d4040c400722000c544c8060a12451980c0c0c0f60030307000400040c0300d4401a001401c0100c90070342c00c004005000507144940390703178a51150355410043d89200014800e0610b0f40184100f0010800b000b181c0c840442d0420520707036464801c0041100100100e00800380c1c1d2840114240c91800e00c1ca101800803 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 939314883 1250 939313633 939313643
    0x1403041202040c02011b120204081e0c030d0c0b0a111c051b07080d021603021501050a03330906140705071509110901060503040b060f0112020c150103030804 69
    0x51460005801c038281c6542041c2160b031b5030751000707480740c100d0b2040300500710500e03010a006082c0ba48175110709007048000382440d1401c180501c4070828809040c00041c0860504400400c0c2100312400040c205d1a008003019010620000015400310740d86d80105428100414103159201010f1800703650041c1c0c0300f05051815490500001d540d0302000f5045918007510411048c01c00c0d0580d6074110641d4014502c9000380d6400b030109941003240c4d4621610307103912036005810301d4429003914101883c0140d000f1131081c07060400810108408450a03014401d44010399509602000c0c203010f0b901c04050181100240381842c03810501000c0c0d8040d00c8007000b0f030408481d403038480c441e0407240341c0689803001d4000300241e201301d1006d1a1a6010440d0700e84070362001d0112650350400200d0030b0b0300076801000400e0000040004000c5007120059000c82c040340d407a04100e80040000300500e80303050700104241c0c1d00180064110404010360030490345405910407c540c0c50740323401081c410080e101121 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 939316133 1250 939314883 939314891
    0x10020f0904051812160f170705100b041e0903020a02120a0b0f0c041e120803070e010903051011070209010303090608100503190201052115030105040b040f140304120204 74
    0x2003a0b030b20704d0301202c164030040c0800d45889002a1240d00480c0e00300307070341103074100c03003202242e40420800c1c8090700300035010344081c0c42c6150340d001031351040c2c4802ea500c0324071441c500b80c1c2c40006c84440c00c3c1d03121385003281c901c00000c1b2005a80307420f81c907084d40000e010f544848a11203100e80d41c0c0c0c000603c01ca40300d201e100307104056101e0b00f03040321403680e065540d64280720040c40b007880343c69044600e15200c1034800d07106a40d85a0f440a2003a00700c2607000060b074040100000304407841d600021070030b11402c1c00b80b0301820064030356191203071140c0d0700121050f0860749450603200702c0603000055803a100d030010101191f07960340745806001c1036520b20035080802c0000002500c401058200242252006405803c0058500403a015010480325040f41032013420300545001001e40400c855001c0c3e607130a02d2800e03070308101001c4100c01d8010300c0c08a110303a04000801001905042c42c464005071b11001d401186a02071410803103d072000b5030400400c0c400454001001c2c00349452802c1002c3c004d0364204 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 939317383 1250 939316133 939316153
    0xa030b06160b091e0309180f01030809010c050f031206010c0b060d0314031515071e0c0305030f0901090b04060c1211012f03070210020f09040518 64
    0x10300303401802501014141c1d00341c0c039940425103090703426911205040507500301250344c128800710010019456840c079480801c030741110b420022406120325014107004102407401250542d00c0d900140001007400c50082210031950740240d4150740800d910030140c5850300b4415019503a6904041507002001a002001c102554004c10201e00c25a8202044811513a5039106100d05450040411020072414178007614584804801560181c0c10410311f046110011000f08814003c040045208001e010803010002421560400c2a940100c15a90443c100c8074280b550110a95038000b03022070000040351a984401c15004010005090b20b54032010f03500d4880c035a00754040c40c043c01021483c569861404035428650321201da002e40e250105990549025803820356000e49003004910b08100001c208180c0181c4540f2031700c10240031810708500c0c00c200025070390300101002d44103003603000842c20210039105e02103e080250140c400d2000381000079607941880a1031108001d46d01514846d9 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 939318633 1250 939317383 939317389
    0x50f01060e130504020d1a090706080c0405011103090a1811041505091216050102010b1c020607050f1204140a0f06210608030c0f010c0c20040e01020a030b 68
    0x50700d8400d8000c0c10072403848140582d030b0001800040c0040c0d80c043d103000014400921002a18420040c25013020081810485080361501c00150400e100340441f00c1c040040c03a071500002e450441e13201f46001003c41c00703c00e00131825482425205c40d0001251040400d05000b10490490310300ca0f010f40800c110442c141c00c1e00b203580154066407012201307420486486512600140840c000000c06c03030864458002036071407504426245074a80310344000b600f0440343d030b02803044c009080015540d80952800041844418180c1040000d01c106c4002c6220301c1800310401000481c0c000c600100d4540d40005490328042c0d03042482a44480c24081040701d40314142401240222580c401d05c19000030706149054441c840c100c80d003802250b913003801d04481c404850254074002c02c122005135a0f12941040c0c050b003013075500c510032081271703047c003102c0106a680301400540164101c1e1401c010101004071400501d0710b6843c2c0c050f40917003889950842203006600030b042d001c10540b81040240304032014 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 939319883 1250 939318633 939318647
    0x206190c1b26060a1e1406040c050301050f06030702100212012c06010e0f0303040f1a0703050304060c030e0105150a0611030d0c0c05070b1305011106160e1003050f0106 74
    0x148a10b50700580042950700300c00d074010240199070440b1140c804c00c18000500c00315a000320413940300f10501000e100a85c101f07842180f41204c51031802626542c10140810300c0c490003910b2241c0212800400141014401e114000b00020188001d40d614070507116980c122003001e001c4c01307500051600e60a00e0100007000b04081824003c2c031500c041e50b50701e50064458000c206000e540056201528503503da4042c8020070241a100000b4901c81c3d05260200755444c100303074980e004020042000c10003090f088810740e54000d9103c4000f10b40041d11400c214041d1805580081d200c1d0308180070f00940d1071101821503511541500e90186050365410226950014a51052481e400800016400c000640c1003035044200d82c0c100320300310280c00d03690030303182c50025805001001808202801d040004150400080c00c003441c01d8600038002003942900d5890103030849080f03541283c00342420394040c4084140740756000703045580c142c0d070310b04024010300780c00c440c401038010400340041595402044 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 939321133 1250 939319883 939319949
    0x2040f0c02060f06150d1e180b06041103010b0c0d08131403070503120a151401120e030415090e10062304060c020301180206190c1b 58
    0x700030805915544010311054002030132080d049aa04280c0314040d5400c0c00c010443c183c03190340d0002c0c003048840c0d8840c04105038074410300c00382800d1110301c0341c0080304060301d90982908031a200105031030300c0c000100103184022081e1340429010000054600b40311000c0d000c99180e0b1803d43d140703020030940403501030804803004440c2260b02c0142c0350124528101e40c4842800d610210382ca0041284c4805186401140b040520040390400f00411240306005035041404990301d2807400f00e0415020001789082e501c0914100902d0300c01110070440d45811013840c0c001d001007541d0b0f51316110005440101d6400107814042440750200080407801c0f02c00e01403254604c12100c0c5015414118211561034144020464004400500d801813401c51401000101041d071034498410341e007841414250b65174580c1003420070f01070344040009600d07800203d80860b1445450f8850110b04d00c40240c1d406044488003600c2400e038800b46a20358800c108415050782c0042c805009103042d5524100c20781c42401e4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 939322383 1250 939321133 939321137
    0x9060218090124020309060705011b03020c07050f061620090c070303021b01060602070e0f06092e0902030a060b0f07030c020d12092103090e04020105071a0402040f0c 73
    0xd0703100b07080300749410b101c0a094000f03881980c0c90902102d00240407600a80320a45090b5590620b80d080b0401040550102d00140c2c02e00b58100040d40340b4031a262601c03445410f000b4031404259202d1a50380c081140c4100183c480003501164003814001890000300b09604000c80c904086480c0600d843c01c4d4140c4242d1005201c4c51030031010342d07070440180d00f109019a603074106e1005800d000c64000e01804d005891658020039640d4a00512840c000d500a807054078040f0001c800c0c48020303142c513107a2135032003110b107801000403101c0321258602c00c41c10102c2c0608121115480030a241d02c103600114002e100e0b05006210f0f194460150b400311348580c002004411104010400000703015105125805000030a52502c0d410542c80e0080302284c00d6141400103400c80005018440005a04c0903400804841c0d22600d00ca183d5030140c00d5480c90700070a000c00c0745420016045a1260003141c444591000090215819903448540300f180180d50032441a0b003401d201d94090b44148c451103003100126 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 939323633 1250 939322383 939322409
    0x5072a0c050607020f060a0507030e0d020108070c0819090906150507110f09040f12030605060f07060615020f240115090902031f05091303120b04090602180901 70
    0x31000b00502035022440072a045815004c803440d042d901d000250000c4c6202d600c61940e100090f00e0010400e85180b502c0714415030442c92000c0150360b1200b02554007248909049407450001e00348000c03a8040d040b41d4880e4480359440c10000190f01880000440f080b0100034080c00f910707441b4400000d0418042c040000c0d40501812000c0b82e14621080101803010304880c002c140500003041900c042141c040e0b13440c02e51074000f501000b00030a84140ca0b2003662904010071800c0000140491003212401400d2890204812050001079400200140728004115210884034400030f5160b040c1d51042a21600800c001916050b5074660314240c24801041003126503800c0002501e10300341c00c00d6248041228804000c2643d4103244019030054880c503401800c1d41c01e5880c1205880c1c0710075000b0a0180a081c4240800c0307882040640d42007036070504140844540011504005014102d08240e1007401c01640800b40030351a0b000700760400341100c0e8094540c0141c0705111180d0380c01c0c0b01b400110040 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 939324883 1250 939323633 939323639
    0xf0301020406170709050306070f0e090f012d030b0609010f060203043006061401020c0315180a0b190207210201090b0a052203080f04020d0605072a0c 66
    0x343c007252580240c4608200011070303183c0000c03e00e0003000b00c83c01400304140d8042c061a96030000b14044031964100c0d524421882c0c400b001c80c005a1044c441c030800e0f000b4280d1005070440c0300c0e615650081c040e08400e0840a0366030700340050803010554805010701da485002088200c104c0b0601030550341150003c518080c5002c6061183c01501800e44005102100702e90740070307005100c8100c0d41d150045002003003807411300e001c00d00e1f004011100740b810356100030044030382e84e24042403220703658075108141c0031903070b0311054072500042c8074440c8640c19020303c3c0020010030620210040c0503040d50100c40302c2502d82404007200b240300307001e00038180911890b08041c01c01000d04500745a04c4851001040c1000c0603520b0207420402039130300020080e11a0104520001d400c1402041e00255030050307150900503450150896202400b2804071503a0300d070001e000d540724595040680341c5d00c401c0421013490070150043c1a0701c203060000d4080c000b0010340364880007072100c0d160314190f0009400e10103145 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 939326133 1250 939324883 939324917
    0x1b0108160509040f0c02071a0c060a090804030b18073c080102040311040b01081b0705070506030406022715030a0f060312090f0311060903011b02010b0f0301020406 72
    0x9640c0729503119486640000400345940520f991711074083c2c008000103818400380281803c0303c11180c0c1c0340e04400b030000e021525000146a0303004000208002001c880504080740c040c499604050000c01c001811300925101e0800340034095a03030441520841a21117100c040351070520402588000f61000840e0144030003450300b098609007039100b840d191607a92188a0030381c0c00c298000e8403500540c40c10800da50405020307a0a220b40c3c01d18000386c00345820003080520685c82200c00c00c0e622400701e04e20080040402c00c60014200c001c0ca41516440c1610b800006580480652045501c0d002040d000190083c1c10601d00008000c02045c140380c6001001c82c015040241f0a14010f5181d40c05c10086041034466100614000c084500340e03030100c404041c101c46000d5210003200442c0706c1c01000400c41e0340d032b06115902c40484000369284240b03070001c8c4c0076000ca1102490800c011180c0301400c0b940550068128500c25944000c891010100301402c07030180d486888003007110500004584c0b0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 939327383 1250 939326133 939326137
    0x70801062118140724050f0424030e102003040c06020d0804080a030c121e0e0f06150d0b010b12060409051513141b01081605 55
    0x84105040d5101c08088800d200580d06402900c1c05444044640d203024402040603240d4040301e91802004420310b84207070500808442640900c0c0814018045c00034984110b04803100742c1008607016032510b444035001002c22160019408880000181450380c5030300a0040900e000d00e48809004a8800d20b048100a0714210082c545001e030104614410351504a02a601880c0101c04422996050040191078410802c0b40c00050010f68410400010114011148050494500810140381010094400304100c3c041c003a68681410064407850220311820085492011014080320052100190f1603001c01d08901c44143c0200300041c1c200301c0c041102d800c1d00741c0c0141c469100f001d220345a1141109080c2c2042e0071482000808511030000c140d1001d030030580848042140205590b030341a07480c003220074080c80300c00317210002500c0d00820341d110580d0107410071400142000300b101d4407610741020050703502c2004040d0119800c0d41d48101c0138148200d041107001c006481d103845040d1120707 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 939328633 1250 939327383 939327407
    0x30f18060e03040504020f031f030b0103200301092402160b060d08030a09020102071a030a110409090507050307060e06160501021312020a05011409040e030c0114190507080106 77
    0x1884200000121a25240f0047ca03100403610b1085459040020b180c1e8070b0b00040c41801c91811041c81c2d401c0c00070840041c4254112540329280d4410841e0072406204c04006800c2599415407170b0500000034403072900403240100c4041002020805074a10103e01280902601c2c0c200615080703450707000080340c8000c280d8011000030445a64908169550f0000340e20032030b514000280c40d1542d5800f1941c0401009025000c80e8807070740b01441c04801c4c0c042c0103000042009081503219415104669080e80480e00a080c41100034400030b000c6081c502d984000324426503000b4407800c1c0d40002d5003445003034900500d01c0000c1a03149842588094820301041000b000d44265500f00415858650b518031018001c14500f10f80003100d40e214010422000000e80c00347d8148062600520741017023041040768001441114009040c40361400818038500481e140700352150702c3c0c075410021201d217400e0102c0c401c085070400841400740c180311080a0f075409468003404115044014802d05010b86a95824 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 939329883 1250 939328633 939328661
    0xc210207030f0c05030d0914030a170306040902060d1e060609121a0a0b01080a0504031223071808010b030304030f24060501030b03030702031b01020307120807030f1806 74
    0xf0309074076040000d05007048445000c0c082184100b04201c6c100d50b8458040340c5142c2240a4491942c440e03c81740a4403000c1581c0c0b201842e00000050803e80d5140d02c500400b40d0003424940c0c603941e5032040c00e00101542e19541c0350521035042001980042070003504107952855581000c03492500302042c1d9000c0c4602000c07a2201000301510034480350341d1000e2840340c03c0a02010032401079803400542900b0010f45950741440c00d005c20080400e4220400ca1150704514000181b0b001c20940d0403c0f645c2e20810182036000d20301c1060280203a401480304070400003061840001d02d0359940300724221509207551300d4142d00144800c0004c507661100141150b4000ca00c1d003801440d07801c0220042100040060742401e6950100340f000d541d252107541031200d01507000703500d4172a550300001d44c1e840c45007900ca1382d4071503200b001a00b680d20a1042c1c07540ca0307910920b01c06007240d06080c05024507104a440303030002407401132200540005030107120100c00c2507a13440781c5200f03c940c0b94000500320340070311201 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 939331133 1250 939329883 939329903
    0x20c101e1d100b04180b0412031805010b01090e10090209040204091b090603060506090d032706180b030f04060204080f0c130c05040b0a0c0b01060c210207030f 70
    0x70500900118641c400c420b00001203500825040004442c48850b0180001c00c1d2421181e000484903880c06400a80007840351034500b090b018100d000c0e000b800c000b00c1e14103601d48202400c100e4150460000d000d401d80750700314005d0300d441d04402014401c032030950341f80108241c100701542640c0d004007203c05000c0c0016240c03949680340082a1a008040c1c02c000841e603182c2c03044010f03400b01001c80500580c1c038040c40b0303241c903280006015006000c0014480c084088002c400c25018611b4619000544c07184484040441c0b88070303008040e8680704603000710b83c8070070000e10b025a40d020807001307a03800c2c1243c060544d00d4807550b44181440083c01200d14680c01c20000c59a150104030340c80380c101141d002400241c03c541d0a2045800070071032a60344181c1441c49800d0002c0c0c1100698042e210b441300d0aa0b1521000c0500701c07490b490943c006040e8030812800811001c1d07101c081000b0150194046c00d00540c1415440c0c2d0b02541309120140060700084020300002d1040100300b0141801180c04030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 939332383 1250 939331133 939331181
    0xe06040213230103050f0106050603071713020a031518080409090521040602100e060601120615050304110f210a0b010807081009080d181401020c101e 66
    0x8040b4030800e8000365040c0e400000c0403088040d00340205005014103892a0741542080c1c1d1000d0040714880c040003003223219400000b50070442001000840540050070100f070a907072030a00c1c0960703a0b641d103c0403010905041070b002944014084961200303500404032480e281c41c000e0306000810450740103c5282c02849881d04419020030301602001041c0344034079070303220b203001c0b00a464071600050b608071036410308000c2c01d040c983c0850711a500c14020701b0300054660707003007207031f4001404190091010707001c00101c81c40d401544800598466445000c0500c00c0c40100b004110b81070f44240c3d82c0320f50007009040482c01404604080361030b034040083c11903002740c085591790346d042c0c003090f041004160700040080000007401c00281e820803969000070041513503075403100c00c1c0354410104250f003440d845070b0300e896291455a02c0f01800a4002c88400054004143e001d0b020b0361101ca0b502c00c080c4608001e03420807402d01c1c444c04421903a609949103040c48020ba0070800b410020103035001c5500101404 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 939333633 1250 939332383 939332441
    0xf13020903123016030b100801080706020f0a0b13080a0804020103050a1406040b03010f0207110a0b0c07090506120a0b0106080c130504050c07020d0f0c09060506160206040503030703050306040e06040213 89
    0x5802625200e852300e00325903040002d8285010010742c80f6008542c00b0810750070f08080082036440c82d203a00020511a280e6410801c85840003881030010645040040c0e81103003c2d42c007401c500d000380c1c070076a8180440e403641c10001c41903030710a11030b080280040d07501152181c6055840403007107180c003038000708079a01401144412600032503016680b070650500c072082a490301004500241101500036420305511015440e542c1525006844100c0e540f0380c041680303940c414011076401448030080b142c040429161480c00d03e2004e11608000c03900c2c01000c10300074001c0d4800d8032896003803021103140180c601001c0001030030014102c440710440402c00720007d6215a4090444d6500800c3c8002c2c00001700c0c601229028980e50100c403d0f2850302a0501696486200322022102c0f641040c0071202c500740006202c9109640c0156454440080d9103002c050304032014621442c4205e4040008080c21100c458480a0451f0300a50101c1e02662040d0f1074501ca0b88a008040300d1044084110f00c070407141 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 939334883 1250 939333633 939333649
    0x1061701030519260c060106080405031602150c010c02100b060f03060a0e01080d0f08070804150f050901090c140a1802070506040f02040b030a020f13020903123016030b 74
    0x4c00c1c0c52200b00001d058500400c02c100c114014001d616041d10b0701d203003a4a40c00d4490042c2111303022030380030180701c510035551103850842e65280f003080c0340d03a0341e1011914014020909c1c00c0380d440c0907008200080c10360450b07922948416a4028140f185054080020588658401010291310100815000c541e6406003103409000e402144010154418001009400042c1c00f41c1c0600c00c201e00300c020000441e03031141c4041d421507809030300e00c240440c110304910701400381c2d17040005600340360100700101500b0540101d10014000c020b001e10840d11409580c02001c60340c01d95581040c8051410800000319107100107440c061550010300300546a0348480c14040151000d442607019000c0f000207501e0316205080401b50100c0042142c072240358041481c1c0160400c000340302d80480d2550100746151601241c00c04d810084c00e0700c2d00480c11806124003034012810381240b64480b003004a200c9506403074002c54821000005100707668410558802007410b90703d00c03c00701900ca10f000340850301d60040b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 939336133 1250 939334883 939334943
    0x111211b2805030405060f010f03021302090d0501150b211003060c020105041e0b0a020a1116150203040825030f060902030d020705060306090601032301061701030519 73
    0x780b520f81e80c0c145410410f00d042d0026046507201404c4100400100f0340701013510b800c4039419a8890190090750000310020702a00071095004a0841641c0007002019400340c2c2400320591412412107407199216001c07402041c507508000b0022a45004903034540354070f41948202c0584104031035544039510348007a612490000c9015039198404c6c002006003072450021a80a40508070704000d5081c0c846058840000c1e000c0289076074002001e409407445802e000c002010018111101c21111160081d11404144605403901e00e407403540c1c1c0402c910100c200d804a5510200426410305842c5814180941c25507903100c00c002041400400a14140d6988548900030023000a442110340107060401d1450101d0ba0308642096809120540d50041036039000301c1c0c01e9482100990301c01340140c5c002c00c10401403001c04200d4044c2c0901070001c090b2400d0580304582e56108000e10081110203071550300f8000101190407041484440c0184442c0c0100118001c80034490b4400c50b440035003120300044c03c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 939337383 1250 939336133 939336137
    0x9120a051501060807030b0d0320010216050105070503040c150c060c020606030f01151412011b030c0315030803070e0907020c03010e0a0f1401020c0111211b28 70
    0x81e00400195401401d419030004241c00c041c04441740d84000120a1001c0c090000d051000350301e0b8136003808a802c60007035140721094008642d01c150042c000501e0303d484034422034007582008005103d043c440c80c2a40d0060b41e000e0740f003009250400858a4181403108100d00400160081c0900411440c0c000d01150700c600307030083c2c4280c1c1448024942489248015004aa81004420b4902e4182d04d038040003100d018000860007000c40c44c000403000350115880131090340c241000c0f20440303a54080311078800002502c04100000c0170490039002d032520240060112200104100082807801c3c000710340c84000c2c0e240c884002010407000894a807801c1d6682401030b8042215003006080900c01e00c0300602000c4001d068600d25a6100e03850542c1a04009015020b44a00c4440282c002d4050350081c4030b5400090120030104004010b0540010728002050034001450350032590800440d41d020b00b550481824032507601030301c036100b1540010307094440c00c480f030381c1c1d8a0408810114a550402015 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 939338633 1250 939337383 939337423
    0x30503072c01170f07030e0102041205030306090f040309060e03010f1113080c03030a050a0909060e0a0b060703022a1203130e0c0a0f0302091810080d020309120a05 72
    0xd000404610000f40148801840c5606201d0003203000d81c16540d01c40802d1a01207a0805000c071064003a01441d404590800c0b612007040c02080780110246109550030f46244035030b503450315402e010264003030341e0240201e040c1110a0001c0c1d84944d10b840c5900341c0c050004a00032030385460040480f04146818a40c2c507501042c0c03280c0d022106282c1e60300810300c80c0b0041c24500c20001c0001c0c1c03203100340701d000c0060000004680300b034035008440c1c8038002c20141100300241681c6802c6c00f24150012145031000784c0c80c0254859051429809584e00160140d00501d25901c0802c81d1000b0100c251480b000c0070b42214000c6135065440440510030001080091500d0308034080100100b81b10640142d040c0014079010841c44400b104281c5104141502d020380103842c108005600a01c11030302c0c8681c1181e0102a4058501c00342c40d0a68056078840c03041100913503440f18840e40310480910703c540142c10401c03103024185004d0004123800c003642000d480d0700715450f81e40e01d441c0c149034003800ca0382d00f400717 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 939339883 1250 939338633 939338717
    0x131a0a0e010c090b03060a0e150117041a0402060903030f13090612151803021e031309110d09050a0b091903030213030c060905040501050a1203050307 66
    0x800d000e02510314000000a01402194000c0036050700c80c2070091504031580440060b12660f0b0ba02c2a01c0014418000400e28174189140e40040d1403c0c40b06245021032a48031900440280c071010091040c1d400660500803246c00d28081c1e0038000e0081c000307907848901408018a076503410320041140141340d0507040d989d108202a54448000b003944031200741d41c0782940070800a040c500c40c2c100c6003a4021b5031256401030b641d031054020014004009442d601c003070446402c0507000034a0304d11400010720340c800b44164200e4429900d101e14100812882c002c10f00801003541d054000100100d9400081c504001000c9596022640456402d8855074404012042401b00e140400d68200d8aa0f001400c0884081c05080502c1080118010100365001035440850303114a40400e02a41c0e100c00b841c91001d5807600c00400f2511b0a0107000d100d645080300001d280e150400d00c15080f03404490b084049c0b01034a231002e460b00c0c3c000170b1881081c0608c030002440148240d234100190003400803c45080d40c1c1c2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 939341133 1250 939339883 939339901
    0xa02032a0316050a050a0809010815010f0c0201020309040507031d0609190f0f0c08121303030e0a09090c030308060102010b0a03060c0c1415090313030803131a 70
    0x1010005590a1061030103000c9218600030040311604501d0034408901040d803840c1c2070345024140328015006008440e10306080190070001068101c000f6a41c40c0b5407a210041d0010542047d58452070100350400c503903a000347d0041803140590341c01401584d0810008101180c01d450049890100003962240006001442c07012840300c010f85210051071145015990650744805540e48009071030b50045d043e4080010b04120b64400e164001600d0107100c0036894140c2011825019000036030003140c0c101c0c0035031000c001c16500440e54440ca5601c1441c038580701603940220b10b03030010360402000000416a03564500888200c180304118420807180365050060490380042c1c00c00d811a4141017038546a551003003c03d80569802040008400521034000c2d94903910304940100039468004000003040c0000ca0850341004e013070f1200c140240da03115800c1c0d40328400c000c00c0803c881c0102006001154154000c0c582c803807095044030211040b41d403946103007884071150100700c400e024000c0040f81c030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 939342383 1250 939341133 939341167
    0x415080a0203120f070b060a0312030921020a230307031101050c030408180406171005011a0f09030115080c0a051207050f0d0b180d14090d060608030a0203 68
    0x4a490309204d040220000031113910384110341d406001c400d10710011944682d124411f00c4010f5034005084c00c3c003031341844d901a000e00004902503840c0069062400051000e0240b4016032039459809490102001c1e9140654001c51203c0715021980307541801c5c1105c24200001e1846a0080d1500b40000c8555031800f401d42d58010621007044d80180705000c00130f1503034016540c1c2c0c1ca208000340001c00c00040d0103d00100401d9002034800c048082c8018034200300420180b00d10f03616131200344503036078a4880c0710400074581118980098800c12940700311480c048060b26140c01e0080003c00d00307080c5400c080c003604986e5007010046401080e0401c0c801e1401582c0c00e0010402a546030350042a400c0e00c03140c85800c3d0b4424540154110310028038540d44504508240e103030300aa281e0498180022003248610103410000342c2441039254403001640601c5852a0442c0c006071090724281020040c41103103550b241c07089400c2e503241d4201044500c03043c4003400e0b100c100780d0b004544892003214025598 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 939343633 1250 939342383 939342403
    0xc08120112051b0108010303030b131a0a0e06060f0310080709020d0c080403121a04060305060403090e06091602032a01230403030221010608010e06010e09150415080a0203 75
    0x1100300442c8082c0f5640c2281c50a811290542800a00785211501080303524000b4114040700d90700d001101d1a031a02c8031000040e26810070f503001d90149444102d5031004202c00da442a45c4804d0600040c05000c120100a581c0070042c1864040c900b41c1c1d5520301454400c150300051310080c0c020a20004140c1c00d481800c413034502c0c42c9002e4130709040ca038802621807004000103403800c035180c140c8008400401082d40145040203442003180360f5403070800c02c0d141c800c20744044000643c02080080d000c1c11100788036020b0714005042500a480d6508a240d0b029907829070482940030a1240d0945608202c8110140000c2119040401c41015408508403042400e01048a84005a0819003503150310796581d80560f15040c01607030360011040d24000350038a010039200e0110132100201c0d0039a484419a03040300c2482c40c445055481e110010354210308507200c45074209150703500080e81c051010a400d0358900010740001007000d141d0140039000102c40c2c20506a5520003c400011410100111054 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 939344883 1250 939343633 939343663
    0x303020d030b010c020a0603020f090a0308090f030d0512040f080c06010317070b0c0903030c0d02010c03060522090809031006150215070804020103181b17030a0c0812011205 76
    0x50001c031741d000a420000d580100720425a001c584500d002c08c050045501c03508001700b0308400c4035540d01d0515035644c44881614003441100c1c00b00403103030900141400011040c2d0700d0300b608008454800105401008000303451b6a81401319000114111000500d444100c83e4060055507045082c01c2c136090ba8031050001d00742e4001c000b69030104142c0d001098100d40728855a56440880000007455405541c003440d415000302409c0990850b0150305c64444110682c5040c003645aa9030708118000c0c1d5040400320707031070040c506454a1001160320802c1118881d0605034105200e00001c80e01e890000304100a45583e10801400482c40c05480650035940784d1008000240300c109000303071940c81c0580201e0610440e00041400c42e80250008018400c0c036070a015040304207418510911401205817a404041c06003000c40c000700c00d01814020b01030070300001d524048403150b04403603046180e0020b40e2101000e0100407001498980618000c040750100c1070407440b03040c240141401d02140030002 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 939346133 1250 939344883 939344897
    0x50a050c0315060306271501050406140c07090216030e0f0a05090403050705030d0b190803042c090303070216050d0b07031d1b0303090a0e0c130303020d030b01 70
    0x41c2c402e804125021014026100079440f0b8a8400128411028100440b1171032a4019080000f03104842c80b42480351a0b000707014002d04d40a034006650512460007003900143e0051030038110700e260306004101140b410310843e201c699070f400c2180101c1e00310304900101d5210090b240b0342071590002d40400c461a0444022802c066440d0010b541030710548100350181516000041c01d250082095541160300072090340e0f55002e440803a0300c014074400c1d0701075200742801c2c00202c5101d1000c40c5500700350b1300c0c1c21005600c0d081c01c081d41543c000844a4901364445403501103160050a000c0450f8000c440303a85c02103840e810100c5019003082034000c12403020a407840380401c4160741d8400000c031510b80240154480d0f40340c030002100a40b24905a10080c050342a1819480c4000000c105000d144c15180e440807640c40601015260301c40d06220742d82c00744c4010070601c01210030500075908004650b41c1c01e481c00704181c03180140d421311030780142c01503081a900c0150700303900340c050011264024a458a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 939347383 1250 939346133 939346141
    0x1020c090f1f21020901080a0510050613060f0e060d050a03051b03070b06030c0a08100509150708061f0f080601050d181b0b070305160213050a050c03 66
    0x1d040c08000c1c20100d02c0003461828010030020a03642c400981201c0340d01c55074110b000940d03402d5003071610b5800c074040d0141380c0c000641c7c80030104000000c0303035002c000307400a100010960340161401170401a802500304000f2811038625100f07030b2008140304040d003d2242c0c5480c1d406076641c800288154059500704140d40d00182020928000e000d9050415a0f1910b1b0b00c00041241890f110141c0ca034103210006a41040c050310503469031080c0c10840c01c40e030219020405020540200344100b2322140d10660101c02507803020341007a03520418101c00c85800150040b4407c10050042c5c48074070111311300d01300f88089401c003c14036103034004034520030b001c0c3d045201c1e100418880c0c1304484001000743e07000124a5980c8514219912144481c1081c010019104040d40070103a03a000100e031848140220b041040c81a001101d08407251400302e24107100c25600c054426034032407100702da007034540d0004807001680c81e880040008224014000750a1030044c0c0703a04100e440240c042d800b000c0e0203000300 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 939348633 1250 939347383 939347401
    0x603020301050a0b180a080f121801031a030a03080a0b0d02100302030711032a010c0c0201050d0e0102030c0705010c03060f380702030601061d120c04050106090501020c09 75
    0x3e200703d9100c0d0014aa40301145129004010309420045502825014001071030700300006030820030a0121080da1803c02003606d841d40d0324818001440c0030115219a242070340d49c0640c1c0450440107030403a0320005400808000780c08d05111900031004900d5441c148800c0d84514411503413502000d4403000003c00c2c0316000500100741000300d040805400000190005104410310a0341000d4070b8103c035100c901c0c4000d1842a490070355a900b155940c1080191030494050080100d5854252280400501180c004450f180e000760b5a07405000c2d2070f40120010010244000c0d841040b4500255403102c03500d20f0001e0035034149842e05001c150500c0c0b401e000d01d0340c42d8821003048035842d403c0b0545480c0e8100344c0b42440c26100f0744108090000e03442294003500020020185584218140c9a00d41c0c2c075150103851800002140720781604c0b6039001c61000342804030881c5080407542c1c040b6421343d10386800050556400340c100d100001c000e040d08018650b0108500fa414103411101000245405408 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 939349883 1250 939348633 939348649
    0x604120c0c0b03070e15031b0711120313030507170d08060913050a0501022a1504140604050c0310110702060f070503040308040f0905010e160201150618060302030105 73
    0x142c0c605200000020400050151115481801026020200d10600c80c00e65800c0c940085407010130307c0d00c0034005800700021a504554009600090140108103a50103016480c1c01103890382031107200c104070000c0c003405408135a000640c480d800500300075050900011481010311071140c05c039440069140c2003d07405c032980c294400e200f42c03240004c40d61610080d0001c0c0c10402000381590068420301001d2000640060042c1030565140d4200e07141110b10460f009003202c26420f1441d0880002107000c051084107441c1c005000d800c81c40c445a001000c0c6904088064a048896610040300038002d814180081c15004070721810800640a206d60b101074140b0070000000c1c03280380c4c00124641c1d8407891405441c22117420008aa0700c6548901d0080710703551283c0203100b90814140f00c00a8500424060035040e1901c00140840c192030341e60301540e0391080d4032070b01410340d520351a120f024600c0303000908008042034bd996403d01640e5a003800040052500f282081500410060004e0344656103 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 939351133 1250 939349883 939349889
    0x40c0819080a030b010212071b05010207060503160509090106170a1a0105030a0908041e0e1e0402041b0c020f030a170c0102090a06030f0b19090b040b03030c0604120c0c 74
    0x107011a40c011021300403401c2a00903a000c3d03c0b00c00020a1010500405944183d00d80c0000da45842855484000591340d9000c1803040e88001a0200300040c0480c401c1e00c011003002d4113504049080011000018507401c0098002c039002903112102c80390491400108290449254242000150454800001a80010004141408000000300e4002140384c0e00c2421400d40040090381c03550744643c110200704801d0b0400070380302400550041050a04480140d0055651100d80501100e50306030110200308002e0042c0da1013035658480b125201c5d49100c401d08030b450182e03906010050144100149080c01c681d030a030082d4000888540010740c0c45420305000044070f8411502e61455200070b0303001e807080204144d0400700340400055143c2d00f40d04041100031111806120980ca404140030009034a40d03230583d54100264004c0152544503400303441d103050083c0c004a18660644080b038a0f59000600c60320762584407100b04810300600c1003040c600390700340e4a4000c002402d15100c0e000c03024030f45c0c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 939352383 1250 939351133 939351137
    0xd09122d0f020f030304030804020112141b070c0612110c0601120c09150e070e0306060423040f02090c04030b2d07020a05070605040501200312040c0819080a 69
    0x801c207040031030003041640c20841460003100c0d0b07a850701b440d0080c0042d1003174600b00d0200e001c0480c130030f0882e001800340d10103000840b2650703d00b55880502c4a5500004013550002001d0100f2140c0d010072072180d0b2102c060130094860706500d0300c0d451040e5040729a050416082c0d02014040e400340d2000206003281142e034039010007581001075090005080d81154000703d801c0d4605060111061243c4061302c0446110902141e0f25540d281e0050b1003840d074041c01c6590503080400004d07000d1074035034054050134400c28001401d80728a9010350b0038484094a05a801c51804400340003180340845940d540501c1c010146802c15155903100080210083c11280d030114461501707440402085200e0003104160182c3d05d540f5050081002c0c4d01d40c2c0e4108002d54036802542070105141d409202101c00721001a501d00710340103646100d00c0f86040e0307000c240f150f50b808104003244141c0346c0c10280a0065001d04200f02583c0c0c03402505c14507280005103c0b082245660300404003081b060410303a03050003054 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 939353633 1250 939352383 939352397
    0xa02030403030e0d020c040c0807021c230421030801140303070b010e061207050a09050901020c0102220501020601050a05042307231303170d09122d 65
    0x34982607000d40400107030302116100304c841010002d540046c00b18000b43c401ea5040220400544084500500403560080503900040e5000c914440800011030340b00e00c02d00c2c26080724200700844208004a4000940b940040400e0601c6042e0081c51503034070303206405000b40d22160703e03590050300f28001403151842400a480c0d00709110786003442200c44c819409001d4100542e142c10344000390740015103c0c1800340d80315006a0281d0342d800a414010703070b0401403445a500c2c0c0b03040c1501d000760000401c0c4443d9075400344042e00820350300b4006031941454490722444078143e01031540b8050400b980c031550441d40410b004002c1910786003d4a01560420754010409070384052030700d0360380e000c0382002600070203440003004403640c0c1c802d0800c03429805140314040a1960826010102d0081502128008500040410010741a140d8000d000c01c010782e0700c4c605180c800e8030300100f102c82c2d008094940c2540d2025550b20154000f00c40d610741e82c40c104d0840e98440f40700d86650080313110007003038405120b41 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 939354883 1250 939353633 939353641
    0x91d03131a090907030f05060301050103080d2c03120a0c0c03030906090b010603151d06060c160e0f0a022107050405040510080c1002060a0506210106140f090a0203 72
    0x2008070342c103801c006031400d00e0f1810b120b040140203003600c100183c840d41c580004244030b4a0113008084c100d030740100c11541407c4034580d20400130000a080311851100445072001080d079102d590003113882c0120061a143d0780c411001c1c0d01c83d0b803401003881c043c01c2d00d0800d45416039038002004074551605450b001402444525000000342140080a0411249d51000090700c0e40d140e00402c4c0000da0030b040c5403450320b680e0b000480318804042e241c0b85a0081450000c1c4440c10200d0242c824116080102c80001b6081d40312188100b0f029040b00300d08e12582e900b009620b1031404401c40c2c02001811086190900b8800940050704408940c81d41c0201207102080c80c42e4800d030207079009080300400402540c181403040c040c1d410851702c1401e2442c02400c1081040703290000d4002d060b440c40350082c182594038030088100170034005001c0c40d40311f05c484021040e203424030700e00c0c002800380da0300000804904001c445d00e401c4003a0003c00d80704041c8000b00340c81c6038a40d030b0310070790f04001c1c0b0010150700c1e625 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 939356133 1250 939354883 939354929
    0x60b0922111833011b061d01020a022a10030b0a1e06020105010e0a0207050304031227050612060f120322030c1203030b04020301091d0313 61
    0x41400c9004404070344018880200c94441840b03108140507400d51030f045684a90b0a661880080c580fa80800c2d04002d00858110088641d0013404d445014001103025000c1030300c110050451017500400d030750204403c0780054040007071130404a180324030b03820891404151028502c1c0d480111034002d4450004d0700d40024000d03081502c1e9100c1c01081500356030f499028619a01160b001e900880070308002c8000303040c40c010f2084074180d51000002021a82d6000340c100d01a60181004850b00c0c441000000f022400201601da48191103a13191241040c2003258000d1003c0761664104034110003003420000c0d03680380c1c0c04070340140503000190000c0780d41d004001205610121090313500100050340c410000c400100c01408469000183c40b0414040340e03100b42107242403804000c02556182900b400342031515040c49004900c203103070103d840b03000140450300b66082a445a41c14136200c007000c20380800d007007646940d01e407080c400441c00c0450031032a5007a880800d01c1001c4c400b8119100041c1201 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 939357383 1250 939356133 939356149
    0x3060f160c060c0c0b2203050a05040f0f080c0909030316020f07080102030f0a06121e06090b1803130e0612060c040608160909021c09060b092211 64
    0x940c1080301007200c404240f0700648105180c44041340c010308514000343c0f0b01c0d005440d040d0321076400044001001d040603a001c0d2555484800c070310301401810b100000301600f031080300304040e044004449260a00c0c0000175450701c00789910f610b02c104007a4003044a4880000f00740c27039201501901c0004002032010081e800d040c3e001c42120300502508001261042c07054000318084c004074158440c403070340d0314020a4201d6102c1d0240040808000b00311801198180701c010b01a102c1080c80c102c4240300d9a680c0341c0844100540c2121410317000e004214000040f5022490b04048141c0070b5807509142c044120513081442c01144407544d82100800e807940c40d02c00d00311002002c04803c8070301500344400105d44a402a225501c0007541030b00018006a50040068a0f0607450741c40d010481c508190404010b0341000c080380c4183c031560310450081a2550049490b501e0180d0300c000303600d403400380c02e00ca030f68003004100380b282500005203007170b0281f100c60300c6841c52074005031f8400e44110b0f2032001582c65 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 939358633 1250 939357383 939357407
    0x4052e050a0803070308060306090604060921030b040e03040f030b0a02070b04150506010e010f08070311040f0e0a15060e0d08040e0f010f0b16050106080303010f060e03060f16 77
    0x4503500440218900d0302c000000c01c40180641c940000030381d80d40041594070fa8003100c003000503030050303800310303001890a411440c05140301c0c001040484650aa5a142c24070b89019682c0029861303001c0200d55003010b2048203d403000c0c180186107007508210360940e030b280340d038400108404100340005400441c19419120040e5100107582c885003003d007418209668140b950980711403074075000c1184d660041555200102c010b8407000d400300210001502c1c0044011b280e01c042c903840d034070b014140d5054bc1000700301400000b49449446810580302c2003040d90001c1048601603e03007090201c101b0034046440c400c9510503d00165072503d40d01c00321b102c20750141c400500580012902140010b0040300700f6114517900720300a0046d0380e8503203003155580340c24890704000510800101d18100090705400d602940254004114203a5400ca0386103964405da008403502603d040d000d00605500500340f0300707034000450090660382411141c100340340001402c0c074100c5510b5080081d10550103688101d440b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 939359883 1250 939358633 939358639
    0xc030c0f0b010b120606071e050c0a0602031201081b1c0209040b042603010918150c12020702030613140f071a0c3d1a04052e05 56
    0x51543e4407510241c0c0c42e0080a00300c1c0040718101c0000300d5600b005070030b9890040d00504a0000966851342051346902810401d8400f80a1001842016202d248101c002410291700a6544100c1810110625001032b0031020b5140c0140301160700303500c000c8001441c850303402ca81c03401110028480c10212615981002904807400320100001d004070301da4424802d03030041c6440201c096804401e10000d00b13540c3c9403148070040078401440344844560060f1400300d48042a0449440389407a5404020784205400b65074a44500400f0000c2d50312200c0e000040610390810f604180c02a80041d03100c413002412403002080c152784079014403038a1960001c1000802d4144c0f06425402c05455466000034010320300300805203050070544220120455150f0142e06000d411410103010f00e07039a4403010101101a14502c910a681d055641d290548288140c140c1d0700151404076001c20042101d07151036518481c42c0f0b01001c0060200c003481c20020346013a0325031400f00e907072191803120491064641055030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 939361133 1250 939359883 939359903
    0x9151e0a092c03070c1203140309031c150e040c1401032301060e0d0c0323060a0603020102150705030a0902060d0f1a031f02030c070611091207060c030c0f 68
    0x56402c0000c4000d025940c02980341e080003030707100d041240102c10b1000c03004002510045030340c103034850360030050346c2c001070318400752032814103d10481d09400801405809803195a104a2021203241d0b0100f0310003460040041c2d016480d107031300c0da881c070b1412620070030704541c840c0499200c0b680e2295211030001e00b044640000740b2801141c200f030440109001f10000328481600c3c1c80380c98070389000c03110310f820b0348003403503503402415962a40b0103168400c503240c640c0c1d54205400c890191090206a1040d074604400061080c6140002446e11031442c10300e40341d440c002d4003030192040c0c1c00400c0303d51142c1040c00110b88025140301060042c4100070302600a14508640d944840c03201d500000448500c00000417100743d0520105900d40190000b03030300c03141524001101e2040e031f142d009554052a600c6c8620305280e03603900c4031015111102032a0105800008100d0903610744400b2150f2101103000040480d14100180603081100c00d202c05400c0c0100403041c9006c2000017400c107110780e584459451 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 939362383 1250 939361133 939361211
    0xf0203180a2d080f0a1403090405010b070506070f0509120a0503130603050a0216121e05041509050306070c170d0903120c0815030c09151e0a09 63
    0x21400402d80c1e079084005281220002030f0070000040c0030000401120151801070015901d8451101000c2007600a60100b401240c250ba0f4491040e60700800d424612240c1e1040d15240c0036007454002041c46040c042d030040d04002c400d901c1010346030f550300e054a991000c83e000b10011480d00d00da0050007803103880f000400c80d02c513001c0004050110360040c1c41c1845507440b9844008141c2c0240010320000c0010424000c2c082048820002c00a4005041104840b121624100c0c100c0741c18408820104000050411007051030844040600c4204e140023000b00d401d11001a07110782d4003030600c43c1000302810800050022040300380100300d1101c0070f01940c0e11100c14200c80500000a000d401080020501c41180b0002c0d0060108a44c107a41e11038071035940301071b00010210310458542c5e80601c200000481c01e51280d2061031300800a034140806c0c1c804014007041a4003000380b24400d488038640d10480b0843e2100e04690b001e4034607600010a121040060020380c1600b28848907084007003005c01341c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 939363633 1250 939362383 939362429
    0x20a05060c090307050f24070f0501060e0718030b090f07092a08060904030c08180f0a120602030a021303030503012c0a0903021c080609070f0203180a 66
    0x41a5038503003030302603031041c0345c0c3d0314100f0480c4421010704a4010b81c40b1410740303160aa100d44c03504a01d4030200740c80d9040180d182c0710303070710030440800d03045440741e6540d80148200386a2a18055000300b0350324201c040048009041444044a440020043d21012000c501002000d000100101705c140c0219409190307a10300ca080541481c0f5907501c40c00c19611600c9894640e005d42000c030714102512581000d482d0803090040c148030003403040d01000341650048000444a60091483e0010000c0c45140c510414041003c01c0d03003915007a6109001c018010080e04e1400b01c0e00740040b0b60084001a02c0b41c0d035480c600c2c40070f4498500081e45440302c10720003000b010780001c055410717a05d901c0d406039224214030101003d54890344c0c8034034001000d04800214080d00c0d5400c20360740340d4400e10595480030020490010307403040c4043d81e0000300e0400d808100c807a007403030b81c1c09503805040d5240a182c000400c1401035243d100740c5284015480030011150324130f071503084e9000300621842e1280b16a01c8020004 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 939364883 1250 939363633 939363637
    0xf070b150607210e0901090b0a0f05030a0f0f0b090303040317040b04261c0e0313030813051e040f0501030503041e0f090e0f01020f04050f01020a05060c 67
    0x520554003400c442864503400c0c09420758240c2c6038040841a402210311000c080c0a51207080fa034001c0045101c0740c404291910850f42e8001c0880d540c0125001d0303e507504004481c01140c110071031501d03111008202564002414200d580d4008410412000d45070410079110030079120060328403038050051210a510000046101d40d02950f13030b899468469150000e00800d003960702609024500002c18040b9078003411035480c001c001c1405000c9039400122400d81500480181c00075007030501264a030101984c000c00c45100f80c3c15010b1858010b4008120a1651190101901c000c801090029000781d40700d000d50068000188882421058540090800305141007458029414184100c48042040c003941c7d06aa600c400658202801c1000414036202010105c03040314001c0080000c0310030840607140c020f450f294001240032015105c146250854507565000168810006076414050031001d4a06945040302d80400e01c8c008600100c3c9040c1c61301e02c0282c528007620301444030a8200f540 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 939366133 1250 939364883 939364891
    0x5030c0a050d08061518030106090617030f0406050c030d0609060906080303040507032009040b07200303070509040e0d030e0d0918050601091706040302010b041a0f01050f070b 77
    0xb10340300ca0030321040c1100c1c40da009403071483c0c011010b030081034600b1352250058052002611503041c00d000e0640c0c0001e0a40e05c01d5441082d080f66100000d0005195209214034540c0c00d40e0021840c0c03200717000e52162180318910036001041804600c8006040c01401102c00704c00c8801414022a905c071200306006041510528110340d117040c42c0015091004025030b4401d54100c009003106034615103c00c541851500c013a4400700070054006c0400359581c400746806240180b2143c0201e180450018041150b8906404210b4410980000580800004481d171204c5c0919042e5140da40800126002e016404d49841e42e500030320001c1042c80f5851381c002c01c1a1001841255049000c0840a03250001700d8040ca0000301c041030b42c41118078100740c00943d085072044c906501c03d44d9695010500e1001c4110607810182c008c4070900051550902508a01d89021141080300c500384041b038200b2000c000000601480d41e40c0c80386055030f0b00850564130201d0912003c20354410040c9070030169040116 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 939367383 1250 939366133 939366143
    0xb040807050f1e010806041104080f0615091614030c091f0903030810051215070306050a0302010c0c170a1b0302180408041203050403020301140c0a140705030c0a 71
    0x50b602c00d92803802c0d00415019040c0454039030301d4900000011142004c000b414650000c0d00c40fa0b01c03003101d954402c000c100074401d0300c001d89090107200100c1c5040003409820507801c8490000440c0302990380003446908200c2c2c070412a03a12030245542034038100400030155804000c040200040b15101c44000d00213139004a40d09540115070312008c1c8518040800b900c400079400113414800240070741c1e0352030740000c1c0c03d038000c11010340e0321400241040704080b61004030780c100380032084103100d100e260750360020102d04048c81668203200205640e0485ea2101a04002ca400c68200a00880c0d01c0581c0140014008060f85001c4010000e03550b8403119004544800603911090b400200316808007007a2540101055124034407050b00401c481000360040e103d44004110020755129002100384075103100f904d13107175201c03442c500401d400c5844d040258814030b25100100030400781032800300c03001b900c00b60402108242034505010307010301035200b000f011844000764405543c400022004201482a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 939368633 1250 939367383 939367399
    0x20a06030903080a0e10020a0c06060603200c0a06090206130b1e1923070c0f2411070b120412140a0f1205041214070309120c0b04080705 60
    0x32114208032000c4a0034070b11540c0006c0030764000300c0c2154004100100492406407071807040c41d1511000c4417507941c00070010903034812503000990b51740a01c9440304802514001e080448140728a034031030b106a41c004058580d0b41c0c05e11011596240169594800e0581d00607060588503501c0401551000b0580550601171005005140103000c080303032030441c2040100c440d030800c14641074400308402005010203100304108040740900340c5016100d42400780d200d546106250401902010f94650031500e040c5c0e91024841188506070020171507003404524244858000004042d41404035036000040d01c20300c0000c0315541141e0022380e50f80154007400d81044410180c0f40b05136004000c6080c5240031000a0005013100c6006007a000c231603480e5030800b41459081c0045000032100c088904844808030f10214108031948003406218500550342d2032407030444103850107800c26400341b2031803050740034119200302002003090008004000004099440e5916085c400c0d444104900695000b0040 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 939369883 1250 939368633 939368641
    0x3022119031a0d0c05060a1106090a200609010c0501020d11090f030f070b071502030a0903031505010e1c122007051302090a0510090f0b21070c020a0603090308 70
    0x1c5110768003da01081c1812030a181401b44030300ca4021090040610a0192131031104250a1200034810001e82003c4c0003a01400c2c030f03182d019008034140843c1d4155892076a030550740c880700304803401001c003420701400340d49003854500d000e40300711054801640c2c24885169042141e850207002c6036a800c41d009610046028149640c0e502192000c40540c2d104000421000d50002e00800c1c0d00c0c4c1c0202281c00442454a00c550160780c0191084414a0b64030400e2906042c2d042c400d92400e0018189419401898440020204901c6000b80361043e117040c0354600114911054481c41140d01c401034080e4030b4444803001d411400080100100ca2040244071181c0e10008910362003542c20041c05188404480c1e10107034000e4104020490308001c942c0c0001c20b0b01c6d0348994600c48403146580d80c20030260700309500b5500e910041d52003072101070000d100f030500c07241010714021409000d082c8444102d40c1c2c2e100341240c4c0d1070305d04078000c0e40111000c4808107203103605411a80c040d9029494850594079 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 939371133 1250 939369883 939369889
    0x1030b10020606092d06101d010f031b0905211c1106010906080c010c050c010e19030501381c0501020d0f0501050a0303022119031a 58
    0xc42808450040e0080800201607280c00600d030f6400850b0000c1892450112468802c1c8140c1d50003514040000700804011603441c04417142c58082d07906c4c0c58070300081007050742da651122102c11001418011400e401c03448941c802e0f840100c103480c0000034982010f4140d000541342e00010302505004164281400508112080c0490301608120005001d0100c402076030200282a001c00d00d0100529041200c0c081c0e0b8040103014040c001000c0001455450f241e03000745081400380e0458180309643e8001004103c0102c1c80320b485d50070070700740b4030282e402c0c0c03400040c1d1020b50b500040c000e0094080c4048240035055019404e4583c0b10900e01107106e84076009030754400ba00c2c3c1038045268140303ca058203142040b06040c960700510b0380c28030f20600582d548490036604849840384000790f03030303811b405442205400781c2d81c01004240d070900f0316182103880080d110110790400300c0207a80c0c01c178102c101c038507500e008641e9114484200f0041c6540c0d0488024042d00014010a50a00704500204000d00d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 939372383 1250 939371133 939371149
    0x240303110f030f0d1523060405090a0e1c09032307140a060804150b01030f0f0504020306070e01020d05091c0b0f1005180a0e0f071701020414040216060e0102040501030b 74
    0x2c4080a04421141e0f840280820101c0106c150a0b00100140310000e080c2e1a540d40540c0140381404010031200100c00e00b4a282004625444442c075441e0b0a044052682101c007210070707603401c1003410b8844110072041000202284d52580d030180315000001944821440c0324640c2d070321040304c02101495651100312026070b4141c3d8043e04840026004c1c1e05840200d611084140320103040205035269403200417411620000c0b0013110140d101c03420001189000d00000d64000314a0400800b00049440000d590303d510784001803d000001818004564811440b0310464081048881e04031125282448468000382d5850070701c0f20f00701d804126810080c0008070140e4001804017442200184207001080d040905222600e1340c0d1005a4810100300f4488500075610000041511740e02d0258450030441101080c80d8841e44148800e2041004d00914140940404c071005030704c900f10202e01c00c49111144e4001003000b40f600845000c142c0042d00500704642017620304010303c16488051007216 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 939373633 1250 939372383 939372389
    0x114011206051605090d020d0b0c0c0708061b0c010b060f070b071103180414010b2109032a0d080a11190804030c080f0409240303110f030f0d15 63
    0x1007003090103070380f25030f0030004146e6a800c0c1c00103040417a28061901c0d040190358080d103509840c2130002400d98070b00f00041016a00030941e140040001e440c00c401c1249900f1101542c6030104200002d81c414030a0003500b00c800c640c04020580c1b596070704047c04030702c2d15a10000048031406444c50016003028010801044502c0c2c007a40030314504400031081a501c0303006072020940c0650740390400512103030454003540c0038100b0400659611440c0004109001008210000c3c0c000c10407070407c0a005404416144c1040c424151020102c041c5141000c03811007403014548203200e0389100c2c40d200b66000347c0b080d00850f40030b2003c00540101d5003548002c0d20800c0340504502c0c01d0604080151403046002c1d951060282c506064480000d50320014903510031403500c203040202280500c0554660b208800019142c03006607640000c0c0517203104001d840c140b2015052100903174114207659010300c2550401903440c0305503551401410710407811a0402c098400310036242c03144585059020030f84040c26 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 939374883 1250 939373633 939373637
    0x308010e100618121101110a0f08131d01090506030a210903080f0a0215153105041a04081b011e200a1d0301140112060516 54
    0x5541400410f9914010b14074030140d110700b0008000843e5900c00c2a030035046032040c0541203d004003c800100076040010100c05560070845801c0000348038620304400240d48040f04c55140c0c00c4559103442003c135a45d100c40c913120000784840d841d52844801d190705840c03600d40c00b0010394980c40c0a156482440d0f80c03004003105101d103052240d040c50380600c481c0300880343c544800e01c41c3c0c8a980b54021900b001c1207540e035109000c41d0000c40d02e901444458581d0600000094040c94035039600c404550b80e880661380158803861a030301d4100048100c8240700e8030588825020425814105002080704440589140044107848510100181e0b4468040e0b90021101400d280000c00000d1805a50000c005d50b1591385625400d080301101c40c281d0060030003100c0014140103400c1305203d0000b803031040c8800c4c014042003101041d039001a0b0300510480c2450001612026010100c1d0051880c0040c03214284034a9000242c5140701d500441e0995210f1032050100381c5031203000c103102c2d23580c0b6998800 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 939376133 1250 939374883 939374911
    0x709020913092a06020607030203100905060301110310030b161e02070e0a0506041802010f140f0f2205010e131509061d0c120c0c0106120308010e 64
    0x10729220341d03080851490700034206042c81c80d0308407021a085060064603410000300d540020044c0d581c042c0902c6038001860b003015071551405004400201b42c0900134824540d03903400118103142c42c250300c100c0303103158800c800b1030f44c90030103200d00310f003208880c8001c440c8d140c149000910f01d03e0794902c140d407825070070351148031650705450502e50884000110b44811442074580c0020a205181890740c083c1c0c01e031500005542c20080c0500c019030b41e40054000c0700445130710318580182d0f400052030203070b502c2c40e1074489010b400001c902c100901c035043d000f044810300862129103080c00c40d0014440b003500170381250305a284100407a1240d140c01c0c46045c0c082a0244501f0a25040c80110030440000a100000d000c00503050030040324521034001001d006c3c1e8818090003080d80d21400c0082078a9003044925291a00d20300c0c0200038442e05206c1c01d502c45400d00400c0c1c04040071019900c2c00707500030000341301e050b0300c55000c9000c08400c120103a0015900c0000004c203d00599911409221920b040310 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 939377383 1250 939376133 939376159
    0x6011712160206250f03030b060901170c0705030c0c012c0603041106190f05040e0a0e010e0a0b040c0e010b180123280c06360507090209 60
    0x484182c10114848050141301250020603c6050410701c0565102c2c00b06614107984905004080358408000305005117401c00884203180e810560100901009401c404210381e1079020300b0f060790059100041c032a10001ca1040c12a040c0400e00c2300c0d65403003c0e03880e40041d0200030200c49443e602d010044482c4c100c40154039002c2d040142c000c50f8814065940466440000c00c0411107a50244010707002201035140721561300c55000360051000d51240c904141058103140c1c4901d01020054008250a50780f4101226004420340100c80c8040d803d41c103882906090f4285000c030014125422181c10000320008110b8600700d44919068541801a103424403442142c46256041d90340026818407101c1e6094000d41d180c070440642042820388000b07911180d401d030044a9204035001381d1103204800e06605208550b0100245540d950441c034045540060300402d90030000055001b202c12286615009045211342040281924031400c11648910341c0d030101a801c0740150170400380d2181407041d0034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 939378633 1250 939377383 939377389
    0xe0f03041a0706110d1a090c0d0513141c090b0406120b04020a020a050c0a06140a050403050709060602150403080601120e01020304060e240f0711060117121602 70
    0x600112485207100051021902d0f100013040d401c001d01c015811a2140c100780e50404800b5070b030130040300054420500900300080c45080c00d004010404030307144da4860001300f0341030306100000580c6400940500c00c540001c0300355520344002481000d0a00c1800450010003403244c2c401e902240e14010040b4180740c14050101d425688941d0350545190722058003003056510741c402040d21a11300d03001400400903074548a070602c0c031040342052151450715000c01070540c01500c030820740303088901c081e65180da1440c0191614020b907017001d0b181c1c0c4036503100400d00c5403403940b24105440c5980c00b1034100c0440602e00a46599003110000e001500c00c0c400b00c0c449500450044e0200f50582c01c0104040920303076042d50072a001181c0a4a240c1d4603180b003c085100c0510840703124520001d00500301e080a412810180c1501504c20003444c0c000300006510203200c4c0c4584c5150b510740a09690107565a000c05004186400088030100e0041c01100702600802c00210381184414030307015401002e146c1c0030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 939379883 1250 939378633 939378637
    0x17030a030e031b010b011b0506070f11010906090b0c031009050a0905031201050a0b0c07050d0c080604030f0807181403011806050a05070503040201020c28030302010e0f03041a 77
    0x30142442c842804030244086540244a40e000b8207000000340411007540010704c0003a1907030459054500050820010036800f06015500c1010f600340000000704100e030840d05240d1510b011441c9528141e41402000303815000702003a54050740c080400d5407615540a00e4a220036201901805041c4e0002c200441064011a91185c41100005900c19060709c4050466100e840d0942c1c51144c0c5900500c031901e44118000003070010110350605000604a540741d4500e01c3c0d02415200b1803212142100b00601c03400d0b070b04c0181c8901c105a900d0313030a1615020b0076815a801c803400208040400041403140b0a1210901405200c0413001d03449240503541e01740d071100d9180b440d4041d52280c1e03000c00420b204019141801d8481c40c8000351741e00c3d1840540e0100c0742c010741007404001041041c000546c1c0d0000c2c81d4411107008481030000358184101b100040355110318a40d450303002d108000804d0580650141d40ca00709900c040c1c940041811005680f01c0c8501d000d8090800c1416405c0e241003400c0c580 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 939381133 1250 939379883 939379901
    0x9070c051014160507020616150219020c04021e09042a030605180c0c1509030d1407050a1d04050c040918151802040c050a0917030a03 59
    0xc107480040600900340001c0d80d60900380e65450080d66014000100503c0e003410960104900e80319080c04c91030ba00058103449500c14503c6030200030305111040c0a2a040c55041008151900310744c4c0300c0c50310f812280080c0c0580540409400354600300f45141c1024000c0700e220714100b4a0f6810b182ca103008000407240c210344001c1e03401641c3c544d9240c00c2c40780300c155821402c10001840c07805500145400406540c01ea40010b8060141311391410050900d080460381c0044941c1351850b106c50341c4a51141c82c0481d02d00300c040019040500f84034100001100924070941c40302414412070400c200d0403c0200001e07100540050410007807480a02d1040c051704003403c068400b00c04e030407404c0e00005019a41d040c0c0300d8001102c400902009126554411034181d00c0c0b03a80200c4801030115110003658030007401121619648405030100c000d482c0d4008460540c0e4004c3c01001075441c0c500f0018643d8100070580b50105502d03510100710074124491401e44070300c1c148000c52900c8001c807421005084802 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 939382383 1250 939381133 939381143
    0xe150d0209060a03051f03110609010210151701060807030b060604031b090f0b0d1410020d020d0507210c1b0318090c0207050409020a05120a020f090609070c 69
    0x320907544107590324801401c1d095a1540c01007182c0c1020307141c480301d40281c10403280c1c003c0b80d40b03181040018440800441404001c4820702d444900100040c1e0030444001b00041055141c1080c85d11001443c00454040e42c08e603031280c0c0344210240302d0450890b819406081003a6001e0501000026940f64426a100e81e003e44a9400c0c9640d0313581e07000c0c4c2e00340c12411500540402507c1400080c81501c500c9641c3c1407440c3c000d1005c044004080340d41e1441e4050041c102e005000407120900d4810070114503082a00d140c04c643e10448440700b0002500804540039080c1e0901d004541c03200d205000c00e041c110851465841d20076031120881004001402031b500c1806185950a828100c4104070805060700a4503845581056140303800c2400806400c0704401c1c030310b400303002d17410198001610f2040c0c6a05170340008000c0720900000b028010554001a444010340c4400344200b040400d110b03550a10a50b40d10a4407000002005860b90040700c8003504018020005030310148244014002c072030140e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 939383633 1250 939382383 939382387
    0x118020903060712050a0506101101020c0d020601080c0303031b0313080a11060f090a031d0a12060e0606090f1305030a0c0201021b0303041a1c0b100e150d02 69
    0x40300071904102c0200c40340008200020500308503440f150003240d52110850300d0410044c0341440001e200703104000c051780100440c0c85406a0586025812101700c00700e000d007220300c00e04003040001e54940c003d018558090041c2c05035070b1a079007400000d981c000c0750000b0451030401d070035421340031694200510380c118140c50241c10001040b9000300801034991150f0340c0101805401c0011450304034094481074506000743c0070000c1c00e11011504040103585450540c03011501c40c100ca1513105401112140c1c449406000040d04120002c1c0f2a60b490784603d006000c4843c20982d4140c55250031a8016009101540080c6560280c080090341c0302d28404140003ca00c643d86074503246402c46130b10030b004070720079003c4902035607010008200712240d299250208400321a000c03079181e00540c0716883c1c118907507145001100c0003030003c1d03882c46602d460018140c0c02000405401602a0000203030043e07000d4090180064410101182c0703002c000b81400305403440d0302e80207c00c02c2d4000c8500301101a0300f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 939384883 1250 939383633 939383647
    0x15060a020a1b36020c0102070614091005070203070809120607052a0c0d1a04080406030f050411092703070203010e030a0c11011b0606090e0114011802 66
    0x510008079084070400461896083e08000241c5010711241601c5500c815410b0100f001c0203d0411a59841e400c00d854050780b00e00d190283e01740a80244040201a41d09003ca008030041c03581001902c910f005030215030b21010550300d2202207450a40c0d00d440107030030800041010400c0c0c3c0b802090368880c0500031104a0b00c00c070b0b0b421410038405486800018400084504542ea410702150000940c0751005040075561400c0041d03507150101d0b0058060141c420b0a2414001421807080b00b03818881d0a0480303c0c070f410719100c4404ea00501841c408203207042e1919802c440030b4820f851041d41e101c10180c6802c0301e610104600400010082c1000c2407500088410008440c40742c4440c4041c080001c589030419441018259800020320b000711b0742c42401031041a69111940700c8440d500124102c154403000c0c40122400080c0340704c0000f1b03d95410030010b0800c8155030180d01114441102084a030714108907403400c3e6880c110310040c182128030011310100e07104810300c11490100d000c1c0103140c010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 939386133 1250 939384883 939384893
    0x30f1815020105090706020d2102160311060a0606050d050a0b0d060218031906090807140f0f030a05070602030604061508011e0509010308160503130611010515060a020a 74
    0x29055803520010303515401841200141044200c0c05000280003604540000030030040040d452810754803001c0800c109828140103281d030440300701c0b8a100c1c06402d81c000c1c0b142400b0300344030f1303507065290300700d10071100011407100e250302c130341c200340c806682e83c0c103142c60042e2201c030029101c05000034101c0e0303945000400c0d41350358103d0807103c11441107a0240c1c40f46400703034102550502c20401180641c00c030950292049007441c0040c03100d140d000400040070f1a00d41042051400351620040081840000d045040c50000a000e2003da0a070011541c0d02c4113003040b42a128002c90310703a0800729105024440c005800e0390050b581c48400540000303002541c0784102c413140c0b003010760060702091080c00184401034000b02140d00143c124411124500d10300350214200c0d560510020300400b4010608201c10506842120000c0d0740000c00c0360b8603511300b01d0300e801300508184035440100e0030440001202c80c9060081a1168140c140000c8041e00b0200a1040550002d100d5404602400d650000060 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 939387383 1250 939386133 939386159
    0x7030f0b091314030405030604080705010b0616060b030d08070e0f180403090b07111c0b160e03240702073f1113060504060b0315010c030f18 62
    0x40c0503403000442d41c8040d410880c52441d1400b0307000d800e40e00704000900c450740340041d40c01d410a5000040554680c601c0c205203005089061215a01c120000741c00711450b4982d1103400025401407104200c1d0504010030141d480102e02d039240080350444d0b00042405000c0c06444014072000b810302e1040c00314000019503400c90701c0b043c8550841c0c1040602c03090550003078004000d00b17000c654180c602002138550106081c08180058424004450304c103040948140101c40d903d0f0f400b03091a42d090070485404010840c90306800070000d02e0380b4102c41321501d000540a0208001d0222180303840d4140f040c11802441c004285005510a0040005102d490509130300c5403e803100c40b40907188882d03049104038000e01d8071705024488007112245c90100e0b200040250b419001201c030b103542241030040041c05010160710140d44103150641c00602d81524000551040e4aa00840048294200c0041d100116003180260005480d031f1683ca0060f030103400a0b80e071340d868270240600400c1e5070341804820340b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 939388489 1106 939387383 939387391
    0xb1206030d0219082b0f09081602060f0a0e090708060108150a08030c031e120a091703041214040803091e0405070503041a010e07030f0b09 61
    0x1c400898085048106103800b244a001c0b110803200c081103074030340d81d111b41842240748000d0450b12440301001e5000d08064140814940d4001c4030401d42d0104a801c0001000040c0b150405180540400d64150355079540c180c0c001c905100c0c6010010344210180a90035087c4450380c4c1e00a030256500c45622100d000e041c01680380090221034046c0e02c400d105000c00a030721501034a0100041680ca0340048030120605076001b00322500e446a440b28411805074280460f0401e4066003101011038003508060301420f00f40300700301308580c0c030986085074950f182c0140b180c920ba801100354100c002c1c28504890502c2c1c0303010f040d2901c0f485006c44961007043c2100107a00c02c030501c40002900504094010002448c00d00c0000d001540195400c0e28100701070441903607651003201c040c84c140c0c0d40c0c000703407144aa103170a0015000307402c10795040c900050311001c26041540340e0f00a51446 = true := by decide +kernel

theorem cover : BRFrame.Cov 939208633 939388489 := by
  have h0 := BRFrame.cov_init 939208633
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939208633 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 939208633 ≤ n) (h2 : n < 939388489) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
