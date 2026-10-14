-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1053
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:01:38.760196+00:00
-- url     : https://prove2.me/submissions/c68b5022-609f-4441-9591-2dfb28e16dd0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 189208633 ≤ n < 189388489 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 189209883 1250 189208633 189208651
    0x1b110c0d0206090303030f1006020f031207031b030507030c030203010e04020d0c0819031209150f110309100506010809060a020d0e1c031802330f0301060915050d05 72
    0x510f184600000e146a1003241d605254510003c14017400808600c4900040c0c28140090101c1104040c1126528010000e6201e00594035070003048005000794482d0464035403408000da0042c000c001c003c2c0103403100b40c90000009240201e070025241c40381c401c0d0b82c180c503070401480f001500c5030f400700800380c407002c4403d4465111600b00000c41400400c000045003008807c41a500e0f001401d0103089007480c80d04042c0d0721401c113601d07840000e506240c5611005843e036400901d44403109a0407004100380c0003100c906280002c02d000c0d540600292021040300c0d82d8200f0b003c50394074000110780d04c00c81a00c1c554800c1d80664041824040142c01521088090004c000b94840403010740a143c0541c51039252070482181d0415400154540102c004100003408441503205203a03001c5850042d020b60030440c49004031840d4076203914010400d52513049400505500d80000d0251700c0303041d030300a11412020601280000a502c00030103450114201d00c1d0b05c910f81414921500c1001612008140801d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 189211133 1250 189209883 189209887
    0x90201050c0d0f2309040507020c0303040806040605010920070201020c180402131a0d0c0306020703110609010606350702031305120706050a090302040f1b110c0d0206 73
    0x501d40d4204a501c00549641c1d95001d0540825100503281e9540c401001c100081e42c1e04004907043d0f000307411644d41d500306441c00070342642c40030b908034100380d207041100764103000010f400500c001001440b1070140e400b4500401040e646e60140004807050b0b0740e07400da0030054506240b0340c01442140900b43c0a030041c011394181ca01e00c400050140441803001c0340c010342100c0240700560401d080d190460740e50b0740c241002181048402070004119480001e803058001780304131020010a081510000c6500c03017000c1d92030340c1c0c651401400004020400d40c0b032a00c0380100040030080c05000e403904079100c07a00d502c0c900da000b01102446940c4003800e510707000c02e441e0a607820302c0615121164031808080c0e01850f1558900700c056a00c0100d40d5101500c0f41200307100c1400d08800100d0000d04869a80c2400c560b40c03079800c038090342c0b9030105030320181d80940303070040240942086401599002400207504d802115088009981c0035a50340d0070581d450f4004100d80d103c07401c00401c101010307400204414 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 189212383 1250 189211133 189211147
    0xc01120e01021c0506010810050f0409120201020705100603080409050c0c062503060509010b13080607021b0405100509060a05030a120e030613170415110606120a0609020105 76
    0x142a644444414856501001c03d05070025885120f02c0e9040102460003084600b4002d08a11040525021703207031280446890002151340d0741d030b000a0b2219800700740c00c039101e01c003100068004d410210003554540903844180034140514412041581d81c086440e41c18103040c04108e000a080c01440003140400c02c10940380101c1c01042078501c10300c0291450708504007003000184108000308959000e25090400600c150f03900d0010103410f451107284000c0d150f008000c0d18944400e1a0b42c402c550900921045c4504140c2c04107045000c18082010811444040c0c000d2100705ca90843c0c49081102da842014040342c07600394007540d0014002444600642c0e00e8a000901740f06520b0003c07103042d60700244030202c054120031640d031500c50881c00b030301c00c0d482d118280c80701840760800c0080000c01c0c051039214501440c071050300e010740301d21141d100c0c0d00032115001801c03030580100d540126104c1c40c0c00040c41442c001842c00110054030010f414149a00c0c1c3c2e9090203050120400c03818054180558 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 189213633 1250 189212383 189212411
    0xb0a0302030c040b1606060506090108040209040f02120303010e010b031510020f030f070204050a05040b0a05061f0810080f0d081009020f1e09010516020a09060803040603051302030c0112 82
    0x1d4041070034401c45000d035013905c0e0702d460740450f100c83e40b01c43d0051100340040302084c2e0708450590740c0302d901901d61034850742d074a242c034032141450204001d5103c0e040b0f0310b03090954038000010354182e41c0c0c446034017003451f41c0f1160150001d0004590414007030b84a6059040701e0701f05081c0d02c00c0e861203180100e6090b10380e440200d0b41960401d042c0f0200a0102148020961400b0b006081d004210800304010605007600c441044000081100c440141c031400442c280c1d407500c20081c00c100d800c1581c0840c80240c5080001c004980503a004144801e54180104128002040546206c0541d500502000c0040719003981c02e00030003444008080100b8200043c0000140028401c41e003060302451b1381c2c5e018081100c440039020326080300d44014140148100c60340c002007102d015040d00d02d0508810550b0f440003e00280e015004914080d0500e4000600d82000001410a8034110b4506001c1030780d61044440c640d100d01c0c04080e501d0303800809144500d500841c80d1130a06c85610001240340005010f030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 189214883 1250 189213633 189213637
    0x1060b030109090512040f0b0714030301060824130905100603050d0f03090b010308161205041a030402241603020d0e0f09010b030a02121f0e010b0a0302030c040b 71
    0x19401d4251900784460402c0018809520209145d1311101e0a050500310b119030001c120380101100c2d0500000c10405100303000c00710103503d044001c1229641d40e120400205890001d880c6032950603050140d08541110000c004c060b41d21005e0221341000b901303000210003030014103a040d136040c05900300d030b120003138443c0c0150f5001e14020001000170201c1d1200c02000701d541d40c1002420140b9100c0c0d4800007480e905203160441341c00503655900c0d000302d40340030700e40c4880417007000300b020220b099940405500b04018000301d4090343d45041c01411010218805813108907002907002c103921007404122603100088000c007c9120f03403102e05260900342855922000d80c14250b001d0303806880030108c1d15512440340101340f00300343c800000030a4814042010500306001e04294507801000080d0519416415500000114055107003141490f800c0040301041d0f489517003510070352610021503a903840504107030407181030240c41031038400d54213400c8009400c003511003c1407010400c0002000c1040c0341c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 189216133 1250 189214883 189214889
    0x3021b0105390d0c0e06030a0e0601150203160f0b0a0207050c010e180402010e0402041d0a0c091208090604080d08070e0102150402060c0610150201051b0c01060b0301 73
    0x8070b44000c0d031041ea04000e0100d001840640e4540911612910091591409a46410815003c045458104440c0c180c40200d1030a01941e00203e0110802200301d501d40c0020103400001400d5550590301c80320800c2100d0101358250000d80c0c4108249043d8015136030154648a020300c451180000c240e50f2040000d0700e05031400d030420381e0007158000c1402420311100c2d451000900303108071580002c2010584c600503400c0360b50030480b5888002402d690280e0319800322a030700280110b640316107601004850308101c3c0c590350410b0101c0000218012040e11078005118295110702c4041e5182c40000484000b45500498016406002d1202140c55050103000500020380281405584510300140300000041c40c41c3c0c1004010700100c00d807a60081a0081f010921a40c4140599594004101d0501c42c44034101360034480c401c1007201055400907200151407101002803904007101400300c4c20b80c0c3c1c0c29a0440c0c884490813620921841c6448004e00084c1803520020030007554510f103d03d4640c000340c0c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 189217383 1250 189216133 189216151
    0x141b01020318160e010501050a11030c0304090b090106080105060309071e21020a14010201230f010603090203030f0711031507020c03030f030714040902041202090112110103021b0105 80
    0x40b00102c0c2d000c0c803e10903500c00d04034074001c01d002c01d840d00c0f14070070b62008188503460501c0340005148944d28440c003040040031030464103c035034030104145031341e0713496000e4880c00302c2c00e038506403564041d4036102461504a0f02d40303903244a416403c01e800c01840b548080c1034482c692151030340c00070304038403000c042000c0d03c3c0f0443c3d0b034514070314601060700803a6161000d6a03600740c1000c0b402140181c0d9100b17a000e06945900c1c05a20001030142c005038010120030303551850200112a04100e500c40e8104403600c04d20383c100c0c00c400182d03030b50740090f0140c40015400035816081808140061104003003d025441d0090090407141d0f08400082030802230310645440c00b4020550800c02c65940420000d0020030301a001035140580d46640740c81503000241c200020020402c9550140314402c0c403e41d4003070f0101078821903a50740c1c0c49040941425120314200d010340d00c6840001002006032100380802e54002003000c1100b10001c0c0114001c2d482610441124007850500c41c240d584244907407440b0391b01c40 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 189218633 1250 189217383 189217411
    0xb210c03041208190f140c0408011404030207050609010e12060402040e0c0a0509070c0c0602010605040507140a0e0a0819051c0f1407060507052206141b010203 70
    0x542000881030001c5034a4000f8410000d05108061400344c40c103d50f015090140003c14401440001010306510905080382c220003105001b07031442400300500490701d0400c001c20190403205800a6068000c680180158014400030080c031b08110000b003075440c2051600740c5465681d140010070101e04441e810119170700003020041181000d02c181d0211821402c02071254443d039800040700445e0f60300800b805200c5250100d43c2ca030307001e464201c084903030081420311215103811009008007400d200e4144030b641030001203a4158041c8038800d08041c41020a03a2034440803c1060310390381c1402134a15000b00ca201000070300741100b8005080ca501041085580003807150030207600e0401002016568210812a20701c11244c00207108c0c034181c900ca08000803101103402c0e06001d14003030800d0207018513081004110303050740d028005001c110440050058855000c0d141609250054010000804c042c0b80160080e15101d4002d0300e0203169100141e29076101814281d801c0e0707082038601ca0f1909041d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 189219883 1250 189218633 189218641
    0x50a02030f0c0609060912010e0d140a0906030b010908010c020120040506090d080d050a24030b011802090d0f140312010e0408090a3c0b210c03 63
    0x348800c20344208400d005001c8542d08000041c414400c4000d054890308000400d40340a4403034040ca80e000b580050005c00a0180d200d002070385401c0000001c0c0e00003100d9107014103040d08500d06903000c01c00e031039680106050910405800a12802c50042d0601c080c100d0002000202402000d510441981c0041440003003407808078415002402104240c242c10302041c000c0752141c82c02e0b1030010fa030880f441c0c1c03125012401d00d20303614400e42c0008244107041008001d03214140d42c000710300003010511b0550b200c3d4200d403408212440940001010310038541c004010340084013520009010044c0320052070045902d0000328030015505084500382d180800002c00c0c4061640e078a0b1007154803501039403510000c017628103500e00c81401845080d840e207801007418003d5050544140d41c0c030250940710003640f545c61144004a901080b00755284000346440384400602e90010f081c039129404445126042007000300050300504458044013000000085c0e04024504146000f400117603030003507807428 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 189221133 1250 189219883 189219889
    0x15080d030f09200d0c0b040e090114010e07020c0303071b0b0f030121230615011e031506050304170c03090904020f04020d020c1506030312090106090603050a02 70
    0x11840510451285040888008a002410890f200080c28a846030102c0800c80024802d45403803400501060517410000c203e4020b044010804d42e01150581042c9569030380f2168240c40070849082140e810000040010010b8004c813903801440a0058492121154001c41c2c0346400c8280c094890442e40100c0004113241c404802014116030f031105460803488001c403200c54070043c460103400e0201d07041100070442070001032041e07091b848400b1480780403608458000006a1060790103490151801081d51082102d55115000d001a1035500428a4050b200d0300703001c81160000d02070685403009007a03880c1a4145000141c01039440c2c4589a082c1403c052500f114aa00c0c072100c00e5000300001c000b088800800c4e00c41c3c8200c221000c40b181e941d24404980e0310600711300380031340103170001c01c40303a00703c54058000d01a036014500c2100d0030704460707080c0d080c19a0002d58407607030184c004102905c0e0600140f891198001c00c40e0001141c401c0c0c0d210703801002c1310619402a10560030000f40b280440ca = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 189222383 1250 189221133 189221141
    0x9060102030703020a080c01200304060c050306030a140c030d08040302060c18220507090e0610050304080d09050d05040501030c1419020703050105040804051f080609040615080d03 79
    0x1400c0c4010740c20704095a5000e0341d20160b10f00040d00800010841d10341c200c909400c03080c9980c124880c80d0400314090308031f400326900141c80848030681070201c007011003032261060340c2c8180c800600400d40e101c1d440d102d821002c0b80c20b24103901c090054040030f480a413030401055140040c10368403802c2ca86080d0500a003442d6003e03001c0c120b4400101703c0c020100d036a039001400c0d02c0758101c4052a0783c0744503000b95001201800c8452500c18200801c1011031500711f0f02e40030445174007075855582c59907850208a1048540d0744c01c0e070003182c001c1c804140071402e65805044c94400801c40040c1070490340d242c1615000540003160001070b030001d428011968076000c0c808440c80b00b410490020045045004900c0c003626510040c054040740011000b13a100300322103002940c100c4000c000609080c1084040ca0348036005080c091141c0b40002c1040c003c00f000ca2040d40c401590740e07108162540c004000d44040043c0050b04e660762070754181e104565000c0301c6000144032890051902982600c1d0240590b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 189223633 1250 189222383 189222391
    0x6010212040911091f1407120f05130f080d020f060a0209060f0d1a09040b0106110102070813031103060c07021e060d050a060f08100c02031306170a050126010b0d060b09 74
    0x10101c140706400010b00491808d95607140d60f030901d004251000007080f80d06001e496900346900c01e10000000d0700b410858500010380b4140d0041d40ca8441600300c0c280d948240c1740545686907485480002e295200d154081d00752000002c01003071810410100d800c1042c0c000700c254402c80f81d40e5110140140c100e82106050500040ea12a003c0c2d00c1c0913254240c10340c405200303480c103010b842c00d00542c00c50020360482c0c038030a90040c01079844940310b912242d09011240800c840280d05500c00740040d00c3c0000704684201c0c0301001c0e0600c0c0095590034401c8041003004a010f040f007080c201c0125030303641c1c3c501409081c5003040000a680c6842178041c0142c0f5500d901040c846c0031160002d010b0328801007581c0300b03c0080300c8000f0030a001000d4049207144604484034a510140000110300c0742c0d80701303220000109103400e4144044d12007190100884a082c400c0104402c0c800000d09031000408464503d1000390750000541c4e51040c030086042540001002c8030303070780d40d24485c1510b86c0c0740055019400c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 189224883 1250 189223633 189223667
    0xe010210060e0402040b03010b060a09030b0c07080307030209060403060f0b180c0702010309150e030301150f050301090c0c02060d0209090109020a020c06070c180c030506010212040911091f 83
    0x70841c9401c14180501e0809080680226151017201085413425000061004c1c80580500e580c0e4038201d50090100b8118002120404000000f08070500101003d0761344298128030307882c0c40c2d030319806000d50007580413840050b0010f505100000c041905072140c0800040002c501280401d441c2c02005404039041e22100a50a485014000b502d0151400e45145540c20700f80000c010f807040c2003210b82e40707450200000480c1d0034801c080304090b2012011718100c40d80d6014002d15490074110940d42034a1a40d10800013883c10700040200c502650000100d125983c20201078400341034011a0300f0768030240e04200016000110a0080e040a80c1d80c5401031512090450405007020343c0251116022041d961040c0380115111342844044015a80203041c0c038000d03240158041d00c0c081028020110500001c2454400050815400410300c8000f1000d080e825625203824542c1e16070040015180c0c01614030b034144441642070700c0e86031145a4100790031005003d0a910550020510b40194128880c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 189226133 1250 189224883 189224891
    0x4080418110a0f110a030e12010216151e020415050c03040e040218070206072a02011d0d081e0403080403110112020712020c01111005090313060e010210 67
    0x3100e040c1016100120050300d42683d00c42c41e54401250f00c10040210341a04d03000b82c4008501b010380002407862001010340c1c090190009503245e0b0742c200e00800cac0b015200d21540d000000001a4500e510b206941f1850354002101c802055050031451061042d03108441d44c00101800200078001861988041514056140c8484419919240d010340d01c240310fa4041c1c640013003402c41d40c6454800e1803121a40964109600e040c260081d42c40409544400100d1030724a071031208102411500c43d8040000c2c1441441f1035555401114a599464202c809124440c0d000d408036560380c034040c44446019800654441c5907030701300c0c2182c04444940c40420b816003040304000090100c82503d00312904143c07500752208848005941002c3c24001002c219440020341508029841070121550600c0d41d003100d0300c180310440159981860002c444285601189040141640e1508003650000d88070f01601e0034140803051103680709000780c00aa021809503100c0044c03650703040020150881e61060244 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 189227383 1250 189226133 189226151
    0x10120504050c011b0c05040f09120909200913020910020a061112070507050705090c030406060801021c0f0902030601080703030806091e0a060302120a0b01120b010501180306020304080418 82
    0x445050f05842260301480c1c5230f07240c08a00350f800c0c2e0321500030f0603000b010381034030245e071048002d1102085000302c1c2c898529115013402c0f02e4410b900b140080018006000307281c0702d500e004210321090380c2e10b2302d140d51030b800700085017150b01c41d240030181c1100950000c06481d20320345003c2c001d44900c41040315120406110761500c11020040d01d640013400307403c0141c0c0d0b0358003a0900d40c2c1068416000150452440c009112081142c08003e62081c3e015490400005845071201070a030f215800002d0201c030010074081a01c90b02a6020348071110048100140079034641d030119080c20b009a00160840d0810710b000c1051641003915690320036401c5540c40354500d00080d040011000c20190a1001c546042c0040d01c9542240d101101a54004001d100798a0082e18102c2d540d0340d0740c02c0b0842c1d80035038440000a40b0100d218280c0700b9039500c41040c0782c40da03007090011110040c5d01c4140c0c4058240100d0000049031042c8001d5000d18041e4410301e40d81c0d030800785403601d901c0c88400d140c803031103280030b0341e103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 189228633 1250 189227383 189227393
    0x21507060506180720070e06130c1d061b010213080d09032a0312110105010513111213020a060f02060703020a03020403020a0803030a14041110120504050c011b 70
    0x1680d0010702420400c44040e040905c0c041c00c401182e40c091541e102d0300030003003600c5042e010420b10807403085075410885101c540c0c412007038405110780503011031011000c01040b020704034260040403801400b02410444804075000d0701c03600003043c45500f030f540026004400920804280c4c0946201401404d80d00951000204401e00074407001e0041d1280d036092000d6840603602000014604540c580b0314940c484c2400c1d01c10180c03828151000c03408042c22a1880030042c0956812100c000303011070041184c2010f980080c00c11710101400ca55401c0204002291700d035001e083c091660380d100e07a4410402c2c0d20600a40400580010040c400c1d180403400069900183c0b00341c1c003603040d282c0580c4900082005401074051078200950051146001041c0014000095840b92041d070409000300f007200211035880d010241c84c0681220b4241c0f50b20703000d9007007070119190400701070f00d454500112120b22072021500c0580e004c44540e0004603400100e076038090156109190741e003650582c510900d0b0b9030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 189229883 1250 189228633 189228679
    0x100620060613020705010903020d0305090c0306220807060e0705010305090a1203060b1c110306060a21060e0a240509040816050d020111210a09021507060506 69
    0x540b04640150352660b45a07001d0301500d101c158008001d0242036401d01d03000e9119002c5184600009140000081185500217541c415000001d0041c1043d5201d0303e40d0610032447d602ca80100101d491030142000a00000c000c0c8640c0c4d0040c0d01c0080da4a0310302009908200140c0d0261b0f0400d401c0c441804684200460704402840d4840740000c004a0b4003002900544a194840c000d00c21002c40c090319014a1980e4805050044200800424440803586c411500055451301d40100341800310105060040414552202004080415100109645805580d0f43e90429214045108107010100c3c0703c070300680203039404c20303003001101d0f01490000d90b01040180c40b810344130b10f500f03501203820700c000c4004490f402c0044011914041c40581070040e941c100d000310460042d841c1540607205800f2010030b8a00d200040302d601c10850031420407842140c071000d01040d10132540c40460340c00503903407248003104940b00c1014035501d4619600781081160001030401d400f40003110000705e031004460003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 189231133 1250 189229883 189229891
    0x306011b050d0e01030b03070b04051e030307030c030f0c1502070f0516050909150f07022a130905030723030a021c032313050610062006 60
    0x18000e40e81448040d40344103030960640018040d40200046081081d5008941c07101c40002a00c082c04414a0741d018166a1002c610801500c80014041031040e45400017a044814031048c1c1d44142a0245c1d0b0300181c1150b116050440109941d40d281c1004c264025084480446441c24480d860359125103500c440d40042580460419900050b020300b0008402c5800c10040d4110f0100d0b00c2051321000344000e000c1c1c440c001c0a2282622400160380e2410025440e01881544545d5180c243c65132450504401d2000d0315070781c02c0d80a100f02c01488400c200b07410070000980b2000c515881c001049c2032101c000c040301d245a0700349042542c400003181d40002119907240e440302e266843c01c0140301c0780f035600407035055018041c0d010000b0300102042c0d000420865000901820403480d4684803420340071540e042d106c1034100d5060320714242c2e145000c048503e0740141e51032001c6000307481a5488500744038007107424030017139410284103102d50340d405505e0500c2c014130b078044000c3d0360300909049942c4a000078 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 189232383 1250 189231133 189231137
    0x1908100915090f2d0b09090a06151d040b09030a020c13090b0103080301050102070b0702030d0f02100e0102280c060b0a030b04050a12260406060e0c04150503010b030601 74
    0x910440c0210304030360700c403007a219541032009030b10082c00300540c070101c20301300e035881a043e062805000071442c0880d2040c0c001c1708494001d11a020841c0d403000b0241c003038103400600c000000d800005601d01c10401901c003500f40d030301c00b0187c5450a450500d5a51801905101ca141e000f801030082c80c07070b000103a504516900300c49203007041d40345003140c00251880d520f004000761001ca00020401c14684040e41c16170b41e0980035110080d03282c4000060f14010100301a42c0350b03221036145090396004999a071003004683c0706440d810700103812000107a500c403a00e028200d81d030000e42480312780841d00c1c0554144000c0c5400031019124030600400700f003001c0c3c46c0a0402c41e610f6000c0091031351610031303d0005562010141585180c242010354684101c503100352501112400466a010311440030304035201e0a501200344031200c000c034824652440184202c409076620000420031201c00390065115141d28447c0030b43d26411301049158182030301a004003444018070041c0308180c010130560f0340c400c00038 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 189233633 1250 189232383 189232391
    0xc020d06020906161203140402060304020102070b0c03040f0b0c07032319050d180b07050c0d1412030417090102010f0614150702090c07020303190810091509 69
    0x6080c500c009100b0114202d43c007080001e0401c0c00c00c45140318104189001c0d030100f250390791148034160141d440b004403030b4225440707490004005181c9400a1034000707006204454420741c9801006803158003004a407103040e480401c007000074070303c00c44504001d807003003000107810120001d44007590303a0040c0c00010141250010f03030b404080040c0045440b5007030008215a0800c01d540800c4034000351100e025a040c0c0280d20b0b00001c200e000d000000003091060703079040010b030300d0024494a150081041190075003c0c0006030191a81d8441920f90040c0c06080c403050940c41c1d904102d440d00315011a290130402040c0100404211500102208207417145000707580c941014004074014034164280028003454510301042d92000b04a80f61040342055610701c464800426502449001d0100000d520404d54000207503031500c03074005485480c1c0b0249c21203007012529409480500c1803180000c0015400f01c040094140d10700c110740004105100c010001d481041030345148000e03c2c1d0003003031429034903 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 189234883 1250 189233633 189233659
    0x7060f1e1a120a0b0403030c08220809040b040203010b03060307080a03020604061512030207080705061e070c0b1b0114040f0b060312121b030601080a0902030c100302070506160c02 79
    0x903c00c4185240c0d0100240c1140d103410b14000d0300400e13170510f1400001340c42c01d00182c022460001d090440350300d01074204915030910f544404055102940d1560000d450361b800304010346560020350701030301c0c40c201003c0d205d1030100103151400705c1da948100b681d98000c04c07422001ca40c02059a03030b000b9406c810042501c10708458078a602da02c880d88164007100c45008420b044c15800310342c1f007040d40e44e8101951041c1d81d072002040504e008084403a882d1815483c0303200b4100c2507410050400e10321807403000340d50319603902c1c060070650800281001d8100103641d076103240c00c6080c402c041360f01c0d070b407203032181003504058035402071402d0f8222000f0308c42c990b1038012800594081000c07002840103244010fa9810000e42c028415001c107441d481560000c050720b5403114280c980559100d40340c1a564040166107400c410742c007800326083c003070360907002d200e240e041c680d1103000804c405c200d40c0b61000342e0b4601143c6441890042c00800c1010b40311107000038a031036264090140d00f4419012140c1d0280110 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 189236133 1250 189234883 189234919
    0x70b070e0a090b040b12010917030606040603180222060b040f0b090111011d0c101b081204080319090503040b0918270705010503070f0507060f1e1a 65
    0x24000d07411607104042c2c5480c504200c00540182304c0c854851000c14031503001c010b41e920141e0000341c40c000d9006405020500c0f6503446580080c02c1900c002d40581500407403500428500b41000182e01e0301d1510440023500c0c21800744c052580103151003031100340340c103113022441c0c114480b140c040c005803400002000242c81c0c4c801e10345014100c1c1404020002800d20643c0c1d03441e035070000200c2c0c480a004014014900b468620580c003070204554449041403184140c40031071103a4051411120740505000626617200c00c40045480796210314070749503890800c1e0500308540c44003e50401d44007800c0000c980d00041000c030580b02202d015400403a242c150280000e908000941c03140750030700401c0340402214414050b010303d10071807907881051600d440010903c2c1c0341c1806014090100e00f04002280c500c62080211141d030900d1480c089080c0328140d0b0318507041d900807500105409448628039410b451440600c082c00000d64941000f840000c201d65030020180c894000348100701040e041c00340c1c06 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 189237383 1250 189236133 189236141
    0x6090302010e0f130606020d1407030305060303070f0302060f01080f0c061b0f0709050903040f030b0402150a0924140304080405030712111c140c100203070b070e0a090b04 75
    0x14001044c0002401401450034000c180c81e00c69800144203071a0501c502c1d900800d0324940340f0301c108200500d807401c0383c1c409402501d409022150503203c01c018607000700d1412401a1502e5200f41d01a0190b820600035901c003a20042c4c0020007160001c103c940c20a010000f02424002e0007582d90a40740d000200035144001140202401c46001d88143d00d02010740204c2c40e902a05c04002c1308000c0f80d1140e5806a41c1d9010700c0c043e9000e5006012424000320b00c12807038031903000d4401040428519100070f0211096081408461b0116104000c248840c1604106d00c882d004184100d0f4440000140d8000704010b14103050207d220800002080600814504590240c40080e04549126940e0b440c00880003506000548165006003420782e030381d140408010075491142d10000d5501c02c00382d15154607501010014610f24803e110a068031926179a010308400c58858028585403c42c9081011840a0040846042102c1c11040020396600c0c501c5c40300968502c2c1200189030030184000c50014 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 189238633 1250 189237383 189237409
    0x50601030e19021e031504080714010e070602010c02120c010f05010e100803040501050702060904060509010609170303010509130c03170403140604080f0a030b180403140406090302010e 81
    0x3070141c00b124824030400c0c2164401d01d18425680d11143d1442d40c000c0400d03c02e02a000141d1517003011001d0700340f0110700c044c903035005801602c400c1d140049542d580c20300031001c8103048516945480e040c503c080428040400100541d00081c401c1d00d07880701009460382c1100254540078003000c601c122180b403095102803c1c1814409c401c21040d40c41d0046068201c1007140e00001c0c000030340d00d000c42d126070007005540441e803042e10741c0e5090101c1ea50811000d07070800903465402c1640ca1000144c0c1b036460b08032241c02400c03103840e0602010704140c0701c10f0030090b0100c0e017501d96500804c0104a43e807101045240e012900100300c8010340b615180c06030000146510280140030b489030001c1c10008928001d00c01c80f4402c04501ca0215081140e4503165581200e004c0c02030b0b10b0034059450b524800b203004090744c400d50324000809003044000a2074100b18601802d80b0701c50b1400c1080100340d004140b4100003000c02407601c0c1041c3c07030810300412221190100904001d012210645280c8964a070503600c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 189239883 1250 189238633 189238661
    0x102010e0c01120903091725030302070924061d040b10051b030a0201060f08060f0601030b0d021507021c1e06020f0304030c0b060402070c15091505040e15100305060103 74
    0x540400c07402d11560b581c0245255803c10002d000c00c030555440032609003c21032b5415006000c4040c0b4140c0420f0090402101201000c0201c4061710040d0416070700e131002409d829100d0740a5241d1580244c40f4580070b00c111035001d40d1928400118035601c00e04d07102c0401c84113181243d5203a1504034a041486c81200c0d09003810f1001140c0c0c4100250190050821b840c4c00740080c3c003406d80c3c3c6040d16590340d0401c0d1050f240940180c800704000d54801e801c840c040200151a060304104581d010544c21241110640c1c03410001013814821854010312120744101c450079038011440040c3c40e004003010188021441202948040b24200901501914600c1e0005e284454491800707080291100214180031600309c2c00f800b00180b8980391a02c05e40c0c00c2d10350445210044242481c0004440404410b090001d0001590000503440d003000ca80c00d622074116515191203921b00a140f8175200f5014004107048030381c0100c00e9496803107240584555890a18010590b030311007800603401032203070a45281c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 189241133 1250 189239883 189239909
    0x201170114011209080d150803042607080d1b1a06030609010e0d2303010b07170405010503240916110102030c160303020f030a0b0102010e0c0112090309 67
    0x2403440d4000c0c1407a08058080e29500c001400c0c0301c03030341e400304e42c000700f03005040690500c025070340d04090f43d0104120300501c2083e114100d0325504918a160020750000c49071700100641034101040701e060540784120420028003866042840803074072082c45203410403c00ca4004020780403110309141c4444500d802c02c100948508181e4001045010111a1640613100b10808034020000c1480307040c420f02c40a43c058002042030010456403a4600d034800540c40690103102100c80a142005600038141403030b0f0907a540149282913107072200205001480b885c0e0900040246076040b0040381d80c0000d42030f040d0f021341d440503902c5602c06500801240d4200340c16004010925981c2c02c601c0030b174203405032507101080c00704111311400d0317200c11200d0340c1182c101401516400c442080310f90071054443d0401500b040512035545400e0b40048401100003a00c0c2c0a620b4019602072084260300c0760214003801e02d1144600002c1d15901041c1c840c065600d40d17401041081c54490b054006c050322800413088 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 189242383 1250 189241133 189241139
    0x160b010f03210219020a0f0605070c0b0403050a0201080612060f09010e0c1c050f030a0f0e090609010b0307030608100606030605101e0c02040e07030605180c0d02011701 74
    0x300000650000300c1d500000246071401d01d611001d0580118a141c3c0c2c002d22080918214100c0b8100446504030780001d0900c2c001300700c1040d0341103260042c00642c0d980380e40360809400c0039040c001083d0f1204d40c3c1001c04200030b0021810100350700465540a091079100380d2a0040411744446270000188481d004d000c0034062042d498241c55402500d00c18020300002c580390580030345900705031011650004520a145215411004030b4014244c0118262484c40341c118406504552100d50300d6000070b000c41c140f049a00d80c05c004020044a4141c41c0c43c0610f00d40100442c4242e03a040c05010304500380403000813107070b03071087c1c0001c4040d01700142515514020700010a000d00714a014610101e0300384040443c281c00c0003045043d03001c43c544d070b4040751811031120044001c030b11a0506010800e009242001503101d50240b80e104010000c004e00a55142d81844011510090807104101c0400248260079120000d0b40d042c1c0c2ca801154a0204401d43d0300c01a15002000000b0180c1140210000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 189243633 1250 189242383 189242399
    0x70203011b080a0c2c03060108030909070509030a02211902030106150f0f140a050a09080d090902220f031401021c05041a0a02131403060606160b01 65
    0x41412441c454a40140d00d03212031082009a4101481d45000180c3c5201c000d410410081c020140f80a00d5580302d000d25240440881e05040b0260010149a407000034503854506125600d698045202e280035401c1082440c0040c1d11802c010700040c0c070503100700c0081d9516020140c590b00e81521041d04072042104590340501d00c3c56240c8406920039460000002101241d514281100e0842903841303134401440f1103000c2d501c42210000354420080b8450715040c0690000c1c0003011a2040741e1145038071744407044401400301e0303c00e821040e8550802808040c8041c2c00400581c20b40703420440c00750300c0f40030881529501d001c0d000310702503001c1000e10000907400c0d420702c09002600d00400e8000c04800d050031446090b407042d007075032091603002201034804018059200907005403048160003030307070041180c600900040503207550001740d50004010452900350300403200140b80c8541108a1444103d00094450b000100840e004540008040030902d11015503001c2e000d0784900c400c0e40c156192600 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 189244883 1250 189243633 189243671
    0x90708360d030e03031620060408090f01210c050d050a02070c0f23061b0106050a060206131212090636060b150d09120f05031b07020301 60
    0x38071004289421002500c2c020301108a07889001444550348165440c4501282c005610710f92010580034080002c540180c03040c09014061b50040841d070340c0f203000314010404005614013042d17050200090b40e051380f0302c90755411040000d030b20b05e5002424040cac011085d240b6226002c01880950718202c05c00040510560290800500034440090780549411480d08207400d81d01030000301444110601d031304601a034940d1040c000300a410503040c4101110148a420581c981200d0b069454020034000390038212880001000181f0040c4020f003864002204c20000301c29020b0841924402c0145115001c0d40402d0f190102071041008407481608141e401081100b02101907070650206000000d81042118900201c040041d010100004d503256002003c001ea040d540010050424a80c0036442401600c40b20703100c1d000204030b10f101031a04201e058840e4000c00300b8011030f0501e541c141513110041d203900001510903110025001502c0c0304e054020828000c0d0b043d03003480ea0940900440c1c000d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 189246133 1250 189244883 189244903
    0x301090b041515140f040204030506040c050f04200702010201060b160c1208160302011104030605010914221a0a0e100204060509040203040807050307030801080c09070836 75
    0x800400b01555032070031041c1a14403401342d412101d00100301d000d280c10030100101c03500c020801880d041e0389980f0142420b50466007030740c1c04546c24070108032606068040c0d0301e81800880e410000e814a181407244080103403800801c0c0210041030681c1107900075401030001d0f01000700d001d0b0304d4000083c00310541a814140451b189107022100040380e8000d1000800b800b944000e5003030402c04000d01952000381092405d508640d20740c40c280241e414420700030000b030340c001c100203d04d5604200161054030081030300024110301d088200500e481c1000c00607074520310801e8001620951504114030400101013440c944101000c0501c903401442c0e0340480064180a81507800a000d02c0c0c4106080380600d12600740461000c00c4080d042e460150300440d4442d105905c400d04125941d03c40c28a5600b100c0e000700e002c1201c003401481113580800a032000c10504884801e51494800e500030401040a030114201c041c4042c140c10000400030003802c0360384000c521001c981442c46010303a54070035510b8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 189247383 1250 189246133 189246173
    0xd23010e10060f080105010507051204140a0b0304020a0e09031c0506090f190f18080a0813080702120129120109120c03021606090303080906150f0301090b04 69
    0x5000003516409202401550f65460300e50080d180c1c030302001565207a02a06045586005001d00011070491013001b03000a0410210b6880200791700030103204510186802c0003c40c00710500402005035035542c1614242ca400c6a00216a510f440e512315146010341000121619441c4000305480c6909034001ca2207040100c41940c07558071484491420807405880c092056510340c04a100c0c03604003600600182ca070751800018405181e00400034454650041c102c4101000083c8a1016540000c1554200c01c00f840044542c8407641d80e100b0191094080003406095014042e91400d0790a60000030490b85581c000101d44c0307441024a4840024401820700c1040301e1208095a02014410f490500e903010315000300301c951003807080d5a1240030003000c0b42144201e1a5403000700441c0c41141c0020800d54551031421411440c015107006001010790060b036000b10f0801c00c5c507482401c01c6200380d000c02d81d8911040c15a00d03020030302428148601030304071ba603104240b20410450000a00c000c404507 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 189248633 1250 189247383 189247411
    0x9060c0503040308070503070c05070308070b0105100e011404170706030c0f05040306090c030c17011802010804030815060c030d0e07080619090b1311060f0d23010e 72
    0x4440503640c900060394007074006a01c42c0002400d8a028000840d0026003904200003e20500e69409240200e10f070421142d40e5404260340081160170b41d07140380505400c035402840c0ca824890014010380286003510704000950302c1035000c2000100407a00502182b002e0003002e5580d074a031690380c2e06803900c42d4000181c5006900e1426622844038070540000315500d03d8507052440e200c08001d03000341001601d04c060128000800160400084801050782d5480c0b03400034803c00c81a1800c5640d004492005040c12142c0300700142c0e442250145e00ca41d147c2000206500c1d4220003034500442d402280760403080014400c003040c0000000703000361040041086c00354074200b92106d03460322090b1103003001030b82c02040411090004480540420044e120000401e4480c58581001e40c2c28259003410f1001c900c001e02000744103002c00754214444050703501500c0c1c000388c0c8034401060301c500b20b85507044994a07243e1600c58404c0805ca6540d15503c0f9113145c0d101d50311a030700c440243e04207850011280c106 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 189249883 1250 189248633 189248651
    0x10b090601021f05220b040302010c0e0a0306050709080f0c130b210a06090c18050106050301170f03070305032d011202030a0204110c0111040e0406020f0d0f0906 71
    0x8009400e4414142818500241ea0100802000505000f518202e60205c5415031134040840c11600c2c280300c41c1c080c01098001d03040c6828040e003151942e0310000700300003105513000e806448502a40b402c0b26071147c2c0000352542c0b082001c07103c200290b00072036070b2402488454040b10100003580301c1c08040480d4410f81c640c0745150300804441e040d1107140d42213000c7e24544084c1c90140c0c41055250300307040080e19091210b030b980e00c6041b05c0510701c040b1801d06198009016031002c0c03440c580201c01c41d0401c2080300794103140000d810b50105210b0110704200c1c00f610a004c0e0481803064102810400040b030b600d0320410329020300150070444046401303010760000980024919069141c680303841346c0000c00a41d003000ea01009400e00098240d8051007607600c1c80e00140c460340b0840c0c3d440840b03c201e4580b22181c4003405402d490200e040340004003400e220520969029010164103e54800001641e40364281400307440c03401021141404070389080314141072001d054000e9021688030b00340c00c03c01c60f08 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 189251133 1250 189249883 189249887
    0xa0e040e1213080c100e030a08030f040b01080309010806100203070b0c04051903120c02011e110606010e18070c080406020105040201170423010b060403031e020a081e0405040905010b090601 83
    0x80c4d071100d0a80c0c0151030500c50800700d401000714580754a0090306803854115517444001c0140c1c001c1d00d1824001121030100030038007a0b44801e4a001d4041040039507d44090b1100017002c0c400041c00d01403090f1011041c6052445c0204100c0d2441580710001403900e2400c80b100c64200c1e00548038150140d03840c3c0c480800c808001aa86c1781c01d50340e016100c942d4040e08400220b540d00c1c180d071000c032b060000070070342d0002003821400b82e2407104000340d40d40c900c583d00d0841c8243c06c004028001e2814000344504031181a6240041038003017440c2d00e070074445140d581510840d10300700510401740c20750710005000b080140d810341100344682c0c002c1e00d4100881d07074504003440b4064022240a001d480c820103400711017003543c0c031802858001c502c1c0003041031628900042c48075030140e40118041010350020b8405580445055041c2c021940058800031400351070b80055031191310f0440604091808007004084820801d9401600c400b600c2000326a505240082c000c22090545a2069818400140c0c040d8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 189252383 1250 189251133 189251143
    0xc0804060608150c0f1e0c0d030b0a0e040611040e1807030312020c07030605090a020405011409131a070c062417030d02030718060203040b0a0e040e121308 68
    0x35007002c460030f029030f2000c0b50f04003580c00c455080b01140e802048034000d01e03c0f403049012081c0e442c0030103203990341e40ba1040e55480c1161314640581031605100e2081115a104000001120312161114201e0303a00d40c40c0c100d00402c1c98108070312501001260229410081812140c8506094046068000e0300000400d50b105440c1c84000c2c00100b60b0440030420710104d401070100c80080390200d6590940304e54030760301a154102e4008090b940107240d40d00c1903140c10b0140382d0040014000003259611850081050441c005012940c075146c0c280e010020018251005145286105064215400d103883e005000549008047ea2031a0805114220b000d154a04109011482143d041d14207460025076004100020b1000c504a02081c0108403902c15503000a61003210f00b42d80d4101c849074405c40c4084028400c0d0081e100315407091100380500780441c0201c075240500c0e418500d40c0c12001c0e00015001d0042c080411845008003480e00b0b1080d10581c02409204505004003180c49844542466a072 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 189253633 1250 189252383 189252403
    0x1020301062d0c050309040f0b10050412020603042a0521060619030503120402030d1103030109050c04090c020105060901060309050a02060d0e03180102060109020403080723010c0804060608 83
    0x2c0010105504012402144414911403162040d40d041501c0d01c40040d045802031a00c1448060300c072042200035141880c940ca044c0d49180c1011800c03d0b08140041da400b05c0e0140c1d00034069540080400c1c1404040d030801c092107c408030705c80404c010b89101c8801c0e801e00c50310510f4000d07042c1c048412006000305d0a03c801007071a000041c109540c5600400c0070368a403403040d40a00b400120340c0400450002c1c4014114031440c4840b40040c0d0604d4414107290110300100070013000352401e401c401d9410040116811560003003404a0380351141001c4c00c560b4030482d44444281450f040d410040c054064200c00c0c07087d04111500545070f80d0f106d00680031395885500040c425001800620018940003000d01851540003000090030300e9440f49151441c2d2110180580d00c50514070000c40e42d6904100c00e60250a0000044d1f0400e440c41e910f40b40f441c01112402880d09284101400d8001c4804805210840c4060000d00000130071081c00740c880341c030907101500c1844c288100807511120004501c021 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 189254883 1250 189253633 189253697
    0x182109091b03040f08090307061e080f010e07020c0901080c12011e02070804030606060512090115050f01031415030114091e0a0807060c1d010f03020a200102030106 72
    0x61a40ea542e1130a0520714190760407510f1050030312840000341c03420040c40d8090400c40e107a4020680002e8900110804c5012440007000704100c01c100a420724100f595045030851918100c2d240c40ea028240e0602d010285807942011902000080d11040002c00020b06501510f582d0006144d503403070507007a941022100518028450680705400c3c0341c0d0760081c034016029041660070036469507100b1058070b00c00d40c81840040d0011404044000c1407003032146e00b051180d40200640900030169046100482c07180300c0c8502c2c01040c505840f82d0294000303007905000440462078503d003480c2440718010702c03841042e0081d807034980c0f040e219210b485565406582c65000803c0d01c1f03100c000f012240740380741d001802d240b0b0150080400001d00042d01034400395208441c0400e03113101c2c162004100b400010510315015003168101c840350b0740c00c03101000b08107942c0d2802690791081304105641450f22000e1203001d0030a101031a030024141036000e5810b07038400ba0394940402e480e009511396407000a80103440 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 189256133 1250 189254883 189254887
    0x615040c020c012f01050a0902130b0114031f1806060306030803060405090f0d080403110a02150c01060f0f06080606120a02070606030b090a0501060b040b03182109091b 74
    0x1404941c0f21008403589104c00c0b1040004c00f0700c0c01c0f80d9003540c109a800d0800140c41e00342c01d008628010710501c0941612110070042c000c0c00c03200080c00f00d0340066042c0e09070900080031801d1104a626031642034900150a4444550f0b0360041e212904448000030008620b492008592903101e4003a400031290008451030654580034200b200a0a000c4c0c0b401265128012004408840c240154105a01541c450305001d03e01410041c02c54501c42d4921042d40c0c0001358114010380d1000d0042c1c140360744040c034042d21614002162401440b00d0380100d01c40f0a0780341e8002406c1c400710f0f0316003002c4e41c0a503a0303000c1e680c2c0c41e0102071045a0150743c03c100d051003e280b0010b080c005907075026150070303409244089036091782c03516500e40e150019114401650019042a0b007844800d001e14802000781000c0d4500d42844e040418561740405000c80d1041c2660b0901e80400d100100181e00c2610400b1607107148909004250003c2c40d4802c0080d0f6008031504000a120726813036020003040300f00840f000314 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 189257383 1250 189256133 189256157
    0x70b131401030603050a050313051f0e2701080f03040602060c0c03070204090305191d010320040611070501090308040603020313170403060506092211030615040c020c01 74
    0x450640ca2a09103604050b074a020000114604010080c2400d020701d01442d81c40545044c0d403050030f00340f034105a0166a0b90070f0240c2e02c1d100b1905080110303039034900d4980d0038601c640d030000c0d4114940300c502000d40d0b0b1828840b418403c4241d41440d0482c2e03142000c03203080d41c02449400e5140e0103144903940158006000154080703507220010103e03030300c4a4058902e80361030fa0740020115912060705400082000c6110602c1c0d4401500704091103c843c01c0c07002c90104480c100900f02508819064100342e20780b0f8903040360f0004a003001d1540b2550792182030b111a05c980c00203101001c42590002c0503c101c2030001020350203200e03810192600032a4142c54503041ca1801d5010b94030142c01c41440c444210401004510196142c200c2e00f14250a229559403031414040156503000d02200d20a903100e034180701841021a040501c200020314101301103a504c0e00380b00c5110000d05c5c10654150054100300705503000c001d0708072200100111020080300585c000e00b282d0b01c803803942046012500003000d076 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 189258633 1250 189257383 189257399
    0x109020307120c0312200a050318030a0b010909050d030c08070c031707020c030d0810050f031221131a272d280203010e0f070b13 57
    0x948014003508107140000c0d52680c5c0c40e03030900e0f12026201e000441a112000c0c041110507203804010088400816840010340c586a40b00e00c00c6001216022241c07006489894030140008414280c000f20f43c40070795a9940703410b801030145030710b044800b030003040b1030550740b60f0003449644503255541e035848000d030381c0d010b00c15140c0001c009002e5080c0706000c110700c5075615108405900c640b2069029044001d24507080c1132822101e9074130701c424000454104403030120151480b0040328000c5546440080140000c41d00380850000d8050602070009030b032903600006801d6008100000581000d042d40d2094401d802c1c00d1980740c0d0043c404041c50849210b0760700940704003a0003244400d102001401030408401107040d01038140c00040c1c02c40d07081c010310122448408a00ca402481080349240144241d040e00c40018040d00c00309501d800d0648414501c240000c01100343e4003030300070415a071903001d50603503500a40200d00071621689101040c0c0e0550481515581001c00d005004602e0400000e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 189259883 1250 189258633 189258659
    0x7030206090a05030a21020705030303270604030314100e040b07090f060801030c080a17070c050a12020915010203121509190c05040b0307050d0617010e0606030109020307 75
    0x22040e84920b05080100c0c05940502124203070038802e1b6524001d140a00700c5045a007003440721001c095400440003006a41c03008000c6940c00441c22a41c2c003010307480036165181f803541c4082380c09400e1140800700000c16415a1010b20100e0380e072075003040c4c1076071a10700344401c0454a000e035428210813900403400203010309403410b0300100b050502fa4a801e0f00c402c050a2194910391042c0c0004444000400520449164044c0078108010103003040030b000c1e4540c42225000c111540040f0400003e4500512031090700460103804002c01d141004c2da41c0c2c030840c3c004142c49440c02c2c1d06c168400000b01d42101c011a03015400c0410680196051101010001e5100072005082ca0184809508604001d60b590300a0030f00c290007040044c2145c1d45105140c01c2250f96204418040c0f000400050204141c6c070420383c1d030b00030414940f035596003012203894006044541c2c0201c50881c0444044501080190003401c445183e0408541d0559144000c1600741c0301e001e080690550007c1c1000d120414104003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 189261133 1250 189259883 189259897
    0x309030a0905060a0f0c0f0b07020a020a0e0705091207090c17070201090b15120a06020a170c1e0904090309050102010b0411030c09060c0d020106140405040312020a12050c03010509160207030206 85
    0x87c01c3c8600703a1998403000d01e00c00040395200c0050b00300120707420851902c500d0f46070103080f104c408041140b8001d00040c145108026030329100713213122007802200d000c08025000180c80c511078140001d403031140d4082c00b03480c50404807800880480c0f0000320086e00c14031408801c60b03000f1035002c0f55610b41e0140003102c40b260701119a001007001c000d000140004000710401076124040060303039032008072401010110210150009880d4800602820010300c0069617802d446800411003412060b0703003c6002c40c0b1070f170001c00790820b0a06000d0814180c22000001c02c56100303030007d100140010302000300325260340c18019190807007800446c1c080452503002c1c03e26204094002454141100700692a0100d0451080c005070344400b010701004904400308079080f841510184940e080942e8003074a1010b400b11035885041d80840c0162106d441090750050380e600d0f800c1d00704400d05103001b003528180e10134013480e8041d0501c0307000708640020758540e469000c1074690291100a0540c3d007003141c0350740445 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 189262383 1250 189261133 189261143
    0xe0c0411041e0806070f0215180a030305040b010902092103070804030f021512070e0118080601082b0804080f360120010608030309030a0905060a0f0c 66
    0x10002045214a80e4107200e0b544090b03166101d00b491410380c1d03541c50700c20000c10300000c110550340348403200c0b81c0020b0844440d00034005450b01c103a440400ea0000710408403a000414841d40d60041c043c1038040c2c1c006400340303015200302c03492680c8074445081644140d003c4581c04c010070310a8080300c10b4055107404400820301059914062494480c0c071040e401c00e0b0026140c3e44850b40101c001c514100d45041c0c1e0f0a9040c1c45420300707100c00d00369111540c0d0401017500d400d101c40d0a0155009a201d810324040c00382c801200c100380c01d91501100303640c0e03403003d0058102612601c1085585500e00e12080c40000780321a50701803412005c80300c1100c0380c00d0064800c42c2c9003e01030264400602041c0d0180100030802095090024041a51410b0155049004404000096169a030f440e6404600e12442030400d450f0107101204080c002401042c840d44209038602005c07085c08030070040480245081a071030f540b40b074103071a150300400440c1e228492002c0049540c80075914005d42c01054080e00090141c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 189263633 1250 189262383 189262387
    0x110406110f0a0516060305010303080f040201020109060c090501080c03040c0620070320010305010f120f050303090601032a0512160303080709080105011505031008010e0304180e0c0411 81
    0x200c0701c240c502509000e08690726000840d07458100e04a02d0342040003040c42d85014030140d4990b441c0680280b1000c1c0c4035500c8034610600240959000750011070b5016480b000810480c1340c0a01c00074080810b40c0501130024661802180c0d1020340074007942d004030b4205040d24001441d019040c0c032202808058000340c01a01078211400002c00d00881c3c000f540250003950a191038070b071504034426215502c0505051900c001808030006070700c8040d060712410001488442114141328101031195031006219100c0007040005488002c20114100ca100d40d4285e030320810074007445004002441001c096003000e07403c0c100682d10f00a403048042c01540c5044c1c45016440040c00420310100c0e030000e40121f517480b000c1c00885035005a1290043c120000200091b50410640d0800da41145c2c00840820001202060103c00c0c6034030404002c20400c0020405480650903a9440b074020303200301f099000026110000c00740580c0a0b0500c0207860324040c0030307052400d008100c01003641400d210224002 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 189264883 1250 189263633 189263653
    0x3040c0b0c01060e06010c120f0c0b0c0702010201050f0c0d05060109090e0f0c121908090a080f060703022b0f0213080706030903080c0919090b0901080111040611 71
    0x20364801020103826000010071041d081071506005044013918035410040759030855000715807404940100c41c50249020b580b150382c040d4040743c5103802c0203c041d10086a000501910314030410040c13640c1c078401c2c0c00a0010342e94500c0007036680035003194a5a040c007010804070501409a501141d84144141410304845891b00c10300012510110300c15100e90b40210048044c10710100a46044107200302c0c2d20f580001c04008405468030640d92411120004102a4038104082001980d041c1c0074090000032001c1d90303903d80690f603507481d10741e040081c3c0503003000b151840380b0074000c541d0000d002500804031100d6070f2690341c0054403290281c0c403c0b03a40d140c8007100110114001844402c03081c0c0141e4007003c0c10100541e051032800d0f0300500906150030704903800280c0001e4007542c05900400199103c070340c0304004c640031a003c0c0141c1c2c17100034111040032941c650700d50301000804400b0fa0303103241942e032500c803030b1802c035642c00148002c0034030288020000b1910401d4103881d1103080f04103641340201 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 189266133 1250 189264883 189264899
    0x910121112010b1615020d0908032e140a0503010e1b0913020d0f020306070306030b0606071110020c0603010b071109010b0409091103060412021c0c03110a0b1510090b090603040c 78
    0x1030514111807209d800000c1c00607203107040c0c1c080079a440181c12442e03160321080c40d008a0451441c42000f1586002105140c40d5540d4910140b004040242c02030103095031070341e00d070740d112003819520f40800b010042c5100306c44c7c00c0000b0583d105420002001784103d0b695001c1094909054008640c25020038400f20010388040c0500340c0101103940b0040303503203411480c210041c520010540b80c0039460900400020550301921880609415140826003441080049040042c0584000d402400020000a0130b05006005020040c09400c490b0040c1c0000400c00c40030701400c0c0310b5403802020902040c4002d2840d40e0110070b082c0d109141451103003c3e071a001c40d04000080318155440c08c6000020560583c0500030465040084a00d03088265040c0b203014200134240c20020302000b84180760b800710f1060070030100c01800c0e04241140000e140c402600d2810742ca40407810383c02003000340300b0a140c5902070300c10329064a070501c207414208040f007018400c96802c01441902c50f04000d000006002d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 189267383 1250 189266133 189266141
    0x60603050303060117150103052a2503080403030f0e0f060703050c120c030711060a0b0111010603020303071704050a08031315050910121112010b1615020d 68
    0x103104501568403072401d0400501640d848015812904511004200300703a124128a070140141c24200022140c8034284c0c4038519031004018034400b5030001c030b501c0c0c14030740d80d101c060040000c0444004440b404030540603819032425010040104e100d080124002a002e80c0052000c0c20031700100240a9032100d20151405013880450400c0f40c210000740f04007140e16000f45039001102180c881c1c5401042c3c000a210075200401c407405034840400460f502c0362003a1241b03035485d201d000c100d07802400c01405640040a04040e0781b80454100b0000c540300d8141030080300100ca40040c040d40c10521180c84881100301104074681840c1e00c10800407589035541009403000d0070400c0002c1da142c0c10080394005000c146038004140c856170001200708086d521600712884240e06860710840c2d100204420b5421b0426a005600c0c16801c0c800c040d2180b40c181f80250000311844102d020b241d0741d950101c42c80e54442da00200e25104841400c00300400d9075141f20b0700030300c050100c2c01480c1491001d4100222 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 189268633 1250 189267383 189267389
    0x21f050f070f051002030c0a03021c0204030b060f0a0f090e0c09070504060905030102070210030903200c091e040807081e03040209091f0e010912020102030f0c0703050d180606 77
    0x44105000910502208102c4c9002c80604824110f185041802030450fa60044071006400c141e000101895a1510509004203486007020705640b5141c4078908600c6c011401c461850007103135a00141c4210b0b00e00115070008a58107818107100301d0f400d00760800090101606600301510a00f401407025844070090035200c1c14042d036540f500c0741d062020040c09041c82d580201c5c0b0a0380140f203150003603999242410701c030320901d0a001403035030002d00d0f00360741040c04850040d03508036080c011107840c0003002c512000324440403203809007140c0e580c40720307255003d40301c0e0681000010b20400240000340b052005281d11402015910b040c00e40203400424003080809003030704a80d10110610045060640e00c0300c2c4c000807400c000c0c0c00141c207124207541482040d4108025000c0d26901150320100e02036001506250300080084800d02e07003040041d02035802074683d800d45c41041000210400c1014007030f9102030364942c0da490329010810ba45c2c0c4016195034800320031031000c540c204000064980c8112401 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 189269883 1250 189268633 189268643
    0x15090f0e0601080a1a0108040f060905011a01090f17100f0614010e030d2012030609010e040c06050304080c030c070311180c03070302090607030908010b0d021f050f07 73
    0x601d480000108107001c0503001c44582e07400d00c2d00100381c1240040100440890030302e021505603440b810700104805280c0c80141c143d918000b1407005102d01900b000c0d65144244240346110b492090044950746803611813013540003040001403103600b5a807169244080880d03c1254a410801041102110125440805004d640711420048410005000c960001003420412080f00300500481d03200d109200c035403010410b0410140301007001c1050b42d010050405000c80f003001d51708441c41c0c18207500559103240324441000000816141860391030b0b10a90f8041da1404046103802401e40b11070300040c00840344076034103011804002808201414000421000070705030365155007041c45513440c408418602410648440c0c070840c039008030849400c03040d0310003a543d480e60b4a4901320000c2c010f411300503a2040d400a5184e0034140c3c0702d481c06083e2805c2c0d00082284404200070041a021003010094020264880c00c04d40760b46403130180540b105807410710902c0e22081c40e50f410b030b10ba030100c642150 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 189271133 1250 189269883 189269909
    0x80706050615160b070309050303190e01020c030301030b06040908040e150d030c020a09060f0b0903150c190914060706060e090d140f0403020d08070206032706040c15090f 75
    0x2c140074582d0304d207035000a21418200a00c0d002ea0303c444e5182d10006001c844110800c0302522640c0e10168401100d5a0007070008644500d211241248c90381d20038403094a0b40107100011410a240c0742c03040207040340e4055200d5107064906003504014103001400c8c01c8054443c11540d0080d0b441d940da060703008621903641c0ca500c04601e40b04001180e40e540e0003030f0348034518054062100d01c4400103c0ca0603a264502156114840301c3c00213880c240940008001c511106001e000c188440b0201a000d10381050b14850316540c0f00d10411103254110f0300c100f04696001c059110704900713102c6c00400d8454007400d00407402d25102c0c5090886040c080e1800101644110b505030807a0350300c0500107007483c1d40c544141c0e00e0549914004501400349000281c464032f6003050310000c0200c2281180d030000c0e0b016044036164541440082600c110030740d00d581d0300c0902c0011113401c1c031802080b0188510350011203810f00301d003442c0c041c2c07050345e164890b0703c000c1c0803441d8404140d250f0801981d800800c5e0309000c0c90 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 189272383 1250 189271133 189271177
    0x6230415030605090a050f18030c030d0605030d140a050f0d09030206060102240103240906060501030f230703020405040e030316091a030c04120609021507080706050615 74
    0x21041c1300c0000e004c00800351426003403000d10010040421707040551103444c030340c031084a0000c0c582541b0412035489d02c1e0b80b20004406103040d0050300f080007240e004900343e031070030809520207803110100c0c0a01401c8010341081580341d9240980060034041413810341c039900304490441035800300c85040d502500941d00c00d4040008a41c0e0400040701840701041034030404264501c80f883d160001800010304030320358200c1d82860703c0707032a101400205900010034401c6070070505144005200700e010741400241403d40030303c26041103010724400c0781040313008003a50030708440c0207294404020b001c2b00105902000000f842c0e80e20341c01500e040307080001c055981c82c1011800410f0210803046030405115019a04000030340d000740040030100e0030000003a540782e94010007413038640b185030411012840c1f403000310020b001081d44540040c40c802d5442c0c0403070442c080800056030161200c01000c0ba030003009510000340464100070741041000e03180426003e0842c6804602e40c10150f504010031a00502e90 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 189273633 1250 189272383 189272389
    0x405150d05061b04060503180c0a0b0703030c050c0606040b03010618021305092203030908040e0f0907080705040f0902062106010c02090a090507030203060c040f0f06230415030605 79
    0x100b0b203949010840e55241c05d1800304094224000201410300d808841c001c1c02d0408041400103041551000b841940069100d40b403c0c001e41e00070000560002e0301d48650340007140c0c080c10485420441180c0240300c03959034a4100005404500304498240d5224400000c1080c90040c00b071030069810100941c07100c2c040300c9402080340c019031065114a2520092055014900c00c9182054600c0207441094800c503040c01d13000380240c00401002440005030000d51100300303c042d1805a8800900c1138020b840d1801c4140c2e941c4502d008100d0103401403c410402890a90f0101c40351a07c3c0d2440400c1e09000350f0009005500310014181d0000d1030394041514003240610b0302a8428000d00f801c0c90031070030301d401080104100400340828256900744042c140101000b582004640c01812140b81b40740080703840c3d00b560042d10072503900d0740403e4000300c0d00e40c0f45000d5940c01e07640c0b00ea680c540000802c4020400d25040c07056407428881081001192903a03082042140710461a10041b5060f4a82018 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 189274883 1250 189273633 189273661
    0x1e0603251d07050406110703021c020906010905090a020d150605130602070b0d0b01030902090c19050415050f1303050102120708160e030c03060a0e19030203090405150d0506 76
    0x205548496141e04001070b0710340080684096840c1443c10003100501550400d10702482a00040d500540060700c0b8544c4d1201160203503a811300c20380c1c00c1029903c17a80c0c0150782c8003056014040c1c1c4401c462001419007807495028040820081c240400d5041d840c080307242c1d190180d0340107000022800505c2e00c01e10007500004800804480c401881c404c0c0c600039420441c0d000720040d10f001a80c440c407060250382e10a070000b850040c0c00030250082c83c00d05e1100c0ca44c503984a1144400c100c000380c1400c48801380a41c01783c03401c80324100388015060000c44c0084869074811010701d54009420b2100351413000100d0000006144200300059807510760340100ba281410003003441c010040d85a0410058003000400d443c500d02460805c14810283c0d04006810003607110607240c4c06100302d0b01088600401a0400200320230804c1c240e61481c0c0450610074502c6da04020090b0151348100901c0b88070741040d40c00b207a4003000c1003003881c030000d410300c0001c1c40f041c003201c0041e185c1e98045d100748049440b0b5407003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 189276133 1250 189274883 189274919
    0x11090106021912050403021801090507020309030604021c0f0602030403080105040902011b060f1802040506030a03230d02030106020f0c040c09060e0d050313060f0302031e060325 78
    0x90810b0388508148900c0c880070784100a05900000d90f1403009207010740c00791000b4580c02440392140d52a0910403001ca401c00348194082941841d005c1884e09002000311003010300050090070056031181c0a004840c00c0d01e40c00c0340c5420396207100000c08109554905040709109040c0581d07070f4202420020f19401060700810311480c68403608000603070304540229000403189c990301c1e1411180341000801440c01c0729864000358104041e15030344030b2080c007982402500c221810415502c1e88818195a119509801004500420740070042c1c02e06410009030181c40524040d8038244000c0038500c180d0b0020390040b00540d228924007180b5410a000682880106942c10070140301c0ca107400405203d0326200b507405212080d00c618086846051060059541002c112662403aa070020010402c429108140010700070b07000501c0085d02c01c0c0200c901a60600310030006495652003c2e180d00080502281e03410f1040564114908131262035003081001e54580484500349005000b1411044603c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 189277383 1250 189276133 189276137
    0x110a050109080c0114012123010b0a09020a0e090a060b0708040602061b030a0b12031801120204080604110102010e010c091715010905070504090f021c05060a0303030c0201150311090106 81
    0x1840b8410b00344441c0c0000750b0040c03808030b580b01070505061124080d40c0b06540c840b400031242a230103503141504803584908040d51030815a41d50307100000e04900595421000164894003c51068942500c0b490340200e0505030018001c2d941d2901c0b2201070703110503021900a07201240800c242501880481e80c050f01c100310403602441049500138a074400200b511580d1030343c4d61048051500c80c2031100e4440e00340c0004482d46c0b8031111454034494845124581c3c0040c0c2c80030020400c0ba0014000d413400c80b085c0c0c600820490300c0b541e5440903408401d0344e805045650f1840054807944090285000c0810f00780c4400c0303c02420301c181d100400d40390741111150399002001c046090107c00c40000d04413281e1000010303240e10b0304082200c0500c42e0f580304100407810080190300004582d40206641540c00003120307848402c00c16810305580f0100ca100341e00203330040d010408a4041d8100d103c1c401447e1000180402603019060320380c04158000740c4146160611410301403c00a03e5103015155038 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 189278633 1250 189277383 189277421
    0x3052b0603021017060913020306010905010305060919080d090204050a1406010518090907080a1b120302030706150914091204030c03150615020d03060b0405030c01110a050109080c01 80
    0x140002c203260807000d821540201b1580d070000b0001c0500c5249501060380c02000d546265079211441d0018040031b00040c2d506028005c04501c541c0700c00110300d030818440c8102c81407142c095860342000b41c2c00021080400d40c5c0c8800d01100140d80310310401b4850f000a1500041c4090a40a001c00c040c1001301400e060240030030040d0202100e030b0b030b808284500200d52440499442d54115400c104042c6e0043e010b911074030a11030100501000301c1d42c11039081d06803215038035503906030036030400e19150380c05005a041085941d000c280f0940082c001d2101000e5504400d40d42c502030101180c51060003043c01051090510040400901c65040300d0035004180d02c0c1841e05644488098014621006040518004009a19000c0f6070813000003070500141684801c1040074010352100110000078000a00d010707004280740010b0020785065402c05401002010070321030066030b00c0c06e0981c0d044203d911560210500094090281203a40c503c114915500d8664a030011402c1d00c50503461032480480d1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 189279883 1250 189278633 189278657
    0xa060509070b120c0405030a0f030e150d051f080a0308010506120c1806030106201b01110102040512070e090312060d030e0409051e0102030f0403052b06030210 70
    0x103400b06940c20561406011600e54440c2c1c0603046441c800e075846290940100d64603002401112114075200e24082d0722485c0b01c8040c51030410842c60514207085c40004014001e4030143c02c003d80c801d55015561020410100245402d0807411300c403158403840c00355001e403150310209580f003ca15030042409444003400d1140d600c24010203650002e204101100000c6040704461505c2d140d00c20441c0c0b40605030b1a80c950712100003c00b039041d0402e034012007a440004c9074400d4480012210130100c845107801891041760f40045030320340281e1030f0000007036400b480080b900b82e0300ea0616200070101c04004091551601001ca550030b200145402e0701d6070001e21000a00d588841c0180794000e900f214400070f800c01c0e81c941940c1e510421594240c005150003a044100480041c1102a000000900003001a400030f00c0e2401e0384400c98840e106c0300012070120300000d00450141240280f0002410740703008004e1900c1d0300130043c0c0b99005801c652074080030401e60500402c244d41c04c500601e4001c1000c40 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 189281133 1250 189279883 189279899
    0xf0507020a03030e0117090a170304020d060b0609030f060907050604061202160615080c0a03032f060c07020a051008070c061d0609010f0b01020604060906020412050a06050907 77
    0x545102c050305100608003020340c141e20950641034001404a1403040c0b0b400d000c52040e035a004500310807145000d0f591510301c600c1c0c284005991155034002d0140c1d10b052003030383e6080d001e003801c640e4840e0801800d2150004e035950900c000d4a204181e60010509072070a040346a00c1c12045902242c044d4500700418030900d41d110404200c400031843c0c0160351010710030100d249c03a48140304054aa54680010003185598107070810b422038446c20100e03046403034038000300270245115100080200e003803010503d66142c3e03029140e80c1340001c246d842101e80c0040c0100d103400d00c081261043c0b4074030400a885001c5192078042540945010354803000c1c800304d181809414070a0280c80001404030202c80d04040116030f0700040c084018051a420554811000d0035940310310550b0030072419420840705c203208425a20443c0c0764090164000d1090351038075100e8038000c2c024000c1c25140c20383c00700700c0841c0910010b083c0340c8041c1c1c4280d000703203407001844c18030104549000e08184101d81040f102001004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 189282383 1250 189281133 189281149
    0x14120f191b0b0f09010c021f0f030e070e04020f030604260a0e0405060a09020c07030b0a022a01090f0804080f0c03030a11010603061a030d05030f04030c0204090219060f050702 77
    0x144103012081c0d602c141481c0103840948406c0c400a61020307030802c0400d00600f8055002c210b4130f0541d02e8407010526210000d6050f00da80804014880e071225400b08040c021b000c8400380c00c50700180c46810061419004030b4103144c0201c0e0190369414180206555148103e44d00d001d44140224942d0b0600c0c10041000b01100d60104000d80310755100c0c80804c40039500d03028940010b0031503842c2155070b1455607100030349915541c4006e548444802d00020402c021500840340203081d0b039080e110002c0039045c20501c801080d0003000c1f0156681d548e80303c0000d01d80c0080035100500501c0040c0e2038500d4002038034600917800740e0750b40050b00514450310003520008150b415100c4c00d42058940441d1150b40103006180e258009000075003440b400d0b5613032003400e00f0000700c0d0751001e5003070351000b81c3f4095055075544400d980030540c0100100018000c03074450f00b0b42c0415944000d02c00308100440390001a4280314191001070502c2d40101c0802515400018500c1c200070107003003841c1460b049400041032a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 189283633 1250 189282383 189282397
    0x10e0709050c0c01050711121c020a120501061e0201180305160b180d02060403080a0504140a11040507020f070302090901020408030307050c01050106050414120f191b0b 74
    0x1858540000ca040ca803203a2080da01c1a00110b8000c005034030b0407480007810400300900032851f5029420203440c41e400c0c03560848584e041031400d900c0402018031202c0000f94009a4640f007041200700c10152803000c00d024407802424150340b403064007040319208859000080c610401560714215046c0a40701e81200901001d0341c01d400d05035212818200006030a904d4034070300810f250060340800004004019100c00000b01706822500c01c0c800a0000740e03590401034030082d000c106400001544140c2942150f0f90151145442100d102e0178130303003031502d85001d07002c0449271410f21143e60b103d941042e200e00c0381d2040146c80200007445400d003a564030b403500c9000207406800345d90000b4070018000d40483d801041041c0850baa1b07403410200c0104642c0100a20030800c0d4200000041c1c014842d400f91400d4901c1c0f0346918003803903084070421004104803090149140074640c031180040c101031103d042c40a000c082e01942c07000d03892505126051350150340005c40211501e0a10003420302205035607074 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 189284883 1250 189283633 189283649
    0x5060306061318061b020d09150c0803040f060f050c0f07080403121110050709091a060315040e01020708030403121113090e070302030d0e190b04060f02010e07 70
    0x80d4041103445006083d44002c0302110440035680d0004225555010030b048120300c42c80c500d40c0c0c1d600c80c0d41c02c03600d406c40340445000007070040205020808c0030b442c81a140050742d0034000344e4010299075940e841d400c2282d00352910300c444c07006c000500a0600410f2000e0342004410483e503d800d4001c0305441c080c8044190b00c401010a00008100070f41c0c0c00c550203580c0043c078001c420250a1b10040c01c078221000740c26294000d010840daa148400c1c000c8a025030302d5601c2e141c0d006810034107080700900da141c807848812042050418601e0b04c4420003140038030a01c0c2e0b20300c9941503504082c441500c6200342c1c0300d1103980c81040400d0203d00007205481d042030f8149042d4881c5581d1190100180c040725150911035680016034141c0e014074019284203c1d101901c091108803500c2804540322130310380c407010303400d500480c1003607200030704c00e440640d080400141300001d2001654090488038550750030051059100160a000503030b003005580710007591902c0240f00c4060f030058002d0f219a141c1c0b180581c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 189286133 1250 189284883 189284899
    0x7050a09060602162714010b0301080f030a09030308071e02010605010e030a0b04020402070c030b070f0806010c0f2a0305010b190b09040f1409070303080105010e0102030403110301090503040303090e0a0506030606 93
    0x21700301c0d0403024980c000e00550515a5840d04001c4e9000e40c82841425117511a07009400c030000d40201c10340e40203071041d4644102e41851a28140c40c030389001881c80c41080040300e10085200b280f00c0c1008401c00c1507030700000340641000009007240040560061186d070081c032010740083c0185c0400b0307a0107541614003684802c9070340380c0418101440d81000b80741902500810991580c011610000452140e54404081d01c6100065a00e90480c050152583c0c2c0f0214161000c1181c81c103004d46d40700c405004441c0b42c88802121300c0b240c01c946800498080c1d46071400d4000300e242c1400300b812618508818110303941c0c034000c01000c03544100000c0b45d0155031111380901c46c507003e903803140e42d4100ca00c0c20344030404d03d001e003400342e11540c0750300084005c41d0340d1900204043d441200341050b01881a0004d6180c20b02f5902c41c101000c0e042c05c0c02503030542d21010010000303201840504000e41c840c1c0c03908070116003400292903002100800110055140c0400c001c41c3d81e90008016030003403001c2e00d820b5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 189287383 1250 189286133 189286199
    0x18020a082a0d020a0e100b0a020a0b060a08010e1f050c0a030b03210d050a05061c21080711010b0d0609020307030803150f04230907050a0906060216 65
    0x351945034007940103940107503084c00014401e500509460301c1360518100034040161a0340700e6400c54000c000450300181c0c8500141c1d800220035540041d001a00100040c450683d21003e0a09680d80407103203d0b00350304214030b840401d06490b0302a400481000c0000e00c0246410711030081c0501a0240c000101034441144102c191001d01c1100903080c0b100d0305980341010014840030700d56001c1041c18800300e10385000175183e2035951188900881d001007103005510605100d181858014070380036540101c5480c50704074550000c901032043e410351070f22016114505140050202e540040c44903e9a90605104414581c4d501c441c0c041d034030b98880000030b52405a400468904100c60708020450319000007408038050f03000d500c115011904468640da011402c40c144410759051000c40a20500c56403051b6444040e2030480c0c0394445e6229007220398069442d400103d004240b41e20072640107644800600685a041c02441034a8680303a6886540b54903140080b203100600c030441c400c181201d400c2c42 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 189288633 1250 189287383 189287389
    0x41a060a030f1103041203060501051e0d02031608010e0105010f0c1e1b050402070b131518020103060e060916030b040e03030f072102090d050118020a082a 68
    0x140d040301c0141c0390b042014202e081d16100207940243c80680e00c4400c00007039003c1ea40d11078000c103020380b00c060352214204600310100780403410701c2104003031044006000d50181e4580c0c40c40650310812600d10040c02200c0000c0002c0d01d08001a0407403101d00f41d410005022598004c000400e00180c05c0ca002d118003410760900c03284040505034640c0089881450900c02e00c0301c04020059000c900ca40041c030001c1d960000c0104a20482800a042d030355014009038141e0086800002c1c1580901c0c41c01c15824540c8206001f201c16030b00c2c0700006111401e40000665034544244c0c0302030b2000111442c1a820007000141d0a000c0c01070210841140d043d0240306004c0c800c1c0c0118151000240080c0182d07000b804841707072640c204464500c40d1644807400031316010f10840510030244410301c42c0c00c242007002e40c89030b006503100120454000030104032203400680240b1818220441410302100310119920401000d01d0440c1c2c41000158403100c21260404203010000103a07155201d100180d5001e14004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 189289883 1250 189288633 189288641
    0x51b0403030507151d060406151202040e01020c0a0303091b060e09070306050a0902031503030f0414010e152107020d080910050c12070512151f02010c020606041a060a03 74
    0x2021740c228445c41030810003000583c0300d002c0d0b8800c85042c800c41483c102140640d8903a482800c1141c01c40c44618405030038154484884401400005850440b054400900c4c0003014181100001e40c0d40200d08140056056a04c070180d41070349015640c0f524102c40104a203142000091081454102040c1c0076406030340440000d090281242ca503460751351400300300a400171030f14000001d2984261005a1401204864080f18105100e609160500304508000000c1003403803818800c15185e88403559446d0800d801c0d000301540103660307a600d000b132201120040302310182e03250420540148038081da000311700c0d94400701443c501580c05a0380d5400e1031785444d500e00384e40001e02d482c04081c408480d141900400e003003880350a00304070544039000c044569200d40d9001400850410010400b1110a140322422182c8001c0800d0740710006405000d031024070341d007403001c0942c0d035503005100350790b4041c00116841a41150108803811204d40d0105900300020a00c9114650000c0c0d444c180c2070080d40 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 189291133 1250 189289883 189289901
    0x9060f030609010b041505011e02010e01050c0d0c18120c030b090a03110708030d05070c02130b010e1c030305040314030702060601090806041101080a090204020706051b040303050715 80
    0x101c500303a0410482482c0200461440e0318000d60a0204014002981569810031610181c0d42ca101c0340020708a5010b617802c0410b1448115501c50381c650051003001d005603801aa1081c00c659900d5840511800c2160808008003041c0700d0503015040408540d18250300450340d8056075240c3e0581a45030185049049400042c0015201740a101184000007019004180320741c0351b903d012003003401402d80e2002c9900c26101c060740100085140c1404681001c0d070014102e0410040c401e0300ca0340007510b02d00c0400d880071141035441015000660b44101107583d00d50058888407400c0d601e8040030b52103048158009001d00d42c980000c18200341c4180c81300d410a40518803680d03102d08103002c009485540941d4000c2c00a0340710100892042004260309008030380c85604900d82d0b2000d0340042d592504000c2c1700101075990b8103402e501580343c1d0700080c02d244d4400d0700700180508e04001e802070b46030455145811039074414070040c400250050b0403503603100d40002d0b510b0201d4286000140152940803 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 189292383 1250 189291133 189291139
    0x110a1d04230102032706040b04121b0605190c0c0803041b0305030c070e13020108060f0406080f060709030506190204030f08030603011119050f07080a0207150309030e09060f 76
    0x1009064118110041d440c3c040c0c003803c00d001c070350407455515550b1b50156000351500b44400045800a132641039011103a50322801e20341342100b80030039202c0d082890120305480140d110010002c070b0032078100303101100052000701000003540703402000702101c00401d0020a5500000041802e02c10016000c105c54009010070342e030016141d2402c1a100e42080e84401d40074420000013044890044d604a88941050140154542c082d6001103a0b0440c0241140c2e4202071800f45107255a02c56001e0040501707a500010316001442da009289411001022841000400c910074000501d020410750b400216054102011a9031000110002e01c00c5500080c000c024a4045004002600e0055485640704600800030a40c451200034113078865035005501e000340c0b003041c1c88011030158010303090560b0a00d418504203080c030780d40c4c610268030100074200940c0c014001004a104041640680f44049242c140944419990045c190568a034a26845440c1c1040010440e0703c0d44091080802402 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 189293633 1250 189292383 189292387
    0x30f0f0c160603140714040315060e0124020a020f04090c1e050f091e0a0e030a030501061206030b1602031b0606030d02070602030f0304050c0307030321050f04030309020a090603110a1d04230102 85
    0x1075101c42100c0000d0100b40103013726400300022a150020800030011034001e02000a4000250104401031000308412620081c401c1c20216014001c0000b4507846280403500c189010300700340800541c24040c140f030360300c101340c1e19081000803616042c6560030f4010303060680070152205113020010304180c0302c6e00406440b01081445a035603040c1c10250484419888510744c041011140c0402d0381c146000c094030310503001c3d000c00d402410705200018032000130710550b8100061004001044001c021121445611560922803141341c180442003c04850780004d21b6100c5c9007500180d100e000d01031083c0c040b0358000c000a400c2c410180104805030398001d082d105125160314020b0820b0000c1d0782e90b040500e0314000248450042c0e481000c0c060449408070010307990f6159004c801078031041504a800c2056105c0003c1c40080500509000d544035017151860011507006100328100264040201c130014002d00c0c0c00b22165170350213250010b801800c4003a040a070742c074030000000c588401c4180291302c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 189294883 1250 189293633 189293639
    0x1009031b03080f010509091c09031e030f08191e05070315080c1f0c0209040605040611180d050f030406021b03030f0f0c160603140714040315060e01 65
    0xc0b1a0850b449461108141c40e81d40e41c0740d4045c030003a1003041b5400c1d5a030b030b80f040308061181c8021074000b850511240c90040c070a2501d0356503d0b1014540001c0041c41c00000a650408160f00007020110440300d83c82c0c406004e00d0400020700714181c0c50940c1082043c3c0c0d90740c20b10341c038610600e84000c060307023a1841403020707041190b8000c0c000c3c40b09064840c1c1c100e40b4505c0200f04c8103008914031081070b40042003424407120030b644685410341400412001c1c000340503040340043e150725906921840c040c40307000503a85090300b003c4043d1150303107a140c800d805e010400e50380301e1034003403c9110340d6040030f51f030034425040caa01d0290702d050082403286801f444049000a2226800600c1c0c0008842c80c0000c01940f40c140c07030925603640540128034044181c180240b4000b10380c17440240100700e200c07500300d825600d01e40b0b4450601c040641c11400000e43c555000d11a484402ca00907900045c00e842c142a04044070714003426540258000102002c0c0e40041d104032408141c3c004a015050003c5541e03c5940c1d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 189296133 1250 189294883 189294887
    0x61b030d0e0a0302010608030c070605131a0c060f060a030311010902030304080c1302180112020403020d060c0813110d05070e091e060709050d080d0c050d110405031009031b03 77
    0xc000103040f0015800c0c0700c404603080a0200035108188403990003080c2c180d0a10710240d50310340141485814480300c1e804001009004089041560300c1020507499440190b810083e0404400404226001c910079044c0042c640340c884441d8104ca030940340407000c8901c1d004200f400741410142c0a5818800418042559807021034404081513040380c00c8428000c518024600f03a01411150130081585070713981d40065405104820303106106010010f04d00354581e400501a01035010051312915581d03641514955000701280b0340080501032003d000301c0700c81d900c038102481c80c0101c0d03a0160000181030780400804020700c1e00540810700c4004030505e8180105641d64481d04901c4202940c40026200000f0b00403410a004002d0707580e6984440d07090178184540403003c0031084950103000c110304094021a8820169a81d10710313501d0f140c1c1c1e4684060900140e0304801b2984460000c10442002a9500002c1318241440b0242d4089a104814103096640c2d07815120011305072042003141d242019 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 189297383 1250 189296133 189296143
    0x212a0c09060503010606110601140d120906080a092109080a0521030702120307050708130503011b0903060b032d01050a0509150c040503101a0301020702061b030d0e 72
    0xd0b60541c000c0007040d960b403008a03021125500c01c105141c11400c0148075490044da11151080d0340a00907040300b4001d9070b04d109213100183d40410004140580921180d54040c240765080a8043c0090214054ad130319040b884145a181c0411030242c0707105480d00d5a8010300d00c0200500500c81030b0341e035000c01070810541700d070890801d169401d0f40f49984000b00c0c01d4208180c9004241c0d580c020b080c8645081c080707003001c0d407010380013900b8840d0900c401c03000120300800400b400416502d203004558a041c3c00e15080d98084142074900040c01c00c81100c840354042180c0085a41020b804103c40f00c1180100b410120b5001c010615440048801c49851261400011017548420004c01c81c1d992004c0040c0225982540c214009800104c7c0201c11540032240c290b4200d81c0490500b884c1c26914400685051004134000700c1150716801106020482003040c4070a44d075060b0f000354076248140d400101140300c1c11f424000c1c04050314110002c0c18100b0400d03900c101840300010040e510440f00019910 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 189298633 1250 189297383 189297389
    0x2703030c010e0d0302120a0515040515190602030909060a0506030c071703220201090503011d0609010203010609030201120902031f05070c050318040b03030d020403212a0c0906 77
    0x5100c0d61801c2c0350f01510038400c441c0c1e1126030002503001605c0d0145002c002d0440074150b449450401040104260303a584142ea000b2455001242c80780e0070010140a5400041d40c1c140c2c15100800408004041d0040121414140c0841d43c6440d82d99800c030029002c994030f600000e401070301c00b100300000c61140c0740c010b0914a0141190400d024500000001c0c248005c98241080c104102d02c10148000054a40c2c01c000d441410045500358903000481c5c2100c003c14420440840300e104070240e036070820b020807500440030100035484c5d50b0500801400f0302916100003410810224150900c007a919449070090a5000f42034802c3d5888000d2040b80d00c281020302c01841e030b45440c2c00300ea081c0e0302075a049007102e6402800b035070174000d4101fa00221140c42d0008643c0281d100c01003082603907828401080507030b6071400c00503140e5066051400307022051411040c0c10891071000c1400094000a202c44010030320500d148107030000c0c40700c514405000520007402c0144a03240071810807020740002050b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 189299883 1250 189298633 189298661
    0x50703050702010920120f010b1f0207030204020711040e07150914060306060c0d05030415140a0209030a0c0e040506011203090b030c0405040c020d0f020109020904020907021203070c060605060304020102032703030c01 95
    0x24000440034100500900c91070ac40c005030303000d0360040006040a4001d06822805840c10b20a000c4140d00030405903a009000101a504040014407455140c1d0305460491541490030085031410050395940504044c05418400c200210004201e6600c0008031140122450f0550740c43c10003507040a41144c20070b403001c9880000003654070300614550306c03c864680c3c200045003005602d810b00414000d40c008891140c05010b0106854041500c00031000d0090072074950001c1d0516250400a05000043c1c10989000d1a50504c900100b9844604107050f541d4a1110b50303580c0d103425140762000c0c03085d81d1000b034001d400c00101d00045038010500303a001c4940d58407030b4072124403050022402c0302c44d9000d0095112070b61002003405420065580740e401707409401102d004566107200c00486400882e011000030300707110000c0c02084818058500204401c0d2101401c5042c50380c0040d40f00e0099174451030012009080d030050b01501000744138440e400c041c041e00d070740e10040354800303000c3c150340c441c100c1e2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 189301133 1250 189299883 189299899
    0x32006131106070f15052404020408150109050c0306090408090307050a03080a08070305010609030305090a0906121103060601080f1b0408071a0a1b05031c050703050702010920120f010b 81
    0x883c8803654010a07208811343e600c0c6207d80144186e01d91070840c0b40c0c15000f60007aa0034000855400010481d001d5003c00100300300d02c0c950300d05840301c8150780d801000d00354060b81c24014010b254a85984141d0031a90043c9090f0300e134102000420714003001588090746c0f2003610713203000083c0541840101001e0351950340345002995100b0054040da80c0a1080341c0c00210180c5007000480c1c82071020300341c203120051841309155a1a45a4030540c0c400d90008038884403140c1d4a1010003a903116603240712442540500143c0c40e103240040c01c1e0020040c41e111070300d1442c1e000201c1440d032030303100582487e094120442d1981c1d07d407031602da5902e00d54018403004500365080c00445102e0f24082d0741d0240c090745d0302c22a6124071542c585e0109c2e4018202201c0c688028080151004540c84441842c5180e40744001541d291440d0300400340d40020b007410042d0791500d90000c0108100302c000729410200c01004007e0241c1d00404224210354550304804603000340a484003c00070103410050021070120f40c0c1c0c003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 189302383 1250 189301133 189301163
    0x90a090512030a0b181302220501080d0201060e18010f0e03211b13121101080703021206060c0703080d0516091212030f0c080103032006131106070f 65
    0x11001e02600c030300048174441c100000b04017451420664510503c00307090003100164000950071030018140348495240c2c5c950005100c41c1c0c604200c4916496030610080c00381c00e1070035803404101340c0003424940125000c3c10003d82e00348825040700c0c2548000038800c12082c5014840c4d0740d01d03504800400020080c40c81890801c0b16a400c000c140194268000003260105a0514044070703844111486000c5100c0e0b10005010f1400e5032520038040c5c01740080300c0e41040c0c000d000428254005046d1820b062044c004554030f1518001fa8650041d0156000f9955040680802e460101d00d548001d240207000104c68901c1000c0340c02c128040c020f1104031499038400d2000c20f80d01080b4a002c1d40744540715801c450404074010b42801040c44a060130009500b1040a824a003a0f400700ca42c8040841d465100400405074040d00540c00c18101c2d40400c5010f2141b458669184c00c0080e014112102910111005105000780f05140c11180141005d0381c880091070311070003070300e0742000c2560b07100b6041c03810b0303 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 189303633 1250 189302383 189302389
    0x11130f050303042102030715020309150f07140c040c03021201050a0e0703050a06120f0506180c0442120201080103121806090806011d0105090a090512030a0b 69
    0x41e4050702c02800070144400131411903100d045000c508103030381c10320800000094850b102074015540c500340d0350203141e07181c910606114009030341c0c00359843c8180c001c10a1010000e5100305541055030b00c4081070394502d45034040d19180500b00c00a16038002d10f440550521550503500800f201001c030748001c0e030207a907241c04000300c170701043c030640031403041440000e04d005200350b00941e404940da2a001580c03d440c1c000c17a00c0b20940e2820b040310311590592205c010310a080103500d6000070100400b04990300c07900310107500c504038000420b0040b9100d120500310b03610803030300500c625291100b2490f64124684817100101000c4030745d046079401c940c00042200d030410341440c0d40007501a1070b4240980d186a0303884202001e140d90300c50801414072041088000700505000007030540c8c0c1ea9a540c51800c0107007941c14880e06900041808034807003c030188540c0c01d0303801c0c5411034004440c12805961410380150251042d864001c1107401006d0407103a00d010803c01443c040c05003070404021000c0c055042c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 189304883 1250 189303633 189303637
    0xe01050408041a040306090602090316052202120a0603021804020d121116051e0a0303050a0909020d1b0804150c030905030d06050306090703080a1211130f050303 71
    0x1404a1108000901c00e60f414140030105924100358aa07140c00e58170b445042c1115411a41229050b40004c1c1640e034601c0c04102020f10940004d404101281c941000200c03c544502d1005402d60046102c8134040182c542c1900c40106210165054603d0b149140900401190208a208800002e103800010f9404002d841c441c55001d800781041c02c030b050300c500300c19080c040010401c019a41941c820700140500540c1411001001a803101505200402002800c110140741840c3e805950b008260f5a4590040301100e8250402c20707036a00a010f4200c82ca90040c0d00140380e400d000203040c50301314049521076a410f9400340c0c000d04041e00c03070110403250f1001c1170ba8043c02c2c45044281f0143d80a0701d6a1114000c42410f007000114080b043c0e840f41d09607044a1030f4481041d0780c07514100118201400080e46c0940b404014000c46800c65842c1ca94170300400c042c1104000600540340020000c13035004c1011000814025034640102d81013411047c4814068860081201e4000141324180081 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 189306133 1250 189304883 189304891
    0x70606171606050a1d06120a050c0a0507060b01110604120e0d0213050c0d060815010b030705070303051b0423010905030307030e04110c0d0e06090d02090907091805010e0105 76
    0x1d01e40c3d2a00713404042c03c440b010704201c0d170030313007155900303400d031000c503a00c03800140007240008598103900e240c000031410844074010000b007590581080364400096000c1c0842e001290301260004e00441d42d6030040700e00005000c6059241d01c104414841440321107601e40f01d20441940e0368883d401540303000e001e0f81d0621140c009401100b42e400c2c0e0a48a107241d0003080d4031140501c0c50505000001000b80180c0d6041e82c00540385801007250314500344041d54003070303025003481d60a180c514202200002c00c6445521009010181e54001046807920800003014402c820194a5a00c690311703812411082c4124441984107850481403480d00c550040c41a101242c4005002d5402d108858405407800c04441402c25409640d40e45038140e2080d213607014105003080100208001040d500c80501164040c4500c1840380c90b003405a001a555121400740020354140e8070740d041601c0d0949801c2c6031140c280c002001d10b03400c00c40348100e0450841c080031091401036000b80008204072003507a0032210291 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 189307383 1250 189306133 189306137
    0x906090d0503070f0e1005040e09191b030f0305180306071d0f100203190309080f0c0102160506070f08010f05040b010207030c1d06040b030a1502070606171606 70
    0x3000103804640100c0c07a031480035406003010030a00c17501074005003103031000303105400211b5004101070103030340500c41169a00a0b0124000d00000d0b023404042c41751440c2210000300840005100c6004a14004880f4001164070241c40b0502c1c002074034002d0143d0304540d070280c01c440300d5500d505120346070000700701c1d0140343c1c180c841c0e82c80611745540b0300d41e40724003c0703001d681c11003080b502d280219128115543c0c0e041c2e6460340a10389070101d8210300741e00c03a446880c0c000105410400d112001c03410b81c90890b0320307042c560750742e1a60307402880781628060b0040c1c1000e1f641100b1011080f10502c400401c00c2e501c034441c40d69440b55107000854050312240b0f020300a80542c0c2d1801042401305060582c046690b101c41401241e90044e601e64482914401607004140e4158000780410b0000c1c51056529401a0040300c1c144102c1c01c041c3e02107035880c000d210024040c00c103010f080e01030301c40180d811100e5a84c0c0002d018400c041e01c83c03900008080310300115030410b216510807040702110240c1841c00b610095 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 189308633 1250 189307383 189307387
    0x14070b031b0711090a0608100e0c0a1a0703090e0405010903020606030d0206040f03090512070503070b0c060406050703021611090901090317060402040f09090c060e0a050d11090705030906090d05 85
    0x300b0300c1302c0d09100801c04c265041d0368403004500105c08110384910101d0078000411110549414136050513640d50013240180c4920500f44840c05180701c50491084500062545072101810200c0d0034203465445803081078000401d010900006400800761607000790219103c031b03122401410303a0350100c041504010380000e404039000411306c600c036102142c001c0c5401d40002d610340001640c1540081115070150344841010000c9045c10300c44407001b00322410601d81004500c000c041d40300ea40007400181519902d0300001c00d558007940c15121f10b0481c1d08a02405035540c0d10340b1522042041940c240b140c03407403500083c10035005015400c095540356031503060180744c6a11343c6030320800140401d03a00c56001e10010603141c0c64006e0b03550060500400100b0100210b04040f06c20150030380242c4108424614507055580310f4441c2c1d070b0708480d01921110b49010140c201030343c4668040c0a0b8640c48010b8a040c002c42907030200145026040b40f0b8169625a03c5510103076036100c0514001c000447c1003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 189309883 1250 189308633 189308663
    0xc0a0f050a05061e0c0609011104060f120e10020c01141003080a030e06072607050a050a020705030a0b04031202071502030406022101061103030603120714070b031b07 73
    0x3c804098103543c0039440d1115100e60001c680d1030060342110004030b506a100303c041181e000307024003e13a02a074000f14580751620f8103124008002012442e650414444080c8600e100c0000c00d034090050987c800060707682c202c210a1024019601a103842c2c40ca41d820322001c0454100a684403900a000c002c45040340d0904e103036503d20340c0b60881c408104c14103640724a28082d18038140b00e958482c100c195500f41c241540a9240602220703544c62100e2035240c51410403801d140c100040b56100d459074140a0b440b909a03040407882d020648d041035408d4081c00c0d80320400c10000b1034545004c0c0c1d20a40b11750070310b101c41200d180b0490140c0d413400381c003150102004020b203118941c01150800d0240401518100005041800c5400303018104a2030554000042244e29840203001400d0401c0002452540c00c02500095450000242c5443c01140001c2c0707800c10001441414940710503014182c2c0d00d2543e880140c90480e40040351041454452100d000e0311a80711402203a5040c4d070701c80d04605074110 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 189311133 1250 189309883 189309889
    0x20c120c0d08071b0501030501090b0d1e060f060e0601051213030e0d0b0106140909011701140a021909050102062a040b0304050705010201050103030903140114090c0a0f050a05 77
    0x401c42000d41d0354100030003044011461010401c044015a2045489440c1c0303000001030441b24164005561140340400c41802907444030b4034842543d41081810401c000002340100780040a110020803061901c00f910b122024290407030002c0305e1660302189095503d0300700541c0ca51088002481b20038500341c0005182401c402040e50209000c1d290080c100b429076808030300d070240450001e54502d08202d00400c5132a51046000c10702120070b0040034184003500000c0751f142c03d018002d810010b40c10f03402094085009500038402d50010030b1044d030359800d290840c60000d51080030040103026009101c0d294060150445000302c0c1e01c1a40180400e0340c6a90841d0b0034507142c1803220030782802c3c615058442441c8070010300081d00160f115541d0300c2c14607141c071502d01946580840d0659050100400100390010000002c807608101004904203288104a00402d688140b000d45043c2c84000d001e00500001841401ca50303040d00c07183c1c0250303200c60701c2114003c1184900c661106406806020710b003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 189312383 1250 189311133 189311149
    0x1807050301060311070c06050c101e0e15070908100203101e150f1107080712030201020c0a1110030e030301150201060504090b041a01120b180708030406020c120c 71
    0x903c1c1441031342c20081140d89000c010107169214900050002c074003950042c2040c4400491004030020030081c900c14178400f00c0050684201c550360309036032103000d00f00d840c0041c0b1020ba510001e8542078902d07494040d501500d03101c824091a06144509040c40344408454800c4a0003000011b010016152421108208145c80c40e83c0ea0404041c2e00303140091085205ca03511138070f800b01038542200805403448020308580e058101d0000a9100c481c0800c040c1d100468070f0001d86008013060040c05140d410264003900c5400002200c501c2820030755403e00c0711040140001c440111030b2410000c048460440540b1001448404243c0042004001c9884106192180c0c180e1900000c81d07110354920009088034182c0c0ba0945840501c0c03001c0004001d00c2c075030224a00c2c1d440509907601541000c000e15859804c034180100b5109001000c00c040c184896081c86200c50050101c40080da1611045500d941040c0b00303401c090711443c9a1140d69240c00004407020656080080040943d4482001108 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 189313633 1250 189312383 189312401
    0x6091404031115010512030910050c010b01092108040b0a03021c0e07180e01020f03060a32060c0318040b220203040311070609050f0a03150902061c06030218070503010603 75
    0x791000b0440c4108c183c45100c0c0050b502c00c10b85c0ca0309510742401c882d09500b954000640c1d141000015042030010703080c000710360f01c90344c07078009050307a06102c136407400e9800ba12603500001042e09010a84807001c5a0580050004040c95101852120748800c402029180101110805078015003000c1c0700c0c1c1c5141080c69105114020804a1110071040c02582280c2c4940124841c0d0b100020403c080360400070150002008c000000c00c112004180100d0034103d09443e80d50b0714500911095442c5640d20001d0741c5ca207031740c0305041d00da494005002e03461402d4000c00c60607002c0c2d41001d91040d411310744401100e10440d40308500000240c00080d00c28000c0d400100101e0520a640c40c0100100c90104001006400b0300c0e2201c4031040d0500b010030213810b9a901c0003512400c00e0301401c0c000200301c00c1c00c1c01306850b10240007040c401480d10001300c040c02000c2603000c010281000314900e15044d900300404032802910444050010b151084198902c01c03540d490202e4400c000400c54107100742c4c404400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 189314883 1250 189313633 189313669
    0x80f0715110d051f030b0f07020d0207092003070309060f3b0106080a1407060f0e030a1704030b061804031b020a0603022203021e0103060914040311150105 68
    0x13014103105a01c00c02c50300f160001d45810848408001036221401342d99034014219000a01400c1c17600040299511000d0040030105500c60581490b14030400d4401c40140d510b00d4680e50b200e1400140c010b004109180c000d1307442a0401d20200882486841865141f00190700000e12200000d2281d240e0b282d2041001a45d0800303081a480c0c00358001c0c0300380009003a0305800341c00300360744900b403541c1d000c1c601c25041141508982020804283c100301d0f10703001c9540d2401d0184030149002d000900b80041d0f100301901c014061100c0c0c9091012420042040e03e111b06210086511044240034490250054200642c1d1410004c2004a0f02500314032001100f25944401c4008076a404038104004a43c41032003c03e070003040c3c0c9064504900480e40d10551108040002d035451900043d110404411070004410100c0e084950a40d102e508000c0180000c510280a5a414081c231184454012035007500020f49000d65540b007000c020501c0da103c00501c09080e50380764200000c100c03002c500180c801034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 189316133 1250 189314883 189314911
    0x81c0e03030a1a04090b0f07050306031f1509020310240309330c0c020f01050a050c0a1112120f0f07021008010503120702010507080d020403080f0715110d05 69
    0xa8207546030700039000114411b0982c0903a6003040c0401200c50803010b4440000e001c014401c0020f13640f400641d404202548106038503500c8225224172008101d245c40404100711070110205007000705030002e600900c81d052144a950740d84a40e003002c403652072103202d0005400c0c0c0c0281e505080c0b02e5044000c1050160040f4414150400d0128100d042c11189c100340502102d02e0001c0c11030940c1c07140d184001482d040c013540340125a0b00240c21105004101c0d41404008290801114425800d5a24041c0b09004075400300c0c440b0306160031403280d0140c00c14461a103d0340110070103500840d8094840c4800c0e01c40c03904040031001b14100725008407140c150500020700c825000741e5a42058460781c1d000720748030703004c255042006150600745624200d040c820420000000183d82c40400c4514194002603165140d051202c00480a8411a48094000c01021038100c40c00710164000b084114440e030403a44d48800182a8803040e079a403030000071314002e020303c40030f421410795412080d4007440c1c8100742c075 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 189317383 1250 189316133 189316181
    0x70e060d031224060f17070c02130b0d11100f05040315150e0603060108010c050708030433050f040c03110103060b1b0f0102070206160816081c0e03030a 67
    0x716610708036400040010705c080c0300e40d421960001c3e809800d140350350405407040e18140f100230340b641452400007401000800b0402c840132886600c030310028440240400d04040d4242449251401310000b058801e000d554003071850705008000d10034900d481c0740c54450401d451502e0b00c0208115400c80c1c103017140d0302c400d41d40720005016112a0060144c85119a003181001d0341810301d001416000601c00f40e14100484030459000301c1503801c25540503000341c1e5a80d95901d0427803040300c0019480c4014504995246036034070740c140300b800341440c8000002c01c41562090030040c001c02d0190f501602a0100101c280080303850350300785410b591f01c107050200d18595611441701a590040c1c481e4160408010501d8082c19028001e00103100401d8000f9402c08440b500001c03c248100d0801160380d500d080d46180401207000152443c03921502c01c110b04041003401c0000326507029080003114556680c81100c1100060301c1141d1080700d015008500b0350341d43c40300c404018502d58070040312a1103c02455 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 189318633 1250 189317383 189317441
    0x1009030b0901061e03030e0a0b04170c040203070201050403020d0206040b060103020708091f09120c1e08030703020a0b01080307200a091b020105070c0503090607020d020909070e060d0312 82
    0xc0c8900c00c2031101c41340c603c5245041c0107001e541c812148910072850140100a928160b0b0140c8058030480720341c1080071050340040c0c07450000c0c0c103006036412a0000c0200066940c0651050344680d0213602034071401030040c08100d85504040343c0041c44007030a0701c0401c2a551190b800350103800e01c00d4402d40c0c0360048900018800d2070b8000d84205071032405d01540c070302886d4840ca282000b44001c0200840780e0300749a0b0303801104481401004150455415420640c400684a2000510600303054030f5983e480740c02c0003515000040020344410324190300004021800004540415400002c40045681e42c2c0f28179014200709203002d160f00c49078020740459007003014801d6000502e000d50400300381244481001e03080d5070005200c07109200d06002800c003c603501000311352014008550b0a9a507500d50b10000358040c00c0110040d40108022081000111002880c0415510f07401140885aa5204100115400310795001000600c0050400e4500859500b204140495002514500480040724 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 189319883 1250 189318633 189318659
    0x5040e041a090a05070602071a090f220515130c020f07060309110102060105061c0906020313022d2e0f030b0a050105070b0a09120201090209061009030b090106 70
    0x2c155801c1c1c0042a4200811038104040001000303540007818540740350a030214003820080e660280515800076040b80555a0006080d41c81d100c000d1010180d4221362240040d1000c9141d005180b2134a400c000c07403038440b10141600d601c810001c0c502e031021900300c10039401a2200120103029846031208200e101181072042d607020341311550380014411254241040c5003046040d006065400840040c004d80e21500102c9003100483e401c03074007100011102000003402d1049001d840300c1d2002c401e10031020f459030b401151050084690380d04420664404c60808203090840e034024405803540c5d681d040c100034018040c90350ba0368040c5e04031882c60340300301109503400641d00800100c20004040380070780c15210318601401d082e03a03101206030030900060007030321038400007801729181a40002c0d00c1103425000103003500d0384110003011145584102a0180950200480c0302d0059140014018242100000e46001a0796900c121851954841040d0032001502c140030300d540b41c5002103840c0e0200b9030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 189321133 1250 189319883 189319891
    0x151306060e09030904060512060c0f0f0a0e1206070509040b03030f0c03040f121a060d150b0102010c0c05030a050c0a0b01030f0309080a0b06061803011404020a0b03040305040e041a 79
    0x2003c0c0d65134031031000401c0101c901542046110b01e60030446020803000c0059515400306800c20341c01c2da204030040e0301054a0280f000100591400050a5204c9030790110380d07a244140c06881c60b640340000a801c81d80c464000306c4400b00007400c01c1c00054040c0c54103811008040e0005801d40c0d1130a1403000590f44141e000020b6180c080e40006410010480e00315810ba00900c86240001916442035407441c4841c6960805c1e203690071009804141c090340c94034000140c19038404c3d082105200b8400f030f804042c040f010015070255103040f400011050082040d40d241540c01006545817040c416415140c80d08001c1d80c841040c440c0c00400310006281481060286024401400c1c0c181d010317140c024040d040a401019550300461010f40000725412445a0404000c4501a484d502c4200050380741c20f0400340c8882c3c2c0756003401180d0382a01c1d040341000340154000d4903064406602c03030f0480040380c8801d440080c00100c00700010801003144032102a005441403084449041c550079481160071000d0b1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 189322383 1250 189321133 189321151
    0x309060c0a0e2e021902090a1b030608060907030f0807110d06050103060b010516060b010509040f0501090b040605090103170f0408010c080711122a070611151306060e 73
    0xc2c620190f003074001080344002c0994402800000009240d010940303a0b0584001e00a09441000c5040103c581d0010f5802240e140c4009c0c64881c50742038001d010300740c507120b43d1030a03000d024003058031078001082c408140d80e0490144031080b40b02d90b44080c101c0e800781e003054528918000e1098180d41d0748159090810340100c070042155411801c080c4c1c126480f00c80aa41842400c02003040c0c614039000000c0802a040b03140003406182e07140c010380d828414891029442032600344250300e5813065034449410707100650010010035000c1400d020443c4e05c10f0103000d5000d04540d0040000074114440245511540c091486c00c6c42c03000142c0c000d6580143d0031004460b51508038030011f09602582c1d00da030054640c178008030100c800d105400d071a40e02e4880580075103140010068100465102e481b01412100c840740168a44c40c501055103842d101c0c090b020005602e00e842c035414402c0010545c414032040d244200e05500c4840101000034550a4100c030840c0d250400043d942c1600111603101d14401 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 189323633 1250 189322383 189322429
    0xc0e0d17070c030525090513060507051e120f070507020d120e040b092a0a030e070602070f0905070210050408130f030f02040e030c060c0901030606050309060c0a0e 72
    0x503180150411000905000c240100217000c103814041c2682d401c411a60529030002d01516848404034800c00e040310007802142c145030500640e941e01c0801481c11060045000100c203900310724103803c521030f80f6003002d86441d80102003200000e9010900390441140d04295152134050750104000c0da10409007500e002c40c101c86880c08a6801c1100c02440200488080000d0100e400004000d010081c1c2688000e02c40b40f4845034800700b045003182800100400383d07640f5a0b800c001c1c0103001d0041000f0440060048043c00504180001850819030f50548042001541800c05044c01820010080e00451040301d00002212482d4031410f030003030f1b0040741c40a9403040c1520607481c1c4c03081954480312035264840c004101080302e040c48044110742c1200c0100e0401810381c04140b450051085062182c02141c081c0003403400e8200050080c01c00c2030300d092004650301c03082030780d4600040f2691402e030303041480040d07040081d601c014840c0e890030341800340d00c00d6540303030100c1e5010f401904010006152 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 189324883 1250 189323633 189323639
    0x201050c2e0506090702070b31050f060a120b13020a0801081c05030c07020a03080406120f1a0d141518030910180306050411040f0c0e0d17070c 63
    0x10b0300a541e803210042ea00040c4a0a2090009680300d41d035110b824020b110200d106242c4030412050071412070088000d46054504011070344007090440e200b51845101003c9070208503040603c107813107201078183c8a104d410a14451480068040d2009103544400e142f81001010852072001d400d81503003d64600780c40e50305003507150f450710b0030125150803441c0380781894140465125089a84c000d090f038000d992600414070114042c070003160401081110040b42c045904c542c8a80c00724001540e00c2000d11840c1c4030300103460201c820740200c600ca1900c040403a007005041501c0c0d0940114410408503600e07081c00d00d040f509066840364020f0141c0508001d200a15041128042e10300201101642c41e0a2142c0c0028420070203801c15401400500c4d103555400d104c56100440045030401c60900003803410b031500b0b82a40c800400341e0b520451500709000e911300482e104451201d546034070b0700c040d9185200b0400950806020040300c11002010300302c2103509044001c2c0800e14410030290020070b003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 189326133 1250 189324883 189324973
    0x102090406060801151107271a0f01031d03040603230c0a140d05040803011e05090604020c0307051501050a0b1204020d210801080d1b0201050c 63
    0x203590303030245041060000050060124040c540b11024007541000b420340101b41848a08241a59214000718060200c100781c0c80740e0000007280200c69841410018000c00c4007008400082c0300750703c40e411840000a030091540264044e860b114480700d20115002200700e0141d14560090300000c0000e038a03003000c604401c0c0d005000d003c0404032040d250700d1610b408a06600e05000b246c0c0b04004100a1002c841b10102c003000487c2c1d0240307070203002800980b40908040703440c1d074400c0c03040c4804420891030000c400000301d5407004c2540c000034008802c0d81c0741c3d401040701a41040b450745410f4042040211f000407420006181c00c15010500442158540020001d0141041d8803181880c2030030020b80103100b299020b41c6030b101d5811100e0342004200d41c02c010440d103030b2182c2440f000d14241c2c111241d1030303034004104034103d5070224119031003080c07484412a034014140480300703840c40d0303030304514001507000e00090514240307410112015980b4600149040180f00c404031040c035000200001d145030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 189327383 1250 189326133 189326141
    0x503180105210408040308040e01060e180a02180a031101020c060403050c090406090b09010b0f190b0d0b030628090b04030827010b0f04110d0504060209060c01020904 73
    0x58090034400e00b04010400034407601d48030b042030b10180d64000c0000a0810551906035006541c120030140e444c1c2e5207520161000d4442070007560003042801c010144a45084000012081094048441c0b66104c52902002130342013802d0b0200e01080c20a5600da40d6200c29a4080040d4050115150301c40f2122001909240840c40303620702408042000b03001141001501403a80901580c62217910703955410010000d040f490401400005840d06011030780f44150007180c214901201d1141c409242a0100078070148807004003046442c091008006046149000e80f9414132a07a2002c2040074031480000d04110b022201690b09446800300c3d062114001007071410304c440c2e2000104103140440d16203207200e850080005080110403400980d80550ba203100c2c0070806a03117210841c10b00c8031200b01300d01a040110055001c0d0301c0412282d039651405000380903120000c1c4652a1809203a441d0600140000800548183c3c0d0200303d1000c05031a01d000800344040e1520005881d06856020407080d5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 189328633 1250 189327383 189327427
    0xf0d15060908060112080d06170d020102030702120306030c0901060210050903070c03061e110405091b070201121b050322030f1d0306250c0503040608040201031401030503 75
    0xc5100002403104010000f401810b44050045000c960380503460180518891f0b6100040391a0905c000010b00c01860f000811402441c00281d61014461100407400c038001260f00c40c0040e80310007085640000981d00031904518080c05503440030440c03c01040c0405400c0c2e101d1001a03100f682c8421030f1155600c04e07180c0010341031000d0762070140c550300d40320241c0c0800d000c041c0c00140c0e0340e121103101d0340d0a04140e1080340420402441240d407081d00341d42440c1c101d03202d401d0045080000240d0f408100c04c24034100d86040e41e21050500842d50011505156480060440c50b945c405103500309603065103501101c081103645080d981c3ca0300100c1c81004000001e01c01c3d01c0c2560120103880042d4024010b42d510f030b80039242c00502036240c43c0940250b0302035a0b10807a054040d00040c400c0820984906403000310311402909000d03402454100d42489113624003404a400a0100f071082521440c01b59421500502d13002c00c070906800750b00500c3c0d010a03070089643e036100085884a0703c0c500c6452840f1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 189329883 1250 189328633 189328637
    0xb06150f0d020f0c1606030c0806100e030a050708010f0c050a020c0108060d06060b030a0b0913021e06191404050a030204020717070b100f05060d0b060f0d1506 70
    0xc0c61101403030180d480c000c50708800e00351900850030009401c0c001c02034030a141602d01c2190a020a0b8040c080c00c501c3ca9402000002400d000102d01c000b40604292401803d024100c005e9240c444002141d13050000c2c102e0036414041d1440000209800b0030401000e40905000000c1580d49001084111404c0721111402d01900f8000480030079008540b5204d5600c081c04c200c0030307540d25080010100d0080c04801804140703442c80c045101e4044501031403082d00001c100f009020320100c208019141c04441d10b83d01e0000c085035120044c1003040010300c0c100c414105c040d030740300b04900000d41d8a42180c100303c043d5503046035071415095805050100c520760f00d280400d141c6410040414000603003404080d0082d41c00007901800c0185003000e000c064849510080d48034633251034460308d0180c05480c0e007d00d0340f00740000031a1480080410004aa0006250324903003a50312107020040d10301d00c01000e600040502004a50405040050103c0c000030712002402282e0351500d44e00400054000c141 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 189331133 1250 189329883 189329887
    0x11130504030f08060316030501020702040605090405100b1c0f060606030e12070c0506030c0409050a0b090a0b01030905070b04090608010b030a1b0f0f06030e0a0309050d051005040b0615 81
    0x20210b5045001e6129204007460000b4090ba9240082803410b00407008a022604940364008140901940035151040c0300b140c3c240003035660365041041d50201601c02500c0c903003289400414101c147e5201859402c80a41758480600d44500000b03c06c90070b884080d9130b4902035650f00c03030400550784284030182c002c2d410200050348064240980d500b0170340d60501e00305000010b0080501802403100c0c4028031006107280c0d66890180029a40340e04188a10f0700040c0c144008511241040d003d400e03400c0d1000b070440c10302d0303036601c1003c04060030010781c1c0d06042c16540c001c1040410001e100800142c41241c2d02d20350360302d24005e06681203d12940c40421503925258134810b0a82e404100c0205003070300000162a102d54040300c4518004103603100d5202c480b08000c001400b480c506030010308841d1750341c0b010050740201d5443e003500c3e40142e5600800080342c0303030410300980ca405090004054001c00807a40240696071280049a200380ca081d50780e403e0401c1000410724003000a5450010b960454034 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 189332383 1250 189331133 189331141
    0x1517070507020306090601030c170a0c090603050f01050403020c0409080904090b060f040e0304030609080409020d060f08010b011e050f120f0601111b1c0f0c06031107060c020109050604111305 84
    0x207188a803403409407a2130b4130016072038072b4006c4104100c0d4045107600200401a0103985203d044010f04c10b501c011901402942002e0202d4041882050b1050342c02d50090840a220302d001c1000510144400f00e0f2004000d000000c0306031110300c101500944104540402807c0202c2000504403420414603c10350501411001c0300c200401690700301da0303201001103105000f500d842c5200380600e400950115201250000c407250550308480126041c01d968417074815111250b8900707840107160b80502046c0c900800c481c1c0a520748160401d8904580b03402c038281100e1101e0043d00394011032840b181c080518061259246141d100503030402400d0030200d8150340507542603600c1c0c04058011404110004450346801d0300c858048500c4021140c0340010203800b10f180001260008100c10b6030929099200490068020300c66081c0010519040606002169030707104050584641c2480440d500c412508000400402800c0d0196100d038401003042c200074001c0c442021101c48680314220f05003800c2c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 189333633 1250 189332383 189332393
    0xf06030804031401020c1203040308180a02011206090c0c02040e03030f070c020a120b160f120e070914010602100b0616030e120f060916151707050702030609060103 72
    0x40d01103a900c4002c2400f6440400c440e1802070090310680816070041c0e854061079083c40c00c008611451080c1c60b807403040d444400d9512241405075041c1c100d190b01c49c00d0754502560085040717040c80e0365070a03000300e031722500d848542c0140c8510001b00b6021550b110314030b10071440d260044003544688035000b58150306e050b589a0600700009010601484403e540d880c2c02c0d034880b000103101502d440031403259026000c1c0b0300320700c0506e0200c417814060000c0441d48420180f0076080907407200c804c4d9440c80c244500c2140780b0001404042425440d6100f50200001c900c0752900403401c2c6691413055003000b0b5894000003a00f07045242d0710b501c610601c0e020b000c051540c0c0c3d100a594480b040500c485100012920b01655492280da0816134400700421078401808000150300b40c041c2d000038151020398403510307a0030b0340d1240a10141080b2881d203810600c4090207602c0b240000f0308451512501d00c1c20050300e41c1c03030001c4043c0c40401c00140005819019030a04001003034211100c4401041e09601d5600c032 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 189334883 1250 189333633 189333637
    0x40f1506120e0102030114090906060609131503050307050709050c0706021605100605040e0c090705032203020c040501061106041416120209010b0a090501030b130203070309060f060308 81
    0x100410300c0300c81e900c4200e54a030541c0c04000351449041c000c5580f540c441d04c07608050509075041910900030000000e200c0c00f0701240c42402030b90701501040c1002c03082d0080040b03a440c0c1e40502541c0e15030303c00b440c52102e4214103910b4011401200030350742d100b031207040081c00d012940c2c01c0802d95a04040600000072024030450711034a80041005841d6914410600c2041c02101030103010780c03185460b802800b52080d840507003102d00031542008124500c1e9000fa4455503000d520030303804208040000c2250b40030340c0c0116071042d000210072a07110328418028600b2260007000f900103a21810b003100141c01d062042d64058203040c01c10006811303200c60203903035600004000807c51201c182801002c044108800e00c41002403000c100d100c1620b4801401c00d4120f00ca409a21440c103420000a0f00c0c480c0f00101c502200c6c4a50f40c11140c141084015000382c40b41100e42900021114422200070180f480518018559640c002c00d01d0250703410418160b0b41c4003d00d8542051821104000141544003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 189336133 1250 189334883 189334889
    0x160501080c130644011a0d1a0a030b04030306060c0f030e030304050d060504061a2103040905240103060f050114070c12030807030b010c03050d0608030414040f15 71
    0x641038080940c0d0b00d04135014001e0028094400720000e064094044c925403041c0b8511800d000e0440c080c1c0da03a50742858000003c3c456039000d0f42c51003002030001c0010142c01840c06048200c91880c480781605010800071009540107540e0101c0b00405c1c4000c0641c14060240180341c5403a00010b0346580b521a08850a4203c03030080c1405244a04442c160300d0500070360780100001400001a42c28509045014000c102c4044607020f240c5841c0818000c0795000085980340040e181d0040034400d0000c0350059110019100941d100078000042d4454031400340911843c0204801c01c038540300070782052032944000001905141c00c10000b0b01411181020389012a403007440e1041d4030440030071100c48076200c2d4a0021b00522844000403400700240008801e10b94400e565408860b0317140c0d207044040720f08100009000a10480c154404280706c0c0020740403800036400c0c0028010342c1c0710b8030285141d0003070744804488007092038030798694074062044448000400105100400c501007040300c2c8441ca42c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 189337383 1250 189336133 189336137
    0x60c0a0302070c050415030302010f0c0e120c0301020a030605030c09010308030c090a080d020c01090b0c03030a0207111201050603150906010b03040c090903080a05060d151d160501080c1306 83
    0x803521500340810900010700500b0050b008000700d40d108680c01ca0121b01c4d6000907400341d800c001c4403215071070480c41001802201d56a64050521507802009405030b142d40c1d03485020301c00d841c50103a85035070a01c010311a140c1c043d140010707010300d000c00740360400081c1540103110309801001000403d0f01e000c1140d610100b2003600c203541d1514800080d20101d80c036008800c1500c20b561541d2090f5800090305154010241c07030f1461840da45400d00b425600c10300000900c140c00910100d2144030450f00a800d41070710840b855220840c1a2002c103046018000e00c3c004160344400a101442c182840029000140c00d040050a4944250015964601131084402060b40080003d040c806290f22100240407521010b01131402c690038014800102a00d07200c6e80540b41001003450761400d44615500140d110305072000030390071540ca4500500001082620204003d0741c54520b0407814040c0d001810a40c100c00025141041c000401c000c1006262030300040c02004840b5006801c0907280301143c0c1a4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 189338633 1250 189337383 189337387
    0x6141206062b05060109061a0706020f040915090501090b090f060d0f03020105070e0a0303022d0a03031e050103020a21082d03011208091c0503071202060c0a0302 71
    0x500c000c205002d28003044a0152403120418000700003002c1201e504131002d041c1c00f800030903161328a0410300300d1609030080c05c1000c10004400012a40d4003d8045051025000c40c10550b0b90001c0400740c5580f12141aaa0840010305102002040c8205030240c00a0101080000402000704108060207403e1841d1129400300080c2d5903034a40e1040d00407540d0091722240c4514480c030700a4042c080a17610700020551080348800c0e6801c1c8259035a0403260168014501d0101c0e007400b42d03032a914082c203008400d4030108400300f00420300304010030070750f4440c1e500041e400c0f04130b00d0142c2c0d00030101148021040c0c1003500403c0982d48010f01c00c0c0c00d403001c025504040445445030000030014044005141c0c1d6808210040860241d41e0302140000b40c002c1c507034180300c000c00c0c1014114442401107400f0701190f288240f000c5040c030000741840c40b4000d0480d0305001d4001c00c8422448801c03440c00ca90540c00054448104480c00c045000407011600045c00141032140c041d260300e000d03c0661800305540 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 189339883 1250 189338633 189338659
    0x70203090117250c0b0114010c060b0d170c0601120b06100302091807080604060608072a081b060c030c090d0605070905100e03060612030f0301090614120606 69
    0x35052140f81840e207100d8041400303c40205001c0c0608010050550705040508000508115880c8009403100e00584d2441440d07100356940000400054188641001c0109080d000088108034601d20b40c182d40075025448074600e101492a05805802220348202401203060015948006c07458002c00221010f00c588006600220024060b28401c1ca501c81700e2507811101c40c103207404813903010391610f03030b11090b581e81e0301010700040e00c40900c5a680016095400141c015200700e5100d001481542d00d44a411801c0035403890740c0c2e401c0640d05480041c0c0005940301c0c81401c2c1e032501110740340c504014000c10310300405c0d4690305000c010078680b44c26000040032b5510b0703030f41d40810b03410140d030203c0c0400007410001c10091824040d8001e0034021003070045004140b03400b0309541a18110010001c0680c1d40d1008240408180500600702e0144014440180d85030241c101642c0030700020080000c0b0b01e407410035655a01e0000c000081d00a1780035200700e0304d031a03102080d210b601010580b02d4401902c8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 189341133 1250 189339883 189339901
    0x50412020409050a080f070c0b090d14331e1308040504150801050c04050d1e0510020903010b060a081b0415030509071a04030f0309150f0206070203090117 68
    0xd0011130050640d500003540e1131203c2804009041800d004a01c80e10000b512000204a94485d406c0e405910012200216000030303c0e080c05450100c0d45081914900000d0760300360405c0c130741046020350a29000700440b084010350522850360002030300e0949105154469200c0c004c500d405000d42a19070890840728051102c1d442c2107900410016108103d0100120340c1c0c0c18041c00740380903040595003010701040c20700310315000781d40642e40018101828540035545403046409075003140301804019a03a0100451018030084008103203001c405a40c8644843c1014211400c0c4c205d0310784141c8050002440841d4019549548041a01c0091151540c5c0100c030744a5400303141e01001d11601ca82c2184210650716800290040181104841b1415211104030b500c0021400c5180c032010418842000403d0f108498503440754040c2c2041d0070856156000482040340a40f010800b08064001c05644540e04100c1e40390b200c203161000d941440303a5480020001c0724501928041d4490314000b044000e0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 189342383 1250 189341133 189341143
    0xc181703071403070201090e060f010305060f0d0b040c2c0603011104062006090312100906060807080a0b1c0c0b1b0d0804020102060609040303140903130605041202040905 75
    0xd50040c0b440d815403003000c1e980a54a5122803c12030010b404130400041741681000c0040c05040010080f131300c801c2901c00110700034603000300300304d0340013010f03250312503003500c4100480030780c940140d01c454031071700d0a030801441c9030400d0b40c0a0703403580c0c1300c02d0740040e146049080c0c001c502115803d1710300140e80740d000c00a40540364840d0750341c0d0a00382c0000c0010f44190020754158201000240800001000d000515290642100c0c200c0c81030300204101040c3c440c04079500e0b0360144980710f801460b540c036412a001199556001540410200c00510141a4101111030790100e80d014047c001408450b000c5452410b00341000210014811a114100691910f00344081c1454404194807850107005100d21400307030101c1010303e40204070501c5041b62007420200d00c40ca8041c0c0040066403140e00620140e06002001507041507910320108503101c04030a005d501a800c80d60055440d4032001e814041c400550740d000009000042000b04081800000c11540e59078045800103003182030b50030650300304 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 189343633 1250 189342383 189342397
    0x6071707050105010b130501050903070902091f03090209091c0e061b010207140a080906030604060b0c100606030c020a17130b120f0601080a1a0d080705010c181703 72
    0x9542080008102051704402901c1405400d4514582140c0d642006452a2140140161f00341c4c06c864002d200146c1c42da0001c0c2100c0d000074100c40040422254481c900740021880c100000ba29000241c00398500792600ea60015600c0c3e000c0c00740e42013202c0840e4090300e0b51102c1c110a020515040350722640e541d1742520900f044440d0190130f0640c031900480e00070350098008491072070b20042031240b6044006100d07020580d0110705140713440389201c100411030b0030090003940c2c8075465042c04254051520007610030395002000070803401c500041c190064481d550840703401c00d46007881d40b10600354001405000c00d500441c8111a24414001e40f4503d44501c0c1000c000301c4260803c0018a03051480040500f00418501101c160301c56194001880e1001d46005000a9032100840c44000096020000403030100c00008000d01441d804101c0ca4001c2c001c041d0345400300403d031402030007420700810113000000e1601103000f610a01e4100c00f4040c0170f0181001c1d0078a000310034010002c0c1042241c0030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 189344883 1250 189343633 189343643
    0xd05030d0e070503071d0c0c01020f1914090d06090c08010618050a0203060d120207150e04060b040b0a050c01110d0903030c02060702030a180302090a050103020907050906071707 78
    0x4072040301ca400964800051007058064490018000303020782d8002000320401c444040f40000721b4442500c0d0a1003a0080e141c000c003295401c0214a500c045e40038018401060b06c202803001c0d00c8104807010b05266940280f95800303040402065046a407850307120f415456004400055440250401d40d0701391a0a03004a0100d42c43c0080104d40107107e1140281c01414000c010b00060781e43d510020168081601ca1135007210303485183d0030002e0151070240758101d000340f048900c401d549014a010303c032000c082c0080410410ba040e240f10b424a030041c0005015500d10003480c00303250003519403e500c10a0010b030200070b00072804a505a030203400c40c90034030f20440351076511850120212030040080790f4003100481e1812000114080c00402d1107882032031150003a6082c240d500307030160b88235001d100c159048140750b4070020005942e0244c42038010399141000144139811441406924900640300e5001d002040c80324044941c0c3d05070444418503400094840c20000750341c80d4801d00c1c0110040141 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 189346133 1250 189344883 189344891
    0xc030603030e040f1d010b030d0c0c05010e0102030d0c0e030705120d111f0b041802090601140f130801060f0b1804060e04151109090c1305030a06090201020106051503060d05030d 78
    0x51701d4150090380720040b0403002d40c5c0c3d044095840c00d51f03840c039407610010441c0e00c031880c3c01c020740e60003400e014450200c107006582c5003038010024003086034035520390440880c000544252084c00c0401046010700b0040c1d4588500c5a025032411b0b95442c507091641081100305119800091130034031550311814150060540c01c40018150103000d851141000b60050385030800c03030f150004010303441c050720b5500a07140c0e8005840c0c4200440300300c03482c856000c198100070044581405428001403400040064205000c1c60905c0d66490940d00c040d40030003038070203c0403018003580e40000116001042c0401b0b016a00007010008a0060250b65101041011058003000284410f4600501c0d107100520810044c0c203405841129250041c041c080380c000e9030080004c1d070b218642000038494004c0f2000341c8002c40e03549200203464000f5151049444c1c1d622020b03d0802c65809000f181c01070001156240c071300f104488101c4480d0302000b4011880341d00b10241074410700c03406200b03c5812840542040c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 189347383 1250 189346133 189346181
    0x10303020109170307080f040201030204050d111906020304060e040b1302090307052224031203140c0a03020a0e06040902070c0b0708040509091507120c030603030e040f 74
    0xe8001e1080080507a011502950340d80c0d06003900508807489200303251511001da48403410007510781d00f0010422070505600308001b007a5551a40c034400c11541c41041200300b420900c6090148405802c130940310b0f41c200d0f02e203052080320340202c2a030342a82c049150101c1c5041d00603000901420800c85146d40003514030b41c0f8400e00c4181c1c0d40003000306503800e908548400b960340c4244403004030200d4541842d541390405000085880f50480a0402c4141c0840e114400c540d07480051580c49075401281e4001003020703070030500c0e90035000307003c010812542c400010b4501415409514454114244101503000550210044c000c500306000e0762000f901c141c1e00c0d2500e81103500c000f984030507800e5400d151824000182c6503c0324046a03100c076809684a42424a40b4083c0605a48090007000303040c0900c81092022800c0b486119204035840c1c0e552208402c98200071a007110b0343c002c01401013506100c401e01c040ba82084051a11410a0741c0c0010004c0f212800c81d40101a140e00c40b200614040c4252 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 189348633 1250 189347383 189347387
    0x6061f0c06020f04170d02100908132c0106120e0f0f0c0a091811031e060711030310062f0309040513050607050313060207050a0c0b040f140d020306010303 68
    0x54819200c09141196502174040c1043d556110080401001a4004400303d00c209116802c0b210071640704000c11402c02c045000c1c401c036544c1560308503a095003540d4440c0301e0000f100310310840146462407403010760f035410400c0040c6024200c00b0300c10107490319550720a00090b030400540e0070b051640c01c2a44d003410014030b015030f00c91054808241c480c0e0850301020900c0c4230030744140c1c1c0310b44c0d55890700305e0f010034400d075141c9001c01074021200e541800345840c40c4240b80c883d61101c1800c201843c000e81a10f01d03006101600013a12400e01c0305203680309204101d05143e00c165000255001030070044034180e00c400d80040c030300808128019500d465a0558070411000001800c1c244504071014405595070341c0d06500e80340c00900001d02140c0c050004503101900500045800c000300500702c0f02c00903501e85502e41a6030101c841140d0b5984070540b0141804101c0c0c000001400b040c0103410303e4a403611581400e108170324050404014036400308200705644050381800e041d58040e05035100e40d0f03924100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 189349883 1250 189348633 189348637
    0x303010302060f16140f0d09140303040b0d051f060e2808060103120f0c06050408090604032009060f012a1505070c080708070f050613020f0306061f0c06020f 69
    0x81d0401b44140d00d0407001c801404143c04801912541e00c610342c0301c0c13a10101a030381c1001040e915406000410010032421090802040e001e9442c0c60f01113028240285a00d12403204d01d031090015101807401401510b0b80a186040c0000c0101c0344041c0100000801005900c0d00c1c50020005080410300010170304804164a8100da0042c56070042c41e0960740c2c026640a0f4000325181c0c00201c3c4028001e00041d0b2590113590464029a1254100128080420300c1503200713030001d40d19002c0403c1c0100100c01e14840501e0040816503003107007541000c0010610303088410f00c5140c1030005807001d2441029902c118401e850f8240154076a01410a052000d503040312200c421941500341400140714500449a4860050384255010b20784010b1b51039925440d04502130495041c01c4600f5600003040c42000b08602070404c0040c14040f0300703e144100100c044103000114003e03003081301006913680d1007056481211900714800d07440708840d500c04856882d40e24070000c143c1d40c0f003c1401201003400c100 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 189351133 1250 189349883 189349913
    0x705030417031314010507050f0c0106050a030606050f040920031504060204030b01080a0f060509011b080106031d0705060919080610240e040204050a1509050607050303010302060f16 80
    0x1180e0013040c140b0b10034542a07030821644a000b05804204002c00a10000014200454541c00000c0c65640301c0002941c0c07907013242c2c8180c0d080b6407119001d10441c40e082076502401c00046408011071520b940c1d4505d030090281c0c803400c40f5108111400020b5071818024880003e400981c801c00302d03d40791030b01a0080d042400161401406d440000c0f542002c0020140e80e0309030021380d40514039100f0356880300a000d001344040c0c001d54035510b00310340b80e2000325010300e4210f5207515a0300182d03041c10f400408680d131031841900500c00486031550b20741c50101b07440043c0c5005490f415a01d4210300041440720b48085402001a10000000a00540c0105001d40944c8610591804869031494603503002c0c42c0184120440314455000210f1881c0212000060004050030150405559a0014896034003690120f044014400740480e00f0b07983c04138012019080803900c8d00c1c24406e4070b8071015a24001404028022800040c46590406555003516401d4940003841e05013410306140c50b26402d240da80e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 189352383 1250 189351133 189351143
    0x106051c0c0e07050708090a030b0f092505060a140309030405030105060d030206060d0c0906091e090b070e0103020405120d02010e030406170a0609110c1603020907050304170313 78
    0xc030000c500b100c056028079001c0d8a45940d094200f111035192800702c0d90050f28140e500c00c5800302c00000040780419150f00c030300b07907900703480e1150b16021003010f0407c80c0312054a0554604401e1040c8418a501d98500a40d2402d444950315005542001d0b643c40c22030144c0480340f5030011007004a10a000001441525401e4009200c00e807a2001402050b2041c1c25006001d40c10000000d160b078240700c54000d8a140c0201c06030305815983d8000c0000701e40303841e04205021626007241c142c02d01c0300c0c2d0420740560800b09408115101d610780310740c00e0350366001e0f080100300505410102126031180d01928042c0c04020a04101e00040ea040c41ea603c080500c407071300c055400c040d07803203880347c5003c0240c0d000c6030b0850720342ca000c42402403c5007002e070100509105990f03235280c2012882d910607104070030306400d24804030340e5581e120b071010310318048103a40da006004080c2003041c8016150303040303015000581410110344036150b03881c1c030091055030382c01c441c0c00c924004001c21906004011035032403428040c07 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 189353633 1250 189352383 189352403
    0x1306020c150301050405090705040507110f0304060f080a0f0213080d030b030c0f040f14060102160f1205030c0f16050d08030423070e100b0307090b0901020106051c 72
    0x4041c007440a088074010035107001c0900042026003071a0f000b817a40102d40c40c080d0b800c0c5c251110002003c850060f0340b110009482c003080f07040d50240800034029041c0e600f800070350510b0b141102c002c0500100f020801d081120200215000341503a0300440d9100c5040c000964030740c1c00001e03468560b40070900c28414140304e03209861503070b41d001c1d1044101204015002e0809506240c0c1480382c040e0344907000d20340196864881440b800ea0038858038040d2580c40d1310f006180c1c1001d900083c60f0103034411140481d5020090100600c04206040d08212274050040560584290800c14210b00076820314240714040c0075500440070502054030981540c0c0f0000d001d03005512039084c0400003845400091042c401000407070007080c0300c46109810404034051400710208140c2016062025903070146440c01840c50500603c0003100d000303040904441c0052604514041c0b200a290038554820402c28220005403544541d00c02c0d0441c102901020300b8040341c56421380d0042402903202502520645a0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 189354883 1250 189353633 189353653
    0x8030703020a1703150909100e0106090b01080702060109090807020d061b03140a02030406110a08010501021b010e090712141017070b030915040506190b010f05130803130602 76
    0x103000c013641d024041c200d03a80c0315044a11018406001c60180c0819268411241010b8152206000310350407581c1d81000407903658901041c007010744085507800ba05115941041141090f40083c03203d04540340c003207001c103d580890400081078401c00b10003035003100341032540d00c2c00c3c49455000b030140301c41c02c202c1c83c06000d2111401103003150081e051890180e0102c00c00b003405550396401554006000d400c1c000b0307410314014043c0d081907102c00c082c0700100f80051f004112075a0181304035081ca118508000ca00d001c0d000c00000c00c1c04c204103488503ca1803110001c0b0301a6886034400a41c44580d41d0b10400001c0c1803400c8442003018220b4485100c243d2031000481c0103001c03e05076628030721182d0020311005007842071100d101d8000420a91061051113043ca10b4000405070084c0a01d0042020300300d1802c0450b907401c201d0040101804002d800c050700c0042c00e036841801e61142c060280351a50b290f00329080c0c00c0018100ca5030120440e8400440c50340c80301030900240000b114503030f8003254000380c1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 189356133 1250 189354883 189354923
    0x18060306090705060414030f15100605180409030309080a0903020a1e060c0609170307030f06030201020c010e010e0d050637020c03090306012c06030a110a08030703020a 74
    0x540501c2d138000a090100b0000102010b0301196490001401d90b500c2c070450800080c03a10104d00c84034914920300303070203000c1c5005001042c03030f003c0c00c0e0034580189440c0b203242004c1460301c010a0818001c9940741e2a14040c18031035072010207100d5121141c0c541d9484110001170002c2c5290109a21942043c0800100d00081c10541052203081841c0200034528100d070a58044d6807414060741c44a496540860024a868420100380d4150700400c90322400c00241c000c0441d0049541146107a01e0030b042800540e80001e0f107048101070074601513035803022a2004803880602038420b103070030101e2201088200880882c401d8461b400c403072070400200c030140d03000040c0400c001010460050304004080a0610749800819a25620004580c170300007036a0302003450709400b40d1290100c55401c05d028901c85001145e0900201e00218150000d4100840000d485407002e140040201c441c0389001c038541c3e00c40d480120001d0020784150394507400107040c080d4603104941c1c012a0190050203080c0d24000e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 189357383 1250 189356133 189356143
    0x9060b1206040c20030406030b010f0926060405010606030c0f0c0b040812070c020a050105070506011e12111804051906060b07150c050f0d05070507021806030609 71
    0x1030000240588141c41d1002404010301159643d10704000c0c28a244504121409080900c540c08003070096685a1500400078100c1d20286030703150411500c0c20850340c409134001f64480135580303414218074070b62941076890754440c0950404088a40180803c010501c03c5c1984004200c0f0002d0328140901100184226030703040b41c07540c009012500d940070800200f1485400c903988503100b900d16030f00c3c1071951317040503502c1c1000b02d075500c001404503980041182460109280201404e00f40345080c034900b07a540b84c2e201c0c00d050050b00180c1c08041400c004100c84400400001c0410341400320000c5a00d08160b4140f400b00f02046004031040303040e201420071b411198038496074020010789800340c022001001210301041d000c1c0d0f400c0e611150086540c141480003400070f01d00c03800001c0c0710b11081810180a07601d814040b081404014400a0018032048040385c1c40105159030005442d96a00340c182d500e400754036030107904a04469020b440c100d10751010240100d80c210203c92403556503904003552a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 189358633 1250 189357383 189357397
    0x210f120409060b120a050405150901050405071e0902030c0d02030108100e0601061b061d0a02030105090f0a020d08040e1306050f060609040c17040506011703040819050a0c0f09060b 79
    0x304008000240417504582c0c80b4541045c8568151419201700c41c8281000c103100340e411081c3e0380d6480c410302c02004020400030000780b00701c842d403d902181a04a41180c02640d02c03400d13041e550004006113089545074103c988080440c0401c54407540c6611410b41d0300c03085401e540d004103141404958100c0400110241203030302d1a90360317452141c102c070f6140c200e2040c081001c82d001915060100d020707111644849040c480050b0003000010b00600415003554800b800403440e41c2c018581c1030780c0300d02d0049020302c42c40d5010b03540c0c001c1d4588a441c10903c40e2103a688083c0c005841da2042c0010100480510710005000e65400c0c0119201d002d90f424000000341e44c400d82c040000c0140102c1803d0030380101c41c12074180c0c20f02038517450140800c100b2004084030b04944603081b22005100b820004406048121100c100075800c040c1003541481e540d8507501c00c640c07030340d1114121030001c2250400c1201c4495620103100169a1b03030360506803083d0101801031000c1b10382401d03800314584200741e09507205 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 189359883 1250 189358633 189358657
    0xc19080a03020a1101060834170708060c0702010f0e012f0604120207060212030703020319020a0f08090a110d06090512070b060d02210f120409060b 65
    0x26116480c1000d80c025800648914148401c0d48480c00040c1002c0c46800000e043e8031010f01030300280f03554840a07030001030503084075007032240140b0800c1d4400c1440c42401c3c1c0d42c2501803120300300c100703e92041c50034030a944803c0c0c06114000030020150400f0003d003030598030030b0300e90f14880c1d070b020041a6036201030a403400d400109140c0e40b00747c0003039607201440e0050042e078080110001030041c40e00c2c01c000089800b070b24100f06089840c444968100541703401004188042c10783d101c0060311a039450710010708010201a004000b0030301d01a240c02c044950761009030411541e4482c0079102404040b002c2e220100402c006000081000304080b03600d44216600400075142045940708004040c1340505068607255940c2185400080c070401804000d0b14105135001c0d140c9110b4584142951002000d0070b008001035030780000142c88034421050f010000003000044003c107002c107103241a001c0341000c06144120b00d42142d80210080080040d00e6000f04c0610580d900d601d10003104e8882d0400c0066 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 189361133 1250 189359883 189359887
    0x102190615240e040b030a050312100f15020313031b0b03090307061d151f060c060f090209010f0602010b0f01090312171806060f030309150d050c0c1908 67
    0x80103d204040708940c5400c0108006070003a40c410200e8a014841c40e411202c6a0000901e10442810340c0780c01036000308042100310f000341c03d1041113002201c11340701d280106604000c2c070680490080c820f4922000b0324000340904140e407420312030501d840c540040103e030480c0e4140070500e2401307401141c0c841d16440c802545400700039aa10300041c805484001d02c140340c5d0000c00c819000f401d03c12450391000500080409061000003404206280b25441c07002c12114041045500d410041c0c604a45070040400030700d91400300100c0b80074194983c0c0003984907641000105c2c07101e000744a280c041e1245580200206101c86051010f4500d0481546002c02c2e802c41c010000580080e040f40d18048051070050105880180c102c6070750203081d9254280c11590184052050700104030041e840101180c10601e05d60180c0042901c3e441941d00f034601400c203140e11480407900b544219800c4400c1964200501e01d80f03801140f000390442d0b01100414010000740120a07564051003204181d080007981d8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 189362383 1250 189361133 189361199
    0xb0f0a06050f040b0408070303090602060f061509181602010608121c05010303030207210c0803070311033d14011209060507090623090102190615 64
    0x2440d240c10511450b00121010400821a00601e50140004040501c001d1038018154074000c0d08040711500101c0031988580200519504e81e020100c2d080310b41614508210f0444100b00d0301c2d18481c400c9031315040042e00c601e140b444850656100d1150315124020000781000510880c01d860840c030400b01d0346e81c010f44038403140700031900090040143e22410082a07003190041e07201545c809130300680110b0ba001c185a01804603440654482c02024403409c145180c040034003a0502c0050000502200d0b408030000c2c8000c0e000e40d000044102c141a8540d440b49004c0c0a40d040f94000c8400180c0e56014050035440e03c40740e110380311120313014401d00d1401c20078105022020303003031604000941041102c1c140d05e60b220049106079000c1502a0b180403e43d0314154402034598081035011800308101e00348419142c10307101d600f82c0150b08004016036903410003000102c1c9003e441140d81c0307500d02d280030b00b00c10821900e40d0201c1003204810751862800390b0f0300d45a007506004080c00e01280d44060036144 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 189363633 1250 189362383 189362387
    0x60901120b010b030c0903070b040810020c190602160b16091a07020103060b120403020f071202061602060f1c05040209180a060203090706030e01020412020d0c08060f0a0b0f0a06 78
    0x951740c4105440c50700d034180b00f21131000a1070142180c1c020000380000286c144000f110034040010f0b00c0039010b005500e408041e003002603903040489000346207681041c914108201d07240d0111080800c21180000c40ca000b0b904040081200656081c4d800c403080c00c01154440e4003940c1880c00312014003100301c40c00300008141c00042e0f0300141c4105d0405599500108142402c10702070b201f008020700200d05030745420324002c0d141400b1801100300c964401181006008625482c810b4400e038142c07500f0f0346599002040302e503003130f1125400a5004401064581d0041c0c1c140000c0d01c520000201d0145110880780c40c2d96080b18001e40b8080d4105210000003403229001424119210301d0000440c3d03407920712500c1e80b000b26042900e0b214119040b000d010810160705001e41c24048002100071864a46428000c240410b441c0c0b030002d005100b0b528a040510000142d440c008081d4401038581e0751a02e80009800740300200c03a201d0000e4a048200140b81c1020b5440e590300e2900506074600c618180441 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 189364883 1250 189363633 189363637
    0xf0a03052509020301120201030b03060603061305120705240114040911040c030203060406081516050d0e01060302090a050412051c060e060a08122a0105040308060901120b010b 77
    0x24540101c10450000501c01d015100035030091011000103d840d4a07548001020346110320790701840780e403000c41031008942d0b001c210035070002d485c040c001a4424840c40c1c043d00b44606068403807002c0030003059000c01d0142c04500300c500180440c4081c01c40b98032105ea6500418420b0107859020000740000b8015400e0a51190f840d4900808500030400031900c0001e0558884052040c002600401030226900b890300806e000740c0210b00c0a807a0a4002d000181a01704c0000d100b01c0313142034800c1c3c0c6101c0300340c05001201c001d54000b80c0300b48050075070108180d02900840c413040b40910300b000006403080d41584a154001ca903c00e040d030b2031014000c1d00c201c074542c10001c10348040400355000f0f0511080b1911800f0b0052200204202c147d1030050108078071100e040c1d1240b40280c20503200e01e0540712104040318003c02c1c120903420690501c008a0170701c903103004000c0340401c0d8030300400e02c03040c10b820001e01c510440086070450440e0780c030340060680d500c84d0400028880d00b0404010b100d03c10000e00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 189366133 1250 189364883 189364933
    0x5101202060a0311030a060e0c040308030c0703110708010e0706030207020f09070207091a100c0803040b0907050402030132010c080915120403030c021603020607020d0602180f0a0305 80
    0x9404100750300c0b1340b82c1913a600d1740151000d5104030ba9984d42003001b0b10894080d144d0180c00c0b60340285c10246162108500b600c401004480074078000201c07002010b0280d1003442d0b41e030484004603250243c80d001e01c1402004003102c10615481070031800036100748030740202c882c0a9406024400b00c500b03441c007840020480030703007468103600030401e001c2681c45e034910608803c000c0c90400d441e0404120002d00400d401c2180300c400c20400341400310300110700540c04481e00070303500062180060799441e080341d041403103507041282d100f8000800090f1800819102c1c07151a5070704a812500c0800e9803a9418001022110581c0861006024140480c401340702400780c034000a00a805c1d00c207045049141d860340000d490315020710160703003400103040c0c1c51f201d123100c002041d000a06606400508207004506103100003442144001103800031500c4030022209802d60200c2c0039502caa0400c0c3c4508010407580035241c0c000c40078900b03581c4840c94840c1020f400c6a400501424100000003060704d84c102000d5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 189367383 1250 189366133 189366137
    0x103050a060e0703020a0e04090803060d0f02130504053903070302030307060c14131203030e0106090506010f03091509081b0d090e150907020708120703020105101202060a 75
    0x40000207182c00050082c41c4140d901e503a00603070b901040d00c8050040c0c0e042039003040c0130368070301550302c00040c00c034804a0b42c200404a50400c1c01c140705140c00f18029440f01c1c0d000f504400407070030366440c010356070704010700461007a426148640d4040b645400010035407201d02c2240b2488290410101900d51262500c0000c05000d0714a515204c0c3c002c6171465001c060219051030759508401c454541c010300d002d10160650315510f150210317038400071030a1071850003141000344050b50a041018000d43c0003e281e400104000d203c0103603a84a21001044101c0e191404256020105444584241f15100c0640d034001240e40405801210500061804080803221800c04000554940503022107196140240500030005000e0703018000f0710030001d5620252a2610282c24803000e90345805052517094416107600c40903556542040f07140c00d4440c0c4c0901810301a00189801c0c0c03030340100040c012540243c000b0f03c1280c03124001d1807942c41c3c440c41060380d11030712001c00400601d883c00080c1058400c0c0c0c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 189368633 1250 189367383 189367391
    0x110d02161e0c0e09151003081209010b0a03050a1104020904090b060f031f05060d020307090b04180206221e052106070503040c030c0909030f020102090a090b030109170315040b0f0103050a 82
    0x2e90348c17020154000d1072440d100f040d1940420070380708024040c18030840f4055980015051a65072810f070303182003640005007900c0c100007200c422078441d0f6058580842009006010500d400d081c100018503007503456600402004d50340081a08001610381c003414103007030030043c2000110b80b02e0b000405001d407050b0b5109030898007610250380c081280d20302510031450300040301228081000300710b031a02c01d0410816201e28410502503030303a00c0143c44480c282c9a0960707000031800190031681c2669600400e0101071a06c8000c90002c0d5044414070a5038425600d0b40714030880400242440b16441c4480e080d5540201c1c00030319003500c18000381d40c1040c414102e205a8a480303607a282111402034011000e59a95181d884041c140d000980702d480d62036500007185816142e80c0071414210442c00390b03000e81e030740781d030003186003600c00750f00c024042500400310140c001c07803a1084c5440343d84203440705544000c8010700c040f01d5151602c56181c040704002c0c040c08080401c00015406040c1c000e111458055907 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 189369883 1250 189368633 189368639
    0x15030f0609011407140a11030408010b01080c030c160503070605161b050304141507050109031713030f022109040c03110d02161e0c0e091510 62
    0x104409202956044054046850510521821582e214041d003020950301e0041c445050740041c0304089401841400a0340d0301d422580071b5445c5101c1c44043c1e1414480090000741510041d4400755607042c090340c501c6525260b070554814140130503240390401078010042c090002440d1408012254456003c0d071f420010706456180444008544a080140a091a010586a102907842404080406006807400858941c07640d81e0041e40644c0d0301181f58040c4102075903a03030090481c1c45021411401d41e81c3c2d2a9842c18a003e0000320b54100c0100390a1014884400c2400e400d035440381d81460700300c50b01861241c0b002c07070f48403d486003100700b54060750000060710074030414a50b08800c1e803004940da998000b1b03030901044907003c0d80442d040601c3c09405441e480112801c44901c03450306032002d0303150200d103a55007290030b204080c001d00940020b0907003464140c0280f0500310090142d40035030b90556460400f624990000c441400e05a0010048010b0f00318502505a070400c4026000ba980031317031 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 189371133 1250 189369883 189369889
    0x4020310170606090603011b230403080903061b070201080703110a020109120309050a0f0c0f0807060201060603141911220f080a0b04060b040c05070314180915 70
    0x88118074000030740100c4208641c60a20711a0141c2080003034000f000740c40f0000d0311818800703a0b42c040c404100804010000390701380e0716180350b03003031241e10f105550f980715030f60300d48002c40d80d03c04400c05006e402450001400d05030315106a031074400715401c006150000c2c9600454694000904820030315a48004881e400b44020020b88450052078000250400f021304100081d03042000c4044105810154031600142c40410030f506156803002c80d000c0981240d2404100200c13070750f0401e910300d005d140c800086c0540300181c4941107541c030307070004c00c00c41c2e0b198501102070328020400d856011880703001060a0804100400c0c00d0107101c4030000541d145000d00e807a0545d8400d444d8808415400c0301e00c0c020700724650701c0820050002034580020149803010f0360b604c4030f01081c005030400902c04005014413810b908a2600b024006108000e40c4012800291644c1c00c03e01094001030303541e01000d408a2000400c4034013060002c0c04807160b401102d0100700000b40024500004c800040b686802d86032 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 189372383 1250 189371133 189371159
    0xc0201020403230106170a110d06020a08070e04050114010509210705040605030f0604030f12060308040303080906070504050402070203120403061d01060605090d050f060108061f0b0904020310 84
    0xa101c0e200e21107000780d42c0b00052820340360942c0000c07806e403819290505450794005021f18255500c44807144505940d2000240b0a080c8407138080c01082c0000381c1002400d0740001c405115409540740c2c010610b14080c01c1c40304540c5c09004100c0019481c40300030600c8c1d070149000d0500c0007002042c0210022100c00200c4e10f021032310080ba0403660180d2820700403440c00b8040d0402030030064005045041112004580d03d40c80a4070107424808117002c0750014030b01c911040c404841b08007a09000c01903980ca0303c4c0c1e0701540300c1e2000f5400145854082030f480440891060300032406655030ba8149070404007008025030141d84100c0e454407408000080d240000000b0f0401035003e2180001c6801c0c041c810a015000c0c281080c991a0340360032020300600350080c01751401c00300162003600341c4401c00e00d00145800d1100346010918807950300001001c00c4000390b83e1b4820b0f00800381c881c03a02000d6408411001d20503001e40300d01c0100510551140d410303e940990740c040e4691420350041e540e5040705005030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 189373633 1250 189372383 189372413
    0x10905010501170a02060301050d1a0c040303140304120809012706150609090b040b060d1517030301120c12030f0f090513050406020409150f05090603100c0201020403 73
    0x141d445100420102240f40455000c040044016200e41ca030f040c0e0010b00580b0050151503c56144d0001d4041400100740c0848684a500e250382851400c00601c0c0964030b80042c401100082c07002111682c1104102058a011b1540041c442107400e5081000307540041008100104035940c43c0302e0410b00300c074503440034085007480c0f000d085000407045c181102524490035600b031540055800030412180e11060f403400720741d8030b0900094207149100000740502040a00a03500400200d08025442126031103d590a00256140c0c6c40c002e60f030f01d21080010040524003003540c1c2040c001006a540c005260300030451184141d4801c650329030a55240d441c050f400c1c01c3c0c000403840c00a00d0030103500710b20a00841012410a040c00c54640317030000c3d11461030180764265041e100c00c081070810485070151800380c02d81010078040306400814041d03445040c0e1280d141050301d441c500080c182086402d03e0302680c0b000e00904214601c696143c4040d140701b41d400403c565003040000007003021308038400c0803 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 189374883 1250 189373633 189373643
    0x40b070b0c0c0714030c03010e070e0a0212040602091e061b070e011e06080f01060302090f04020a12050a09020f1912060c120e0d0e010c0f060209030d050901121d0109 73
    0x1203c1340d41060520f0210000b048600030b03807500402c08800701c00019000d044a50001e0910303529554003403002c003c0d00480b84065aa040410306100030421180c029251101e0140c0303444807000790303d03218a8094074442d0002900841304018681d040344048110f00d4a5100e1601140c54455581d4101c1840080036400364400e05a6003d409102e602620364240080141d0b00d84001d4a080c880400c200e004018850710080c5540010500310f00d4551051204034010000c10864030780d888000c1c098036008503440010748891800001514101c0c0ca07100f140000d60300034000d843d50034000420301c0b01c02c0c4465400d01c081f148a1150001d0094000c1240f0b4803014072451020483c21701c10140a0030041805101c4000c0340c0c14485040a041300010709884041c11310700c2c00e07001503250703031005881c410740001002d001c031168a0002403d101c850340040c10030b41030907021074080e0000440211070034000d45039510300288807134155a441440c290851520184608078180d585a46641014219030b0100d2003150 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 189376133 1250 189374883 189374909
    0x51e0109150e130e1b040e060a0b040e01090506040b04080f03150901061b030503071101020304050115050109060801050f040b0d03020c0306060a060504032a0602060f010605040b070b0c0c07 83
    0x10303550410400f0108180c0346502d0038406214140b450742d890b05c4031031640307142ea8049281400d80d640ea464100c21080c1c0344100070740380c2c941400d04039080500505140c541c007e0303040c45180c85c0310840520407140e0080d040310203050f4a4903035a4858002c214007402c1529208801d000c92100d10035104011802504881c1900b0004480c420034006440c00581c040740600c5120440142200020003501040a40c90301d0400d541c0d44c1d50382030558007400290001c8455610210030403080020540c0984501c801c080d07805107106540f4001140c5002290142c0c0001616202c01001942401c003200701c0002c0c0d000b007010440c500b441c40443c2d2030500420042c0c1c016408074000c1042c905092051580003082510041407142c00e000020300a4852403100402d8103070208581a480000c0d000340644411004804054841d40c50100a546020540d0b800012146000000991a004000301e808480c40000340c035041c54481d440c0c2024202e8001c1080c1c001043c20407240d0f0080c0b10a10001c8045c0c600c1f0003840fa = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 189377383 1250 189376133 189376157
    0x17090307030305010e0402060706090204060f030c051908030d1a040c0804022e0e21070315200703031d10110304050a0f170712030510051e010915 64
    0x82c15200103030b00c8440d40c20114424440941c80300783c02c54142c41c0e000700c00030440542a10110f4020003080d44081c05071424250041300f0003c400c1e041000b156411116007145c4090640d00c12007612440c81190601e600420089050700c419400c00f0208044034080003540042420110381a2040010380400140300d01c0c1c01c100441c170309812400f00000141075040c1d40011071203208100d15559200410600004140120965403450104080100b50756114078212221b00503450703841480b408125003401c401549102c04001601c03600b48001110303081030700b504c01292000c04a9a000da10280c0400d6103413418404807030b1019003000031104089005101e034404c40600b06040b290183c640c00d501031010402d11010a400050911409410950000048040d49011518507508660343c2483d4500450302c1414084040c1c5000050f02554a09104039070f10403510b102964030901030300741d20074011071103000b0603a0758000d603004800060404040040c0c440d580c1d0700c1825075560240000414103002c0f5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 189378633 1250 189377383 189377387
    0x406050a030f0e03040b070c180207031116030b09100606321801050d09200910230402070803040c0e0123010507060e0705030d050a1e1709030703 64
    0xb01000814450100100055045525103034400c0f0f1040c0d0314078550100d001024400351048030001001071030f900701d26800c40c4050210203074110180030380101c0c04031946072005900c007240d0718a0684580c403242010f1403e43e070301e0a140002c00b83c5804000d02c5000088035141c1e201c0d10924004d41545c0c0c071140c10a11046070000d610541c1e45c20400c6400c00d80e940702c14009400348098030000c00043c803071401840900c80040342e41c2c0c091000004502814919110103000003281c2c410615003001402038078080b06d28040c068200400d4070781e82c440d00b03e501c904010704075a90f610203440342c2003043e000390251b0138800024243e8005c00401d945000c400014402001780c0103d0343c7c802404000c070004200e40c9811b20381441000c1040741c009400900d2061204c846e0701c0b607000c650074250312440c01c001d40100214166030f182814001c450092040a6410a0381f5000350152011030065a58840c000e2101540750b0000d1004282107509200740307080d03591140d17694502c00d0740c8100a040c0086440b02214100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 189379883 1250 189378633 189378641
    0xd0e03060a1806180b10030605071b0f0606050a180501060c030210050405070504090803070306080303060f150405090439060e190609080c1e01140c030406050a03 71
    0x540340c85490308810002e200101242807102c950460000144520801440c001c410b02c48100182000003400801c203491555089010a4a0041d8020005030380c4411095801204440001c0e088007200f0312000001391000c0c20f82a4034174858079010442655500c0400c2880c44141c116460b00f04103104030361032440651251900406207450401c0e40c014258801944404082103100e10882d21900010107008081107400c0c01414040c2081060716114101000e5541050f254a000a07051060000348107500009803806298024000d26120280e08100941840c0f00303035059046c84e0041c000040c440c0e0740c4401c064411030043c02050500034103107d00b00b0070b8801104c44a2007a00000c2410b03108890544d59070010b840560908000c2494035100040600307007a06404424109001c0340031400360703441507020046843d19422141030580c45000c100e905980a4040d6900700103084581d0070562003406140c682d02c0c1e80d500c6044c030305204103103024210307485504080081440018103031520b40e89485 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 189381133 1250 189379883 189379891
    0x60d0906020f0a12150510110a080d0b040c05092101020313170a0203040b0c010e01060807060216030209070804021306030606050901080109031e1716080609010b0a0f030e0d0e0306 79
    0x304014451714080c600840103418051540107214100c1102c2500340501003e0540343c0100b000c0301c10130382c000d151111203584201240808a41418022151401d260040c4199a140d5481d19400c010121080c1312103d0140002017564500503011855185402c0c03001754090380d02e440000e0364001944c1802d545c00c14042d80d00d10f070303451400c02400f0440d07507001c42034805881501342481e60b41c104180d000d601400f4a44481c83d0503528200000490110002c0e10008680050b029901c2004c00c000c0c03020f61a81580c44003942100c1d030540003075000d510445c011036000e88010f0070050a583d00b0f1144008441503a08122880d40d501c00c03080c0300301c0c50480030580c0101910302c024001036000b55030003480c1d01000a4004040d0700600709a01910b4043d100403080c040e14400c014441d49004000c0d441550141c9592030301250000c00810207500f40180b4050503200c894000c60701d031480714003044910580c041c0b11103041503a60308001d05400300c1800590680c2c2d000e5612006900008000c060501402130 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 189382383 1250 189381133 189381167
    0x30705280906082a01030b0103091a01060206131a060120010f05060402071e0c050d0803150a030201090e070c0b0901050414010510050105030604020c0102030f04060c0f0e060d0906020f0a 82
    0x44603070f15413090f645121001c010300a00c0c0220b01065120300607809810b042070002c00c5a542818400e0101c114113441038102c400f42d43c01c40301c40b521000d1181c0708840c01000080c141d29010710804040d003401d829580c1d04894185021681c1c00420900c9850601034030218102d203945450380750400c20840c0c05955081401160f0071898041c450b580e028881d204a0090741c94404803c130f00109002d0003641c400e005100180001c0c04600c00f6181c40d403196802218640801040301109601c5418044a400241d036070603110a0410b90500e01101074066000f06203038100940c008074900002d40b104082800b5648150000c50241800d20f084108240c820030051280d0785000100000c15003002c1d00981190401e0a0160383d030748508011401034403d040d800b982d298000800d01c0601d40c000d511141c803540c042e01003006a05080c4908461050b8107100c0e1000003160304403400d40920b004001411402c04d0380100240700d00b03407940d9402c160f810550540c036400c4c9000c6070200055400c0080b60354000c00314 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 189383633 1250 189382383 189382423
    0x120b07030606050d0905010e01051006030e07030506011a091005090108070e150a1407030c0c060c03082706070e150408070e040206130e100602060603070528090608 72
    0x200b18014480e00a11070381200f03050b10384407038100b806820b6001c034010340c81c0103001b071089103010540542e220180b0300c20780000900d040049885c07640049004020f4980c400084d00d850391a02c0464030034240303451a800b4680070700b00304c0d4601a640d950300c44110f02e034440d21003c1d2075841013030001d4041c3c54001c0c070041c1801909a00f400007a9105c00d8960410701210904e076407600c401c80e0342119401d801c050400114207001824505050700045007080c240e2155240c40b20041c0c80300003c8035070003203240006005c154842c1c08100d840d5401c6603a45450582616014803020811415600d0000b00f5250800401c07128004075405041c00c1042301500c2c0b840c216114503003442d04110b1035841344180304d145030080e5600b01107011581c0322400c40b0180929120200e0304551150f1940da44e040c000c0d00c00c1c11180c0c2c0c0c505000901303035002242c2075205020041c0030b088864508014003481c213406002c10f60065044402d0745094034102d182e0300c40a8800108001080c5051a092074900104001004082045 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 189384883 1250 189383633 189383639
    0x10f050d1505090111070b060405070c0b22080d0509010b030c090a0c0e0303030411100327140706020c150f070f05030d0204090c0e040c0e28120b070306 67
    0x3414500c0c807101000820000740c070340c0c2c0d41c007200c0740104203584d4800e8080100150002c00d2045200c9294000c102c01c9408101640751038800b43c3c3d00c4a14108014002030500001a200c0395110038004045004141084603015050b42c3c0c0d03008076070281c487c60400c3e9a0360801c1c080130600900c07900300310040c00d80080c41e04040d000000707184800020302d041050740e140c0c1102e90701c13103100c0c250030b014001018086949905080c501841c00401031640e0502030b0316403500c05401d440c4640551548969185010002c5900b148425010a0807024007500d0304000c0695506181d182002004000c02c030b01d40c0034100134080401000342501c1242c2200741550801e212030b010041c401f500712078400343d001d15600b8020886140290071030040e13200d81d0640034808100000c0d20921a0401c01c0702e52220b548582d03410a400c0c040000711a503070f100d0b1400044000307262071443c1c10005507045e012843c3c05d8010411003d91199060a000113811890f150720610942000b00051180d9240d085640380c107050001a007 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 189386133 1250 189384883 189384893
    0x7050d08030a09020d03211505090403271d01030c0501050a0c02031c18030305031902040f170d050901140d020723070603051312170708010f050d 64
    0x162104090100c0380000040b5100340501c2d80400300540e40074102403107070241400c0c0588401c074040803850310700d80c050480010008051245803840d88034003120b6801d140c200700520010802c0248200c0502282010460010404480740c0342c00502075040700100354100100344290009840054070042d40c104010300014490700b45e85070a5500a281a50311522215070840d0715400c24040a90140560528003480c0300e400075009110b82d40a0700e40113180d00001d11955101800da11004d0000b03074060012071720419154185c60102c8050100242c2842c0c2c403907108401d02c03180b680c03103103811152040b4482000402405448007201c081c1c10054145600303140040c007041807500c0c500c0103000000a5041d110860350741a00c6040741c0280c41058410301036140088501081500e503030742d0b440394010014016201b800b809105d0105000007800c452642d5448480800b40004103d0a0100c1000d17125080021a40d040340300701001d545807002540b5003481c1c20030608a680080703029007404201040800c5c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 189387383 1250 189386133 189386149
    0xa0902070503190210050712060b120703051305010f05060306101406030c0f0307180504060815130803090c01081608060d080906160c080303011208071a07050a0305010501020705 78
    0x15045200c0d41050a0760300004a0074620400e1021300398074609070500146a48c004480c0c07040345841942041000d40b1600000418082c10010a10350b0701c482000801c0c44d44243c0049411030b40e0031540c0c115011080c2e56003425103501e2403440b4005a075410402440e49020004241c001c10001500d200c0242064040301074480203a5040e400350700d0000204043c04d070700e002102c1400701c1840b00e0a46074141030f10020180d0b218003003503904024084101090900d030a00c1408200d5240c0c0e030042070354410049101c901400300922044140310041d00610202d40c11500643c81440d014019184442200001404620014049102d503008140e290f400081d040310700f0982007042111600e0100129140c076204c140302e01c046117900500301095005a025071020000c800768410440202c1940d200c84d00c45a032400244600341c0d01c1391001055101042c4400c2c010a400c0e07000b5417594440c2c150054002005510580d62080003603030001c0d091045503071502c40c02d4003505003407002d08100742c6040e00141d108 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 189388489 1106 189387383 189387397
    0x160302090c0c2d2a040b0d0c0605041d070f0c21020d02011b090308070303180b1617070f1b0305030415020c19080d05150a0902070503 59
    0x16240c000d041115038030400480800c54000108405411b42c0720190340c21400040308403021030010442c05001d0551610b42a9465181003102c01d20001c280d00c0c1d18020f40799181c00e0080c07140d446482c00700c0e40c0301e00b85440d42400314541480b606248010711004100d0050714001c0c005240c01081640035400d032a0000c00c52050201c540c4060158910300e00000140b1007541400041c1d5044040c04009000e4600082c0940d4808110051446003842c182d6a10800c40c0800030100d035006d961208030855403504002000351641482e05a4501030308079014010064101c80c442d910404010b580121015403480300285507007806002c036413041e901a1240700980030155104220b074003c40e0101403011008084028480142c5005003030444170850342d004003001076400350b08140c05694001d4500010030781e4011000340c20066419440e500489110740103010f13000216001106444d0700d = true := by decide +kernel

theorem cover : BRFrame.Cov 189208633 189388489 := by
  have h0 := BRFrame.cov_init 189208633
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189208633 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 189208633 ≤ n) (h2 : n < 189388489) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
