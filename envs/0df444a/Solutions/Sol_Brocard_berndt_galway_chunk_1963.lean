-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1963
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:18:49.920249+00:00
-- url     : https://prove2.me/submissions/c6f280d6-0d14-419a-87cd-684a1a74d6da

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 352877697 ≤ n < 353057553 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 352878947 1250 352877697 352877699
    0x20426010e030a0210051b0c01050702120c12090a050a03080703020f010c090b09031e0f0c030114010612020c07030803090c040e21040902030403020307050f150c162109 74
    0x2640d0b1a40107a005400060308220301c0201c0041c0541c0004e50410a804c000c0d9036090200c0c8a94030b259803048444c28003d944403000c1080064050100d0b200740c50720329002d90310f00304213586659100c2080201941110501060400c6030751103114640001d00805000059055264206240c00390040d4400300c005108400d40c00c20b00701418000c5010b10101e80e140e04c0105070070f0034000c2111750040a0140d4151180c0801000b4020030710948500b002e00480103003441c0070301c0c19040c1d410700b0400c041c028026030500200c0b82103407400205042c116a1a807910005511042d00204003a00c81c103804200180f04884000c01804040c00c011400313103604401b1601044022424001a5141c8110280c6903402140602104001001000903054071088460b4a05070b100c54450b01241c00039038040d4016400070843d8020040100402c07008516008001d111a500000c0a007100410080180d080c170240401d03d800d10380240345410142c150300000b21060100c0c185040c000c0e4020030000207001403221a0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 352880197 1250 352878947 352878971
    0x10501030507352d1005091b12030703020d030e010e0601030b07200d090e010b040b0703091d04060609020412080705120706020304030807090803090409030302042601 73
    0x5024414000d05000150210703980b50f070382007103607030403000741c44503000d42c03007452100108040c2c07046070800d10800864085148280464034104100c1c020700e100780e2821040c054440300000d80c03403108008040d1541142d030008000f181010550702d0840c81c442c03101041c00400c054020a100c44207858503079003002414034021500342682c43c44080e00400c4c1c1c000e0001803002c50445024903a0040690400101046100e0038203c1c4100040c44440d043d40c001626890b2466408039030304d0002c00c034410401019504002100702c0c54032031440b030700030b52440001c0e54004040c060005180140303d0409d402c003940740f035995035044803a001c80d002c403003c81c40c0400104007074201d071007641d042d03074000d0f03211624000a5664079203007503210741d105136000d110381c2100b0500f8032542c030000d000561050303c0150322400d181c900900f140d80c01a003007800b07022803403c05101035140001903509021040301e01058442c0780e4242640203118981000c6042d465550144d1219503004081081746908103008001d8561400 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 352881447 1250 352880197 352880219
    0x1205090f070303050d0c0e0f01080a150b040305150f0f060a09020d0209030f010203070207050418050712060b0919020d1514090c070f080a110d090e07210c120c02010501030507 77
    0xd480d40c8001015002252035110f201c820390f00c0f8042240c00a0200c0b100440800c00302332a03448140480300000303040c01048070a12400c00316409000c2104401d042600c501010048001c121500c900355441c0003030401d56807161500d000f440c0084e411503541c106002400040d501991813580684140526010000c3d4144212441a041640548681810901040040c1115076600884407a409100e040440c4091040000806500101a55280d030798a400d03001e45038200140c0e48117042e04820018202d00748c4044409005004500503aa021750180e148010009a10300c500d01c1c8071040304c0071401c018080300e245203142040b82d41800303c0d5154071038101e2070f1090801c0100741214030300044000461460240607081014100420035007940d031456860310000044030000103005500405c0180e44000c1540d41240d407500d0040100418400071b0324201a085020b41800f41e0b82e00740d40c10070300c0d110f103440002c800342a031000d0110311802c3c20002c3c0070f0036081c001920607002c2c803d000200e50580e0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 352882697 1250 352881447 352881467
    0x61d06070e010f03060504061e0b0906030f0903071a1b030c070201260a06170309010816090e0906040606080619091106030406060311040c1205090f070303050d0c 71
    0x1681c81c207200c909500300440c1c04940b0f403403402c418540c13510408241075031180540005040c010041011110071001011150b8040b0350203018540400c2008200380d8031004100d0350301031074005048082c1c0e150440d0052861040c44801340a0701a602c0039414402c405c0303550b00703000b040d40e010102085058011300d061580300c01c0e02c070903280b04030412803200154060241140b49082508845686a000360420200820b0444045500907500c02d801c0c4034180b0304584400c0101c81402c011404c0c21464400a08241c2000d804803d40f445050300091a1034800ca02807030160680c20340c52a07007402c140b000f440e41e0320000c1d202220154203000e0b01065609000411030301c80d4080688142c403840700e0551000040c10b14500948144651010b0020310f6124400294083c0e4800c01c000210946981058000f001522041070310407820704119400c00d0b6446007280d01c907040070880c0010300380c8504441030303d0310090080c0d800312800f0301c8500000340f540040c0a0098441084014040107030311403001c9a8580e24 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 352883947 1250 352882697 352882711
    0x2030c030c22110c010902040c0302040503060a050406020f0c1509061608041a070509031506130216020306090d1803020a06120f02130305010f09110603040305070f061d06 75
    0x4a2000140003401c0b03490301e034a08500d040009811181c40c03925007a01d91103000e41c0800740c0c0d1a102d0880441c20140b00d122031202007850214241801d00c0002925054054400c5c28050380f1a40410280107241e03044994030044d4007001c41e81d031010145840d45888a000880740812385d480002010f00a02144052141114a130704584a10380014240c0d1086005001902e070348221130580d9007250f05080341240541c0d035680b205138035071074204c00701032400414806040a003034800c0244800d5446181c207651b01010302c84c0300941c552980d03004102140f2081c0b24081c1d0306102d50740c2400003032000450401000e040c00e5545403040203c003007c96100d00413501c0003e4206000490400055204640c05903e0400c01c01003c00c4c1340d03814109000580e003003050692150103038040204108542445000d03042442c2c24401e101c54034071034540c011054441038403240102400030009013014801d00031174400e9a8448505d0f0b0300c550300f42c1486802842c01e03076404e9495040400c01768081060000f4241d01c41d0390 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 352885197 1250 352883947 352883959
    0x1a09130c0506071a010b091906021e010b06040b09130903080a0924021804060311040b0303040f0f06080702010506030604021c08041518060e0114190206010302030c030c 74
    0x1c540410300c451580840700644204440961041d400c60156458070b0080601044c400e48a02e110340c104102101502c07459802155802c008220700e82c2c02113101d030301c2002407804841501881001c1940500691210558804000280426500e898401500080e030054a540702024000c644c26404c4800042020300441c0710070f000070740045810b030400c6801c0e5109050f5406900104a0b400b001400280c02c0092210f40108c0d0742c2d01a0324000d4104a410b8030b0440c0e09001c41d914640314400c52001c1d1617900c50080c1d480708400c1103940c508104403001403804400d108280c1d69501030398242203050340120000100b141001c00c04961050040c680560700040150882d6103c5508101070503103560035503182e07514800220404199100040c2000745000000c6440700441d00c03100611020448283c0c404681e034a11003445883d6100294200c1d1000078200091100c1c0e030041c1501c0380e40907120304012400003406406007200d17400300e020b42c1221301c2901252010700c0c1100415480f4005040500e400c01 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 352886447 1250 352885197 352885199
    0xc0f03030108060a0203100e0a0504031b03091203031b03140a0203040803060f12011e06060203070b07050a020106050604090c0210020f0f090628080702060f0601080a0608011a09130c 80
    0x44d0750307004540000c40d91811340d031070380e030b468003030341000322088030741800a941d294104020303d500080710b06010081d00307101020308155540c01500c100c10301d001300500d00322848070780e40070140a5405000ea40140492a4524055424004020b07000400c4440501000c03440450001e800d180283e03406a03600c0740c500c506640c1c4e01c100b03001c021150303c40125408903206088090024003840f800300c3c004d1401c10341030504116200084191190340d4012421940100441404240007620158004806240495032056007680880c0075048035000b00758840c00002e00040c00840030341c44500b210782141c0a50303501541d401c01d580d08a005025018282c18401c101c01c144618450340100f041c028020503880c2402c0d80d2007046031031617030580b80c038020b12242c0c840b9503004103030040320855120003a44000c11142c5803143c0e00000010f00902624188089000807445400080d000640079244103c000c100402e001d01c03140714840c440c40c0200d0702a1000b1b80100c0c1c0109080c1000c2050a500026020055 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 352887697 1250 352886447 352886461
    0x102090a0513150b040e060f01050702010c0606080304090f0b090712020913050c03061309080412020d060c0503190908030f190c031a0607110909030705060c0c0f0303010806 76
    0x42844010004541c0c0ea075040b2600c82001c3c00361500c0c0030700b44024006850b41d04100d0407103003101c2c01420003449002c6003c00c142c2c0301c0e80d02404482e0229030a28040c1c001380c0c180e10306107001d4030158001101901001c035010a2030b4501e0780c050402d12000c0ca50a00140c41501e043c040600010783d6800005501c46aa803c0644000c0d00140426200a420b1a0390b4011013101c08085880503190100540c1c0000700b84090340ca480a0203100c5000040d0b01040281c12643d540f083c00d100d81e2281150203046541c201c01550f54001c00750b64160340101d003c2c010200c0001d4000c041e40d004444580350701180030164407147d40144907161145a02980007895500d0701991079005460042c45c01c05690a0a1003403455240745019815884286490219003004144100ad001110010140c2e00403101400008049000384040c0c00301e0b08000d480301416030704d42509503421849103c0000d0520311400d0b040c03141590404c0000d00c50520580140d0b081c519080c103466403240300030300c01c1070f00550080010908c9 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 352888947 1250 352887697 352887709
    0x512060406052a19080c2215020606091003020904080f0702130203040b060d150e2a10080c0a14070605040609020414010609031b050910080f0102090a05 67
    0x3001c1d5003c0032082000c43c0e00c0c00b1144900c8944080f80003004030704403480341e006010444010002d03040c0445180b41c019070710102800b6030000d070245140b1090144100405660b0311001515046c900c45c0c86004011101942d0b4080a60b2040d0240e0a15000101800c601a031500142ca40c02801c0315401d4450b519207804e00c2e0041003009030402c074100030b490010f07654520069800b9510040150300c0b45080e00b4003241d584402410280101074070b0300824009200901d01c28041c1700c000301d0019510200c60800303407510b65441030003c4078031114002d104480f00c2c0728a181c41c514404941c04000740060810494540700143e41c0e0090301c5c003090000c6040140140310020b0341c0803901d4801c9040111507164030040d01c00a41d0140c0c1c0b03180c0da0383d5100301903043c01e000b103d40301052090156141d501d4000001d24840f040c2c400070b440f038400d00302c0d04848100c20340d0240009080040c4544900c0c14800c1e040850a44184a119800d02c98a540e0034411401070007070310a5540d001300380d01311040c902824001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 352890197 1250 352888947 352888951
    0x6080414120901030f0e0d020a061a28170109020a15050307110a0b0c120a0b0102030a03091a040b0601022404080d0e010c02070501020d031e02070503070803040f0b01051206040605 79
    0x90300c540741d1440d695114401c000c000d00030800395000f403a02c2c49c3c2c01d05003001140c15080c0903914000c04062942d030342d034a4040306082e48403c5201c2c400b40312960300c0017502c2441501c5d08180307100040d41d414248142c5054000044080c0219440c034055a503a03c00b50070b869002140c0040414070a0000492950140d02da50034460b00c200e040d100d84d681c1e00d55492911100c1100c110b0341700e1101040710804070a80152a079071002c0c1440c020021100c202e80041e5032070040b00111010151a0401d0404004a503003508811220100a000180c1468a400d10002c0e0f000c0309d2460041c411140d021500d0b0f110300c100000d4503810650310101644443e1541d03a03007948100074503c1d00310380340d44044140d4402440303450380604c030b2940604803032410000021300780501d805c203801c209030a00c0c038100310800d044142c0126018201d140107030b650110b46402c5055015481000d010441e011007004103002003171100a03c010310842010710581e03214010030001d031018403801040d6903c140005400607071240c3c4419 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 352891447 1250 352890197 352890221
    0x4090c08041515030f060c0e06120c03072d0e012d1106130b012903060f06040312080f13150e01060b071704050132040608041412090103 60
    0x4500702c0c3c51317884445030003202440850324150384d0040d401c0800c0c0d2080d44d03221040c10850b001c520703082079000d1403407001c64050000ca047d81c40010224031b80c00c0c042c080c5d8400748114200c2200035564281c00b5214420902488000440e0b03d0511101c440d600c0f560324422142104003000c00e6500307071074090203240003e00e0052000c0c4100342d4140801090100403503071040d40c801c2d11031030140c2402d00c0c15005400060b844100410910000181079402100d01c040c0e21040040050341c4a80e00c01d4005041a4401e1210039004600043e0100902000243d0b580c410f0241d511510025242c081d4078290001d02251410f400b503000450100005600c95441481064031801c0400c3c8034000c02622801c59010740c0c480d05161000080010400090041c0094254290b0280e181000e140c01e0020b4152200d0340100c2440800c03052200d1b2082e00c1780d001200819810700c0343d05480300c0d12400c021b0082038090b1010340d483d1300709c00380729a280754001441030344807150b01c3c00030381c213101c0c0d4900150007410a00f0940 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 352892697 1250 352891447 352891481
    0x1020a0504121b03060c030605150a180b030117010501050a15030506010e0a06091d090c0111030c060c0c0f0d12020c010b031b120a030f050703020c0909010204090c080415 75
    0x2440c00101c104040c05035018460008001c03c06c80d10103001c8590300e0307011b24000c10201040440364020311007500c00e402898109629210070b41c01146569500d50b4000c131401803030100011030318052102010303803404241d074008c000e01d0f41c8550800007541664070410342c1d0300d461a004401410320a82146030080e4040c10702001180e05031380002c102c903040d6040040001c05244040003000226000c5405408000c0303440665801e0130508203071549c4500e90b285051024000744010080070420817103200080380c4058584e641030070000020a83d2000302001e0b040d100d030b0615500c00d00b0000c100201074a0b41a25202c0102d60301800d44406500a0b19071700039155a05c080309200b684041c01000b030003000c040c440f83d600000b42c00801c51248619084068103901c03091017080003d810050090103108541041900d4840301d01d0100d241044c100c0100e030304600340c2c40a00500032015005401070351001c80341803001a006c94011118281c045070080c00840380a001c0b51247d60207540b140c03100303403034040c11 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 352893947 1250 352892697 352892723
    0xa030b040c030b01120902030309040e0a1415010b210a060f0b03040c0e010e1f08010c1707110a170f0a0507020307051519021c03020d0e01020a050412 66
    0x24045410701079202000c030381c8520a600c4a507038070000210342c107015031030208072146c1c954003c0703a80c0b80100b81c1d0307841c050341c0e582c1d10070b58a00707904004561866038410303004840c1060340c0644a440b55044035061910502e0103001140340d003c2c0d0384c19588021642d403440c040003100f0000311020301c0b20141c5002c2009a41e548049064450700c44204054404051003030f0f42c0c0d051600c0c100d0b114160550003050003903000f90060141c60212845507401c0007500002c411114204808080c244030b15900209280d0320340b401400d401034021003006c4400c00b880a80c0c9c0d100e55185d420030369080ea6048400c5000d0f4005800c1080000d000e03048130010a01240b03000c3e8141ba041044540c00c0d0742c81403000c2030224102040e048110701e000c2112001800d1f055650003c10080542043c0300b034000c2118102480840c0000d40f44102c0c401c00141c034181034002064420b002135684c0180003517110350744081009040017070010400c030701402155942181c0303a945503d81803524500c120320020b60300d011039114452500c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 352895197 1250 352893947 352893949
    0x1b1209080f060f070c0302071e09020a08091c0c0212010e01020f191b02211e1b06030f0c0408070906170a0b0c13091802150705120a030b 60
    0xc1d40001d465540d0042c18030341040c2035000d1040c0070007452641080b42d003003107810000b40d001c01d40c001290726a00c12898440f001801e8211300e0324035a000034030001e02c0800c0007100a640315040a001d0380d8002d06541c0d8001c00e5880d0807102e001d409080310046000340d0034901c018240259510340a00c40000000b0f4004070000049080ea032003501c0003048844040b070144100c1400d11840003421a581c1003640d0580316016503040550b001036400780c4621142500b052021526810b8205a005e65405031090002c0410549a03011540307080443c041c424084145081d4410103983d0f490910010040340c00c50341d44140c09545c8030b1004241005e120b02c00c0c0000500c001c001c100e0701015104203000894840d04224040f2503042c900010700829920a040420202d1140c503205500070244030200c0740d640c1e01d900581c01640b0f803264022200a8605000c00055032902d030044c4000c544200d5060041034041c20b481102400b4400d0040c0664100c046900ca40302410001001c00300a2801c0224040f0f042c08 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 352896447 1250 352895197 352895203
    0xa0203010609090203060702010606120e031c1509050c090d08120c21190b030f030304110f1f030504032604031b11040e0304051207030309061b120908 66
    0x25210102d802e031078682e42011440c09202c1c0542c0008544000c00c0480e1070144001e10005403412031803019036440650418105007441190071500d90030041400b0300031161392400003400400d541c681c06c41c070307008030128002015000301d90041a8070003105040512410803c80c2d509035140f006c507840a42001030b01c0c2c00041e0b01c036482c0c3c4907114004040386c49498486030241c03003940c0b003244106270340310078010421040b9000f01c0b00c4035a402c4e42d00700000c502128001007031400014044003046407001108100400409820706040c00b2810754803081c040c50080240507008050b0042100e070380318455190400d0910984c4220313401030103403030150f60340a030b1880f4803450b03144000d6900742c038010f05c030041009258000c201031843d0800c00a583e001081141c585c1d0300486946030700035118039154101d0105840081042e41c02a1000518010000541d801041d03039503c01c4d484210007050325401d002500030b02a42c4400c002502e180c00c8512216240d81c0c42029408000d40c1d8101031100456010490311810 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 352897697 1250 352896447 352896449
    0x9060503010530060f0a230703060906090f06050604050907030504060b0616020a0f080307080d0b1203040303090602030421051c0512100f0e1317070201080703062301020a02030106 79
    0x20024282504000800005043c40144000c41b41d41c1000400d0b40e18022646215481c00c10341040c00500da210340340301318090b1000350701070514141400c40200d4a0b04041c0e00c05001403101e44010090980e0b00c8040c031820340940e100307280e0301c80041c00001700c03014001d03000541e20610550300021102c070610006030264212410a80040081c50011021410a03000c2e61002d45840031718641d82c9454084503a50303c1c8146040101549004501e2011f155440d03000720112001c01481020b6010407810b46903a01d07003103071005078001a80954001412030010003102c2c1901c08180e8a11110705120920064500030400d00700c4451051550712940c1000c040700f03102c10352105559041d81c1313440020311419100c1018050b081c840d000c260f420015240c422300400100d50a0500050b400e0381c07180f80104c902444258060a000c900c403200c01460300c103041c01000214400d89a01ca01600c0b01c1d841201141c2890080b0307108100d404441501d41c40c091820160a848144102c0c3e441740b84540c0032900752901 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 352898947 1250 352897697 352897789
    0x60f0e1306230a06031707020a03050a05030306100302030609042004050a0e010b0a15080714040b0a1b020d0311190503030109060b03071b021804031806090605030105 73
    0xb401d00c0c0a404400042180c009000802c00c2c0401800c64843d2501840300400d001d007000000a4124110f40f2034442903001140c000c0c3c20b0314155441350510503220342c41140d1151051039807181e407040070750007842500d00520028080021955895440921202c0782e90401030709200f028035003440035035940c012140b25800d4005e001c180007030f800c06c0f40ba0039220b05605092169600e100c6c280507503401c00d201d080180d0340e5458024440d840d10107096031320110002c000c003580c03400003d000c81c140b00c00e4001020f01070850364886007288403203600041c100210b414000d51044c1851000700103c0c0c495002c0d000100030b000e040d00c8103203803801d02c5101d01e520207607000c44d80c030b81003c001001602090f1007000000e002c0c000c4d460340388d13107408240181451140640078500d010340c0072288007507464003080d6811284034070314170000900382420094881d10840c1c0d04c01c080026898070201d41c003413044074108115001920f0341400d59091004200300380100150b041d0842c2c041c3c88441040340f1180d001d80c044042 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 352900197 1250 352898947 352898981
    0xd03140d091b03110d0204020906071103060a0e03071203021909150c0309030b090a061103100f0b0414061303080309300703030f020a0f080604060f0e1306 68
    0x156241000784a802e0002c0d104911014030b0003040499005002c00610030000c90b1540500c0425100190080c050140e031140c1080d4045103490802218094989802d101181154001d5441c04403810a56010200b1080190001e01400c00050805c5032098800c00c0941005801c18910104501d07000528088502c0020101002042400b01400051841c25098035108121625986000d0601602440014258103c010010f245c0250920921410b02d07801341042c0440360300c0c2050b8240c140c101380e99103035030b0805080000030f500b5a4210400200d444580c0c0c2d060410b2718003800340b00c1d4070020100c455009a02080796940120b0041c0d0110b0145116100e402c0d164103000800301d281c204604c2d4290140341919200c00d04102e1140040c9411824403810580e0b14102c3d480c00703d0151503010035044145001103903c0500a801505001c2040745a60380c21303425a9a80c0104420340c0c000744240340902c0c488030b4081c810a0140710303441d43c8c407281d410700b6044145100c1d6581c00880c0c00350244034842c58 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 352901447 1250 352900197 352900211
    0x1403071a0d0e070e040821040305030906060108040b150d0206030112050d030e0c1302070b0c090f041107030c0f080403122007060318140106030b070c110d03140d 71
    0x26241c819080c0c502c0e8000000e01001c0c2c1410450041c000002d031001d0030703180c4042061001c111005140781e0030002141000351060034603190140c0240c205503112aa603018040c005076040d4840c9030340c03d118a80000000b10103844026145019419140199800c5110b56609002588032440110300804032844901001c000c01e08000e400d110640350310004150500041c0d6000c0800080e200f1103503101210103012103c803450900000b4031a200000306280340600030402c6c5040c1c2500a408243e406840e035116101910702007104544191039240c0000f041440030300b0209110750141003100e4401e507105050703442140c071288800d810a600c1125544110818424032550080c010203180d01040b1052101c092404032051b254540f50086600705036030345400c09001500c2240d0b200080350000061640c0d61010201c8602a242d03030f00059514207552008240c41c984117582d00052540c000841a0b222042c0404211418191034029010041c15881ca2859080f045005203005e46010400040340 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 352902697 1250 352901447 352901467
    0xa0c2106140a050105180a0f061e09380a05030f01050106021c0f180f060203030a05010515030406051902031302010f2102070510020304080409180c1403071a 69
    0x80d03a8142c0245000e00b20f54104100d9182000c03040b190040c4c7c5003903001c20f100b9607112207030000703102c0b552080703068106100d490400c10300c200188005031540b010080c0151484205881c1d00d82c03615084c42c00d4112002c40354002d00300809490007892440040147c181c0558620000f840c10413603003240101039554000400546170108025461014890743c8912540c0140c0405449000142a080c041c800290b8600110381081d800c00b070003134071a480002d846552104402980d030b4004481003aa03484c0b8001c000319281c13900e402d80f41491500320070741c03500d5981c031a900c5102600c0c02415000380030041001c070346811002e50002d1413003070421134000901c0c8030640c000142182604580c40f02030081c540c1d45c03034103210755130500782d00d508100e050003680d5403c803803411a1034a42140300e80805284040140010003c0440040c81142c0300e0072030600800203181c500004103100488018002c0d24a4a0704004011104007280341340200202510940c1e0741d1104210b40c4d030700103284000e0805c0f00004919020f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 352903947 1250 352902697 352902701
    0x20613081005060d030f020c1f14070c061b02090a09051b09070c020d020603010e060a08031303061a03160513050907032319020109080a0c2106140a 65
    0x1d0680240309016a0a0200201d13180120040002d420003803602c0801d25400d00800c0016164507000c0c1c100c2030900d00342d544540e6040082505c0303100160995400c01c400e03c8401c4240d40e002c540140000d069a860980241c0b0b1120300000066a507101500d07160b0090395070182e02e248200c030018004520b5990a24000b0300302010b80e4a080f90030f03a0600f06c10569070b210102d040f03038081d802d0700703141c80b102c3d5060000a02c45011060025400040000089003d4404c0041c107406400181c4e1402e00968449901540340d000b6030110894598074910704001094040d000710110030940c0b045588010900804079060640100009004100b0700004104c00d09088012500c12644504108060b040c0b22440c0b1392200481d100251801c0115800e2865452075418403c400111802c2200c0000c01c00c440c1c03140c0d4100c840c1c0c1060740814a44030000920040118542c2c1c91140d005410076131755401d050710b41040550706031203c607030b2020064509000440a210380038000c2c5040001044905d081c0c6442c3e01 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 352905197 1250 352903947 352903963
    0x30c1b010c03081b070f0c06140307170a0e0a05150c0408060406050a0b0901030c050319052e0c0801140301060515030402010e040504081c0c050406050f0702061308 72
    0x10400c00c03011600c80100341c0c891030160300700410310150300c402140e0b06024503190041070b00c050400040341e100c1b4400c1080080404040784d0241c0c6401c4400d1070508041032040c002183c0311400f19000b83c034452281c0342e03d11a596030188480344000303103d11100030002d1500c003617404221001e51241106841c3c00f5407660b40258407815150b15946040d06100c0710344c5d103800001e007004010395110800b00328524216002600d20040180c00c0b592150303074908240a1002061043d039010303000d05a5401440c03060441e404a1454000006004840680c4401604096050071192031403450079808034200e4503502880034801000d50740d4203040e50500c1d0300d4920303035600b4041a520980c0b40210030880748e1560b2910b85d2110751a407402a440b541c0760b00061b9a01140790141d076a12074a440b080204200314500981005141c000e03040c0700e102440454002111005002400403070001e010400c44d051080e002081301540c03003014941041c0c010341c080751687d0030281003445244c001c020b0034801c41c01f00300401c0c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 352906447 1250 352905197 352905199
    0x30c1103071203080402030c0d0803042f010e220b010e100801061404050a0609090507090501090506091504090b10020c061803011b08100608040c060302031008030c1b 73
    0x221407030345840c0759101000c0d09150000c00340b20003480003e0a42d50180f00d08a012038002c7c000440b5685a441c0c82c0c10241c0c0b04840c21610200000d58040654101810028142c920b089141d000510680700541f0181c42000045078001821500701c0000390000d034115003410b1007940042042d80c43c540c009401c502c80d610f42140646a0b4100d10103040b680f100c18541110202e06140300051000e068600840c822034000ca6000340c02c02d800010001c0c0d2021b4480204c82200c3d50812040d11140b10480307102c03600344145400240210303000e005a19154000740450080140283d4681640c50342c0301803a50400c0d400034503c203948a20480c0c0a0034022591070004003d07102070000030103420000340c002d00402e40121201410f8810780f0f140340e1003d42c400003a10182c8211185a452400001840d084007203508100c2c0300107101c4002592809101d43c5402a51b004949050fa00e0801c03004600a40000703055450111421200082d2460280010074880e600c1a002d0000f075408090402c0034580c031400c4c5e10f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 352907697 1250 352906447 352906453
    0xb03100b0111030f0706021e0c1005010e04110f0d0609050c0307170303150103060306090c0306061403060c0a021507020c031c02030702041e1109092203080601090f03030c1103 77
    0x1440c0740000300401c58176502e6100364016110a40c03001500303094000c140c1d545024000029440c0000800007442c0c00801000c14000e005681e202da15100da20361064600400401e0540d00c00711042c905501d00818054000e03064030300001190310380d2420303160024000d84903900116440000390806000a9000e090321a0511914041950402d40e4900c0300030000600d803240074004410310b07840384d00404011a042101400748071018240700c0f885841900c012245140f0788070b00050304052001300100400c00080240049944029241180e03074480120f60085001d40c140c091400143c07500d00c50b0043c10154010088a0010024180707001d03040ca148031f180c4d505000c007000b403c40c1c1c000100e51201ea81170b00c1c04030b8503440c095039181403c0020811070142508082007880c1070340305c40000e040c0884084a412250ba103904020514800c8070b000e000d405a07104101c060301090040d03c8003600900d0600d00660701c03d95031408000b402e1043d800032400a500c1059040502c208000303201e440c1281103010b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 352908947 1250 352907697 352907707
    0x281208040203060a09030c0b040302031206010e0604030201080a0209030a151103011a09040f050a0c09050406060c0b10030c0b090111010507050a120f110705060c0913020d0b03100b011103 82
    0x83d543c4500030004011551078021490805204180400740994000020062402d00d881c001e512a000f40d007c0d0754a0209290010b490b030740c810b40c6004828400500b1082c601800d6800450701d469005210306203070354080001102e60b840c20400804803a01030f01d0071012403a04482c00f038040d960185081c011401003440103000003150341664121054507659510755400c2c40301c02140c064107000340401c80307082c50302c0200400d000030b030b4005400c00c03c0e195803006070858880040108403106406180000343c4107504080019440c2d810480d001040f041030803241c0c0c0e580340e03107090000403aa0421403c003807010884038100c0d6040094030241c580040000c4c045460a05002482805502c0c4100304024550304c0d8884480030326800106000e41548041c015400d2800341c0e072002c1e0380954802c440520030b01c0000350400d10003009803440c01500034044c1c0c10058003a4602ca0181d045081011140366540046800c6035608024104442c400c0782004540c01350003400240400a10744e0144402d030300100030f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 352910197 1250 352908947 352908949
    0x81e07050309010f030e060a06080d0203130e13080406030b041a0904060c091e0f06170109020702220b03010506040b0d0b091603030302070c050f0f122812080402 71
    0x20b540e041074080c03030411408050340500714044c08061142001a0140c2002e02c4040d40381e6800c040e0584805004584000c001e6080c201d039a48901001d03c42c2d40926502c05000b0654034480307491300089820400300d88071081d5142e44e901c2da4410741c0b201021994580c030449050900b40501204501201f035894210340c41080420f03207001000b0402030440ba0344803810051a400785080102904401603903002d9120703904854400780000340510a034001000d840050100d104010003103a400321007056a2559291054040294003d66822070340040400403201040074011040401c3c83c21603d0003148400e010010305007100c80207020b4038001ca0400e40c0c5140c05845041c0d50121050f84203025961030364a14103a20704003da00c402c0c4008100e0000400014160715402820311240510b02c480c1a07641e03907408001c2c02010012005d034001c402404031050900e01449500800c2000d20180c5100d804400c50a80c01064500d9400400c40000d51201c41031043e5421203d10740e03009410505020300b0990 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 352911447 1250 352910197 352910203
    0x11040b0a03050a0608030d02030105130c0c030e0d0b091b09010521030c010c020303090c0a050f060310090219110d090e0c0408030d0e010506090609070509030f0a081e0705 75
    0x2003a00285a01c0c0c0c0042202c10180390301c800f00a2030404240c035242d9030510301d290f010b0750003885102c3c0316002c00c1640340c1c42d040043c03080402680854a900003420140d54084e1125a4458002944040035104c6000850104052140701d00000b4010700160340d00ca00540b0000d509410680b0701668a850040c07110362212503400951290820f0075080c0d00b10100103042c5903200e1210b0918055003008480a180780c2c0020265000b40c00d603c09580d0481c00c0c0c5424843c02080f68443c0300e600c07020b030580800c0da5003408001140c100c9144840701c0781c0982c50342d200780140d038041415070001c5200b07010101c0310180d010b00c6034400700c1041d0003d000404000385000309000d01c6c601541c19480c2c0d0580128800031421000c44000701314540c20b40b525031603400c0200c0e0080218940419031942440005030841c03914003038561260b100102205025291168111840c0e00059805a05132140d11010310608800700401403030030b8420071310f0540d14000484200381030700c1c0c944540061001c0510400b00000c2001c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 352912697 1250 352911447 352911457
    0xf02030d0e01110d0519090804030206030612010e060907170606041509050403090f0801051b0c070b070f050705030a1a06010e12070501020c03160509070507050d08010911040b 77
    0x50001c2551071000d40701500401c00100880c41c81d01c00041c0c0142082c00c0c90b0041ca1203248140e65088504116078008003e4500c00000140030400800041c001840d082d400303503030001e1002d4004040c5c4440d001c252401c41d459a1000f07034641e800301c2c0070890105001c114a00142c035a0f0b4170f1507000780469031496036540310040c000d184074548030050003400039442c200c204000c00030a001032016082038100a40340c00080e000c1d01c641c4408407580814544d5050040380d001c1e44940d03603c1e84002e11a0900080307640c101c00c001c01c00f5400f4090000403c0c03001c49000d42001070103030b80155000d20542c41c0881c0342c42c240350b102078020b0f040750302250007080c59009003880c60007a00f6207484030317035072441300480d0b00e401c2c141d551640c4030324060f0382c01146070800100041625800e8007264a82e0480104160307072440040340b101546107030300038144100d050103c0c500da0015864103096080901d1381e55800d003441d11055248000450407001000441c12030f01031030003060020458149400d003495a0455a4410 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 352913947 1250 352912697 352912717
    0xd0c0203071208071e05070e0c0711060906040305100c0f0f03110d0e0f060105090105060414120d1107051005040b130f080304090b060301140904050307060207030f0f0f0203 76
    0x201c034007000144a0a00112030b00164401880180520680802901d110005e50241c4991003100c2000c140032051880c0b01e070161344840b00a5040c040c150f910390003d6541d5481a42d0880018000c0010380d46900780030f4030140d4468000b803c600350306003140d0000c4804403c409020802044001e08466030403d03081200c901c22807801003044400c554600701d1610965460140c0207241caa81d0107107145c00804c60840c0100404103580302660b95400304002c55100303000d0030754046001c020400000c90080c008034003030000078190f017000401e0413807168100082007202d0070115125200038082006c0512083c4040c01c011546031040b02c10740400140203014038010b002c0840c0c800035800c1c000900d08510040142a0666a8000103480f410055142e030428412040018145102e4001c0d07403914800340c9060380d014881da80500c00c951400c00501403c040d10959490008001ea400410128002041c6036802038880005440c101c400040596800c010084d0402c280320008032201c036404000c49074007000c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 352915197 1250 352913947 352913969
    0x7140318010503130f030806011e08061201091e15020a020309061602150406020c0a052b1b0509130c060311090307030c14060f03070c0804050d0b0103050d0c020307 72
    0x60350000c803144c0320310150005411000340a00b10b104040d0703c4000c1e544110b0b800e0b62440e40d2150b054008a10708501500c0c01808038241e4400101a0b042050380c0341c100c010908004504507100380c440a82c41e4010b030627581400070401c0c042005005070041780c04048014000d04625007046c0d400000c0d03c0e8094404000d1003100c0025400000c40b078203403213100800741c000700030100203250002514400d81c098441c00000d80901c00680c4418605510310310704032000a0301400313060b04c5a041c41c0ba86491000c266401200076801d000020401e0201821040d015842c22081558144010020315a1004004d0b032180c910040100000804980070701003201c8460501052003000008224028010b6510190309485100760000a00160081ca402107948001b0321240a103203201c02e000d070328400c0c02040501d80703008102007011a4410010500c0380d6014000c0c880c140780c0c90300c0000d03d540315080f00640b0f8030701e0480014400d00105120f0081f11240320309000003074128903804a901c400c451700c50620190 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 352916447 1250 352915197 352915201
    0xa14030a020c064905060f0109121511130e10261e0307020f060426030d0603050c0102010c0305011208070219080a14030a120507091a07140318010503 66
    0x4410903403528007103620424648030503400c8001200405d4204e070120b1045800340d050304425405811044250340185084448040ca1038807846207110b44807009100c0c0555a82a00086140c641c0107001400740318058031550500c0c00d401c2c0300803400c001e0990a0744840386141084500c01d00d00c0310031460200540d10700c41c0000b500c0c82c0705080c000c0400840c04040e003245080c07056003c000c402440c002d4400c4450300a100350400500100f802071340a800c0c2014090070140994070200712100d4019044403048920b003105d609000d00648100364000c8070254031001122180b50380a0190090546a9241c10060b40d80340118050302082c4920780a070000b400003c400096495403115521042010401040815603030075582d580c0d03010410007650644441e0320041a07510001c001c035541100a6611501401030390054400100805000b00061058180000502c110103410b40e00c20045949151904d55146003020990349484a82070752407500300704903400608004040710721071000c080c68280c4d125 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 352917697 1250 352916447 352916527
    0x6130911030717011b08060d05010603120804060e01090c051314040c060809030903060106031d100204090b061201060c1e0b041406070906110a14030a020c06 69
    0xa190525281d4050081d6507001c19190300b0b64201d01c000035103440007000100d4440f81000b03a9039400b090400002550300300415400e10705159252a400e0090000203102680c994940b00a0350301454141c0111b08141c01b08028082c00d0300c40c4412605048000b800f0000440e0785241901ca0207006581c8510f88000c0c002045e02d800b5404040c900f140e02e0848030381401d03d0304140000d022103118040004400800040c0d080c03802005452401902a00a08169080410030340180234003180c840f070b10f1104ca0911140fa00b400300104040101c1c540e00c0160b40b2400c100240f0207030f400e08001035026010400c00020b45416a1010904440d200d140051401802c1d14000205801e0711420550020709140c078542801780d1254240c0c0550b110300c075082182c00c1c5d41459141c480100310345410209180e02e00403c486030040400003000788030f1200355184100241d40e1400300007036042c4203506551010940d10038582d0100150203a06c6001c071580e504125050b100401d09068145d1204888081d081580c260 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 352918947 1250 352917697 352917713
    0x90403170c0c16080f0307150504060b04020a0e09060f010c06020f07020a090b04150302030307110102030c07061d030f06130303060b07110906061303200a0b0706050f061309 76
    0x80d000b00c0c4015505408000c0c0034440d05031843c2d000300c0318240a24240382c0721900303000040380c090541c401100b64002c00c1c80010710b0024000140f043e68000c0e01d500000c40c4943d524801020400c92603140e0f03007940d4500900303008001c00010201c5010300c900c1c00130788103e680c12080494919038820740140c0e5070703540030000800e64002d90700e0003074001e100380340081103840c11500003001c040f6040c0c504000c11103440070141610701c05484013035010b820402c80d07080862a04000d0030008001801100d14000c0d41c14143c3d4680081c80e0722242c002184a41c040d188400e14000380740201004800a1000800700741001e03413156000fa06082c0c1c4610f194555604041c002d03080440280a135210880d1114a03c0c200060a60040407000344101c07044000105640340c0380044d0741038000c008550141090030340c0e5404035207106260324007019a034103900c02159941c2e84032201c005007821090003600c0318540c2c542001500d030041c00c00783c28800c02300200701d5151a0491514803d0018110110b140034550600c00c036 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 352920197 1250 352918947 352918957
    0x70203251b06082a03060f090c281e09031209080c010f0f0c2a0812032a0c0d020f070e01051503090f1504020f090403170c 54
    0x884190090345030a481d075103120340c5004603619070b1a401856071300d010b80c035001d0490301000300700524902194071609102460186500c090302603c4485200d40703501c00a01e07440c508403440c03851840f0005000c400796002500481051724410344c0d0081c10740000a0280c0640e80702e030343c481078038000001c982d21039900c264001c40046802140c1c403101c0b00052080180b00c102030b8001c06000780308580c1e880760107500c00c080020201c4002d548078209050380010454039115440700540d945554030308012038242020940415104018121200c00392405103620304001c111860010192002c0c010840510201d0301048400703400c608070b065000603c040d11520500500040b502c0510444009030007140e00000c400e44008a140c084a5040ea076030110055107000902419030807000c00750f8120305100103100a035801c4041801510894001020020301d4840d003000c80003100104402803100307505182e9041c0303540c4207045e07662407040c1c603250310060058418520104032008901c03000036000491300701562 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 352921447 1250 352920197 352920203
    0x70914010b0c03040e0403170105100804060b03070b1308060606030f04021c0b040609031202210702010b10050d0506090106020a02010c0503090d2418140c0a060c150507020325 77
    0x41039041034100241480882500c08c2c100040150011440c4d18203086d00d00028a496070300d46845d0382d202e985541c041e0a1580b109038140c86a44000318002042d48050075803144140b0304601c02d5481c11110740e01e081400f070540f40c02035004005009400c226210210b0b4400d8054507550b02246a48000c10b1540d084090f010302a030002d5814070007080241d4000003441c0b4026910344d4100c6403900c880e4012441601444403c071450030320038503000055240c50326849103050000080040240001c00c014030640f1010300001040024419540800f5204054000c00b042d940640e940d0b04009010b51f40703400404020381484080742c41101001810000c403116040094188611007805140510a91100d4803240c401180d0700c5085958501c500c1c0320702c42c420408084060b075113031110344955540c0c0d6850541c07180319001b0154100400e4a480032000d004003503d581d203c41c00002810709c40040c600e01550a420300c2e0924060000c1541c0c000291601c1c04242d40c90b0880251040c0281d590b0391b5600c150007 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 352922697 1250 352921447 352921469
    0x1801091703090109092f040305010219090609060f1b05030a020f15091c030f11090f01110d1b02040e03070308071701090905030c0a080a02070914010b0c0304 69
    0x4050080000c00941580341c2c003030700d41d80c0c020783d00ea005940980f80c0741440d091152010108090202c83e0080761000d0340c070071004000d8a0952240c581c1070a907840a81c0040001500100b00c05040340c1c4a1001c80c01490f861401805041c01d0141c018500c00d6142062020041c1090708002d072202c1d048015031005520000300d99540040c0e0798043d480b080380c003102e00c91078000c80c0c103a2803c2d4081c001070b075407181c1c200304003070701c1c0d81084004114208900cc1e0b01c42c3e070405548240419071565039100700c0e0a0034402400c0c464441168104201c010a003005022741001850b91001c14108400201104056014207100d0315013500030310319071400001907038040c0d03019003000c2d41c004409401000a04116010b41c2e41e40c0d00c540c0c0d801c10150782c080c0c00c0720003000d400c40c03a10b401040342e0541c40e8001740c112807003001605d182180400d18a0b1805030a820162503c07240002d43c1c41510350108001b000408000c1828070801311a0307242d9a0040c0014843c0240541c4001113480e42e0000502c00c5601400410070b803 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 352923947 1250 352922697 352922729
    0x30601020601120c03240c08011505071211030c0a030c0b0603010912050903010b06132105060703020a12050411120c01080c0702010306080a0308150f0603041104110703020f1002030606180109 84
    0x100a02188c000c0c403406d01c01071801c200e00060380d84030300d00b150652030700049800130700c424480c1e0441d040421020f90702c07618001072040e000d8100081c0903c6034054020760356890307071060714100ba403203420014115900c26850581400000750304090411154809030070400c3d2a80801c402017030143c48103040880c5d00010001c1e0102d4240301f2848a00140c44856016415041508030110000121f1344c00c09000b907408080000c000d5072194000f00040d980d240340095080380301b903190400340c50054400301c1d040d04204001d1a00c038100704141640441603280244101c0d40410006060204007a00e0802c55070303030004803002035900030303040400240151030403903c4041040c01c004109403025628281801682c001d1448503250a03040300d81144c80083c00140b840d1a5681c600b410003101c4a40315401c540c403034500320880c240000c060f0684038041c0d0050070b400c0b8140c072083c5041850300c501c0e110b40c1e60301c14018002d25845410a45500070402e1900303c2180e00301400589200d02b190380401d2502d400c1c440c0d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 352925197 1250 352923947 352923971
    0x601270c110312010f061b0609020f0a1203020d03060f33080403110c090a020c01060315021209060408040512070b0409020702010f080103020139050102030601020601120c0324 77
    0xf40d07941241c101615941000761584401c4544003601030034070300d00104059400001c15850761004041600c0140304443c0c2d140f401c00030078152085d550006c1a01a0640100418135405020300350080c1101c1c0f4040005a00b08071404180b049640640503591100003049040842220312408440301302004401101448000c0148040000c440440c00100c1c11103020668410024269101d0100104004155a12001c0d445e000750082d9003410070f29074031050300102041d0195440c0c03101400380440981d540c03418a10f14650004040d01c40c08443d0f1001c8100000302e030b030110036142540c01c12190a0380444c7d0700e01c0d110389400c04640202e13110110002d80083c4000d403a0740200329162007a210746034044200401a68180401d01c07000c2e0119104051271400020469000d8944403848100c2c003800340c8074034105c100a0f07246940100d0315603600209001e4cc66804010311030050601380354902c6101e14555503103e000360a480000c0124601d1003c0c485980140c0c0040f804d404440007040100c011240 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 352926447 1250 352925197 352925227
    0xc030723030301080303130f0b0408090f0a0b030a020a050d110d0606080603060105190b04122d0305030a140412030f0204050102030405060a09030c0806090601270c1103 74
    0x80854191000384958500d40104040292812900404055421552400c0b99901c0003440c0780f008680c4551480300310000920494412800707140503c0034540c0783d88241060008000c81c000e1254400c0728817174420406c408001c01141e6100f0180c050260712045005015a020b00607008800302e00b41c00d0204880b048d04680c1b0103040d1003002007105010302c1da43c13880e0a4598050a0300c0b101d07003540062005201034281104260031030441ea08103c030340b0540c0c07030491800c035802c540c0041503164007030307040302080c44005d82800ca0751194122844c0145401e1001b032081c040140d800c018107000d404800241c0929465100c1803601d0036514102d0714925007440c11081407040310301c40001103440d00e0303030980009403c1e20940f01928010b030019450b03e414001003104503003061070708404000c00ea80d0044002000300845400804030036004040908040d41000d0404005810001d07056010607840c081c0d015030f01c0442441030114440c0000d016144440c2154010300c0c035445040103100028100304c081c6650 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 352927697 1250 352926447 352926473
    0x1060807030b04092102030d0e0106080c060307050a0804020609100804151a041e110403051c0804110d140309190302030a0b15030106141e09010603020703050c0307 72
    0x65541000aa4002c00c1040304070f5007808009044456071500c141c02c4954850000c1241e028540110f17410034000316040303003d07206540b015800316511440c1c100b120580c10840d0017168002207405504520704108000e109000394105601040809000f0400350748030701c0d0407100400805003120801451201026240580546084504201c1d901c012036502150b8865841d5455102c00c401e0400f200c86001c000140c17004121301c05266036400e0070080e811440c1c1c0b04540d1103800800b82c058555107141855402c1900c0c6602500342400e8244500c104a54031414aa520a40c4041040400107000000c26483d51002e0341c000c2c4500600389030f03552820f8002015010401013121514183c4007100614105100140f000a4255000c20032600000301d038528103035480314032107606e11080c07800070f40040d00b035500700e80c0305440c41c0401403111462801c1020b4070308049800310340802400c506501c08642c0c00b540500c22a030030194045925802c041c07007203084078910080380e000c887e110303411800c00040301400c2c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 352928947 1250 352927697 352927711
    0x120c0807061b12060608070c051509070f08010e070303030c020c10050d0c110a030c031e0c03110f12030903040902070821090a030c11060705010b0a05030c030c2106010608 75
    0x22440c40c3e01c0c018000f5001ea042901d010350764810443e2902e040948045a880400711202e015500020034180406641c641c401c0c5680d00080014520740704d8008240b100c40c0e084500680d062607924032036154000b4403103048952510700000c1c0035160140032424000302c41c071025402414014036940d440e40c410060280800080010000000c0c105c0b030550f1100200c013090b104603003040917000082405010b060050714041d00b84bd11400300004c0301d841210610000400c04030700d151201c09c2c14540d0286201554401d01801050302a020480759559400704001c3c44169140000000d03017540400d0094600070078940c0420740d01d070342c404d25205110760071820340483c54072071080d85503128046014285000b82c404c2c8014117000a15610100e03a840706028041da0700d030034000b03203211b503a0301d54100810b0200e00401c000100f13000c6075030421005034a5a401184a6400710002d2441650003240400082c3d101b00d8410081070106160f410106910040c080303000d0203880000180190040c01161080368 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 352930197 1250 352928947 352928957
    0x27030d050103110d02090c07050c03070303020d200a0213110d02210118020901051b0604121e050d1b112107020f0f0306090d08060607120c0807061b 65
    0x1c07034202403140c036813040040a540720358504046411064920010202203002e00c041d2100344e100b180c0402e140030815402100140e220508508485501020340c07036a817001464103911140c030124800ea511402c85001a210308a0752216840d030761600e038840803849203840c100310344844411031144004d40000000c0520004030520401c10040031751021810384103034603100d40c0c0005015041d00000c0d003081c00b50700d050040c10000f00c07018010740390411140d00380c070a0040560746000e10f07149040391180403044040c009106140d450030003100000340c400900ca03282c020f0301d0b0821509101c002d0042500c00d0f007000825508202c0c10142d11003008004005004200d4441504e03c021070343d58180800c2c0390721700044043c840c50005182402e109050b08100404040c0c0c00300e03194000a0804600f90758074201907201307003121040150400d2040f03910540449240b0b08141440e210080c954071202824410095070410217401c02c0040000e485103660000700c10407005040d800e44000542d00c1d4024200810 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 352931447 1250 352930197 352930223
    0x9010608190308090732030a0c17010c1202071106070c0e0106080c12131403190509060306040905190b0a05180c13060b030c040509090f0627030d050103 67
    0x940001e4034400321410402100c91b07080103426110002410841c01c078000c158404407848465504100c2c81410714041c480350700c0ca1034900600d01200e2494207005180690401c40d02d16451500241c115410915008005d0780c0c4400707a00d4080d640450f00c051440d80040045071490500142412400c01c0d14102000041c00e6600e4510a468560301100c030f0283d40c000410050340c0c0d0288940d5502d80000b07019518051800d41551240d240c07994070600044541d00c017103285822200196008001c0034040d00708a446c0c02001c0020801a1000030201d6010729240c510280400408100040702480300f81d040310059107140c42d00001100040e81c07003490050510000c0f84000c1044507240030362200030401407420755a5002844286007100e00210300340d680d05c06d00000d0820b0014020340c8070b500a0002584c0e20f40c00c1c1010441c210001400031a41c0b44c0c41002070100c112000918650040c0804850701c040060310481c510092000500b219450b01022030344021039072440d0041da059900c01c1c42210130312 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 352932697 1250 352931447 352931461
    0x1030f0c0501110607050d060806070c03030c0306141c02030303100501021e1c0201020d150305282a0603050610031e020d06050301092604060e01050309010608190308 73
    0x1c0070b22810b20b0000c9404c01c402140400340100010466401034450200b01103a4a074041070901c80704580310408252443e03988010981d15118048488605e403c04114007410300e440403075010705102e40da5004803d0b03040d21054400c40598001860ba80c01000c6a66900d000392581600c002203200f154054400c1c034101842c14038440c03000700c081e11220002405002018840340e20b02c2c0001e41041006d6541c02c101814400c0e25038041c2d81048841001072803401d43c03640ca451481d050403840540d01f00d100340d014080b90903200c065240d4003160002201013200d441072441e182108a00a5010701c0c617103000c0d40000344580c051300214071922085481c00302c8221050f906900382ca0030740c2d0040b50074240080420303902c011075038040c01c4c6550304014001440d54071603010a00b1601104026600340384d5420007201034a0302010744071021404010114105858000058081304158605a042c454040001000d00000b540072030b00519106003110b40f402c0c917148503405074000310101074000444240000c0c0780 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 352933947 1250 352932697 352932707
    0xf040e0c0c0c011704020f0117073204030b0c120406050108061b0a0c0c08060a0e07140f04090305071704170c090105061e0f0a030e0c010e130207060501030f0c0501 72
    0x7004e0011102060240e42d16400c00074007811380204241400b40744c000038110b0081d80c50140b0302c9044030351222080e0740c0b00c488141001c1c0d696581c142d500d140030040c8100241c2c030650b040d0f80840c2d40c001022109078884061800403030142c00480d82c80f00c02d02e081080140400c0707800590481c3d00324415100651100803440414004400b1002c0050008005480102d40700b400c0c5921080c2c0580c120030080e68517120280c1c02c1c0325095a203255482c1e21514071031206041400040020001c20540590881c115004207032200e01d5a80120f20032961022403c0c1403500842c1103c0809502503410020b01e1b5242040c071a081d04907002d00039403828400d800754a00340d4002088410301d0002400e002080c1c0ca0302041110740d03808100c04003c106081a2210382c01e248807000340141101d9091125203c011114005044410300c2d000440180d0101c1c19030001030342c002507040d51400d02039809a0190000c9414030000e0720903100002d018602d040000014403d20341004002903200300700508507655201c2c0111a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 352935197 1250 352933947 352933967
    0xb03010b011707140c0304091b020a150905030c0718061a070201030221061314130326060f040e03040e040c0f030b09010f1a060f040e0c0c0c01 63
    0x1002c9500d82c403040d080640d5407181580c0c4440e96181400349407680d1207112000340c12200c986000da620210301400f4404a50044281040c480010980e00c11a031850096490040d024003404001c61500506040010790f00140c1c21182c0003030450340d0f1080051501596480e0601c11900c103d40c1032420104022154001e01040f5041c0c0244c4580710700340f424540c00c0581c4040000ca050503401c00400a41d81c0700c05001e0081c1e81d44041c40200b2500d0b1241c01d010080d030341c2c2010224418074242c00864100d00e18820140c2020150350000c6841c0003034a03003680c48004060711403ca4240080020b02040392480016100b0038083d80c1144031485848140002d90364840c01904642d00140014030415442035500b40d481405030b8108079145507190f10020074020079400643d200c0c2601010005c0d004030900803d0000d5a00b50f40402c81044540900a42c120300c596929104440000c2e80e60345541d40d039000e6402514940039548040c0c107004000c000700b035115003410348860060f90303240d50266009504840f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 352936447 1250 352935197 352935199
    0x50a0c025b060f1208030606040f0b03150102060705181809010606030b0a0803070b0a1103070c020306070914010e01020f030a02070302180603060103300315050f0a03030f09080109060f0b03010b 85
    0x48551205c0d9540c060f00c0d0001010f2170780284043c0000100304a102d0359103001800e1141400350350b414410040c0440d1910510107505550204061004155020341292020014150440302001c42c4100084103403001d8011a120164268240007525806500000444040b80c808004580784501408070040e0a13100384425600309020080110743c06841e000c0c0d0001100303400044e4440592481410b50b0400e80360000061100112074045080401107160821f410742407030001c1c03500d0070b03c00004401c1c40600c0d40b410844903082c8643d00f40d00800140c43c2a80c40003054036222184681c4c02961034140340300a91090451008483c5020796810380d450140c00058081c007000c3e1709588600d0160b034140780300100c2c6440d0b030107145020081c40540c60102c030041c4c0da8000c500d0444407681620403030110b80111344074110030002c155495890010650484c2d6060820021025100000b51003020b52a03109144079400c02e1280001c00810394000442070000d04010800da07210103013458203c45c900c15081d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 352937697 1250 352936447 352936469
    0xc090302150f0c0106030c0f12020a150507020405040b0615030115051303080d060e180a02090a0e0d1701061b06110c070306050a0c025b060f 62
    0x14030305400084001e14407004410410741c07070081540d0b00d05017140e40540c029100c8041c01b010070300c85c07003130303d190b04400504007050b284141070a2900081d00d160b5180c031840300e821001c8415084060700600c2a0344000340c00400800940c0b600d814003c410445c03c4405500c242a09a00c500c3c104036141c059078142c071002c104120f03501500d03103000d459982c013080c03100084079507491002000a0511005085050780c00001081c2507281030703480c8940c014082c02c9104040c001c1e01c0000ca60710400100c1100c900d03011103110040d92103c10303005000b021003071031900d0180202174800c3c2c42a50007001c2d400c2c00c511910800c010176a0f90300030486422000c0301c0c1c0000744052260744503010690541110400b44216003015242c895491a403614200240d4411a900c40c0c5130000c000c2241d003144903038002190726002403e4200034051114498807201040f49114803030ac0c11071b4480c401ea02140c1e2034200300004020800100f483c0346180c04403400303649000e4446007800c1010840309001e900b200100c90b02d441d04 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 352938947 1250 352937697 352937719
    0x2d17061501111e2b0306090b0310111b0607080606190509151801030f090305031b070c090911030a120c14160501021b0a03061a04090b0603010c090302 66
    0x180d00c80710780c0c0d480e1078003c0c0d0301c203201c07000343c10710850f583c50189a441440c81c0d03010414a1003014080d9012548150361103480e000c0040d401e600c0c04105001494a0740e0400181a01081c000c0c01d2140030700841ca03580c00000c000341e20300500000512038021101d41c0c86400841d66404c04100c10ad100d6403050b0341009144020316030080b0701800103040d100394000c06026103488210800d200b00c1c3c10030380401c46182d00b04c17000c1000740d507054400c502c20f102c0204002e1103480d15070f48002d001d42c40003038640c0203200c54807e401100f10085005845c03600d135100480509042e540c0316628050010301200361036400401b040c10040385800105680340303641c016403805010101510542c4e01035620b884c00d8030101035000c0790b015214014040f9400030170040700c0f485040c90400d00028540306005404100300d140c1e0912094135507030350916110441e54400f0012030004419110b160b11040004a0160441d04204d010010080b13101c04a610502d420340c001c00005d07052103000c640505581c40302030b40041071201 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 352940197 1250 352938947 352938973
    0x10f0e0c0913020d050403021c0504030803060f0303040305030f03040c080102070302070b0f0c0718110310120f060f060e0702030414040f060e070302041404062d1706150111 76
    0x10b40400540c1d01100010b09000c0b4003100c24064070011034089005030840a455100d42905541041030703445680352060901d4210340d2821514803014100a101b1080d046032001d05903410003c44025640c0501560345904290300313511081c0d04281c0e011640000154004103400d8414400c6d983d83c1c0d901a4018016245070100c4072405074011002c0c0c1c80303024001c211034203002c80d08000c148020014154950102c1c6694400c00b03084a1000c038201e40c103000d04000340304440e10030711000d0007566011104003204007010300d0014100d980e4814000c04c03d5007415036450010071a9030003c412112030f00c9181880d40d48039002207890344614015069032408003244580c050610343e02c40358000303030400d00005100e600c1d51080d016501d0221142ca0002c0d40004047c4120050b40001c1c080c1c0385420340e01480454104100003a441c0d03010108130b42c540046820400e90704d403040000034010000800a00c23142c480c0c00ea41c0a440345c804660f82c02104141c4081b01c00b00d0751089032018004107603c400f41100f400881 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 352941447 1250 352940197 352940209
    0xa0c05100302270a091e0c020106060c0809210f0f0d020307061109060403210c0206030103020405070e06030c1b0a080319060302221404052e1103010f0e0c09 69
    0x14058607045040f01300042041c8205108101c80d0301200d006055180c05004400c4095540b803442e1402164105070f420840e041d0402c04504030701c1d9100c20700a4880350382e0400302e8100c600c0025100502710318640107800c42c1402241d444607243c981030503555500e0034560401c0e0350b040883c2d0f40000580c810840040414211b6000201c0d490090b4401482c0c446104001070441e085031704140d8020005107400c0e10740034140d0325808042540c508040480d000c20740c0000340c0078001440042e002d0b03525000000e800611418170140c0742000204403640328102209071a60580000400c0f07140000149000c4206c1840003a05150140c3e00c008101c4c95a50703900302d44041000054001d07051980c0b10b040100050b2344d09041c030703190b0075180d80c151000100310480240544940080c1d034a030030954002440041200070480b401000184c851300950030129041c0f81e0740300311420848200d4203140155001112420200450403650000d002d9400301e13448032a140070020f802d6070030000081c030070062600f40b82000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 352942697 1250 352941447 352941517
    0x4120201090513140109050402090c09040e07240e0a09150e01121106072001110304030b1806070e040c0e040e0d1101090302030301050405180a0c05100302 68
    0x10301d00032200c00d90b198003241c0c007400505030302c01c2c525031210000502103010b06910360041c60002030030710003818075401250302100301a000ca01c90b00000030b8485015107850b00318840720b42011080301c5001e66580d500d46140c200012480c09401020013042200034407038449134074054070081600c01c02c54a444040002484916111040b0580d804000a4643c4460080750300820000741caa0100d4841032401c640c2e0104c001821038858882801010049a0048010b0200f609190140b4001c0c40c041e0005071010300a5a89110a910001034080100030101510b60b0160b165042c049940c47c4c038680d0000d4482c101241c076180040d100390034402031032400d07401031000b5800a0600c56040c554080100d420344400349001e5140d9442040c001501603400b0300740702c9145000320003c1188d04126030340252244018802ca520541c1c0b16804900c1101c0780b80f010008006400040301c170f80d1b4444d8078000703131110b213140f049510074055030002040d040d01074000c940010311100c0c410000700d0105d406100700359403a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 352943947 1250 352942697 352942699
    0xa020a08060d0c030515100b0414130e0f1e070501020604062f07030806031b060d0209190f0b03060108012304020c1b06130303050a02010e0303102405041202 69
    0x43c9503000008990103111900d480c405107120444036182404006030100040d074098806104100001c21030402c6c100c45c9040a52001c603442c112002f0b101c001007000d40007680d80d40e081801040030f8001001000524401d03803038407000c901c440c01d001c0d00c07004544403840f07071041601613007000c0c1c001070019510340d00c846801c41c411030a1503100101c0e1005044030100740c0c0304851035003200140d400c3c2415080903185c0d0744044203d0040c40c1000001450107043c40311a61141d0142401241c3c04103c0d04107070301a6080d03520003038010b03903001201c1c41c96110741c0241c5118031040100020000308812110a0403a44075407410b84501d60140d00c0d00600d8244000013400120b440441e196043d6407a940320b00042c4049044607000301a0001c41e81d80c858405485840000d00c140000c020018a200041201100703c9805040040d101c603884c50b400d070b02611130a4601082d43c04004100603070850040c0050051300e111204040301c11017440128800d101e440384d001804103600744410800d0301056804016130f83e00c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 352945197 1250 352943947 352943963
    0x90102041a220b0307020f0616050f070f0614010f0320010c0c081e01050103050c01030e070b0d061503050906010e060f030106151e0507080702040b06210a020a08060d 73
    0x10b09810a1103045800e40014405900000c20700540030750402200c1e001501c1c140c050031107030800103100580c0c0c01e44001c1c0d42c1c050103800700e01c150100460780180ca115540000005000c044107140c500c00a002203481000044800300000c40c026180c1500101030725070052480c0140c25046183c6054001000303255810170400c070120400182811846100424440c03000f407043c560f2300d000700c41c41407001c0e0070118500e80c54680100040382c400144200500c0007806c1c00104113a1220314a1308003545904012001c180001d0804075202456200383c003140d843c0100601d42040c0c0020860030b481d01038400d038407154850350042c090704904031200760b0820801400c803c640d100c2440861f00399840766001d5080d900f10b041e01c4402c09600240c903030011014900c1d000070b01781e1252a02811034000c01801134030714034001c6200b43c2152210380c403011351244010540c1d900c524110041d204805014280041d070522818045440320010b4000c1e070700500d0180d21030306200d950300000d00034003124280b8107890340c507 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 352946447 1250 352945197 352945237
    0x9060601050d27060501080c03060a020a050f0c0d02060f06010e0f0109050d0809040c020a080f030a0f020c010b1503060a030305073905100509090601020a15020a08090102041a 77
    0x403c0f6920410012040c01d503001c980c82005081420481340c05034811441508074010f0541c2c01c0e54086030966100c0440c690040c2c44190f4900101c80c3c1c0c0c041e6030040c2c54010000643c04203141030004410246484a500311682036503400c162125201c03060b1015400b060400a961200d46007a900b01c001080b010b00d001505140e80f000080d050f4003c1041c161081c04001462900074181401400702038a51400140040103da540f4042d0522426402144007034002c000b00b190071311a07810821144101e01400e64030b800c01081441c4c0249002070400d44181c41d0030000d503201122240c2a244175607401000c0380021403443e142507d19074060380d01200d022510703080d503030603911801e1031000043c01001c0400394000003118030324405556903046280f05034545000700030080d82c4041201d01140095600706e9061300c404c0c0050740307461084d05005000c16003130703031681448195a50241203074500f00d999550f00c64984a00716400c0b4801e0740540d0084100d010f40703003906242502c00820804001d544050b01074 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 352947697 1250 352946447 352946471
    0x405060a110c060d0e010e0102040605030c03040f0c030b07020c010c02010e100e0a0e012303030a0e0d0b0f0604060609140d08190f1101020c06010311030f03120702010c0809060601050d 81
    0x613510080640b42074543d180000800318100f40b041404075a9007070700071458141007080107003050000509076003541d10000000b4003000751202040400c554007260302070310b07030780c0b640351903d0210710468540d4014482c0c103000d841ca540c031039143c8140054041c1c403003c000c801403100348001d650b02c03146120706002c4625142c4001d5200c032026200100420344001d0b40079414000c04503152181c401115289020840040c1010795000c0119411400f080c1001a003400d1080c01140260800d10406132440070312804201d61012002002846824104c1d0100034540d1a4882a82d1051860051448030240e400c225015820580c22242009014181841c10482444103045200c1c40c00640800001d50205000c031030303a13802100e08400140d82a00a41c1407100a032040d9503a40b00c1440060006048590140c840e40c03400e000c01c42c40c10b2020300580356a0261800e000c10507103030684001e0010342c079003242010801d02c0781600c41d0060303c82d000545920f484e120011581c1d5000344401d445115620b041c2c441ca4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 352948947 1250 352947697 352947709
    0x3021b0f010207050f1204050405061809060f0924100315020403021309080901031e0c1e0215070309020301061203030504110a1511010f051f0b0405060a110c 69
    0x511080d0400140c2d03a840c4614240d070818a140710841402e0340003c6891240701140340c160790648005950004480e600e002c0050745000100b140748188060302d60038051000c2002c00c04605c515903010000c5001d881d0303034180c644d0382d014401d0b103001110b080c40d074610380c4146030b1041583c100d5450b010304000c2c00d440340c03190140c40300c801c1000080345500242c100214201901c00c807800d101e0208041003a1545525a0006882210811410075958480e41c0070384520724004c200381040d50100400808424040c0980030100405421280480081c20718000c035200143c0c1ca04481c40025035240c6640b80c41070164044d10b07483d80b081b60f0554903400c01264100d032000c014983d01d070190b540420b4901b02802c0144810302e010985c680a41e4802d0003d1000c102c09400d240c0c00111603280405072100f940224500414541f084001070034184002c0c808242c1c0d0b44044d100c0c0c050121807040e0341c429a40c1413102d0f498030070b911a41303421140c1400314414003405071741c400c20340c80082c1c0c017a514800003038800907103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 352950197 1250 352948947 352948963
    0x2100b0a1a0a1103161104110301080f1c022802030d0f0f0c0804140406080a12020d020304030222020d0507120b060310270509060411090f010603021b 66
    0x4146408981c8100d46a482020740292940f0203000d13601c1d2003011020034550905600c4043c040c0c070031407070072643c603034440c0d50229031303c428003013841c5440b5610303452a66118010202e44491034440c001e24000f407442c00038012070078032007660001c0807402800002040c0041c0b22101030410f01c80402c1c05440941c0381405200c142d003100d9071700c40203040303401180a003d03500d20883c00010020845212800905200111015265640354100d8408500c00005010b041140c00c0f205140c06200002e000b00010810000361800c6103800b95922800700400c100d9590203240b1020354046404035000c02d07149611844081520b0140c0c40240c6400c030240c0ca400c094440545a145c001009809880840c2c80c8621070400c5400c01202c0452550901c0c0c2c03e827821209081c061440011f109449105403c014000c40340302c80300320488140702c03928040301695210b8408035000e40e4004204000700c81c8615200d50264481c5074010450301d8240d0820008600a41101c940c40b1741c2d82002d03500704141c0c3e107010801d4007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 352951447 1250 352950197 352950239
    0x50703020a03060b0c060411030c03010f020306240405040203150402070302060405070909080d052215050a020720060c0f1606020105010501021e030d06180b0303090102100b0a 77
    0xd661414801d03402012148282c0c032514440380c052080034004c1e00003180380f40e00207800034460003040d807a07900000e04203d582483c0c0c0f07505603e0100401c0fa5151142c02a51150030111149904802e1a500c4c2c00301102c0d00c4034030f0254409d41040148010305c1d00c0d5001d1a000880c40000d441800c2c86540402c0032a8010f107400d8005d0303407042c01080100802040040003a1203944003d01c10425031340c0d24502a80908480356901989910004043c3c071455000b034444940c45000401c3c500c0c0e140e0500e00c020b1040820302145450810000411802040c0200c406159016446465608206584141300401c0c10300440d80036504000380c5090740301c00c2002c0c010000c056409840d150011100c0c1e100a8081d5030302440c29a414100100f01581c4c003c6070200b0310030260310030582c942e0031690780b140c00c52046140424506140102c04911a2000c1034100105450100200002c444400130181e6074000c41e82070a006038000307c6075842d0f4620540001c141868040d02d031020407a103038110045d100010030a00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 352952697 1250 352951447 352951451
    0x2030d0e01090c1a04061b0f1a09011401030204090c030606081b0906010e1903060216060b01020a0506010501120f02030406090b070801060f08150301060609290d0506060d050703 78
    0x107002d100843c1c903120020916203d0007000f80034070184002e102d001d01c1c811071041c0300d80d418500034003084184000015550002c0503598010840c036040f0f40c400c000121041000b0064000224180814496a1429441c8410480d8960728681c20040500240c040841d07108004d1000040068072a00803900585920b0740a044040041034520070124000d0215a01c581000300038080582d811081101c0c100a050701d415420100d100c8503179a0500c016440149964400901000580801241004540d1041c401880181c140d00700499641030517040241143d08084010000756008030004865a40080c00105802031412084000c03600101c9050b5803164680714600c04114082d502039030721584900f40841c2d55410a0b1008102c950344c00380c911300307210500010600458400540e4103030500010004e00189440307601c01090741c3c03410700c1052580c03540b0001402d131a11001038100b1400701c0e80016141040d102050030380207040b0140509401c200200800300520349503000310351182c0c215480c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 352953947 1250 352952697 352952711
    0xb01120f020a1d0f0d0215070c030c170c060a12110403291314061905160804080702060f0403061a060304031d03011806060311030a031b0302030d0e01 66
    0x6010400094001c00460450702280183c0781c0d582d072044104d2000603204c4004811a610101d41820120310401440b0400402c02004100c0c1c03801c4420260303882110302e0b036100c6986140807940d020030904241404c1d0040103a0030100e080c0701029007400181c41c5022100d4201d1000e01c1c80840705041144030591400181c24828094040a11204e1000798a403542d0035102182403050103200103030042c51441c1d500040842402688030309864485101002d0301c04a0810700307109590710403800070546002d82040e0000e0300c000303900440365050781e02545401c400d03644e81e55160545a8840b4604980c014001c3c4501103040c84080091b0020f588107403c0054035952843c640e590700d03c0000005c1d44200c20410800001940c40340401c400040c5046a9141c01c40030240080d015080c03c484521180c500c0c560b8090a00140d13070818800c132406542000c110420001c14592101d003a0080034000c80d104000342e00300300c109060507403c500e0091050f07034249445820310382c054801804404c042a915004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 352955197 1250 352953947 352953967
    0x220b06010c0c090c020102180a050d060f06030212010509010525050304050f0304080d0207050406230406081f230c0c010e0102030103080406030b0109061b030e03150f0916090b01120f02 81
    0x10f1608c1806e281101c2e40600030345040c00150388801c8041e4014401354859034120740380501600003401665008008c002a1804042c0741c0e80280b10440e40101d00e5030804020802240d820304489801711000305140c40040110341045d00c0030760002c0c0c4121454855009480c0905206002030030240c0314800c064a03800c020307a880245010615000b06100349d2520004000c01800d0740074403020800c41d04c600766011680d010000300140140e42c0851064007aa007410482c009003112407200c09460490100311511601c9100080c4980007074442c0b6034000341c4404270f200e10b19090003800541401070000308000e0440c08041b03099800c00e9100b124140400324050007078980601501a1a807428a0414055441d20200504010110700c0c0e003101200d46801c0e0600341441071440600c04140941220040d00000b155501c2e0034108232800c0c0380c802e0841001c1003030750030049425510410403c0421440364103100f04c05000b0006038280c90b0611042c200c00c140811a0b0380078614000d90361403001070312110600 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 352956447 1250 352955197 352955227
    0x17303909120106080f0f10090510050a060f0905061c05030d0e070620280c0308030109110c0309041a1f030b012d030213030803220b06010c0c090c020102 67
    0xc40311482540184110003c24040001c507c0c8040d2980140842c00003101d081c100e013890755407840380c03659a060100300000c0074520380000b03048480d8400c1c202000d90b9104000b0040302c00c03e441507070344109010940c009103080200a0740641e4081d0781035070b160003032200c400e004482032048940c4090b0040801004001c2d0000050403600f4226001200c1e07180042f4480758903500203480926040000e8003800d1080241501000f0015621104240583e40c0300d04080303c1c190024440c1403002410103a400307001d51403000640b280740440c1d500441c1484442c3c2c0410003c0c0661035820707800094040c54041c515a91034004110400c05d41d4041030301906400001015516420141810310030455554543e442c08041c42c2e040c612058410f0305e2001c03c02032021000b82c41060283c10b00c600b90740c60084140702d1685d000b580154180e0211313002e9400811005059100e440d0800780c9a050380c0b000090300f9501a0401220b01440f83c00b074038603241e07125141002120b008a039402c2c0141e50105244020360249 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 352957697 1250 352956447 352956463
    0x70219050a181401050102190c09240b0c06070c021f0c030201050a05060a0302120f030304050715030b01090e04051216020f09060d1730390912010608 66
    0x300642020f01d40c18800040c0d03880484520740310009002e0034420313040c070247e180d0500203071010407828400c0c04d0f103281302c1505000b0000070f6011400c000507000558000a00211030780e0840481c0503080a0f520440f09071a0085070107000e0340c206180001d038018140044108440a02e000e460f2404402c0326824000d003102d0300104645400e038a0b080c1405050380d600d81d040d20440f64125180700d0072803074141c4454181203d4940281903840b0100500081213808107114096802c43c01c0303541851034820008600b07469507440d00d103003c5103040405224880f0801c1d0681e5000b4020404c4030b0103000c00000a41c0d60341c0c401c1c1d500e110580f002d8080c13801149041701d035101d4256012170303542c0001c1c200070002030550180c001d801840213504004180549012109540d13641c103d074248228942c0c100c56229884448040c004198183c00c03000140c20201c1000005110f43d1008001e2041c1421b017400340446903200c0e40c4800d48499040c400c0c85955650040880c480c41ca10300300115081e4034002119241100c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 352958947 1250 352957697 352957721
    0x13090510050106121505040e030403060603050703021503010e0411061306080603070e0402450403090504050405070b0306060d02040305011515022a0d0308060111030f070219050a18 79
    0x4240c0740e500d170a80c58459282c180c80d02102e001410700ca0fa1a180e520790f00c51544000e00c9141000e10000900c8030105a01d01224001d4a031003800d030a68202846c5244030034060059020410800328000c1401031030200103102000d00110301d0448079420218911459902040008038100200031030b0b030a091001d03a0003006001c259407414103040e0300040c02c003000c0072100c0c1a85055061518915002c500002118603e4840824496603881100e0503103c14100d03019004035505100004071810944142031103903812002510030035003030194004260388041c00303003540010700780000d920011072440104001e52281c0d00018000a0341c81d114540700f01c030b940c414400c0c2005200c00f902c1154010400040d804160050744980c60138004509445030651450305400215100c0160100b5800c0781e40a03002c2d1500f6219010f07c0006502d0b4182d030381c03040741c000140c400f034103101c008010b05209241201d0070000f0031034014a2a1a403010030325a4649601070312030b03100070080c040502d503028400c290300014 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 352960197 1250 352958947 352958951
    0x21903030e0f040212071223070804060f06120b0901061206020306061902151006020d0e0a050409080307030b0607081215040501080106050312181309051005010612 72
    0x86551000351a404070451018021600050001c2c101d0362280d045031620300002c031490810f0709013600007e02d1a03408180711802e4074075040c1c006400e10f00340300310a6515060750082d00c15554610070704407a440d002900460714103854011000340c400881c003850020b003e10307a0a2000c0c01915003001e24043c003000c1c04c14100c0d42d2504c03e060106204000c0d0f98170016810810240c2e0b2070b1a02030202d4140d119005000904c551405504180c2507404110301010f110ba2944d551500d4032810b03000c40e100c0c4d100e0311502d800759026520901400e400740030b410444060003003021031b21b540c1e200041025180100d404640c0c3c041d0000400064941500c0340010343d040940700d01e4100505951040c00500c00c0782ca407603110075101c40005011600f1305100400626010300248807950750354620a001e0500c0303000b0540310b0302440d0300c013102e075980d00d8050350516501040d90030307142c0c0c500006010044d03113500070443d10940c03626a06c601082080140807600f078400080025590b1408100801c8501c0b5a01480c124074 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 352961447 1250 352960197 352960199
    0x201080c0a0509010c0f0203190b07140a0e1203030a0501150306030809011d130608070e06060904111e0d051608041515090504050c061908060423040219 67
    0x1d98044140c0d5000102030820310410055418140d164450b019402036040c0b140701c440b0010000707104543c1c2d02482c41541500c4090303d9014040c0c607044103100070300480c500e0038040040300d28031401100d00c04400c082c001094203d1000c94442c150340c422600c241081d80c881d80108601c1403c1c00c203218880e585450108081d9080d40e450901501c5070701600c13810000c10b2142444040074108500c52030640003000c100d4200001d24a102c041d114601c1840701c01c0c0526103002803c072000f00903040c450540106150300d03150204080000400d0103000c00000468103101d655110b82001d10200c0504004844031511144103200c40400d5130030003043e02884107401c035085105903400c541c0d500c0d04954003404940b0040e00a244400062100b00030810310103071040740020b10f0314000c2d80014061070003801650820701e0740c5000d1062078401c901e002ca403156440d040308948140714840c21900444001c10106d1410f40032101100d64800030203500382c0180c0000c00b400308510f803500c2c0c0007983c0d4031340000d103080306 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 352962697 1250 352961447 352961467
    0x22020f13060f02060f0c0f0a020d2c0d0303062c010b0405090406110904150f09050f19110301061106070807120f020717130e010308030a020a0c1e0201080c 68
    0x7024040c06801d5417035034200104001c20010300035101d00740c1d0803550880d102c52807110020b40d03408484a601000c9001a4495081e0125800d643c01c1110111688840080c0007001403261142c54940254209540c4031000f26545851055040c0e0b01300792084454a528422070406e14500070603885140c0e03c0d10108800c00480c1c603102c00040e803003904035000040c00c0d040b90000d140e40c1c5c4191000346520914043d50184000c44241ca01d0041d42c0c0d51581511001d80c992031564221042990151016122040002c60f8907000c0101e4481c1340b50401c50218240b60701103030503407403a0030a03007201010505001580700d40c42010003055511040c1da2502e9885404c20602c040e010818802c000c0c2e02c21625038540395110710b684d070101c6c0d080c02d40c0101d00803401468148000520b400110440d5501c2d54600000a002c411130581c541c16207030411482e91454642c90740c0c03a8004d6000e1454001400312103079074000450aa103000d03141084e01002062824130b800c0c8001861500000c0c06510751500901015000c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 352963947 1250 352962697 352962703
    0x405070b1806030411130e060f04081b19060608010507020c0906040c020c0603010b120c070305120403031b05090310060807060e010c05060a06150c1122020f13060f02 73
    0xd9060380e04a0383c0f0b0320785083c60b401d0040703404d9201da00300400c103500d52252038040c0e122034003082d82a03090300d0580d210114064010718080c0c80143c001607003401260512104961407000a1192104403501000c3d201954410709002d100d05907411035460700d0400401c2e00c01c1c0039450b40140c140c030140401111410016600d4540a880070340030366642c0c0f40700280f96008100b0800750860017441d25480390b94590030048540d00031101c9000780d911000124019412130030942d080b103030317158a44a0400c81e01c5c104802181034014410f0f010980c80d450034614110030302c0003801401d06241e54003903031603118000b4103150101d8400c04048641c6812410411804041800404d980760703490981c40c1d90b03505100407190210405000350080c010207040c4a6001040c0e0300c000100e401280980c0c02d800c0c0d802400f901c000d406030002404038025040141c3e0030703140c02100306450900c1d011100c4c184000110f400c6080340c2066035100710310280010342c0040c4100405001004000b02e14000c000070030460300c0251 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 352965197 1250 352963947 352963987
    0x7141c0201120c03060302120607090501140a030f060302040207061a010c051f1104090911010512060111031e210123010507120203073c0c0e01030b0405070b 69
    0x1280b82e9448190040e258802e80081c0c1c02960000c08581c00c04400300b400c6a118801030350400d011400e08207000510394000c1d100c0c410798040c460309950408100340026400380040e400001c044660742c84000c40140c1e142d00c090030131140034240c000f8203010000c01c80c0b0318203075902c05e520b07050003009101c080001d84e00050702000e4102c03420400215120403107500c4080e00b03803044042e8450a01040c0454100c0d0cd80d807200c03039002c2c068032480c00741c00880001910944a10711181d091103180c6d60004590394003440715410148243e400702c928042c07a140c48000612011b40c20403a12500c000b80060751490240d88a880380b8a841543e03079500d5260940c0f00c0b13107a940651100440d0030740c0031460034003030380694144c444954101ba000220404503005c000c1d22540654001c035218030240180ba5202008400c172038045020031801c820300184003404456010000c602c00304ca058013043c01c0482c15002d035070002070081d4030030162400e41d81002d00e841030a100194020b207580181c00d100320071043d105058030003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 352966447 1250 352965197 352965227
    0x31003020f03071d04110607080a030e0f010213050112110a120213030609021c0c06120213320913020d0c0e1008070b0409020a1107141c0201 62
    0x400741110319001c00e0810310a68480000c446144410299204034140442e100d10301c04c11031304440f580c94a0070401980642c030300161091200f40042100d407802580803030450521141107500c44a1249011402ea9201003110340c1c941e86808410003255801422100c070340004003400340003800084007840c00364040c903480c40d02000001a03840521052550454080103040300010f200142c0380c1c10150040c04038000e040b8028082080540241540c0504c1d5041541d031100289034078038034100c0c1c101c901c0002c158040050340e40c01c2100c3d460220411840b00300500e03000d104007031100040b6091004c082d00c43c0da130142d100511441500c0c51a0790b4050403540c0000e800e03e00401c40000c600115184400900000b401248d01a00c007103001081000c12611520501074008409903c0d5040f00707807501410700c00d5103076620b418441440341c02c107190080d00350362500d0b20307003030174035000445695291064951003400341080404010607c0e042c44209200e1700c005207841c0340703c5500c981e40001c25200501003c1d03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 352967697 1250 352966447 352966459
    0x60a0e1011070e0603030d020307090807090501050112051306050606220609060f1e03060806090a0c0f0f030602030402031c050a140a080a0b04061e050405070801032102210316020303100302 83
    0x5025103001e80c41c0d04001d0500fa03410dd52400d07444900400c0103101c01e014260110340ca50b0b1115552041c40d00407203100d0034020148000594072907075040c010308800b4060540c84101804001840c0418909400d25444a2000c1d10388080c94a90050a01c00960308140100407500e03003150801034000d00b4070742d01e0648114803c5524540e8a5044001308040d4102c3d1116019910500076200790000c1c1d0380b082d8a000301610300c0380381e668106090700c5914600c20110208803806040010505035805103600900190541e880c0c507001c4034407070018400d845516000700e00085035a001c45503120070b0380103140740340d480242c2c5802d10a001c05003003464010480e44106450329205251500c4680200b00103180c6002c1110042d40340307805c078000300302c0c2600039a40244e25210020f03d20030701c0b411420381200c0d003160302c0c4517131010480103011130b2000d07462403a41581b064200512540c1e0702a2202080c1d400c111201c5500c4e801c1006884400380d0200c490001154400c0c03051080c0340c00020040c000f101c3d41114a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 352968947 1250 352967697 352967701
    0x10806060315040c0e01170d110705150c010e0a032c1002011e0902040e01020306150c0106030210050304110d050613060b09130c06030908030402060a0e1011070e0603030d0203 77
    0xc08413001c90a504034000e6401001e0000452102d9482c40e46148000725081d28032401122804861a00042e4400b06059001d034108004a04003440102c402041c6103c0d01c518115100c010302e8251042c41c0d684088682c40a030b121814142d01000800009444c15010b082040307840109035400080003424a128500e40940064424000d5012000e5410810b444225138094a0104001807004107020380c001d600f00700003a4042c00c010302c00c40740b040f00c00500050202c0610264201903801000040041e0b40d40d40ca0084090780d204c0c501c1c4220b2400940d2411340c0c1e807030a46069000c00381c11111440c040c0a0080840e00011780100f10aa44a00001910440324901d8103140000e4920b41214642205024041c01408541c0181d06c600e0340c1c1c0110b00384e0b02d42640d556421012580d4405020b840c290b0280b0124005280980041204d84094038062007a034803400002202c61170300c14084004580d0305018218165070901c0030100400005001d02030784d1410f2004682c0380c0c842c4507040610f090780080 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 352970197 1250 352968947 352968953
    0xb030705090a06080106320c030d061e090b010c08210103080903070617190b040513060b010c021302130f0b0a0201050f071709120d090b01080606031504 67
    0x70745800e41e40040025510b90303a02d4601605041080c05414002400c0201210100e003c0c072041e03901620004410700f954540304c41041d0600d800c0514203040078041003200c1582400180100f03406080100b0440b420405564614100e000300c5a102211443c00c15203007050603030b00034400c212142c0d0800c5070141e80e107030b0000d11131501c0d00e01c1d200c074008401501400801840303032100141c4452181035048841c1d250315604240c45007000d6425905600b400d070000a03891402110001b03000e803420b881d020030f45211403000038083d190100c4030020000360b02614401845054000c080384588282415075101c0f8054005c151030308284064481420340001e000c0f41c02c0749003050040300501c0d03040000342245865404c00007051b44600c0e07081c1c00540c28800420070890f6480b1040303009101948600035081c4100c000b030480140c1c01000d0107041e00071100a004c1040704c2170020700f180544280005500d000c1494840110081070f0002c038826031180040100c10b841c001140082c01490780d0700c1007825500c43c5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 352971447 1250 352970197 352970207
    0x607060b041d030408011a0a03111f030b0102120906040501080612150403030609050c04030f0507150f0323010b030406090501020a03050f28020904060306020415120e06010b0307 78
    0x450b0060000c00310a080c2e21203a00088058010344404400a00408621000301d21500b031540111315401070601404100184051048900c1e209024204c0c6034507420f00014815191003590740c140101c0d07160283c00c0360030b607414003004c00c2000c400c80c0340505115800002c034146000f5402264184540380012036010755402840c200340c224054100c844030b581d125440b80321204142c90480101b414014049181c2e456405114030501f50583d805040c01d2450300c131021640700240c02500d0320700030041c020850010440050501c00c070300d521020000301101c1801003c44044011040c0520191a1510b016100200d8840d0468900c03482e0321351a5221400d00000404031050024041e40c8001091000580c150300458441c0c203283c0e00c04041a500d8410403d035014114086180c9842c0c4032414000d0060142d001d0303c04075002420000d8115280c1d83c03030904a0744150090441c003011005490507955011400304078010482c003050191058921242d5074138541070040d4031403c0c1001c400150054811 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 352972697 1250 352971447 352971461
    0x90f0103050d20030705160f06080c160b0f0118020424050408010614090901090510020a03240905090d020c0f01030f140a06150c1e0f151a0607060b04 66
    0x407900344e9550b1802803600c0c5a03a4101001d654440b6003504400090b1194001e24080c101c3e07100381c440e611039036540d840d9440d15074008000840400d90b40b1001c1d0340401c081e04405480b614210686e000554105052900394144c0c1d01c4000b031500d401000140134503160b40510301c1c4401d140300341d0a0072088010b0001e50b82c500450304032192a6181920000302071401e0440d108003048152070140050316000d146174240c5144110103007066010100c10100d994455008003041e403001e280010301913540040727040c1c0440d00303044000c3c040881100148100e4429114294100b83d4400051210040e2a40042d4441081d01c401511a007171001e0b842c4400c0c2d0080e00b001c00ba541203580e0801c1202101d03009018102c2d4240c0b041c400301ca203010030200d1441d20080101c1135800907038844e400190b0843d540c50300d041c98941e503401448a910760702040092180b40c1c1640c201c510410240c3c41058200790103404490b1500c00050080082250171919600c0d000211050907401510100d031051000011401038904 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 352973947 1250 352972697 352972757
    0xa0e060a1e02031c020c0c0d0c0909080c0f0f07060c05070b030c0711030102043006110c06090a03080109020a09150c0c0509060306010b1803070311090f0103050d 71
    0x91040000140e0b400f0000302007801c03120f840b220a10703081001040c120301455a104400d640031455072200744c5040c1d000d0486151044002d4050507446400e03d07815502000300c101c41004012a100f00b803003005000c51085c56250700000c1420007040034982c1d948240c50b208030f9081c0712981c1c039a14148a4180030300d401a041100100382d590800ca0312185035035101032819605417035005091034161906000700c0d0b0484080f80e1342d035111081001521a80b6840c154150151000c4150030803000400f940900700300d510484c0340c165200d0007805051410014000c03c841480d4000720b02803400241c201000300d0540b040c2171401619403094000036110365216411010130151505149800f075603100701d6061403144075001c40c807001681c4200b8803001c1d800a0f101141d040e00141c0040c010b43d04848050400004941c42d07107800300f01142d01003030030072260782c0041c0c0384051704040c0d005050a2100615030486800c8003101d100350b146851381134842c0c0d02c13130342c9940c100030060440100c402e45010b030400304160 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 352975197 1250 352973947 352973987
    0x503040510020a05480609040609050a0207051204061b062309120705101509020d1d06040f0209060f0a15020105070f0c060518010f061a0a0e060a 64
    0x100702e8030517040c00401c6903010f80317540c03081c1704081004240074041d070031740c41c00c0c0080c1744801c0c51201800c01031a908110241d0f034101c0e0380c62200160050a60080902641351a80c0061792040300d814881d09150907200241c480f081c04000400505074030403600e03401d00c40040c50b00401c264840c60b021006c0e08400e840c03241100e807038048070410300c100080d20b68041e0940c00d04031501f5070760009003200e2501031090081c22a0700408180318075500d498003c407050b00c4400c0b0701c640c9003030380700ca11400072170f04440d0244030020354070342080600c007404031403051440700c003100100708925240c2d4603054a0034440100a005440c414085929a2251003c0d0381e41b9601c024803000310152106404101e80e9811001c4600645c2400045415a800b4032420a09900c7c1c0303070780f00c0511114a48501300078007000743c20009503080c1c866644540d0750b428030440c1c50007003201e0004a01e1074034080c401d13850407045c44060b00a040d010054880d07403607004812100d0840040e201c440d107a0b501e82d002659500710114800c02c643e0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 352976447 1250 352975197 352975213
    0xc07020303071406010f03080909040309051215070804021e010e13021e0c030f1303060c08040209060a05060a0e03030c1516020304141201150b07060b0d0503040510020a05 75
    0x8481c81103842e550b90450000c5855684c0d1b1000c42010006042c400506403c500b00a14240d905140140950280c020306041c02c040d681d0300d020a4183c2c00f1550400080e07044020802c801c03840d10306400382c0018040c030f446002400d00d5000151840c4c80c540701203002c0c80700035001e00d00a13400380704400042000244482031804494000c000130b944078a2502140110a05c40900d003c40c202c4241c0380558400402513003011002000ba64a07513021a81c0c4070007840c00944000001000350040024214141c3d9584c8928140752060103041e50000e0800361291740120340c14011a00c544007a202101c4482c070f084607990001c100402d041d480b51620f458000c1c010031501502e0181441c101c54040c116100c0c10000c12a0782403005c03a260b02a9000d600e881005000d440391603407030102851030300922000300014500000d510b0840003c0400c0e032280b240001c01141003820b0100303500c00ea030303548032007660400c2c41d203001507540984038407ea0140790b00c51002c01d1000c190a6100300b080d004c400c1c0d484000c5814017 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 352977697 1250 352976447 352976453
    0xc0216051e060d060306110a0f080a0b03100615140f1809090d110105070801030201032d0e2b1b06060801060e090f060f1b130f0501050406050405090c0702030307 71
    0x505145c0c0030642e01c0074181240070000c04824011107800d07050710303580c110000000640844410030003800c0004655151400e1000950301400400b0521204643c00100645400241d218080601a0715428440c954140780049143c120440e0398258040709510f940e05e4101001c64881300c43c100c2001d4000d620301080003004000000c2d94000342103c0e84401030071190200344142652012501c0000103000407004000650003508171350002c9081420442160540b607030f030280b105030940c0014000c10740300c01c15809020300602001c0d00003d03450b040c031004040795404d41c1102d403c81c002e01608004c0712912080d80001e61401e8211a50780c03280e4107000c4565205c1c0d050b8003a005c940952048408008041001d01c1c0d4005125600d0095120280560340d680141403c0340e000020325420300300706901700500b842e0301481d00074100341180c4001140f041d0304000020210381841d0b00b00074107000342040284560b582010986e0201c2e0f00445a10b485680c0e05030003030203240a03610000b501844045151020 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 352978947 1250 352977697 352977701
    0x90f0207030206010b040f050f1203031509070509030a0b0c0c100f2d0c020319031401120506010e0619180e0303010b09010c0516030b01090c0216051e060d 68
    0x40385001c1d034221442662202c4955406105520846080c621549410055410004280c010005000301101f40304c885090005080d58011996440d408594489a290303500d440003c0300d4110741e45140048c1040d44070740100f036442c2d16403d006003407084000c00040814070bc82044900440345141070303c2000f1442055a03019102120040b012541091101080760b0000040207240828025a90080c0d0500b009954001c011075081d03d011808100000181502042400e1815152a650015209049a00343d0b00017090603044889921800003003880400c100060040c151404400402c031a07403504d000054549103a08181e03401c100c124080007603207105070301085010303031420301d000d003d5200c1071070140340c591109002d03014085070140001c1525500c60415115400d21410072a10840c0e1514041001c9161030b40c803c40341071201c8001481044032138001c00760083c003c0e00080ca910030507840602d05640c07c9001e00c600070503000c140c45c204401480c0c00b810149070050070f1183c0c4c80c03001c2115480 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 352980197 1250 352978947 352978957
    0xe070e100e0411010305060f1203040503070806040f020913050a03030e06090a211101021603110102030402090f1f150f1103070807050f060c13050f0a060f0306090f02 73
    0x40c0031140c1000207080742055107101d128940c4200c401940454202c0103400400d8040c00c030030b42140800420890644a5070259252140701500444e151480c1004140c60000b039034100c000030350404424000060200c40310400003642c1180d461002d0307501c298140c00c0104142c0300107403052003280c0586007032503003652002070940005010744169582e0010240c1d0740d0503407140001d2000d01c0040d480720080d408100d01d070442d051189442a030030440001c3c00e90a82c1c21440d01400c4100c41c10720400c00305500450034110030b119043c02507003103242540003c0d4018030000c2c00c5000c0701030f0480c00980e520b421100070841c4410740e0b402c0030340d4040c3c40300e2040d100d031418010104080303801c0d112019200c0b80150800709c0d420001c0d1006525001d003641d40d0001c1500a404110740034456001c1d41642d41205001c1588101506031901c1d849803140c2c60700d0940d140550b40114094403000540c07207101c1c1c496100c80402d450850621340b100082d0164210010304440d84035144003490511001c21542c01500248 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 352981447 1250 352980197 352980211
    0x10504150605220b0415140a0e040b0118022a0f0109200a270b15030406110d0603050c0a140d03180b0a05070c0e010b0a050d0e070e 58
    0x6020346540030701076245450b80003110102c07a2044041e40402d1143c00400f592040600041032003c10701b001c004018a03180c00980803405481012000350a04d0000700004013158441c7d005281440d40701c10400f0141070082e044507014040c9446000d03009501110700c50340100021a10700316018903418402d0813a4030900c030503401107586a503011081405050807240e0410040d914008542400300003d481107059a50400c03000720b0001030045084103802d04204400303100c80008494512101d04032014221207501c0b130a0f41d051499502420f54050380c2d40140d0041c030000d8000e00c2c0c40440607541c044c5032014282981800c41c0481084000f150000f100003060340e100d1083c0d611000c02c12540500001c090760080144000745e000300c0d1007500407030354040100305c0c07208005859001044590344549801d40c046000000d0480170005000709010050007420203080c0d40b54189080405030b0300c82ca1000e0401c00001094a000d44611980010000c2803c8411100c456995041905070070404880c05 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 352982697 1250 352981447 352981451
    0x7090f14040b030c1c0c05032b02070e010905070309020619030b040b03210408030301060f0e1210090c2402060717040204050403050c0724030204030c170f01050415 72
    0x31056400c0001d0400c0110000604022103050344902c14052081d4400050f50840c3c11a00000340c191000c9c8109148940220400300c0e021a00c0e40e150700e502c3c5c050b040351904650044908201c0d11001030b6225054032503003400440ca544640d90300318064030901c0c001070b521040000f043d414440d49804020b4607030450762024025414640104801c4520540f501074158210350026101070700140000b89014a805649d24205900c900050f4074503042600b0010200d000c1c200440040c5420512150805e4402c07a1510340c062542203c87d511a0050100c1506154960080c581000303151500c5c1c00140c0182160b8036802c0541d0302509202002d00e807584000350154102140f0307410720071848021078202d0107403942ca041e11a0350a110007000000c00c1642009003c0c0044880300100b40306820060040754086d801501e15442c54800020310756014105040c8104400c00c0050404107008003214101440000d40d8205810240d0400162680165095180c1000c000c10040240030306a00300300c0410741 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 352983947 1250 352982697 352982711
    0x1e10060603020c100e0a26040609030b010506270a0302040f06061b030509010c0201120e060702120901021b060c060109050a0b01080702150406060b07050304090c03020304021807090f1404 82
    0x1c0ea0112252105003402940001c3d12180200d04081000c44100d551a54407860041821f1710001d680d07017064010b4000034003100c900304140281c034020385014000440b003140c40e0440c0f2070070800c09030002a00301140800c899107a16219a103000401c4021500a482030000036104181c400003001c1c103005c1c00020501c0660242c040c50104900c5008455058640c18034010fa618015105801002c0c0700f241000880340e8040d11515a5000b5a5035071001c1e5070007000c19013480c0030003a0420076002c4299601000502c05802d29a81c002600301c0c2000c0c0c0400c87d001c0200450003c40d01c0c501c54130744881e4080c801c400c0002010307102750b07201358401c407070158007002000c40d8040112005002a10180c0c0164404000b2000e2130314140101c0c1d42042c4540c90004032103503100030300a13842d04040341c16244c070307003001c20100315580080c024800401110715003107240d890254000391148070365400742c4040380c0074400010b081c00c3c01600440c0140074541d2840010300d90b507404030300d403000b5070340b203814001c1c0c1c00e10b40 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 352985197 1250 352983947 352983973
    0x2604261c0c050a05090a0504140412050901020c010507050114240d030801180e0f100b0a03050d180e010b0a030e0601030213020702060909070e0901080703051e10060603020c 76
    0x3140c039000d82002c2c0d403114a4000300510403a815080f07407401e40e6004504400000d4580e072144225800d0f141110310501d80d500d02400c0c082012980010740d04107220f0100b0807101c0c103a0380840d040c01881e4003420071076200c00d01810194010900b04403000303c0ca41004090020002c0b00684810391000d032484140005000300b4140b007141c201c3c18034000c02280d407030001404030300c003828441c9880428142c400990340c81c0001d00a85031002d0810200d0305500075100205000381a8001c030b040805050341c011440b51b00d103540e441e40e134401c6414000c0800c0b8001403c0b20000f5151481200205000c40b040030725961903c40030705442d07201c00000310129244c8802c02e081600b010a1b846e0407a60018050204c58014648980195109840c2207a01520400030310321941e41e8074000d2405040e081e910807a402a6400910506034010f8005e4941a8000401040082d07000a01d6046404070404440d035687e2030400a9464078844284101e030700c0d4140305012510340e50540c042c00f80210280121010010184 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 352986447 1250 352985197 352985201
    0x1006080f070f080606100c060603060c030f02091f020f0f06010f090c0f11010e01050a050615032809020904050a0b0109060f0e0402010917060402102604261c 69
    0xf00c25841c1603000354002481d41d250005502800b01103904010102004030395844046403002c6c2c000311403040c0c2d00e141d070030103442c0d1610a07281d1035014514214a010418000201802c500c0080e071100c030703040e0f00780c0180e6151090000c1003903444001c044804a4001744120398a0302030034014504130071015140040d406e821406103116896040e01e805007000e007004c42c1119507012511500c012592244c05404885109228251180d0115000011241031441c1080351000c00c0300c2c1c0d0300348400340c148140000c0c040040c001500100d11910042c2581040c01000000b608000300040d41c04412181088107200c0041000e2800d10300ca05402c501c140e8850b4a0141242c2d41c0780a1900b6540c0680c109100c41c0404030700e200e42044c014144003c0d100c1d6201c54258403000a0089490541c00071020f02c811410560f424001030342850503d090707107a50020484880c0814580d48008101c80c0c100031600380003c02c400704020251500c911801e9005480035400300b076000014503c6070f0014040c8404021111b8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 352987697 1250 352986447 352986449
    0x50709060f08090f07090504110102070b040b030402180f0a0b190b030a0209030f07170c0603060d0f050607181401050304081c150501020c0f090a09051006080f070f 72
    0x15440d10442400860000c4400001c002e0111650b40301e40700b0044d252000420905004005000340030400749404d141c680e0190b10f540040d81c1c1994801c6005100030020101a581525440500d80d6141d54813400024041040b01e10f400b41c8080043d000c0c40b1032a41100c207010702c03501c410303181840720f01600e5050000c1e8a65004580101421004081c0301508020340195000701c022100581080c504a001a040c12032001c80060180c0c0b02e1070080140d000d08a10040005100d54080c000b052000d4000c581c840c440100702602c60388800c902c900800100c007400c107034620b40010841e9031904c1d011001400390386108007141180712a03031b00b000914014440c01100040b6040c1d640b076045440313a551307558541d0485c8911510000c4246100240c039842d40c4901c0c54078012207018071101d20302e0000003a041c980c21420940c0140131030902854141c80e045949a00520060f030001405c130a0b40c01c02c181443c1d08400741607246420310000140c0e1103400142403005a99290030340b00c4140d03a5002541e500021 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 352988947 1250 352987697 352987709
    0xc021e03070501031104150e0a060201021c0e1c0522140405040f0b0a020a03050105061602010509030c04110c0c030a05060f07091706150303040e19021902010b04050709 74
    0x40100b4000d9511a0700700b4145100c2c00c50782c150620b074030341140c1080d04020030400c0c40003400c10290114030303207080b10300e400080078140004c52604005046181c5103c01d0040700b2507145881e0703007003881c0103030741040402c0321440704200c8024480105800103059030300030001c00320207514200d10a14202c48107082d2008880c1c1d03070302d04503010f0f040c40414003010380030003801500e214041d43c0d903840218201000c50ad1103842019401a5640c08403030015045801c181c000340e01800c0309001b4446440384070001c685e24103409003089500c3d09900000a882c021380120b055400a0418940c02001c40c0050b000e0850441d1003000d880e500d03513101c02030503075451000901409035400794022880701e03d902440140c000005180101706581c80da0002c181000415010380c0d440e03440304080124044805041d00c002003811405903280a01e4030384020039406c030150040810200400601030120b07269412075069400901000001d4038142c44068000c06005002e54000d0303040400242525200742a82000d940b0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 352990197 1250 352988947 352988953
    0x9170c0102100509032a100902010203030403030f060b070503120903092b080c030c06011a07030311071b03030e190e0a0e19110402030708011a09100c021e03 69
    0x20b041d460040580405400d03a11030340420001c84204000c0c40c42c0c0c03070105200030185104c1c240038125000349000c800e42c0c05280c44a1804188100507a1b000c4200ea07003241d0103103000320b01e00c40700d08072036001400581e000c0c4104000010f400c2042010103c060400c1018001200959a44894132142c81384180518560301c817290742144502c0203442c2c64020706980a4110014000b8083e80d500105035002910000c081d0b813010840701e0ba0f40c5801c00215004d80807040c0c881440c0d446c0680746500c6030003601c000606144d111810241911468015211000e8201d299415401c07860203040802e10160b00082e00061b030300c0300342c000c00760510104a40600c3c103440c800b041d600d07240c503c00c540c11501c042c0c4403100392919034030010070811041107800079a00981c07580071700c0101240f80c5030118108aa8156000c2c0d0300500c100010341e42c00500c502d0442d0100514000d1054905200c80103520908040320307404040c0c010014082c1d54412078125003907209881c039a000078000d00303070326183d200d0049402c0d41c554 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 352991447 1250 352990197 352990213
    0x8100608040f06153201081512031603120b0102030702010305070e0405040507080106060e060414010c06020f0409060914040210030605040608010b100c030905090c1909170c0102 78
    0x1800260703403401c000d00a0f00d0004240241469000800382c4550151030416103180720056a203140584c8840c0110400007640013108202c0006442c2c1d80e0010b048245500d0f05441219440d22410403c01d404210681034a82e0b4800428a0b03004e144200281500000e06c64551070380180510301c104440e10744160021420940755500440152800408860030058403007001c1040f6211401114000e600c50740140080b81d023080304041c2140d9050b80110104221108203a9072916204120f9083c0c83c0d42c544a480b03940101d0005a8a03807841c1c00008007414800540d000072a19400042c02c159a0952800c0c0215551b550303182080e20800d0100d00888142c250214006183c1814501416186400c01040f11aa0748001a0465581c0c0e809010284d460f42041c00c510716103080444a042c1e040d003004140e505c0c079130b20000d00ca082240210360040f00c00102040003c0c0012080d1000d040444408106940c101c1000400e40032880c4225281104080381a010304280400c0d004980601030340100081 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 352992697 1250 352991447 352991453
    0x1504020c010b1c0537060e24060d0305030103141c050a031119030518070605030105030114010e0708040303090f0501090c0503060c12060f0d03170c03041505072d0810060804 76
    0x108050000840308247d03a510800e00d821800c0c40314491184260071054000088000742902120004058511035a040001080066048401e80f0305483d004601d1412519640c018186045401b42c031807180418809880c20704268000024042c140d1150b074180a407900fa55124010f5006181112104000c0040381109641c880d40c0483e0740f00500c0130b15001d1414a8036111790402d002a0000c100050000005005c503003000d025101d20b0350110703103108a180d8501084140d40072009030052080000e02004181418882d8000c801425045502201c144a03180f5205000f02011902140c01c011030040000d814503001c900315110310011744c121031400114035544904500000c0c413103a40504e004c18407036140c1e22081402003116200344c585540b0b03154902518200810000d0038030050309010020000025802403280701005c40219000c20b440c1c80c1c07101c083da24481c0610b01d1038041d5420301d00e0083d542010b1205085500f80b281c0b5602d000e5100d00051050920031400b410b8040303110754000c1800 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 352993947 1250 352992697 352992793
    0x70503041b270e12160c03021c05241308041a030621071a09090702030a0e190614040b1603090504051504020c010b1c05 53
    0x908003a08031181c846a11280310114502a0051200d010100d842c1114848100c1e0b11800c000c07820044014898850141c2a11502d4410401c03c03107000001014018104682c01440700c1c00f440e4018461041c11030a00400d00300d2040007841500c01d88201c0b501650800c0360440c403040411040c540c400c901e030f42c0f41d007850209a00c238043c0499030f2a07820840041c51000300b000e41c017101e0002c0c80401d90750b4103105041142850241509034000c0d1649180e000e2440070000f4040122000462800c8084807000310190307c501501c101181c00c203540c101003090260340800100b066903000c0e01c0314902e00458400f404000d41c0048112001e0750381000091044500400c0808408085881002c0c90715407165007154035a0003003070303805e100c5c10101c4c1f103031604164111521201410342070302d040065103415a003018160b40444003080c0200c0e4000b41100d1420340070740002d0541a8040d024030707511080306d00301d08031654801c0420780d02409480070004805040f40c8035000800701021224401e0f510002100354 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 352995197 1250 352993947 352993973
    0x62306060f040e04120e150a031a06160b1305100506120d020f0607210c0e030304080309041b1418091f06020106050604030f022403090705040507050304 67
    0x1100c410203000001d4524010001d05100c0c40c0308102000035289917520142454401d401030503c90181002100c411400b0a800d40780d10140703500e0007207401065244900c05900302c0b400510f41000000865804103002c0714080305901e48034406400080c1d844a074403045140d40040c001700250070500000407101060740146820800040c075101c02d031900400070b1450201565564000368003d6082d5000d44d1a091003c0c0754003655901704400610841b0300028100c20320418000704440c1d44000303080e805442055000c200b1900039044036952034440e0545581e80d00070485503489036080400804e180d8402c80000340d544900ca444504c8506656100003502d07401c080b800c1e600f15403110110a00729980c00312818090a504d51122103540a040410300136a12190850015607040c000d08000544920040300c040765000030901013a4940317403000a090030000440c1403c00b031b11402003c28841c0104006500402000c401c680c1410f5498041c4401e64904482c6280232403c2800010003140b061540c8907 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 352996447 1250 352995197 352995217
    0xe0a02010c1e05100c02060c0a18050918010605040c1b0f020411030f06040603120f02120a0e031603020d0b18010f1a0409021c051603050a06230606 65
    0x30319902024101006081c01c8074042e20203034446030300c3e4010340040b0b100d9085e0f00703c014406800340d0300e0612034056491154212a0007005030004510240d410451420806080010100e464500700b0105180200b40320f400a0802d0b946011000509442d2a1140740038042c1e15407614150116816081440c0501c810404d136203032403a040c02000140e60780d1292030340f4030f4a14044036840303041c400c15000000f0b5000301903034044d0b03103403800c1880410f107407500c04105c2d030303071a1f00e0201000725014404a0405440d0307003441c0d0f02500f01107049900700d50481d0344c0400d81081a811104400490f80c100c000c840110300c4065000306041c4641c0d808503a9040b0f18562010524015a0140400d04400b40c2180d10f00c50014030740642d0f40c0c0861164980c0b00c401100740142c125400d00c101402ca800080f044210038000070422081d1001e62400c00a051011021b1203909594500c90143c0d0f0342425911001340000445d0181c0c9000c02a1982a41c00c0500c20012902c0101c0400d00d61b4070314003400101c0c0d024a13a05 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 352997697 1250 352996447 352996463
    0x306010c0606081f090b1b0904060905010611071401030c0302090d05060619030201050d0203060d0c08030901080705033610060f080a050604030c0f0b0f0414010e0a02010c 75
    0x1600c0440c0340c0c0d01a0b6001032000c41c0c02061003415201c1d615203040d407454000c011150400c10108081481c881d615a00103c60741403641d02019940700e08a003078494200c05ca07410904200c800905892554015412a425520703220362005120000e50388840c050b018030964140200d0325600254420ba00c0721702d5480742410014a070521a400103204041c5201044a15500600030821303681000c40381441b242e461010b0a100b11400c66002070200e016581592040350381c04000107070666594810010340c0d5410050385605617403942c207916140d03800300c10700d180490581c4000c550380c11710400407240324a030f40320140c6002686c090700e44640908004410258030310312006210340ba09040c040c0c0c40345c00440e2038000850a2503c86070f245880a02c3c2d01c480019002581c2c00000b2410101d80603601c113500d4038140c8040f0f4580c6c40c200e841a0340700807000e01844081410002516400d80c119800f481c01000c1140074141030100c120300303892155607501d0765a00401031060055018008514940744100700c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 352998947 1250 352997697 352997717
    0x3060b061606090c270f06060903020105070f1e030e0105030f01120c030c090c090b090d0201081305100c230d0e0c03030d090b0c03060616050f0105040819020a021005030601 76
    0x1ca11181200c05809103088003410340305e0160b0011603c00c01225410009090000324504071002d0310700d0750036103c06810320000040420811680350415180f090380054441a2001c0c4036419121004c24250300f1400b1882e00b0703070381c25500d43c01542134034810325146d24040e444e607003401c10814950f01103d00403500e076210301074048001050000660081c046900002905181901000b450000c0991100100b64030800140800d40c41d41010360000c0ca40a08008445403100b1080703254071859840080e000340904400381500d074000b500886414100c03a5100050382e80740081581c00d201d0200344c42c0000c04402c2044035414007180d0400c21101d8014402d0310b0010b024600407906540c082840c01c0e02041c0e59501c41d00401c0000801e86420081650710385041d172a0080111b032991082103130328520b4913081d00d810003c00c02c0c10040d5510140e0b040b8001d2041c3c2c02d09180c2880150400d000800d4000d4410000c007503182e100003465200030350010450140a10a40000d4806030300141500e4104551502 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 353000197 1250 352998947 352998959
    0xa1401021207020c13140601050a0c08040803120a180b06040204030f0f1a070f030b060405060a1706010302090f0d060608031209120406020c0f040b04140103060b061606090c 76
    0x81c00c0d449420141c014241003542d0a0030054031030f0707204034804203992410211040c0c51120b02c1340f59a11000c20709020790380c2c0c141c40c1c4003507401071460b2200078800d04000601181e09031010000e0b045c218a920002078403034984005c26400d44000010701d02030201603e0403000820488108540c0180c80034100502c1c264690301d42d00d9498641c440103503404110954100104894a840368a0180340d21400c0002130601d40070007002e1441c280c48a8080613194405555256200c4080360001c2000402d182d41d141150000503040725610f1001401c00c0b010303440018a694041d0080f145864001402c040c2d03d07407038200030448001c41c00c42d001d44159a035088003041c0e03964204010099030356040d288608601c1c164203154a840b40300000c107041c2032410311040140702c0d00040c80c805180012075541c581c04003290003040083c000c2502d03203a4030074140405034a4002050700c5030f0381602d00506081c007140c00c04105011482c8a0700360f0402003100140781c448041081031f030151059901c601d05c0d10100c15a505 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 353001447 1250 353000197 353000227
    0x30c0106060306123e090c07030f1107090c0f0207060203040f05270f2202010f03051e070507020112060b25020415090b090403050a180f090c0f110a140102 68
    0x3042c05d507005034508000d4903091914941e800d50110041c041b041c034103107060360f0040817010300d1652502032010781756441608101c01d219240140c0a00b0b003041100b0600d03614002c040380300307928441d40580180c00011074014808021542078880711988a005949000c0912480301e009040359040200e030702483e030141d00100740115005501c840100310041c141920308110182000402100441541c605000180d8000045000340202414001203e41e18403059688020322481140043c4444a0420011350307040b0001e8841c960003a039072212090350000c503030011500d003406423006a40c01409404076514082d5041440c1842140300b443c0300450380d40c00310f0f044d1140411010404045810f00b070080c1d000c64440c03a103134000c08503101c0501c0c0c28a41c8003d0454400c880048041000d00d070b18a100032050550034a0007403501c5140e0924040da51400ca00c002c12000542000044214580e51340e0740d0b01c60000510034050b503002606840c01217655000c18400c441d80609844e5400f40603021240c0450 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 353002697 1250 353001447 353001533
    0x130c150315080d14041d090102090d0510060f0e010b0703051c05060f0108162703050102040305120a05180a0b0705010c02060105040e2517030c010606030612 69
    0x654002c19805856080143c20b010100da03054400c0c450034001001222201c146e40440f50441000750400354840f000b01e00d0180c070a10170b00729000081044c0340c80c01c0100008902548a40c3c00804019154464941d400e140805110301803181285400501c202111403000341708203031090600514145084401d40e1100d074409069a10a6660f9010455a8108100304008200091074602c01c2403410700099203940328040b10b5401044420b01c070b540c07040303052592800141d9002c0c64868403041e035207161082c040d42c001c0c001226140500034481c008050755005588100304561601424501c00c00001c0c541104049400c5501004a10001404103265001400e070603002d40d0011410f10440c1001a10340754060780564011440c206403c1c81c403041c041104c0c1c40220b42d541075030f0f50080644e442c1c2070b45051181c001c20300705d500108410b000d0100000041981015150003802000d5443d8010340441d8072a00c500e0982c3c10f00c0d050301c400091050b159030860f092090b04001000000c0300b00071454202d0b0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 353003947 1250 353002697 353002709
    0x21f200303040515040305120a0b0d0501020c010c0305010b12100909050c0103050708060a030f02040b1012140403050f0903010f0609060602011d07060809280209130c150315 76
    0x1050000f80041404400310540d071091001c2224105568010305500c41c081d800b0f101504a440400c080607001c1c2c10030f188200300146680c40a4515040042c000e42c030401c0302012942c039000319184c52a0090103694100c55a02484a090114076440d042c0c404800a19210500c1d0340120089528501e5100b1a18494003580060155442c0c081c005402c80b18007410101c107000d00d010030080309568000e501001d40341d02000082c4580790501c0450041c20310015816800744020f08440c0b036040d0b1007000c01c0030304022504c0c10300240c0c19000d44100320300e82c213860107000202c0030400103000c0c140c2c810041034074440140002881007054128801103404030f4201c1151035032651402c0200d25824000d0007a210b801c40411a850b1101c2c20040743c1d188414401d150074051030754001220450b081c8074551280740200c001440509051306104200f4a04c000104c1c82164940d0120310020481100c40020550100c20a0306050034800c80001800f20401d2450405840302105504c03803c000414a0003400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 353005197 1250 353003947 353003953
    0x90b0f15161104110d0c1e051c020a11070b09010e012006190b04050907030b0c0f04080102030106030e031309150308040e090f0a082205030f060a050a0603021f20 71
    0x100b1050014240d4017036500c4101080487d485400704020401e81b541d90b2221141000c560312095110700251244011141c80345d45da2000c43c1c10340706507030803104010140520405a030035280d00c81c0f203072540d180a01003240c2d000a5041c03000c035a55501982400c19820380c80049900390a259880c014034000f0105c40a22038169550301044000030706004003031101c8002c440600092906141c42940c0c0c400512000e060100c800d408611504c0d0844105c41e0160b00f041030781580c80d07403200891401303035200380320b030b980002e15080b1042103402003c02682d5080c1c03201030391100c4070b6103444250400707085070010510b8041e2032b00e83d00200040079480200300500014036481c0c034503c2c0c02e810090411400c480c11001d40c0e080b007141d807400a48044201d8080305114442d80a0300303c00c85041c2020030800b40c00c140d40511843c4000329011000003505403159240d0241400203984070200902610520301c0000e40003c441c001d4140c950245005030b98032543c047c90400c544007294000c007030a459442b0107220850b0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 353006447 1250 353005197 353005207
    0x1203180a1119080c061b0d0e0f06041805070e0607050604110a03080403060225052a0604060c0206090d0b0f092109031006090b0f1516110411 62
    0x4103255120301000c40700d0382c00b03401980b880d1603401c6031541d00003400d291081c000024080410100d91440c91144a81d8804039140b00598010107000403e13250040f81c460011201040320b640b603c0303402c580c02d4644030b070300b0b1401806034a1805070213480050302e2481030100c40e104038681c030340310400a4001c40703000300c0003090942400e040c29403040703001d826010b008401c1004184041a282001c54003260390080c1d0040c0d0300d030b00c4e416440c0c00341d00d8a5510061180c1c14102c10b40140140010b0740390b0064440f41c0103140c0c000c0c503480940420564000c0700d0390001400d0104218441c040c2e00381e0b0500c540064801c41c41c0034201c90000300e402a220780e003143c0c04030b015001e221084c0c0014072490b81c440007e01c020403c00034400a1100101425050320400100024000381c581d1402e100424a02c06451810710a0a07203c0540101500403160058000c14481a402070140382c58010f07020080b407030041e102d151254119034403000d40006070095401d00000c068100310790721584290440717002243c1205480e9 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 353007697 1250 353006447 353006449
    0x1507050922051504060803030c09060a02070506040909030f02010510060e04060e0a0504030f1106040b040809030106030302031e040e0112032001050f07031505100306030c0f1e081203180a11 83
    0x172019904815015130040c010045000c00840441d1002035003211299166100c0040803441c04045070046604050007150024041034140c114600c0e651080d1500c081c80c0d50014070480c22500e00310dc16200b032800e89901004280d000d8080d008030140e0180002c03400e29110314508003503980946404805d0781c0d488007017109140c3d10101c1007447d800145000340340c40e8148941130340d950601402c0a04031401707801c003040030070407010304079002c440014000340030071503903418041d440c0d4100d01166210007642e070b900164510324100445058a6900b0450341c1540d082401d9983c0e0b8103c1c4ea20114280b01c1a840b200c0301480c54185981d880076206000401c0c3e610b0100c0c43d1110a4078080c02e201e050600305245803000d503402c01404c005581c8250b03403880880d003d810301103001d4070a0780d1000d40090a100c07008500d1003400310001c01500c4040112118641c200c0354051060f0070039128441190b08009640c50202072540c0c01144c1019511241c40440440402e08608006203c42c0440c0c03015100c1d4841702407 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 353008947 1250 353007697 353007701
    0x111203040c1403070609030809040e0f010e12070c090b01030b0a031101030c09142e030b03060708090712080f030c0703301812050a021507050922051504 67
    0x2c40c0d0065002d040510725000c2c3c050325481ca175000c014500b5102050014280d02c5e0380d4041520740800744212107078001c4050700c4c14020104034108202c0ba00036125001040c00c1d0407011986141c0d880103408100d1454200044001c1c60403900c524101a21040c10007003a9888600c00e501460140c0c4d01462100d56010002d001c507903c0402c41c0080c07101c405410050140e04002e182c0a00c00152030b400080c20b008580e0710900781701301d03440c0745018080442c1c44200d01d030b06501007000d0340420743c00c41d0075540322024251811142250940d038144d010a40c01d20040259800c6208040c2c0714054047c1841c99001c45800113400840e5889168680802c6a000340350380f114082d90070000d00f40c16030203400f10144e002d9464882001d142c07503026031079001112481c0c43d84020741074003a07000306080240740a060b400a181e60701040c402c000612508215903420921030001900460881d202c1505d0280031006010640c2400b501d500810494800601c14000b980c0c00707198810015494400a01503101c410441 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 353010197 1250 353008947 353008979
    0xb030f03030126060112060509100509030405091f15050f040306020a080a090b06010f111504150203070c111908010f0e010e0606013002090f1807111203040c 69
    0x300c04c2d031056004000d0250390750802032007142c0284021503650384010070a45090300340989809810b24081c1002005503010000d002501c4088440b0f1a0a4480810f001221010400801ca0214040108100d10b81081d50391107501c0a0904000b03043c1203054405003615000380c2e001f80d410b541c0000c0e4003010315600140050348a450074030104020b0348562200211400001c01180c10f00400c1280e900741d60380580d59040307002491108030b80396151440c1c6601041e00050b1002c5404400c5002021034005490003540d00c0780300140c3c0d40c1681c943d52929804015045420001d1304070108010440800312652081c1c00503082d90030002c01c81001101148040302c0341c0c2808160346c0d902d4046005450b4402190054000d1003d291410030101c1e0f144241400392440d03640d031180940101243c7c0c0359060726801603c0070560486484615090f80700500c94020400074410048145400005440b81c0c0111022451140e500c81102c0f55140104000102540242d5040c0c0e24542603170f004004040d403103a2009 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 353011447 1250 353010197 353010269
    0x50711301506010f0807030b030a0c090606090b031308182d0a0807050d0c080303130b06060315040504060f06030c08010e0d050403120e060d15080c10030b030f030301 73
    0x1284462404c0303c01003c10b9009440b14003010b4454212101550f01080340c014000c0d00540e5950340942c0e200c41c10304c01000c980c0f003080d010860600300010344040ba44242d038400c0425144170f180364240c684d00c0c507445500c01c00134a80c04122510113000c0580f503000204402201d403869148000300958032402c40514514181c2c1e104500c0c0682c18810303840046651000c032001500e0300e1b801200c0038a80b9135540300450300013000c98440070080002031155050b601c000e0f58000c905040c119140c1c0301c01d01445200c00c591400c02d500f15807080b00042d04007070788030300e40c468081d20f4000f035140d00c0080c080040e1401030340156259011a0001d2000d10001c1c410755100103400001801d080a9016025000d0301442c44058140c4411000b04114140100001035024600625140d590307610504980028490001c00711003003143c400010a001c1d0300000c162200040090111349640c0300d0319001c80140c07410030707041501030083d087e50300c0f1860020806540030f0403070600e10140c83c0c0d103401c41600000303216000300c0b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 353012697 1250 353011447 353011457
    0x10111804020903030a140d020708040f060e1f03140702011a04020c0d0f03202d18030106050a12020127120816081905071130150601 58
    0xb9009942d400022202064064207003490342031404010382406025040c4c02e2a15180006031000070410b0741030080c01900c1c480c0107103288503070300c40c0b1044a81940d0100369940100030400c843c0c10910b8034800d0000440300a140218410750f03091500f0714503c1060b00c0b4600540c0d142c2d1010180c5512541e50f498811a090b01c0071420305032040c0035265240b00e070000141c00d1151801c2a090b01c2031090b040105048400c0c07045407609044503201c0c10156100740011404c403521410020340702480179a451018000010b21141002801082c5000c15045078481070382c55966904c001030652a1209628000c055141e0120406403482c000540340d4003441c41074600001100b5110400b20401491401c10344241c00c03034020303a00c5024074161078030b845003940d80005a91340e507580c0803c00412800a14084006410030514603480c81003d56817400791043c010b2449031541c00c0404541023041e03a038042c418000c1c046503210000b1101c0c003042c024022a00c000990000c1000d24001301200d10a135030402020f1800c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 353013947 1250 353012697 353012707
    0x30c180703060504020f09060c03121003030e09040507091d010609060614040e1b090405040c0303021b0a1503092a0b030408070f0201020f0f03071209060c11031011180402 75
    0x1046e18910407442001d108820201e81c81d42c44100800540e80728043d0502100301074101403604a035961010721040300081c00b407000e070140900780042c2031409503500c80d000703020190610b181400034040c059481c81c2240b2002d1000c0040160034022040103140c82400046d00b182860401860840ca040e49a90200300401081180303604c07002145611400d80803030318600e8400104021124031941800035402410481030000348040103640304101c070b01c00c0d02100d1199440303408070f6568903040d101040c0d0002604404009400740c0020704404c00c6403500d00080c0b18001a80e40307400d5008060b6240000078032040a03941310341d80924280d00584440417543d415031403d55114001c52091090060048001000f6075085900130884080400c0f5800b0550b4003290071f121100d81c2c0c4c1c0d0010281a81c0c0c0c00b088248084249014500a80c143c404c9a5222103602d54582c94003028808010384058244c81043c003c403a60085d0351280c142c134041c0e480c2402e0740d20100d07000800400c1c1085040d40d0710035881040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 353015197 1250 353013947 353013967
    0x70309140a081c091a091207150e0a090e03030703060f054c08010f0503030301030b070905100306060810051f0302040504050406020a02150601120b030c18070306050402 74
    0xa5545061030f4250905002d408400400722112141603001050500340055a81011800f08018084440d0140d5503000e09040108070b8990f5807a4511401001000c0c00300205c0990380b04865100030600701030310340c0d0100360707562a10b03004a4101c44103011180d0000300504c450564540104001482d40c1088000742c0c5092400203402d41c0e00c08520900c00c1c04440d0a15400401d84102d6612009441d0038440c90030f40266036146450101d10442e040050081c800216200300410040019240060011030543c0e00755520306850b65805011401031140c05440084c45903507940059546100c9580c0c0441c20501d0303d00080d042d9200640983d0104903078441c1440207481c0c49a81d100c0c0c041d1032654070200303030705001e10982c000e11480d0001c5400038105010802441001d0b0002c0079a01c00660803103c90416070004481c0072401524250f000450500300704800084032f4001d03544000c3c1c006e094038031800c00900090400c000610680c94581081410071442c25014071510000b000d081e00c09502c0c0584030310f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 353016447 1250 353015197 353015203
    0x3020c060a0e0a02121f02070b180312070c0b0a05130219091404050d0f05070813360204030203070b0d060506040e0901110a020c24070309140a08 64
    0x3032241e50241c0d03403854810a2981c2c10011800c07030940140601c030060040d480480d4450b1074903841650034602034881e07021500840c0c4219100d040d0000c001c4552601d440c0c0c0c14948440464401da42c10788002d0201e00c411924000c0101c0c02a43c44c3d8683c0c500041c010310380031003107000007801d11209514107020404510b0300000703200d803955030403942031500e079881c9a01840d010009030404003030180f501005501c0200c08441242c065401501122a0207100340011161004d10348200000100280725940000d640b1002034600b11141c4201202e801d034481e0412030f1075421000744901550340754120002c030b4a204110300c103500800400c09514003811500840d13901c030101d120303e0b010302c04005400b010016150b84944064000204a150b8031a07031900c507817107841c8041e80d4400e0203500c0d141910300c060200c0e1044035802c0140f0f4003c3c10036400420100301030b95001155841c4907410014007003507070712007080042140d035200f41c54031661181030a0f817045640100c000300c280030f4040f5100a211400e400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 353017697 1250 353016447 353016451
    0x30b06090319020a0807060207091406150c01090b130209180c28230d150f0b15041a03040305040e131b082a10020f07060c030f03020c06 60
    0x11000c0b520502144042030400c0590fa005180c0350040000c007191407940032070290111b03943c43c0c4040c0078203d880e4103000d003c90b00a44600b0341c407187d582c40042c2c502258001824064541400000d00c035102038944441c01001202d1f5001220030001c0e030b24007149070085090b50810507080843c44440c0c1e09140595598045c0d00842d071284030420409401b0225540d00a2035054140c81021a116500e000000440d03481050700744407504100480d90003400c000b2814105150445580d00350507000040722402003100501400d8070300d466101422158646c00c0748461a2003010203026512450110a000e52510701d284100c0171000410610010a40c0401a01c081d11060104a40d0545401101854038800c00c20014030005139841080f40c1c0102031010700040b00d6021058a89281c08142220100f91010988400f40c03501214024a681040290000c1c401281c0c01115809007500402500c0d040302503000100042082d0880010585d00902c10205059141820f504008c50400103640f41c000c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 353018947 1250 353017697 353017723
    0x603060402090a090c0509101707030e030c0a080301150801080307080901020f1615020105090d0324090c021216120e0409050d0207050a03020919020415030c030b060903 74
    0xb02d011406551404401402080300751020040d180c48800d025010b81c0040746050302c225940071206075018081d01407448904400385803d01c40d136544500c01c0e001072014840151007440240124110400c042004c005101c4c0a211440e45030740c540f14144488002042c800c2c0d040140e003400401449800105070b520a580c005240c6480d0070701100100d181c01e00341425000e06120700240700e00003c1c540400c200c195a2490a00711445080b51010b0b400c1e650191109200c035480590f84042140c07195002c0a0145607148001d00480c003411410a1004103e800400800780c0d1442000c5006030100040e10440904c03814890030002d0008078070b4104011180d0142c0348440c80d214607809988110019901074400610801090109090099444842e8983c00340941700d4444e0124070740c51710210040c00c5982c000c14419460742c0720480c05001d03840440101511580900010802c066400800295481d0310798000801825400008007a10304820205000b180300f0003405042d030310089421303080030780 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 353020197 1250 353018947 353018951
    0x50f070e0a05040503130b0a12060b0904090c0b0a020304080c101e0c0803040b10050901080a1106071202100b1813030e0a060207080f060705040e0702010f020301032f06030604 77
    0x1541c4e04141d0300f103115005040c620f880d0020700201f100740034040a0640e00e0a50342d10030030000700802841d0101c844900a1111303864042c41108500e242542188600038410294095050f642da1108a0385400c44071002000d81c0000c2000d21181c0c03010061049485403c80f80c9040794205c10b40040e00d80541d0402d0310340045044421002c500d40102d00c43c560241e4032201c915680d10b090700300400c40c1c00007a80c02000d1b120445400044900e04401814142c0b40800d015140040603a907920100c101c860300c81070b4012a051003114046400452440c8c09420b19401038400c1e02800e601c0c14048a842c0800c043c840c04103d000c2080846c0b03248070050f40242024600c41c41042542415601c0245804840da44412418070110382542d0100f60764007202c810604903408812000013050b10703480f04441c0400003c0c4244801c008409440701e9458001205000010700400444141810303030380240c2007035070308004510000c8001c901c18a00b041c01801c0c1000138070001c15015000a02a1201400c2544141e07 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 353021447 1250 353020197 353020201
    0x1c03270f03090503030d0902120f0607030f0e0d031d120708030a0f0f062303030909191a1f0f030507110708100510060c08130803120103050f070e0a05 66
    0x5000b00c28400160000034101d0740c0b10710100748401c0c05482812412400f80442c01d003550804d030030000d071032580c0ca0000800382c2115070300c840e4201c004142118a44070035503112012400c8006080c8a2341156512a43d40030480746a4005215803081c400d403c442e016600c548030860a0840b400c0c150781a159021158699a03125106440090403103901d00b414014039004c4203041c10f0513264080c08c100e03100854800401990b40c003801c02c01a01600070190103130001c0107130300307502d20f012400c250b88090100e900306840c207406030b0780700c0031122803480410310034a08540d81c4215140042c440040310422429404001600e040c0060000301100c175820140b40d105d10100d84035500a8070031940e080382000899140342d503100d03035082d5107030041d035280003d940c5402c01003410301d8943c001d44816120305031550302003003c241d6100d1203284d01084030101407404c5140c000c02d000030300340020304814408a003040010350450900c3c0741030108107a44802c81307500004041120000880300d0381e90002240d45c0c001400c1d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 353022697 1250 353021447 353021453
    0xf02030f1003111009170f0f07032103110706020309011406180735011d04141203040f150c0905060c210307090806070c020409030905031c03270f 64
    0x110742d03030b044083c5603600c07050300c0d82800b1b000047e00d03403460311020101c45000e80c5c8001c059854000a0101401416500750605200740c8484278804290072145070004090401000a02d203030f0300300440c00c079801c0c2d80000c02c2c008040802d00880c070f2009411102106582000c40000320403408220880180803002c1e00083c41d03580c01260f02030310905000c2d02c4c50243c0002034a601980d440c43c001c0d00e80c5152b918100129514501008251104454400d004100d46550f241c020340300c80f40d0783c40d9403030901c02d1400001d100d51074600510b001d01c2c425802130403c00c8582c81c120090320340030213410103928540400c041c0c0499200070440100c4074143d404a540394a500046410045021116468111861440103281c00004029441402c2e83d039142c458150b1246949a1070f032000380c80d413100141d40b0700b4182c000340c6015442000710b14428100160120b80d18000f003410501c0c0b48008003d5052140017410304103805004582c1c0300e40d00c1c40780c0b200b4404600c08500d20800c0201070040e000826144442d030030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 353023947 1250 353022697 353022707
    0x7061215031e0b090a0c060516020d0f060f090804050118030204050403020c010f0c030210020d090f0302030414030c0901140d0b0c3105040209030c040f02030f10031110 74
    0x51900800402c040e011281d4000350140300e560001c45030078150b00300141c400e00000c24142d1460340d00641042d40765203804c1c021206500042001c40350100c0c100007540069a540c0c50300002c40388a4481054100001d043c268200e52184000c94140c90a00d0010000900d071442140c0a0315400d013400c48a8040c1c2069522a100707aa41000f500300c0c1c40c00d400d110a0503000200480f50007401d90304e408400e040c180084400030320424009002d68000a5250440000d81e0060300d1000e05072003000640034000d0700c4540550070440c3c020b0b030258000080511140708140e041c018070600540c010304034001d0000c081100c481051280e044040301003072190076190381c1e4099140e0280d8000e20702c01ca0301c2c20022003403030702c81d03100714a06c802113043c40c0c40044021152802c6406201540e0f03801c00c1c4164a48000c3c40081c1d032100080660600907411409000d5550b841502c084c0d10f8100001a12454045580e004004000c2d0600030500e60980b41000000c8141c0c03002c007034105c130540740c411801c1d100250a450b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 353025197 1250 353023947 353023949
    0x509010e1c05062505040b030f150303070f030e06041a0c0a0804170601171507050c0304090506090a0b030706180e0403111209130905160f030b010807061215 69
    0xc00c500580c0e0502142d000035242600c500c1504d003001c50840f61060600392024400c0780328a885041050001a060115035807a40b5132042410740495039601e042c500013403c5901c02d0001310340011401d4030600600d64404008a2a4241599114038250904805203050225a01d9202294400040c1c80840700b0040c490320030707225401001141c90300e450381c0600f40211024409118684222000001c180e02040d10710000c1e461100003420620440c03480d00450514018000014040c04100040f40740c0f0003003008000400500314009000c2c20f109040004010f00940210107490402c1c00c2480e00350307408115a07088841504044518000c04100c110f005a042d50051014502040421041c10341110039806008128003d07140d10b100c80b25a580c0e0140107e0200c1a007120b280d10b204520aa80e83d440728002c4c50248040300e00e0000020140c4440821030f41250343e006480d001d0410400060031101805026000054110a0b040110090940d85c00f030300e12190264449190300b41603400303510088 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 353026447 1250 353025197 353025203
    0x90609040207020d06060f0e1f030b060d15020d0b0301090515040314030c070212060f0c1b03030702160914040201080411040f0b18010819030215100608070509010e1c 73
    0x120070507a407101c116a2030140da10800344080d017001e00207a2000d80300c01c2718405650298a2049099085803284c0314501001003070301d038002e1044c4003040046111300e8040e410003246c2c51400b5075a49540a100000d0b21010038100380246e04102d03040f800141c0104802c03a28a1042d8540b0403640d543e420100d509501440c00380d004004004240800c12a02c0801081654001d54501300f1003d1840e9a5580c0c8a90884010b50034816803408a082000c4c036400400c0905a0030820000ca240c42d4009581594000d0314054007581c0304900c1d007104ca00c00c00342c8a074010280084200108002000304220982c40280024100b00461002070200140c60b4101720030884043c0040141c3c0146503243da0003040711010a511540b20040c0c9a0324414040ca03103541a0344408001d4440079003640c13981c40140002d50300c03c8055000301c2c2010316202c0c9903212024841d0a14441010b0128070b0400c02821a10010742a1400c0060402060b14a40d8000305081019241603c05441d490310302d011014607020181001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 353027697 1250 353026447 353026451
    0x801230d0606080321040c030b091219080603070e0106080403091d0a15120b09070e0c0d0c0504081b121614090712050a1805030d05060402090609040207020d06 70
    0x1042c41d0300004007500203c0396214099400c02003140060a0f444d4084078002c00480c009501480054440b0000307a40283c60001180cbc5540c42e03404c0b402215812422110041e9a10510180c0000341c0c4402216009002038000d4000141400b0036043c8001050249400340410000031030b04061185d072030840100003000c10541003081c01500018241c9040d0740004910307082c00450720102e0444080351040302d20f8600002e034170b81d00035501c184148030000c01c00641c0e8020400001100030000020f42e00c40e08a2240c01952071030b184010004440082a01104100d0300344803e01c01010700140001c80640f841449503465502080000c4004610360110701840c000d40e08015074110070200c4203400c1d103500081075808640d840060221941c0e0442d00d540c0003c072850118108600b0070b50005d50000781e5040c0209880d040e2800101c5049401001210254400186e02c0490486407090030b8104600711010352a0024801c0019480c0c011011401e00c966800101e00d4110341c1c0714480d02c0341d15503110f041 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 353028947 1250 353027697 353027699
    0x1091e090c0201020a1e270302030102031e09010b10110a050f03070c050306060a0e0a09020306072006100b0d0204090615080108010c05120705090415060306060801230d0606 76
    0x100a000c0d4100f42d5180000c0b40d00041c0d440c81416811121802c0718559507147c0500000e0340400640050070f550360b0b18a030396043c41d03010002d80c82c280020341c4a102c000d00314a0503020540b110740182c5a0052428034240d142084070032107a80c80401e005070135070062409a80500c4108a050f040c0794180c2c4c0300402a115181071540e8955000c406011114042c40d81400c1c251342d41c001341505d0304e00865005030720264841c800e100300380301074000d59080010030320f00041d500010780c08240740c0300c0305407041000300301c084181e809079140c0030b914400601c1d8100041d0101c2e04010354180750034a039900a030386030181c0101d110070215801d513040d40c0007030607a1003051100c81e50303607a8405c3d0340741120240d5000003000440003203014981402505480c100030380c0c50340c1c500346540c07040303d00d5614040c0c598006c2100c20044c075640350759980142d0b8400341c4042c0080c144980f800c2009400c032809a80041c091140300707001000026075a880107403040c04528901d1020015020002c0c0c3e4906080c4c4008100d6880c20f48 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 353030197 1250 353028947 353028971
    0xe0601030e062503090b070f020a0803090c131538030601170c030619050301020d1b03110d0c030902090f0714090f0f040b040e060a060b0901091e09 65
    0x8000800d403100503c800080d0300300a8228240d031050030024005202100116020b0361042140001481c43c0744151413050f41d099079902c0705580140d540c400c00c0d6000102c1d641d0b203498030024070b800c1142c19920401c610041c1c02c41c030350300c0318140c0d20605901c00300c4517041d258229411050b0b640740b0901c424646080030618900039141703400980307580b030029a010b00707440c00d2a460402101d0250388800a00342c1150b603000c00700400c80140e90305c21016107021050015140e01d090000e42545c072403400300855003400740c0c15a40009480c0210304010142480c0c6464198400b1740304942c8035004006c4003040a030322107001a809002c261a0003901304099204019406a4135040c540c02000d4035681c00c07140584031500c5400382d01480134041d60001d203c4821144074548900310048001c80984003042d0a0b09003030010b000c66031140c26202c07658200130200610003900e031107258080c1200003000b5007032410071300000300908101c2c0074040802c440040c01c1034007443d550702c65030024692aa8144402100c000c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 353031447 1250 353030197 353030221
    0x10f11011401080606190b0319020a0c1704050114090f030d0503100905010e01271a181315061e0302010e01020f03030c0a030e010c030e060a0509070e0601030e06 71
    0x1100b02c0200e0f000d2180412903d11b4020050310311480c0e010a9030f11014140100702010350700240200840b070a0910100682c60b0050000c0c2610b10101d440f0818000350a007849410300540740da00c004440b000304402e104584e01320310f0120b1600200b80300b00d9100d50440000c10401e41c21440000e5140c8a5401b00c0300d00694800c0c015031141e0301040d404c41803990345900d10070943e0001c0c09107010844640c00140400f0f0b21010391a00d07030004d1140d07002e504074040203400c0103c502081d5054888401003200e004141080d014074403102c90b61800c8807217280342c480148d86001c008004010040e070b14013003046030808140c0c0c1100d005010800041d2019440700307880f1140d02290361004902103030300320641089039800440c2540003111507200ae5480c5903546800681c080d4000d0b40320b8414195902380061040740e00b4840c2100002007030724009030842840d50650f1034800c008008500142c14042080001c68000c034041040b80d0311480b5040a50303d44000580c05000040300341065031084408002c40d480c582 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 353032697 1250 353031447 353031449
    0x7020307090b19030201020d031a04060b0a03230a0e03040b030a0501090e03090f060c011e0e070503070602120706060314010506010905060c0a11030703020618040623010f11011401 79
    0x4407400c1c60659084820b5400800e0039204c0603002d40c1003404404003990190704041c50000c82112000e4486c0c0c40200054100c6a03150400311503400c001c07401002c49030701441b0381d92454000d00360000c4940f0b011000c890390000000c00d40710b4401d0f200c3c100204c80ca101001030f200680328200426071a4608051020000c020034445c58285a007450b181c0100200044200c4407040e00103080344921201c081c0601509a200c00b1404040f0b6590350540303040d0454184070000c043d051a07102140500840b002c251074090b42c3d40040b403007a04214001c11000703400040a1880552050402e51520042c0c14590b000b03160550001d0010050b801185100760810744c03020788600d0090722220070454030380052040d0741c0560310b0b50002c43d5100481400210785050700c100a014001070480703c0140d202e83c081a003603000196005913400d50300d10007282614160164001902c0000003100f100140781f035600f1724004c85610018180800340c200c1c09440751107403121207462000f070741c024096081003035092b003141ca1017 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 353033947 1250 353032697 353032699
    0x161412060f04050c0f10030905070906140324040b15060a050c010e070b040e040c1a0c0d021f0c0306090c02030706060e0114120a050613030e010306060210020702030307020307090b 79
    0x7a40080e072255142280301c05c80d00c0c801c06020110b2034003180c1c40680007405100d2301550759110704031001810100c3e40c0100c4020304240c03055a030a046182e02071514102242403074000540034203a00d00c4940400c11406c0c0e900c541c0246d03000c4465201c944000400e8090126402e82103140054501400e0360480010041a0a030303400030001c50030b51981d8107403a10442c1c0070f1042c0310f40f800c000402007a450302c0700c00c54000c2d004020910246654000412007284c0c0e9410100d440381001c03c00c2c030885841444569003154260000e441c0201c00180e9404151070030403040c400b129a1744108049240c400d0340000090030800d4410014100551006540c0c0c0e0481102111004d0620303101081d90410108524106c400d40301c01000d203c0b10540403c1000621021240c2c0c49202d80250840070840801809015040035280035405030140e05006152060584803241854103040c82082100c0c0d001640031140620315000584807201c51000a086104602010303525210f61080070a01c0e00403a44a101c803004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 353035197 1250 353033947 353033953
    0x806060a1b0326090304121103030412050f0309030c0405180f0610090902100c0228030308010b070507030b0601110a0b090c100909090c0e04060c02010c02161412060f0405 75
    0xc0200030035a40f1408a49030b5a594000b40420401e001728004125409032240110104019285000c41c1c69900030354040420802008442000d010040c0081010b400015020390b2401e00f01802080d81d56581c3d29150f4002d9940c0c1c00007800c413640d2102e050031310448803003e07681d032180b409221a54400341520812100e42d500d80c00000c0e5200b9030f01c035038210168042e000e0f000d1a404e40300c0c292034621450713406a07005001d6000e1340f003041202c034a54030040d894201d00d907410301c0d04600b001403c3c064140c00140582d0f00410002c1c010840018100c0112075018a4484d01a6176290049412a0140c12029050303c1811000c408100c210000140b181d11400c045401c409190002c0288481104001d04089028031409100326030840d01700660090080b000300c038002d0341e20130752255a003800300d40a48200b0b981d40a809011642030103000c0000410340f008141c5d140d000e10410700d080081d4442d1119034054001c14142585804541440c03000d001130030f58190f403400c403d0400c00143c080b902210180 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 353036447 1250 353035197 353035247
    0xc030e0301090203150705090d080d0b0d0f12111002030f09060c070b060a0506070302060a0c08010b120603100203040321050705041701090c090c0806030309010806060a1b03 76
    0x414140b00740329200390000e0051801d03d00c01040100b000d0000382150080210800400107603445034aa0305c00b056110f2905030380e407665205a1203044440e405040c903c10403d030005500484ca040492128070707500034000e0052806040c80c00d540ba59078469150006008000007044517808541c050342c030031142c9030085803203076071204040c544641084030800c4d101441800004003213101443e240d80d0103d0040c06a402198450300002d005410860b400c0b40164400800c104148019010300691901c441c180081d295051001e0000030307000e002c0c0400340660604001841554041052544e41d545035070341103569003031600b401810494400301100c402e68004c0c1c0c03420751041ca03611400b44141d540f503943d24145814804510140e610300420300b6669900c0715074440c0461603051803039004282d2008005515400103001500d492001440e4511a41050000c2030a99030054801039200c002114556070301d6031a004140c0c0d8162069550343c01340d4a56030742010130190005040341c4c0c00d00f0031000725480a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 353037697 1250 353036447 353036449
    0x301050a140403180e0a051609030203100b030a060203130b071103030609070e040609020c0d03060509040803220809130504260705011e0605030706020d08150d030c030e 74
    0x14804240d10340201c040c40c4400140424410654462204030405640b51250380d680c202c042c0e1848161121180c4079514410700025001214882604a02c5802c000544600e5900044d460305600090f000100740c4075041600c4640d42030040c048070b00d030700090864483c24184030009074040441c0d8212241c08000740441e00c8d07079000c0c20000c00030341c01c040015865a95281c05200740350f00050403600500114040b42c42c040d540d40c0c0558405403c0010f0300588600c5a88080d030705d0001000d05410505203004410301039a1a45015180d0240e00080c910341d0341c0d220310355000703800d6400302c44c52860440001d0005040108100080400361011504507205c0c41020130040308451081c0ea0091003021441c000a20024007003400c200401c12500702c46003072002030740341e8500352056440104038900e840ba26082c0c1c070081c20311443d030141100354028a400c0741800c402a6a45981541c410240b1448400150081c0c181400341c0b44503800143c1410f44410070303440c000c1d109001e45d8404502140b0519603440e03407 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 353038947 1250 353037697 353037701
    0x60606090803030f1f05180f100b04090203061504030f0b060f0d060915020403051509030a120207150c0c1127040203070f030308040302060901050f06010513050a0f050301050a 77
    0x1804009060481c9441301c00176100e18540c550b10806419000c030745c0c0001c040e624000c200c9292900c10602001c50300d031960354100e0703800c0d000b8094513900d90440418051514520706450035540607110041c1c1e25140d0301d0000709240128540d401c0b11460000d40072003007241401c021005c0700e100d00c040888580341d07102001a092034138203081d6040040d50003501c0101c2c0943d000841030b00d01983c544c5103082907d56a580582e40141c10a5403ea489907500528000c0511b060035070200e10700b0082d604000b01040000c141c00006090344038201d40100780203040c0040c1c110440368a01c2082c03404c0150114056024203c02503042060742e0203010307001403c3e01c609202c01c61300305411440c0005141c0a8544045a000c0310001c0d00aa8051040c20310105206406003403d4000c1d600a45880c00e0310f1500d0300c1c000345402d00090071400e950741082c05102905130348190300d80d0049400d0070320b0f503114880380342140301c011b8803588090f0748001c07444000105860030f01c07082019540d064009000781e0350340f01c0031602 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 353040197 1250 353038947 353038951
    0x91806130c29030411060c031201120221070b12060f0a1a0a0306030b010b03010e25080c071a18010504050607030e070b190f0809060406020a1106010306060609080303 73
    0x2d916880354014070000d40c1c0d182c021035015106100400450060101141840d00259281c03201a8000180c0280a154100c41030b4014200e9507081210200a40e010580b8000810040d040b100000c41d050201d03554240000070107811300303c00560321401d00c01c070342c5000010140d03925801110680402c10030703800d003014040103540c101200c28242540361080e0110382e500c106503020405903076207404000148190703400740c0202113402e00319480e9410504c00b1046c00030701034036031020a8242002607003d00a09151510060840d05060340b03580d40e0301003401401d21034544000c02044054001d40d04d0100f002490390b02801d04105111401070400d50700c9400ca03041924043c01c0380d0b20100000301c0c400d04c0f98011a010014407001e44402950354150b000039a00040c012219480203084564046a4001518030500c809071804910a081a820f0251100800b4002070031042c2c00056002c1000c0c0900341c84a009c03a00141151078035a56401c1140040009010f0003000072204030001580c0c56000007524 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 353041447 1250 353040197 353040239
    0x1515090905011d030c1203060a050a0b180d050d05090616030233010b030a09080c0304031104020708160503090d0507090c08061f0c0c0303030b0f010f0e091806130c 72
    0x105003106509221b140c035810080c182544003081d6100418035448864681d802450700f402c0e86c03030710307900d101c0741e82e07040e0040100750640100644c158540108100144002034441e45080c82b0b0fa4400904022551601c04d5101042051080c601c000d410943d00082c00c2c202c4d14070507030364605507500c500c1c5c009044610803894406d8008a090040c06048505801940c2000c030b074950000c3d0390b803020755400650b60002c1e0b442140715040031904106002e8059850b0f10806012030b011803074070351140c0d42c8407403601a00100101c141e45803600081041420411165491402408a90304000501e082592a0030701c0c0507040c3d15601700a0650002c5001703500550144500500352a181d500300180f41d080450b081c0d056408202c81c2c0e8032004042a90401c012001d9402540d000c0780c8501944180620407104286160400003240c440c2d034121588071961218900c4100c0c0c40c10b94949800364005154804e81c00782e05128050003081c04810241c1740000c0661030701c1400303c18130755a506c1410542030302c03c10b07240d2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 353042697 1250 353041447 353041453
    0x1050703080c070b0106090e090d120b010908010204180b0d1a09070e0f0115080f071b06060e091908040506070501021c020c0c0d1515090905011d030c 66
    0x440001e01030340e200c56000003a032110354100940b507158000c03021400e80c004804540005401d01189590440d07095000315124002d0016100558006280c20400c440c9030303d0265071215141c18a80c814140c040c0100360380340c000e645035034440e1550204182d180410b0b85580f07281c042c00400345e041241d1184809504601d0040120071040c0c80c40c0583c01000301982d10034043c10801045028550708032900443ca050010003141d03041644644034400260b0703083c0c0a010940c002c0025150b22600c4059100c00c56291140d8441030610400d00c214108c4d100c018099810160042965070030340355501c1c4220b010744100e4296401803003000428048060001d040c2480030007080c8100c2c10101e006050092180e000140741925030a10070030b4190301480f2100a098000500300030012041080c080d80300710803035100100c142c03290b4070629803070280b03640c6425950b10b03003248020f800c48500011009103403040080c000b00445141c41030013080848281c180741c1c41c0300101212000030020503030300920752403401 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 353043947 1250 353042697 353042707
    0x1009090809060702011e090518040c150306050301060b121614090d0506130210030606020703020d0206040b03070804051501050907030929041104020319050402040f02180f06090105 79
    0x2e0107600c0e0721985090307040c800c4c000344c26002d070705138406225954000f540c1e507042d129040c00200800c1d0049400c1c5182d0080f403480503c004504108803240c103c450344800e00b881305003d0a000d4000d880300741d10440d490751034013400045c4412390b0801010f0006480388446401e039258601b0042d142061640200000c02800f943c0003403200312802010a142d00601505201105a0311189071080464000480030225802e010460a1a112090329a0002c0c2801e102d11400d1000007991078a80e8440a840341003801e180b0780030364440d1000c90340a0540f447c001c0d9039a00e400c040141c4003450a6900712894403400008913120840901070505903400140b51810b1604c8019044024001401c001e40d42c0c2c90064060441011584003052a03da807003041e03405840c609810490268654540068003c1b401002041004061201d09041c1c00740e10343c1001400c3d44581c00803400524079a5203c181082c0700240485900d080c5c0021289202021145a48032007180005c2c04128091051100c1c041402400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 353045197 1250 353043947 353043949
    0x406050307080c09120c090a0501140648012d060801051303120501050d150f060f0504150e1909021005131406030114030a0c06081009090809 62
    0x81840e8006000740703c1642080304110001d50344040c0401701c07455950001c0b40d401414206081c0345a4040300b400030802c66903141c0004400c040c00c00c851620320454001400c444c0643d48151114000c406601c90303003d00d110a5074144001c0d0300f44903142d000200b841c246014908905006001c0f400d10f42100e003000c0116440410515107c1d40c02e8138903951502c80002083c0c14000748969840307600180b5803941e0111980c00d0180290300154000c50956050900600243c3c4820041c950021b43c0300140703a08040b19600c010b0700400301c0000c0c4040d42401c0200c0001e48218459110f02541c00840707007040b0071138181a91200c2e1440911810300c0b0034080000060502d5040300207450052205800800c00c0390055001404290180da040e0000ca0400314140d06078506e805022401342c09101d0384544605507210000c3c07800c1c0014407400c2c440d03081250304000107480c188404080700350f214404080749515400060094002296102000d0004110019000c4d04c140181980309401408007468110080 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 353046447 1250 353045197 353045207
    0x4080415030e0f0c01090902030603060103030c0206190905010f050a0903060b0111030d0501090e0604051902040b060a0327030c060903030902090a0605040f14072003040b0d0509030406050307 84
    0x4100d030000c1c16624110071190350b0081c491104480c980c04080c003503a520650002d80a60821380002c4e0881c0d20500400c009610009860f41c1540e402d402c0003030070b030103a078400241c1c607100d00716200b801900c249801c11445a0131484103019140c003600c0b15450707031142601c11203280c02508861000103032180810000f1407256449142c8208041c5001c01d82000100c4400340b4651110002c00c2c0082d80d5100104110b04140c8030b2400d0341118807001d407000c0d003025101e066a4004610301b00c108000d0f0200d4490440d03403075901500c4540c0014004584035040700c1d4001e0f0080008000304002d08210100c0f401d400da81600342070300e0315039154480100315480f0781c841c00e0041c03002042c02c405040d511091007025a68140b0f04900c04c0000d904085405800c0c00180400d4445104130030131300034100340e40310400b4078001580590108103032522100b01403500140071064050b04036800305ca800000303030206a0040ea50000c0008801c01d0400b400561203506032540e0320311840c030640300050301c203001152521f07101d5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 353047697 1250 353046447 353046479
    0x1081507020d0c171602040c050702030a0822081c0905010f0507051509030d0b09011a0c010902190501110303090a030f021c0906020c04050c090d1e03080907080105040804 75
    0x241c3c0308195540e00300c1d0542c02d010740c40402c3d101c0e410041c6241ca172046151134008c0c2c00080605184c00350a04d01c0c254007080d500d0707503500d00003445010041142d03c0740e101d0300b1290100d68405e01144800a0b6501c40d60030b41c82c0c02c0c00d00300f106200c0d4014091110410301030040407080b581f060751055840c4400c50811036407a007110303004860ba4010358243d0103281201402c2c403401256000c01a580e034103003503041b5008a0b040440c5880c082e0031481d00402c50625050b6080c044400c0001c0020b50b07845400c0009401041503000c02540030141c0c4c807046070220551142d42c41a52800c1e2182c01000c000c69846580d20b0008454041d495032000c00c8000000f88a524031800c66015401141c07007042ea62400184031a040144680004200303040800c0400d5041080040c003101c00e907801c01c4641880300541d21140f05034004580a000c100100104000c060003184201c3e0759242c84031144132120f40b0340103100b8802511003540382d115004010480aa061081c1070103280c0c060f503201d00c1c0038a030000c1c801a0480e4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 353048947 1250 353047697 353047703
    0x3200610050f010c061103010e16050405011407021011010c02010204080307030c1e05151f09020a1809020405010e010212040e0408040915080105010f08030313080f040e01081507020d0c 81
    0x10f11084c0400091050041308104011105015129810b0043c08105004002c0c900c000b484022a03602c0326860300041100c058030020f18150000289102002c442441600c0780290032900d04000c0d401076030f80c48030482030f1020410303009203e488a2403008a081c8e000d240030341c0c0d500740c0007040741d840024010000e904055100d44210002d02074010012880c0e030000369800d9400c0c6d001082235019140c0c0120450754000301a49041600c640125108006800c89014441c0030382d50001c2e401c1c5909015090f42c900203001040c220119030344030300302100690881c2c851180801c404201400b40756002088491010366545443c60500d407400c181420540c3d0090010b1b10110810407001c00c54449500500007050482c42d5101a05031601510300c0c03c4070b41c16440199144c40314141840510804000c490b0080e8603052500d10850203400d040800f031003036002c0c2c0e0b0754200e00010300142070364420544a04903011801070303542c2d020048249901c5a20126945070058010070704403401540203c06801d12240 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 353050197 1250 353048947 353048957
    0x80c04091e020d080307030902040b01030e150702031605030c071d0a090606050612070206060303091305190603030f12020f1b01150801061703040305060c03071b03200610050f01 78
    0x500b0380c075181e03151783c0151403000001ea100d9000005600300741c09400c1c40c0800c2864100002c1561a000f02e4407541c80c0b000101c0c41d0000c190100301014030030026549040240d00c4541440002d900d410f680d2a4405072001e0014010400e0005a01010640b01c06200d001d1100780c14181d618020b401000300b00495040f12502d030b0358180032881d916400c010b001d002c03081c2200e01c50306082000340a490000c009180e240300f580104001400c2c1c2d00e95145041e1081242d40f004a5251107a00e110b0750004101230154044c14030b85000041416400b404941e0f124850b13071502605200c0d48610381e001d0744210741c0d80c0f1605980c108250860480684c3c4a801070580c0c0c44000030b001b600042000d6200c20a0743e00145160307440c0c03981402036001c541d1610f0340809c0100011450030746140e58103520b9510080c4180c1554001000281c610340c06030b00340c403c4901301c2c8201040c2a2030b0514014002800f0b8480001d0460034000b0109460740c0b001a00c0c40c001c44503000520081032800041240000c0e9374506281041 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 353051447 1250 353050197 353050219
    0x120c0a0f110a0c0603050105040e011b0f1b060c1701051c081b030c101e181205030f0c2809030605090d08060a0609030f02010324080c04091e02 63
    0x15041803c45000740c1031365a0003050320352503c4104030949074076207501c28083e45000c0061400703861030545e003114804142003281603003000c42810307640c4008512050403001c0d1010300610400880b42d1103001480303a40e480d480c0c3d40c0b61407115150a6101d09000700c64000a07803007852035804513130140e81d1003607910686141345002240d0810000d080d081084501c005d070b1020900200343d031424002c240b10f00708100300400100c040f04809041488260550586055944035007900340031a2051030360602d0b0304107041c0729640c01400c070300900700d51040341c1400d400c1d500c1c10f01003980c500d060720440b40740e0884044218a0007450a8205220b800c0100003903091107003816000001601501400d07100710615405010b84400090019040c1d02c401883c40340f0510407103400f03004a6800200110661350000b424460810f001d1006074010124008520600e500100b032420032250002d130035000f9030301c044054901000b182c400b400150343c680c807401840c9001d00e804003801141c605e1400c0800d940014042d46030742c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 353052697 1250 353051447 353051453
    0x303170a1b0e2803020d0f02030f0a0605070c05030a11032a0d080c0703030f0239120a050c070b0a0f0801240f0e090c120c0a0f110a 58
    0x154480428003012424000302d480c8a45001e00b0a102d000c220101822080400c07007030040820306003030100a00c40d1380c0c0c40c59203c081c00a4440c20452855024045030b15141c9440201a40e403070465070100d4502e41480c2c0080c0e581881111001d10266105009504100c9055419660300d4581c048111031480107000c062070301000140c09080342c80255100ea8074601c6882001070820b60340740303c0f00041c00400820b000d22801501c04440c0d40f1505840e00190400101c140c0c400603201d100d901412401c00817016010300e51481d0500c03051ba0384518802814206a2a01e042d1180000300b0844c105405c180040300c180d0703000300b00906800148909031030010f031b110100c403c1150480404240022807460030107400c0c6800c22011400350005400700c0403090300e2800940c1300d0028801e209000c01154203011546c581c0143c8000d40d0a031002040030407940380a19400308150030040900b0040d40e00344010840d100d402203700d0310025000d80e2030072406200b007501900c52140750741c9121450311a421041004c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 353053947 1250 353052697 353052731
    0x10c02060a0309050105060301020703020316150906321501090f060905100504080303040f02010507020d060f1d0d0f09080d080601122d061706060a06090303170a 71
    0x405080c2c80000d812810782c1451821a500140258000ea104015130004aa0008140c9210740c10a00c034008014840d03190040c501c10000084050132801c00700c1800030400b640d00543e400003c01944001c524140d1150101c00500d800a880341801e56400864504001da43e0540310714841814081c01007543c0300e00840b038a40d0395612034000504030480511281c909000401c06010003458090b05150508a0103500e030312000d400103181e640301c245c48500316406041500c4000344c009200ca480c0d0400c500300744024001490051303c00b245030242f102001c1034800305569031100800d0080403006405142520b80010150b0303440288110a0703000100d01c0d07000c0010800040040d030702e1907480d003850f20014000940228000400d113092259407614000e65800c41c180084201c050f5203422404d00e008000148880d402600a0846500351351185940002e58140140fa05940400009a0318070040b030383d291700383c00020002010424441e181581c0c403505650004120000010904000c04441c00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 353055197 1250 353053947 353053957
    0x501111603170f1201030b0105010f020615220501060f0302040b090f030c12010b0f0108150d03030f090b041406040302060f100f03110112061503020c0120040f050607170702010c0206 80
    0x1001591382005001f002508070034140104001c1c00c01001e241e4503180c0107505c540c00142a002220b01c640b840040964841c80d074a1100f00d80110003007003070240e04250401414090091002140001e90000c41d07082c828401c540841c0c1e482000030342860307111740400000f150f6003040c05501d84188105030078169125100003004030042000007640f02a1002401403044025290303a05100d44641000134040800c005464400d81c101e58801400c1058a01034004150340c06450f04c15519128241d001c00c1001100c8501450103a480c00d0400505440c000b99034000844000b00141c2103c3c011038a540104840507070032004c020480d0311103d44402c13501c5a0f000913980261100c0c0140c041c2c500710f03960409001c0800700d1660300180001814028003a1f0a00e03000030008003019400549815908070a500c65203105001150b00603031001c0840c080742c0c081d0414000e450f204840000d000426251220071226900d5200f286c0e8507128403c181d50300c0154119150036410700c108000003100603500c00d00144 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 353056447 1250 353055197 353055217
    0x319110d02120a0e0c09040b13140f010522020d03121104032f2206090b03150f0705093007080a020a090509070b0a090501111603170f 59
    0x41c1d0b1a10b01202c001e0191412440c102103250400e42d20800e958407600c3c3c141d680a6040710340d100f02e503214075417000c0c41244e0742440038116001c0c101058800d40804540e0f0f0080d41a080024445921038440032541e001c0880c00c4001506105440c001c018103125104800c1c26000e4240885c0c0310881c2042d80e401d13100c411003840030010700020180208690750300c407075103502c02074400f000f580c803c0103000002a1204120032803141480a400c20318031103543c0c0101204055501090003042e9071641000c000c0c00c0c0c5491400c0c803c1c060301c1d4102039160b80e060003661042900d0000182039072074222083c4e0782030344114850303a08117400311420540c01406011242031a0040c03801d401c0083c034080720003810041c0603003000366590882229100982d441c682c1c0281556114107001507141c46000c0150301e010700d42d5100400721403012981070013984c1c02140020480b882a01e0340104000f41c100440d440b000d0704409841d19030503099040c000b00e641c0c003040c00d444440d0807180d2441d00070055440c603116002510b102c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 353057553 1106 353056447 353056477
    0x30e0a03031d0f010501030b130305030a1a1e092a0a020a0203060c0c1018110105090a1e08010c0807030203060a0b04180c050319110d02 60
    0xe81549868a42190207503a543d80560f4041c0009100c141c07000008580041d4114160000081d5200c2c0e00da0394040c55941d80045600c02058140300c005400303500700d404c910aa03103a06110030b0110b40c40781d15104003624440c00b0000c140f14010903200075032174469003100f201d50681c4141e10425428500c0a0b0b00e035102594100d103082036000c4003035410b00c110006e12032003032a03030b40007018500a00815103200c0e0f40141d09000c1900e48441c955107440303a0802c83e000c082072074230803003d650320414544686495204c00018118200390b8120100c60b00c5c441e81a4500890142d00600040c19400000d01070300190440107441000c00078410400d05400000044d42a03482466400140074441c611548864540f1201400001c10545d00302000e807402d40c01d07a6440f03008200303980c4510ba00038042c0307102c0080381d54800003424041000000942c0c041c48030b014540d07050b0020f044984210310344 = true := by decide +kernel

theorem cover : BRFrame.Cov 352877697 353057553 := by
  have h0 := BRFrame.cov_init 352877697
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352877697 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 352877697 ≤ n) (h2 : n < 353057553) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
