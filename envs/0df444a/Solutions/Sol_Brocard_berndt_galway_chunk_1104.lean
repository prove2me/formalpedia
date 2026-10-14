-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1104
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:15:41.540437+00:00
-- url     : https://prove2.me/submissions/35da41b5-f184-44eb-a28d-c90bb53e4838

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 198381294 ≤ n < 198561151 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 198382544 1250 198381294 198381301
    0x2010213140a030b070c05010903030b0f180c090102210c1203131709181510020712080405060f0a0210090f060b0307120605010311030a02010801170c06040b0d0f05 72
    0x400b040c45070302000c0c0440c920400014000b5025032504c5550361790203c000c20000f0703607a00713009004020303002e100d92146a10400d41c4209142c140e5800300d206d51885100c400507154410021119840513441070f05500805505480c0c051104441842e40d14103001c400d81d44400c01b415070390800140703401002c00005c1c240b0500028040c50403186200942c0111503170307000440e00020740f170980112021701c0d0b4050580507505071104c0d400c02c0403a010706401c1040800c0000241304001da07480f05940040e0040e031000b4410000064140f81440c40d050260090900c0c1c540c44a004c03440c60340c0150304603403509a00095000d42640d0400550706124044801003080b4000383d5038000e2142812040540180d03215080d140705070350207100d50342c010b08800f00c20040701c2940d0b11b030510240100b4442039a0381c099105130340c5c0c80782c10017084522900380d05035140380040c0e0812280c404030401c01c8203100c030280300e640b80c03800c9141c43d040018000340030309084c440d84980307105031140143e90940605c014414201020b1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 198383794 1250 198382544 198382549
    0x50415020705030a0c020301020d0c02010c120605030307032105040f03080703050f01140301060e100e09010501050d03081807180e161a070602070b10150203090904140a030201021314 80
    0x150f0300051845d25103000c06065600010b130180c00390000380c0b0625490801401d41c039a03015400901d1202041c0c0382d032484560384006440440710b60303114a541640041080c01c0019204481421221039405000d020804c85080030303804443c4219000c0728000f01c0b44240400389904034030b1203907007d15540b41c01d028501d02003600b210fa40341c040c4654488041144c1c290341c9036a034203400640103060342d402c441484c0d2420000440e038101c9603100e40071495000c00c0214000d0501801030303d043c0c0320040c00310300606001e607a044036550002400507020000b8241485146201801000000c180351400308a00e692100c4807001200d2140d03080014550200c5e2450442c07070b030100071070400c6079803812041d60444110354020000388103502004087c5440000c9800400c06c1d0b041806000d0040b4410440c3c8890311841100020040304804002690040c44183c3e5a803030840181c0e40e1061040242ca2100015450154a00390003a481100580d4000c1b03200e034030150650610000802d580c8005050b1030805102 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 198385044 1250 198383794 198383797
    0x308090c18090102070605150f0105090f0d02120616090806040309060f02070b0705150106090b09040209040f020a031b09030206040e0901110c060a05010b030405030a0c03140403050105041502070503 87
    0x1d031100d0700722004000910b04203003035041e80da83d1a00443c0902003850620748200c40181c41c0344c1c80910810150160101a52060054440c1901c000c1d1140b143c8412070340412802003001c0004070313803040c0f4407030507041100000c7c002203004070181607101303404554004000c1d0a508154101140c95400a820840469840300000e81103c94034204540c201c200d002d0100d00782707000c0c1e40107401c421400140440802000240030140310310b041e882204640d0f22400c086070605003511030000a09020300c008a1b942c40c055004210700300d4020000100c0d01e8070607088a080e82c0148003070f200441e982d14100b810700800d0301003801000e290752070104d50031401c0d5400504a4002ca01070280c40c0b400040019802070710950114101e25544040c003501c92034414961559050200c2c1d00345240c60604000040000c2d140e800d490080764004091360900945410444448601e040141c041103812008821f40404486c003e101550060001284030f1500c0d042c01e61009003805502140f00d441001050b010410100 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 198386294 1250 198385044 198385069
    0x10020409060b0a1209080d110301030218070801140d02040c050c070b160305090406052d10090303080402030a0b0a020d1a01080127050708010e06040911010f0c0813030308090c 77
    0x980018602d0314a0800c480c05000386c40510316024942421645123018120256049034800c0301c0c40002035021684d0b400c210002034039180c0128441800501010841c502216a01d08000d0490702c90034056800040a07601e8140c0e200000c10400902c69011341402c5c000d00c0301402c1140310051919980c40f002900600c14001c000d4200003010511401c1652141c100380000c01c401084100a0071502d07003c1810f5283c4000f8158608d080e0384040040341c1014910188103d000340c81d0803964501d151000c0e5015200104100d0349809049054000900402c0f0030342e0040a1051005850340400c5040c64102d40c43d64081304000307209000030318056a80100160b06603040440e2480150706803062207040c109a01180790130701c03402d0500304141589c1c032540541c101c031002e4240103010f03140c0301d05003c115503c003480a440d01d0100000c50a195000359840265100300d89000c402801154844c100702d500000c400c4500300c0d00115042043c150b000109541090281015040100d030038000501840c1842 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 198387544 1250 198386294 198386327
    0x110d0302060a1a040504062f072901080717010605060729091b061c051306020d090302010605120d0f030e0307050a1502120105041a0310020409060b0a 66
    0x100790101c000f42c404100d05a5048000d00180304900301850800050510303440c1d0a40b00c0c3d00d10596625580c3c456040c81219400b15104c29440c1c00301799152862050f6050017054100c1c00040031082982042c045028001d000c0c80e00a0240380341010b1489107001024102c1c1071341b07a8142001440150740f54400c030f82081da4082c0c2e4641610750000100c0390440c03050700c90000702c4d582510411102120204191111941d1041c0300944131a171002001001e01442c101c940c0525a000c11080031020164402e07504020500d131600b1521490365038003401e1740d00031240e5a4415448859042c1019024017507035002d40012500d1842140f07948110a82c0c2e41490703d0300c1c004100c90840d05401e1503000344c1c000d0818024010a50f580e030005820314a5483c203800c502100d01e030b100b054480501403000c1c07007940c007507848131420040180d180030308200140c20f1410200d900d12034482c0120110359000c02900b03000c0c040009015071620715145052086800c264008003607801c00304510508a580310890040a0005 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 198388794 1250 198387544 198387551
    0x70f020616030618020310060318060b01090b0a0c05070f08030a0c080d020309010b01120b03192316060903020607020904031e0c02280b030912030c07110d0302060a 72
    0x60340001ca01034601c1d540800000d19080c1040d01e450f12443e00114803c2c0b82600302c04047c07950302c810440c202e80c0300c414104440040150200009a2030303800405070600140f60034241d103601c1e00c00e6100307640c0c8907186a0001c40c00610641e0100b18080c807980c0300404800714020151850151a16224800d031003254042044202e62642000411001d62f100c0c0001d0a42c215100e242c4034020718006c1144075020340c045003104200c448514075038003615842c2c25010b03001e0142902e4101c80502c01c008500f000301d84140d40000030071004c4800c00c041c40c2d80082c19030010444141c4030001c01c0d2140c84d941c1c000e04100b020390741e400d10260325130104690b809541500c015040d60780342e00b000c64011261a404001e02d42c0316210098142c0e43c0084031780800f81c0215001001401d041021840c1003c0c0d1815403240c001600300304010903000003000d15132045078101907132000709004000106950085402d1040301c100840c80d20b0034040703150f8041819040540340d820507240f10b52406540d0700401028003903015203 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 198390044 1250 198388794 198388831
    0xe09040309080a08040e0907140f06090303282d0c060f0f361b031a0601020a0308010504050c0706050c04061b120c0606030b100905070f0206 62
    0x100348400402404440300303583e400c020614007000658402e125032502d006149012801a12012950000311412000b20308140008a014000c051440c4040c03290720030400e008090840c1c900b88000c1816500341c1d58000e00e6006190404680940410701a00c100014400c41c11a846455148440c114512a00700076030720040b194101c407148202c1000400d91401d0109100d5501c1c0b00b40c007c0c8001814020081c002801d100600603000f9410b00401035201c80c25060309000b5600e1042d0a542c06030062459599103102000310b40c0510074680d104644900e68230011459140303440c0300903504201c0910151041d0040b5450090000806000b460312a07980c0c0c6020420003419407040f20042d5910010601c00c524042058825a0b009403048802041c164071440e82041c0e0300c0030110410660000c402d5002c00c03d68072007150594140c40c0d0859005a40f070001201082a00040a00c5001c0980c0c11024450904034544207890004d45414140803244011104031030f00480d0342544400b015000064024 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 198391294 1250 198390044 198390047
    0x303071b06091a0108010b01050708091017040507030308340908100501170a02090114220f1103060f01180b0c0d170606030703051b030106110c0f010e090403 69
    0x20260001448030140d0720100e84041d00d50328229040345d0842000b08420480712005442d036115003e0002c10750f4404000304801d5103080d5100ac0d8400c0310342d01c1c0c240d00d0012540022485400c0a4605503129840040c04004240d400010203502c4540614034034a62401461134620392040c0c140030360342203141c040041d0a09403107240c0b04002031040e8011180c4503500510134030000d05c4c00380618949010700456800c01d00000003210406103602804040c06030b80b9100c5410500803107490681ea002000340c1c10450036035403050802007040903c0d0000130f40403402d210030f40d0869002c4c400302900410103200b004035a030340c3c101c01c0415144c800e00b001c000344036040080054070581608554070307890000c10b500200340c00000711440c480c406d44e00c0306441064204042c0320040302c01c85820754000000c100284440c1e1003504501e40124485032f200006c0c4c030003010303110001e4200342c018100040d443d0340c1d1103405034801c0200240141d4161585000d005202000909418003448424001c0aa02c1d000c1000c05 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 198392544 1250 198391294 198391301
    0x61208070f080a0905030c03030403020907050f19050a0206130c06030b03031204030201140f1005060d02130305032706071b091814010c0c060b15030a0902040606020303071b06 77
    0xb540b00491990b41d5101e500c0c09052001c4034042c85020703209420080b0200d0a001040b54192a0000c00a0070740713a650400455481d8004a0419452441401075030054000f51a1103000c140781a22200d445440c1500000e00d440002401d40380601541d001d840041880000b000b002c0d594245004580398511801013495481407402c00c0090104400070801810f07819404032400c00a00c1001da07882e9111901041034453307003600c0d01071400c0c02150042085203020300c020012846002000b50030000c44100e41d95407081d0781e03070065a49400014281040b46003610401c80007460038030306080581c21010104569024280000342403018212030100082e0065210324020701800c002442250021107201c0104ea500c01002c99551055002000011030180100c8607110080c0c1c2c0c894074814015220348002c1d00e59110406c0c0c0242c480d020481001190800662280c0d4442c0400300d1480f00a2042c001140e495a003c481103401c01d00a200c0415442182c00100940380611000100c0701800c0c010011b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 198393794 1250 198392544 198392573
    0x80309032104030306080a031b1a1017070303050f130b0403080406030c05091e0103020c100203010812031b0c01020f0d0b01080108011b050309070e07020a0b0a06120807 74
    0x4411501001d295103075105a48144294425541030280641c1c50200b01d5403243c281000038042100303440400c2003403680450a2028a001d80080c2e40e802d8000038812410b16000e84003c101c00c1c1114130b080c00412061b0301c07204000038000009102803443d64400800d40e00800c0d410180b210800280d10018120341140400908411074151f690b481c1d0340d01c1c0c00560745e4454882e9101084c01c00400804060160742034422211000c2d010070144410104800014140d1485450526500703100c0c03441c200e072040008032180104080300507520b504180c0c9040c5001c00b050301481c40740d0f10030400c000d1004101d9080001c4903100700d002e40c0d00d680050b00e601c4d0280c000e0406040e12013002081d001c0040034150040ba850700403c1e00d0f00f90459896818040c00e8948107950980110001050482c003540b08600466100c3c42407815100c015813a40380c1c0d40c91088046c1c65400069011070003c0003800f402c1802c071a00702d411320740200700c2a0300c0d090843ca0a603080050207040d80002040441c140700c00f5170703c00360300d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 198395044 1250 198393794 198393817
    0x60801060e160801050a0506070303091e0302160602030a11030c03030a050114041406011b060507020a121701090e0120250206030612070f0801020d0e030a0c08030903 73
    0x120a0300c40c00d48070a98401124116141c1c0300302c800200809024103111416074002500c00c0030f0050034a0b0500c96940c1c41584210201a5120484404100e010b14004031990001040201805807401c1c001d140041a40074030510141c083c40030082540c0010072600b541c0150b043c00d03d03080300c9540b00c0c903056000e203190004c1580000010480e4140d0710754092410382e0301203a4102014100d510a00c81100c0c98008840b80903019100441c1142d80604070150100d420b400700f03221650107642e502400d83e03000343c5d81e44025a0100c40364104214141c4500c120100c0c0754a8400441040700c41400300da03400620a101c082a507179201290308072801c1d00241e0f21495a0309680c40104c41c1e0485c02c080aa005000341d81c441124264091403071411a80003c01d1240c0080c03059003140c558404010403500541480d500030301c2a00070001e0400c000c180707a407008015600c00182c4030601c051032041901c000000c0303840306030000c00505007902c1d04115004c4688c1d0300441044d49903500c08140901d10303c2003801c1c010 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 198396294 1250 198395044 198395051
    0x30c03030504091a01170a021b0703020f12120a03020c2a03160e0903070507060309060b09090a150204050d2117040b04020406090e010905060603061e0a060801 70
    0x145070700603008008407004140d04100360301440a5144451000b040614001500900702c040c3c502130400c600c1d9000071089000601c0d00e0845444e03100500042ca21074400b40e04404001c0003075150080c5402c8003c0e40c15121903c030b03801c0102c030701e58075040d000400b02c40d84007002c91310100307440c4680c0c10b4a0000c40380208a075080414501d50265417100c10707440c0403065602c000c0d004500c0c100824000c42400310001e8180580b400c1529070518418014048039151005000d64000708030304000d5980203000395100020f40780c1007410042e040d03d0b101000c0e40d005800810a22441c0c840020b4000313040c81c1c110096801204605004d540070b4030840e4011544102c403942e1031814880c034840e48510f03084001446900c0c2c83d000326410758508100b61020440400d0240004002c26614800c0c95409032004200044042d1070f40c0d4500700712a03a2003c2d0040d41d80d5070358249020003404001e0250002c0c5c0c104d004104d40e142031008081070202072000c4042ca1440c840100b201c0c58a60380196024041060090 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 198397544 1250 198396294 198396299
    0x206030405160b0a121a060301061706060702011e0e1e190f0314010f060e01030b090a021e01031404030503100b0f0403240609150504020c100b0307030c 67
    0x26541c0341500c010740070b866905004001100c02400c4200e4415040390303100e007504d990240c001c0078028000001c840c0914400d4610100c0140e03030341001980a84180e803207681071803559020001c070b8100300428450059000308190350141c3e8004016200183c421040250a0075107200300b12400e001c0700d501103400001c00c3e844c220a40701c98105401c0c07100700551340d0002c0c000103161821880c40e85841905143c9400c02070a001255a00104450135844040046882d00c3e078800c0314000c80b501c66012105600780c00c0014403c1001c2c004d000b640025054009140358001a00080c1e4801c0741403a000526202c000100c04250b4020707000038001c07120090340920306141c0342c00c014102c1d9000300c80180420440000108800c80010103803603283c400800214245810342c0e940c0010440d00070074a595a2000d09800070140100780181d0014041c00c43c00400c0c250340c2e11000c0d5240c1030090308131502c030702e00604c1812007000c000500280105030103100480e0071041032000c6400c0500301d4001600407105601c01 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 198398794 1250 198397544 198397553
    0xe13030e100c0f03120c0c0b04080f070503030906010302010f030209181909050313210201030c090e1501080a29151308070e011206050601020c0414010806060612070f0c02060304 78
    0x178051000c43c0710030f09110340719010404807a0b010b102c120060103c01c208020801140704040984420070f0205070844c90495244c564500e1500101ca1540517075011000510840d41c1c40f280d070100e041410f003415401d00c900304002409101800f90903807007c0303030300000081e00c09031180300707882403410700d4102000224824103269849a210100c2c58080c0240603200241c4010000e07410640e00801a8600f620001d40f80d0045029004500b00702d01000280d03640071890f01752250015001c2c036032244a40b410b51141c0c400141c85020010a0300100610f800d26003100c010118081a40c2070b14000c40103280308030fa01c80064090008001112140007011408078401c868a00f0401c1c103442c06401124901a40c1e003c222640c01400d000c1e05600e403e5508681000403005d0b08416001a01401611030034030030640802c0c122040006200030b003600d00c00041101381410f0106c140c20040c251085407924001c8484503503000c4000d1300c4ca00400400c900c4080c0741c075104043e400d005650040c0582d55a06107800c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 198400044 1250 198398794 198398807
    0x32001140c070c0909031707050a030e010e030403140703121107090603150f110d0603030e1203040302011404030c030605160e0f1009081005010e13030e100c0f03 71
    0x10304500351400a020500e500000c1c010b564840c0c1d0721000a038851070030300304090060240101c1c101d05100d081003484000d0281c0559140c45015965106511003d005400074140c074420301c81035042d45d01d80780350180d98060100899040e00c0e0030200d05803800507150001442d1100a50019106404214141070b6459100185a0003442308204403007145884800c444101c0f0f0740d074031000b04081390070041c42c0105400307074010034000d07622280000385000048400980550010200c642d0a82c0e03190018420960020400044010243c80200b8032a40032141c5c6aaa8800c40c00041e0611460602580102d2008004c0750003940d4030101c1101100d03643d1501d807000c1d060a41e1a0001c01e040c00006e906030380d110b45c40c0bc03d480c900040c00d00904d03081410a2240301c3c15050010410009001e4021483c001c04000c0484c0c003510654001520f9807400520701b458030805445042200c50160b0700001196100c200c0000c445800c8580e40403200c804041074407000744c0c1801c020300c0e44a007813095005154104a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 198401294 1250 198400044 198400061
    0x20102190311010c0e01110303130b0a0209030a03020c01170c120c041809020103060519090f0609090f0c0509010b1e04050d0c030302070611060a1a061909050d0b06010c032001 77
    0x884400c07004131f20148041d140d0004407480e0441c0f0718108810004502c400c4119900581d10035401441c040001012a050945601e07050340540d02145201e04030b944d10600c0605043e9a009140c0e0761400d018020011078454021a0340c0851400310100d503604140c0c00480d8000c01d82003040800c0c401000000401400340010143d000c60300e44500054541468400202000880d4040b030804a042c00100700052003444911072245540700e1000c41c3c1d002207071250081c41c40c0135600e4089401700902d489846502541c0000d4015109000104060b00f00300301035031800072446070703415080415075807580c01e80d01641e400981d00545680c0d8142c18071454840704003d490081e070980300b602e9102c003401d032860512541d5010702e0754040c10018811000a0340001310f02c441d0794403041010204032001801030340000e0b000302c0c2d0401101001c80d40c0c80b500a52140c4c000c12054409002000c600e40f103161102500070045c0d030501240044c2c1e2001c152064204400f504050f69900e000820081c2d0403500801598 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 198402544 1250 198401294 198401297
    0xc21040f08070929120c060703080a0b06040305031204061815060623030405030d02040f091802090a05130203010615080603070e0103290a0c1704020102190311010c0e01 74
    0xe1580314007a219154050300c0703111100c031013004626508040c0241581800380c00c1400d4014110108110743e0b401d0700910501d4001d955201150030300e014000c048480c5000d0251003420f08120400000e1404015501140400c280d0780c00d195941e4203000019002c14402d200744040da15294804114525071312651100c0c01034800c200c802d44510040d10040c0280c000300c24521543c00c525949004160019580284a5400d41b402c1c001e03007040000603608141c128015400c54440c0a004007400b40c03080d914841d0341b4440b0801c41403e1078004c5030a00c6005425012035584800000e03c65035000800b6200055020b0020000c4983d00e44002c4003207880c0551510014290401240540c0303000034504081d86c1002091080c164a10b03502c425035140c18601c100502800307a0b0030110890070044c0748070f204d00b00355140490500b4008400400040500c81500e40c0d110101c401e020140c2d0b4006055130b00060340302d24514441403c1e09090300c01c0400c150410f100366081030b9030301c50300341d81c00744450161581c203 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 198403794 1250 198402544 198402551
    0x90417030a0227060d0c03020405030712021f08061c140303010501020d02030403120810331b03030c030e010608010b030d020f100504020117100e06060c21040f080709 73
    0x2070906190f40d000d2822075039512803000e008820300c04060307034043d02e10742c1e0380c5050041c90940c2c0c400201c0e00717056095000d12100d0150700840025400d250000100c1044825002e0a01680c800009041c074080500078038055a0882c08070340311501040361081c0003c0d00030440c070302da900c04106410780e40d5000340601070043c0901c00c80c195265000000f43d07002da070307446500d51113003c5551104548058000704144080c3c48468400140ca07a503184c083c0d40351280c02459000e241030440d0042e519148901d002ca405c000301111100d5034450f03044804101c1e00d45c10700c2c01052802807510203d014206c0c24006002d69440c00f080000c4000c4154003104000742f042c0c050b2059010b02980990300c030404520802c8680c0c100180130b00c0002c200d07622050340144141409601b0400c0c030400010600c07400c903400b03080240296020700084001001b41c6601290845035145000308036046280c0340c071841400e44041e41ca05101c0207401d460407005032400381c0501355002c42e595556011050761220584200c4854902c1c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 198405044 1250 198403794 198403837
    0x905070f0b070609020103090f0503070c0f050303120c0d0e0c03012d0902030313080f060a0b1003090609050a03170f010f03020f13020c03090a0e010f05090417030a02 73
    0xd8054044084862010080303007015401e0f29040058811250308904140e501d00c01c100002e04014852210140604015502d801003407404088003a2a90018080b5421041040099a40c00412038a090b8440aa48041030302c0b90791000c8614050f140e01c13060407a041132210f0400000004a003192100c0440c000e0141e419280001d9000000c510412507880301039000c2c101000e6010340100440fa440034040300e1a0100744e40740f100f0b0601b074030740010381c540e002080c1b1541800d0040141307642003c04080100158801200094842c2644044400501d9158101e003c188000c2c3d501c505d4101d50418240e46400b0703040d1500510000d44041a41d1128181301c000c240605800a5124140c4e4240098010840d0070f580810071500e0f000310203503600c1520360580060450a5002906407200503030001c60701ea155513402c2002501e1580c102c3c0010400c014010058015005050303000c417003064070106c2050b1664102030200e83c4800d14000c0f02101300000b4400c4c000425802801c520365060106406140d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 198406294 1250 198405044 198405059
    0xc010f0b0a030210050705030a050a0f0905030304150e0d0305192102180307030b060a0501031512050a0602030103030906080108030909071d150702120d140d0609050a090507 76
    0x144980c0d05941c1140c050803042c001420074680d006810319050070160300b060300580d109459580300200361000a940800c50715130541d081301c00c50907011601e083c10f0030101d04250100f5600d01a9102d06840020b600b002800458010710712007082100160034202004150704015040b644400e102425401e000c3c04c1030314401d4401c400b9080c001820018070362a42c041d260400020750000c20b928100b117112506180b40d50f5408001c0d08004520510819219207445404c2240032502030b88018185414100c0c00712030440e0f222482e4042d903d02c490522140034590922520b0148600002414a03100100210a1540090341d00c4122a0244c2d00ca01c103076070b01c640c0c001d0385900484409039007107078440e03010501031030080458686a101c824400307c41d030550880041d00803009101c6040c0c0780c0b000010752034250b0070001c001501c1041d00900510b80c4003082d0000400503003400340800500d1001107007807511859260040d00041025003028050b505010306264003d04440304100c589200302d10700000c0a0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 198407544 1250 198406294 198406301
    0x90907030302150112020607020f060712110a030503040f11030706081f03050c04110d090605010305010e030a0f080903070b01150201061e0b0c15040302060403090501090b0306040c02210c010f 84
    0xf1802209049172200e0301b81c0c280021a000324a0807640000c814940d000580ca4560147c41918002c08420030810100c20000e862031021010025640d0401600800800d80240460f50446d5000d10340c0040c044403130030b20007090400014199414040c1c0000090143e42c000400b5010320045500f0b070503485202012504c0e01e04142c480200560016920800c1918080c0d0000c00c07854540c0149034540444840035030101c13071200004a5003150b844005009008092090b480a0302842004510b4520087c00140c805a09140041b08100701070700040c05451050080d150700c0ca51141128030718bd42c4910803040c940e050005036400540ca031200c00649000e00b00200f400c40c01d04241800c0c005d03424a40c104d1169070020200720168404c11405940480c201000c00313200c3c82c0281c2c05814541414076004003050b0041d40218100a01d0302020310000500b5030441c0e40280044500041d400d8042c541a410160180c2420728500e8100d0314104000d071007a00109040314448000704800d03681203034840300302c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 198408794 1250 198407544 198407549
    0x804090b180c16050f0f06010e06090115020c0603040f11030604080901111e031209280201030912080610031503030c0f0c09060e0a180605070e0909070303021501 71
    0x5106000442c048401d000000c0c000061003041c42218107603240c40c1c06141c49030010700019643d1003800e030612020003d02200340504020740b0801864109100015801034041c01040c03140810700b030900c40124020408070003c0d01c0e019000b02c0d107a1801d400d218521148402068401035200d070a2601c080c9002306015100d140e11024050509201c4001100c074540b60380d080f40d050380b0400f41d030380e40100342d02000030710010302040007159255108103485070000c03009402c0225a0744200f001500200c110400d0b6030343d4407124500003186052600048024000001c0050504110000b0142c1074603402208141b00782c0c2d050742c60b40071400000504800704e40c07840042440c400040c00e410b20004e4441c0481403507642c004d800b8905000c08540741e034200030140d0b62002c040359035140001c00600721652440790744002c0100c2e04210400059140001411200c0001480181d0380e00000d00658021046841c18000c0942131800925140701c3c3c45036110401e0000783c0240c072403da44405002ca251800506 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 198410044 1250 198408794 198408829
    0xe04030215060f0301060f090b1807030b01050706090b0604050c0405030a1e0506010e070905060307080415020f070503090310090c060804061413120306060c0803040c0806040804090b 80
    0x3034142014804050300d40003510260703103d0306189010111365424058200989400075a1a11071803610102c1e2089a0503011554001c4211034280240e400d03892a01640c00b001c0390501098074840080102c44038801d05038020409403800301541c05000d8169001031184409440801643d201c1c1720030b00015008604c20998140d0001c900000000c40b103115407000d21003003500b004a1b03240c00b65109420001c0c00d80208080c0d1001c1002c2242030341d40590000010f100030360f030300c52640c149100000c0410b100108040c0c142e002c1400045c4030742c20a68111030709014040702c07094541445251081e00c9912854007130303101c1d104036107513124082d010303100d03914144d98030101c4050003520f0f000b400d0303503241c1c001403081c2c40c2c0c144e03141d003004056154915071900c503900641c4101000c0410b454030001c5490404924000c241c98100e050000b10340100b14000c0454105c2c8409440350380c0c42c580f41c0740703104068202c0300e25401128240801c01803440c0c040c0066400080c02031181c55811024425595555550840f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 198411294 1250 198410044 198410053
    0xa020706090303050a051008031e09042301050108011401030b010e090a06091406060714010207050d11010e060903030705181801150302090303030c300a06060e180c040e040f0201090e040302 83
    0x800d208102600d4980822442c1c0078ad410f103290080000c040381c480d10600c1e45084003034030500e24008120480d80c1d01420342401c2216255041c0001c0361454100100c0d514181075480c0da62820381e0703029420130140d030b5100401d02c0000e45400e00054018001c0c5108031f50680c1c0c20580550342c3c90028140c071074458070025284604009440c2c0b1030113002688640d440d0403d5600f0811400450070900c14801411003545400040c1c41a8010032403c4424640314602c454020301d0a0002866000c01180d80099492802a1b110355030545403c0d1078103001d083d09540507043d100800e001c0c0ca400d550060484002401c81069854007000075800c2c3e00c1200101503158100704001405101510058203001500064182604400f6007100e0500d1000360340000d00380120758100042c00d1b4003801a2409008146040c00c4101c44400c0843c0418803a0341c01060441901000600d44901e00016907008000c04c0318500100d0a0909200341307802400401a400540c0001300850341c99100c0d54024000e950560040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 198412544 1250 198411294 198411307
    0x403080d0504080c03030903090f040c0801030809060408031603030c0c03020c090c0702030f0c0a060c050601030803280213061403150307080d0206010f0e0c0307080a020706090303050a05100803 85
    0x34024000108112502001030044011000c400c001462055200c84029a90f6a180404116a411400036070502c158208200b000c03140c0c0d4401c0107281100c0c1d00424880d200c0f5641c2c800030f02c1500560b00828418840450031189a900d1000c040e03c200340641c80c100152181e140040300c80030300c0040b000d4096803000081260a040c80c2c441258441d2083e80b10508140b000d0340000d051003024100c0350070740e17407010740320710850700d4000c1b11a8001c01c04e1b070400314074200b0b0306d0340d4841e140c132030500c0060481707000800050785010303556501c0d00311403000280c1c05040031200c0f210b0800941007600d1094010103e0100407810754041c01c24000544441c0c81e00c0380c110340d1448504a030036000301403000d0305030081640004144034100050b2410303020b80c0d0094200c3e03604200802c0c09031411688450310200400c0180210340c41240f0459400050a16028007190b0380d42015001030f204514000f44a5440d0020407400e2541c90360005005038480201484a80c646002000862040d40910032183d081000b14 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 198413794 1250 198412544 198412567
    0x50106180e0d0f090e04060207030905040b0102330f04061113030807050708060c040e09061b0d0b062b0506010e040209010912050106050102251a0d0507020c0109080102040308 77
    0x190507040d142841c0c04540582c4960125a45c080e080e00c007107480315000f20b814010190403030a444041d2009441c104508100000000d41e622a4a541c0f070005241c0d40000c0c85142c46180003c010303600300c0b801401d072141060500004000310454069401c103160081d82c2014808181c122200001c2621001031003d0940d1280402e41d80022400c40d03c40c8213007680011002d409110310f500c80c645900910351280c1c50075092043c010300c01000c1c4031468018004002100240c4507580c0705502c611002c080d15184007440c50380050100a07141b90f800400403440c01d4102003540032081c0e083d46041c40808180104640d02c0b03080d1182580c105000c00d0600070651024141540640003c400503d000e1000c503549102e403c0a600c00b0202c161030304d035100c04061129503010090305e41d00c0350344000b031081d0002284040c18601181405040c003045511b4200b440401e00040039035080085114003081603081c02c00c1e01035520682d403118103000c1030700c03c1c50015541c5010310136a01180c0c1c010726281c1c0b42c40e541c1c401 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 198415044 1250 198413794 198413807
    0x903090a1403030c060f01090e06130605040c0801090b10050108070206010506030a151403240103020f0d02040c0801031101140d020f190203030403020c0d08180f0d050106180e0d 78
    0xa07180c0c05200900c0501d0440c20104605400740f050042002d140f941407521350420f580c502052035003940e0110050210b01c01c903d01e017100307041d0340101740095251901e24140d00b4a1440350301ca48810b40c01c0084d07880c180104040a64040c04007141c0840180d070f6620015074000302c0407038075480941c00c4a00108007506008004582c4007842883c00102e850807010007440c000859046a404004e105401904605081100c10303200e4032201c14650f48403050a503071140da0f400c1400001d00410036006590425101c1c6000181c40580c01001840341440150000301021824402562401d0900d080c124484d4020071036400e4000b0f80340c254902e010038a214400c083d5005050050500500300010080742c0d850700d5024200f030700d06502444c0e907410a410000c0c0317028034100d0390341e10034465031080341c00280c481c0f0101d485801001600e000340070300000c0040c1300f1091030780c0840c1d0420207c4a00d0070422070190300120580d9503081030541c01042c80c138100130490710000e141501ca0f07802035a440024a01589 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 198416294 1250 198415044 198415079
    0xe12060612030921120309060412020c0a03080d0b10050a030216050d0f0e0102030301150c030221090a1a1204050a080a030b030c0102150c16020316030b0903090a 71
    0x2101d207014401d0b404520b90381c0000c040306495442e880030302c41a80702c0c1449145c4d8044a03904140d82541001c4001c5500c4100c050300040008101c00c10701d2a020703000f071121013541280101103082007952030810072810f502010902c60b180f40b4101c6002003619190b1111603e00103541c0d1550b0810328420000d800940c8051b65544220340e25005032030000320100210b0303207100203031b946180180684001c040d000060440d00c0d00d040d5082440180580c514680c40070000c50050314106c20200307a0743c20281c0c208600300400c1120300c0680e2030b80c0594072440c03d00078980340c041510392402e41070b40d8076a05103450030003108441582000700606010480011480340e0030500680a0f9480c4420039954502e03a0384c0050005004680c4039401644245020b0041c600c00d000280080c0100c40451481e201c1810b90080c9515442040840c041051003070442200085a6001d8200d40590a002c0782c00d0701c41e0181031104070f41465a00002407409403002c0252140c0c8c2d140604101070031410010015007940001e07 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 198417544 1250 198416294 198416329
    0xc05100c0207060318021002150907140103020f0c01060303030b0f0d0803040b0717070e040c112505040207060510060507050601060c2d1e08030a020f0403080a08070e120606 76
    0x1780305402690319100300da09560030355001000000203544064101e00c800825a040710b8009400c20071140801c4003443e030103090240307030060340c1f4462411a2640c0b8044d5600d420030662030034a021042641540c00464400c0c01201c4007040219544c00f0082c0355011342400901c0070b41c0500100740060120302109401a007181444605204c07000c000d00c41065084038000c00140310207040000c241002c0c8074100044138285055603203680e030500c00a681e03000009080003900c005101000d4204102401603028220080c01599910b40c5410480082c0c603081d6581c1e00301298040002490f1401041181c0d605984500a411568a0907a007500d005091010a69899100081000d460665050001501e0040c01080c40010f038a0b400d1050724070007080160312889450b0380702c100116101c0c0042d41d40c00b51946102687d110001c0d510380589002c2c1c0c0e40010507040001c14803280c8bc0b6080300e86584240017a03990b200c0c0362014141004000c0d10349100c260b440d90802d8001c40c000b07040c01c0360540c1107140714 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 198418794 1250 198417544 198417581
    0x1207060204031e0c0506160311010e070609080f010524040b040518010b01110c090402180106050307020609070f09020306011e0e030f01050121150c0c05100c02070603 73
    0x1c2e501c0e082c88041c0c038290b6000411a0100100040005603407039400900000d40b130b080d04080da01c2034a04141300c40d030b0300f02405010070a544501458004d4001d00d00428080c01a103200981d1100050142c2425000d8548503000322010440c1d00401413081a125000464910400b02a41341c1e140d11104040848143c020b40c40e214003042945460144601a400810f505075404400040d024215090b00294604200e10380a102e03641890001785030010040c1204c0c2d4032455102c80c40018a24041024100b8084001000000e009500203010b14032951490702030701c0742c9130f464400154030707046070b80901c0d141801211401d022050f11640a1031b4859010f0400100201c1d6051615144006082d181c0700019246504000d050030280f003080061700801000f0b0002e0750505d103149040c44a600c140100c90613001c0030030820300c64804441054074419810030003001050100040c00a45c0d200815251445401e0a00f200d081c09480b6a011203003050340500561424014200c018140d43e00032040018031 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 198420044 1250 198418794 198418799
    0xf0403110a0f0210090e011503020405090f180601030203030706050c430503030c07030c080a0f27060f030b040f02030604060b04080706050307030204080f0c0405181207060204 77
    0x10801d07049824012010720800d9000e80c410443c9204880c5407600802208803010822104030307010850644100284030707030041c807880c0c004400901496100cc0d6114124200713001c0095040310107240604100300b501c5995042d1194190f0f0399400c01c5c40300030341540c82005108089a0741c0c0c0c1c00702d5001550100600d292030310400c00002e02000d00075004210310344e501d100300300303c4101201400b08400d42c1c000010390000d0a81301c180d140d0000609241d00340c0c000081c010304051040f000c40380c0a03648003204c103880310071f1000002c01c1c40401d840c286010a80c00c42425850f19403100209142240c4110424165410884100d0380036045044120500d5243d04805000380c1c1da80c0502c5c0c41d120021000144ca0346800c60801081e01c45543c03201c0c060140402081c03209910210311a4203580e400d0801a980351a101400c42c0203104691102d00a4041c0e11070503d44844c0c0803981039600b8400b1101400700d80c891289a40c2c5108120340c856070654800b0140b00d1020701d101028011042c01200e0040c01c00780e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 198421294 1250 198420044 198420077
    0x905030610060206091f02031f0b0702010906030b060d0b0316090209030d0c0206040e130f060203150906010f0c1401020406270b1206030109020a0b090a0801050603060f0403 76
    0x8001d41d00088607402001d0144031155040006592120040700103001e18110382c00d03c400030800e005511016540c0000c0060a24000d419600c815007034600c40c0005105d43d2112004e24036009900c0403400100380803000140d452207805507400d000c500a01c2c2904e00002204048000e2480400054050040702901c404140c40307230225400611a036140543d40307842000030182040344840c0e81c00180b02491401d031015841d400141c406407000180c00401545420000071020f41c0d414000400c0d00071b40020420400c62a0b0700518051000310242540c1d04404900b0041c40c2c11048811900185100710f000c1d101078030908034814158002d10549001c01038921045099074400d40060012030710f4205003c0c645000041140581c00300341480350f8445050007041041ea20403802c02d034140c0c410301004945690350a41c89600c20560050604614561711102040150484020144545d40301c000000354900b041c011248500001000351409507960985107429078005030084c0d041210380d84242c480e11 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 198422544 1250 198421294 198421303
    0x7140f0d050a140d02070803120415090f110f01030e060c090d0609030c0b0702030a020309040b030118052514061b0a1b0b1303060c0c060f0209180c09040c090503 71
    0x1c940c2000d005030000d0700c0d1005e40340040c42e603c0038180da8810842d40141001540250742c000380e01030100c45c2444c400610350030180a803400d000d0b10900156500c4010082042d80d0009204000e4680c42d00404610b001134044a00d40f2494007225000500000d400520580c02018a5480101860141a16903d80c031084548181e0300714081041c645c255401d0049014160b68003412920066160001c408402503c6c1c3c0611900c5c039000b0f680b14000444155001c2d0800391031000310810131380c2c4000c0142441903a40c01036050205e45a490314030036039400040c2c908180280d030b22410041504c132203c6000e1150981c4690b10820f110b641c1c0c07034220503401109104a00700c4074000d020f0904c8801201005076100b4500742e00404c05114200017484070900107da04900300c0b074026000140010402000381d807040c800100041c041468150306961048980d4040c4c134845a05a03406400043c01c50303030100c000b00f0141d40c0441400c0b410700200c4c26510b465000000f4042e01e61505044607a591000700c2d262 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 198423794 1250 198422544 198422573
    0xa140c0705070803031306051302040c02010f0c020106031a070c080304030f0f0903111002121c0b0a03020307090b0604050406090c12110417071e0807140f0d050a 71
    0x20100001504014040200038502c082c0c15180059031541c1007800d0581c440901e0720600800c5c0390388490001c1c00c207902400c4100b4106402502c00c2c421001c0c501d6001f402411a54000400185411132601d09540305225203000d85e85e120403110002080c2000c0c9900900c40108035404000a044091002804190145005900c644c0f070301320a0012014014140c8441058403804002c20b910040002c14403031484915000300580c1c45507000200c11004a040c200c40200669002a000543c04041604c500f013054410245039410031002e19070b54100110900244000780d4554056030301480018015030090300c2840001384254903265a50010400740c6031141d0010100a58541d81c00d403585400450505140703108200c100141e50555000c547c003801240181290300f404260b4000703a41c8e004102d1072018252601b103414002c000c05d004042030b2040b43c0101511030082841c0040e1141c50341c200b440844d54010f146070003012080c01801060320f02c209068480b40f04040320b8002140101044969 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 198425044 1250 198423794 198423811
    0xa1e030602040e310f110a1205060a0207050d080c190c11040b1011150903031f0806061e150c0706110c0f010c08040e0703060909020a0b030a14 63
    0x1c2d0b141c41c00950003481401d542c0d142c09040140c0491980035104050744c18900d5001200a03007184541c03c14005001103650b246420000803980440d54030061135030b03109000d02c070301d00300c500907640c01041005901030801c00404550003100d58074070842c05074400550049851101c88d090048800e02e800e0441090291000426030b802d43c440140a4244907406008074140e40c180b0860040c0000310350980788030a00034041100300c544044401070180010b0000101c2581d01c000c0900340354288585a90080d00c05240b1300e500c0c4081d40a03031610002c200030440d20090302415450fa81d850502c2081800441011001c01074410305014035034904810300385030680100c08e6916400c00300c072824980807a54004005008214140031591240024174a1615105030b40d0400001c08900058600c0c0d02040001402c0c801d000c100800d004000303110003849506aa81e040c04205c0c0c4d188966003c84030780c0c03c03001e5040000d240085c0046003910004603002285400001400c0003800d00c44100e481701610540d4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 198426294 1250 198425044 198425069
    0x1050a0b04060b160209060103020f040305031801090e0408030709080d0807140705100b0a03021f03060e0402030a030f1107080f01241403011b080604060b090a1e03060204 75
    0x40c4a04191254802a0658504807440c1c07102d14005000c140104210092044a50a001565592091b0142d845411004601d15102c4c2d46038585951071350000f960f083c402203403503480790403190f20801021040742c0018030300041e161115140c13810141d10090650082c00540440000c03120010031400645030040e50b500300460404050003070202c01c403080b5a018400092060402060020030342414818211000046258003030340440d0f003109590340065401442d900e80440c502011104184444000d960104807032512440e58403000c48003030700c002e501a0320641c00720002a02400c00c202c05207000c1d00707100e40c4400c0c03401d950524240c00c51304140d803e5000300b00400c131080001d000d014012075084080c2440e050600106510809040c86401460304070b000c03440f11513807020b510070b1401900c141c1008c0c05a11907010040c080c02000d80754903000314941803001514104102c143c4401c090020034a60f01c00349481489100160099200e1200e0304410b240000014103c0c4020802400c8004004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 198427544 1250 198426294 198426311
    0x3080319020f042c150108060a0906080a210c080a030608060106020c030f060c0f1b0d080105090a0c080c0c07050d0f12050301050d080f0706060b0408101104060e01020a0501050a 78
    0x3c2641013515036240c2d02e18500281408070104003030b203500400d00020301c0d2200315640e4030400a0407039030b08d80d030084180d245841d0300441d000c4408100101a64001e4403039003010042d50b084001040c0d9400d03a100d001407180f0714040006401a401400c82003101d00c1c0114006844805440c1001001e90055000d41c1c415913600016080911001e25004c1791300c80070789000e1810b0800c0b0f504034450340100c99022540050403c4d130241c6000e00480c100120b100460f42c1c2c1c415001006030414a0070701580744184099000202c50b00c01a002c1c01084690300e45e1411120348840d00003072810f804c0703481401c90354000d4110200746601c0c0c100d90343d964180140b00303400c0b05545074240707400310080c8100c0e0710080110404c014016911354a511404095012039200c1d42c4103000e0700c1408190142090040106040410004139040541d000e8410f5034190410340b40076903c80500c980071144043c4c0c03440c0c1210000d010400c0603501171a00e4510200060041d1410300d002135507000c0c21108202d52400702c255948030340 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 198428794 1250 198427544 198427589
    0x9030f0c040e0109020f01050a1e030f1b0905011b05010e0c100c052a06030702011a0613152a0c12030c0b0705090d0308090d050403080319020f04 64
    0x10001c0c0c44542000130402c1da070311500407406443c4894804c2d81800070028001400b141300340c0d007003400d05400301c0c59143d1000c030f462030040142824503541d081321403e1035511100050008104542c0d1072146e1a1001c9180c981001541c81c207a034403110384418002009420040341c000e028420b0716015800103131140b075807020b0400000b2004400c5010400183c89a1140010030004a03001d1110351103c081c0c544003042030640703541c4a02d0b404601d400c420044244071005405400920004403002c0b0366500d8149040144900c0740600380081c120514a80d0302045036040c10300d0840c1d926155450301c4090894030030249200c2d441015052044030300180b1440c030511080c0d01d521800ba03c0c1070090715110100c582c800502d000c1a100021340040941000308070380d2405041210f00d01d190250818048a5a60034090700d80403045030003050302d00070031601c658007610a030125820340380c1c4100044d0035511051031544145d05420741c1000c10f40d9080043d07504002d0b01e003019200506503480165240041d8500 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 198430044 1250 198428794 198428801
    0x2040803090144221403042d0806060d020d080c1e01110f0d02090111100e0105150a0b210c0301050429190e09060f01060903020109060503040809030f0c04 68
    0x52095200720710420f9a88811000080c0e140e464202c6031105c0300c9088000940d040d0700c01c95109105010030074105850b40c0440100c20881c00709042851144c05960b40a07440e10f84004851040d0711800400d1341e000103103840c01c10360701d40500440c041424202d0700520580b5040040f442c1410081e40d0401b024841c2000b406591792269074100c4090410111100040b040c0c01422001c1540d282c0100e20016103074400d140c0c038107400c01c04400701c0b00c140e002e4219090062010145540055007800000351005250040c400b5030054054480e04850380b901801c4032282e04148040c11601d42c08202414001c580e11540a000b144001180c1e5a2945050100800c0340c0b208554400003c1080d00000b403400c1c2400403480d0a04030968001d14100300c500c41d40e1a03810090340150842c2290b120030700ca90068001041842241c60a000d04116600c4203002c1d02c170912244002800110424421321166200da001b8640052103501014100841000001d060012076409500107900000010542c0e260500 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 198431294 1250 198430044 198430051
    0xc010f02030711100e1b0d0b011410030e1203190203041505090610150e12070306110301030c21050a0b040309061b06021608030406061802040803090144 67
    0x80e41040f90543d400c400c0307511804920740c2c400446c60310200d00407142d15201850f694440e84100c003030495686845000c1807200ca4004110300903156900705010a41c01380c81094101c104040040c0b000944030440c1040c3c90740000c0440c6844951110806c141d0f000d01d00145001c1d911034400c2800426080c4c20b40c404a5030b00903e14401c9510a02c1445403250440080e0020341d080c400c0100030461040c9000e641c981e00d001d040f50740002091620680c7e505011a010065a1143c14148000c0e164a00b003000103010030302014000e503030b0038141000711110109905102e00d0303560034010760f031a86544680d0f04000301d001042e1165040c4108100402d58070840c6034001d4032490030036880200c400418880303000038820009182544c0090400c8080b40340c190810540c80d0310a60b126520704c2c040c0761200140c052881128500701c1150740800d9188824020b031030035074281500650922410400464845129041480c109400c4460a900a1280c07000107000c0420b00d0907410070785c3c617414141c12050140207 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 198432544 1250 198431294 198431323
    0x9090903070b0f01210303111b060603011b1b08070302010f05060102010213090b06090423130f0609170c0c030613051f060906090615030902090c0c010f02030711 71
    0x480188107145c0c4003a1500030b225000e90008581d0202413070243c00401c0c08003240c0350f10700c0c0c000c6011031b86450703442800384404481e00180c07540f076114142814203880c11560059100b0701218600d0781118814143c01d6907107c2c00703506988403a242601d88101a511101080c0c005035183c2d840344450403070501486401100030f1001314988001407040001c010f449000d07031310b1007039120040c4180b542e4505040d15001100108100555000c0041080c501032005000c1e07800f842412000404a0700400480788201c0d82042101100400680d01c500c01030a485104490ba50200082400d070107402c10701409981070920021301e402c40c130741820186410001040c008001204101402c0050408034000c20814422840c0e1442d00c440c842c0b054014021540100046c1482e187e40000e03841240e40040c001c64014603580d85585056000807001d9070345500c00030750420380d81801b20310400d411000800c0e643e07032003000024018214070b1101f800e80e403003a80d10400141c0a6144d0b000080810301061a414910 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 198433794 1250 198432544 198432571
    0x90212060f010801060c0602040b13080706030504080301092705010e15011505280903060b0103051303050a05070f0606240918060810050106030b030d0504090209040209090903070b 79
    0x700000c28072041400384a0030420408540d0b000c0003c5a01582c001d000060746071503c0e0310b8152074a5903c000703a8480c800f00e0748100c010024489010384129400b4680000e00c04e8038513828100369901a1100c0e0b5024080700761151810310001c01c01c00c412110140c0310340c0c0081550f211590915141c0702e800b4014a4422001e4801007118101c507112500007001c1034204603481d8402e801c1c08000201904414034000b903201110210a2079110f0103a0050361f125120800c999007500c00110101d4404031601c011481101030440301003805100640038620070b5160207450540340b50303110031258142c020200c0d84551100301c1480901c190080e429036084070320101e0888010080c42c01485045544941d040201e100346010441c940305401580241c1004000c0b41d00d200d4007103074010000c1c80244140340c0003a103041e001104500d804140c1001c1034100c2d680721401c26060400b07800c003d40c030042405174082e5003004000b0841e12040342c154401d451500145456546e035007455041840c0080842a02c1c040 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 198435044 1250 198433794 198433819
    0x1503070501110309120a1209031502091c020f040608060f181902150307050c01060605090a0306021b010c0c03030b01051218070801020f0a0e030105010509061903080409021206 77
    0x400403d40ba2138440c100c84440790003000055643c01c00494900140c0711129442d07241c4803068100003203500720381c4902e041d58415903a00c2a0312040380071b07032664907030b014400c5012134042141c0410344102090008000407046030b040c1002408032070f455030080009400001c1003085103028000c1a940c001401c1034508407500606541d01d84940c4100003000001d070006800409644030600c00400c608041003500c1d9880c1400c7d4030290032034102414040c580d60a01c000801c64520a4090b6a440100640151582c6007107940e03100280d0040c0c03000c014108a04400115000802d00403c0008800c41c0c4a49000006504000781034903280b05e800d33030505c00100300010f0300d040000c941c241e0144018448004208485040d41e007411460b80c0b101070a503002069010024061a0040c0318403061500d0b51203100d00036900741070980c0c1d401d2184582c060300c00e43c0000d07014140036141844010680c81105034054030b95545a406402c10740100c1403440d40481e0410a50f074144850039049007040300d20898504 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 198436294 1250 198435044 198435077
    0xb010e09040c032004091406070908071404020c010f050103031d0907110307051005010810051005060a050d1a012a060f02070b010e040303060b120606090a0b031503070501 75
    0x4100b0701c0000d02106031004202c03c3c1c00704c0c60001a400034030081060180c1d89060600108400684162109900501f0007280c00c0d14060411681260580c03c0500003951034440100096012110402c0d0403a400b004005409a03080c03082d18541d0b80c41c2d00002881d9411404c0007094001c2d40240c00c1207400d0084014110350340e49640182d400400c510341032901814081c0c40501b903002d0401d000701140b01d906064200a031140e080340781607420900448650040f00c416107020745406540395084886101414441d5042c548014610b10a1508000b850440103041c02c000701c0d58040b80301d207290036403200c101c01e056911441c4401d014130742040200d0305056001000c0c03400c1484260081607155224100325050072590181c0788604e4001801002075a0760720780f10355460364100c8048000030329020010450070301d804143c13184018115089900d503a580d50612500e584040c0102d0387c0000e8115000583d6007420008610030b44480002e0491b00300d5600605107170215a070009810310a9000c240322020 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 198437544 1250 198436294 198436313
    0xc0307060203100306051512120403110111030c1006360b0d08030108011404050d12110d020c1b0312160506040f0309120b04060c02010e100b010e0904 66
    0x258218000580c0c07a01c60280d00f50400c0c032603600040c5001c0c00d1500300305d0260f034400e2131640059815100c0d81d1042062400c059150303000324111510341d081c10700050000c80c02401c18003c01e140103041c07c0b841032401c400c026103503801900b40103107107622803804442c0f108064060320000386400e5402d101c0c03120b0b455000d1035070403035449156002180020b00d0740404a4040e004044089400740040b04501c660303092600043d03100b401042d05a40c204225501c42c42c05d00310b102840b84c1d0b0020050b0070840960b200c11152130404007401040e00c0d40311449400c07682607203001000070b801c60090059448000c6007201d820480e0420b07520a03003000c40001d43c21151004144102c000c80c654003016a40c0c26030030269111075802a20140107031240e00d080000300110900100d201500030348500d803c4c240c2c0c640c1c0030310301481003000c001d0100c0800c0010800180351500b12100d5a002400042110140030070b1807885d005203c282104010b0b01c800280f040d95030090b800809818090f2494159403800e40c46690703a4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 198438794 1250 198437544 198437557
    0x60e030304051e01140a0302210114010804052a03160806180a0b0412090b070201020a0305030603101b090f080703080703110307062319020d11120f0c0c03 68
    0xb0b00800f00c40d60078a80c81aa50440c080f095039810310b403121540303070008000790460b1001e0324090799803461b03078401b41d440219001d0407110041403007448a091240110384048014008036001e100306a41c16100b01000381260422124400000346804e01000405180448140e106410300c60034500c103110000c004942540d11015000e005213200b40a85806450000c1c1400060314012484060108000d0403400c00040038045a0b03e102170317262600d00c1201030748035040c0b009000d44c1c000c080590003e401400a035602280c010142c4040314020800035094900c104090000300040300322030029180c1140c8098064480300006004403814074041987d0740300c850001a0980e50045140800c141c800c0b014100e01c03e0f41802030b2501c4412501c2d0410150041c182020320f04807a08440061544910400c0b62142e81e001c40100504207855181000075406002c043c9581c1d61200e00d245082c00034207008008030418245e40b159549810030402c2d14102d805400f1405180c401c05c1030f40000324000007502c03403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 198440044 1250 198438794 198438829
    0x90201080a110f070602090a0501140909100503101d0a32030c03040305010f0c0c060e030415080402040605030d09301a07020111070b1302041401060e03030405 70
    0x4a4040c0101411118001d010540403109000100001003010b107030058071f0110015142d0420040c0c0350001510021701d500c808044010042c0b0407401980703030618100b40c000c0e40b02141030501741d4440000c81d08040c0b40d21004421203031103108002c2c095264850012407624071101800ca007410b150b41e040221a00d1002c180310700804000f603105c007084454800344075480100d007103903a030314400c01d02507842c2c0c0c20038441600c4035440d1240b6841c81c0000fa010714031804045030b07180a4000d1817655544001c3c10710b001c8400c0c01d407100b03120108580b19030119084904055844880c040d107440d1040005985084d008540281c100c003959a00d5103410031195015203001c480c14024402020820310209065a200c4072458103440c0d9045050141005c244901054452000320141d52812400d80c2a11103008841000041c104004404514901c10311900680300c40a00c0106030410f4000400b45c90144010b565040b507041d00400a50b0340204540c810240c05a010b1401c10f807a1100185880041064802 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 198441294 1250 198440044 198440051
    0x9050115050d0f060e0117150f07030e0102160611120c070f0209010b0c0105100e01180b10050310061b02040e0f0607021614030703110a0e0103060b010909090201080a 73
    0x100d42c940c0c41e001030001c03074030400c420481266030f400034041080303003841220303242046e64406068002001c41c0ea100c142441342814080c84d110014224a10000104290f080680d03c2e0400e4a00b040c0030700017070a150700001d4007603151380c1c0c180c1052000c985107540c0441390042c6c01c011545a102a403000d05600020400c24261600e80038104080300c0301c02e00c02c000b540038140350000710701c0000180141110750f02d5200200295520640c4150002c556409044601982013004000c1410b02c2150401d1004011030046207041c00380300482c0079400c49446240206602104025229104204500052916141c5880d40d045014082d01d00740d031070590081c1c002ca46429100783d07504010003160404804540403107a051802d203034000d45502c8138203100b008000c41208001003020581e00d40c810000b2008000d444c0744c078695515030304154103000595803c00d01107000081e4090707032001400d0086004550124281d80f40d030340010300f403107200c3d04040e00d000c1c607241200700980d85c80080d181d8400100308001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 198442544 1250 198441294 198441307
    0xe0703021804080409090b0a0e0114011422020a020d08070c020d0c030816020406090e12031f030303020901020d0305040f12032c010b0102120315010e060c03090a0905011505 76
    0x43c2c0540314a070414030311141052070160130040341800341403280221100400c862030150a1540c2a65842e030090944800158014030031300107050b003005009030004015040301c1d0302040c40450350180f07207070380c03158480c0d03001c1240100c4c0d41d010300c500e11841c212032410b488540340040d0701402c41498010040e019844485001040000000503030001d16041040075840d00750301d400254152241c104203c2c012030905900160415040c014070840d2800e00b0b0280840302c122a604c0126504000d00304030042c04410b0440c0c0c0143d2036249000c000e0b50187c1d4025a584d1804c6001900c0c082c00d0501c405c04061604003008089100654425006603000740d0401c8100c00000040380688118801c100d5588852282101e0500c43c034800c258078440150001d01c40203001c4001a40c4038514a8410a10b20b0002c00004154038001340c1ca003c0744008c1410018003241c44600818401d4001080c1002c1c26400011a442c0f6460400501001000010400d1005605102000c1901d54039804601c00384880480d20 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 198443794 1250 198442544 198442553
    0x6230907090603021303021f1205060a170304031a010602280303090501380604030506070f03090b010b0304140601261911120a03021914060f0702010e0703021804 71
    0x1754002103400400c0000140d504441210400c0400000007000c40d04140704004200500e01401d0710452004025561982c80d10503041141c01402103010b803a800100000b0001902000080e2818440110344084079030620f007020b842d00b1410001b01040c4c8508a51078200541d50320703030030b0003119070525010440c80b006107001c501601c1c01a220f0300d50482660a002d0b440d1726280c602580003201108210000907002c0140a810321403800040c2c0540c1009000446407401040016213010b004e00c1c4c00200d11600d52135100f0403d1003a04501d0b06000c00000b0302041c0010440c02c040300c6200e82018042d04d51605c101c00100d00421140c204103048401c01c0802185400e200035128100c000001400e0401c262811181c0c010520b9151407060040810000803114000744040031590f02d03400500384814011043c0301409001c900445122401894010b0340036402d001050064a40c400991401c0c105000084c5c251000309001e940103501c55407042016076108041d00300309005296941360151150b090 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 198445044 1250 198443794 198443827
    0x20705120a12050703020c0106060507050c04021b06090610060f0816021f020901090e0c071707080a0201140603120d2f090301050601080402060703210623090709060302 74
    0x640025910b00b10400c0381c250f4154000b8007047c1d60b0300c4c000300041c54131200c2c1a00c0c14054010050200e61088810552504081e8014a20b01c0ba14412620340c2440080e255441e00d042145d0302c0f012600508144580140c12840b131002600386801c003c5d005062824000306208401440201285082c68000d003c0c64002d02c0708108040c80c03040e0805100c484100720310060b50040b00018000389200100266020b500c080a41c0652440720700c0900c0c02481d6200c1d41003141c031444248491510810100300000c0402e402004113012503000440d41c600d00c542911800300008054038065003100c0c602d500400c241c01c00f1144070a040c040e0001d2040040c4131120282032803c100c010a40c4c82c00504921810b010101922100ca01140284140d03a0756800464407100c09440080d0130100502030840003a0059444908066020302c1e0340020001d041c83d010151784044d40854055542550300300300c008801a19400080400d8540340c40710f00703090340003e021a03141d105010416902240d8032045101804 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 198446294 1250 198445044 198445067
    0x1e0b03071d1801030510021c0b06042106051008030706150f0806151905100309020405011706010902030402010801120c0f14010305090c011b060b03010f05040201020f01020705120a 79
    0x50801d00784001c0c1100b4003107501c80a00042e00d181c0f14030b45941e03520040341e008850007582c2e9510201c3c490400499001c001c0c012010b2000c0e4084018000458540c401c1d80b01c0400c0004120035134500d10110741400002c0ba10081c105100182c03c84c0014000d02c50004202c0c0c41f280e50103c0b00154608030580041c00840050300f1103180b19840e2400003961910001e40c0314066600b411042c8420451071303081182075070840c088a0040d540d6a60100b01601c2c1111010034460998100030842400b140d00007421103a00b600300541002c0040384101c6030708c0341000f9090242c04035074400c40c61403c0540000c1c2900b001441780396580080562810100b0091442e4180107100301454030100b42e4482c40d0034455240441111030000346044005181000001003200940406849040000c1da40341c4600d01d82c201c20402c1502e03401e03207404981c01140c40074462481600c07808140044c5034140340c400281801c0d501c0c0784003182030780180301c141c022403c0401c10958990120540c2540c840072174205540305002c0070b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 198447544 1250 198446294 198446299
    0x10c0204141501081012030c050c0a0f081020030702031c09060507020d0c03030b0103151401080609041a041401020a08040b0105061c020906090604030c1e0b03071d 72
    0x12003801050780b21156021100c21090300d5503032440d543c0040349000040144940300d0f60b48070380c400d0000441e010365014140d05001c0ca00343d0300c0c185120303400f1070840c0129a03c5045001c00c10a03041000740c200303012010264505207070500030f403101c40d00d9441019829022070f40b0041c01c000b000c41c806a000f0000c07142101c1030000620a1503a2400d07100009129484054031103508201c00689600c1c404608200165840d4039000007440168408500030304003d2501c905040c3d4840031207504011009807180100601250301000c100d190700010001d18000c0e2501d80070b005248184000501d10654241414400750b81c800300c84e83ea40e08049030070b0041c2001103400380d407000404400c095401010300d072096000d00780c03136003259a8500501c1124131420380da00b010781b40c488052000d9a51a41c000f0040444c00400782c9040c81c1480000401e29442a403085980303010f4814100524011071101035901c1c00c420124000641c6001c04214403441700401c0c40c07040101003203400c420351400d402c140480c02c601 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 198448794 1250 198447544 198447581
    0xb090a03050a061e0204030b130309081e0c040605060a080c0405150909240d05030d061805071d0f0111010e0d0806030307050c011101060b0307050a23030105010c0204 73
    0x403810f088004100d20329091a44803ca090141d19401d1180200c80840354400040382840d80d0700031355150021151036040b0100200b10000007821081049820b8840d040d0b10101c040700b2180c3c810380c1d49020507a03c0103501032401c0c400b04006039943c05003501c030111400c2c14410060744d00e03c1c20005103441207170011540305d00d01a134000c458100100142c001154191655542510b4602c0d144004881c401804498a00300286041315410aa980074403128402e4003102d08200b2a44040b0090354070680009030000c180100c0380c0055005406034541100c240c0c1403402110910000d20480c1c1804030400038010110902c803503495174480c2d6414801082e90034003c02c2400300501e2141e032940340f16042500007441c0ca402041ca645800710894910b030b54048000d101d18104440190307111006841070030a41d540e101c03000550700c40075000442c4103107200c0e6580b664400c030356079001d80b010030314840f080707103000c03010f204040101800170489054910900f806e141c007004070310009001c0c14200040d5403e0180 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 198450044 1250 198448794 198448813
    0x10c0f030315030f0327120f15020a140a02150c16060204091a0901140105300a0e07060e0a050607050c09010b071104090c0521060703020c06010b090a0305 68
    0x5080142041a6101b55500544000755000400d1741d6200295080282d1204050802445a40010b03903150306203e40004c0140000710b0700c07219442c0051148185400350000b8051107a50b030b01144c180d04505031101091300b40b9200a078000d54038a00d55511040d181d03c0f11003ca1908000c00045c0d946102503042e82111010a503d0900080e410502c9071201c21810010b094a24a42520061148010182141c58940e01e000b111175860750180108a060004c204142070104480303800a0072620201601c82661008006510881e0b02c40200046691131034008480c041d6440443e40ca42101c0580c40d004449884050029600c004154401603005000098030b100700100030602a03252101243c09201a0780c1e01c011248240c410310718028184d0b94482214072440c94564859582a030251461081c025120f00106410039041c10078070603040a204a95030005108004156000900c4d25055041c400f001030304554031300b8180100402c02d031000c20728a040340c0380c07c0900e0f0b00650b00003044598003035 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 198451294 1250 198450044 198450053
    0xf13111306030c0b0f090f04150b04050a140102100b1f020f0607050a0c0303020a0311030a02030906071b11040e011805070b120112060905060702030a0206060d02010c0f03031503 78
    0x18142c4000c03074808024110028248000505030313900074588969461400c2e4114080016401207801d4082d44150380e20401d41a41c1c94008508014041c0d00300342035504c40c01c1c80e0170044603064591180311180d0f01401c903c00e803030340d01040380180c0c0d000022010902c0d515110004400074541d030b542041d6000010000e141480c0d00180100031004104140c400b551a403407004c441710721403010b980d0081101c1c0341e01d103000288a42d0092694100c0d525000036441d11803443d00e040f0354000d41d04c800d400350b0044140036107244180000c64000b01c0c181811341110300310a5221580741020341d0050104c0e4999040300c2c16945454100312074204500303000300405c84a1034000108620303484000d407114818100b002c503210007203004554280d4540c585540c0341d40c0c070f8403680c0000c64076105411280b16840e00301c0c100c001002049024050300c400d070040c41d1100c4103003030001d2400d100146203a208081e580c49801c01344c1d8100e4240c0131000d4214410841c02421170800341c014291666041000c0c1314081400801e12 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 198452544 1250 198451294 198451301
    0x91503020d15050d03050a02010f090609050615090a0902060f03011e0801020304150c02010f050c18061e0a020307050a080909010902030610110708010609051e0f131113 74
    0x14200540c040059145840429510b0007160180d940c00c00704814100c000302c1e000b00e019120300c211900c00490550140c0d284201564612841241c160743c6a02d50001088401d000265100100c501c0c80800d5408080014580c13142c0a810412440e550706002c00640d260181100e11022000d00341a07071301e50b0f4600d119040011680e400900104c03024102151140e01802100d0040d6006039a242018403034102c42401400c6072001070040d0f6503a04820b84104291740034942c4141c902000300c9840d10440303a5160016007600c810b452182104000804030401181d5160640340c0c45240c00eaa1503401c000001c1c1d18610030f401d0094294071810b1406000c002c44403000740101541a030303001c002a40c0e2802c02100b41d0105440c003a602c82e0b112034013022035600c19160320b03140042c01402c940085135525075032400c5030120b400c0075952580319010481d0b801c181d44158441a1911400c00d034180c90092506019501c01921550070500440b800134203010041999401a074001081500c101011101c2e0400031b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 198453794 1250 198452544 198452557
    0x10141c06030515090a030909052203180f0e040807020d0209010e0103020102010b060405091b1306020c120a03050307050f1b0a050706022e11040b0408010f0902060d02030709150302 79
    0x4030302200c3c00076500b0007012601c2002180d040e2120b222907400c01100c080030380002490710705803c0d52803038529110003550b41d0300d4403080d0003511000d0f0b190f1721068038aa6a400c9070381164403030715204a010000d0f0344100c1901648281c128101c103496051900c000385000b54410000ba611500850000c04c1500803911400d049901c01d8002300100035055061040070701640c8201d40e40302a802001804c0d002049012000003503983e803589203010715032081142000340d01c0e048440180d00072104161181030000d11740d108050000c1c004d10003040c0c9550300410700c1c803009280c8000c21034013082101c2500070b0181517501d00300c2c04a100c080607055502000d179803a401f2090503241841811400203080b8004030b40f0010b001a00c240d9804405c0302d54104040d08091903642d984425074804400c0900c20010000d00003810001c401d8030781e258a454082c07400d41c0d940c4840308003850301c1c0001600050380d85800300c8490066a20016031250742e880390607208030742d040e4451030b000d0110600c01e2030342c1070303050707004044 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 198455044 1250 198453794 198453823
    0x120902061c0501050f361e0a0e0d05070c030b01030812150603010b0a020a0b04030c030207060216151209080309010f1e0b03160303050a0e10141c060305 67
    0x1160303139030310405c034850313060540d419004000400d0310484100000b036040c4080c0c408411810040c10080c2c095242034208544c1850080d00c240c0b450110180541101500b0240c0681e00340404072414481e1511079420124040601c4000235012007042540c10b681c0b001036810603c184415a502d081c2006142c1c49007181050300420800096807401a4081418100c00c0241c02c0b2801e41e802c0c01c0c59120300d54030019806c000d520076844075070001217401200c680b05501c60381d100c0d03001700c1c200c0ca0045c0c504542070708240f007075411000068008800355140d100441e0300e0031090a100c004521800d40e0040300900f00440202d0516a6a00500410200550140d03413000c008011a00c0d0341a009011140b0302007510817500851440005d2200b0560081c3c1c01c000c000178280c5000c11148442d062048445a10490101d100400c4080d4295000400f81807403041c01d03030b03034602c0581c200f04005103464000d803a140d80184021515003131548a00c00142443c0300e240804000b5a03440e41011561241c1e01c000151 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 198456294 1250 198455044 198455051
    0x11040e0112030906180b030a0c080906041e02010309080d0c1209030c231c122a020708070602070e0a09021807030906020f03060414011203120902061c 66
    0x40c0006400e2514150941c160790f900c110300e070402d0401c036184d41603141101c120b85050304004c10301c0c2c1100d800840c0500c0c5464030009086c448210b001e040c03045d00800c0b149103600720908010208144800c14080340c1000e41c3c00d221001c02c07501c016001081742202c06017030504040f9520f05c400065078041c004964103a140c1e445e00040389994a820b032008810000e000a21000c668800141048c01000941c040050f6406901c0c458045051814400c101c10071034402c007803000002c0d401c1c1c11051074511b8100c000c1060000d0301c81c500c070b100c0501c00b20640740094231a240c504580e00038424401d003400341c2010400d80300f03980c0d502d2800a45d180107600810034040d02d10713400f00d0442900da10400070710603030280042400095224901140800040412041c55220f801c0000011b0b00c910013401600500110f85849061080a10044131300000030703948000c01b00001404401c5581203c1494250f041c0b426401d0065005801d00103004450f200a4011002043c84040324070001d00d040101480c144082 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 198457544 1250 198456294 198456299
    0x30305060f031c0806060c0f0703030306080a110d0c05041d070b280504030b0106200a08031906030b2a090f010822050102091c112211040e01 62
    0x15120712501da081038080f060a03201d4102d8900030700c03140ba40002e0003040142002d02010f001414070300000040516500014028000c2580510a01c0c0c0a08600c90003010005603d69402183c0600c0e242000e110301508118242001000341c040c10207040301030014411111042d8007290416034400c684040350042c88030100d429008101038408070744000c5030069800d00203132009904d4600780c50500041220400000c4040380d900b0522a000302095502c1419030348450618010241010900341d40a41105031070b41d01141d07908040d41d80010898101c003045a08150400700100407030707031000b4030485196041088414440c58040e03811029400000c04d46408000e10721010311030402c065a200c048004100d040b54400d151291f44039a40c1c9038041101d1801c08003255800307010701720445882e9000030340781002d4105541280c4085031058032581000c4059910a02c40e1014a50107900841500b0741600d10030703c0041c0840c2d92110410307030400028080441302285a403103401100040d07e001c9000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 198458794 1250 198457544 198457549
    0x290313020a151709060106140403080309030711060a02072102040f0e0c030f030706150902030a060303021605091b190903110108070804060f06053606100503040203031204030305060f 80
    0xc041c1300740c1d45407015141d03513802c0110680d605241c001914880c8142400b0110002d01c0003001580903440c408011070b1104258074004070081d52a08110b80130307503000c1c0003652440307400249100036950051820225112155a44110075845180280d4460300f04a107416801c6010342c4100c2c0305111340c205503003d044480c0245035580c0417949440d01d26038420482e0f60082202507004078510305103007031441348055031080a001030782c000743c581a0045654400400425030100403854203103c0c06010b0001c1d0b2440c00c0c001607a030f240010b004d420960026900e000b01c1d141d1500c00c44202409807000c0104202001c0d00c02840040540811180301590000d400d00c69030090445603c14a10b590741d90400c0d40c0c3d41d0361080042d00d15040000c1c00300341c40340ea02180c070380e0320304280040310340c0c01c0340c1c1d40011420790003441c403010f0362202c411040c4640580e0a110081e11021a41d5001c4949402c00e03030b175642c40d28404071303241d4851085540001144841400105607058000c18040d5034101c400384611503a03c1d08 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 198460044 1250 198458794 198458837
    0x130605091c0519030c06110d0f150918050a0b01090e0a0206070f21050a02070906060512040c18020702040c030c020d1803060204060e0901290313020a15 67
    0x251881d440f501c58406011210109402c8161080c54149a000b0a650300c1c0026110505001c00c0e0803100820009130021440c807030000c1d2180441410703c042c2c6041c5e00c4142c1d0507155030066074540d50f00c2d0b520040324628007403a60015240c0c0001110410655800e100818100030701030b5240c42c505000903151480000120021a207800420300c4d8500107055581c0000298510401c42d80100501c042c0c143c03001400d00e052441484585400e903840c414000d00034140740017600301e01c00c0c5918007007041c082c0c590701000703441e02d5044641020190791210b052000c40c5c107603d60700004280c0d04a070340d0001c038221190041e2070380c28801d88040c803000001c0b540c1039050352904d1405d80016407001c080128aa44207005a1503002c9104885c1c1c41e01644a072195003e03a44103030005004207090b00b072140950f04100b203900e801000381e0b656050354034003442002d20080250380c080c1800000c0210205c1e007180000c83c1c11030741665009026a840307c2c1e442c65803010700c900506045010a200020100d00c9204418 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 198461294 1250 198460044 198460099
    0x309080309131a1003020a09210305250305120c120f07090b0c0a14030418110903011409190f062406090e010501030e0d0806030313060509 61
    0x14451901c02194003407150040c0028020343c0c000603160010004035854005007400703049101d6402595174600d554020b80303404550f034850300103040303003012806c0c04070380081e01ea000b10780d80341c070300035940705058004d092150042080000710b502d5408101420907400800820b0040a1940901c0d941e42c4e443c81d41d030103140200344200c0c50191007100050070021682d00e08690101c16030401c031079000d49503148141550040c240c1c080b242c2d030107603c401d81801482085441e560102200071880c0c0b60a00313480899044151407120b17001130301c1d4106c1c0005000d614040d205e59a0f000340007003210016146071036810303402c03e6844c400d00307000e02120000c10b0440c1c5000141c12680210300509001c80740e650780c40040070f0003180c92841e40c0200c0314070724100c106058000c0041c4040e81e0748800e0030341064207012500c2d1041c3d0003a4140340c904240c035603000d2008140741c200e007485410724103c5541c800300070a0443c4030b071b0301c1c0f0400b9030104180042049504140039000014007600c00203103108660150001564010 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 198462544 1250 198461294 198461299
    0x2031c14070f09170307060c26061203030105030a080904061503051f0b04030b040f080708030a1103060901170f010c09080717070e070306050303030a060503060a1b050901090b040f030309080309 85
    0x4006d8400401c0a94204014910b00341c0303080c480e0001c00072032007000c821150140d0a965134928050060500d03210311840f21070744400b0050751540d450440040e03504c0d01c0c0c101c001891500d01113007030900c0b552684d001d40000d00c0d0702121064005a0740710300a0003040112004070302404501d500070a40715048500c1300c1030f54500380c0080e00c0c05045490710302860200400031501d182c0b1041803d4001001e02e0007130001148980c1440e03440c1e080c00c4e1020300c2644c00e4807100e4194428107004101569641e6800c090451b2034803070000324445c0d5491011420848241201d500a60900b2460440b8640c080f04e410211602d0800b600c110b5a10b0b11003130341940d200070f442400c565001103000e00080d60050600e035002501401c002030460790307400c046400d6400441d00608078903507401c001c00103410240a901da00110b032010030400c0c0090040303620180d001c9600240d041010100d001c4c452a40a6840003014041102d1580e03144d40e9078048102c8204454042140007410f000c0d00015001d90000a0b101d044200 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 198463794 1250 198462544 198462547
    0x60c030e06271c02060901050402130902131409012f0901180810050f040506010608090c041a031c12021c050f15060a02031c14070f091703 61
    0x9004203050b0b460800d4180d00341044840b03481c01056042044031400f011804400c154034400702641c040d0500c10000d04001040e41400204001683d421a1440e6001001900056840c00c00e00200b10409043d11203800354610b0248240890641803440c144100c907200003d218409825002d00070001e4624845010b0a140c0c032451003c1000580c042c0c0086207040c0340401b60700c10b103410100d11800302c9901010240d041078005a101041a0160302d071b00c1072990072107503501d081c1036482c1d0b03641e80f00500c03c210410030b0103030101d480e094082c000b00c9248207008200340840c5110300c20f107d004036040070035035110388141c101d0100e0700b036a06007203080b01c2c10300e50322500c82c51203c82540713501950055902c604104d0940f0540101401107100e0a40200c1c0c07079141c1d1a0007458900d500075811844000218416139043c84102e00e4541e0000807184181040059650b0100d110b600c9040075000d04448074000035803c0c0308101d0b0050744584c1c50241189950344501000d03a4500300303c28030007054003840a06400 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 198465044 1250 198463794 198463801
    0x1905090106050702030a020402030406110a0801240c02040e0111070507080118030f1409040905031b0316021306030204020703021f0603030c0308090703051002181507030c060f1107060c030e06 84
    0x4089e4040c40e07015004040c00300300d9000700d8015449030380c0000210004a00c00b80010310181840c00c003542c070003500008400c0300c0346e140010064240d20740001c009114985510954941400030b402110440d0760300c0c6120707612520145070aa8850740140140c1d8035940c41d00d0040b81e54182d440e59801c1025425488072003e000d0803403800c0321002e100003e2200c10010410504240b0780795841a041401c1c0504040c6486000401c6032440980080d41d240d00070742c0c4280210603558087e0014060101e50413580250a0804502180040e00e000c1d400a50f0161010030720300180342e008991440b6001031002014152941c05c0e0046e4100c480501020340012110452400020701412086400490207000c940c41039a4a03601c50b4604600840041c801c0341e000308041c119211001c1c407801085400311030704030010144004001d49401520005420881e804418000340800e0340d100f0014403504040c03d0012070300101140059502a4004031000703490f00d100c8000386441ba01c03420750701c1c155400c040c10b04e41c0c8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 198466294 1250 198465044 198465049
    0x30e04022209091704260703080304030509030114010302100e121203100f0b03010504090302010b03071509050103051918050318090619150e0a0f0801050c0f030403050d0b1905090106050702030a02 86
    0x141b05000c14591840340540c04408504080080e52150b446035a0706170b0b43d48803100c00d05080d2641038994002c2c660a0f1701c0144010307612072003601610b0100d40351208003071004d0030003d14240c41440328514113001e8025000f01c1b442100f00110312426403415401887c0350785400d810321001d41882000340045003800103201514040d0071076040c95000e4800400d100b0b108500190034200d2960004690101e00541d003400f480e0041e02004c000c04013400c0402c41458064580805000c0590392404103d0343d8401c0124070030303a800c40c0110015001380850340c56140660b4507020400014040b10301c10701c2400001555490300484248040d40c0100c0031a0301c141c0f0780740d038030600310422041c01d01c14001d0800b0704d5401034541401400082186001055a05103803880321030844e94090501d03801440308004600e40044c2c8002266000b55141c1742482c1d07122401c0300300c00001c1c400c902074660701440208600c203200c40d60710000d80a54200311100382090b6a86c40050340c4030722410b43e0003074158003d0344488000d0f2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 198467544 1250 198466294 198466349
    0xc05010509180a1d12121b03010602010204061808030a0c03050f0a0e0405060a050102070e0903070c060e01020f070f1e0306060608040b07020a030e04022209091704 72
    0x5001c050a81014000d240300c00c284070050441c0c5080580791341c0c0010285500d0210302c4040c10070070450182070a41140485440355202d01180c01c031040600c10040340a80e600e4030201301150546560302520781d61601c00081c040c1d40903110360000984440c01800c12085105115412565400025850401045030648620503030305010780910406000d000c800c075201600604074440c056452106044030081080125880501a2805002151f10901c460390700000c010007515142184904140c0d103a0301d00d9451440345401c008c00f0844120310015200703410100e10070805400340c00b950306040607210030980c0c551740c0340f00c0c0c1d207500c5d038803020100514211039403200c3c0c0102e0400880004d06c1e440b501c0314400d91f8081d074401c0000031030380010131083c003001c0c0c4407168000b0344910143c0b00c00701c4d0b19140200074203204281da9115986c0010b18409506e00041441042c0408040080e00d49680345c02c04402050000c9090310141d40c20340544003c03080590495042c0d80d071192188011a686c5070007201034 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 198468794 1250 198467544 198467557
    0x504090c0e031902090a02120f190c0f110d050f0702040216030203030601140c06041401020912071701140115111009120f020a020108090712120f020a0c050105 70
    0x1e006071841d010750a514184601a02c907500c2491202c107120140c0f05101032420000c141480c404d1060012801c0020050011900284803554560954030303083c8004948a0310107400920340d92805100d140360b41d4100486080c00c5095480c0c48050091100c001d40c0c8a0040e6822038001400400c0014583c3c1c0b0700c01c01618051b4009000181802090302900c103040783d20080a034056030001c4200500c039a8030540b20000c02c5082c240550902000c40b52180d81d0380405080201304600244981c2c5013640700754190b450345080200081c0c4400d10100310b441e111955409951003e000304203011350401c4c81401000b140c5641c000311000c1c035a01e450204000345210420010410031011801c0000e034a0400c083d16940042e140c002450092501c0c1c03100b00d001140b0760304d4003480003c202842d1626008101e060620780c0a082081156071110300403810b102c550381050158201c07452049040c0102c4804060800c00300e070b240e19450200744001640d0310003141500400403100020305101c0742d4030660203000ca = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 198470044 1250 198468794 198468797
    0xf070c06050c040803030405030912030a02060c0708190f0206070201020408061f0803041e050d050a0f020f0303040b180d050a12050f07030e090a0218040207020a0305060705070308010806070504090c 87
    0x40c10f488130089400c40e441a1ba05462a61011928410130314003003440746040200742008528005030300c20041d48070100104150b40c03c5901254420510403038004071040b00d0180c1440f403200b15a000e0010703022807403e180c03010051080d07500243d2014014801c035420b451308600103220903078540c6410461240005108400700420718400210103100700007030005048084001240c0000c0704401070240000380d0b120910640e60400c691001c9880400c880029030f401c044000041c416900104101c001c61a018070303014440040c000410a44403005000111194409400c10f1204001081051585144041c1c980c1e0080100079001406e01d0080301504111800c01d6070600d00e8024a6100a80051500f600460203150801c0c400d45001112035a1003490000d0031800c20706203945100e00c000d0801f1386140501d0340040c1c00010b554980a9040c01560300104940282c0342c504030090003a0090350003100843c00700800810071a80103d0070f00e11a500750340e01c65050a00e4500c60744c015060040c103100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 198471294 1250 198470044 198470047
    0x30201141b0f0d09050f06090a120507170a0c0b0c0a050f03090114072607080115030f0501290a080601030203070309050a03092306071103100203090606090f070c06050c 74
    0x1843c04a480c05240085801140601881c0080c1048a41032100c024207540303131a001040b800001500d04c1c1c0c0c00e800f0542407898a035886140a20b0310080a02c070b00b50748801410004500e2120301c50340b011900130050300c41c40038284d007500c4030744c0e88071494024444000081a018000d0803400b403151005503030f112030280c0010840d06c50303070301c80c052801000307881000000760281052000c1404401804080c0709081d01c02c00198134288200a0003000107003c0e000c00402a40c1510b02c503988070b038225107000010104100440c2d40d4444000c10140740b02d0411036004d0440c406a16000255901902d1201200d601ca05d08071f41e6949004400a5000522410900d552010708002161040203042030142c1300b601d4403481c481c10510440c9256600740071200891940400a42d50b0b500c031242130b00c40f901d6000b007614a01a1800000905004148000c010020710201c10000303e800c000508034090307401510b011086440d030500640012004907012030114600c81c403d00002170305a4000b23070380a1007440916 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 198472544 1250 198471294 198471307
    0x30c0306010c21080708070f050a02031b010605010e01050a1d040626070906050604090c030e0307060902040b2715120105040c0e01030c09020a031512030201141b0f 72
    0xe81948000d090aa4035039a0400303a0f1000c0d454014515076041000c5003000b1040c2e240c60031000302004035400d08882040300104015040d07a00800030b03994009a0b00302000a649104107105001f0b007114483c1500050041042004550194040710008035055548000c0803020f00187c80b4090741400c0d50340e80042c0d940500085030a1a9841440804070701b4001d6803038a01c02003426803400c601038100c5882d451908808008039a11903003214100c41d2404804900c0d003582100070780c000c00403110707040114040080c2010030801d00364050322400c1d1085404012032201d000c20720000c010121036044142103c4031407041c1302c860b94801150f11205d8200e205500801010100392955100411200c0aa4580061000300044e2540b214041c101c00d5010011130b41c0b4540b41e4007402d80c2d007407060240c0e0300d5001400310045482900603041140104c25401c02c0a0741c0c1c1c18906000004815003a030065103800320240c407442035031118602804c40301c0020717419030a0040c5402c5156001404607500ca07502001039 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 198473794 1250 198472544 198472553
    0xe0601090b0705100b0603061c081905040602010c0206010e1f0f0618050d050c19050303070b0a050a090203100b010c0b10030b010605070b04060506030a0506190b0102010908030c0306010c 82
    0x24802c40b4400c0c80038121340d40042030941c0586030311102171441a41d040c01040100e07291f801101d030441d007405040908404140c18180c04038440c40402c6054103110888001034687c0000080085514540c000c00500f0303216078040384c640c1030a014803030942c0d1800307010a01500100522000754811a03410f8030301c0d550b42d5200002401e101e54810404a1492049400203001c60744586c401448180d4551070320002d9503942031340f2007801c464a50721410742c0d00124004001303104070b0903020b0480035040320750312070031801e001d00190001c94050122608200000381c602050b0701907401300d00d6000e4010810b0308000170080c0068841c41801d28100f01c910005d0f403003c0b4444454050041e440000703001e1041d400c1d82400050150160000424000b0821504000a00201140303078482d030808000525a11080000381c1040c813040d03c0580030303100d001c0500c080030b0004026a54a4a0b0001c01002382c05070f414016403c2c1e450380000500040420310000d41c1035801c0d000259403000c0149400c000010300e5546 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 198475044 1250 198473794 198473797
    0x1803190809010e011a0f09010f090e0a0f051e0d02150a0b1306030302060702160902090a080313050109050307081002030601030e1b030d09030818040f020a0e1503010e010e0601090b 79
    0x211181341114005c0e04851420011380080124000340c800b21340703079810078403d8080100076200e030b0407903e0f40e07802581420540a01c10000016405020310084840606045695145401001141070642150990f441600140e10b00b58140160042c00300e5100c4002d03010f00c114401485c2108103500c0705030300c038403541e0351420000f50b102c03185100044107030460600038a0020002c10b86010342d0310019201300015800c0342d18204542344007001580d61001480400c2c041d242a0b408040305201c0800e02d40301c101c410906503000e40d0b10a036a81540281d83cae0042540d616050b100303031a8180c1005111040401560b0019588150181004602c4045409d2024640001c2111604d2140a0300518a140b8502400081c00d40032042c07509800003811921000c03840d10920400d55980150b6018600761611990444100032144440443d104d0b02c2d071043c080c240400000c1e680780300303914041c0901100592242075905842e0101800c1819a0070821080003902c00602240e05120103140c001401540160 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 198476294 1250 198475044 198475061
    0x201120f0c0819020306240d0501090f050c03070507142b030606080c0406030e01060506040b0a03051308070b040c1e0905070f0e011b02040609051803190809010e01 72
    0x259095040d1804030540c0c0c0c18083e03541e80e10031485004000348001030f5580c401001c04449907200e10280c000a030a400c2c103062042650184445040c01c00010b600b01c8d01358061244d8028104c1c0901035581c0d020303038181544c4802c880001c08148144407010210f440d000820703841c07002e200104e82c03246501104000502d44444040000e11107410030083e421039141c01000005c00b00e070f0401500c542040240401036010305d005542c00c05543d2001101d01c42004d40011004000140816548649502003040760340c0c08405040c020a003800c0100743c80c104142d80d00041590410025414124155600451404040c5c41521f203000d61a80120f440454190301150300342c121440c94006c0e0b40340012010503542d005200d10140040805201111500b0400c018540c10003460044a550400725060181c3e4a28010180d0090700d05480880d40015aa01c120f02868000b613842d1611131880c42000e030b03284140e46a2801044d4000485456035000d06101d54102140c980081994603211480c1421a500700 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 198477544 1250 198476294 198476297
    0xc020406090207081b0a0503072d050f070e04021c171801140a090603020f07060e150c030c0702011209021306060801090606050306060a05040e0906040c0b0403020d0201120f0c 77
    0x60907040c0139602d00480031010780c1c1c174000781c0b40345951601c0c2c99460340a120406041000380400ca28406c040c04c40400354946007160401e40f214916041aa544031031640c045100c0d0701c6070140205001e4039510200e44035a9004012a22100c94042e41c07198088807030200300c03010f1040c0ba1002d09101c91050103040d01607914114040b07607550741000100642401400706032069070800064801c0d41d80154501d00382c500908026030390312020400f03d13203188103181c4060040c62030442c0200b00d010b03020a416030a4121640c4401c0a500d90030b006407032911003a2080c8140c804104641001940942d4005800c111042d50000b200c6096801080800942c2c0300c00d025044e45e86d00e024403500d0341110206000d04030140e42000103909042010300548400b0b048c4601c20b40d000318811203c07e00c11400c82d0007410b4050040d05450918800281da60b041c260390860b20410300002c08120041000241d504980d002010100c0c200300a03001543c81c07040c2c103000cd18048c1d4590240740500846030140040d0850300c0e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 198478794 1250 198477544 198477547
    0xa020a030b04020f090105010507020d03092705060108012402070f09020306010311130326220501170402040f060f0f0512010603020904024b0405010e01060c02040609020708 76
    0x144100b1020300103c04c02c05126420311401400140da005081d60302040c0d054503032252842c068181507800d51090740c440c00301400d00c0c0d00031a004c00609602d0411041b81080240030949801006540703002c424000e8044010001102c6c030341401c104c0301d0702c1d101d42140d03006a4842c20f8840000c5040c0e84c44a0b002800700300d4000051000f20f5a040c411200d48070000c1c500c8508007031801d08140e00f244050301c03010307202d10945d00d0514540e80d150a101d41e0352221100d036050b0f840022005920b144111070070b4040c01c00d000c00000144035405a902034140700d01e0b4aa2105560740d865080000800303440280c0c80d06507036600d2010504412206111026011a05c0c0d000c5aaa01d013808125580045426000e0683d040810410050315040e05c0c040e0010341c12500c00c20060030446d0011804205400d54000e800b05d030f5401064000c61045400459150070084002c1a03020481030006a840a1048030b0100404900401000b4842c0e80210501c900c0148040303a104e03a02c084036070581c5c00c180016a01e8000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 198480044 1250 198478794 198478801
    0x10050403050c010903081603020c180f0709030209010b0d02070f140115050307121a010e0106090509090d030c03020f12070305060d030c08030414010504031722140a020a030b 76
    0x2044180b00c140b0003403a00e002e1042c1156903414460040100784809080d071161800b04040c000d000c06248804050006c03025059215040d80d944201901c0084200381540e011a0720540710300200e03000d88c2d03009050019941d10b0b104100a09500130000d00302c02c16401d028000001d010007141d16506800307060458443d00c241c014650841d4488000a862040411010009618086a0340c0222404800180300d14101814504401c1100600000c00780d264035001183d84120040c441d4140c540e036645a50304103407102e0601800041c1900c0500803030b4003044510202a00c40d0304201694500340c80d015003407a4800310214503e800070f4044140020000303040000840e818411560300c490308940c0040701403040d0724090140054101e01804120b40000001e06001c44020204003d103050b400030032441c036050800a0411250644103100051441c001c1030b038828003100c00d001600112105840c00344001d0392050f04031800400e1050160050b08083c1c00503a4444800100560107008015490715 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 198481294 1250 198480044 198480053
    0x609050a0213050409030201060b0d021218031602010e060703050903010e1f020d0b12010b01111c0c06060312180806160c02220213080a020303030606130510050403 72
    0x1400205036112062050001400c460700c503038078480c21a80150741c00925010709060403070241c4950b03040084c1803400010007001c2000564010076a04848140903502c98a80c4a0102e13460400284c81341456402030100342c0c2c2c00844202181c1c1800d10506001c004031030380c4070124696410074403094000c00c2005c01d05111340d00f028020341803400d1600d006800070300c41010303080709406e54101d6942c120703030780c08500b9180c410000c2e0300860782c20000030400b0f4803001a400d0000d010742840010140010040d04920851100008241e007401183c0b1054110280448800700c1d59206090000d692454a0303840020105403007081a1a0404003a52000c01d40c466503c0d00340c0500c2c041d94030600c1d80c0d9100304100010045130300c0211158040c58500a12681010700004007580140c10031a000e0422400420304490003690080c9401300580300624001c030780d1000e445440c0e20075440d003c0c0d0142c0040000903007a1070904000c0c14191386492624044544800100300190204508a404036200140520500 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 198482544 1250 198481294 198481301
    0x5030d030903170103030f080702010e03041413060b0a03020a0e04020c070305070609030b060402070201050c060c030a0b03070f1a13080c1203130302040b0103090503070c050906030607020a030807210609 89
    0x1400f401c00c5030f003190351440e030b001403031b800012600c1d80401001d00040349105e8400e42002c5e10040140089039107032902e4001520300b0313400d000a0f9520a00806080322807075051405203500711140314a1650a10350100010750107540014401c104004000c8080d00a81d078030b038406007089144a000608030302d421860b01c1444e00078260000010f01a0710001040081c13042401294810030580e070160312000180f0050701c69010704405800580201e80801102c0c140c518003a6201c0e4410350f0050020307480d40001c0c5925080580690354000c0046107051040d01e2038080000d600c4441c84066901d020410700c3c21500740c0d41301e50007070f243c030382c1241040003428600040d9118840740c02c20040c6140070034404803a00c1646552200074040da4807000001207682c025800724200581003803d480c0c0d10101071a00a904254500800d840341a40202191441c1000210f251052891741c000b0825820355480076510140018020001c006400c9208207071f0000691840000e625411800b0440c5030401610034241c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 198483794 1250 198482544 198482567
    0x3050106090606110616050f030702011a010e09060f0105040506030a020901020d0806030606010806032109030d03060608010303120207080a0206041406100902030a0f180308060a05010518030705030d030903 90
    0x40213691101d0311200e82000c109140c000c0c070000181002000701c40da095070740340500d01500480720401b02c1040142c0d50190429801b01713258414108060081a00544d921100c2c2c680003a0040700503c00101d0a04001c190000e03031003c14103016042a540b400050900c2e4001c88180b01c580f41c010030004010358042041e0101011b041c01c3c0040e85160007404280d035054010709241c100140b150100301c0c1a1020701c0340991598002e02d00743c202801211001900b64081c00c2840c0c024419104100611442482103a05640c11030f9100d1059074a140ca0460b010000c84200f0000180c0c2041040001140080100100500c075001f404407441d080c01c0501000300d0b115941c00498100204000c2c2c0d02181d660707008103990104070016140d48851a00100034003140e969450350b180f80041d00d070a003400d003c401c55240341c031070b56800805549810501c10192107901c60103000c01d8042c07106d5042e50a0b000e1070040318400c0503040720025641d4100107480c1000c0325058602003a500c401c11800c1c5030340580030450 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 198485044 1250 198483794 198483797
    0xc01020f0a0c33020313060501060e03160608010b0a1701092a090521010509030306100906090513290a050a0b030f0405150726190506060706050103050106090606 71
    0x3951260390810603003911101044003c19a001000079291040c90080000c80c40c0c00150410956171610000b5210310058902a8031903c1014140d11039007420307618590a540c81a41d0729682e507442c16000441d01d0704491005810300c2444442d8444590311204042d000b00004440801d1a24680d4035107105041d541c81519082d4096000c000440d5402c1500707041140c806448143c01655400015040a958203000c200d007942401f044c06603501000000d0b6014a400303c60071407140066a40940d040d451a11800d8045107029104220900d460503609203c021550700c0450103a5200d0103035192604d51040d402d28a4403131103000049400c10000703031405000150b910700c1015080c101c02e05442d020060400d0318801c0c080c000a002c02405100007520a414440b1019140c01c2102000d0700008807124201c108802c0030003000c41813800d0900f11400b490309098008106c020035074080001d0200184031580281003085480c1c0021014442c16000790300480001840d00d00700805007058030284d502540 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 198486294 1250 198485044 198485093
    0xd06092003031912060503010504060902010f11070302060a0c060c080103030306120b040809030a02061801080a06030b060d0c12060204031103060105150304050a020904050307210c03050c01020f0a0c 87
    0x59004a20200c40a5640f08604180945030006020744018080a41000b60554200740a020800c516a0001e0110501c01d0300c400d604260040000c40c0c1070402524401450792105100f0030250400d480180300a45203443c26110043e250f46030340096400d451000c10016002500410500d03a00d8030907100901080c0070141d828071300c19199140a410090000f070081c80001800c01c40035a41001803002199000d8501d5031528030140407810500a401506808110003200003440f60160384101c20030307a40d0003d02c02100e40c84003c20b01c040d07040d020030704a44080b081c160101342101c41c04521500d241c4074040150f40c41e400e5182c50221059441c207070320b00aa0010005220554801d40200c202d007a0417060161243d945081c00b919048440c40041d4115019000380070038003002000400005004e91040e00300540e0802d000d2152252514142c800520030404540020b0b01c55001058455602e400240c1004800d03e082c00243e0320420342c14000c502d03000e80390740807c0780401e05040e2240c0b0014118 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 198487544 1250 198486294 198486307
    0x1031406010f1508090106030219030c05040c1202210903131a1c02070b0403030902040e0f0d1115010801140903040503071a120f0a0b0306040c0905060d0609200303 72
    0x44922141601c42c0c10600501c4c00000c2e01000c42507020100441d0014060380c19034030000c0c0161102c1b0100e000554000100f80ca000c034080c100340c000c0d0840c0100903a644d8166201d485c1882c0000d42100c0144880e0101800e10080f00d030302c4804280c2d00900015000e555140c500d00b180000542c4540d2041d40c2e03841d6442c0701c2c102a64520b20170348580d500500301c602c1c00085186d210720000e110700b4400602181c640001d101c241a40351f480b40c01182c0c403d4408100300e45811001e560798000d06020b19920f41c1c80110f40301036051041c03a07c1140c00b54001c0885490407620110071042c108260001c10712030707540b40d100d100c852b03445040c266040310600014502d003500305004a501c9201500070300f030110004000184010210398112140200303240154001c5050046042c40e001e0016142c071402e00d03040030511002d5190108503140240da008200342d50a0f45003a60b588054100105007560110780840580701140030790007194200c42c0301e802c061440221500080080821460129000307602c1881003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 198488794 1250 198487544 198487559
    0xb160f09051807180f05100c0b0105040b0d06050109140121081b01051e0703060608040f060b060a0c0201180602101109060705060105180603030a0f0c020901031406010f 74
    0x3906000300703401c44044aa640c3c030710003035400f050088840150320340c2d01000000d080f0508020b03442642c0c01125052045440c3e003908680001c800b00d006401c80c00403100401291409511403030003480041d05005602c9421780381d05e011580240e00c44d204040d16004d80b2551010300c500006c0c09000240300b803100c3d0b24114001d208440c201c02e04001e20441c030020306901c041081510740419420300070003d0103103160480100801803c0885500040c5d42c4020100d80c0650190090006480d074640d6103130f102d80e40d00d44401c2c0303d10301583d9084e00d007565242c8050001d0303200c00c1d0052450400c0c91701d90072500380307880c40014501a94150018052101504140403160340481c2c403110700300000710b0108000250030322240080c8580348080d0f6000000140203010400003082840c103c44003207840003a80030f01103000580d0b46604441e0540d154000b0003e4240322805141c071070010180915010307010020981c085030700d942003130700183c440e0300c10300032111803400382006001d01405628425454513031601c0c0e007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 198490044 1250 198488794 198488809
    0x403090308090303300c0a0210150902070803090c0306060d02010c03021c1d030705100c031404170c120d032a03060e1b040612090b160f0905 62
    0x34204070300000c101c2c140d5901002501c000d090418801c030281e0f21014036001e02601c0b00c0011003074404413400050380c102c005906031440c801e40c40e006030107070706141569400205480b0424074400d401074607010451103504c1c4041d2070528070805500d45e480c1080440380f460b009a032400d803842030784110104040354172800010040c156080c200f80b0302803038043c42c007a130814902109003480c0c44000458001d280b98061840d13031001c1403031200c440329400d40380281501e55411b401150741090046100241052017141507040c01402807808444051075441460020350060b8845404150740b00c002442050781404440300826040702c845042c003c500a09580f2406e50322070507818507980781002c8946181c0391690880c5044009000b140c0c09a01c800b000d40104a1802202101e15064000500f48805005803034290841460442d04083c9400000c803000750140d1940c0440a8890340c0b4000083d011840a6004000d40000a006940d07603c000610949400104004002515400b00101d445880 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 198491294 1250 198490044 198490049
    0x307050c0714060913020d0c0806010e01020f030a05070312060b04090b090415020a2607021507020304030b071b20060708041412030a090305070e01060206131103030d0b0f040203040309 81
    0x190170504181d600000384001303000f84a074100d925800c000f01108415882001c881c440c2c0d000742c075440d2180c0a10401203a40b80c0b503c00080c4400c1d402013041c03101560050000c5d125040c4240b52048040742c0614184054032900d520180c500d040102c1c06002c82003840c06140315204080d917640390700b0720707081d2901c1c0114144800e00303401041e07000510240c92480b4400040300c03602c00807080610b00c00840940c8000f83c004482240c018000e1480401086c2d01c0d82c000180640d503550700079800c15096882e203910380d5201910780341c14445035240c80b5280420800f401035495014098117400c0390400d0021411244c0100b1465101d210208114000911780390292003d0b87c0320b84c00d646c40704c0030103100440e025111000c035002079072002084001c805640300790369605a074825402d4031151b03a40e8001d0442440800c0c05118056004080090414007c00c0911099103004907500501d507214a03010034159840800015115901c44c0c0d801420b5060003080b035080d50406440452451619460017003a114090 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 198492544 1250 198491294 198491299
    0x503090102061b4f090204060f050d060e04060509070603050c0a05030408040e010810231302010c0212010b01180b161406010b030708070305090c060a03020c01020307050c07140609 79
    0x191018010000b8507000402c502c410725490401080c1c18900384e62045156400c030b6984d030091140045000c254500071748040b94610380354800c4c0641208000d640316040b1080755400c0030b03a03034003000485a95403903280d0b00540c0a04400119030418648660074000a900701034281400c00d01031000d4003058008581941d145840c2c46a280d03101d6141c15442c0d0700c200d60100e4103843c0c008001044a06020031010300c506e90368503041140107044e14805644043c00440a54000c130010002108200d91680951007544140340403045e0400300d42c00518405030354609258541e54520201c0400c1d41c0000d0318050103c0f10070b0211151518060954082d0f00c114070103081d043c50000000803c101e04000c2c05450001060103580c95582c4170588425950021984900090810004103d00901074807981d17020b0344c0c0c00390250807403950240038050765500c030504003c10541c2c204402c1803003071802c0c0302443c011146950f076030380e41d208503180d42403070b00000e5040301420a96400650702c0300d41e101c404a40c42e040c0d06 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 198493794 1250 198492544 198492577
    0x102070909051905010c111f0506040e0607090503010b0d150e0708030c030a08130c060e01021906091a0c0d050403090513090c080106030b010509040f0c030503090102061b 75
    0x710b181850802d80aa44600010318281107003104000042d00951104110307680d4030003084034180042d40d81d03050303603407a01d5205c042c0d40411800d1054075900100d0b440389000e440403400528107100703a440c0c444125621800242d0004052107645002c1c0104811504221810080724078240c4071a50651000e10020710019510081c00002c1d04013802540001c0c141d40050b240c0362901c0113402516540003001d400c0004d0480800280f002402e18801454103410001100c10103090190030b07074000c0d650603921410343c400e5a0005455440755894116000e2154a01264100aa24001c2501c1c0c04100c1d61150005168080100547c4100181c40003a0042072000c03079646c0702c5040580b903214564100b99001801d68010260300800b6801c5074015900c100d50100714980d4410b447c0b401c82d030107030000501311190072004101502e81045000c0e00103000f0080110400c482d95150038000009600403100c640000c10004040c0d038040c026542e1125240b403200e00d030b03502032503084501449008051062202c4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 198495044 1250 198493794 198493811
    0xa03080609100308070b041b08030a080907090e15060603040312090c09090b070e0102030a0e010302070212031308100510050120010f02041e0b1605160b0c010f060501020709 76
    0xb8020356078011a0000f41003541c0b602907051030120480115800c0d030318960041c0800560a50710590780007200d407050b0117035003085003400c1d0445200300041c0080d030301c80c495280c002c14440040c0c414103012240f40401003c240315804c029001040c001041c0794810b00081c030800000c281c000b140208622842800015400e08a10b48204503001507084413650343d2400300b03070354100001014594041d01c41c68a81c0c14160001301d004a03500d2007440304907800101e09000c0703c2c0712940682c01400d080352009100500e15000c06108038a1500f03c07030070038008540d01d200100500c180600002d40d618150700d001348000e140179440001521050700c00c40b4104203050010510508031030001410540b60b01d002400201c07400e43e80b20029400030701444c0600c030f8000b8460360070220300a68560440300341590503402c03d5601031070213000440c0c42e88142d409004041d0500c08911942111501500d0b130951000e40f1071000340c003001e00b1510402488040c4502d0000107015583e000540001202da00041c003052905 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 198496294 1250 198495044 198495061
    0x405040c03080f0c160303080f0108030f0903120a090e010b04050303030f06040f0507020c01090801091104091406010f14041a150705061603050f0f070509041404060f0501080a03080609 81
    0x2c298038040301a8045c081101101c0240c0d40460310499001e0340c1e41c00090f46940b460380c141280213110b5407135194410400e402d48025088094600301e60010291113100300c1c6500040402e0307000030280c00024000d200184181440004500e0240aa003000c40b400c241c03c010100e541e070300c00501030041c00d00c440f400090283d90b5039040000e412200800c2401142000c4001039a10f9011010b46404201c0d00a0040b50407203051044040c81c58010811201c0e14640c81e007404010710910303009507000c01e102c034a150219030080000e80d0003881d1146902001c107151031804103584400710902845281410100e0703500c0507101850300d0b01001d0480700f4500201c285842050300d032194040040890040c0810483c1d8000c0300d1280884156443e02d0178440c07903550319103e070b107141c5045422a4113001d80e10040b0741c160b44104081d01e1803c00140001030800842841e01024601c04c4504231219901d0399001c540000240c0611401891941d00400e2213500b070b80e402910761480206002d006103141800500d102 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 198497544 1250 198496294 198496297
    0x60708040c03030e0f062101060203090325050d0c090501090902010f2a0b090606030d0207030b040206130909020102070b030709030807050c1f1e1205041b14040b0405040c03080f 78
    0x444020940c5951f500381c207943c01c070381c05c10340c0007500c0d02c0c41c1d5540d000090080c00401290105a0018003a011071441050034106c42c182c2c0240390282059081004034068440c00c0d011045203000704212800140341c480d000040d104142c0000898900708060f020050340c00c408c400400440b20300f40043d0f8004c0000e4501255804c06601c20b200c0c242e00113441003881011201e860140341410300391805680d507802030544c0c070108444d1550041e4010382041000c01d0009203c01e8006200404c0d0074600b1002035500d0702c10407100d400a4480782c0c2d46000c060115a0100107000003000e601411505528003500060f2006c60548006080c040c000034101042000603c1344201c2620024800c25207090074549280d500d28003c05000042880c0340c041d001d800505407030500042d052503131211200341414140b80040c0c000031707104031380341c0c581d4080469000c0f840e0500c1e080074000204840c03078803400030002c0005944440c8a90b1380100d16000034480800e14600d45501643d401180259445440303000143e403a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 198498794 1250 198497544 198497569
    0x30f120204090b040b0d0b010e040f0506040b070e150f0c0c03030a090f0905060d0807021206091006060314070c0203150c0d0b03011416091d09060708040c03030e 71
    0x4a8400200070079020815445525002810344d01000612445420320035030034042440980034100c170100400545080362031540e4801d01c26415041c7c0095903542340341c600241a02c044403401ca02104018840340c2c000807101200d8400ca03010108a4503414000310284034a90b01e215120f40001080841910f0400070f1401580340601201e544900d5110000d0201c11075004503c1d2804103200b0008555245004844c007540b0000c25046c0c000c00c00f40d5483c0c00a62007100126004100080c02c44040b10341400014818205200034040c0d608022400703800b102c546402072002d25161080c8214842c46400205610461605000100c2d00260001030310f400b011580080b124480c07241084a001141400f925502c041103c2c14044201800e04040c240c1310f11840d04061580c096000640480013092266a600d50505054120740e03180c1405401c01ca80418500e00d1007a108414040015010003100d90300008030b103001001c9040c540d86a01c407455441c880130f4200a4003a0501c1d805950b058038105c407 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 198500044 1250 198498794 198498827
    0x9060a03051213080d0e011b1b090b0618062209090210050711150d0f02121b0a0c060b04020304060b030c01090b07080f0405101106090a030507030f 65
    0x1111142c8201084150300c019041c1201038092840042c04050000d00103180d81c1c05a2034120003002140b004440c071414010b07010a044481000d02d00204080c40c0354208010780010030244030a06101741d89050b510390350340c0e15016034010443c0d8110002c007a18000f050210448030540c2c0c0c0c0b40365042c28440d41100c0d407e1002014135076080001d0100561b4004180503109880c1080d0400e11910152841e000f00c40c0d000d400f00f042601d20b8030261a11201c1e10300710861501742141491011090f0f142107540d03030b048801800703500240c980451403018040b141c1c4460010302c1110b0b03074103080d50018118001d01d15400e050100107420700c030400013140c001c001c03810710180c0f04544924090406101030010a03e60034024040c407900303982103510500e02d503020740da4a000b100b0704d0300c405681da4603030315800f0400c0980e4150081c0008140c650700d4a4002c9101c8031141d840314003640c1119040360400074003038214130445d4030200c6030000081d00325055403552a0142410020350307072011f00a80e0045006040d201 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 198501294 1250 198500044 198500053
    0xc071103150921070c0512070b0a2d051603030207120906080f060307060c030e03120304020a090204050f0108180601090c110610090902150705010b0f031b09060a0305 73
    0x442d403240040c0c0780300301d0300000c006480400c2c1c1c0fa154080c101c0c400c122010b082c95082e14414041400c04c3c064a070b4400c2e8101c000c443c24180d680c510280c240d0081460000085d115801c15040511401000a103044264082401c440802d44015041b0b215031001c1c2c405850741284507006141c0a981a1440d00d5000040340c0d0b200d590749040200f0402c941d015000c041030501d00440c09080c1d41405c028032454014005120142c2450010340f0a10400541201080302c200c2041140c0e480034081d8640b5000d21080040d26410144104041c400342074006400d43d500c140000c124682d144074022000c1c10082c00c0914090302c4104013030b860398600300401c006038412080002804445075001d444c01a405540e464201c00e1040803481d100c842c02c0c0c4415904c420364071f00a0114045650180c2003051004024070581d000c0c69500304030503000400705407100e9540700c2099065042507482110702600c128060404c0c4010640c42c0251004003040a82c002c3c1d50302e0700000e02d140c681d0503145001c0c641040803074 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 198502544 1250 198501294 198501301
    0x909040f06021231080919081c050a020604060f060302030607020f0c0d03050d020c030c061305011103071e02012306040c1701210c0e040309050105030c07110315 71
    0x304600340701341c0d5a5a003030800005002c54200e0507131010080104c0c00e420a4a000718691903001e440d402c18000b05501000c03038000412410300c00f0581200230000400a403a040f010125a005400c02107500d12040c490100300b02d03500c00da404601d003640b00c0e5000f07100140c0801c003468058010070164000039054800e001c2408141600025185403801244003210f16000c9000c0508c0410007140d00000c0204a0520454844501d65009403880e0110102100c0c14a00e03250310707440c07230141e003921104100b20450240000f8040c0c00c3c09485c181520750a4558614245058010032140c0341c04803a040400d41983c10101061007908201d1a40b56551030030040c44a0780641c1607a03001c000d80d94030344030b90b2070108201d240c075004583d4007007821303510052041140c1ca802030742c00820010700c4466010140101071800018014031400e400b92a03e9240c40c1e0452400e031401900310b44031a01311a0610005004209808111508031a91a9800280d40b40034238425004645000c0c1246590300e50810a00c041 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 198503794 1250 198502544 198502567
    0x82206180506040605010801020910031d120307020f0102120705090307030b010b09090f0f061207030b010306020304030206240f010c0c12051c0e0111160905061003060b0909040f0602 80
    0xc45000e07130300502c4104400e9aa402e84603080384211140e03150040c000400103a140f90184d4481c0c00c80b03010516801c0e01d00179140322401e04100841540c107034903160100501854640c1044111085c110080c000c5207007000d0403807010600e290080c021002c10034001020380c0651400d0004000444e40300308091000c2d42c45000c449402c2c0c03c121030041c000d0101b6800101c4000798295024040c801c2101d4084482e1600020b10460541e4840324888500c031f16440000003842d250001402140074400c01070304e81c2800d207002810310a015284114615161030440e80a881c11180030403440000c98074034110003143c1300143c690f1481c100b800780c1650b5242000080c244030561036511041d104034150b0b41c4040702c00721407480010303080c01071000180c002c0c183c03010769500a100302010045000e089848860b0b134026000b00146150f00182602034861060049505000d90070002e00d5849060600a490a2172a00c5c40c413401240c2d401807042c14031401203414010702006010440e0b800002c01c0d540c070481c0e40035 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 198505044 1250 198503794 198503803
    0x2011206082802060901080c07080a0507030935010e1605010206011e090203060a15020a050f0a030507080d090f03090602060a02090d0201111009050a02100822061805 73
    0x50000c0c810611090b0400c0e850764030b500d030640e040e0f00404060410340c00300011124424020802e09000104020381400f2070032200c00342161890325500c4a55800d00c0e481c0081070512035a00c0342030441c039643d607465040004000408501040e00e0318109042002c03e07081c40c050300b095240101c49008a0404400703c10754200700a0903140c0a8080b109142d0340c44000703142c1c642c50408484201440c4c180144400e000319002141c00c10350080075070542c25221240c00e8081c040c148085400342c3d02058400d010170405110180805c007111010700181079407900c001d0158440c1180081c10300c48005042100b088c03266105040fa00d41101c00885600447d142c003806c3c01c41940200c5001d4460100060860100c038022210385505c00780c610346000219038010b48141081e415801d00c9805410011900e507090b80c803414150b18020401000718082c940180302c0d100060b00c1d9184c0401140074100440d09030601e050f5580600400c40c01001c10440d410010010103200308800041240c5012200c184800081c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 198506294 1250 198505044 198505063
    0x91b080a06140121020d060c1206240c0c0f0b0a020f031305040504030e1509040605030604030905010f050906121609030308070302090609040912120b01080606070201120608 76
    0x90040080c00601495082c01c0321003485003500c00c00b07030541d040b00b04109200e071040c0002e2015182c8040b50b007850b130741c05c0151003060807c40b000454a0b0040c1400358001d0080728010806003000000c07400c0b0040c00c42d10083c020f20300540c240403004e0040010440010b03944130042403224207480340a92074075880c0344550f0086140000610455216040055001c800c841c0310200d0080112802403500c801c0c000607000c02402542406003007803241e0920b448041c6441000140c114405503290440b00030401203a01a1300128003941c040b00c20400000c0e0041810303001e0302c0003401e22605580f075000d4101e503503100b246116a081480403510307882c4084449001800b80f628101c41c444034031019642143c20415a00c8040d00242461001c150328502a50040800c40d01c01741425280800a0005c18280e80601404586003c0d1110b80e40110036400b040c410415000050140500001000024031340c1314081c019604c03602002407403c04581c0640e030203082108484200788116a40e034000707180c8070741300103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 198507544 1250 198506294 198506303
    0x50c04090507170a031713030c0302030d0507021f1109310b0109061115060604211b1206050a020d0c020109020f03010c08150102150a06030c1409060103091b080a 71
    0x1081c0003840707180410340340c038441ca44c4240746087c40c880c0354904581c6015000c2003a020b43c0410450141d404045000b02c0744034051030f0f0001d203403c00074107845000706060240914403162400030040c040d1140c4004032040c130b08040352031501c0d02c0b0660392491a0011854988118102d13054000c1c40320380d03060b40010325802001d0b25000c01084c2d85042c19030b804030030b00000f86000d8020100c10040700c02040e5405401c640040d0066003880c0d01d4441218030548052000071110281d580c40d4000c10601c00c030103020401d0300901a00c2194600101400c840c842510b0050a00391501d00040030004c0c2d680c10740344080120441071003100c20f8003402034002c1490760801d134001c905288034020340b4101409072554000e1550b4441d030300342d52088a110b130145498070b01641103000359698410783d400d540d043d00b07028414408000031200c2c07440c40d21402e143e20a6001c140480340111020725a0341e100720000380e21480a0030003044201c21407178482c0180043c0900c003120181905c0e0f0210300014006500880340307204 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 198508794 1250 198507544 198507557
    0x204320f070305041e2301060305010c030c1d0609180612030315041a040501060504060809070509010b0d1b0e2803031101091208060f0d050c04090507170a03 69
    0x95410403000e443d000c8801401101c620420a550003d00300d10380c8681a0007451510010349000b04802085203004040c1c1800d69101c000503c14080284078030b003084003c03400c0030001d0004850001c0c111541b101000c1c000c4440a01d461640d0341c0b604c40846040300c4004000c0e26000c030160004841c0301c2001e0318200e000d40602c1150100c80c0000104490061403d4150078008050101c100800390840a031324803110041000c042e040c588890251501800701c5448890b00c1e02d042120050829200400f07040c4d16a0240c007040026448070740d01181540c03080381c01c050303554084180c0e40c0043d1841140b91100c000406070254a5203511081e008401001207a6660307490710030407480301d54103e840b80410f40403101c1090030000a401a0307a24407c800c0a600040340c101060f488007602c0380c0000d003621010900050400540c1e00d02003078644000d490031507102000174000e480704c40d034822001d0152800340c0e50391240c042c02d2007803c00605d4000c01600740b00a0840b042608070341d0302d5459100044001c50310 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 198510044 1250 198508794 198508801
    0x60708092b0219080f0c1c020a0b13081206211609090506010512120712080601051e1602030106150306080a05060610030f0c02061803090603040204320f 67
    0x141070352940a5600841c070b407401c0c55484000c5094540c000f111032491886007c0b105985000b02141201282c03502c1d030050010460309040440650b00c008110b2414610485a80d000080202c03082d030f03c2a00712082e001244c2d596a20119a141000400700110416400c0204640441c0010801e0700b05204046c003110490307813030025800b650040c400c02801c5410550050080d4140408407410251100d02210080c028060904c4000e034440ca0b800c0c0c0d12010025101041c6541221906400940a20340b4529002d82000303124445569010008aa900300290018011400b0307010610942c1d001030003000800d81d40d040301141203058241c4540464102100064200404215128002c0d003180184c4000d682c0e8004000101e4900c0c0da1407418550303110a030034078a44440c421203000c40f140d1b40007003c050524030040b041c1c1c0740c41c00070790300d500750b0007007140280750b886e400c0075650002c1d415500031801540c0b4440380c89200f000c01104d02d00b48104040b00300350f01211401c45038001d10464080d00c0060300d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 198511294 1250 198510044 198510073
    0x106080706050d020309010b15040e01150806010807050f0c0601090f090804060e011e020f0c1c02060705070e070203030a140103030801120203121b10060503060708092b02 75
    0x111074454900031801c180f00c0d075152100150000c5034080302032400007618403060000200c1500c654a100d8030076a00c00300d0300744030b8a241031144074058820500710080c076202200b0010305040340140098100b0040742c010410090141c01521008024191051340b601251a5429a2540300744500444942410b5540104042c0c0e4442e400c440760300240320614080c02c1c86004e861426500c02c505042014000b861822216214030804400c0403c2c0e02400180c84014106440c6c41a042c3c0403520503018100700200780311701e40c1000207000f035050b40c1d856103c070b8450030302c5402d0441e1540281201d440725000c001145d039000c80190320400b00003004000e1005911944411040309000081c0401c0968006110314105d014a10208620003801c441410209006500583d0061185000000881203408440c0c00080c807031030b01000901001000001d03d0000080e40d0703000302401c128280030b40000820b417030b031505211080e0720203154900030613600c54080150003891040b215000c014051304c00400b4110 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 198512544 1250 198511294 198511303
    0x103060f05031e160b120604060f15020319020a0507080708060112021f120e03070218130b070203040f090219030c1110060e0106140d0f0b031e010608 66
    0xe03540a0001e0401103980f40b40c80180d9103600620840d1071085420454000d00c40b001444003601c0040c1d4010380b203007441c1c012480e103218080d05140c400c60601d20700b44403600c2606521400c03940d460400c44920b441007002681144503a4210743d200082c0004100169500060800c1c20188114212032820b0368800701c4a80304d10761400790040c01c0d0400c078010422140b004601250080c001080114002c83c0740d0395220140f4180222032010610111103040740c44058803031040d0100000c0c01652404030b02c0d50014001007070140b0150007421440e0041007914204000c00c10344d1550103920804141040b90000e582c0340c01602c617401c41d03481d22803004a0108aa8001d42e43c640d14a007a28841c402c1d00c40400341c3c054a401d02c00e44041045601203829424020000c0d822020300c040c00c0080c10b07900f40071001100d440160488801d000d1807036441000c4c906140e003103c06a0481da540090240b40080c1000c01a084018110346d00d4420641c2e241601c003444400d001c0c44590a80007004001d0340c42150310f444 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 198513794 1250 198512544 198512549
    0x230d030206040b0c1612090f060e0d03050c03040f0350010c050c010608070e241e1e01020c0d0602040905070c050706030908040b0a090905150103060f 66
    0x5800001c0420b00044050310010740242d013070300c0010304160813242c01c080495803849003034900f0384454007841909a000400c5002514401604180460a101014081072a01030405004511001c06001454030900030b41d000c0103554401c1c0d0365115910404003a84600b00c2c0000c3d2031080480b140c9040082035504500d440c0d01c82809403050b81000380008884006118070049841c0740c000d10b031608407440a22680c040700d156a1501512202e001c034140b42120560303040524180d00206090041140741d8550f640d00c400e01510303000300d1010b01140030404010011645400c020128082c0d0350712220f102d555030a11b48180e901402d00c01e000210203602c0408401ca01380960043c2c00500c4190500c104500d41c2103004000252409664074071180c00c4400c211215030000e1040d183c0b038400c1010511041005180d10714003484841c800384c41728241c6104600c14000c546c00002800a0308078091040c400080c20b9800e03081026203400c09680041140503542980040d103401808203216503c581c030b00c0c05 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 198515044 1250 198513794 198513797
    0x16080f01290603040609050321090102030c040b0a02030d02040e181501090c020307020a03030f090806191e06060e0a050114030a020702010c1e03030b060306030d030b1306230d03 78
    0xd0809080300b4420280e0010f04103607400b40d11000804c0c08510f0810040c501801848420041007411f00705403280340001910108240c0d00410501413043e8004040d24203a070500c01c105030b0380b81c2c1701890603880e607c1031140c541c68090000c100015548242040d05104ee2540d01c1c41000b00c08000c0304894403100f8070542d041680c2404c600501c0310620701da00440100300140100c070700c1c1c0f40540e0000740350700c6016402180050a00d10b02101d005610900082c0103190700d0005040b01c0c10249020035051a130803686280440c1d850a00310721a10b201d100070f06410034070381400c0120507110302000700003811100c1e00328040c1110400010b499486a1240c544a40103070107010309580710f5000c0031001e5400844242c0c10424a1032001d000f0401d0407408110050740d5200113801051079140c0641510060f510041c41424180100040c2d501c0101d01042c003014249000617600304070f0000554003a00140951409503d080000304000c00c400107401e1001d28844099544240440b04000100000580090 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 198516294 1250 198515044 198515111
    0xc040c030c09061d0a0b07030e09010e0c0f07060509070906061103030103020d1b0909061508030316030608030a05090a05040213030602070809042301060f05071416080f01 75
    0x401d062044c021003041e03083d1080c084404466010004a08082a03040b0480c20765000400c4410150042d170302c5488000180e94001142d850301d00c00c640403c0c0010035804412100145c00414411600100c13010264003c008000908000e40c030980d90344114001c04050500e80900403c045010380703c07184002880000542c6141c0c2994240101d20401d950126100e4003008a081c0e0301017106071480e03000d0020300c05c000420a01d1070503c44141d95850080700890035001d8024081d804010003101c3c0d010320050304041030004101011001011541d00c80f8049000102e02580902e600400615480004507440e03140191141d04000072880350205928842d0036030101003002850343d4020f0415580a44e0f080d130700b804070140200d003d5610300d03800b489400035130b01c209900400e107078000540540070624151000c42c1442134042c060b40314802010f4102030100d5802c8c40340300310401544031403610149200c401e1640c2c0b00e0b401d50359001040000c90700355080c0f11700c0141c495000040404035440400c00e90 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 198517544 1250 198516294 198516299
    0xc020a09200c0c120109060c1d0a030803041b0e10030203060108120406120e0303070e13050c0a2307080a110d090302060a0e12061008010e0309040b130504050c040c030c09 75
    0xc0444e422040c1a01110b5494411034008160300b0310a004054689480c1c1c1c01e4080109040900d0300e924032903080d44181c00030101031020551284c1660f03801644540030b090401c001540748641003020303501030500c60040f08108a0040c5141d80c044085034403c0c3c0807030f0080c0e6201c0380e030701d038441c1ca020950886882c1c0c180000c0000510990003410800d007009000100380f110388101500790b6108403a20b102080e64101407241c075052030950b4903010692920104503038100403500180c148030f201d107440d040004480911111800e40c8044609252002d24150341c0c400292424108a81000d10414046040e5564112102c8400325140d00c00070807954a41030224115400c20007941c02451248040101615402c011910340f0b540d080d5284e00701100500301c500d05082181d00240d400d03008012181d040003040d1032a40400026150000c40c22500071800105503c08100301d0200c1c42d120660030b50410040c0f2092282c08140d01d094480159810301c02c40307008481c260305641d081c90200c000030310810000c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 198518794 1250 198517544 198517549
    0x5010911191a0a05070c0e041505060d02040b040e010609090618080d1109030d1101060503071a070f08070311060f0412030c02030c01020403140706230a0c020a09200c0c 74
    0xf01845412030404034200115500c0301002c000b09034100050500c110b0f4140000e20042d001c00c200412900c8205105501c0c00c0000b00f030844640c42c1d03000f80581e4507140300806540e82c9400c0070804421000081005556542140001c0e15076004180c507110700c1d00d1880c80d20018898441c03030005410080da18540140035007000010310002040402d2100b0510004105503000c3c09811130580d15652181c1e201403c244a1508403003141e8030039031099100c1441000482905001d507800c1410b440348840c2c454080c2c0c2012111b0502c0588010040440051028201504403401140c40c038030302000c40d0160380d10036210a0f44000152070142007a0900c0b13005141c4030703100b9000300d00210301d10720613a42054810382055080e40c02c07640044800184082c1418a072940400080000f0b0005183c00300060030745010082e03800b4010414244041c03000103100c82424050300801d061f056020700a410100e0b0342d52440c2d402404416840101daa64144080955045035010303201d000024002034204002e28404 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 198520044 1250 198518794 198518797
    0x606180c0412020406033206090c010c050f0105010605070b130221010b06030108010618050402060415180905040b06010804111e0607060204050909070b1206010c05010911191a 77
    0x104030b900c0345c0c6911011000500c50100790020300800b50062072000082c402240c24602c0c18038080d070541e4041400c1010020300001c58468404003800c104840110508200b410a40c10340d41c00344841d030818000141407540030f00245103450165903a49055281c038040704c001d4404903c00654072503014068010391580300440340c25407400c3c2900004061901ea404214aa04241c1c410360080c2d54483e01042a20254084030188001030f07801007100e450150300085050003180a1a003480400ca05403c04082c0504a24807100000d42c0c9080460380c0c0e1000d242c0050700c8211411075030426100d01241e032650048201c613018030f130f01500b24400e03010321100f44071684050041c69482c48841d1f08c01941c0988030400180440d9010f500090b070760f01d082109110211801801c86007103584220810014100150240c45500751503100b94006074651000480e903010306040058015440c28045100300b24900014140190702954908a202c0c80d160400c41c00b04024810034019101190002d0410305ca00f00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 198521294 1250 198520044 198520079
    0x1d0603150c0901110705060d020f221701021315030f09050c09010806010303050304080307030b2d060c07090209030102130801050603120a1b140f0606180c04 69
    0x1000c85100d10410403010003600c006a8464403010070000e8003205550744000c4241000c00703240020240d092410300462070b10b11490009131141680403601c1c400d04e845003402c807004c8151a0300c100b640c0451010400850314588d100300b941c410313040901c1001c0d000c0c0c10b0090714102d192a0352074200f03892500d2105005881d24880440030540e6558944600a005215410250340903c0041c12548459001e00000300e00681100d009903200e500100000795010040b690310680c03005006032070751200c3d038040d13015100c0810001e5100e14529201080d401000548203022040d400d240291013034070905020321441603d5024600b81c12000c014030855140d078000b003074101405000186044911041014529116003041205944804c01e11001c0d143c00c100c8070300010005513680c2c2c9408030065010344100030403101e0005c0e000c03203c01030340305004000700403441d0440d0050695006c08502001c941c0c4440040302c8080c07081c1180c00349140150006505180302c2d50104003010b190a00f482071029a40c010603 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 198522544 1250 198521294 198521299
    0xd0203030c01090615140603040809040908030405010905010609020313080309070e040b010315020306132301140103060b090121090210030b013b131104030510061d06 73
    0x401100d0108182440f980c44000c0c010040010341e280d85d1044801007181e40e0780301803c5e410126188211903030701d000440b034000740d100340c0c0c1c0341d0b84440b1040840d01408080c4405001c2034008020041480410f4020350320310341c8188001c1107400d446100e144102d00050f6450310b00d614480780d001000a00381002581c0104081084130601c07555818102805001198203c508012800041080103c040070619205085071429030451030400041643c0c00740301140d0040b920b4a500300c1d84586208288402d20004142688090b00d42e1240300e1415619021225140001d19190300004d422907210700f62050301c0c1d4140c0d1107400142020418000d21102075102ca0440c40da1030b102403006a50302c40c1103880e26225601c001c50100041c1c40003401f00c11280c810701003102255120096511040d40b41034103c400f04051240c00b400095011482d000005d0529280603494000381c06c2488145001400490344a54100c404000e4007802080a60b4424030a802c034a442192011100c60010101c0c2580001e02 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 198523794 1250 198522544 198522547
    0x315140f191b020c0112020403020f130902120c0a06020309031c020f010c080708010e0631020c0106051504061b02060904051906050a0303020c10091203021c031103060d020303 77
    0x544402c0824000105614805030b0720042c1148080c0d41c11040c820307100000c8800c1182002d2554020603120f60403220000c0c41081280410343c1c90301d001c0c0d4000644140c024005100c41c0403542540c0b03a550480045142c45010304000002d0780a100008507442c0002c0580600704a041c01d80322003544201d486221030542c041e406c60b000c80381c0d009205003981c60101d07a079904010b042258015280c4072040e00400c91515041c000c020042d214114050b45118448040c1492025052503400d03440380403c24404c200750000a8002d80328205410447c01d4030070071288540c0380d802d0300a21043d640304602c903d030041075070210307001c00c1104030115160381070340003a02070b51620300d10b0000a403c8980c201c418500c03c0f540c000c0414030811032441058083d11054803103002c0c40d0300b1924040d5564cd000c4650034030400c10708100d100043e10400d002002840680070a402d0039141e80340c040c0d00e41404200b45d00d64107510206c2290b0840c4207014845d450403041120902d540c0300d04040c0204100d0700981680c25200 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 198525044 1250 198523794 198523811
    0x9060a210302010e030c03041a03041a040c05040f05010512060601090611070b03010e10050406080c06030c0408120a0e010206010e07050703020703080d0608120a0215041b0315140f19 80
    0x8148024400c0c031101b003015540d16418034031090f020030319200051484060070700030400000d10b026101400303008110782c401956611072a04041101e403941080e41c016041c00c001d440c000603d030300b041d81654807c40d500c0701a00507020400340d80780811112a800140040420070505000b511010f40200940064520242d210b44000e41c50358800e9104202c40b1100a00b0002012148050784025010071070302400403619103c41d01e81d1b140b10520206200d80000000f203958141e03c00c0c2141c1c0244070500c00d031000911000300d801e02e02d412042403c008103040b41000c0c0190b603c08600c1c18103030f0310300d039041c03680302d840d01003040f1480d80100404505501c41c0a00100c089140003011380710350844c0e94400308480382000d4807a4186104c1400008007480b00f4403041c00c0c4940c01203441c91000800060769441a682d0781000b084903102c404074149060082d80021040c40148040b480013030701c0000040c0141c104400c60303c80728140459131b2070308041071000131811208000e4108103001e54580310208203280f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 198526294 1250 198525044 198525071
    0xc0e0a1103070c02031e06070e040917070b070816030e15090f2a09190f060918030c02061308070b040501090f15050f0c01050f0609060a21030201 64
    0xe0003500c2c060042100f00c0240300440c0f50800c00079000012660a11810801a100c01e03556900701130b081206000b4070702e030510600d0301c2c0e540c402030196411001030f4203908130b80a5a0740a903070000105480c00d984400c0019081401070700043c5c01025420081900c04148c104110b00419401c00c1d51031050058801c402c00349552005018010f4400901600c0c070514800d60003868156500f40b401c1c80c0c80100800641849110032807105081800d58000c0e94954031201615400c0346680d0000c00e01c00e1501081040e1041c0e143e000c034042d5000308400f00135446013582e103c2e0a0148184004000404082503200113042540c042c01c801800d03c0400303112203032110003450a0000c2e5400840c400f01d40032808201942c8c0c4910b02c0710040015014040c0345908003064500a1302480500300280100007802024194054048900a00d0b51000030042c03800c290568103144002a94001c2c4510107841c00f24110b80340114230807040300c0e810424040700c8503d40c0080120f141002d801681555030b00d035076462602 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 198527544 1250 198526294 198526297
    0x13091109090a050f09010e0309100c0c08010b04060504060503060411040605060a0c05010c0c030f050304031e02030c07080f031209010603020607150f060302090403230a170606070c0e0a11 82
    0xa01c040351021031945842c1340d4610346200c00030461616a13060426080302080044120f03044170b01c3c1900c450b0101c1001500c00d982d2401960b2005020803400e58001038039043c194040d150400d0115070520201d03640e4810003040d901980242079064006c08082070020300ca00c800d112102c07802504c0411110313907520002d01550021140e100106042c512841d0403c80d0a108001d080c03e4581000da05542d00c035200100501c12440c00c1e01f060050010114042c18000d0300c1200c50345801705410080d071500c10000a440341c2054400340c9e035034462440007040000002c1a42c21041c0d42c448011410f0a1440d84041d6031040d000d424040c4956030b0f4500800075849043c02000003c0c00395080701140842120503108848900c2c408200043c40d150050006981d21101160090313094541151307111185210360343d540c4440c1c1c43c03d121881d00081c000300c1160b0420000b401c81081039030b0f4050301e0703030f00c0506025070b520511000a00700302d00310300140041c0d0081c003041178118444040c000380c0c2900798419001203 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 198528794 1250 198527544 198527551
    0x180106030b1201110703032f070602070c0909051c05091905040e060f0901060e010608270c011d060405121903180603090b040303050603011509050f07051309110909 72
    0x259040085c1c80010b040e01401a56101080898100001c200d0b246400d0f07500c100c0040507072100f501c0001c208062002c00e4041d141c43c80e03080010814840d80d0f0341200801010710140445071400b4038412054489400c175202941e20161342c440b545070400744c40c01c0040d40041d0070410004141e840704c010900c0d403200d00c20900c56040c2c0d94010926402c140f90041072001c0300400c03030856270b8144101031004040c50030f4031700d04480f102e0034121500c0d290700b0312440750f100d0801c0300c4035121804445c802000000000d4001c4100000703032201c18110b410031050301807004907026202c1c0c001c0c004020400c010300f080d981600540b10305406803201200d00300000102140c20300826000a100741200c1a100c403034804010000f0842030608200f10798150750f810742002002000a01030694840c0003d103952403e401c240180c0b201d80c641102c10036154850200200420b87d01100308900d048002002c950181c01101d5100d950280307030203205842d245c0322101034100d81d0305072002590107100061090303c491100500 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 198530044 1250 198528794 198528821
    0x70f240f170f150a030804060e0117090a1101030b1e04200c010b04020a020a030309080405031e06060d05190c1802070302010e060105061b0705091e06180106030b1201 73
    0x41906100070342c506124150a0f81521805010204000081e0401c0031a005c8801030b042c00c14941c651640180c804ea03206103010a000180c030320820002500100b201128035204101d0740030300c441400d004604444403040c0c1c094102d500c0e80c00b40440c00300c81e40280c1c2d8002000900104030043c580999a00d10f14003520002802c44020130359800a020030b0280c034254000544085090a00c038440c02580c601d81f000001d0305043e0764803c0e01007801840d5049074043d09001c0c0850b02d0410825280c0c3d1201540c00d170244000b0b002d00c02c0802c150307203020f00c1c14148c031507080802000b03141072944000307040f0700151804a459000420001440010580414040f00040030f80180c446c02241000307400d6506003820040320f03030040001440940e032044141e0f4060000204100c0a030051482490301e00466078020341d600c400250b00300a03e10300c40400360300700d03181d044c40d0200140c1c4600045c410b0b004400300503007402502c02030040c403985100c0e1340b103015680fa00034015101e441800510500711601c001c0c0381107 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 198531294 1250 198530044 198530071
    0x105031f1524080c09011d040204060905130908070209180114190e2a04140115080606120703090c0303052106131e0608070f240f17 58
    0xc41c1003250100300e155074003032030610300a10b15080c0902e82c1c4034440e080206051248001f03500c81044002c4000d0580c410002d002195960303105c40002d4419030b0307284a800d10030803034083c110010302c005003e00302c1d9007503210881506101842c1d080040404006041c102a54040d40440c0e400742800d004014079001e0013400e60143d03080000040c5425800102c4010b0000d00780761601142c95000241c3d61005800d42c98200c2d00d068031090001178444165070800c2c1e105080c0030210340c1001c420302c4204e04076800a030707020742042c091601c180c444203006c0700c0f8140d00c00c82c203002d0f902c540d41d51084200c0c1d10403081d240024008486540c0c110b002c2e19075070400da001400201d022000c080d00100c3c0c99141d10340e4011060781a25103880002d080000401150040c00d80780d1102d031010442d0505007145540459200744119500e42250030303aa14898801c040c1303841c42d00200042c1048918a81e0219000611114011000d2034070041c3e03040e00e02811103504204400e8040a1540007003441e040c040c945807a8182d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 198532544 1250 198531294 198531329
    0x10e0705060f13030b04030809030a0206160201091401020307030e12071b030602070f0506090f060a090809100e01020c060304031205091e0624010f11070b0a0201020319050105031f15 80
    0x8200c842d0089c1104940d074800c1000c05a00c54000070810b80c40316548480401100c031081080740508403000d4003d20800050198242e00d41c0e06402a52040c40c07150b0b41000521055007080780c7e50110f10850f200c3c2e2040420000300421110036840c10003402c044110000c15980b81d0359181240e200718800c2d01e18100514110702000070174480340d07420084c40c4000f000206c0b41407880716100c20014003d03404856030b80c492801004030907400e03180c900c40d00414112005200c0b440242481d5000b2421600600411500c903000c7e140040540e4003554241d65031000d00d2403200c3c040310081c039000c0c000c01c030b062040c011030000b20170580d5260021600d0046c090880c41c24180d400301d03441c01c00c01c0302c040c04271b110600f07225409981c401100380b108500d80c81c043c00440c0140107102d003010341c0c42d00544042d0a0020380c0c22002601500114024421590481c0c0e44444c1c0300044002c8403401c2c051183d2580084040e41c0041d000d1581195440ea200003000510001c003841101008019601603207600c0f200300e07681d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 198533794 1250 198532544 198532547
    0x433050105040c0504050d020a080d12290f0307080303071805060405060a050310081204030510061802090103020412120908010e0703061a0901030c0f08010e0705060f13030b0403 78
    0x18240180303010303501440041e8040801420a005034091180130b0001c0425060070365880c0c0c031600c0000c06d140010742c0c21800303008400410000c00451b041f0391a80c00c10404541c82d12031001d8407011001000b22054400d140741040050100c0181590341e410310800c44007240c03c07001030000b18040c0ca05a00c4008400002c402100c10340300007a80840e200b14401c0c070040016440b0305045401c0e4240501d03089a882d40d41d141d07000358032440354205070140d1184032a0081b5002800c00140107032070141d02142c038211014583d0070f003503c3c1540107800300691500c4102941c91190b8001d00125501410050b00f466199a40e00c00c44c14403000003582c038000b904010140c007580005405015011200017440015800c404169461400d880b0041005517100c4090317070390b903035008103154031420010000d4900756901d060420b001c0419019400e01010322100004031746205100b0695400052005088018a050208103d50b08082c9500e041354900300990b220702514901e80c980078510491400600341401d040 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 198535044 1250 198533794 198533801
    0x102030706061707050406030b04030e0a1a0d14060d02040e0106050916031503081804090204050415050105030f0703080a11030408060106120203011d09010b030316020f0103020a0f03050433 83
    0x49607000c4e40c038041c008e1000c94406028541d0180e05400d000003280455804100d04103210350004a048070718030200d00003100c210b002001c40c0c0805000034041402011a0b481c0601400e0300c0050340300c2c104051000c010f00f07240c1c1012007a42416000000c60035034070f0000c2441c200046450b104001101d010040c896501841440704c01c02d42c2144e0403090608544d0383c52103d01c1480b04107108041d160414021a80d2150400354600f0f5020b002031103103007050315101140c0c1910141c1501c0483c140340000c510760400003680f0380140c03401001020300301d20f1a107501420b503100324400c0041115201c807030402543c003000180020440e0b44001c24042d890030900800d0303082c0320604807912a00420041200e8042c1805000b0203500892416886448412a440c01801380c0c80340c4139054080403400d00070760000c0c1800e1440ca54000d8410640400c481801181244900103240c03000c0741c5062150b28102d880b030782c0055030080c441d64600d0030b5040282044641c8903030070181220003018041c00d40600040030700 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 198536294 1250 198535044 198535049
    0x27020f0d150c0905101809020a0c0b06010807020a1104090516030c0b030720011d030a090506031003030c03020c13062c2d0703060501020613051b0102030706061707 72
    0xb0f45260f0581c01d201c0020308111200469408200c2404a513074101c070f00705c94544004003052841195a10051030000d004070344049010b5624014610000381ca03540100c00c0f00340b080c401a03000d01074020180c0c0d1003015040041e603907590001d60310303009100051410451840c00241445071106a14a0752800c24004411508411030000081c410302c828160001800050281d06d801ca6558003c41c4c00368150043c07040c030001c075174100c20181d00f4a114000c00b00040c8140c00c09030352001d0a954460041c000c40348070135115450003400034a02003010030711549a10301114440c0c03040c0c0b010282c2a4001a50070050306401c07400c6a640e81074100049d42c600c040c030074005110300c40c500c0000f000d0710351081c0e10010010411400c41501840401d1500d44e0b2083c910f0440c1d003018465502424002c500070002c02c0d41f4001d86016110700da02041900300c075941014001c0e07074000000e2644081d4000880810900c841c0f079581584818045e40c000a90b00c0d000f9030010b80213903100b04860350b0a10320300a217001c2c40d55 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 198537544 1250 198536294 198536297
    0x3021008160c03080a050915040804060f0206010b1e040305030a2d200102040b0c060105010306120b0703090809120c0312040e0a050601020c06040f0302010305060427020f0d150c 78
    0x707003440000d03002032000b40e00c6103005c9800101580c440140c3c0b8209a201042d0a4120071070f14200003c014018000d0401e032030150703035072140b1410714440607170360f0302001c2c00b508441c2c8806011201c0212007007640d00c1044520042030303c0c1455900e5450345d143d40c02c801c5064000c0751845030b01c03005401c0070b26511440300f0340c80e04200d5584920848081c00100019124420900005080d918140001d4049034000c05200003500d40e42d40714000615159502802550b0000741010701c0040d42e00d500400c000425a000001e0062545a01005900404154004460020b01802410b00c3c55a070200403500e10b9640f43c0240c581c42c07814000f014101940d128000c0b411580912040c401950240e0643d82e229512140003d0140c40e8180141d02d04403038030401e190701030310003e00800d0304c1146c40411002c50b4408c2c0c80c140856143d55040005840584007564005221504080e080e00080c000c407c400c0c6001928003410410081c0c0400d08a00e4848800d40e50108a800402003030b41251140380c15a40d0385 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 198538794 1250 198537544 198537557
    0x9090a1b090506090f0418030c11032103070903020d080c010b0913060e07030b040302030c0d05040608040b060a0801023405210f040f090b03010b060301090e03040302100816 76
    0x42000103102c43c0103405800d400381034990320200c003545866021400a90b5080345801e5100c0113480c008010300c9e0240e9085808070740301c040e45469800d0000341401c1241110f09000505283c981c00217040307800080c400c804100e8621000005078507506087e0400c540a01a09540c469143c4141429030300b2843e28a4024400700c0204005041140601c600380d560210003c681007005c0c036889441c06039650401741440f83e5000c10b1004050b0004000c201c140d40b800103490840000503c162101d0144d8030840000c0b07840031000800180300008001c0d031080c0001e200421700f07611410000c2c2241c001c0c4000b901c04034103038900100114080355050010380c81d1040500307039a42c2d2541e5080d803901c600024400780321003019000704940303d0300020380d0749015000d8174540c0c9407580d520000007602d11a12442d0040c6141140607945401c041c01203228240001e4421031079a4601090b2800414010241041c80d000501020005a4850101c608103075860b58550f039483c00c001007212445081020920b00b801780 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 198540044 1250 198538794 198538799
    0x6070e01050d020d090206031008060906160f02030d141e060d0b09121204032c010f0504030219060806120d18030609050703030f09060219020609090a1b09 68
    0x1c0c8941281c0c000d01d2070000c0540c4a45581543c00007a01d0002c100030b502030740110802920b80e2001084408031003102046684607224251800e882d541c05031610b04a0303001d100410b10b0400c1c00354404c5120300305140b045a1900c03030944107a80848002d4004105d0030304843c001c1c4412410500207e501c40e48182c0d07600886401d0513400600c207841e0f4180d00070a80f011031070003c0c2c1c502030140102a09070341045091581c41140c40a02c401892084030203c0114a8428600703a040f0440083c03504c1211050500d4102070085c00e006440b042000c2d40107400b0810100000320040e122001e43c1c043c400c208808110b009801d00e00003400c10f4000802c1c20740240c50120380490345103400581d00051400c0c1d030904c00d881e180007550840c10030640da0000780013142004144020003c0c0040e070501100d0103a81c8400001c0020a001c80355244107100302401a4400315600b8480b124449007210302c144020400381c5081c1c22032011550000d01200c0c06003415660700301048449021203c2c65a0402c95894610103450 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 198541294 1250 198540044 198540047
    0xd0b040b0a110a1707020c0d0b01180c05070f240b0a05040b0d030f030209040c020a050d0e010914030106030b090d0e030c060a1107030519060f0b09070c03030b0604140306070e01 78
    0x50307184d030030070064022000442c0559000b400807000701350000c0e02003944001c0900300031054078020321070110381d0341c40d001c100d80e580901c5118a01c070121444e5203040c0341403a1511280c41000402506903103030490100041442103c00402d0740a000041ca00410b101c550401001845400da41c03115000f10f04114004525665544540c204940c0c075081c038070a203201c41c240441c0240600940907400600c0e0038849200d207500012030243d0180b00d1000c0b6000445d80003003c9502405070125607010455a003000c1c4034002c1d0070681d2200038000034000141d47e076529190154a1001038604c0e40b89504003081c0c0b4a040c40d441a0707007240c6800e040e80100312010149020401d01c0c07082040c40002c0100301d64129500c15001e011400045421904480072840480c172503c5806200c050120380b80b610341a0540c3c40060940201000443e006024031038a58813203005603103100103514124205544d43c41c503007070140e40b4000540094002c504804140448850503d440c01a02804140c140025081c000203e60b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 198542544 1250 198541294 198541307
    0xa0c030305250303050411010903080a0509010c0507060e030d030e1c170702101404050a02091f08030910110601050609030a0f06050603120a0c060207020d0b040b0a110a 74
    0x8a900d46030082d41d41c402d40030840d002e0b103200d5142d407048229180940052580c1900800e000c1c1d4000d01002041807900801911001d14500c4020030104050041c4148280640701500c1d081c90103061496442d00160386190070040c403a0440c102089030030038040f400341020028134001a80030f0500308031803c8a540c249a46028103403164949031291810301441d0303842110640410800c1c1280b000036400e20b4100030303440300505a03030591031a25003090030700401d06101400e40200e4000001e055206116002c2c80007503400201840c4851900401c00b000d81d0304864250301c028004200130315122000c080070800c0304030304528441c00f0420030090340301d002803000c14024111101114602e0b9030b100e130a004a030800c0d0344000b0260281c0c007049088414001940c0002d03100b08001c80a40d90090084400c2070114010742d0103010000703004000c0c070f100040c003079402009041e00080c00c100410100d59500703500c10780704030b41c21540c003c840170900110798502c0c0035548442c4015200d581c100064060000e118 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 198543794 1250 198542544 198542549
    0x2090901060311120307111f02010c080c1c05040f0c03030503010e0a050405250b0a030608070807210512030109020901121116080c120c0601051e2e0c140a0c 69
    0x80005c00144005a658600310040420b01c00c107240092810b0540b00a4000c240c023900bc2c5010a441d000010102840c0c041102d41e402100001c0150502c040300401008080c0240101c0749084800719010106112801d048002c40c0310340d035407031f6496040580a410380803001d88102055410403090100090000c40c081d940701a84420346a504084003400759030f05d4049610492601500090303030000a545500300d8810780f00b0041c1125100c0340c0e584260b690350080c5100304000001c081c4e80000030303070342c0310644501454003800480b14403c051210040b0380d60704c2071744200d00300c0d07600080140003940c0040e000c036141c440c1190b003084048c4030224989114031610042e00c0000003103603c0740c0308104010301680c0448a00104442c144c035900c49610210b9404400102114803842000151603c1c000000c2503684000c1000601c00b40c004801f404066041761640300340408401c0c0d054103c0f508800d0407000d020388590f941080750b2910307081040c10f42298a0150010f9000b000f040c001040c4101212000c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 198545044 1250 198543794 198543803
    0x110f07080306150f0c011401230f0910050f030d0504060c0804030b010b0703030e0705010f120f060f030b090d14090102030c0d18050301020304110f0a0308030c03070905120c0f03030702090901060311120307 90
    0x200e076074089d0001100000322a110a0b4090344000900c0760403032520290700140e41041d100d0b805030003280020940c0d5002c00541c0603000070000c000a115a40c45062100950780c4a00500e9041c1920303541d5450b0010f200342c0000d40441c0012405030b00780f40c0d05001d01358400c1301c0d0b4030240c000356013480d0009000002c01a201401d0000700725100c0341e254070f194050f40f203080b42d10508020f40350b1140d10708641c8200c144801d0314850010030120300e4098020400c00c0d10140d1546a29524560040389825280c21604d0290306600080c001925038403404c0c4003550f1514455035444c40b001c080c505034071100e000d9682016009138410310411000032041e880d402d41d044012a808040c101410002070382c505069000145808800320502c212000c40c10b0196004d000315448070751141d0f40b0760041c40303640101145d016844e41c1c402240c80005d820808186840000d020381500d04d03060458001c65513911013070b6503011580e07654030780c100b00384109641c246074001811101c2465010500c01190b40e00d0140301409032 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 198546294 1250 198545044 198545099
    0xa080402090712110309010c050a1d150309010609060603020408120903070807061707030e03030f09010204080102041706010506091302090a0e0415110f07080306150f0c011401 77
    0xb070280d8080c80211400400e204018404502d440d6100b80a9400c162081c6005600304844200d20f280104144c500310b445594840e0600ca05000c0248004151042601d4010002c25801c00e9075200c2c9900551040c01450004944149040e41000880300c1c81d0303212070101441800180000980828540550790600300159101d9000c4000179050003200e5010f54200c0c0b0030408000756041d04519002a00040d00f504500b03599079400c410b409903000c14035032140395002000000ea0300c1c07865090164104000c1c100040c1019201c00301d00307007280e1141e005507810307010b09034101c0c84045040006c00d000d084240c5000c0e0500001101258110300751201d400106500802d9164403900c0d5202034000074801d0110380c0170582001e082440e1180388210385100d1075814100c07035121000851003280c400364035003401d40d40f5241d00f5485501c2d0b00e42000c0d000c540c1c85450040f0400035450703118058404c0a03001691180d0390388240005c00d00b181d1002c4070740512410550010846044141c088981c402050038551 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 198547544 1250 198546294 198546301
    0x70504091b081f1e18020a06020c04200319020d02030a060312110c010c020a05030703140f07050a170102090d1101120522030c05010e100605060a08040209 68
    0x60000c03422120002101c0e8200a10014900400180c612102ca40d1451a2040c16542e0600f01c01503500a5003803210400c50350344000d0b4003070b141c0e50010340000d00d03c158403402c60800b503000030351741900c2d540300300d0040c0d100f4810b00c411481d051061181c1000f105e43c4072081d450000c011203da40c00020069101e0010f02559560381c8000c9404440091604141c11556450041c0c6408005e0009004c1030b07071005840300c00304140c18020b4084183d64426000101200103a410045903240ca00000c01c0b60170204c62480040c107078604002c54000f075403003180030402c4140307020b03003251034040410703c10740d0194400f2504010584030780c004141650580440358080f4202e43d5140e5029101d42032509400041c0c42110009004404082d0801d4040907661311840e070110504280c261041a10900300491a003c007114007811144d07881c0c0c02141c480d0500003001a86902c4090856022010801098201c0d041c0c4a000501038030421000d064121040303130401000d1400141080002400280517001c080d012 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 198548794 1250 198547544 198547553
    0x6050901140f07060f09200a05031009020f0d0c06050f0405031b040e150f091f0b270403030f0b10050c0601050609060304060c0e09150a060201020c07050409 69
    0x20400d0340110722a00d90b560b00030100450009600001055800d94940021010609030341d00540c19519000040f20032410303102041440001004101158420424a80000c0e1900c0038089035058244c100400545003d950043c044605211400203208180705000c031400074807d464000261355052400a40315541040c42d02d1691065400099042c412045e44480040b00c151400130780f0203050303509020440e105c50500d940c1c0e030011204060701e45070b110005120010b01da20740941c4100c2c0501114855818481c0817090343c0d4040c3c81c0b01c29030304d4036409008203608028030803516480e040300303410700300317944803503d4084041e4003078401020151100d00300c0140c0c50042c1c0103905480c0004100700b0088181e1440031b0590b60102c1d00e90096409004000140343c03400c90180d88190340d002d0070082c5151346030707034490005105241d1038806121910000a105031103d480300d80c81642020540014071105000300482d41d00b40303910a00441e1300402c03820301d02003800f0651601700c600680d80403c3c104443c2c42e0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 198550044 1250 198548794 198548807
    0x301090504021c08030901060f14010e0616080705120906070f0203070f0902130b04080c011101021213020306090a03120b0310050f011a040e040201050f09040e030903010c081006050901 81
    0x901440e40f50380c10189030a0010034002075006041c0c0d41c0081210750b66864100088011a1282c000070100da040346d90380325401201614084140200f0403450500207002d400d050a414107800e4418080c0130a20000300607041101112082e280894075003040e29100020303445105001d40101105101e0684500b192400c0003030348017030007c40414010042d1242042002504102c840e03544522045900003804180181120140d58030b11001d800a82100c80054840b040d60b41902a00d40d0342c00c105010910184080c0e05019075030030000710440650a004140c60038034080c2c01d070740c12500030703440c10340010f80c0161100c41110407840c0082045450340000a050011011004c81c0c400d08190800081611219a01d816030b207890700c4481d54032030142c04a20440c06680240c0040c4502500441c001d98014000342519900302074a89180444840214081e90041f9050459991010409210910f000c3c0603070500310146c1d1801414a2800090742c280c00c840358030460080c8400014031070a982d200300d0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 198551294 1250 198550044 198550069
    0x7030c11030607020616080603060a02070302071a07020a152a080d06211203050c04030510060302040b19030f140a03081506030403120f02130303092306030109050402 73
    0x4050b00d0b201e15160101035200d00c012250062405e000030442a4405d00406c9014000e1001400404040d5036030181a0021350015406406601c544800040e0005070711181c45070341e030300c016000d58031105184144901c00d00c1d5500143c2c264501114036001445c0c1c400382c0d040000e00d001041c3ca8202045200d00c0110450b140710203000034800146116250394250014000c456521005094240855082d08030400d60b00100a0804610071482c1440902c039801c0345422030a019121441c15580e5a100d81c41c00070880a1810364503165a01081503103017a201c0d10b01c0200058901013132141c142100c41150064501000340ba46620000701c030f046c0056407007070003088dc0051085902901d00c0e820046e100450458010480b80005001c9450b54103020054a014662507190b4034200301c078a421243c040c04103914030354036059082c00b003240034507010700e150341c0210b0081e15014100d80c10120074002158441c40d52144a6035450050603151f00c0703a10440c1c1c11036658840029003a00c0364030005500103040e5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 198552544 1250 198551294 198551299
    0x50c07061a130501181b111e0105040507050f010c060f060306050c0705070518060d150203240406080c10050d020706020405040b09012603040305060a1b050403050307030c11 76
    0x107441901c00b1400e60740814107071105030a1540707000d280440c0d140d0030b4503540304c20700808041e4044503503400e50041c1540d0055290100c1a5241088458101904440704a8100706e180c0e440300c0a21060040521903040500300c2a0340454a100c0c500002034411120f458000b05115030351010100d10401c1c42d44644e018542c4414240801c0c20100700581440c0c2003202c0980721805030500006082c41c086190600500f250070040300d040d40c0d51000c00080301814030b000c2c1e0b510581140301c1c4408880610003548107148807000e0981900d151506001c0d09003008002c01c0c016447c10000b440100c00c00903203203886401c100c82901c001896070504894174003907060700041d031500225a84040084907009002601c00c1507508016246032801017003046035083c400c946004049004039100f1030009050885040c2d4220110f0340b40039560b945091601c0c00c100ca801d10110399994642c22402000c0c1c80c03126100b03e80340b500341d08080c19510340b80e49034852010000c0c2170080321000c0004100070401a0802079400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 198553794 1250 198552544 198552559
    0x2009010f08060906060f0c0703050c130b010c0b06040209040e030d150f030b19061814060904060216080c0d022a040b010311070308180d090506031e18010f050c07061a 73
    0x164540a0b2f5117603400135001380f1400284203103080c0c22240c0d2240f04072001c0141d42e00b071101070540d03d40c1105030f41e001d0405e603002902040000f505880c0c5000302034820f00303444002e556031450f40004004a034042d8591103c8101d2012080000ca00301c1710300c050581e604810340c0707812030311600700351401e29801d041c0402d44142000c3c0001000b10061154036940c0074144030510052102c1031b4903c0480b80221007040d4800c411401050100e06960b000d0641d522030280c214240c14500d40b2941c1841d0402141e00400f68801c40034426111780c148032000c9201441c2003000408064940b420705502c0200b62280c0c041c95a6040e20905684250824a180d51302e16002d00c0d900c102c0d50800034070b50700d81201c800800000b00c0c03d0081c0c4038040000c10000c0642d144da20752039214100010403640d40d00180114000846c00020000b20500741c0501c2c3e401028094071081041004030002425221044600e5403100c0c0f030302d0308000b100305220085074026948000002002199240c4051410114070035507608240c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 198555044 1250 198553794 198553799
    0xa030605220b04050c0a0c0c05040e0102030402100309080d0c02100903030b030f031903050a060b0a0c0b060306040b07081306020d02040906080303011202060d2009010f08060906060f0c07 82
    0x44210000e21000051041803192601480920050302c10175110307411400342c10090500c03003600c1040d691018a01c03039005407460650391000141a0ba003c1c0c0c0340c0000c03c0c0d500000340003c515181078001c51691481c00e050218809540700c141640c042c02c407540c4200c60b103461808105501c24800d0071008590705104225a620307905005008140c00c0c41024001d01c201a15607c3c2844d0000940c2c420425800700710b07030305140c01d44003207000e04005000d020030b0701c4c0c8403100410315103060342c00b038454138540b80d80c1c00a03015450306005c01403003405007940b80a500b205041c400400c2c0740680d2b00f80c0c030013b2401c003654241c9030740380d441d0542151030381c1c081d18240c030206211b03030040c900c3d0b0001d00459062a10521280b40c031340c3c00e41922840284070300c00c8201041d151810060410343c0141004e0b2441080001d8110b100800725410441c40f840316041100340010086030780c0d0703000705610800c5d1020703207032052042c030b4040c010642142c005403007180b1035003000c01c800e440d2444d64021221682020400d489078240e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 198556294 1250 198555044 198555079
    0x20d080702030c0d08040b1c02040e0708010b030c091e121e013e0f040612050921070203070b03010509010605031b0702010c02180103150c050904020a030605 69
    0x3040118124464069601c072207503d403401074a140390b41d07a0401241443c00d450200b0380d21196011001405030101000078030083c28041d440600014a00c40820031080d240502d170041c458101600b107518100c0e428020b01c1f4580c8100f400782d4941c0002607624160070059001840c20781c891b90102c06034400013041412080350004100990038540b42120700700c0000d10301100600380ca945400c0f20b41400c0c0100c407500d140c00301600e240c0503068051000d00d4010081d8040c048451350103440007036030038903002034200803055002d100c04002c3c0440c500100224140f441c880390b100c0540c515407001440e81080c20b40c1800b0302043c202c82055600408449030650364100c40090394009100d581d2103104410000508140a24104d07403260b120303000e4a00c0c41060240e03081d17403a03810a200690401c00f00040b00001600c4242d1001c0c03041c049400519400d62541c60908101c400340c10f8a0701009042000c54401d60b0f4102041d55160750b011140561903020401c0220010720107584800e5110302070304020300100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 198557544 1250 198556294 198556297
    0x120c05210d0f120504020f06030403050306130b10031a10020109060f06080618030d0501091a0619050702040f05190516080105131d0c0f03151305010603020d08 70
    0x150026000d8440030754121006a954801403a520004602e03c2c1000078821820b9512880d40184002c0c8281440349032403022541030b82007100c08a0100d04c0002c14080149045c041440d0003449901c4284800c0750200d0205045010507480202415220307000341e10116031048804891001c00307040e11034000701c402c2009020700002c486c1540e1403031502c2e503c41410b690354000c94041d501c051000f4881612030101090204000741404092404180319240b50001107003e017034000c0903040307808103e465040e2030409a404010601c3d03071107444100500000c00a5040600c03408030380c2d60420f903499030703554000714016062420031411310174600804c2203500b10344070350f03006107401048100b041079555070340d00c11131082284642e9502003030100c0010042c03440c01c0d0305941d41e0310801200118503508000c120a0001d50742040d001d400d90030a5000000c5814102000c005c900c8084008110600c9111a0304a00c1007000e4007820f0020341c10881c500a000303094000b200259409011030092074590704041c4843d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 198558794 1250 198557544 198557599
    0x3170601030f0e101a0d260d0509100c020c010c050c0402030a24030b040b0601050909070f020d090509010b070515040c05100f080f062403160206010f120c05 69
    0x215864940c010018400e041030400182c070006e04107403001c4089889408038850040d142c0d01005031500d8003851403041d440041e20b080c160340c0c40042820f0074081421402c15070380e24005481280741c45620707002c1d203500007180c1800d88020b080c9a031440c1581d0620904191817020002d401900000500c030300380e412544908101c4007415106c02d511000d0f1120000402c1944c84040c1c113425440002c180440d403048240381d046441418800d1420312680045121410101c4120707012400340549642c0545d014400a50300b0400c0b0300d00a0146410000045c100303007818010300206007404940c140030047e082281603680c02141c40403218504e002d1070201403c0d1441e02540c0d01400b070091054403c42d0240301c01038120151512500003a82c0d400721079040580f00100010391000f10780900041105e40c500460204003119050960740349007804004810b00f026401d00021903000d0001040b00d0320425803c00c06403102c652000407807007128100713540207131100e0300300e40d1b8848180fa18858950002c188184c00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 198560044 1250 198558794 198558823
    0xc08070f08070e0a050a060e04030e04050709060903120c14032503020a1b150503060a050f030319200a03021519020c011d061e010303170601030f0e 65
    0x824a4840281c070703407220101d02c40c050071031628070040360904071582c000383ea01250b0420000f5402c0c1d6150b03005000c114080c0c1d402e5000c160000740c683c41c5800c2c24014698082aa400c0040035030b840c10b60018682151440302926082c1c0c5000800407482c400c5211501d0107030016900c0e03540d0440300c00c034a0744aa0001080c0c1844d00401100e094003c5201c1021211041d0507030050b0500f4606920f441d890401c000180708480c0807020000b10342c0d8001d050010f0180c0a01c0e41d501500c03842d1070f034140f08401443e41c021a00c501e4a601061b00d040d60004221182c0361710050030f01e241990311150030b45401444120702e4204482207039800f110f1f103000107400138286000c2c2d803c95903c20305c10000141c48860650364078450f020f4602c0401e40660140c0c0050543c1001e010001601c03045001c1030140c5841240700603400c941000c4188080207507281000104132040c0c00b40c510341c0b5495594050a8038010307020241414644100140c40d5030b0107584110244e440040c000d10000c0d1942020303903100e5040b48040302 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 198561151 1107 198560044 198560069
    0x140903071802091504030c1203110106030f051b010915110706030501050901080601120204180b010b0408010c0c1a06060403060e030915070b060f0d0c0807 68
    0x1801000301400c0050701c801d0b0f0300d03041040e0b8501c60074028035000c0303007800240040b56a1030308400c01c44180e02400b039000120b41c9001d451041064103465070301c0d482c100000060100001c2c030321642c0c034820382c152040d45441e04040d41d4800401d0408a001680e155820711480c58141005100008207040c5020a08151401da628040880d005540085d0725075004110030b0a00c6403045004d4040e4a000d004590b061080440d00100361200c040e2085c0d4445041070344140100ea40e4a052039040440f01c0219a160035a4074441ea1282c42043e80940c82d15482e001e029100f14800d095041e4446a000c034003031110780380045440005800181e020408100000001c1c03010311941a40a486c0d202658841481108002c004905d041146c1120842085190300040b040c010709540958221100c20100d500000455801000d0180091992840c8180451550f0001401c003045614094041 = true := by decide +kernel

theorem cover : BRFrame.Cov 198381294 198561151 := by
  have h0 := BRFrame.cov_init 198381294
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198381294 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 198381294 ≤ n) (h2 : n < 198561151) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
