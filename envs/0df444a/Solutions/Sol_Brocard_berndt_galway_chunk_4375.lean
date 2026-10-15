-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4375
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:25:13.85798+00:00
-- url     : https://prove2.me/submissions/99ee42af-726b-40e5-bff2-a7283ecf997a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 786690647 ≤ n < 786870503 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 786691897 1250 786690647 786690673
    0x5031b040e2b03060e01050f1207063212090102071205030f0702010606140703030209090421020105131403070b0f010807050d02063906010501030515090c0a030f1d 72
    0x9584d5034040c86845056080040100d81802161440b401030000c10f5540d000c1d00c2d0071130351482d00c4540d5000c44001407011010881e02510309440c0000181080c3c9130070000070518038580e90f01e01c9400c032007545000d400300000314070020a5042d40d04241c2d210412007440a41c440c07005000d82c10030b1350391019000c900c102040400340144600da041b24815282e4560070403480c842458031740c00040e419000d1540030821122a03948030f03c5041d00c243d10070042046240e5200c5099010003110300d0740d500c107681c035110600082c940b40c2c0ea8043d00301588800c00104041003810b0142c10343c010b407480141780050010a00c4050000507045074140e40c2504226031f01c29a440003001040200100007940200c3c04000c040505a02040340000ca09a4800040303501514900f035a440f010710f0a00a080036040000184125a0b050003072a412000322403504100e136240380001902040003625040012600040c520100d9020760401c1402c604060800c1081d2407071406030320b902c00705030b60480101c1e00801441d02c1034 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 786693147 1250 786691897 786691901
    0x306010c050102162f1002072c07080c030c0f0f03040b1603061202040b030a0c0806040b071d01030f1806061412030304120e13020a02070b0405031b040e2b03 69
    0x2001101817000d44010030f802080c0702c1c400e52000c11510440c0507802c80444c5104070040b0402544d2403d0512803902c0b801407891104242010b40b107130303081000391024484a14109000d503078001e18212002a40c9151203801403407540302d50562150350700c01c048200401d000314185098410321007004003002c0d240e0401c0f41101202c4e9035010309010450b11100201c05401c0c00d50018500f080f000e0304480a01040f925403008000581d400034429a0103c0c0810041107a2a15865040340503400c18030042100390b41e000c558440a5000e90f4101651201440d4503490389420080c0c4400103015422404141d03420035102805d150301400d5084401941c1a0440e41007200800b8841c90740c1501443c2151a80d07511980c07125070301d0240704102b02c000380124101c0e5891405031000f032241d44000690301c0c011460080e061081940c00708958000c1070208001544001c0740c11409807103059988501c0b5040d0f180054010090340080c16580d2068001104031102441c1100304480448102d80304003009110007281 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 786694397 1250 786693147 786693203
    0x12140307141c110d08040f0c0b07050d0206010b0a11070f120519020d0b04062901030c0807092d0e01030215040f05040c1707080601090e0c030c0306010c05010216 71
    0x1000b80d0050340081241441354801c19002403007150a81007140345a01d61484030412398021208010000500300e08008003000301c1001c0b00b4550000d001103601d03182280005000d03010341b00d42031002d65044414091018406003002c3e118440307018401546a01403200311450080c0c04855038802c0f5004da560404003000c084040903030007402c808140c06036072b031580302c00d0002400c121802900c40410012144c44030594560845000f031704c110030710364400001030507100208845c0090020b80f5091001003907010041d48203a07041e02c010880050002c2038450301d0556134030240c084003182d0320f200aca0022245041641281d0080702e0342d45002c1c4080382012001c1c482c51040d10313081140b2071000c100608003508003035a405114100345403030750b05040c412041000100c81d941e00251144082040d1984c0200d1102d014000c0c9400040b118030b09480080407500c006000c102c0000408000281c89a11442c0c0403a000c0303502100035510790b860520103130311050100d5000c40d01012900400513000c281400055 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 786695647 1250 786694397 786694427
    0x3090a060318020d1509080d0c1b06200310090e03030907060323190608030f030a091e11131424031e010f0612140307141c 54
    0x15503002c2c9900b006042c641225086a15490280510703801042c9446203466180c000e6403555520129500c108084420f0b440c1e01000340025441c0c883e07101d00b0318502e100246540300030005001d40301d080d0309241e04000301d0301d8451209400402c000156024054038000c68000e56000c0c0040508003444644030f020498a0b5130780c4c1e40c040241001002c0c400d802200c1c40f2810707007440a218042034200160300680c11186071101500c3d081000540c40400e00c640340052031001c1c091800c108100c03c000e68103100148c10305030002d4455044030280703c5200c1c1d074955445038983c0d0f0303111082003030f1500070141d00e100c00501d4421441d1004040c050b90090090001c10741a2401c0c001c21956004030495030502c0c0d403480c1100100d00c011440c3c1080e05c1c200142110f03c4400a80580402841c403000d5003500c110b05040d001550401104000074544021078402e1640d1200850380380d140e43c00c416910314080c124000d8210504a1980d00e80c1001c04035000800e07032030180c1400a031105036641943d18a894030520 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 786696897 1250 786695647 786695681
    0xe250605030c0d0605040903020c090901060605041e080f060103031701060c0303181209140f090f130c03030c050f010608060a0207030e090907050a09050708011401020a0c030503090a0603 82
    0x181c50010b41200403c40d6001e450760008916440300049412101062070031000341c0d1160240403403d2826200d0b4a1703011290700000d00405080c420028001c0c0903520400e1482c4400f10701c2501c00c4044980c418000c4d0080e0000c40d82002c401c80e0400c1d03980c0c0003e01c0b054011550f1200c04140c0c14803440c940b01d050f2031407078883c90003080482d5411002843c24000c54030302054240f1a103800107110307640c0c0e0350510100740d0700e11145506200402c075502c0314130041148140541206001a80c03200f4006580c4110f060440d00030035903801075202d96419203048011b007003101a0902100701a0030240d4022240c2c0180c084544030300a0803921822100c90740208091030303102c1c5001860b0550740d80c0080950350311078902049862840c501082c40c0d080140e86103095600302e030300e0500050400c03072120300040100040600c158100b105c0c000e020000180a100d49031142210107100c141d00030490000c00545c060b403031304142c07596170410549135084540464071550070480b0008185109004180500f443e41c1c40d4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 786698147 1250 786696897 786696901
    0xc070b1302011b031b03020303010f05040504021003090c090e0a170909040b060105130f0608090d0c0204020703050c1605011b020a1701140108030304030e09150f0609040e25060503 79
    0x40310200034001282008407114094207014240c2111050385c40c80780d00155101d50600000440001c2c1a401490046140004010141c1d071464844c243e1511107041c0024140034508041c0c80b0500990400c504213810b2013a052074110000070144c2c00640600a034900c0d41d00300700400c400703e106117503000d85e1210301440442d020074031030852182c04c1141410a01e20340400494443c0d4060b071a81d004403840b0341046001c021041d0402078850740b201903080500510790f91350101824508c1c4280c4068000c40d80850807004040c0030f10122008a20780350102c031010000d4400e89080d1690600820380090703000b00c942d85070304140d545680ca0255004107100340f15428410f01c104031207800001d1070700564981d0104032014a40080300d0703002e00f00040c00307541d5921301400d02174806151011028000c100510406c00b000702641510704003e0300403250b60356500803130030025400340201c04420b5440740c03420040d00040d100000e0100300c00c1e691010346202d40c0b0140c041c1058a0b200030b100c0d01004c20340c1080 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 786699397 1250 786698147 786698177
    0x1050412230a060e010e07060215072a03030f1107170f0309070f120309050103021305060c2d210c07030b0a050a0e07090f140c070b130201 61
    0x14050311140d181c8010001d601080ca200315141406500741034820540d188198060400d00380142d038540344001c4000c001c0c440c9481002542c502100041c40d021400341c8000c91242d503c107500f07000c2003800c0701244c049688500030755000d0381e045006086012925000c0a20702912140c012114441030350013101c1c0c14a83c094541c68600901c0607201c02c030303440d01080000e61041044019500402d07085000700702050034005400403c001607044500c0c580004544c03000003070780c8803940b1030680c0c000b8030300907880b2828500d102c1603c0b1040c2c0c21096000002140e644840d900c0002e40c40b818419002c00e0200d030090000002c010304404000d404503941000281404413081212401c160400c480011440d0199042d80c0b50305101041e0401c842c2c041c0d4100c180183c1100d980a01500f0000492041021070305981005586891502c1074584035501c88480e036007001c00f01c0c2e018800c1c5091002d11080c42c0d2510200505c4035502882088030110009004180c40300307905040203851640c1a110402d0200c107001c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 786700647 1250 786699397 786699413
    0x70905150f0d140123090a241e06092103091503050601031b0e0913080c070501030c0f050a030203181902010207080c0604260307030203130501050412 66
    0x521070003054801001414030700c100521544042c4803101c2960b00095044c103090042d00c0c00c400a1440240e503003c04c0b050b4440e5500f44406401524100b00000c1c0d06001c89903420621440c500e406c0c21301c074001000003c00940611001040c108146000070886484d00015114004140110161081400d402580014207140701c1d41c3e40710300074180718207415039034400b036a00c1c0c040500c0b0071000203448a05014040d42c140c02002d5200b03d400403049030058800c040180b1550140c0e1260748203e06440c0400c24003101074000010300f03500030320100e80d01d20310301004540d20b199134400c00e8002890918442800da10032082d500401d000c55030744c589400200b5000314080d4101070090202c9104d100403041c00c00b10704010032140402040303c410030182c4240000fa04060700c9512280c240e4201003da4a910754401c0d00b210261b46090340041c0100e5190f0960116840044070540d120303110002d42c110506400202410121001e0003950581f5600c0794011201da0159201e13200055165105641c00070b0094 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 786701897 1250 786700647 786700657
    0x90409140d09050a26030c0d020123060907080a020c0f0a0b060901030b0703111b1b040510030f080405282102120a0b0c07050c040203041a0403090f0f090507090515 72
    0x21086a0500c43c100c43d81c1030520f05864008c4025039510925990b56000394800740856203060000c0040700c1c40c0c0f07100400d80110300281408100b01d1003100090102840b50b064400e84050803040711030604035080f03107543d0f68400f401c09031400d40b00b920001c0d840d03241c00c001181c1a02da010500e0012030710b60050136000b07442020204c10f8021400d125000c40d25946001c0d424074071034080010001d2500600812019441210940c0e015904201c01c0182e50340040384400c04481d80304000700e0240c074607404c0c001d00c280160303007205510104940c000742c040b0074248440b202007e200b0701a80e02980e031351103e84a00c14107a1420302c510ba00410404409890b280c00c1865050380c91009881140b072030717680d42107a5918100e844140c01e9401103444018018104008120410180c904500e10305150321131142d180007204080d6803041c0010005820507125507132300d100802c9803640b00c0100c02e481c0c2d00340c001c00c10b9807400b1785200c00b80780c00006001c9900c42c981c441c1c111003014100c120343c8051080312040c1ca5000c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 786703147 1250 786701897 786701969
    0xa02060703200331080d180f03061b03020702090f070c06110d0f0605060301050405040c0306050c092805040e0102090d080702090c0a080c090409140d09050a 69
    0x1142c6a03081200740010305126455400e0454010b1240140d8400081c4114186100001d45202400b201d02d0010b4030419a00d640c0c1061005841d00320450407c48040e41c1140d030105215810003c20008a6040500240d10045c0841c1c50340e49845800c408a00031031720060750040840c40424012040a410b25800034020b241044110807291038500c280c50307400e03000c4107903400009100c01c1d00c1e6200d03200c1ca5075541c0c41580c040c40583c1c038001c0081c0c442d01040c0a802d10881c2e0b035802160030440c3e503a148500030b503807008050103a4075020225411a81040030380501500c0e0004040740c1c000e46e481102c075421250075040019590402c0d0611000b0882810392880a65007085082d13000e54032031010904d0588514602d650350265071060000c6003101030038118600400744000052283c010000b180c6c041c403007628031030303c800008001a0240010700806400a94510005406028003007400044c600c03031500d440c41c496036240107000da0050a44030b140c48101410310300e5641144800700040089035 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 786704397 1250 786703147 786703187
    0xd03030f090f0308010506180f0102150103030806010e063604090516090509100222060503040501290f0334050307050d110a2607080a02060703 63
    0xa00264020031554a8003065a400d070ba0302a40300c0030581e20440480c00b4240a44e01142004690694800a501c0b050700c3c840c030911900f140c4101c1c3e80d2080211511068045201d407040b540c0d28240601709410070b690460001d1f0b231042d0710003071608184c0d04590341914404030300304480c480c600c0e1925180e07848203a83c0c2c00e829008480d002c469a280e02461018a0246000d420400c0c18401c04da00c1c6a00746a026000c070350300f880b0800c07070819404a00980c1d008400c203809a07a5800080c1d1180d07100450090b82e404c0085420000b180703c5d0340c0000510b104511500081081c15200c001d01c401c85c1e81c0da142c414030540f030244000380c054144941d401508501c0a0115111200c9040824400200e14400f0b11f4a89002074039180e15080a80020402001c0641c05001580d00304408510354207800030020b40314070030071a440702280d100c1c2c2074868000c00c4140d1040c2e0300502c1c644043c82842401c0e4040039103038490002e003c16244c102095942c41e069000380550301d401280e035801e45911800c4081c0344640c42c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 786705647 1250 786704397 786704411
    0x100309060f021206090603070308070303060f0905070201180507090f06090e0309030709090b06010309050309090705192c0a030803040302010b0a060e03070b03090106090906050403021203040507050d0303 89
    0x190060040510140c01c0040150300c0d003120f0800403070710180081034944a2140d0005110f1039803804941d10042c1d80c1c204c580b2584c0c4208906040d0301a2545038004441481141e030001a68005507002a0003850298002c1c44100ca0788207030143c01a101102c09040c41d004001c0c100000132032540310300010290010003140003a520460602142c1c100c00c0d10710025000010703038480c0c624084c080344c4054206002c040110f0f03056070300d0381e16019000a107220305155a445800c41400b000300203a44c00f0300402040001c0503c1d106e44010000e410103641d180e1007903820320b44210310038001c0f1200354034a00c5000f0980b02050640b048040c15034420514290451141e500110101d1041401103200300e0203034002250300c0801c4810b001c8800b03210345c040010031504000c40100303642c3c0440e03170b5402c44503c5c0341c841b5203a80f95003010300e004100960041d1040d070714242e180420417510385c01a52265000e41c00f83c071200110400680c0701d80c4003c1350010f00d190400da10030b024030324040a400740d06a01a00e0009244 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 786706897 1250 786705647 786705653
    0xf12020705060105012304060c11100e040507110c040c0c020d2406030201050a0f210509010c0905010507080307050d0f1505030d200f030310060f020705010806100309 73
    0x99005900a5900d034018000504c4556001103005210007051a00302110700400755200c02c0602460140310108101203845800384000b0340600840c05a00500394081c269540700050501107450281c50b0085007040c001652250056104038034580d40d8a002c3c001600c01d00701000024005e10704d60109010a607401080540c9030912001c5281d031190a034030340d410200d801c1100c1140780c41c00c0302d43c0003141481d8041c40141d03840b405680b862007032070502404861089074159105c0321500c0681d10600415211011400d0b00e581195003c0d4600c034008220003581c402d0104c0f24460140507141c0030810802c01000010154402980e10411514200b420f02041681c00e400303464035000654869030325001910b140706200d0381110700421080300246140811001c02400e8404245280603010943e4486d50141e231609103c0b1001c0d079145c89058a49c2c0f0314100342070b40081e80180c040d4030b0000f41210022012103000007a01015100143c54071017a41da908010000f8040b00403180304101511900e0600c00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 786708147 1250 786706897 786706901
    0xc080c120310080f0115050105030612060c0901090f03030806150c06011205012d0209040216081e0c0a1403070204150602010c05070b010603020708120702011e0e0d0f12 74
    0xc2c0e4002c1c050850840c0340c0740101d80f504070700116654880e4506201161044540300c00a0100ea03c282001503e0b80d50710307800100c100c03050001c2072825000d590100844403a01100400d452802600e4000000f500d07568044c0320140140030090200701c100d07000c0303111480e045100c0312040e84404800c0b072a00382c0c009000c0d4141802a808003c2400712070306503204005081c0248040301403001603941c00c0880e00c100c0080c01d6050442c6060711705038002000101925590100d44a02070b80380002d2141a02e11328210300c46a200c541c5600d50340c2c12030f1107510010f01c4484101c3d0300054448005000700c0700c540c0c560341c094241c00304103d02035100820612005880f98040c0c0c920039110800700d48181351038208040d0948091900203001c10804104000010f00340011841c1950498030380162034a600d07140089030b502c030b400c40e00e01030442c00c0d03010800070544c1504485240040d4031610002da201c08510803040e00e5214180f0029078115039214291140310b5448582d41c4181450420f0341c8080701c03501d240c2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 786709397 1250 786708147 786708151
    0x5011803050a0c0303120b0f060904090c120605011a0a05130e0901060e100f1503021c02031e15100e060a030605090c0408100c05091011010e0d0c080c1203 68
    0x790866a8890410a00da0800030301005000c0001083c010901031400150340700441c48d0045d4440e250106811000da00d89601403c403603680700440000682e210f600003048090303a880e0450701d04c0d05140000c030300c1c0c0225110000c400700042c1115402c1040d0f43e4402c0e0741d10f800185100c0040f88090b2400102500d5150b0214001d2507848000a512401c080320840f4810000342503e1190707205210401c104034024441a04450503101e9404c2c0c80000610120041d10030b048907181000e4041c503d6500c800c0b100e900030350003504080020b6080320020030315620b40302c900300c4001c240f0f601d4071103020345141003005422108000519104403c2000b400004900b60070071781002002903900e000a0106082003a011900414003501342c5d410f05103020b50701f0390b894094040020500341c0303404c074a40c01b45000c0c20070b0310f02c0c001000304010307114611071780000d19001c84d09404640542c00c154262000f2400800c0c400c070f1101071a40c030080c1d45541a00c404015a102d190341e42d05622aa500304047c105114000d14 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 786710647 1250 786709397 786709403
    0x4020f0d03030c030e0f030a030e03040e1f0f0302090a0e010f05090a17090901210c0e07021005040c140d050109030f020f01021216050d0e060612010506060405011803050a 75
    0x160fa1084254024210f82d075022040000d980100f45081040c01c000007503075184201460042244130307007482c110741503029a134040d543e81203e100030703c40803101c035400441404084d40300418649507120407001c40c4a000d4030010350070401500c08500c2504450700b1134905404070000125400c02c00c00a49012102c2c1110720794002c0d00038030201420884c0354088050000f14030b429090501d9590302c00903448090603c03903c01c3d400c60641e4850295036480300708110315030f000083c08c040180d680750700307a0440c04212410780041c01910030084d00b5002d144902d5005640000c1344400e807074207140d04025020b1009030803a501156075046100012003d004100c10740e03100c1d54411342c0c0302805080103445c101c1800800710803a40180115202c0708103201d24036901c00401090b0309003081d0038007010380f09442400035200025052910510200b480002d07894001c0c981510581c2050303913030700125400ca0b00240da4081d445141040308216a62081c0c4c0080c403450451204801c4c03280e80c9985803460035140160031 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 786711897 1250 786710647 786710651
    0x501050a0e220e0c0607050c0910030c0b1306031a060a053013030e100c02030a03080105010e0409031e180905251b263a0504020f0d0303 60
    0x5103c0d03141480283d1400740e090750410304001c0a0303612162103889a00101d80039000c4040007840110340a009103006603003142d411b100454441c48848056484940d0300d00381000756520014a4034441d12071411000208200c102d16014020100802903201c41c40c0002000424401a69002c0c00c1c04100a00d10300885198071604e85c07a410010420180103180001c1d00c1c96003e443c40101e50002030340200e007070044884203c04002c640095031031100390800030303402d885501d8000e410160407040441c10394009032107890400351407004000680f58503a10003000100d0030220320380794007010809550300d12014104800d000300111030a07205a9490b602c207589440c0c80c0d106020100f1802c40d071a024200c403c04888400b0b1216181c080d240700300a501d00c1d10b003c4540803444003402904e041c90308150446a00c440040400146083c0039604890501c81000c0d6060b21941c445445040112000e034040c10010700244101d644020000d0000920681c0c0240e12003210603441e5556603c002040e510903200 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 786713147 1250 786711897 786711911
    0x8031b0c032203080702130209040c0e13050601051225110c09071d04060302150d060b04030809060c10050a0921090e07020703050a0b0708060a031e0203031324090501050a0e22 77
    0xc00c00480e109378200c0c4841840c040a00204da644101103842081081c065201c41ea00c0f55011043c1000d020702002030844444d58103201940c1e4041c06811107500200200c1343d0740000d05c410000348250a03500c49004c11510044050301340c0710002c20986080c0001d0001031210b5980d0085800c1d0101080841c1c003a80d80003600001d007044511a110203050712403c6241040d04556440c14203109010703400340f00c0d900102e445102039000300300c19203203820140c1c001c3c012404c06040c0031014050300c00048a50210328461032000c41e40060458401a032160b80c1c4000c0c0341d02d4124030b5001d44201400f01011800f505102001056040200c0d9050301c2c8504800c80c01c0b8540201c0c000d02114015103c04e1043e407440504001007043d0f035050b40800e900c0f0a00c41c0380788a12610001c2c1c074511032a0742e08940b81049240c00a102240300644400080c40001c148904000a94040f91429114007a45011420900501c41c005114020b640e00c00f01d4040d1049441d40202d00d010842000c8580c1400d1b01151580a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 786714397 1250 786713147 786713149
    0xa0b01030804210305120c0702131b03180323040f1716051309020301180b060603040b041101030e150109150e010308031b0c032203080702130209040c0e 67
    0x801c0307110030a00900d900f402c903581503034020418441c020207003200c844c030400402c5003032090104072a5503a60040050b043c02e03402c64282c20242810071591408124050101b1185601174011114840090900c11003103081e10f0740d05980d1700c071101201000c0c40e154440d41a0340c070605040240003400500c60700d0303400316283c0b041420602c003242c00b4100d40e582200c000d0004100030398100d03109a480032980c1030003000550362440001c0040c0f200c00f81d0b040d0b081c5107002c041525060200a002d03400345000500c6070707035018144045480b06480007090040000e0004011030100c0407450900c0505243c04500c002002074251f250130301010944103480702c22001048900204c0c4642d100704043c4c018a41c00d1a46000740c0b00182e407070148405001e041d00000001d8080d8140c0501d40020b2450040c11600c1d101491800ea6580d08400e850103c140440e41c5502d10321030f0006c000104882c0d02c01191407500315958203104400c9079145240400d10340a000407666580ca1740240d80040d03103141e46140d204400340d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 786715647 1250 786714397 786714419
    0x40e041103070b0a0206150621061c0f0308090102070b0a05090f010e030406081e01080604030e06031003020d051e0c04060e0609160e04020409020c1c051b0a0b01030804 74
    0x58054212a007040000c1480e890700486c0f203071392000c3d285041340754100001313010400a01c11100c0101040112140302e040c42710744003a10601500d403c2c0c980500110040e8107204249c0c000324800360060704000303121030009120b000c580c0d60090a550000d4100502c699807404c429409488400c6116185c0003041040c0408000c5800c00928200091180c003210000c09501e0348038074081d19082119a4000420ba8900000210f031b05148440d00194150394401050f51584000c0d00d084000540c220360204162030940c1c1601d0082000315030400d4514a9982040795403440c3c844102d17510b0141c4130030b4594124003080c10700600304a1001a104095105e0700f088210350064200c500d40159200910009449049040750b00485100c40c1250f06188900b003950035482650b0380c0b69000307000280c08541016690098001243c080701214140e04e0035480944403a00503000b00c10000d481848a49007014804e0104000c1035443c00658407005140e44a01c0000c80d000d07002aa40d40000040400500c0150 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 786716897 1250 786715647 786715649
    0x702030c042a0c0b0103050c0a1e09021b150a0c0c0b160c171306051c1d06010e040c050901060203030a0f060b160302070605120c030903040e04110307 66
    0x100e908120400c80b00200e0000008403455800c01c0b4851410090850b42c003a0103240c1c29240c001003280455a03407460301540d03840c1200d541900404041100040442d550032685110b07009007003e411034a410207090200079044030110b5000400000340720190700030300380449080460040c1c0300e00c0f010725219003240242d801c01300e0a00e0800015140c00c4004c03800310551b10360407246070300520240c40181602152040e00040d0040d10303041e2003140c650b52203101d00005280390a007100b65006100c1ea202c6069030305008404a0b00840c80c4c6206109081c0b06066104c5641c98030710510400740003104c008050b1911030242c010154034040d030f50520003030021444807840105002c98580f12151b061440007502c0b800b0180c480104252511301403008100c2c2904044050300301d504600c2c1e140c41080c000e0006828002c80d013074025004408022a00500c5801181d20300f2a0802454400352240340c01450305610003040300045000502011902600d42510540500d02070309401000c25900c004141c146140c0f = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 786718147 1250 786716897 786716899
    0x20d0f05040512040e013605011a0703080f090304150903061508030a0f03180b04030807020105060a2603030c0304060f05010e04020405040614310215030406060513020702030c 77
    0x105000401020145d000041d040d202500200c2c07104180d07003030598280c0c0090303204440903049030f19800802d0b2041a0300030781c1241e0720f55206c1c11500716940303a2440540700701640900040c4600002070590032800701c80342c0d0006000c00c126490300740d507443c034a41c100c100000780c4800075407211810401c0c003009004092514502c2002401030603d0b0000c84c036030f03a109a800c0801800f10405a1480302030182d0f2040c5809410184005040c070f0f9149011201c1c40800c0758100c021034200c001003045140b05100b014810800640b6004070036090002c5407901e15804410624002400e0030407c410314014000380d03001d61a1101d43c0e0352281024030b802e030140c078041002e2040c030514100040040004580c0044c1c1c020340c0607180042d2a4846080202c0640404440a4198010042440762034050411411000004001822419410710305041000024200c010b03501c1511828407000682da000d0041d81c1003803003a0700c00902569640082598811910b10700c02c2c0c010341c0810030340c0039401c09202d12034940700 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 786719397 1250 786718147 786718183
    0xc0a090608070317040e0a0605040c02060702060c0c030f16031202090109050d08091008160c11061b07030302010207060e06071205070e1201020901110706090b0d020d0f050405 77
    0x10804611a9889019200c00fa04e802c400001e04d8400380107940446001d4422422504898600070052070013410300c40c880c0354000ca00e003a000c0302078a8804106c10340075140a901915007a225500c14100c5a0085c2d41c81814030300080000c6080110540b008100cbc00081c0301801f038040600381006414001440d641001c802e0040002201c0e6aa01001040a1340c604880c1e00c0c1d01200319040654550150110060300503104480014666030002441c80c403d845a54071003414100b9264100c0d030b1045000c038001c02c84c04001e0007001a601d4580050318040d00c0044984d00004010400c262034200c2c20344c000d03005030b507001a07050240a01c0380940307014501018010041e60800d101c0042a004e946441c141440b0383d42d8010609041c460110070081000c0202a44403e54900020b00c0c001c1d0300506409011540003000103120800108946040b10302c944c540341003691a050841c00c0310b6000e50240f000855003009000c90244061103030f40e44000000b03030001014546460b1180c41c101c01d4503070241c4ca8aca = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 786720647 1250 786719397 786719399
    0xb03010218031e03092101090510050a0c0804020f06070b100f0f14040903031104140f032b0c020d0b1605040506070201030f020706022d16120e030d020c0a0906 70
    0x2140002243e00314602512240300114460a409a01b51070404024207503500b0001c1c1030042c090005584190079119400400c4140c940226540494048100120110310341c200018050300d4143c0c00d0311601640a8601c03440d090302e41d5540c0c80b06080c110385003001a0200c0c401400315900210420b400b40ca00c1d00c002900050504000b00100d000c1300101c5481292103200000c00c1500ca42c1100e10600b1a03026860380b16a1984a80d01c9100c0140618902031120005800614030b80003071850490082d00c141101590355121001c114003410312940f10500c01c0300c216100042c3c681855000d54280134a80d0710080f403d000f40940021601c6000040401034148000d202da81e6803081100c1d0700d298242400251440c61110300c0c2d000c1e006112029065030710208410f600c00c404000242d9406014a410b2072801c1d40c0c007112221540900c02c0c0c010105006107009a00044030406141c030000c00900b01001103a40004c0000d1910350120b0150006030410302d410031352401d105580402401d05804140310721 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 786721897 1250 786720647 786720703
    0xc080c0604060c020f13020f091201050c03240a030f02090f04120c05070e0a02040806130b0412110d031a090c2506290108091e010b0301021803 63
    0x3d4244040d11a55007695a00c44a0340c80d10203560350031040301419134440c001d0000c0044645c020a007094000d15040403070240e605410b100d194071460f241c84085041d612a408074860b2051410721451800309400789a0616640e44001800110b22604072042044200e105204100e0700180c84610503815103818040020505e1104030b0840205240c03a12043c035032420140d20b001015030020340080c0804091000f20b2001d50020010703544003208a903001d0b01e8480c8454400000c2180140c90510010701040c0011006070665000341103914000c4520003184014608080e40b0301054004a84e40d190803026004c10b030081f600c258075084803c0c03d014600241c1441051044030200e0388024040c04011000b6000c1c80000d0007000d8000c481000051204e440d01003c84c02c071b01521000420000880b007100d9031180380028410314070400901001e082944407800f25110382140d850a654031507207140603d0700c0920161411110000e0300402c014216414507090080c4860624090b900500300d00e182 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 786723147 1250 786721897 786721907
    0x8210a18150b18101a0f0a030b041103150306090d0804120c080406030f05160f0309020a05190315090305160201020309101e0f090306050a02070206070c080c060406 72
    0x141802a01040000ba040000340c14401151450f00181034524180b04101554810300002d0710300301c911290303c1085440c070201d014000c4190950441038100240400c0c103110b034200441310107000d0008100c111840450100c550400c445283e034640f02820a10030501d0200026500560b444c0b001c0c12824003141001444400f000300702625840600c80f0204010344212544204150002540340d240c0b1784400008000e0040d4009400c0510704002c0801c101060704444001180d1184e00c50491300c2c5c0140100390040d288440b41603a000800700300000d06600e130b4175069a02041c841300d07152241401e62a045440c5948a09448180c610381800d01d40040c1d008000c641010140102080441501e403004034994410000c04640182c940308507014040d400075031803a603c00c81011280312107844020102d450409084403400020340410080011511960051f50001e0305030170003500c5d010803600400d07410f500000c003c59510448501c104030840e030a118880b514442114103a01c0d0a1806030000d207 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 786724397 1250 786723147 786723173
    0x901150f0b070206070203030708030a1a06030105090711011a1801050a0e18010c080405011a03030f0d060b07030921020303120a0e070f1701090c060c08210a18 70
    0x8000c8030000b812000395640c40058038143ca90003400c0342d5a455043c80e040b14241c009456040d140c600f400d050052104005d00b4114624030003501c240d045030b18000c02c01602d210b0140c404010712511011038030100b402802001c10f03625000c000100029603490030311140720b00301c0804c1250f1500c21001413043e551030350707401c07400c440382034020314150f88075418000c494044814140f8510341ca400606580c60347c1042045210f04c0c004c2c0001c00148842c0551002c0003070510220343c0e490340040009c10b5038020b2000c0502142c0540d03200006e45075484403190400b680c446c12055010031103820f01046824800007006000707221b00d948408900364a90b01103079407801002900d06030844000001040c0080755440012501c10b070a0071030ba203407036031171500044182ea2400b80c0b441080c21030f002d664101005016500c0d03410303803002c40301c4015071410804641000300c3d00c5081701c22110070801105003d174440c03550824600b59540c900b840e070a14500320011150310b28080d04418a00840d000c01242002da0300103 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 786725647 1250 786724397 786724409
    0x9010216050a14030f070e060a091e0c09031a040c05060c030702150d0f060905060411030f04080f0a03020405030105011205030a2001150810090221070b03010e0901150f 74
    0x190315030300f02c100002c0c1810705071003a404040c41012000119001c1881da0b550017402c0907513103d0720898a4522050645d05010600c035020040300c1e00b0309166100540c000382c4464a6881c00c00107040d1640e0b5281207800c8580d0390000041600d500340800d0082c00b580f20b000402c2e04980c110300e410b441404054a07030086810191050401d4104281031458075801c541e41c040040801304410908440048014074aea40034014a15141c580054024209131080c001c0b101134041c0014155540d48446c40c038082801041240c09c2c8005000041b100075080c406880c09030b880781c6026880e06c1c02d1202341800c46005901c0b00b424142100c04036000b240d008012107440410034030f0040d2240035840340c0d42c9240c00b104034122507290301e441b4030707201135009103204134054400990a913442200c00700c003031809035070007248041d6120010001e1145145060b904c0b031020341c512841514070041d43e408105103e40c00980c8401910340348242044a814428807643c0d40c114061004814110b003024280d01301051203010310 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 786726897 1250 786725647 786725669
    0x1211030a031e0306090e10050108030f04030f170703020304030506220308131403090f040213060c051606030902100c031b0321090b01080d0509090a020d05090309010216050a 76
    0x2c981003601c207400c03150160507180401e000c214a001d464a03680c0740511035020340c0c14a007000215aa1002208952065000c0c541c00760030b081c21138a80c00840d920703075402110206001400551103490810281004a001c1e03006903031200c0c40e5042c414249880101800380c8070b000c004520300c07066084044c1501c0d040e0075180c801d8481d918540c0e9131425260700762001e06408190b0301100c05000000008020340c01c1c0c01e440000c101400c080510060340501040d00c8090240c07650244506481000d541c12403d0140c0e0440305041018a00c03080050181c2c0c200c2170000c1c1d2908a03c0081d81010000c1451081c0b4514000d101004145c40040000c894510100c810000c24a8046e00f414452a040962418074000c10104588a4040107008050143c0100c80000041000040c0c0100103d05103a060b0b5046d101c0515000d004002c008100c00d0050001c5022a400c0c0440241801a44a030900c1031050030000e5503030b0501d030000a0300c0d02104594084102d181c42d50213101585500d90081d046458101103 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 786728147 1250 786726897 786726947
    0x10803030403080a0e0f07140109050d060b031e07050a0608042102160e150114090f150c0f10091a09420108060f0606040f1211030a03 59
    0x201e04064800d820701080141b1999013400c0c65070310003040b00c0c4d088440d4000c42070a9009a003005540b2900a4842d180e0311186c0d4403485804900260015608487d000701510b41e5480302c02403004030686030121380b0b00d01c0e034440403044c05a82441010400540001e042005c4a490241c1e100c44050000350318112100603002c0180886034000c10803404a60030200e40251001c0c0c0b10b01e481183c40138106c80f41500c00e4001d00703a40c445540242c6a0412040d500d0170746d80e203031075003150134401040404545c003504502007035191040c0070098400341c40344851140142070038105541d5400d140c0740200c500d00c807015250201c4040098030102e00001d03101940b4800d000d90f07039070b03203a911824900b9200490b000c002800c00107903620742810307900240ca480541d0203201000003243c00a029100d00b400f40700441d61054001c94011041005000d50145d001008546400e0b100c480300d240c2c012095100e0000200d001503281d00704610344c0d100e880e18245c298001c1140ba104c2d920000c04040c81102c0c0d000e40030350350550f = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 786729397 1250 786728147 786728161
    0x1140d0908040b070b04060b180a0203060d020a08010c03360512070c0626131115120603031303080f0403120f03290f010c06050c040f0e01080303040308 67
    0x9a4008005541c4065212996828000c2c178949044a00700c2c1e00340d00d0b04002070303480e01d803904450100c01e00c00481011103543d081c108200a40c409000c0541c008034030321100c001a0340399210f010140001000100b518210480040d05540c039400d02000078a18010780d015641905101d0321010590790440d4607800701c40e504001d4204a1000c001440c8071000103008018402c6041c0144c045400c25038860303215418007010401101105a807180301e05c3d0b40900070a0564100f100c09060a41c010100071880d0754030704000800b000c405903046600140d010504c525203042c41c01c0803540c04071095020394a000040c610501d004200360000500b00b030300119070000d510307007a2000d84010390303480000d103e60340c504404013504164800358481d0029060000c00c0e898000e201080500449a030b2407407011012502041200005e04a0009410030400170300e100c007c9119806840c0c005e185040310780c0d42d200d05005410490300300c83d401901c22817551b0001004081d40001c1101c3e40542c15284c00d070401c3d01c0d050 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 786730647 1250 786729397 786729413
    0x30a032a0c03060c2606100e0909070906080a0506070f12050c0d050702031e0c0312010902040602070608010b040308030c070f031e0c02030a060911090a140601140d09 73
    0x380c4003520041c40c1d0702010041180740e0340521081c130026101c0383d424150212600b071001810843c0c101c4421243c1c0041821070801884070680716100742070542071801e1040200714030120844d42e0007500e40c42010200b10b614403621a81c00a40b41441c0a85a0800c460300d5440d9148030281541082040c0d82d40130a021621601c90f200354000c0d661030a0045061042c3e410f50250019016003841d5407030500070400b0580008200c82c01841400c40f0003015640c4e508008500b5002074510440c2400304100800389010240034a5010384070f00040181c9075400d22000030301d015555000b42042c009200e00511124089405a0f401c490780303d4403059403030b030711015000114041c052005043c002458910b004254202c01103003c060521001440c3c1e00001d039a0807184007000b44806505030300852007680100d00141c20002c8480e0042c802c548820720050701017a0f54040071200408006e44d5025040d030300e000f80603020b941110003460440c400b16040100360744a0b2291080381074600e070351030f00c41ca4100440e0b2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 786731897 1250 786730647 786730727
    0x3011806080307050a030e040509060403110f010204080f0d080c04090c02010b060f1b03040f0b13030b01171006051c0c030c0605040315060e13050138030a03 69
    0x1440030b0b80e0300c880c09450310340ea5800c64900101e0101c0c02c4c100c8500f241e400c040c810f061181031084010041511603480588000d1844503200d010b601513091241c1008200740000d000811859004001d11010b05456508142920b0b081034104041d400a21440704a90020350341035425162000500d1441590140d0050207100c407490740011020844440c00c526607005880e01c00070010340d143d800040e9113505500e922450081e1030700e5a00d40f48080c400c00349580c1c041d10902803000d441c44085920303501c03102c100304001d034010108080d21000251070404280001d01c4072000c044804d00500e0f0170100007a044400400704c1031031000003e02890203100a8000b5003004640007940d5181c05900c0350303c000c00c250f0190101381c0d01c6c07100b090300c403092000c49807041344100c44030f600f445c4083d034448016040c1c859403045c1082e9400d6403640c2080c101100e03a1a2115481c0c20b0300d80411000c102c1c1079010140028858030403e03c244c000c10b0013a03000c20f410213682030541015008100e045809601544660076107 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 786733147 1250 786731897 786731909
    0x7090306060e06040c230a120501030f021207030b19020d11130b0711040e03070606080d081303080610051605030717030c04140f0904060507032003011806 68
    0x5050300040e081502d401114010441558180012288034109540b01d5080e08030030680c034021041d245211024000141286c581c2c240b074403040c1c01440945c03001c01d488080e042600c113041c0d00004081146010100010030341140720180890341e10b1510780e541c0347c010003061440803528403000c03014200c0403681100e0a04002d12000c20120030f500701c400e42150084011290311440700003020444500c003d0640d52440d512000e01007104080e04240000350a01c0d1881d90054070040c407040340002c00500482000e00400c90080c088892441d1008101000207840c211998495158120101e80d01c230b0000780d40141c0984040000c080010300c12a00c5200d0244180e1800c42240001e10800501200422440c2d0003a000113103404200c0d01102c1c26440240e039140b21200c0300300410004d81c00101c81d1052082c10003041303540003914074004128090750454041760f0050b5900104031403590944a1000c1c0001882402ca604440c1d6042030704c0702d0710040c0500c0745804a4082000d0541d0310a0700418080c05c9 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 786734397 1250 786733147 786733151
    0x7061805060a0512090d0e012309030114131104020429090a0f03052b1202070b041a0a060510080402030a021c0c090507141809100302090c07021807090306 68
    0x2404403501900c8801c2c80346168002030300c0e047c001ca2203610a528134201341d4140c000707547e10712860544100550b44110205070301035484901c00070074028043c42d6680700c5e820641e40000102c05600d05000d00c1400c40a400b8400d500c1404140312022405468028078000016030300075000500c80042d84500038058a2980521501d40203ea24080840040c0c101c0c0d00c51400c03030300d0710301d401007881e07040394140528400301a01200250000c81c0c856410100c003900e510f000145440c841d500d45540c0704408a905460921743c0d02540b0321403201920700b043d80315242207010007039281448009140d081100c480300d82000105030100e025964141f0041c440f00c0e0340280140d05200c0480e07203a208040412900355400c2b0003000c0c000820082c2da0051030322540741c55882d00c140721850101c0110542001c070b40b906103140c0500f2880516216642c00d10300448820300199521803840c0304101441000070b12088507458180480310058035070100b9117289a6103142159142d0b0b43c2c1c0413007118840700390ba0011b0280c0c1c3c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 786735647 1250 786734397 786734401
    0x83309190c1106180604080f070c091b0e100c0c05030d08060310050105090f04051606020705120a02150901021005070309030f0e031002130308190207061805060a0512 73
    0x141c00100150400032042c058440c0344c0d60b08460541000001410380c403c0ea000030002074001005d010040c10b850241c039004500b00a4903444255000016401000a60f41da83c0070499120002032030084500740d50740342c115015102d040208003074401ca450550309002d6402992400c1101000c8176001400f40a0b044074044191000700410310641902c40e6802401808001c2e004548140101410789102030b000340c0381e98940c3c80d0b03000c5000c1e0300103006aa0500529008606c030b006140c003010002c2c09030b40d0040110300d0070141040300c07003060102040d50f154020050240140c41d10351200004a409000135030701c5d015500b0040c4d0501c44144c40420307410b0b15100401030407070b40550080c420301780241d80d2001001100c810981d6802050b100b0160b040d0f104a500d0103156003070303800921101034098052500f082d0340340d59284c8680c1103600c0390614181c01941e10428607504001031402401c03140380c0b003003400f101c041c40d403181405280a11805204d00040c10581305014400303c64002c280407005a0441c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 786736897 1250 786735647 786735671
    0x3010e1c1b0c06092301050a0c050118120203090d080c031606061401050309060a09020f06070b1b07021c08070c090b0f0909100504140d08330919 64
    0x842e03540a0b00000c5605250003080764645000c0050a0030142c280f400804400d1000645a580003106158100102c6d4030344140055001e02a0043c0c01d0f103d4640081d90103200e162403182c01c1e42c039800741411540180000c1c485507940c50226060560030400080e80e40c404c0c3c00405045201c0e8408610f000b208040e0700300200501035104d4411103041864180605c25004011542032105482504256014002050050f086584041c0c42a4802400c2d40b00f404080720104605400021065034400e080004000b941110425034504a201014103140340295a078000b640300008600c1456040b00d00400000c10040c2400480b542c00d90010403400b081c56a4406401c081c240d03401409002e0040d0100652543c140004401e015004007000b03400b201880090031b00080c4002001520366510446200501d40428446034440280542c0c450307415140c020010f2116003501c2c03005007036040304009000c850300c2641c8501c448100044490702c1c0a9103411100015911040000301d1103185400c90341942 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 786738147 1250 786736897 786736913
    0x204062103020f0a0308072706020321040305221a04090b010905010e0d02041e090c08060609043305090c0d0804170a0b0702150603010e1c1b 62
    0x30141c03190b421501201e002000d4240c4402d071880c0000e021035030702c60105206074040c002400d488081c04100007000340056105080802c0380c1e500c09005600001101030440341c10340c5442031f81350380492100030a03081595004105d03204039002d2104040c07080c0c01510100c1254600d040c014800c030541c2d0300940507051045d21f205d60061180764030092400400c40d406502510141c0300311507050315980d148510060600024020342c071030881c0d02641d9070515440d0f07030641096503004072701056400268008903140c0382403401207a410612050307104601b000b0441e40c030402c04560103584000352282e03a980d00585800180c4c1b1201500c00034000080c0d5406060701183e1009108009020842c2c140000d04820b2000390703901c1c1c80000d070641ca010002449500c000c082000540342d030390012140c5503180c2e07171100c80000c0001d81d40c62006800c0303074090802c2001c1081c003094001408600801034054452038080d500c160242d600080040701500707200c2040d000d40726826603441c03084854004d80b0001c0c60a400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 786739397 1250 786738147 786738209
    0x70e040f08210a050a0e0d03180206040b04031407180b0d051c08061c1403040509010b19050c0606041a0a0902040e0a1103131e06090b1f050d020406 65
    0x2282d04e10b01000650b04804a0150002da0010640505180b90351036001301c0c01f420b032140602d032507041d184004a0041c1c46640080004014040c1039541341c03421403a15840d5103011007110441940461024400075840d98440140c890b1128800074911100902080c00c007907604001030118000c0d00e4488060100b001100c1c12410f6090303403002120b03521007042194031aa072088080425a0301c03005400000ca1004603c4c0c45034214100700d07800c06646000103200102d00341c008101624010803a03e220400079920407020b507110742001030401209000fa01c0d070314a03008003050f1180b91202c03210071440c184000031810f000005044420b0180d01c0e8140600654050f10401c08428220400945844800d06c17485c024100030304070492640c0c44402407400c008043c3c00040d1361584059945900ca035000c4221760302d281d84186004200c0b0300b0301e42801e0405050040a2a110211a0070a55490b1414910100c01d0351411074071111003407400d001240c010320f201e800c5041400b403803000400d210f40d0924007101c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 786740647 1250 786739397 786739411
    0x415081b01091805182a0402030601140a0e031e0f070303230d061202031b0913050a02040c08040b0a1415040239070e040f0821 56
    0xa08000352540045440302c046120303034203039014040e0003c0903800141e0060341e00241480703003a040001d41c1030841420f00849601200c18500c124211001500305500302040d4040300310750440c00e6160001c0040e00c2c18070850000078412a0001c0c40f240d900d4058801105180005012200201d404810384100f0f00c4510803110401c2c800c03450614811440024401e0a030303949991510f03c80c40480e0f41d0034400a15000350025119030503c94905030800d40d00c1a44020b14483c5041c604084980c0140347c101200108081c10b0300103480d0f4030501c503403a507040c181e030400907210805503415100d0a207203041c4113032080000d5000e8100b5030304001d00c3e58420079071030180e4050740c1c2c500d5080e200c07100002d045031648000401c3c0b840240300026201440e000d240a100c42c800f0f8000b6252034001c41d43c5a812141c0c110002e00f0342c0c1e01510000790701500c990009600b08000300000c1c8011800c02c80c03050f40c1510000c10040401c1c0c14224200204000320095440c00c1070f90000484c40156900c110224050040340c000d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 786741897 1250 786740647 786740683
    0x7120e1023010b090f1807050403060c0f02071503140903030609060d030206070305041a1017030909060409030306080609060405010f2d0615020102180303040f0b09041508 75
    0x900724080720780c0e114504940c2c0c40e070710144c580402d02003448000480c500710254800c200c1503c1c0007070355003007120039442981243d44980c2c0c0c550440c5414000c5070320101407602004020308400800c1900051120240c0c0c00c0c840881c00c800c4058502203003d404c059103e0031000140c0d00c2030000d080c60000203540a071104407410709542e9a102d05004224008000c040c0041c1d2001011510107800781d8041034000c4d000b1a00034180122076030042c0d10340e84040d107409039510501d800402c0500c118440340c45803240011301441c545222000000c2003074a001c1d2440384501d940d4840c5404050027036108000030028001502c0c51131411000564990408850950385542080401d0019508070b01c00c801d15100d030075103030321000920a0000030060709171020b10102076648043c00b0a540140d4400f9202010140e800036955042c03031407001080505402d8880d0203507006100034008a80c00e8800c80d0280c401c11541540c698000c0000100580300802c82000f80141586021411960101e45002151038492130 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 786743147 1250 786741897 786741941
    0x70510090e0f040b0f0405100908090f03030c0a06020d0b0a03030203070506341101020301080115080610060f1803063c0b030f06150a0806070807120e10 67
    0xe20003102c01e003110004c080b82c4114000070780790f1010304215908035018800f01c4080c0040740710004100d4001d5481954041e0003ca80f4109600e17020b284804800c500307a020710700380107904400c56901c0401c214000c183d65000301d00d1200d1211181e0209500310801400d00804980da4240070303440760301020060707400b4091800012081c5030504421800b280346800100e01c0c0d00503002c00b0544d040103540da0340007003050315440416024801d00165000c0c2c04241d0000032062041c114504040242e54030100e110740010040000c0c8100c03503402041100c0c1142041001070b6401101100c241480c0b01c401d03410030110040203c14008a0340c030203003424208201c024420752010526030b0740202516500c40d5001c0c40300310320702c00a01c032039000201d240b80e0240032560062070b002451800e1803011100b603e20220650200c486501d00b03201c4040c000c00804c0090880c0e4282110300402c1410f00421003004e000321308400780c1c1242c46952105158107500d406982006500d01b4254025252070000c2d000c24020b4122 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 786744397 1250 786743147 786743161
    0x3030a1b030b030a030c11040e0106091a060316110319120b090103060b0a03050111030718060e010e060c01020a110d260405030c0a0312270f05070510090e 68
    0x2c00c11442c618000d00a00c00030000340d070304940f040300f21941210014100d01c0000f680d03131100c0c020314007c000010000301d440c0d030820203840211401c1c03c00c1070194400c6005c595005442d00b5007120b0300f01c9880c1c01400140522800159044100400c1c0003d076440b000030990b02d4010743c0c02d0958480071507030b80c4c1c12030321800b0703605814150740c869540254000d00040c010400114180d0140c12200405840440c0d03803076403a00c0300c81c00c50b281d0901040100100108105c82d050307004241000c1c006000e0380c401241410240000c00d01011000600c4c10b010741140342d03152681e00c84040d10742c2041c8482c000d40d42e504d40c4060007400c415007080d02c48418481c02e12451019070090074441200c00300c3c0080050060b600b40d0000c4e9800038050425106800104040e040307110040c0030f80e01c0440c1c00703621100c0740c0c01a81c0a80208842d9440480c1074800407201020f0482c20100c0c040c1c1481c60341044001901028508243d428000c043d880a5031155448405621042c0c1000090003103614054140368103a803040c1c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 786745647 1250 786744397 786744401
    0x41a07050f19030e03041e060305011d070509062803050114190503060c070c050f09070302030405250e0a27031202040f150306230f0303030a1b03 64
    0x18001c2180e40c009105941c1c10305100014070101020360f00d000304021481907042c4d400c40d403007030304103030b4425140e02804c2e03100c115544441d1000700403524041009614000030f5180c01560308480d40400c414801c00324001c0b9100d0002d584030710138014051907590701d0040d8441416200e242c00c1e1004a4108200350703041502910885048440c60000f15002c6c2e401501080084244076044150314049148081901e03202046500e00c80c103c3c0e103080c255103a28500b000e03030030390303241d5440144220441d1180390255111341d15565085606800c01584945551403c00c2c10030420302e1700740754100902000524003500041d5540c0c111210782d000c022603900c50102000680b203400103150906615481c5803200700290901d11600940241344c202046451454184260303401030b400020303200c2e808481032003401c80d2140c6003181400e43d800c0800c0b40910340841c200441c800d142007501181883c003010070a0342c4901d085140000f000905690fa28030b001820800244484191001025400356504403068003138 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 786746897 1250 786745647 786745657
    0x1011030f06090411010c050f070e070207170c1e030a050304180e060606130b030a0c030b0f030d0e1206090105100602060403080609100803130312031509090204060e041a0705 76
    0x120400c4a04c1840c1d400c0151895a90400b04a0700c0340704401c107007060b070f08003800707400080d04030035075a200d00b4104844000d150440e1034104c1d00801e021890f61426000000400788440c490594603480f051582d5860441d00c400f042149513054010030040b00c0800101100900944000c070000d20003103e210b5404008407480c04905080c03907880400031900038030f130441c05003404009100d83c911550307448105120581d001551407070140f584483c412a84d094042c0114201c1900603214608003d42d00400a95103e2042c1003400c2403003100100c40001d81c40b00340c160303144e408690048031b4441c1448a455402020b007280c58400e164146a00428018804624180116015a9a41d80350384402c0c041042110001d802c01d01140100d46000a030b403c01030014044242e4140044c1d20b03120325508080c0b005450f452001420185004e1000300c2180d11030160a007540c0d4100c0c40056805030701c0c40810000e00e055040194540080010001003107110584040004028944426a034a400509a8480c018 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 786748147 1250 786746897 786746903
    0x3080c0a03020d14070b060409051b01021203191a101d0a0b040618030f0f0311010203220206040b070c090b0a15080403031b030903090b07051e1011030f060904 70
    0x803c104403400315401b44401d036000340c0010000035000d500d40e61030381d25019001080481c0303444220015074166806000c00a060141900e0241c0b6525011007040552003c10301d5080410b596031003841040c06410b0601c0d10b0010028283c00c40b00885c0f1180a88560b50390203201081c2001005e68101c182040811102101d680c81c1040381024148042990480385514040540c01c070020780000c00301d40d5010f014000c080c09803c1c0c034100707128103090040c0848501d44000f50ba0342c2c0104140140700d01d01607184094220501d608070000c0c1c00d640b001401c184180d902480704408041158424884610300c000d00700c1c0e47e410303c10025840103a0512070403240504c034411a00b066103000341c40c018004e40d5040c2d481f030b00c01c0ca4002000c2c0c0a0405940814400c60510800a030762880201c04041d00301d03001c40003600320040242e00300012695256614a1292400900300648111030f4010410400110b00c1c034040701d0708203110190168240c00c0d001e40003111003203405030898021625a040c89001ca03409150 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 786749397 1250 786748147 786748187
    0x5040e03030103170f1b0d0207081e0111030c0901090f08100b0f0901180c170610050f031e01050925021216170a120b04020403080c0a03020d 62
    0x21071504c60080500386400e56040155040020194942e5002c008024a1000800d242078408a01c0040d80c0392944905410080d54007609040c04280381c00201d094100050601c80140c11640303c0c042c5014001c95141e500c0c50000c00320502042406183c090501e0403002e9a5907034405540e844120244d10151280480e1038020004502c003403841c9400501255501500017201800c421000c62003040c0264005100481465100d8404c01914005c0006000c0303649045403503240419280c64081002800c81885010041107910300e0600510680e9008038009181039124030b4107820200c175200d400c03a80d00f51100002400401c00b4034004587c02c0c0660300b401d1072003009400040e180d4040c0c02d901c039072500941c803440e0010461030040700010480b4136001c40e1450320040c010703d413400f0302c1c0c9041746c0c031642ca502c020300184040e968420300500220b80203420114000b450031b00400c0082c030136504013400a50300010301e89045080007800c401c401c0d11a900b281d82e10914900d0031904001d000c9071451600c1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 786750647 1250 786749397 786749399
    0xa2315041a1e070c02060c0c13060e010504050a06051801030b16080a0b120a03030b1302070308070e0d0b04030816020304050d1511131410050702100210060602010b090105040e030301 80
    0xa49111202c0da12a031141003840003005190001031546d0440031038880180d1019004290900b044040400c041084503401e100190403e5151034403410140a024003c036070b2140090b140e800182c01800050402070214410300b902458100c034018030902082d03810580050209240184c042841003884c2e40350358504005850301c0c0000c00140c841806c0c0a9440150306845202e103131402d01135940a03a100e600d0000c3c5121204042c03101c41095200c107080340c10706c1840310102090700070080c0383c0d205200340350036003100344140300081140c0c1d070030000942800e286000308810150006050750140125000c09020600c200000726035030711590040e02d4100c0800503005000404806108500900903000410245503c8900850b40e422288002c1607521319148100000d140400102aa001d0296600381808000101c0a0924403078204d0080c042c21015680002d168424405000e075480340c2c0e4003d121130342c0c2c1e441000f07001e401c00e20001446134040728000074041c0382c144116800c28030040061400c513 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 786751897 1250 786750647 786750691
    0x503191b080a090306020c030705100c0509150f030f0a0e010509120f0904020c01060e0a050601140a0201180b01090c020a05060406020903070f032409050a2315041a 72
    0xd50400025002404800c0340040006045c0b4009031440981d0781c1c004503250581402d216140c0071860241c44105403505c2c1101108550001c00ca4107404002c1e9545040024524140038080c46a010003000300f80000c42400685103040388818041d41800c0028800c0405001c043d42c01c0301c005940080e400d61060b980c2c44824400c54001d0105400e440031502c1c1000489000300c2d040e42c0c8007207082d886696440905000000c2e00c03a442d150054107501c0c0411a42c0340400c0040c00b490911841e062142e00041000a107482c802d4204601c48070303040d020100d10890030716040848072428040c03000792504000c0101800f5200140413400710390030800604141d221911010001d500458000b6003500a1030300201d0800080b68003c00254032524040b20407006105150200c440d9141c65242c280d800c182804010a0b000604201c103a900440001915004101a005080416800360405020740c0032404401038420807a68401d40c0150481c64101e07400c90308100543c00111440500c004000511f4010 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 786753147 1250 786751897 786751913
    0x1404050f1513051302030d1d190b1803070b1206210609060a0c0804020d0b07030f06170d0212121906031b060e030c1c0606030503191b 59
    0x4901d8060401109102410920000d6581c112850000d80d02c0ca01d80342c03001c505040048001c80c00c7e003031800c0350200030005800c4900740301d0503d001c3c1c82806922000c0c61040009480340000b00910a100c540d240c100c069508107468595a407640f09000300f0300e001501a0340c1c0c00480ba1203550300540d04603642d030b90400b002041050000f00d22144d81c0c80040d41c21101b501000104e0140078200010b050f20300e0000102d2054841c000f640070100701540d400d000058540d010000d0716203500c031742c0142e04e80d5a4100200d00a1895074540083c01d0b040031000200015420b1414005441a50940302c2c403010484090380e035550100c0b401c5201200c200864140308040588082d008440e202d00e102c0c415840100100684110390415165202c4a81543c032900b0740002e1424000e200506001c41c10103103c00010f9103525009050900904040d11011620f15043c60b0160750f85078021000c010303c0d0b840e814100d03940d030032400000e00c2d40040d603100c6515460090316510b00030703020f10340320880740d200349e0751a40c02d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 786754397 1250 786753147 786753181
    0x70e040e070b120a0612140c010905011b050c0301110c061f0b0c0a02060a050a1b0c0902130807060306030210031b1103090405090d18083703030203011404050f 70
    0x600568844012488000701c0c41c0d5008168007c0071184001c0c004a502c45e0304007045801a1818008000d038100210f90f0890308007007980c50034007964882c0c100c03681002c9040074a032050499241d403800b03407100801c40908020b0130440440e001102d01d503070364944641c81a001c004880c060161642c00c0104401d00c1c191009201c40c0e02c9050a0b03a501001d81d0780455220f420080100010500100b850079169907c1184202c2c01c80c0e100144024010458a0f100700401c0305008041c0d200c0c0e0005110340424800280360b0006200c103508481001d9074800e4014014003071808200e2240c8094204005214480d004602e8055600d4104d9203007008511015510642d10300d4020300c20b80014400341c440c40c2da480c03040030300c038407100c0014085200010400800018540315002c25002144100b840f5840000609269180c0e480d01c0000c0c01c218001800322120b040051000844410320300e81e10209070b41900998102c1c3c080860302c503400300d080420003041d50011203d03030080ca081080058102c603410b0700660 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 786755647 1250 786754397 786754411
    0x110d1b06181a011403031e0c121b061f0e15210106050301110706111b0f010b0a120f02060c030a080105030f160b0703050f03070e040e070b12 62
    0x1c071281e0303a42e1400c1e400035845442291907078840004104440c5082d80c0200a850f0890156141c080890041c100b13100441820078800d24010a95404004c02000b0b114510288000c826446441c0d122502150340c2d4013a6910b2514081c1502080d41c1802100c1d05919095444075840b44413414515825001a401442c1403180422082a01001d441d21050386004540c032589195083c0b580c220080c2c2512500d0340a00c0c00790303140c101a04900007940040d11f000592044011900d07060306144440c030303402070b210032100919500000458000000a411004044041c002c0c007815a030f00e010085451490711903507448803500f80211002440140a101d91140300400b22401d0051646469107180c00020070340005c40c010200510a03071808028180260391200d00800740810751101c080384860b900e200d500045503000c2404000c06020b030003516241d145801030940c503854607403c0200b1807100075200900030f51034255070020402c00801e05c181910a908201841c240c0208071000303101d14014800 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 786756897 1250 786755647 786755681
    0xc081906050c0d0f020c06071b0803040204091b0306050c0a120b0d0c06030c03050a0504050a0201050d14131a0702120d090506010605040501110304061407050c040c110d1b06 76
    0xc3e8002100c0b074402c0c01d104803007800005855101c0181001d00c1d020300948207109103e0621120741419010a00300e510240c0c3c0603003044d450382c495101040c081c1c80808001411106108540003400350081d0350801143c2c01007509002d41d84441580070704901c10000b0b450005807525112150031030198220101015014081200038a82d0f9100da2180c11100d40000c0c0c0081c1c4c0300c449401d41d455140c0182a0880080c1c003081001d400c29130703503ca42c1c6136219900241805004241c071410075201d5401a078407039410030004462031070804c2d02c0c001609940720003200c08250090080c0d5000064600843c4902e0550b00184800c444220404460f03400454000001c1a26641e182d40091400d01143d4002c00f8142c4170b80f82c5031420140003400245038601001c2040c3d20920081020360b0342b16507074400c0800f0040b0440e03641c00040c1042410503048448280e009030400b103400c40020390058159481e448440f080d585c071000101d1f4100ea480e49028690b1a250018031200c0b030108109500818201e504a603103 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 786758147 1250 786756897 786756907
    0x31204030e1003020307090e010f0501030e120c060103020a060f0e010e0f12010605040b2209030c020414070e0a0f170f070b03070215040b04060906060506040e040c081906050c 77
    0xc10342c845201d44000082e03004001d01c5401900940e0740009080c2180c80c0124545c140604200448128481c1d1410103489501c0115000c10501c1400125100c01c01c00350b6481c0043c88403183e070f4540c2844200c1c0540b03807106c3d000075220700c40d4010035280c101aa0750b08811909800044603850070441c0b02e00e90110959800340081e50700c40c03440f4101c2e000400c0022441d503280c0380410080701ca032505450300890000b0241000c4a80b11000540c4030802a0000a01011513044c111075180740400005e40040c6080420340343c00320b14020280c0b2403045a0f980602c042c405209020380300c543d910842203007102c040307810f008000100a800c25400302010031140420200d0071100d1500d40380e5031010f00c0401703001050204540c1d042c8000c20702000b40700c0040d044c40c1025070340c0440891008201130400d543d205000e01c10800581c0101004042c0104500e88a81d1100300d180851b50081e14126038080c1d4441002441d0700011505050200c12640202c000c400c86480c2e07040500002891070f5940e00341040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 786759397 1250 786758147 786758149
    0xf0f070504051806030c0102060f040312090609060f06061b0321060f030312110301140f06030c04090621170c0d0f020f060c1c0204030c14130e031204030e 68
    0x3e8a00c1d04034441070b8404250030030000303260601c00c28101d5581103400c440200980c51283c07000c00c07a041035041c44c00384080140c030105032004000075003005048900706200d031400e000041e0054580c88144038400c200d5982d5406040e6070915007600d0f140c4d00c42c0c0c3d101c007415003c640100806014101840005070040420070b40c0042100d04a0f0000091100c00c03840600505a20040c070f900316040428080012061a038a00500d83c041403250805041982491070501e0f2695585416041030142c8a2622800c040c820b082054020340a9034203044c4c03403c10b001a4088039405005c0c480554010040041709464a958900915022160700c60010030440d18010401c1003001c65004552075480c070381c0c025855070b002800d2102000d00400203a201360700b44113040700c00800701c0f400c004546903810001c032000c0c20b40c9c00c042c1c09158005840b41e00d01103800106501400c1200c0340c0d250080b5100f140458228002c0c90440d00f084200c4407256009004030060180c04655264000d4001d041142054007100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 786760647 1250 786759397 786759409
    0x1030606270b03010906030b090c03070302040c0519030c020c041515180603061d15010e030f01020d1517030703120612030f0f03090314030421051c050f0f07050405 72
    0xa485501c617655100f00404c1403009811880d034100d0404005800111480c100003070303031400c550201a1040c1d981d4007107100301602550458010b1a505461910404501d2001030000c000711b041c010050b0158044e00644c3c1d1825116805142d08094035001c020350170400350f01c03c4941400c8400b014080040c802c000a41c02d01c40d0408010202e41d43d004c6038042c180300107400140303007540d14115010741c04403c0c0410f4503031404249070a44001e2078841c0400510a000a161003480b40c0c0722101944000703003000a840f01604040000390890244079070240d42d5014814dc4013041590491244e0011b001c113500191040c1c108400e034561a03000441e500f51201c03040c41240840b2103041300410801d4100b118120b0b0480c00c05030881d0207a003400c0040110b9a100903048040c0c1e403000b00c0100e20000005402c0060010014a02100340c5410110307600307051001030507036405040c5810341c034007054007608100082d9020b401d00c03c8541e100700f41c1c484e4407490700c43d00c40114040d00c1501841024800415951034903 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 786761897 1250 786760647 786760649
    0x6040302030a0b0709091a010e15040909020306010f150c030201022b0e03090d03030e24010e0a0b0f0103090201030902100c020a051503070c030c020913050c01030606270b0301 77
    0x440c0310460b1800c026031301800602181c0d04c0302d4a06c80c1413607100c5101032034040d40054031030020309020916442d108001040519407410f40a4142c0000c1400b0030303500080d9108015251080c0d04031942a6202e209000655401e032041400d400b0016201c01004c41c0b0840401c01824480e00000d800c0ca8180d480c4c1f00d0384055205903144403501100c140e07140d015801d02410364510310b400f018500e0600b4010200d052460641c1c0c2c0a4141600c40000b80c031400720802114000e24030030320101f440881145403007440c5032028811013410210303180c00310f030100704c60703102e0885101c2c2d005000e070b00c84c0440b02c4010340103040210001d80c18165905044405030705e460054210708a074540c0c0d00d02075036070b1520400c14070b800c00e500180c2c041c0300707204840f0030f00544001c2200c0d0041c0503401d044002034410300d0100c41074800c29030021340102a0009210070010a0403001044510400c1600c42030307800040118101d07001d502c60100012100202040300c402000060f20740248a04030910303070b50b6116180c10f50290b1003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 786763147 1250 786761897 786761903
    0xc0703170705010623010c03080a090804030203010e0708060c032419090c11150a02090604080706020a030f080609190b0405180c03070f1e0302040e100501050a0506070602030606040302030a 83
    0xc0101c40b214641e41800c07240d4441801d00781a2580c511f10b850042485100410f1003424540d5102044148900e48c400c1c1d8000b103900400030311640c801e45004a8480704c092042a00c103100702800f1840200c141810340f4454800e40ca04000c0d644800d005040ca82c408004584d070300700d680c03150740c81c203050048101c1101070080c100740428103200405d001010600e420700401c51075001022a20030100d121102241c02c40750b14040580ca581e1404006141403003658040d0a080c8a0304400081c0e0580100b0a040d80354060749842540301c0300c2000551300400300321030b4150310007038900000305448a81c60541c848121b2244000500e44401c1004c10119481a076942e003185c10301909210700a102082030703000700c031402d4000c0c08030245080c0079504407140a020351030a90b200b610b8101d9510407548441001182c00030700500c44c801d2501c1103aa00c03048414906075080e42884000b1842e4240b034a40c1d00704442024044624080070360b01e407136009400241500743e121004000000c05079404018030f04860b80 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 786764397 1250 786763147 786763169
    0x30206010302090601050703091217070501051510050702100207080703080301170708121c02070f050c040b0f04050907120302100f150e360105010b0c07031707050106 73
    0x41103004000c0c02c03d1000700950704010301040b42c030b40000e500c50004400c4400204104107a1216490300a1056009031401d4000a0700843c01a007800030540109029007814002e51901034103003801d0045441d076000c030390008508100302d0000142440b0722541d04507200342c41590f802e503468008682c2040340a6100780c5400e41c010005100000040c504880a01c104400030321070b951800206a8a910060003031403812040032901b002d005805400c0001c00b4160050210b50703840407480c04c00c8280c1d84100080d10980b0441071900b4080c1018031854400e504010701c009080340121040101800008191600a0040b500c00050a0500c0c00074120300c18408d0300503180026007139041c24107c07104030100e602401d04045110895100500061050300c042425005641e541c40c500c000020400303026048109a141112030700c004050b01810750302110b000000c2c0041c2e42c0ea04440d000c00e003e21016a2140c0c0c100e10380c04c2000801c82040045213000c500000c03030030312546494060848000d90300c01000d1074 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 786765647 1250 786764397 786764399
    0xc092806121401060503190305130f090b09070e12030705150402011b0c06110328030b24031902070b0f010b0a081b070203070810060f0803070206030c0d050403020601 73
    0x40485442c51200007420000c015451a01e130029a845540c040c0440103440c0324a2240140340c8a041203c203510380c044500400f841d51480034002c00c8000340302d0b01e13060614200d0251080d160103c1321702e0041d6010f90343c40032400c1d490310400190b21130a0780d4496040c841001404000b074000c0c4494203400b41681d00e080c8480c6803a000146c01074601c0700000c200b000c03c0860120028090702c4c40c0506030781c09494032030018504108081e241d40314050704002044409500c14010310304240ca0600e03042000d985c144035009500d400c3c0420102a0369601d0340601004510703806a03e5084c01469124012800400d540100039152348100e83c0700070010f03507248299800b000300b46001701d115107004000c100d010a203401c103407a00c02410010b029010315403044855803401000451007040d903003040d40081c1039440984da54107540350b030391034849843c055641c10807400241e90800300b081502200c007600065850071251783d080150a40c0018000448044107101d0345003c0c0001d44103403031182c1d11a8000744219 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 786766897 1250 786765647 786765653
    0x60906140f0118020a0e1c03090603141b071e02100504051c03021f021b010c091806030c12030801091a09130f0b010e090c09280612 58
    0x61000411150a10a07580c00401240800340079020440e40b072003200607141c07107800e178084a4102c1c40c1c82890b0f9004600d04860070403000c08070303824004c0a100c0d4941c00140c55843c20286c00765030031701940131001004000001c5010a400064401d05441d46c0d904e1864050b650b51a640c011008040603140c030603240b0b40300d0045003891603682c0280f80c401e0030b10500341072134078000850400040b0300c005807150343c00c2009020940204400046c9450030013801c1d400300f14030072005000b50000054400c01c07183c80101d14410210611076604488800d99980c00c1403414140340c945c040d00002003e0400700d94880300000460500710941c8042c24141040701c81c081c8107402c005200726410f030001d86103280340088405008100780c402c00c001c01402ea580000d40d039a0203401c0c069803113461802820f44010b44280c0c0081055075070f00181600d600304500c24868556441d050707510480413103a07940003484100407a200e420f00100b0a4442107405c8101407528000c140e141c03040e1290b44c2c3c0076211041801c001c010030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 786768147 1250 786766897 786766931
    0xd0308131208150117060f030c130b010e0a05030d052b06030b060114090f0a091a120a02030307080d020d0908131e090519020a0e09010b0c0d050c0a060906 68
    0x4401d00b4640510318030941040031742031060261190748510030b012413a841e5600c09000c0f0019000c00100103808151031890080040d0020a10a50008101d03401c042c003a4174086524205a5102600078441d040f41c140c000e4a559120803907190303007210081090303007115802c0282403e407071420601c0815490b280d441c24180824000e04117070305004803207540c101c04502880644a1301c0c0c0301140c401401c0c0040d10003103a00320b00d007500100340c05404c00d8002c034448124a044141580b406031106c504000340302440c16103405501e407000390325410030458503001c41c0003480900103a80074014010310700340c00341090ba011100030010803500b03180d0106107060840305d040c035140000c0c82903221148603c806440c0300c0807202858042e200c916560382010500801400c04410304021400030115610708092601501208051710755a10440e0310200104199003040d05661300710780860024210784a501405503100d070020100a00700d4440d014040300410850b0080c91416030040600107500c07000b035211146 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 786769397 1250 786768147 786768181
    0x121b0a080426011e290130060302100219031805031609270b090a0f11030c04020708070209074a0d030e040b09091b03010501050d0308131208 62
    0x40d14032001c541c1175010481140d030f0301c10240034a80100c1c01c006103903084032100a020340801c004009070f149068500d19a60042c410780780200e4524400c0015480300300c0e5220880c0008040c0300d000440503000090290380b00d28400c1100b080541038094032071004c6490f04007040c00c040f10452105030104044a85480341058003541109200d02d403d0060280f041c00d16030200004080952030000100005000d201d21840c0640c00728082400f1151401d00d104c104850400c0984070340100d11851803d480c0038400c64455a0f40300c180f039402c20103e40c0800c040000010045010b12101240d004401c0c1000c1b6211844200c00c2601e0001d114004842446000380c01012408034a400c0c0d41c141c1402e643e01410002c4207549841c164071a11035100124002d84000010141c05c84903080c1440105000071982c0b000400c2c003800030645440d528000c040c00d0340c600388a00e68000c5c0341c0308403103400300e841a40c1c060b0b804408090845418a190b60311041c03952584000200000c014400b444160060449458 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 786770647 1250 786769397 786769421
    0x3071a12070806030d08371a011e0c06021902120405150c01020c12070209070c0209070c020118080c01081311040209040905121b0a080426011e 63
    0x4481c079064011964031000c0e080d1711000d110071900003800e0a0f80150184501c0f50200500010701c054201d05108802c01d21401841030606001c42c56501480c002c03512144808140e60788108640c1001010740050011003440c003c0000c0303c00c1d00740c0854450300041125405c041c40e4a070888180c040f0083c20000c0c0d071080c030f281404041004000175075032035003c602c01000c4844038075650740c00d00e840240248034074408002d5500a0040b107440246411010b04842d900aa640480950b81d245084520762203a0300b000b54030408101c007003824244502d001102d000d00c18100010444040d0f40f103203071075914550049029602c0002a4001940c2c061426500041d1072194200303e0407076580c82e44d101440c80d02c00113003e180e0105500c80c00355501c1d00071002154014040d1120a01c0d41c03c20400079a004c0361076007443c1c02204282d07107401c40700000c07180c40c8a900104400e00303190800d14003e045444403c0c0d01841100c4501e001480c0020070710030000d01c0151100f101c0c001104000702e070030648171490310321 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 786771897 1250 786770647 786770657
    0x270106050603060405180f010203151f050307121505010e060a0801052e0f11030406020a080f070503040608010509060d3210060f0b0304020105041403071a1207 70
    0xc021940310401525041801150f0215095035145000c000c405480d000013001032203a00141043c3c600190300640c010074549403540001e00c001410700080e1030110b54050110003e801c2e44903040340c841c00285421180740d1602c0124480c01445800944021460a40100d0349240013001350b582c12030703c0b0504c095403d9407010304140761080f0242294005100c0c1601072030141c4580b051400d07100c54401801034458000e032107045103041c4010101d00040300440c3c00304c1d040c0040401040000401c2d90704a66103603009045c00030340c1da520b540c650b801070b65076903104405c180041000108180003030000303400750f90303100e85035580741600b0411070070005841140248002804003000c160aa0082e01190743e2400a81103a40150380a1001e0f039605c00c0d44050041c051400c1c100c0c400d0142d03402000c22603402c800e200420035106c1c4d0f2010243d00c01550003e01084080004000c900308c43c10005840140041c180d505103540c1e03050703107100d9a525070000c1c82904030028224803000380f24031703126403c82c200d4540 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 786773147 1250 786771897 786771899
    0x110d03060b032206020c060a050124181521050c03010e07020a050709060e161e020102190801091a010905010509030f0106062f0712031106270106 64
    0x2180d840c8809041c10900291402c107062441c0f81104103030701802d602a0b001c5558200c80c00d0b2841d1664810799440040340e0a020000410300300384c000c06500b0509100d0380040821245009641e0400900d080103003006007800c0003d02d20441810b0400144140c0d116003110398060034248400c00000d0350185600c52900c03051100b1600c01100fa01c0c15aa10381420901d6034407440c1041e4505820244018181d2049103004070740801990020800c4a6100c0c2a61500c2e0311440d0942d442c50711000d4002000882e141c0981540f400174902000f464140f5000041c68004c65440d090304011043c2200c1c0b0200c2c04090042081114071b210b031416500700d00c0f6504035010b2103040001c001007210700c19075040040200b110400d0365802d0001001000c10440208540340d034410000e89207560304804403445414100f4120bc0c101c0048800d2803034000e6010140c1100c03410145001c4041e694080c06174100800301d10146030320107082001c0303402a49003c10240c002e059190071400c101c1e0000172003c209905145d4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 786774397 1250 786773147 786773159
    0x6100b070f060504020d0b010305010209100311220306110315060a1e12060806060114120c13090c090f050301061413020c1b0108070305090a0204200406110d0306 71
    0x1c20300504903403010001c919a2a01d000044140420030005840301078100d0000080000c15030041499001c180c074255005c5507000c80c103400300d8a4141c075a2403840410000003440c628443e050400e8015038420600d04a6169201e1a04444071650107040b1540700005021f4400d05840100e5003103142100c0b4103140c4004d1000017041d40302250031400c3c0750651000e0700d0050f18018044d07118030064405080200507607860b181961101c00b91101804507400600030f07444900c2600854014481401c041403503500c5a211084182d4003081280400c4401d144010401c0740450055803500c2e851940d441c1d000d41d060001007a1000b4041d40443e2103a850607408108200d05101c5201d18001d003141e18417004030185420360041e01c580047c4108038064000541d95074204801200400c1c03030203a0b900801c0340c1c0d03100416800c50304d041e6003141046d030280103034000600e4240c020a1041e81445104089904501d14004007900207810883c0890310040d846a9840c1e42049460240503851a0a201c06440e0038 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 786775647 1250 786774397 786774413
    0x17040201020a060c0228110a030f0b040203011104060806120616081332031204110f0405010f0303021006050d08210406141b0a0507030912030206100b07 67
    0x81001400346407130707840d0030704440e00912900082e140c0303c035910544100c01c03a40ca06008100d03180c04480c40104110317004103a0a00008482c01d60760710404407c41c580d255118820110001070040f6810764840e5400306000d400d0f080900010700b03640c1c0310b413074407403d0880400803030b0300480c4d00c0000c082d84203108000070201f1840b01148540d203282000b0005440e40e03101c1b801103900100e4050041c50030110030f201c0755125444401041d0034078500c400904015070354450303107074031410181c0d01803000e01501160100c0c000d00414012160003d1490102102c02808102500c01c00d038050305d00c18015040c10000c0c181c040c00110901980d5403010045d4030304010000d606940d40c00b034043c20f48500815a03905000c40010301034104060022400300c1c5142c01e2501401030701011501c070324030a003103102141c0c2550203007038020040d000550f211420050884002c9505801c081c100f542082154400045c807a010f582e81071140da401fa6019108a25088030407880e104201c0d80602140c090401c07009001c10100e07 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 786776897 1250 786775647 786775663
    0x70f0e030607141b070e0702150402100302090924030a050a11030f0f0c10020c1011070302090a090c080d0e01080c04090c09080c01030209210712030e011704020102 72
    0xb8100050490079400d051116800b446403c0c04030314501100489012a0005081003110300c1c80c0a103181e16603aa5402300d80391802090248081c600304d40c0840c00608c4c012030f60089004040c9001418170607a4400100c91032003d80d4500d017030036003080c1100310f00c180314054040b45480a070010300c04200365503142640c42c600400090003c41651b030010900d0760f400d1111081d0040e202085801003030040f0440d41c2c07680f080d280304503c180b250050f40c02d049400880ca10a108030003e00300c400b4070540100680d0b9000d0382c800c03103103080d018a460100050703861310340b018002c51007198005810195454a01007014840d000140c40c2d910000c040e001841d4000d511210510084c40c240040e07031a50000700180d8080da4005543c6e450410040d58485a8480d001404884548088034003402400380107501324805d20382025000070703030081c034481c1440500740c04142040b0340380115440e031540c400300024600f00303080d0b0403400030309000003402d01903905c800c03211400403d02244a1060819a00103507a500741 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 786778147 1250 786776897 786776911
    0x2070f0b0f0a030207020a1d070804110f0a09060f0e010803130b070204060504050408070303050f060102030d091524060f2109020319051002180613031a070f0e0306 72
    0x1c00076400780442c2c0700b0340644285581c050140000355440c3d0640e05810b01a000d85440700303090050000d48402d206a001c24012070304904103548241044090201e01715092442d25003040036000006a5811030303102d0a001082d100004804107420401800680314041e0710050b4980d1007801030044010942c1d110a00b1200e0000b03043d56503405610105d00540076079881543c0c4a441d14040005102c165002807040d0741c0f00743d1b020400355444141d4000c00400649106006902c2440a40d0700c850302c1c0e50040305014050442a440401154105d0f0141c40309649072920100c90306000002e181c1501036040003030b2009007405121800d00040003442186811005c00e800c900306003070b0a410f814079910042c80c0540140994020204050464880e94846442142e662141040700c003603007041442900c0d01100d050344405d17031012240d03080091507000900003500140e0010000800240c561824038079411103840540311501d0013500140c0711b082400c00403402c0c009090320f09605550042003003644000303 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 786779397 1250 786778147 786778177
    0xb1005040509041704030b07030b030d0806010c020301021210030203070b071703150d0602091809121308070909060506030309090613020702090921040f0603050c2802070f0b 76
    0x1c3c544c2840543c0c220b011103084050200020007100740f100e40c10b0300612841854406200c22091602031544d141803003070704280081c19030710120b803803036210314111658140000e00141c200754491802211042c020740e0204000c0b00c5583d402c204506086c4103041c014200d9450032810450035450f0110104d0f02c011052035800400030018070b028101c82c1c0d1541d0080d00251070710002c0c8210345802ca00079489808184d10901600300c0813448415201d00d4203100e1555074024005056041e07070300034096081b00d50a03142c0c6c078a043e18003190f5001c0c2007005500400400601144200700c60400360111040608118000d0b08100800d8030191100c60b4844e8001c132065401c40080c0000c0c101480003405100300c000d50110056060121715170300028480d0500224460841c541080c0340180d44062050344103080c4107411019040204278000d600599004451040c1c1d5864030411001d150000d02c0d00b040910f9030482e140c0401244154104140009171020404031400c46040090481440c0079060091054403 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 786780647 1250 786779397 786779401
    0x51206011d07051b0a0b0114030a06020a0215160f03020a0e0d03090503010f0603120206010e0a0f060b031305120a05390f010c03090b01120c1a09040b1005040509 71
    0x54803440403112164a001580768556288130f002603281d03504108141e6107901148001f1407000e4080500c02d4149000030300400800301e00da5140ea01a41045450f8401d6024090640b0403c18001c00c1680c41000c074070034000e0400c8070340703070740944111140081401010b106201d00d0843c2600182c3d4801e4444003140c5000c183e13421071400701c400c489950050f9401d5402c2102c07045002d045030b04840d05480c4540307480140e40c40034603408ca903112070034072030040c061920744d01140321580742da840178410415005010034600d0300c0311700708115940192080c041f002980e02c249414004203210300d4814000100760185001031284004016014a410008444a460b98840c10080007800013106014a030254154404000121161540c540c1d60301003080b9400c00c141010203910074494a54840d920110805042e424401221007915001100b25400c0e012110042442404000110b040400c0c0202103565420342c9010301c01940c440e01016805482c01c10420b480c0c06811030141c400b5030340103803240ea07607075 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 786781897 1250 786780647 786780661
    0x20108040b06031c111005041e111c23060115030f050a021c112505100c030c0801081011071205090a05090411060c0a1a01051206011d 59
    0x204030080c1190000318850b09260801171900006001c0000d4032480103964900340700ba204200c400a1000020403003a0940c143d02c150000d4005011b1141c01c250700c0b0107030010941064401461012544581c400d800030014a20295401901546040074500402c1d0b68039a54804040c01010b0218040140c001c031414070070fa0003102c280c0c03443c1006100b21309240500100943c0300c040030003006034001200c10100c4501c1d0217402d2118010207011860004001c81c0704203032000100001c00203049007100040031070b104000a110003042e51200045035280c8020250480d1101c3c0300507018444032200401408201240d81850610504004258031032800d00021141c4240ca00040000d27100507440440a507000c0050004030000351011158540c941c005c00c0800383d400ca03801482021440000300590030308001400504c00b64900301c0700350004075582c8200e0b8400740c444a201c000346c6c9000400c060710300f034924a041701030300102a0025506080303010103402c4611001d040707e103403036074085079072 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 786783147 1250 786781897 786781903
    0x160308130c0b0c061006090311010504090f1505121b01030b030a030207140904020f10051308010e10050c0a1d041b03051008100902040f0c0203030f07020a020108040b0603 75
    0xc150710510003601c03141c0300c0803054441d4010320300302401d80c40750320001140440c000d040340c030a880c0103460384c410051a580d42c5d4840305104658650401c0003c1c00001003000441c06500d200c40d600050105804140d000341800070002d07079101e00e1141581c50700e605450b560100340c03002e4144c07030407400385500689040160003074103020a0380303901032103040c07004404d060b40825070702d05540070000030045100c05481004590a81a10003941c0100f60b050304181914003034072208525492410000e0601c0348842c40c050030020141c2c0114410b9442d51110420b45105202c00001110882c908026504001e040014603000311602041800f042c00d0641002c2074071034450700d0391200010000c0c0010b080d1703400d1079064210301c134900d1000b04e406d00e03011804159003141e200c030580f11110b00400e09102c0044c017200c040c1c048200d090383c1155032070741c5d054404e840d40e00860b84561415001035a490034001c00c1d05607524401024902103410485c11103005070381c00484a130300700b070704071600c42da2544451000a00f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 786784397 1250 786783147 786783181
    0x1140610051e19020f070b09040218130603060608030327101e0e070509070f030b04020724020910031d060403020706020c060c10090807050729160308 66
    0x700320b01e000c07440054200d400303410510403a9099003035590071000712040741e513a8409801290b01412080c0112220b5081503809008084031881c2107082c2406c1c044046445200c0000200040b40d0315040c0c01d00c180320140c01010700506c0301c94000c1d499480c00803000380d2040003280b07458050b40841c1406c2c00c108101001801e003000102e2008109158194055250483c403501341c207941c0f00c1c03c001c0748025100020450204592011b03100c041c841e42d49030402c4903558105a907200a040d90340d40b40108a44951018000b860321070142c4081070010880ca254014041803419840e00340100035011f0320b52502d44105181c0052800d020030303d04299010310900c0a40c004032445c3d10700c110410403041c55800940c90044032041e03002e9910301034400701400600e1050003101e0415038003500e507c01a003100b940c00354404d1400740c2da0041c00d280742d41d66198101001684840c441e884c1a5030524191019140c0c0c1110120310b5490151074559071511516001c500f800d80901800b0809002416450240c0301480c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 786785647 1250 786784397 786784447
    0x111030f0f0c1c0c020907050c0a030e180c030403091a0a03020304060621151a0d02180f0a0609140f040c0f120b0901151203120203070509030114061005 67
    0x10b40108803040003413401404800c2a4441c010220218107075a00400c200c2d40402d018070702800c190b004c1780c1c40546041007440c1c86247c20240310b20344250340d103c0840c540d82c00340c410700c07140533079034102070500500002064104024040c216425442c07035804800465103040f1083c203000d61070382e035a824400024045580100c00c030079036400d8070380b901c1c014001c1c00740ca03680c4c840d501c0c0602491001d43c82808503150702d99000c68000d21032a0303103411450120083d065080c0f005244d40311030300c0504407841d0422001c4d250041100705040038080c483c0824040c0002801d899201003229004105140c2551303140906400d00400445c80070906102031052380101816059000030405640d880601026107442c07032050711207417020310100790307000018041c1a040c400f04141c840c48060500030102c45440844200b2000e100100203100010406c43c0041d520a0130107072a029200c49241c801d141c00d407020f039000f2020806104003000f0b102c2d6135400f07241000c01d200703280654507419400e25601c64540700c0700c07001c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 786786897 1250 786785647 786785683
    0x1505040f09090b15060f0d0f091b050303090d1b0b130e0c070b0402090a0b1c02030c0d1205160f060c12050c0403020105071a07020601050111030f0f0c 66
    0x2041448642c2c2090180b01c0c4103441da0341090756643c0f8034951107000b00340107591000b400c1000d004103803000d0000d0041140c6244000030070b0350b240c40c00c0e04116410b111044030101014410511502a4840f42200038039050b00034515002400d030000300b100c082842c005044000158859140a00d400d4080d0007511b4041c0c96950b5840c00110020320101140c840d102c14401207000040b8811040c0d000d4960180e07103e1011441601c13203a08000da08500144164072040c0d030345c1d00c4401607641b8100f80010240002003c60a030841e01d005060030600e11482841c01400e1035480c40c0e002034510303159150049420f25005840c2c010442d140320b82c42c0c6920f82c0c081c00948200e010710051040340e070b00040c81c00d001d9844420809404140c801c007503c00071039001240c0c000c103100c20405940900010503040b07219200307032500d100d003010303c1c044c50800039a000c000681c40000144000e58001ea020207684d184000114144008135006908070722500004002c22000403c0c1f194403c0420801d00082c21106611 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 786788147 1250 786786897 786786899
    0x30e06010801020d0605030a050d1b0816150203070804020108060d0b09100b1813020406030501020a020a1106250201021e1f020c0c010c02030313030602120a060f1505040f 75
    0x528083d4020903c4c030321500740340000008007440d000422141d8141d211000c0c00c844103000c07d0903140e15002103c8405a003071030f0719080000a100c0130040030320302c0102240d240c40c180c95003402070a60511003010b4040c5403041040c03107000c0f50081c000381d038070039070910b031001140d13070b640c40230800c3c0014401d0000c1c48130446c4400c0c04180a030116040f40001ea586608110311f0403401d040150014050480e100c028500102003a2984c6848051481e01400600302281c1c0c03030743c2ea695203400c9078090829140180c00c26141c090801c50381100321004954100d43c050b0402080c02903050340c0d9101c0c02860144114200424000c69009011090b00c44624082c84044207034041c8074a43c560400d00c103030b0445c105e00c01010301c1980006100340da0800380c101005013042803901c0011f681100004a0aa07414841840700f40f42c010850300d0014091071080c80f0150b25091424000038041c42d01400c4403149a0504400f40100e4102170440b408480301a10700c507070440c826070000e0306c4c40d205540000321070348d0200394 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 786789397 1250 786788147 786788159
    0x2060c011802040c0c02060318010204050a06080412090b0a0e031204080f0c0901032a051302071e0f0f030512010605040509160504060e1206040b0414030a080a0c030e0601 75
    0x80104649802a9004d0102c007910000488500d441e400c0d00070340c000c80603c04501201314240140605c01c03c144001850b040e06c44000804d00d80d0158400e05c00a41e14404000c00c000d041895038042d1241400c054042c6410683c5000721070042506403001c21140c42020a9140d07020044883c2e0103c1c0c207100c03c0d0b5503075114000b040d00d0b00d801e00030804030b92092016200752810524080c5041341d0304403880010303980c0e44034600c003030f850311901041c80010400070010805503104020700e07802d45014180141d41c0c0100f880d0116400c034082118107045107000d1907040102d8513064640e00001d900c10340114000900d071a05075401c0c01070294a20040c440200042075980c0c000000300141c0f84100c0b10210140e5580d0383c0e031b42c07080802c41035100000d04184003c00085e8020011420440c400506054414560341405490180308440c03c2e07940704146814842800070b14030440d000d041000000d546842c40b4104003810388600607004110240c1d03114403503080c15229a2040f201e010906060380c1d11960740304 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 786790647 1250 786789397 786789431
    0xf04050607050c120d0207090b060912060a060611030304020402030c040f091a060901230c120307031103040308060616050303040b0f090a110415050a06021006060306120f02060c01 79
    0x21483c2d6004180e110303036a0110700c00008600300c00c003409034020a503d904003070f07216020301901c1d1092030b00020b091280c00d00f103540c0d0300b00030f40c80d42140d030000b05820b00d4000715000c1643c08550010003171041c00142d280070010044201d950017a01503401503030300d45401003182817038850340d848800c0890400c80f02007a00803d58100f810450b5401f848040710420400c00c02200344244c1002c0d60220b068101c40300600c0c40401da031030300d1503070b0129902c03820704c085517400c5070500080c01d91940c00844000100907815030103109400507899100319440c15071a0030342e40a0a40700300500310511420f0041200480d6030000212081c003a075010301a6516420b06e45444048200d0549401c2406402c0000003842c842c1e0008881500b980c00410b0108120914400d210080c07080f00586403048000d50700104254485113108001008a0307402807040c42442181501107500d00e0b00200101810000100080220b4501c040c0c0f1854210f00c0e036142110a920000341103119004516101d5400c005410500d60715030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 786791897 1250 786790647 786790663
    0x1908030601020d050c0a02040906180b01031a0108150a060929040b061c0b0a0b03071d010f03181b0e0a0902060318121c0e0c0f04020f0405060705 64
    0xa03000c0f2400c0018000f02034426014003803621040e68441007103100580f42c1900f1610074a800b400c400164802011900460480b2040080e200d0039905401001000724594103910f00d14030118001c5d440d0350400203880e4640b0903058100c0030b414140004600c2d4042d06d644044014500748074100314202111010405120004d522198141c040703c80d2035069007003038058804544002000039140910b801001a440c55412902c050829603a1303c200e0002e03115412a01c0180000e200700136280d280c01100201520007244188055104543c0d9940c0c00da6005441c1100c1100c241c12302003002c4000c20f0384100ca0f411140d0f8042d04d2541500c1c0b000c49001b20119000c0f0940300020800722081d599091840c0941304001402500868100700084c2c603034484100c641c0b481d031030f1102500c0011f03403042c0001c03245030070040202020101c48500c0081800c040d100781d98030708456001408029080100007052039480d0440c160140b03800007034404010710011300300c4014200061145450300d1071414499620151 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 786793147 1250 786791897 786791899
    0xc03100f0f1505101e05070b07024306050d0605030304030803010608060d06020f13050405090c011202091207050f0a14130608060718120f0b0919080306 67
    0x2034504501c030541c1e990301402c04444000b00c5011081031802c02404450708140520408101c41d0311203030321281c10043e03a0a115850155261902c40d0740e0380c1040031864201030404029940402e011384c04000c8143e410f202401409241c44034001c4070440c40c645e0224802d0980c03000718005800101d08560002c0250107075500c810703410002192250103040c2e9900c95804043c1803800d0130f000403c00c0e10311401a82d0b0344070a000e070850800d01c1440d61a0002e90f0045071580340c1603070303010034015107482800c890400285000c507000d10450134a460016120320716410620b04002060189008012050b0100c2e0b5003008007800c0300c04808030700c005903031f200c8a0741d004940c41a4220807101a0300e10700780225038162580700f01c02c101114008010004c00761035417600030503542d86030000040c5e400c0040c132100b403048400d41c581c080602600c1003400c13443c00da03c1d00703c80c2c070401100403020040345002d0800031103680d110501c00c032261548c5540d2490044124802c0b220034214103490713800c100c0300501450003000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 786794397 1250 786793147 786793151
    0x60e060706360c12020102070515070b0a1b030b0604170f101e09050109080a050c1608030f070224040e01121e02041104270209010807110c03100f 64
    0x114000c400c89500c4480c0c2d00500311500c83e000c14000c5100e1100407100d214414012546e02e169150041241085241c07039415117050701081c130341d060000e0402c1c103e03806498a13400b042040c0c030300200c60000350100c610b21402c05544615008641e16080110703000b4114500000340c4000740012503030395404613410100300c0360254a1044641134100d0080c05104121030340a610b00b202c070007690300010800c182c0c09803074544d212642030000c11032040044c84080b400f6a2560366404180601500d0000841c0c2c11200e200c02c64201089018000310650b000c100314101c0c46a9200b80900005000c0ca0010f840c1855810050b01d0590102140398010011a4900d01c0c0c10130076070f80e9402e4018030341c071000000540742c1c0c0490f100034a0240303000c400b201d0900744000d0000400b110303445844255504241c00041c4415510041c2c07042c100c1422040049034241600d003035182400f4040000c2000c2c10241c01c0a061000403803040441403018048a401544d01401b1034000e602001203445c00781006210b4604558 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 786795647 1250 786794397 786794471
    0xd050f01020d1404053a05031617010b0f04030204020a030e071502070501030f020c0703150614180402060c0f06040b011d011401050c010609060806010b03040c060e060706 75
    0x5520701001445150004060411000d40119219041c0701c0306d46030302c081600084121881343d031103580004000c03d20380c0d0f501e9228a80041901e0030001c42148039800e022404850303144900d4900138060556007403100045d1200318501c0d45400c58000c50304003d600600225044841c144c0c503a10000713070269480308451300b041e40c85a0203070050b0240d0b801980182c100380c80c20301c800e50091304041c0f070042c4005001807901210383c6086042080b56002181c00300f658540c41d405004240c051711018080b41111032001403001303400145481c2d28000545619451080001e00750340e140d41c10340d0418040c0d031003540c804401303240d0700607200ca80031542166084014070000c185c100301150a58031501810072221250303400c00c200a9030798901409072070b04100f02000003084e82202802608010001c85001150490500b01800e003403110503000540c031000c0600401000c03d130384401c094103e41a504005c4120f184007004110b55100e01d02001d0180d9040c511000003000c000c0c0d19032000050301d420084012 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 786796897 1250 786795647 786795671
    0x201021c050a150b0d020307050702041e0c050f090d020a0f0603050115030b1809120d1406040e07140402040b031e070f0f14070210050c010f0b0d0609020d050f01020d 73
    0x90300c550160303103984e02e803e102c0c075544a030540d4015a04410282002410300250354000340c00d44034060300b1204420315400110f00390f06098007492462501e02d04180f414140c500440c0a201c0c05803d01c902d01c0b46000000c018199118054410082c10340c005000110945903400a00505428480d021f281450001c82003200d6100348259400302c2001490b00012155000b00706100724005803240010740620b800d11b0312100201c0c4024203d10b034007440c0120f06a4034010b00c0c40e03013507880200707480e00840c00c2a001c120f41800c040750314401e542e11112502041c3c04a20046002409947c010340c0c80404000140107410f07601c50f000b41c2c8041904000303400c0382d6460010844910188407035100221b0241c81164440c070b401b0b130b45e440e0360b8000000b40c2c25007011090380024038140c4074440110085480042e40f5540f84a0a018002010110030001e000c072140e00d030b01280c82c10f86003032000f4003545d60300c04840086550304100c0340c886136040703406c8031214484078a20900030b500038490181c41c585818021815 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 786798147 1250 786796897 786796931
    0x503040e0411060906040501261f0e01050a05190509010b0910230d0905061e07050a050304030807020a0f03080106031503020f150c0a0b010302150c06060609010201021c050a 76
    0x2131050094a01c6080614020040d510811a03031156010444440a800240030203149054480d8404412006200245202d14030304e8070b000e40c10568508850500601c415142c5081c140308440003039a55841150024059449074007090300042d5000c0e8180f400000c0c09441c980c05001d0f1903c0880c0c0501420f00110f00642d2a500050f5940f50721346441c040720035001180c18064501c2a04040c00480c032960556134540c102001115480040807e010880102d13503803903640c46520003003504007a4902002034601a1203400000c200408010f40c000015114910a001c01c00b101d5507c821055002420703890003a0860909019040006e4603003101100818444854041281c3d001b60410040d01d9252050095031003003030a00303000003001080f40020500040000c003000310700031850301c03181d94103505c1040700400c4043e50801c1d942209029140469030049445a0030040c1100c44a50700d120000c0181e01a00505000410045c48000c0900c00d103149074100e948980109401049001c550000d1810 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 786799397 1250 786798147 786798157
    0x90a020901140a0302040f02090d080c15010e1306090221060703020a050f0915040f1410020607032705330a090c0909060c1e0e19030503040e041106 65
    0x2910200f000b6080000d41015402500e01c2c0c081c03032401510b000c0303122020075400c0100d00303011194800000781c4141500e00c240007280c1c0380e41410264207559490090032540707042d000344c280b101c2c03101e28946801c1000344035800052001c0e80a0702c00d8000c0d07860003500c01e03808800d482755030b6481d0051500050485210303108a0745206500d032502410503c51940085c0700740c0200e0301d0244c100380c0d4507042d00503010005000d840140003202c0400314240c10010700c941000e0710740310b4443c0a036000081050b19960041607407640411030741b82c001303100215032000c01d8140f0481409803c10401e240c29140500401050035001805c0781818040031404180900f02c00890409072190f186940d04041007000041da04110101030040b1203640c400c94460364079400b201d482c00380851340d041c1d443c0004044542c200c103490341111b41048407690764010548001d03040510500c40184103c49a0070000242042992440c0c003458003c5d007200e844649079120200001825074096602c20701c8581b101d14185032203c100c403 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 786800647 1250 786799397 786799399
    0xb0f090f04030905030721080903010203040c171212060f120c0f0a06021c0203041505030403081003020a210803072708030d05070c050a0305220b031f0905090a02090114 74
    0x80d240d1480590400e47e40c0c403e06400c40301c0c0e00d8200316180c034640d000d0002d180180e0148884485184c07410140c42070510307000404500980060841e6909915010280c6511028489440885a4680f400242c80d51120b40d44603600c071006a0400e102040d0016404c9881c0c5026182100b60707210704800c2082aa0040c8140001030340300e020b007542c111403000b100b1150141c05004413820b0a880c0c01005403c52091040940050800f00030442495400048507801c5100068080300c00360441d00481c02c4e842850044200c049a8161000a4800f410160f24016a04544c140741c6a0a00d040000c2c40145420402c50800c49026480c0d0204150600d0840485074910b000310300d0202c00950b401c01821009004005002c1d01a80c040003141d428400d0502151280e55a9580d07120030101e5420118100070000c503a922041000b81b140c00e0f508811250004002001004040107401030060501559002207009174103003c140901e91b400014411030151007250b06100503070f2a42c03188800002c0442c101 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 786801897 1250 786800647 786800669
    0x60b03011119021906020a02160b21100911120412020105061c020405280f0c02031e0f0418060510080402090f040203010e07140a1202060d0b0f090f040309050307 71
    0x600c0000c5c1441d802019840c0a80c01650b4611911440c00003031807001e0381c008070007808005940d1300c40c40181408241481d00c1e0922401041c1810340c0b5a03d42c41441c2e02030014042e80d03038080031484400b00800d6600150103280602201d04c1e01d8070b80319603045100c4204402542c04d10b00452414684403101402212102400300c501002580030440544005400000d03007001c51224001030650884516019000741d80020814128140c40b02003150321042001d411500188038104d544680300c80541c0000c0034501c03099844081800150f500340c42158006e01100300d803041644040602500306000315107049a442d094010764110540c2c1c05a0210350095000744604000380a010001902640050019000060003418800700e80d181c003040f6004581069541e0080300e01e24500768000714040c15070360403103200e042c001c1d40c04102a4047c044201320b00341e46460000c8807030703150526004ca814200800f01a61401c0c44011810340700e03025602a800103c00c07880c0416a0f00740003c030700e400c4451034510 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 786803147 1250 786801897 786801943
    0x501030f08030403120f0524130509030d1d061f05060703020f061e0109090b161713140106031101031d0a0503030105011d011209060b0301111902 64
    0x1c0241991000307008030140300030300c207502c1201185440b40182c40209544000703194142412031340d518a003201e03101e502c00ca5076100710742c00944581004844000c05482c0c00f082a480728200c0310f0030b40c0070f188155103503070745007a200103601200d80038503c00401214081c1c1e91282c0307600c01000d1240c02e040c960b03000e21a5200d24100440d0a00400809100c1c0c0284152003404100c455410700b448816202040d4a42c0a90212000803217103007441c60041070120300400c83d21201e9561110b0320f00d0b004091254494110705e09012441c003c14000b90110501e00b402d002c1c80c0341802c45070101c902c02c4007040d108a4140030b25405480014400c1c80c05490304901a0181420340000440181809207200d100e92030340700c042e212030024104943c1d90854402d20266072690b042000041502c00e8015185401e4501c0404440041e41c221102c0c0c0100301040002048444141c10141c000c0d0035408042c9805618018404041c1d480c008040d00080e07410f1070a07000b601c14810000c99036022080c2c0303441ca41d0512444 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 786804397 1250 786803147 786803153
    0x7081b04063e0f0c0105090d020909030d02040305160503191506050d050c030f15010b03270604020411040b16021807020c0102060112080706050c04120c08060a0501030f 74
    0x2546580520354050b00c488a890020500c4001c01e0684000c0320360b6601c01003503010303001018081d040030800280303003039400c0c00141c0d00080e103a0000c425000e40981b08903004691001d00500449004402140303040d59602d42c0da18110350b0b00c503000076511024403030365400403405182c085110341000c185004403038610145510342d1141c416031401c4070f00269a55040000d01916581c410b03880e2140100040c201605408043c503040c140d00300c03205d806c1c2e40c1018010f0603001751050030a9056809200310139440366107208080b02c03403042c0304140720f16051443c024000d14010008440b0b128510948081c401400c015a100819025074012000c3c13040f41400102d40e03c1e55044204541d01d80000c103402c4840c06401043c039400c1c5003d69840005807c0414020340c1c0d0b580400c007150041502e50501d01c51880903465001d01805240e500510341c645903004614001c4000301950081c01311812810701e4a200d03071810f105907aa592103505524080d24002850071810307440340d039040300d400c0120808050070580e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 786805647 1250 786804397 786804437
    0x20a060f0204090f0b040515090415090204020423010819050c090d0305040609080a0f0213060f0b04091a0d1401020f120f06033c030307081b0406 64
    0x400c660361040d8240300006044106000b504860380044900103203901d0f6040c00e002c10307118010503a010100004c42c0b213036525100c6051181c1e00c1500300c104a5052322401007028041e082c1072801a500900101380419903151221280300301640311092080700000c100f0041da4400d07411510000000e8000c140300e0488180d030b4025551101281c00ca185c94081031800142c02010042d80070ba0000702c010a0900c00700b0b0300410035030082c1507484000c10a84040360798214400d0010b00c0002d02510b0320300350402c080d004640029001e80f45a000f003181164558041c174410740c0041c4142d81030203003030654080c524003140d40003006002028024004200c0300741c850749101884414100004e46d401c11070b00030040c00100241404014050721104581401540700411602c090b0189100b50480c0c2c03080300e440f91015070070801400000803440655482c01c14003e0003e0355100068a0500000040180159000da480b43c4031340780c1c5d42d805820210070b50007250464001d5010740000700b004030410000790b80c644 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 786806897 1250 786805647 786805661
    0xe010c02121902070906080c01090f1404020d0f141b0702030c011412010b19020105060102060f090c0312070c1505040909060e0a030f031802090a050a0b030318150307020a06 76
    0x5004413201a907035441c4c4203003244d50503480400140c0240c0001c1000e582d220407048001d014401c1e12980641c01c10402c0c0c0c14500c80e4008541c0304c0c17680010400d000300d000340c005200340360b0507482c10000c8800004001c850381e034040740c080e00b690200c405010181ca48403002d840c40d441e00a001030201d07605403001500c41600d00c0b0071004144209214106621070082d81050281c181c230300c0c40d6030302c440d4490311203e002013180b001d1400356414001000000c1c2d84c00a95154403400c070a50020668403030402c0c03141414004012290107010b41d154081c146000741c0c0c0200b048034443c000b40810b8030b54070030a280c0104044901c1e180025020402040004210f4010300f0700c1c030b07014a00c0000c154a0080805140c09090402103010580d100501100150580718400443c1545800c221001900f076000034000030b0000c100c0c03847c8560f01c00115203140510b81c44444024000b40c00c4a0b076419880e0002c3c2e0328000f940300c61500c10111080f140d4440d08541044d00d004003200d030014500c040c0d1958549c0081d00320 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 786808147 1250 786806897 786806947
    0xf09010c0506160207060503160f090f06030b1216030305090f100804032a030c0501020403060c08041101050406050f160213060e06240705070302130e010c0212 70
    0x10264801000c00d01c14004240503d500c0da050f1040006103440213420405181e000d44180a02401000004241680300740002411860141c5c038000361050b0640f618009a000020380c0181c0460105900390503a00541c0350318002c5440c000c41043c9034140c0741d44c8500005202010302e489200410000380501c000d0104240d00501028010751000085004440e980b0b0500c00000c61110a1000389a084650001c68814004111380248850802d04661901003040142001160703030003207041c000294140c80186501400034008441d02060003440c9400c16501034400c0034039071800a400d5030041040b00c0446020703894581c240301001c8150b21090300445404c00501c25065001801651000880d404032082c40400007070300c500f0096016883e0b00d0080c002ca014541002e060000340108002134081c444801203102c2d41c520840c0f0303101e4141303c400e9000039082018184c9602c0c010450341c0181000c020404000c2001084444d4100d135500008050074541006c1007040e030402140b0250782e860344502c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 786809397 1250 786808147 786808157
    0xb04050a060f11010203190b0a060219050a0b010b0712030e0d030e0a060c020105070f020703020d14120703031a01080f06060901031d0a260a120b1e01080c0c030f0901 73
    0x200f1010340c2802d81c0c2c812144410050782525051000c06c2d0a441007003a00e4005503107550000e410000081c2d036a090760240701418800c02105001001010090340d1a110b0f448a5014404c0d40d503114001c0e469040202c04440015003241441c1d00c86100b445401126000b02004000441c04003106078020000c8410142031402800d4210010540d00c0c0101c0d400c8040950001415140c101402003929501d00c400d80110f4001c104108090795400380c10100d03603604181c10078100d180f080002850520a0001e0045c1e00b24085070039000d054060303011800c0034003400d040500d06500c0000440d140141212550030802600c2e000c03801c181000d070064803c80c0c006040000300315034646d0099920303108518400c07045622240c1c0160401c00031880c0b490600c9444450441410307060030340700381d8901505060b17004000424860001c4190550001c41c44201d01403e010540901400c815580500c640ca01501140032607000c5040c0705020b204030750a050003180510300f482d0b480750b242c0d54a40e00031250f00e81089 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 786810647 1250 786809397 786809417
    0x30f07120206090603090606130b011d0a08160806070e06190302220504060501140d0218370b07030c0f06140f1302060d0b150d150b04050a060f 63
    0xa04d4440045025400c210b006245d5880d20000301301248a520120100060504a00b008140d8000a80d00e40c0b0713507440701031406202815004154040b515602c00c401c0c510030005103a08201c02184840d040e51000826104280d0702d0340d0083c0c40c0c0342c000b58615504540e04000500b184035400f800359201c81c5003442c015103041d0910700f41240f040302c04840c88145c0172041c60208454607051041100078642800d10038140381e009c0564682c10b001fa100b201d031045400083c80e40d10902505003941e9046d4000303280b062103440301443c4500e1000b82d0300641e6a00c0c001e40b00c819440c072030600c0c22102281c2e50303015030901c0c000580c0da0448002800c00401c82d1a0041c90f090440050030301d01400d01919140d2040e02414500302e1052256150302801480000400c180c2080150f1a0310701180c592591013100030800300c1c1c0800116801da003800c100d052644402107807448000180703400103808070000101c15644c00d51510b03205d07085c0b445988200741d840390054100300700c1d040c02190036900c08111414210144 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 786811897 1250 786810647 786810649
    0x6100e040e0304180f0509030405011d03060c070510050402060a12020f04080d020d09050d0f150e01061a030115030506120102070812010b070b011413060305010b030c030f0712020609 80
    0x143d00715401840200701c010540c0080c4840911905d0745620b8080d0050001f810301511043d100c1c4034901440d0304210300c482c1035070b007429107070800d02c010800090103c82041c54043c81000040d000300608985900a5659040c240121070240343e0145400504480c0f51150401082d0381003801c1d408840300c0f8076002c4c086407814092941c00703400288008000307000004400c100007400c051008410f8420b012018405010944481e00c944200f81d5101150346084126401d1030742c002034800c8000410182012811001c40c1d038103401070070444d0b40300c82c0e11110001c50300104c0b0382ca90009014854810600b403100c2c0401a102e40c10898000f800604040b400d1000c1020150aa034010f600030340f48284001041e03e5a4007140c47c1c00c0340101880402c07542000d80310354550b420300806200720721061035103040c6210240c0e0780f1507500c403000a0440041014035560700e44076018000429065200c0e0055400316540740c1400714214860015103c05010000c1c100425040c140c9100402070360082d00c00d119249007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 786813147 1250 786811897 786811903
    0xa17100305120703030e03040e070f03020409052503180602030a0b0a0305010203100609031211070512010516020f0703032a0501050a0b0a08030f09130c0c1a06100e040e 74
    0x2d03002c03060700010f41da074080703042c00760940b01540f580c42100c2d4000c000420120051805050f0001c14915140d02c181546910440185c0940d0704505116480c1c0300500850510305c10040c813807003c049034692141c500e055020341c01c40303284045071210802c15401200c00500a40c0c011988101001e50001d24001c0303940104034940d0300d030741048541d81e40c0042403151145581441c00e00806a902c0e041d0300e9203007550f4520300c0504ca046680c00a0002d125001c03c16440c043c0703e948041e1002411895060510f00c20b4075000e882e084c1c5025494000c0041c184045a20105050f0721800664006190292465400301c03007180c40912420002030000381b072031000515844000280c40d0040d400800c02d4280884040d0884248003c454400e80c0c80440070000c00201105075009075030501c80f0161030b003407600003088280b00f00a0f91600c040303150011a015494200c030759401500d00803203200c00034000c119a0141c1da41d009890450f44072010120050006104242a00d0182d8001c7c0c00031910b821f88450b07141c5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 786814397 1250 786813147 786813163
    0x20d081201060c051c0f052b090311030726250506060901150e03120a05030405150f060913050105010f3b070c050304060f080604020a17100305 63
    0x4009444204803c050090400440724256031400e002a10300c0444503019015a0070b401c3d9410a000020a442040001c03445001110304e00c0717101440c24410112129034002c105501080740410b0040d01c000c0c4001c3c000100303035050b241d4070210203200581c58500b201c00d200650031282000000800c11244c1c030410704489543c21000031020348414880c0d500d0101c0c10b0103801000e880c068840d00c80104448803814500c10348041090410b04101c0c004880442c0c1040e900c000034009101300042c42844190303000c0300070352007070f401041504d10309042914400c0040c0703c15a54403921408032000311f03569240a00b0003d030000451000c1410b80700c40c680d01c150039968242d000c4a00d0082c1549c0c01c20a2800c2d5400c141140200e41180e010000045c080d600c1440e1038440780c1000e4008584005800a4013601c0d490942e2034010044903242c07075450030010200306c40403403100001581840400c01078100f6009580000d616500c3d40000c84030081c03c00c00c10080300400c81e0603015445000040461000c1c84004 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 786815647 1250 786814397 786814409
    0xa031a0d1407080a0812060621092b27050f04020d0f05071227020a0806040605090d090518042f190f1401020718020316050a0507020d081201 62
    0x3501c40b9607610711b01541100c0101058040c400030854681e020b02114004001002c01c4100d4503030a441c0d00099502e00404520341c1a4103070302c02c0c0304241040c044000f48203420110341da1078200e01003a0300300042c0a00d00e13008600d00c038034000700014040c5241030100c1c450240d401a00060801304880c200400b91034142c030042a02e260341e0b00034080d40f2a803188449405c0210200c007070081030349540746100c00d1000c0415051030044c2100d44401159554003002c401894440100c80c0d4500b09400c12000510007035404c51410b100b01c0411207006405002070a0849200a103962000e400d100385c45030f0301c050000c02c102e4031580d0783c00c7d0b01e1441441c8007100400d000f200d250724008003580c01040c400d01c507424000c114101c1011f083e0820504103000074450a0310a081000c203d540380000040c0c1c03501b1881c0d04403241440c0f42074100d0146166a074090340c412001d001d42c0d0f1002c3e0404903401d50300ca101d4a685000041c904000b04405800c0c000c0b0a07030006440307640602d01e001001180e1300c19542d402e800c24 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 786816897 1250 786815647 786815663
    0x70201140705090102070e1b1e030c1b1204060810091d0c04050103020d03110111041226090103021b0114011d1012140f030a031a0d1407080a 62
    0x40410b5030704100100c06810204d650800b6070614100042308149500c0303184103589400101e289003840c0c005503500702c0084c998682612410042501042d6400240c602c0303408103800017210348807d0000078040c2c0e0112a00032224605824080110341e0080020000e403030714000803400240969441c89140840d4124a49500340d0502460780039040010040200e445141008014000350351105581280164141440c0b00035000e010401400340c8007524402c1c1c0c5500001c03400154000d00704102c0d002043c0301e90a08140d4155071803c40d400e08a4080d02191200340620502d88294060780c014800003107001c50700c03c1c41840005034075007560707038081c8100065986c16004110301d0040088042c203621241c080d90728546410012144124000e10802c0c0d41040200022028485021510a940d503840300540d80c854040310300e01640c07640031100d402c00113442d1032841c0300c1c01090800b5080c4800801050114005c406803150700781c1012040b82a6034a0141ca5030005038600200911003403e4803441039 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 786818147 1250 786816897 786816907
    0x405040519050f07080f120a090e090604061103041a06150301090b10021203070503060411030709081c02070e0603010212010609091404150f0b0d03120e01090b040b070201140705 78
    0x1405090030440e90101100b43c0c03211603000300300103007c54140c25111183d8000d030703151015150112203540d91940b280203000d840744240203141c00c0200300c0070320803802030609001102100d0201002840122400340403910301d028240030b01d001c7c94400302d81101009154882c400c1e9911911007240c0d00a034000f80c000da60b40d0030000024203101c44540c440d84450f0010b00302c1482e41d43c0400d58207220051030b9204202000001a5441d0b565504c1a000111000c0101d620303403800e04006401e0411030300032900188501d408010700c041c041c1c0d6408403507009950144c0340081c5003102d14001c03268098510342e4155002d00c403201550304074944090081866545c0d0b440c0840c50008800304441c2c085070004500b144403800c000205052001c00c5001b0307040a98002602c2241d019158014050b0714000303640400044540c505050340200802c05011070f245e810800c2401e41389881c0d00f01c44e201400282100b10403c0064041000d03c114240d00209500011640713a04808100d4290502107542001040c0c012030703 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 786819397 1250 786818147 786818173
    0x9031e090315130b07030f06140301060504060819050c060a0c0b090109030503130507050306010b09040612050c060f040503070315290f06071208010e0903030402010806040504051905 80
    0x40540149140318002615906200042d600f400b120b51101602d085080e0000c143c6452180c0d01c1000c0341c000700301c03040004903220109a0070080c41100000d200758280300000ca04c91416105060849490340e0042040b03130445070700030070822207440058400c7d000300c414001007a16610010551403950b6900d00040301e8062800036810600901000d00c0780c0e05d0302d406500000d80100803030340c10412920b030b8584c2d1a0082c2c5861440c2100301c1c1c00480d091b000300c1c00005008456600074280510301280c040c402135488051940080000369409400e40e4440242c11100d810708000a02c985226484028034158a0f200884d1404445510481c1c1d00f1140c0401039101c0200c034450003045007412600e00e0210800c108480e0320800c7ca9902c41ca1003213440c41c001043c0e60f0b442d1021102015440456903d119205400103400198240708003a04040204005002001c01004403441264143c40341039103611014107200041c000200220b43d1440f401541714142c920b031550114007107100300000e12000c07405103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 786820647 1250 786819397 786819403
    0x6050f0d030c14061008060f01031424180102070c09020a0903050115060314071e02071d0a06050a030b04032102070506061f050d0f0b15040602060f070e040509031e0903 74
    0x19012580b0b54200c00244040e659000802301d045030f411040c11600f02076005002818128172001c40c1940d9000c082c0031100070990040c2c0d840c8034614012950b00946641381c8800e0a03845040360080c005c10350300509221025041c0d0241c50015105c1c034040e24604d0301d81d46c1d03017421140e480c14020070183d80100d081084030387c103010f17030b103201b03c541c0092072200d00380440c002c1d000800804840c04043c07050b04030140410300c208034800017800e060b40b501d270038944040001d23503000f0400e40e110000c05041c01004500e60500c107500c441200d5000c105120701e540c95890845940c42a0301310040c0300101082c0b024018030090015080c2c480c011350160a80b42880010010408100b40410000d0510300341c56038001a009000d03500350007030312200410308035040800070009200800c507296001607405540c4400b040582c0103042a030fa85034085440640712003c0329a44000101e841c0350010b520410440814142a08541c1c1c0114550080381c0c1810000a4450134200c002c4000400d80080801c001146d8a410 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 786821897 1250 786820647 786820649
    0x2070506060d110f01030e010603141e07061445030318180f044b0b0c0909060a15110c0303040e0f070306050f0d030c140610 55
    0x8070b4a50140c1180da6945000e103402e40003603180f05032950041078000740d000703400405c448040403008226140d120304e0240c058040c22461783d02e1038402d05000031144e41034205034141e1640548001c00880f03140503011600b0640c600c0803c1c0c00e0390010f0100e15900701c0311100c078030b078410700a003181019200c00d220401000340700401c500003e200c5e001101034051b1400b0048400c5420682400c2d001000080041803400c500c201000350303151500c0040106644400602c07501031031041590030354020268401080003507a0f43c1050b6412100c520b00140c01d03412548101070001210708401c0c0381070f102621000c10002c801c85000c2c1081c140001c0410180c50225499a480039040752006c0c3c296003880c0421500f010140d405005100420b00c0c038070765026040000f5010302c4802812039640b2502c8504244e080901a03542071304050096002c1480103002e80589000d5820150901c00c5035041e031400c00100788040c0c40150140100c076014000803e00080e01c00ca000032440c0020702190400c500707030a18a6510f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 786823147 1250 786821897 786821899
    0x3021314091507030b0103060e07080106021002131202030a060e0705030c0411032d150a050f15031504050a02041a071e0303110705010504020a05010f0221070c08010207050606 77
    0x41080861400042c980d207083d00440315240004600f103c020040e0000c00c400e030400c001c44014003040000043d404501c1c0f038184c500a03426207903004034980c8100d00380c1c01346580c403c8a03400501000c1c01609915007440c0d1071180014201c440316145a2a2070301141c1640704005c07400d401036181880790782010000c10045e03200a80c1d00300100e8903006496a46408090500458040030f4100c1c60750350010903569014131040b46030615154203100d107103000e521001c1640c0d039000f81e010010020303103480d01e01e55808000d103001d030a900012502c901148502d900080c0b95043c00c0411240d43c8945440c1c610030780c1d11030030301c1d0040103a070745003400d6207e0070340c0210450401c12074404000750720001780389280c04034101040c1c138803c1d02c0594181c9005e4011f03080807a820700c85101c01084000520405400031800380340242e58400040c2d031641c0c01100c00e01e4a204041c00542d005040e00c490200d60034078145a2030680030b091500707080d60740d59061055005030b88201e01603900814098140b04040c0301d0b40d40c1040b8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 786824397 1250 786823147 786823153
    0x90b0105060f090f0d080307021531031107080604051204060504090b0a030204020d150801061401050c010b2707081501050a1701080703060608010c080402190302131409 74
    0x3549942420031480380f10901d0b0300507055044540080d844104d0040883d56009140d640c80e880c01e050000d542c0d002c15110741003880075000118000e4051030b140c200300125088803002000450480d107259806540400b1000c0084141c02ca113004001404008041d00c0c54101816241c10705082c075a2800c0310140c00451140401c002c1044040d81040458040f100d0b10400450041c07000000140c1014050780040c0d0003600006540320045959400344504154445500384082c2d01c07598a5402c85a0901481350150400002c0050660282001c0c0091121050000c5400304400001c2030020412415001100601003840b0a01040c4540081c0c1d000f0040d10340202d040c0b030003443d00c0c002d0001000c101414404002684000f00340305d1204620342c00aa9200030481c5c1d65201461a5201007074402511000c0c500480031500c5041030142e05103000d2540e1b0b030142941c0f11034081000300700074030074104041d10aa80c00000143c46110b00f0015244880d240040c084004241040f544a0001c0003244650 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 786825647 1250 786824397 786824407
    0x20706022407120905010f0b031903210f09060212070c0b01030201030515031209010e04090b011e091107060501080a031709100603050102070515100e06061b01090b010506 75
    0x841d0001c10680c48640c81c5850140c044111810000800e140080506254201011180078038400d802078540603809801304d40d11184502c0150265911619006000070b04901050170f036802680a009029031744504009130305012844d024045840b00d00c01201c40c1138000c05c43d0320759404413428080e8030078107500f058009650155150021900e05003c0241410f503036038085000046005036074018010054216100d2801d070030356552040d00a0207485001400740c0310034402c2800c05010340310300154840e502d110141d007400c6272040104d181ca01c1c0c1c0044020800c0780082c070038486000b031281120010101a07a1094941404800e80300d0580003403070542c2c054140d480c0001d41c0000500c00752201c0307a810003095102d80408505103000b0603007009110381015404402c2c4241075009221992042080329501028000b400103030300f504807001403040010200c100180d12036201c40c0c5500a4005010ba89001c048450180d18041410f080001a0b035403100c585003004544081c080c007421007251030f60300340 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 786826897 1250 786825647 786825703
    0x24110604080a030c0552110f0312070507050402091008150a080319020606100c080f0d140612100e071a03090c060a09090c120c02070602 60
    0x602c1641084010140e441958094941c03042d019605017810001080380c1c1d55010994841003240100d800aa0340d01c40d03d28080013030b4440c030700540401d08005403c6a03039000f840d203894007140c0889051a8101c840241080803940e0244021485000c41341229a110242403d0181c40d0191b66008240161300c1040311443c0303941e680700c0391a52a0650314040e112a42c1d641944103958503a80c015a40022103500d0100d2000c0011018103c11200d8164802c1008103040080740e841d001502c4494100d0409488080c0341482960418100d5000720111031514801003e00e04c15a400f1850f40100140d88100038044584021401d541041044400400c00d4511210f415200c07400107900400a940e24140010704000506c658401400d0700131800111540121920032140e02c1116000c600340240c2c0104c0c0828a04480ae03105410880d550760400702d0f081400c41360082503005015410301442c0458001401c1d524040c2409100482d8003910040f89400406071824501c0d82041202c40c29220040b181c03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 786828147 1250 786826897 786826913
    0x60b03010509090a02060c0312130f02060a11030f0901030c090509130201020c130212070507170306130e030c070f0b2a010e06150102030c12031024110604 68
    0x1590030444a882c0c4648400300102c0c0b4000b6030b2400290880313004244886609004005044801504d840903201c42d43c90800c40695240d82e403c009000c000c4002c0c81101600304140134294030006824010107000c00e500c40640740d034020404039910014006140c480650381405180089403090074199242e03405c007000142d43d118020840f160308500c407c0507505680c0b08000880034a54050010700020b0b030000748000181d840a601280028482d902082040e0f210b4802c5032041a08000030b00b0062014014001d8141e201606903503100c440c40c4140710310f62240e07100d1031914000030070045603111412080c050600f42250b1004502e5052a14108a00e8817924211400f4058140d9000c003c1342408240c005103850000031a13115628007583d9851035040050443d00580c207800c11804000d4240004994903c90b00d4002c1d105038000d65000100d0b00900c40142da00140449640c04e8501d03210441e0100d640c03543c2c200100c0b080344441250950303a402100c0215402c441070b0150400e803520f500c4400c1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 786829397 1250 786828147 786828149
    0x801020a0e040c050f0f0d050906130f031e080108072304150b0f070302070e040f03030504030e100306051f02150a060f060c02040e032b0e0105070801080f01060b0301 73
    0xc0141d03250143c0c0600a0301c2542140e10016042c031a69440d0841d100f483c04440d04002900450300b490034010401c500c1000444510500329000310481e260515a41e001c04031041c0002101404402d00e003c030a05241c0d0302181111381110380d1120302c03640c98110100c0c43c1a60740d0344001e004084802a20203002c0703002c81c0171086541d00751004200103030311030320402c1043c0f4160b000440c10349021808040c2031144500501546021340d00311b900c0282c07500d45005111000766802440c01c86080d508000183c06500865801070003420129240b40181003c9682c0c901c507404048002a50307148184091301d00003198a0010806100041c0e00400c03002e0065650702c20708200c202c0d0310581c074000a0031229241c0151000d4920341c41900d6842d07654000c040c00b0600061000c80c440c604020181400c3c4000206a44440b0600b070301403050050418800c20700c101700c0b10300801c00e1503201e610480e10340209024403400b6001d166250005585443c10303513070400030424011000d99061401c20444114500700b03880c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 786830647 1250 786829397 786829399
    0x70b070b0f180d140417030d0c0f08040f030c0209130302190201051c0b061803190b060f040b031e07060201050f3103200f0601030605060a032004060801020a0e 70
    0x3134000e56070100c481034501455103d90030b000540e00100107000d4011001d80342c4180043d01c01d101c00c1c0d540d4030094490800601111001031044c0c000a004503c400640c00151130090030a0036071302c1806d401148c80040d00301c9030b020f42e0480f86601c420030140e04003e00c040080445002040f040c119070b000901c0c0b07124060800c05041d20540b1868050302450380104c00c4d1410003844035546590060000c20480404051148240100110a010340c03414810301e0502aa004038451066035034181007040c0ba0403555100d83c0c11503515030440045880070444410700c4940c4081000c0031507400c05543d490b01069030030650441e4100020b1110b90150f1081740c64004159401d0765208490f4041861280f558000c201c00780080c1042c204014560010030010380c00c40c00701030041d00943c208640301e50320003056000400b141d2110004201244040e401907820420003407402c60003e46e60340300c1560701c0324014444251182c0c04d501c0c0e0002480c10348204c1e8014518600290300300481c0c0c1c20003606482c2d04011003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 786831897 1250 786830647 786830657
    0x31205031f03030306031202011b12060b030405070f0614090f130c080601080108010e150406060807062604020d0b040305041a03160302030906010b0c070b070b0f180d 73
    0xc07900081c00000d1900c0040301031104400da142e80d900340180542450b120690314030004d000c1c0e42580030310600446950302c9900840c0d083d102c91002c0c00b101c800707000402c2daa1495a5480002c24000c3c42200194011406a002040351504006001c00d0b2000300e50302c42400d0100d900400c1d92600041c906032503020703500311001421861510080340303803181c01080c0105039034038144c03c0c01c40c940d0700665847c0c06142c00fa6504515a83c840a0032400c95103006916040c41c2d1002d013240c1240b01110b0f13201035201d485030502080143d0340341c00c10762401e04280c20400104030440410784150081c9440c000503402c000c4020030603410603030042454118000307000b400f00030703162000405250280044400404848008001c1c0f048610010800b540003503500820801d50741c10650840b40c030900940f07000b0104500901383c140d10380240300700795502a4641c0f580c98011001c0014207403545202038500e10340a010807403814600143e0076940c1c40c00c02400148801040d141d60003c0c0e403400120600c0b220b01c40d0900c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 786833147 1250 786831897 786831901
    0xd02100e0c01170a0b0904061517031206040e0f0307030806010e1507021908070303020f0d050307110a12080402120d02070506090d020a061110050114010e1c0311070b0403120503 78
    0x448020709140917050b80c1090468051104102207584544070803884c400b4507010036621070f0b10009041c0d180784140c580b0b0b80e00c244236081e4951071074450030b50000e02c014000510f200103600d080e0b0405a00c218112400c1d000440d0394020305070080c80982c0c0c011024a05044c01c01780d45400100b44a0141c4900c03610743c0c0c4003144000071500d802ea1030504030308240043c442c41070794a14640c1d54442c6107010031401402403480c88461120001075079001c084591b00da00c0d046507180c10f8200c92001c0b40b81548005c5103c1d6846800100d0001006000405550b5030380c070b95945818014400c41c640062055071640c0c0c404e0014a041d140d0118021007595000c03104603035140101c00c00070303c0182e06804080d41c80f0307440b804001045c0303801001f14079920309100c041d20503510400c500602181c0c0244205d54015403a5040b410140d0f1040780010f02103000142011280030031a0700b0004110b0260300203d021440700794403010306e01c03010411400141300c0406d41610b01821030365482e0768800340d0f241d0784080c8103000c40 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 786834397 1250 786833147 786833161
    0x9021c09060f110a02010606050f0909040201120504110906031b010e010507140a1b030309060c150510050f060c1002030c041518091b0807110d02100e0c0117 69
    0x180c42500180042803000e810007044400f00c41e0302c5003001d080590728040000405038042d00c20307121005c00c003a04450034a00414180b08000030b004004038108103610104001210390b6201b443c1c0151300904400d4036046540e01449842d42000d0031480c0b0960161003054500000b1207034801000c40280b8100c844640034a0040c2e4076800f44030802445c407409071080c0010b40c0c00011701e00700c00c9030181a41800c1000d40c2c1c2441e80c42d40c086400040c0c00180b21680600c8510f008a02e03804041e44520004403803100c07402c4d44072040b988259042000303083d444004001a14040100c0500c0306003c40b001071074602d00250965440d180d00004071140d03900400041c01c2c0446900543d4020583c40ca641d2f00803403170703180c001000160740c04070f070551504045001249401040c0319001707c0603090302c000205410260300948003010020002c2003000b00651403507001942c140504039000c51190000c01c00500c03406111000c3d14081d0031031014a5100c810761134002da070307c0b5a110030071500d1010b035240581c403099 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 786835647 1250 786834397 786834401
    0xf16031d0f0918010b1002030309070501030e070b0f0d05010e060111061012060b030a03091802130902090f0415051f020601060f110303040b1f082a0901150909021c0906 74
    0x402d50307485044901b60f100c200f50080001c41c41040e0100c151034010703450b1001035040b0741044a0101d05036000c1c040500803100c5480050000782c101c01d850a0510400e0b1807640103440090300035500581c00203080c0180355030040700c0342c0782600c6190050312071071a142504465521442c0700c1c01c0041d0004124010611285500443c01213102505640c145001c42c280a45030300064030400c0051000c01c1c40c84100c80c90b00d40f00b80c40748032051a0142441c2803802c40002c01035000b00380c1c055484400801e5129945e601c030b100d020750341041d040d913a080d200d14010420204644803042d124585880310b9a00d090194003080042c191225403c21030680c0c104120200c48000d8584244101480300100348414400c1c0721000c1c520a00c5001c40c5019040006c241000d44c074075840c85044542d9008080d41c002c4081414082845038a2440410480300702a000040f14810280e21448003984e1000c0c16400441c0c2c81a80003015242109041d03150a0405041c804035202c90a0f0460300d966586a9402c01c100540d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 786836897 1250 786835647 786835661
    0x308160201031d2508060703062405071101120903080114030304152106090207022b2d1515140d0606090c030c1115010306020f16031d0f091801 63
    0xd001101c3c16480c0246024004001e44e010702040e50501c16001082c4082b80300c681c0041c112180d880344d0616101d641c828500800c6c0401e81d5051101c003104d07044152541d88211590343d40a50ba51069a51409040300880e8940034105030113038100708024003852025440c980035034000c52400315035503902000c1c9001a0860501d1b0f10780c455040046c00508800c164010300503080c02252210700d07003154800c142803241da250000d010315072404980e81003c00d00045203a03100046c00c2e081c120a241c2d400c03031010480c001a2800f143d107400c007880440380d4000c0c0c4d880303000341982800300701d401c0c468200800b64030381d010740e484614495418103500b0010003940341c00c542c00a00c5041001d020310031510f2009005080200c03d1000011282030988091442c00204000d18034416035101c0d10036429912140c010b50b2003080e884d1642c000030818103642c078051030324103502c2d030707000782d0700c1c03142515800200104600002c22024450520780da52400c090341d80403840d41d044803a1001540f404041031503414054580 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 786838147 1250 786836897 786836909
    0x50a0f0f0803040b060a0605070b06100917061008010c0c0b060609092a091005180a0b12130b0708090a080c160506032505040308160201031d25 63
    0x1002c0103100801c080240c055009030411921b00c0c69550315a1000c403413902594002400244000d0b01091b658100841000d400c01c54510f4164413142c0c48900721901050900400c581d0b6a014504020325465a0145076000c0c00001d0024401c03c0d140302002030038441c8014001e0454111200415116030315002119001c5074094500240d80c5060020008210301512203101e20f014244860200c105220b0304035148004024410403000f601000c0031249a0000d440300114035600c500f4240c525610701e0441c0700242042d205180c0d071441e8801c400802810040c105086400c812841880002c00610b4119440401450f1481340c41d618032000a00c0d01c1c90142c00503101d50400283ca080c414004118400000700c800041807105540d80144040c0d8407044030b481c94061aa1000c4203150807100207190703082d1141d0300d00079017440d481c1c0c0c441c10300581c000207850740c002e030940e81e00d5403c550700b5004a40301e040d40c90300390560b800617100149490b074516400060000e1169a0588040b11145011360050300c5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 786839397 1250 786838147 786838163
    0x111040605120c07061109030c10210f0f05060a0f080d0e03031c0213120209010306150b03010605040509010e0421170a06210503040b1c021909060c050a0f0f 69
    0x600300c0d02e682503400040d441c0e02a01400c5001b80c00b902b0705035400c41c1c05c14402e54450044c542203110070500200c58045030031105440c2d42510001a0380c50290003061440b10b500002e280c2001c000700705030440d10380e0001103802c5a02d00100300c50715000c02d42c04144007440c00e180f6190f0620b00c00090461051052000c241100b4000e41803440701c0d10740c09000032400246d11100300c01d494104040700065407a02c000e600c0b00300e038001400028095007100442c44c061034a00b0001c1c07601d54180300c4143d00301340c11401c0040c9011500300100d16298541d20f0040800548000642c141515404148061401c0f05d441090050b122560014410100e0411080094030000c542d810302d0314000307018101511401200d42c0c2c035030300e00040b41200b0000e248203030b82e0300000841c6031501e040e2084500ba0008c1c409031001041040144103180413a00041c06400009001d00f010051f010401828001e0f4a402003c00c01075040d00e288006500020441c08442c1c202482481076400c5107014501401c1d002c400400d449 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 786840647 1250 786839397 786839411
    0x70c060906150920041a04051017070f050702013009020f030706021c09050a060203031f120b04081608030103051005060603010302190305030c0d020111040605120c0706 74
    0x41c0400e1110800c2c0d6001d0700041c03000318607054000c803440384e042075a000c14810411003002071100b50305c1985900c1c5038040100f820542e80f9170016051040c45503454000c111000e9446092009080140f176200d44a414404441070303107880300078598003072502c000741440109085c003080400c01c0511003924080c14003003000000728503028007014204270141240250140d06480040e8580410f51000340c440d0356004151352040401031009542c00040800700340462f1180c0402c882d2a03c543d590040d02042d0000c42e607038104030300442200c040e80404030a140b840d0765000d1001d144510031200c07440f508419001486e4a035424164050b2054004100d010212171314020304010807200654122401030060300c0c0c500c04040c0f26201541c008413842c075800041000107100504c0c244c2000300540303102034030501c0b14a032070380d40e05842d590220034140110391000c2c154420244e0b09000d0100c2898044440e1420107190110140040c00b41130b00080318201c440b070000d02c40000d4441035520164005d0810b0082c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 786841897 1250 786840647 786840671
    0x150c0606120204200f030a0209030a20040c020c0625050a0201120903120507020a05011104050a0609052b05030d090c0e061003050c07080d05060102061e070c060906 72
    0x1072650401d0890040303080c0501d840305004480c030800805404401450700d410501d44c540c0085a1008054091032a0300340207511094604001240c8414412400305d070080503100e40c540c00e0300055150081c8a1400c1c06443d144180c1c2c08220b0000042042d100d1640311840001402d0340105241025085403892001c000b043c00740004100e115203000381c03079046c3c4040c28012140b0903101c4100024004c0748103846242290441c1c0da01c969444001c91040da00e81204a42c1d82c1400e60700e0751281036010420109041c09580b50415251008100d242801c0e00710f0380c5000003003208482c40c00034551400a10b814944950b0798503012040809500c02c0c00c3d02d55481d030301c0b004240103041602c402c0d503208012110120300c58141d442020300070740004000040e240e045040440151400400c01000b403c001d010081c0001c2c03922001c1c090014543c3d0000c14540351640009141407001072400006111704100c07661038041c4000903a40100040c03030111040c200e60704100c0080d11248400800051400c0780c3d800003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 786843147 1250 786841897 786841919
    0x20301110310080601151412040308160207033906031a0a030f14010f0e1b0d0305040e041b06021f0c1403060a030203012c010204060801150c0606 64
    0x415010035801a202c0c80d240c0641690b500d10901a0000e1140c040c4102c08200f806100c10058101c0c0700c214440c6441c80d20343c100c6920500640341217020409038028058003d07000402c611203040d403031000700842491620355000a130011004022860440980418240d042126074250441a42da010b08802c2e40d8090040c01854400d04610204154a82481e450316201d0f141404803a0040000c035651b650703d880d8100d8645c0e00d82c40e50f12440d03684a40c4480400d18500407000c213100b544010741058008181e15400d064404140c072842840b01004160000350000c0a03102a83c1030000242100d55031440e159920112800c0704610315400d46000003646c9900061a44244101c404070034000c05482c80c81800341c8483c0d00c8403034042000740508100c140c40100c042d50380010021700f120041d07a80c0b03401103400c64501b41401c3c488505a865514a140c2641d00302007000d038041b070000c5207494a054070081c1085018055480810348402084d140244070b490345811494019208001940c0d50721801c0319 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 786844397 1250 786843147 786843151
    0x30c0f03030a0c0206060a090507020106211137030803042d02060d0c0201020f040b190801050d200441010501210501140f040b0109210203011103 64
    0x584604014030f00c0f40040c40440c0d0a405440081d044212141c20300c11102e000d0b0030020b001c0b104540d81c60707800140121405100301e0090400e901055003008071030410180c44428501c903039010314dc0c9540088428043d0355003480c513840d90307001c030700d0031109205040044041e4551f00241041c0008820b01080c441d40304402c00c0c4a02208000a08034200c4000d600d04000301c0307500c040e50007042809086c868003915005022003040c144001071400342c0e1041c000000760010f4022092404e004210849040d0309a904121007280c0703420300721400d40c50540000c601c6c50b00c08100510403929250a2031015400c10340e0101c03e90b80042040c010008221909242c100c40c40a00d6140d08100c01c2040d00c0c0d21f40e81c1150058040034541c428401a03003480300554a2042214a50451480e00c810440000c0c14034400d02d8043c00044800c0c041d4441030108105015402042d1148076615102e10b4000a82c1c100404800310340300140d041e0b82968501210241400050384042e4255081c40c2c00070002c00c3d02c5000541c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 786845647 1250 786844397 786844411
    0x60302040f08010c0c02010503090c06030c180904210c060905060a1811040c0203041d100b09090a0b040f02160b09010501030b130227150108160c05030c0f0303 70
    0x408480e0307220042c40c20381d62035031540000319080030141c4015522403402580e01c84004400c55410030200c00c04100c90340d20031102c10f0aa8100442c1c400d84d61030f0880c1d0301c040b18003000c030343e80140c50903e902e64585402644040594508081c0403903586ca500549452810365000403040000c032403282059503c560301222010072f0f0311710b050b00b141100c1d08940c03030041d41e81ea08200268605d196607024840102090000081548010f0200091072074a0f070381c01c0500340f00000310480300c038102503200c0c04422505420191b58550107209156041e2110029168000d21a00b03020038000050f10104009103202460254810b000161074620440d500ba1079401d49446116058641c1c0e440700d01860880750280030051074880ea85c400319a03071101c81a0101c0306c59000420310100d8502c60b907150f030010703200c4001d880401105403041100140000740c12103641e034800c0c240038240f880c00c0b2100f04003080640302c2c540c0c28840c41c1d61000050203010820795040c103007070318121242c14600358040c1c0d0350383c1c0084405d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 786846897 1250 786845647 786845669
    0xe0402210906100b03090c06190e030316120e030d020304050906040b0d0f110603041a090d050a1209050102070503030613060302010e0d0305091503061003021612020703060606030204 80
    0x10807040703980050a0780c0b10321056092200c6060401c90307841416403010380940c91074812000840855582c01005205020b11004507803108030302650050180480806580d109400c184031030024061400f1001d01c4580d8007440012000740603410a584402092140c5601807183c05d02021a4035000802441920000ca448a019564540410055400c40c08581d27821048d09121400000c280c40640d241c0a489100d07151640ba005c8004104d10340c00850b019603012045c62121208a00c80c1c442440c0c1054142c00070780000001480c001e4104d00ca01844041044002045614076a0580e4002075030254060020740d0f450511b410901e689805c03d85e10a441042d040c8007070b0000074001d00ca244212030781a1507018548020310304012000440d440b0540501c1300030006440244e6510f04002d1a083e03110410303941b02e04004041c85415400705098038249032040190f000240195400c0d10701c036079444131030b13147d503079072140ca08908002d03a95000030a407d040c1400810030b1a00f64000c0c0040e140011a5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 786848147 1250 786846897 786846901
    0x9030f150702010e0c1309020315130605130506070f09050409110406050a0e01060c030903080d060812071e0219140103180f1401061505030a1410060c030e040221 71
    0x846403500051110340386d0001d16080e00340e01004094011681c11030008095800645502c440485503510888600140d01e42007a0418200020b5216060700f003010980141c030254860b9603140d07585c0b00040c140300b091000c12151012030320301c1011000c0150034040c00609c4043c2c454039004170f00c0002000b0852180b07042040202d400d00784841d003641110103101a01c0c000341d1a00000341c4108902c210154100440d4401c08004609000c00400c000d09011400140b07951400c4a0310b07052203540c030f0b03210b030400b4000c002c001d002c1030700010711065400c800500b5007244070362440042c00c064000424911209100500001c81030303803003881c2c00150413003a01c3c10302130000022900f05031200ca40b500100f06605000b000e02c041541c0b001741c0c0081c400b4010000070007a0b140c030305500302960018050400160000b0410080b00c1290291035031541041c5840516428024611503825109001e41c1040008400046080c10b02c034400c020158680940119604ca212413000240001c007460302c09042060140 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 786849397 1250 786848147 786848171
    0xe0f030d02072109090506010507080403050606040c08010b040b03090c0306010314060901021c0911040e0a060b100206160207090507051b0d020303182503170f070809030f15070201 79
    0x1d0401c020040507550446850b0070301740d5560081c1006011701d410040240880c1c000501603500610185008900a0540f890301c80108401d40b14110b4081081000135001006100000c00603142501d913001241c0f512643d84403400da25040307645180d603901d0312821000005000900c030300041c1d01010a0300f40c840a035540c00c00c9074281e12038440e41c03203030102c0c2c0035030040c05003241030b03104030b42c1ca0f41b00d00d0030740d445a180c5200180c00c1c1c41424400038029007022408008001039031140241c880400e03903107482d0138620220003a444010040041d4100c25100383c0c8545054401d1003028090310f039007502000300e0706080900138420780001410503014041112051070b8050000340721240303260f00360b004600c1c558543d1272020525140c4498840316114500c2e040b0511044596500c400420fa114062042ca10b0741c01d001c001d40e0181c441849511070104205a003041f00c0350100d402c59030300f042150380d8030407000010038541024204104c805004081380540d00c49010903034540030314400e600901011140607 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 786850647 1250 786849397 786849443
    0x5030f030a0207140f0d1506050d0f06110c07060801090c03020304050703020f120129060f0d18061418010b0f2806050903070f050904060e0f030d0207 66
    0x5092200940c0c8004400c02580c2d0a00e44c014002080103440c440740000b0304008580f500c00d140d6821a00c3c1c8000a000d40c5041d00c6510030076000b0708044480c20081310a81c2c13203080268900c884040c01407600c030902d0328501016401100d814540c00011981c1d100d560b0f04009007981028041c02e0074242c02e050744019494480e000b42c07405550840083e055443c0f840d07007002212100c1104041c0c10144002c03215070401000e00c42c0006142e07000d8000c110304409031660401c59001800c0d014030070803007400362a010406200a84042c0e10980b02c0004203120081d071071036007801d6840c00051046050031140004000005d45841c054401d0301c10b848002491006914243c801343c018003604403030320341d4003082145012a08203d01081d10f001032640140d40c5003420082c0304254102d1800700d1800101384209040811281004003041c6e62048107640c144030005d400d00c0030103440070301450b4451a0403003251200b070148401003151001100c1d031303500208a40c400a5088840165480030081800705501d090034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 786851897 1250 786850647 786850657
    0x31608010b0d090212010e0616080910090c03020d05151b09040b0a09090516090c1d0307080d17060616140a0c0b071506061407110405040c05030f03 65
    0x4003801c1e41850300c0710b09144010030382598140d902c0f404640b00914031480a11542c0c554009100c094101407901d500c6043e80030070700c00b64440800030303001c0c204900e085c00403400d10403420852501140c51012418018007151041d04080d601001036001641007210001c0c0c0903104c0e41141d0a000d406076906410381402680700340c8079006005081110a940e8030300755101406034000101146045e80d240e01c8410704174cd0f60907004540b9580902100000d01c04440da1640042100c81018415000d40c50401809603042d649022140c002d201003901c6155410b000300801340800000b2145188c4191200030f043c01c1422001e07000180e0003002040043c2040821500340113000020403c444040d60b032a0070b002c9509007140192402003200340c80029800c005950001c001003c03085840303045508140c1884c4460901c80c11526240410420003070740c00440c00304918405888580c0c8403560f50902a00036081d505007694014580b00421041200c0802d44006940083d003c80c0e0020701d00035185a603d01c11 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 786853147 1250 786851897 786851909
    0xe01140307030216120822020a0b0a0c14030d0f11070f05070b04060e010f02010c02121308060103060f0b03030f040902031803030928081206220203160801 68
    0x10000500d049001c0d030002c0c030713095200143d113080e055100e07210303222220040b0a0a1000071058018088030010326505040c80044c40690b0304401c00d05030380003800ca65581c0c071414a00f41c0300810419200f0340103071503c0d404180c00070715501072444100b181c140c50358441500705641d2413419050ae0800d10180c0b1030303001e8892a40040c145403000945a030340c11652071103002c907440c0c8110040489c5410805020b070008008988a60301d0718000b5030005000c44505201020840e0f242540c00310041303500081800308100c0d4680c3d03140e961030b64003110070143d500a07000700b18188180000001003081c40d41c01a4040c0e46002020132291101004064803403140c00d0090588100611061061340c1443c0e00075074012440d502c41035a56104580b4103800c54004840e00140c68000002d000303031410911440200001d481d0442e510100c201c0d80e2070a40718082c09042c15003803002e0b080050099102c041200c0e08050425110019084c401011030740a580126000c421101c0c02c1550203c1c0c0a0040c1071003070580340 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 786854397 1250 786853147 786853187
    0x10e010b0a1b06060f0b040302180712050414011d12120c0a210e06070503310b130318031203020c010b0402030118060b07020607020907050d020d0203070e01 69
    0x40501c144100b81c4034441058421a43d0f8100000d0200c610b4043c1d180103041103c000307a15a80fa41c01000030300c88661b800090085085420001d046a12107506080103003802400030fa039480f641084044071501a42000c255881c203000320450f02d04282c030a185000d0043c00b02c0344040c608140c00d1186008529403d42900e48030004103901003d20405040011402e16080000d0f12415031540442d505904420070501d54400c1e054400386000d10049501070300a003401d501d5418041605080443d001c00c00180541140254a180044400b1720000f620380240b070036621410410421407441000640483c0070406120689513800b16614204003140c0e00000b0403000b00c448048241c004c1d5100340c210786825569164840810355461002d14041d02d10507070105942c2c030a403208902141e000d40c0001242d12002d002c8600140d030f500c41103400c0c1d180e0603203d07076401e6112550181d405004001c2c20070125030011460002c096015030145100710510740e1054070200c400c0005440e800390f07148216a043d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 786855647 1250 786854397 786854417
    0x3120711011112190506010806060d091403120a0c0801120302030c0d020318010c0b011707091e1d070b030619080105042901050d060e010f05010e010b0a 67
    0x14011101590540c260400214540e0708020b0200450752000495210343c0032110113010201d00001c0c1800c180d9082d0000800143c10030500103841c1040043c402e5100d400000307240300c80945c0030380010807482e900482d00d0b211807107208a05616a08011700700314144851710001000d030740d114081e40e1038101f100e80300d119030f03a420501d4820519001324400d4080d03120820180100d035408200d091708074800d59014544a9841e0b601c000307203006401b4184c50400c01c140e0203000204802c2414241100d03406040c2800444000d2010307810100070350320000075640382801910002c0e07042d9402142a00300400c0401c408841ca40398a8041d54540d40b50100a0303011140c180303c0921584002c640040740104584801c120000c003d00048131603030050300a5035103038014402004298888006008100c2d20914469258540d0a0051a20502c5020300c10104c0c03103501000d101e540c3c0e1004c0e884e119101c1c000e200300c524194501300504428840c1041130784550000103081d501c107400303448a189484d60303490249 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 786856897 1250 786855647 786855661
    0xf0b150a08101508040506070e0102030d020d0b1503011406040e070c03020708031c110a020a030e010c08040306090515190b060c030301030b01060306060c02151605010c020a140312 79
    0x1000380100b400c5800896010041104a0328610500c40041c81d0350701c0f0101894180760490801c2409042d103024082d0340c40140d00243c0e004411303240007555400c0c0041c2c60744050503101000d8005881040d4004a80b0754502e4000e514100046040ea8501c0c458003181c010110140400c3d480380b84512a500c0c0f8220000c14540342c400e101190b05940248116103006840d0032680b4110381c40140c10900303030001c4010312098400c207802800080030180500c24180a28141e000e5143c00d4840801010040b010110800b2a809070000d842480d800008880c3c44070781b689031a1004241c40c42c0d06403424841c01c1c0a82018056280403d88101c8501040750802040c8401020180264020403603100c48140001190040100b001d103009500442503c13445500d089400340484025401140410064003d08800f41c0c4448541002400d0f0045503e40c1c2e602c54980d644a24184a8400424070350800900c201d070076600003043c92425010f15a51490415612001da0b607900c2151507030000354003044000707981 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 786858147 1250 786856897 786856907
    0x601031e170c0a02031009060509070605091002210d05062407060207061104053c060d1d070e16030507020f070801064b0f090f0b150a 59
    0x340c0008a0403100c8035800c55000901b0f1490340101c1d942102e5817008014203200d00b5025180d0000e103400c001d420000d080035802009842000c0c0c0301401840311626400d0418803c002c84801380c02100c01c051038650380e82c1020f00c010750102d0140140070b0304040100c0e20131715028562000c184500c07000520100b600501403c400d4104890984400c0c1c3d081c0440c1001c01d01034090801d0070341488000380d0f074840c1041c042202c1e041600d0a6643e0f072050b0312802580002084003411403200c00c5107600c1e441144c010707000420a100701001c0c05d25040c02d0003a00100030030492081903100039968283c481039502c0f0912103d104e902190810b84003d80c148600c0e020f60b000b503000719008116481551071003444412100e2514800c0e900c1002180c3d07403a5410020f01c8005124011946200a4125140d0324001081d603400b25080c04405031264030682001401800380e0240c000505070144120041d603982d00411008040c1c43c1c030003d5601d4145070010081e864040466045008824415418120504400c40f2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 786859397 1250 786858147 786858157
    0xc040c1805120703170c0d02120d051816060306061d060a03060509010f06020607030e030304120908011406031207210311070f02030c04180f060615020601031e17 71
    0x5141c00340c3d203400f00c0881ca051004c1c285006508005580d50380d50502202c0c6818a80d00d030010464200704034070b80400040c003003142c115010740c80c800300e11510387c1c48500341d400040c02c0254415206a824004a0030b005603d801c044680544080100a94590040e655032202440d21940c0c00d2040c40080c1c801e01d00702000d00b040d146070b450b0000d41181c66a0202c1c0140c103003a00701e0040d01082c00740810034690304202c1c5030341c001000c1c81d050025050316400a9901c0c04060801841024040c14000290384100e0503038006185900091140c840e0003c07071946607801c10760312940680904082d507030a8000030400c40e40c17070543c40b06003c0340768281c440b0004510080a002c8100b0162200c0d00301c00b803030041c039000c1c0140b00d001e80d031010b07049a0240b04040c6420f00c0c02e12854040e60621498144186141440c510b8aa40144c494620b4040500c1e04c0341c020030440d04030b58a01806001d6070741050780d0026203607050301d128951400c1264042c1700c0704004460442c4c0002c00f500c0d40c00c4140f00c0303210401c2c00034103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 786860647 1250 786859397 786859429
    0x50f010503030f1c0204080a05210301140102010908030a0605030c1f200106090e0c0111030315010512250507110f01120515131103040605070c0b0403020c040c1805 72
    0x2903138107000c03550104140da00546c00300707001e40c0c1f11420500070f01805124224042c10304244240520501d1761820300035000505c102040302c0c031a211520f0b81a4000e40040032215403140b9403036580c0c904804210002c005038002c0e00d00900c03a00f410000d060501c00d50f80030014020f004d80b80003c81e85070204450048041420328100034000281001c1a0424024140a0b0190400101388040c041c04402d241900c0450580d0400c02c0180744d10300401e0011080380e420211804807004001c0c0076000680f803600c146000280140100410807081c0e941d00454909850f00107019004000b042000484072405400d2002e00f0320800c1c4000003001f807800c800070034100e5206050914842c0d403070400d00c10803a0303003c83c0c0a154901402d5014203c62424203002d42d2a04400481044621030189002c030850000070700c02000e142d42c0f00080f0310f07414000c4000b04a141d42c448035101a51805207002515881c0008034203019500f415050b8201d40e00620440c41803498010701200fa1034039140c00c1040140a0059030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 786861897 1250 786860647 786860677
    0xa09020102070312080a0e1906111303060c0e060a0f2f0106081204210201110d030c0329090406020c030c010e070902070b0a091b080a0204050f010503030f 68
    0x40c021504e500c0300d0440584807541e2902d030000300f03c030a075007a60443c00800c0d00001c0007082c0082e980d50607540b080380c10007000140b0000002c840c0c1014802c4c0d5403100d000070708800001081051703030380044906000c10394451400760082c4050101c140107090b01a0081060482d04c26440c51240001e20f013095051550640611003d00303180b202c00e035618412401a9445010030f000344101003007102050300f07061140601d014036003150303000c404000c1400c201c955148510101e066a01c00c44071114044079103010358018041c1054050020040d089010700840d080c030204038044c4003100390030000030000c0c12151019441c090200700d0980c42c01001101c40f00e41c28048150003007010009000039260400001601c066104c61041c0f500c003182c0c0c800204540104000400603a4440c030300341e00403035581c80119004c00d80d85440d0891005960001a10500740c60f00058480ca0001c0c1707000455000340c40801050300e03407445004600d0024019242c056208122020503a101e1200601c0348000300c001c5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 786863147 1250 786861897 786861899
    0x3080306060706110c010b190e0a06031b080d030209131806020301090c12020712140d050f010303080f070815210304030b0108161403010b0306100f06170a0902010207 73
    0x940c0c04a407012906128540e001085d41c0f11108000d108410b00b205040301d118551500030f03880560070b041e1500425130607880160114003a400d040d00042c010b1070707112100290300280c001030a10112003a220b024175520400282000f840d0285c807c81d100020041c0961b100703981d01c26180c01c054204500a820803840c40d244d081c0204140740b0140d07002e401d0b40c40c0049280056801c000b002d0b020b1041000c104070b44104003000c00203d05c0c83c2d00404c00221410900c024400020000525008241904111508180030423904403000302003241640e21035100d09506445203414961014000c2301c46101145030400422420412420003d2501500411014043c0d85d0f8080032200440340360405c002c9980041024000c20525451041c05010040b0081490345c0d19000b804492004910880401c80722405115100e83c4007034200c030206101c080c089a4a500300b81c0b040c1c0200301e20342e00c5265a02e400c40c44010031500c0c0700e4143d40c50002c0d1008501401506c4060f100001051403c800b281944940c0d00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 786864397 1250 786863147 786863153
    0x7091d0c090a171513020111070306090606050916021b0a090906060e07082505041707080d030c05040b250303020d0515012012160c0b0f0301030803060607 68
    0xc44070002d029600c8990780e2062092203c140391000340c8141c200c80000040401c81c002034543c540e10a00d82e02441c0401103040e403e885c00d401c12016800c09028103060406200030b01c640d5410031702c2115420380710201c26a50302e1501c0011f000b00b0030440801604000d0090440c1c840c070010141e085040207120861302e5030744000c0d001c100e5807086411180f640d2a25000c000c20040311080c940d00010030701304a004c41c90440a072010020074035104800f01000c2072031441300c0324882d4054501400700e440140c020181d0350b803140c941d9201248500d00b0144600400b056200d8030a000d01744c120780c45520b4071400e05003003040007c1c040d0000c1600c0306108103590003200025049611140c2d0003400780c3c40043e0380b201c90a10304410356000811003424420701400f109030a076030060780e80450050703121656003001040413402e410a54144483c801265001c1410030308220140601c41d1154494148011407607501c80203911240038441c1c0c00342e43c0000500c01040031819003c0119071050002b0811407810752266 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 786865647 1250 786864397 786864409
    0xc0304060c111b03070e0105090f090c0d0f050d02010e0318120303160e04020403110621270c03070b0a0201090b0a090b0f04121209020d050a0b07091d0c09 68
    0x500312561000c3c140c02d0380405090522150300940107003003001e503c540c10007011444540c4040d02c080b0740c0210401c00920307900c0c3c040c050f20a90075070091180d40c10020b0b80c10160091601c0103019119030103180e2400003000c0c014840c0a642c1c01e010710186040400c014000c0b006800b1814486412820305d6090112140090009510445942c48469203890408400030000f40310100844d0050b881080240003140c00c1c2014544411400c5071242d0fa110f6110700c140301912080c00c1c09a041031081320520400707403e04c000e60404810954940300c40800c003c3d402c240e88140310310040760180c2004906000c1d800d000802042c4000041c00040b0300709030255120a10b20b0000c840141f260390755103110001300040f02d449190000f000b103203801c1c16814140c5a0280c0328428144c0b0804ac0f104c0540040000c030440c1d00040e04081d0010000480c0045605101ea01c0f81c640e2141103079000c42d6140040c440d18042c1544009613480d070003100d10460842101e82003010340280c51034000c0c040600c4064075540e034070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 786866897 1250 786865647 786865663
    0xe0613052407081008030304120c0209010f080111070b010b0a1724030102030f06130e030c0d110f2a03061006080714031b090d060209180c0304060c11 66
    0x160000c072400d1030901c0c4000c1c19800043c0408034003140c410001c00c28580000260fa8102d90408020340e14124001d4098071003e440000c025000a00034000042c0c060100c10208210b4541c01c000740466281c1107040c2c0014460303204000c0013206c522005000d003100401c044c003806000360030301e0b43d41c0300c0b8540e40c50011100100c4101190008420440c81c4503042e901072440f490105400035402c50410a1440c64450001401c1e1402882000048107440d801c0b604288440340d0b4400660b65540c03000e174140380e210602e140008000c1024440014090040081c1d21426540c0d82005095486c94845507120b0115040c0780c101c40d03100c201b40c0c0213503003a60140f091078058072080c40d20703031a080e02c9c228015011020041a0209101040100b800c2c040c03141400caa60008005183d1910b00403608403161503402945881ca8206603400390102c10011103500600002604032501f686280010044100c1e000c421100040d03420402c0c404607000454507048400c0045043c20411520704030451428070702491 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 786868147 1250 786866897 786866953
    0x13021207050f060c15040c0f08060a050606040b0703080c091c0c06030c0905060d06030b040804030b01140f0405040303060e091b150f030c0405040219030507030e061305 74
    0x40d003000c20a910340080e400100203001c0d540e641c108064940b00b142c0701c01d111100451340c81c01c00000202041444940c8401404100b14500c0034a9202c441850b03855908446400380180740502003881442c00c40251400c95034126050383c90011156401c031558500603016a076420f0040c0400001c03903a503180101410258201481d0348003119041c1b0f00d26030807007588503000b41441c0c500070344003d584c440c54032000c0da001518115078589511110000900c85680040e02a550020505c03041000940c01401200e0284110f4043c80e602c0701090038500c000084000d0b8051980c86864001e81408c2d00010ba1150003130070001640c07969641d040c4141c600440e005c884030b41107801010500142405029011001a2260b42d8440b40c4a050004148580040c0003801e52002c800518080c0d1000d0840b0003604010304295110740142c00300e8980914107501c0f01c004a424100065603c502c80e00c0b64111920134800240400e44501c3e040701000a15840291194010044a112847c140160510380481 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 786869397 1250 786868147 786868153
    0x302030a060b010e042f0705070902070227070305090a02181e1504021b03132420010204090e15070908120d0f0c090305160506040e130212 61
    0x40707402c00104400c40d003580c0d05100d2883c243d0f0350b603820700c920064100901c00e0030040451009600448004d540034040d030007800ca109061000c281d09015070041c0118500c2a64040c00158400000320582d6001d16030700c07001c1c59158000104200e202c1d0300b00507000300c524416140e40030b11a40100342c040c000345501200342c500c440d0038048501d140a44030070310b50f141560242240c0c00c0c00d5090a0304800d60310b142600c01e940124444040304111083e0308020000c983c120b940e6103401142100c1a46036a2007907130340340900020344400d00034007141c0725100c1c01e200340d4800207040809001a100120a41d1302c0c4401c3d59070074407001c18108200d206848429581e1340c0200340b2101c62142d61a40a140240010100700c1c905900300100040020310401842c084d20f103854131104c4840e2280000e00e02502d03020b544908202000c076500da000451201640e00400940d441c0b400b031007100441350700d401e110b41783c0c1040d0308010401040c2e009040243c3c11400d0b50025040305000d503000251860380e50750314905c0c160 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 786870503 1106 786869397 786869411
    0xc0d020a150f1707080417160804050301230a020a021615030605040e0c0d023d020c0f0409170f0a020c030a020609190302030a06 57
    0x40000515000e0509020200410109216a07000042100c1200d54014410038032039191140c0150307100d088451b1150ba0319455802a100900c41d50b0403c144000c0911141c00b48040d0130060040040c9078645040030109030840d4118a40700e86400602c0d58107070b81401441400c240e10900708500142ca44040034030a90501e65180303d80000c442d801480810840c280e5480c0d00e010045a580401079075440d0824081114140c1c5c48a480a522450900e032062904a14a880d61407014003040d1181c0078120200e1104802c03120308500c0040c01c240f039030023141c080306030001c203503000da00c024052035942a0106482d501210f020700d0007261501408828441c01c4015022061754110900350342d02c0541c6819181e0344c004d0109640140910692003a40d403074009014206180c00405e036600e4003844408004100310594000011098030a0300080941c0d42401203a2145010741c2001c2400 = true := by decide +kernel

theorem cover : BRFrame.Cov 786690647 786870503 := by
  have h0 := BRFrame.cov_init 786690647
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786690647 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 786690647 ≤ n) (h2 : n < 786870503) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
