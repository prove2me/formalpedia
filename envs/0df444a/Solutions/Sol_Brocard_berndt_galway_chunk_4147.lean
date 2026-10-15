-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4147
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:42:35.937403+00:00
-- url     : https://prove2.me/submissions/1e97abcc-3990-432a-9fc2-40113dbc40d5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 745683453 ≤ n < 745863309 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 745684703 1250 745683453 745683469
    0x5040605060a081906180513030e010f02100507080612070e0118150803070b0114060405040f02120106050903280609030207170105011a270a09060308090405070c0809 73
    0x401c41400b02d1030140c1c8180c10b00005c40f20181c010b000c55011451041007001424031039254880044220440700400640b03025100345050440d950401244070900c562191003841500c0000440c2c0e2810710190400400141c1510011604076018088000341400905030001e2440c040702c07124020b09140340d007048500c520010030107844c082c140b0788504200030304003c206d202c003004014a801440c1c0320040e40c6844459840180d001c02004c0c011070100b000701e0b41e00e03803007150100d42e000c0740d0020f401c1081c00304200203401003c0b00502d00381607040c000100b5030f801000a0081c0b480031001d580d01255040360001749240a40750903844034004010210000c0c000d035002201d0580280100c400307842d600d0090300c0a0303c1d003d01c01e00242d0b9449400400c288885110401c3c40c020100070b40500702055040d000541c00b2001a504113407000140903402e039a103650700d50102402c201e100034000c01ea280d00300300613240e0040c00e140f401189800c0010301d403144203041007281d081d400030440b46810a0301007001180 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 745685953 1250 745684703 745684711
    0x20a090608060102120d02090a17030409021b0f0703020405010602030c03252301050c070308070e190308130f061e033b0d0f1d03030a0203040f05040605060a08 70
    0x145c03103400d40300c0000e00004005014100400b640150b502c00500302801056072031340d40590000321180e900d018640d44040f080e01c05685c5682801030301c0381150180c12800c00070080d44002c0300d00954508000c280004201c01068134000d903820b00039641e0b1540c2c00c90b0b40388103103003400200341c0090100340c80c40130040c14540360034195041801580042c0d80c80308804000031801d05600105200842c00e01d40714207008156018014103100c506203200c80e200170304002e500410716002c01080c0c0380d45610650782c040020700001412084900c1040c0c6910b40b5032882c3c0e1200c580b45421601e0700100080c030313150030b91004050b104507a03100b00e451a840030800d0381d504031004602c800c1c191220024001418402d0f83c404001914210b00b03540d405c0d50f000d4100046045003d2000c49070011100c100132541c100c035410600d5900c41c90b0425002c503e0100083c143c01028441a030703d4040080d130100312950010180003915a08040301c4c40b01070790f07601008101c41c03007072265a4004100f44100c0750001d0241034202e41c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 745687203 1250 745685953 745685957
    0x6010e0d0f061b11030a051b010e19022b150b0402070c0303031a0609100908010207050a032a12020a0501090c06030c0815210313030b0a020a0906080601 67
    0x5806030340c2d10801542d140d81150800524a039002c43c04540c1e1000e0307940307215071202000e94070b0007000c3c01008025206000752000c0050710003c040c941a0400d5001c2c8000c007016100340c1e031380c0848020b03544032401d00d1a402644111031408110521903c0c1640c000e5480944c401c0450196805955030203411820505804000c4d540d00d541c12101d407198001032016900caa540107010b5421450080c080710003400d60107113400d46594441403d6141c00046500300c65085a252802e0a5104d508640c01216500504a10b50020908038104035000a4a0900302d01c2600c46206001d410108440401e080303d11118030740b00d0301d58110707000c280072103803507080d00000d481556075031100c80c0c8410382511000c13a000c032559400f0f079200704615641880386000d140a9482c2c4a0f41c2420008a0442240140341003a4811042e404100211088842200b010b41c420401602d4850101c59000000e2491a20051b15400040c000060062880f4400c44d1715210068441c6114181815422502842c00500c4581 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 745688453 1250 745687203 745687223
    0x6010c080706050f0105011d09010611070b0706150608130201030207031e092301021002030c120a020301081002070336030c14030f0d030b13060611010b060306010e0d 73
    0x4a2428003c9511803410b00a840101e545840001010049a403014420082480080000960700e00c80c0311411107030103180031841011068490303410034030760b44c1c000c0b00b06000000314807007080030300d4001d04019020150710300c002c1c0d56120411b0380e018904440000c8030951a1240c41c00642c0a0703400b5003102c50013864405081d401070380c0000c1c0d842a01c0d00048000c00c000360004c0140c81d039141c10b0080030b4081000f1400280e926000041c2d65505c22045d41004560003100040c07042208105a41591102d410011014140560f845000354400e0188503068000d01d83c41018568050003280c82c841e61655a13881e540701c1a821040604054080100c1c0c020b103070108040b011643c40811030061401290322040141c84d090003202e442c50131007140c03400fa40162022100940b804550101100010b0801196054145000503480c3c06141d0030f054400741350110204a41d903100c48007046501d8180d000300522800b420400c103150008840041c006045446001c02905191100700d502038440d1840071 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 745689703 1250 745688453 745688467
    0x7081b130605070506060f01120f20040305150f04060504020a03060e030901083402070f170105070810142b1e110105030c090d080414061206010c08 65
    0x2511112881c0e0003600010400704041d400d004003448551b800a80849040340d440741c090f4000f800241c011008154466540c0c3c141801d035040700c5d0803402803d800200d01c010f259558103101c4115402502050350140301e180e5a18400c0c18100489900680035884207903a0b5983c1c560b40c8001602000344101d03000860180f001000914070f0145c508031100342c4001e0341c0c65400d070724001170000300f00800700c2c2215600e00f0100c1e070010308101d01d046030020104070340608601c0c3c0d0f50800e0380f400c0075503404032486c03040903c0001141c414460031401a410403000900180d110840222003081007555541d071151080c1c3c1c4100140020300307214002001c4050404d411203022004140200004a110600c50381201d01d0410100802d409100a0f00302c04112017601800103911079081203000c41c20800c0c103010000000c5040e032018a42901c0001d440200180c40c04000d514085003107030003a00c990500120244181c030070741d00e880c4040c0e452894010546860355510500111030a808103a402e44605000708224 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 745690953 1250 745689703 745689727
    0x702010e0d080315011704030516050d03140703090507210b090d02010501060206101e08010c030e0106050d031b030e030d080402031b01020613030210020c060a060e07081b 75
    0x30780e2000b406032081a441e8035004038401d03030860002c0d50007410440700200c2e0740054000320050540040e05840d00c56122403011100100c84820464094803900c1042501540250b150304802081d5542448039540341d110400c00b0760070741e038402c0401006600440000e014585811400f21803082c41d0800004a028498442e80174803102558600095004044240c1c507058090148900404941c8020211480c14120783c914001c0b4500031a03500382102c80ca007191814028051002510340a0020020345050240240060200341c540280e69400d051000420303203800201d8880d00754141d01e484a50700c90704850090003448181c821001d200e070b80880074016490800c03242041c0341654440032202e00302401094940b16020307501c0c0703020a0060360200d0680e607012682e00c0c0c101c05601a0781c040032245180590420300c2e002c6114515900c08510001b841300300040080c05500000001c200c020342758a40d9801c02001101c1d5170b4041900300001c03801445002c00b0361030b41c00000d03000b41414955503540d1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 745692203 1250 745690953 745690969
    0x210090303061707030b01060c210302071a091b0d031b080406090801051b0405011b05060a09021503010803090118090501030f03030b0a03021e04022a060108210702010e 74
    0xf002d02c80c0d6010300400c5c41003100307000d413050240005003056140d04000e41c0d1101c840d1050000da001009401600c05410140640c050716900d80d48800760035200411000d107404400b104651040903485040c000100000074200b0905928030040d001c0d0301d441100792070545400d08150b60710740200300c08040f00404030740e95902070000b030240303607a504483c0c40c94880c0e12404d48078081c04484c03800d980102d1030281c0c903000b041110200d0b0300a0900210155242c010115501c0b1403e402078024025601046102c204991045007858401c80c0c02a2586913620a10791941c002406020800c0c4d0003080403414075805440d403030018003488145452125104c0a000c002d031232003032f4822160b20500b11002800c154241c01000401003043c0c8500318480e2840d00020b0880c1c039049015801c1c1c03c4443c030038828503240e9804a44011401040c1d800c0f070041180b4541c05001550054036001e03002e12000464006404202014040c6100303140600c0c4034906060004a9441840b0803414003e41c3c01d0011901d440301e000c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 745693453 1250 745692203 745692239
    0x5090f06042c070e1e0a09020307020d030207080d0506240a0f0e0f3a1713142d03010c030207030504120f050304180b09010303021009030306 62
    0xd040d1560085002280070a05074100206034100c05a5042214040d80903034443c8604c48102c810f08240c00381030303264a500001ca002104c1c3c01c10002030700030507041081c2e0001c5004e0b01c410b80c2101d038178043d0840128224010010001d0014204020700b80742c4a840da0021600064000c010031500301d0f41081d11000e81d00381c00b02440041e207010903c03195440e005800b4000c024207a082c1340380c01903500300020f0308540c00d1442e12031154a0010321001c039544030100d848a20010143e40903000322404400070400401e40908840c1c3d2000344d120310b005071072614103540d6014aaa05283d01c058241303007600b02c0c461449825260810900501607402c041401c07402c8000c0c00c03141142e0242d0040d014145401e46124000480038140104003070030009500804071000c03203081ca039040100e00410b18180b00351082c030140180a52001050208000300c80ca5807940d8409480d0000300b00c0805030321b00b40252503509100150168101507010720445000b500b00300100745c0b180c40c0c005007542e1100303d03030368046100396 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 745694703 1250 745693453 745693469
    0x11404060b0309062a1e0408010e0a0b0a09020603161206060806100f0f050d060801060b031e130f0c05120d020115080601060f11030403211d0105090f0604 68
    0x200034041300302001c203610004031080b200508454045200100031a06c42d054a1800c1441c05440c03000000203644e080c0c40103801c00300000e10004142d2000180c3d18140c0032001e84412418201141e52803446210707505016a001d410b00c0e0455480700d090401600421000605203c20701459207419100ca01c075680240000740c035003e10508080d014071032240c07110400101801102403170640e0190b00310b40c60050520140c03420a540c5d01011308c204001e03010640c03107070300c540d800c001000c910000e44c0c9000e5803154001801c6072500c110341005c0c2c00b9446c003050b83c10303501746006011a9001700345000d075802030180c01030795665a00c3d641c5101244510881d503440c10940e8005041d0140d1041d030a00032a0b50380340304807040300307601418040d246407564818480c62040c00f00661041e060306006140b00007401ea6520247c2e03450b1681c2c0d00380231018802c1600746000092506d0075240f2140e0244d020620411901074039000d1140246005580c150b00081d11668800e1640d6000c0340640d480e54001e01c00f8201103 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 745695953 1250 745694703 745694713
    0x2d03090a0b030132041a040c03021e070f110414010e15040501050a0501050c25140910031113110705010b100206070309060b06130f0b040e011404060b0309 68
    0x50030650041e1004c504003055024442c44500800c1504608118661800c84000413082131146186806808540c0c1c8950002d08207541800c4041d0554081c0541000b000340c904512140c4205d80c41151281100003441980312800a20200c4c82d0405481400a00504000366110b16140c0102c29204260300803160080d02c00100115003101c14601a105442139400384035550411001405c8102940282c0e41002804102490075041c200200070360300c115510401c2030340340c1c1400c003d100c4020303d000309100718040c00652041414030b115518840c12030413000046060035581d824850b030110703003800340d40628040c600300c0c0d10f0740152051182c0c40d40598007155031200b5514105094580001d400c3d0304c0b50114111084803560081a40b5a12412520b40059094000c2ca400002400c40d08002034000c2000f18580728035480001080055075200c050741e441c9113a441040045600c680e000710342c100030404004002e1a40d100350104000100180b0114130903032079080740f80c1682c201b102c2b100e20a5003d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 745697203 1250 745695953 745695959
    0x1e1e0b0712030b12100207230105041205040303210605030f070e0c1303141518150c070303110c0a1b090506060708070516090c0905032d03090a0b0301 66
    0x140c40b84602c140800d6484d0707485000c0c1810200e89403452080c034040c1c003a070009041c2c001c05c0390b040e8030a80e0ba5441010300c1c1000c401840016070081004840c200c17540006480c600005500800698084070791559039544501c2c0c01c0341a0607200c01c40c146002c5401038890038007040e1941d0038401c00008071240340040145501c1d06400803401c21000e8080c2801210402c10100350700c3c2e0320b80c0300c0030a4940140c84001c1c1d92610000003481c00d03040088000c1c1842d500014441d40700f1041e0a460745801c0b00408841f040c11108026000d00e603004d0711a91204001040034100107802600207c0340c02d4900062603050200500320341d410300804c0d5008540300022403044141c000d00e600445400342030910b004001c04e2410078086041d91040c0da0000d01020b60104814041020401101da180412100381424255403549544060070403c504200400c40303480e00485d850a00103081c1c0da903c601c00700c03000300715a44034030451710f070f08030088104e8101e0204020440c020344800b41d00c0001060342d244210340c0d940c9 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 745698453 1250 745697203 745697207
    0x803090109050a0e0c130305030403061410060f0f1403181608060708040203100c03020a0306120f0210110105040f1703060a090203070e090f0103020102071e1e0b0712 73
    0x18160802c0d88240e40d107a0703040c40b00e008120031107036212000359103041d61250012040248030210f940002c4c50341c800000d01004109080c1c00c811002d03040c03426032400e00d85511080103c410104c0c000d14000404070200c00c40d00611403502054031808a0a280d03011020744d1070300104a50044a031410f407000c80180c0704001070390810401c0c5c81c00c500007406003000c908154242d602d568014000c1300030000a41e0200b41959030910038124661441c1c24100032002d80d183d00580a90060742e98040030074901440010303010140081114a10307400101107011840d15800c2112441c481b8440d801080715030403001004050034401c3c0c0740107600a0300000c0ca01805407420010500e4480b001484484060051150039210481d0b44001e81e61081009030b00ea6561a0040310900301031f840071a4020362910501500ca40c05400e0241640e000380e080c6c613095078842c05103026a0700d940007900c40d041c011060800002048100112030480c0300c00403444604e541301d030440d82c40d401c02101603034aa00005d000700791040e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 745699703 1250 745698453 745698467
    0x1805060601140a02030f030a02090301050a0b0a0506090d120912052b0804060b01030b0a0b030f090d120207060b060a0206251202070c09090c030515040209040224030108030901 77
    0xa030709407112803403c52a0748000303450380240725600c1908000071002c1070240d8920740540e140c960016000300141d14200010b000580b0700394602c40d0164118420124441c2001c4045415545001e004503100140c1ca64503003159121500c0413208119800d180852034105416104040c85d000360300500981407180c48030850a6866541c0c40a4640344422250085410001c074940c0190802d0b00068003040b241d00680c040d012141603035902c03881100010424454800c082c600406c080d2000412647d40d40003c00d94588800d0380500100e040002001c103003a000360000c089032403040e9000303d4405021004148190045520000941c06c0030082082522800448014012840c2004103228040703100190811100c5180c3ca50299000a458001c0c802e03800f601c04024012104100404100b40c00d000e450794055000c2140d21b8064407141204103655452100d0007240c00034006600e40d00c0b82d5082062102a000704400c25440072001e80c2c62103407038803020711300815170b4901842d51000c030000010600 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 745700953 1250 745699703 745699727
    0x60c02010c1407170a110c040207081b070f120b0a0506132408070e0916050d0f1a0a060e0417090d0503220603140f07031805060601 58
    0x40e0314260a16070755603400300e011240081d0350380c2c440c1e82d602282e090804400c1c0603514501200303540000c0c54030350580c1c0081801001032441c0147c80c80481c041c010081a03104030b400141000009121a03004090011150b1000e070800e003044468050303a41100c450071041c607602000c0354942082106003480401d030b0071250b02802d88003003040986081000607800030800c50100420a58440c803641c8171084920302075054610912000c907900da910a02e6a5403000c0da8024092018401d0003c2851031400064001107040d0f6841804525420481401102c45e0404025258032910710500c03000f081e00303c4010228042c010b42c910100d407a000054000741c80c001e40c814000190003004100c042202d800d456000c0f00081d0904940c0c071131031a030000b541040011409001c3d4080001d003d1904948090f030b0202c00380d21940090344150791000c2c191b0803070741d1503055003a45000000020301008c04c1c20300c286a200b01641400100100c500e1080301a110611104841380d510a071b0a0000e15071700203940b80c400e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 745702203 1250 745700953 745700957
    0x160303031e02070203100e24060a1a0f0a090b0304060911030f0606040c021507090e1b07030e1c0b01050306130201050414150f030601080603010b01050f031f030f060c 73
    0x6083c0c5558003199031440070810319903c4a41c0c40c905031061080c244070394950004041d2484483c0264000da80025460a4038045d116162000c0005104243c0c5426144140d01000030507060440c0a000c41000e58040c5041004104a52001244014907400614080e03400b034800011031800900c2d0401c03660000c0007205e03109602a40c0c100929900016030203034001800c1e10003181c02c0b1440e1400741d25044001c0c004a90a6250b08100070406034402d003528211754031450030501c81d80303401d90341180b24050b8030b90b081c5c49068100a603001003070299400741c80d6488040c0c03892810810154401810b448020710032201403040c03c2c010031081c50300700031030750704540104101c6241a28650000c1c11600c0340d8410b4100f0504645d6001c2ca182e81c58140941a0b05a40740850b641c03100348091510056000321600c90104141c1c40c0890b645003014856068102c1c3e060710f44502d41015200076203643d03040249051032000310700101654107000c41a040e0025841440c1e00c0c60551054a05102030301d01803c41d80003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 745703453 1250 745702203 745702207
    0x606031416083c0f0f0d030c050a030507020c040f0c020c100e09190207060c031a090c16080706020c060109050c09010804050f010608071a210702160303031e02 70
    0x501d00c40000d15192030000c000f1010695604030040166030100c03000d920590700400b40004403e204c0443c00b2407800600d5001d94545a02c0b006d800d504a44c200b0708000b00090b81030008840f154001d6100c2d94014107030780111031a1a000d0f5001600b03680c8560f501f1600d448d29000c54040244d01000003002c118000c071490f40340300c000110300420119480701243d10403d602e401141e0549090960481c410062100566403142d0605002c3d001e000c0c44200312002074076140710704e8080008000da03250703025401440501c040d00c076071038040c6803a0050094545801b4403000140c0000e00424000e00405114081c05070300e410848807003d050080507807003d03d1140c10304c5d04002c0e58099040c1119200c102c00d007403110a42c1c42c0c80c1045461f20042e02883c100b250700e00134010a240c0000580141210240d400d01110981c841c12034060b14014250040300065a00c1c1040425090700c00f8041d904c2110307841110200c00c503c0340348030700602d4603a0055011a68400c2176030780b281900250f00c001011a510154 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 745704703 1250 745703453 745703473
    0x3603070605040810150801110417030a021c030e1f29010f0c150f061707150c0c0b040e010501090302010206060d110d05031b2107060603141608 63
    0x368075440c13408074020701c80f0703075507150403c0b511003500f080e2019000750700c001c014080180346591065841401880242c04a25112010300400007045031581c030704990281c152041c0258801c00c0d400d84420b0700d0428103485000b11400190208452980d40540014404903800003159880c00c540c1c0020400c184680c005460034000401d50081c3c03d9000c40038039242c002c0c041d110700119010001500700a106c2c044d62141c000707940481e500328507141d00c14628200b00290350b41401c00c0c00100200f01d40c20360341d0000070b400c22400f10074028010541e460b5080c00400d0b085142d0729111001c4094201c1c4c00300c1d0001046c00d0082100e50054940944000c4c00d00081d000c1c15600080d5661100410b180e128103500d0302076004112001c02240c405040160021000324900d00d007903078903030b00b000d041041920103540c419581401c0000b0300340d040741c0390038607031143d41042103d10342c0e02540006010b6502c0c1e500c5040c004000b0b49200c45106c10f12115001800030806140d1020400c4082c07944110100c4d07128240c44 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 745705953 1250 745704703 745704719
    0xc031210150c0b091608100e1f0f110c03120c2b0905011506080a06030f0b090c0607060615111b0f0a030503131d060105360307060504 59
    0xb500742038100c50540307090381d654510341d032810600c590040003007609940b0000b02ca01300042d07010704000c4401030902c05403101034110b550342d624003c02d00f2240b041c42103403001c00c094a035000c1501e40e5003c01d0007140218541c8104660341d0b1080c42d011100b5400003520f912802203103610903822440c200c40c1249045501c0c01041c00c54a01094048008402000d8802c03c00c1e00d01e40c003100d88a41c0c000000c3c0303c1040040445460900f86129503400301d038207240060075200c1903119860030707260720525000c003511098584c2511450000c0c68400f151092800603107003580c0d03d2001c3d000580c40344502050490070701d954200801d0000d0711060a00000035080c5c42c2c049800300c0c0000118015044880610205c1c1c00000e894050404c03401c1e401c40c04a071004007e002001c401005040d40c0e10132590b50107961002d521702d0f2941c147c0280e407500e069402c080303003556100b5001010000c0310300c84020421003a403802043c0f1100070081a9082d041c0c00079210106050911001000749054241741e4240b074030303045a03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 745707203 1250 745705953 745705967
    0xb042904020906010c05060405071505190c0c0f0f0f0e0601120e0c04050c03060103050c0a090302041d01020313030206060303071a2703090316050d02150c03121015 72
    0xc002d1144020000042050348a100d141080315000070071a0011309240c100180c0b92245070049401d4805810080780c0c000703000302e048a0440680224104a40c0130380002291103881045085502c0309101d6030004403d40d00030041030162802c0d40c084d0713080310310f0200710a0000140d603010100c4a0174071800c01109a0b0000c2c1110108402d0610103c2d221754204042810003401d82c0384d903030303010f4501424001e20007201d002070b44c4101d2080c1c80030810342d280d189041420b401240804000206031000c180700504168107d0b03503942e00300c500c0710032602039030000c03443c00e9810403507500d100105082055403c3c5035040140c3d64104800394042c600e4018103448840550400c0603030036680301c00d4940810b0381d800480341030580200e04c0c00403141035101d14a83c596120782c48182c01500c00c0c07003032004424802d4911041002240e5004000c00c041d50002e9003441110780ba124801e0b9400201481840c990310300c20b00082081420b6a480313000303217150003180ca9400c02d8180d045040a103035032148024103140c111700 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 745708453 1250 745707203 745707211
    0x1142d0a061205102105010f02160204050705040b0415051303050a020a091517030705160608060406060e0f0310110a08090105070522030507060512090609032203050a0b0429 76
    0x2c0a5807103451300341807847c054600e031101c03010302d144006001c2c1c980350b450a9420800520807038017032103240c49409085407240210b014501350520308100400c9400080c1ca6440086281c9082145c1015242c051641c1c41051592041d030f4503411580c042c1086180c0040308801034444144100a60726200c11040b1456182e07010b0045505c2c0d542d00034030a040f20410903600716541c40303021034000c5600c0c0301c102c070b900d085a40309520105a0280225844d803505000700002d45450fa5a40020004c46000b004150b080c0070441c142c01d406103c180d01200c08003405540712490854004603944e08101000034582217006140701016450942480b00c001c0d0b103c1c04443c2140c02101d4000016034140d403111840c8102a80000c180344260040003601503001005828850300c4005c10084540d540b4500301e8554004072000304a41d04200480c1103500300004d41c5c0007410b00030b4401c6944094881d0380301d40ca0420f8016060310090318110802007003043c15600262001200540100c83d071641c80e13001c3c508400050 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 745709703 1250 745708453 745708499
    0x120906070c0b040305010213090c020a06050c09030f0706020d0306120204020f250201030b030d021f06030605010e10120c05060906120f06030601142d0a06120510 71
    0x19209003400004144000079000b460340c02c95480d903881c0b03031250003944094220840231481000004036041e141c403444401181d2030300034040800c031550780e41004003001803401614080c2800742103500c1e00c0c01c21a40004112182c01001294180300c0301034504072011001004060a0a000303002d180c29000078201100d40c156400340c1c490100b2400340146d0b001e0401d400c8100700300015a0070801404590300e030342250003a00c0130030154000c01c00741a00c0d00340c10381540001d83d0000b0442007113005400d40420102c0303000200060704d551031750f6070482520307400c0e8000c4400010601c144510400042e0420b001850070290403160000b0541d61024a81441c0c4a050b1040b04040390102640e00d40703204031848041101c00c034100134036100e41d80512a503c2030f12101e000e441420000b185540d100816441034190007000c65443c0282006445510501198050400f400c0520030103075680301c00390f01001030802078540254000503c55103004681009140503444034956204000c1441a001c0c1c10088004807 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 745710953 1250 745709703 745709707
    0x506100524040312030c0f0503090d0e030f01020a030b031212010e070203040f030b0a0b041109120309040615121505010e01020c030d0e0301050c03010501140304030c0b0a051503120906 81
    0x101c0d24020150003140d0018106804c129254503d40307615078402c0040d1341c11074450050b4040e4602d000c5480c1c2c0000c070b42400701039002a10411550380251110003980c100281160500750040a0382d40c2646c01110601010a840f880040b1480c80d042c4000d03498401c0105265041107030410003941d40c20410f20400c10681007400104280510920860300640013005004100507901d251003500300200300c841c0c040c5285000007000c1d85142601a8070058003109081ca414405c201040002d2003024030032060451004001046840c0c1300d50254000801d140ca090320894440000701605074003e000001500c245021503144100248000e00030a0740c0003860103070f01d98a00c1d580182d14082181c40d81980c540728a442e144140742d4000c0c11000d0102c4103038004c0c4216110103040c80342c40d00080c0200c0e0701268000b20b150f49902d8000010790344c041c0c0a4642400c440340961143c0030402425640000e6050320340c01005174881010f180e9590003001030700101150000f1706462100c500038811018880c03100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 745712203 1250 745710953 745711009
    0x1e010c0503070f080a080916050f040b0310020306010f020a172a01050702010c0311092701060503060a12020f0424081005090d08060d06020c060a060305061005 70
    0xc20907034081030f80c0818100c1000700c9a0500c007000741c2012140d07400041350440000c5001c40086640440000c4e404c1d1078044035402d1100700a41d4007041c080c5d2a8102c0d0b6242d841c00a2035600700107240c8001d40008c40140e890070194001030075140e03664454010740d8411540240080c0c5407000c00d40145800d05c00640e22070382540a6040d0b0b042c03510090b4800c01c1401c071060901c10006500072805880280c0080284450101e01a130649181c1000107403101000d00c85100681800143e003241040117903c032800c0300c08024000d40000300c00381c00200018001004110150401003190790240543d506040c81182883c0d000404072850301000c5802540c4071100c180b80b03c008e051404103060840100940d080d0b07158003006585d8851110a04d40306800d210124005600100f070f002c0b01c0031503d90b2541015903401c001c3c4804601035000488180da42009a084220424800b044c0110080d0a020480030300d5403d101e45004005808443d502c6c900d15010042962141408801c6840d4100281e40000d4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 745713453 1250 745712203 745712213
    0x4020313050a030e03060a290105040803040906030204200a0c02060c0a141011180d1a180118020f0a030b040807030f09030c030f060f150e061e010c 65
    0x408440c010400e218084441d400c040d00b2640d0a103132030805400b216815943e2004100640c1c142c1c0c502d540c40c2c1ea02c400d0440741d032904624091240c1d043e060421070303d8185c0c0c5100d01441e584c05036004a40380d5a42c4c0c0000d100714940380c002d906040c1085d4008200001e403d02410347c0c10710425000b007003808101c50b44401191a80c900340c403445c92100b01910114155410300c001c5002c2c0309114a0300b01c2c060102c4120b414025441b95a1317155245086983c02c00d800010038400060210098aa00c0510079103c0b000088907009440000c1001c00d4047c51107007450303141e10a1600c03001816890790f0741030007480e030f10300c0300d140d054032840740d404607031400141034000d010400c0701d001500f0261154050004200510480300010308240b882552040398100701c0500440749030b0054000240801d056220030070100c1c2100303044210041c090b141c000391141200585008a03016100d10302c0880d881ca241c02c10202865a50300c641c4020180d4200d00c141510105030f075040014001000d042c05550071210742480 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 745714703 1250 745713453 745713481
    0x10050a050f101e09140901030c030308040804030501020a0c02100c17070206070f1211011e0207031106070315080102250519080d06141f03020c03040b04051c0c05040203 74
    0x14201c001e80d100c80780f01c6007402482c0c000c0f0f50088a007840c1e8441086001810000f04590482c0d4002e41c030f0012040c1580c1d01110046000761003641d41c101d003444003001082080c4010420840e0988681654440a10502040d50040c190200030320507510280c0c000301e4450014404444203400c110741e62003203140b0000d0b02e2805440400f0b00380c00e146006210801c22002d62440404145071103000803403c00848081c00e80c4e036510700311043e040e0045401d82a07201250041c00b60144627013450b160454001003c50300d0113204459a000083d1100340c411801005080e41101a0007510000c1d481d1502c0503407500120407510040f82d41d1070360510340d14028080240041c2c4403801c9806001048000d29040680880c0c0080820764420340c5049130014280c402e82447d112040c00c0600100072502948550481c07a4424009040c14540c003000f002500c0d04c4c05000030400391101840f055181c0c0c1c01c010a000c5541058401446160b450113120408109003c000300100c038011980941e03680d44a00d000d00e400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 745715953 1250 745714703 745714727
    0x3020a050c0609030d0b0d1e020a03120f2723090106080f0c0301140f150a0305090d0e0a0b0c07051c050606010e0f010e0a12050610050a050f10 63
    0x74002e07901881180c2e080840282281d41c1a01c40070300440f0440406c011036170550043c010440664408141c210700c8411401078680c9000905d008103035a5641c580c0424000d2035800304d000a070058900c0d81c0100e80007103000c0c08280036070f0030989080780c0c0d00e00ca600c8006198000e8410300010803010042200c541003220700c0302d00004e00042d1032540d6480e00989a010283c0e0403085d00340d42800010b004410f9038043e24100c4074117255004198094005210030300440000c640d80000030004411a0a403071000140800603c640d40068540b038002a542e0400c0000c48402e000c2001511040e5165907400c04000305076006a08141c5c0e544c220301c0e14492420b00c00d0750210360812007454000f01d10320748100c507075001c29016000b0350304c080d03030f0b0500111000101b1311405580050f1441d2140015449980c60310110a8068104e0f000c0035240d61034405584c10310001220680d003c02c081041031101e00c00004010f040503114480c602e0708040c001140454641540e9010304032102048100c40d1040346680c505c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 745717203 1250 745715953 745715977
    0x3161104020c120a020706020c01091412011107030815060405010503101208070209061504091e1104051c030c0308091c0206060109140d082b0606080f0906010603020a05 74
    0x12034002e4944070f031002d41000b01c446000d400f440100141c407500204d40070504410580d80c042010f0305000c08503602c441c40c0c0c0066a00240500351b0790401d075070240308410744c01854200b480d444800c00d14004128180040c800e440d5980c100d07132480081c1d1118403c1e074007615003d081c256107030340d00d44403015880461980000840e0740070400107828828450010200e07140262207440303e41c1d4425051001c0c3c070050401c84001c0e44000c00c002c2061200f0340d4410340d5a6068110340e420a418504610b2050300d4000c485220300a80000e010425454510402010040081601e041c40e024a4070090150303084c0c01c201505016070400002c00c20f500a100202003103a0441c84461225444c8038021340d1004d044801c3c42c082151100041a00c40c0c082c0c2c06407404010042c00e4a420508580c3c4a0301e1a0700000d01c04812501c2c914450f0b0401100400b4005980c0301040d0300090081c9043c400603c0080c0c0600044501c405c1c94003800b880c0c690200c1c4450540380141800359542c2c0440301c0840c0e06201d54021140 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 745718453 1250 745717203 745717213
    0xd060e1911041b090312090504023004030210051518090c06091309030203070c08010207020301050a2702031207030305010f0603020f0a0e04060306020f03041403161104020c 76
    0x8001c10441c9120720901c06407000c114403414240340e040004482c05840300402c20541081000820341d80700c0301005e404500e00340000076541d030081000c0e43c026200203112020201d100024111510781010800c0802c080307080d000317082c9030700c001e0f443d2003910200324030907600e400001d503440400c082119003102002e0708140040046050400302484143c3d202034860080c0d55000d155403030f1120665181180042182820001c120102d5009141945085056010a2205401180381022090000c03c03500780096a9545984105401c46100814400e2014680f051285000005800c1c00004144864811001071001d00010380307040c1102040f45c0101c0c0f0002500c1d0105a0f060b0412412222010700d00203510791640f00940c00e03401040000c0c40012018407016985511840643c00b200d07101900c0010419202d0301c0f07003c1aa07000f20b0160250a03000002d1004005c00702052000c4030030100c028506056465020750305070710008101500440c00400240856a1141d040ba00300180391001c9034 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 745719703 1250 745718453 745718503
    0xe0a051e070e01020d1d12011401030c1e180216080339030f151f0e0d050303060f01030b040213030c08030f031801090f080d1107020d060e 61
    0x70400b00b440720380c490045c020050084d01d100e006d0402003951a905280701e4514882ea081841109444140c00c05050b42d250103c2842200e489034045001e903001e101104413040c2001c699154070f11240c0e40500c5056500d4070300304007846a01013140948000c1c0c00d030140c2e07100e400885140b03000d005104041c200403000810f02007041c071600710003981d14800c00d54111003c07120054007400e81d1b4a41c1d9071003240300d80c1040040d2024000d14075081d070011001d00e844041880400214690142c3d41ca4001114040500a030850642240f410640c0210445911641c801c0ca65101c0b5142d02002d407459008003045903041c1c030f040c0e020340c21880b4482d901410440d190744880a00d00c0300303c040c82c841681c0d4000c1e00070703001c10720074804001c9510401b02040c00e5403a5440c1d0704480d80000003a620858080d550740e03215030700000c55184000b1580c1c0d000307440e42d9480b032442060300c20864094040d4641000401c100702401a19400c502e0315400343c0250b000101d0741241308140d403c02d5000b00034040a825480740701 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 745720953 1250 745719703 745719707
    0x70213060b03060406230907020708150411061303031b0807080a081b04060f050d0c020d0e010507050c0603040c0806010e090c0a0821130e011701060e0a051e07 70
    0x141d4401e03d000c079400d02035580e4542e1101400556450300e0740030042602d07100401424040c00300340c1c000e07400384100d80210313503950580e9092008000c418050b030440c41080c0011700c00d10f0710300c1041d030000c1280c3d034900d80844401d00c600350b2902444010180714044070340020b41c0b01d0503040200c8440e0003002e401c0d0354030f62502c2e001803e80c0c030040928000c100c96901040b00c0c861500c0594690344440c2c801640360608000d0305840c4002d524035220100203040040441d1000f89008080c48117200c2e800502c04490400303070140028805c100418100081440590302003034000402280c070440c02e94540d50703691034a0a0081c140100c07070700203c416104000001441c4030710440703180c0c4180c1542040d50740501c080c00c2000302c080c400340b00f03401282c1e003c409010300442075401e40400a040440d200d070301c0d240c1148044400c5402d558401528503100000400c21070581ca40046a0903c0300382c002c0011030304141c0b0703c81c080310010700f26810041c0e50700b0000360084041103c0d0fa80d4511002400d2070149803034000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 745722203 1250 745720953 745720957
    0x6330e030a080903070e010509040809040f091b1502070b09060d0c0f17010302060307030b01030e0607110705032b03090213090201120507210b120a121d0105070213060b 74
    0x10f0a01074411880e001505075803403240725043c0d910003010f404980d03e0301d443d200b0007a08411003c40d401a90b51403485a8030609110300364401d841990703682070100985514803210b0409a1100030400650100110417982c04500c140998609070700c11525114064003181c7c0d24020b4800d0741c03180314a0020400d000c541c00080d15030351a515640d8115181c44154150b052411080c40025001b1300c0500c0412400da01940090490708018580003d8688151a03003502d001001e907004408208c1d90341c1c0c0d01000ea142400124040d01c82a401000540050600324404005201c129028040c941c80540b015034440d4111086141d00140140c040000102410006114025080713010540d4a80007517080348403400b88512403091515140c0550681d541c5240b20151075451440398156211038245a55a03218038419000103220000c1040740b02a2610303070140501c0700ca0210601c134250a503028640030007800090f45c500280380c805e03124011403011a07c4a090214491400c0b030804c40701090850b40540 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 745723453 1250 745722203 745722217
    0x5030c0a0e391e070507050105030712060e06100e0303090405180f01050a051602060c160f0501021e12012714040203011b23040f06020d020106330e030a08 68
    0x4442c00c080d40c0c4500c0300f0240b1841100412540003054104129070159000e0740e4461401e0a003903111030041d01219048614607040075001c403005000740901800c1501c8150540005420521002506c000004e9920700405030014844c0b034480000442012501600c0342044001904450364903c44920307082c041c01084412801d500e26180004925224200d1703082800c5505801034039250b1151600003103d0750022602c20045504503c40000164040c91203581890045000684074492249440000c3d8000050010002000c0c80000e8600140e02002811100100304070706014405058030094041203001980aa03071820b030458403000b10001c4114803d13842140200403d8000e103c5010741081c04821140000b0700c440038803084500a41155010000c02080180c20950b0700e44002a03004010b8010500582242e072811030115024004c80d8068105941ca14040c40000359040421000380c007208225841e07040360140a441c00350035214220750024064a90900c0175050011a40d03200304 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 745724703 1250 745723453 745723477
    0x50303090105150d0f0308060301110703090e0105010503010302330403030201090c061805040e0a051c0305090106140d031e0c031106160c050c10030605030c0a0e39 72
    0x100d1050911300002107001c100d070300010708010355541d52001ca64140000f0081e642540da142ca440e00c0c01040d0703202902c42c65220380d0b18641d140381003292749118160107a02c0541030040502c01403006a460b14035003106402c03044103a100f05ca80d107a050308107002d415005007820610025000c001e040d4107400c1b12503d680109083d105891782d4060840340310010708100c10725000c0c0000d00f1f000f6031070503400641c1140c000070b08684440c1c5035a00c5135410b012050302c881d0b0f0303038002c4240b1182034182c01d401f80c41e034090041c030003c021a51a0180e18840360981e000024440c0d49100540402c060140c0c1110b00b00040800031940130a00880014103100b4011030141d001c607440294840b0240e05c0001c05034429031818103681d040c0040c0c40015100154070a100711000e0194100c5101c02d42c0310803c200300d9001d155500401c1452a0a00789070a080166080c940203a4089130140030150b61292441e0300002c0c2280402a6100d020700b040364449040e02201031480014040300d10304460000280c00743e0800e070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 745725953 1250 745724703 745724731
    0xd050a020403121106012108040e0708180c0607081b010f0e060402100c020a0305030a020610080615090c090612040311070810051924060f1b0f050303090105 69
    0x1550301070301c410303132180c10a812a0380f18000510000388114041401c1000a1051200310b1f42140d5580c402c540080d00403000450a18007002501940614196000701c0b0249115180003550fa4049494800450105000d0440051040104685081140c45071140b0106013610741c01d2256103d4068000f002c1d40588032070400002003041c900202d600c500455009141c4086142c020700141c41090030752070705036801007180c200000400c03401e0004100c0011030340d0150241c2d01e010100c20b02007000d2a00111020340c003400c20001c42504008000c5424a41211403c010355120401509584079011005410003004070700002158081d02c580c1d8016442900c0d4003109a54841c14107940d00b80d0752144068903804180e1014041c401580503540080d000a00f40d000080d0580500080d25000c00000c0484101d10241e6a100e605880e8104040c040c0f600e0325828021525000420441100c02d03481e00042e0451750314030030010b1091441c20020350110a84e51079251542040b4000c0804a550696102e18 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 745727203 1250 745725953 745725983
    0x50f0c040204120b040609020a0f360e10020732071e0e090a05210403031412010605030a0c0c0320121909080106030f0807080d050a020403 61
    0x841d00a032015901c21000c3d2030014499501d551100440203441682c15a84e115070312000741c2c0720641d040d4003038040c08620306050b6140c2503890045242d08900042032414040c96019071600401c20710050102401c0e000c00c0407994650b085003050079501c20a1781e0184001140c104000803a00d0075505182d100003440c120034250341894a20040044013028244c00c5110180f0040707402c46180e60050528808000c17400f40ca50201c01462442600c83c040c0b55480f41d0055800c001040050105d290322580402949002107502c50719140281c0c00b008044c403491100721600c2810301c10550b405440da052000d242941d4520300900390740d0042d070725185a103003071000c40c0402a02600540300c00681c1070369184070306109125103052402103034030b07109003034020201200c900d05e02a1020300305003c0306480c0700401c04440381c4050840c107035a41c0020500e074107189041022521500305004d1301030f001042d00707940b887d0514000e4411300c101c0c40c48030b54643c540000d100103444154090402d030b91055000e0071903581 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 745728453 1250 745727203 745727209
    0xb0a0306080f0f031c1e0b0906120634030605130e07181d060619030b1617010605040504140f150f060706020d11130b0906040302030a050f0c 62
    0x1103e0401000c42d6208210080c4132001203603d004220700b10141c0041c280d4520415011480225907200214540303416803480349241c500007850704107404640d560850810801e0580d25004010405005502c0000309403400100c40e007014007e20624500107802048420700c054010551406544d001e03c52131a03041e11910324510403000101010f0009085076864503054401b40300c551044100d215803612840304070301004001c108038015030032028109074500041407281d10841c2400710359a990010b1001c002140b030062180b6040103201054520346583c0030303020b95000071020740f4a07485121031700000580f00e6200d0041c2050301c500326403e101c04035514110180c44841612841c46000c84400410180410703258000315145000c0d00f4440344001403000640e058115007400e44c0c90b6900099019420080c5114118034600498211824045200d800c2e0b410500b29005424030080c0c00142000c00d0b9403001c041e0703401142e0040480340034001520f0095210b8274050040080c0e803040f001c0303401040c6 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 745729703 1250 745728453 745728463
    0x150d08030103140c03060f01050f060405030318011202090927060f07180b0d150801060f09060501022a03011b0302130503030f1213080f041401170a05040203070b0a0306080f 76
    0x1804201f0080c5d08240070401450100804160310003030800c400111503e040c8068002e1040091801c82120444000036011019213202c41d092148100000001c0c3e90740e640c1c0d442d80286000303504050109050010841d41202c0411441c42885200d080050341010700e42c110f4415000c55882040c003c0c1c204444050b2207005001e003440d400018041642d4403480d40d44600044000b00202d803402c10f036241003a5003100c0880d0000d04101d03075100801e229542860284c040102004e100030f080b41d400c1c03040c00c02207040e0285280104020318112501c1c0c65602500400c03c01d007001c00d4501c0760b081c0e2076a0060300a45c00035140c0d1070480d04810300004e00d481d0220548000c000100300e0a40f41000200e02e10151b100001d2030110301c200b5501034030340440d10110203050f55900c135240055481e410144800d0691810341055030412040400f06103c0c42000c4510320b402044910f404a09611144002410060b250300444a41c040c049008205907034182c10035421901c00506680308000301064060302c070 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 745730953 1250 745729703 745729711
    0xc120403060c170103020d0f060509030a0e060a17040507030b070c120306030206030c131a040816120605150d110a0e0105180705040f0b041d0f150d08030103140c0306 73
    0x10305510f80100090b09048103d962503603c03420304580d42c0101540c40c04100c81c01a200300d071140e423020910f2a0302d9500101504c21243d41151013905080c18064024195003007183d041815040c900c0104041100c1085003001942c1d03c20100805450300c880300500442110109440c0c800302e802c0900c100c98028840c0c8410f0300c0c0c015112a185603140602448031303500011000034002900180000e40c0f101412089a4100c003090320903566502d0320860902e805013403d0200881072070300310104070902448480000f0035610207070106955540310503184541e08032140d5190845c09407002d9030108114a440c008010000300d0f248455151646a04d0840b075409020f96500b00340c0d050f844503a2450351001280e4828498907010746000e456480640d00b200303650344030f120b2154001c135080c000b5007548840e000c110300074411aa161464102d040264026010344802c004441c541c0d41c140075915511680a80241c00c218400d5595a507490503e00c0d192028208980a00400f141c0003214940801c2007401 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 745732203 1250 745730953 745730987
    0xe032112130b04061d0a1b0e010e010306110903030a030509010c1b060e010b0613080c0103051611011503051005071b0303111201090e06060f060d05040204020c120403060c 75
    0x990743c9540d8080140016510880080300001d840000c40d54100b05945c4980d1040e15014046407501000a1041c003880e003015491001180041c40070752101061641140d0300107001060800380e601411000d0f101790310400d60035000c0040c2009400da0990400b502500d0800c0c002c0194500702d86080f94001685d186500f422180c402c80d03080801d505422040c05549900c0000480d5200d940000c0e00035440b44488a00340314a9501c20890807800303000348015a4801e00703040c0300602d00034400640b201c0650181d04103220011101442c0f20340250f0006401925800c098946a500c0e0300700380ba682c410441250b1071960600000800c0144201c480d44428030310003400c44400f035803503681030b005011045000c030140d04007803104ca203803102c400e00914002c1402e00400036150f040a0b08442c02c0c900c1c014a000d000744400c04a003041510b503c0f0480798018454038000866480b1440020302901c51031900d8011481840682480380308008001c0c0b040b00e1003400300f0024080090710035509480d04201d1000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 745733453 1250 745732203 745732223
    0x6092a080c09010521010e0a05090c060702060a2a0c120b270d052104020919060306090605061905060a03090807121d0901080309010e03211213 63
    0x411035000ba4060205c004a0680040700100c07040c91140c4034150990080807200417190502900059500ca1182c2044140006d801d408000b100450b030300d0300c108103000307005080004100b02828412030f01e10001d8940c4880051a580b100c040d03070a900d0210400030340310b60070740b240c00140c000b1100124100490784013501e0521031781c50081d05070489040c5802008801007104d809100344006100c1400381100c65220340b86c940400c80d00105512640074176140d240b241d200c05110259403507003002940003080c6d042c0d481040707912800e101d01601e150340c00180042c3c20442080100703c0346400807071181c074050720030b61001c10080d100020241100e20489400c00800c000380400540310b50844413501c0c1c065030a0a09d0f101413503a9101c090f1500c03e25540000d98000c0103d07a031000c0c2040801c50000040720098000e5043c000c819442e40302e0021030300d040c0822200282c40946003480401c8041803281e0069000380038a02200480fa400354812180405002001030800250b02009502c40e0f504800005 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 745734703 1250 745733453 745733467
    0x170318070e041e0503120a0f02070b1503190c060e03060103081806160c050301050c0a0210051003051b0a0918030c020f0d080c010f05070c080d06092a080c 68
    0x440400e81c03507000240f5199611154004980100020481d46100142c14401c0b494144c840000301d40d0041a84002c00d8010000078001c1041c00c0d046903000362904c09880b007036a814000013032600b2003420907a1000e0035a41e82c0d000c24010031240c984100d5280c2d031540b01d1004440340030551200320074000180300a800b0b000851030a03201000206c0680c070041c0036a072900c00140581c0582d01c9445004855000450b00c0501040c14203000710358010086403106810481d010101039164210450800881c170356a400190070100c00c0700010000f107400001b610152481643d80340216103403c1c0c6440e002c0c1c0c003204400104001a88030301d0309640d0040304446035280702940c007140c0409080390280da014150007984086070307490b480115a401d204810303043da21914403107200d0a441192410117046441d000170806800c0d00b1040c44151284d00160007a0340303a0300720002800034403164016070090780c504112102c66180c0030304500c10b03170402d460320141048080c0400300c4521000700e82811a21342c00b80150 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 745735953 1250 745734703 745734713
    0xf0f0618090602090402030903130527041a0408070303060608070503070815030d02010923211908090606090c0d0b01140c0102130b04030c050d0807170318070e04 71
    0x8168160b204840141c0351154160010341607030401c1d0b441e5006600001034140a0b0003110f100c8a004004c01e55034442c0c05402c0007807203001d402d010504004085046000141001541c062004100e0481c4044e9409401c2904181d0006d402031101200827a00d480c8020a150b8050070b40b00d841271a80b03a0b1041e01e180c3d1404801c03190160003a0051111512002c0c142d0b50b60341d0140324021440c41c0c543e0000458100b1410403445646011042c02c09628001000c04003a150104803400209120b00c0c0b100780e04000c10242840718400d0a00b5410344003514100100c1080e4004075007030207200d8003011988607031549020002c04507030640e00d81400c0c0740100056039001d02190061420b00720141009100c0f45840716064155034082c04400485135800500c1074040d952030b140d00f002070314144260354241030444e5500d041005c294000e892180c0a80d84c80c407402c00c00703240f0488030300c20b030b00448916106104000301e800a4005807a4044001c041c0e00100c0d1180c880054540200c5a102c00d4075581502d0f10f03190 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 745737203 1250 745735953 745735961
    0x50c0103020d1503240e1905190b040b09160e10080a080a2718020405030a0507080606040c2f03040b0304021f0206071d030f010f0f0618 60
    0x31280300c281d01c50200310403c41d409090b0030010350040280c1d20030701196840c1030781060f180401c2d90090707070b00e80381c480c0d2500a000620503910001c4130048440150160409901d420505002c2d000394461401e4807070104000451000c1c001e03485032100800c2d94a651140544400b2401504911240b03c0c01c000c101c40343c200041c054100304408001d010345522060ba460600010704000d9860103000243c1c406080e5102d0002a030000031b260040c10b0349001c0032080c001c600c0b42c0384100c0302e016403544660001c001d215412074004000050484001c0107040c50005d440c0d1142d441030719094058400011901d0a05006090076030100f66a02d0116181c11104039480a81070f45842e041940301c01d41c0b005051b40100010400342c00b4411580781c480c9080e01c1000004020413072580403d6640440061032290001101500300d495420101c0c07245010306140c61076102d0642c141e076030610401c20709039440c06040d40201500140000e0902040901c6000c1406941745c3d44211280005c00b061501403108441d80 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 745738453 1250 745737203 745737217
    0x105100815060c0d0c050606060306010c080d0f0c020c010e190504051302031e1603030f05070f02041a0910030209070f0314010b0318010b01120b0a09020f0705070b07050c010302 78
    0x41164100807005000504d0a03c4d180281400f080c03c400703018061100420000350710240c112849450f600d4200c4c0020b19420011900600d018008203e00981c01916000070140c041030342da00700030303425042d10000c1d0f80f0580c0c40b04c80c40c00b10340429211270003070910301e03850b8444020300c07041040894641800c1c003004150080c0045441c1e014503499000594080c000c0c51300d940d0381407052064002040030300b6800e080303101084000d0350622000401c00a0b0b0840318100c481c040f14140300741c81301010300380040d100c092514001e510a2810f01100c4010124010000c07a0303038810760f144c050698030030618000c0c07400305001c081d42c0540d0201c0081d541074400e680c160300100b070780e180c0841d101040a2030016040002e03040416815804010062100304559100c065220018024459081d00d0000a45401100203100f148036840301c5218006490f07400a40303000702052003003150740e440900d2500c0341c00c0d0404601104e081c040c00600080c9007034002c1c10b4a42c407941003009461402d0728040150001d502c004 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 745739703 1250 745738453 745738459
    0x515150706021b1e0613030c140a211404031217070201060501080a0b1014131203090e0c09060904060b0304111306180f0b030d03020901080105100815 66
    0xc04501094042440186481c001d005041d603030a1002011314404152080300b8440d4000001c0158220f0480207100a2a815007040e80300300807a03041201d0011141d0082080038482ca03240d000800074051031001c01451f4060015212610110b4220b50380342ca500c009801d0301205000c02c0c008034044440e000704500990400070500e124010401c55600c030308490380c1c800760b50f50720001c04ca00d58008801c158000d035141020005200900002130f00e4005d0010880704000035144490740000204040700c136440c00302c201e604a8590b40350400080c00480010840c0080c246460020b1303a00c000000050086904500903418044e032039080c0f081c680c0200c1c000c03580c4a52a00400a801f260040096000d18052905030448041d80424403d49100422440081c036160542c00c0018103408162260302140b03c0c80041344140251442c0c1e40540100038010358540211951070ba0410b81642c014112003a007078072030341d01907a80d0348104007403044c804800c0d0001c80d071100c0006807141c00c400402140a0001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 745740953 1250 745739703 745739707
    0x51f020318210c040507090b0a030902030c0303121608010f0b0d1401181d0721021f120b0901090c0306030804060e1c05191103030d0c03051515070602 66
    0x6007110044403a1003400c64006030400c0540c03e409051900a196101c0e0250600842252a2045174006842002450420140d68201500855800384981203801034010304580d12031840841035448241c06803012500d40d1002820602450300030002c0305c0c100c2e10104218420186003040035481d56000c0b152030f100355940c9091461980d020446000c0c041d040755010540004800c40100080302c01c240d080c0418255002009000f0781c03000a404c5040d46c0c9210501c1c06c40d2440c03107945075408a01c0820007584044200e505c140c500000f880c030160041315070741d60190540d2140d94610212032142c0195a040140e41b401484424200e80245105806501c0e00040c3d1680e603440c1c03080d4a41040e00950700103a4055640506890565417000c1003200c07501c0000c0a0741e20580d64155a600c2d440c50030312000030401c506806000741e4a41c400c26030080074094903135601440725800000c014010403107003c203140c44046a80d10000381c040b48007400d4060503000114140d0104110703107803c4100120b0303a154003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 745742203 1250 745740953 745740979
    0x1a0d0311160501020d090807050d0618030305091506090f0702031b0c120f0307060e03041701020720010207060320070f0308090d05030606032e051f020318 68
    0x40150300d0407803440301d00c100261801c1500090401285503004800c00070146014000c054020400d4021903d00316801030580016250000181856100c40c43d03101d400441440181030b0175400051165200030151495462480c0b090580c60700706481da9078005402e0400210482c4000c08019000902801140d0a15204e070700c0c25220800c4900c062003154100030040f40890038207103071214060801d040640007044108004a82d00e0060080142800e91103c04a008000c401c0c41202e000d4010240358503c11240c1c460307614041d40c05400304441c0200f0520a914203985032040c0c240359280c05174042c1480903e0034000f2809400031041108080c1c080170804003031160340000410b60944540d501c8a41a1750505025000384d400801c070111170740240c80300500803940801100d5010400b290415100c0d11603d0704054002d4040c6415400000d0b40a0390071041d011140e280d10455404a600100c1d50410380c50a507441c5a00b1541d1102580c8140854174940e91868070360311750354101819000070124 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 745743453 1250 745742203 745742237
    0x17090c010c150f090b090714101e17130807060b0103240305060c03133509030709020406050a05070611030f0115030b1e0d0605100f091a0d03 62
    0x303c070340f4004043e558034042101001402c03c481a4000130240103040f000b032902c00c0121007600841115403180301290b903500c59050041558030300c003101a102d102601e40b60b071140901503140205a4848010081000800a0303100c400c14510b000c2d800481503042216035910400078049500126045c9034495031038001c0d1040880c0340c0034241e00a000a08142032541c20a1804c088015081c030084503c108101b021035083c4030b01c4c0313543c2c40f81e00248a0ba04007011200c1e904024484440482e80c01d100c400d000c141210b1b11030003030490326000710155510a030743c84603808100d200c1c9202c2c24021400500400d01d0311402600900300c0d141c0a0300011452400e10000411f05502c105c40c40000c400c9040014002201c5018038241c100426043c1005800105400140254061a80701e40406843c1c500c404041d1184650142c1c1e03180d01800130701c03c0d42481111002128445d00504c003941220b2080007a00d115140600c005802e00c55070131140d2500f40200b40100307800780c100c1c00e806211507040c800b1400c0d0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 745744703 1250 745743453 745743461
    0x115020c150a08061f0e011205070207061107030b0a0204090c18170f01060305011401060e01020a141f0c030e0106050d080304020612090307020a051215070212070f0317090c010c15 79
    0x41d00c0d80e07286c09400c0c1c022000940040c1c0b007175001081d4180740c01e041108080d000214407050702c005041080c071060b00c003400c041c0340181941008055403459418401d004003590081c0c025100103260501c13031019402001c44182101142c025001c580500c41000004001100025940003038002d64070b020040740001420b66090794012101a0f43d036000d4641d02e0403083c42810b001d0301c41d034038200c500c1d400b00e07400013990340c240340201410f0795100901c0340100070740802003100b0107001c0c12010001000c40b40b0a400c000c0c40c3c1e10812101013820420303003011600c4103105820944d00000c0c14402c8095941c1c441221540004200b02d81100007003100744145848113040f60b100b000385400441d40d591692040c4040f4804591000d40a011034010302500c1403070114181950380041d4510401035501e641c000c92510502d224000b2420400040060074011280d49541000380a52102611281101c06440c150103080b15000c18039000110803001c030b0740c820960804c2c2680998250340c010402511414115 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 745745953 1250 745744703 745744759
    0x5030a0e1b0a08031c151203020703020102120c0a080d0225061a101d1003050901050108030c0a0602070f0c090902240406030e070306050115020c150a0806 68
    0x5030701c0542000c0304600c0d00c181184042e02e50080518142006034130b6907010042c2c0c00d9034007901c840d283c025114483c0c90f10890f00005000504880152503218200a5101e070654007080c0c0c018001c640c21291006e54074002c441d909404a00140000c500305d03258074100b6040a0180c1c91110340030032840a0720b5840107065400c1d40340305942070f500310441d880c0134421180c000c1083c2000025241c0540c0007030799680700230203444134135050000c80e070920800b90144101d20860a10f03440000c5500403408542d042d031141d80b00384400d40c0200503030f980740c91841d83e5a0141c91749400c5035602029030240051010380142040328451783c00c102115005a50792400ca98054112105c0d040c0d031004004154a05102d45040e140c9030750005da42d603d2014900d00d200c1d48111f010718000d040d200c01042d104508104100c40046402c00300030000d55854114191554170311410241c01403140704503202d42850301215254100c814000c8403460410340840503903000307200401c1194000c100c84c0741101803460780e000810003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 745747203 1250 745745953 745745983
    0x2109012301060314010e040303020c01090c18060f080309011d09070c11010e130903110a0f05061b030403030c030216080a1202030c03040609080c070e190c020d05030a0e 74
    0x1542c14240c004084420107003122040c096000e0040046003076940c0d5190300550145400742c0d8441002d0a154003602445070000e2010802d40000924080c0076045024114103001040c446599551040304240c520b5000311012a001048441855070243c410001c0345103608880c4004126050000b42c1c40010403a903100202c1c40c88040d03507041010111130300e25010400d09004900d00082004211218102144401465520f00c0d00c0001d260140c000181d2041800b012910503441e280b8181c0a25449a081203a90b84102800306009121407480303516000c07840d4030040d06641d43c0d40c404402030080c1040e08401d16900f004041000885000c40001b598007070940c2c2c2e0380d1800c81c490020a13922464820050f030501c18070078080000281000c482e085030704a00c011540f42003a091000c1c1e01d100d240354108a52049880004552041a80c0903100b4100760150701708181011000e41e040d5002c4032031500c01070308620112800180a00041c54100301e01440010302e9001c02c0d400c2502c0c011494103e800 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 745748453 1250 745747203 745747271
    0x3020310171e030c061503030c06150a06020f0309010810050d050105011806030206090f061b010c1205070f08040312111209010204030305070f06021c0504050d0302210901 75
    0x80c2e00c60481240b180c00000040218581244988500e4541c20003a140d120a076aa189a200c0d080e40d0800950b005550300720295952420001c031852012070310061540d00031a40c0c400c1c0003c0207400070035140100c0c1070420155191011907401100e50010040c5592141015408042440c0d11003004511040740300f83c2c000600740d410400e00501545520702038111441c02c101051005880d5907041c0d40035134800391586100b01020360300196182c002c48803041c0d0204003012980c0c10242c0150082c800500341500c49030312030319500a2040039140221200c4c00480d0340c8459000146116442041d070160003440d240308040054601c41054032001c01d140301039594080391201d9401481100d250700030608030000c520f8185155405850350042800c0544410103402e2000d040c45265011980015030700c44d03041b869160104000b030000c007015035050300c061181500e09404580a0b100b2500c030303400010200302070724100c490940a01e580c01003441040307540b0313240c010550741d400f00c1c0340c05904e00101d54001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 745749703 1250 745748453 745748473
    0x3170f1804050615160c150f090b0a0504050d060608030309010207050714090c0c0109060609060305160e0a021606090506090d03110301060c02012d0e030c100302031017 74
    0xc0c2c0d0b0002d00450320404448807200c0c0881c00c0c1c00d040381c40300000c1510101c0700b9074035801c0c400b008903d103030300213211400c802516244541d030224020109640948461300030039100d0382d50204900034006400d002c19410001031019207400d420045071b00784109030115040da00d80489074110742040e1108070180e0740101e10201000024071640002d4404006204050210000002d03200390015000b1404014001810350303994000390049510123401c01c2082c020680c1e141d00f100014405407006035414001c0c591001446c00c0342450385030032a111a880c1000c151210949030700294018925501c9500e504100d42c00007485500030340c0d045c603005801070b0581e46410b1340f9450900c541c02c0c212004252520b000000c4100450007a82e0644029140c4106022168801600e80c03206034070301c040c2c140898500a460041d550724400b07000d081d0941d51901242060070078036503200840000c859001c040c80740d81c240124829400755030b100c01000122004640d481072141c42c1c8000021386000710360030a142c04 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 745750953 1250 745749703 745749709
    0x9060917030a0614030d03020304140a050715020607021b2202030604110c071e031a01140103060503100b041d0705090606040302030c010e190609031202070503030403170f18 76
    0x110001d00c0c00140d821602d1290f130780041c0c0c444c403620903c0005d059011001c2010f10840c240d00369460716103001103c80c0038109007403c50792280c50340b03c3c44000100005191450300c4c030104100340510183d4004141c03034042410943c00e1020710211190300201d1042081300004640b40d0b46500c0344070b50810044c0d8a040c00400d0009450444102400500d01040f80e08600000014660b00300e81d4803044540c50403003510021811400d151f8030142c501081091107480440d80e0103591030490b1541c0241d10b4010300080010b40c1641c44a1180c6a03140d0454425000d00b03040b1a0032071140f4107801040000e0201425040b400c182080c5c0c0c1c038003c2254843d03001072100741800340410390004001c540c15030030700385190300080d9100007200d0031504022840c04006006d45039483c500d1010007030010801d207100e4445800030000817a622064a020314030900c9800c8550020420005031034018003d145001d0440e19441513414080003d003003c0b200403c03141c100000003001402009002c040011011440f030810 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 745752203 1250 745750953 745750961
    0x4050403180b070b370b0603070815010927020426070f142205130b0a050c030105010507030e3105090715090f06080601080a05090a020409060917030a 66
    0x14100c0c0303c0750641c2c0100790f22a20b1042031724804104028807100c3e0003288140005004030780081508904d011080c0082c01d0b810050305440f801c4511a5800c06290b007000445942170140709441d940c0c1800d02c14901a0407003140c0301980c0c510b4000d405441c1c9a03642040e4140d0001c1408200e0403d400c120110701c20607414041c01c8010b12403904c0985445040c00450840640e00500191040c001004d243c0640b0500e80c0d420754940540510400c41032401c0080b404046014030307807c580c189010720000720008900e00c51203008024801200c0d09517802c1200544150788014001e405004818522180b1036031080320f2503907a05003195451055280d241a0300c101140030003c800c805030700307050812a4003035002071510200e8101451b04640d441e84254261110149031f00308848450000c100800d4841d0444550340c00742500780d8909601c1d075100740c000c4089071000c0e640f11440f0781050035031401624158105d00080c0d400303208000b8540d07126959100d00c15490b40c0201003180340c04070400c440d01c011446 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 745753453 1250 745752203 745752211
    0xc0d0b0312190f05120a18050601050a0b16030e010504030807081306030c120209040b0a140906031b06030c12090106180212040f0807050703050c1c03020c04050403180b070b 76
    0xf008141c400c0041c00144c490b014070504943c0c4403805c200000c628400e6030b0403002e0b0000c3c0c090945495000c00c2c0c10400d0f15808240034090080c94800d100184881184d0300322900c100142d5501804032101d03540c1101c203250300c1010241004010700010010441c0341004011051061644c1556411720304240c680901142d07000c8020315151065503010710360840792082c0400d0300fa820040c0e55072b000100107402840400c5115070000c00200d00480c4d00d4000c2d100d2408035a2080741d1140441d42e98500b096a02ca60b0032180766900c076143c15420304503040c50406903400c040c6a82c1100e0600081c0051074104c0d1030304136944603042c1e440d041d04000c040110540403050481a02040d442c04004402d0040c0c00d01d005031000300342202c00010607045c042c080060341e0300c155004007079601040d82ca040039a5038904184500d0303c07a450b4480410041c03a028545483c00c10350640140103222503e808020041000030004c0c3e060006144980840c2c2102e0324045014003900c8003441e484622a00308003004c0d0000070 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 745754703 1250 745753453 745753457
    0x4030201230a0c23030402030712170a02100903020d090806011d0a060305010221010b0304020a06030c03091b0806010e06060403170408120904150b030c0d0b031219 72
    0x48003200c4422610140550107455030300046400d10440004684c070840421500400d50200140030701c2190b500401113000794007c8040300d001603100d02407001c0d000c442900080818803a00f500040d044c9040024100e8a54a4016601611103615089080c0c1d0b000d09811030050300030885240e261500050110040c1440d9001821258101202d28400c2000b214020540038910000111030101c40e400c04405154003d0095441c0c1d607030382c40c081410001645110743d08240300c0002180e90388460060728420b54000b803401c00391500c0c000040d13005144503080a42019211401c140c041002403148076442d0380103142d071410b1a441c1004081c10000f040c0c10400e5003416482c20f111103903170340303209490580c1c0d004040c81c403420504501d00da58610403030784284400d000381c0803124071802c40030020b44004030058400380114111800030b0344c070a01840c0540008a40c040c0045861620a003020b0044820703103480005280c84642c0000b8600542043c030204503d03000034030b520814003520240e080f0501d50f4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 745755953 1250 745754703 745754741
    0x90b030d3f05180604080a18080d020c09160c022e0518060c070b09031006120210020105040c0605160506090c03012406030207061b2a02090f0403030b030d02010504030201 75
    0x40c1c0d1201411707c59103420004000c12040844a00007506030707240c00606100c41103650b21440741402948414010005900c13861411000a078660306e42881d110181740240e44031b90721000365a08202c1000301c114801410390502101c0e022200c407405036800d80b81c000603128540c80b2500000403e41c03c404c18222580500814002d00b0901305000540030251b401441e021502d81c581507001c24681100004607a500c5410104c0002c0d06284841105c0e0032140242c0e070302031031f2040e01d900c26420786400340c0b0004c0182c0380e02034040040e513101d0400341c440d205100d03501845901440d264540307408022b9403e2107a03074010042040e0149000d228009442c007403140c036008488000750700e84050125502c00c03030b4203150b000144641085078651000c1d446944100c01c41d40942d0030150010450142c0f511070440340e009001c1940743c1c401c034034034290640e81d84c024040e448903030b20b044854640700c50190040b0141511100d141103190b03420301540341126016030000641780750a050003400d5400100d0398042480b10 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 745757203 1250 745755953 745755961
    0x61d06100f0b070203030c031803100e060a240603050a06080d1d0109120b090610050f1315061e05252a090b030d3f051806 54
    0x103255000c4202d51510b03903015214000781c0046419032140c140c4d0410540400503032404915064a0103041114042d41100d0340d0107510245081150051104130b0034a42c031040c0000e0b49070403190040600d419040102456a03c1540c1e5103d1040249402410202c0d07216010064000010720444004121a0008041c20750781244c010786415041162404800b00303244c056040c69014010303090080c42c85c28080d25003403441c1d081081190b8416182281d01d0f006040c0414014941201c041041d2100100828003504200c0e040200c41d50b814601800844e4492410010340382200c0c0e4071400410b019219400998041010a003e810801d640c4800f409414454900524421820341c8098051f0000e4400182014108001a0620a80d85821240c00403520482d415850b000c0e6004032440d048041c0103015060b002c00d82c6509540c200c0303d000441821051035180c44131105100100c00c20303010050400d0340404041400aa40b43c2d00e6000c60b603d96003800304181c252a00c0410016840d000ba10039810 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 745758453 1250 745757203 745757219
    0xc061b0201200906160b0c0904150614070c0b0f03011e0e01090f0f0c0e1306080d050703090b0705010b01080f0411060a0e061306020f150a18061d0610 66
    0x50f421003240100c601040e03030380c16125020540880035800903000b50585c80c0034040100c507a4800340c0301074015400c2001000b03401480c403400d5015264107840b03440c05800071030f148070710b1504443c006075201e040c1d100b070024507a14031380000d1050000c600c102564941c10300f800101425038910b101503031041441d20410086030507030881419510000e80c08581e16042d4030000c400780003210070f8803082d9482c00c04a0350080703030060011406c4c0c0c0001c1d41e40100f04a401034540048509501c160a1540c0000007500c048038490320050104034828200b00c60a0f98850354100083c1d0484501116a03079521148568503680001c03200c0c0c0d1201d401c0035240c00c04e1516584201a0041c40f400e01c0e0300905021072702c0031481e03004004044c2022406050103407100e042c01b1402601d000b9a2088d41c1c05130241c1441b21550700700220343c903174003100810300a40b02520750300740300401420308100c3d203020512280d0481b0000b482d140600741044514a9001021b03003000c5400c01d09010340903100818104508104101411b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 745759703 1250 745758453 745758457
    0x91323011505030408040306020a0315051c020603041434361e0e0d02060c0924030403020f0d170c070c030804090609021c09030c061b020120 62
    0x2032442c1c07a00301d481c3d44452410184c1401141c0000b445503001180d2285542e80c1648505070340c505c4080d1840c0c111f03035070f08244401c000038a901020b1424044104202608162004580061003444181002d01c480c0c010030742440c941601c0806d5600100340311008001400a41234103c240144256600628040103a00c010707640c2080f0440398180354248901030000580c08400c0c0e0f0140301418480c0300d010701440d0504022000e00b0241c6c8528205101c002c1502c0003a8800310904140c008040a454890740020540c101c15040360340000344480c400140740c031201c007090f003007000e49615a40300d041625000c0e007004c20242008410782d00001500c0551640b080ca0080d0108402190300255221302d603071000c7c54858404c026041603c107100000c2081301c00c4004004440000904004554131401c0300001d82c462200304403070701d40f01000041501000d40c1c0c0155016031090034008210120360b5102e0055483d00801e14441100b070454007a41981c0a0251108001c044030910641007040083d80c1c8144c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 745760953 1250 745759703 745759739
    0x30201051e180a1e1a0f04030503101809020306070311030c0c01062408070e131d060c03071103210c0f040308031b070c05130209132301 60
    0x410552041d0682d9444203001015260760012400003494500301112041404944412962800540302141c200b194104c002030190001824031052a10b880d01d084400c0e400c0905040001c90004400140990403002543d4030a00510300100d080c0915004142c14480001c02da6810f250170003071840d02d0740726202c04803a03010944480140d11083d0300780041d80180f5041d081004140350b82030410b210b440e051017a8425251443d6140d806954a1075412159400f92074100c0fa000840c0b40c0351200800b400b0380240340010703c18071400c140051041405031034264190360b4005281b8000080c0603001d58032041d06525640341c100254134000c81d01c00301d1180e00d880e034222955600840341c08280071442030300171680209555a0003070713181c41d207a052100d4241c3c0300f035034034000c1140b0a21394000a444048150b6800540210425401070b14042c148032007130032031007864060700354204400102941e60300314803c3ca510500c00c0010b00203000d5003203154402002c2c100707280200c00d640010442c0c00c1c0424400000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 745762203 1250 745760953 745760971
    0x50f1b07020f1302040515030f090f28080d05041502041a090d020a0e09011409030d091511031501020a02060706091109010b0a120c120209060903070e04030201051e 72
    0x243c2015048800d0003406141c01c2254016820099222131107208809503015420340c0ca5441080d840d40b60b516503071122071080251807900b02001110301c108440140e90319058140885040c040790380e40d1801c01d190303c0306038401203155480c0103110511902203510210040301900841c500350511b286415544480c85400750156000200c180e11a114501e00c000f032241d0140c0080365158070b8007040607a4420450740c3c03515662804010071f00003011501c000e4002c0580402840c5400309030203c1c44054490308500b52031b5000700f201e49840084a502c21940c0101803882020703100d0030121a24510541e144101c10b04541c020f24502c400b60b5290400c885000d80d09c010001070368821881d0140d111031111403001c3d48046403600000d40d41125000900d2007844e02d981d02850403031040302c8d2000302c0320081a8040050820054444d81c03440a47c010891180c2c02014681460754080002e0300d4200f042d001a0500c010310001c4c030040640901955070807a0318446c80c50056016000b180030300d00d10060515030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 745763453 1250 745762203 745762219
    0xe0702010221100b0c0307051e010506040c0e0915031b040e07060801050d03120903030606030b0d120e030a020d03030903090b040b07080d1409010507091a04050919050f1b07020f 78
    0x40f1044080088402c500d82c044242d5080c0c8404031a103200581c440302035148a2b50070034001884c00d14143c4103026080c9000d4662000368100e1070140300b00761100030810b00448480b4850400386a030108502d4488440c4948004030b003060f00300a00c019204000940007003030344014020301445400088090565100751900220442c080c201102d03018844103180000c2460000d9110078554103811880030f5800a440c2480041045014003221244440b809010b40e14044140c0144070320581c40c2c1008040000d04444001c8095000144a044800c404601103507035044200f0415030021020340c000e04607d26010b041078178100340d4160328410014010f1843c800080d03295022255507201ca5000c4691518010507450700d03007a0350b4002e01c41039503140c0c0030500d40c64000808100b00103409003031689140c251030600e460842400200320000e05000c0c02d04001ca40700c25414840361050350b01c10b01d0100031202c1c160034804480c00b81d100d50051340c2003071381c10100040c2015850b20003400380f642c6000d4034540 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 745764703 1250 745763453 745763467
    0x10305030d0c02030f370c12021504110406030b130303060e01080a030305060409081305120c180403090b0703020105061e0619030f060f05130912080a060e0702010221100b 75
    0x2d6680510301a001800c0c240701111a454030b940038924416a40c03142841803400c4236002c070141e079110141c101c1403070501110000100041c00f8051020420341300030300081030b015241e03076610400b100704a80c2c1002001c0611484c40070b15601d40200c0005204002d014420703541400b9075a0348640190f44060181500c1ea80403a0182e00c8aa11402c42c29070044082502c1c2d01c1700041c40b641422461003110322650f404c4500841e560004980724482c840e004090000c2d0301202c688007103400300003c0040d41800100707900000e01051000c001c00d0f010780700e540000b840746480006c01c8075058030640949071205c1c000c2060182c0351540002c03265840500c044d841c4143d103038071000701c01811404960380c0c0f8540c180500000c01100d4803c0180c03d50740e045420890841411804204881d81c1180141890207a0469000744038064800c440c4c015001420103e882c0351107454022a5020907101000140c1d40041c10815002070010070707001c00c031035000c110001c900700a461031030508a140108160000005009 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 745765953 1250 745764703 745764757
    0x8040b0916060e0f010509130504020a0312091703270a050301020f0a020705090919030c0b1003050f06040c09020a020f071d0124050a1205010305030d0c02030f 70
    0x41c91840841115a290301e5494020052506001e4031040740910b00354882c075a019802501510407110005e00180088480c11310740d80f02414020704181d8102c0040b400100125048840f01401100700307031160001e845c43c001540f150103010320145081e60700f060041a03500c140f0010315038001c0400c0ca054800c2070010310001100040700d584002e070305601c0050101101100e05002d041c80c001d03203800b45c8110640c1c410601000400455a8000c0c07078000e50201c0802001440d01e4000c040e009140182d034012051b90b62140583c0f0a50b42014048580c44c400c00404c03d0410240681c0d0200c41c0c064089030405546001012240f0700a6500b050780101d03800748243e01c00c110005100360307080116000c10307568110207141d00d1100d003a40c48059040c200042082840740099580c02000b6049580540340d00038021142c0e074014409090812956100d001716140d194011f09010318001d10107141c2d5004041816011100070122000542d00288041e01c1c0b10540700c815903481d140302c0d1880058000b000704035 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 745767203 1250 745765953 745765963
    0x20705011d040b09190c050705070512030d0f02041716060e0112020d050a0c050c0613020a080a05061f08070e040503040e0702030405104d011b0c0308040b09 69
    0x22103800c44c440300200309441d8191602400c0841985008118075000c00c40210b40a2182c940040c0c0030b0b034810602007005041c00001c02406011031400c0e2400c1c101d80c942d40038182d9003034145a5038140c0d0045000d00010001c0d0001c414021418402440040c40b00358030310828182070300c10b81c8240509120901840c3e401100d120b07901c0d102c4420215680e60003240e0800041106031040000e683c90100a102030750300600886003141810001400c00c2e684d03114090300b045c03501090482c1c21035100c4600080c850f4003003060800c02031043c005080d40d450159811690118020800c01c2d200310382d84070402c00003c0104186003907640f4200605801d5449007051352445c07165901c848008540501040400c69010010b0015a04200d44004400740103020841e6000420502c00820401c074907080791403100716943c1850070300356800303040c03c1d0701405070b184007035a240136100288640d44880400720a94801011451158418103102101450b00e131401080300100401c01011414a07a005c2103110400700a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 745768453 1250 745767203 745767221
    0x203060d110418081234050714010c0e04111e160308160c120806030a02060f04031406090303070507050114070e041b0509010c031b0606050a06020705011d04 69
    0xe2040c1d5503180b40c60410f40713039448408040242c01840c40410b0f500d04050701803007550b0311410312030194220010412890740140c181503500f0703c0010080000065116021740305010800400000c461016050142910701c2801e01e803480b41d0700d004180c510300c507105000d60341320b40c80002a8120079908040d0340c1440341f0692002407564001206200f0030150701040a601c58064401c8103a00e8558010003943c00391408040200032031050020072100c680300d03450030790b03112000404a42c0700c9101074020079020f038048280701103100ba000900340140a981c8038070303144030840e1400521071854008407031526408090002000c0040002c2c100c3c0500609400054406040540c0000c1c02d00300746001403d10340248407014025420f0000540700040c4555090780d070f4400648419140c420340c2c0300110758102c07018508405124415080c1c10380120514010800b02c0c1c455600040c00504207000c000224001c0e038400407c41d0711440301030000b6640107160b44080080c90305024940001d0394002400740c041c1c24 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 745769703 1250 745768453 745768481
    0x1a03120a050d0204090504030207090b090a1a090103080d18051506060c0607080a0c0c021f03090b0c070203010b06040810150503010f0c091208030610050c07060e03060a0203060d1104 80
    0x128010495071700381d07407042d40130314400d40856010a0769606440d041d201914102540b204452000614904158104030021880c6015154080321000c00180d1400300c217070804d445920f03001c07a0304660024548100c01c816100e4095074011601260382d400c0d5606105030004000401800100d42151604001e80d000c420070340d0103a41c0545403202c0001c00301c00b0301312109529603040c004490700b05406a900c01e140b040e0040c2425460044050300813031150400c5000c0400c041e995000880424804c1100314081d071918403140b0760320b1605004060a56244401c00d5118150801c01002410b5000440c070308200003068002c04c007680061070110300030a485d8041d5415500f052030001081e4410390002d14001c030b82e500c4041d403d0f52955074210355056403000041080f00b04101044d594a02840c0c2194600320900e407051901401041990030315169500c000040340c03408181407505c1c901801070903844400020110f08525042d03000400d110b1f051900900b00c40d81044000d0700316211a04150b141c54425 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 745770953 1250 745769703 745769707
    0x7020321190f0206010506070f02121614030d020715030506010c0204020309030d1401061205040c0305070806010e01060513120c08121c0c0c020105180d0b0702011a03120a050d02 78
    0x32900a0b009555120b1000014040c1d0b00000c103c45c54107200f600c0d406038100b14104402c0e2440e500748910a2404c0400c00143e11a4003503940f0580c0c0952141009404032a0125901203045000d1524010240241d80b0a54112010900c003040300c0c1c556210120090b0314010410b501e4000c010b1703800b1070381d65401a4001d4000400c100313a4050000091541d8094a04100308448642c5100c82c0d40f10001c0c0184800a483c0d43c1c0e4980000761181c0050f500140100c0f064850300d6940d594041c1707459059884041e141d0072800040145070000c50300940103001500703010740f800390a200c2d94030790701445011f0912110000d2410707505202a110816014041c600111218402c0c8808800d40c1c0f0b402448003c285114600390f038012444044c0140709554490340c46120000c2e080d5401074680e81c0107015051001c803904c030317080303c3c00365941545a2000c600807220400ca03400c02c010005e0035200390004405002d43c00701c00d00c00f4191400105092184245007641ea242c0001000840380f81c4140003034244040c0c00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 745772203 1250 745770953 745770997
    0x1704080d110306130b091b0c0303131502070519150e0304090b0a050f09041509060203060108010e091e0708010e0106090c1b061805150a0c020307020321 67
    0x48001140160402c031560300c0c0d1309145440c0746040c3c491240e0925040b2110002040e0490010b1030300c150204a85507c1c07134100351050440c0c0780755400464100140250301c524601c04d011192014810103440800d080d46841c4290704c2d1180d4a01e08103200c07001c0c3c4400d681e6144d003488250b800b094a80d1491a80500450244800455880d00a03006809511b80340c115454101e00c0c007a06004102c460180542c102200484100544d8287c020410380d00f41d040f417048042c3d80c02c081e10905074941c1c400d500058989c249800010016081601704130340e007a183d802401541540010f246005448520064a0301405550f80d2070501c55903601c9503607990f003025001c00160f001900900c00303641d06614108a80780358030300100d96a01d0541525000e2003c8002c5110205803503400050300c20342d1500740444140019038480c2c0c5081018001801199142030070702040e070105000b036907410102c40c030045051074101c1c0c00094440c81d203200917050302c0d240310482c00e4507090700905a03400103100e00d6000c1c43c80c02c0307 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 745773453 1250 745772203 745772231
    0x170c0a0c020f09040b25090504050604020c030309060106080a0c0e0409050115030506010810060f140d0c090b090a0b060a05031b0406050703090e0c09090402041512140105071704080d 80
    0x2806894640006500700701106d030b080181c1b10a02145080d80d540c3c1a8154a09402d00004140203031070650801c0d000c01200c1d00a41040009500541e0000d00500666140420041c80000081c0c2540c804600b01070615480660007003800a2100d0100c9000440c08a146482d900402130b03001c220b100c060307102c0c000000b8490b0104401d4100c40300c140aa5007412818824601100c1c4039004150301c2c0f0646e408148800d20007000001c1128078042c1c001403003050b607a2119458001603900941e00c9948910545804c0e0503c0c2c508260000c04110060100b03442c03010010b9554055040c115003040f4020000030340c564010303d07600001e071108085099072a030b00d500700241103070b0000b401a00440c038000000640907400b492a90301c141d0004002900307110b8498100058154050410f0b03900a03115110380b00744028142100c401828080071f2010008541d2070000c02d01c100b4140c420550303925007800c01940700e411041c989c403500305164035040d4513510342ca801e8400340a801103070b07407105103841a0320039841 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 745774703 1250 745773453 745773473
    0x80304061413032f120a0f0303060b16021809030d090503120114010f02301902010204060306050301020414190b0f0315031f1806090b0601170c0a0c020f0904 69
    0x4140704090303c1c1c2c0020384100784078040301c09149a8486a1049011a01003041e0000016947e0f00c40d01d0045071348caa450031030303a800f500410740034841c0318a40403a603030442c50301c1d883d010161980f0980d030b0006450407141c403d440340101d80080c44260b4a44100e501007200520480e101030200c604044c0c503035619a1155100311400c0c100003030200b0003c10300c0703051042c000628425000704c00076481401240c9002014100c280d07081c0b14070310200c8148007500881c4156040899000d14a500060f1102d00c4c0060007400d0715065032105019034410441842203658400c1d20b5200c0060a8600d000641da200d4603e810190840c0d11208a0031000300d01111106800d40041d80100c1840c8034420984030b40404040d280d070070800801100c00006030f041119030050750000d00310721440710851003e4101c0340e00c5a400f0f0780d2180004580031500a82009565a0850b08071600540d441500c01258600040760112900c11050070409200f41500b03100c0031540e1360000d61520a8000d050718540341443d2420140031 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 745775953 1250 745774703 745774763
    0xf0118050625150e070305030f0d0b09070e01080709050306060d11090c09090c0c0a0f02031c03020d0c050c0706080c2502040c140711030705210708030406141303 71
    0x1c2c1010007404136107030009504400d49400c00c0186140044804d0b0010140d407004a120010607291390b00304003e0ba9030038900a11400300c41c0c0f1038120b0103081a00043c80c0d00030040c24041840a400c0c4c05119944000031034540c00581980d90a88041d40c131f052401c00022040d020580c0840c4c07403400c12003c000410b029008140090b070b0300344210788514140b841c8078084c500203500301d60302c540c90220103d103245508480060024055400b40c03001c1040b00e841420b00a0b402c0400300c1d030000341100740a082489a12902106407078282d0400544407402a02e40003d40304510810551801080280c0310000464000030b08410b4200c3c80c111240c1d0050030480f03d45403061340b1642c6022140c100c0c00d402454a4040e41c5080903201d0700d0308240303946401c00d1a54003403900c0d8161148000118442d2074015405042086020300c1c0c0d031300c59401d0030015203400c00d1504101c40c036800a100070040d15030400e80700003011a174400c10341e496111181e01c80c18100c0c110390002d040c08514040d420004401c0301502a10 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 745777203 1250 745775953 745775993
    0xc041707081506010807080417041d01120209060108070207091b0809063c0403020102030f160c06020306060c160603110c0a02010806010c0f110f0118050625 69
    0x6207002d200000b642e0b0850407078141d0302150f8420700040d0311500c11202c2031b80c000d2113920048a4280904100d0310250003d800604030b007141d503e0340890140c01e041055004050328420154001c0566006c284030003006050036051010074004589514024424500039055003c410410300f6010000090300302910285000400d580d80007061440714045000780c0b040d100744081038121800000c2d00861100c00c1201d03088080aa90300a0004804100c00180618029400562203041103050300a0001019016040c0c18090901c201200c0c0d0700f0150000c01c140c0c20020040c2c03a942c4100c0030501c14890001c0304022800f40c4181e09200c0070300001c02e01c00307444160341c0810903441c1504080503644201940c42c0799a9122a2030040158071407821594421810b242100c0004242e03a29100c444040180450344001c14188580c07041c00e203007021410701c000920f0030b11f407048c02d0f8040240358044540038644c0500d1001034104800c403002400241d4040c00210f04039440940f504091403c148c00e0384003848 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 745778453 1250 745777203 745777213
    0x105040b0312191224060e0a03120516140607080403021506042a140a020703021005040b040b03010e072a020f1203030f010b070b1906150201050618130b0c04170708 72
    0x1450b40e200310786003981600080c011064403130a54844807814802c0cac01daa02c04000c5d042004600403c4800300072010542b01d030422100224000080b5070900c1d00090000c1c080089000810003c254000307803801d03440100390a00c0030140c90303550124014050300142c0c860030307101c078804203800c0c400300b454094030300343c503a580e03551059030f500042c45098400c1101003001640702041c10f102520b480301501107103419a050061900d82d0359070101c81c058019901040700c0d0140803004200c44140d90b5070484c1c0c8100c2500e0655288904100401403000340c802005078480074810b044070854681103201c3c0d02d0041c000b0714000070080e11288a55403a03200712000000c50100400001d0380d02480b0701a550a1a4030000c1800c0c1039031058020050140c0150703800c00301d10b40703640000981c0001620744040c900c000f030740041007919020003800035004000346000030b0442241700f0000800e44411000c003241d0344c0105000e06a403034002c06243c0b1070245801042000c55a084000320751400060300ba0b04442c02c4006580c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 745779703 1250 745778453 745778459
    0x40209070219150f1503060b010f090b16050f030403051605010f210f06032a0b1606020307020105010f0b0a12090819080105040b0312191224 62
    0x9031641c1808000c101041802e0031140700054020600c80085184418000350300022003d480c0140c4215400c4000754507a048814010700049020300031428800b0f0914011588074050000e042c0701592107a40a80303070340801d2884103c2e4413804100e804035000003c5440c0e070b41c0700080d035030784030b90151204135403611407009081c0c10314128900407811203e0507160360141660704202650203002000207a5041c00c40012401200c0b4136500c6402898611071900162490552a1110094079006c4884100041c00c4c0030502c8000c01c1700c000300b8107417012040c0d0b468894410440d1031408810035080104100d00200400a4542d41540024125001c486048074101d0f600c61030051144515080c5100050300880b40481030f5080e500001604c40c4100d6025181c10403000c0e50b000c0d807900901034007000a03041d10040205250030b02565050300b20840c0a000440c0c9a103000ea565841600b0341001c0f1540c481c1821843c0c0b44c024440d050046120820600c005c15821100b1441c280080c000180481c040c41004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 745780953 1250 745779703 745779707
    0x1a030f010e030d02030618040312051515090d152a0215100e070e031c0e0409030e060d060302040f0b030604021203041a0408071208040b0d060b03070804020907 70
    0x42207040410710301951902c6029a01c0300080d61004040d05c1e049155194002d1060700c0c803c41d5903114900954440c0c40503400440050241c55002d468400320340c085e00c01454295031104414020312803000d5420fa5109010700100708080c08404001d40424a66040ca001c2d60020350414149603540d074060718002c0c14001840710940088040d0301c401644968000304403502014881c1390806c031188061550360340d0b100f40086110808556181c0094a004030702e44403030808101c510800f1014007084007903003c2510740140542c800910740c920840d111032101050501503207416012210140c0707120740c0d03400c00c010303030401800642c44228041e918004140115030014800c000321214002c01501082d120383e02040007004034400300d01a540805c0100082c400001100c029401101e10900c9403980d25003814107003010f4140e4003c03840109005002000510800c00300c070709441d00340c100c1c25226000d80c00e658000742581e80111100000c000140030805030000000c2c2d104078800c0390015078a43e552042 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 745782203 1250 745780953 745780961
    0x21050f03040b040306110712022406010c031404120b091902060a030c0e030105130308010503010e070605180405011805130c06201e060907050d23011a030f01 69
    0x110042c02c00d0038403003400064217076040b28903641480ca040f141401059154055500c40800840001d0f90110540500210500040d00b0b941c22502c0a10f880600c0c00000190114030034600050400c4003d482030b5a441040005480180140c1c0d00800000465032821001003241552154031501c2840700701c1080134035119428204039405844c007824040d68040070381c00f030516103001e00140a50303168403102d1924244165845100d030b502c0517072a1000c00b41000382c946041a005036010703034101000710700e250720001010b03000c80f44140b80266413110500c9402101d0000310301300303d500038103100c000140010400c615074002e03a181c030000c2100d51141c5031880c0c030100210305e0040102441c0301c0200a90b9002d000b208001c01041030204a01102007200c86003051012000424102038142c3c0f00e0740100401c03c41964440b040d8001040001e080a0000b10a0000107000401031a800c0307021400c401715a642a4900e203140700000c3c032407024500100c00e0300040d500344160080c81480d840030042601401 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 745783453 1250 745782203 745782209
    0x30408120c0a0e1c0b0f0a0c0e0a2c1018090201020709150f030c03050606010203041409040602040e0a06050f0316090902030109080d020a0f030b10030f0621050f0304 73
    0x5440000300343d50010b0000b0f03104a05442d44948440308020800702d01c504000500c9030380322000c0c00007a03240101038203040310b040b01d03650001c204902e140e00d101038540124000545000d01002000840c00f48601c2810800d00030040d90402c110400744a800361a542071320083e00e00102e40004401600755061046414200c40a80180d0100a0800c00e86031035500079204001c03000c2205800340e480b440c00300c9212405500444903030240201c20003d02c41e060206540100782480034520b0a86440c5c599a001c0340c1c402800cac0d01c11201c0030302190820a8580c1103c000b00ba102100701c41c50710700950000c000709030500c2030900401e8a40c4086105203030100342c00107d0010170321501c1070142407487c584000c102d44e40c003c981665031000f0680c0460720041c00b03043c40218551016a0700c215401d130041118000710058020306080554850203540d8400301492401420301c0d001030501210007081000e4011907103c00410302800340b4000c6103034041c4000c464450301071000c031501b00b03200880c41943e0340b0441c4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 745784703 1250 745783453 745783457
    0x20105280c020115080a05071d040602031e272805030d0504081e07020d020105131e0f081603030f0210110d05060d03050a0e0114030408120c0a 63
    0x264a40300381100690040c04110480e200028144860000e1a0100000d6800912103075000451403010844104010300c0942810000b8035060300d4020002a618100980005c6c5100d80103c001b40042406e4041041c071034070740400942c1d081c200b10000074400c0400170001d40403071040044110f100f000010350709070301d8502d18800d040403040c41114400202064003084a85000411000c540140b5034003569009a005800c1141cbc0c076445001c441c03d02c958800c1c0303e0060721000b40500070150b642c00d40d0707210045070282001a560810001860701c0500141c100d1440340035a0754802d403e00c003401000c0302c09c0d034102c0c9482065482d02c801400c4d42da00d5032542154030301c007141c800c01d0000a11034001c5081070600c500480d402c108183c1031090542d60b41d95001e52000304003054801341d00b070541c050300703400031402d031740c10002465140c50041061182c000900d0501071107200800069204052145154520402c625164100303460249070715407018511215403080c580103d6824442c3c201214440403c40d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 745785953 1250 745784703 745784761
    0x190902030d14040302040504080408100b0a090b0d050607050a0e04151203051b0c100305090a02061606090602190f020307150609150816031109040f050d02010c020105 73
    0x1581c12a510036514000228900381071100000603203032401102c2c011403054200707070f0711142800e031454502031b607401c5402e140c02e080c800f4013180d9440b001002d40503100c0c030690205441c11090b001c50a04451800020080d22400042154040c0c2c8140a40b041e44901d03907402208006c0c44c41000b06407403c0c0704540340304204090302013069821078603007248c501780f1a003045800d02071100c1600303402402800ca20030381e640140769941194a081c03804007424030014141000345042c45040309a8420004074020b00603580050034608003070141039859101503000a0510942d100d500e0204042d40144d103415010310300200c181c441a502810f04c80c0c0400141d60300450405030f16403208052010780c40000000160707034410114a4030030714000c810708840160034000c05146400546072414200c1100345400032540b910900000b1401001840c900e01c0443e5182c50301e03110b6080120494005400003001480782c80e0b4100b400640642080c1c0f030036001134000f008036030b07a0604019548440100640c1c150059 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 745787203 1250 745785953 745785973
    0x3060f0e0601020a0503070b070215010311130f09290c0316030f060b03060118060212180d030810090504020906060c010e2e060f03020d0f080f0319090203 68
    0x4140d50309a00c40070501c104e0b01401d5560f15050300315481200141d664015410810210903010046603100120f6916a103000350701d5902d51598040080c4202446034801034104201c0340716030b400441d98485420b104004205840c5072014100c0328210788042100340101c2040c030f10001e0241a140309024150340145103030784600114102e00e104c0c4a0b624141680c4405001d4071090520681000e44602c5407919a00d041c01800034142035450070035070882d4041d4800170302800e41e000c14820324031110010400e481d0130142c8100136492850501140d0006810500042815804000075000301d6603e40304140300391b01d6410040946801b1a000380d001100070b004507502c0d090020042007141c1c0c0c2040005100c00c4000e25241c10030007094100c03009079040c191070340c0840f04001140d01000b4006a0301300107040ca08665001c480c07a5a00c4040d11a80000c1011803d00401d005a00911a40100a1f695600b20402e401c035541d04156105800700040c401c9000144009121b044071b0190014001e200c5580 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 745788453 1250 745787203 745787219
    0xb0601080c0c0307030e12161205100c02070f08030f07080f070b010620070e131a0106030f06140d0209091504231207080a0302251203060f 61
    0x9030180001d12000c0007000031440001c001e1001e8800240310b50b42d10795040307440380108000035220403060782182d0810381841c100c0380c4003c00d2280442d01116111001c8010300d0821900700b261812242aa0b6414449141142a8041001020b541020700c40c81013044e00c8001460381e0340a41d001d2007285410400121000c1100304020b48100180c002c1d42501d8049584c0c1c0301020761000317a00c008041a000c2c04d086000b0521880c0c15503800c80044024800f00f8900900300c110110082c0c00524140c1d914205207003402600c009031042c98420783e405060702c1d60766000c001c008140c80608100e4441c2b51a00110380100304400c1c0b115024070061006d18840c490b60204000c1400140101c00c039881494031800340c40e0125201e061249000312070720503505156031104e00201120300139641940d040340718044501100391090b1050740e0b0b009100d698036040d055505600038441c004603904e01600b00d00103800780c019070105001e5100c0c411010b92040b01d42d0200c05900b900c03828041e1001d1502c40c2003003405018 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 745789703 1250 745788453 745788467
    0xe04050613020609181008010e06060f030106170607030c03020f0730030b1525030207030f050f01060803190302030c0d1805070e130b060a05040510050906030a0b0601 73
    0x280020715080c60040d8680028248090030040481091841410402801b0400600400803d44080280800d40115407920388840004203020705c00c0501d4034000c54541c809500c50000b925400d1500200b201d01030701259500c0000310341c0400040d0621400610440c401d00a03580c2c44040d0140080c101240e42d9952003040f10601072601c1c1e4062101c001301120810044024940081e40c2ca00242c0d4500e0308080c08510b1034419440d82c507034102000002d4a1101c22402e402c0000b155400d001ca68074031350f240c100e091051b503910103440302a86001480901c40c000c681071a8000609008100071036440000da0746900614a22241482d902c21050907900c3c002c1d0021980300700d14009452401c44400b40300d104864900d076041c224031802d0080c2c2c1003045000c2180d040504510700c0b002c403851804414500903004440001031144440c1d0000c10700c4c175117501d6012800f07040d000704144110703d042e80144260061620801d0321501c82400494071394140852410045a04003907601c15581c1c9050064a401c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 745790953 1250 745789703 745789741
    0x15030c1f0210020d2901091a07050304062d1b0c0b0c0c0102061003200111010e0f0d050c070e1b19080105010323070c0503030103060b09010e040506 65
    0x54000c0b110b0305000400c441c4018488100f154400061140021040a100760100c2c2a101c90403070000414841030703a0404548422039000780600030300c0d007140045160b03060080040c000d1040c4000310b40400c03020342103d119880e500b500c542010130915902018003084152a1008012070242c4942c00a0450100d4040c00d100d8004c00b901088280e80e001409581d6201407001903e270742150200108070746e4103000e0590009030349003945075a181951118460560902d5038003d41c00c00c800d200d02120b900030321454070940c03480d4000700840c0c003d5061143c3ca4a21171001ca104a0083c030804290300360091042d107000c0d002c01c1e40103000c22814030300c020510f010080c20901f0340c1a4001a41140c8011045c02040b81c840000c440d68035a1841d940701904144043e0042c07414035050149001186044014401d12504490145450340d15034560541d4441c0d003a0101502c14000040088284107003904881521107040c0d6201700c83e6a0303140540c102c407040641c0c0040946d0844c20118a0345461419180d000d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 745792203 1250 745790953 745790957
    0x141302120f070f0608010e0702061303170708040507050303070b040f021f020102040312030504050a020d02061605280c230904060f0b06090a2c0103050615030c1f 71
    0x249000600703003900c0c21a0303d600c407064090b200c0c1c030b0034008990f11441e040d0040c81c00fa00010640d0401840203510346600815000582000d03806400615104070000650001c81d1640d45d8405d00340394900070540a0201d8054500340b00f4544001a1410000111008503401081d0f0045076202c640d12110404401c44059900c403044212506003090840840305183d0748a400060340c99240d898000002c20204141201385450541080302203035000c2410b501d9a43d044480d0025407119100140305400364400400c0d2022444031208100540050800e1212980015100007030503503002002070032801340d0b0000d01e0200007200803c548072400d1215071035001d2003005c450441301190003042d0444d0b400c80302590840d8440d0208115008144640d200a06081d06c1103172034040b2003c041001c00308035106251340700089400c020351450389150100304586020340100c0940d6540e08285650351000d07140d00d4421035045118404502d400660900c6002c409000e50501c5a142d4507101e000401c41c0c104002 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 745793453 1250 745792203 745792213
    0xc060c031c060504110a080a14060d1b060f02010e010603020d020d140105042f091816080102071205030115050304021927090506061216090b0414130212 67
    0x10319540da409410b404c5004105c4581c0c841064007002090301001402c03460314a440c00407240e91000d0042c2d800d640c400c42c141e031500c031002d0b00c51400d00700b1101204d258150015800c0302c04108154461000c551040c09079000703101c1c040c0f94400813800c996152000940c80088442e2890050070720021542c60f00c0e000f1111443c620f00d0002495003514400c48040f680c6412000b0105403640e084215014245003808911140c4c00c2d08002280340c010000c0c0032048203601003004401d50310320820421f5441d0300c5032031030a07107000e81e00c038540e9000c1d420605089031881c00c5940c2408041e032164040d01d048500840c0e100e9035845240e003007515a40e0018006070313040762000391034a00c090f4454176403400402448003145ea0905201e00003007030407803005040c034590394144510400807403000102140c0109048030900c001f06002000c0c3e600c1c1c004508050000d80e0b40e080d80c0066520307640e5000050308c0100b601c0900085040040784a2180c1d421621101840d01440180000d42040c20700180040302c09802c4071 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 745794703 1250 745793453 745793459
    0xa2007170706050a0b0a080f0a030806040e0a0f050c100e090709030b10090c030b0a0e060d020d0305090f01031806150b07080301090f0608070608100902031501020c060c031c06 77
    0x64241c3c1d03070484a0502480e20b03030a040e111030410b500000f00601d00c2130003a10318000d888000b180c461028001c041d00b08400705c1d001c10241d40c0c40e5070001e030403403042e4411559100202d123403990000d0518481680c8a0280d0295103c060901242114601016541d039520500700074003000700c5a50701504620802440102c0400000d11019045010b01d030300c1d18045c075000e441d0001100a0740c0300103a000c4201400e214494149490b112a09001e845840c0c1d0440c1c40f590350180030803079080030740c0406944584a658003000381031300b01d80103029036901611020b20564040c001075080c1c500c4126810181c060103002a4080782660f0301880700d034010b141940100d01d0f41e41079080c915400c04030302038848640c000010444890303540b080c0514208100c07002d00886240070143c41c1c96070510f20643c000d0150ba0b800260000c21800300c001b0280900c1d000854580c20440c0104903d545018a6903015100b0354000c122249004002d5401c0c100d00c2c076009618140000422010700706c02c001030003002c075480d00d0000c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 745795953 1250 745794703 745794713
    0xd0206040b0702150c0c06070203130e0402032509050f0f07050313060c021f05040c05130b060412110123090f03060106020607140a1b0218040b0a20071707 68
    0x120300500008280684406d01541040d052510140c02c03002075600800c5580200480b4803001c0041344e04c088000007981da01d60001c01d003030410808101c0c100516040c48410040d402404a400380c038a0400c00304215503900300c180218042c1500d0354496500ca1800103a10359102d1b400455002c101d000649021410340d42e1220b00b910486010039016070010741360701c4c1282c106940f034140d914040c05010f21003800e090f19100f469507102d00800d03010300b00301e00480b07020303c030780d5004032070b103030401030490343d980d0359a440d500c280592044c1d021600240a408101082e41c4038407129444c061010f146070070001c1341c40303c0e0010690f201c2551950051032414800680c1e0b9824400c181c02049940c014219034940101c0c020241c05c8049502d00760305400f44070310005a0350101661215500f140f501000e24034250000406c032060683ca801c41c100d501104000411800d600e4aa00510020740244010703407409401505400140d800c0543c08103060007a10b000c50042c11881c0040844c81382c0d990b29080c80c980b64 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 745797203 1250 745795953 745795993
    0x603280b0c0301090c030504080708161410060603090b010918020301060b0a020c0a030b06090c04030b04060b1201090506042603010906031a0105030a110f0d0b0a0506030d0206040b0702 81
    0xc0001d08010100040201800601603000900031a2400f000030f40342640c1c903080c89000b02c80000d40740700300c0410105c80c020301452913214225000844000180c680b5986640d4a0545c41e102020060814000281c194000d000750304419900590003400c80e820403101368000e02907424200e080500400301280580c07000e00c0388502618070112482d548048854011380340c0b800d17031502c00703010b0140b0107010008a10046459078010788102c443e000c41e07417100c540d04400f50013207400151041e055481030000f000340c10761040c14818400d03101c129800400d090310a00301e84070144003916940209001800003052000300d41d40b00b80b003480480c40c0d442e400c00c22420480c0c000f42c00001d00140d5441c028801c0c816444c2084c11035070388a6000742001c5d0b04200c0845c0d01c80c1c1c0b4217034004000300e80703192601038540e54139034a0300c1c0400c030040d2281c018040e40d070811020007102940e01c0c520350307880d090105429085c089030f88481207110350001c05145d00c0340d6681c0c0c00d00550080c1400c085014034100b20742400f841c1d03c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 745798453 1250 745797203 745797211
    0x100204452409050c040803070303111e120f09030f0304060213031a010e15010e040b1f030e010504051c0c0507060e01031b020c2214090f060603280b 65
    0xe00c44254500b06468201114405058103101d40b5017800204402e50001003281c00e019418500820206000c180101d258010b002625040441c00080031780802190400b40c0a01d082944000d5200e841715882184a500b0507501c491050304104a155294895030b8029908244101801450148a5420415040c45903081100d08075a0407a41c80e2011216141040c00b501000c002c890f803505002541b000e0710340300e8403c810305104100c030365850556911b601c9541e100030081c2540310841c0d29490000a0b03200c00455960100c1e160030f0044040660500c0360902c900c0d840300060040c002e07044541410006000e00c218100085041300c00000303503040c08002c0042c801c5440e5960704500d501700140c240d40380010b600da20320028038a080226a0700007030446911006941c0518007204424040c843c69038160300c050650b5051990420b43e4540085149100b030414000783c404000000b06c50070303200c2001f95a03141d4142c1c040981c074040f01c8411034448904001e0380c1103002d8a5041641c0301c6400030002c403 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 745799703 1250 745798453 745798511
    0x6041509051305060a0602010b06090103090305070b04060204061103040317031009090309031406090705060f13120501110a170c19021e070b1b0304050310020445 71
    0x10140413543c10908514030150504d400240071364050003001c1281405014001e0b81010380356285030042c540503e04460284c0c0d08103540c0d890714603140c1040da0280d400b030f00c1031b100051a20802d0f80c60510303011080d10242c0383c1c00810764407001080030031100d00b0b4002400458544c8141000012411420720906c01280e00c039449881140d072541c180142d681c2505150441c1d2a00b01104209011b07001081540c140c5100315900391301c8901c00304c1c60410341d01074450f80c541c1c0d0406142010900460900304980300b148100c000b807106a14146900718140580c3c4200d40101e41c0c81c21205038204040ca1400790312501c1101140d0401d25100c403035541c40c103114141000945c00bc04400b40701d40300b060400071640c7c0103c03030082003a50b10f4184110b001e0702c240c40c04402c0e108403907680e11f07a40202c02c0c41204c0080200600b110013481c01030304001c00a510521803910724040311400600b01e092401d0b44c048200c10411198080d080c803883e000c0012049035204002195030300d2120003181203050f109111465810 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 745800953 1250 745799703 745799711
    0x4080601030224031308090a080c24030703020d0b04050f0612010621051c090e10060806010c420b0303090d1106040308190905060415090513 62
    0x50040c4081071075030301941c1d00c0c3c9404040d40c00c00c180c601401242c0c1c102d5849030701e0029918107820200540d0290308040c681c0a101d0310000100710200064040307a80030202c43d12a1008119404c0d812031484141101c40110b00600004405d28000e0f0b002d091243e10510001c181400705000260440f0b404071122405008908103100b80c0b8100492000380818561008110540c2088125030085401c01010000d80304911508000c1040900c4403205101c011013110203031120315000902308030001c0c0517504882c46101d0020f040161480e20784001c07035a09444e440903030707116400112008610040d040e00c515601001c01050011034001030f0580030f845515100b0b130507940980da003040c60218038000c560740d07003010b40c03940850781c001c421120100350440b070441c0c5240d00c070b107821030302000354489075a400000410000140031156000705603588205007034103142d00484e8020340d98903402d80616a044081032105101d400c01d51060780192880c142028100c11b42e842000525198011a14100940c1c40d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 745802203 1250 745800953 745800959
    0x308180a0c06030f0b0306061e0607050d14090d080c0f07060818060c0d05101d04150e0a060c0216080c011b08030f070c060e0a0302070f0503060c0904060b04080601 72
    0xb040c400c0ca283c000c4c240c5001e01a00410070f0000380e803002c015003030034402c0c0a0b00768a0b034680b030302c0b01d030101049420203400b0a07101c074046e0910075111000c0c1c00064001c500c4900720179101ca14441c00300d551119005203400042001d50b10b814a4030b40150030500d00500c540c440d290050602000110010656503072a100d00d0314100b0f20b03503008101580b400403000da0080c0d060041422010094480d034020115002580e0340c2c60004210620b4515405000d010b64141e1a54180c24074014120784210700031051070303144d4001ca031110401c46070143c1049210342c110707040800000f0601d41050b01c60030120b01c1100c1c1c1c44e42480c1028104080154022805940816440c0c13400d960850190318014030300307801344821650300d92105c4080c1c8c80300801880922110341c000801d00d5002e08902000300d60810010001c0b2000442902e6813001e0402d0705402510a500001174900043d040c0e2030181e640140113800d01d0344884442e01d4513900440c824551043c1c60b113201081c001c41d0710010340f0040265200400c07003549 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 745803453 1250 745802203 745802207
    0xb060d02032505041a0f04050a0303030501090b06030603030909060301020c011505150a02100c021929060f060306040b090f10081603030e010306090f06050406150c0308180a0c06 78
    0x206042e460000d02105000421031a1500c841030401511803038151507840100583c0c100092080381c00c12940004e40d01004400c1c1503140e030141e4142c608003801040304070908410040d80b400b080b594103a055000700320080d840c1c1020840031340c21400140000d418440d2007502e49003514a54110000f4600000310b00300450300e407401e0100e00300d10404c10f0301490309280d248000e44820310540941ba54036107030704484200510801040d070043c409444080c0c006091403034480b003814410070b0141b49030780c80d00003214880e683d80c2c01c00314045d88006080c800c808460009208003500b0003411280e02c20703501c41c071489a03615002c0540c1d224201c51b8103500708618110390800364126058020031f00542c410214121a0050b220756501900d0301410a501d2042100b80100c0191200e504446800f45c142402a00050960b80001d01034410403207007400711644034170b00d0f142c01d06081085400013420301031501012a0048011355000a0580c3c1880d680140b072441052130711459140032520400c145d401000029 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 745804703 1250 745803453 745803511
    0x1b0c0203011802010801030f03091d070e0405060102061b0408061e01080106080d080c160c06140702090402150f0f120108030309150a091a0106030b1c060b060d0203 72
    0x8034140d09182c92001c0640000304031600500000741002030702d40c500800e050081a00000405c81b0114101020500100a480314041603c0040110300807840b074140c00c2c5814000c143c82074074103038003d00540c0e070b5902840d040f40000d50841c05243c002004041042c242c140609071003484a11180f03040c45420340d1a6104d140c0701603001e116281d15180c02441140d0f030215a01780c00c0c00e014075100f10b07152540200701d2281d2040200c0750685211800d001810464007036807000c211805511044030104c6c0c80c11100743c06200d9024000d500c200302030006401443c00c82000a0a02e031800c455605080784880b410607654040c6500380c00c00781020600c41c010603c413458060141a51101860445c10300b01c144070340c0d0b00580c001c0303241095010b40010f400c0341038941c80444459000b804100c10107801e2045500392100c20b004280001e1b0800120003001c0c1407090074035582551080503c95030a004c0e80b0340c940100103d11845900c00f004004142c641a1280050350299070000700141e5180c5411550094807 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 745805953 1250 745804703 745804721
    0x4020f0c01020f03070e0d0b0103030c02130c0816051303080f2203020301110a050702011116030f120f12020a0516050102190e0310180203070b271c061b0c020301 71
    0x44c0d10300e150081f000941c2e80e06094116076242c00c0c13841c4401c40900c00a02c0004059403c1c0951b81d15041002045070fa10268850203107007016510307082e1800e070304021682446240c80601e0090000d000800c005503030380006011707000d0000c15441c100708140342c90720b80b14803104002a100802c1614180158034013840360260900036401c1c180e1901105a002034054050414041c0c180b00d5944028404003c0501402c4141d24103a20b2103039946841380f401000000169800390388405102e014100220b01480320706612035a00e49549055010780502c0e00b02030745c40f40c0590020800c06001d040c12140782168a401000e11038030001da280d0520780700d13115119075031401d10020020041c501c5035050b2804114008803d12164010a55841c4507040b40b68080303501000942610818000240604600c8060110919807103a146207030903d80001000d0821011901d59102d0804440b10034040004245603a80c14411a00401d14401c004600c10072019200300d04004200d40030f880388214502885000c400d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 745807203 1250 745805953 745805959
    0x70c140106032a050a151e05070b1519080d0206190e0109050a0303020408070e01050a0b09130c0806034e160b060301140604020f0c01020f03070e 64
    0x14061458607140c226a880740c04900355040581c12148094035040c6102024040c0a089000b03e640c0d0780500e5501c10740c10503030100001f071400e028002510341036442001184025901c0c2c0741888050745a19030100400b130011612400303040e0a1680c6910b40310840314540a02e0f04c90648400d140080c4c850800c8000c1a028045410500c01c0100a612190742c114100400c85000600c0c6c400601c2128014060840040e0051042058140401d54140c008006031080c1c50142e0f8a115900d20800500030710a000b000d0344044511805d0000c07100c00c10180103841001031441ca0004850b8600760202c4110102c000005900314007000180c0c1401c002c190b02081c0d0703d030890300a54540d0201c95a1050002015403685075440541809150740e00e0480103000f103520340030707560b42d14110010b001c9081e000b2004071007000d0380100045040c036041c0715504a00036240c0072404d09581c0c0d423003084001e40c0806052140000b0a1151540c0300400344040c2000495145095170b41e400e0008014040749001c101c0148 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 745808453 1250 745807203 745807211
    0x20061009020306030601061d06041e0803070308040b041a10060e010e0a0905040812090c150c0604030c080408100f1b050a0c0305091309171305010e0307080105070c1401 74
    0x2444e840000301c00d07045a14500e840722000c41c0f081034a54006241055459011901140114105c0300043e40f840d030403501074040100c030607a200e000545a016005000d00032030365040000300070528010003140d2107841610401c142018115948080d40e40a0301c440c9856440340750144041ca0300081c8400402c0030034240302c00305441000000703212042500030842910b0702e460204040000c1c5c0000d440d17804415417404912803604a400301c0ea00c0d240744600750711525000415961481c080421941c100101c040906030786d60741e5032030540310100765080c1142d400700c1c01c000008403120107001c506110040c040380440e001e40b88a0700a002c3e82c206581c50000d10a5001d1140c20312034220084540c11005418040b00f903ea00f41070580d454094030100d03030340108000303144040510007503004c2001c00d48240084d0007004000f40040041e400b450070300421900c0c56280078009503004510f41c1413080001802c841e000c80e00d891b5510f0a545090f03600d04042000220107808114071807450003103131115980200 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 745809703 1250 745808453 745808461
    0x506040b0a0b071506180501231207180b03010b0f060a1209120c020102010c171b0f1602131b050f07050114101e0e07200610090203 58
    0x4616401a00c070701c19400c00002008003c020440c00000e2426200440410519030740c0ca0603980e19106d1201d48000b42403918001044440402c4004040050f000e80c2101c0d2038a00c9806106801034451007546a83c030461400254480d0180101c1c0105046000003081c0700442c0424103003520310f0741d003e4900c01c00b407000c580304081c9c80b403030b06803043c01d07440385811681d045803600e1120048c240c511028020020b12040c090110383c010f01641c01042c0700781c1c02080115082c040403680c801c8503c90960540b081403021483d00220300360315041c1010780c1d4a003030349811201e002c840d90650080e50700311502540b5091070403d62500046d0701403c001801001c0c001ea42502006500b04414850704100b80400400c0c1a00003902c0b0205490302591b00c00000c000500c80040a21b41c0300d0011071b408204144844000709582c0034003c0000c1c07020b0107040c850000b640c100394004011090003081e4000b08100c2e9a98142003919081c1c02d60850413800c005005581091807102c4980030464001884881c010001d00c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 745810953 1250 745809703 745809709
    0x11010b0409120c0f080d0501031a28020f070609020f01020607080f10030b09151e0c0a03090b0c030a050a1a0f0102120c2506080106030e100c050d0506040b 68
    0x40e00340b103445190195100d1120718021540c000307540070140072900b020925241c00e804030307803005050300d025081400005642c40115016844c08985003600c503212004642004d0f598050101e0750440f0302c04000d82040d0307007640c3c01d00084d000903c0076154282c1703601d254415405c007401c20030700240081c40508101d03d0300100103040200c0142c801c000014400c00010303004c0410075049005035511241005c99420061201903661540400048411400ca40840c07510302d03144100c081c4c40b4804018034096a42e44404454858000c5c01c5048185502d801c038a0000540798019544a600b0b41c86850341c0b6802c0110604040310801409603900c14541116147da151361400070a41d841800c407040300001c0e903d000101d041a40000b07030140592808204c00300041d0000c80c7c050300300a044a0600c41d40341d04110000403110720742c41b503000841d86940060010910a8008500410700407044070400032034281712404a40120311200001000490110882c507420300549422010803a02800355540e41800 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 745812203 1250 745810953 745810973
    0x40b04031707021f09170a03180b1219060e01050d030e0301150303120c1e0e060301030803010501120e0c06090109090e0a0c06210b01031b11010b0409 66
    0xd0007807040070003030042014519007241c2d0b2656000e409032040c4280a0107010088900c0c25080010541090000c00c0d0b0b00e9048034011400c408490081c10040d0042d103058405a030884080210b511142074040780300c68204006012041c0c66000148881c034001a8000d5582041541300350100e0401350100042060361800b075055560865074608442d0081c0740940320100507000654040d4248090f00c0ca4500c035401002040700e00944400d41c003519042040c038100c0d02181400c0f401f0544209200440640162100650504d5810011840d9041c03100017100303030b0403d90084a0507500040140060750340585080b4011807600c01c00d020030032656807042d0701c1d022100202c0380559004180c4e100180c2c400c0c001d0304002d10340c1450802103c0385035882c03540c586140a0060341c030b88440c4800000c00c0c604c5900b121014a00002a280d00040103030b43d24005031074004030807410181c40b04002c04100d11201306076120780560340c9034245220b07001c0e481c07a429184444815842189010000c1e00414a03100c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 745813453 1250 745812203 745812209
    0x114040b0118090b01090819060c180801050604180b0406050705070f080301060e0307030c2106050901090c05010504030206090616080a0c0c140319110d08130506040b04 74
    0x1402203161060000100c800c00364824240b008042d49290016001c0104e61014040380000c3c1d0700c000c1c1990300c0d6501c1c2c55032a250300020b0030fa06c40c1002040c2c03000c1001366109205040952a03c42070305c1415400c035034010b0810360098000e42c1d41d00c106000103440c1c503104000042d1002817110706210f040f0f031240440300394001c0001e0955601c0300001921a84602c0c01c4440b026441181d01c0e4071051141028422a00240602c03030100d07082004640c1c1030300c0c0000b043c004903a84a05151205400c0621110074407020341001094892a5044400080e00c2802882c0c4208039180002400b90003074109852440d41c41e50000b07050000030081031000da1540d80c2250f104040c291101c42d0790b40c40c7d5030f215600e0181e818402074800c140104140114a034801190203e450169000d52070442e11007000300580c4104100f496810703480b240d07084141807c2002d007894842d0064402c0041d81d15501c2c0407412040c84824200c40d5040d00180d2a9003000540c00448060308007510034605050411684011601c0b03140 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 745814703 1250 745813453 745813459
    0xe1f0305013615062c1c021c14060f09121308030408030a140901050d0507022d0106092c03070210030603021008240f030303011514030114 61
    0x1240b111609498105460b43e5050103102c2c4030050343c8460051000782d22010b0512039045152048407100483c1c100f507411500018414070b5189011050392002c40f4500c1c00490700960407500c1c2c03e160003000c1644400703c0340914040d0300401003884610381050710041c59842d01e80130400500440400000b200c503166954804199650b40e03080005449107a44c560098003640300028005c81d20801c04005031100111940341e41d03407400300603c80004140960301e82c4500080050106410f0180c1030b401842d0880d2007401980c001010b200c80003085411030620303580030b810b80703011400751001c400d201d40c400401181c0c41c108030800581902d03012035481d00c0300c5000e0200148000d400703454003d000300d510b0300da402440150110300303c680190180040b40300680c842ca00022514441501401010340303c0d00340701c00c0c00356804e031444007295060614584900e410100d6415500d60036102000154042c00c400400b0304e9810100c00002051101103a80522a0b05030034001003000800da14a5400b401c4011 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 745815953 1250 745814703 745814789
    0x109110111030c0303010b09100c0b0c091f08160309020f010f090f14100203070506041b03020a09051501021f0507030b060304120206070201020913020304030e1f030501 74
    0x31204481c40c5000fa400e040700c260100100005103840381c0d40042c0301000381900c0210410b0700d82c81d003c1d41c80d540811405010f640d80d000000c1d01c2c640004008001010f0001c002540040158912a00701c080f90b44491000c079004105001000076070407a10100c2003801d24041c004e40d8079550200e1030040001c0d0959050080790502101001d0142401501400c00903a070001a59910004681c004440d81c140311300a810601c055491b00d0700c00b10807030b004960020020300c1152629604d19607241502101c4d00d45400e540b440210040e031310030159800400d0a4200441d0908001c1c14040790320150000081c113651242e1a45103a8201204456240982507580000c1c0c0b66034004017540500000961250320850010070070082042d4059a50035411880d8201c8180f81d07103011041c1d0807440380075506607001c0e03445c0d490040d108880c3d4004541c0a840703440d0580c001c4101c88003080080c0712141402c0c891811440381c06602503414440c5a00510000da03a02c0001c080012441c424000726010108001d080 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 745817203 1250 745815953 745815977
    0x11d03090f040b100e100f1e0e0307030605060a0f21030c0c081e030f0d0b0310090b0103050c04050403050d0b1906020d08060409080a11330901091101 66
    0x641d034045500400c002e8022014410302d004028031100c0c0c3c0b0785c0d81038401d000d4200c1001c031103442140f243e40d1401850b11074180112000a020b803480c41881c580d0000c002010392684180d17101840004015885900085850300703082041102c440f160b42c008000012603400c0810041c0c185400c400841c56000110740c2e50b1401604045604003503012018144501c2d007600003c41040000c0d1016030402e1611201061280360000345482e44504442951001010b120783c03c031750b10302544908180d5600404440005a0010b95082a105040f20a403680e80f40280100280720b030a0006517101c0508540c1008146881c0d9006001c1d0301919074408029561204512840d44602d02d5075401e549141000b801c6e00e45e82d50100943d250401465800020030907400320700705007042e000307400c40260300912480c00c10035404c00440d040041d11100c0030701446500700030a0000d468801c101d9100c0c0e5a1151101d075030040060380c110b8520050005400c5a150103508004244083c20645100c142442e1904110308 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 745818453 1250 745817203 745817209
    0x14100206071224051309020306012d0f230102060f040f0609110a1409040210050f07030c1a060d080a090506030f1005030d0915030f021803011d03090f 66
    0x41070003408240c08040c01c1d500c00100b040d807010703c0031104100d03218802005014480e805075005d001c002501580100011301c030b80c00c942d1011085c048804182e080e10020344c2103032550040000d90228039102c00c504418400c2c90340d0062360341c86038142102d080794007901e1400001e5940078014600807140200c44003140400802011011105410103000c4c0100d150f01d0401c10100c0b2000d000c3d0074425130018900240074009a0403c11120500411001c615a00c680038001d0b40c0078202c0851081000805c0f08240f501080d8001d005e0081c0680d80340b12a40e8a1840c0000d1480880d22808054101d0002005202d540d0541002d40096100c402503440b02544281900c03e101180c020303551240f0044100620003040c080c0080c810120740c0c80d5454000c4d07844042c1601e40d0072314883e400000d1390001c410710031852104404a4504c3d041e1400007a04c44205c04410101d0704240f01042c20446066110302880c80c01b40503803134181a84601032450000d44882080daa84070780c00480c0d004180c50038050341e4940d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 745819703 1250 745818453 745818461
    0x7140306090a0f0203070f0e0a030201020a080c01020712080108152206060f1d0a09031d1f0314070504050102070909080f0304120201140c0901110c0a0f141002060712 73
    0x401d201c810340d100e007000e441c05881f40a86500380340001d030401d03c2a941c64504542040d0449406801a0040b4915915000695402a40e51050b550b408004940c0001d014400c072009a4155664183c002d50402090300d0a18480400e65000700c0000c5d4140304414241200151181c3d111400355210b03902185041405040190b000510118014030300181103030f61a14081c2d095001a0444219990b440d4240c00407a400d0342005000248414090441c0460540a0f283c05860051100560b0030000e441e54081000d9809540c00180c0c4a442550070580d0100400d42c21800608042d8202070400c00000d40d0340a003803003441c4940d901c82600c202488a40b100312001400c1e2442c00565a02c0c15091000c900a005400600107611300250294101080a4024003501903040b581d49449460401180d003403100220640d028050826400555590b003214207006100c070100f0503814614150740d440c01007001c6c04241e4010310f420700c2003400c065408140c1541c0314201d801d014062114221010b0028 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 745820953 1250 745819703 745819721
    0x7020703170a03180503090607052a01020d0e1f0e0a030501150803180603041e0311071e060305091c020705040c03180b090309061201060807140306090a 67
    0x70402001a145991001c0c1004001e000d29940b010710404d103141c10720394200400204c2c00b4000713403c24082c04000d0324042c4001e2007510700038811075104a074200802d0320b584003148800d03c82c94035480343c070891a50301408042c01c401c025081c6245c0e00301c10707140841c40000050000c400d030003c07a20074800c0064022200c00302050f801415480103d1380740c0c40c04600034200c62526960003905201e0004104800100300e030444000440d05400e01c14096080c082d40f0382001d03104540410a0200c1002d070003410715804e0110900999031010040903001c0f43c1410f00341517400c81d14000e5806812541e03000c2450310103004448843c07030000f0b9140e4444000d6418041d59070381c03102a80b00c8095041005035800540e41c815988100c50420031422115000d404032400a906054019800007403039020880400483d90720034002e1098a00d002400d00014005030f229080000a858441005100c9141d20081031540a807650512040c40c103400704501e41d03030340401803000b0b200d51856400264841c01c103420401c61 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 745822203 1250 745820953 745820963
    0xa0e01020c07030503090a082b0909090b011e050d020f04140a020c070b07020120031c0207051504050604060b06040e0a0f0b1f08042d0308090a020a0e07020703 70
    0x820b940703a00d04542c8a510010f0300c01e108012141c1e0114000700045044060412840c1511440450314500144205c0750741545c00c0601964180000310306070079004041619200b0070180e811036052500b06085248010300840f540901900f050003d601c46081c08070020b501101c191019101c0440081d001d810307003a9412a0703980300c030b509021828401da00130b049002008000c1e0b5080310b0300e0384404200c50040034800307170016501003c3d100380b0035180d00d4a003071410208000d8925001d5025104c4070440c800d0045280081d45c0002c061041c0a401c1c40b60300100c00d8607406100c410706080c3c43d00d540e20003000c1d0019100e10750381c0100c4a002e0b40c4003c101c0317000308000901c041c19807505a01000007480d03201c07001443c1d07504041c113610b502d00c0c2c6003401d0304802c18201c403509811900352400701d5000500400c1210f140b03c400d0b840300440401c0021502c101003c00c400420290010f28006024400140000c1a543c1c011218140141e0380e68043c0005d0f10ba00810024050340d400e04202e291040d10341c40600 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 745823453 1250 745822203 745822213
    0x212030a1d0d09081605061e0f0405091b040b030a020c060a0b03010c1e0e010c39030f140a060f1b051e0304030c17030103061409060a0e01020c 63
    0x110400100b48055000b03403d0301c990984990390b0420f25100c0d07216140225034600401c2c0300340458079144d000b030f245900c80c11040c1802148444126400c541c00802c1031284070034041010130151501100d030755805855612642e00c40905400b01180d20301840c015041c62704004400501c2e1000c2c242d054441000c000c03012201c0038103241c002e4000030314141d00c10038069400c145100a070b007406000c07a4503c01c1136929070350a000d62015800c444021004851034100b104511520b004252030320500d1004c2105a2b1605020704081d0f0741c0c450004502c80c00f10b800f440b0380380c3c6080000c43e0248003507003403194000d9101141d4a005208580c100050006d0050082c0d10b000040c1d820f12a00794000b40d4001e403903400c072000750081c01806035441d000368204503581e0800c0018108007070280d91b020310303041031103030410031844046960349135070030307101415900b003808030200040060110900804200410300468030115091200302a510388000609010544c1e03281c1d541d161115500b54110f9002d8000700040d20 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 745824703 1250 745823453 745823501
    0x303180d0f03170105041a01081e011715040f0f08040b13030203070b07022416030806090604020a05072006040306051b2106130617010e06070212030a 66
    0xd088082001c2c581e443e4406071074008a01c0b41002c1c86040400d0750220100c2202c8285840116203c40000f84118800d540d150302c2000c4031407052220303e010f0599902d41141111a2119043c070300907115032400c089070504c9003400013250801500f40041608000c0202c1c0c04103031400c01c01868421a4070900ca50400026004400c03400f0410304020b072442101925096a6100d815003418004d044001c2d6201c510440d00941c0000241682010b001c004c100060810110001415103141648001d0b0701140ca04020000c00d450280d1409900020481c1c00b18280419088010118018640000c041d070010301c2c05649610f030700040e0f4025014004040c103a44a80381c0c50014040d1034280c402c2851401e52030440104e0f2114001500c55803950b102d15132000c9180b0401500c1c88070800b5000c02e404c4403400d01c0c08602c0c0040740c000c030406018447d25000d403200010f100356084900e449050750041d0400001c2c030901980c0880c0d080ca0881c0c1c444e03820740d101e440c0e44000b90020040229002c0d006160445c2c1d40b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 745825953 1250 745824703 745824707
    0x3250312020a2d120b0f0d140d0507030219122010060509010e060d2604091a0301050f01060e04140403030507080c040b040509040312050405030d0e03090303180d0f03 73
    0x1100b04100741e503607a801e5554408403110245c541c00703000658058440c51044001e030911403064152107001c0c10b003036921009040040390400301d4019040c130005800185c3c64041c160100200544d200c0703030906010344400e10392502031613010039142c1d1404200300307070302c071141e00f483c54040c0c0c0080d00800006940d107130390303040e04203000a2980780700b468000d988150001903014880354400d803043c04041c02100103601d5680d6a04208580c440143d204541040144c002c800b103840050005080801e00004038602012900c588040300300301054405c1c1c0c1044108600e901c413014425045880900b40b41e01c0c240c6c1000d0015001e03002d0113161130082c3d84008200004d050345031700580d01429444d2a07020181e11100d0001c2c3d000e02c2140104c1614680170042005241001c61269a115001e8034040c4034000800514100340d840598003600d0550021450703c80881062044851b8140104003c62804440c1000b2030b0f100d016003200c000760740a21a1880c40c1507291841100c2e1751940c0070000d0000c6000e03a02d00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 745827203 1250 745825953 745826027
    0x906010e16023c07180b03120c0a02040e0307020109060807092c061c0222090b010503010b0612040f0c0810200301081506041104060203250312020a 65
    0xd850070f5410201103c000d914001c40c1c00390580c0c030141e103036841da80e02c002d2981c8042c09030b2020490300b40c411105142d080103c80005041a680311401070320b40007406004001c150380b801c1003900c46c250420821200140e8001c0c100508076000d038200302c12540d032100400e40341170440b40e21080038044040c10081c0c00fa064843c0028040488000c02145600c5a009103c0380c01d030301c140360740b11000554400b9005498012910351300009101110f41003600c5102c03c1d24155452004200c508113900ca00511035032030203004224406109039205814640f52900e80c2c008040003a1005d0a5050040c100d0810311426110600c040c090300000c41d24612600441c55009050880420340030901402c0e801ca110b03a00102224101c03504400100801c10703881000482908021705001d91095584207408542a41f41d0050f0004007855006183c03502605490003402d09841407411a004400030104000241c01200e41380402c0c0c17240c0b00044c4c032180650004d0ba070344120f85c84010f46081d049080d1500528024803 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 745828453 1250 745827203 745827283
    0xf060509060f130f0905071401020a080c010b060d1401050613060c0f050303040b070e0a03171305030709060f050a0e0f0705070b0117150c16061e05040b0906010e1602 73
    0x8122145140d85960001900d22540b48c0140140c210003844804200c0d201d01804002620800020f080340b9090001441c0b60b008840707036004103440784048100100c058419030300515041c0d4036140b0b0700744050105044a4100e0140c401403005640200d01803202d22816021020392100442e666410241000d9030b00d014112003620001d0000718086029050010401c07080300c0c6d00204850a0b6032000107551460780003e1000b684085d00c0d1b04c4d001482c0d90f0f007040090024600c4800c005403003411b10b82e0110001d9500c0d00700030b02981c501700d020010148500041a41322241c01c414031a0707034032000c40c00c560380e220701d15010b022444110000300340c1c0004800581c4030070010400301d8011682e1a030001d800b014040329a51085101070100c1d50b01144942400a41180b2454000a001c0000315487c1c84540c2d5140807140050754903c1080200301407814140d40000860004003c1c1e5071400c81030354a4940c0081072122013001444100801c0c40c000c020200c00c521840708000700440f085010107140700c103448 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 745829703 1250 745828453 745828463
    0x515360412030c0801121e0c050f0303040b04052103070c1706150f040603080418060602150601051b03030f0f01050d0305090d05210702040f060509060f130f09 70
    0x30710201c5054000c0c46090910101904c4c0c008503070303290440c559200c201c40d5105503444010030021074541c2c3d9410b15015000c92184021001007801c2c030041c44440c00d0902c280c80d020340d104010500c444103040040c1d404464081310202441c41740807400d021015003200d16254a8030000c81c07000100103080c9881e90668600c0f145210120300c812500e80d507101c0c0c041e516842d00e2204041030400c40d062508030450f00c44409000415020795940e50b05103140d2150788520b0b041c01c020010560007403014060703d00105120b100030f08120740c111640f030301c4004018000906200e000124603802e12082c40e055261654044140c0b5100d141c410050440c04608442607e100c13540300c0e001055034945100b10003026901541e541341080d0511090141c0c3e00380821058900307110b143c000103001404000502d01c209200c1308407035160031492040c8800e4840307124172480f2403818850188a162a401e0b00d235684650111b0700342001d101c500e030200368103620200b0750300710a030308041030451501030700d400c010b80c00e512030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 745830953 1250 745829703 745829723
    0x3020703062003060405071e08150909061f050406121b2718051c0305150402160c060c05121e0a0e0d032105153604 51
    0x88400c0300e0382051502c0042216900034000700d02c0368203241c0d002e241c0c130540d28100755000071142c030141100c50744c040b001d440015080404200d01c3c0071001d15003003844030007074500801606001a505407a00801440b018000040b940c034500d407041c413500c14130010403010300201b11454070748070000e1640300d214806840b0116849900c03008840d203c2503803001c41d030b804003202020b00c0040200c0401c640904803181e0680340c807070904a9241030544442500b6601c104000c201040d000100d0700000100001914203040c0380504000403005216924018034030116001a0b88040c40195501c0c1e500c003d2030702070000014150080381041c2c002210034007090081e41210301503083c61094480394031403415a175100c0800016020454100c150240c51100700700d0904124034003060b40032801d025404c18040c1c00044a82220000007451041603580f8003281940c03e0001d031410800c03d14140285291107030089c0502d2242084000d24002c002070700f400811454070480d19900b26200315180305a501b91400d07402 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 745832203 1250 745830953 745830971
    0x7050405100c120c0f02100509010f0f020d0f181707090504080a0305090f15040c0e070c1704120f02030708162c07110c03030a0c120e0d0302070306 65
    0x9210b1140d5580e5100b403030301e200c5400c210b004071105100000226800e4079101c103e41c00503a80d004c1c00401050082c0c2d00c0c55144c0021038001040d05100c0d4000009101c801440020301c40c1d40440c099850010608040301005041c080c02c891044500d21946411804060041041420300440070b4407615140226854603480e44108021103206640c02030210303004210350149540281c0140d07030710050310016038a420390000b01080c00d104001d1071b5038030340c2d09148040008121030b09403d08054450382c001c103012440c101e000030784140c1c0740c40f4000d0b1902e400d82100d01d01085d0950112800703818400d041c60a150b6252600d94901400c42c64102c0c03190107441004a481c4400060410b21964115139601e043c0d4035010b60a05041d5080010341141c00190050110003520f80401078060360301980c94071144840300075598144040f6140c624400c0e0401c103c0c110035181d0107001000070175080702442004401c2d0701001d0343c201c030300303046c2c0315401242c4852600241500860315804890180d4014088160 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 745833453 1250 745832203 745832207
    0x907030c12111b071503050402180c030a0b060405040914011a01231e031005030106080c1c0203240f0403050a050903150903180609030d0810030b0705040510 69
    0x10418000750160414095034100c41031140360f0782012000003080d01c94039902c640708505d40b2004003000c03d0210b13844e07a09000c11030a000c2c080b510700d400c0c038001d881414104041d140029100150007404182c0d102c180840c403503624541150001c0600800400c681c03003503403500752450306442a161013154a03100b45034202c82c0002071002002c0030705a50301c9501180111021441c14100203513100e62000500c00b2039052580694401c3da0307528510030054580c548140c8043d01c03200d942d041107001c0e0341802c9041020001c00105009901811100c00c05a1a2002940128141c03c0a40a90325115460190b000348480207000780303280b80b400480c410b080c0d076407410140c42800180c40041c0000c004100302e0b00f031b551180014080b2150000d081d42c0d40702c2100c20f404550030009444110301c540000480740840d07001d1802040c06074000303441c21801c01142c82c0010b92200903040342002480103110008800461142503034002d19404128440713241040400142030760464001c19026908244004210318 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 745834703 1250 745833453 745833461
    0xc02180702100b1e0907180608010923010501050c1c0309050d0c03090303080405210406030f14060f03030403060e0615013f180501180506040807030e0907030c12 71
    0x9141d1a61300f03000900032828400c0da9a0004e1420041001440183c0c5100c20800e10f203800404003503803002c0103941448900c0b000c4039410800308200d008103807114407141c40000039840c111102400d22a03250b5100102c0c0a040c000f60000340701c0c101003085030b00e01c0300d5074040c0e1040d0310b0140142c04940240440c0d03502500e0b4480880405804540440070402c00280301d9082030741c9c040c0c81001551184005140e0545a40322a50301c41c4031121008074040c4021139040c4140e410024880b0b00603c520b909811549100c180c010309564000c40806070800240e881c100219002141e000390100700f1415484492a143c99041c0c0e42004118265401c040e402d6200312907203d00c4820380c440b090400c218044800c140d12400100c0117400a0b911031442101d2012440741c001039100800740480c103031580740b800030b003102d40500c1500401c800e242c0308240422800100d00c1d23486903120700c41c0c964a13845404e00760341040504210a031b110f1005010440b440764503821154108801361592014020003152030000c2e1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 745835953 1250 745834703 745834729
    0x10e010b0306090c091906080702030f0412050f06070905090a0e100c09050604030b0114030f0a0f05071206020904050601080603250503070e07080606040e0105010c02180702100b 78
    0x25014000b08445181440c1c103240c20980003920a441d10b0808000700b44400d07945000c1b2100d03201d050b0300c1013000743d4004583c1d56000c0317a42d1000d0741c900304500300d10141030b0080740105070a1540c2c4545081c1080b504005014110380c84204071001890203400041c1000c035a030203020300079404c1d040801d0311580385000e41545003150101400112241840017401090710800100030040c0710b110008094840301c00410295024200c0380c07841d9810806c44c0101d80f8108138003640254000c15000044100c0401d10300c2c0155805584444800280e0400d00d1070b040e16608098103071909000f5820800c05198018254044142d5050209540c1d10313006441c4000100c4045816410034030f042000d031245100091120f044149a45000c02c0d105c102003403819407243c2081d20292606406d0282180d00070500c1c0d9406101295100d2401c3c0c10030100e881c2c0010184111414442422440400c40d40d41440780165401c14181c118000d02c1d210100942c0c401c01540c84040c01490703e40400064140403000c0800c0c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 745837203 1250 745835953 745835969
    0xa0612110d0c0302060a021e0712020d03020708030301090c02162102041e021e0424050717031b03060d020d02060d0515010f0f08071d091608010e01 65
    0x2084541105100000800744011a0700080d000000700040e5a008045d00a0018681c010110104e000c0c210250b41c003140360811301f050744500c00070400c1500410741078030a00e0f410f07a0346c92011801494164600b48003500030100c0f0740804800828110135170751182a04a165034210b400d041824000c4070f0b0030200e14012030f200c0d266110b0480140186456080000d14406080018005101842c94490310360b40f013850031108d030300001c0a00d84100c900c42c020924907960846a0f281c03a103042c4201c05040290000c82401c1d08004030940c0c40039000707409071444948c00c5840c1c81010107520780c0e038091a42c0115540340d0345041281442c4002d00d100c00580380706000141c40c1071610a226020021442c801c600700703e03802034042010fa680750000d8080d43d8000c02038052076403003c9884e08000740451024042c40c81c00c015000f0340c4040040e0384612441c1d0018203034100782045141c1d0100300458050a4040c43d42c02c100c1c404203100607900d0380408090074840650b149211640c950350803d101d22400c1c403412013 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 745838453 1250 745837203 745837223
    0x50702010f110705061c091401062705040606031407031209140d0503090a08010204060e0609100833090114010f050901052502030c1f0e04020c030408060a0612 70
    0x1101d420f02c0c5004055036031925070915041940701c013601003034851900089030920b423801081d030064102400b41d1000340c510b510220b00141007010b00304d4030b1788d9401000400a2511200481cbc01d01040c1c0c3c0c051005144c00c940c04500700601c1401c0381d940d420440c4400c5030b8141c114140c00c0d07130580c421411142903824513030003203504c2098482005080404940309684501017000341030043d5440e4056200280045000981c86610708035028061040ca00651800f669081105403580d542e0001201194030260600c0300e001e84520420764414101c90100b02100219002480720030303101a0540c0c0b961440c01c40702c0701d6240e0f8035124008444540f4516450100311100c400301e40d0280208081c1003024018500f660070002840107054a0341203508080803841c14422141b070660800b4080c0c007800590a890000d403c1c82e41c1c0300f0510011840403100780030051840540d89150387c450b01190a821103140480c0c1c0c5441d01d42d6001c5485810503a407510045107040c80001e04121050040d60199412546d146 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 745839703 1250 745838453 745838459
    0xa05060d0303020d0b031f0c090b2b020307030911060f0f030a11040f03020933061b0c030d020d02060121021302031f030507031b080d050702010f1107 66
    0x54040c1d00b000d0305500c03543d600c61748100e146031420042d500d20300200d04002c5452100202c030702021035240032881d0f13040003240d020910030341046400722401c05c4501502500724081d80081549003002d11010510b1540c000024080d155038140c010104040c000e80d101380000d0068002c2180901c0780d0003651340001000d0007103800029036003001e03542c0301120250102d074030031070800e0b450b060754400e8120f610000b4032a00141300390700308088611b41c400300482030241118040d46c0601c02a0702845d12030350880d08611a20b40140c1c035200250390b81e0f0a04c0418002d01041c1440b0b00303a071034000015103240644259122048214400905a40c03158490380142030264285194a88240d02c19034602490100009a820058035540b0b81104080c800d140011b0300c9007482c985030402d03a848110300182c08042c2c1001400800c00209642003101c0e40070107641081e60740300d008410407601551100d0604d000380d480400303415410000405001d03100f40c1ea030780801102d6220a40351501c06168150f070a6000540074 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 745840953 1250 745839703 745839707
    0x501140603060a0b1201030b1f0b0c0a0204140703380a0305030706050f0a02071e02040902030609030901020d0809060f04051e1006060201060317031e090309090a05060d03 75
    0x6540020b809030400b01c0c1107450b844134002c254000e0120122406400c0c2c0100300703001000e07c845401030041d48224264034440c501541074001d0b94050400002400166410b1110041008000090780940309105010040d0046041d014046072074402090070580ca0320030008441d82280130b40209603070001413001114a0121030703100c0030781d8010340002c41d040c0c000c80451000c0020341080c0c2d1054401060328078100302c0880b20300d04007a00002e40140184035030000151200e20010301c0c0c00c158404035501c06080d00003c0c0140c000b400c0f0203034040c01110140041c101002c0010041480c080e002c4480d1206c01140417140d07840110dc0209454100c60040703404402150b10040d001401481255040d080e0403240d814001c06003c0703001c03a564040d05030807103a02d5080c0944c9000f0034280c0020080b076480d40e10340e8400d607550060158100c810000002c6c0403c1c0c5a807040e0454090310325804802d40c513000103650b0362584024202c0c0e1044004000040452100c5d015480c801d56000e40024003a017056030302 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 745842203 1250 745840953 745840957
    0x601140f031b030408030907050906014506090b07020f0603070315060f1101060f151e0801030308090115050607060212040507030b01150206010612020c2b020105011406 74
    0x10b03034550300030051449000300e081c4006940214003503405540d03281400700c40245004880e9014501803244501000156a04030402c42c0f00c99001c0c0c0752800115038210008901d80c81c007401e80c001c00704a0742010301c03111003d80c40d50606840a9132140c0009580361080e21840340120f0790000c2d44100d4007010b150030350405602a5400030b00c203040c042210701201c1c0100e081c04219400c0040000c41d0a000407280307a600103024070180c3c0010000300081801c2084245055803140a172060340003801880440d054442c6070228000410320740e44181c045100348000380207030b00a200c02e8000495030000314080d040103201e00036a4039002c07038103e6031240ca40010b120890300705000942e00c0701e0b400d01484501c00048070242d8483c0f8030500140c402541140f51520f0003002c1038210300b1405214595480c85960006402e506680250a1440040f1004155800640b080700e005400600494080250039048040311a04420703200281c000340d85241042242258030901c605554104050780a054034109140 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 745843453 1250 745842203 745842211
    0x3070e34120b0d0b06040b010813030c050a060e161509060e010e06070c050102010c1b08090a1701090c1a0706090515011413050906161101230601140f03 67
    0x101c041558107111001614000034400159110399207003080050a00e000d100350901d12100342050011030078119403c17102c800d011000103007480b500000344d00a000d030400400070f4895008800340030040320851802c2c0c5417508035808000b29003802c40049525004507403000b40e50700d4255031305140d0320b1401c02c04988580700d41c4a2141030003684041d2107202e0711020001c0c1383c2e150091480040051a0400080c01c544080b000031003000703203450b0f00e01402e945411001400d0344d00180da07140c07074007171313250000b0000c072625480038402c07404100c03901d40c0c082019007000c4591402176090340505540e8000950740e00c9846d2400c6065440100b0039500014420752000003040c3c050400c4440f40c211105551a5225003038001000908803504082040c0c83c00743c00f448402d00070484240998180b401c004c2c0c1e980c0b03501800c40140605000051460b0034401c0314040314003824a8020f12600c03000c120f050140d1615001500c0441803004001101ea5000b450810300101d0504500d44c50201503c0701d10300305800c040c0c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 745844703 1250 745843453 745843487
    0x20f0708180640030305070b07081608040204020f0705011407110705130e0d18090c090303110f1902091605040b0f1e0309010b01020a05030a0c1103070e34 68
    0x583c103d29403101500320314007451098030303440e96820803403c020391040300081902040144c200c0c1000b007069494000059544e07084c0c10140c605840750301c00107019024034403803544040c0000c1101412301805420245507240c512141c848103407283c1c8405c0350300399501a000e404a40c0881c00c1041282070041a8a44800d0b85d1500090f40c6135640a601e4100001000260b00084504074296482440d03807403080c00900c080041048920302180e0301410f24280340c4000340600a003c3c0c1d001407581c1040c040400401401025030311954040d41c4954203124400d00182d0143e03400310000b50a85000a0054440c0c0d034094807040d0920340b814410000b02d5004003044c500c215030500c5101914410002c4d440c51061155403055100d02e00a0712450031241000442c0d41194400c10711980820000301c00c40e110740006140c011400c1c1d0503828005155624680201c0d0944940c00000410b14180503240303000c0c1030034061017170001007400b11503049a02c3d43d48004541015105048029a0040760460300c494005 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 745845953 1250 745844703 745844797
    0xd020f0f0102030702060d1409010b0d060c0509130c260f1e090c01120213030312061206090303060e090c010c14010c090801050a02070803010513020f07081806 70
    0x135901142141d00240b00c1c4100a603203400120340d0480c1c0d01c2d64006d0b4880f40040003005040c6800c170024048024450f8064400c0e96109078601409210f0b80840340f80c110f010303280a000c503c0d040c00400040201460140c001071038080031100080071802a40e507010a40c2000001a89a0b80040761000c84080d0440d01001d41c0302d54441500101e4010403441000814040e240040d60755002400c540d00004118400d40c0c410480381006d405001c030030105480d094508007901d8003080041e0402003400746c2003030b01d2400c0768030b08c01010450b25400c0030015520a903028070842d0f030786d001c04001140b82a00c01c029181c000c00c2101d0481d5218601040c00ca6004502c0c2d07403000004404802c0c215501c000c14140054225001481600024040c0c142c0003420345904514002c150740381e00e0361502043c0200d6204000d50810301100f88482d405450314040c0040090780d13101c0301c500d0095a5a8042c3c65200700d01800301c51641110b160440c1543d9080c03078480910140d1000a0f86101da000009654100c1381d1008 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 745847203 1250 745845953 745845967
    0xb0c030903060708010e07051911010f0e0a060b0f030601060507050106090507020a0b0f1003060f0b04110403060c050909060405060a0305060c040303030b0405071e09320d020f0f010203 81
    0x7003005014016070701c0d41c41c0c5458a504143c20210a6200204041d091040c2040401030001d1850050b0b0054203075840d02c00058203240030594058030401c1a4030780c0882c1013a01d0101e03460004588410706500c01e030410802ca01214062180c40d68840e026968960850001004401e00840007010058401c800004041d0b0701c4007604011940d0030380300396005038001e111b090208242d408900e604a041c1c02000c04a924207108106902c3c001c3c0c1c04010a95922448500d4040800da0040c20a283d0028010b000c2029052003482c030a0700944400c0c0d03a020308116400f00003e024404403a03101c2d001408811301c0d0b1b40c510b41400050280500f816401100071800040400c00a001160264403403104581da0783c0d166040c0202641c1596141600c21403804041c060440d8101461030b41e101351810312030680000844040d2480fa080354418200032854400200035012211840d8040c042d8a005110061016006001390035402a100a41003030b0b10032020100780c45c10708000303680d90905104981c17074810 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 745848453 1250 745847203 745847209
    0x40f02040603060506010e0a050f0f030a0803011401020d0305070801140d02090406051f0b03010e040311100b01080a14150a090e03030a0c2d0e0619090f0803040b0c0309 74
    0x50640c402e880d030039a201c0c00c0c17240079a4000760100b01d08a040300c03007070822030824000441d203102d000240761040c80342c5000c40300c1584051181448075504400a03640325070303460540c60303643c1c03c0000c03c4a0050045104c0c84161030b000b03100341406208241d941ca41540c1c00d202ca0020003c45a010750359101c90040c41c00340040e5101c82c021840740d8400c81021485080c84000188411016400c00e40c01420f003060a1201180c1081500d0446401803200d080c0b03a1140d00701601c0b840c031944030310000c03030040781c500c010961500e030005071340c4c14000c0c0c0c0c0b2000d180c2c2c2c403c1c0154080340e041120800c50354020501107885540240064003860341c0003480c1c2064150361b0510b01c0704440c14020844002e8201004110100d00244200910710300700e41892600034080d1051244040348442d100020008518081042c1900c112800448040701408107603a034803c007400d400c488510041e840c03001500240011030b008800f041c100341200d044030000e40c10700b400c0c529008800e4110a6000209120512941d100e070f41e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 745849703 1250 745848453 745848461
    0x1306081308031306050108010b0607060c1b03050c2e0905010b03010c0309120206041a0a230f1b0906031b07150b010201270c030b0a0b12011112040f0204 67
    0x203c04070f034500c10455189000d80c02c0d294142e00c4103034103914244094000b44c03103030710882d40099031103840010094203045050710000c1c108501a9080340035011007608258012005080891038201120311045401355515842c0c1540d11250070b0244038810b1100340411950002100503200b000041008098032001c6400c50710710b40c840d2400240c0700c101007030034401c80103540c091005051014007070311f00d00b41c0c07125150540410007280780c02c0c85441c00990906000d0b4050f540614100d01040602d41d0842c003000c00c4013000b540c0403445100900042024440b002c9a40c2400da420326500c90b0800310620100151500003d03c500c0341340303441030403034040c2208280c02440481d1090155494028801c0304040458120307142d0613055a240c440000c864160859604a4541407801d164000d0141e6203422040c03101c0540c002404000e4038010710056040030340220f0b038220411755145401c410080c3c02d090903188070411a04030003808005440111581803111503005003c0e040c4580860625400f142c221 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 745850953 1250 745849703 745849711
    0x12030e01020a0c110603040b13111f0806010e010e060d06050a030620040e0105040b12161e0b03160c0f03090603050a020909150f1f020c0105130608130803 68
    0x142c2c1c9006141d04101c0713201d5004049640075554030b421807400750b80e2096080c40c05081d100000c0d101e09059070410403500b80c400c140c56005040210f029042d2080180849152084100490400d000080b140d51183c0e06940b40340005940320a41542c803c0107100b8680d016403180f221090701d400380812030b921000740520045200314000110365803c0344801c5109036240f0500080728008000421003005903d1000703042d6030048900040c1e41c0000c0e40010000003420045001c240600707000782c800c0d9036042d441002101c00c41000d000100101d03c0e00d8880d03000d2a401181c2204e0170078400304d0590342005400034906025400c00141d0034a041d02d0300c5002d00301c1260100c3c0014240041130005550501403da0082a800820350400c098800050104c50000344808294406140f00448968804106103401c00e005406000c076074009400f650b5107040c0307451003000540300b40c545024031540f0660481d2500706000300d01c1078800d81043c00884244502a00900b0328110141030040810004c070011405 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 745852203 1250 745850953 745850957
    0x60a0522050f060c030702100f0902090403090e100605030f0a140414071211010e030709020c010e1504031215050a08060703060b04060c080304060e1509060609010302010c12030e01020a 81
    0x3503040c88480a0f140080042101c0b01c601c0c000c0c0b043c411030310340000320124802542003020407101121007030b203001044480070195100710b1070411b000034990001c68070403d407469540e9405280c1e544103c0341c2e10180c080d00c0f03150000340e0100001a0b6821021007400d4101c0038001021901d59500015001d28650580707050341c141030103058100c00d4180401c000c01c02040781c08421000610141c540305111a4002c115605000c1144c140740c15030340e014820b541c040c07c510602117484100c4510400d000b402050300700d0f012803007440110b101800e814915030b0f114940c940d9503c0c840041c581c204d20098100b156040c010119142000f0407141d42d50120780c0043c4c070020b40203010340d14100d00002c098074415442010b201c3e00820050000f01e80c458a070310401608a601c07141da9481d02e140c140000d02c203080c409030b0386010340200c40200c00e05003140310b0f0003a00d50f1070485806032244810420004800e1000a0110344075580140000d032003200c0344c0f50007401600300000c9503400d50900c60300f640d00c1b190b03060700 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 745853453 1250 745852203 745852213
    0x40c0807230306010506030115090b0a0306140301110f18060a0806011805061b030906040b0306091f23040609050603070803040e0a0b06040906060f090512060a052205 73
    0x1804008614488034076401280140080e524001c0403036028841802030554061011059075200c2d4010b2903550010141c1d00c420701c0e59290907520040080c030082c09408206440c034030300030701145014007a1042044034400310514010511016002e607621240074480203e041d4100c060701c41c0e0391035001c0c1c1904142501d4010382864200d00040400c070004050b00b0203c2540c3c4e4007800661110000c0d1600c1c10b0300d42c04c888034078040e8810030500d18043c030100300385d100c0000135001c00c5d10039200d0090340c0220015101e41c03609840f00440140c95120181c041082e01010311700412040d0480071281044855080c800158800d0400c041001c0d98010f801c80e1916a480d0000d126850504000500046c003d40e40618185800e04002564a2401620a41b074240e210300700c603c070b19501c0c06c0440d0001c000c800410445240e507014041e005004074040ba00120300e20440c0000d890800c0406804031000c01320240c006070b0b54400311400200806000c45006580d480384004103901c02d0342d0203041e00382c01000142 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 745854703 1250 745853453 745853489
    0x10b06030105120f060a09120203030912090a0e0108100e030c1c14070b04031e080f090712150c050c101d031c050c041d06040915021e09031203040c0807 67
    0x203003865400740b51103009c545c810010094500c001007404402420b002104507551550758000440f203403402d0300060300d0301111400007e1000c0c400514000e0400840805001860035a11301544a0003101545c06051300300c40c18000d149030302200d01c045081540c0c244098164907101030b01285400051003295064100c1c0c2c113100505030001e202851800659201c0b4501110f0b20000922014024004000c2810700c60045444441d052112102030086401d4480c0440803608120b21030031240c1ea18401710364030b003c3c0114040c6101d40101d40345094820003d0400031143e4070709400038000007000d0180486170307480c3d0100069040c0000d0244050484d01c0d030840b059005c001000f120030291103041e696908000401c00b050404404603944842a0200086540d42d800418042c1c5a0745000030189054028444500302c0759502800340401003007024000710b045006810054030440c41040d62551004a442e20341a24500066034058482c80000c094075a58001440c5014200d030444261608900400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 745855953 1250 745854703 745854713
    0x1e0d06090f060806011d0c12040515060f0603071209120f092306030702030f07030804030e01030504031b1403030703051902160206030a0b090126010b06030105120f060a09 75
    0x40e0090303e64034025081651604480c500d43c148070307a051030340131381002c4001202c880d03a42094030041003a5404040c094542442c0c19501c818480d108448640fa030000403407064144099801c104040250402e0300d140c82d50704041d0780700035007440c80fa1861fa071035038800000180b4600401400c0c08054441c01d01804004001410080090304134418401c2140000e68010030000d001c100416030607202d41c1d55980380c190003282944200c0b20001e2280740006012420154001c0c00c180c8130b68003d642c0c6a40010394480110107554056070080c0c0001d2030b444083c2d03038504012401c9038001c0d01c80c0b078024003600800c02e41f0030304541048820801007944c660412084140e02d608502d43c00c90101c204500d4030f040c20340440341070580000e020740104400b1000070100c0701280d1090144220092440c0207079a9140980f090b600300303d00007d41d0b803030032105141540c158140100e04d0481b0b0000c007118110307030802c0240410f482c000e84040b0210f11481c0b54000301424103114542c0500303507010020844800034100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 745857203 1250 745855953 745855961
    0x30a060204181e0b0607080c0309040e01140a050709181d0d020601060f170f09010c02030a091502030f040b040807060801060e040e0c0a090228051e0d06090f 69
    0x18103880b06041041c41e0701d00b4010762818200b00b489594000400052050201d121402240c02c000c0100314000707800c0c003511100202a01602e2412035007481407103d0840e0317030382c01d80d8407105002c1201035120300070408050342c80d00072035400341a6140900d43c00303a8a01406035070f04600109a03c440340d407442d0381d2003d1107241d41c03400c0b00f100c00140106015019010b000350b440d1014428a01003207200c1c030300301d05003610400c0c00701e0000010f007054810038104508000303c240e00c1a0f40c426000d40c80e184e6a110840d0010043d42e00108584d00c1d1601460b15015911152030480e010040850104110001030384106002510141554004c005c2d11541081da415141c5140c03a082503080c400ba90780104020341d0b000c008003540c15025140416403060307190451780707030045140728a0b80c05104c190012910914942c05030209511003000482c40c010700c5010706a012114100200005038200200741a41c201c08044801c40800f003481c032854005000b1002c802c82d641a080406507640326040c0c81403a12941c09 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 745858453 1250 745857203 745857239
    0x11b080426030304080c010f091a150a030213091406010303140f0318010e030c160e1e0907030501060b040e150109140a030602040f18020703120e0c030a060204 70
    0x40200d51001da0000200c0ea24007000f00300401d10704000800640080c0d00b9046060030503101c0c0003e01c180050351030f18800505042c07801200c2607100800150040e0140c002c0840007540252000d03405508580a00441414030340c1007845a5031151000340001c0c40b20044040c14044071805002c032035056240062246032007010117100301800f0302c0f400c0c4400712420708690300400c041c040e420381ca0364516982805826600c20156140c040810103c5000070f0100b9600b080000b80d07808071410940b502607240010009030344501c540b41c0c9620402105070740100c8800d80080403602241c40050756035845600395401074124004442c40810208501071036050850b400580461042c2c80354854200000d116880d107200306007002d40c4441d0000b00341d4641680701e501543e013007c03041d03648544403028200250050711a01c0d0303e9840641c1340380c08100c214825101550392556451051554104400c0040c0024100220440c02030748410181a030b0308002940d4002e1043c403002d41c880c0d240022080040050741 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 745859703 1250 745858453 745858499
    0xa03110a02061602030a050d030204050406050d110f0a0e0c0414031c082a030115050c0c040f06091d06180309210d0903170a170402011b0804 62
    0x140c11400507540e400c180e551038000c3c20030340300341ca190b24000207142020154002d041d50281c0e14184502a43c1a001030055440c00c0c0c0e800d0003096916070034010702e5880b011000c2c01e1101d5000720081c140c6003641c94014801c03c010124a00c071078440340d04410702141a42c68020b031040005040000c0403540d002c16017041400c40c01b03840204036a4000e155000110300f00b05007000a20f070005803080b68074144845518540801d50050010000300c1c03030149034070030300074800d60349107828910410740c1c03080048611025458025141030103500e800c0c84050206c042c81071000300d0b1280d1020450b02c07601c2c03003044e85403500518158409080d00100343d0402c500504602e59010101aa002c100c9200001700c5604400c00d5921700d185030180b0171a114100c1390100480d0080c082c0b204002c0d12540d110b22060b040c1d90044200307500d80c4c480081d10869900c140080f4102044607000d05044000343c4985040d031060040c100525400600d0000740070101c180f000844a044001c00e05105081d0800130101c00c00c5034038 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 745860953 1250 745859703 745859713
    0x60c09060f12270606010807051b0109050c04061802030705070210030207030305010902090a060c0627030f05030f040201050912010c0504081009021f18090504030809062a07020a080a0311 82
    0x40d51401d5150413000b00344c14140805080407581b581c1c4240d08070f8119140f054044c03003030081c1da02c0300d45018081c4a10161780178400c202500d04140fa0610840088600000c0e022610041000f44a00a50001089032003403003030501006016803145860012410480d0b580160740b4001b80c41c0183c1100d0068100300d120a105115107100c5485940d07401040d5850b906000006a1103494002c0203414904549042c08121940390508041c000c0345410754148640ca84104411201c0002c03075460104440c0b01d14074204003004034015501860003409a11005041c0c08642800c0313440b4a800c1d24030110188000903000a010001c41ea001d1001038845921315200740640100c1d9000240c0c00003052184950100c40100520501800b903804e90018002800315070a40750780e50a07208000341000c480541c08120742c04002145000045540707446203521030100307040170006280207000d0000a085d6458131f8401084805d000d4ad68003110f19004000a03c01048200e100c0d1070024800c100e5a252041c43d507000c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 745862203 1250 745860953 745861021
    0xa0305040905160e060d02071a0906072a03120c05030603010e0a0f170c010f1a0108160f051b160f031110050906070501050a0e0f060c09060f12 63
    0x4425400300704c1d00030885005445803812000c0780024841e10740001d064160151f004144440007202403885110b0140541e8082e0391038020640d8901d1180300c00e26882d804405090406170801c00502440728042e1502440340f0f23400400bd182152405901000804c101100b01304440c079090240600098104001d0702c005c11056480001c40c1c144010018010100d8507840311160039010240c81141c01e0b900c000303100c1940302d08803060041c850a0031580d6410b071381c4c481c40b01495000d00c400c240a0403400344090709422070a03c0448025913080c001d28108a000c015090000001070020a8070f90a05c00c05000074130b002e2000182c0d07130100340c1d11000746407003105c0c020404200e038026400c0403464150381c03801d00115460030441e854490366540c242e03c0342000c02c3d150306100e0151f10840c0301e195401000c00401409241c056550100301d42010007039400310001912042d10403015002c0f803840905a0b6050010f80801c20314690814034a061080c24208100148803c1066032000110302d40b0061020240c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 745863309 1106 745862203 745862207
    0x140d0f201204080405040e060f0a0c2c041d0c03071206021e0a020312070c080712140301090b0a0801050906040b180a030504090516 58
    0x1152000d00300025030314000c0321003a5480c82038618105034070070205a18210000300111501c0d42c1c14000010b164a50307004240400c01144050b04891030b0404482d4070090000745082c1126042000120b43c85400c10106c0c1140c0301e81c6080d01d9128030075504a010b80c0440ca10602d074009140610b1400c03840c4040a5102069079000c1c16240300302e51110404d81d1720501c50103208013074403941030201c001a444d0f6000344513504003542d1400d6100201101c1400c03c0d0800c1c040200903810000c0c22202e10000c400b4401d034000c2c41402c00481210382034880c05058010410020066840c4200140360b490140c0541032080c880c8910040d92036855001c00d1010301410f894003801313100b139201d0119503a6810b009480c40344907140003c021075031380c035269006c5000c0e005d04038402060080c8545240d002c0c0034008070510038025110280e40c0c6150072030300c4003110002041d401da56604c40c940450301607 = true := by decide +kernel

theorem cover : BRFrame.Cov 745683453 745863309 := by
  have h0 := BRFrame.cov_init 745683453
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745683453 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 745683453 ≤ n) (h2 : n < 745863309) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
