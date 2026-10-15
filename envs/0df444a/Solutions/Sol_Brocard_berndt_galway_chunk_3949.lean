-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3949
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:08:33.927854+00:00
-- url     : https://prove2.me/submissions/ede2afdf-dcc9-4ea5-8b77-bdd31f50cb6f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 710071942 ≤ n < 710251798 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 710073192 1250 710071942 710071961
    0x5070908070b0d020c070e42031c091a0403080306010e01020f015702010b0628050421060b120f0705060a090e09070f0e04020a05040216020f12030706050a 68
    0x142d40071042900a23910703116204140c1c4004981050001c0804001c20304000c4d941c242e40e00b040a1b0408483c08982c0c120080c00b007078401c0303900d51901250720400f04e04420320075800050810340050001601315071141014014400c01841590050359444e900c40782034071501d90901d41d00e500d03d00460b03000c041d10801da02031050540c002030b48a540005030444004500381c014001a10645401c0d580182e0003508101c80840f00604090341d20360141600540d00000c82105420340b840881025140b0752140c425602a0b41c986480031000031941010171007030361400350048030044c3d01c40c5c10204460b51000d4243c6820004400a0071a03c05016401400d040a0b908001d2080109005007201181d100d00d01c4c40071303101c1d042c0e00d41056442e10b0421a03e021125403004200b2050000007042800b58500d00a004510944a10840e181c9580401007039010b003110344031841d6010b6100801601d03101c01d2901c4203201c040d000c0300c0711a00c0b0400c9581503a00c804000e483e4103494a0034004940424414000c0d003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 710074442 1250 710073192 710073241
    0x1703070f0905011b020406080708010902030d090302090a051b210109050c0d11161211010606120b0d02031b0114040302030a15022203050105070908070b0d020c070e 72
    0x90341c2c20000040e2000b12400c1800000c1d015140ca680d0854a0307940c45900503040c10011610160782d42c2e18298064041d02a0480c000d01450390000b0762540201c07101c005813940106040c07650340d50a0071072001840700a000d0080f0305480c11131007121451324001898800c10080010041048500a06009200681c444a0791914000070807861240031030544101500c42103000c50800a0a43c4414050241e2814001d081e6449a42c490411004d19280c040707000d42511075480c0d9405055180e42283c4507441200003041d002a507036110185164081050030400400f5050b000e00585c02007480c02c1e0600140079072600761166039035010741e08064242201c01281e2a558501800e41e40803d4440c02e1402e802040302c900c074100d00310300e81c0698040c0e0b94000e030000f4a4052442d0b9550600b5200400c505c002e980ca54a040d000c0b8100a10440019040e12050700080c094a441d0095140069002e41c0c0e407140707410340c24415800d40502c00e000c14030051492804401c001e082801610351940741140c0d00418 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 710075692 1250 710074442 710074457
    0x110a03020c040c020f071410030c0e060702060d060e0a0605090405030d051b0705030703030e0c0d1103010b040204090902090f090706030b010e211b0315040606031703070f 75
    0x950016400007030100a5501242d0380701c051405920b0001c041c16860340b0b50054600105a401c0c1c0c20000312481c1d6000c440c241c07103007507104900b6402c80d10041c90140021703401112610450402038001c14616102400040c580314024100d54202c03511600100c541c82d0060051025204d17486c000c05d00a0321007140e0405060400743d035010741e070348036016010b020300791503000103040c510003080c40540c92194030b0703039580d0780700054900603440c2da011000c1140824070700802d62000e5400083c4840306600302070240e80042d10f080e160102c5880035225810b0340f5640341d210580312601c990000e40300401e81c8400202c0c15205130320400007003150040c0592802140e4000300501d15100042c1441204c80c14140080d00c03210410040b42d8a0102580031038200d8042004003454161754a9890803061402086e0360a00c0c070a08a1407604c201145c108903410b510217060400c0c60501c027803400c2c3e00203125010002e0902d60b02d541d0112903087c603641c6503510601c007008120307100b07400000345c42c07184400e494400c2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 710076942 1250 710075692 710075713
    0x207030212030a090e060d0b0103060527150c09040e070510050717090a050d03081e070207213005041d040f05010f060f090507140c151611 61
    0x800130300981c400d501d800840c0c0c20108a02d034885440d210109a00b080e080ca0740d0f50384a00380a0007030001a203052003c0032104014040b00c41851086684042008014020407103105e6016030343c5181c060100c8400c08000c0102d41d0513940c0318844c480c2c2c161000301c05000b480c1c0c900f50410081d01c084802c0c42d8180300c0c0c00c101007000100c0380301514040541a0041d86d07211080c400101e01080d00a401598200c5840203a0f4030501d0f4019500c90b1140c48403040e452a17200e11800400c2c0e030004150354440160340640700600c2601510741c0c0d405040e04a100181445034516110480e45d9508074044d2001c4103400307803060320543d4180a06800001290610624081c40c2c80c9805400d201721044030315600090b070000c03404001c40701c054141c40c01e802500034858005803941d03000c01072800744181c07850700c20604800180381d040303405094032600850300c41026203080701c40c156910364070806030201c0c0d500a410081d0b01100c0d40107003180c0075481d01340b0040e45042c007200000d050320500d100b140e100c503071010060740b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 710078192 1250 710076942 710076947
    0x20a02030601080d080402100306030203011a10230702040e0303010306090b0c07050a06050c0d0501140418120804082b06050402071709010e0306161b030e1909020a0207030212030a 79
    0x1c86d04a030341a2a2815076142180040b001045240c2000358503500302890340000c00c00c000f844401155048a1107841c0d2503015100340d41d40750340c2c110381c1000035440041449104200d01c001c0c02d070741e42c0082c2010a01d408440c1250b4213f5109800440c1e03441d603a600f00b44203010168902c0341e0700c4813010184074030700950341c0c417503581daa440b010004000c991202e0014040c034894105480200d100034a0900003544c548540b10014454054040d010b6031500300804441c140215003026000d4105268440c05142e004e0103c66480c001082900c040d107040050014070480c00c03d06202c900b007131001c01818a42840781d50005d959042e4043c0c0c0c4240d0041c48644042418a4030f4460080200c400385c541d68064940141c0740540302c205083d85c503008503001c0014820083c0000001c61400e03a403104400d020780c4181c201c42000c5500042c1c002843e8502940d941d0030010030002d5405240e1945c00c000503502c1710701d041668080d81307000e00140c210101c104114144098580c07140401710014508000144200 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 710079442 1250 710078192 710078207
    0x501020a02070602240a0b030a0c08011505010804120905090901060f050603010602100c110312040519080d0f021c0b010f080c27030109120e030c01090b0c010605030d020a02030601080d 81
    0x34172028022004a2480800c80e8085245214003400780c80e02034001d0306000d000e420755446180029400c0c131000780505c1841000c00700544030141c44180b02500c680c0c49041c0950302030304085c0705000f64160701007101c1e6a1030a0b124071841c000800803400906181c011911404181d00c454003030001030006000450300803c507401070441d4614002050942c008049a0f090780300c0e441d030f40a43c0000144254041506442d0a02c00c038000d508490902d00700c0b00c0399403148100f00304080e0884100380081e01000c0226000200710109400e0091304101c4200c0c0c1c20000401003101c1c1c20000307a074802c180c181c1e03540c205014000e01c200c1c50402003036030303d001c0801100c54840c4e0b03d00c07144030b12000785c1c096000d005480149456184041c000f042135100c1441d01c80c0c601617001072404041404001c0306031143c5800901d0600404041e5202c100440c40d04201140c280c01100c020310103035403100000b1602d41c904028000781034a6a9000300000400740c018141451810381000d6815007060a034404695005045d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 710080692 1250 710079442 710079493
    0x203070e240901260c060406121808041e0e010b0304050606010e011b0302030c0a141e03071101030f090b070f05120f1306020c3715180501020a02070602 67
    0x4044040b15220485c01e0001e000c0c03c0651000d80846c0224a060b84048040c1480802034400c10800c03031001024908101240d00050070038001300014000c4900c0650601c03242032000911001013503c1d00503e9404450981004941c040c02000308401c0c80010070500390171100a0034150f80000350b000008042030411105090101e448000c49810144200100c0700002030b0b81c4141d03072102e50b403403405950202c070701a40900c4502c40c009121840940b6008241844400781c0011454028540e0f500c0064100c802f00f411705140d41c49040c00380954180c091300e18564810f03005a43e043c5044000170b80755604040b980d07410400244622100400c07200d1489800401d0002d00e588265208400f40c1000032600400400b0940003213072010f1580c1000030100c103102461000c1f4194607022022400c860210a5043c10a004060b2200004960301410b2410800903034100810103446c68914122100300c4010100d4150707500140c10b215840d03041c4440c2000d003443d4805012408103450071182465018803 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 710081942 1250 710080692 710080739
    0x3020d1220090d0209041109010b27060712121a060706050408090a030308070206010501080405060a091518060b0f060307030b01030207060c050d0e030a02190203070e240901 76
    0x1c68202942d075803c01c0c1d0714a182c0c02003481d01d440c500b80c07910312000140042003a0050012000100301c500c15607054034610110b02260700960b00ba401e0114005e400d40d02100ca80003c42088003801050280f651001c10f020561a05c1034280104001201212011301e0150044c0d1010b8440b00b0650760b81c1c030104d807141a002640800e2a0311181000140d80c46500240c40d0321800400340041016042104103119158a80a640d416030380d400054480b05070032100203100d41c0169000071042122580801a02c0c0d000d0b00d00d080100940c1919041101e54500b800034540903901700000800c0706030700a03510070510a40b0503040704020074010640c0c500003d0061814152504900041a4400d5055408039900000184860b101003203000c0c1c955403080380e42c1c00c0382501f001c030030081040c1d00008a4101d03505c3c81e401020000d0a401c4107081d4407403540b0b070480c0d050250080004040074a100c7c928000c4036001007070002441000b0090800c0c0400e10700c84c90042d654030004000c201d100b80c0c200156103c2c020f = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 710083192 1250 710081942 710081947
    0x605040e0628080705030102090604091d070602030d0b100c0f030e030a08030a0c09050f010c0305040e0a05090f151902070b04200a030f03181203020d1220 68
    0x90300240880880500c00b40e0041907000e0184141e20b18400304070101d8400400359800e880c2c8901c240b5090348966040c1a400c020204010444c10045a00c910311120070300e03141000c0000300045440c14103950303611250040c0d04c0852111800303207582c4103c0003411800c41d494901c4a10084014000102105025092280500c074001c140343c01070a06481d0000c0080603280e0032030a03442d09070340f244c005460a1480d1403403d40d18110840c0200c0040c001d07160018451070f146151140112188440d094003241040000e01000802200c001c1d816405200105000b04035450945101403422160b008004003c0d880038044038542100c42001c070350043d40d65007000c5200204031742c219010784550384000b40320800e00402c110074028504000e803e594240c0c60704540c5900300b0700400003462024007000c0c03e00c2c54941600d1002034003800c00c48000c1080314118111107540ea4829002e20494990300b41c0144c0c0040c0304104025500818925208600c11020402041919010700b0f010007501081802c04100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 710084442 1250 710083192 710083201
    0x1206070f05030907150203071203020d1107020d02040506040f0203010f0501181d060d080703020718091e02030a140703021011060423011e050a090b04120c170304110405010605040e 79
    0x71f0080318101500507040c0c40320f041007860000c00a40c0240d2203c01c0d860300e8241018100c03180300c0116807800c0d4004180101849494081200600002e84416405603560b01940c80b44462800035600800d5100ca15003c0540b502d00090154000303c4000d03000662071a00074000003c1501200908480d900c440c0400765a4007000308d080d082202101410003440403c608003091303800103c0000744c070f1200c091624403840c141c00050513200c44503002081c032990408203100c41300d0800c980140b2140001e04661410100e6114440296040c1b0a0754000303070040740c4140154148072500100180c51860400c4091121f251400c0d100c0c40080e20084c0300482000101340031980018961a04010300c03002005201400481c0407107440d100a400742150b0f0030000018102003d6209003078086810450f1443c6940e100d981d0a4030100e035407506203081c01000c48903440400c503200c500602c50981c0c004056a2410142000445060700309a820310581c10003005100055000040da0111182c20074800d105445 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 710085692 1250 710084442 710084447
    0xd21030209093601021305040204060203270d0b0f0903180105030a0f060f180b010c0b040c090204090e0606030a0c0612140a0b090a020315060c0c1206070f0503090715 73
    0x44982c0c20700300004000c3d1442403019401000b40700e000910050ba40c0e07035103800b4003040c0d0165201d440050380080c40405201d0710421005c0100569040c2125403c2c43e041001840d200012901030394006a0f4204208080225900040d044a000c600960501400c04000b00d041922000903c0c10072a02001294440c22190400028403204c0351080c88000c2c4c8804040522040c2c9114140028003049038891030b4060b0380c8524201e245040e500e10075074000e561aa408642e0026000311801c11110800160b80101c91001c3c00181262050114140a1140b000b40c41d02d04041d151a110350808004400007076402c1e1181c400311005800c0c41c000490345101040018140c0780c400c43c82101c001400c005d5500020b5100c080b8084040705c40145603190846294100d0204486400501400c210210a82c1c50b02002403c4c0c1031242208851141441d01d000c16005611008800401c2d8484030512010941100b0b50000c03103201d07460200e045103801c0604c0e80d60741410744203045004a00700e0442c9082407 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 710086942 1250 710085692 710085751
    0x1c0221010311100e03100c020c01111b010507080c0a170c0c1e0306040b16110c0402070f021822030c02100e09070503040b070905030d03050a0b0d2103020909 69
    0x2e9000301030390341840310b07261000050088001f40c0c50050164020894140d030207084d442c941d10344420004c01c0020240ea105030f120300803004502d810302409020080001d00303620020185031000740d002d44550001c80c07401c0c55041c01c0c2c441a07210242400d02c03101c13003403140000b40789090756000c41e01405c2c00442c6410b068074100031491059010700942c01000700f44180e510342240103251030072107820788040302c00c1c084070702d035003051a665500e4020070090f510f6858250054084940201d42c04949101694001100181c0340d0504054041401080100c80340e415158520300609180098035443d2031a580100b02c81c101044c020b200b180c170340840e0310f8903d128224080c840c2d0070241501c61a8141032501400c10b4200716401c4071790604030000601502e21520884040f90340180c0100760210035024241c0162000821020085503500c6004145545244446a505001d103140c013860040c3c001a004000070031040ca001414010461090a51a01c41040758482110405a0050600800c2510a01 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 710088192 1250 710086942 710086967
    0xf09041103070905090d03020c0d0e42180d0c0e010b0309010501061b23030a031401120201081308040b030a0203011e0605030a0b01051c022101031110 66
    0x40c841c1e01c10203d0301090715803282e8000c0c103100b41140c124007403c5800f1826485004101c1d062600400020b00c04c0d00d0252a42c0180c0241c0101030001c0010103241140030080450007070f4801d0403c000e14450480d0380388240f130701d80745550100903140440c9003c0c2e070100c04980d4403e140c00345004801e007805200e00c003800e241c0501840859817a45596920168400350000e071500c0045510b010000920580a65040d24040c000c40c41080440c42c40c5454802d25020700403440a180290038100036508602400209000360361034400244480c40c10740144070310070f0142c000c151280002031086000d40e800518070360b4002e00d03119003001c03420320a181264980c01350781e101000031800402840485c034034035000b07913050b00c021011918800b200900c4524003240303d0310454000c50f2040012070503169082c4c01034940000c040c1066031170709028003805c800365501041d2000d032140c4c1c00300381484000f500c40b41c100d0302003610110038440e650441d240c80b0144014808454403540000c0c04180c403190080d01000c0c0b07034 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 710089442 1250 710088192 710088199
    0x120306031e0819090611030909070509041409071d0c0d0207050703080d0605120a030f08070c020315040501060806100e060a090f0606030c0c051b0102030702060d020a081003020f090411 81
    0x7090f80000090201049402504046101d1400000503848000261480101d00400c02070444d12180c0040c0c8407540003092554000d6151220314580301155001c9600600a2030010003805107802030f40f80030854070b407000310901880403061041043c0d1050a444c1d401e04200f1005a0783c00c1b1030300c2c2c498034100069000800d07074500802c610b00404490380c010022100203070303141c00009180340c185a849150400d00240820944050404158070502c2c2a0358400d00d02c1c01e0505c40c0302d80613000241780282200031403205401060400040010a0040200600c0040018051744c03d0920700b4281440003801000104074845002400c43d03034850402e03000034400401c08214034404070340c40b140a45881c0c010709010078188150041024400c02c01403c1c902d8006018040f01d88001105814426071480c4090442c4814880e2002580e110001030100100d140300041e6500303040d4402402c0349200420013040d0800282e82040542c9400501c00c1e9201004c50b43c0c641c2c0c6513114603007004401003211210341c1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 710090692 1250 710089442 710089477
    0xa170a1b0f120c020a0f020f03010228030902010504091e0501080f071e09110c0321010b0307080c030a060f08100b121e030903010216120306031e08 65
    0x41c0c110800600c0440380340d03511031000c0190050002920000c00b8000c006900180c2c2000224000340c001680140c40240303684405900080000c3c20b90700b203640102e21012085403229002d01d840500310619046505042c0404d04032038001810314003c6200d490174603a203a85103440f510381903041180702d0784a810402c20855071504a85036a44000b0000901c95100303412000c90505c00009000d01810100b1a54000d07840c01c11004401502580c40e401c803440006010640d1103074820305c0070b850380495000100c0007020301c4900701d0340070001c1a40300d071601c01410800e204101d81c0c069900d0b0340c0400c01c038004951725144e003600d190060886a01920301c014103004049440c140100b4503072000707010542c0034001c1d88140b01c02c00582c0111031499825a0307001c142080140300510002054410300f20045d00e0400d4800400710f800d9034040b0840301c00c400101c00c1d201c1c1c200000c0b04140c0541111703620301089280d00b191f40340c041d00a2080003500c4c881ca40ca0500d141009148021941e031561518200b10 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 710091942 1250 710090692 710090741
    0xa140d0f1103120729190905070314061e06060313020307090c020c0433030b16030f0207020306041704090218012712151a1003020a170a 60
    0x40e09400c2108100d81c5e00c10403862510b600008241405200361005007800107a403110042a041d030b61000001580d03040d2941c1d07010020841c20700407003004600a0440c0804c0f01403042d41c0d03e00b0308000038084030848084d841d5030b88080030202c0400750f1010080d11019a00e44451040b011802d5010750025494032840c4c1d03001c10b03801020382100b2403510042d002c48800075440c03810001035610b41c00c03880211b003240c44c0100c82c107039000e2000302e06940302400f4440407841d03ca486584800c5421680740307000c8208800900049130345403044240000d62800118100300d1140c1c002a2100b0010b40080d1240c407000c0120345600d044001140e00400c501c540855542c081c960080910320501c0641d14041410021401d8040318400142d520b8011b500350171201e403034200b4401100610122900b07441602c2590412a440d640912800e80c2d402504410480000008020000e142c00c500076030008041c010700c290310113075800001400303248111021018041e90b400000d100202000c440a000d407050f42c0c05c402 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 710093192 1250 710091942 710091973
    0x1c05090109060f09050c2b08040810051e1012030917030408070b03090a1202150a1a06031b1308070e150402090114030a0b0a140d0f1103 60
    0x10381c664856401031004094a80c11103045480d6054042c15907044841064001d15228811001922002d4980f000c1c412140102509041540b08122140480041e0512501d40304000f4082e2100c0700c1142400070786024000b01c4020f02169100d40105005000429404240c0f0b001442c080d10030000e1804c3d02e540c4504000300f000c40148105e40d01c0d80b21003e681078030001c02004603410360b0030b04001008014909605d8400c16400103003800854010f403070420001400e6040352400107100e6a0040c0340507100d03d0001464000050507508515181c50780031000346801c180f510000d07400c00c48000e0348a580340c3c1d04460111004a401100c440c100240810260b41400300c5481a505100c007201c0009031260240070841400359a03040c06001854070f2600185003540003449080c0042c0f419040340f1414000486654000741c60a4902e161240025801b90420305c0d450001005001d0a108500a40b076010600d80c0d095504058000603041e00b00c2401c1c484441000201c40d81d000c6c0454195081c8000345 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 710094442 1250 710093192 710093201
    0xe160c02010c1b0302041802060909070e090f0a0f0603021e03010603060f0c0909020c060f041515080f03040b04150c1208010512010b0906190f0803030103020a0509011404021c050901 80
    0x120700c640d01d403480b1002c0b0b00710321f40ca14008050303001e07000515000b4203200300071007014000c0c860005c00c40954216940354403540c103094054083c844040941c0d081015545060700d0040500800c1c50307107041000c00141c4d0740d51511040f00001d41c000d81654184050200e4050700b90b03a00060b05207400c2000c00d2038900c0c02e90780700800e810001e5032440140da84500ca910242e08c9044034082040c1e00500c003003800803c64402070340c4c126100d03603c060703614800f03008154162070f0070b16404208224040010050907a0a104515802c044000034602e42030820155207142d001c0c41c001c00220313046511400400900440c1c4d40c4250315002a090204010754140040001c03209000d064050f501041c0c1c150024001401204107400700245500c0e02d65440609200c0044c140c84240d115410b8080c1c0000340e0110b03075071070345000392140e0b0b0003642d41c0e50b0540c0140b005401c0c1540c040741c01403c030741004012802400e2109101070304201c5e0056a0717103010603010000300d5040d4441900b92880c2400307020b00b44005601 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 710095692 1250 710094442 710094449
    0xc06030a0e06090d140412080a050705010e0f06060a050d150e1002040f0b271c03020106140316062d02010c032a080a02160506100e160c02010c1b 64
    0x7244d5485c80c1d00b80c6041001c600039840b07041d4404060a40690006944d00c010b003d1a400d1443c0650038072610780c5595003500c5043e48110340e6904407240d1030300418002e100240d0310010030b4a00701c0d20701c4d140c10049281400b1000b006050080c980e201b00c20300d46642c0c1c00007540d810001c421203103c41600c8040c07000a50103071161082c8003050400004014206806841002280310803400c2064045c0d403071f400384d503601c0000082d403020108405410030b88403480690802400ba9000044060400601c00305401c0380e040750b240300b540810b40a081112000d844070042c0c40c1c00b031074240800410750048050541050030360703c010201e41001483d0361136055200e281c00c21129a01844419001c209030444c1d00e2102001c074600602005e05c2d041d00c2e9005083d2941c01c1110000d006160614540b41c071000f40701e54400c11541c0750072410510003070450313004c17040340a03001c0b00950201c0c0d41842c04481c03810a11440049050018030107c540540e80038000f2412050b4100c1c40b40103400704074042112042a1902 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 710096942 1250 710095692 710095697
    0xb0307030b04082212020f012f1203250c0f062c030d0b1309052d06070804050a15050907090e030304060209030f03160b070c03020c06030a0e06090d 65
    0x704030444c840400004001c45540303200c51000542d182d000c1c003021182c0450103070305000019480d9145403000300a900c040d024801950181d00c0c1144154905141045005070340604d41803081c03201ca0003202d2441065882448500b072201c4c110b41d001035540520507440030300000d00d4079400100f4171025401040059045c2c903440c0342c0348280c814240140461500d14200300c3d62003070154981c03140040e4044542c0c60402044144004020400c1d201612949401228603400c6004041c005140e825802c00b0000300d1038107004605918080943c3d03071090024032142c20082c0e0341d0089000e008041c0480040369421001000f065824011143e014000c00e451050082c42110400200142d05202d86513070585044040c51841e19107813500c134042e40080700c030742c1d40c540640203a68400e03120820040c86a940183d40705118030b00503081100381e911005003110b0a102c1710808034000244d02081c0218202404c45110b5140d40302d107800174000b481c1c803890f0007806211741028040c1c8041b00056605848429a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 710098192 1250 710096942 710096977
    0x3090a050d0c060f110f03040305060c07150f0b04051006140c0c1e0616020103150b160606080a03090314030f041203140f03040b07210b0307030b0408 66
    0x154244a0002040340001e000200142e00c01d02045105698000c0150150b01e008041440308841480c10310450b408900f240758400901003041090502520703910000c03a401e1141814a107443d80700d18501410101c1d15901c2ea0f9104018828000e42d0050fa03036414081c10810040c50310408008100700349000700008201510049895210000e08480c0c20840300006086a041d2180500c00c02c01a404905041c1e10140704000310a0780312100900741c0d817024200c034026014600d0001504407800401c400c46480383d801d400f4883c013244802103d5204840411120783301d405418101c0040685070800c401c24010b204604c403c0c5940f12064600741c0b4001c1c0e480e804010042c070002c540d030b41304e81b202200d0504000d0008015845e107404d2a00c00c0607000c1e08115150114004450145a101c4494541c0d084404014407091004003102154466813a00304480f544003030912a669001074414410710b025200c460071141034405118540003540d10000d00e1034581818508114a500110341b2a184003001c03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 710099442 1250 710098192 710098199
    0x20a1209170d0c021b0a030b100806240a053105180f060714131a07120f05030a091e0605040302100c21021c020c070b0f0301140a080105070203090a 65
    0x40d10940c010b0417500034401149986507544050668000621201030002942d44c00502d00341c0c1840810720844100b0542103401d920701018800e0780859961440c0600101041440702d603c8071001e40311421042204030826a009012501d0265001c040028000f801c09061200c1c600403103803000c4050f00c0382d20545400031384c8840f405643e51411071341540020341565000c00782d90801030041801500d14040600115150b24407800d0304401c0f401c03100840400055100709201c03907403190f52004c05103403130044a1104071400c001c1c885d01000d400307540d500c3c1d41d0b03c90101c1004420204c82440722215110b003c0747c8540c43c24040010701c0121030070340250143d00c41c2c3c80d19480300f5110f06018070a26440d040000b082d140100c0d100700d11000d501e20300d907079400c010b40440041400080071042070701b070102507621002c3c00040d609040e899481001e92510500c40e21080b1341c2558103490564001400380081c100c48c88001480e41c0b4001e5003c81e1a07540307081700b0301c200c645e0301100074840ea04061740c498600d1a81d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 710100692 1250 710099442 710099473
    0x80f0c0904020f01050a02151501080a15150309020a08061e090303040b040609020301090506071202120c1e030421080601082e170709020a1209170d0c02 67
    0x20200c400a5000114100e181c0d5513600650103800c168450344102d070302c14104c010688004503020741d201482140b407074205580030740c1e1009189600503e910414041c21400103102c01c40e0609600884000a01c002c0f03141489501c031f030b0f100d5410603400034259850135540d01c80c100e0f2030719000d0320f880280401e507400c420f00361400d0000080c05207040a00071843c1d5a103940710210003140c050f10489889e030f20380039883c02694090184076070140c010030240100381072005010305104404c070710502c1028014012200300c03040c1007070516884a540c10305159185070442180e45496000e803503004029502209003c2404082d40403000d1b40c2501e45040300d8418010036050310f180c402103030380900003401000016000d0150920a101a4040303000e43c40d41412505c85c4007510124503000301107090b4a060884251410800411008101c3e200003186070140c0f200009024540c002ca50400c600d0b01d03102c24204001445286060041c0c1d030070308040e19042c111b40741102a0900344c0140c40144500711078402e00700b9 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 710101942 1250 710100692 710100709
    0xd02030f0a0902012a0c03121106011511010207050105070519170c180604061817030415020c04061d0702280305040902030406020403030f020a03080f130606080f0c 72
    0x70703016100c0310551584140c1c1040d015131729181108401704103081c030b01d0028002c4401d1901031449001c1c1894400844200100b81070048c0e10a001c0360791010f4010004002e4010b52680035400b02c4c07600310030450003409501e000e032080b10002043c40d86804100085c040c1c0c040d029004c102d038a0500d681703001a90a07030858001c480168080380381c1c0380600c04121070001c254010070851040e04800d0b0300300304103840010741d00e0700964400d201191001c40b52603058112441c51a02500e500921000640081c6907816540d006600900428180b450306002c080e0740200103101c03e202c4001d10a002c1c3e83c1d103511a2208102d0400c0000131405050008202001d00100d8000f06204100740388000c2d4a0740c0c9100540c941d01a000141c0501008100c0850b241070705000851080d401400050b95491940c0340092181c042140c0d018119042041c0c6100002e50103080160000c450314280c0c50140c84055109046110151000b071000c3d01e0840700003401d142c04141c010440c2c03154001e461020a0a4061000c5070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 710103192 1250 710101942 710101961
    0x114100503100e060f0307031113020408030702330904230403030b06070c1403150103030806090411130914280c05090405012012070c080f0d02030f0a 66
    0x84444a09203c180c0000701030640c40030b0010052200c140880d008a420f0001540041e5807403030403200325510a0800e584c0050308181d08040461400345001d16441d200d000c1d40d280284601100c2042c190402105040314500369517201d58513030741d02ca44a41e0000180d000201c06802a800d00c1043c242e220784591549a81c5885c3e03041c0341c502e9540b5603800320300238198800e140791322520034031601c3c01250020020f400030340840c0300407200d01e40c5007408052502d100e405c440c4080c0b440900040c400a90320040d000c0e04403000759440d41e40c070344451500c40d500c8180200c100340c0100c101139020160881c142c0160b0240340c0070b515031401d2201ca00740b41c691074110090f08101030410141c00819404800204040355a0090340d41206c0c00d44c40e44009850404280d4090f17400c2da4564501c90b0b14204080d8840554001c010401407801501d0003621650b40c800030300c142c003401403491024050280990032903008400110100d940c1d0300c034640d000c4000350025510001d019683e00d00150b04036443d40300d0702550 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 710104442 1250 710103192 710103211
    0x340201030c0c021f02210403050708030c0a030e030a0204022206091a073f0507020a03060507270905090c03031207020f0a031101050a0510120503120114100503 70
    0x4d918095143d501c4140c0030300340c00700c218801c0100c03903c08848680c0150040d101c584003010303680c501e10300301145480c001c2d400821440c4c00c00c2000c00311203c00010014401541070502c0c819921200000a060020a000c041e4126000140352001e1038801c007900201c0005100c805c14081da19480704032403011590182041c11031280c9105038080c107a00c40603101c06441004042c0c14001c0020384810440301d1021290040c907441000260407a007440d0318600300c02e00a240c510b0400c001900050110001c510020306040e9440c0d01042d0a51702c07501e030b02e6061049034592122140164120048055518410070800324506808a40301c00c001165520340004010015404c2042000031050201c0000e030030721056200d403414451540030107001c0070340340c03d000741c44410380044010030321425590014000d00c8070610384010040d038041020010000d0340c510448404456185240040c03942c8241d4441c80c00107072564000140b0f800e920762050030380721816a09001041c3ca0410203817403902050724002007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 710105692 1250 710104442 710104459
    0x4051e0a0902031905070f06030b06040603180c0b0306031603020d03030e07031218170d03050a11070501050a060e090606270906060312040503030f340201030c0c02 72
    0x8508540000007030078002401c0c0c2e6407070180c1c0400341260321410034007201c480d08201c0c0200b01440c850341400c0018012818107014400310340000600d503111358002d0500381559080000404140c41d651014a594001020b01c560350301c40208100b00c0c0c0003200c00600c2849110442403a14000441b80021660302070181c602010f00c0744d500368040c2c00000000700310b9118084001010840012741841800440e458860440380c40720012410185250050700300e150701100d0400b1840000110b00760380842910300080d95844a05440c00546081001d442185e1070100e40390050040650001d40991f2511108100d041d82c0d5074030307011900c0421900e2800c036400c044002510303130a01132005c07a0450101341041082800d007520445003da13040d40ca10003964800020454035040810022400300f0354108100c1c241031400001a580f4401d00780424000030010900501001005242c1903159a80344206601301e11510000c06407021004410703400a400d1600f03801e1a41e005019611085402070600f04 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 710106942 1250 710105692 710105701
    0x50f01050301092301060f08060117040b070e040f0b030d0c020a1502031b1506011e121d0d020106090207120503040213020a0c0b060621310204051e 65
    0x80080c80384e1204070035107070030903414aa103403013840c01c10718064103040d2281000c04082c00801080000010082410b0224040c10014202040e001d001c2c2d001e54850549820b41d903a41e4011603061409115640d089402d1190b4402d551003260000b001c090b00542c1126450308186104507800034003120043d410846921080c032110340c00c0d103210110400c440c0103da20340890028103400b04106038003002c015400c034140c20640080c0070383c11142c10500901c2d02075440c4081c5242400c1602d4029502d0701448040c918400c4e40c481c80303412116001b200d010701c0f003d200c140c120320261590751115506005504c0d0a00200b0a040e003032007920301a82d00840d02c2c94100288000596090b131020b0820b0703911900da56100681102280000d10484445a64a1006140030303e0301443e00d1001030103075403040000748103100b5507112215016050a40340800e241c0325803a500303485001c005490304e2548a18030044400d000c0002c0c4410485146d80c800d030f40400280d41c4034007400c520300c20900241c1d00103c07a020080b9 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 710108192 1250 710106942 710106959
    0x3031b231005091b10031b120c0207081c02150c040303020d0305090309040902010215090304210f24020a09060e060a121109040510080d0c050d0c030c05030d090c050f01050301 77
    0x501e0161201d0800290760465049100540022031021900241044000414404236405034420400d902d00050184600300840d00c2d4031080e50410003424100031521840e0454030810801c000c00e200c41a4010321410406e00141c00c0364041d003c00d4001d07204080c8805030071442445190711980d0721802031800c103d80401004003509031584141d0461242442c80e04010543c2c2c04504d02568005005550b035038645252010300b000300807900118041901040004038592204e01400035a200256000e5280c619510f08681d0316095000d0390320610108400c0b4015800103031030360944c0e203030740c481c40d812a245a081202504c2550042000162006040590800310760031104106103580c000c0e600b040c85241c08a0103c800450f400107c2418000c8104009042480040c0b90711b2a64640016079403502d40b103640d52400250200b1040040c40035040c001d0600c100454040381c0c0c1d01070706507952160803044c210043d1400e124190343c1e01e0624100050303180b81c04940c2040790702c0103845903411a031800441 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 710109442 1250 710108192 710108209
    0x71407031e11030d170c0f0306040f0603231b0618130903030501140d08030c1c0e0f1c0207050111010b061c050f0103031b231005091b 59
    0x11111070320b01d90120815560140680501c5405a0352000b116800700303400c0146044001d07211140494013041400da2140c03810046a600c001e00391000708200040343c00c5000181065480901150341c440c02050002c00c84144c58400b41a041c021951440c2090001000602c001640c8a520500800a5100380c91121046850f5a14000c2c10003c82d5206100c00c44150b9140c1c200803030000ba5110300500054030a50744281030750800f980c4411420b4040da4601055201c081c11000c405a000301d16a0031521300304032580e02607a205001440030510311034049507100d081000ea8407440c002c00c205c0320840c603d6000000c03002040c540c000c00a10346024015038801e500c0452002040d5222071706011765885400003805240510b0518640b00360440846404541000e02030100314a1a41c004001003036200048100000200103140240307181854006400854010208011912590440580d05000c520242d110b0b070303c1c010502c03840da01c0c05d00c402e445501e20001c4c80320399154006050441d0410420f0b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 710110692 1250 710109442 710109503
    0x61f060e06220513020714010e03250c0e06040c2d0e0901060e01020613020d0b07110a05010c1701051503090a0b10050111150601030b041107060207140703 68
    0x1080110380b03841d540030440d02c922101604e0b21441e00094520100300100e4042c1035801c0002c0000c22403101031030700c096160310178000f0307801d0030030403082000340001842e0b101003101550020b015100e85a4442d00016031502c202d584c0c41c85240f8015a02d10381c2409101005c0c0e40422030900d0801d80c40c1c01648030004540c803c01640c2c00c11020f00f20303032002501c600060fa8040d00b038a84a80c1d51510f040c000080c64000014084940030307601400181c01038480002a806240d40150604080d586403581102c002402015030007051085180c0c441c14040194088000081d1654416510741040384c0e0007071104c0000c0c4592070300901144960200ba9070b46402840e0461403081c00d4500c149100c2c1c944050898095a90b11015650110100250360f00440c009102d01c0e42c2401410300003409e011441d205000007001181810389580390b075002a6595170006000d00d840c54889a190006800c1001c02900401c1040714501485440b40d8102c50000580004490f030001c0c2200e40001780d4240e600e100c0d6480d10 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 710111942 1250 710110692 710110747
    0x140310050613050d060207050607051c0c03111902011104081e011b020f2b030504080904020409090c0e0103080a0c050a1403030709240c0c0503061f060e06 68
    0x2008103d950724070341422280d40c0544e001507110980317400c2031401c2100240c401e81c10310000b0411007000250820a42c0c01600542000040079045000181d0140943d40d11a8a0a050000b02802d842000821f0440b00401d2603001700448903011610115034171940c0142d51a942c040d8984150309401c4800640700002000c0002c80c1805500340f5140350540d89890400160304030f0400e100c6400c4c020081c0c400d03214010300c2c0c0030100c5841e108040ca031a41ca4000c00004041c2c4420000d818410103400b2980001e1024200715901c2e0b0ba50f03004030008100c0a04100d41c00e107082c4000003400050100100d040e80d4118142030703d0001c03031407419030744040002d030701b1a078034064200300d08041051108030046507034450000e150b403441c142c0030080c46441141c212820340486141d908071a42d0700c00304404c00da01c000b41010390905286041c4500304850319803140b40e25210385405c100001c0c1c0d001901c1d0000303410125900700c5c0280c03120816150b540408281503007040050000560745560310004022070359451 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 710113192 1250 710111942 710111977
    0x100e13150906110a2a03030b1908010605030c04090c0608190212041506080c060a18092306150906090a0602160f030b04020d0305040e0a06061403100506 67
    0x669940043c1d4140c1100600c80c840e01050201c010b58200d400c001c0c00680444000c4904440c0c500d901071a845414009002c056441e90403603616112850844c0ba49443c00050340c05141d910050a8040c1c00035000d240c0c0a4000c1301c6046101d0f0900303004450030554454036440c0100e0500c01e04454850f0010151032008616402c0e05007000748034401410300e52501d0b4100821840d0500340411030140341d032580719483d4a842c50402c180d02010a030894000c00842d102c030740d540041d140444030014150101e03180c042940d0000140c85601c6e610424001c20601c030145094280d18551010b01c100031160150404d28006d43c00a0101041008083c0385400a26943c00c040c90b038804501d050103150089030141e403004d030342d10500208503400c030401400400d0025011500b143c3d0b4143d006240904000c0c05034030a092500101801a029100680f071300300208607039417070418601c4020b4040c81c8a9040483d54081000b002c103a40842100d100348804144150b14510309002d000c0d807940700310020221b4a590 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 710114442 1250 710113192 710113211
    0x3031803160506100b13090b0310050a0c081b0412020418060621030516020303091c0314040b070f140114150306040302061801150608100e1315 63
    0x14642410781540100c00078440303840d080309802c6a00c1c074190803c1081100034880b0b4070411418000380c100b503c1446102041340c1c4029004685400c04002c09140070500340810040d0b07010481d40134015004107681c40d55425115004054a070034250401140b01c24400c00040c0f001d14109c03064039038880c0c4007820000e0300711220780b20285030060780c00040b0348a9849080400404601c7c0600d900041030f0082039060b003114550340a402131007410801c08103003040348052025907030140243d8104040c00b9000e050440e00c551618104681d0f4594220046850101c00508020180c010365003541d41d50f901052410065440d4071040c1c01405e8421241000503580d5445055020b010b504041c052044048480d4207000c4849a4080012001c450207079105404000201342c0c0041d28a4002c400c00281c8040014051011409841c0190b02210038051780c03107001507441da000030741610071a510a05034003025142d50848a81c1c803030a950070031704003002040b54004104840c241040800c003440001502c1c0b02d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 710115692 1250 710114442 710114467
    0x3090e010e0603100209010207050904020406080102070320190f152c01090302190804050402034201050a050c190b0f040309150c0b09010c11070803031803 68
    0xd8101c0752400d410303001804001c0c24200300100707920020340c0b01941407084210000f0342e1039006100d40b40c07049038604c002c42e081d500c0781c2d1b000030003130320354140203542c3c540782070402a00c0626940401c0b0203c008501d51015122008251150b02d20036800e03a880e0501c81039110080700c01004002581c400031000c0021241c00300c24805c4501861200c3c1e81c0c20218007014500880c6400d5500d080b1703482e64103000e41100060b5000c07403000e03110705001141a280350510704008500f03004607007200f60014400010b00200c0d1040a041e030f1003204071802024004100180c0540d120714940350f01c9200c200c8141c1c481d014560048020703090990b1140350007428200380b145180d1404103100d4072802d5000c4020111418440c142d640380764412000c40d040460380c1401d40d001405802035100f448002e101004224085a10800901c41229041001d50103d0300f090b0032100d000300b0f1038101d4030000c42d00312070b2814251034005c10307038a003200d4520001e5400e540c0c0d00c1e80d9030149094000a01d568501003089009030542 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 710116942 1250 710115692 710115719
    0x9080a022b0507080708030f03010e13061802090604020a020703060e0c09160f020601060f031107062301050a05031c0903080a091d01051e0f060c060a060501050307020d0c0309 77
    0x41c0202c0061103603a2501c140a814000503402840070b42e00204000d008481c40242160304680040e00504103a42e06c100c00e8030021100e0386801454036003401e40c0c081f1907000c0751610203500d500071500d00486407284020030040380300d24846180980c21040080001c1079070b0740e1001c2141c0006005555220740840001000c3c08011510004500b15141c0c50804042d4400840c00c3c01d41c945000501c450350400702c0151041a59420950805460322801807403d1903c0d01603c0ca141e60000c0240041c0d094101c001006000c00c034005200514080000545403802000180481314060050902c5000054000350410010004c21050046a95000002800c1d0380010508180e0982e1841483c03401c1c030821154401003003200400b4146064014001941c0300c940307194007110000040e079032620700c030301c0420f0b02c0f020341e18480d585c448400324002d4031844012a00707500c140c00b40f6508201098480300191164001030740c2000c0142d1066042c100203c0c041c9518100040c0281003042c04130740e507200442e5400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 710118192 1250 710116942 710117029
    0x33190503160503040309030f05070902030703020a0e04180b060a2103081b030f04050f1903080c070c050d0501062408090f10020d020c030c03030f010609080a02 70
    0x4400000700960860a0207a085001c00980782c00b62a50405441c01072602105000181c0701c08120344060081140802401d030050030401003d40d1245044c200240080d08005d441c480441c1d48418110102d140c10300c81d80c80c03148280d50f00c0542400741e07902d031600b11500041629030030000483c0049007400c000300182040140081040300708405034500141000310203000d1016080d403070903d0b0803041111005481e403000300314000000603640c1c0d081c00c42c540104101c1020f5680900032040030340303803c501008440c081c025200c04a40780c86960200c2443c0c86100c5029200781d64514041c0316514200400380da034940504000f1505540340c0c040c0b4000604101d03a490041072000c400071a559130024002d0744e1240b200c1d00a400c152101c0c021140c0c4440d102c1c071800440d00c1e40040d40f2012001554180e8200c0c040c0d8004498544000000d595034a500039a44080d502d15034500002d00644540989000d4500c0071001c1c110301801a0309101e03001102007111406001300312520158001e4003420110b58 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 710119442 1250 710118192 710118197
    0xa150f080105190b010c030f03090b0f070314251806081b0a0c121403010332070b03040611070f030f26100f0b030a05063319 55
    0x2c038140400703062030050200d4001c1d80010705010036500180e800c5015070f8607098050905030720107450b00e001200244402d0f6801040d00c07400c0010300400780c00c084401791180080e9201040b849881d664486c80b5a4421200980f80440110704050308504101c281c0b460320100d41007841c80036400140908405034984c00c1080000c031907100b000b0000b0100d080700a5544c0410350a6844c1100c10300000313120520130b69001d09802400c00002420714070400c00e402c0f40e015401512502c0756102d10308042c9005009601c0b64004503107444014400e0f2a0140c4201a0108a002005001e1070505101542e0700000c00680d1010355451450308150350b104020030200d0710030400c90641010390701e0003812007204081c00e0340030040402001441a240945104102c4210303204401060340c0c0d0080c03080b00c01e40a50828080d204081c0000240d0f1400c21000c1c0d405019403030000e106a59907003040c46a080703a0340d89442c003c415000b800302d2000144000c14042031402c066000d240c008a500e400703181e00a1401c40400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 710120692 1250 710119442 710119451
    0x30507170f03040b030a0c0903050c040e1c0c050f061003140102251a07050d02032502030703032003010605030603101503050c121f021201170606030106030b0a150f0801 74
    0x440083c1e845603880c20100d50501d020114115200c0c9507960352f001090034010740d92440b161002c40c904001c2036001410100d80526100f40441004081002d44501100d240c490b1003c1d000c460f0f007001c652540b081d0600c072950000c06245454000300c59000c1c8080317078900e5500300120507144a0f103d078903007580021b020384e07141e4500302440c000e0001020420340b8040210b8690502c00920303840300c12242d646040100250312a200c25010400000c241400515110510542545e00e1a000704c00351000c01d0207500d040101201c0d915007032003c07a407004445102d1010400042c0180c0d406a8003460b00a00044d04450741180103000c0c100c11900d400413656545890300c1420410003004008048126006a445081c88400c0725500350743c810302c020340c01c0060700444140c504912055410342d000808201007010079540e440054402031035442e80380825900410740000d50354181401140100c0750b00000095081d5143e140c5480102030b5801340c0b100000030140002032a41405d49500003030200c2200000c1c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 710121942 1250 710120692 710120701
    0x22a2536090b160207060509011d0301051824162102031515090d050312010b19181707050324060d030e040b1318020f0109030507170f03040b03 63
    0x65600c5160410f160841d40462070900429601805607039141c1000c3c21305408440610420aa917184e9440290b500340d860442000740d4090010280c0d0804201801901e0610b01d0b01801e08500503a01d050348601c6065001c045035600d41d10f98400300703094866182011008480300d48001c0c0d881d55010300c4903c00c80c2c001c024440e8075460403480d203550ba403003140c03003510144151480c1c0445001d41141144108100c1c0100006c0c031030184200d528000400880c1c1a20790307120001c1712140e8204440c0c110a003a9042e80d0b4641190065004041c411101204400500e01c1e18200b002c9846840350000000e000700800080c003614100002c09511526052200800002030303211503130342d240240707440d10602d08081c440004c030740c1000300c00104c0107041d9000f02d840e4802c0c0c0e02081070b602141d2040b0a2052a001140c0c440a080c00c2000302d6141c4212202140c401c04c2c1001140c0b03000d02404040c00f19042050200311242c420700e168425070700440c05959580c1051310f440c0d411500710764403400b50040c0000410 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 710123192 1250 710121942 710121961
    0x60a2c010603090b1308090a080a0c2310050d090b0105120c0618010e120c1810051e0607050601030c090207110103022a2536090b 57
    0x1580034080510b42008038402c1c0da1219034450f81d0241414840000d081c00d200103010040046921203100a44018100c0b5950401e8030f5443c0b110004c146c0d01c003400810702054001405a444a141103504d4000800c50100401c00801e0790041940b601070102c200b11a0038140c030180035181019004020040d030b590f240c2004c0c0080b1031000296118130b90072003150402c00350386d45000e45070204603012110200e00d40040040c3e521310500c0c0002d6901c01f459410b01c028038000082c00050344002503c8201e0444048140200c1c50321701600c400d001e00c1d1000a0a12042c1000d40030000801045820a150fa040f2800421042d512207071064030960016001442402207c01000d0004e03d2202000c52801d2815102d50a8800d8810401d03410140c0005505a0031000750442a11200d90b0f08201114107548000c0e8a41d00c100c0c00f4010700802c135080c500c0d0054442038950301400c9a041c00c2030305085203168011640992400003082400300a074195103800e0704800c2c4101e4207541c0c0b01d801111003904040148 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 710124442 1250 710123192 710123279
    0x613020105090f100c14070b0f070c0f091b0e01020d0e0f04020f03040302070e06130c020a060c110c011706060f0c060f150301150513110c0102030a06121a060a 70
    0x59400540c01f440041001d080480f00301c0354034226032020b41b82c83d10030a15001900d803080d58030000c880c058071100401c2000306940310040d030090441c3d03034003580094800c0a4409234003448006025800085076888414091f4420b9001d0b590001e0400700d02c040d15400050882e0845401400f40310400320810007019010449000541014080802580750201c0001d4200380004001c401c50350711070402c401c1d1103008200381c804c030950000040c446250000001095004a0380e0800c0c110701c90344100010950141011414001d8050f2050880e07a648005024581d444002640d54460003041003030507081e000e03c81c180c0640c1400d6080a03036414800000d00b162594051654820703458854142150301507580200100e5505540342044410801079a100030603a1a0301e064070030400280e2500c0f034810640c003c51181001d44801c0000e1038a41d02011420040284018100820a00b0000e240030500d501c90340d11003c0141412002c6440e483c0004007040c1001c9a00303000499405031040b030ac0300c4001c1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 710125692 1250 710124442 710124473
    0x50603130309270b0f030a0515010f050d0818120304032906100e06161506210c0f080312090f0304121e0507080d020613020105090f100c 60
    0x500310078403c001001005400841d440b040480340d440c00010f0154559000d03500c82004020180d85540c040c0b400c2c4282c0703845802100070101c151490004c2030001100b00101c051710740c054160340c7c201d403c40e601d180aa40c804a01c4c080000c5410074603514a54600a5050a0b141400e02540d11103255183c50b14080002c9805002c3d51250240745000d1401043c98490f40040308803456401080142c20545006640320008c3d40c01c16000200c0c103d8009010001415580c8101181c106480399804c03903004581b03040c01051445008075400200ba074a10b482451484c5008030000328030713156152003612182c42070ba40102c925030000314180f803200c0080c003001503101c021080500f021104920146440384594050240c200440002c01c45c04e20072031027895030041950707000380302c241100c2e410035555a803060300c501310a510500f0044619a4804148075006403a20031103140150510781c01594039411100900d500b0640801e004c00455441c8040440510140e803070306c0e0201469818103016000d0400c1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 710126942 1250 710125692 710125709
    0xf0603060b07030e0f010320040302010809120702011d030303010e0a051311010c062003160302070201020706050d0f1b030c080408040b07020a030f2103051618050603130309 76
    0x8882e10209401844200d40e581003114600c450b016020010780080c1122071040c3c102c9842191115110118000240280c90007602c80352a40d0351034a030419a1003d1000c50902620070900c800e40040d400340f0144800e009944d08400c005500c0800803d1950300240c0c030014901241c402405515aa24410310307400c10894003021b00000040d0f100c800b003880600d000c0d10f0401200b5035108003401565441031404400720040f20240005141030003ca0303410540d4505c0c100100b4a41001c1d050313011b4401c42e080990306801409000340f8050041e2801d4019086da03002d21074544c40d10705150859842120050160081414807442c64210000e0440c0c415411034001e02440809010200e0490800d69045031403458481d07075545900d00c089041a42141d000070312040e9014111010001c03040c18030900311f541003801c200303c2888480110240c0e41c1c1690401c07100e40c1c001d00c0c007240e81c91180b10016440004c1580c000390941da15004941640d10850304580d00022a003100c204060307000704803000529450 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 710128192 1250 710126942 710126947
    0x190b0f01050d0b01060f031e02030105012d0503070e030d0c0b161b020301090b0c030f060d0b1602010b120c030d051c090c09060e0916080d08090703020a0f0603060b 72
    0x5035218002d00e00f041c0242c10030301a02c001d400c401540f103038100d141599084201d4101c01010001140043c4d002801054049100d01405c8032404414951440c500000922900418411128192442d078006043c40d0304000c0715580c0c81016031002c200b2012504025900d001e44160399040521040c40d01520111400403c01f20150071380ea4840c0c00b01404d031a02d5600609a400383e0b1002a00400f0043c00c02003032503241c0000c1015040151025501c00c204c02c0200f0103981d5a88020410500b4940100030184244480490704209a188407540b103820140000a644110500083c04851070210852001e5100404040c0d503420300380040419082213061182c00c1c0304420f00d450390300c440ca11902d600215600c0e0510300500082460040041c0301d0300c8010070009840f02070354a03d280d41200c4410284c42480d5034180394181000b18881200c07048406043e401c54019412108110302070840f8021b0b00c20f8440100c0540d4403000844020701e00031800c40102c0c0c1c81d01c00003600707561a5901c04201c1400c00e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 710129442 1250 710128192 710128219
    0x200405040b0403090e101a090a1e06030b090f0a0906060f0512210703120612120c05061f090203070804050d1d010f050c0a0c1e050d080c190b0f0105 65
    0x1921b03044c0030340c0d401c10400304891040a99a01240c050384031501d41c0f10001d210001050040c0c00c602c40b00c2040c0d6106848001c6460701400d034250b55500380040c0d00426000006042c0c485903240b00c64101e03084004c0071803048159201c290643d6140d41041c400020b010504008a1600d000500e44605410000d001c5040b5040e0031021681c03550101400c1e00300002461108140c4684007009520003080d0080103915140c143c1144413102c040c0e400c960904000503454001c0d8068012204811741c0540100f0319940c0385008100a20001c1540c0b10740000342e40303008100c002c0d042c00a5803050b912940c1d6a0310500d40303400c1c010714200480c1c0e000400c0c00300c092540403000b001d126401c03035595000e00340161094031b140001c586911480407101c0071405103010303000400490301c204400302d400743c01d200032845140d00721100d981010303440b9866020004141d0100042c0303c007009002850303182c0007a1400300c94004500c4544000310b0408658a00741e980030888009032020020b80900fa040e176005803840403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 710130692 1250 710129442 710129461
    0x201061401030504020a2903070305040212150a020a0903060504080a0e10020303010608250e03061b030604091a010603021e040b09010e040b0a03080c060a18200405040b0403090e 78
    0x2801c4c01f0307030703060391402c4054011070840d904000c5a2201c0091040781c2d50346410314008008050640b403ca120300f0003500d081c020301100103000c000140e107100080c01182c40d0300a82c3c40c029440086943d040c065a00d000001285042c816030344990701411000380e840486034402441031f0b114244240c07007006095194500c1c0e41c1d00100b602d064400c1c5080010290700c440084c40e4078001503010741c541c000180d04044940c140e00150301c0398161419812980c05403144010054a00b9583c050300340480c2061001a0640c50682c00002c030213806405040307051000103c0e0f45400000c241c0000e4042030700050401001456008038103002c1c102403905034201800c020907204ea610526010307a04002c100522801c540d60340d54803a83c0c410000500f40c0c00d0150307491800c2d400580040300b1580241c0241d000148401c405030060500601c251121340d0744010a40d40d40345502d03110300106001e442c000d040c05214644441c49454022400782207550154030b402d180042c603000c0540c0210056900d11001c0c01622030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 710131942 1250 710130692 710130709
    0x30c010201140130060f0f0b030a170706020a0f0e04150323030c0d11060f060111010b0d1103062a09031c0c0201090b0c030703210c020106140103050402 67
    0xd96803210541c04070400c0c102c60b0a5440c903070401440c4103e101e41d644c410410326130702001100401d4082404801c4070002c006040390344080b100c58060700420080f8001502002c1130340345002d01010224101170542e20340380101c0c1c001c150f00c000442c05000301080341a030840300030004040d00311818400104404521140c01c0041c1c400100300b541c4100002003910174600400c21050703c50401c43c0d4030b41d05c64424580d41d906007101c4400200e030001d4007200d045007001c01c1c0180b0a108003e98031a464507000c00440f1544a02c1400c80c0980d580c2c0e01321203190303a84800c09044507a0042c041c80303518a50b00d80c2058217014024210040d00a10080d080d5200c000002480e101c25503141c0c18903444449000119082140b0000c4070345002c21440c00040d55103402002c0107031458000c0c0c1e2034621142e00c80f10800042d1084c1802540c1e503510130b100309000684203103401841b1f0120108803880142103048540107642c0d26000c6400580d44560042c040c45e070301c0d03c0030740d4044042460103000c603081c150089039440c03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 710133192 1250 710131942 710131949
    0xf0303011a1c0c081509010e131a0f01060807050a0f050d020906030a020d05070503011419080f011407030c0c02040c03021c020403050d0503060609040915110405030c0102011401 78
    0x5070010480c4002a038418400c0c145507406084180503580010500400416044410f800703d103031207035042d51480c00c03c000b4a1741a201020001d0200313455000004820303c0d030080c0b0480d5105001400a071802c1ca0205005004142c480d0088049505001d409840140300519150401c041804864403650344049042000065824580e03626010300c13030404007070311a00810f640c11400c000184019100c0da54000c0984445052040041e43c44a580440c3c0901c400e22401d010541600701240301880c007120807000800b844c0c049401c61640d80c1d01d81904000202c1200c5140b1396440300b00c02e104809411103580d000307150349803c00c0300340080d000180591707610380c202034003581d07a0303000010f5803d0195040358090302e2044a945a003042440901000e5030050008952074010300da45800081d005106890142c0f100170000d82c01c12400b1001c3c4402011194001c0d01e5018443c4100585002c985c40345945681140320301e03ea8484c2014145131504c41440e410b24110381c90055080e03c0045941c070f4142c10f4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 710134442 1250 710133192 710133239
    0x206070309050d1107270c051c0b04060f03050c09091f020f1612020c01090b030a0519050a0911090f160e0a0b30011203110607030506030f030301 64
    0x300c031128280d40d04c1c2c4071640d0040600000e81481c8820343d06c50302e01c0780c04103055043c002408072600d020000c950340c0c09640c0500142403a2044140d142c0303555900146501c0c103002c5c100043d120380d03030a10403080750120350098565820100f0303005060309211039072550100662006014815005032440a403185d182d40030084e480c0d0105c1c5882ea0600c03210119007185d20b4010f8000d80540c91401d001c00c03407441100380e241c054895501c0f000540e5000311841d0003180c1403108441e055541c3d507156903025000061664011400c2c0141640d880400307441441e010340020280051010799500c0e15444510100300501e01c5801400100441c40710f6040e105076001f030510745007444101d03080c4001d036a000c0b078000482c1d41c400105400450aa00010050034010400207281c4500d0700204111030b010300d01d10240c1c1607030103070304000502c5200641d0040e200d146c0d100e460b000020000d161011400c100d01514084002038581e0f052291503c1c00f005011500d0204002035480c46d403400101d10454410301c04201403 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 710135692 1250 710134442 710134457
    0x5060f0f030f0d0504061707120f0e070e1b0c0d200307030f030c0c12180f090c03141005010c02120102070303051009021c0207060914070302010206070309050d 70
    0x200c0752814480089901407107011030305044000c900242807a0054040d0b5000102913910109420044011040c00385405171034014170415540740ea031001d444c00180c2c0c030380140c1e240c8010304544081006501c0041036800307030341615410142900c3e91100820780501355131450502c40c50070f018501017050120450300e030800143c8401030f040d50000884032801100e0303090101041c1103040c940c01440070b4101c030510344d0f001c0141d40c0c0101c101303031529201e07103201808509200c00658000d41c01407031b59039182e1001180030041c0d16914407490b2018111a0409440944c48150460365660140210b03072007402c1340d1000018620f072100110317034400c0d158820207040004d208111025911004a00341da0240614000d55480c0b0b024100a00505000c3e642c00d107030301800303141c0026010014800c0d98100404410307090401c5a0381c10081c401ba40107078406803441a5104034103800940c0c120880342d078050780c60014107205c51441c0006410020000c20301c0c801d050070001003100060004c0b50700302048949042c04203 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 710136942 1250 710135692 710135719
    0x20919110d090201080703050708191104080a0203010b0301060b0f0f070f1a0c0405010221160f06051b2508030a090c0f0f170a06050c120a05060f 64
    0x20103454140c40005600d4400910310414002030340003698101d0003030700d8912160300d458100b1001c96404442c180009494540860000300c03150003102d80d45c1e8103158001c5240040c440701d01129502662140b106680301040080841c2402e0140c409004c10480080240507e4002603414038440d240e484400c0703503400070b2284200b00306a016613141d04d0b001801c4243c1d100c0341e4504074003844451714601a00e24009000a24440c54901c00c0b5401c3e05d1069002d441402084414001c910380c108002c081c0190041c00309c10614190708421854850007038030014403182c0c0d2030030007004441d80580711060400d401c001188a521a40e400c8540d100c9152001c00801e44004a10382484201c0001c003e0102500205002d010700c519003200c0c5855008114108805580c1c034080320740c030301c15849040c0c440c061541f02000410030991b100c503105142c61090302d40c850a41d0340d038101150001c40d0289075030300001c81d1190711405642402a03200215000c01c101038107060001500c4122188940b500c01d070189007000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 710138192 1250 710136942 710136991
    0x150f1a0f0a1e03020306030f0706050f0a0c050f070317040515070807061b020d0203070b1512061006090909050a0803103803040b010308070215030f010807060c0209 72
    0x8541d10b542003080a00380c0950040000c0c0a075000380c59407480f0b4815140b503012020030100f002000c4500b180c84261500030040c3c184409600002042d0b0140440909401c0c003041c401d020707915000641c0c401614009081d40ba10391440c03501c000303800c00010810f1000b40601c0d2603a81000c071034203c80015158481d03c0e24a01008180f20340040104103c0c100718506401c80b007020403200c0c80308030345d40a480035410240000c0380c0d28003407031101a100408540120752608804042059004c2029180407080410301303946900e000402c0d5641522424070000401c081640720440f00003422140f0030504c064801d507210b140d501c2c281640080c01c00217002010504c0051702c008548000c082040702d900f004811103d0001041e108100015040d0145a02d01c000e8012041d0840340705c0d940c48080458582d00315192503001790000c65003240c100d0029485171004200c010040d5204248480d0901c242d07604040748103082164981c4080c05010a0f12140001683d50f06c1e42c45500400d00a8a0700c14444401c503070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 710139442 1250 710138192 710138207
    0x7030f1103011a011d0a030b0709030f030c030306051008070e030705030a0615120203030409110d050a1a01110c09040809040204060c031115040204020901030f150f1a0f0a 75
    0x840d600d5031a284820b00c2440300c40f0000d181241c0240c88030b49018104440b01c45181910881e81075215145000500c00103403a00c1e0718070740258941c42d08013607141d102da0301e100451725104020b0300441d400c24880c004140d4140600c1000c3e2006640e24815103038042006400e088000c2d1051062081034a4010703451b841c1004600000c2000a0032540b440c092420610002c000241600c0c0700c1c2c0c41d054501240c50401541600c600c1e42d4003034000c0d0301c1c1c04c6c40c0840b9000100300d20421680d000200b0020301d61400c0e01401028080d2010200001c0c0c540004008101e20140300822503041c010111080581004003089003080044140c07800b88580d501e038503040d0700c1032142e1165aa40180b0106011507090340c4942200c00580c030a407504c0311401c00486003207584a0811004002902c41a4001401400d15401800d51000c2c10b06001c0b81e01300311b00e60303014280e8005407001400c0c5a0440740400070340303038541c08483c004c2040c0b54010642030b5600b45090340a104400c0b030001d040000003044410785200312003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 710140692 1250 710139442 710139473
    0x50601031a060901032d05010b0703020307080a020a1505190b06220b0a05031b09060910030905060408031e090a020d020a170102041805070f120917030906090a0507030f 74
    0x71006d8801c50741882c000d8843d202916002c0915141000105903100c0700300403030304502c1c0c0507001107081113980d1b039a10f0380c0b55102c0c0c020350045004441c200303400640e91040e0f50f0f6181c0240750b4007240500c2c1c140c141c0b1101200c0016421000d5091420403842c40c1c480d08110b441c00c42e140e821801c080144001d1300d404101855108c4a00060009441c1014a6200000d907000b1080b5810580d0b00313034210342003e50980504650240e200c41d0400c1640344501d800404101084414100860742103210780b02c00341403640403107060303038074080000400413115459200d07401062240003400c3c80c01c0c201260380c16541d41d50004020300828081c0007401c2035590b8441242c0003004800d11080945948a024502070f4000e0f20401407078228440644501628900500f84a208a41d03a100020402c2da00200c515104400d17250412030750b01c880d0a0007040342c21140f0300480c000c07400c1095480c00c0091400f484c2400090039001d05400c40090240014030208800003182c1d00a284200684050300740401050103649 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 710141942 1250 710140692 710140721
    0xf0402060c0f0a06090b06100909022503180603062102010516060902010831080f0a2c10050a09170a02101d130b06130801050601031a06090103 63
    0x880c08020090150805d21045200e40d041562a8461a05210b2440807004910000c0f4005500138046550030b54040c00302030060348400518541010350880f030f140340d044400d0b0700182086402a00a0b100c4518580040c01180390030004d0070b00e4030359080303c80400d503001131707904e007200201400a5a103e81c003941ca0105400c4049580c0031900d10f0001c2c0140300c0102d04034086080f810000d503030808045a0300d02c1c100042000d050084807083c0010790400b01e892411501d80c1c2090040c02c1510040e500505444940340d2201d52040007240c3c000d0348200e1000ea111002c00c48624007800c465160400307600544519400d0040d00c3d800d0440e0300f511149400d4000d1002e112074820500c2240d9000240250010f0086e1031000d00b140c1d550804403001d4050a5101c2120b849413200541b55080000d02c801009101050001d21814440e001555642c0000403095103007070128030900211000b81708854100c030007401c0c104120002d020145850725004c40c03e00b03208000c042143d900a0b400ba8012414101540 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 710143192 1250 710141942 710141953
    0xd0203150c0c060603011e0e0f060a02040e0a06050d02061b1f1b0f14070b0a0c02100902180903161b0501030e0309150d0509030904050705030f0402060c0f 68
    0x1d29040d00507041505011094426100400e140e402d0600c036041e20300c0201d0350f001d0180800c600d81d18010303003220941107159203d2039228030116002846241c0c003600c0c5041000d6a11450954650340d04000585410030a0303144c0305c010041941d908205e00301c200c1d4190348030764a40700740c0202c528599004019803a6980600d000d4101a41d401200300408007440940802c0480c90310341c4001c900c804e1442c001740210303440700192201d05010b21480c007025000205198a040415070b00d243ca405030a80700c00280d01d840305100e154a94050040701800440201d0400c401485600060b1031860044584031444d9401d20100d040c80d8824000c5504070186d01c0042c0b00860000d18204900b4948542c0308034000c03220440205142d0b120f4003500c40c01e907000e60700440c100300c103410403c07854405465000b0300c803803002c001c01140f4400f03501525100e241c00a0266480b2161981444141d850003410002040801c2080141d406000c84002d500260140c1c3c09545442000450b10301e84140d40178821711a1154 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 710144442 1250 710143192 710143201
    0x22021812032b090f02090a0b03070b090d050f1c0203030702030a05030613050403020c0f0301200310030b0708160e3a08070501060b071a04020102010605130f0e0610050d020315 77
    0x20362144548003031086c0d038400c1c1c1540d5034010110440301c422a00c158581c03c0030b1810828100044041c02c5a0800200615100000b81e9125407038030414241024950b00111400700007000c01a0009501070741c580007441c0341d858441c200a449100300c5010070107004001c1b01142c0907072641c4109015040d03d440d020800c82c00c0904010750748543c04040944a0045019260f000d400c06009110410101e11610000c00305000020969030704014480310804070a6035000000c07801c0c041d2118000c0c0041d8030742c4582414203240c1d489000717116a00c840c0c1840700f480b6466601d600c61400d0031040541601c10070b60b039030f200440300c18144c0c600071386030034082c0312005c0c500f105100c403040003850f0f410300c031318001c01c00180e03500b0110610340076400020304006a2803010000c1b10204006240d0302500c14030000030741c252180d00052142c1c81060121210344d40c0c1c2c004102a01909124203040e1802c100010f000c24600a0b060300084000741c09a24000c1b4100c0342070a08645041000f00500c0030101009982d5152 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 710145692 1250 710144442 710144453
    0x2a010b0a1e2606071d01031e02040e1e041a0405010e030d0606020c040603050c06070c05100f03050708010506030c0c01020405041a090c2722021812032b09 68
    0x40781c802c8100714040c1201060455008403100d8401580301841311201201c03610041d401012107502c1c14042c0001010000d1380c5130840e10040003e080c1c501d00007001424002c540300d641c0300e00d02c00200e0501d10b1480a01c804100007140e400110015040d4422440d69a46403041c00342451003c100e0f50ba10020658144640582d0080800c2ea0b0f0036078202c07010440605c0420081d12102d00c40034110b90040d01c48007140d03003454801015101c0c028482c5403030041c1e0300c4010a400d50310281d4000c0008180d00f24015440e50705002d42c0303820030b2161070f00059650412000035668070018144800902c0c0000d488802c6d000290161401468000c1081000210000c0c1e0803840002003004580300d07528207400501d500640109480300402501d81007602a0b03850000e54032865000081517034098099070410040c07080c02c0e21310240301c44540c000980c4a0b41e140ca0503440900e60440312a20542c1c2c3c0780100c6951500c00802c0c1c4910a10702d2107100001004482d5810380e48850040812041c1e0514009109111 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 710146942 1250 710145692 710145749
    0x1209031510180212011505042c0609040b010632030709080303010b07150204050d0f020a08010b090a0207031b0f0b0a09030c0605060102030d022a010b0a1e 68
    0x552429100c000c48220108a0b400c92141014a240c01045a0f0060256030300c1d055102c0e960200504103203160580310400265208144038040100308041007000410551110000b904040291584207641c145696141c0c0002c20501840040003004040c81050b82051440d0304640c041080e4440c2c0100c0049401034280e500c2190b402020615141001600c0d01002007224121081c0300311240c10981542d0780c2c49150743c0300300c03a00c240058080c00042111350b620510824114410741d14645201500e10500c5500380c2d40354000c0c0b10991401e101c0c1d40b0b0640b501000c003684100c1c10400141e0f00c600514043d91a040b9810088400314240140701040103000300034010207902801664006655000c0c150040c3c2d50b00d070350001c000640d214260f200044154101c07941081050050b0703401d01800340c442d041241c0000101600092340280400f0860020541448510301034000900007403040d90041060001540b10340228141400088180a50790185a03006030580c41c0c240491102c081901c80c8078030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 710148192 1250 710146942 710146949
    0xb0a03090b06030601080d112409010b0f030a060213030501090b090610060c030807140f0a110703020105121b0a120b0d240b030312160c051209031510 66
    0x118080d0081101d91070000755150488034000c0003010409000c0d502290366550708c0c42c02034405d108000388400020160000c0450800607040e60050750b103080c000e024299982081c42e40c8c080e001c80c400c891069103000c251041d207181c00040242e9180c500d00100c000c20403450303201400c0341d40384c140010708101c5081c4906024414513403c0b5001c83d100c0c0d001c0d6040c05820f0780b06a0003c2460b1b00d00840c0001d0207130091a911a102c0c2c2403e403120300005d0080d0a480d400b10980e9800604005452800d00740c0001c846003403101244000c0415508550019042d8454500300032036010440c00003c528440986080300d95010400d429620b07108080c5015000746001500e6800b15030504a441910742003800381301c548035411040440207040c251703000388403a15000c0d010031411910f444d221820ba85041008142e00340504083e00038a2600c081001400d4a40050030810030200e003061070041080040c0342c0101e81151825142d403901000002840d10090b000b80880c500318030410411090300750310291084 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 710149442 1250 710148192 710148203
    0xd02040f050901090608031e09100f020f1b24160b090a031d0d0f0b0f060307300f0f02120d051b16030b160309030519090b0a0309 57
    0x343d98940044405580c1c1d1401001401e07802880b07502c02c22a403060b0185001150040d030b107843c0c180034070041503c0640940441020425508601d00c00c103030704010b155a501c54034009050b40d00304d050a0b0301142c1070318201c1148112540207810180345d6110400312551503100302d405a0380c0b001c07040300c2044450030140550360b6902c1403001801d95900800d0342308032503500d6030710444014441c035810303c14400001c0f80d09410014002c4810000b48001c3c6103840002d0107019451a14540310750142c050807002040e01e4040d82288804102212070680141c602e011203101c2040c140c07072020704400e001c2c1e50076140031b00000c1201e616042032150071064112464002e96203402810352960301076565080810700b030000110104001c645e40c0d04103030903c3c2440c0781c4200590310607201d8055a000156400c0d041a13400b20488814800386543c0e120b0014192201c1f801d0601c4440800d44000d40103000e1801500d104072a050610300350300c0c1c4109641c2000d040e20202e225101c010a4a0041c028240181d040340c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 710150692 1250 710149442 710149459
    0x6031106121927050106060c1a19090501020d06060c0507060c26070c06031a13060504110d0501140a06110c06181e0a06110a0b3c060d080d02040f05 65
    0x711f140c8115074110451b0780140a0708002c0f0303d00c5221045518000305081d18881919160180704882070140c13500040c012400961112502d20300581140e24070f60042c400d006000a40c00001000800e0039022500070307040501103600c55050402c400c45e0f003080100c00400d00c01c5520426074000d80d003d0500c960080e609c0690007030712181d046e0201c1d644440032241ca42b0440045001c00c0c40c203402003003405100101c001c070b80280d41c2c101140661f441400b84a0341030501003607100107003160344651801032240c8148400210710107404074400c0352030b80c00b464040140040d450805036000b00414401c0007806401683c0e52256882844480c843c0322102074424010350016030b0031203443c41c03101c0e48000310091402281d6031520000b80ca002c06a014159554020381c0d00d00d0300403078a0200101c0c031480b2501100c030300c2c0d40b41c000940c00001001d902003c689501481c07070a103401a2161285030b0014045c1d404881c140000e080148103030050030f04000c540340c0000b8000c250081101411400c403401030740e0b103a1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 710151942 1250 710150692 710150699
    0x19060608160315140301061805041e0206070f05150702030319050c09060306011206090606080109021303141023060604030b0406050612010c0306031106121927050106 73
    0x10142c44641007401c08044403d40c040c807070385650945a4160001c020000583c40c0e5581c1c1010f03034507000c10071038a800155540104410300080841b4030400031041411610020700303079400200d040c080d84902501c01040f02c05254200302080019618500f0100380894082c541100002e6407031340129148070311a226460005070040c16402214010908201281d0820100f40180007480d04006d00703040c10480c580c07203d49544015441000080c0c100c071580410310900b4910064241c0c40306034800e20806204101c542e01d8203410702030010503a5800040189900b8002c94114541400b141c4c0c3e0403142e510302100c03400c000002d281240345400200320710030180d95604041013428000e0f032101610403541080010000b400310b0303008076403188000b440c2400d4220803c8415003150000c400c83c9002ca035440384203005216481c442d2120a070002c498851a090b0707605030304d0070304003006071881a040d440b0021103480303000c0542010105001d083c1d6030021410003241c641c015907400503410340d2030f5480c002020 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 710153192 1250 710151942 710151947
    0x30705100605190306020c01020f0307030b0a060813060b03100e030c160303020d0e0310061706010e0c0703030b06071e030f05030f070c0201110d17100e06091906060816 74
    0x40d050b4500703043c1100348030b5145840314030195018001408582d5802c01810340c110003c8c001031030003241c1c0d5660000c1c4d0045c2c5001445035240315500000c0911402c5000c00903c034505850071400c0c2d990202000c00c0562060010030324101043c44000700ba00c1c00c2403000d144040340000a841901c0d000000c0b00c081182c0e217400b415005015010190050700540c00000096009180c8040501401760860f00c0a40c401211f4904a402c56000701191003400e0308a0101003404105060141949030b001e03005508040d41c400b9260312900800400f07040c0c1728600758019a45802c16290625008911305a000070394448902c00303504032036000c401003101080c3e00342d04544107100760380c03155020100e1540b9a03202e2801c155900c4500305801c9042091080b03070b8000e040c0092181003460b0032241c030b8012020381072101840c03100c0c2c00200010014614000c1c104880444180c115070001c0054540c442c00d07440b80318071301243c103c2d50150010400e0800000280c441c4d4400c84480c402c1c084540e800d1034444000108 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 710154442 1250 710153192 710153209
    0x2030f2d0a030b040f05012411031c0518031608090d050309100e0d0f0f210207170703060b060708030403020c01031a0315090a06050c0a090b0307050d1508030705100605 74
    0xc4230710740380e101d650059408141e03644400380c100d240c0c101a5022140c010394107256a22141040411507035642e02c68043e20a203004642c0c004059041d94801c10600300e9089560f401181540034010045e07080c05400d0040c503c0445405480103481c204894056082c210b41c5c030b0380885807050103000900d047c00303ca644103a01a000c480d00082c4124040141c0340ca407861860a4418103494440200605400140784a80c4986004c4141d986840d11a5000f5a0103801c002c0f10764040c403082243c040320070401e407401107030f0a000d8070b5000700000380806101c00850140d000d1248004c1990303000205100903d9000030f12961010700c240c2c0e09001c10100702c100341654420030b031200c1f50142c0c00f010600b4003811460020f41d03840040c107021030300085d207285c07a08801d4803001c1c0c1c2c074024070a07400201e0640442d4000038440282c000344507607900e0341c180590020814400d00b00303c04481a500d001104407103c45100c404000d000c4c042c100c03511031000713040c45503d540341034040710300d0245060400101030511410 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 710155692 1250 710154442 710154449
    0x3052e140a06050306131103041109070f020a0b0a150303050405270601030e03090310050910020a02071a0d091104051807030822030510060602030f2d0a030b040f0501 73
    0x21518215281c807400d004000806500510151f5104d401500038110950007844c030890150488086010584040c0203050b0005443c2e0410420307a941c00120302c5800040c102d100c2980034015041503500e540000c8000c0080c2a28000c41807004503000061680c00b80161054400031680c9043c052080e24040c0c5044c9092400d200000d1180f0000030829030003030b4496210381180740140c03840c01080c04002804d0080c051106c40d60103a8505c20b110442070100701034060515501011894116800c0303010750340700c100e4450100904c03039101110865811000988010312440801841590358510f0120020250410005e021b41d2070180040c1030121074900c1c0300101c0340c650f805810490700f1510b8071846603105039103407005440c810a02e0014204840c0c0c25200850203880900b081c2c103041040c550a40d07403030723610005c119803050000c0014462450100d60549450002c03070340c20484803164546030078044003002100b00c0f41c00f06050301c0310b903056040358500c21011602000410f0b00b40421404840d002e00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 710156942 1250 710155692 710155697
    0x4e060a082a01230c01110d06030501050105060307020303010509130c090218030d09060e0109121110020307021509010c050105010f08190c170a0f1b0905130303052e140a06 75
    0xd2840c070001c0806002050014804c0c1d0002c03440c442c0c50040c4100035407002600e03407200e5680710740410a1080a1203454050300003150841d2460a24550080d03981c0010300405201e1041728002c0380703a6841d01c0742c2512800e54455803a9582c25600c2007110000e40001d2035001500062144d652114a0049110100d06e50191980580b40e811309104440b48402204450306000d4512008584604100c01403943d041c801e030b100740050400d032001d014800d20301d080b2690540d841800007000603035402402d0018504400e070710755100d145080040340e5404190780054100e5181074000716019400d00380d04c0058a844030700b00c8040c40c0e0840c500b803031420f00300d0002801d10030300003400380001c511403000d0311803005121003100c0200c0245c0d02c036840c1a08405608030f40c3c4c1000d408856a0484060301c90034010088441c080219181030014840120003040c030003070170140e8a20010311480764000c002c3c000202082c0b5499a08443d00810310801c22a40c0210307009501d003081e8540c518503004039410f090354170b541d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 710158192 1250 710156942 710156987
    0x6040b0403030b01390614090c151204030314040f021504030809060310051504051f020c010e1306080a140106060203160c05064e060a082a01 62
    0x4100c10b03285e040c5401d9000400341015000702d400700d0042d00490020328134400700c041c45400c3c0905054a40458404291b004d43d4145903004035009114064420540010340c100715199100c4c58100c0c000c1c4003441c020711049402034244010b0040e81c10800320071520070f80700100c42c54541032002009010780e10000b441488100711100c42400d11001558014580400402c2c83d26215000105450802c803c0c0c16440ea00116040100c0e1603c44544207803480741e00e10081c41e08403840710007501c80802c3c50444d4144034800c1004815512210604c04100000e4a030400605841c0d2210540f80c90f02c069007600c59a12400030316050907410b01c9920704a9015400440c5403040511500d5111088602c1c2520f1401c4d44540c001415180c0800038a80c2040d00d07041401c00c0011180400001d0001c18191a6030000311203800c00a2100003042203140680c05070800c0071035841c40b0020f41079001c3c0303030440c0c80039004510640340d1410201407540482d442408454644681d48401111703140c09410740307803c440146 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 710159442 1250 710158192 710158247
    0xb0702090c400b0a0f05090108010519030606090c080c0c0a12020a080307050307021b2206050d0b16080601050405041a0907020c030f070e150d0506040b0403030b01 72
    0x40e007070403070b007526840707500e00c00c114542c0c0041c2a56030620f58080003c1d04400100b0392000707544080300040340c1c102420980e051110040000b40110f1050003018000c2000b60700590907644002d4001d0006d682c0f0250510220351101d040d4006001c980000c500481e242c140420117004501c400e8420022413000102590141d64450480d0307110b0b0100c80c90705501407280380e10086464080114032070b84903078403560b0762401c1c000c0000789000101103640354160519250f40f080782da034020000f07041203070403101d171050401150094801800607030b102540c00701140500b40304100155003010702ca0000c2415400240b42004019616504100d03282400100200001d020a02e0182c0c8880d54511880b61020007040140000c18079284051701e0f00c0001d41c1c05038a40b105035190802c01800350008030b03405030401601d40b4800646c02c1802804046180c8400160411240c03034890a1b11300d881c0d085000c40d052410f240c00d001165601c269000c1d00042e06184e240c08295000344c58004517609140300c00a2034424 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 710160692 1250 710159442 710159497
    0x10090501030c08041a04080d061e0605130e0606040f031a090d0c0318030203150a240504020706020903070b090f0906090f040201030e0a060f0b0d02100c0510060b0702090c 75
    0xd00480322087e0034000e0a0300300005201e010040d00801c0e100b0324840d1000c2014951441e41c0d03a02071010004108034111820340350320220400c460740788044074441c0e00d555000410a005942141400317070034080c400400c0c000c9041201080c0c1451442150346900c500c1d8540b40c589045549040105030702008480000c1d110345141060754807000c055a125075180d03800030b410400740420401d11203001000f8002c9001c414800c50a039894005442419074200c1e11070003071417500c640705541c466a40070030502d042c8103a5404aa1695200806450f0519100d40100032660400d4000c031740150500d00c405e03207c508161404600a01d0010458800d0380c1e140c0c100f49440c0340001b007049041680769105030305007c00030444070509c4ca2044c0c4c4049801048400c2c28012078004c5a0782910400801b0801c10150f121240081011082450144000704c21810003916080c01440e401080300e1404000080200903d0082e14142d0b10880345e503080c0762180c0c80200007074014070045603031000b03001405c0c007080d05 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 710161942 1250 710160692 710160743
    0x30a0f120908030a0207020112020301050307050f13060f03031403010b040e0405011d0d03050a060312200a110906042705120a050a0f0f050a0807020c10090501030c0804 74
    0x10440840466001c0c010b40c1c441a05400c161110188550003091107400c56030401404c0a81c000c070072600718210341c9408002941c0d0021882502e016080c40c0e20302c40b03d03d0b116030b2060790b200e420825040c4035540da43c0780c6003211100d02e8402075001a038059032031516180c2c807100700c0e4100d44101c0070050a1a00f005040340e160b00000d03208403060341d43d40030750740045050400c1140643d07601c08050a03010040c940d0180035158001c000c50016450a1000d10004010180c2c080a010107817424103000b05500c6000e104000124010000a101d1007401e0000c00c2210004803200c0e2030241c524207a00c1e15402c0c02e000594910010b00d8040074004080798800c00000110701400c44e0140d401c980f01c6032041440036219a010080381030025100240c24044150005010360b401c0203546041c0c2c040d403a00500c024042d000b0b00f40900304100d030070004201254420090f0410201c0001c0144910108034000600b00809900c94107010904000300d441110340182e808a100b01c3d0003c1e482c11140909401d05000310 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 710163192 1250 710161942 710161967
    0x108251103090d03030b040e010e060a022a0d1d0a061d0d0606050319050303040b060d120c050d0e130c05130305030309060a0903021c0509040c02031209030a0f 70
    0x5100602c5000519922142c6100c0a44d020b5100000d0b400058400e01c41521080614940c80d81e041502100d542c20307000400d5503000c0950040143c955001403d942011190542c502c0d0b5051340b80d00e4502100507020480300d0314042a82c45210ba410610b01a0116040c04103540c00e034070407200b09040020b140034560031012148040c01031160000c040001503111004000306032a91581e0305014801828108034084c200307000c80d403141c10302c003805076202a528400180020513089204012071210f40340c81040a2001c4d07032000340d4401c5a1442c000090690315182019286440749800c4403071503a004514651400102130440b0384030208141c1810080c05290308a01c0c10000d041102d030900c03003d80c1001720040d610820245980f4105034450b0340c40d100780175040009492500c07603102c0c006900069049800b000e0039440342c6080704110070944a40c040e8080b11a0424100040b98035115808130040008841a00d400103160b1036591410f99280a40c003200400704012101407601180505223441c0385 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 710164442 1250 710163192 710163227
    0xe07081509091f0b031b0d030c02040f050a090c05150403030507050c030a0c03030f0215160306051e011727010f0204060809060612120702041d0705010825 68
    0x91202891543c00301c40b04145941d003036030b0fa00d05040500c1c0c681400000722030300031610746030040115a4006071840c5080c1034000c3c140710600703144038219190303500306891028009404000d18500b0006c000050508541c00f141c0802140b10040b420380b401038800c3d004a050440c4181c2010706554060343c01d03034000d100640f81032048200710b2050b075404004802c0c04920951041c600c0d5465803034058807a0a282d00d80c030055403c030b1440491035104003201d041d48040d20600240140116a00540003800c164010a801914009000c8420300e800c251000070900700ba41e41002001c441e01040d03a1502e825600e2880c04008807a012940c8000480c0441c000c2400d00f0000070060f0240079000220f80c010707070089011a03c000100040d02d00140076007603016009817079084403032640c118001d4413484425002000f0381c801080300300a5480785c0d48102142401c804c1e140800c13090740c4821a40d155003921509000910b020002000c400350b4100da480300f521020510070305000c0c0c14100342c401c5581410070030708 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 710165692 1250 710164442 710164453
    0xe06040e011707090209010509010e0d05070b1c020304050616170f040c09150b13090e0a02030613030f030b180f01090e0708060402060a051201060203040e0708150909 73
    0x82550252401600070058a9103014021118000702d070704000280d88035006051040c000071100766005000c0b0389449000340303003100c82d1050b800000366103401d0002c0d0181ca644540b46010070748150860061041115440f50003492202d40c080745420381c482114010b006410000220381100d0104000031840e41e51400d203054143c041e00242c1c1d00313100c0c0c1100c0009003642200284814030850091680190030303017200070b012080300070504404030381c01442424144400000c04400c402d1507040c105018080310201407000000d800030b00c55442c101490183e2281c019000411929000c502c00020300c158542c031151010784840005030001c244280c0119086400d1410480d01c6c100d0302d40d601d62044411160f003039803d504003607a800486280403140212544078400070310150100248080c0d00c00e41c1112595074403260050f00f224180101d40141a80810400003c0b402d240c010010340306491282c503902d641c84e6211001280c0a000c16541c4241c2081c1d49440701113242400c026540e4801d009000301c54 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 710166942 1250 710165692 710165699
    0xa0602180904060f06050a03110d0309080102160501062c06060d0f0203040611090303041802040504090c090c03021c021b070923040b01120f023d02060105010e0604 72
    0x700e18810884044458555403400036410110611680c0003410050b9000030007942103039a81c0c0d00210004600510031a00e1101040402d032203102130308060040e410096469960000030f04144040c0707504102d40135400c2410105036041b246007100048138040c104002c61a200b9411a101180041e1145410102c1040104003414840c050103010540c0b4400c0160380e45010b00700201212168026000401810845202d4a0350000300b9141030f100300340d01c5030101d038000c13407180402403249500032358000d03007040c0f41401802640c05441d411a11444001e0120034030740c0c4012800c92244110300740070b010031702d03020041850341c03507001d410403100c20540256034aa41035902c81c078103a120b80c010004941c030340d10746445440210030900c0380e030688802c0341411403e01d03a541040ca10340c140100381d01d0304800b01444051011100350216482e402810010b108940354050040d104040c0340541640f0300a030800c40d5601c02c0e04903000504030f805a024005907403c282c01180c1a000490417294060401d10010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 710168192 1250 710166942 710166949
    0x403120905011d01051005030303060f030705030d0302030714090607122d030b0906060315010c14060f070509150a210e010c050711010503100b1206010905120a060218 73
    0xc0c400b408007002d0307140c1a01683c0c0e469080d00d00003403c0301660100f611080190b901c001058981050301180d01000c03408a06001c81e140040c03a0b40000d0381442007119030040b2581560080d40101e480c0d541e00100030b00102d500e0720790b9105405c007403900042c00300300317901c08190000d550a024860510f000600e1444041c8541d10b20b0380030003d0320440d1030060750000c13500c2d80c151080726044102954484414036110000800c0b03804010049107003c0032480c1400c83c1684900d0050030316562192002c85e4100801104a58a042c12504c1c1007142450b800840c030224015810b450141000408101b5522460001d010341ca80140e42000705000c0c00b00b40006410001c46049136103400841c000280e140c0b040c03440d0f5400d5030711881801d0240001044a0300201744d11207001e0b13000b01000c1c00e106599450f241090362010303190364400e000c0c103400440d20141c21000e003a107450003100240d0700e8601c07903038944007002000d1001040da595580e1000c0320b84030026116070003070809407800c07007481852054100b012 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 710169442 1250 710168192 710168201
    0x306090a141e1302010e0402070305160312150b0315190b03040204050601090803031501050906192d120f05010303020a0c090b060901051c1e0e010e06040312090501 72
    0x2041d1801841803a5514000c100800043d40141100d01002002d200e0340c00284c40024a60591805190009008401d1601503000c8864403882150240f4580c03025050080035409800348403040325080031440901c5480c030300640c4c800c2d14030041d0b2242c44d40c3c4036408400303600381d8510001e5411114003c0ca405010f107241000c03100625540701d002e80d6a140510400044a000406a03410b00161031420b0150100010950b503100d1701e800d500100550360032005844ca40103a208050303200c0300004011030203e4807031600c81801c0c0c1c5a42c985103041e049402c0d0002001e85001708410341d2104c1500071840c854401c2410b0a5000d900b1140000c00810200c86036081d41c400b6002030740964082205c80040001802d507800043c0f442d102d00b0083e1024440c0010500d100c1d6034800350402202065100003091841000b8040c0c40800034208050000021010980344400c403600600d20728005e060340c0810410f0150302c4211203c00007418050f174880e0390586003009082c6034001400e544141d40380003c0c03401d100c0c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 710170692 1250 710169442 710169451
    0x60c010b15132103050319050a0609051605090409150905070f1d0a020913092402130b0309150f0423060402090c0c030d020a020d0c080306090a14 64
    0xd802c0d42d90307100c91503000200410f6406030742c03000208a0050103e40000c0c56001d58250300d864107554a450b087c6401098810400756003008a10f8802072049050303182d0310050484503040410301080d40e0305000068000c41c03035410900854810003071a0382c580381941c0f21044181c031502c0504d80c6040310b86440000c8508821044401c0d0f4050312042c003908079100030170401019889003251944a60070001030784000c1c0900b44900954011a03660441d81d501031a000303d0a060340e00400100c00c1504181c4400340009a50340c400600680c00500200458021103030409103103645402600d00e803d1031031596a10040c071502031405080701c0a80c0700e400482186016090310f800041131401c1034207148041e26640810034026540169001c948041d02144980c1c0c03003a0115181511591240501500f51041c0700070580350707010000380c01c4580c00072640036040300b4040f0380c21601100070280f425203008200c40302c054030084d8148001007091802d00000b81c1d101c420044081100c2c100f01d030850010f1070064a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 710171942 1250 710170692 710170729
    0x301020705191b060f051e161205070b0f090f03160b07080906130203011104090626101107021c0308160c1704031a19090809060c010b 59
    0x3554406104640300f0300c848445040f0070341084540380400140c44041c01d03013200c1c418883c01103221111135048200b4248180c014100b100e944034401000c003134034400409811642900a80c00202507603124600313940789940d002420001d1a16010a2400c040500500f00d203828498060442d8010070140041d081084842c50520307100e441625000d07428040090450080181c0c100410a000d500020f9481e001501c41d20007480c4101540042070140400300215069201c00050019080760582e0020040b1046420b0022425507006514900d4030b410800320b008a03407245161203843c0040703500c07070241040c040a8a078500040b95000c2104c15501c01d095611040c5900e40c0c032010305402403442540030110070500c0407004d5040002030220f51020310064140ca8442e8417001c44904d40100301c0b00919080071810200804070320583c000c0300c4048039440860326031220b4090a0070f2960050441c4c1941c010340300f50820782d008081c041590071154020714599240d40710340c2904e860380d0411a80380226407 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 710173192 1250 710171942 710171983
    0xa080d110705030309061e0103020d02030a0606060504050a090615360806090609120706110f13060219170d0c02060711060603031b03130602030a1d011d0301020705 72
    0x4050241000c00080005007d0103465003540036420b00001c0d02415254100d4140180f00c1c46da0021910385009000300a20341803a05101042c84e03a000760282048940c00c5441210300e03921003000f20141e80c154400e8884ca2500440c1c410003184c050740a2400d10b001010400f144480401c06a02c5203040450f25544103602c0104103122503034050107442c1d4051034001c0141020f081821049580d1b1001281c105210300f400303c0e111040040c660000400504048940c6c4d458010401d6032890b40d40c442e00f000c0c0c080d01c0c054000056440e00201d030115010302c03841c1c0e09504108060b207402c03203414055800c42815010400c00e00341c1d482e4292282c400101c8142d40244150710307000e103002c2c00361103c051452070070b9400001089415600002180c41b6100202c24a114045400b1107141ca5809054900741d2401c0c4824004100503900101400701100d1a640c0e41001e560200110581010106a61400115610807000c800c0401c011504074400d00130f000180382464540780c8a042525028071000c2800c3e10 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 710174442 1250 710173192 710173201
    0x50a0606030b36010209030303150307060f020d0302160f030c02010e040b0901090209271009020c0a24061403010b01020c21160b030403030507110a080d1107050303 72
    0x10b510425800340c071489049600e070202e40000000d03510005840000714203c03d800c682d480c00c0c00e406440140902404484e2a4240154041c0c000d155055003203000e40314040c1c001881911a403c1001c20140740d401410308050540000c4000c1e5000d00507001d0700040d40324180f00007621130704480781d8441c0641d48944058a940c400100b00c40381a8007500d01c201c2c10421f0010060341e400c09a2030445017411401640c91400c00081140d00328505912039107001005110702136041c40245540c4075030700e000385042585480b003080300201c1c0a41d0b0b0b40015260320540d044000115081e004049a0100c26466040601c0500074803042e60031542202501b080145121106410240542141c1e18800d00240c02180a504003061051103108030104280c1d0100144a40c554800d10420000d4623810740e56101a40d29400e96821550041d0340840c00280340500040c10203200300f0041102c141d0b06800b402601d055915568015080b04203140c0c807255446490280141c8640300400d08103109102030340d20382c0391 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 710175692 1250 710174442 710174453
    0x72303060a06030b0f0402030a0f06030803160504030c03020607030c06020c1b03060108060420040f020306030c030f030f0a050c06040303140a050f01090221041112150c0f07050a060603 81
    0x100e9030b005a052606001500155a03107854181207009426200161a551103c0b4540085c0c140890304120807494150044103100c0f601c0015441540403d0707000710581e00060341182c59118074031014001260401040c07006240c24002000c546010303281c811071910b181e071505002c03607000c800f207246594410701f160407400200314010103c44000300e01406041d071400b03c00301d403103400c0100000e0403070071022281c00c03421007000d036007018182014000b002200d85c07540c41d00c4000c0d402580e031217201c1e110b000d804c600c1500d000503403c0d024030102c0015601344490400000501e400900f005402e118040c0301c00004160b04200c0d041c40b03540255008a030020440f0060565200d001e0021212682450300700314203007182c269000d046400321040141c0c2c5004520258030421003c2c2485004105c08409010034000900542514100111001441c8009080b241540d0740c6083c80c0341c03800c01c03162000080102d05200e02038250031183d01d004501c0c0c516660755440c01c104d40118100d07040b95444c90144141710 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 710176942 1250 710175692 710175709
    0x801080c030106031101030c21050114090720070812031f12110f030a1a15010e060a180e0703111c0f020f07050705040b0f100807230306 60
    0x8001d8008021250070350302c904602414181c3ca00c1e05158903020050212446050442c15911340c0b000c0c071840000302c80d01c54401810003841031300095a0800901409882c0000200740104100d40b50004014051004001519070320980381c0507901640b04002540141400440210144100b03426503910300311035103004101d40300540c01c040210064080c817001d0003445042c000300782c206200001035503944000401e1a403c0340207150301030245c0c0030448108144140c00c100304144171620800340f6524450f08240014525103007900180d154118403456007040d00041c0b101d0341840c50100481580590004680c0c07800e03900010f4990340500402c41c56903414816200307200108004640b92040b00070b0b040b10290328107580c4805440c3d59820001201d0490387c1190746c0d0340040d0b29600d44503031581c1041504c40c010f5120f0725009500b413646005031480c0003a2900008000140003420b082a8044200c0302498001c0103401030081c00310401940c0000c04040c0d00c000144d031017040703a0f40e1a000041c06202d5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 710178192 1250 710176942 710176963
    0x40210030b09010e060a0f090b01030b010816080a020d0e0a03020c0306040308061e0a080a060b030c060313031112091f23090a080c01080c0f03010303110a0b07080108 73
    0x9880c040c1aa407803580c0342400d540c115800340305842500d80b2903100040100c0120360210f5034600d0700c104d00003604c94064000344c501102c00d0302c0800c02c9030081c0e001550905c108503103e01c004028240f05410b85401030140e560440c00c0e0b06401410542c480d0501012144284c1c4444820740c80f8040c01341c20181d0401c020184030070158040c207807605107607601a01a010182400788a00d00e194403183c02c518040f488800c3c00c042c0140132882187d620481151900c101c54030036500281444010800e50900280e03500302034002070301c000e01e16a0303850503941c1501945c1004a0030000c020306d100030b0110003004480051040300003016603850444040000507000d07190314180100c118084861219000340340101004846460b00c1c14011460000c0362440c403500c0011075100054560116810b4000030710514001002c1e01c0740d80041d01e40700c13480e5540d80038110416a01d40002c200510002e4810001807540141d59012944a90903d030380d40020020f0031580c0000094503913004000896007040048440e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 710179442 1250 710178192 710178197
    0x12090717010b0315040f0609031e03020408100c120207060b0a05030f0a201305040c08070b04140103110c0c091b1207090b1804150602100507030b0307030605040210 72
    0x91141e00004684c0f04d81510340c1c80b0025403c2c4000007410702041e01c81d28540d050303200008120b045110310b0084c0400d5545100000c8014244000403503c174028421241540c019a004000110207000d00d0005450080030040412419500c8031009038100d00180c030352684034075070101d500c91444007480b40c054000d50111388264041c0200a6498002003098400541c00040a00202c5803600c0001d00c401840c4c841c0c0340c1c1040510710300b094801020390010380071710701c990b0007120500c0d03803a00b032255981d00074000d000d00b0100c1004100314035003c181d0000884a010304001c42c5891002000790314507004003107003203600d4029820300603042c43c4c280645036001100b1400c0c1403500183d170800c0c030181d002d2501b1000c14592000d010428070750003070029400420b01c17040584d55541604040c2000002c00c050010f014504004042d42821513042c0014240c880030780c010711302403140c0808140030300009002502410b44d1401040c60b551001d116040103180161004074140c2054810b011f001c1c103200004004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 710180692 1250 710179442 710179451
    0x1b1503020a050717190e130c02030415170a0c0e0423091011040807050a06050d1517010c1412070c06140a0911010c051f021209071701 59
    0x3501c03900441034030f8107241c011354504103000c600d1004c071546105480117a451210107440014003540c1c48500c1c5e50703120800781c52048010300242d0702d81058985004503500943c2083c04280401761a50400175628415803420010017030181c14800c0d8818410340d40c600d559511401d298002a070403450009207403800381d03401c1190404907410b0b400030801d004c403492000c1d40090042800d4803010060b40d060b0888420080042003401c1d100545550302c0b034819100240503103400001c1030325292380000110361490304c405190000e4954041d0040510004804810340c0d022400300d02048407201c14040d2504850001500c1903107000040c02d142c450000744001c80070100142e0110520b6481c44903044001401d080c042e0301e0703051901c4406400c0d0b00c7d61260111100500701725020f54039811002d4181e000341180101d0800d01c400440703000160042c050101c1c0c0c001c65021f00340c2588900f14903004812007900500703280c1e0100d1010f06100065442c0d100e154404102030010130f01d20b40e8010983c000c020000c22 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 710181942 1250 710180692 710180707
    0x3021e090301231b270a06020a050a030305040501090b01090e0f0c06041203050d020c01050105040b030d020d1d031c110a1a07030e10091b080615030a1b150302 70
    0x410000c01030458440800e004c0701c0c4845408140141c860521400044d10760190b400c004594403002000102c80c81022600000580c4600202d860700078550002e02904403000c0d2620154080c1c48050005c46256584a210401141402c40039501805408a021421401c1945501d25040d50200c0e014403076049034035101d0b4145d6428040314100c5140034100c250721407642c2000da03440c0c054074440306c040600000d50b1100340741c01940118180d1b101110200034400120041c10783c0ca04041c1058005a070201b00043c001c11b0140c0e44c039030b25241259041181400844020908144030124009a902c0603800c012981c150003201403c4c01c428200000d260720b07605a110010485008040d40c12103141c11008a2801c52081d04150703115000107081307a1900302c1507801d08000305103d070416030310040440c080500c9550328010f000110f8100c900205404e466203540d6800e104451202694140b06010f82d50002401c45a0394031810710922560b010390a140002216003140c044141c98105441000900c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 710183192 1250 710181942 710182001
    0x210081501180909080f0a030e150f0a0e0709110c01060b09030d0f03180b0712020306031f0f1b020f0307150c02011d070603060b040e1603021e090301 66
    0x10001c8400d43e02001c542900316003000c812500c110407440d070340c20900042604003d80c040d000040403400e5081100d803020040040c1c20403020341602c0082d030340501c1c4000b24503500156040742c100c0898503c00c0d2851036035100480d4040701e90401000f902d440001c107600791025000e104407002000614491440c04412400207a00c600c01c0b018040280401020140186486580100854950b9541800707075003a0783e003000c7c40107010480d115000200c013007050600750025802504e0280c10054010052860340800703401c9d2400b0116188240740703a81c0c411500c2c0d030707503941d009002050b80501032503846080f0a150081c10000600300300510380c0e004126103000241080301c8014100385100c00000c0b200003a280490141c031750849145219032100924118001001c0b41e11070850f11130341c0341000f4144c0d031503013000c006020b144140003081c03080343c0010340c02c034030310841d940000c00180ca4010300c0e0070f80c02c0381c418650942d001400400703048045000180c508091051091a08500422640b2281414001c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 710184442 1250 710183192 710183237
    0x5070209090a020d030c050f011a060906121303080c090a05010e060c010f020c070f080d05070c090e150c07200103060b03010e06040c0504031e020d0210081501 70
    0x90084008400152207a1810310081d0506a030040c81400749002031304005001003840030707054034140030f02c941c00200305005100f4102d61940040714100c2e030071510400c0043c3c5410280720306030050010841c02c1c842c120992074041c8280044481d00c4101c243c01e0800824040c3c009003c040031031420018a000340d50b0340c0e00d0b134a04495003440e00d403035a20361590102d526400790b401c10300c0c500d42c00d1502848122005801400c0e410984e107085401c1c0300c1e910f901058203030340390b403182c0d001603004014030904441c442c0c8010030342d00b4012117200031481d07501d00030395003101e00700c03002032000c4d070050401b40b6000020801e010f600800b201d61003500380a0309032560410050358266030700232241648090710f80e590281e0000c00003400030b180d0303268a0390f0390350001c550803800840f81e080c401c525049036041c1040c001e0080d034007680d0f0070005001c80203910110743c07803c81040060070791344105141804401a0346100000da9100800e0b0b0ba60b08007414410342c031020100001901074140003040e4604a80d400d0b403a100c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 710185692 1250 710184442 710184457
    0x170c04090908161202010c09060503010312181508010614090409050c1e0307050105041a0703180b0d050f070221120108031b0d09031b050406090f0f05040305 69
    0x3000031080c91618000c0e00c50300c82c504800380c1d405494034102003803001c800091181c007440307a00203110050f032260702101c2c046802e00450010400070b00c01840421800011081d50007000d041140e1038218101c40f41000700300d0359028552400702151203039000d41e40840e900b401801c99080407200b104007a240c400c44c1e4040c0c003e030580690794940980007403140c03c10000c1040c46010b810401641900300091030521101c5145602a01c1603100c000b80951040003241d0440d948410b40003d0441c4030107030a0707000d512100042d4200084403c008450303400d241c907a04001d048003041c207075441d2168104031055400040400050340c0318141040080c0d900416480f20180b250442c11840d14441c0d0445c024501802c0040040e421003000040307035189001008001c030482034100b52101e11442c0e42ca465580380c0015001d0700007100030703800301b0005400d080407040003940d4180b00907105896801190850b442c0364024a40f01e40c4480c2c0e58040d00c0524442c00885025051003400030345490703140a4001d206510 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 710186942 1250 710185692 710185709
    0xe1204061409010c0b090c12030a02061f05190506040b0306120a020a09090c030c0308030708090c01020a02010507061e060906170309010509060c0f0604120305070e100504090504060606170c04 84
    0x700003840101040c0144000020004c06007103850150a100270f94036003000e80d50700003521440c404030310100f0f00c0364000c0c0301220f443c0940d11081c0e401c240a001104501007800e16006010306404500e50b6600300260014211804406803070303203003100400001001241560300e46802c03914400e0b0150712800303039010030384007a0640407a400d8081c0c40c02c901058000e0340040c01c442c2705144044104581c03800198016090b981e6015000c0c3c41c0c1c5281652070306880307240140540e209a107410015400390015002c694022500000c0352420604070007215003100954607042c59884400303200c0e851040c4600b80140070144203c200b14101c460015940e80b207645a01d506025001c240d002c0b055951001311000b81c032400c0d00b81c416905043c408599503120a031030441e8003440b032000c4160143e00c2446000d2140040380da40d01032030201c4a041c440000000b80301c0c003040000400001c1070b40501409000c1c02a40f0803580010702c80c0c034206000340301d280303540a500107020103201032000c540007001c250360680b210903 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 710188192 1250 710186942 710186963
    0x1c05310f23030d050114122109031006260c060c1e070504060b0708030402090901020d090f0c150207030813050a0e09101e020d0e1204061409010c 64
    0x518140c403841c05000c8440c0d05840000f48116822141c1c1d00b02d18100c1750408252000101c03004100a11094040e00c040540d5124031f1150044104010401d0003000e403d4021030b01d40580c80e03022a0034490f1005000a461752030304810400d42203041d0031410035020142002c030b452852112840d449030300d032521140c4641d070041641c91441d03405101c2400300c1030b0305c5c08048035a1021410820b407039118074492a80300c0c81c904207001903042c80b56000c0f00c101036807020000b85580e58a5081040e03c1d1009024010150350900403060515018424100b9840c02258407141c60386552400030320900d1650800c0011003000300004040b2900098200c1c00c1d240e201c1e4416480d42c0c410100c8980c004c82541c030050f880014a40d0000c1c40c118014492401050840c0940310140e0000c5420015a0702942e900c6984400d40001d14000c0b4a0640c05440e0302e40c1c1c1c4a4000c212000c904540d81d00d48084003805600b01d0200080c00c0004942151840304410155100070341003005035000a408643c03207800103031044500f03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 710189442 1250 710188192 710188223
    0x813060e03190801090b0a05060708070c08100917040e01060f0311040906060e0d030813020604120b071808150a140703021e0702151c05310f 62
    0x41c001d072403200c0806100c1020410300b004005200c1034082c030901901d24601400340b6102d080060859064440140c00180b804034980c1d143c00c070662101002340c2e45d901001e5400f1815150134814101c1d406030000d0040744c1d201040c100351622282d0380a51922070700b010030040080742c00301307034090741101d00b242801203040805440c2030f8098a184500400ca42100280100700304443c0d41c09107043d81e4281e035420080b846c80d43c0600061291500024000c112800000b590803080c0103c0c034034200d84013514680c101170361910411890500010215030f0009060200400181d20026005900700c2078007070031116034038110300f1689400741071409882c4020a02d001662010558000ba05c4281d4444a4400741c2d1a09800c010000e41000900f000c042800c0f6103c090300340522030545001c1a002480586415040425014039502415aa005078907220101500b00c6505105252050301015100303095520b050141007581171218150304540f14445045102080c213a10350403e4040c1d01265034038030300c401c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 710190692 1250 710189442 710189471
    0xf040210050d0510170615060a03090f05060f2a090a05090f060a23060c0f060411040c0512070c14120415020303061014090603160807081306 62
    0x101000c01c203042c0e08000a010048491450700d00884115035040c21031008265036042e25a2400d43d900f1400280e0400516043e01e0110700500d112461803c0c006011900b5950b00b81e2139019217407040c0d406411402c00c021004265840059018160340142c24202c0d01039800072520310451842801e080002180d007400d1a15081c2e1640082c120040251405182c800c2e4035442d42d45048515038044d00043d030001545800c910707400250040e015844c0c5128103040c40500c00f094000c10706100c550b114400004030880000d0045030f025900071010b170202d07004200e0034042500c240c0306191040003001c106100c5001c416040301c903040301035884d1401003030320035041003245171900c080d6200c5d0a0292481e03084900c0700e140300038030031607e4018041400c0c2a0117442aa228001140c5454200030480710000d00c4a106114403c41e00000710030311401d2040020100311907030011910075602c100c414504480d556005464243c3c02459407416011a03e4007040b9480200006440205415280c501d022440324 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 710191942 1250 710190692 710190697
    0x50d0c1505091c02041109150c10020c060a0b0a0b04060e0a08120a1b0804030b0415151e0513020a050f0708120f01120b1807060305060a05090f04021005 67
    0xd2000340041e1080089410120505101c0b11049100342c2c90310500c006c1c3d5201e81d9042c1d4a900c1e10082400031002c0e610034412545600c40c4821a88130b00500350500d603900b10906c0600342c89400c2d10004c001601c1d014080c8011a001c034080fa6101b5000c04008104907110f06003140c00780c1e40c2d20f16040c0c8001c1592008940950101e030001000d030b0107048085042541244003500c4c172071909d42e80d03460207001250220460845404409080e14200300030600100350b0780d400c00c90b08144503051450544c40031034054012a94424402c0b9460704c0c044e4810049890408054456911074900000c0428940300025081c240c0028910b40b500f40c0200341c0d00051405a030684031401a840d000c03541e1040d45281685003640a0345140032643c10031008640c0c0180040c0c070143c185d078484108500300c10181d403501c002d4500000e08021049150400d010700e2654240144c8000305090f44010400b405d08804000082c10190011801350740c0010400001d407003900c1c1c3c81c581080d0151001c09800180070821100762 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 710193192 1250 710191942 710191957
    0xa1101021c02180d02030d1404031202030d0c020f0615040f0207060902190b16020d020d0501050901060503010b1503060d0803040f060f050c0a0807020c0d03030510050d0c1505 77
    0x241040c03581000e21402600241074042ca05031001543d0f140310020855056150400650598000c0c140783c0101e030301a000c9290030f0b51340c4102c10381c1050303602e03502c05580d850b1148034000107800c0860100d80800c924000c07900c4c611254001740203012501c807142649c0c2c000081c40c41010300400400a8040c0c0c446078028468a84841c105540e900300606025002d40380000d01203001d031469039103480c2c0f6040441098420f450a03080018503140304c48100003038083c0c0c1c000e016640b000683e2071120050b030f180303031400302c10500c504004152441c001d4032081c2101c0266010314040c0c0d05002404506036103440d507038802240b00001480c0c40781c5542002c2009103482c100002c0c00c0100000620060104612b043c6c06100c3c42414240704501c540030840c0280c54060710403000b0241c043c4156400c40d1f019031940c41d0310480030710440300d0b10510100007504550080c681680405e5441d02408400c1c19180c9600000c0c0406035056401507050340c0c0d601d00411800e00c22103129403c11000050640d00c12000c56412 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 710194442 1250 710193192 710193217
    0x25080c0d020d05100b0405010906030509100e060a0c0e0315041509051006140112051305030d200903071703040803130e0601030e0c010e01020307142d030a110102 71
    0x2d507030002c16064014034043d201c1889403a900d100000d000340e01d160469050300c41c180d41d01441c042c5000000c1d000303031101034034244090040211340c2010118a2081c007a000031107000411a0b07003000d4843c0c1e401c4458140d488000c00c00c10b200000b5054900180d401441c00c11540c010500387e4441c00d03c41142402404030a000504100d41041800b000103100c014661664a040080644c0c0d4003d504240c8103480749640890051800c600f281000c50380120f9003c251070012a108042a545060560307202540c007501440ea1655845044550300c00b09810081c3d8074905c5c18079001240001907641c0c44144601c0c0000142491172036007126090040c1c0b802000d40ca0126900c60344a04040118080b042c040c0c403614450440008043d58840d0094410007100d5401a06c940c1c0c0b038520045480701c040c40e42290651000300000c5000403030b00300c551540c1e05240300290081001b8540d030241c0e80d0641120b10030b02000e0381d0f1101880103001000b00d60308070030541080c1e4600098041d00758060b0048070a00102c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 710195692 1250 710194442 710194447
    0x150b070507050d0503070b070f0903020427080c2a040b15120a050a0519020c240405010c02030703020d0305040c09020703020c010801080111041e0b030106020309010825080c0d02 78
    0x200138000026060300e510442035820660743d800390468481803110f4070030001a21041d0100094240f43d072103211801040108001c0503050b420101e04c80b510307402411111030740002508444a0030a2144c1c28a050489000f240c105420340c00d5503c03006402031481d03101c0c47d40c44858003a0f0750780c1c8840c0911680d00303803081d40f5100c0c0b68103501c01040c401e04403071100c40c0d1410400001c1200000d4442c0e0f07841042048c0207000d07885000c144040081d0404050801544070300490809100c4034501140d0700c450013460440040e00d402d10f89642500d0750f560122095500600c0038000090f0007090203115036900340350028450362f46041400306a0525845120441d10008100b001e140c0e01080304d0607009800c5c0c035032040503640c41019500302d03040007003d664801418002030081d455919001e013001c19082d08108042900e4500c4d04101d980281d100d040503900009070843c0d0ba5070841e81b00c5e80e10501e01ca118407040da00c050741071950702040144900411540d100020904600302c0c0540b40c40720780b130b90382c21074 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 710196942 1250 710195692 710195719
    0x3040f080d09090b06031b090a0803071127060a090903020f0607080c0a110106150c03030c170a0b041506030617120a0c050106081c030f150b07050705 66
    0xd46800c00ca101050002c0c20346240880d003041c440c081e4401c0701d8400b410640c80e41d40e44c1d04030111100c2a6090405400000700444585552800b040d02e000d4044500510303a0b03400c040c42c1610703245c0e011071007660107080d000340d107803131040f005900d12130120300301140341000d650b500380000d1800301c07150b0410307140d9900e40a141001e00d80c2c0051075490501485003220f115803146601565844000c9441d980090001c0140314059403283c401c401550400c08008150281c407510b03080a25492010340c0400102413a100c442410f60500031b04d80141c0c82c074100340081800c465070051410344002c06600569455114095440c2c03503540c01010317032124407480c05610300d440700c10080162540344545500c140100e440440058004180300c0111141010707541d00d8010b0b804016200360420103000e07501c0b07551b4be8100182025052000d5411207034603225001c1d840400c26005011a100c8403040c2c01024035011141480d140602201e400362200804000d031101100d2822500d850781e5a00030a03040f144044808 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 710198192 1250 710196942 710196959
    0x706020d0f090306021810090e06010c0f14011e231306150503070e0c03011214010c050901030f0b0f1e0a030c052d01140c061014040e1e03040f 63
    0x5c042c940448042c01f5a81448a04940078413150080314200000c2d1008103009600907d41540010704c40c2080c0100ca04184d11074600e500004000d4404a035124110a0410003041814424070030390300034100404410004044130039170b04584141201c2c5000c40119500b412592403400700d640d84548248009603a43c140c8407510b00b15445030602a12038a58085003000c0440c1d10a8402c0800703d032440d0841c1e1916039200241d0500c58010f50300c00803540a504181c00d000e00a8100484081d112942c0d180c0640000404442d01b400c0703506421440d001d2140c0f000d81c1c0d0440c5c11515100101d41c00c4284194900c0801404c191b00e44401e91700801d40c103800001c0150420504084680444210b4200300322108070000324040c07505100409480c144852050398000c0385148007280351006001d040ca54090115807414030240d034032a0104150040070410300c05804460510304006460a00c11041d503425a00c0d0359a440131101003d05403441604c0000c80c1d410015240200300c1145e40680ca182c1c1c0d4000b6 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 710199442 1250 710198192 710198227
    0x110a090305010510051804020631050d0201020a170d15031707080a05180604060c0b0c040b0d0b0f040501030312200403110d060e030c0f0706020d0f09030602 69
    0x101e806509080001d040c0508020302e0004a50740982044962501c104e124203251000810807644800103100c03c582210000101c480b1b25002c200807400c1100740c50311081c0ca480020382c415446070b103a400c941c10050b45c1c01704440c948103600c641070f0407014140703100342c1c04030f4007a081040a00c2440c0050155145500d010800f0889016070003070750000c124118a000c1c103108241010348402030400c448040c09210704010984c6803680071402c80c1d54042c42d000a901544580d00c02000201558580403d1107645410b4607000111185e400b46081c0ca03203c0007407064006c4030040c03a81c1a9075104542e10a4071403100040c20b42c00001e01c108000c0da102e02d0040e0035100c40a1400c7c131954a450a15070400a80b82440c0100c4200e00d03400a0500d4916540c1000283d2004152a048845142c1c480700050300da00035981e401c8003000c0515103400940d24428900015410351151550002c3c000b04202600462805071500341890000f00c00640e00b6800c0d00c031911a50300080c4210310018140858104902c2c1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 710200692 1250 710199442 710199449
    0x403200109140a03091211130b0604090f050a1b1107050603070f1206060903060513060c031a0603041119030b070509040e06103b1611030405010302030406110a09 71
    0x750215401e841b00f0707022852003502c140c02400405650940d0000340751801c0410381a00740f50801086181072880486d2041d0040d0b845000000c1d1960354401c8155918003d2942c004c41c0240708210300300c104c064001d0044840d07450303070040c0f005c0c0c0030300001004428060000504400780625a590606400c02800010b4030001040000c0b59401d072407034083d2042c0118002c99500c0d5403103032080740c11900d41270000c18001e02080429540e5215110001c2c07828050b85054060940740010355a008141617002030b2620700005110311010410400011229a400010710005a643d00d00300e02142d4011840300c1102c0d080600b0140841c0104407102d6449401040c00030402d50382070098207158410305545403000c3e90081c0f230840001c5018000814000310201d41814100d80c003040c04102d0044111070060b2100121a4404011080010200b82e0f5003003d4100c10062030204036010500152944a000764000c0504054002002c1418003006402c03a4005c840d440324005c0d500e8500500161800d4254072 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 710201942 1250 710200692 710200697
    0x218152b0e03120c0d1806092a09050402031207050c19030b0a090227010f170721120e10030203060d060b060c070b03010f0e0403200109140a03 63
    0x503060020315011003510006a64a0800c3c10681c031920810300e95074010080c411142c664034003981c0340c440708050002030018003030074000817403021500b0000d00e01c4550f020960104a4800300300d04204448620310401c039126103500044a4880d0b10021381400b070307000c141c10105c84020452005111b804580d00701c7c0600100d5100f11418410b51204850100d07030700c0064507400a031400a49100d03600d800019802e44020501012100c01c40e10710720012101032420001940b403e030050180c80300c55150480070300f60200700400c0d801003c16000d640c030a29402210752409038a80c0385000102d03454034841103150b1102e40c0b2070306015030340c2c4010280301d40c0e41c10301c1d03109041c0300d0b4061199074003910850f40580301c0a080d004003012103448400242101040058000b40d00700030300743c0c00100501840380901554070702c0a5a95152000e00f032442402078015421034600f1006100c00603402001d0050360443e11001440c101c1000c0200b20700500c40802c1c054948003076a48281c6004030041444256907100740c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 710203192 1250 710201942 710201951
    0x20071208071803020904030c0501050703060e060301110412080d0f09022805010c03050d0204140328020f040b030703111305091222081509010218152b 66
    0xd00003200e51124054110414042c070350428005410280011644a802800c100b80c001c000c540c2d41134210341003101c05000003681d406051294010500c2c1164020303008500038407140b4001e070000c8805100d10f115003402643c0e000072031010040107a003501c00c081d0320303c6010049801003641d444003403c03072078208034032038050b40030710800104d200d180c540259049441c0515006080130300541d01101c1c0b0580540c20300105100015141c0b880e030000304050680c00504080ca0343c04d00c8189481c100c410310585081c410031006403400d0301c40311045412802e0b01114400c0c041110716001c10010308040c0081500350064420100034070011528850000c03605071646900700c008101c8900c1190015100000300380c00c003190030302c0d803052104040c0c813803245407005040c6400c0780e0007040e800303804a503070140c1d8840c0c00070100c48031a243c100f051a40d0002c0313010000e6240006141c0d000000c580d00750441481282003404484801e41070b54103960b8014010000c5154048000c003c11500c814800040c0d4160703400c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 710204442 1250 710203192 710203201
    0x16020a05040207050d050f070f0c050f0a031703060109030f1a1b040b070c0807170d11190312020a030e010507091203052203030c110a05031020071208 66
    0x2442143d07107983d000700150845041090b412a41c0c1e130300c14065600b14800500014002c90b003030b2564104620b12410210f4019032400341844102000c080c0118413401413640c0800115124000e0002c1040350720180940ea1303a22030005840c0e8503541d820140441c40192203110401582c420143c20301105500b00319010fa0314404c4c402c0003003401c1c01d1210b1803034005001c01c0000c3e85000005d000c10611800c0750b80890b079164000b4074039009980d4031488170308102c400488100201400a01d180c1e0800d443c054805402c04100c0c80d9035400e40d2440ca400d08402c3c80030020a2500c00c1e9582070103e4170100056669015035007004001d001c0c100c2808299500c0c100100da01d050040080ce03080350920511b4010707100c500d84066400cad402c0918000c80e404140494401c0a0801c0c550681c050362194860026401e2282400c610401c1004d1203075005a110303850500c007695000800d070707401c00114040810850243c40401e010400036440c55141f00902240542c01c10001d9030481192444d2075440a00d59980c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 710205692 1250 710204442 710204449
    0x10b091302040b04030303020d060512030a1b030e10030905030a03090c080a0210050309070806011d06010905090109150801060605040806090c011d030c130e070b073516020a05 77
    0xc0c51007040f203894800c000c02c2000030302907000344c400d4240ba0180040c18580d0750700481c0c0c0940c00b01c9600b001a03000010344c8440b04c0e8011385c45030f4030b1014070200041a0480d50f60042c010381c002500091240d000000c0c0416031502c00c1d0481c0100c0d6a100c000c0d01c2c0c036600c1200d0094058118480101c070035184c0102c020840d007070000b035122070541e0020f04000c2d401800050075681e61740081c1c4004050700820b000440c1e800700c2000464001d003101090300c454091244140b100307100c4090030060402030b1040d400c02940d981c08187e00e054402d40400081c031900312081e54541c426141e0700c80070300c55085c070400142e02600301001e0011126624141c401690b1550703401900d941504d68800c1c04104480d100c0903000c1c400c0c044400640b01c01a0885054900c00380004201c0b02e4001000540d40340c40d203403070b0a991401031169500900034030704070a060210b503a403018480d2003a104c0d0352408800080c4100002c140b480d008031600410798800c0c0790342e14210392041340d4030070710001c00782c1c020242008009523504 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 710206942 1250 710205692 710205697
    0x6050406091515171e07080f240609060f01270602010e0609100207030318060e0d0207050f061e0d2405060d050703061d04050f06250215010b091302 65
    0x121048045e01581860400021801c0d290548880191092080210f01414100004205031260100803c407000203c1e05414040040207500c035a800189014400203840f20460190041c008543c030000300710468004035580c0c02c4040c07d40d0f160031201640700f541e1614446162040d82e400d41d000344a540303003114506549000070345100001d641f0581c8101007803012603010f040301074400c1c50007040d1240f44000112060200c2c0b07500781c44481d40c402102c03042800400c004583c940042c0050986185030500080e4155007000b425409610b0009248030354003000800c0e60700c84d211100290740c82d01121131413980145141482c60000540c4c40d18072113000c01100c2da450040f100003e00f0689084240e004182c041d141c05040c00303090607100e803404120044548800003903190011140d900500e41402c00300c0c81d0614034101d100703c68000c40e0900588810b8005680c1c081d40b0030980c1c64020a41d2108102d00e07065071060585030a03003c1c41b0010a15956403401040c80c0803003124600c8100e00000c10340801c91 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 710208192 1250 710206942 710206979
    0x1205070201080c070c0f080616080c250605190b041404230f0a061a1c0f080a0801060f0e0a1401050c0d020102040f0e0402030a06050406091515 63
    0x40e0002e4006140c0f0b404070001400c0d4144034100036076155959512940d541c413002c0d04000030726008001000322241d003605140260131440e28003021a82810003017101c1c0d500c540900401e1030f0301e80756141181e140b510503418152070340c1b008042011b441c2401145028801e603944101c0b642e810810090114a0a0301840101140110b20302c0f141e515a43d640005080c4521040c841c41400c20904441c032081c00d112182224280c1c00c05030411042d9031a03c3d42c00c807050b442209001013401c02e0f10701000d8031090321180d000740610f030f40c1c40c2c1c440d0058140080000d4008400400b1214005039403034541d58460b00040c105e842079150390403400e01048040d1009943c10486580040c610141040301d80f4920f00d51010740311040c10b02d503141050f00300700903061004151144e40580e4000400b0805104080301e10300040209100301e1110741802d44c00203031208004039024009944500206003440742d035900c005041a4400240c240e5442d010706031030302900c2411900701d210182080b002801ba031040e903034031010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 710209442 1250 710208192 710208197
    0x91e0c030c0909030810030519050f060c030109110301181112010909020901091a0906042018010f020d080c0d0e0c0a090c051215030318040f091a15060a0305041205070201 75
    0x284c0c0494018025404009d0605403010302c543c03040707a0a9214240301c0c860103a81020102a80e0b981428044800e0b80ca16241c3c0701b030303103440801c01000028401e0900040503405003a011545d1100700c6801e0b2880d0056a140c0c25100006000000e0b20140580c811040103100b900c0741901c0760707a549510000c0b80c00310500b850400d2150b0340704602925000c90b04661152000308000344050380c007154040001d88150061194000024802c45d0b4101c40d0706864920035001d103015800d20301030783c030000e4588407030301502001d02000d5070200b400803124134140e801c2640041e500f040b8449488074155912010880c107e8055034034001c0100c1d084d0800d020300c0021048544505103001c01c0c01d00307540301c0c1c020014011200c611850300c1184690354103100074035485160080505041c4c0380f10b0b0812044a8003441522200c030310308406440080c403030342d07407046940040c5003c0038400c0c1da5014040315031240380040117a21034030008605122640560256009034007410040c0e5100003d114280c0702032080d0b1304007030702 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 710210692 1250 710209442 710209453
    0x3010b031f090e0a1103060601320c160623070c0306050f070809031c020c01060503070603020a02150f160c0206181201091e0c030c09090308100305 65
    0x3404160300d40700e81d554144440216801540d40c00080c0884900700181c3e4500d1304a06035000501450751206078011108902900d0b076401d280300041c0220080c15400d803501c68220040d581241c0c03103415481c0340000e03038402c5145c0d90b11403203698944441d4450542c800c1c0d0400034202140da40e104920f0f403030501c0080c800b4400300c4c10b07541600b00306136000440100d503a03820903040480003410034019940102102c0c16130710850b0401c0e80001d0141c80000300007030f280ea4030900440311032050b0a4406040f40c408040c0060359000b0f024285800360125400040e058450030300c0004050358980c0c01042c40304080c1d82510f10481100c01302110800c019601c000c0c1017407100003c02c0e505031a0251205206401b4104801c008219901240c0e080c3c21000d40e00002c08200d40c0c01e0005810021141080000d03044001c0110900395512004036801c01036400c40000c412100040801201401d5040559000145215a03995821540002e4058000210006030312100400c128003280b0200780140c0758070402424 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 710211942 1250 710210692 710210701
    0x1c050a0c0203070f061809111206120d08070201060b070c06050f070c0807181e050702070911090a060504060804080906071208010311030307020108040f05070b0315031203010b03 78
    0x46820a042006a9050045070b10008a080041a0040050000f83c5490000384000c003646c807a086019400ba00d0011300b084a0350740c42003400710481d5800081e40e14081034946a1102007a4440041c40300c4c070180b441140d481c0e22900d0380050080307102d442e455000b844070b946c40e40c5103a441e40c0200391004040488812003403094901880140014007080f140365030500c6031680301c031030821801e5400a41c058010045c00e101e031415245005040c0309039100c00f400160100c40640e594000780095003400142e882c0e020580040c421702c650f1005160140c014400892040d01860480c0c3c002c0340882d1107000aa900060718500403000d5404031512600d0781c0712540d80e16210500c080e84400c3c50254000300400200c00064000d101c0101d80e622aa6500d484075810341c030308040804035203900c19200b58020310810380140c1e4400c00041e809a441020000001030030310300540b8104541e0480d03440c1500100030413040c0550800c5000032420100c044551003030300051201d2a0b4802030242c101c10301400c20005 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 710213192 1250 710211942 710211947
    0x1e011512051b070f020114120a050c0405031006080d14031b04030204240b0f0714010e0d0224010f14030a0210020120120106080a0b031501081c050a 65
    0x20b0b500106018200d142401c510345411a160302181e0121001111076102074199640090140d07100030b1000c55032490180c0b0300307401542e129401841039400a840340002020340944005070340c020325016003260b52064201e54001e01418050160540a10403594035540e072502c501c3e01c0b0404030303204414151840d224207103520303180c0005291025141030200070010050311584a01300d007607015402c5d80301d140b0b0011104485858030039400001c001c807080c82419102c101c0001252041513002c03203807900503280c00a030701c1e0140803c2c000c0b01d82280a031031b820900c4641c0108111181c00e01e4015402c0070403105075001003203881c080c003410b03208846040c2d0610011071b000504205208008080b550340341e002d5800601d40180320840880180d46440c403482d0140100c820340b0558034148000c4074101034810140030102c0005214031010801000e000c1405c980281d80101c28046000d42642c25070015042c20307002030744003881a0710551040e1180d1282d40b809691210407040000d982e014174192810b5000c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 710214442 1250 710213192 710213201
    0x1b1a0a1a090c070f0c050904030807020f0f190204090209040501021201150f0c02010e09011e05030318010e1c030903032a170d060f0617010303170c121e011512 70
    0x5c8410510a43d0b001c41e80d980c5034030100780700e24400e5a480204c0d107407102e0000d041418040040c1e4150b03203c0113100c1910700c001301380d00c101c11840d050b603028000100e00004000e0706c020900030750010f00402c2844284001034000f41122104940d40200503641d60290708030480140304400001141592051589840751032554501c2d4014036100000301d0349400058101d260a034810780c00102c055181483c4004100c0505004081c00c030f010354205000c1c160368200443c1d104121904100c3c031600303140c4a5598400c1181c007608000300d841885c80740946000b50442c85140000d90104d01b403552140d4600d2080342c600c18a41c10016140c00e071154841c0d80d500d41020080302c901c03120380c3c030600c1515241c0d0700902c00d00000740703400d51001d102c8174500305001c1c0c6440340110400e044e4203a03010062003c42e800041101140c0003403840c5104035030b40c18102d03420380e0140715480e81a583c280400e1002214000010001981c0790106405650343e03660610080080c1001112012034039200c00300b00487c105134403 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 710215692 1250 710214442 710214473
    0x906010e03100f06060c03081f03050307030c020306011406091003020f0c07050f01022b0207050604060c060b062a0f07080618010c1b1a0a1a090c07 65
    0x140000c480c40504000780c00d04065082203854150346070b8198403030705402c1c05040b00520b1142409039001103d030700c0041ca0001d00800c2d5444c2c81c1094440100c0d5040c2c088500001541c01000780c90325a0400d14006000c0c80c0709020030b0384a48101400424070058850f813000c0381c003c000300701502d081d501e4000d000221502c9007110051581c00e114150406640340000e040b0018480c001c0d204203420f0800704209191107628040c115444120042d03290b42c00c9426080503061030411a0701e1200e07806078104d140041c10b0300040d03008140480d000580c2074200105009851240c1406c0c0421010601804250301030310b81c4210400f402911000c180c0c1d0810b02280000d54440b1060358610b8030908103482c9007a00a610045240c0d10000400c0001e0b07402d1200c0080c0c514004000f800f81d01c0184000a1000c22040804041c2c401c4403000141080140316412860b403940c1040844545070843da01e800900701c40602001030301d080400d81d012880c02c00380041c4074089201e5600d0030141c1381d44404601010000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 710216942 1250 710215692 710215697
    0x6030504020d061d21090108091c0e01030b030d0503070c0804080d081905040f0209060d060c0e030d020703020d080c15162a080c010204090905010902030c011d090601 73
    0x180702c1c02c0842c0450107103a1068070f0901c0243c8404081030b0b482c40c0303030490581008074000100b20324180c290303010108640100744c091802ca0040d45800c3c5000382040c09103021100c60007042d90a92071250b030001c0c05012002c0003600d0400c0340311441d2041c55140ca82d168084c600041c030410018002a01603002004900d0248036054101904c0d1150545860322140070f8030042a00c4600b00301400d08040c08180b544c00c00301d1000c2c0010b081594035032041400b5644000d00c1480000000360709511484000e505aa420103028070000901078409811000d4408215010380110841500322030b000240060489a02600b5034002c1c040300d4546455540000038006c1a80c0501c01914401a1030600c81c0c030b0159126030020b480c40000084054008100401000f1084041c504c1d05007644031410203141220b0b8120002541c0c50440146030703030082c03103a0b42001c012180380240820030705c901580b11541851080e0211914003c000006540c2d207800004103802c2600715141541c068200700c89015000507060 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 710218192 1250 710216942 710216959
    0xb070f080c160b0c160e0601080711150f090a0809060a020a1425150c081b0a0506090606100e0102031c0f0506060f070f0c08030703050d06050f0a0603050402 69
    0x1c0c00c0309100c03001d2a40706115508003c0b46040c00d04c1010710801d25100450500f01200500e000280c4060240052142d1305000b401c1000038031060141c1003c0d4100d502e600247c505401070f0000700030025500390b40704016800c01d9030003c1c414840c000342c01030115800c6291241841401c80800020750300c0190303040114004c0140c404000b4642041e0b4001d090303100c1002c0d0010410b80e1600340345440356a00e00c14500c2c420100c1c100241e1009220b9032003064080d00d8441e6202c2100d080c05c110074030403e40b1100b0100c1003440324070740307000c008a21403611500c14000d490450300c131020000c0da0703414140c40031903000100e4521105c0d03490007150b0280c0400d00c18019a4102112004102080c5031158641c2089580b074003501401e828580c031a007584070000710303401820007203080100701c0c10b40104d15005000b0300d22141000f0a2150310b0f6140e0006140c04412240d441c607440c94028016005030080003455810401d020544d45064502011008000f820403442d039454418120090030001c1d00c1641c02150741c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 710219442 1250 710218192 710218213
    0xc0f060c010501060908010b0a0b0d02030403140d0204170102070b011203030e1005070e10120218093301140d02120421020105190b0121060905010b070f080c 69
    0xa0103030318001d084075180e09843e06d14003040c181c00d40b101c2c405020310400c0704013024040000b11200b074503e0701103483c0340107850380c0d0381d0710702920380c004511a04c10b8104004903108000e0503075a0000d1040c0d8000503440c501103401860b001d4280c1c050210001d0055807070200621442c003045c4100b4170703c540039180c080744007070040303185904020411070019982a1a80c04201c0204d4001c0d8003020401c001359101c13035105240c00d2009010509004500c4d8110360005071440904e00c1d000c07407540401c4802005203116081940f124204100000060702c00307085e504625544050515007400c0b050801a10360304105020a02b400c0c005034401c2413442c4c01c80ba400e0013611055002d0480a42c070452003940a600e0262080381c0e08900b0002001701c2404680c100070422109000010300d15082d400c0c0114042160054940103070b03148842044041903290350074454100c2000c03660804030840340c0d556010425a40c0320380c0071104a1041440181c05d14110f519200300140b0710400400720031001c0300a952a4111 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 710220692 1250 710219442 710219467
    0x81b04030302070303080108060412050306150c0303040b010b0732011b0305280b030f10051e0402011b170a090f21080c011d0303090c01030b030c0f06 66
    0xd4000354010b070302442082c8101a001448207003d8035a92005002a16140e5112a510b036015030540c2c00300714011000c40c1090b00c6403404481c04200004546032544440030303c0f00d90b240c008460a44007410404000104100600115040d8a0f00408400d0081c58031242036020303150b50b0f002900d1b600307440481c26a8402c2082c4201c2103105500d10540114940006008054420145c4511a564141120300c2c1204100e41000d807a034050614003c40c0327407070b40f11000a050140d03d0100d680a802a004081440394955026522402107004603483d105601340b85a40020011034000303022802c0c0480601c3c8002c65940c05008140c80341d030044c003048040350041f00880d01301a0080c030204c0e10b4844144008040d21002c000541102d940500450414208079072040e444158058400c010000d41c4140781107085d0081c40020000c001e0b81c3da1444645880540c2d01d13401124035803a14002c02d4800e079081d44c420701a10f12548002001445905608010040c0c0c4036624055198842020010f000103510b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 710221942 1250 710220692 710220697
    0x4050405010f150609030f020414010b0316030203070504170a050d0c0209061203091002010e01091a1605030a02160b04060617030903120d0902030106140a060c080a081b 74
    0x148644000300c0c0200b8803004110644001d110611000c030780300e41c400e001c0306510103014411a0f4029114040808090001c81d0051000a01d1503608103c03c00c00801c41c42c034954010360181202100c0644004031252041b002ca01040d610100010001c00c800c004404007014250190501d0b1010341d58012003030750b20b2610b0200c4201c01000401c48032103034001503203004e0300440d030700840c00d03950801150542501c541d140e102e1440030f107204950759100542c00510035444890b0081801000b0000c0750311500780310545541100030705054002840004520448941d50b1444001250310780070b00710745940f81110065004081c19150614a1041a001180a0b0480c550160303000c0e0100048480c148526000c6400364008140f4080e4810090300300700e0b440000303851610503441c0c6d07041034560380c0c2e0700e0840c0058a120503001e5850360030500c01203000a071250514034480300880d04100419914070f03041d21640b0105101034617090040c41a501c46c01e00803604940e22514280b0002c4e0145c441950720744d0181c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 710223192 1250 710221942 710221951
    0xe12030c0d0f0b0a0509100306110c07060503250f03020c03071a061c0b04110f1809060901091e08120c0301180908031f08030724021c050c090405 64
    0x41c0c3c07284050100383c00c0c8a2000c0780034040c1030355100344a240c04401c80c000e0a00d030f440000c104030790382c00341a9030000d2160195400e0211500a840c10b0540c0d8202c020015001562108030105d0580c1d0003e00e10302040c000081c1c03800d86910b0303081c0072404102054000707400c541d003c2001404104001c00000c4e1420390b00341c509208900260140d0b082030014008510b41000488260035840500d06020440328003105a1040d80400039401d00f075400c5000c5082c800b00b04042a03004100c07000c0007400604866603949c03040f5940001c0750b20b03a6441404581c00d0700d80c500001761550310f054240340c0c1e0305207400341d694000fa4014985079242c4118074420211301502210100351304000480140180d0700056450041034000c4081400007002c076481d640010721024003808004001c0714110094051600000c500402c603e4090300e03100c100c142071401c15802903010030141c600401c4140d42e601e043c1031081d100041500c0c41c0c11030034071200c04034000c01000d000e4140e00c24003605000c00b80d083c0da0b82c0e003e0103104 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 710224442 1250 710223192 710223221
    0x30f090816180b03030715110a0f0305061c020d0602090603010b04030c050a0303090b030402041d010906110a0507031b06150302010806040627020d09050606130e12030c0d 75
    0x1072481e2071082d4900740c5a001e07150503524244040001c180e900001566030080e00301c50001301c020030307030400071005110110707182d000c140c80810314030301d020741040342e0340048a0561014049542d6070001c0091000307480c20621400d500100381c3d00007605121110400c02440b4040062030021950700199864200f41c0c490360f0b400e070700003c0910410442c00100d800500c010b4807121084c5082d80d0303010f480040d1034002c8165034900840050300b550f44d603030011794808940026450079110b01c668060301800e41e0321010707101c003030401c4000e0070801c00301e804442c0d545001d41d5505042c020b1550f0129482c40d020540a03441d100c0202020020030020320401c4030716004281429511883c41c400988144801858070b03100324a00001004413004844585044425020341c80100c1400c9058045c000c1c016280070705c0c0031501e411020001c201001442c180101e0b41103490f07424580101c0d1020065a400c48121349940d042044032824030303030320500559008030000c000e082c10b110109521408039050300c00c2031100f = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 710225692 1250 710224442 710224483
    0x2040501170f01050c030403030221010b040f0e04020f0d17040906060e0d0309030201032d02090f06030408090103110903010e010f0e070506190314070807030c1b030f0908 75
    0x80448003000008441074002d0000e1000f8503103c54616000c1c0001031000c1d050640018112001d02c1d844400c141040700c40040054a650b110b0540c0c1c61950421300400400381001d5034003040d2b18450400c00340c03090360700520004103401c1309018030141c40c1c0f020501302c1d0b00c66246101c13907606001c82c40103440901001100028ae4038540403000f84a004460109401108115480d0003c0f950109500094a4080c01e010607405038521105107818514040c03c0c54115030030204d05c02d03011544c6c00070401c000007100c03001000e414080402445100035140108403a20422650010394042c3e001030080001d1508020f00700409140801e081d5294070110700340d01d0b59520031410050380c40d449885800c01c200c60042030101c0c10700707000c10f4042c403071003180d404000110b030801c0401074440d0b0810000018259851400381c00c0001c005445080c0c01d6580002090411030585901d521418840c1e15000b002003410b101e0030072546058600444155407201000144d0741c020800140802200003001a90780600748d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 710226942 1250 710225692 710225729
    0x6030a0b0a0909050d230f210c031305010b060a030f11031006030209040902030f0706030507171306114b1b06242e090302040501 57
    0xc5040c2190b040440351600e08480007011810001d00d0b8001800142443e640760b880e416451000c07410fa0084c400c2851800250840b0116013500103400500103040d080550721601c00100c5200c2c0b8011100801554001d00c0003816282000303490b81c91142c0600300019000d8054000300c0d0b400c0e031100100c0c81c0420f071035101c019410b40c6203204214446240159845c158104611a004141c03144c0c894442090b4001c41c22400580c0e80d580820440c0d503008081340c0322420131444068503401c0074801c00340400c1c1ba01300015103090280c1202d541100d0b00e030310350001c2980c40c00c1c0c50035852102c040c01075600c0c070340d190824004136110900600707030740364078101064111101003542c0540f00390041c109020700381c00281e900c140400c980784030070298002030300c035a4840611014480a140c6814482c04a80c8681d0051011500c1f0341e90b1201e5101c41107159403049460b000060042c90b099800c1002c503a520f004a0415001801c00100600c200480c60402c510550300e03000107094407020f0308a07196503003002c040354 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 710228192 1250 710226942 710226949
    0x1e02090f0411030604150207030e0907030c0f020307030504050d110a031433040f0605310c030b0a02070812060f12070311060d0c030e10020c07090b0f06030a0b 70
    0x1559518003c50081c2094034050f0f403031400708451040130415258010542508240c011140d10544a4000d041100f2500e40a03c0050180c40040340000228458a100c020740390301c00f01c01c80c0c1c405a0152602450189440d051002000303846405440210500c000c3c0100d9585110000c0c2c010f50040c00403041143c02850114146400004481d0b14031802168401280180245400c04041c1540d0503100755541c07070406074907a4820003401802c075441c010400c044c50f83c0341004411202c00300428040c01c1064805800240160714030007514024504408000040c0d40c0c00100d41d00c100d810b240581401c1d40c550342c0100f04e800c10f150b0001618110030400056040102180c888258100c4660200c00480e428054903500c0e82e000141c0f0502c2000c140d00c005480f45000c580103180d95010400c8490070b805001001005840809e8130075008400900c81d00110500035507503044106e0001d051444e14002c9400700800400c0d1060303801031907800701d444080d82c442001e544542c01542c004100103100d803081 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 710229442 1250 710228192 710228213
    0x81f1e0315060f09091a0f010e0c090306160908070e010515190c050109080a0810230405100905040c0920090f040b0a0b0904150506071e02090f04 64
    0x1a05007440c902034080181c8005101007100721050180001010441404c11300e40c0031900300c2d103850b444101c080522040080600c01581250f0040e000c05400b81c8941d01010750303510a0541c025415806000425540042084e0b4512100d100d0b040c4200c0c0e60340c0d00e04c943c50404040c0d1f40025007031040c2500401143c10710408800d0580b500840c032528102c2201405406040040d40083c00c01c1800d04101040040941c409111150007104183d1241641c0100400c0020200c0f41410005800e107400071b5400034922964101c3c541095181a000960760144001400001c005c000808119400002d40c411203200d40e0740030301d0046003050b001e10706044821058030600411600c244107501d4104428507c140c00303036403426108482080400d4100000034003d0032440b05a554040c4065030b0000340c1c21072800052105d940141d40600844102d583c8443d0300c1c40d8180725060700319004101c0103001070203459146164070351040c0c0ca000440c50079000b050a00008940e9000e036420344c003003480300340005001d2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 710230692 1250 710229442 710229473
    0x9120d120f050412050c0106051903050d020f07061b06060303051306021204031101050c0708010209030c04090b0c070804030506070e01030612111309170721081f1e03 73
    0x1d060202d410b0a0b550a40e00e130484426002c100000403600c0c5590907002e400c8180181030003002085111901c0c21039010280c5c41d44000c075480c2c4110300c0c10045843c004a00301e683d8400d00d40c05044228076203401035071215010740d60b81003a10002401c03800029150f200d80c1000d1070083d0f5803036444010501d601280d04102e80c00c51401d6501c9402030b28400340c034400480c1c0c1502e07482080d0700c05c1480b0200c01603a0501030300c0e81d5500140200b100c08246100154003528160a0840803201310b01218020700080314650303400989480b1841000030000d06c178000062590318416150305c3d182541d01c0d11024145502910003500040e507090303800240f50b03490f006c0c04e009085070381703800710b0707a2a03041d41c4031080701c180c1140e01405503d0700340c200507000880303501102c2415003021940c0b0382d01c400082014038a034028001156a80b444421240d044044c40f0020701e030050316920382094540301c6000400c440e10000e06100c2010501c0b50002c10b0001502c12031070600040080c54042d140c0c21443c01d0403614a8214 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 710231942 1250 710230692 710230721
    0xa050706140c0d0e060417010c020c0609030709022506090c240e01021e0312010e010f0311040f060303080f0c031302010324030c090c050f030c09120d12 67
    0x402c8803880000b188080d41c02c0150f083c102c40010f00c060200c4d080e030086a01c10070f109031444d841e5400100341034200a29120540d82614a100d1110042000f21f01039500701e183c040e8020f420500c02801a58001c0c06480014480043c15039401d032242d2401001e00d00e82101c81d240c8030b903141c60411000c10074003405070070802e01d0b12107200c22681c1d610031032541d031220010801913443d01e00c0b022a4004d1020b50f0841c174580980c0c23024035141c00f801c50780e00d5120000c03814800c1e01c11800005d09490b0860010306031100c441405c03001328611303140e401c802c080c400301140c0c5c06641c41d40b02d000309003100e116100c0158480e80350896580380a000030f00c100d134001480090181020810410182e0980071a000d2465090800103034030604180001419109503840310000b400c1c0385408014441b000582000315404c0c010184a032005044048465008100980c0840c1e07206002260060703171440050462031002601420030389004015240c40c000030020003402080e440600f5000b04d9202d0f0145030034981d02d51 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 710233192 1250 710231942 710231947
    0x10f06080d11030f091e060a02010204051c08190e0a15080f062110060e04120306030c050f040b040c081014030705300d0e0108060d02060a050c0a05070614 68
    0x2031541300d042e0700c82d4664480c4501020b08928200029106045a03c24406011940c80e81d18100c1c0190007903005000d0a032003608407448000909420a031032810301d0303a010001c6802e040c480b0b081d1310003903aa038103c203030140490701c0d0030301180d071721751032500f000800c0d080584102d1002914800380405c800984029190100c1c1000c0110f940c031520941842d110340311149803044454015224184004a40b294910506001d40010018103010369240160b0081c0003100c415480c4800680131200a07200080c54084c0e10102008540f6101c00e00403210a4080d001003450342450000804540c1c1145a800c003048000c4180501d8459202500001c0c011346441c4c11018401300002940d50300f6644161845103a42120b8000d80c1240540d02d80b40880112401d40b180c01007140304592503064101d444030000c0c40c0d00c001d041d1b440d885261868090303c000750408903030b10416028001254040f810207014030400f00950381c040d440c20170481c100203000b4070160088605001c070041c200d654410b03183c80d290005 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 710234442 1250 710233192 710233207
    0x4060501180303080705070b01030c030b09030c0d0302071502070b040c120506190608060412080703050f0703090809030a03050403020f01050901170a14180f0105090304060809010f06080d1103 84
    0x4988810152a01030804c00300741c2d52a25401c550034890300fa001071a52000e80c000200300b01c01803140f007058034403071040c4104c1c0790744440002d1fa90780244042d41ea030320360089000c9070940b80258000c0090600481a1008450000c004282a81c0c020002210041c07a62000c2000f840a44800507015188105440c1900c00c06c50300c0341582c551001d080c2000701105c24441c6a24004d107035100c1da00404916068401e149007500782021250510600080480e0754540014034080c401c1c0f05152240c0d104040d0003400da00c030b44008900a1040c102d0403101e02c907041104c01c41940c3d041080c1c03e0100d100769100c2d41c0d030f2402d51040c00001085012f80b41c1c148401405200b503160b822203001c182160111102078081c0d900e0003c1400604291034900014a180105000035488480940c2006038200da00701c2c3c00c400d100341513403403c840c4d00f01d611480540050000b40300c1103100310401e82c0c000080d42c3c004103004d103c283c1050112215a0310070340b903950024550a42003030f040300518880e0b074034080195040108 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 710235692 1250 710234442 710234477
    0x50c04020a020c1e0609010302180d140105060405160e01032702010e040b0105040b0f0d140708060d0c12080d020a0309120503010e011502100504030906020c241e0a020c04060501 78
    0x10346c0d0700c01c0b1305164011510084110724460a401400740041c0030f440c034030f5000c0c01c00750100426240c20b80a03039400e040c0051804e0405009850040da024800c102140b13400301070446240ba8446600e40c100350b190880d402d0000451b00c483e218905410085404084041c800035002c6240c403484c0e940200c1c01c00740103200d81d03070f00101598100c130038203440c0e87c0d0340c4d50003c00c0403030701ca2080206460b181c40c6041c0514060468007002030b4400d4030b0396290000940c42c3c5004010003003040b2040248198003004040c40300031000d68407111458400e1001609150321070241900340c2c4c01c110007200000c1d0381c0741c2c110070034490b8100082003c4807050800511359410030107070340030b00364050080b81c01c01e081c0d414034081c640340708001045266260f00810081801c0c24980104003112900c5500f0042c42808140d050724a4040d520b5140d40300344a40301019182c4618040019811055074070003503c03000381d500d406081c8240001c01700041a1340c050a204030700c0d0010001198919000f85040041e007002a100107034 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 710236942 1250 710235692 710235697
    0x12a110f060f040203071802030633090607021507060c140906070f080304140c011b020f0a03050f0a12110c0f0a0b0c01390c050c04020a020c1e06 64
    0x82c1c0800a1082a40e5500100e480c2c034410341c0c0b04c0d080c1c1c00d00e10102e20b030060701503034061401410200d46950110110b000103148203012000706104c00e02050040288150900000f40384144010b040b05041c4a1603400180e060040e4a42210600d18005401d0b810004076100305101840c0504103116103124079846012140144840b40e400380c0e000080030b60900001c44020142d491307100d180380d0750f80c2c50f0a04d00f2405000340b000b0684181d00c9400c0e031040c03856004034617044a03441e4440c0300742c0c661685e43d020400850154401c0e0f9400c0032028802001058041c000d051806107820001c0803100b6045c030b06145402c204075265810040f03040140c0704a14000f1030f156007103050441d201c00ea10341d4260b00041488180d81e0040b404038000103050f000da0f040640101c1101c005030082c103034501c02d006010010f07030368050b600c403d205003030703400389100c0d20f030066002c40da603907020718200e0700c02c0c1d02c4042c08181268042e41074180580d00004895900b482e180c004204c6556070713504400340030300403107000c01e1390360 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 710238192 1250 710236942 710236951
    0x3170a140703020327012d0810030b2e030210050c0c060a0c0c0b120f0a02040909140c0d030915020c060d20030f18012a110f06 56
    0x49030010301c11091601c01c00035101e8100c0200540000004030941041c001108600c40e6408680810b506007184100305501040f4a0340405c0d100c9440341d01e107102210500c4005100d80116283c080010011503903608043d8400c6504014602401e0303140f0030010031182e540d0290003140e0084c18014801a2180042059404c3d02802e200b9110400d01e444075003800441c3d2003407504840086403505a03264800340311480b240c0991440d4180e5516400080ba00784140e0340710142c03103081040801c4a00010801c190342c0440340c1d0b20010704140d140d60b00a4155800300c40309407443c0c50807900b04032445000f40400022000c0c00c60749100a071102e6034004d00b00054600c0b0304640c19030895040d00066000340606a1000070081c0483e40d19218501e03040001e0900a0450790007001703880040302e8416080e402c581c01045940c00d0106280c0c0d4814420f00d1803081e205d00e481855484280c00360341c0402c5200d074225000c0008501c50326245100c0c02c01000720302085007241d8a0740c446904220380c2500841d185412 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 710239442 1250 710238192 710238227
    0x80f030a17101403030c0d020706030f0b0609150706060b1209010b0102100b040605060301030b0709170304030b1b0d0f0e0109110f0102032101050f1e011d040603030903170a 76
    0xc03880f80000203411801407045034021400b507801908905603021036844255052501c2c10841c2c00c0e5901088402c40395040d44081d0045010010503125140210b5051811070740e41c44030314584161652040d0940d103c0d0b0b0b000004414002c82c0301e2129040f0805000d50110122000701714005110f80003d6030b464440c004405038a41c1d6000001c21620740790480c00180c0000340c00319a407541d6a1616030712003081242d4440004603060300c0425503140c0c070b801c070f5000103c0c444011814a42140c88070040c0740c2000c0e0811445540d40e400342080415600040c0401c4140000001600000d5000706015946401200405a4900b0002c02d00280c40142c85891118080c1ea502a03c9010000184c1c40d41c81442c5900d20b8051000d0090703100e650f14650707030b00d050390420b9a5002c060f01c040b4051000c0501d40396100c0da0400000c0b280400154410b8a2207100d011030020522501da040d0000b213011034946400c25000901d40300740910a0040c00880306d03030442c014080321442d01004100c010010024451968071 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 710240692 1250 710239442 710239469
    0x40902100e04020f0f09030f0f0601030b0a0f0e150a06060903061505030114070e0109150305070c02100c0b131106180306011203300209010207080f030a1710 69
    0x2810344035941903134211280400040c1d0350310603c41e0000c0483e0440c1d00d100c0d21038817030940b414800220102d203a28440160310004c1c0166403c44c2d403202111400140781501450381c40101c0683c0610901072802600344400c013506094545840401600748000d0801c0700741410701d00c0800c205980000004116a008540020400340400c516211040182d00182d410f60a01218441e00c4141c5110240506401d417181981054503000550320f1038214030031f2808201c40c411882c1303841c2c1e0007904040e030702070038515141e20030704e0850380061000c03002040200300040201c0c01d024108564004031a402c50144500500c00041640d1a8960035141414242c02840c0c00b01e810044040d250f214203004400060640e4042d685404002c184d210384514291b00240c0c169401c1400c03c07055444075100808600b105c0425201e201b0901030180d0b00801e481d9045106400b0001150750042c40f013202d03180a01c1024554410070340c80010308807501610410007490341401804504002c0c03034104400c5a0508400e1074 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 710241942 1250 710240692 710240717
    0x120b0a0e0403020f160510020c0405280b06070f0203010b030a0605091e030406141b0307061802030706110c12010209010f14030f070306120c15020c03060114041104060905040b04090210 81
    0x741088031000401d03401500b00018808009060f6338042c1c242ca1240100006a0703501094030ba003a214003000b0313190440e2040000101050100e044509414000303800032520342c80c0d203404a482c2c000e40e40011707a10070b50b895041c0500031005102013400e0840640103044034151000302291a48128031a84040c0010044522484404101528540c81c0000040020821084012520b07640202d4048034242d217080e45003514031903100300c0036200d540c01500506e4268201107060714410340303518900200d48036201c1d0f40300031a6030300100c004900c0483c44c005030f1079504002c000740810f00301c62440414407004103021442d074002042925400359a19880c1e4049031100b981c181c00601d2240c01c029903008041451005004408a21808071600840000c00304a000002261904e40b14095694503811401c0104580c121342c2d6002c540c20403009100003010084980c0300d42080c0d00603802180480d091260812040c6000d119451a440090b40d043c00100e200758009150b42034038500b02e0040c00041c0d607000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 710243192 1250 710241942 710241947
    0x3050a24060605030c07050f100e0106122303040801020d02090a1a0d0b0f040c0e031510031428031715040f060e010b090a0b04080706120b0a0e0403020f160510 70
    0x2820701e802c800c03040e27070302000c05400f4107000381c00709900720360043d82008000640c84007000680744032a50040f6400e0444003510448014030440c0315407210340d0744014040854001020710081004a11940700165100c40c808180407074150b480e13100584c0228051401c03924640943c0448030505a0200005900c000c00350001c2c1605c0d402c4880b040c0c00c141340c04111981150410100c55004078100d08888140d145145442c03c030075011034404d50500d03c140c504000154803101c42c1c14500e9201c205540d000030781007402c0708442062070746034007004217482800800c0c0b6801041d0f01016175044004040f0500e400780383d08070b2607401c6440306030296643c0c61900d20031b0308884d40b0100250807003500042c0300c1e595035001c491681d080300f0009442418415030020b45010a03900700e0303040b00c00c848040d0075003914010090340d60034a00400218456110340341e10348980d4610b00c0300005412480c000940c213042505000785000c0c802d00001c259580720b520001c001785c0f0b405240c0c500b02d031800c40b060415030b00c414004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 710244442 1250 710243192 710243203
    0x601080d0f0c050f03070c140a0320010c08071a0c0309030301060f17010602030a020c0a05030a02150c0a050307031d03061f0b1204380a0603050a24060605030c0705 72
    0x100c1303007800082804c504210810f583c01c01100c03186007941d0185400d05082002c0007401e0b1200920071b00c3d8010103400381c040610115008100141032074425440755407500b01d03e6602c424011a9201c0102e601900c0b025030400519410130310507810541149407800d02d0640d244810300880c03050095110701440c4641c49000c00c0d0b0004808805e404a155a441d82e029589070002840440903010b40c00c5404000d00b445080c01d81251340080080c81c184565800b07008030024000b504000c045820001c2e001120004c101402d10103120f10001d5541e8149030800034082c9500c1c00010b070310203194151075009540e0010755607401000c030510601305016140d450394080c1015034030443e01d81101103007003884040a81d0030180304501500415004482c00322489000342541d01030640045104515944208200c850644d4402490800024200e4490f25002e1a05030142070454480441c410310800140c48800041b02e0703207030007080c2842a43d0038003001800b0b41c04001d01c0c2c50f00405000c2448418080308014 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 710245692 1250 710244442 710244463
    0x10f03020405060a081506120c0a1403011503050c010e0a0b070b0c0d1a13050f010902030702070302090a0f0b030c0d02090405071d0a200d0e011b030e0601080d0f0c05 73
    0x45032440034102e02001b4910900302c90892013000200e064803506400407070120911280180441c0d8540c0c00c00424420741d6510b0100d05030190360f92107032104081302034040000558050402445400105c800042100c00c0400da103600075201c481c03040240414403010345500c4d0f6400400071032690789512001034107008038070b41d01c01040e0a140c44030f2000c0480352440e85410b0380a8803034400c041c81078140b41050f1780061b2008000150395200400c080750b1180d000e544c0028141c8150744440b5581e800280301c04006541c007a580390f540301d0b125001074886100f42c143d0143c050300601202045480000c2c03101d244001c02070300079000400000c080000601040002e002d104d00c600c050a0692039042c00c8150048480d01c80032850540d0980c4910841070311100b403201302030a003510301696040c4803005049030000d21a090340d2194003401c00d0600d41c0541801c1c1c08019580003581e800c040a8003480c0c9041030b03006071130300d401029a0100d143d600000c03420b00b00041e41409850a44245051460040c0a04 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 710246942 1250 710245692 710245709
    0x30c060515120a02091602100c110609010b06090d11030f013201060e0607140102450d050f01090204050a1509110903010501090c021203010f03020405060a 68
    0x1400c0101c8040700c0c429024080700e0a45111900c81c0d0034080341c1da500c0010560107035005172148000b031140520702070710300c800380d42600c196414022008961000c3d50075070440c00005c40e1031413503074000100040043c135a0003c0c0b20310003840301e00e03c03c1e804505188a000c840e41c0c0566080c03254901880800b444102d501350000d011545101c100c4a1100e00900020368000c031001e20203520700c80c50030b01c4d5414600d6000f44000c140b1035280d2800c003040c0c034a540d01b10701c0c0603003150090154002140603040d0076102c0d141d4280c005655036540c0106034110b0851807444a81c4421441a01072403451003001a04901c04001000e0142c001408001801c134405c408004107036101d40545246c5c0300e0b0064201050ba24800c0c0e800f03102e80d49440380c0d05000d44e00700c01c2521603269902c402c2003107499090340060440d001c4510410789003880c10360129080d140f090308814038650701c030704003115116810000050080b0a080701c0358103550400c0380042002d48584006480b80e5128404103400d560740c200c1c078800070310b18034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 710248192 1250 710246942 710246951
    0xe280c090f0f080c0901080601180b0402070609050705061e0c0c0306010306062619020136090e1002070303152603030105010525051509100225030c06 66
    0xa4100200c02e000c0c038000c1015500401c0751001550404441007816074552101030013843e800e00e0000707001440348220800c092611682078980e1911079100810b40640554804655800700303092084c0b4006107540842d003d08400c1141d030b03900003541542e02c1000e100c00100a56036507075241d000303407911650b007902e07640c1402000000000c0208991101c401c4411400540105200030340041079602109103603100345400001300c40c20359100100c02542c0e2288141008201c4c2103034007007014502441540907902000610485080c514000d0305808000c246150080c0f10242074400365640720b0f115951610011600429050b04140c0250443c00801c091100c840c90034aa48a80801b010a0300c80c07103a900d024102d00201031300c140c1c0441140d050b41c0068442e146000c280c03058001c601004003511804808040d61a0000106c003806404c55403055100c405d0030710305040105506041401c0e500c0c0340701d6031040040031551411000c0321245410741c03120040601d4201d090a55100b01e81c418001c0850340390 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 710249442 1250 710248192 710248199
    0xd0c060e0a02042f040303050a030527010204030212070602120703021510091503021012060b0a050a020601080106060c03030e0c0901030302031909030818130212010e280c090f 77
    0xc3e400c140c1410b01d0124021380c50700400507100e2240301320700001d030000c0c03030400c10180260300a400c0150041444da04164a08030300c00040490490322101d40300190f500006c0070000d510300352400610180c1b0312400380201500e0200b0280d52030100e1000003201410101e00e1805042c003d2018400c481941a0f40d01424501b0101c0e10400b08c1c41da000700070b1804d00e0b10003482907520b90703400c6a505907030380a89004130740c03a140041a22560001c271710918400d80c54907070118005c2c10004c007130704002c0100c1c0c036555125895058041c0c24a10145c100070078030f80c9072880420815038000342583c40290142400a0404480f00b0103505000159000d550071030500000081015800001400c4000141c0c030004040d4402d048211040c00d150304c00a810742100b880810425064400c4501c0a444024861083c0c00384100014059030400050307103143d5078112004101c051a621125039219014401c09181e5407002405820020f00c56a091020103941d40100c2c2c010038060a41003002e04200950103024554 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 710250692 1250 710249442 710249471
    0x2091c080d1521030e040e030913020315060703080402040207030512070210050c0a021b04020c060c030906060a150815032a01020712030c0f02120a030905030d0c060e0a0204 76
    0x61034460090f40d000c5000b4204014400803881090044e4145c2e1000600803a02c410407010300845030960465000410016a0325581d04448815070002000e000d6100d00d08014054120b114189210b40980300802205000903407050b0f241c1d9225504803001078407203c4a0800300d802e80103031660700d1320002c113102c01e01c003e00350001900842912494824000c50b5145441000c440c0200d000da400540e01c04e0702042091402911030758000311004d4801404c040e501010540352140584891030300c48000000c0c06a070340c06c06d00c65160f000006440c0050300b03920b130407440031441910020710b1040241d5030010402034aa800e603440c00c0140c000b8119154642d180003144210359800428007603a80744034924009550001c24040d003200e800202c40d21908180d502c0035030303d81d00c07865011030340c18071010001030050b51140c00000701c0b150b000c00180413a180500e400f501d0341c0c95030f42000d4401c0e4405500f0404540c1d001c041c400c009a800400402ca800b10402d0b408e10344180c1790b000a502a0030818030078105013 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 710251798 1106 710250692 710250731
    0x102150a09080f0a0905010206010f030320101a0922030306090501030c18140c0901030e0a3009141c0c0f060302091c080d 54
    0x20351070358a600c1d1a903c003880104108074041800420b296018842401611081c0001c0c49294140429004002c14078071005007040781451100c07200001c20200c808052580000310382c812000718164201601c40e0f075410b00760782060904902803030b280c401181d030300a803001e101c07110030b860800b980403110001015056041c15114540082d004a036842818002c40c00707441c0a09180d03040884030703002c01c2d64018600c40e070076003000590985801040307596500f0407046400c1a64545103000180c004d022803101d4080035005500b148018421030031541c0c0785007c01060800d80240013068510240c0f03008003d60710001380546010320250381c00d410250621030300104107210303c46902041e2074404d08107800172540d0641e440c0b002c200000340c600500c005050181402e50800020402082041c0c0201510762075400e5603208142c1444a0784045491001d06940709000009400080c0103090 = true := by decide +kernel

theorem cover : BRFrame.Cov 710071942 710251798 := by
  have h0 := BRFrame.cov_init 710071942
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710071942 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 710071942 ≤ n) (h2 : n < 710251798) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
