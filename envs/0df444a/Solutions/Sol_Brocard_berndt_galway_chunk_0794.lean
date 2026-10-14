-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0794
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:50:51.887088+00:00
-- url     : https://prove2.me/submissions/185bbd93-16e5-4802-9d84-eff299a737ae

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 142625899 ≤ n < 142805755 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 142627149 1250 142625899 142625909
    0x140903120f01080a02010c170a0c050606030601051f140d0605040b09040201050a05030c0f042c041709040b03010204030b04020109170705120c03010e0c01170c030406020a09080a0c03030801 83
    0x2101c801004043d100156202c401034081c00d1810301d80c0400d003000083e00100c0700100b10408070000c0c2c1181d1655201240c2000b490281c0107645a540b00c030420152990000c0c41003a92005000b41070404000c86c445100030030a40506040410b610b40340145112a000b10303c00c2829181c1d5000c080019003414061702078800003c0b100c4c0a02890a0750000c0c10b82c0c0100040b107020424080300044e41040d282c800c860791200070707100f039689442da01c850a07850300d2000d054440c034810011001c1c00301118802d001d280a1988241000c000a0701e21561148542006401c585d0107600c031584551a51000e100a10245004080340725140c0390500014000003e00c1c4d0003800b036145a401080d00042c40400c508003a10030499039a047c09603114155440e00d00184a0190f065180c010a548040c800141181c0d42d02c0007070301d40c0c0d0420040a00b10060012b0103d805107a91102000005c0000308541d00602d43c803021810403001c51501c4407180340c0717040c0d400c60b0708030707118110000240709061b003100300140141 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 142628399 1250 142627149 142627171
    0xa060914120301030f032609060403171519050603180c0108040308070f0e1002060f0105010c05061303050408060a140c07350f0d0e0c091914090312 65
    0x5450340c0e40703001e01171070341940140c104103d911250a0181d40810f42c9110351445525990650401d0100303a6201c00b000d5408402103040b140c012031030904100e0300c4034031952524080319000c403012003d0000018240e03c0f001140b00443c40080f030f4980d03a10005d54044c0c121181000c481000c00e1808a18003110110317800d042c0504882000b0000342c0c080b054903401569480e0070000c0100840040c1c0c0d182840b0b21100d030344100310310b049642965000510501c00e14103292450030381e9a0320300054401d1400844041e2542d0809000110010a40020041c40034803034940140342a43d80c007211401c2201c160303044440152280c2107400500100000c458014240d144030758581303035255803041d0452407130a841540b21032140010605440c0140002c130144140e080403155140195041c001d103952001c00c601c6031a51401b0411070b513035003002071603118400001e000340c0302175294035011041148100e084550059244c10044540036440545030b400b8106000056840320340108866411a0000340f09503480 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 142629649 1250 142628399 142628401
    0x220608100605040b1c0825020312030c0f1c06060206040303110909060d210c031b030f050d0f0212061201090203120c150405070302031e03030601030c020a0609141203 73
    0x25075a4201d00850100845e4002c140020052800303041038003502d54207654403a904180c0020082e100211003056910072020384007640e989403880c11540c001503e41400d1003005100d10141010307810010403540d0404004034079841c1d01c0115040541c2c40c107811000c010b800c01c0d401e000401d07405001346902045210082070030f1103614400300c0c031840703002804184100134202a1a05101d00001540c4280d204c000402440600c0880c1c040c0500e140da0380d0850018003030960318440c0c2c400a00c01303004510f0b0326a648901d0050801d204440710741060402c00c02041e55180e04031101c0d600d80c401050034058080103001c407490034070308105408180070092140d80e4142412000142d60200d4161003211030145a661900540c21160345003010384030b041c00d00c0550800030700081c480b0015130309048a00c21412580b01408a101d0f0340c0c81818000002c1265a10600200301d156000340c00c0340700307a01103520403030704400f01c0c40e251380c030030746036991400c1d40d00010f21100f01c0581c034024800d05031200c0900b00d8040ca5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 142630899 1250 142629649 142629671
    0x5120a0203040f0b061804210206040b0609060a0e10060801050105090a0303030c0c0807050c0301110a020a020603040623040501060b0a050f090a08030403080d0501050a030f0222060810060504 84
    0xc907440c81c43c014922084040000c0c40c9599403529828400025950b10005207040c0c9031120419640f5110400c241c0c05002900701305610006106100c7da9000c100030025840b001c0503c044018003418032580144220030108600100c000c0300e91190b07400502038080c0302e103051400341c52000180c00403410840204200d0704546c582e98a12000c413a418a0005800c08140c07a040340c0710101e00e42c00504038180050580140071700001c0c0c032450107004038000c0046800149148189114109841025821900c0000050b1610030043c40c2d20901074807020034003003000360040c240802c00d0340110b02240055400d20040c41030911580002c0c20300c03c80464904401c040b40a001c83c040c040b01580c1401000880c4a000d0f01d80700c0310080185484012a500c0c0c40e00c9140c0450700c0d4105c2001c2d809014a007400000e068070301141e446013180d030008000036072050b0785c1d001d1101c02900c1c0701113040f0000c00351110b4085081c41d849110700038402e0300b000c0d00e142400b8420441c141c80d41640118410390814580250b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 142632149 1250 142630899 142630913
    0x912080721060b0c010608010c1107061d12060f060402030106050405040f110f031806011508070e031603021905010e19030209010902030a0b10210b0a0605120a020304 73
    0x1129800940d0760407040c00318010180082c0405800c891480b81000c2a8140c450905421074005c0e114007400a11401042c0b601c116640000b5200d030140b5070748480c500f0400a03001e00143c1a81c20032200300350100541c4031f03000c9440c40380ca1051500c00c0703070301203402c00c80c074807010541e03036500a802250203614651507c140103115004502429103c1c943c3e490924140c14a6a8401c96801560b92003042e00c50a19100c02d4405402c116801c64484013412204107040d2004280750341a40c8103882500004940f50f802110340f030500400d0b074020701c4003000601038039641c1004201ca01e088034003000b821241c10351041c02420003001510700c0020103c410309016070780c1c001040b601210030941c0c0e1541501c0300143e0803401710549501c042d4000019400200e00c41c131041c0c00a42c40744080050611010082000b40700044000c0c90060000a4a01040002900050000036a01d04010780081401000000000d440d1035081c2c0c40714010920010350203121038240d10030241d0104903048214258541070301ca490b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 142633399 1250 142632149 142632167
    0x1081501021e0f01140106020f1f02070822211a060d0b0c0301060318030905060d0605090901020d05060109060909021b0109050c030c030109030909020313021309120807 74
    0xc0b10241c020b07150000c90070104040d00100e480c3c403000344045100f0b090b07482e40b440c50a02400c8014021000c0c5481e03d02c40010340d60b001d03460720000301410f050a0302c0f4200300a401c81c1e201241c400c001049200d10101100080100340d00b030301c643c1545241d2401c0d00395808403003040ba40c00240044103401d8001325450489440140e00703462945809942d506001501302c200b00500100001c0c440014040c0610034400a541a901d643e14100801c1c41c40c14103039041042d0b0880000c000910b02c1200b0700041c100340018050076003c4c000c000c40d2450300c51000480400342140c52a61603036004c039070300394450800e0040ea03820200a0802144003403d00c04001e000034428080c1030f03401c40d0000b908080401714450602d0b100344042c0002c000302c2030303075160003a00c80d010781ea0003d1282c860b003001e0141c20b107410b2041c000c40541c581c40c1c0301005450141c040c1c010b504018184d59950101003282c0015807540f0406003419060590006004e2115140c40f40910320508907120800c28100b00300940160008418 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 142634649 1250 142633399 142633423
    0xe0a0b03040f0501090209070201062c1302010e0414040c0e0606040b030430030615051803010212010314010e010b06030c0c0106180e010b03030a0c03050708040f030b04020108150102 80
    0x1004001080e0030b000b401741c040940003d400103001800c100d9803c3e410740c4000c1c19600310141141d0340c442c180713800c003c00d1202890034402c003000060105100190b40110010b030140306044c071400040700040010201c5030641c1c103038a070004000040208102c0d0381c0c20311802070607801c100d14419007407040100300c01d03010780c0c02206900c40000000c01c003844402c2c500440c18600c405007209080c00503580b142d1750315081201c210046414070101060004241c900103245180b01d96885040103d181c44c1005600c03680201290155402c0103e203110101070501c0030b0103540200d00384004c6003c0c1c4c80d015801c4910303100031614281d16002e65051182c1d1040c00700ea4001096014003901d51120131000f60041240364000c07e01405400c80d0711045011a40040d03400511050017003160102d81c0090546900c40c04545a00144e280e00e124800070b030007036000e421618050246542810b8461444890780c8102d03400a848002c03091040104660740048415403040c2c8540314103400e50703450300000c0c1d80c0c0c410614072 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 142635899 1250 142634649 142634663
    0x30a050a02090414060a020d2306011b050d0e0a0e090c010c0203010f06081c1103030406021e0a1d03150c0a110303100906050a03150218031b010e0a0b0304 68
    0x1140c14014100d03503008031001d101085d20354504090841100942c032502d118031405082c0340030600310140c1048820304008007070000b401702e55235090044414010754841c803417440120702029000706501b004422002140d070b0b01c03107a0000741c0820400140a215500001055901170104100600082801e080d003210038206050403414920001e400361040d0b2140004e444e24000c80094070800000c3c0070380c0c0e0040c2140c8401a6064030000071140103062030900e012541c02003022400294040c0d00500c117025000c82d4581c1a03003245d00d2044119031200c408a0b00041c00b030741c5a00b0550501c510b0004103450100e0043c0202c0204100c6032801c000c00030289021a0800314190030350a01030b620324421a80242c05407556803901410a00c024151030245811003450550b000c45c650901108a80580707400030350044110302e48440440c0603510800e0303007081c101481002c6812644041144541d0001c6c50401812221369010004122203440010749210301000d007010459510070a08036034105811185c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 142637149 1250 142635899 142635901
    0x702031603050c0105070e09090c0a0e070507170a170708070c05030c101505030106031a060f0a0b0d050a020313020405040f0c0b0403140a150509070b0406020304050a05030a050a0209 80
    0x7400d03545400307a4454002d0a508020070421001c1c1c0c04400c900c041c4504440102140d211075191543e24800103102c42d420900b038241c01d008c5c4e80d029064095003d41c0742d10b0200d1416845607550000e422243e0302c0703035040c40b0b0003141e00c08000e070300308008a840304651803c2c641c00d4600a04000c161280c090421800d1000c80b030308801c1070150510884801112003012101c04084100e4010004c1c080792685020301403103000e01140702d00c0c06028810460341c01105040241c210180602e801030006004103500a42514104ca00c1e900c03519400c000820540c0007054891400c0403221080c4e4400802d449044d80c8100b04000640b100000100c7c2401d40640b0001a50b51b624504042030314500034004e00050b9006000041d007141c190300810546c0d10559581401444c02c50f401560b65017001c50040c0303000c088400c1c0e07100500096100c40ea104810b4000c80e50820f85d01e40c00150141c3c0290090340058100081c18000750901c1042d01d8014402070b0024156010181c0f16541c40c0d0003ca08001d00c42c00d8154 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 142638399 1250 142637149 142637153
    0x4090b18130318080c0406050411071b0e070c060b0a030203100908040801092103021606050705090d06060807050f03060711030c1f050606031311011403040b0405070e07020316 77
    0x721003c2201d003100b020590180c0e0300c581c0115512000b088013548a01c1c103082c00030566041030b014401c80c50303040c5466907083c0302c0d031981c903480b20301d041c1080c4a008410b0410001045c090503642603002c4da103581ca5440407440241800d009681601607004d0040c0003403001040141c50002c0d9a514940c501d80b4002400401881d04148500c00c0780d01c00c2100e9030034038000c5010301c800c1010713014110400c5051040f12401041e000d50036030080e909400384a207828054000440e000790006c07a8402c9841c80c00c5032074000c1c100005840002e5030f60054030500d40d121802e01c0b0b111010080d80c00070300800c550b41201c0b5100900040d548200080540c4104161300038001c548100030030688106506540a1f10a1000100c40c880c01114807944010000760034070000c0fa00509201c000c0328000c02580700103c440401580b200805514404010381c100b0a40c960400c1084004101550049208040ca03c1d00c9041505000c0e20b84003068000c1c1e048400e500d403e0200b429000012a02600c810140e140c004082c14 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 142639649 1250 142638399 142638407
    0x3030c0709110c0a110118121b03080a0306080601061d10020a08030702030325020307030c02150d050603010b010807120507090302100201050a0e01060b09060f071704090b181303 78
    0x42d82805803501c80c03440500200b0420005d4829071441c07c2e40c0e10402181020346580c0455118401c244004100041c400701044841c078504013a0940f407115400000d40d03e50711425158803610000001a540710300074404107000348000303401061b10b4904001591200002515a0601d01d00a035204492000104000c98000c0c0b006d0112141c000ca01c135510f91070007010103034403580102c0d20707034544c1840405101a410f402c2c03400743c019a0102e500642c2000c00c250b41c2031b40c0d1266004001e0f6400000b003190400030010b402c000700f80c0d40c001c4000c00305081c201041818207640c122007001e0b0510030f00d6810061082d500c0281075286081003600800d80e926400c406540741103494001035080219940324800705501500010702a002e0000c003044803240c9c1140b400d0803a8000d000b8001c000c002002020b0340c40c6080b4014112414017111081e182a080707503039090b142004031550010444000c50100050049131091500106d41034812681410100600035012100245901034041a03484550141803103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 142640899 1250 142639649 142639657
    0x909061203030c07150903051c06170d0305011409190207061802090f0103020907140d02070f05060f130b040809030106061d0102010608031e070602030103060605090603030c070911 79
    0x4081e02ea0342e0414411032102640641010342d4500c0c607005080300b19081c0341c0325001c030301c0e60103958490a22015486034a48001519511500b003516031602203015444001d22445080000d40200382d00c0d0708010016094800503800740d1540c904088010300c1540f140c190503580100a900b07071031344420001d03c11000038000c0c1007028105030325210a0004483d01603108203219402101c09800315035a2543d500c4403580240070003500b104030000428043c90184c045180b034590018085805c05580c542d00204a03000f140d81520b15964120782107061000a010741c50f088640786400b2100c9141c180301c1140069800000200010f060380f0001d002d1040d0758003a02c40020004000380521640e50704000c01031031025a808a6109070003600309d100f0b6005125400440d00103101a504001828030410404003405514112a0704104421000545c2c3e61000394013070f5102d0381000945905107030a000790070400602c03650081e13104010301080c0c1d0200186a800319080a8008030742010501600300b20303405 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 142642149 1250 142640899 142640929
    0x20a020f010c0806041b0f0e01090e13030e0904030903020d03032c010605040b090112030207030b0c0406030f09150903090504021303020f0402030f0c09150a030b01020706050906090906 81
    0x102e0b001e026008160300449280c011a011901801103008860080f04604844084e02c0086420040c50013103940c010301c2d40380c040010505140050b40e503505666813030f601084552500314080e264480c0300305904400d0384880054180c8003800140340c40e56002c0c0510007107020181c400d142c0684940300301b602c26044250201825030b8000000380044c0d405183c0c0c011000c208000550a01d040856141014800d0316036018005003001d004e41d10300030000d24901e408110a404500071101c0c0400426440706640d03029402c0e0b0740c0956035440c6041002000c943d0f007070103668456814030ba00c650100390700d040403254066159000107003441c203030325041d900b05030250b0000c0c0c1c200c2c0c00810581c007840c06889421088034001e9900d0810054030000b080200e1004a4108204071521800b1810814030079024108500d070140003d801c0103e443c011060342d07000b850140300000d803608540a400e50741402000000c2160f0f081881c00d1032004000141c00d0b008200c000d60103440b80f040001d000d40d50700c542c0040004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 142643399 1250 142642149 142642151
    0x906040308280209010f0212180301020f031003030e09010f030b1018020909010b0306060403080a1103180111010603030e060a1803051e0c010507060203060f09090d020d08010b030a020a020f01 84
    0x504038040b103801a4000f44c51071408500340140c500f5269001083c00141e82c001014220728141100708103540410744001c02030b800d0365081c4401502104850003d60044403626003c06025185280091814420128881c007584070100100300c008040b040c224140c03584141510140d5551442c1403500c1c0320181d009045584102000803040300c550b90080200180580b140400c40c0c2c0c981c0b0303954025101c02d0301e400d9041102003200300b001c107a0141c0900710083e414944005885a0900b00b0307465600041003100c611041038000e44210760304440140c2004007100003d01100d1303c0e588001d41044090b403000c07030103181c0c00505480d07402d108001c2041e940350440d0601d0415900c0382403196440d146085448411411210032401a0700c00040044070f0080c140d40c1d00d4a0302446a68000103500083c000381e0300407901c00c005554650b51000d4203803150031480000c0506407107024000f49003c00c2140130b80c05000001005100c441c3d0340030103c99001f5810100540e0b00c0b00811022840c10401c606c140100f5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 142644649 1250 142643399 142643461
    0x80304091d01202203060e07140a050105030403090f0308250f02120304050604030b060a06090305100209150313060b04060509040f02121c090f120b101505030a0c03050906040308 78
    0x10a00358888140c03c00d5880440d0400349d111240c2000d10f20366464403c0c4d1100d60440d0411180d0700c100015035106200f450f05840003030751050300305e1021340641c0084548010105403001400d040701354900e0700e65001400304c420315001d43c51704490110707900c102074094980005d2180d8910000c00c100d400411011700003ea8036a03480c1031140314100146c0b0032a208103e41170f40022202d10402d142c0081e05c0d044130180c0459040e8065000c000e501240c030807600301003140c0417a0100705c003c40c0510700c20311844139040c2402d10245080001c452481050510451800380103000a0700e07070040f13a503405035015034103044120042c00094140c1d44031880b004500d124213000d1140355081000c50b000e031080c154880035840ca44860007114504114090b203c541038000c3d01c02c0300454400c42449421401841d07031555a40c1d103910100c045c99104254078404103400005200b140002c500c502e0307100301c445250400c050f003800c00e5400d4540c00041c1000d420020200d01180d0040211403c403a25000042510200 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 142645899 1250 142644649 142644653
    0x71a07051e0d1505130203070903080f0a2c0402030604090c030c030b0708010e150f06040609031407060207060f0203090306160815060301090c030204080304091d01202203 75
    0x100d070744081e02d40000b1a00f04409258100c100500c1c01c0c0030f54000520303d6070341520301d4130800025000141980c081240c406000004101803000600c0946070030940286c0c4d0b407a01c0c6102400840e0002e0030f144420001d04225401100116080f40100b00c044901690b03940300c0300f0001d8050880c46101429206110b80c0020800c480b2480c2d100860b40301d0403a802055907107042c1911100c109105289114001c88001440700240d0541000104001031503c51a404c54001003903a40d04183c1040e000f00e20010070609c180a29007003510502990400102407040c10b1640003911000c281c82000d00b8050b40035100c1556500900076544041d00183c00c855681c5814140c0705a107080302d85203400407950a8011481000b014000901c0c243c2010f0030451540e440c2107115002489001d84c0e82040550034040400d001c2010b00082000746201d10000c44c118850f1036070410a03412900000c0e01517071401c00002d20b5845442070801080001c0c9500c03545401207056030040301c5091090400c21418a0840481 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 142647149 1250 142645899 142645957
    0x8010605100206130b0c070b04030e03010605030a0c05100c0501180b13020a0b0d061e0906062a060219020607091707050d03110604030e030d05071a0705 67
    0x41114421111240120341d500c1e4166240c410030b803600e4400d00c50160a81d070100d901d80700030a420003104007100345414070a454580d0042d000359001c030009407503101d451909140034020000540000c030050101c0b440c03541d4444510010b40e01c030380c5003d00401d1084d200e0b698041e4103410141608040240b04400d04900c4404106d000c1d0401200c48181c0440840c101000c507540200107d98060320101c1c046003040b04040710fa41000903400c0c12591242c2c00031031038800c0c0010202c10210100c1c60340d0100d0382001400800da41d285d803c81420001001005012441b60410112100841500c00c0e640c80080f07003880c001901c00e10114902c1154200c0c400c2c020194002171240c4641d0055550110040e11210800c0c5c00600d1507a540741203520106041c00300d46003030030801030385910905000c00886540c1781481c1c2004c2c01103d0640c0400c1004040700e410b402e061080340c5044c0f6152400310b2901c4c00b55921404603c8031038040c44402c0c01030a000910840c040c208641600320b20340d14441c0d0040008140718 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 142648399 1250 142647149 142647161
    0x11e18090f1a07090e190b0d03020105060901080a0c1707240e04020a050d0e030c06010308041d16051b100207050c0628090302180403181503090201020c09010801 71
    0x450b00e109810000f0f0203a482041c501042d90040c10345400c403a12003968200ca131031035204401d403006554260300d40382c5660740c01c402c541e803501c03980001c10f2a103850700810030712a50503441000103421001c04040061800088501907454143d07820000c6409403c0c40b80c0751000940081c01d03458820b25104828850348040014049100ea80e1014210000000c1c88260b000c0d412055022038400d110321341d80000700b500982e48070b52403081140d003044842c0c501e0038030f04035080e80306603840300d80010300740070601d402e01c400c400300814018049410b0410203401c3c0c0007a080003004d4010020040350941007000b003005003e2814500d48100d0390954112041c200c000d600c490000c55486c0315a240c00b4941e4201002034503441a000e40c102d05241400042c011780081c0c20344082010400c55003c0803006030350b03d034a0306086600310b214001c0c89107800d25001d00102c0051280f041000c54594003003225026688404400c40c4007480c1c0480d840115200503490b02641d80d0500c0d40c41803401b00081034011055205c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 142649649 1250 142648399 142648433
    0x20d050a050709210609050601030c0302030d02010203061f0507200307080105060906010302090612011203030c020105040f0320060c210c04050f0609041d06011e18090f 74
    0x810164860b01c80543d03080880b44a5060302a46010b4402c600882100d00c910666010340c3d00030039010900d0f80d0704c0d800d06000740c0044070341007880ea41c00c0c025800c04114003814003035540001c42c558248000000ca0140103800354143d4460f0031803584440604c104207540c401540300c016507401c8410407116a072030221655107079010307200e065800201900d0501925004002c0070b06112000e071500710044001c0c0d80515001034101c0c00030070200c0d6982e013140021343d0003000d26944100c4c92218915008095600050201c011607061409100201d40c0000c014021140e150801110401d915500b85620300440130899849001c1d000401801c072410000818005c203a00d51225010205081403010b0320f507054810072500c060610090207a42032a90751440902c1009244900341021040040c0035a80e40c110981d0344113100821700d1010203070800c100340c09031440c00c40328065284513030116028203070240320b441040e000070404089144616401313240c0d1139801480c102d82c5100941480d4103180c070b4036404 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 142650899 1250 142649649 142649651
    0x1b0106050f0301110f03130b01081506090c09092203120c1403010b0c0709090f140606010e09040c0e0403110d08060a090b13021c0e010203040507230301020d050a 71
    0x80c0780180c0c50107101d50110350305103014050411000584680381900000c1c12460068aa0300e00040800c4400c2c0a284c020104840241314040010604640060000d01200c0c01801e8040c1804014024030042c0c1e1041c1d030341a00c41c92104c0d520184401c1548030500d00c018070307050309600302c10207055100810501c0c09034201d50074030000b07601000c21541560783c50324540140c04140300500020790480020401142c003402111281502c81450004072544010200e540d20601d600030420030040358520300b40c00c0200005010b540c0341080010780701215103c0160f114000020000d410005417103003280183c00e016507076000900d843c0c94040e10820158010030b556104040080c20710700e226007070750740c4030b444068142100c1c2441c0c102201c014024003560554400941005a10540d00510241a0501c07611146084c08800001010101e80d50030780c403003c207640104200804907800141000484d250604a131000044107482c0281040101c003003150716500014490300c503010b080d04440e000d9101040 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 142652149 1250 142650899 142650919
    0x12050402042018030a0209061903051c0f030501060206130f05150f163507180f1d0709080616030b0f011416140106060315030f02060f1b010605 63
    0x10130035a4682825000a501080d4800001c100d814200b01503403c0b80050b150081d0842d450b0b41d036542c2000d011440c4060481500b04006d2103d84d840198001c1861107410100015410802c00039210f0100924140c1440403408104003000003135242480c00d01d4005046d03d00c0e034168081c95034404042520f1520a6a01100200314803403038200900b40c50780d0054a500081061800f085070140700d0b100085d5102240c0c2e0490034410101c00180d0341c1c45118244d40d0201d0300f40242c00c03660321403400e541000440280500c03080c068042c9100b1003a140581204161100b581c0c0c80101300c1e42154203400000240c00341d0340a20005144e00c032026000380001d0b45060006422140034000741b601071f401c04500103940701c44203081046e050001441c407041001e800c40d4141886844828200c000800314203035680d9102e808203c2c40b40d0522813180b0000c14001c419a200703165444000080d800410013078030400c030014101e103103a183c110880388000190030281d100d20564801c0a07000b0301c1c603445154001d0640304 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 142653399 1250 142652149 142652197
    0x10501030615020601030b13050d020c04230c0d0e0a0c09060b0304021807140c0a05060108010912110a0605040f031d0a1e090e100c0f120504020420 65
    0x5860502c20700ca40c01425240c0ca0f5899280d24518080d01c1082c000400b6072082c000304806015004400c40070b0303001005044801c2c0180400c9880031074001d100000c010f80034480071982c07225071039000303880e8001721900d0f090004440e80c01030101ca807032441107115144d0703040200421441c103001103d04049040004590b5800d100d0042d20003103800961188000012600c501c034019011a002055807510b0b01035800e0440c10f01d160390344100c0040080f84d121541d020200700c0304000b103501414541000707002138081551042e00c0c040201940d04240010b0406039645030304200208072502e0342040040c040343c2041d0070314004110000e00142c00098003420074010401c6139640424415102814a10b191450700c100c40500355112152200e80c07ca6880e800148924607008100281d0044800781c5810303020120403104035110002c40c481030004d48400e140c016078010041841e41480b2010114450fa00d03480003800030b24030040c207030f081c0300d08491480c070104035070001611516018100000d0b009510b1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 142654649 1250 142653399 142653419
    0xf1706060607020607060915092904020d1e0602071104050c04090b0409120e030d180311060c010c09140414010312180914060d05070501050a0905090c030105010306 72
    0xc86119801000400075140181085002807084600a40001491110f242e541e410389000d5134100c52a9143c0351403038001880300301032603c84500d42d00000d2907003d60300c0b8900d201c522507000b480070b8481c1005809003802e00c070311075500000440004500f42d0700b03004070381741c0f0000035040507038151015030003082d50b030815040900c25175000300f0700c0c403c5642c1843d1601210001400c401042c0c02c0e000b940f036071410700014100c02644070f40443d6070748603903054a0030032092516200305160040104034088858051426030381281da41070341d8005c1800c151a12956001c0303615403282600700702180d803a1a140c17499185d8004a140f090f21200580307090010003030070420003038508071111000006000c04c01080001d41404421028070994181110050216045422043c1d843d80c0a02d401c1030320f40300c04450080c051ba4802d54810300c02c0b910503680c003440d900d0342d5544031045c1c051035050150008440750a1400750001400801c0010b001381e0051809115426140d0428410180400c0c200b003004101982c003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 142655899 1250 142654649 142654651
    0x3060a0302040c1101050f0a0509070b09010c06140403020d0f030e1905070b0408011b030c080403030c0203090d150608030703021b040219030207050c0f0f01120f060f1706 75
    0x402084821400d05580810000b055000c2c005001c1c411102074280040c4020b0042500c80e80b04050304041074034114480405684000304a45016002440140300520894080c0c480c002c0080c038000102e40803030324240d00108000204410032200500801042550000e42e00030240f40e107645031450303000d8040040d41035078100b440f8481d442c1c01051524a03540c40758680d2251450044040f28552656016840050b42c02900580c0d01c1d65141e03c14103100c259103610194000065213001c01c0200c3c11840300a001c80d0014000a01301a26003ca1a071028801c000340c0e10050307030003060300c01544554038155a4244c469110f040f0020b0034154006528403001c41900c0c8496015000342075641d01851243c9070003034078414481c0d8050b90a00c46011020180b260004407800a0f40b40160b40d65010308203903280c1402e10000c10321841e1140c8490700541c0342c41e014408103031007e00b4030417074540e0700403588009441207125101d0201d242807800070b600140c14007941d088481119100c108030380d4490f03c050315140 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 142657149 1250 142655899 142655911
    0xf140106150918110a090608010b16020918010203070e21060f070507060609020414040e03041a09040e0c090a0c0f0c1104060b090a0f1217040812070c0b03 68
    0x491104108840300c08081d0100301c0039400f0006a200700c40307211a5001c1c4c201084a80000d2900841444442d03040a41a409050503480160074280200c1c20b00ca420800e10100901400c0b2010104c0d6440c2e01d290342e6035496244c0c2c030009540701d28000d08000d12950003071038511b1042502d0f00e0021080840d418000300e0400500c005006143d507022203036004444040c02d070004101c410860503002c56010300c00c007005400c0d00000541d40318a48910321068100200b074107072080d4500040c5090703846001080340d0486401da51030401c0f5404160f5001c000740074400460390440c3c1007036901d2007002004a260411080215105182529148e503030408a410241c003020101e691a51018800303405120b03402c01c803d1141004204484203800414260303206640085030f4048049102d80b06441d1413542d00000e8000700c00110072003450008030756514401c00802610943c0b02401d031920b0042c801c000c407006081c0e01801c541d014140741c2d40c1843c80c0ea01000381921490408080410180140380c22203000c0c0c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 142658399 1250 142657149 142657157
    0x9011410020f070303080a0b0418020108100504020d140705070b010509040c121101021c08010e0a021908010503060a021204030e030f120301140409050a0b06030a0f14010615 76
    0x48140028003080c0300ca40c003052400e41c03042c184000400a030030007003000030358441d550341c4209082202c551002d440c4510780d480c0c40780b8108282445000a106c2c040340403180c0900e084103080d10340d0f00d028651210690441070b0001c0c0001140c1c0c440044075000b9003080d6180c3c0f80506a81e649031007003166140034100c401008000e1f24801003041c0d00d060410243c1040c0a40700940442e1b40e61010581c0d1b10588010455000381c080514140642e010312809052011605200901d40e03d01040200390755014043d440389254400040340410b00294152100300210b04140c40701704203105000b4040c2e180c248a030602c20b1082c040064035604150080c0c0c1e41d0f8072041104040a600c1d1513500340c07040210200166014420075000701c541400070002007a508182041d000d0741c07035040c090b100d0000802038848a005900340381a40c000100700140c1044002e801500c100c880d41c5130174000038205801402c004d050201114280c8040c030804d80d00c45115050408000c1202c0e0303565504469921119030700da20082 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 142659649 1250 142658399 142658429
    0x1060e0c03190f0b120a0b09071511010f0212010f050d020f06070609080316020715020601170304030506041104140402031b0a050a1d09060610050a0e03011e0b0901 72
    0x4100b9034020103003000700000d001c11005800310110b00c00030560b20b141c0340384e80d1000003040e06000014070a01e4104d5200c1003e00340e41e0f403e0883e601503000e8140c402d58200240505002a1000c0a51151a5404100000350341d40d01c000110030150350002e0149070705441098400103210700d0010000415168042c00302940d0141c070408000032134002070403c4d50001d440300e80035000142850b008602c9000c80c0900101c20420550b0001e05e13002e43d41e001804221821034440203410340002d0840d04484550300c02001c0f070f00504844034258002c0d41e00040c000e101355400d000421404c400c1c1082d809105541c01c115041740400310300754000040c0d030043d4254000104403c4a055009640340031500080d2171152190f6488000c500d17115580d903c44545200c03d2200191115414043c03c0d070010b0700d101c0203210506204002174015804a2100d5051040c0016221201805100400c6901100400800c08107181c2280c200429a511410000161800d003001c141ca00d04001c1e0305050324800c20003d20343c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 142660899 1250 142659649 142659691
    0x3120318021005090a08010510060507080417190501020301090c05070c050613080a0807050c010507170318030c07030201120903020606042304030507030e040903050313061d01060e0c03 81
    0x1c600d03629410001007050811030002d845e251061000014002e03071000144519104c84080c1d261400340d003121040040420421700030500303c000740c03400d6514070704041034880c0c20090781520304058101280302e0300f00e40b0100c0505110041d400b542c1220f010140c00d0092580d920b000300d802e03120b00140104206a411f10500c27440c1480030251070000c401c0d021106d00d8a0f11594060300c6c01501100c101d5880380b0001d09101040810310a803107400f2801c2c05d01d9410400c0641e41e0122450000b840c3c0503805c01c0c0800000d00501c54041441c0c92038200e20142c035590320340c80507842d0301d0300c1c550b00007a4003040c0b0641c0e400c0b0000c40d0b02e11446110f950513074040c00f41e03500e501c0e041201800b0126520141c003404000f03409140403800742d10300d0050780b00e6111a55109214075019200c038068495442c411031400060b00d010a8022044a900c11881c10311012240000d01c0c0040041c4103940f00e40c0d507038000c040007490149030305500030703001d9680101e164031555844040f0000e09100440703021505549020b10140 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 142662149 1250 142660899 142660909
    0x10c08130b0a0b040216111804060216060203150a270509100606080a050603060106080711150106050901021204050a0b070c0302040906270b060f011403100312031802 73
    0x10700b190761000c0c04510361140200040698001c00d210b0401784008021201c20440141515940c8400644001d003a085400d408800340310001000648069000900352a81090400044103070326844401103440e4240802152038900009524500030004d40ea400301d540070074409050030800f10355810100d41c1485104050145c807028000070700c280b048600a8030850098041c42020b030045030380d0051540b40a4560100340d0318060481d5010740c0001005204c036540c04008141c0c021500e0070004201414001c13054500160a103030a100c3c46030560011480799403040042002c40426400c8031080d01d03480310307100458400e92080d20b51000c4180f004201454401010b8003c0b50300903848602110b6407a00403d00f500e0701e81508480c01c69940c40c150050141e80c45000316020f61031808816404902d54824041d940060007891050341000c00d0601c46a102d0245003c100300c141020b079859040071021006030034502d01085610b181c0b103460780c3c0035181c801d110300741c181010031050451200c50764003400 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 142663399 1250 142662149 142662151
    0xb0f0603120a0c0807061422030c030c210818070e13080c010f0b1305040203100506060403060218040516050409020a09210b01050f011d06071703040302010c08130b 72
    0x100c28130310601c000c0c4003041291103100204203400301d501e0304910740141d0030f29106144400403d035844c104020035011942c003e000c84c40740d81d854100700d501d035980c41c01c00c41d003880b5070308258101404805a4038440c191784100c506000da40f40c80082001030341e250900589802c858040c1c0c009414200000942d41c00c041015030101e140680c41c41403428070950820307829220b121494842041d242da0401042d41081414500c0000300d2640030005030400e0741c0000d403a2120841200c0c8065200c0c40030401a6542d8000c40d401140c2c0900d00715543c098421101220b405100c0c000e901c201d2034107000a80030b05695080d800e1911055032054941401e00c0c3c030540c029001941201c04001c4c2421022600d0301081e0300951503400381d4010761350070f20120b1400da000ca04050b0042c0c0d000c1c0210b48076400040e6000310f910841170250401c025100d00c03402022070b40900403040c021b801168104040307900f90401000442c0200e0081c0e00a0040003002c85047c0c84100c02945d2403925580300301d120002003030034402c0403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 142664649 1250 142663399 142663403
    0x3020c060f07031119090f03050d140c0f0a060b0406030b0408030405010b0a0e1609140f0f1c0c06020705011205130503040b040f08010606090506030403020304120b0f0603120a0c 78
    0xd883c4c4145500d290b000d801421031010300c64081e50407004000d41000d204002001600b84200a0324255507410b034031004003040c0003041c0308080d4880342c0515a65010303141c40e510150112521128032440c00c50380c1d040c00d404140c56030303450309540049500b050700410b030940b9040328a08520b80c450342c0d2410040e5000900c00c0c0d4180d5640c41001c012030381c070480c203200207000d11120400103050200310130501e00c02c045600300c14084c0c0740d4002c00c8511000c004040b01800101d4406240120b00c01c04540c500601c2c000c250f03844211a10030071a01260101c00c546617078000c241000c1980d450340010307a981c2c0d03024001c090102c0c8801d103915000c60125048954031030200c80c40d2400454442c0d40d02440d5400c1070300120110500460b0512200381070010190081c11280d00911030145003190190441089004090040400100141c02d150080044030010640143d03100030810513420b04514500050720804c56070110030000c503c03185000500314051154000a0901d1702628a200340e40e80c4d8129101 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 142665899 1250 142664649 142664651
    0x1a031605150901020c090408040815070e010306050a1a0d110a170f0a0b0409020a060806040e0a170304080417100b04050f06040b0a091404030212030c0315060d0c020a03030c03020c060f0703 83
    0xc040aca00006200040e0300312040404002c0c0d6003001c14001d040c1c1000c00c6501410113103020380402007556020442c40c21030341e86030003111a280200482520510803503a8011826081000b2000c510798508014006c07416150b981c05070304106032201402525055511209509011000c10919020303940311980c4144010000070f040412580400c41600c03566109101141090301040034504090180909480b0290041e014981c8141c1c4d0302a4110746d004030112010502000040820610380200c8020b00094019444003a840c02140341d921411500f11102490510101103501e0030903008481c010b0a552240c00f65a0342d0f54414040106107140000c0e610040d0100001604a0103200f080501d800350b40c607140d81841e050030068508100840c06a003510810420819803024070000c0c0e03030b08100c0e1010060714100ca16000142d4038081d4030801d042552a0040c4082c0241c0c0029107a14040e102e03880034042001c000009500303c0c003401c40c0c84c122640001c40090352600b81e1200c4d40f0ba1142550038 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 142667149 1250 142665899 142665907
    0xd060e090a0303061205060f04050a0f1b0b04060c02040f1e1b0c0f1203060302060d0504120206010b0901030e0102040f0b0414030610091a031605150901020c090408 72
    0x1800000500556508540d80c0100d1481000c0c0359040c080d4401403c3d109620103034444c01a5110380d81c4d00d10040040a0454103070011804001c400d02c00c120310950446442d500d03000440c18440c0c4254070f0401d42108805006000080d1042c0c920181c400b111032546074115080040e8003448050240c603241443c01a0380e50805080c11100f0150300c110782149118001018052910100c81c18038065942005000c4d000b052100050344200e8884040c1e68010b011818810006106402030201600300035400040450340c2c01405145600052049019000010543c0905602680c07101c50a00034609001c200f0850320495500035007020403688117840c00113140a82d00c00c1d032590080c8041d00051210480040e007000701208444504040410850240c00c0c2d9003440030318240540014403445441c03548402d22540c0345600b14034901850600030302912102c0b105201411154251400750314031501e80301145c04003602c4803106a6041c4041030b00200355005101e0108041580024811190040204 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 142668399 1250 142667149 142667159
    0xb07050c100608160902040b032703071208150f1203040b0403110a0b0412060903020f01050916080f250b0c03030609010509040c0308030a020f03010e04020120060604020d06 76
    0x1c45490000c0015402a1007401145041134400c0086907100d402854014070050240c17840c07100c112a00110050b04500c0440344411501c403200c50510912003180c00041001d005105030035811002d0004a90707102820395560a00b0111035a2207441400d070020207060211071203042031495401410200e0701180d090542d6039090036103031342c4141c00448020361121900341c00e9043c03150002002e031192880a90500f810b000840740710203040c41000d0800340d201d2080c0e2042c54001d0180d40c0480d49920001c3c082444e0000c04140d03600b030940110580c01d5071004c400100b5513804a41405000c1c500c5011300b4040c807070100c0e09004494102c1d4040d202c0c00c2c007603000080c86040c150051521b020b0680141d0f48903d009001c11030f0f1004140c1c8154003950300f040c108000504030010b1102541c5d80f1100140e00ca8803070ba110a4002e004814030301c0404140003001140300e4425929051007103200740d0701c806004480c00403a0240c41c154400e41000b6602076070206031145020f030042d1001c0308c0103040000703031141e941c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 142669649 1250 142668399 142668401
    0x103020c0703111816050f1921090503180a0b03090a1106162402040905091b011e18031a0a15050103090c05040e030c0c030a0b07050c10 60
    0x42d80100c0d400400300345199683d0a1800c00000503410b000c404005505d403220540c241d88001807190400c00100040303c2a4100007602a10000c1040e0409044000706a15018124032210302021644122140c40d0740e000303d034540030360742c01d0b254000c010f182007401d22014500c0b00d0300710601050788107503d42c001140290103280a18403038110a00109880c0040d810106c0c003030159002c405015140801003046802401195100390036481440345200c81001c40015208920a00f07005e030196000240c002015141600010300071040e030000c3e500700c41c4040010310540d50480c907440b03011a240d9079207070ba07401c0700120320581810054241340a100c0510000e48180035a0742d007044038100700c210032241d480b40300300206c20303804082d0040401541540c441091006072552003003d0400d501c034500d010810100019200003050050018048540c003101825180d400003840b00820b8130030301042c60014500010b00d103090700e412140d4001c02e600c0c0c907602200e555020b008503481c14407521112000380201d03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 142670899 1250 142669649 142669663
    0xb03040f0f0b040c05010825020f06010602070905090d0806120102040302060f300118150b04060f0905060a0c0f020d03081b040305060c0913090f1a07021203060103020c 74
    0x102d041911000c0c42c10b844c00440d08542600071504100c031020030840600e5031007010b02c00901360713207034201000000810100c0c5016280112162940951800000d250342c0000c2e00350241c0703480b02c005003e55901c0c94103482d070b10306001e0811400512000040b4403c0d040c024103a4003524a40000945000c2e10b03030300440e00e0b50b4410003c0b03e501200002d10b2440c03100080310700b80c0480d813007a60481c0000200b0b1405902c4e4031418083c0302d6100706500012000d907036a9a00110002040b40c0c1070040701a9104115010303500a440341c80c000c0f4610b04140d0b09458814200c400c283e41c001007a03076051003c03203041203940546030001140c2940e0000c04640150307032860800c4c00072034865501d81c2070510349203030704d1084a082c0140a5400040a00091000a4000c2440d5a1001a500350181c42e05090000a51500b1214401e44c900603c1c0c182030005018440d909402c84c1d03400303544600082001e100400110010071100100142c00404150312640c2d568002950410014540075040401c111003040c2480b00b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 142672149 1250 142670899 142670903
    0x1811012703110102010b0108040204020904061e06090602190b0c0d022710080a2003040c08010b01050403050c0405062101050a140f040b06180f1803040b040b03040f0f 73
    0x1032030400c00030000e1a03000c04110740da007031000307204d0303003003440000307000001b000d0002442a40c010690030b10b2910b40b68481070084c2903040c4d44400008505500d418551168050740f80002c40464010540600004031001004a800c4200a4042190700e9040041c2c8020340750b00c0341d03d4000c10907500e4102807030018007600d00060b8481414a0340c0300f40e0721852490048003440c0601c8a04101d440301342d40003101c1c0c1e40d00510880e0041594844004901d50206041400b001407240c0441400280900000c01106a81050000700040d04000f0015206030280e444014843d44c011100074115042540105811070700c0a046440d0040003140451201641c4580d080103581d954010022024000c1c068151804200440701d8154200051101c1d200e0100500242031003852501040e004c0e00c07184010021054940003245007400c000c2011a000301c01614901c03071110004401c00042d60022044400b15a14111018600381c900004011980c000030800d40c0c002044042d130340d003c00c108811141040f4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 142673399 1250 142672149 142672217
    0x2040f0311100e0a030b090c03030a0f0207050609060a0315091a090a050402060a080714040303030501031b08190204020c060c1b011406011b0210051b01181101 70
    0x2103803078091000e41d82044030900e00300103401c950340788151684003868040e02e030018003801682d0360301d440075450981c00c880403540520000440c40740c400d9003c074800d4820016a8291071090780d0351020401700e030040041c00c0368400300810550400d18001e83c40f50345210450241050380640c0d80074840304070341074203121200d101d64011a07082d00c3c6c81e0000c00d0b164041d043c480c04002074100b42d00400c40c07a005108c80c031414130002c4004036150307500820b214070203002082c0b02c01c0d980369120701d002009010284000c90720483c040e40580070712841d44264000b52440758005040c0a4542c0003c0300d52440301440070703038019608000b108108501404400e100311300080141c0d550f09494604108124100302d0f2400051345020b0154941941814106406c442c1c24070f40250b00703074440c800c0b841c084103610300002c3d40301180c0324041e080180c005d80170300b0b100031a00980f14224126011101d00f40d40400c4035240c0049486034421000402c01404111000c00603d85440d850100900079072058000046411400b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 142674649 1250 142673399 142673423
    0xa0b090c040501180504023706050306010f200604050304080c12120a0306090207060902010e01091a0714030a0210110a0c0b0a020903121305010e091303020102040f03 73
    0x2001040084028056041d1010040c0c1d43c0b60402142e16039204541107080d950b01e407000f0505664442e030401d90b038503d05641400035400018207030907014129008402d50251289000102240a0f200792803241d03906840b0418003a02004048540d03c4260b4134004d840c02c6802d844000301c1c08100141072045210740004c1d80e446090560091074080034051961103102180707880780000d0408580d603c0700100703103c5815140d00500e0003c0d03014100a802081401c0d1011440e58103002d03550700007101543c000e80703500782e064007288011108043e00d40a012025646c3d01d89101100c00d524000300132403405045654080b07111064400d00719803140742014010b90240c14150750300c6400c0d01c00e001d5415031202e103692809418050213801103d1041c405000500d5101c00501007006540403229003c1004042c2c4011810310301d105002500249101c09200100c8030b40070845501822401f121504000d100b0100c41e034030003247c1d00d072407403050404504554080c88005000002100d624000c0c521070340309200b00c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 142675899 1250 142674649 142674661
    0x40801090305120f07051206011214160302040521010902060a020a1104091a0603150108010204030c0503150402090903090a0b03010305010f06060e0607060b0904060506031515010e010e030a0b 84
    0x42d000f8003a1040d8150441a401d11035015045821a01c1c40091410050f1071950f841c03006031240101c08a4981402c0c0c01d04118048d4246a400c0e01c80c420b2400d0b0849010040307594008500304e001d140141900180c088428511070303203030f4242c0c0300300d911000c80001c00d07400030a501103207541d04540101005a402144214100001910f15a00e004402e43c0e040040c0381e000c1d110103c80b80d120740c20000c0040800000b0921a8500340041410f2041550410a00396520100d560003540300c0c6c402075130715091030f0343c0201c0d55142c04140c048441610120400ca10380300c64080210819014041070843c1c0720810120441d0b8503104c400400801001c000c1544961550078680c0c2951005407003c81485d19000003480420b810189540360100b0a0325901e4898903903185c802e00405484625943c848000b00401040001e00c0e003002c2d100d50804c0d0b00340e900b4025084ca44242490055809455000b80b00d2420056940f1540d00b6001034001490700389011841380c400309040505001c01a600442d100e810082 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 142677149 1250 142675899 142675927
    0x122901030213050f150303090901030503180f10050a050c06010f0e07020307030906050306010909020d1d030705030a03020f0d0c110d0f090302040203070e100302040501020c040203060f0d08040801090305 89
    0x1400b480440014001c40c502800c01c4120784200070652006101d04400c0489962001c20568001d12406401e050948d616801d0280e0342c1e410210701d80904581c01403d00302d1509210074201a0b10b030000e010304025000fa00c038140d406400c942c10202c200071081c425003140e00c1041212a00a25410910850b01428200c000d145408014022000d5600c03c21012000940c820040822203142c3c0c130f000c035140d84070400122032160550b403241c032450b40045010810984250b0145a00d005940d03086600e1641c0041c00c03d80364010504050302540080c0048145c1b03502a8000b000301c90304814005140680304c807135450486960352003541c00030f00c103002d01214040081295425a415038241905084d4001600a190700c000b8000280240e130044003140680e4003404102a980400504010520001d40c40040003500144100c43c0140b26500810009060510880e801810040e00140038200e0f040c0a01141041200080b00d50107010040084e0098080c42213208a500c00c2c0e4609030380d6160800828 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 142678399 1250 142677149 142677169
    0x120a06060c02091315061e0f1d0a0b0907020a021302040f0603090f170a0212090105030a0e07030c230901060f0f14030a05180f03041229010302 63
    0x482030040034030103840543d9034001032582c803a00e050348154070700d040d918045095114a0010400c200e00f059004140c1c91900ca04043c44e060f08083e102c4031081c0c1e2040030740134601903441801901d01c81c259000500c4640081a5548006118808168030303062101146255104984260068025504000852824405440c81720f00c41d000150701342801e200a00c07003109001e116100c00d1550325807900c000c0150b0003074008401904501d41c00c0c0c00b00841054030440d5480008020014080c9205501004500310f003911107040b4181d442c2c900315983ca01c1c1c0840181a1006003012910843d6000000150041c01c07640203000080c840e40d150b8109110381048e04104414007601c112101001400b00c1ca9114502c1a00e0a2880c0344c58914615804806d85942020403002172681800004200305a24150055030180341c1d1080200c500303080704141c4c1522000c084494034226001008100244080402d030008503600601c2d0740c240480040b030809401e0380585001500c4206007200400540ca0107904207 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 142679649 1250 142678399 142678409
    0x21603080a1e08071b02060c07051207080a020111030c010501140f040912050304210203032530060305010914060c09060d140403020f16030f080a0e06120a06 69
    0x2480210201c0c070010f415810014115400c000301c60200343d042d2010350b8802160760790090301b00341d80d0f0b100c10180d080c0c4480183c001c2030b0003a000c9007400703281c9000010f0000b00325a440c50103003030103040c154011148121943e44044c80b0b403000740202402d0704001c0c0321b44c6008042500403a4140f9050300c080c0105954150f0071588102d2900703a511000c07410a41c428425080c2c5890156501e40c0c6a2404142d228842c2c0c0d8004803000e03450014045240c1c0010056015105a5420041980300e51440041144510030420b000030084901c1141203402220303c441c404111000f01c81c001d0309400a004100d64150b44141c940740e4542c4400824884031811040600840b00050119481d1540d0005454440c659041c0d000d1030000510b26142e120a502c4403001c0703100b84203078405074203003428001d40d01e0b0099032035a102401088920006000303805040c10440790301a94200000e8042c0c0ca40d16000c0d0090440715081c444800003080c5550b1f03d003c0100301d0260680620807060a18202e06001c691142d044 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 142680899 1250 142679649 142679687
    0xc15020703091203090305190606090504150b211c09050a060e0402040f090504060608031602010e040e06070503070905060306010c0f020a170a03170403080610021603080a 75
    0x36000c04a40c0c482809015241d01c0385000308042e030315150498040700c2550024086000d2044201c1c43c403a480b1a1820ba02e902902c000e00105031603085800c200c40050720700516143c10000343d043c9071600743e0030905034004014100701030782d00c09150030700352107250450a000c181c005114904400c0401c01241480703000615140c0c4106003044041280d42c46c45000c0d400c01d2100d0b41e100111140d849404580c0500f80c4901c110054940c0c901049015003c25a0100d0b0294240003010a40c4c000000a55a04810141d400320300143c0b00e03001515080c03101d2020795000354641da90103010a80070050a4003520050b80c0741c50352441c0c401001800e551040d00001c1c41844c1c100103100f1030386e034440300c28800b09801c80320403c3c209a40d48005105032603d540003104070000072494040d0341d000490301b9031100e4080d40350030f081502e201c8892a00328000325002808240404c020030205d0801500a0f09400220300445d100034000340c0c4110742c01d0340d0b10b5104441c0f854000a144034410350100154401ca521841 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 142682149 1250 142680899 142680907
    0xf06111c02030106080118110d0506040c0806010e0120010501141c0c090f0e100e01060501020a150e0a1a060109080d020615030a020d08041a0309030306040902060d0c0c1502 76
    0x1340186030000c103200e0555005600703843c090061a0640c4600b01c036502e4050501c0d5150740c8032042d04007400041b158903100d01d1412452143c03050240000314442c04052f0b641402c180c043c80b006443c0f49007290100c50340201c001382c000300b540398244034860207003940410340d10742c3c6950402008010180c03440101c0300e41c480d000c2554006410840c4501c140c0d400400c020885c215122100c00003003143c074400841920401028100020310795001c2c013540c800c500c00030b1008548482c01603a482011800040980349150019181c004c080da20105660081c071064800c5034045454856010102c41c0340414250b42207803e00c00d8035a000902107009110400103070504400b00103001e500c42030001e001d0807605103140c171000e07aa036a051016168241d8010030085581199041244150304030380910102c20807081080d40748240c1074010303244a808880011861540c030f55090001070803c21504a0f00150280900c1c0c43c07903209400f070740070a03045c3e5551340360740c01d190390074250244400b0719a103c1d52184108 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 142683399 1250 142682149 142682159
    0x41a070f03140903150a0f0c05160609080a05120703050906060108150a0303030e06090304230f09130627032d080f1501050403030305040f06111c020301 67
    0x500a000c0c039030181803080e90150000440c0395076200e5442e2103035160148103103c1100848031403074603025201c0c1480402602c040c8081c0281250306141d000c0700480c00a00040340110b002c4150355109510520020512506955640c2040e82155802c0c001064020a1114160345828941c40c0d11821502d02403000b03040045880da03d4000203030209040040c100b000602c00c0302a4403140100c520302801ca43c060316907030b00303000300203140085112200c0e000d4440031882e5120000282d606484803e05048880e4001c6007c0c11402c0703001c0b010068000082036610749180c0d40c0c00000c2486454411280316909503a45059000c81d4905002d10480c1d41d000004070036030741c581100b24030240d50300d03090009509080d058000048d4444c2d404480040c0907910001d05c1c00c3d540148680d02814200e01e802c03a060311610321214000305207000081c0043d40911040020034841e0f0400e035081800f400070140d069490752a080280c45446540741c8030a070000a40c8281042c440c00100f840c1c04640004500710350601d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 142684649 1250 142683399 142683413
    0x5030103030309050721050c0f010206010e071b080714070e010b07020d0f1406010e010605120c07022d12150603030c03030f060114070c0b030a020c12041a07 69
    0x1030001904043c0d41e084a0800c004041191802030410101400030000e5007181d01c1c00503c1c1d990f20115081c2c012501e400480b03042c01d402603c40c0c00c405170040c0c100e907800d00c0500780d81100b0050541c4c042000c446948165a034008458008482c0200356165840b01c041c1030091440360b038810001c905501c501410041c0c04000c50740c15041d41d01540f021036071500b460000400150070b400e0007400a481d81e4502c482000031050f4103a1a400380a000d03165241c0c1d841402009009003481410701183c2d04100200c00c04140c0c129140d40700c5e076060402820401c15801003046c010b80018030304c01816405000340182074080c0ea4200000c0c40c1140c021400303042264003280c8600d40d10000002611240c004288956000c2c42515051702131401140d8591421025644600c90151250382c0072683e81c0e0404400714200e00122680c10780c0080c803181000d80f1300420310050f1b61009201c502215801d0004221401c820b2201c030113000c15101d10345480380d05080e0390010900c50614103503505da03c1005032000003058 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 142685899 1250 142684649 142684651
    0x6120103050d11010b0916091e0e1f031104020408070e09060f0415090606121a09010905071401090506071b05040b03210d1104050406090204150f030f06121a0912090a0b1606110a0503 80
    0x1010537040040c800400c0401e01a01460300032200c14001c00b0030101c2c1d10a404130102d8410790004045800b1a154071005580150742500d0280481d076900070307410f04076081900024800391241e000081c119540d958032142c0340b43c0745032044500000f84480020b81d80440da1040c2e4000310100000c0203e030900d42d51b031541d904c18510451201c81138220031070b8816801118001c0040002420340355a0b82094a00170941a0103800100344650160b4404070303184c203240c803801203e581c005d00180710a41074010a0706400d0145a1504031028007000350101010803405094043c002207424107440c2c5042c05c04000a07900d0701c1d0070043c50b50703205000c104082550380003260f12011081c20030f1107039580b2250b03049000c1c01001c51095600703030400750001242d503d41000441e0f03860140303100031036880c3c91040c65003851000f520000c0d4254080c00010124440702c0b00106100400140b440503020f03950340c200c107032a0308218203140081d04e01010403814401c02d409180c15030040d515100d441c240103640054000d001c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 142687149 1250 142685899 142685903
    0x5040c0e030d03111c06050402070c06110a030c0206090f04180203010e031603050c0f010216050d03050412050c0a021201090b0906040305030106050906120103050d11010b0916091e0e1f03 82
    0x11403c145c44040502c20341c0200d0140c20041c009540d02c41d42410300300707000c030700c148940d2000811b0109040300d0401c022404001559060340c411030580c0f1541c007004542e40050f07080642c02078600d01c4078182c603540c0d441402050020080c207031100a03000d00401d03084401042142c40d07240c00c104100c161386507a6195007041558141001358891b94030000052500d900103081d0ba015620000300c0780420104280d4205c01c1a101c1e038100d075a02041c08400320103540007501c000b4a5260703810344480041c0d0084001e020000c1038079003101c1403840581c001840e290f040102c0d14203541d6440c1c1c03602003800402c140c03c503808103d9500815403800c190f03400504c1840b0512425003000800300305020300b82e43e0442114017032000d2404110b02542c40c0e0614a032178140541320f510100c0d460303501070700c54050180141ca009620060020b925503403201007807005403030308100440030800300690100e011414076035642508a40881a00e00c01400c2c600d40c905030080c050b0685459220f400c91004154001c601c0c40c00c1500c0e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 142688399 1250 142687149 142687177
    0x61d010305070207080718051f090209010203310e0906040605060d0203010c0f0809011116021f0c063b03040b0c01200712031505040c0e030d0311 64
    0x70b910108201d0902c8190f0308075904500800b8800078038203080400c00c0d8030000b0000f904200310b07225070400d01c625001601d00340c4040b000c200c4007000b2098090313024103c40c03070301030051707a1408002c0000340300031030f00b4501c500c22001400003030003c02000c0c4104030b07401b81c4045032002e2038034140b2000c11991003000030b00081c500c4c1d403520005540c50301c84410084a45a01030002d01444181c114042c2c1043c1c140790b440000500010001501d1840500a040c52900501b40701d0744ad00b0020091f100c100340701180b0a03038010100c900c200240c00001550321003011103d60b591400c0300c000c0e10f056001d550a4140501c041c080d83d122404072009414000052400c1c041006c481c1ca8072142025425230040d42d00c00e146503000405c48410030036041d00138124035a5000340e03941c106109482c0502480c054200b0280c080b20396070070981c4089029074803000540b007500c030241e040e641d030b200c001400340c5480020301400103c20280d6010a41802c002c1150041c102d0b040c28840c420103024102c0c480d00400c02004a12 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 142689649 1250 142688399 142688401
    0x90b0115051b03030717061302031b120a06051f0e030a1b05010801080a0503090111010f06090209010806030111091306031e330e01020c0a0c0807061d010305 69
    0x114024030031030305801150402d4411800d03103841c00b29100c2c1c0046030f00001099240310440313802d07811000c00510034031004180d0f000c031020f071000020003500004c0c8411202e110b040c4041555000c801c01030000745549041c0c240321480c2c014066070a688403540218011034045500c3da004400d048515802a90f55107011200c014030100080d1030311508444c080e15074a2a49030b03244610f405801c54006a03842a26440101e9903900d810b29074408014001404039042070090340841d41c418424641c40104400010504c541c130141403034100c6c0c1213a441005402d80c000303598901560800c0085130707c090300301c000b0080c1c8603881d01a011035210b01c90390f040c803c8103246180c0c482c000c06644400051b42d0000c500b0081e0043c90042c5030044065030100303031502d01c080d945082c068100903a80d2001031485049081048002c1300c21407020b070245d982c0849807035400303004006207030030204a400e40c0326000d00c105013042850140440e0800459400c0b5400300700400304030900b00c40d00140700070070420b0b0a20340040e803 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 142690899 1250 142689649 142689689
    0xc010e0303090a0f090b1e04050601050c030c010b01030b0105070f03050a11010504120201051003030c030c020402270f03070f0506090d1403030405010b040e0a0312020f07050304080105010504090b01 87
    0x1d502c9214a0203034082d25030724021401e48068810b18041d143d180360104220f4640d4810420022000c40403d825540b40049201e00d074106a00116000a0103050072400d245078400581d056330004d002c1140144c0d51080081d42d40c0d0781c03501454a0220003800d10380d2404006131981c00c00b24011000103014000005070715140b091041055243e15601c80f002005a41401d20303142035900d10300d503100300c010340c2848003107000c00742440d00c030a0440b030b030648403481188032a59040ea21040c1000c41a68015828411803403d40981100c840c6008034071030b5241c038072640d1301d000c1040840110000c14003d5001503070901c01020040035000503900304030f074580d0321400d0342c0c000202224008070008180700d28901924074540c01c000081e50185208000038007000b0220330502080300c023a03008110a40d8015000b00c1c000c00c3c01400e00d00c1c03441c007041c1000b6150107004001440c060380001400c48040d4000036040080260030720070fa0b800b601d02103805000114a6481d2701d82201018000d42440011000900342 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 142692149 1250 142690899 142690903
    0x903191a0c0903190203160b0a080a0f1b111605011d0a080a060608010b01080105100e100507020315010b0f161205040e06010e060318070f03050105090d110c010e03 72
    0x740040101200d400b0551548071034001d1150313040880c002d1007480050201403540c0d80c0c0100950300b417068464204052500101d0b0021805403e5000d030707a50360401d031242d000f100e004401454a524180d0b182d140b220f02c50083c0220070701640d040c010f400218081020080501040c1e00321042403034594900b01001e0a941201e0304c2001d69650f110280d24ac0000300c5840201702c05000324060072003044510786d9485c10f982a220015505800140300300d0041c000c0d440c00702105402c2c0d40c0c061904011503500302c4003040e00b0320f44071241003003c10400b0035100308520f0704000d00311120340c007540c5001040d45458800312550041c1c3d82000f01000300480c50340f4400200001080c4020303081490310307034082c1320f141014046500c24040d1919042d00d0800040e0154050040400c85840c060519071856039802c40c01c0c2302508040641c402c00307010383c0100141d84c4c00d41001c100041d501800c00020b240c10042040e528000841c0c1c044030600c5124020754590360000305002444840c28201100345402e001c0010f4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 142693399 1250 142692149 142692157
    0x9101a04090903031d070b03010902160c0303030b1c0203330109020d0c0c0209010e0c040302030703120305010e0c04030b040c05030303090f0706050405090604020d200903191a0c 78
    0x1150700d032402c810b0606040e455000946680d200d281450440311100b01d40a441792401c4c00b80a068900800041001c0b0f509580188802c9034490740851010009a80310a144180c540c02500003035201c5919031198640f4041c007150b615081180700c00d03015a59400700340c40d040b02e00c4c40403c10980d681c0c0d40c0c03081064804895a0303105131843c04070407a5a1600244402508040e50603102caa1038040940c0c9014042c4c034445041c290000d044030a980c0c6400c0002801041c02800d00344081400c3c000000103880c01c0100d41c0155118110600c1141700850005040700c89c1613100c0130000d4001d409101310b5890850031941500d170080f0050034a80c0e1b480c18020358840720390f40300c9500740c44004204411007001081074541415441e00fa11406642c0c4d44d012140c5d4059809a250b0103443d020200e080d40c50141d0043c0303032840146a020175640c1c0018128060305200c04081032100f440014a02c02a18040c08142800c100c1034070503494110711901c1d40c4524032801000c400440001102140340c00d6150410344d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 142694649 1250 142693399 142693409
    0x1b0a0308180909011a010503071b0311010207060911031f050901021e0309161505090301110a090305061b0d1d0304080307210c021c170301050f09101a04 67
    0xe4490f04265a0310342c000d15815124400b001c450303000c0a4250741c8500c0c122802002d0f950b5950b001c441c0460428000d4100301d920490034451200000038503d00c01b0b0014183d5640590b600141510700383c141000e80100c21041c040c825009001c0321082409007852540a00c4c222130000222175a611403140d00a101d07070b00802020f929404840041003280c0b100030340c4100c10f004280c0c1ea02d9008050352154140303150043c06c0800e4490030f8a80c40a82c4202c001c1c04400c0401000070038a1420030580007000d600864a003000a10301040038014000108842d942011a03001140780e40d04400e0762040140c007407c0c0080240c40d440b03510b107040e003245d144100c40c0640c01e15000e072655035503594501a40e0b84d2045c00f084540a00f055400801051580c50314804505607440d681c52051182d030030400301d88104851040104aa100c11002182205003542101100440d4280c2e40e54100820441c0c00d130500c00c4464800e07107404007080102c00400c61284c00b142c91000c403d4400710319928200031140610313000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 142695899 1250 142694649 142694659
    0x903030409020c010b0f010801060f02010f0509071502030412020405090f06250219021002070b041e090506130f09020d0c030b01050307030c0b0f07120309051b0a030818 74
    0xc0030034404802c0e0b00811500082a00811440100b0001c0c05100810001424042038481004020302d43c00340c403124407240c807140b0001505052540d110402c880040d250b2f0030150f0300c150740610442c02c1d074070440303045d042c83e5000a504080c41c2402291358a54a035800070b00803510303030001c00d0200c0d0040040d203d0b203e0311907007a28214034108190b14030080d90344401c0e05d110022130341200072003400450448480125003044503a030740c2c529000e01c0380300088041100214400c08100285410203030000e40050300c600c0d00c240c0549286c25040c030160b40016041300480c039182505000059850780e0f4008580d504c1c510010505516008119004028002c0080c1d00408030341c000c2c0080012004090341502e11507030543c881039881d0810b065840307280d40030007004134200c070380140044002080501078840c50302031500e14044565a5054081410144000110b81c40304201d000301714080c400e540380601208080c241850002000428001d06880050884035001601c0b118403451100c1f00041403030040c00d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 142697149 1250 142695899 142695907
    0x7030c05060f06040b060a0c06231302031c020d030b010302190302071a04020904030c020409020a1205060c0913050a0603061e06120201050909070e030105161103090306040b0c090303 80
    0x405a80700c0c00101e403c14812464241e10710f60500c1e004050380c120007550781e20701c501340c0300c1c56641d40700900d00001000c060309000503101c01c00c1c2e070381d00c4840362142070300d01c60034a014600c5105051070880400c02c0103241c030001221007030364254001606003814206140214220241000680c000d2103450200d16580180010307080416130960000c2040038811000d013540600c09a0207500c031010b0550307000750f10004500104011a00c20f41a181500c2d000410000b0480010780c0050484682940600002001e0070408010300c1000d1011691100f10316042034a03080200e0001a00c0d0801c94403070b5903a455032980415488005940b101d0b0207980c0c410f6042000c00d020844035500340680200700c20b202400d240d030105900c41d15038441e00520341d040e164941061420310800c0a1103400170103e1040042d160b42e1000c1580d02401200c0c00340710300440d1801c0c00544c0c004005d110301d001803d10441c2d54070402c40c00300079803000240e190340076810210f5000300e40c0300c45101030694420322548a0749031202003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 142698399 1250 142697149 142697161
    0x60305060c040653070309060b09070e040e0705030d03090506130305190521010f08030c120a20010501060905180a050901110726040b0301090207030c0506 68
    0x28000300107499040c0c80307000452066880480707070f0042ca5900306213402c0d125008403940040524007141190300d20088900e06404100c0c20b00c00f5910110344800010b900c450354001409100e10920365240002d40f8800081d143c03248010303010b4240a0b480c203026a0351000080303e4101c0c14404580036150041c207132064107409803070040c0903250025064602d8010740d030124164111040f612581c446d45a12914105900c2d14a000782070b0b140c0a0307010080c001c04206400d422110002c00855010709007000500035414621b845140e40c031241c11040443e0b10410105100d10070004200c100e02d03600307800c502d507182100f1a003180d03c00d2184241245060920f0000303910402c1c19003140d81a2421596003044113581c0f401040880403425118200c013004280c0810900469500035550140800c8000726032000980b00111a59029400c02c0c1d40b0421040c244903140250810402405c1e2201c5810300d04103810200c03048001c0c40107210711010160300080883c200350044000c17008064004013035890354a450307 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 142699649 1250 142698399 142698421
    0x203150a0c0f080103020d1406040c080706031a040e1606021b100f0c0204020f0d060905070c120e0102070308030702030d0506040608070e0a11070507030308220b060406030506 77
    0x1035440010180c200110004100d01c1201000b03000450b41e518410107902c4c540a110000018800540e07001072410041030a80d802000014000c0d48540e81b69680d00c3e140c0700715a42000d80a80060040608111034442e03122400c0c2c010801022007120001058050308210340d18001c0400c05070030700000e41c04000202541c0218007643c0400c00f0250010000803000208000c0c162086d400c0d102160f803a00711009054801d03141d2280d01307072019000602e0010281600d101c40d400507640781080301d4503280305126042c03090003083d40100c2c445c241356981c0f803059a14100c00d4a0340c001c016041182d1720b03d20700551303072003007068034015600a010f0917901d0820010003500d80c2c0c01680400851414000071400a003032610550303007192a89006000c00c40e0418882400f00785c000b51101c80c040b43c541c0f00003404044a4002040040c3c8290010901585145409004040c000f880450101c80070710410741d07828940100c450019900580260403595000f00140c020045a003001c2c2151160350304200d141220 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 142700899 1250 142699649 142699651
    0x302030c010c030c0504090203042f03010e0304030c120c030b04060b010e1009170703061407080114090103020103112101050f190b090a0e07031d01090b061c020315 72
    0x103090002d00041c41d240c00190152998041c0c07030000034804000403c00c20a6581c0030319045881244406185202e118400b031507510207032400004040ba800f4400b16910f804d11507a441c07440b401e0061400c041c65610381da030140001d44280600905807062a408000180001308091503210654002c0d6040604203440100705801c0325034041601840704032610302e0032950424581d1100d5a6114803203060656250355807200010000c16440342ca2000f20000b2203034080e4081c90345102942c450b4a10b40848010900c00043e4040410040869400746190b2035080c101815a80c0a00707010821800305c3c80c581416101c3c9107818009c80303480c2d2440380100e1442072100f90407102c00703e0f81c15002082c0722040000404a4246245820000c11010088805014040c0001ca9401081f040d003c0d5514555141120403c0b55008002030b603a1400c070030101981c00c600c01c14004010004c02481ca41075680c021900d4000e0201c0e803084944541050a5541503081d903002c59601406888000e02035145241407000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 142702149 1250 142700899 142700917
    0x206071205030105040e01020c0a03050d060302030f010c0917030a030b01090e0f04050f010c08040f030c0c150311040302010e0114040906060504090506093c24090114010302091c030203 81
    0x101b001000c0d60350302d8050082e1800020b02c00c02800b24a161658181c40991240d4074540e1000e45404c40000503a400b40032400c00c40150a00124080424603070003001051039400c184182030f55084200b015400010a0b980b8114043c03c0020310086202c1c0181c410b840140e200c0c0c403105a02030208150040c510301c0e85805940700e1822984460030f520074040c26a81c800f611040001d852800160202c1c208000b40885030b8001d04140350041d16603121040420410b802030740440c448100b11318034566051040008845030740211608007421540020105100d028140e41080040e0070164400101c1000722001071031041c4040111030340d03a2034080c21a42061003811a02c0d4500000640ca6040c01c0b6100351042e41101c0c0308960f00d0314400616503028140c0540070141e04042d41c503c10012600304201409406120480128041191101d040b60080720b0890342c0a00d250800402c642e000030140c5030740404003400c0c0540c840300c621010030000341441000c00c444401d0300c590398040c03503004402032005030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 142703399 1250 142702149 142702151
    0xc1201020a0f02011107080702040605030607050712080105090c0a0905040c02010b040f020408030a0507210806190303020c1c0803161403010b0301030201050918010608100e060904020d020607120503010504 90
    0x420300b52400c3e800c03200d621108002c2160100704000c0051400320003490000e100500c006a411b8441c0301080c030749401260100085200002c1440501c05240503c83c546025441c0c4083d4030341c1400c02103080d11001030811a030311000800c2990744103000c4c9240754003501002d04200000e10007014024082c0055444e0700e40550700e041d4bc1a9809041c6000b12016204460025880c2c03125124041700c03540d00100b410349907044e81c01c00424039440c0e10071882c5130300e10440e0b582c0e41c00c03800c01c44200320705440e00c0074001510b207107200801c000007030300402c11109401040780c410394880d950146044521000c440000c154420010400414040b01264240c010a0310790715001c11b44400c0c0c600000a100a00604848003018801000158480e500801d143c09024001550350200ca82d0701c1681140c080c0c020b01e020132020410807a072814000402c01c02059100f0a000c1941403400110390f1105010340080e00400110f03d44406549480048429180e4081e1201d495820f9200009016030001e009182c411 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 142704649 1250 142703399 142703417
    0x3060c0406140708120910020705060106120c021c020c040e100e070b030109050606040905040c0501020c030c010905060c0f030c070303021006050603071d030a060b090708070c06020c0c1201020a 85
    0x1a640310000c3c2c3e40002c0e0f1101c00d891078040c0400700c900b00184014050f44040c402c08200d1084401c80e80050500140310f80d0042017103505241000d09101a462486140c0c54904000e09080300ea000a2100003034a42403c1c4182d041e01ca94403ca0412000189080d0060f0030300f00e220000030800a0001c1d2054100c6c0401c020f01d90781e800708243c4410162088e0034000d0800c0c40140306119481e4040340e0840001070281c0d140641c2e0f5a410b0090344c0701221305035a1079114000810883d6018850644000c6080340504174000041e00007030a200d405014040c02002c01180403818040300f00982e10311a000f041c100d0f501d924000c0a10b80c2d652080e400300701c0050181400300c6113002004d0061409444005100505599a10307004640c4060103801c0c080000300c1c0e18543c05c076540c40a018030485180258804200300c203200d001d104200da00a84554100407042041011660707104a1500045501c2000541d82e90385040e54103141c0861592496400b08031201c101c07141510540c000c041c0c0041d152a25240 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 142705899 1250 142704649 142704677
    0x5010801030302060103032a03020d0e120a060b03033a050708070c0614010f0f120804060c080702030d0c0209091f0e0f061812070201020d05160203060c0406 69
    0x900000c0c400100541d00607001400080e005000480c00c6a01480c80300a405c0d4000f02d46c450000440740080d070150300310400e811071040d80f150154044940a9844c0301c005041c10442c04d65400305140c000e05007558960b0300156517507041c03040b280c0d201968038921010b0f0008401040c8400705400e2f5245030740c009040407510210160249034440e510035168084075544050b0156400403140c01c00711035441c1d4440c20170722444103890025000c0c01d10050756850300e505242d02502003514641203040e450914121510000711408100c400f40c42d02450319074144015403a15807054011010000e40c180955804d05000c103a000c00c2c03e100042c001ca070450410b0700d031a05032545548440000240c01c208032070000906001d10340200004068680445403220b6414000b01e0400038250349119240c0d99020403403600c2d020802420500070101f21305c45103000d04680c001717075072042c1c01c0186405200003c03500148032076203041081d04030364020741512014601082c0480980c0d02900507103003c1000500741c445 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 142707149 1250 142705899 142705907
    0x60105031c02031611150318070b07081c050114040b09150f01091809020f010207080619020d140a0501150c02040908040b0d0b040f0203060f1e04021b0105010501 71
    0x600c00101e401440c5031105005807035106010410f800d031030743c05442605c1c2800e43ca4401e20684d8100c42403078403944905003610500d060000c03203580f420b81544900014440103c2726412a609268000b4006d596605645020024040401c8240d08d0044c03a1100000b0120f00c00c001e06100e2120448080101d42006810409100010351b1000381c0e00b072003000324440c1d074240746950381000d150504112004a0340e44201c1480703450b610502d24521502e03485040300b1070500c5c00c0c0d000b0701450240054495182041840750342c0704401003094008219903d005031a907469a4101c890301014000180582821407510303555009065841d140207070701d880d00014141442c1e030400c06c04c041c4d071079540340300045054003048003800c070700364042c0d585544c01c0000260042028000b003580d0201d94001050b423745250401088417411202c50b207805004008000c803580d00d0b02965000c15004850380041c01074641111151440349118503038010348006411040400091040c2205071382038070081c04140e0301e51004607 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 142708399 1250 142707149 142707193
    0xf0d0e0708030d1d191401062d150e06040b0a0f0801050a1d09070503010c0c030f03150302010c0516120204060f0305060c0c01090803010303080106020c0a08030405040903030908030906010503 84
    0xb1651340180308407110701070f2910417403038495001d412034215405081c0c001c2800c40718160711059130070740e828105900040d22100c01194804a041c5540d422514010303079417090b218022016010031507502c841d01d5055940800f0f690203840709075002a01e85e103a8030409041142c4840740e40000c5111a400014549000f002c0b0009941c512807000030140031401c00120b426402038211510b6005020020031503881c01d100c3e10104402643d2072000365001400c0c0a0440c1c201d00b010841098180070407441d40460020070401120760a00c1c2410b441d803c42c0c03e00c5424844602000d042004000c007001400010842c030350200300340212010026252703940c0d000c030700f0b5041a2000a10540143c800181203041d0800904600a224000440c00566561382d00c0c10aa100340c008502040030b80005110440d4104404001d00000341c035141c0c0100d0906207090303500d00683c460716224580300c00045007017522a4001c9190349a0000344240c49080c5812516140e035400d001350b83c060b1140d90103c020a040e80d5842c4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 142709649 1250 142708399 142708451
    0xf0308250203120904020408151602190209070201090b18010c08040b070503060a03080705100b0928020903060a1a01020607120f0902030a030306090c020c01050f0d0e0708030d 77
    0x144002032094042010f075803c01551a84c0c4168280700c0001c40c15414002c030020245101c0c0c0d51b0b14289404a01020320760f0301032004404541c0900c504c0456549000c5a40904c0768049450454550742d9030340072405840098401000444541d085c4160508500340038100c641700a0001d019400b0f20400c202c9500c001260701a202c0ca150700c000c2105240200d00a64001c880540007038461500da07290744003a03a00c09a8110381c66800080340000306c0d60640300703203038540300c080b185410317141000c400440f0841d2203c5140e02d950381c4103001604401d8a00e074101d54030324401a00361030240c5404415480284810b00c80e8084641910010f0080340d840030500398822000d907111040c0f40e08168a416000b000820080b0104035541c0f110760015a8040003d200b0740c45c4a40d07030100d8540d04001114056a83c0786c4055400c0d03601078403d103c21681c208050314040d0303018030300d8281c0703424510340280080d00c1d607144800c00034041c1a0000c9031804c03010005001c3c84828503402d100d2502010390004040300700d0112 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 142710899 1250 142709649 142709653
    0x4021f020304210506130611040605180a08070815090601050d03050c0a020a030b1b090f0904020a050a060807090605030118050a0f230a05040f0209100f0308250203 72
    0x82c82030f540c0c1108001c01c055010611440e40d0407481d40c0300ca1610909407174141e200010070314490708000b400e000348400c810147c4c85803801c1c5441c2440c05003107805400d107000c44174180a8410241a11380c50740c44802807074000d08480b1050359030007210b45c6600317a104000c42e4040d034820000b1844c600009046040f04c00c003034541c03156840152403c40b0340d50010741c40c0140e0f41c01008004005a541c0c251200051030050040882a0802e81c580321414a42512b1141200f40c00f44010030072541d8000300d090300700400b0303100000542d0fa548001580b11038203400a50380040b01400c0428a554040079452080145460320304500b07803501e1065680f0b0100740f00c0e00001c1545202080c41845140e00b095400581c51440429140400d4400c070061b12546000100c040d003a0001180d428640c0c10001500240700190420043c140781c0c8440d09142100070001c0c0c0100c4249000c05c0000f141516280020b0420803001c1e1002601c92a00b019581d200ca1060010b550b150000040c00b400d18103030541c004e641c0100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 142712149 1250 142710899 142710907
    0x140304030f0807030e010c0504170601150c0203031303081b010501050d020d060f0c0e04110301140d0804030f0812091606031a060c0706091205060403140d020c0604021f0203 76
    0xc0845006034010000f000b0503460341d44d24800d100007402108588441d6440d41600c0c0ea003003490b00b820103100c05078003940d0f030351105004214084807000001c102d08e4945c41d065110344840d00101303186218400c0812942140c001001091114690140601e1a1928024007075a45e9030081b40c4e098881c00e004440c0d0245001401d040180760540341c3e5003600d44154404102906407031241c000700e400120654020503050b09111460b45800d100d030b00104800c0303000d403038219410480211250b01344070003614080d00780c12400c001030044640582d0000c0d544403540c02c00c0c01c450b901c0d2038065038001031043c04c0104440008603d00c0b03100890b41040100e14050200e001c61b180240490150122402100c09140b5a68081c511522042c00414034060781034001c00c1107601d0510300a040c02e240d0b030f02c4142400448400d80000981c0402c006802c07a40600d0a24103030140340001007558452484c1008106100240302c911681c00403840500c514001c582010324410410500341d08200351004110040e04108 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 142713399 1250 142712149 142712177
    0x91a1e1605030a0605040923030406020307120e06031807140d0f03030b1003020403050607030905030a0320030411031b0d14070e0f250e060d090c1514030403 69
    0x74018640c410b107540d00204460b42c0d504042003c441c04481c00703585041c001d0100c00c1d50034021076110104260520000c0d8030b420328009000752a03001e440c0d8001d1180a201c00e0b12103032113124150070a007403500288284d6880c18100d2111500348a6021449030501603c00c0004403090081c0750f002d04844040c10810403094156203848441c048404114149543d4504103829922200710180051009071001a9500d045041981c50a400280705900305400c0410600000e54088140e40601d840740c10082298600b03000f4050014804c40e2540c040c040c0c001c81003000340507940e54010340c1c0039010b030107807015605c62108046000c0c14190300f11b078210900e840c4000000304034015043c0c5505001c0f0507036901544a2070004101d0320141c6440c04040a44d030203000c400c0048410f030501110184c070ba035078164030f8650006400c003000b80300c2d4a40b00384004204a283c40c2605e803c50a0f005a10000503082c05880f10101a02c02121006240009102d07401d030101040201c01140d020355055100c2c0c8007105ca4003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 142714649 1250 142713399 142713407
    0x40305160f140a0e01080a030e04050c0405010f09080102032e05011b0804030605150a0f060f08090f010e060702010c03020c0c04020307140c0601140d030e090a091a1e16 74
    0x51030609403c0502d42c2e00004030700710001c0e4041d01030320a0314040c2800700d40e01d08004055910142d9102d200b14035000c00d12200110304401c4608840e828202028001e00c010802e6808e00820340c0810b5686d400001000100b8000c000400103907600c10035040d402c030a803001d4401550b4400d00646020900f02540045480304d0200c24011641c400d5002c41d1030180c50341da03694103030f0340c054920840c140f914a0b5030000e6450003010100c0942007111400c0c400c5440c010b8000c04c40f1b80d0100001e401d1100c034230041140c540040c4456882115094002d20940031100340d415900c42003150010015484c02912101891280c001c60382d060035000000d10070b00a18a08000c02540094841c0c400d0022562840e0401c0710303a000501144807444001c1c0c52990300d003040c0b0140d5600412603807031181a03814100700000341c01c80c150262420040d12000c805a41d202c0c2c440000b010000e402800c50704408003402d00c0348aa00c40454403903203031841c045d81d034124107114252070194281d0301c00d14542c0703032044030b4103210340720b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 142715899 1250 142714649 142714679
    0x103060b040608031309062c0402040e190309050102031810030b09100302010314040b040b0601050405040e1e0712060506060d110d05180c06160611040305160f 70
    0xc000c10000c0c19907595450320345107901c03054011407058402031041102c0c0c1c80c14422400101040c0d041403604900746c000381990141d0359403100d018490500f01140c02e54455070703c58860840314004803030301070481010341c2c88041160502100040d090200100c0c080d40b0100039640401c944010b07217000f541e00030041108096000c004981010380d034034060f040d590b540d6440380303019802c110120322040d0704500004007500e1383d5404452480c100d00d4248000a040c852659503c40d4209440b0710150b1179610048900e44910ba0003158084d0600a6807450254003140040050201003411b0400d1111240c080743c84000500c9041c192149102d0840c1c0800d03100e41040f54000c0c0f004120900e4000b91a03480c40840307402c002c00e1035602c5401308201c54181d18030300c5200e403c806003500001c801710802c1d4150740d0300e0f10300c0c0c0055800b806002c00c90801212030f00000c5003c042e070001050013034605005482d019900325100580d010710030f01c003402640c40302c4100c105082d00d6508211144440c14441d881c01c082803 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 142717149 1250 142715899 142715921
    0x15040b030d0912051005130507050603010e060d032d030b030a020102030304150603050d05030720030d11070b1e070504030b070f05070f03030b0f0406050904030e0a0e090a0c0902090306010306 84
    0x10110300b03103050101031041030f00ca07e0300c1d03120f180c032606090f0900e01c3c13a044d250f0300070a001c2c0e2800c10042c4640c2e0801d40240e64890703070484000390f0b10035080ca000c0b40d08080d00f010018103842440100c03000852021500031200103155010000522000c00b00b55448141500c068050703002080400c0210b152201024a6000418000300d086a074955078030303140c001a414236500084000c401c1c01002a81300252051800f00301d51b090340318030f0f40b00200e03603281d04c59030f1028590259241881c00c2260500d030180c4454907048010f540c030310725100014206540c112141c01c141001d1220024005900641c103a80949801041046882c0e0b07441e50140c40c54130030089080c003840014021100003500481c200e44100b44a07a50110f80022402e042c4500403000361a9180300324100041403126880b940d500a03401a01032821a218001601c04504413400a400008000d10300da420090041000620108540e101b540c81da00d440350b64580c00022405034007145941500303c10010004102c441d004980202 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 142718399 1250 142717149 142717153
    0x5030d021f020c0a0b0106080a1a010e040f060308120402030d0807120b220b0a1a07060b04200a120603021e010212180301060b090d061a040515040b030d091205 70
    0x40081e17110945040c2d8242e102c100018120002c0100b00c0c0740742d0103118031001c1400001070308030440e0800a030161401988143c010b923038072002a038012080307030030400003150080070880c2e0f25118040728030107240007220182d0080c401c6950a070401d500c0307808024800c2080e41c0e58014212411026140035000c91040654408021406041c4184502124003080d58000c140000e40500d024244003034480107a01084015000c4400b002d5001c12540844101c01d62140b4002090754905000400405155900240e01e14050510320242e002510042007102ca075030b160408042e0684c41904142c6019000003034025600d941400c41c010001b103c070224108050050751704d0440e0f032891681041d000b585080d00242001e41014040e42003e1188801a00300140a140b500032144040f41a814840c64001c0c1150350b920b41d201031100d000c242c0c004e101c810051080c01141840855102010f03d122000792056260070783c4500b01340b070b00080915000409440b80d14009180042c144400f0908820942d454 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 142719649 1250 142718399 142718413
    0xa05090412020c090a050f0105011e03110c070f0306060b131205010b04020a030c080105120c1507060203010308120604090314090a090908071211100b03031603030605030d021f020c 79
    0x9591802204e0744210200c2c04000b80e6031404441451281e501070384910305002d64a601c08480c5106461000955461428081207002c2043c01d226107a1159900f1846e81c2e0096140101c0c11b0030320704401d80101c0b8050b0f8400c2c0611604c44001440e548a84108500e540c0009102000f14140000d0401c1c0054000e000000340001d0120210303060742e20407005030700000d41d00c0009e4000b041c4c00c4100d032800742c0400d8a948440c1c0422504144c3d444080000a610505668145903400407500301101c080c40e9000c1001d40d00c9503900c0c642903406410000785080703110780300c4001418078107151085001c03058140d9220400c480000840a031160b100410303054112041100204400c24a0b001c2c10600d54406e0040c3c507074803011b5040c0560141494442502000008002108020800501c0802032111054001040c0508000280c514442c0079440c85000b402140c03150181a055030007941100d1040c1c05070740c5903003215242240c850390040c083c401303c400032004120040503598080c1c1b45002c0c0d407130229551 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 142720899 1250 142719649 142719673
    0x717150d02010516050f0106080f06010603090f1703160201021204121202030408090906062b090b0a2403020616020307030b0901020306030c010804020d02220c020a050c0a0509041202 80
    0x802e0414132000d40f000d6100c100c0010030600c1c248506030080c5540d030060240c1e0408441e42c43e855a03010700c100c1e8100340d00d403c1808140301402807080d00d04d60380504189009004c80d00d4504150300b080790180000e00007040c00e40001c50041c000c0720407841000d903441c4855595562206602d9803190011740070000c180084461b01d220603c021800b0384d0140040d20348a041c500104030722618014030440c0980000e00c841540c500580c503810b42004000c06841c0a00e1400000100041000351750140542040d10180513446980f5401192200d8240042c034950104038600303c02c002c9594440250440001c00800d088290039041a040b901d200405844a09543c0d0f00c0c1e00550201c240c130350f07044c1d9941c00001c4c8601072504000f00c042c0450207080a101503e4503400086424103030390030223070080d032440120180f07c1c603c1c652503010446080c0d40400c03110180402c001e50341c2e1030000f01120648202c0d80c0c861082c0c900441d070601154002844502c1590f030300da468000500303a41240d142944980708040344 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 142722149 1250 142720899 142720927
    0xf0503180316050a060f0b030312091f0b0306060a0803090103021308010c170a0c08040b10050a0612240302100905100e04050703060608130203150703050717150d020105 74
    0x3090185004104c0381016081100403140c904c0b25031407a00e4503100c1c06103d140c034040b00b9036440b485c036440c2c400e200d43d035210071941c02c1092401003071103c0011400b40b01001c032081e9001c40701421043e8100c0d0300558864003800f00b021454020403507180c4c01030001c070015600c20780041c0346083c48900340c541c0c1d1584d200c8400c2e080d600c80c0f81445007c18a20710690000b907445000d480d62106900390140010311650701c0c007402d844800303000a03006400810010303290402042010009160141141c880c5650395100203000c200750303200d480e24603800d2000d0104a0340340c6083c206130400280041c0442c0500c0c6608018443c81c070720741100180030b0741d0200005c0517562107180d60030384901904e9958540c1203100410089440c02482c540038546048003d111055020b8100e40e4440100300d840380304043d0b140002480c1c5260003417080419104401044aa036906030031044c0242c030707151900303c0c1140030741c85002c400c01340c115010f803032031110b0401a039140c0c038160307075800106401070401c0c601c0c208001020708 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 142723399 1250 142722149 142722187
    0x120507030231021204060c030b031c0210051e0702070306060b0310050103020a0207030b0901060e04060b040e07081c030f05040303060e0c04050105030103020d0503040b0c010c020d0f05031803 84
    0x41041e2000c0840d078110b0070034210b011241e80070410781180f030b04980d6503941e406400c000d400900400e0740c400c03042c3c5a160213030f030000031081c100408076a003048401e000000c2e00791070701600b10300601480d8554100c0c5501c0c0d014142c0680b81c4044000c00301e06111440b80902080102010708602ca80900000420301d244a400702800705410541c0d96440c00404c90820514541d000b941098410003032440c0e01c5601203041015a98082010481d0391940800d860241015810003268a5050303000c1c0301c2008082e602112422900381c40600490341c40300c0403103464204500c03c005940d00030141004420202d07400d04082d11302c29060000b008840c150054003140c00c11039044020941e1980103014285501141c668805800650305107064102400240740307000c1840000e0180c0142079005041200c240140c1d03002d044003403c030381c1d1508590000c45003e030002c171508501501031048074410b607500c01c1001c03040d00003540e15628075640703d465151100f1034040002c42c00c00d010602000c560000428045e03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 142724649 1250 142723399 142723429
    0x80d140106020604051618090303020d020408031c0b10051c1802030601080106050f01110102160b0f1608060609030a120201140609070e1002010902060310090c080903041205070302 79
    0x200060300d0903180841c6005c0b51801071103030140c007585c6d007004400f40b10b02c9000c4503648010341c0820400c030145003d4001e03006019424441ca0f00126010400e0940000038025220040d80303001c44c42651044070000300e0300070306601038004180d514001c1c03409000380c0040c04e401000c161f603140e5485013511140202d0781070107201e0940c040030200440540c9001c00c0024007400c4090001c00185240c50b0005501e01030011031541031144181d40406562800c1d415107000c44001440c1800c02846032a22022044c3c1c103c0b08107070f08904203004500020402285500b01d010952240000c58455000304082c0350000481650b040c4107445003000000c004140781c6960402035000481ca205160200c0e0703400800044c20103016024100802ca035856200001d4900da40c03003518489c01909d21404c0480c0940000c402c0031350441800014050f0030f9008080540403507001c90303030801000310021401c681d1850300340d0b5100741c6035205000034042501080c80d032240c81c500c41c004444149503240e0103d295846000c2c80 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 142725899 1250 142724649 142724653
    0x1b03030b03010506010305091908040f0b0403030f0e0607020d050a0f060c0f030915050712051303081e0a020c0c0409141c0206041b0b0d0e100e0307080d14010602 71
    0x3030040350900340102130308a1003d007800e01541c076051400c0c50b076600c0f07403110500810007001095014007064a0844014007548034980644a84403d011441a88240300442c00034004081d0055158030549649800d0700c0000d106500e4410f1903000c00a61410301d0001b5540f41c064001c0c00400030b051070707000c5100c80b881100049010300b40080c025283e01c0c0c0ca0210b00d014523081894110002c0c0b482e52580d01ca581c03140702c0000d980d80700d10604550017180c42c1e50031041c0303500c0c00040c49086200d203c50006001c0c440e54648101c0d640b80000a0b80b1031245404d0140d0394035081001c18640030094024001d403590000c100c4d5004007155002400350f401c008010345056002a40e04032030070324280000d61203030328100281e110821854000941d100350090029012003000c0d400c0800081d040e8040358000c01d0002001a1241607210345040100a00150000070780f0452145850b10562401991400c1880d400030b1400d2440a031103441955022a00141c4080d079070f00f603400d1407841e80022490181c003841d40 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 142727149 1250 142725899 142725911
    0x170a09030303150503060c070614070207051f0c1709031029130203060d0209070f020f01050709090b03150103080d0c020c0a21231b011403071b0303 65
    0x200901200d54203d11103400554000c014010b5480001383e0a800c00000221503564240f00d04101d00242100c00181c9000b0140c0403c0c4540558001442c109559048554030a03032500b1b00718100042000c2c1c4101c80c04500d240030090082103e504415803039603400101c040c5800e25040c0040d042ca140c0840034140c407603585402184150005c0c2d9070562003420b101b0f25001400c441d00005400c600404042140c96400000040b81d5480744c00001018035400f80c81d0a0440c141005d000e0302c00103d87e8403000041c492540c00200b595014000e050140d445500c400e24200d00b004402d00180240380045901403107405014407210b5010340446000354095404507885410390003110050b1885a01c0203421907100800c9030110b581e407006500c086540585507500d408051a00074507036a1989800a0404660f0114904d005e4a02c1081d4408114540c0242c4003036100400500d0200c42d1070401950024582403204803022440b04001c40d0040c03020304107522112028bd1500d40c40b071060450480009850390 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 142728399 1250 142727149 142727153
    0x9030602191103070305040b0c0f07090b040f060b030c070c080d020313080a0b0105040519110414032a010c050a06091109060922020307081605010903120c170a0903 72
    0x21910342d40d89401c0805586040c0c59a100108a40140c0c02603120040002510048400742048984407815041d000c0d030340100c2d90340c480307c402841001c0350a40035a0a150070624602500c0c41004280c07181e03222240e0a5482ea04940d400d503401481d4126003441103108003142042c41088005034550b11a401160faa03428003920f05110005070303001556a0748a000542d000698001000c1c4c107403a020b80e0005040d6407625003125405000c0d2245104c2a8030b8000000300284410340140161020070030a0b03051f41d82104141680d42c0021101400501d4842940ca03000020343c40c2a062001c00c1490a01807502c05a01c1d01030800711011b00860703d40740d07211454000c0010503850240201c02c2194844c12501c0c00d640032a502090017402c2d04002610907210180702061760400c990312135005011030f00450744480042e5501d002461209030481106c107400181c640c40380315481e060325400411744161000f83c2030203589910a42e8000c03120091405207000d44040c612028051001503030340e40c2e000725442c0d4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 142729649 1250 142728399 142728407
    0x7050301060b0307080a1e09060509060112030e040504020117010f03030e010c0201170603190c0905011502030d1104090203091605040b01050f0711040e0604120314040308070903060219 81
    0x70b03a1007810081403d00401111903000510540e00800480c00410190601c0c01c422050083c0c002c8945415031500e00c0400078000190300c2144104264070813919982d0300c40344002044007202000800141c21040c0351802400c164000030342052040c148807000350f408560741c3c1c10700a403d8000000d0301c00d551004100b0b01d5805500d03550300017170a0900c245c0d80d9240f07800007040308880500102007000100c000c0703010f9440410101070110600e50030309102420a207441c03503c01e109071041180d01800e0200200d102201000c1059180d1001c0d0000c502d8100341081c00006007404010040c50381e101032000080301c51040c0001c501c00e4a03d000905501682c2a1109001d202184c0013035025510380410b10341140d80150440d103c58010804280d19044503183c00a426041840456005420081c3c40903510307800281c0c80e806240b207181041005c010580c4110120794a98040140c0d051041e0003060209000342a01034000d2014501101026140d85592040c0e90080d50305205103440d0702c070048a40703640 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 142730899 1250 142729649 142729661
    0x12032c0114040f06050c010606140405090712050907090b0604050609100912060c020105070e30070306090b0f0f0402060c01090b01030c050f0402030115030203090f0a1a130b0a0e03160507050301 85
    0x1c0c0d080103001c0110106d13454202f4001d071b0240d00d01a019040c04144508e000b0141c00180d07050124040c0101d142ca4050a5220201441141d80a9003000c81c102d9544c98008261016654090111810004800d0401c0f2041440f04030075001d105020101040c0c8416200186220502034000810204501c04000382140c0c0000c0802d401c11006589514566980e442c8030101050011100d654841544007003010458010903a1400d40c801c41c6800001c05c802900010380b17080c00b6240d00c1101d6918058114041e010864040b0013684100780050010f2031f11002505240141100015140842c0d82e1080b000c04002e810039180a864148104514500304108010001c0c068800f1b504551400703100f4031881d14015001418160003100065440c1d4041142100e50107035a0b0803558080150b08001c0385a8405c00e11214482d807541c0000b441704249000c4000a075a400184010b040d50781c962600001d01c072600380301205010420822060211010382c82018602403000f601c0c40503c1c240401d401c60384 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 142732149 1250 142730899 142730909
    0x60a0501081611120c01050f0c0a0c150914010912030b0a120f0b0114041d060f0a02040803040b0c0105090a02090705030a0f0612032c0114040f06050c0106 68
    0x994442004241501c001d82c182c001c41983c00c00c6075100c002581450f003090480341013540840000320701035044000541105018003903802030004a030f00c500e202c4103c18417401c0c1d01e550106503000c4417040017401201b015600f82041610000d900003495952500340194030904203880d82d1207111761400d100f0754020341006454a07003400c00c981007120002c1030308220741d40b0403004800360001841050001102d5003400c9103a024405245561316400c90500f000b200c100c015015a1910604615081505080d0514500c0080040100b40e540200380c00d03000000402143c03465400744000603100c0320400260000c3c00c0d01d0f681e41c41c5ca4544ca02001821244010124a016482100024050b80300d80201e207811660b546031181d580c1d0b481c40075030000b6000034111603a0452034070f800020071998040400005511a40d01e20034030f02002056801185004036151068010400c0a054038ad070140014068400035440f140c3e09059a80209078495200da0f0300c40d00c0442d000207030849403a0800e11074840682 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 142733399 1250 142732149 142732157
    0x30702120d1b2a21050304050105130206070809030a02120a02030c0402160f050c030a0606030308250e04230f090d080f0702010212090d110f06062101050a05060a0501 73
    0x44800440e0811044030b480e403450907120403049803041c82402c1130000341c404042100b0031011140442e005040d82e00417a41078030390b540380602140302004c500403000546d03500202094103055164448000980c4801e000c00d51502c40c1285440060311190658a141101c0002803d8000e98a0045c036080200303001c20746200d94130421250941c2d01103108800411a00041c0c5240704510a19100d4540319148880c15031510035800d071503081001a80040d01500c0c42030760380512584401c0070011801c214186481d0032050004c1a80c0401c0e441024500624407006102050700103960302103201080300322074044544020402080040500a1403035074220464000414600d9484080204940380c0075044021210055002c6140c540c401d4041d1402545071074040745060500202441e510701040c104803010840f4900380d02180032000c6100b0011a215101400c841c0e41c5d910308110b0b201002d214030022205107108600088182440307614864410300c18005000c0c105042004504803050380424104 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 142734649 1250 142733399 142733417
    0x50a061a060c0d0318140109030f0201091a070e04050c04060306060c080412030e040f0c110c0a03080714030a02010b010207091a0f2b1103071a030702120d1b 69
    0x80030b400202280480c1007860002800720700c603400c43d40782402c40103004c1c0c02c50366998180c410991066002c2500c4034840c1c1c070b6000d1035036821a01a0700786c4401c1030015000346649540c400e410140050b240d64040c0703451038403040e02042c1c2c40000f411030300c0640c0c0758500002c0104081c0407040e01880f501000d0300f01800d21180d460507907a5429068031481c05a803e103d8100441c40e001c050180414488500e0002c03c1072240e189200da0701c3c030050004940110008040010741075211a02150100035040d0207001032400c1810340d00c03182d00640c807400c022980880480c0002c4c40d100f10501c003070300303070206694000b080310807a02c3c000a142c442180c00c1104017600d0461660420000c3ca1841c00c881d006c02d880b645800c40204002410340c034480700200d0140388c55100d50010248036905940d04052091031202000031260301455a281a507024502042e500c0300c007508403c2c0045400303954056541d10440715500d1114003010283c1e00b09488003541c0c10f03265002d007003040100d94541c040b01b50141c6041000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 142735899 1250 142734649 142734667
    0x10f050f0a09020c01091205070b010501031b0e0d060c08010e0a060f050d050106050a080a0c0b12062e050403050f011407050c0c06030403260108030304020f0d050a061a06 75
    0x440d400c0c407a5542c40ba03070000704014400707029001245020b0304118031003081401c02d1000b40840e444a20304032400c4070800008110780d8007078890050300c03c01600c280007100104e10001e0381c91140180565600c0300031068440001212402810507a040d41d42d00c03a945940750000d0403012035409001440420f08010050201c00b1407144030600304c0b401100c40800d118800d003030840c0181100d8108a03044040c000c00464109400188082128440d0449071002d03640e505510107940946150050350745142000710b1000e00d0510b02801e0340744050362400a581400541c07408100c0b40c00f1400c100440c0002c14100203200051050901c0404950000d00c0380b0449100881c05039003000706640188400450720795800311041003000700001000d0301c0680c0e82e080605028020440d0701c2d044a01144c01401c0390045140b14801050403034046c0c1e0003c5055484603401c0250301d00d141000950403d0104c030302440410700c104003080360540141000200d00121054441444d4484285103024520030440000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 142737149 1250 142735899 142735909
    0x60109020304051011120103030e010225030609170301060e040b03010b010903031b050f0f160303050f180d1a060d08031b090a06030f0f0b060702131d0303010f050f 72
    0x6004e00c0d1800041c4001c0500d40c17601c0140105130341101c2d0b0000e0316001104050b0401c4221801d400240c08586d03a4155144840800041c200e0407110440c0d60080204002400c86d0007181c0301303510079402070410340380658061041d03030030903480303040007a09030900c0d41c41761300386442000300c4204140c00900c00407a0800000e030401c0c0440c0302c01410004000c40b14540402e64140300c0340c00c00c0e0311800341c401c1800e803040880d940e40c480300c2c03022049014489ca09421851500500300c2103c0d0b042d1905800c00c501104401805d4002c5c110804082039010206100b503a02c00e01c0606849102c1c4508408118000d18080c049110040001d405400790624541c0410004025264418962040c04411070039038650807519000348034940703400c00f0401101081c202e0301908100d1502010b00c50800c031550314118048180da00400c4541e420103010840c035030243c244081140c1610048002c045040c2400061620b40e41c8041b070382d10300458002100500c80b01e811a4203080080000321009400e403941e03180091 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 142738399 1250 142737149 142737163
    0x10803160201050903012910140702010507021201050a0e12070b06030a0b09070305060a02030606030403050a170c04030b090f1f060b040e09060a09170a1205040809010206010902030405 81
    0x805040c031400300e20116803054084400c0210003030001d0090064056501401089218520105412010081c0868201500c6100380c00000d5600c042c1c84004500d20007001e41d00000c0c0c02e0b81001030800408015071180c0c41d044540500c3c04000042a10304800403504130f5442c003d10040b035401c0755a00c0b10852b0010401e50310401d40058400e40b59490b1400064540300640000503d1034640c03908205801c031004c03480da400c4034020025200307190384403846041240700441d48264025000d00105010a10442c094a4482121b0070300302907441c80300c01c1c0c4085c00e201c111100d9000ca200010300b40b041104ca00721098120504d07000411186803982204d5840300a41000409208504c00c0d000401c0c417400c0d00321400503d050b051071b03640e0740d13150241461b8100d821914480f40c1c4c451000850020304192113030003412a003201a030803c0344010580e50500d03074813100c51402080700032503043c10007802e54800c3c140109d03c500c1c94160b96800c00000039040c080c05a2104441d0b501c188200030100c0c03000b081103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 142739649 1250 142738399 142738417
    0x2070911070606060302030105090703090c0b0307170108030d0f0207020a1a0712020313080607020a030f031517010e030a08060f13180c0b040305031e040b131409010803 74
    0x450406642000e1208501880078054541401c2401c00200542c040d13000754180d6900742c031110641d1342c0380b12059040d0340340c00030000e00e000d1003404100301d03003841d040146030085500d143c49c80f4010113803070b145080141300380c210183c01e400c00182e44c48106d50340e104c0c000d2200b00200040d4240803d9400069145410303108406141955a11040c0e12000700c004440c021548294404203e1079a010000e64035041070301c1c41034103d40e1400c804245030500054452040e406a070061031940e84694040f20b00b1668070b03240c0420306458034056000c4c1549004400b02400341044c0d800a0168010140350a40c0c02c0310281950603001085408451544000616406001074a080942c010201e01007030300185407080c08a4002e15001400000100079000aa0070324007600d60407000300e48410902c40d2510852000801c142d000b08007400034070761009610320704401044402410a940c400d0101c12540c000c1c039081c0740d2242c03000c4e03061101c011150328144040000f0f80b1940e5a640c18007201c90307624882e00701b030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 142740899 1250 142739649 142739651
    0x1090e21040506040e0703111c0911030d180b04060c03030b01021005010e040212011b080612191202030a0e0d151107110609010e010c0f020402070317060d0201020709 73
    0x8540c94160842140c00622015001c940c0d910f13170b03904003012034075419182d0000207418030202d10040c01c00c0c4001d680a0904420702c1499280741c421843d0024440349004a44810550014546a0344c0c10300801d452040780d5140d0038a524020013248170480100d403c041c03a510300a000c1486942e07403101000461540c54240003444900d4500141c0c6004150120310700d0f41410f120020802030050001c1c14043c03442500c8840814001464041c02e0384c070301845403403042441c1098005d0341ca100d0003003036403c000080c140c080f0785603442c0002401c0c024044004e001c51200d14480ea070400c002c020390b009104407548082d44c1841ca0b11140101511002e1624920800c400c0ba6040240a510312052000745003d0320300304110410091441c1c8250440c00041d0740c4e00c500140b00d40050f0034042c045501c1200142e442d131010341100b40056070034013076039001a02d15503100020704005031035510082c614540282c85080303c00c20306c030070304918000c4000c00044c011905244100010b03600041c10300192002e90b48 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 142742149 1250 142740899 142740943
    0x130207110d03021f020706021803010b180c340b0f0411010c0317090d0905010201060f0510141305091305060403050f090301090614060108100603020f090607140601090e 74
    0x40244043d02817248003031f2010348002031180b80104039089443c0c0119040c4c00a03c15682c101d0104a10319540e08540e140c0703031200b88001002c1b640401c1c010800d5084c1201d4032424221048501a00e0380c00c4818100b801081450080080c0b2000c80b00c841c3d8461240703000d400c414640f075903030706c030440c0f00042125040c0000602104209401005660f1880032180b010781241d280c22281e1a0390313240da6840002c0401c52058001c9859403042c0160000e036014049605500743c40c180500000f40c507a01040c2c3d08010480f00e00d01500100c1074018072000c15904054100b0500302006c003c6021030140a4a0080000d40c10010000d1004642a98810b03010309200b034865001d54050007041c81142d070880d0707055107801921300400c035103a0300030710b80a10f100901c0003a030350360100155048041a03500072448403a80c002006002d11a8000380401c01f150f2103443d040c0b180242c08a01550025a03049401d074441b4080250010343c00c2000350700410200308280100328548608a86600312403202c180b10401c0c00c4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 142743399 1250 142742149 142742203
    0x7150513120905040c0306050603180a1a1e060f09091905010e010b10050f0702030709060e1b03100302012007081b040902060405040203040c05130207110d0302 70
    0x65448242503802840215001d1504900181011070501805108503e0200642600f500c80e200d082c05481e03010f0a01480d548580004015010424805000d140300c0d000d81c2e44002119541d076243e007086001d001c1e108604060240800d41403024801c2608000d1100c10000180d440300c80b5079036511019140384d00c580e191b200f1030504042a02000c40683d44446505e00100f100c1540500d04a482842c001c0040e01111402c104025040480d0400001c2c410b011800309020f400b070051481038030080032140c0d202e5584078454155070959200c62a101c62400070484410100541514080010410903155207411342c42001c03110902c1c00082e0411040b4051074601d610881703841c4606600160440394030f146e0303c91a086c0d8881d0270012a1803540c0302c9041034042424940a1000d845031b0041c426814181080c00303000c000c2d00010002d94680f03425240001d1540c40c2e000c1507080101100b07001690319010b5044c4004a60801004140034011903080c2c200070a6010940100d03407100c100b1080d610034090 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 142744649 1250 142743399 142743421
    0x40209010c0f02041d1615020d0f03022a010e0705060f090a080a0b07090b0a0f0f0513060e0102160b0d020c100606030b010f05030f07080606071703040215071505 71
    0x10070617540c0400741d820040402030000103011003141e1410400344401529000b940319003180c1126110007590140310610510b50080102007194440c3d0b02d00142002040c410350f40c00c03c90703034141840c00005103002d40070b07204000b80160142072280d035009109a83c41e0001258007840f650b10300c401803800c04210284140d4809003441c0040081400700d48403003181d814104540714080d02c0c4a00456003400c80000d1001841c0151f950171595034541036110a040c420a0300d031010780340d0880007000f104000c15000300c80d01c0351042010342010b42c0d51551965010f80003903e010f038801112820701d04500b00820103514240115078154605000c0035031903118080f211b40c900f83c0b03e845601a140c0c10a0b8011410030fa156026085a41090783d590a840003081010340c0e01d48002d0341e07058480261480001d00c124083c0041540140c4c0c003400c01440c21601e502d644407001807198603544108070000500080d032400c4c00b0f6500c031048003c40031358a02980b03640c0b41084007038000b050f000b210340c480001402c04100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 142745899 1250 142744649 142744661
    0x712050f15040b0d060501080c0a060e0118030503071518050a02060a14120a0506011713050c031e060a11070308191406040e07051e130204080a030e040209010c0f0204 73
    0x406003030b40b407500d1400c0c9050400707490240600047c0c1d115826240907244ac01082450407643d031901d038440c1c00a0340e0001103505a902d40398a070180c0c00110300000002d07604000800000340241d1991503d95503d01010003921091006250f000d98a9030b2141e0100c5d0012a00600c0140d040b20115580e101f210400e9030240740f5130010560110012400d004800c5008451512500340001c0c1044950303658001036407446039030030602070250001000200e01501d03204083e0351140c015800c503010807980743c0001e441d05500c12a075046800e1071008440c20040308000264114110b440305110b00180d0301001d030000c0c0034100001d003c01160402042c1e00c402d00540a258010243c5070901405049161602d0700742400c1d55038070300a030f20744001c3d441c190f000803a40400399200142882e0343e034040211581c6083c0219843d0036032045004136860701c0d0400a04c0103200624445020304200e070014140903203d50a5600e2180c091070040140750800c1e0390098803000b902e41d102d0104180c2500c0c80c0041001008 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 142747149 1250 142745899 142745921
    0x7270e0709050702071e0b09040e070b0c070503070f06051909030611190804080904020913090c0e0c03010e011502010b030d05031f0f03020108190c080712050f1504 72
    0x1c42c0030305000e0000e5020030f4071410b540380c082803c400542140f01c941080030b05c500c62150140000c3c400f803209882c0941000d40c02004001c1160142521000300341250351018441155590045504000c07a09050021000800c030a80542c1c1913545000c4d8050710911500282c01401100806c0c100c2c2e403240180f034910f01a41c0c00c640108020200761190071000c1c2d0141c0030034201c0c01c1c84010320440c207034402c200b03040c800c0380d01202d100e00301840380c000d00c80a500404500ba500071044100c0e410540c11038400c1c0b017070030b034020310240072254076103c1b074407481701c0c0e01a04130076801108100502400001c0c5012504640c0d03c4449241c5152004200328010441054140c1c0d050046080701054113a00001850090070881104281803142140482140541303110b440401c0001080810156000b0913041e54842142000c000b8540300701c0c11202c003192030547d08240031445850030300000039070220803140d40003200142004142009985e0020030400101150404d800c2e0031800044c03500c0d80d80258078080 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 142748399 1250 142747149 142747151
    0x5090d0c030804030b1815091509060403030605011d010c02060f03240102030a0905151204061413020906090403140f0d0b06070c1a0f0c010207030207270e0709 70
    0x1540701d1811040c203030b0041c80181e40800b0ba01000c142001d400d14080040d004907000241112100c800d4501000d58000f0040710f210f0045038a000c0602c2d02801206101d1440940030300520b260918000c5c0484000d5080749040010794400b2441480703c0e142080d080340740900f010990400f151000411501c10541002c0d44440040103015411201d085403a46500a40308286480c0b195000126500e01070540b0013000518030000400c40f505024400c0b100c1d038104103907450704c3c0012800505c661100180c2d0100d40702c541d10710000c0c105030b4140d00110781101c5450381015207062240c000030b0807080007a003200c0c49454801c001c103081500528242d240846100040c60f298400c00e041290140c1285901440d44c6040c0041c032043ca1518000701c52106070b010806c1d42446041c00c00080c0c10100b260324103100c40c0010030840600a01d4840070348001c0e0760120015a03500306e03900c0c0003810103202e5448047c031904202c0c0149003c00704200c1c1e00c0c60940102400007540d00c039107420350b482d0040641c4244002c0b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 142749649 1250 142748399 142748423
    0xa060903020c03010507020d020703080d0b12071e05210f0105011d010801050108120a0903060203010e0402010e0a05091303030212250203031003170c010c0306050406080114040305090d 81
    0x5401080b81105a103088008000555a0074816620341c1c00000d103038801600280c40610010b00c00c05c000e4150300c0e0300b000300080e122160201050840300d02c0b004101182c1c8c0b01032400c01c8003250803c1c110b41001c0586622025040c5810003080c0100c0c0340710303403694800510321241242e40008108021000c0003010082c0300c6941d590304240c4906688810600f52041440004583d07001c05000e6281214008801003603440c42d2015510100d4200c2c41900007088144034002000c40c0d03546c000366018205410400e14242010310001d0401003030429694010000c3d41010003081d5940c0c8040f9610800f821000742850f012886c0c214020710464400d9590900c0c3d0b101408040303060149002084d4080310001c140e102890b40082e40c3d40d0008950701c82c00340c84544424000103035040021400b08042d81c002c036081846005a8034203694125410500203940c9010800c0360f4605401485e008007604030003008410011044c503540a20b0040c405002e0120025441101d600c419000010031074200310b180500e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 142750899 1250 142749649 142749653
    0xf090c08030c10090f08030a2903011d07030f02010504090e0601170109110f130e0a0204150f03150908030901051f0806150d0c0902030a0c03050105180907051207230105040b03090a0609 81
    0x142991741030f4ac0c0690310780301c03041d03082030002c07035060b0555040c840091402d6859583d40d4402d01c802c50400701d04100060200144822240c003a0f40e40321a1081e010300b00c1c4d0347c140031118400070325141d4003113a141e041c80b0324880441c000201d01500400250b5001e034580b101075011400e076a0464250031140383c5421050405044041203503800305208075018002100c480c076509840c45143e014a8100b084008410400201c1040461203070b8440312401155038a02c03a2907a454a0b0021200c1d8011070751500c00b085030b50f4207501c520560301348691002d40c4c1541d0502022a542e907000070642c112080711020352504540c2d406816500a0754070030402c1c8101d035103803d080000303034201750b42c00c80103581014040c0c1d000500900509051707550280c030b00c00c3c003194441ea40c0940004007404685003801955030114590f01d604085407402d501c5000104045441c0004895400c2003e443e07410000480760701d00419aa4403c048408036156092003030f40341d80303910120390305145582074020042441c003078184003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 142752149 1250 142750899 142750961
    0xe010605030f061608041e110a0801090b010501050c0706050d0213060207031e0b04020d0201030e0d050a090f05210c130e0f0a050c040f090c08030c10090f08030a 71
    0x12041a54600190030000131440580360341c00140e500824118a207a641c264103030030b40008466990158580c0d004010103480820110001c40e0090034103651203c24410500c8440c3e132400c0d0040c107082c80d1080c40d251b04106959110403207400354408100000807400f47d11150380c1c0650b05542c0c880183c0c000481e03600c81000e0740d9001c0c80c0c441166403125110383c654038000c1e009000d034980c2d40c0111b0621b80c01e55940c0c0c20031030400d02006040b0705056544102420f00c200c20000141c0200c2140c4034281c3e5243c0704070010b0800c642a40c06007010f848610380c1800292200c00e02640c298051a9409c007115018078411810070302600045504200c10f20000d240050b055002046080c52200951701181c115202d0380d030300c4822519001c2c0884d4408615144035042035803212041c440a9500000c031481541d444d811040b11039448030f50f8542c03004c64a441c49210a2114100022065000f0041185241c0d2071040e00703013a005003c0c3c4440400320026010b45540e800000c141206500022610300203070070400d0b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 142753399 1250 142752149 142752151
    0x1701050d0f05030a0216060c0b01050f0415030b0a0f09201f09060e030105070206061e0603091513170d02090603040606030309060306030206030406090501110f0301030b06010c0b0a0e010605030f06 86
    0x321004c240305000205240207880e80d010f0140c000d442d0b40c50a80c00c1506001004200c0c240e181d420dc0d80c0c03098441c68040215410902642c03281e0b0150300709061003a0341c6e030180d9144c40b00e880070207460202803a0018a20707983c45d002c00c2c0042c0e0104810309040000140d284c1c02c0740c1d4641e5950980d5125011a0b4940c84074411041d180b81e91240b0442c41ca01e00241400c88404480c000e01590003040071500c14580800c0410703210f000040c0207540e00c00c1590215102d500241d40c5040550b101d840804e00340445c8500040d401802265580c4800c030041d200e8081c5094250f00070003900c440042c0d404803800c10703501191801400a400c81e6a01c3c101490311034002c103000c1c802500010000b81020406510a01031602220b40007800c00d415615103407181402000994000c42d078035943ca08a00ca80d070080c046c00390260a20f021529a22903144d400c0c00301d20001c0c010203150401c035100c2c18020029206a40240d0050f603890303000905822102c03d810b00400c000d401240e81031190f552903440003e000582a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 142754649 1250 142753399 142753423
    0xf0d020a08011413150509010b0307031a090307050a06050c1e0706110309030405120a020405040318051005030a020a1103031006021006061e020312040f121701050d0f05030a02 77
    0x4655a280100d50100003034400b0b0003030401e21240c18400c6440c1c1241c000c6e1381c01810140000400d0f00c1e402c00000c0c17a090482c2e1084520444544100c1c00002540200550000901c0003844c600240c5940d82e40e111022403000030840c55895002c956043d0000040c0d40400088c0d0044400810010310f50a02c0c0e9040000c044072040c0c18100c010740074000d204241da000305100707802541440d0500b002c100120031381c40c0c103c50003407203080c0c685d40160390b0328050180118041d45410071441210284c510301c0c0342d100e4010030700421804281500c2e0325444000c03a5030100c103001c80103860b005806421501c10304a052821903d10012041c0302d035491401d000c400c21161180c00306e8903038100c200132210a40382035114920129205000c104c0f80413811486c02d90111501c2d1040da0724141c1e50304910b0b00d4000003603e041d9500d6501c509a14104422140d2500c0701e0b0b04c25040940d203070202c1c040b55150007401401600d002e00d0200c1e2852003040041035000d05655400710549840c0c0040000003562504030741c9075 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 142755899 1250 142754649 142754681
    0xf020a0905190b0a060c0501020f18010207140307050112022b0c14040e09030c0a110f030102030f0411060403060f02070506010f0b0a0302032707030204050718050f0d020a0801 77
    0x5280754000380d4403a454000401416404d4101e1030000241c504403800c601c1500c4954080004d1043d800d82c610042a907202062039001f0990f08840009213008075076008030582d100c00c1030100d0700e99600080d040045031000d180403041c802c01d4117804c0c1c0181c081c14082c1d1094018000c601c02101c9040042c8000d04406140c0170440352064600840e10b840072800032030b5400c10200014000f40005540b21035000d00f03182c2c2124a071100c9080705030700d480280001955080d03005040f5100900d040c24030026001d2088000703605604020324840500c02c00900002c00d040400c07422031820340c07202c4054600031034025600704411440200c4940103540300c5d400845290051500128501a06550b99029640601c12a90070308081c04001d500960000c2c10000074001c09040c440015201604040511445080075100310703882c5205102c16164003811a030180030b032200d41d1a4482d00300d6104d000032108100c0d00e03c2c1c04d502c5104046031003002c801401a400001d01e41020503100b41c1500300c14003880801203 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 142757149 1250 142755899 142755931
    0x30c0c0105070e0910030c1418010806060301140121030e04060914070201020f0316030b0d05011508071a3711150f0702070e0a0f05090a020901060c0f020a0905 70
    0x7040346009806000080c6a81f010510034428260440f0510706180300140c5807402141083d40c95190f02007099021810a40c404010444141000e00407062034820852071400c2d203505051002d0b6129518294502c000c0043e14134580505100d4a103164400c90f010713004001054958054101a0145200880f1801d4003400840c1140d0301c14400c9540c00340407140600e056488070080300342440011001042015258100f00e85c481d910070b035002c4000f51061000190001009019807020025580b214142e60000e05017007000410741d04408988006a00b000307640d600203080420510000c00642034010005101c0741164440e08036041c801c4807060340c0f20034100c22140002d080d80c80006002c02c514030a241008505101d030904442c903003045d003d0040c1e0711070a4032003000e510906012500310031496280c0310a03c1c2000302d07603c1595080b8008501420080c4804e8000c03e808134418440d1000300940b40250300180014401e88040161380200540d8103656140c06100103481c0558070f400b0740718813501d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 142758399 1250 142757149 142757161
    0x603020414040c0b0d0e0316110910060f09080a060c021606050706050402120d020309240304030e030304031a010302010306050d020f060901020a0501021b06090d0212030c0c0105070e09 81
    0x66401e03407089901c410071924090a013242010b40760000d0046103145500d501104d11101c00500280518040c1c404440309805034904100d4801e01c15842c0142c0246544018031030b81001190445003074820a06142c104000c101c181100c07201d50b0342d4081400d40c066600b0a204100e11a00800c83c3d0005650841e0340c00ea40130004071a00207024803c1201040c01001841c0019082d60041d96006000510390410086c008034541d00340090442d0250040e04005500503180c6003440c0095045243c1c40a8a01000301c1c408400e406444050406400c0c0b0600340743c1c80143c5c1e502001110041c40c0c0c09501038811044c40d808890000c03400780000c90109040c110080381500704026074501d1103030010714091041d00c0400503c440b036440b82ca91a411400303501c1d814004248240002e080580034100c0414400400b020301509009002d002e8140c9074000054441c03070b250740082c248003500421026184e403a00c841420092920641c00c44190a508040c20894010b8000c1510640450262480c1d03409503107003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 142759649 1250 142758399 142758431
    0x4080409061a190e03010c0305101710050901061206020c01050105060702030a03030b04020d0216050c09060303071101021507020d02060703021e07020d081201080f0303271203070306030204 83
    0x2210106000300051040c1a03003c040c10f40d074800803201c00d003440003600c200c64001c00e007503a8084130040040f07500c0e00148500d402110503100024002d070151084041a000f2555840d048010189001e042e19400400c800200a51203040103080c1e5480d254407958191600402030b42003441040e141d940390a0001455040c170404079019507030b000300038080511003540c040d00185140d07802d5a270400d41c240f0011a1100e041d100501469031003081d0103500c0c4286182a030701e40b0030700174119401a107011017800f02c2ea450000a90780c100d58003001001090405000407841c0100c41c41d132400210030f4010030b01c680035802051003020a20654255181079035000c9040c0c0517803062061780c8440b100c0604508004013081c40c080c003a22440140034513070701c2c445601d030300f003041d0444d82d803e00c0035200380c0004001304101001030901e0680408082c40c11854100722403081d9030b055440b0b04030020103480d04a005041c007407000c498054041803d1a449090010005000f02001c0c08200c0c000c9250640e460040445 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 142760899 1250 142759649 142759679
    0x13030f0b10050d0201032a11011b1e0c05030a080a05090607090b0c07050612060a060c0b0c0901030e0a050105090d0c080409090507090e1b1804030e060408060408040906 74
    0xc3c0007440c4040c1c1c103600440c002c0c00c2441c2554551108902c14038100c00001c2d400c950007030026610308500e95070200c411402c590300e551442001ca43c034401d101ca0070a81002c403003081c1004d0050918114603a03038405841d21580c00000034564040051031803251604041c015008083e031000400c0182d94032040940c3e540c1095841c9404141c000c4c908202076110a0000c0142110b51801d0f145101c3e44d440103d4025007060030215114000c14041085909180d21500028446071078503200c441d071207441b030030400c034005490380d02c02850000d603030011030340a50003010805c0f07401811145100280e0800a0082500380d543c00c50034000e181030503030043d00c03620751040310030380061055181524203451140100722561701128070b4013030341800040040c007a211b000c501003c00d4010f02038255090018280401c640030020b0f11502e245243c10f0300030404400c25650281d85030814004c030000c2c507c0092014042c55201480317900c6540100002c000c80c03400940100c50440b0380900080e9100c40034010f00d001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 142762149 1250 142760899 142760909
    0x3040309090b1c0b100b03010801020a030c081005040f09080c011401090c08011205070308190206010b0f030609060604050d0311010b010504032d08030f04170c0a06020f13030f0b10 79
    0x60103c540c1c40101d0140c0e01101d4206041d000444085070341c80c8201c0071075070001d078083d0502c0e9601144c412000d03034243c01041c18500e55454464140c0c07406111080035010306005107801965269140240ca0000e0351050004540103031000703480d0001d4005287c0030f044088c102e006524683d2000044d540340031f000b520303030317241042c0c0b61409541e00b880500e94a5036041d02c415121480713510400404a0410001080102c0101e1000e80d504070103d00064901707101a40440d4020808000d840110710380c40341038982000080f1050005500c50000003140c40c0200d0300020b5121002655000c00c1581002c00b800070304010b00001e0004c044604015500c40c081e074400500b04801007400d02c10144880540c80c009414085224110f10415460300821a041200c1603080e1503003200501050200401c40361140e0705100144030300d001c0d600c1e04134989074251110003c004640100f034a1240010710310650b0810340407019868049980c0b8142080e00365541c0d02c0039039107081c9000104101c410340100400c243c1d4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 142763399 1250 142762149 142762189
    0x102070612020d02071403031b030412182c0f04050618031207031d0f031603031b03060512010b0d0b070201020910120c08240607060203040309090b 65
    0x3005016281c0040d501200000381515800c10002001449200c41d0741081d02400c40219100d1410004d9211002c9074149599a03030309041c41004000317802039000e01d2100c40c8502e070600e455842c40012043e030034029045554071111041941c18080d4081c0108040700302c2d0a0352200342915803211078900403000b42d40c05030003034114000281c90002d0001c0d041544691131001c40b403600040e1840000c400740155022400607494445030100030f188081c05484500101000d40900c6900412031039991081e1300350041c0d1801040b52883c241800380c1d00110400442c0c1100319000c2e0084075000700101a0703405414401c21000d0035003070a440b0140302e050f4001d480a0a185078840990b220442d4400000b002c41c0c0841d9001c222643c0240c59030100812045402e4a8052004003980c0300d45050321580c040302800c02201c04c0400c10f9400040d03081c401c440145600b0802d502038450003044081c851140080c05403800002400101136002c0b40410403a92240c00130001e505011040090008414003020418 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 142764649 1250 142763399 142763417
    0x21c090203030405270a020901091401090302040e0309040204090f05131101121d0606030f0a020a1e08030f031005060403110f0a051507140705420901030b01020706 72
    0x1400c0c149094803c0848201d0b103101a03102c818407543c031030b0204445030321083d03402088c0001d25580001102015020600c202407200c8403501c0001c0c03031086036200203841681c9524036111076036421f02c00c5680e9504054015543c031610f9100e13140c080e02102c4001e0116500c0c00000441c1c81e151480c0352145194004804c0040d0480007004498080c86440111429a912880034000c00d41903500c85025660080142c0800c0c0303401d0007010b090581d200024809a08015000c40c010b0366100415000e0350390300c1403164460562640c2c5140e2102407608540014400043e0070202404080081c0d4842d100040502e0107458981040c00414042c520000b04074a0f0542c040007814505044171122000c0c0c0a04000c4845a81c1c0d03001030f141240c802c00690280a000825909000c03401e588a14244040c5004000c41c41c50030000c83c01006401160005055481c1c0800440c0307100c2c018051920008440c030801a12490503811046a0011907824046071601d844194254008a00c03a011603040b51640e081c1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 142765899 1250 142764649 142764659
    0x6020d080c0d0b041b08010504062106020f0a0206150a0e0604020901020f011a0a0503070608040f050c1503090f010501210804080109060e061003080f180a09021c0902030304 76
    0x564100c19280300c00b0940711120b406003500c0e54491406848648000140d061261000140c0b503010107030009802241040700501c5003003e0201a107031042104079410140e08514240000203009a5026140304140001c4200c00d507540082c00c40e0049807070a42c031040429942c3d0400401804a10800040500c100c00055142c641907014060341c160600641e90700010801d030480c210341004500040003401d0500148503810311502500140109500034490a41800d4000e003885000401c001c1c40c40360015050350030040240046c1d901124090308170b00165102c40461320305070b007080300e510006225410940641c072105002c0c040c101c4025010030b414600c040b8184111a803400c107400c1e03404c1c0d50304001c0001c0e83c600900c80d0382107075030190000080300c0b8403d110140c00c0400c051704052440e80d040c0003e0000c03c0044080f5241055050f950701c0d0345a4158241001c603000c21050b15601c1003242c0800038512040d50000c040d04102d02042c40c210b40c0a0840d000b04981100c500650160f2043c802884 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 142767149 1250 142765899 142765921
    0x605090a15020a0b0c0307030b040b060702040902130e010209120105101404060b0c010f2d05250f0e030703050c06030702070503030304050d02010605060a120c03061205060103020a06020d08 83
    0x1541c02400c0c0b054444141c0103441d510301012042e20741c840030381ca0020400040c581d1512848821680484043c001508800005502c5006101010b0310440d076580c0300c03108658a0304040b4407203251004061110840b140364690007034000d49903143c002c001002c040010480180702d10b81c482ca140300e8207101e500382000c203001440c071100580282c109a40b480085100144003015118141d0240000305840c02109003010980c0c640303001d40310300c5520041c0030402e0388180d101c800b01040008040024582d540071003040000581080f00200e0011503021001e90a600286a01c40c8070075907201c003408080340c2c0040c90340c5d41840c4c0c40043c02d55040340d0440c1c0701601e002c800560700b15a051046940c81c3d91500000303410340d40306030307812141640503108428100e50280196401408119500c0d03003001d00c00074010b040d4500c13801894400326950384001c1d0b06540607611980103040d0108492018036094a030459130380390203003c164030600b807a08000419070700c00500108050600e9131000c45546800304101 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 142768399 1250 142767149 142767179
    0xc070b07110313030506100902120a020d02042103090807060c02040207020604031205031605040f1412031c05090c030c21031920030910170405030c070605090a 70
    0x190141c0810000c2c01c000f00310804a0002850203100030f0280f5003008109010b40b083d1a071b11421600380107202c17186001c880c0c5283c140d4802e499410240c1e441d42020b8806009214a4114281903120061b0b8414010514010744034045d2182d21050046602c0d03405059580c885803050000003404400704000604194003d010020310140c4201e0500f80c0b2030f5144000050440c0503000021b80110401100425854611009071002d00b40b0900d8141000003810540a50740517216502c030b80300c50840a1903d8074400b00d0b5003c03032064103807600c1e0700c8045080212101038182244143d03041901244406070003007048042004004c0040c44581030704400d02114906410f000c03e40460030b902c40d0302e82c9031000d100800e0316412200d859858584000320140102c41c4c40001300195151448400e81078030340000071140d481c84200c1d501e600510120b04100c51036004081040281c900040900c400c0107000400340081d100c0e05002c4e5408180c54042c221254016204400d41c4602c00550401100b94048131070 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 142769649 1250 142768399 142768427
    0x901090b01051201080a031704030903020607020d050d0306060f02030405032e0501140a080c0109062001090c061e05160303020d0c09081207052104030507030606030303050c070b07 79
    0x41402c01035090043d001c144400d0380105c1d0160400e03d2034104259100701900166400d1100c0d0304101e0500d924010401d40503804020b000707601c002021300555481d40301200e12247e000d022601c181e400500b00502030302c0b01d4840c50000c2801000c2d40106203002005880903180d01a0003019402503031000404081c40c40c0c0e4407a56100100342243d40302120500402c0e02804d03442c05003c2c0b58055042c00d2000d080c0715507201c03001503042000c82845a03a8000e924070112000c80c9044a0f041c903217021800114a60700700403842030340c6020036401c104140b6170740181c211541900ca0300240d00c00881200b03088146074840d803000030010046400c06441c8407980103a0325001c1e1034014101014986500700b2912400d121070042104070b6000c000d01c3c40208010300105005148c841d0602d10169135041d6a4000480304203e580c0d00c03030900c2e1926091039010b4038025034120b0111006c0c1170352403d0420040480d808240d0003c1d09000004058515250444a240f42e0110484025554580040b920f814040c103d17 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 142770899 1250 142769649 142769657
    0xc0503060411120907240206061203041e0305060702011107241802040c031a040902040e07060f0207050f06120411150c010b15070f0f150204150e0901090b01 69
    0x2d01c0000d0b4101110702486000c4e0440102102400c207035202c1c024400c51443c503001c5d00d94012284c0d0441d50301080d06604803400360342c016502849402120b0075030046800480c1a09101813654080041128444084034012419a40c054a81c2a4120300303035a05507141c04c1514008102580015000381c3c9c2c050b030080c0c6180c1001100583d010300c00c0041d115000c11000e496054501c640f000d510b040d114030103c02640b4182088050300040300303010140c510b03051044c030860755411200700f9512641c000d85018844d0303d0642701aa500c9400240c004106041d5040c0188100c00000c03d090a00c201e0900482d00024003403070a0906210b0f481d0031009000b0012203031100305c00ca40d0841e03a00ca000e8080c501e103002c20200c03070b00e07070a81544030303801c4804c0800d505100c0e0901148200002c1105c7d000c8414aa0300034400d5001c6c07004904002c500e0040c448001044110020102541d1640e103034050020340e010240708004400e106602160714442a03500160705c94910001000906c0440d0302c40c1d61000d0041c14 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 142772149 1250 142770899 142770907
    0x9060c0503130608041e020109120618030512070c022214070207080f010506060304120215130215070b0708090f03120906010f0803090d020409081b0609010c0503060411 74
    0x312108009540d64043c07404a140d09090004002c04c04040840c4400301e440aa54070050a40000300380712024402c0e6600b40280000490920481e80c000d41680c1c240e0f28150401142d040c90000c085510001c52039400010f0302e00880e460902c100805d02442d0380007004181441d40b08042d5035159403240d82661642c56449110003c1d9400034a07220344248111740140c2882480d1240301070424070200340440403645000100403050f90b17900c0c10f0302d1f001504028100803004910750305900d480d01044001e01c01d2940003041200c01c2c102c903d11903280c035100741c81c100201c469a69460383c560280c41001080760002c00005080389119450456018001030211142621035420782d509560001200c1903a034a00b200421140b41c00401144c0d0050160041d60b142680c50312410035141e02850741c04520407014070001c0810b40d0760b1601309405890300280102e649100e24a019002d032501459201e02078061000002d01c500c0041c40340c1c0c1001c25080e01c48500e166210400c0000502c4d00b042d41d0a0034101c00e04c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 142773399 1250 142772149 142772167
    0x30124030603061e05010b040503060a0b01030b06040905061008060d0f051f05040515040507150302040b030c0304030e010e030d031d12030a0e1204050409032c01080a0c09060c0503 79
    0xc021601405491003412a02810132074040b4151041604159041c00c41040f08022a07280080c3d010f90080c502440011505022801240688035030900264003920204004c181802c039a0302441c0652001c03190314008080c041c4091b0340c440c40481d170141d03200e1014405c0f034002c120001e0132034503010b20401c113452500c0c0c00342042207140c41c00d8820b19410f0545c0d07102044200001007005502c3c003100c00301000e01a1505644103940c50100340a0120314100c0d41c208000f00900a4050304d02506515191544a00e0102e0b28a0442c0e0821101640020010420880740b9401054501048800507010701401c0c00058019400b600c080c0001280490504294010303410080c8804c01c24107003050745c40c540e42e04190132160251080c4014080b410b4019000240c4450f071801e080f40c084a03815540410006590f043c01d48500e241544038001001240b4210804001d2049041441045c240c9801c4003e45035400034604480c1c4481d42d607004524100028040c0c640900d4810384028400e0003202d10b0a82c4013 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 142774649 1250 142773399 142773401
    0xb0606070203280203070f050a0302130b0603070c11090609060d150c0206090f06091005090c03070920040803041205100e01140f0702060129031303031103012403060306 74
    0x100320040805401003c07001186410700030305000b0100d0802c1907400509010018042d450300c0e20000740710b00084200440c028403141c01034501c0e140020035083d102d152404002e002120310305011607000d20020000d4405280c10b85255000307000c003514072101a90794805004241c01c1611081c0c0d0b0b07208201c850002000854010321002d031996a000e0000c6003400300e00030345803409480a1000e20f400020802100410006001c0d5070340d00c0344030b80800d01d0b4445040990810900030304040e0140651500800d02402c140c02c51600b1104101e150301d04009030055006481c0a00d0052000f56042000100000e21414404c1080180142e0945180100340444801200c041c545105a6a5145c0c0d01c2071700311b4000302c0c2100d60310072007160b090301041c44c0c040c50094030b500c814010404c0302c4008203c0e2074109080b20f2605044588000003490703a07401e0080c0014001d0342c0700c0c030b404c9000034100040114803407200c4054030304a60842c0040c40c0e0b000c1e1107514040141100a118008050f602c0c0c4000002c00c40b1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 142775899 1250 142774649 142774693
    0x9010203102916170f030c07020d020306090114070309030c0f23060403120e1c0908030403060b0a081f05070e06030c090405060405090a021306170709060806040b0606070203 76
    0x1200c041c1c0008001d2501c4c20384ca000302811030b01c40c1000d01c240840ca0a8000c0c0303500712a80440e01e480d0043d511038140c800070354100785412000e901403050004010120205510002c480c18042c9407000b00c0b580d501c00d0440942d241c00320000c0000c0c407080700d0b400008216100c520052845000001c140c0f450034a00c42d603d06010000c0125150f0082061000703054001030440711010480f907013441280c01c440c1c05c00da41c82c128441a200305007816803258058620420b030340e0014018820a4990350ba98a0400d003016101c0340d04011f01c07031103402d000098242c40008040f59240c10710540c07980c950903801805030090000078441000d00200c0380c04559242d40f2007000390300c40d8450040031344e11414101c00b40300442c0c5c4010201c6005038a8141800790400c400034a003080242e0460741d404903420038070341e000082d0440c3c2e8071844e4001c0c046844040b01403400b1904106848581d134080110315a00c018140e0380f98019280500014140004500c143c00c00e200180380050000d030450f50b058052003070607450000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 142777149 1250 142775899 142775917
    0x91504030b0a02131511100e060c0408070612020c070e040302011a090a0b0105070816020112022703011d0105060a051f030506011b0503030a05090102031029 69
    0x400101441005030401c9056000a2005000c40c188200d10110100ca180700313010304465040b50307060300e00b0410700c5000d882d00042e48a80684d8a10080040d13004041d0201c283e00000300e004080000700000740c40021344045881080050644902e840002c0d200405180d2816001d26000c200602001404019001c010b2840b0440d03074229180c10f09000f421120641d00c100d10300c041d0440011042d1f500d00d80706503040342d42d82100241c00340041707005035402d1044841c02019654089106075000c4094462401c005000f82ca66500810700d8264030381c01c030b02c41c2200030070b544400341545041a1144d0709031299044006400001c4e0350421902c4642546d000c610400b007a60b448104006040c203008001c3c07001030000b9910a600e4164801181d8075030b41100b01e00904143d654130029085130703c107009920f881c00c03000100511018a905042d9203a60044400c403001504100c04201c09034814801c40c2d201d00500c0c0c9843d1032490501500c00c6070f00592900b03000c0040301114800311501040c3e0000e0034592 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 142778399 1250 142777149 142777189
    0x60206070f03090203070506090103180b160203070b040b15030f0606011e020622080a0504030512270301060f12020a0609050913080f0f0d06080f150c09 67
    0x12504140003000141c034401c04904042c01c0940d030750f00503140021000244c2d10102d844540f1a500c000c012030040801d101e416042c552401c1d400814005040213442c018801208038299444074500107a90b40c0c400c40000030308070562b200008003c03950039031034150008480601028003e0001d400a40761105010311f2040395002039090005a40c0c00044045403051074403050105c64860b000b0184d00d030341000304140d2040d241c1821080013074402d100b400554aa124202545a9640101c020820380007030104035400c0c4a04940b118002e0203090585030703548042c681700c041c00d9035001010301d410b2030211030240e0999200c440c081640b400c2540f194001d85500384010800d1003043c010800070001552200c024480c1c00181840703030340c403400303c05588120201c05c141c1e100903c5207401d501c2841403580403d49000081250220882004028101c00409000500402d40c640314820f0301c07000c004c43d5080080d8840344191058000681e00aa481680c03500f8241c01c00c0300c060007250101011000c04031846d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 142779649 1250 142778399 142778401
    0x30210150f0b04060c1e12050a08011e03170f0708030f011e0531230903160c0f0609030605160e01030c05130605220602030307050903010b0411030603070504020702100e0d0507060206 80
    0x103691040204bc0146070282d0b04c0b50b41150315154404900c80b075404094460002c001140302d5061034030f0700300e5600c405040611035440c0d1850400c401a50004c0c0d400f001004080d800000e440802c070b403050192007070b131019400740640c9010100404d04008070000140e100d6803c5207072011108000c483c00e42c0c115918004aa60b50143c2c0c0c80845031009210302c0c0900e2039602050241c01040002500c00d544071070303100080c144084e8102150070a0540d40299190300a120001c1411607101c4201422a446071005100c59150002200c0d4038039003608001001841c0b283d5100e130551b100303420a03d10071105080040c40c0c10a0204c400350b092059400c804045100003980c1c805045a01403c0c0003051104900c00b03100c00c0c02d0400003512444003504010400002140b1036003259000c1d8009124900300500800080c41c050030038440681084858500c01e014681c400a51802c140c003c440030940d00a005e03070b0030311034400020b641007a0382440301c94200c041404000009030013001180080d00154000b01a1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 142780899 1250 142779649 142779667
    0xc040e09010902132c1e030708041202150d140c07050a020f0105040308070804030302431806050a060201090503031807050307030807050d0906120504030210150f0b04060c1e1205 78
    0x4c0500b202000501071f80c02000101e02280c4254151030075210144d07080341c0e07010428000034034201e5034181441c51542002420742c24815541d03101448542010345803803100d03a20321503d2221070142010240c01c1c3d80010506000515000a548490b018141851030402d40c0b030fa00d64140503082000100c2d140345001806205042d0108008401ca01c034408000c00c10031107082505032010195002e4100e050303400d80d40e24a03101502e25107000580100030840d500c14213030952400103882c1c07030320807240141100030010611900c10300036100e00f990070030000d600d9501c81c004512078916070b01039140042d001e540701c003003120350b4144029002940a00070f0651910041c3c02c0143c18081e1600c00035007401010002000969001001c8058400070030000007031035987e604041c1e041030400702001100c645440c0740640100c644603c00400e80d180e03140e4041840d1303201d400007030042c4154050700010440d0400d2940025401c40521010980c2071f44148000b00348a580d00060118941918004502c0204407450 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 142782149 1250 142780899 142780933
    0x102070909031d0a030c1a07060212190e1911060a050d0516080604020307120e100f0e0304050d0804080717010b04060302100302090a030206030c040e09010902132c 72
    0x449003c04407824181c161542e40c6004040314144100210410881800c90403400400165801f01c2e401000643d50740d2160f003c40081440e0032280307010920056580c031079500c0e4841c892442002420380090040b107100400f00701240d10002811035040c0e03503900d102d643c55111003014082500716911a03e8a980207800c2002c00c0e00c900420505905202010414a10703a01400e66908040c0035100181d8030345481100310351400300c0400030745100d414421002d41c50740000440d000c43d81d6100c03200b0040c5508000c455410741e031205034624083d50041c801071289140444100a200788100c0d1602d14155442e9007807814090b05601c030303c403c514400c0581100000a0180c2804110200ca0404c80d2078156800103504116000e41e61003010390114000c0d2032525803421280156030020280c0e5100d142a509070062a44280226103c54140c00046190010305000740501244c2c001e0402c0c04404030311045c000204003004443c2c511481c1c51158865103042170095025483c2501d016000310030803030000e50 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 142783399 1250 142782149 142782197
    0x10209090114010f0c1e05030a110c0f190801110409060e090a1709090a0b030c01020d0203030103032f071707050a030b061f03090b070809100b010207090903 69
    0x800324810300007020b1140da0303000d181c0028003815130810315441c203610f0a181c000014100208422082a140b50006200000001d0101c11040c1e070380d05905442c00e804000d44036040201183c0d04800e260400a41e94980b0584086490078200440070f1440e030b44029190070340740d40b8144031411400001d0306202140c864000c1d000507050f003c42145140c104407880954036a860b1901811191100d8005164100b080003150000c0c00000c20640280c00d044003000c0040c509503035918407a100d1208a803505500100c0c48080300c44982d0040c609507840c644064441d12010f02d00500c103074034000d000d40000903c0080c0b0720b58249002006000c02c3c0e042c141005041b0001404022066214013801c0000d0340c1d940c07508205580d03004003210040d40350640851800c0701c017a10010700344142c0840740c4124a5050f03011031105030091010140d5616030902c1079810300030503102c10308a0781112074201006030b45070300103803418041071041b40c0b9019504c9298004039004400110009149801c0c0d15015079201c2c404c81d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 142784649 1250 142783399 142783409
    0x3030801060f0819020409020408011401150807120b041119050414010e04020c060403051206040513030c170316120e151911040905161d060c0703050102090901 70
    0x103903907060550340010b004042d00130551040643e441e4501c400c4211150117450041c130f0301d0030f800d644480c0c075806980d000c3e002540f080c1d1030501200e40002000c407602d4010043c08807041d1102e8005840e0b2510403500e080c000005140d841d9102c904080e582e07112441150320107060740c18166242d07010500c000c03800c190381101c1041042420320050106100b00b94005c038201d00b0034204080810f62000229000e40240390160b00701d0b0050344104424150044010040846562200708495450404000c00c851702950024807042002d000c542c0040c0c003801e8449612805441401031595080c061511103620440e80000111001049250b01c150040b421104002030b1001c2071103900e4800a01c030760385001ca0207014a130300d4403140108240144a420000c40d024410720b003440058021054540543d00912942600e00e26203070000300d054100708400480341a442c0d442d90440b000c005140355150111041d0907500a00400030030108030300070803902c0015031060b0000f58a850610080101000e016071003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 142785899 1250 142784649 142784657
    0x30515012d020a05010c230708030f0406020c06152704020907120905010b0111030702130b040f14043f090503030705070e1003080f0d020c160303080106 67
    0x40508250741e041c201401c0c0c9200a059560041c50403908a00d803022012000c2d0195181001803290036500a003060403008424058029440100e40041341910031400b0103411600e0900208170303a800c000b400b40360002d000b41000350621419110540c20640c007078444040c21032032031010766035900704142c0d18080c40c68590038040481c216510b5000803840300030701c000d220300201e238001045540200200d40050320908803c108526a0b450494003c1a00c0d040140c04aa900070b0f4580203a800001150300e000e502a020a0400c3e0b0b130068583e01070000c0030107966005465405015506a40d032141040404030149010218201814040400c02901540840300301241100c0640075041c006244501021902c44c0c52011210a5040b1102421600400c0e414000061040c013480740000e043c0040d42c13012000f816440d01c80840410020445100081500b13006001c02c81500d00b158014081200b02d00d0300162406415560300c0f8106905c1c1c001030061118030071414000d056110079114050005410 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 142787149 1250 142785899 142785917
    0x810051005030304080c09071106070905041407021f020d241508070e0f1203070506220212070302090f090609030a05030a0506030a0c15020f030403020a0b0f0c0a0303051501 76
    0xb042601e0354006c2103814003450240d000309280381d2040c0042040040448141c800905105500034a10030040c032881e44194102180c011404d41106d110300d000c0c070403540042080302d15040c8038481906100310b1840700d0036424080c0c0503105d02e0a000d007001401c0704110308800814000e1003101465101e4000d0b10041c030a42540060f0705401c6501c0715002001400e083c511000d8420000707600000310010150450058000c0070282d00000020f400b8051244064442d50359580c0301c80c240000900c4011480182c0c041c800d0800b50916440080d1541d0400050b1400180c0b030340c000c102182400c1e0b0340c148640d800d1008000d0a12403c0c0030050304500b140c0d000c1e620f8040d540400800c6400041c040b44034587d0b4401c0414002e680c10081d014034141d01c0504e814181d82e0300c803074103100c202c11441204094000c00001c4030785480c0100840e0700390b80d03000745009440e03400c000e00d28802da00011b101c8410503104009607165447d003081011400d901c20307900070072246041614049510214003030503052110b045 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 142788399 1250 142787149 142787159
    0xa17070c02010809070906031a1608060618150a11010501060c0209090c030d0203130b1c180c1203090621050a09081204111512100810051005030304 65
    0x98540e4030081d409181070340c01c81c2c4039501c115040100325031000403070030300d82031700001085000051582582d2609100848698407480e29181302203035120b41c080011352510000341a854640e01a198140300000c4000c0304002840202c1c00e00901e201400418640105403508070540c0145201501c450610007800507514022015003040b51f40440284200c8000d80041c2d00c0b01c000b00406250300c0700080c2122800c04c0d0909001c1d440b5030024102880c141e07055440441c580d0111800c855050880494103121200c94410f500c0c01448005040d003040c5604072011801700300400d070584090f244511040c1002c882c40c3c5809003c5148031f030300403814090700c1074151848650049a0950000003880c02107484d03603510581c90010002c4a03c024075030003020400c070025054032074003180320301d1007011521242041c000801030000100c40316001c00000411440300710100600d24a50004000c4804451494480e0145410b14150741c0d41c4038146652030080000300340641c0d044030010301c029005145060700349 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 142789649 1250 142788399 142788407
    0x405010b0a050901200105070c02030606010c0f0b04141005010807150c0201030b010509040204090e0106090e1b03070f03030206060a0b0901020309240406020d0f080609130606030501110a1707 84
    0x8121501c0c1031018617034601000701e03420b10b02c4404243c004002040b09181a11001e4980030202d002a8000c0c818000044c0030b5502071280c104141c0c0d080384001030403405d10344d0750700307441c00e0300800494040701181280d81403902d00308030035a030480c074540e0301054940c1448143c0d4584646988017007040c0c3c040c3d40385e90200f1a0050f14800c20550207203030104109907500c0061320030341305800580780c106100107000a0045c0150380b1800b12007130104003d000c901d680d4481c0000f520a810000c41c0a90082911020b45400c0d2426510085002a040d500d110359112034083c08103807180e20940268018400f001400c1c070b80203251300007030140d54000a00348451440000d40d00c1c014040464012a0000b0070a0494444030b0080d281c40c130340c10000d4070342e560340340d100003510780c00842190f00204980b020b02e400294040c800e00d0348660b01c00742101643d0b0380e52001a120358869428140d03441e55a404012010234401e004100000c4682101d803036682d0360f01103000b0311409a98200d851006540018801007641c8 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 142790899 1250 142789649 142789657
    0x40b0601030e0c0604090b03070b040b0405060a17040305180d03021b0d020406080c15090d0305030a090c08061e01030b06090907090f0504140f070e15041104050405010b0a05 76
    0x1c0c600000d2039403603030008a142c02c0100f402d007540002d0100700001c170b114058210f490642c0059050310105650368440c11a680924010701444620510050203c0d040a0026203a007820902c0d028be040c4840340718891b802081a10140c001660001e2190142c1c118009045410841611060701010070b9440007034841f050116450340581035103440e10000d98134895440e402c0c1d034000b401080380e6640c0d9a1519940c8a5003241c80e8018000c0594042103000e908094900048000e421045003003803560301210594002428030240c1581d995014000c035500010a1003d40350900040c042e074102201205804880c9101c0d02040348440001800005d0690020541003075050f50b00b03900f2074541c1d0441d603081440680041c018a880c18010260001d0f890f041140658015100c2c0d00000030343c0e5011035151641101040000c2e40b242004001039a007a44207640c2c0071010049280c2000c1150707000401f41c50500380407043d00c0d40c010406000070300c1d0078410503004100111480c0d2410000c3c00e40945540a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 142792149 1250 142790899 142790911
    0x62a02060f070903020a0b070b07050f0f0702060403081201050906060a02190830070e010f0f2601030b090304031e05030714010c020f0106080a0605060604050303030f1806040b 77
    0xd00c101046582c0e005582c418040c3d90b000708a401c0890b11120a0b031400c0d0800e03803096407090f40d150086200107020310112450504c040c0381692901e072144654441541c4040c1003240c01100c108000404201884060003680808550f01c0c006545000e0401c0b12583c800ba10692140ca02000b098000c550009107420303940e101800c03d50304103241814240701500404c5001043d51241042209120f0310200f907964071403101d201c601200c0c0e1110501100c22047e01d07440301e800b20390714000441c1000c1c0102d01350503c0c0c1c0094544030703140c1003c82040d2030b800f000b09800e14200806603c014400c01c441807810310780c00150308004500f0b09186466507442d40840b00b00000408880c04801814000d06104662a02c3c0c1c2258414010042e2614038034000d0a142c0702081c0140034940d1481c199450601507031007103485803402080f009560b03890b6200141400b400855001c6c1d810132000036180c0f03040c0040c2d481842601c0d5000c0c800e02d01248901d00061060482c01c030f880c0c1200c8100000079007609030040d0481 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 142793399 1250 142792149 142792171
    0xc0a0b040e0603010207022e020a030c08130b1b10050609070507050f010c0c150603030203031803040512010c081b03130f020a14011106010803090613030f062a0206 72
    0x1803039842c0403a00a10440101075000791000c210182c0441c411004120002010440245806001c02e41213807126003d090060010302440000c80c00702d8000b80c090302d9107071f005030b44c0940c400b6030f55050015540e01c00c0640104540c1c00c2144101014800c0c08003081e1502c00403c2800316251040001c0c0f0100001070404040c400041a00c0040c0b05003001103442c04030102000700072500a0300303006404c40d43c10f4042100d07001000b0844a0140901d805000200c0e03606400642c19503e0380303100402141200da203070174250310080c000000d46581c3d0503014801c0c1012040001002800c10500800e1120000d00d5041a2118202d10b0414490820100e0380d100152507030499070a01039180c517840d50003001d00060352000640d480407402d65296520211041c000340c0785c00301601240400d80b51a040e0900c6000055041400340e060141050002032900a00a0b58040c1700ca5171640d4a07001c03400d42081c0140d868664402d100c0200c4071041081441c0c000c04000d640c1514180158003e54807800208404494 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 142794649 1250 142793399 142793401
    0x90b01021219090308040305060402040507020307020315060f030618010e160303050a0306050316080c0a05030a020d0819020a060605040b0f01030f0e010905100b010c0506010614040905040f050c0a0b040e 89
    0x82e407080740c80d03101450348800c450390342d151340782413803940d42da01070300c0980c4502c1c034002c0455171481c000002c58400c07a038040d020b007070329030760030820541e150f00000c00c401d400446001c47c544035076509022052191311030000702d40c02115064086402c58170350040282c0140e100004001c12a0800f1500c4000c40e54075145c5103a80c0d031001c42c0218003400d000c1d4842754061007441e201c10403250760341e0460390a6680b01d9048800300f41402080251240d070a10400e509a006203003108094104040d82c810401c1c01110140c5c6052405d0290641030211f4254640068100401507001c10032a800350400400040300c040c0290401500019402e182450003c0c1c107041e80c0e1815266012940d82101240881034002082504810b05106440e1031102e540890f0280c9080482e0040c0d6000b21400c280c20744d00b00000301130790780c01d064082d03803003180d0080904a115410300c0009401501e50055910907407080e40030314200001407411030315101404100d64450140c80c1c0c4240400d52020050f281142c1c0410042615 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 142795899 1250 142794649 142794697
    0x1802010c110d170a02160b0d050c120103030c0507060507030503221e1a040c030210050c06100e0f160c020111030a08010302030d0e060a030c030b1207090b010212 71
    0x18a200e0590014070251a22071940000742a20014152413030860b001c0e01d01c070203420701c075984d81202a0b0081c0f0500320301c01c0c0011003802041d07502169201404e60b200d01d192070900081c00c1600386090f80120002108101c1c80410000d090020000174540b13400c0680c1440b07001c0c4d5003e011804024501d6050020b6200200680000b000d01014040d1b0850010b500c211040700c100e1b12040d500c1401644c941c0d80600b201106e08038100d444602c540c1c0c000103444002411a400c01180088031086001080002d0107803c105070f4051113002d0103490070149608541c0c2c81c00758041d42d0420020a00d0050000fa2001c005003480b003051109003800541c07810060503d02c80c40161296190303060035848601c000315404010981111446040c0d9000701d04072091300442c0c0e80100c4613100c070303013803402e03005042401083c07580c0707010380c0140720717404a0f5090104644144001045510b12191f40b10602035121030007c201949161203900705c514401e10160800f54206008a989031040d17101c2c200d005141c80031030003c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 142797149 1250 142795899 142795909
    0x51302091f030c150e03030a08040206040e1005040b0d050705010e010512010b0304020132070606171606030e07050603100f03050f060705120f1521011802010c11 71
    0x41400c49040303180c42040d03128101141c1c0c030340044c011020940d003a100d00c103841d68040e42c400c0407000001001149403203442241102d0004026200b02d800c0361003800003185464402900030312801b050046002c0c02464003080005035490b01c42d45a0240300745110480119074081110402e46900f8201000c1c0440c2d04001207d5610a564520b1280c141080c004680103203000011130155000f680c1c3c80214010113481c410a80104801d02c03944803002c00c040800c0d102800003c0c200e501c4c02a040040c00d030340d460410350380180700712203142c000e0b4210f000c80e0800511480b0307403200a04903500d410042d02ea000200030365690740381e003c3c45200b01d00c040009140c1c9400400f00c40d010300000f4160101443e0389180c015a260040e5450040d60700400e80040d0320184503c0a40341d0310090a000d1242a407039501c41103812403030151140211051080000c0c0e003903201c80805406c014810031142a280d0364400890342140e10291107600030030003c00d40100540e80c086c041c01c103010f80052507035000400d03401c0020 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 142798399 1250 142797149 142797181
    0x51501030c12020412140312070c020406050a0303020d1103090303180a0302032509150504020706060e10090b06030702150a0e0d05030103030e030d050f0c0109020d0503040f060305130209 82
    0x82c1a140005008545c44610349103842d4000e109401c440801444155003584178000c0030303d20980340c0c00c2880061180c510a6090b100507500150002800a441d900800c602c003107a0381081e0003517840b03007901c00fa00a0348610080c81002d4000091030038004010700003034072841400c806400d0344c2c0d4420000c0100c0d507a44100400110381c01030444104029400181004030ba085a0382114030184c204002000140d5014260400c0006080c0102190814080200a4000040c1034030720b1a40c0e4000810350b42c4035000024001c842101500e4410b03072410b41400c094a04002000340500414802e1020898002502408940c68a042101c1c1030380c0300703c1e00710010310342680340980920030007010460080c2c0280c01141a0f038002c0e0740d202620b03100d81060644e60582001d10b80c002850402c01e450039000f090b00079004800e07003c00046803043c690b070005a818150704106880d242c01c005000c00c03507107091034500c00c028021410300340103d280a0505004190081c00b0203805600341074005410400c5500d004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 142799649 1250 142798399 142798427
    0xc031213050d050f060a0e07030b070c0c0608151909050c0c0307080306100305040b180c0915040c2a020d02040c0201050a0b01052a12160507050103051501030c 70
    0x200b507458105003081070f034032802984000560300405020400d02c1c030740d500428a105403000c00911269286585000d90003000030980d0301000b408000010000e03408460f0746006080c1d0340e541c1078031400c1c20700d111882403810380c1444c0d1207484103c0e440c50003400d548a086084038410031001505680b58190300b095442400100300d007a0000140d528100512200514000c1000b61440d444c141e420031415002c03544160313000f405502540001600c5840108840340303189414109449c8482013110110308070359015105c1c00e000003001c0fa07a5420038200b034820f21800031998030300b001e6417000c2c0202c2c2d184c284011050301c01215000780198000d54540c40710400d0f00b0341d806441002000c1c3c030503500038028001a284050003509014400313985602c5801a9200110866802c40503a0075804103a00b8130321404e50305400710b00850078a410b0440d021009401003046507000f480300104546007060801c1900e0700304070f06040c504028044100a80400c83c080410300b8200020030402900d410b8912100050305 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 142800899 1250 142799649 142799659
    0xe090f0f0d0801090504050a111207030507090e16140a0b0a120606020f0d0e0a500f01020a02040501090209030c0616021005070b0703020a0f020c03121305 68
    0x192100c000400900c2070544400c56030b41d80b403aa40c032000d500c82500d20aa030040c01e940e0240d9500c9010a500c0c0c02840410b00d0020454420b00219070034035420700a156009035602c1c0c001d4402081a640035005100441c007004d0081c0c03d0207101400c1c501501c4056006803001d500100e080d82005445a0100902400010003841c5d1148211755009000545403148000e0803407c000c0001030143c00001c02c20b01c0010304401078404010100340403203950042c4008079a000b62110b0b0300003a680031048401c02d240783c0c811503c8003070f080201000020b41002e10141c00e12103145c2c1100600201070001100a600000c585102036034420800407854142966806507005141070000a2128140d600814405030103800703550304961550104100d50207000d0180703084100f01850100140b45c00c0d45441c45920b41341c10014240600368071940a80c1101b1920070010035400540c040c2420740081000c89114014070040c00400c100c00c002c00c3d1240310040320301c4c4e01a003011400740100c400004900000d8400500 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 142802149 1250 142800899 142800913
    0x106140f030a050a1404050705040b06040302150702100206010501050316031b09050a120803010e0903160b0106080906060d1b0801020c06010603050f040b0408030c090409060515190e090f 82
    0x440000703220941300322004038501700c5140044540e000403148600d4214000d01101813600d01884080c05100c0500c0f40d106000b04404030050b9103a06860b020340c9101c11030291500018810711004a0a800d0315005651044004228503a80601180d41c004c5449150801c802c0c0ca0040a4001d450b41c2c0051001c0310340e21a4150f40c03000d43c410380000441e5000c80300c4000143e600c2e05141d01881f601400030349000e8040006009800d0612201c94101e03120600b01e03803800c0142e950b10b1a0884d459107045401a0910b001085880da0184002e900229132074060a024101070001038010100e440c002010b04400108801d581013032000202d0083c20b100000f50355a28442c650251100000d00449022074500382c04207413200541d0041d240700d00d0b0322034810318590b1125150100f250300000c042c1e40c1e0f40c00c0c040200141baa1100e0142d24907140c0b00301d0002c00c4030b06000c4c1001d1124841e000c000b40c094860340d0061040ca1260780b0800742224084030700c02c1c0483e118065428205484e413103000c0042d1007020 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 142803399 1250 142802149 142802161
    0x50f210c1b010c0605191a0109120f02091f0902040b070f210c12030b0102030d0906020921010606110c190812031f0f05010f0e030f10050a140106140f03 67
    0x9000c040400080e11b5080164048640840e03808540920b10b03e400070f4050103091003203074581075000710380ca40144080188840035500184d98242c084400c034021500d50b024988110001c09010000b070218180700354200f904010784240c9600884102074940c0c3d1110031010f00b80b028a05003c54159000d1011000840c0800700c0070313007001c20940040380e402c0c0a0281040c01c1c5440780c031072034054450580c0550f1038030320071482d07440242855000540d2a15400c1185000701e9607001e1008004d0150703540d03150240411440c04908489050340214288504002c0b002c1c030a0300042540d42c00342800311001032103402182c0d2924100f0302260405a50b52040940440300704840002441c862a181104101c00020440b28142c05c400c00744541000504c1c00036040c44a5070040400d9011205949040303001446104006840c282d080f02a05c8000d4000480410307614500c1d02034960700140031721040c00204040100b80c00d813100140706020401103508100e942e0384030810704171644480c444420315101e0800c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 142804649 1250 142803399 142803421
    0xe030a0905040902010905130b0a06030f0e0a152705070302030f0a020102030301090209031906020306100504030803010306110f040906141f120207050f210c1b010c0605 74
    0x8084210100320003040000391882c140c06640956075042c0c2d180c58460307242034248889144038007000c440310307070712150310442e0b54440704034840081445d50341c00b1500e003030016250b00456900c021810f01a401484895001c80d46080444a400414160000d030a441d06244098180f903010043c2d00348510600c01002032110016251054a008030309440c103191700e0700403140e511200040c00a000d0781041c801000921199400f40460300c4018060302d80c10740c000401c00c1c0349000e1280d821030301c0540c003100b44240d41c140b11064101b00040d03030510a140c1410354544124a0205100040c0b0032a107407111101c400c0011000e071040205241c6a5640f2951106090340140002d4003403180b01004d100800d4041d031400d80384410070500103a2a1001440707000c10101c2c3c1c0f00c06e04910684005800f00009400103008101448800c0d80349405003d1128a00180e01003a550440c01180c421105200c00520700102003601425030401d08481003030030360032000680e004d29806201030700799480c0c034080010040f00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 142805755 1106 142804649 142804657
    0x30f0903080c0105010609140d060b060f030115170c070b1510020606040b06120703090201030b041a01020c06130621021611030303010e0c07150e03 65
    0x140d449001e0030350b1041075006410b80d55100104140f580c4941441c01404061600c050240110000981c03054112500034203450f43c1c2d05090141641c84c0803c0f10090140784400301c0d02c941c2c0d504201c0f41e4a40215110343d001c01d883c194190b20a00c00402582e124201d203091482c10107405484028280e500107000803068954035070800744598070b012207800111002d600803d404d10707007541400241c0361040c40e40340c0070744000d128800041c110920a40d40c41001860000342c03101080c00100c6c040c00444070019045031505d40200800d00c1c0842c0030241201081e0202c03441802a1800d1001510801031a0418624040001e01a40c2d125041103448181c40c419008903528100401e04104d911060f100074062001e804080200040030050345032481e4210060b50540d85454800120018020181c5428490010b80031080000e003280441040800000c20001101400c0e032007035032540 = true := by decide +kernel

theorem cover : BRFrame.Cov 142625899 142805755 := by
  have h0 := BRFrame.cov_init 142625899
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142625899 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 142625899 ≤ n) (h2 : n < 142805755) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
