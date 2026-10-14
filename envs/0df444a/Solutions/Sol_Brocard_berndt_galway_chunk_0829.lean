-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0829
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:02:00.131636+00:00
-- url     : https://prove2.me/submissions/00c1eff4-685a-45bd-8030-53447def089a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 148920863 ≤ n < 149100719 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 148922113 1250 148920863 148920907
    0x150a05010b03071205070e100f020706181205010207020604240c080d05061809010902040501080703020303040302100201060f0b040905090607020715031b03090c140d0609031112 78
    0x70082401440341150704650301005111070f082c4003240315681d0003005c6901c1c41020242650080c001d10141c8042500910114070f05034180c0c3c2a18250b540b101c40944030b10a91540008991a000e8403c0010040d0380201104151042002515204558000038490342040d08116084101e90036030103401d003264224500c0c03e22850404146070606a102c060030b5001d50101c0c140310035242d1000500f15030300c40107a8910607031000d50403c014142012030500a1203071000c100d010b14500000030518440005008049950017030007103181c20b0840d824002c0d01c0200040c1202990340300e44c0301142144e441000c4102a101c80e034151078540740b50030410710640e0405000500c56030010018440841d40c08640e0300f0a444400e85541c603d0407141404400070420f0b032030310001c0b084030480c110302000d50681240c04641d00503905040e0058864105008441c2003038002c55002c0c25809070000011041c4c0c11214105000781010f0504201d19801903081c100c007a1803810361500c00203038501108220710200221 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 148923363 1250 148922113 148922129
    0xc05060f0a120c0504061b0203010f02090f1e0105090604030f03080a0506010c020108010e0603160f080c010815090a020904020a11160b03010326070302010204080105070302180918150a0501 83
    0xa46840500c0240c041c0c8030f6409028201f201c100300c1155000f0196a00001d01a4040c008100c9030b1444110304c002500700d0400700744204120070a142851504644c41c049000390400040e10030079400d001954513074000803546421036000d200010226081103185680c11b406030310341c01e4040c58044050000c489004140a05201c6040d10035000350340c0c0300041505440040c0e03c003c03da0b03260200003d24028040003440d07075004070014007241c106405040403041341c08640c102c4201e111200e00544451400f160780d05400741d10b1907491100352400c01c0d800f50300900c04c0340c0c0041c940310450012070180c0c4d0081c8912004115462910b0075691130030045580c1c00070140340300c5944507040003c2070744c0603c410b21000d00b0790100081c11489082c0201c0741c0707060070031042c0509540c448551a01902039085403060f61901c0d4070300300c0080c0c0720728002d00807503e40c2e003000f01c005003041e04261f0410600b00e0b030191945280d400d40701d50940710400304000c03a1000c500100303070710030703962a00c5241e82c4240c900580110380 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 148924613 1250 148923363 148923371
    0x70603020403080a0c0516090603020901060908030d0b0414010909020901050402090d03080a0f0c0c0b16090302010302130b0a110105130f0212010e19031d100c0c05060f0a12 76
    0x1010a00400981d012969a451700c104020020b0030220f01e002c9051401d900341c801584000224804550701c2042160310070343d620b004507030fa100b0054504895900c134200003074008100002282025504c0b002000c1d6000f007000034401c50181920001c07031303000d80000200540d80e820b160250320b05003c641d070041404440035481c1c4624030001c1841c100c55208010180b040030030101e1001d05070354001c1e6410f10310108082009000404d0014500901040107031071000c800404910f0170070100c4414500c05505481c0c3c5100d541c6568011002580114001d00b816403000c1d50105942704018001c1664031707200e94548030b5804810762280c2c01c590024250741000c0c0400c9a004001402000e81e41c888550100c50b46240c0e8100e00b2070040c05803844840440341809400c2800100c50609000050014042d07503a04c03507202200502010340d07508a031906035111407666481c01c042440b608420080300d105801c2c40c0c90150341c850105045411103916007031700010105aa0001d6640455100011076007090180 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 148925863 1250 148924613 148924619
    0x50703060b19082a0306040602071506210218010905060f03010204083a05030a0606080603060c1c05013c1511030c010e0118020102070e060d12020f0706030204 70
    0x44e50395081800d028142c11503414240c8940c03043c003100348107401d0041c01390b501a15203450000000d521079001101c92070b0324000400f01441703051044105544d03d03409c10006148a1503840d1030528280f02049034000130800103da084069012840d00038850400b01007038034185039040101c420302c01c60845000303a105104c20082c2c0d91001815030140e54600d07803110300b43c2d40c0c41c404c50710000c3c0c004540070722200080c00d000000d1580c454000e520a03000f03614100451a181c13942110214820f0750010341c51b602c180702162001c00311900501e80100203040d8458103009048040003034480036030258401d0b000841607040b0700700303004070100d003181c84041c03104c080e8051950707003c891031400c3d000d44200d00780040001c00a042c010310b41019440b000104403a11030314840c5085000e482054004103c95003000c503d0302c0355009100744112000d6058014000c02030030040c041381007401c01494554400f20348000d4002040c1d013070310105c1a0340c1090b0301600c03803e540200485e1524129074410010144100030030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 148927113 1250 148925863 148925879
    0x40f060902030f280305270a0806150409080315010e19081506130207061103011205010c140a0e24041e0302060f0919080a0c05060708070f03020a050703060b19 70
    0x41c7d818481021103d8040c1005c000d50501101c07914240d40e8100c2080300d40401c02c00030004000e4400c8010a0010280c546c40405010940301c54104c0144110001c0c40401c960759182034041c2080003041c5404800c139010b6200040e550310050114542400742c0c00821300510364144815488511040c038a0062410a4804182403c0108200e40c90055010030706504014058020019145c1a211034076260f586840d032180c00003600c2c146c120360355071806090b06401390040681410b10140d540d880342c00c103a400c2000391608000204401d5110b550441c00d0f4070f101003061035800510018807101394445080c40682c034090f040c460030b45014150410010001030761418100c40340303070401805d0340303441e400c0003800700783d5103c41e40000340c40211a1010105200c200042d00c1d030303051805414010450769561040c0000e62280c2a006400f1400030000c85001c14031060084039a144248110744580c8240c0e00c5441c10b046070398000311041600c4032100550352402d110381d54a002c1c0c1c0b54084624140c03820040f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 148928363 1250 148927113 148927117
    0xf06020c0604120b0408070803240a080309011202070609050c011205060916050c0a1212020304021f09210201030614030d08060f040e030309061e040f060902030f280305 74
    0x1c2c110314811380081c5c100b002c40015a00e00d264003035202c7e40c0303906241c520b0007140140f10407504456003501001c8069403414a00303407400c40e03951101540c60310788a640111444000081005c005540030020580010700764070801440c903004d08040c0000c01c03401d41c0010a0b40c02d07104000f02d450707810401406035a9580c04041504103a40d060072400241d41035106407103900801d03400340010b025009101090020301825511410b000f59034240011170102800c01c1203000555019401c203110100d1551442c0051000015288050900300c1000c0d913104030008229445480462070708110245000465800d070141070058007130508a200c200c3e00c0c03140440c1e681e0340d441e004c1e042045055408500281c56850034402200000f070001d00c5080e070038070a9595070740d2050f20050807501c5541d00180003074815503242031149404449030003858482c0c7d215080c040c08104819182c141e55603d080300140d0342007001068031400103014041240300e46a121855074403220030207584110300f5a01000190340401 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 148929613 1250 148928363 148928399
    0x3040c0e0103030f2d0e03100c05040b070204060e070c061b0804021e030a0b011a03041205031b07150b0103020a0f0c150e0610080304050105030a0b0d0503040f06020c0604 75
    0x1030f2174007500400080600d0200c4003e000072440711074262641c03a651398400c4210455120680c104c48403510702c00c11600c1110034680c00c0d0b0000410610081c0300041d00d44005000450000380082000c940b10350141d441741e101655070070040303080340d6060400c00540340120070900d00714040e607003049103034204003034803441d00144020304c6010301100401030740350000b01810a440c8040c040b10600545071400440c225000e00442e9004885103d20a03404070094023103900c5290300455241605855079000d80d80354002074190b420384c0c843d5141e44409030001030081c0101e0b03401168a10720200c80503041d4821600041c0d441410140104a00b03506141c2041d1240240522860452800c00e2207003010062119600101120305040501c0c07000007960001d2344601070348554000110103561444030b2645c912452065034080f460034000611150710a43c03040d40c456402420f2020310b01c1c07295844070b085906c960490181c3c12032500c0244820340c1e04200e030145510003551844c0c68a030401140885040b1601 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 148930863 1250 148929613 148929617
    0x1008010902160501061701060e070c02010503040525060f03051b16050a0606051e0102060103062c060106121109150c070807140306070e13020c060c03040c0e0103030f 73
    0x5911203000c01502c0008402a400c070000700410754443d680b402c900014000c81e90394640c208140071620302c1765001c1940c011000d0f5151511221354a50064805400042050790103000c2d0740e60101d031074100140e24182c110402090f44029600f84180a40884610300710b5104041c0307400100081030011100000c05076030903d8080d0740303034006054135100c0c05582110081c268041c0780c0307110041000c01c0d0401c500f622012103200e0030384007002c0c00d1150780e49100403420740180c0c027080041012074403c2e8040d60303c0c0300e403030b603000700484091500040d100400310008601135803164004001ca20340c48401d001b104031ba5900140600030ba820186040d81c0500e010080c8500001c1c008140c440300c0000807122008900e50585590940d18401c041d00c500b018455645500c0e12001c0302c03445481d0101751b02d84151650380f074100104103144280a45e103501c039040000216406c104402c0d1130308003000084c0c03041440c3c1040780d0f62403506240901c1c0307005031544941d610310401c20043c0700203034000790301e600c00030614 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 148932113 1250 148930863 148930867
    0xe07020d0e042013060212070210031b09060e0102190602030a090b15100e060307080403200c031009050a080f0f03180114063d120b1008010902 63
    0x2070006000b0241415561074032000721442c4418240c04102030f25084052440407841c00e95142003da0700d0b05140148014a0003003003000b00010b20b0000881003000d0f000c1d250028012001584448105007403d08510104030081420440c0a85c060880840b4503000c0c8081c11403810450901a52803800300c000400054003c00021007004242d8004150303203402c640800e8082c1000d03661580048111070300503006900005004105074050400030400e40c031b001e001c580c07a40e0b9541504940c2100d0250084042002079844200c0a0021603040580b07c05010060300d05404140700705480c00e8040c1c203044d030f03a25040807990800f041010480c510b405030040400750752050000c0b5030135064401c411030b501c03a808003c400c1c4154164003403100200d144000300200304105910045501c801c0b070440e070f002d6109440809010080d1403810840d0740d40c000340846603a034400d10401d6841c0c207600380c2c09004e0000e005041e401d05181d000380542d12801109441c0510001a9032a00030883d040501030725141700e0700 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 148933363 1250 148932113 148932137
    0x20304030f170301030819080708060409060924061d0c16080f07050613021e010309060507020123040803010b070305090d030e0a050303030105030604030c080409060807030c0e07020d 80
    0xc0c0007004507800701d01c894010f03074075078491801050725003086031f02480644949400642c498010307166240101400d8079141c00942d0b0700e03001c20000d0310684104a403099103c5084400007501d1042851441901c0c0c600441c80700150340030703030040365400c2e17100303022510208510306008400000d200d900001001c2d041a60b0380c1031020101c1903141441070042141c4800508640e03c41065009841214824404e0f28042d80326100c915007031007900706001e035012840c050240c1e4030b0b45845140c9a00035406040100d5084150744880c02100d000310b0390900940d450b003020b58a4002903400c008810041c90402a0b41760a0a031518a040d0105004201e0401c60001e00708081c18060011380304800d100429610f409110b41c84d0082c14051016070443c0100c0c409200451a480d004c4241c9050b038901074000c044580d12a02d08907020310040794280c0b0007940c2008040741441c480d01a44d4050040c2034010005140f030b601e0303e03034121100c5070b010a821441c1013003440345682d408242c445d5801000d14081c1c100100d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 148934613 1250 148933363 148933373
    0x8010b03030405130c091a0706060b031e060d0803090307020913030503010323010c090e07020a11040506010c0c0b03011d06010f1112040603050105030d14070b0916170f0d020304030f 80
    0x10858000d11f421000291180130a42441e1005220403441018144480c0340d454100e10414002500d18000f10340d0680542d404c2c005442100d5039000328010101d0b21400f4154403451655031040d680b060041c0c1000400909500300b10341034070340121050b40181003850a68400405502060000905100d400721380700ba604484492000703c1c41040c20001c11a00140e80c501411401c054824024211020710018a2690000c12000a01a0810380310100c3d889160304020060500810150520802855017008924144c039180e002e031a89049040c0e0301d50410076908070b03079680704030001025030440c0c040010bea40e1218a0080358042c500303000340d051004020050404440d2216080041000f14002440c25415003046040b0340742a0180d8401c21000e1104582c5030b00341c0404c550b9500f500b0440900001d041c04116603000c900c410558452442c03280c490150249036a1091508009e148244c400d14001400100d40b044a144000c014849000340c002c0c2d140d0199110107040102c0031211340d01808 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 148935863 1250 148934613 148934627
    0x912030a1107080c0c01030b0303030c1e041a03010305060105040603110405071416021512010b130503060403091403010507120b010309020a0e07080a021c0e010905070b0408010b03030405130c 84
    0x50350005442d9103842009500a6555170041c0c11030740083e0600840c001d150802008590040d082801002e240003000703110510705403078805544414410400000070000d095010303056540e806500000d641754514107050386011410b0700540e10413490010304000094510700d803460900c006890224855491020903140c86a40d400010034605000450380c0042c884868601d0240340308803600c090074001804440594003442da0444400311a940061144030028000f030710b1400c00d450821444a61910042400d10b801601c2c2180851402c3c1410b0000902c42003c40448500950081025103044800203010f408824030804c0582d07507590000303400383d119410100da1140c0180540041c1c654402c0050705039001216a84001100c42c00494040e00c514001c80c0d100403440040099609458261100203010700d086403005036503188050301c001001030044200030010715040a44851504515900b950f44000d0814031075002000140465595252003010448011000143d01e6407420f0302503402da = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 148937113 1250 148935863 148935877
    0x103020706050c0c070602010b1e030f010e01050a0c0c15020a0c0209150907051e0a120e1c09060903060b120307141501080c0d0314040803040e0912030a11 68
    0x150b4107180070401844480d01c0100502c2c0002000c488407070f82e68071070403030803202c1045c60940e120b05801801d14041000310400411311000400751440c81603940002803c403001440340c0811070351645d0411040410b1880798901d511941d0400d002c0a403559a00e444800307054455a602480d40450009403480c0310b46c221290a56014124031010300784107230100341e0840141d51041c0304035400c00004603035034811401d0302d10060340719900c05068084058200700300d4010480550400140003000d0440c1c078003c4c0a80e17000e026080c806880722003000200700c0c0409070030b02c400310140080c5000400a00342c4c00700008040300c1e003040000900105940004444005c0c030300010000b44070120b164018400b0450b409900320820070110f4034007219100d4101590307402441106c403681c0081b80c1c0186d29007408114040e0390740c0b00b45022050742e0545500348021f80c020f90030100d21940040740034442012402010754008100c01c0080030720b5407441c6400b140c0c5100041c814074607103864080e08041d006c00c00d025100d01c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 148938363 1250 148937113 148937123
    0x31221100810050a050c041514120403080f0c0a120e0307020402121801140403030b12011805071d1b041203050706140906070309051603060507021002160303050601030207 75
    0x44082c800000300081c2c00280e5000c241185400081001e8050140494089440036818440b00202040d400d550150f0109082040c1c05404c0080919882c510744010380700740d100e922442400d041c000383c90b104440c4d008000d00e094800c1040880403a41d0000320400c122900500c000c120191174001050a500a865000b134102d400400ca8035540b5500d44d500c18850607000c0e001000380402210b00f03500344c503010a000f8070309030718902c040340c0804d10a4100104520300580301001c1c0c4100365181c2c600b1035000c0e84c07007111102c12802c1031f58101321040c1704007001010a40a01c01050f00030faa40c4840c10840940184001c0f80841440d600810189054070010701d50000a500e0002079428003902c1940000000c0310946d181200200c0e000002e10f40d0580034000d104024451552941e60940080c103008505a81900c1110310012080f0410050180a076200c2d54010805045c5044082e1070f2003040149108410b0040c0a1040b64840140c01401d9068041c0707800301e1261505001038000f88138034980548 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 148939613 1250 148938363 148938373
    0x6030709090807080406020c01080907050105030606031f03060621200d0501020d02071203050907030611280809070308030403050d0e0d0f090b0a050423030607030b0312211008 77
    0x1441b650040b901e040040d9081c0c9440506036079a40d1104e445000c9409024042802800070035040e00301900610b6008401034210b80c11003150040115112041c1d50044680e151511810702002c09588480c2450a9424804103a0340031a540c81002e20706e0000404c0811001c1400e002d40d86a454032840c15850360018021503075402c468250f040a075004580c180c035418062040d1000e00d0707210340300d41413003154200003400c0300030705540d82d1001421010400c0310b40000e00344025448040300074009111100000c6081c4105501004050200c5c4002031160300d064100500800100700440f085940c440d03414580147d4811003200b0b808014402e02c1040c0c0428420180901d00694209250800600c003030749401c9003950741c0b02c00e124802c1c801c41c0d040c8000900b060008002d5001c00390a0344078032440111400d84188201400309150100071603801d4002a201c2c4500100c906041c44502031103d000b010052070401c44517040462007858847c104e025141e00f400113260090f04450000103452080f055031 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 148940863 1250 148939613 148939619
    0x60d08040905010e0106090803120903210f09070522020403120507022b020111010b0d0320010603021f0c150f0e06010501090b0a0306050d0b1e060307090908070804 72
    0x4000301404d00071800c141001a00118045000d40c500800b112401d0004611300403840c007a01e01c046001030041400d070321003031201901c1d0310060200b201c148000108008003a242041c130014000c08080c04612068201500a0117030341c44a41e1030a68992090000f0440c943c800d4500c0d400030700c01c0d5400608144950007500d100349038064018a442402100d000e04503503040b031003010249401120450b800100c51003804e0065014407038001360500d0040000441035605c00c04254542c401e42c5080740050b038502c50044907560000318000340b104c1c22000030083d042c01c56000c50140c0029110b1040b50510001c0000380c61840f844100b004254806100e0302c0100326404044050b082c4030026650290a09680c0c0b5007072400014028100c40050391250b54261410303124185592040161108064560501091503250303860b200160301c1c0300d00f204048901c1d014034100440f8280b40c40300c0d41c4004101060020b41d560002c0c402d01510042c58000610101c00e02d000c3d901c91040607002004103002003000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 148942113 1250 148940863 148940879
    0x712090302040509010e1b01090b0d02130609031e140d08060102010b010822051903020d0e0603070c1103031e0a0306050d0b01140d0f0b060102010c0504030812060d0804 74
    0x1410031a807081e9414001034560020080c01d0b1021021642040c0e4001c02103c1540080b4940340300d001c20042c11300d0704855440340014500c0c0d902c52564801c007581c00240000b03d01e5201d40c0e00c60024400d91400d0245076046036507045906c0100d100303582c0f000c010491520103102145001d583c80c000060120307142800c0000002d0150703801110241c0c00355192a480c181254080e02c603b9200700c2050000c2040103421000204a0000c800d42c2a110382c807880c04280c121068034000005118040e80040181c0c1440410003440c01c00319042140c043c10041c807c5c046816004451b98002e254003018450311b00b580040840d1840c05000b40c00614030554110140303840000300c0003010030410b143e905011541e00c03182884038a40692000401001060300101715061505400c101c11000c01042c02414122035203e86420070076442041e00ca804055003442107541e0244a00001e025039410014102031458541200340d002c1e040b910f200c2c080750800007442c0c682d00d83e040320011340c0e030091206496035111815 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 148943363 1250 148942113 148942127
    0x50409060b040e07060206130305042c01090b030a02040c02010b0301020d050a050a0203010b0a052101091a010815090a02041205030a020d0513140102100f020a140a1407080712 77
    0x41c4034092454184a0002c40501040702401e580c8a5001848151074078840c0030f03407000c0c03488400d504201040c00b000c81e1a9840e400c0030004441c11000340c56064461020ba4060b5039010307403004114514122210f0216100410384030079440d0112000524041c04883c26070260900e0400e00b13a16500c00200850700b000c0c81d07480700b07014902040c0100090703030343c10b00302d10104e100a00031541d0070607003030046d240218130803402040751001e20042686885494110031407034220a802c11071030161074403014181c0d01202e1056001c034000034641410b160400086141a0f0004880d070707240140d0302500080c0b1610700580445008042c4442e0f507400318002414002e88039004100c203940107000352030610200610910a85200201100c00e1510251030a51035607070700ca1001e0308d014158010f00c40141d40802440c8111914841896000360395510003107001011000c041d8690440d4a0042c014000c885605c070443e03080e4a05886510381e921541410008200d02038030000400301ca0f161150326600641c440c038 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 148944613 1250 148943363 148943381
    0x100509030703030b0d020105041e030b011401081b04062f0708101415030a0204090606051011030a03020c0a150b040f0207111e0612090601051212070c05040906 70
    0x16040240c04c44101c200700719110303081400782c00158240400e1026034600c039000c08010814140204806603a540c9900804009920400301c0522220030b00d009540c2010542c0da200c0105452490982511000c84c00301d405280240c1082140c001140c40d48a0804441004070710b100003c411000340c0f240b0f0826030b0722212801030841c00d010b0121401c50000b114003408228581d5800200507a5031100380c2401c40a141e0000340b41d16100d4900d0120143e19140324840403107009610210740c0382d04010511081300c480242110800c40d1a45481c10180d00200640303220b6019440d0240ea11442d4442807403501c5240343c00603040c055580110b001c508056807003160000c0c400e1398140980d01301d8a940750102c2c007950f20701412403100e2030001099443c007654a95600e07074000c2042241c014000000c030392240c001110081142c100705050004c450010010f041c0100002c543d240900122407141603150b8030f20321146414000081070890070808102401c0000c0e141c09001081181801d06150020380700b509 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 148945863 1250 148944613 148944617
    0x316151103040e0a09020a030f0f0507080a080d0209010c0c06030c020712020d03180f030503030f09030c19081902030a1e090501080c0c1c020c040c080c07020102100509030703 77
    0x50002480d0040070098504840ca080044281e680d9900502c8010340140e01040340c0c40b4045810110010790081e036041d0f03040340150105100304829240c8503185c00c41540160345a503101c503003144000769031603040322941c100441026840d0350840717005894a1064081c001c0119159610110303141c0c0c1d146d40700d010340d40c0c4181e08441d9010b80d0b6400080d29448520b1019400c29010710002c0c0100b40a03a000c528034071a03030809403044503502c8144c40e5045506420440f100d410010500482c240c00222054118004001451130584400c44880e512841d1040e5161441c44c1041c10b4810f100a9005444084001e4900659441c1d0919002920380c0d1101445001042038401c024965020b0b4140d00a139040407078940601c8035082000649121400800003180c20030100000d0391545000c0c018941c1d080114aa640c00159880101031300303202100100e40d0096241c2400c0185c40c43d8000e07840f40d040a00418016911142400100d04011085008882080c00c20702845054030000000301030241c001c0d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 148947113 1250 148945863 148945877
    0x3011d0a050601050403060203070e1906030b030313051c02060304031e0206060102121e0c010204031205252108100e0f010509060310090506060103060929031615 71
    0x11905a030440e50181c51141c0060820310081c00003e038140c1c0119046051810030810b105101030004241114581e4514801124a2010841c9903003500906c1d1401c0b07000c50181d81009024000c42c1c00700f00071841030078494200100c400d80c910806140390460181c014008a03234910302810098001031308134120040038000e0b64216201e161001c581c0d03501485050380940908102c1240d0760b180e9400100e011880e0107030012044800d103074501e0013440e090418000150b02c8030300e17608000030201d41d401d4441041c03010400a42d000d80030315802138001a46462000359070034400b03040ca010001d013400007080b5500903a2603030322612504561454400c60a514101010580ba014130003120242660410041034100006014501d8076540f829440000a012280180125084c0c0c40c103458180301c2c04c3d541a0071041c203014070340d681802104040d2503496428010f0346158015441d00c03094030905c0d07800000e0343e40361800742070341c0911114041414400e1110a40d40e200d0344944000d02402003407a0120344a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 148948363 1250 148947113 148947121
    0x1505090a0207030c0228080a0308070801030309050114070b15040b120a02120f07030303050906010504090809011d0a08010204152c030114010b030628170705040203011d 74
    0x540c0c021240401c0d4140d90781012043c0c01d5080c02400b402040d03180c0000300c1b9850450b448030140c1c1c0000c50080c21164001c1c0040a5107081c0a81419800307824001000418001440400d130031501c8901102c07400c1c41e000101c10f88d00c040c11500b60103581c400078006251441480380c0420610940b04150b40200c0d000c005040e9001304000780402401c0f400c10850300001c0c04c120141c17401803006116a0983c01c240d410303136004903103d0350824155820485c0440d035904140002c00008004090240c60192010812580e0079110000c8038050650558104403180502c1004007000b801000398504000c0c00340c4812700d443e440c11030301030340140c0070381180c020110f02c4407100e5501c942100f40400c0f038030390320500d441403080c0042c2d049444200e203c560159203481d180301009800c290702c14020502840050384a0500d2030401c60310803103448200c1800c07903640207401002014406000c2c2211041c1c41d8801da244409000700d4100211075003ca94480d1000c4000259000035900c00c1d4001c0c01c0a010191695403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 148949613 1250 148948363 148948381
    0x52104051f030e011829040302150108060f0103110f0307180b1e0904030311040603060e180d0513050301090c03020a080d090e0703090b070f090803091c15150509 71
    0x1d4105d1035007120765034030340702c150200d071900c11400d0042d40c078008030700700e8034000c201451419801078804900680c842c0440c481440d8004004601405000c07000d0300c0241400000c03001070040602015040e0100400074650b25624500c2e448110031014040e82c004035500c05e594144201609403041c40b40e801c210440c1d00a05c1c0c503003200c4501c0312102002642d07422100d0b082c032241100042081307041c59603880d10b45c0c04850340c41c0040d0005240c29a0046905810241e40b502d4a1501810b54844a0b9200700c80250b540c4020920425070800d0b464410303203411f4181101160400c40d0303480213405501e0100b42c4414454040094400c0d03034000d4034040c03183c5545081d6260780d200010764090020b41c0b64241486080b0026a00642040c80c43c80e0100761086a07444040b14100c05503501c201281c00d401c0e100345800e030071080c41402400000d001e90b081402810200b203210300d034100180c1c100e0b01c10030508020021743c0241c2085d000100c2c50100110422000d83d440000114000c6070b120b4918080000c0d00d00d1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 148950863 1250 148949613 148949621
    0x40c081b031e190819020f0c19050402130906050a06050a120e03120603011802090f04020102031209060402011713020d020f030d0816020604052104051f030e01 70
    0x240c0240080c034010410102d903028148408031410428002c281c00d651040440c0200035100380d0291020aa403011a0990301404c6800e0240070b6055404c807002020020801060b04880a4410344003800d01004450b0a0000da036103d41000e580036101280c420b945104400c0b08030160350100d1801c010712610f0303004002c00e6405070311130301d1b0004400300000c10076580300d0a40005003200600c000b00f0402c20450700c02e801c40e00040c110a0b02c000b144010400c44d85024068820281500060b80007581c030f840d0080f03840030794020400e81d28902084003040844e44201b04550590700103805508607418004001034a500d03090b00e0503800620040200843c28080079080c902409402c1003500b40d01100313909002e200140e04009907401034031455074002607282070018012008041d598410689482d031040002d02000c101c032030b821036100108103c00545c0c00910402c6154044442c070820440e03604003012188150380003213030001c00032110724001118106101136107403040d45080c42400701c104080c508031 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 148952113 1250 148950863 148950913
    0x5010905061510030b0f04060306050f0106111207110a12050d0810060809070f080a140705060a11010603060c0903023f030405060a0e0910050d02091806040c08 70
    0xd02030b41c1e01e1040913010340c0c0007035064000580100c01524148000034211205a481900c2003500e90040002e2030b41d00c1e1841c07a004d0a4241040b400da1010814080e80c3c400403003a402200400020300c201c24460b0b1907a45584014009106020164036489039041d136503400c4ca421174061041e45070b44e2031481e0094402900c030344183c40c40c8804091901c0700880c6d81303590140100c45e41e405050808a9401c0c00420b00342c026000203401400e48603024a00903901800c222010301140d04a40c200340643d81c2c0c2c45c4111070488442340b411500c082d03c82035605004041a85c00100300b2840c0c80c1d400751031030350400000001ca81c000c64110410b0401c3d00d4001034076010401c5400c150450140d40b81d4103201c548001104148803120071a0708003900ca4003c91001d5004001d12800305442c002090010f1410b010f04660003450840503c1c056417405000c161103c01001c4000d21458010001030241818000007281085600003280d103541032508207500c0300140c501592805002d15101d000029465170482540307 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 148953363 1250 148952113 148952119
    0x1103070f020f060c0105040b07021018030305071701031208090d020a12031d100b0d050c010c0809091303020606040903050405041a06030901150e0411121207050109050615 75
    0x201455500300219500340b481403591100342485158181e810900c80c440c459841541d440c411420302c1940039280c0032024405035900c07030811191000f40324404a10903050f941c981000308003901d6002058a0406640e034009280c06a0b600c000070504c900e09560040c00d0506460b600c03811f131140c1110a1700c50100701d01e940e0140c0c2c40b00705c9920003e00d40610282c8580303180d28001482c031240c000140d001c511040b00303d014561003050810140100d030300c03034481c0200c000c50303290824043d02d944d46a19010580000b82c18002d00b003408905004055040701c0e08580020144580ba20b064501030314000c0b43c8403416401486400000f07040c1d810544240d10f217846d0540c44080c00c1615000c10480948200c0307141342c001c840c2d01c5244184540f184005140a00c1040001190010f000b2404c01c1141d601e90b440340b120780e41170030103020116280c0301801e550031000381c94090340d045140d0340040c41c1401140c4080b001c66000030380340080c02019484084940d2281045d618251604181c00d9880b507d1244d20640c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 148954613 1250 148953363 148953383
    0xc110303070809010209030a0b0115091d0604090204050c070c05040605360709060f050a050405130b03070f0906050402040305060c03040c1e060f02010c050a1b021201020406110307 79
    0x2400c1d4003540c0810790200c2e00300d001500d403540c4440828180300303900d182240d08808444c014403030401d2542440798a8409840d140e803501c0d203450740140d4460310f116801d4074605d45000105050742c9444d0000080b0a401802c1445070781402156004140c0c44001b059440c0d603c40800440d00346480e0046408075600104280c1301070489140d001129100f0403c401f500341070340c0c1340b1402c0001300607065038803942030343d11550285498400c0140030010342d00ea400040102c200001c3c402d8075000019075083d2141a00d40d050a841d003d44a903000b4840c81d41e5440d07242c8111900003c440140030741d1002a100c4c01001070152a030303036100748801c2c0c0c011400020061b03000354001070038408e03059001d5a07003e4000c070038000c1034503500c00850055012884d41c000e400d56500c13409000c06500000c03102446400b501c000c00c06140f8148000340350b4001c0c20350321010008503810001060008000112203135400070302860f6800b010080460007580030744190f101084010094001601001c01902c901c0c5c0e4220003c05 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 148955863 1250 148954613 148954621
    0x70f09030b2e0308040e130b010e13170d0605150304080c071a07030f020f0604081305060c01090b0108160312120203040b0402120d020304030b0c0c03070302100c110303 74
    0xd65400c4110385041c00c1141d41028603142d00c001425200440c020394419a44508040d10340100810080007a641104c411720840000f40708082410f044444181040c003051301e400c240791440c3e0174141e00182c82203900c02c02840c441c2c1c2d03c3e40024420507280540421000d07548905100c0e4203a5903c4a0441c481000e0000a021812610041c060ba09011080d02e071aaa2200c40c146001504000030a210b114046402010150010300381a00902070380002c180c01218500c190b41d8448000300018141c00d80800d400d09010703100001c0d41d010384401080701e92204403400c2c20314028a40300e1070644081a0920000038001e801003101c1001d010147d8000340b045080d82c44400301c18103803403c01001c020603501710303520a00d018070280d03014501c6880803060a00301401009000300c007041c00c0340d845400800244020580001c21141100da100c80f8404490340d40d0400a40d0703234003606052201e0740c00000b95500030194042103180c2042507400d000c000c4046002c1c0c1c200d541d501c41c000003180750383c000c1000c1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 148957113 1250 148955863 148955881
    0x30c06070f0c1e020f03031c050c031303140c0a08030613060506030a0b0d0b010308070c09020a0f0305090a02031507020607050304020d1103010902060f07030207050405060109050d1514070f09030b 86
    0x1401038009801703081c0f80c1d80218040317032840e03000180030816905a5420b9840c40c0185028250b0090101140c050841c00c0c0045820305100500c0c2000301808100c071502900344102000362a18290307000240c5145402500b400031141c0d00894449115038100c4040ca410b42142d48544010340c0c0001c0d140310b06668801c0110b4008080d00d419050744200e0f0000c0d190005002031403482e000c3c40c030403111180c0b10070040c54000200c0350950070201259006000d8124056031141000d1039401031881c01107015120120030506140c06a40065010700407090705040c8440d0300c0c05840e0140e0711950864400c0e130b40e0b40908803203902003034900a5006c08007c0c00304001c980c110303000710301b842001000001c1545c04c0fa80003640d0350784081d846c2c00c110180416070300241034051003000014070080d5418005441c03c200007c1011400e03000d036520500d0814200000c0c00342541c0c9114440100241c200088511a07804660b80c0b1011034074400001e001d091081081e51151014004032544072052285c591900c3c4e001d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 148958363 1250 148957113 148957163
    0xc0319150e060c0702040c210f020d050405030a1701060816020f010f0c0306080105040f0807031205100306060815011710090b010f0e090c060901050c030c06070f0c 72
    0x500c110080e1190751408500c10280320aa01501c0221a5603954101920520003583e103103500800c1481349400e4400249000090404142c1032400c41c0019090140300044c0001e005240512030b0b6507203050704010420900100928581c03665444e18002c03100d800207540d807540d8003400740708001511100420540a00c50b0fa000c403590620b40103855510300204652421503040400700104542c44100c126801a01489400c014002002c002c8c401c0380b40030348442c0313000b50700014010880360b8005066800d140c41441c4d00003254080400520450510150000701c40089000a54903e0b1401600007202e0300000380c1c801e4141c01000341c0c42581d078a882103910003030410400800c40ea000303030340001c61482428400c8856030f91040c4180401c55042a0412060103081e400526096030270000b8000540c2c6c00041d02902080d049848580d110a004012189406840070f120440e100200f62072030040b40c0411028071404141e40c81d68400805440112407400300003801805d0002180610880540b400c11 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 148959613 1250 148958363 148958393
    0x506010e120c01030207111206041b05011b02150f1806040303080610090515220305070b0a020304030606121a0c090103090c030b0405060906090c1e0409080d0b01020c0319 75
    0x6010402d04800c41c022443e08114040d0b50b0a90390001c504000030003032f800e6254101c06035454000d00d070090030318001a112135a81c0d80900a04010ba094003811552182c03882610083c100a0281d22041981c000750b504e50001045c500c401c20f030305100300d406418250162001c030307078040c2d403440701e5915804140000703e8507107040030080008000c0f01003815110705002040d101d00d40f42ca01d5954580301c0c6421050842c0750000d0130f40080701c000b0200045000000c6100c282ca1840340c1c45907660107452001c1c0c1c51803142e03901c010482030404000240b1801d4031038502c070119002e10f07000e02c01c2d000c2212109100e41401c8031035801d060028807844226510960000d0b5030b691080e00e852103800e0b00c039242c110140000f1201141e85510006c10010140814480c2d02d8000c60000003c1078003803800000240d524007444d031450104002d801d500340e01951a0b41100b19000d4108044507500d15007011900c02400160b00701501610030064402c2d62414001102c4007079604408039005068119913603160384001c1c0f41c0c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 148960863 1250 148959613 148959623
    0xb03060f06071b15080907080c01141201150807180909050a02060c070314070b030103060f15030c14090f180f0304060306030212030307020c120703080d0506010e120c01030207 77
    0x1843c120f04541060402c20058404080328010210890b08010040c0c1e100900f517000c0f0385c012403420440e040c000214000020401d0070003160704c08400c502014a030144002d421240355034440005a11141c1900b41d14072203096640c0c003043c503944c900c0c1c152140212011054400018040200900f40d419070040451070301c0b840680e030700003d1b5600080c04942048a02c45d2254000150070000c101003103281c045105000009085400c0c40c0100901c81030205103c00f92143c0e80321b20703010322810903940c0b00c12310f440805d1101e450003e41ba414114548003042c042e82d41c0203400403885d40118079100b44858414544100d81c0c01d270954030080c08007104128651804c40354801c06c0d84811500310140090800b8040a9400046952450042014007140e0f602e01a00c160410070070f02001582c0442c00c0c0b04865001d80f4001810703004809110b16200c007a50020746a4480071510150301e04507074201c0c60140303100740da03144403803062001000080c1350444030861660744802248800c0354043d401804070f5500507 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 148962113 1250 148960863 148960883
    0x180b0903010e030318060f0705180d0f05070e010b090f101701150f0305130b0402150a0503091c080a110d020a0c02030f34090c0c0c0b03060f0607 64
    0x280216600c3c41d04151840d0000d074007201d40302c402440013001160b0b48a00c45103a00000b50070704c406e014201e03100e5001203400285100c0642841c40d1140320040040541c02a5510f1400b4210300b0300d00e860306c51901030042a00c07420400005c6910185068421444d401040381c1012402c1d8000c101050b88840c888c04140002d85a00346800c07010064203500070408414009864140ea1100805110171081007409242c50442400307986602121110702ea680d00c840c42c1e1440b9200c42c0001406e904054100700c1c0d002500090601c0d00e07079031080246015010403812035130f15000e01c2c51291141610080740f00002820b400c0010510740c05904085210000c20040c2031505111161003000d0380e200b001d51401290510074144110b041c100400c2c0b0490214402400f4032480406506c400803070121f800b03c1036000d600c0014290200310307142c0130000f030042c02410401407400b07540c0030f4a1001a0b07030055481940820002880d460200c0850748030b604010a800309030300c40e202c20402c0640000c6415030740d200fa4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 148963363 1250 148962113 148962131
    0x6030910060f030501200922150e090309030d080a0e0d0309020117040c090b0f2701170316110301060b1c1407030203040f060504030c060c180b090301 66
    0xc0c9219840160002125500e00315085040080c02d5407844500100310829503094001c64980f00820b46503840c2003100c044113982007a0442080d1129210081070783c0310701d00345008000610f218046000c4401200030034800b43d40755000545c0303034000c5c01001a050b030080801501c00e6445120190f620690402002503006118201e46280055115195011035500d030000005c0d50703006154040d0900d01c4030030840035480c0507519049089103900ca4401100d031901040042941c0b0300348041c881205c0039002103400485402003010340581e5440d4004860480c2e00003141801440241010f981e482c280258030340b01d0035401804035050882001d031001c0081c0c940c2c403240c95400380204002003049500b4070761155122544000b08280c40c07841240c5c1207292003104404a200e510300142e12003800d04006850383c1d00c50030440d11600810800906103803801042100b0150428146a00e284c007405042001c00707400703170050780c00f011030022441844001e9030007040151100002480905005400440c0e0540 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 148964613 1250 148963363 148963393
    0x507020303221d1504020a140c01060504020d02130b0c030412020a050405090f0601050303090a030605040f0515040b10031a07200307022b1506030b07030b04050708090309060309 78
    0x884400d0240c003840b9800b48007085a8181188403014400c171800c501c0c00550b800b010b028050071910400501901141200301c942003036104400415010700259943c2440c40c141c10002d5100b440c0340c504c621a9000c010aa04002c03c00b1fa03031800c2044c3d4011407030207003418042c42c415040d044040f41d00c04d5005401080310341343d6010310f5004007400710040404200c5d88008a081050503000789000764418030003500c0c69611001d0090440e03402410000d06030f140e50805220500420030b02610b6032049008146580c84080040c0b80300340e00403607250300141c03503030380080440c001548400361400c0c01c000052440d03d880461025003003481c2e400c05045984000c145d038650480c2d28000c41c802a040401c0400a40c241652300154180e100303181e501040340b0501d030610321510741301e9020781954155030314560740780e0321540000302541e0440894002032a09000c01009028050f150700e014600f044045800240604012801040c01001544c1001c5e810300511816801c02421114141315140010304940 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 148965863 1250 148964613 148964639
    0x5030c07060603080d0203061f02070902090604030c030f0318051503130c06020a11040c0807050f040801020409020d0f09050d050a0912030f0206010812070f020d020a0902090a06050702030322 84
    0x158010250322171070428200140b41c00d4034611400c1c0c0c9c80c180201c201d119075000c1101015640750820058440130301c5400316044c0d009a0300001c01600f480342001c0140710240c000b02c07099510036501d00010b181061414080c0c4a524423a9540042000b400e003801d81c1c81c0c801c0596441102c2084400006803643c4500078207091035800342016070080501c0303100b07000c1c8140303000b4030901041c0c50500802d19540302c02000b44030000c140c0c2040000205061142c0603400c0201c070000c000b01d000943d00c45845210304402580035080003070348545883c1564544000d14001c5000081c1c10001603d03009091405c161455804004000d007000040480421400e0411010031886030090b954040c0030a13204001034503042042e0400c4080364405800004001a0b40040755080c41d40710600c510a10140e2001c14440e08042c50001d43c0709108682c04120608154050b0504100856681e11005c0c3d4444058619104404019415401c2040b1403e042d61040907985401000c2009003814107a8841c02c0042c4e107 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 148967113 1250 148965863 148965877
    0x6030606020a2901030b090d0201050415110f0d0f05061e01080703020c010e0a17160206070807050d030903120b060405040506030f0a03020d09060f020a0b04082502040509070605030c0706060308 85
    0x10000140c01d11060100401441e540502230340020055800c01e501d074010000c24008413100c2c0c0503221030107510300c00380b0300050b074030701200d0b035010a9226944806180b02a10100429002c0c8030724110005845103081d00710018921103a035140d8100310164401100d034000700803d14400d144e02049520010b810900c1503841071204e0381c024000784607031881e1202c0740400c1641e9180e50140203001e10311034030030744109109805504581243c3d89419515022030140201039014201e402031445590080390580c0080300b02500ca0742d03600b4141c0011400020071034142000e45500003c05110902160600e54059500003800404644104410304801454000d41032403c40042e086814141c10300c64101c1c003c1300c00707403c0e0744c14100d4041054400c025594607054601074070159100c3c0214040c081e45008a841840f0b1040044c40140e900e02d82c1d0407610708070600c00728025071402001429085001c01c80005403050340e0b84403171440c4c480c0070300000981c10082c8c6c195105982d403a800400030b65224020418 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 148968363 1250 148967113 148967123
    0x11040b10030e12030f19090f20030708191a0103081b0714010507030c02030610060207091404150605063610030e0a0807030c0c06030606020a290103 65
    0x81e003105404550800c03050030708440f521402482801500800040003940c030080e075604004801d0b0007860210040c0c92280005400103070b4235880702c814021003040700340e14400000b254804640340c0d1000d06659200c20f10802400340c000c2c1d08200401803500d040096400d0080708082c0f1050440700e8034000400c0207034001c807840c0100044203002c0c3e00c40340294046111400010382001e510b444107200480613140402c60401400240410405001d603043d00c0c03206070003800f204c2d00d904c4c0100c9100c003040940d00481016200f1a0000070301c05803603008904a5840391801d6002544481c4d4030140311042040740030501640760840030038151a0003028009000c00000c1290f161f808481d00c600701440c2c408444c08035140007415094841c3c032045078543c0320b61128a4000b541c04511003096042481080f4020602d90001901c401031550003500a00440d00a40410a5140d550107058003114024407480c805a0007840040300490410f0448402150401070b81144001505000c048200426001195 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 148969613 1250 148968363 148968371
    0x3090203070e071e170705070f060606020d02011a100528020a0201090915030206030606090306013506060405151201061e0303140a0e0d0501020903010b060906030411040b1003 77
    0x80139101c00200ba0000d543c83e41000031044415580c141c0a01000070820340501c4800120241040402c0c102061100c3e0080010010b490301c80d0b1009449450803100c1d1760056082407503407141901c144844900001c0300808241588038a03603020b50381038000c80092005d048030b030a001d03410848003808001c6030011660281c140f031881d600c0094482038190300001610752400c4035407001d601480c1140710540760100c80d44c60300c4c3c2d40c80c1e0000800c40d00c1007a0440b5014040c03000001802a08002140c0703c005891041004046030341103500320307000c80881c588401c0d5100402240355401c0550000d60800e4854501c40f1100c00620b02094070100c81c0c0c07083d465241c0d95003000b00700030915080f2901c5d014600001d02d1143d20b2460720000c1c07400e1801c0384149003142c400201814518000c6000c1c002c1d00802410081e23401c4401d0903c00d000750080020140079500704080b011807850000c00302d07a6900c0c001440740b0305589450b191001c0040e0700c64040358100c2e90f2400005184d544454818038595002d0303138046 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 148970863 1250 148969613 148969637
    0x203130f060f0323060402040b131403060606030112020f04060e190b010509130b040c09030c1d040b04141606020f0304050a03020607030306050d060b090906040b0703090203070e07 79
    0x1040d00e00041240000c1500e800c3c0032018440792280151004844e50092090907155040054028896544226010140040c0c9800f181490307860041c00c441d40e240c910751048115800303140e1070320300803603900307070b002208000600034140901030103250380d4001b403c40140700d6001c1e804501114626003004044010a0040055250721901000440454080e06126441c9440d0000c3d0481c0140742c03180c4d10500d0482803c032a02d070140d84c0045c03e02e1030024004e020b03500c4405000b40549600740004e65071034903c24008204111804460030380c060845a4080b1710756100d403156104204040c02c02c84448640c1102042d0119082200c0c4020b24811000b20030250325020000e464501c5411521400340c1040c0310030030640d615001c81a04507901980c606543c1e29071468201c00030411904143d074407250100c80304090290075404400d1042064072070701d000c1d880d88204940d46001c1154010245080b0a00080a0301e00c170317400c2940c5051015044074134854a868040d2101d51003150344100082c9104542 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 148972113 1250 148970863 148970867
    0x504050403031a040603020108060d1401050705041701020309031b0a0c03050d0f0905150304030909020f1908060904120509090a1a0a06021c05040305100e12040b0d05070203130f06 79
    0x70f201c2050844003006403074615800a030008078000d06280c4500410801e20040c800c0005481c0c02070000d140c000c204038509004d0103445e5402c64051000e00072404051042d00881c1482180e0081000034000d506180b40440d00300520041d0b00d0844d907090040030800000120743d04450b4010f1403017034000d00740701c1a18000007001940d032001013400b00702100d00304115540711800a904559808803515940b95100d0a043d04e2207015503200101d03c03440090f80708040030021002e070950700d0307400d07042524000181100301c90251064403481e500601f07400c0468009806030140c4180780b94075092503800c150158000515205007200c00104480c2c44032a81d02c2d80028030101101c503d8822113050804030704000c0000d5564410500ca0030500000311f91841156005109640045034002c0440d040c20400700000b80180a0b9544103110b5882482c480c82e41c2c1c2c4402c82d05480c141d85840c0b880500b843c40e050122809810090501004c2d80000c2002d480110b1032007159070040d2100f0b923034030300340d0034070b03107000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 148973363 1250 148972113 148972151
    0x3121503031101020406120c050903070f05090a0c0819110721050c03070605070c230c0102121c0f0e0f06060d02060901080601140301060906080c090a06050d06050405040303 76
    0x42ca6483e07441000244040741c3c101160203400c00b2203041c00610240e15803401c0c0e51510402c0460350b494414503000056903942c2c41c5aa0003078130400c6d035103843c05465148011045c0c500b481c50803008181504001042003400328128051907901ea00c01040c0d441c40c5c0011521583d02015042d40c0d50003202c080300c180305c060f03c0c1d0003c0118200380340141c41d1440b1101c140b07489004501d0028992925400032903d02c41c45904c4081c95150081548803005001020208100720030010145c0c09025501041c8220760010681c00d110398040000750746004140540b94040066002c684400b445d40c5448214508046109a8103001a070100030102c0c050400720042c905080105414452082c204541e401601d0b10802d076801e2030741c00e081c05c0c40240c440070300684140b02d400d000307007050f904041700015003a50f129480c402100d2080d1a41c150070f80f03030744050311a03521070a4007040c1c011110410030030a40d403146c0000d103103000c3e201c480002c03c10f480740000340c262142603070150002070311640f00568030605007003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 148974613 1250 148973363 148973387
    0x6211e0a050604020d050307051b10111207170703020d170c1b010f05070e0f0604030c2612031005010507020d03030e010209030627030f030c070312150303 68
    0x10090240e2001541c0d041ea460600600c0240910241d031281030401804000383d88541e9070040580d14000b000c0c1c002401e80006500030a4800c0c2600b20703014200d40c0c021103200c04082c00c1c000150840c02c02c00c6000d15515030010004840340795040016003c1402038001500740c95101e580070340741d0034400400041800480501d1085036403090024031191480080495028082501c0c1203280040500c21042c014020018034441a904160410044d503a00250b0807051034001c9603001c100d001b418052240a0241e404002c4c03020000300014002d91722001080300381d20443d03c0c00601d852a801c0da0085c10a28011440c21b04118044140401001d0107040440900428a8100c2c2402465000100c1c0b1501010025042c141d417004419149602034040315407503103010302102d14500b0070058014810003400080280241034204681c280d01010045500e11441d06070f9460454403003c0044086a00c228012000e1003100c1c2e0881103042c50300e02400c1103d2803036150b007410b510300d541805499814034035 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 148975863 1250 148974613 148974673
    0xa060803030906011e0305031c0f1a04090c0f0b040807050d080d0e0c040204170c0d050a0b0c040302040e0c09060111070b130b0310030611030609040b0621 68
    0x802003002d00b4900152841c11203013070040c0d80c0c1c40310305510491044150079400103401c50000060309a515002c420154074004201882049003164010448048444030704d03203038000140ca0941130403d4a05a009003401b00d000301401c1a4040e035410800d0001d0300e49602c040801c0901140c01c011806042c8400f000502c8140e0300440641c03034540d503424580c40340d18502d101c5503a80303080c0640d0200042000e81030880b80504219034881d12604020a8502c1d4000d0f04410791080002c40211401c10000c074541803944103000307081d10280750b80d40b082c080391700901c0350040503024400000540d41c4d82c0210810f0705000c10140101d812349005004822600610680c10b1102c80304240c001a1030000c0d442041300d1803900e0568039440e080754240c0ca005203650050050038004024002c2110700c850340102240d1003040b040140c841380007100000784c0012100030b6070103054600002c0104148042c0325030b001030001c01850b0280010344180002c40001103c10751070340d010b5030402080c5ca43d07800240080312030013 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 148977113 1250 148975863 148975867
    0x11041104061205240915060f070213140103021c0b0c042420100e0105060108010f050a0308030919060507110a0506010920041e051c02040b2103030a060803 68
    0x134501083d40413081c80c6040c0c000c103c1080007860840744805813400040c0b009158075510345c02d03070b1400d54594000d400144c1c0329046d0f4a00c00c0003c03004c1489032081d440210b5005918507032a5070200030701d03102184a060703152444005448002005024003900c6000d0450095440c0d40c1045580910b03110303a40a90380c8180c21a0404a003080c3d00011500303030022501c41007400c8015820005802c182d0224122044a4140300161508070410742107548501400ea0764911143c2c0d80d001070b150899818801c041d003108440e20b0178008120090025540015100d0884400030b61340504140c40741168a0f040e110f041c2e07180c0c180300d0b44590000c0c40c56081c1c040b100090400700155124551a1501032196111031580c80180303800c0401c03980416101032441011864417640d0303c01c07001c51201d10141140040c8103000001040c0c1c0d182c120001c030304035200702c408a85106007990a020040030800c2d84c082d4040c2240040f12412a000001012024110310280d82ca030300700ba1081c2e000740c9004e500000660b400c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 148978363 1250 148977113 148977151
    0x3060c0f0e131808040305010506150f0906071e0605090c03030d0905190b0901050601170708060a0f03080d050a060302100509150307020105070905061611041104061205 74
    0x100040481c400401140e00c0c11a0a5941058030300070705900f070400c00d01c1250142d401d8107004030400a841201d0058000f0300c4265214803c001004210351012400c2c00c03020b00070303d590b00c04440041d0002d0503000d08a030345091055100c0440c00f6400c0d1800d00d101c005628010001c1004501034941c0206002c0020811000107900080d01c9008050041c100a42c2d04c82d818814001c00304240380061040354020081241c803800c0c0424070900807907548a00d90f0a16008c110300c0d500c40e5075110444084d5081d14078a64071242011111200040e103000c2d40412455004108079480d42242c00046104c0e054441c0d8804491115000703907a0300419800c41c69240a40400150f02e440361a02425070051408540e1800e281d80010080c504040c800b41c01d0f142d0120401000640550013a800b607070080d11070160550b50340003007000511900c10700f240c80d1104445850005100303482841904000144041401c071000007401d1440d41003079015070001018424203080141087c071400ea002002c1780c20920020708 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 148979613 1250 148978363 148978367
    0x30d05040b0d0b0420030f09060f0408090d0204020409020d0501092714060a0e0f0607050a0f0201090f05070317040303020c010804050c040501180e16030303020c030c03030a020403060c0f 82
    0x2c0c049600740081e0b21005400d00700d0340c540e40300c031040030003080c42c03200d02140c0c0b150b80c0701c41500100d4941c03540024040214602140000d8211300c41c84071000d00003050303581d5581e0343c0c11a8004407805500300211a80d5000180d84d1800500050266080c0058031001c42454040940341d040c0d01460049142904002940c0d40400c8110a04500d801c082207030000103203001c14101200c000c4680d0103000710000d1010300e8610380c10004100003010111006040708c526404e845850075205040420020030040c0e50301409901c2405500c840c0d4000094061169101c04003158150441119640c00c1010148104854243c071480c081c0482d0702030702c2c00c0500310364000c9e580707100030310b840c605100010000404128007001506a0650040c03c203000d19607440440030009001c213030710414054281544824001c03c0000d0090301e55180102c4600750910316201035000b5445107015040c41d0204002062080764104015800740b202e4500c0180c1c0c0d03902d90304080c422940345402c1390041108921203000410703 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 148980863 1250 148979613 148979617
    0x31e0405070902090d0f05061005030c090f060604050301090602090102160612090807021f020c04020a0221041e031203090b0a110d110711010201050105010504030b10050a080c030d05040b 82
    0x882c1600c0040c1ea03a406040064201d00900c00c00414220444004070100200801e98602413a0342e13105031319880e0388400805440305040741d03c01da08540031200052151103000c04250b00160050170280c5080d4541010074250b4914002c15541e4a400042451f860759042011814900083d100c50306c5080c1002c100500e240c440c500101e143d141c8172078500342030007000e8084032501c1d9401841c0b0450501b010303510b0799654014401c3c10340036000b400c4021601d410b260003190f64901d2580d002e0903410210080100140c011076254440c80c030030500011413800b400301842c010394008200041c5032203146241a07124100131010200406003403d89050008619600312604907840007008a5043e048946030000e42c050803034101c000e0b40c1841d01c103102c10032a5000410343c4501030010404c1080071040160700b0f0362400c0c400d450001e08100700810108519004103a089200000c01d04116980c0700001120041a60000c0344c5a400219000b0301510f4204958480c48816041443c200751a008441c0054 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 148982113 1250 148980863 148980869
    0xa06080105130f0f020a08070f1d15091206090c0a0f0501050c0f070603060905010e011505031509190e060702190602041206020c21070201050a03140103030203031e040507 75
    0x1925001040802c6043c0e4100925180301c4803011034a0307201c0514020115102951402c0110700c4210010a4040c41078030000040d103003801048000c0340104050140701107800e80079003080e01c0103001308041641d441e0700b074000140d010b80092540c0e04001d040381c0e04002d46540d21900c0390305d0450040040c00700da04950000c4810034200603468024000c8080c1c01d018648182039900d0144240101e2001d8056000400b6282003030b500300000c1ea00d43c400c004c02064280074000141062107208030245214200455100d840000252614490880880c00a81055449030003c03101c03801c0c1c02c103c1508601c100001118040014800ba0030031810103500c0c0c500e10245012090040300075001881400d8049400070100c1d0f071141c400024950501c0e40c02500075602900003802200200d01c41c580c0a03404100780c0c002101c1c40c81e407400b00700c0e9005503100e50040840c0c109040c0c54001100207400311442140c000c6000c0c0d0003441da01c3c40c0c00441003003002643c10042601180b44411720020a600255000039 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 148983363 1250 148982113 148982149
    0xe0403080615120a0f0606031a09070c05010e01050a0c05090d0201080709080303090604020102120708030f0a06030807050f16140d0302190c05040f020307050304060b1c06050103020a06080105 84
    0x2c84080203102c042207125440100c1c4a80d10403c040c442150110b503c001c0f03034011500d10401c841d0b525010101d0649041c481e0030b00312080780883e000c4c13551a25000703858100c2c50f2401c0505001f10541d0300c150940e108003042c0b0702d03165580c0c0b04012845146014089a80d13495142940c60700c291f400c000ba441b546095806030400001d040040d29142c040c44042010301440c108681d22880c0440c0910b65034041190102d00600611000701c01c40507844c019110400c1d0702038240b50841d90381e910108910b0307400904002246407942c1e4000007160018004000007400352001e8034040789146400c514121402000c80c070f4100c40814200122525850070041154085542c20003e19090900324a040301c001804140145841c45c0725007001202d001c030307004687c0e090f18180005121000b0a004a002c110345000220301d081000400040c041e0b48280d40c0044000d0107841d0642684546403680e02c0c100341c0c101c40440e544c9005205602c1c0945102d0010241403038031054960400000c201c9101c14581c1c4100 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 148984613 1250 148983363 148983379
    0x30b160c05031c0e1917030106090603020702040914150603070f060c05010b04110d0c02011a0d0516060509040506030106080a0308150603040f1104151401050d050a02040f0e04030806 80
    0x1c1080c02e80107400b00c00c003203100f118061803041408540141c901c000c1200c840030121030071b4040b05004800e5038100c030010340380d5140407444c0c20b0050b4041d60100d60100c0e44140c1d2210385d00f0000d042007500343c814402c4403000308501c075070b824000d12014401a2000344250300000c420403070b65000e0700c1c01006403030341c4d0b10701044240c82e503180041c0503100301420207501a06100c40203e03040301c904040d05035002102d01c10300ca0402c0c8008281d0884040788000e83c502d000e1000341820f0b1303040072075441021920910444000a5100d90b5078402545107030002c2e0f00054000900b1002880d003400f078290040d400b10001c0000d0f616203600c19544800240000301402440c50000326203485210f00c01c0010200509502c2c0d881c80c0c2480c1c02c0500540c4010308035980d441c140242202d40c1840c0c881c594254402611580c503d134103000712550550412082c0078104a81009a500707040128054a4011541341d003002d0f072503030704142c080048080e840e000301c511440008104000301c0d50021600742c0055040d10910 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 148985863 1250 148984613 148984657
    0x2061606020405041a01120e07061103120c0a020708010510090908040806270a1104020f041a0901090605130b0a050403080a0c03031802130506010306030c030b160c0503 74
    0x1038081c0f0b41c0640c0d405803070108000e0b19440c0b540440d8909131400d907546401440901d40d00411260598043c0c0102d910109051003002c0c0954804500c10001e502202d0800109102501380480304494049840b103000c00c640080310f404210010250034000024080352038002d000304440034152207119446600d4603c0d82090111030800c8402518034482540e450b440c1440c00d0080311481a401045040c19201c0002440303a0041490020b082d408000c0e200c50070700304002c10020350098005540700c1c0c202007100280081d1010959540030f854074142d40c0d01c503000ea0001401d260015407100d0140328017005891010070000c03841e0400d41d1030400707c0300c5e2030340b0000c10100c415015a030401801100d00082425090b50004c8550f044e65111760741c00d01182054444005103c0d2004400a4100c0300003100345560065580011758056418900082d0031a620b84840740110141c0d44142d560340c00c100203100b01c0c24219030300d885005829042c51400380e5459070703032503640e0b101d240f10700010450740d48440c0f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 148987113 1250 148985863 148985873
    0xc090c0c0708150a0905030a08090f0109051c0905010917030d020f13140303180f090f070e09071704020409080c01060603241703041208040806090109020616 69
    0x650100500001214640c1e91552070302c2d03640388a0005030691402c000c0c0005501d201240c055591a80c1d48000618200001403100b643c034564007400c0e801450241a805160414091140c0528140200028910101400d0300500040007100f08401005000001444588d801c10304080031221341940c2c0c5e0403245904034810703045000d4035107400041800003604130107194507a000b40006121011100b55580e507140700c16aa410f800e00c1003240c040d00144040c0d0f800300c1c2d2168442e000500080d0100360343c54009000100e207610110b4151f8403900560062014041d8030020ba41c1800b001520302021600349158050300302110004110b0140000000003001c40d12990020a000c0381e2049000d070b00c0e24184901d150190403540a0f410000b46407404900b40b8038504801c0300c0c200b41601001850f20350034011403400111140d810000d00b444100400218400658031180031f150003180003a4845042c070554506103103000e00190440d0307041c215010050303582e090444094a05003110281c3c003c00920341 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 148988363 1250 148987113 148987117
    0x30201050f0f040f03020f09150105070203010e06130507060807090e0a021306020c040e030f07081b0f0d030b0931060e0a0515090307020f0d060e0f06060604080c090c 73
    0x45088084804100024042d004807210429030740301f190070322503826030f40d004d000740315004407441d0484400502610415502550007484958005400401c01043c80c00003980b40c041e0903202c1d4031f1070700940700031501031100600c000400745c4a64900784a81e82005a0001c103001003d0040e0988031502e20041084401c850741201c0301c10301e8a6180841d1b030b56407140b004c0d4403000780440250089003880350708540d802000c0111a603c1a030382030014207103006512614015000680100441480118182c0c1d51400c1004081e070945c06d46001021808003400c030080a07120038181c2c840c01078428000348804e241001e0b40050340f0b1421101d06110708042c1400d030300c1d9402d081e00780c0900003600d8240c84443c9018003280e194100d50080c0d044441420309055500c00039542151206140d4109219030001450201d80c0404442c1008101c2d1081c0005a2221000c503860550050442d074440021021407001c140f00055220344102c0c0c04508140c509101d55443d01400e50030f0760310500514000a08142002c01 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 148989613 1250 148988363 148988377
    0x140405040c08040b07030b06030c09010504080a0b04020a0e010810150f080a170304030c11130f0219030b0616080c120a1d060a03050601110f011406040510030201050f 73
    0x80c04100d80718080502030032403c1d1000e0f5100d045107400904403a010f4055010b03214000303810249036076101c180d680d080e0b4000820160403c0410000091041020003600034014040e00c070340102414144104080706000764080c440c0c1c50040c2004102c0b4480215000300c0c501160a00441c5401038455540d0400409400c894112180349102041c8000009200c1d0f186511031400c004100200d0b10081c28940011a80180003d0805800100084078011910000340300545040070410900800704191044140d401c03105541c00325410030440b0702c031444c3c0c03442c0b03140a0900b000381e0100880460050f11a003100c042e240165000780c24200b12041c012514060b003600c0580d8001d4034404001c0700e245c4c4c0040d1059000401c0e107031400002c4d41c40000100080ba100a00141c0b510901c032100368041e100007401141400960090154108824418003660200e2100002103900d2051038840c80884040c00c600d002314600001c0000520580c042c0b81c007941c0c1c09080044d140d100030402c0e200184030380340c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 148990863 1250 148989613 148989619
    0x501050a1d09070e0306092e0e12190905090a09150f05091e0303010e15040c02060a0f02071205070f050304080604020a060f080f1803070506010603110a0e01140405 72
    0x260400c4411030b130100c501c0c0d541e2a011400e541141d12418030040c3d807018484602c009130300031071290b10703109014040c00080c840030300d400124070240040d070690304140303c1c4202034030381030000a00500715445009501146602904101c0c2040d403c04020403090130004003241c404030354629440c0240844c481450b40007100e10791041c440b40c0700082c400d6003e05419501e50780e0302e2047d80c0e503c0f00024260460840f05c0192a0020340c1980e10300064124003840103008892010030001e400c2d44a91030b180a080041c45846d0028149403c000d00010100c032030b80f5100c1c9920358414400720000841200810030700e0306061a00548590070b07410041c03250000190010002d06c4001000100964049011481140220f810348a0f240d500c101c240c03182036a10b03491034001020180018102d0044840a54108203048100c404005e08100702c1340c61b680c0148002e60310782d403200b40100180780d494020001032100c010031460821070080c0700500104820815681031002070002d603611400704070140e4004141c01 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 148992113 1250 148990863 148990879
    0xe0408091302030f04061a06070c050f0909060406051b0d05040c0504060503070308031f090b030c120a020d03120c030b0f03010b06030a0b0d0819030c020105100b070507080601060801080c01090501050a1d 89
    0x18500ac0702e207542c252007070a004918862480c403a6203861102c1c244595403510250a4540e1076590380e40003003d000308104a8210303d140003800c1c0354441400f41401d000c0d08940003070b250070503060841030840035078006803180341000c4003071205803008200c4000b140d50103140a034607a15142c0d0070403020980e014903d40018008100080e00d00c0103038221540341d010990070f4071400986030040c01015000c4d423500100300d034025817141006042c2186508d80c41e42c00b0f0b20345040701d80d078017401e50340079507507005241c20019441d0f4a106440d481c1000341070f00021401c5000b0400d1107008400b25030140401000d10129942d40c1480c20460346503210300100c0740ba802038003956640340169090720480e100000c941c001a20388214062814014440c141c0607246484281900740d01d400301403c038aa00030a030468060084520014400e20f0810030503018000b940c80340c010710b6040078a0107261021542c60350b030422002074010085030340c00c0720031101c1c070500c580760084907080104405e6000b1715030201450380201d00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 148993363 1250 148992113 148992127
    0x16121a09100f020304030918060819020405010b09031507090308040e010e0703061a070206090405090109051006180c0201090237030c120c0e0408091302030f04061a06 73
    0x450500030340c0000d010104800100c0b10a503000700d0208840003004501d01560501c8171041800944c45103904021012032010f0b1241051824070412044200110b04075000c1a011450140145409070000d101b90310f0030210000c002a54134102900c08001130514800403030300b03451180544802842d000a00a55282e0765030391080c040342400d22480035002c40c1078011802c0c01e40301b405800221510b03940c0401e43c110003c44010007a5100242c2280c0c003800810a031038003500c2d54028070340700e1880c19000013210100c40c1030540c20428518204c081042c07030b06200703105001c0484a4525030000c1400000303450700103411b05034010900808040e52064a00c550303101d40c4503143c50310ba0001d501c4400000c0c0508c07000e40550323482080310300004090100055040c0001000c02d240031030404d01420650b480d156582e01d00d980c405005407010740b001040018001042e040c14060700c0b21108001900318a1b524050180894462024100800282e15801d003204170180044645901c05402001079540f011 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 148994613 1250 148993363 148993381
    0x3081e0108030403060507020a031706030a0c33020622140d0905100203070605101d011505070f020904031115010906060302030f010e04170a1701050316121a 69
    0x138401240c525041034009012103101241040c8041e0741500c48808886c0b4185640e03a1401004010b280c00d40f150784400340208540a070300e4801800400140ca40302d0110300740c040c0e2403001200d2030500b804c20b412003000015500040c2c081d8886561900c4140c0240540050844a02c214001500311441c400d1601c141040110b648002072000341c44080a09589809220500111a103d03c0150b041401a071020940e00d0f080268084c0302e40131b821640507104c110301c900d0f2120700350b000c54898035990700500031412810a0150f20030b0041c1046402e04019685000300780d1a0075400a02898041010804142c0211b64803e003101c514415a140c00359046a80c841702c5000b4444c2488141c103080001070b905020f442160f00901d03240818041503030074032501f6800c6513006031044400c0c40c40d100419610000c0c20010b000c2c1c2120b00e644507400041da07562405103001c070682056100f40c1141600700326200c4a04d110104813400042e110764488500d0030007042030301e82c0031500e80701c0500802c10000000b07 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 148995863 1250 148994613 148994617
    0x9050307121817030f0f0412030f0e01180b0d0f020d0e15091e0309040f06090e070e0117010f09031808011104030303020d021c0506031e030703081e010803 68
    0x4403801800c1c680d60303541c0125010f0b2070704500c40b0541d5042049500c00081e101c41c020510b1030049220750b4034042c2e4848034020000d180240c2540000c90880200306102e600201c811403100d42464890100c400030000d041c01d01006220b0342c40d0303c0b800000c80040c4000b2a4202d6200c070301d501d200c2107480340010b24070700340640046440d8048a000d00d031000e00c0f018a03e00f40d01c80c00341c840007001380344400101d009200c172440412800c42941c8800c0c003094041e507030b03140503820800c407100300d0116202d8902402e0f4416100c1c550072910f070b04c1d00100c03002e10141e00d4224400c3d0450b14140740441134a011240c4090042c60165407903030400d8100407195041c960003103017a414044054081050150361603800fa4200d9144044216030900100004c20100c0d01c00c1d006444c0e1a444400014035004007600340c600504c4000c40d652800c103446608000a603e001d2258041011f26079450318109119541256201e10400100030188100300f00030504c0344034640c1c1b00d40881e4507222218581540c485c1c229560f40d07 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 148997113 1250 148995863 148995887
    0x63a080d0b01020a050307120c05070602030a030c0c17031f0308090913330f09030e030a03120e0312011211041103070c05120a120509010203190905030712 68
    0x10078144410242554400940e00c684940c0002c051030428a0300d9a95101c88001a002003080240b41000f06011030400c4c071144004180c0380d0003c560300c007113031080501600e03603914680c414081610320a0340800c1043d43c40180748030118004941d20f0703603210040707800010244201c0804120821010080040701e000070080090122030701c4071141e9810780b460305031001d548001051240c0c0303584d41c000c80c089101c03c030120980b81500307041b03110100c4004c030100300c980100801d40f0a80d12078404406054100b02e800110401c11750203000100c1840d1401ba0082801800b00b680032030381d440d1540700e07a000030310646240035541d004090040d41c0d500c0140c40c0c0d0054540c0c00340da254840c001da8880b645890301c40c003042c1301c00340f800d0281181d4924005480c0c0700c042500c19142c1d4040c20700c0754007822244070300500a50040391038201c1e1246c00c140c458002c907540288900a5a80704005000314a01c2c940c01c80b4001c1c40703024030301180c000b4003803514904500440000030001c0c20300c500b2902d07859801074010492 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 148998363 1250 148997113 148997137
    0x19020109050c040213060804050a020d112d060d110a08070909090218061201060609180e0601031704030602030f15300f0607090602070806063a08 64
    0x2048042c0e8100401c9100708400100314481500d001c008040c000c05425600500031030694003600400c1c1c0114124515440c0102c0b00d0302c2c04d030b4804401e03034580b0710302c29540060408080c52840f1000d5036000507021b5620541031080340c0103d80900e0340b454681040e908500040ca1050b102d03401541d010713010340c0045e11520040741c1054004240034070103100d5420656001050040180076510a21030b20440c06040b040d0410707402010740c0d200b0306090180c0b000809080d0344402c00c407450034140c0d80300340030b082100b01d003602c0c20442000744000c0c001414505594200962100c803180740d115101c03ca20841c1d00081a0324004000c000a024110002070b05c641c101c640b5469442515400b007088010680301c8003036214401c00c0340508480140c2e1304118040b8000b10032150406000c210051a00f4170032980400055100074081c442035070305111060040c2141030042600e400c040e000220f01c24880561498003014020f041300c1d08100d4000c0b400018050551000b811070407500b400d440c0c5910101031551 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 148999613 1250 148998363 148998373
    0x20d45080d05090603011401050702092806230d120914040c080c0f090a0905091e0d05031005040504050c03010b06070201080105040f0b0303030a06060201050c1207141902010905 78
    0x1c040d4090b000f16100400001c00140c9180e007442600607141b5040c121041c100441403007a03100680303560240318001c0001c21815145000110105d004071220800c0c00e507980c1c1d003000010000301c484031030b49000c86424440c681e149a010480826005a500c0da405040c0d41c0084030744080486c2c00510050680d003000c1c800c0c0b41c42c01c3c0301c002484143c40b40c408444c0000fa0110001414815811002d080c40061014255242014140001b464110260010a0a156900b081c440584810405151030407484140914000c8c03110400f2070f280c0000d4240c0340c09002d00000052540c1858151910141c50300400402860030a428903030750b52510303000498040d40ca40032120310a03240080641e0b8256505a443d5607441e82400c0601c80036100310920188581d0701c0e501040800d0b41d0610140d881000480e1000420900d480c400a0940d50302602c3c0300070701c42081046040304548488259882041401d140d00d80381d0107492110341d9403003a40c400072125040720b03a2001c0c00d65410342016600030b0180088407 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 149000863 1250 148999613 148999633
    0x9010f0e07080f070f030e070b0306040b0a06020615010318080903070e220c080111030906070903080a0c05070308030127020c03041205010f02030112030f020d4508 72
    0x52900030303043d21400c100c40c850b01c1c000350340b51340720700c1021907085140d01d00810555660325a051500f20144c0224480441c003100b04002802c2c203100358081c0c40c2d001c0390b10341b10301482c100300a0341380c0c0e40c00b4040400305c52a41d075081d48543d0298010100c2c566110200da01c5090b45030a000000d41c100201c4588640500c00300021404c00d0449070a0103504d01100410400111400300c2c00003050840c0c0480e4400510f41c40000c52078828800c0d00602d905080c1c1c0c4968920744400a0707411308900820001c240305140710140041a07045060302c0c00d8000300d00303010003c40d54a0034000c4c50009242c1c801403000c0320000021a0014802c03071002800480140c11b2290030b584140130324180d009082d0310b01401c0d0b00a010401c04c2080946108002da400b4100002d40b1844d095000020703a807098202d01c001c110040681010103a101185175410f030014400f80200c2405204020000074420f0241c607603488025030307087d807021340244018540d040c1d00301030568440410620700c4c60041c25480340c0311060140280300 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 149002113 1250 149000863 149000867
    0xc0803070c0506160e0d02040f0c0807020d03090b0402040e0a0210030c0f0914010305100b0a0504030c050d0b1f090e0a020a0f0305030a1d030f0714010e0a1202040b09010f0e07 77
    0x302c0301404a515080c030174080a00500c07130100010841680e0064030703080c048040301100e110b0001d1485141d40c44008500d002d140c0a4035081010b4002e03020545441e4405003c981046419038000c2d0f8100c801007003c04c2201402c0d450b041003900c0c080d510120051242c4022909a480001080019201d12946200100d026650641d45102c0ca120004190103828007541c03181c0d010030f40c0700c40703c041d400c0352203034940a580020740c010180f50742c08240c0005003070061003040c01880c4020301e02211642c541100303654900020600182c02c00009900b251500312003411596440d1004d00300c410010007a80042d01d00450741c0340000001039000d0106088007283c0c03021403080603c2500d030020006c501e0300270540b00890742c2c0841c2404802c200c203515103003004203035401e00240683c007004c0001854494100208190303031903103450646062005030180020982c6800002400f2281413400d040811419400810054a80d101000d54010015800400d048031001122410b0360000d85103c040c60780d400c002 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 149003363 1250 149002113 149002141
    0x70306080d0c0609080712080105090f22020604091811010206061e040603020607050a060b0301021c0506060d0203190c02030306060909281a03031201150c0803070c0506 74
    0x5000c00007081182c00e18046915908409103d6100710b0200c0d14021160b207031444103151900400d40050010310040095290841c81c0e40c0e00034041c04a6082ca80c00c000c2c4000d40150402896801000c000000c05810740d5070300030540e002042c3c007200600804101d128a40c1d1080303800c1d0750032201c1100d41ca0051b40d242d440040d20911034a006401c0c031010021098541c1001e9289640d030642c015100c2402000513120400640f20040c401c3c070052034660711038607090040d00c0e408141c060080e0300c1072005181503902600d609142d11842c81c0002500d885000105180e48640f2009031102d500001c18044506070100c02069440000c110412203105020800c9072a0301c4240c8409074041003d0161003100d1410345501600030100c482c262011b02c0c08100420b0684903041d842480b920344e07a9628907058110500c0f840c00580c4110099417510280708013068003a041800381800d06150844100c440c5030040d60400046900030703a940f41c503032a2000b0300030300140c2c8401c800c450601581010030300041100c01 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 149004613 1250 149003363 149003383
    0x601180f03020319230309041419050c0a0c030201060b0703020a0c060212040902090d0b04141908030a0c0216030804140103050f2d130c080303040c09090f080a02010507030608 77
    0x40078a08410ba1103040800b6500c035550f5001710f8082004090625a214800d48101c8002e0101040d0a403030050200c07181c1c0c4120810019a080c101004c008c0c031411503408564034141c1c0343c2405591000303a070900f02c1c01096503030020b05003280c0000d2603c091540005541484505c2181040035070b98444c00c0407070300c0781d82c0040d200621900a00c000e1100c0480c5401422201d08040c0c1001030300c0748552a04500f8a400359005c2d1800e42d90b1200d0301078281d07014441d5480c000c450000c0c4840c00c1445a0701c5103020300c802450142040d44c1c82c02c400458910912407031001e01a1100050703030440d00e07820700e903609a01610450151500d00307065007446500900510384501c400c00c0d020301c0308d0307a00d06141103112540d01c1c075003403a0711204a1007000c110a0ba11003c80c00b070b081152a90010040c0e0303243c40383c0c1008054211003c0f591080c01000006290340e10b100041e150f40003008181c030b4803d881c2c0071008180440c0000d08032100803a0009025a0542c000744c0706443d29a010300046d03555004154413810145 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 149005863 1250 149004613 149004623
    0x130b0316110a080a12020711030601050303070f02060a030b030a03050307031401080a110a0f0801060e06031204062303040501020d0605010e010c0b060d053406170601180f03020319 79
    0x1142c1c2e00c0c0400c0026003d0030000c0c00904180b5031000c80104c410040b6800000b0880d984840f030000c0e01903030705041160a01510060b40194a012a5a201c0301c02032600c0080080c0300d18000217100c051140f003a001400d0030a0301a0884547c614a854090600d800441d01480001c1c5803041c1504022000100c85040314101005842c0519050711010540403566124540107125038800165081300000404010640d10000040c11414801c0c0500325410140084bc440e80c000d190148901802c41700f140d084445038140070705070105c4401c21460901800b619581c8100b008010803051000c1034000740941113040204001d105d4940d40155002c9020f000024001043d8000c40e0f80050207040405400040c000d01c020f50703650046e521180b82010324030004c9a1501a1125900b042d603107071101041480101e00260340d158207110f070081036184002043d2034000b100402042c00383c2d00580c204010841d0b55500d42c1c4510b615480e0700c0301003000a100c00c80c044e125608656541511400c540100e03150b100d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 149007113 1250 149005863 149005873
    0x216050d110a0809012006090a0b090a02062b05040b01030506100b041509030804170d050412030e19030b1006051c0225060902090f15060d02130b031611 67
    0x48004450154031580c4228861101801c05070401b042007140f41e11950301940109154070700c40c540412040c0f030151906000e58800c1c50b801006985d5002590b4210001124240520030b18402a003481d041c0c00c000d1640c030717600d85030900081c802866641416240564120750352501d802140d40c2110103103110b00c40c601d16051000340210500381e41c3e11640fa50481c50444407450f2240c4400b10554000e501903040341354250b140107030342c3c0d000340050050030195040c000e061624101e010407126191041c0101040f003000c2c901d034590b503207914030901641a12108403841503100c0c40c6c002035000040c4c0c0c4601448105500c00280c8900c540100d40002200340a4404c0b0641c02500180c042d40042d85502c40304440204501100807404640308280d0340140710100d0402c0160050100e0f0b100090b00050301c0072003200c108224000941c82ca0f032030090045c1c40d00c0f41e071a0302850740340d002030090117084561100104000541e51003040041c50081c12004604420161081030640b6140800702c100c1c02c0030313082 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 149008363 1250 149007113 149007127
    0xd0e01050c0f030f0301030b0c0c120706020409091203110c030403021c0203060c0d0c030c020307020928050603010f020405090c030a111605010c020606011b060216050d110a08 77
    0x89140a000d07040c000d14102c0e11280300c050319040c10341e00600040c000c4900c002c0010400d1000c1104d009070000b605c42e0000380341c50341c078801d143c3d101d9250720400c0083d608002654020001d00341e04460041c032020404000303000c514039040c0318400785102204d000238241300f070300200b50000c0012240700d85003420045151910310b900b44202030036a07155041c04000c0c22068080580c4083c1311552146551081e540e80d40e01c601c0404ac801c584031002c140781014602003483c4413154000080b240c04a40440d42103205030b954000400d00f55205a001c072005e18082c103041e03900060035030455030041c40110300038049000904103813003c0780130f00d10401d030340942c900011800c0c1248034401580c1148011a01141c0c041440030b0030007241e40700360b82059003070500c1081c01d405c3c00030a2103104020b8882e0304c0600000c0c1840d20000b044211003822205c0780285c420044003c002c0c3c0c503411140c80841c0342e00907294800081c1071042c0c60f001410208804948005401c0e038034080042409039010b44d200004504040c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 149009613 1250 149008363 149008367
    0x901080105101703041a070606080601050d200604060309062a0f0e0301020a0903050c01080c090f06070203061e0907050a0e0613060e060a0b0405060a18030b010605070b06030d0e01 79
    0xea20f618501e52404104408500d06152544074040300056000c03140d5511864a480c43c212000f03944603a000760410b000520155a4691085015a0700902c90f0001030000c3d0141e241c80100f904d80d50356110740005400500107405420568080c1e0289000708032200814200d164040300101c1d040807500e0381180f00c2c0401038041e407180700d807600540c0b9262620f072000313801007822684000402ea01060280307104108108040000100400080c03914030740c80d00742241d04111a0050110441c450003c0d80f0700e4a03440c0e11000207071a0a00c0e001400c5900c1c82c202114510341490f000c8496500381189000005d080e0600000c8050440b0340180c14911505e1810103500343c0303100f01606480c5d00600902030b103a034800760743c000e14000d8241005403551a0504000b0000c01e81d215600046682c1810f110400807a902c1c10240e620f4140a4181225034541c441250442d12100ba0070044c94100300c10700204000342c0c004003904000d8803481100c0000d0700d401c2e08056840000b8501d09002500340501003500d54 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 149010863 1250 149009613 149009639
    0x911040b19050f030112060c0e030604031d09010e0106031503050a060f0e0604060506030c0a0f181103180d03020c0a0615151e140403080708090d11090108010510 71
    0x100580c0b6115040102000000d19103500a81c849499928007151901c1804a1845605502400b900302203001050040105e82c841000800282c140500022a8051105d400500c03000c21000100781c1c140540c0c4034151440c1402d001c1c0140e500187c0390007079080d50303881011018130130340307070060028240b410040c2d54203405440c2115881200c0381d2990071000111a04200103030080c1e104041c080b84902e010130074107140810b41c540740c521600b98160108180c1140c1e00e031490549a421010901405000c05e0002c060035010303200e0803080e20000200101740003104207a840d1240b907141501c2400000313090480176030280310000c1525800c1084a00005034155215400d031410040340c0b0059180d40b034550701d85071007001d40359001007500c00c2c03100f079181b03800226003140044ca00c0c24440a80380070303010340c10260300940c00020100c5000140c03020074804900c00f5224488802003011070707604010316008203140c2c4001d010302d02414070000007150762481806074502c514881417401c0d00c0c00d46000b145486034 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 149012113 1250 149010863 149010907
    0x150609030b04112d010822021309080a2102070b0606070302072318010e0103020d031124090105072a0602030103140d0203040602061617040b010911040b 67
    0x1314903482410603000308500d503281001c0008200544514150400142031030340d0003400d01c55414154180028292402840e90000703e8058440010840d0115034000041074046d0000d0891403022541086140d803100212400080b14900c650052400700034600076401804002440d00d0408000140241000c401400006010340304545089a44140300750150256a0b0164481060405005400c0c105081200360500384060128095894413004a81030707101808001c0c4902c55080000040c107110720100e5030521178110565948201100510100f00907104116482c2403200000400d0020103124140c4103c4058450310703400c4200c50915142a030507001603503900041444d8400101d80307503101540c00b86105d040c04480001d035196041d45822881a41c4804640c0104818042c030342e4041015a0002e4412465142c00000882c0c261500440e20305102406a0640d04100034014001c01441c121044500100251403004208610358451400341e00c000d10000c00000500c210030201100f01 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 149013363 1250 149012113 149012119
    0x40c0801150608190501060f09050d11190e0f0402040c11070312050c010203010b09010201060803030c0901030b0a050301090501050402040f091a090705030d0e04140103020906040e030913150609030b0411 89
    0x4050300240c413503003c855081c0c0000340001c000058104569402188610103000101e4030302801c94800da0354058400e2038960064041c47e038401e03004403010b8480b00c076000500402040c8565030300c0c0410301209036010468081e840340d400c0102c9481000d0048040200414101002d00002411602ca00780742454001c400e004104080203407600c080300030710145000e0850046d43c6a50b4a0000000a0079a444c0350041d40c503d80040040c0031000b801e080458440380002c0c20007042400302000014400030039a070103d80c141d401e02820000300030040d071002c2d109520880d420003203800300c11081c404070385413440000c040c06007545421450304021030300c45601034010003c503a071568442000c04d00b401d4000b00020040b803a074182d1074502c0c2c5450700403080381c80000c0e1a803c400c0d6241d03030001500c04502601d80c034003403a40c84030040a8606c1c00c0c0100d0340c1044000d401d031080740000d03140b80c60040001240541c0d0f200c0d820301011403180e105145200071242c010301441103640361a125081c003010002a1654 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 149014613 1250 149013363 149013391
    0x60a031109030f0a0b06060c1f090f080306150306030c010e040e010c02030c010615050a030905010f051e18030f0313120306060f08090d03020a180e040c0801150608 72
    0x5a03a002c21540e180d148000d000b50144d94120325000500c42c1014010b13070b100f6441030002c518030403000503000d0458040b0a0900020100001040004082559014003101d8804078a1000d01100d070008500030907050700c0c0b64000020340d20342c00c02c06000c240c9142d503042d0030190a000c01580314900ca240f9242d4010400135102c000c0c0403489084801c003050100140c0c00c085240212508284942001440c41c290640340404e5101c40080151054208007000c2c5a61000c2c00424410254000c2d40e4070b03507044c81c0411990800e070a039101c0c11aa40e0000c501216030b0000003401d28a40d4941120503061000f000b1800c0c001d101920724000c0d000180716403210a0003610400110301a040e203040220b50a450000c2c1407800c080004225149424a0005004c0c001c828492039070340003d9542e800014610700180c440030306080c1140e040710b400c174500007201462403010840041185034640101d01c1001d615142e56500c014a80c261000104195015240030f1070800c81d80d4000c1203a603511400c0040d500c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 149015863 1250 149014613 149014627
    0x60602030901031e050f041b05010806060d0e060108010203090c1f0c021305070e0f0f0112020c03040b040305012a080c03060a0b18040605060408030708130b0d0b010215010302060a0311 81
    0x200840f0002c840341c2070025001000d10060254209242240c01c2210901c6803400c0e0a009c00644000005080e46008941c005201000c200d015030028a015a03104192109544e403490f03024040d41090f69400c46c41d000306010f40c2c0c0c041c40d08244444001224809001c0980002042541d42a801040c1603804c51001904000c0020380b40c030030780344a1041916451902c00350f400c00e03c800e0b061048280c40c026240d91004107080e0b81c11403501c8806a80c03104d0302590718140c37400c003141103000b01d84c02410308410200d8080104503064100010070a000120355842d5080c05042030030304440b000d410804205004041000719810b031000b907a00c41000303850341c03034041d45e034250303c803c030f50300c4500e03007815003689030b01c240e440e91605004e541e0045c541100d80300c0c1880e0810013807588901c9103840041028000041c0d44d10b0540e0281c06110081000070b6045488090b4490141d000e000031008250041c0144901030302110010241e1906903038000c0d1403a814119449030036001468600c510041c03095082c040c0c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 149017113 1250 149015863 149015921
    0x306050d03031514010203070221070314060c040b040303110c0603010306050f0603030415030905011b180b03250c0606091401090207080a08180105010f080d0306060203090103 77
    0x220340352103640e000501d528004010100ca40e00b54003e0000b41001200c00d0140b82e82c0002a242c0c40c580486240c0d607120408805a840c143c1c607000f80d5285409100d0000080c000c000e15005080c1e10f0007000d0b40c1c0ca5541d075881c101d0091041b0701071031051300424041400402d103d01891714a6221500c1265401000c4800140d06508240c6c01143c8061301c4a040003110b07506081500d801c030a040d001541000e090040c80140d18548459000416503100301d08010712009401080100031005403001c180a0882001826800c1a9480740207084694000044850428040301c2c40f6542104803144000603807072411112a1450030224204001c140211021907868800d00000344400240020f5038000300d014140850303016403013559210f1040c40403030082041807084410803000e6241c041c1250351240c11100300300d19420190a502d6107810000b00345101c0c260807850560b4880c004030307404c5900b031200450944000c2c0c0640c0005030414808510154001c0c0c10440c50100e000008681e03040010903c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 149018363 1250 149017113 149017129
    0x70b03130501022b0c2a060e0f0601060903050d03020703020102131e06080f0109181205040905150123041d010e06190b0f07021f0801081f020901030605 67
    0x2000e130305116182442c1d421004000c03903054200c01c001480704018003000580002c0c0e4000c40051001c00c02e02d0910707440c0c07004666058860354411030800c480c81c01a22565590078100c0101c01c22031141b5000441c030140118040002c89234800001c088000c02000b08034007940128008400307540d002c0c0074020001049038204c1015041c0d40d2440f80ca40410f04a40c11a1506517034051410b00c4503200900c000c040c0d011941c1415281c24690100b10424641c46103103142c0100d400140200d440c411441111603400002002118440201400030b5140e103080180040381c054040b0f408205550001140c0020580410080283c0c843e0802d042565a20482641b0000d6112214401c002d480041c005103c5000d2801c0e0400b1055486444103514407510ba4000c403400d0082a044c10383c00f00d125901e000300c0904131800350750f01529040c900002407031050403211a040c0c800300440c4a5a001060758400012203000d002416182c00d130704200c01c10002c200a600980c0310604054031607402040d15180c10711 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 149019613 1250 149018363 149018377
    0x2205010e37150e04050a06050a03060e1606050c0606010306050105071401180f2616020a120503030f01060e010f030e03070210080106020f030a08150111100903021203010503070b0313050102 83
    0x790900b050800303c04010860f48020a0907450360f2522000384519201d5508410941e50b02247c0021070700342800d441d500c0d103003070358044400c603924410380407504581c40f401501120200c0e1040b950240c55850040d415030f01e541c0601800200c2c06d0011f000804e10540d420b1080002800000618042d00141c609110780d0001058501da02c3c2041e19004204a50580c9250483c841e07a011000302000c02c80411903100d402030705520414024001405d641e0756444d007000400c28a050007864001e14130300161030707400c12554112a0310794034000060342801030040404850301650b41c20610440160140c00403c04840340c0c0c2594030017403000e40e005840b03d500030003002c14151a142025890540300a250565620300e12000b42c00038060990865082102c40d0380140c01c0b081c04801b80103804004070f0780020046401c0079a48290308c0c020704580c00300d81c848907181c1d00176401d4604a00760322040c40c1191200b8400e1030303019031004400b000f05502110141d40c02040c00100c0001341d01d0a130321420b0030390f080380c7c1c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 149020863 1250 149019613 149019617
    0x615011d030d0c02091812030702120304110111010902060f0c0a05010f020909070203070f11030f0d050a0e01050301030c090902120304060315091e0f022205010e3715 73
    0x10a61410f40c034000000d146d01c402642082801e545506907503030f841d07680f00951090325140100200341018000d102c50441041c2c40b21896443e49014100b03012040082c0f007496000c1044110f1241d0b03070800600a4002c45600544098903250300542341c58140d03444111020b030b03180229103c16001a40c28003408215060030070000d83c40c1c011003401c2140c0200054561015540104250000141c5040c001402a47c05c80007110b10020168042410300d5110501036090f0300036030490491058001019249d09903050340c0f25020810803e00645152200380000b82a040b82c80b101048560080c0e0070210b00d0703030301c040d00308110700d100e400c1078918507001038001030302294441a000c1c6044401c282444003d2400c8031082c01a1081100780d43c0054100312010f030038180c0c9603007042145410f1601182c840109c40a540c440b2070010700c0300c01e45202c1d0360303010707150008000a00c0300c40a403520000140d42140b200b52481a82641007032050358058000026031003210b5145000505165216642090b5103c99 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 149022113 1250 149020863 149020877
    0x31101060824010f080c09041a040c090608010c020c101b0b01080607030b0f0405042f1c080406031a060a050c0f070f050d0204021b03040603060501020615011d030d 72
    0x350030b01c0882080c05800090403181e003c00200150000000d500401c2e8209550b040341c903480300d05040c40303000d20800b03d0003030b4020440c080c0810009007114000854100c2c0d070302044115100c81840d826154015001ca0043c2d00407140c0d81c001e803400d8844101e120302c56061941c00c4100542c0d1071f031400b160075801900c071843c42c0801004980c005101403540030300c1c585020000d10745c1d082c00042001800c2e02401d40a0380d5920000703810000042c01000b07803890203612000d28480402c170300d843c50400641e045405095407039808140110400c81c401e10032688144c510703081c207003018021402403142c4e2a00085180f11030700491309648980005040a0607071355500c580c0c80c0b500712a680d02d8444514003004d4070768800300c0e04000709031103000e090050320000c80700c41090006500000d4007a01a003640c0380e0000c48105520b00315084000001c100700c074141d0f2420700095594100690f01d0b0b0000300c2c0c600c0a00440500805150740c800c54030480800c503001d40e0129881c558002280c03034041c0c0304a9113400701d005 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 149023363 1250 149022113 149022163
    0xc080c0a1a13150206130f0f050c1c050c03030415080a0b060a0905100c020303040b2101080c0108130803070507080d0c030213120f020f0130061d040311010608 70
    0x2045c40341a42c029250514420f59151a40d5085000d200c0c91501410000c01c0c2d10340102000300a211030088280c00030a180c54403400d00903160512105031038211003074031076010f070a09141004001d9504641c80302c03100c3d0361041a04003064070703d4074005100c2d01c1c003d0355400079190607036202c0e80a000310302c0560307984030704481c1414140590700d5a03400807002840424400742c0c00603034000044a040d00c2c1c0014031140c50307501d0302c5092a810465060203010a85c003013000442d00c0768002460f0810003000340d8070300d1816160503203041040303114104c001d4040c0d0300c20000162003c0c003d80042900512482900340307001c214618410031948840e020300d001a4002a0b1101c5180250100002030b00300c00c0c8009500010075a901c03a04500c003104000d01074038140c0e01c11110b40c0e000c0c07040003003110300266400354149514a030303c0301402005000c0030300a03841c0a1002c615004103000c0015001d40070015040103071a1a1415a130001c0d40071901035045d900d904000ca11a0400c1c01100b4160710b98000328062002 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 149024613 1250 149023363 149023367
    0x40501091101021f0c090e0c070c1e030609030c0b0906010501080106020c0a050f04020702090a06090c05030103050d0c080c01060e1b0c060c071106030c03040c080c0a1a1315 76
    0x2045031800d045600100701c02c011590340c94180000013080200000f070300850f100050360601c003075902100c50940760400700142c03951050002c0802600c6414501c400d29100c420b03a0b200c01c100e403e80c00d44c1242c09031b6002e01c006038003607016580c46406818424030301d003203655644103218402c41d07000b40303544c115000421095030440b011078003400d07480c0054400790b507003800811146103440c401c8d00d1207201c3c10041032141d6155030703045824030b980141c000051031a0010b0b412015050360f104048480345403c51241d0103922400c2900d058a0b8041c01520008818010454101c0b003284820b40d854041086005040700c000d109040003450315401c2031070140f400c4000110703c103002c0d40c0c0e144600c01c6d04018440b440f5001003007255100b0801c064041d00c940142c1032045020a4034022190001c40000a024440c11840701031817003103200e11107140c6402d4841c0136a0f83c0303a50a13410401d410143d402c40900c10f02148007160107100c00015403c505001e0504480020080d50ba070000e222030030410004202d0036 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 149025863 1250 149024613 149024633
    0x1c0f02190810081209040e0d081b04050a090507030e0304230301150608180a0c03060e012904200301030b0c0c0c010507020d0210050316020109020603040f030c080304050109 76
    0x12222001403081c2e0f00e04812a03489958070075000f4840440019108803a54883d405030840038040c604645036501d080074080d11000e07007603440400717455140201581c03004c1600d08490a0718005020b4540e040d1500c01600042c000143ca0701062540f21110041d1084080010f80010454143c00e9402c1a04010710001c03260440101035010fa414142882c540d0020181094129609458029000c0d504c4d00c0d180c0c0446e003002d0001c0343c424040d000c0030200b4008030b1361906042da406420300b08030541040000e41c0c201e40d162107240b0410241d0414105a25800c4640300388946409040866000340081036070b04003041c9401a07441c11240400140305010424031856400364030160910720f00540e02d40c50640d80d403a462000c03410450002640e00864a822260695030f03a4050309001044000a00c041d006400c1180d06180c00c00ca890511080107205026030380d265030b00500030500e10349480d1220480d091661a05800740302c00c65121800123020080154459802074000042c00364040c41c003403450b2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 149027113 1250 149025863 149025871
    0x3070b09060114180601200d0e040c020d092d030b0103050d080708191409010f0e0a02010e040b15030705070201021605011704050c0402070c08070603050c1c0f021908 73
    0x2030f507041c0c1c10b58500b00e00b642e01582d0170401c242000e041c44881c0080c285011011010941014007030858100070701500883c0484504000315401d001c039a1926a040782d031040005040400603541d41c0c0c00b00500d4003004008400b2031080c1203501c01f8001e03c2114081054480e40c011103e644007003004109100c018821a1124040c42c80e28614605103102c00914010b4042c00007042c4e0092902c1c4012584160b90151001d103004040104441c58a805003500078410100c606848600700702c1c009010300c0001c504040202d50507141c800a02c6604810705c802070584004d03003604141c181004400015000000e5489110680d03070b050f0b038a0b03009100090800d06645042100d165001805019030380e00312803032401004445100000664490030418944004c18025581052001410341d007401424810072043c0c8094000b02c400c495a0740600324100c600c08c0380c80030003850007809481ca4400e010a000b2044807070700c1c400410300b00b140d960310808070390001d01c003441c4140c071000e61a1141a04904070ba684 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 149028363 1250 149027113 149027119
    0x50406060c150b130c030f05040f0201170c0a030b0307030c0b040311030102280c1e0605011e15020f06010b030a0e0703150f1104090203010e010f060c02060c03070b09060114 76
    0x211826080200d80400400c0c154900031171789880100400c10302c207904c5a00d24210b405400e00c800d090500b0a080d696002a0040c2c1c0001d03c10045490414142c0b540c10340100c5400a0342d0b8034203181c500c411002860103481642c0c2c075000721000000442c0000c2030200140c100542c929a8441c514906100f14003189400355010743d0042c40244206030080405043c14986d2458600302c1c0210707010210354241a064000f0504005412942c456805614a041125115032000c102c42e91320b901c502c060b00c299040c0060080c0040641c184a00441100405121100703401190416101c940c5405d0808609801081a1180100c1040408019401890884911391000d0107040e42152038240c0030b9000b0160101d0700c1501d46003010030317190282e480788402e0b400714618152a540c5803031046002e58828400c000c500c0c5544800819540a42115182200c40701d440750002c1091503805e00540b0341094032102010700040c0200408210604001841140003c001d031085604100030105015035240403140 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 149029613 1250 149028363 149028371
    0x105160311030403030509270403080606070c0b0c0f0708071509150804060f020306150f0c0f010f06051005030f100e04110301180b0a05040618110a0518150406050406060c15 76
    0x50300300302230310b07007240c00c2078140c07404e90341a03698800811200e1040034402803001501c190b002a480da1000c4c05810180032000580300d56450300c030f02040d070710703181405140269007207a2001c1014030800c400c0c0c0f401c401c000c0d003088030030195200c0345100c008104113070700c801207902c0781c0800080059501c5000c01c4007141d1001141141420004200d09001c01c07500c250440100040c420b0564040c481910b600a06950445118189007445c0a018109401804500d141800000304651510f44980d00c2801840d580c0c107411a42c8410041c2c01400c0c0240540100455240c00424146006804248914051007000301c1c1d840d844c10525003190985084a20004804c3c0351020000d0f040c0c0080c9a0001e800c1c1c2000f0880381c4540c00c107036004000035903030a0010291016000d0400c00c0e400e9405900710012034004440300c2d078400601c1656241c6070551a803020440000440755038000710402c140b03803005000001c0c81a11240072030121117072074200c0f00201b18039541d950208816401c000f9090640740030280 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 149030863 1250 149029613 149029669
    0x106081c1e030b040e0705040b0a03021302030a0216030203031008060115140c010507110c030303010509040609050a02130905010516020703020603070c0c0b0301051008060105160311030403030509 86
    0x400c8144400c140081024840aa00020324400e0300640b8010390020402c20009001000d05d5a945c140c038407a2601542c24072400760301900d0000c082c0c0701100d801400e4a41d9440c410a0329200035071004046010090b07080c400601c03c1d0b80402c0c0403940e640d00c281c0041d41d81c0d00f0308a115018041c07541c0e000c990a9440100123001b0500918014810f6003401c0c01c0401000803e041500c5080c080c018404015602e45010042c540c0c0d441002880099060025521040061818541ca901c42409095007003000a0b01040c000743c0395034404064180a1700546105111550004090b41312080c24136003415202e41812060240031b100d042d4000f04040751011040c807031300304043c0d100d548503c406449080c0c0840002c1150340214840d04035240e0009000011a0300d40c104082c1c50340003802005e00404040c61081d80c103d015408160144d98161507031030038580342c03501c140c20301700b0280021020420190640c0c801c50600f000944060352107915810340760050102484904405200a200c02140c40a501 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 149032113 1250 149030863 149030867
    0xc031a07020c0f03030408060a0c090905070503060120010c1d0301050103052d0f031c0b090f070509030609010624050319021c060602010c030603050c0f010e03030403050106081c 78
    0x4042e00c1030103558070000c00614100181c114010350b403069401c1e000e0032041101c20517140d800414208100d403900d032801511210086c084074000c540c81004240c040011508a41c051f02e42050700040008410310017401d01d000d21401e568112524070007107400b10001c44900106011a4815407030207400801c5950701d552640e541c0d0310940510746440d084000300c0d07640c0b0508141d4040e11300c0c60700c1c3e80c100c071003403001050116034940c40401c0c40c0d105011500049008044a8010070540d0b450060541e5255190b01300b1450914101801031001d103c010400000942c80034480e9a204007045000011600e1809079801c40c0ca01c0341080d420360715a190f034030705c07516280c2241c190303030b00245000301980500c1d0120007450000c1c0f141404140c00c1c480d4204400b83e0040075034001c001500c40a074000c0c005640000401c2e41034a0701ca0200811030f0b000450864050700b0310141610119005160291840511101003800c40c1d005030801c0e1510394494400340606507040110090184001044440c1c1740140c00c00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 149033363 1250 149032113 149032123
    0xf0605120f0a080304050307050601030305030f0c09060703110f0a06060801051b030f0a060b12040614130213021e041a1801110a02100f030501210b0709120c031a0702 73
    0x18510300f004800b080a000081040d11290355001d01110312030750b12810080c00b6a00120b420003031080001001410b0400c2613010340703041c01d9019080d01d00f0402c007075906882d05004100071301d0051140c0b40d525524a1410014502001e001c4d13000001c0f100d06100300b0600b5102c1c01888494011481e4011207140c00350710301206da1000c0a441070703821585074011004090821035201d1100c812001c24501d07000407210712214000d0784190810001c03500c4160380b450640c0e500303c0d5294554042c000e811409818440200c070051310010700018a003005091720500403420840c01c28104440100e03007031203102e500804041c11050505501810041040c0b20304420601e4100c48604002c607500d055a0700c003600304003241d40c4990042103050b200c0d202c03090040801e04115129000203052000000ba8400c0c100c100f0040c190544011030b26580b040c0c0c40300d00c013441002d0901d0742007055545000a0a101522503c01000d00c40c0c8090784507140f460420100030030710188060803440c00b903810f2007051900010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 149034613 1250 149033363 149033383
    0x1020301080c010c1109040614060a050112020714030a02010b0a08030301050a0302040b011e030507020c0603010b0d1e06030b01091a030a0b060d060204080f1603120e040603060f0605120f 82
    0x3070b00401c80074113850112081080701045c5074202401c04103000400c031582c0c009a8443d0f5451034408001e6132003400f0891040501d201300ca001c110030710700807080d00b81150010f00c6082c4c09145d4030301404c9113306a4924580c41000110010707590b4800345401445c0507825440189a00c03002181554113080000f40c003e40b07031b840002d21460b52001ca42d005640034075040c00c4105010080c2021911080c5c4c400b5019000480300da00041c002c04a061440303250042c240da0603a200444001d00344009640d12800030a141c3c098211441044c0300e088191000ca4050103018500c80c50040780154982a0700394145e58003040305646004c1640f4903c0255140024442801350704040b00080985450b1301180203994200c4c80070707000320700008001c20b01d0a40025800001c64580c8104c0789044814410003020098502000f441d404065903202c44281c803604680c05440e8000b400081c01300e68903a02c8104131091504070101e00341d19007004010350310f42600000119000c04000d046003011030300b86d440e164000b0034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 149035863 1250 149034613 149034617
    0x3110a1d010c060f05012c041e020604060512010e041e02010e060c0601030519050a030815040501060315060201180f0c0b0c07081b1f1e0e011101020301080c01 70
    0x4003840605030700c20090030014070f402c28820070080000814001c0501002d00610300c40f00d05418a80c4034107800c501c403d42014040340d100902603203503070740c031043d403144050203802d440300e000301e551000340e034544004100420090300d440d5a02c0c0000310300340115420580c8404600600e4030308000204010946c074031b820b081e43c2d0304048400d140c07a2006844464800b40c0d003a80006001c42d4040c900c150000e03c16050781d00079800c41780004405004000010079038200181103030010007003000002d0294054540024028102041d45807400340441c003211000d070700c140d0009403284c10703841c42002ca071550705015011600c003d01901141c203003100c0608440b150018810b00990140300300740f25980c26500c014180d4080711541c1c1312440d01c9100e23601c5059020345802400303408964101704404036a5140500c00191980c600d100c0141c8910020706944001c0758207102d884044070502002580c0c1d200300f09035480d15074003103083c16040010800206d01d610718050ba03204000500003030724000b8000b02010024 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 149037113 1250 149035863 149035907
    0x6010504110a180902040b0a0e0904020a0b071502120406150509010b0a050403060603081e0c07060e0d020405010602011b03060b04090203040215040b2701080606031305070b090103110a 81
    0x40c18030320343c0210081c2e000181c0b10b031012802288040310f0000401e9088882d80e2040050340c240130401c00001c9080e9802075004807143c00c10454180300c0409070001b68002e42c02c4a2103400c140f894201a03038400301c1c4008010200c0000c0008000051260b8060907210041d52826a401d0501050f00d1a8040c06140010b980204684584a100d0421100507640c2f091050110a507240b402001c15000620650721074240104904c1c403024000080c0c40d103001000004041071880c0030000e03a4183d201115843d0000d1401c945140581c0f00c40c000c01d4000c01d03455000054650320400e42084070400d142084003090b00b8120200401c0b001030055409807540c2200060380d03921184001034034a029071020102000010030001000c00440000d031040044250304210010340c490914203988582508040c045030802e404501582880d03070180d54480300d031280300d00180d00a6180c0520f002c1c2903074000c20381003400003020441560300d4062101003582144e1254180610702002608007124100301c0c404954603 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 149038363 1250 149037113 149037137
    0xb15010806132307021509070308030a060b070c05030105061804120512010b0903010f0603031e11070e160c0b01031407030c090b100905010f030b0f120303070206010504110a 76
    0x700e0b90200141d58100003000307000c500c2c0790303c4803075458030110340c46805406200c4680c8007446480300302c40c0c45001404081c02025080d0f580d000000d030409051040031a540700c0001c00c03030380491130003810507900450b904260a4941820142034490003810781d4002c0100a00d0004e5841d00284500c1c5c100d5801580c10a001c09500740460752406004844062880785c03100001d0445840002041400e0041e030007840080080c048800a80d000b512008002445036220b14650b00703c02d12051040c41810b14068480c0400f1038803c9141c08211f80080c1b50b0000032800b4400031030034101d08a032000080782801c4900d032001c1c0d12008443d8205100c00341c549107058006c0c46080c0c105012541c0034550188006c4038145e01c610381c0314002c0102501c254010f10034103900003c12800342262004483c1c05075205245000722100460280c4402031880f40c00c50643e80203040e0035640c207501c2c2140c3c03040300300003940c8074030348500002e10381141a48407030f0080e031501d58280440d441312000c070703072410700e29080c00d00031101 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 149039613 1250 149038363 149038399
    0x130b0a180e06130b06030a080a0f0306050618180103050a17090414070e01030608030912010b0d0f1e11040b030c0d050d0f0806030613020312160b15010806 68
    0x503150100824900450080040031520b84098605840c02000c44115a03545d44003896590502800080d00f40b003001d0011095540c402c590750301c645041440c010030007070b903a8004598241c0028035544000009c40030010390703e080800707004548111984900c001545951a941d0311490704842c00740c80300c0001c564008003d00814125107a021001d481044241d1841e4005002404240c1d040b0002031015900980150700c82c1c081c9505950101c000340d45071914110801000300d400c0c0d0181c491075520388000c031031255200c5009031480e902401d0343c4501c0324414505907030b030011074090400c4618120080c410224402c0445092802003d840000703506500b4400030b0b190082c112949a4001e1500e41c0e090104000819001115140c039210303407072400c401800584607100115241d0380c0541c49800018004000601c034000300c1030024081c1d070150440100841c0040d80146d2858242c264a038500c00b08020300c002680764803a0070b03586060f401c90300c483d00003400c440000d00164800d400c4070250701d41e450 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 149040863 1250 149039613 149039621
    0x20409081e0a09090b010801260111030601090816050402030a02070b13110d320313061206080604020d02150403030c0b0604050910090305090901090209130b0a18 71
    0xa89403030340041e031200032040000c0964021840580010007034040052008528010841d90000c1615000c9041e130a00710116054052090b8000400e0400c10128103004000e1043c1034220300d000d10ba46541c0c0c68210000f500e403050b0741d80100243e038010b152400100b05c0da00161029940112030141c0c0e0f80d200e500580000e03019500b03014114101003028001c50a800e0950b02100c1b40c4695218071004d4140010072420400b889005003036081072900120200001d203840301c091141c8880000480541c42503d149035400403810001c0d400b40301b04090201e07540140313003010000c000c40c03400d00943d414290802d85400c801740c0002d0042d280541203500315a680c2ca061400007030b45403045900ca5036217040040c891500c14605541050844006ca06103007400d0045600c105440c070020001c40e00d4106e0b008000f006000400c1e4100441800650901c3e41c44401c010b000700781c804800f503102c03081c0b034080020090001654140c1e40307140c480112402d4582e0408c11301100c0680880701301c1c10090700303c880060 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 149042113 1250 149040863 149040877
    0xc07080c0f010f3903080106140706050415050f01081204031e111e120304050306040206030703020d14091b0a0603090c05060d0608061b071217190f110702040908 71
    0x546044c80e0030380d1041007000c1c03441004900a540700c02c1e03142da846000341e41c00d040f86d040c0900c001c0c00400261011604a422030f6030050f11622400f51000400914030045034001d07030f0b200c2c004458590041000140421040c41a40302145000d07141a1843c1c1c0c0b8110381c00c81c040582d00103146e13104600d000388004202e40c03900746103001e051400d0031524820900005810415014032411202e050100c944c44004144c03420340740098010001912079408110550f00001c02603020103801300200042040a40244003c0b40c280190305101c07802d0030741c181400c0403c4030241a032503071981c649000d102d668031540b81c0210303030260400007a908110f0801d14507214058110903000742e00001c0e4101142d81c95403000044030b00c000292441034880341010308441c1d141950000190b40b042c001100807942143e105d8100c04428141991710000324104c00745426000c84480d0070b84101140e00030001e0340c01d40a0544c1c054a851001c0000f6001c80d440c820281c092910064000d9546014030010030520324101d82c00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 149043363 1250 149042113 149042177
    0x509070e07120c120606140909100306090807020108090a1703181218010903050c010e0a090c17090a0c03140c09100306140420010509060c07080c0f010f 67
    0x183ea00850300030b00008021807140e4402031410400082d0544500d001c0d510003504c8111031840c10711460100704043d040501000b000ca0001c0c0c0b4004001041c074800d910001f031154414a803254194000500034400040c08a032032038021518a40000b03080412032140c0f40300442560382c9a072106025401c402100c0064a0014410002ca40781c540101c000036180b0b114031110140040d01001004440c4629140300c0100654050000703041e080d1301035502c16001d1000a440c80c590b03103981c2c50012050750030406034800400d445128182081c4011003034143c1c800c0c130043c0180b48184096a9041a4403003605c00a8019801e4490610820005100221408400804401d1681004100d04100900500c400c41315a40f81071844410382d00c3d0003074001c4c0700e107800014491001401c0022441018a004c00b80380c1001000c02c4108860365468000e8600c0781e8503031008004003810103e01901d0800d2441416104010502e0a000c0036a4032951200c0003107264607102240500b044030ba550380c80541410280 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 149044613 1250 149043363 149043371
    0x60d05030c0708210f0334030f0501091b08090102070b1008070603050c07020d02040b06030c040305070905010e130302011808031f060e0d0519060c0207090509070e0712 74
    0x36084030005404d00c071550340c6442d0300e5800380384e14100002a1003015000d000c1240148001906580300080401103145011541140c20729096000d08400c101d0603880c00c0231960703d4482c50711040b664401e040c0034142c80c28040040303032084e04800740071050503c551000c018000b0002150088290150364015900121303105960428080d00002d4504c00c0c020403110380b050304c01c00100d0f00d20a02600c1c3c021440003000d240344c01255000c2c0041c42680d10003e0360042c3d01c4411018081d04c8440080d842009009078075034030707070381940f901500700f604641c01391070458200740041c042c3c1c0312442e0a0035044480c0101090030500e1a14083e0b001d000c12091001070311242603030500600c1010380c021071040701244040c0700d24240e0a0094903040c012801a0b00c0000c206100444440c1092041c8210203400380049400010300100101d085c1086103400b03c402175241d5004500c1c01e80c04015500161070760791001c0c0001e20b0403c0580e95074a686100d0741500490000c08504440e00812030382e10820355000c2e00344 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 149045863 1250 149044613 149044619
    0xf0504030504030b0705030709120609140106090c03050402030c061b0304090507030b031609020309150c040905010b04180b120d020c09061804120912030e040510030506060d05030c07 80
    0x41c009810a22040c0c8981c550000004e0256202d40c0c11a40b0924036a05c0700e50b09942801030b0010a1084032400702d4080e0f96604001d00404c90344600d00d84200001d200105406003400ca110054940b841a614203250411050100595004c112801070325401c1d01e00e0340e15003481e5208462180f14900c644640ca000c0060041030701074890708024414180c0380c03018840e03502d2507400d050b074403100f04507018072108600b40c042c0a140c065030001c2d83c0091020041b594025900307440400c480c0025520510070142c0007804200c000e0250240f2401812034421b020706092411407103864505900c0c1000c8100c5544250032007035661800e4600805424510407648500320315000030f5542d003100d0600074414505d07030000440340e16102c4c0348400c0c20391030341c619030300306454560381e6514002d5611b4031081400515072010524000e0a020840414081e070307580424001824184811102c015246100408804d0014408540001801900024280d030034036810130103828050706501600800ea01107000c0da139400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 149047113 1250 149045863 149045867
    0x6041104120c0b120f0c0409060807051509061b070902030112050c0a140105090d020306090703060509030306150903120d090c1409060907170c120604270201030f050403 74
    0x101e460521810400d4841c54943c58034035214014419000b0965188000044168961006240d0010010344056003000e44940c4d030502920714a40214049a00015041200d45000003181e800001075800003031406c44002c002c10701c1481140c810038250301907803e03030401288040050200a0442d554110344079615440c10b00c04c4408224410f64151080220b094202e14003100c009044038041200080c003450071500540f0305410030b05a5035408010100c8a0000da20140a101e201c1c402d2a006821041c0c15490311808075040a010300d04107034020b0080100d551513400b204001e1002e07010f44d007510b131102c82001a14160030410320780141c0001064400318040c1c10341080e1582c41c802c440c02c2040700c4e122240080e003686420865540000782d41c010a4113030800c02c040f5500701c00c01c3d1078003a082402c0d84000f804485001d40e009500900006640489040d10034481500300c4400c84060011039215402040c050790b664189660440c81424010210780c066405544007001c6814188420310b094200 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 149048363 1250 149047113 149047139
    0x30e1012060603020d3e0702030a0305070b07020d020307060f15090b0406051903060c1202030f0f010509090601060809010e0a0f051e030307030c2705120111030f06041104 75
    0x804000034201811900c40104940c0d059103d051940e503442c04001b420560041d8a481401449128070400c0000101584052040550080c02512490340c0d40d005441c1c00030844900810b01402c40d0030104241c0c40c00c2e03601004440010350003ea0204020748150000001449a1101c0b011049841c2c0800600e000840d0011607240904517030411040790760b04c0501803803a000840c26400c4901650ac2480068901e9010366020915890052400448906814126030055074400303030f0088120300300000d01d00701b04005409810181c0720483c0750304010f424560342d45418020f24050100200004007104e100754032441320a40d00504840c9081410f09004820f80030320071041d82c0c6405000e1100c0d015039481d1500c10648240440214a95915804210001c100003c000d03404c000c104041301803000248990442e5000070714800c401c41602c0e2204000280c007081c0c8401701564100704054000b0f400900569503c48110740424139035503200c80020b4000c0460440c0b00e1070610000c42c010814405000f0b07 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 149049613 1250 149048363 149048377
    0x91d1b040c1107120804050a031b0b090108131118090111030c0403080a090b0301090e15130314041d010f240509010c05060901020c19030e101206060302 67
    0x1410001514102011a5802c01c5418904516441140200110300b0a02104100c081c0036544160820f074071000080c403c0d0209034030075a5883e00d02170050010a060036000c80040111090785442c000481c00043c004e6a0001c1840c80d000c1801c5a60354284250161300d41d08001005050780d2460b900e2003203014205174141c2e050b4146603c2c000c0e43c400060f092204403402120400441801e26195503109612540010b030103200b00486d03180c0001d66141000041d5010b05040c007004105240e00201241c5400700108a40071803000100034030005071031443c01d56a00c2030700351500d941491448440c071481c5116a902c0b082a04c41400001c640c50035940ba50b080c1600c03180d045020b180341d503c1c15400c0003506588584000303c22166901c401c02c0c0d0041e801004d170881c060403c083c0044032501c40c0d50a090048034034001e680d4000850040318801400080f02a4903c140c0786010040c141e00d0007846040414821401031419105174040a8010702181d8959100240144800c07600c40200501070342080c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 149050863 1250 149049613 149049619
    0x12040602011e06060e060a02010f1d1009030801120c0302060304050102030417040e0109020d090c030b0106030c2303041a041a0a0e0d1407060204150801050d0c091d1b 73
    0x4842c80c0001c140d40e00444007110110707070760104c00c0e21840003007100551061105909641d81c90512000d00f9180d80900380106c1107a4900301c102031480c290b4075040c4561202065090361904403880c00180d0003401860560300c1a504988041d5001d01d084240307400b05801c0a51f00c081d01008200070868150001c600c00c911034a401181240056003420f0a401240107820241a03080010b00115405502914041c2c07039840c0d000c51411060344400f400701e1380641040d60f0346076581c401401040e4050140320701c004210701e8859010070b83c0c0394420720b05440c600c1c0014803a03800040490184500c11480c001224501c155032036a5090903e4086038441800801c2c07a2a400241c00040300c840c5244121203072401e803400908004500c0c81c104403000f840d0301c41e10908100741803141c0000316400d48041d1000c2c1c4a408880048513000460141a4207030591100e44500310f102030801c0002c04226954048441a441c0400c0702c404140404510320a080b11070722482c443e21502d01040080040f046030022415 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 149052113 1250 149050863 149050901
    0x151806020301050f1c020405150613170f0307020f360a050403020c0904170403030201050a0501141003150b0c0a031706031504020604031a1608070c141204060201 71
    0x12101780418820b489150010741c280c60010003003d0f09280d0845940960217103440440291132600184803500010f039007000c1564669002d00480c0009070080d4907400880c0000c107107a01c0c680110790754a00c11844024000d9a0f0800d5000180d200c10103024a1910680422840d500410542400c0c172070301c008403000702d01c3c40355001c58407512103813117038174042c58256025100e001044d03002e0207085440a0011510800072001c5240009000c1c00508003451107507001268038141449010103468068016901400040340d011207903669240500f040444103003000b0502d00005c078110640c0b00c40e2944075484902e030016080c9400b20740824034103540c5100703031684001102c10b0b48220b03008074812525150150310034030b00751862521101c822507009100038001854141c481d40c07804a055074030400442c00b000b40720248030100301d2883c20540c00c110f1505d001106407800620040070180d05180c0500518880c80000c0300a4805000c0381c001d01329800e90b42c9640d9a03403240d00a00808628030724101e81050 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 149053363 1250 149052113 149052139
    0xc01060b1b01060506090d3002100b06030c0304140c0a091407080603060703111b060402010807020109110609010c0606030c05040b04020405180c0c301615180602030105 74
    0x1020f843e0482c1000d001d04014403101d0343d40070b090000300300b84201704123650f1825031402940311500000746150396010307004003181200700300b003079800724404980300b51400d00070011503503c0f503000d8035840f0b600032038421080c5810000b0796044c01002200343c0e802552500010812241d035400001c0030a0303141414028660b40e808080380d840d0015600035606400641c04200d401e4481d800c02e144001c0d43e15101450001120318010300d81c03503c8404030350303180c005108110541d80c118000740e5107e50280028804402d90342e440031030010b0980c4c0c1651003080c02181c00c16040c6d00c100344c0c4403c803031303400801044015180e041a8104100c0c1e0b1203400d101c0c80c2020360b4860141440d00036101151005400d0382040d201d4544107800101e401007110181d01c0701400300b0038500a00308020b1000b1210030221115400d1701c1340790b01440381489440f045070b40d60108200d91806400d8003c00e071049801000c10648480ea502c0c0ca040502812400741d0300c40c080342d444404c00d1056607402181241d90480d801d10310810 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 149054613 1250 149053363 149053369
    0x305030a23090a030201112508070b0f040302010f09090504060b030d020f0a020603041727040501050306132108010f0f030510050603010f09050105070f03200c01060b1b010605 77
    0x80b40306400380e0040460300042005500418005842c400031100780c89003214088a48000071441540d0502e6215455104005019041c0a030501a00c0140034203071412403400c84035103541c451480000c5c10000d403a13032444441c0c0c1c400d41e1180c0241c5040c1c2c000f80590b042c00d042440140805d02a070a20900804040380080c9000082142d02c0e85009001b9180ca45450b0302007280a03003005005588010803103a8a0903c2c465010060180b9044010145403204486100410a5080c05c0c10b00380618544030061009640c0014125032040c2080ca14243c6a842c80c6040c2d40026a800011805032071142000405160000b500905a9505000d082074440d99042421400c0300103101c050300035001424a0741e504841c50300090f9020b000600003203100481d074010380342201d000444c1a14079941d10003d00065507400001603410800502d4244000703130f100c40b0a04000d1842c1d01c1d24481e16070b400148000c40310400c0d004040103140302e42505d9250041280704a90220209078144599460400e011031185 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 149055863 1250 149054613 149054617
    0x504030e0a082d0f010603081c0203100909050c060d1d01060308030c0c0a1502070201030b0d021e030a020a030309030201020d1805370503070f150e0a0305030a23 71
    0x1d10041e001d04180b40282c3ca4140c0d499004079416202c40c0221a103200785840c00340070340c800951084c002181d071a403406074001903482000c4070022140340104140305000318004000400d803031242100158030606460441d1a000c1c1c00741400307030882800f054401520049070320024907c1d00e00e100f003202c0c420a1601241c202c0daa540002020401c1c144086100b040703000c000f414200c9070034030454a00d100b142e1103000381189400490b002c0d450300000c5800c02c5580c94000c0a5010000350b03113074003921200d80e00140400071004040d000d17012011641d100340d035804000d400d0300e05070050b014003a11510f074280200640d815001c186e015220f602c0110140c00d2041c400031100c05402c10100c9141c40c20041005007070140200251000500b003c103400f592004000360140105000c080421182d08d040181410704281ea031000c1c003040c11603134040001c908039041d8045902098600240c40408140c00102940702c25080a0003a1002081f1b52500680026005ca0a51130420720600380380d2201d80c048801d4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 149057113 1250 149055863 149055883
    0x70e06070206030406111308061603020a09050f01050702090405030c010c05070b0103030804030c050f01060906060906120f1d0d02071a090108090f0d05040f0f03030516020a090504030e0a08 83
    0x803202c1003000a000c1400e5900c0074074100d8451280b580303005000e506a1401080c150484d103115008a001d100d81c0c1e54600d07141e4540080e440c18298208840504040c0c401c0b0807602c95075008040104010440b45c0c802c00032075100030341c000c04000301424141070003035980d00000320100540d8641041040d8660140701500c03c040c1d070121184ca8645c2c02c5540480d07403480040c0044042c09030b0741030300400080703045c012004803803164000016981d00d40400c0f04155112a03012205008414009000d001d0b400361014092815000e030104140340189082c0006002c0c90304080c000b5008400303240c0003020003203800d458140145e421241040e0719a2100c0003403034403000c0040000030702041003031515401840450703071051076003050300c0d8170071841080305090a0310348040700009040003074140941d002250580c806084607601c641344580c00c640d00913000c1d101b10003840c80d400d014044001c00b1035480000400c0034108030b01080c089420145005040307100317405a41e600c01c00e5440344c04204040c00042014030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 149058363 1250 149057113 149057119
    0x51501050310020f07061404020a2907020f03010203040b0118050c07030e0307090501080c030f01060e04080d2306120a151a09010b0301060206070503010312030c0c061103070e060702 80
    0x2800412103603010083d0b000080c43c058076002441740c100841d07150721030f21115803030070502c032070700c074a028810440384d0b001d55044400d62001d50341e0303820011442c884a220102200001c001d40e40c8005000180f03403181c00f20100ca60560001041004000501c070046040325114040680c3c240d8081d07040034250381d000c407241b0400b040d050001c075010038411800250204409030503103490340e80307803c01c10054540982065140e94422a148103c0741410000b10f141311010708000c00113203091403600440c400000d007002c1c1442c0c0001c685054a0411a40403011151514412001e44500d4007601c05003200100c410368440c208404040900c0e00e00030810314140c40d80042c09001c0c92100803185001042c1500b58213141445000740c0600ea80c0ba01c09420f4060654440040d4481d8507000000b8600240140000304000c1e0500041000909140124844410900b400700c2d560308281c104884038090f500d0060b203a50b0825803541240e00b81000214092043d540c5c3d240b4103c3d04075000d01c2528403420b031000f90 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 149059613 1250 149058363 149058373
    0x30f1d01021504030e130b0312031003020909100509010c0908010b091b0f0403050a051c0207030b1e040f0605070906200c0907020f1b030312061507030c0515010503 72
    0x601000b61844154414072900344a440201d0f03ea01103403018181e20300e45207103542d0b00c150740301042c42c0c1000450b045000c80d00019103940340c20341120403501450311000b0300482520740810b0441c02c0c2400859407840341101e04010314540402e000f8068094006140049000140046051803060041c100c1c0508050100c808a8540440b03844000052250303104c5186824040803019009a1004000940c001d4000b030103104014103200d0708000b000d80c81e180d843c8542e26000c050980d00410f12038201c94208012900b9640d60040f10303540c10100900d54920340000c0f00c03c200800c0880000c0d5200f003802598104480d03075803a5816a05030300f00b8000c500c041000004090764244c4100264000e080109045d10080c0c0300d0540032502c3d80e081039940d01c02503080b0035a2501104020883c0c0c100300c106450108240030343c03040109441740701e1807000044820000380011038a0310303490a8901c0040f4410103841d900c819034140103200d030803012402c84542c0a44006025040c9140c0706060680b040200900 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 149060863 1250 149059613 149059633
    0x6010f0b211005041103180d0c080703020a02040e031b010b01230d05040807050f0304140607020109050303041508010503210d060b030a0c080a0509030313030c0807030f1d0102 77
    0x1603101d0034010300c4040b000300c0024021641e0b855a005800c03100500e404420b40300d042511010308180c05046c04521039902c5007850203903481d4050003250542da00200080da59202c1424200d041040001c0b000e500300d03082c00b10f00c1800f5100000140b042c1d444000d19449808080e5500c41c3c241c81420307100c2d9000030403180c4804d18000710005640d600d00040941c9500c0e001000419000751340b82110305480413000402d00d02d091050a00801c19913104110242d458107080181c11742e201800300080c01e00420b0041504401c59000c1c03185100601f4009080ba0b0302c42c2e03913507032408048034100da40030f00024400c0c80001505041c00203000720540131150356500d182d03d03000944004c070342000703a0580c2c0c2142c4450300090001040c1c0004c501038002d22401240c9210700d400060302000c5c1c0609490002032a01040180c01c0c100801a41d82014000000c81050101d130305007141c2c0c041d80218007400101000950034101500f1510101d1028841e0729040080340005802c00c0f007c0c3c908bc5443c03809030b0004d00e150 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 149062113 1250 149060863 149060917
    0x6130f3507060e040603060f09050d0c020a09050604020c0604150c140301051002070b04090c081509180c031507020d0503040503071e060906050403140c1903050c030c06010f0b 77
    0x1043c0070180180001600941d203464090a8a481d6441c5444160fa10418141444410f110040b0b140200d8180080c5440255001c00e482001902c1141c45a6583d034011070201c2e038445c3c0442c0ca0f07151180e4101c44040c1020f04100c40d1032a20340f11410003491400781001c0001d4051420010001c0c20b1440007802c5a1a00007409095165014200b04500886001140d00741e540c1d400750010f001c00d10400903026010340806420f20602410729501c012481d107255040c0d94031540890b60010b0b0400c8044984070409049920b0304506400040c0e250207440700c041076400a52800c144122115400c44400c00c000d113409031018817003039030302500c91f030001c00c1014042034621032492280e0000064074070380701c0402d8482c00c08a4081500407900580c5640901060503481200c0401720205100090f14000211b000c80d950761816044000c0003603200644101414042c50642e21800c40b403209413a55030010f880d0700c5403501824000c000300c80807068000b04aa240d4a41030350b641f00c00c802a2900d00501c21821 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 149063363 1250 149062113 149062127
    0xe0f0f060f04030b07050a02060a0b030d030b0310020409090506010b0a080c21041b050a121401020904021309050708070e01080907050307082b050906130f350706 71
    0x416460750040000000061000016600c9410141d403a207440f44080c0400a00380300e00980028201c41c10501c80c071445a402090201a1005c0d50500040980d44000801c1c2030400404080100c14401b01d80043e1001c025003000304840d12a10941e07105a0f00c80e540c110032405803140c00000900c0c2c0500188034030b00810001c250110040420410040100d1402440604215001c0b0b40440c0c900043c0c7d03200c20004078260b40a4003045030046591410300c085134500c41886100504004001d9201d034030841821b41c110740440001401c159a60610394110410000440c45005501e0345024006220a4070503002103001c0c880b40d80c1c4044a84003001e00441d07401c0c002900d800c0131409601c80004e841da60030402d40005141010243c25042a12102d080790004c1001400c03e01201d02c11030111842d038444100c1c0c5410100312007060b1941400010017000008030780050039203101074000825040c00400b5010008403c100072340c06c0c500314000b60001d4252101101d124660300c0045c0a01c922401110 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 149064613 1250 149063363 149063377
    0x90e0c03060d1b030f02040e0a08090607150905160801020901050d0905011b111b13110c010c02031305010e0a03060c020a020d110a0b0f0406050304170304060b010e0f0f06 75
    0x45040843c1c00412940c00e10200c10b03a00031661552009803d0085003068081e42040b05108405401e0441c0d2a441e081510f102e045011403068900048000402c80d000483d20b82a10078603c0c05c2000c2c000c180741003a0703101220800322106001d1202c00040100d0140200c1d0b81c2c402040c1c0d611414803241c0703400140641060300c4100c900b5500c030808240b004a45c000700b508005019510030a50f0b0a020514508004000400b07580c2682122800429900d0302181410100c040c1c5200141e1140440040300e900d02400c05012015402e1120048d542c590000c090a01a03200b0f4451114541c1d8030401900c400003440490782c0c0182242c281000420b0180d03101000c0c3c03800383c6c0165014904941d000800340324004804980c13005121424110f541403181151014000c640c0f0564075010b0b45461226145c05184075203010008008006010031000038003c100c00c80c13241d551151642800d00d045400707001101d9a0f140000c4080528103002e00e0049100c400c8028060000340d01040c52406110721179204078 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 149065863 1250 149064613 149064623
    0x516050f030a480816020a06030204140906011e0306080c041811040f02040308040305060f040503030406090f080307020c01180b0a0e120a051b0d2001030f051303090e0c03060d 77
    0x640700001329140c03130b00400c200190040c0b41055680548100029080250041420144180410302c5110f55589071401242c500b1664a0140d0360b800c00103c5484086003d610420503400c038001c0012605a0450000e40b613582007a00c10003050781c000c0c4011104d0210000914a405180e9440070030034009030308051003400b400208440c921005218181d9009500031a5400800030741042440340600c14282c1142c0c07c0754080c001c81c185a1030300c030740e280005000505050360307803880002000100080003032541c3c4c0c00364a10307032245010800651101070071006a4003240450a602040d140700c01c824000341c030410340b00c0508003000c05004a484801214417250091f201d01016414401e0400100034113911443c010144010680c6c2c0c0c048590a41c500e14600502c500721100c000104807101c00c0c2042078110525a013090300c550b0040380074114410680300c180d450a403d20030791a200071107640d0251b020f40ca86084041d0b80d00c0058510800450301001d1103403091010441c50f03d02500600b42c0c150182d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 149067113 1250 149065863 149065997
    0x30809011401260a030503280f05010815073204090b0316140d0503090910080c0d080406080720030702012d0516050f030a 54
    0x10004455050a080e00410341d140114184000344040c0e4210000030300f0060800f401c202a00342d07a02602d2030002400030344000e88054400300031204c0000646009500542c010301005907854840340c01444213002e2000c2d180910060513000124005525000745e210b5540c0094048048003c50054000c581c80d030360501108442d52100c032040f10300034001402080300005820004102090b18050740c50415030041140310200b00704082228261805124050f150251514854036010b07080d803043d0442aa442602c0707005004a001c224210300041c4d581c1d41044440756906902003198001c41e4501c0208000c40800c0148011481200d8140d041800341c03d003420034505401c611039540d0010b003000380300da90000c200071080d5030b0b000c0080c10550b0301100c0d11000300d543d002c51180305c00744c0042400c81803040024030140200000c4009100c415046021b60b2516400755040a4803980100319101c009a601c08841c4100c0c0920828104441c809030740c10784c0ea81c40e40c00180300c24102c1040202d00382c2c1c00a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 149068363 1250 149067113 149067131
    0x1c031205060a1d09070f1404110702040905060106080a110d200f0d0f020405030a030c02130f14090c09010317042103020f030f12090106050a0b070c1a030403080901 72
    0x51142c21151101c5a090859102e1500280301440c05c2c00b55800010704c62080fa41c10400c0c200c1a542c82c8040140540d8003064008400d490940c40b84100c0b40020742082c5071088402c24040c0201e80641a21025640c1060944800c072114042d10040c090f8248082010800d00011340c4090380592060b003e0305494925084410120644607005040714442c0c030b40c000211801510181c0c814000c42100b20314085090a0034200481d5407800110001018001018203040a542d40c0800656010340fa1070014480d42440b80d25000280640e8003852130354010f5600410b007500c00102e290740728104040c025180c05da1030340d151900c5821580390458228442000042000b00754541121941004401e03c0e80201c0311525009107003110744410301e0300c29001030064240701005402110760a03405588000380c0c1da03d030031b69554018143d0340e003c15403050141000090811444015010460103400008a01075541603402140c0883c0754144c10300f04010400500003d00900c031a0f508140c100000259240c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 149069613 1250 149068363 149068379
    0x1d1503010c0203030a0c0804170306040b060a090603060512060403142205031c0e06090604050901080c0a09020711060703110f100c05040b0a0e130f05061c031205060a 73
    0x1c040c0003180040e0000810480d034403880c1d0250225004151512416524107500c82c0d00300c1c2e500c1060b00c083c0502000020138110782d80d503007008101307844c0104030310342c4c6045104011f0f1280c4241c1c0304441c0800e003401000101840c2503d84060340008072406021f0700d0382c0f00e40d000c070b807440d401c00c100d40c3c16910240403188400a99a112404c1d03d440600c010b10f41600741401c151510310198038001c858270603018002c1d000340d406050928030b2034003520107035110880311000646a00890b0400d40c4c0014450000046008000801910540094070014803d0303071240504d000740d00c11118007800c2a55000600c20030790030010003c00d52079000b490b14a0a61078500c042070704003041c1c090122015030003030074050350801052003591900078076418500c4c900b038074201c6801003502400d070340007051242046c2240d9550710303580c00e4030811085410342040b141c01005588401031100f40c403414001c0d0322600b4010582e10712030303001c581026056150101c04000c612400c0d000340500800840d00725030140e100140ca01 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 149070863 1250 149069613 149069621
    0x308060a03060501030c0e0606090a060f0c020d0b0a0507020d0206010b0a11030a032405010915030618091106090d0b25020109060b090f0705070c15020c040f061d150301 74
    0x14030407210054000d00c0d2810801f40320a020304094401c000c104001810b50b691001c1c0707002101c420b0b0034194480c0c01030910a81d40c01d4801c1c0c102039044004a4840c034104040c070441c0a1040055840070030007926244001ca0b6210292202c00c0090703402000144900b0030898007501484000340b400d40200c04400c40c406045030040448400426107544865056031480001d4001c1200c075404c088090601e07050000b080741d18248a600c013800f81100c0744460b8180b003900260701400c0c240d080e1484410310b800c801801007a0340c81c41590705c0040401c41810a103486400c81d82d003600010880e18443c4090341b103d03100004003802c410042030200d81e08441d41d50642c6240015a2466000041c030142c05041c00c1c42610300903040e49103d2483d08003080022080381046a030001c600d071500c0c40d203424003494841420307942c0742c1002c0c03007013102d01c141d021030340e5400650320b6190340085d83c042c8807110740c200640c0c0c10f0301d07200d0060a44004a6620401d900c01c1946d10441e1300103100d0348907409401d00e6402280c219 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 149072113 1250 149070863 149070869
    0x30c030303050603060c0f0d0b040e0d09060212040303050a08070e040c0207060908030406050a11150f18010b0f150706020f0c0d08040206070b09150901150902070c030308060a03060501 81
    0x219403154100443d61800f80300c8240d019001800b020300d07000722151070b0819413040c0001105603654801208896032680d910680c0102c4043c0c0403102802e00004024200704003c3c032420f070051240d44041c00c4811405019602280c0e8140c940900700000f5880c2510b035128003c21884c100600390590010a80e5603000d0f56100c0d40450b009442000e041c03040003484c59440fa0000400c60f44100810003c5943c40300c100d030544820392400b41c0a0043c05482e0a0034110300c00581c62050003040d0900c401e034000391525500496007009003824a071405200503003030b03800301088141e01c03640d4900d101e480b5080065600c0d0850f030403480e040d4507000c0c01d5901c19040b0307044180a5018500c02040d81044107504010907100140c49040c5040301d0300d000d90010b1035521454500500d60541d06000c21082d4004000440d24055440d00c1174a141c5090050540241501c0c0c0d4041c038150819078000882000e140b08403081c554005c00d415800d2400d640b800d48002d440a81030320f400c060418000800303d410340c819103002e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 149073363 1250 149072113 149072117
    0x30a05011409010b01020f030d0518060406140a0905071701140a020a09170318130c0c0516060203040b0f090901080a0203010b180f04020604080a030512101518030c0303 74
    0xa207081a811040c01c44d1409031249040d0741c0100680e0652420010541d01014040e840c0820305580f2001c1340030040803c81d480b1141486a03100f48400c01503550030200261050301c0d07450301d642e910368501d4000d451a120002e0041c0d0003000c0240701c6100c814142c3e800c50b41d003850012414600b0150b5000031505c0440e885102c10b03034045000082030342e11450000061007010318603481aa80400c99075124480c90f4080000d0b1000380b015483c9545503c060040e0705503041100304a150545a009821034015000881c1c040c09103070005d42c06801511154010b590060780114106801e180840f1025403241600c002045424440c0b00109d54400e14414040d0040e14041d02c0010050701c14182581d0702c82441a205098408607480d14144003c034055000401d29012580c4c1e8403280045000f0344070b01d800500c19809000701c100241034019004054403108400c05180d9550384045201136481c640c040d02c0c1e803443c40412a08413681c0701e24488502e0a007070190425401c0e54035a42c40d0240d40c2140d0040740 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 149074613 1250 149073363 149073401
    0xf0307050c0f09220303060b0a0507170a020a0b10030b01060f020d08070503070e0a0302031b031b01050f03040c0b160308130c050d0609020a0806060a12030903060b030a0501 76
    0x80340c140282c0c409800c92007541c203150302c1d084c8250003150410a655401c46001c883c5070034207080c0b600c6038000700000d000389500c8a030b4600c40810000d0055221060580348002c2c0d1840740032078a011842180e8103006141d01400b00850702d0342e1800314041000c0d01071811000740050220203d0001940c0d14001e09540e02c1c0e8004203151010b0107410081c14034440340a1140190400100c0c0340c00004483e44011b1614007400c00808100c0000c0e9400420b0700040d4041c4204402d005004288613088981c110045040722582c0780803614050768244561620342c00148148104490404000c02071034010344100500642507480d4140f01d00f840d088500d0031249e00107100102d00034150091a203d0b00203400c0c1c0100f0001d00440c2d22501f0030500c20707100d00d602800000c060001400026401384400ca17500800d0030107a16a1803110f00e95801c070503504188110703600c02d000580c044100c0d4410130035a5050311444515071440d198400180940c80e285a014050070141a0000d0028800c1101c040c05000e4440 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 149075863 1250 149074613 149074633
    0x216021921120806031c08060f060903071a120f0a0b0d0b0c0d1116030f080f06040b0a0e09060703050105010c08040311010e1c0b34020f030705 63
    0x181d80d004420640c041c540c4922107200045030403102c801c80b0b903610078242058161103200200346007102d6605403c085440380a000c0e2072050340700d8049030164400f144e03204410360f90701081040501c41c40c000194154040c030410441c01d140d2100700310100c101446500e051024070b041e01000703420125003100020000004000960105104042c5880001e44500740289415500c48030078001c05030103152100350109420480e80c1240c2c01c40051000700018180c1c8410380700c400c031410070480100403008103206c03442c1c1071003a80c03007440210312850050348105416280c0b081840010907400c1c04a0703400905034040400c6080084460741c1c00380d03c021005080c60310f481c400040c100e58040e00501d0400115408107004120a107040e00c084e00d800003c0c400c13441c1c00c0307040180d601c041d9482c403103900a844014500d003244045214452898011000030300503517603440118158510182140c10a100b04081d020154800303c003035600d110707440380103e5121214441103d0300d180c21030403003107420b40d000340081 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 149077113 1250 149075863 149075879
    0x6130305190c2f0d11031b030706020f0304030305071104110d0c020309010c1e1a04060b03032703100f023103030807020703120509100f02070902160219 67
    0x45100d03c004a01000e116440f000281c25068400caa00144210800306015003803110b80088501036070401030440700c031000c002d20f1200d00b00030060b81c014880c2c00740d060000351480c00820300659072520400510320701821a0fa090310103402c102c0099503042e284581c40205a00e580c85550601052041143c3d1180c04540c9100e042c0c81c444c038108011900140941c0c0306076608101c8030750841e980588004655001307814a004c3c000c1c455000642040002484903150401008050b4011809250184202000310051503540e00c110690304041d074042804d07007841c10841d413108088055000b800d441461b91301082d66002c1e15543c1c01b00451190303000800c8441540c0d0f020b844400c07007201110002c040542640c06040d070700c03034511004c0d0a0106e804c0004000f06c1c070900112018552160140c440303003540000040043d0000c50a4901030441e42000c600c0941c0030305483c0e10181c106500910310241001040000307904190780e028800c07040c0042d1500140d444903445980381c0f03c01e0a104000501d0a054 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 149078363 1250 149077113 149077133
    0xd06170c0a05061c0b040903030219180302061b0d0203040807090b060d150806070906030509191403091f0801051c0204110d05070e190806130305190c 66
    0x3800e8401d038800d44080082c0d86402051340d00c000c207024808152101421806805005501103096009140204c41001c150305640030b0410018403001002560031b8020084c0c0311805207010303412034400c05640420051808000421400b142e50f0079916960005620080c5002d00ca5114000580c101003010301c00781030100070340001480420301c11700c201c1d0302c0000400c1e61031007800c540b42c0c1110307102c04540d0000d84204200e20000c00619045034a50318003440001c11016140c0900b00006c1d06250110760046000070750a015403409015440c08010390b540d440607015200041101640030034802400307140d5890304031500c0ca801c4500402c08400c1075410050030044142c0080c0d00c220400d090446504482440c0e2104042d0b050b90700141001a146400c0c8050082110f01c070f01071030802d000c02c18290f5014a48440908041ea9174a150150003046000c0b9840d0a000d14502c9510a50025042e4500300c4032111049004c0e0900d20320f004080d5500100080500d080100411003182d1548100001480c0c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 149079613 1250 149078363 149078383
    0x41a160506040b1006050904150302030304030b06190b1812030412050c0d03020a0b040303020904050a020903010605011416080c0102031e06010e0607020405100807080a140102070c05060f0d0617 85
    0x40c249500700d0515170040c0103409280c3c0c3c120f001d04d90701c07035580880303d005050180c00b4540090862342c80b1036032841d0503c003601e0304076603060086403640c000d2009800311654020a55444840e4181042c10141d160079010800c0591380c1d40c408240b010043c00950240000c1003d04907003074404800c81150306000d071510407800c030318901035400e4890003030101e170380402c80c2140d080c1e2000b109609501c960600301d0181c069825200d40c000d1901061110740140c5030b00a00d140780043c0c00030300a2035541d10040d2841d1281e1045808104030802c104242040d1454600c100c131445600b0b45800c0c103c010141d50700f243c00889003010306031041000c0020180c100c90049600c02e0091030306000c142c3e45440400d409000381c07000240100c0d2550040b0740e000c11948070410103800711904903250340c0d40c2d4900300ca907a264620b400782c42511381941013100c00901030084074941c1d9041390f810140c1c1480e0209020003a4441001071121900c240710003e554207160003424020f2020004821000c09440c6c0080d0401032050 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 149080863 1250 149079613 149079631
    0x203011407110f1915020c070f08061e0c0708040b0f0a1404081b0f100305160801050a120519230f060c210a021b060c041a160506040b 59
    0x10482d985424416540113101030340c0904040d04003051460444007034010554645032a02030204003046194441407420304076190303601295166200c0c0c4c5201d00904140141e0143c41c00c9004000800107020389000f0500c1c103100350388942ca0039a940b0007400a0ba042803c000d42c0d14403000030b0101300c0e1988181c6002c0d915030541d81441c5860b1400c504544da030150071400784941c08185a422080d651008585400618060024011880b000350010001c20381140da011400c080300c070a094060f4441c3c980e51341070300c9001d401009600d0509848294424070740c0d20860b11880340001c0c0c0703140e4040c869150810b09100e03c44217014400350041382000c15118803191000c641c0003510000d03c000d00021f5903070f00030702403005050b907814a2601c1c1d000e000c2c1c4880034402d00c5800500500803022815402020700150003030009440e024491012900d840701540c031100d103c034080c001401a8907503034900c4500c4100111841d413070010300000d00b1840c40c0c1c0300318040e01d031030300000d040100780070700d890000c2c0c0c0c08a402 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 149082113 1250 149080863 149080873
    0x3030c03041a090607030b1215010e10050105041a0f1c0b010c11040c09090e1f1e18021008060306070216060c0c090203010e1906051005070203011407110f 68
    0x40101382e4806004001030105919120341c2d01144d02c81554026221820100340d800000800c401c03265220b101b03215902c0e001d00824009001d0b020740012001c10350350f0596501e8035052800c56170082a12007000003800d0f0a404001c2900581004070091401d41d54a0b42821081e40e0110f19001c12900b40700551414011489200000541030750442c000c91202202c0008051403603800c100c40c1c0d0022604130095451074010f0590800e0400101c501c03207405490380780b880140250070280c0917210006041d00d42c0364011507011801109039008262903901ca80c00d2007011841940000e13410303000f030803139060100340100d09000040c14103000050340002030380028510b461704040e183d1050300740c13481038804020580758003400b08404c1000060041401d40070a540f656120025040c00c6102a40c42001c0700030316802c00c2210500030701408040345d0008169a1034811480b40c2a10b450f8011801268903542e07500c0300742084203c1c80001030140110b507603408007d40c001c481203803905601c00080340c03242d484 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 149083363 1250 149082113 149082121
    0x50d0206061c080a0210020c030c16030201021c03020f0406090915080d050c0f01090b0f0a0e0309150712120e0102040509060d080c060f041703091b030c0303030c03041a 74
    0xd5116510030594040c56080d904e694114089040c854201d1943c4001c130f00006241e0300c010303000809002c046440780191020103420b50402c40300061944030003405608441c61100ca00340c0007240500e4581d9a03820090310300031500c100201c003640b103600040c021403000792081c003500c80180f06011807800408880b00b88581460760f80c56540c0e8102940b0030400c2800111551002001c1c4000398107030500c40f00901c0a0714503481d04119131541143d88104681c070f407000240d60803465008041040b0b07844005146807140031030510401d2040d5030034401c0348242c20803035000000c2a80058800d003a0b510342d10400345181000d1200b05031039031900d9900f6181c1c0144014031003583c0c0c07500c8131600a04100c811044144207450700440c0c502500a8842050280104002c01c500013075103110f1089128400500070258280c0300c1c41d0980c00300b0340e1802c900f80d2100c9114614110002447c1840744001412501c808150000203807071030f40111000c10304410007106000401c081011403481c4c65840c0b420389044c41c50 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 149084613 1250 149083363 149083399
    0x50a020c040c030b0901030507080c0613150507150f0501090207030801090504031e020106060e01030203010305190516090e0f060103050d1d0409050102030f070e0a06110118050d020606 81
    0x1445412462090b80ea407000400c0e0b0500a130300c940b00343c01000e80780001d1581c0d20300344151180344600c030b40110390103003001c1c441d40ba02d418011140f5100c403003104200d405042039040c40d020301e41e186921061020400c480b03001f240e0070100c030b1010fa030301c11080801c0712001c907103a403c251081a405001480d0041c449600040c0e00406040e054425016000a05644a080440d03034502900c021200d40080d0294440d0242e40c190402c01c03c1d1925600c840b4055a0304000450480c0b20911000d882a0040c50180f401508030083d108003140c00b420071100085041060711141c114154042107089698460000703101c0e406205803d541802030380030f40103540c51a12080c1d101e02d480d241e84410030010510130740c100c0e0980e8041084400c0060b00410180c82e0b9880c105000350320907070364105c00e10b41080c002220035100b0980c0074a010005040d00f0869464604152541b0042ca501d04100355280c458410312008000314040c515030044000708a00780103001c0190610b00094090360003030288003c1241180 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 149085863 1250 149084613 149084623
    0x5011103060114030a0f06080303070807050403110f0d0203010c0f02070b1206011b0803040b1519090c170705040e090715141603090512010504150b01170a06030c06050a02 75
    0x700f405580380c0c0d0b0301d41da100700b600c0042c00d18a0918690030314083c4040780e800b0000000d5841518592a54072454407284015a00c034003a030711000f00400c0a00d9103044440c245508112200c40000c3c01c4070100c01d07800c3d1700003400c0d2242080000005401c4400c040d6015034100240310051503079007143c9241c19a80034158501e4440241007a05200580e12803400c2000e500c981010800d130821040b80e22401c1602e811052500191526640c41085890b44120791070880100c190550441000ca030f00107191072001c43c050109043e0040602041002140c0c101c8d41d1030b100c60780700722010307940d440e510350510100b042c44801c00780014526a100072010b1041c1d4a440415404014090411201030030f40301d00c030442c40e840781c00003401c0710a0a041c01c0d901019041848801542c10072181c04000f43c1c0280c01150881e85c0c02c96014195104003e540032040b84587c6c800400000180341c001c0c01010100000c0140c0350b0281c400c04404d41e502c0c04200207221010020038050500c92030514030700102c51000a50311 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 149087113 1250 149085863 149085887
    0x3071703120613020706050709051008150103180f12050304200a03080a09080f0a02060403020f030c21070e010302010e150c07120507081501170705040207080304050111030601 77
    0x107400c500022821603611900f0740001d000c1c1800041d50307039082601c0c00c080507140996400e8003255000c0300c04a41c0380742c056003c0e035000b00709a13151916643c401c45029440e07201540090305042e80c5425081c403a5078924040800e0034003410702180b03006154035259100c14000c404440c04c10405009210002e01c010000460b50b140552121030301407140350005c1c084480782e40c4014600040000d205030880d80140c208412035080105584035603e8428003182c82d4400329070001e6110400700428001458044e41c1c18100b07402c094120b8501d40c0c4520003013070080c030481031407801f54110390760a00b00b1b04d6800c0010030041d0840101c44551545507600181203110f2700d00d0480e00c02e011003510060741c1300100c400e49040c3d0360340000700c0380da2036514000d1494005a0b00790958a0b0300a4460214502c02c1c006521140c2c403042d1a94840e185c3e1038003c14101004e00e000344966180100341000540ea45d8070b00290064500481240741d407814540780c41401c4600990225884500500400110340c5e0490203000c50 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 149088363 1250 149087113 149087137
    0x90203030a1d090717090d050406051806030c070b15010903060203060d0203060c090406080606010912080c030a030609050a05040b0601030c0e1002070312030207020d0201050c2a03071703 82
    0x400d034518290654641c0b01e0202d420380014a001c108180c05038854205444c0c9a40740e100520151103c244d1039490700c9111380c0389000301c1c2040008000451086008000510303892000c00b0046540364006042948103482c01d41c03c500001c0340000030310095165117504596030070090108850410006802801c9911025201e079502000180f400c1d161f000e00341d0150350f4000c090f100e4500e0034159440c02a00198241400b4030b10b007000100f50685c0000d805405904142c41e80919145440d20750040903400140c2100c601c0e80030700c000e0650180800103007070140c51903140402c0c2c0500f00000c60040b15001440240c0c5a420501404046005000f41c00c0e008031007860301042d1070387da0140a039074100c2d50105140d0000c40d04545c40c00c5140d80800c0c6131003940d01c01e40741700d4a040b2240030200e050340136404020358481c4030350600200540c090801030880c952a40241c6180e0550a43c00e4648162492a03007542c42003402d041030404d01e024042030001e40b1040150510941c8801c0144c0e5a80c00350090000d6 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 149089613 1250 149088363 149088377
    0x15031505041113060801061d030615030304090612060c02030703141b1e19051c090803030a0c02101503081b1009050706050906120a063303090203030a 66
    0x114a0610404840c03e0301e40600c1501081640d4600003807601c442445142c1c0098036559002440140300b13403802e444018014010070460711008201c418800c03c461040e130b81484200000203860180d409603000410300450144d85892003400e044045d203002680c600110b400030029900000e03007222603086440a900c0480e504e8039031050070740c24810034820f002400313481800081e9104805141210060041000941d5180c1e4416180035240c2c0280c444000c00c20b8102000601c2005450300307026010034030030b24010020b20759a04000d82182d00c1920085511521070304541c1100390100005072061040707040410001103401801070881c80c00c2c1c0001400c00d000022201c0110451507041c04505045000391030260811803000001011522001c4441d4003e08030005050790051040d01c2c601003020b000280f07840c811400c0303003075800c60080100c00c24030703503800d40800c9010f00b03500d442d5140c0c02c4210b80050a04100360300d0124515a06c0d0810701010b00306006500161008002c0d0f506d40007160600314 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 149090863 1250 149089613 149089631
    0x11180402090d05061f06021c0306170a0201170613020f040902040e0f0105060a050a050901020109080a02010c030f0e030f070507271406060301120c0e0c041503150504 73
    0x1806407081608041c0d0211181900d03105005021410600580c0c1d40e008014121080d224806a110360a10603800543c000350000c001400344034a982d5030340407903807a00041a540f656694040b451071050500140d5006203c288110f5070001040305444004103080840c07444c081c1c00140e1039048500c80d00b034540d600450488544822002a1805411110410754a031a04d0f01100700c03444500319208901c4c3c0d920880005642e0510004440c0e18910940d50949415503404d81901e050b80f1100607141150f40e1010314902144035000500b40044071a4004103030000c183c1001400c1d1900701c0081c010035840c106940b07c184d40008200c0c3d108507064200341e42c5990040c00c050341061a00d030f20003103000c001c84900725501d100c40d07185070759900302400c6c1c100070702c1080c05c1d10343e4200d1004880e01d03a000751040005200714080c032000951070522075000024280e440700484c05031200240d41441c0705001c04582800904604803408549401524040090310701040e0a0f05100d4082d02c83c1d18002c0359641141 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 149092113 1250 149090863 149090869
    0xe0a0b0c0106170a0519050703140a05100b01020c0405090a02010c17070305120705030415110921060f16030518031b0c0d050307060e1911010e041118 66
    0x90004064000e44014244000c03005151140d040450450f0180134181c524021b00c000b0040301c08039550000014040c0c41d05503500c1355100807000f82c250300180b1411401c000080c0c07040006440d424070b85200450394400803000a454800b0100030380303108505103410001c40a40003c0c0b8062034030340919141e100032051b030400300c950503400ca20b0261502400035800082c95003050040ca40c1e580c404204801d40d5a91040440700d0b0301064170f0007000c181813a48624013103001703504445d000110103407a0a00d46401030f0000f80c50442d1100010781501080c100083e409503050088030350080d400246c1440700d280c08101c06c0800c6950300d202c0c009044e90f0318080b90b03607140b07500080c0d843d50081c2d40071680c7d541c0e04002981026140c01e2461079081c8120183c148050915080c00440154000001c50a0044641d03402010300399020b0840740a101d581c40e00c40700c000d0001001d51000c0d000350b811701025400300c0300040c0800c0c8018403c50140782044c1c401440455480100c03a01c98031200c14207040340b80c101c400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 149093363 1250 149092113 149092121
    0x90606090604050a0b0a090b030106050d090c090204030b011e03241409011b031118040b0a0f060f02030f070308042609010207230d03030e070b09010f0e0a0b0c01 71
    0x100719000002000c020450117030200080940b0f000c07545980d1b075080d5845010000780e22007402960700080c1e051100c8040c00320550400c01c0d00b40d01c82c500d8980030760380b1900c1c0034049030080d1740240c42151400004004030941d000c94000d554145400550103641161a10101000014903079a07174120894003aa4500300305500002c40c1c040c11044203805800c0c0004094060000c10724101c01810f681c0c00124065030103841154069107140010070300b40b500f03111030007100049021102e6001601c42080380500d548000400303015000d00710340541c401d810070308002d1044036032000c2101035500401a040c2039003440c00030369000b1079262070820702555403403909825508142da1400403202d580d8440081d108200f8000d001d184c1821380c2115019507643c0d4200304000107071360b4140d05541c0c0710324060519042c04252500301c41d00a09010a40200300c1a0081c900526940500032446000c5503610071036900240c61500d02c1176914090030722520798000200700c0219441200d24160000a603c0c80105007904 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 149094613 1250 149093363 149093369
    0x90a08031005030625020105010807060c0516031b0f0e01050907050c0d03021815040b0318160f05010806100f020114090f06070f020721060207030215010f05090606090604 75
    0x3a82d440742840c145d0700c692510701d140c0e261074040305011241c0c51144148203644c1250381030300040a000789000b1040e01da104520405807014041d00034146a61000d52015038002e40c82107a143c0440d002d00c10040c09a160150840420bc030f10511040000c50146008503054174ac040f076100c0480c2c2c60300c400985141c032403404640014010107598801a40c4c0543c090200309106032503140740214641c00304600c0c58029034098103911801d2005000c85070005c0c000d1648001002d01070340d0356031820191982b400c1204c1168107512604000f081c4000460350342500c00070318003800e152f50141003007000240188100c580b040c04210010801400c4a4400d400914490981c0310400d0701d02d042440c0c125481d240e402441c0031292041d203000c1040b640c416004103107920b07156405048101d041500080d104000c0d107005c0c02c1c1691070020070001051a40c40106141482a0024010880a17102c0318180d43c1d0142c0c44110f2040c0306110400144e1210203280c2c2c1d224508940c0c0c0c641d228203241c00034015003d150 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 149095863 1250 149094613 149094619
    0xd0204050717070504080a120311040e04060b040209030d03050a060b0f030a0b030c1c0305090907120605010e030a020105030c070b0415140103201212090f0603090a08031005 76
    0x380241c107600311052040745080880111070aaa40140545a03407103248955206944000e00c200041001d40e085815800074a25000c203110040c40d03d80302e415000303a0801c0c1c03200a045400d220411109101e29145c102e4107032025030400c84407400098a0b04070820082040c50340380c00000f24101400d5006c1800b800b5200e10701c5e40c954070386411510044c0c200310303245200640703042089000e629000490a0907244004e2800c454a9036056503071800c9018540101d007400402e0215080d10303614200030034420700380d81e600d2001c06007010420b00e095a2040d4406414001e0004100406460209640083c1502824039580c1c944681840c1031041c461b00001400c1080180c1c02d1000308804190b040c1148214180180700712409000700b031000304020b200042818a403101d1111006981011800b0b81e900000d0002c04220503024200e070504030b00c1031514492650006002c802c518091246c0e82508806030f581d18114503003141000d54420501c54041d00060002c00040da502c036140485002400000d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 149097113 1250 149095863 149095871
    0x41203020c060c0c13021206102f010b0d0231090302030307141204030e01020a020406030b100b04030c1214150a06080303040308150103020c0f0a02030607020708060606090d0204 78
    0x1c3da80c0136200d5200f500900e03c20301e90501560040300c4039000703030703450180250340b06640c50700d604d010807000c01c481a100d031040c0020403011020099124004400700c42d90001030700040604c415800d0b0840704005401441803034132126010140c1c0311070315914010380c1d0035444075218048041219a441040e5083c01800a0a2102c00010568084060347c010146a181c503074a50b085003039001b9881c09081503510300c0b0602c2c2400038011a11640d01040f1140043c019212080780a4010800b43c4170039800607191112450705020040345400d82a000805401381c425061600310350350380d28803040c07504c21980b40b0f41c4200d0131003051080750320700508091424011600c00c0711116904c2c800e410340407620f10b40010300c5d01600090f400310210440c0d00c202d81c540d5544240c0d558602d0380858805840d98000d042640c240304d1650a028204000e1305015078400041480b0042c0c0e1040501d41507008200320f003150010a401c200440c80000d41c02e402c900105c541b1a1104d49102c042002c01c0c02a0802030b5025081c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 149098363 1250 149097113 149097127
    0x304030503040312081b13170601170d050919120308011503020901080604050a15080f19020102070311010c1211010c03050106090905130507180f0603020105041203020c06 75
    0x10001c014001c03248076595a020006400006450b096411a5020390f4254090084100041c2e240700903e24080043d0036100e030b00e80c030b035031040d1401c14082c40101801e900540041c0004908410004108000600102121403074008003c007940190740d0041e00642101030f16580d03c481c810078040240c01e8029007612401c0c0a030400402c50b407020b109158500c8010143c0000380c922a00071a000850183c42d0924551505018080100401401400080e540c1c01102d00030140f03001079000108803040051507011002c010302418000000103520400c44601c01042c0142d0700418170804680d0411802600e410030900140c5041c051500004c00c014500e1b1341000540760003617040d0b4941c55018008003d00c9028907015012604217000e805c0100e136001600300240032140d00580e0380842005d64503140340da10340c0d807820728040e2a90040009000c0c0c01004503070500440c8241e044090b0080401d01110f4615000648079119a02407809c10030380d80c041c0a0281402041821591240503202c1517440c12 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 149099613 1250 149098363 149098373
    0x1e0f0f1008010e01060804020a031b0312051206090121030e06030a05040302060f0702061b07060c050702010813030c0b090c0306010e09011104080c10120204090b12150406020d090203030403 83
    0x1c000d00602d08004051400400c0c0584210070482c03059038080d01c2c0240d40c904541ba82c101c6000b000f8103411490242000220000e800040403d07a510101c0e182c032900d400ea5007203c945101c10040c0f88601070390040d0010041c1001c141e01c4192002c101d040e80030300301200d5007001c4400b072940c800403a800903400018408100520380c040b40c481e900a5003550669100d54400600901c0c05941e4100140d000394041968411880282607941b0f48000d9081d02c1c0548954942041c1c40c0e400c800100800c901284840a558015624580c00400004020480c1d03c03150340c00340c0289100c03070024004900400009440100c2000903100f1000001d0440d451982c0d02c0c0c00003030740351130102c1c0d1164081d42401c88441110302c20b401501e00fa20408400340040042c00070501001c0b04036080c40c4410012900081d07201c0d0801403005002070041d0402c0820a00d05030810b014a80c0c081c921018a40e512030000200c181c00c01c0794030780d0f402a1f40043d02517520754000c50310b50003030882a980a50f25020000340081001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 149100719 1106 149099613 149099627
    0x1d0a05090405010b010f090303020316110904050105040302240f04032303060109060801060f0e040b03070b071401060602060712020d0507110c1e0f0f10 67
    0x55651001500541080da03064950340d644500310300b070303a503801110781c0392190b96410613003030b20f51950b50025500e01c6080c0000d210b40c2030034811901001990040703420b42d510000c04c91072641c240390070424020101030324200c0240c80b5014140030301c2007455800b114000100500c01c01386c0d030348003c0700c0201d4880051048042041900c010500741e4070342c00c05040f40c0841204032a80740c0c601940090110310707081c2c000e4020300591400401ca15584034203043d080c3c3d1094549520340d40c40c00340116014200220009525000700000420030901d034401814116001e040443c080c902040e4501e42203070b116000b0400140c10040000d405140103601002d508a4603441c010301d040d0b4038010000440c1e0090f56090000341038107000c00c411250810036200040340448041c140220000c444601018505040d1405440b184407031500c1030f500e92a100640c50000b45c81003811a51505008180c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 148920863 149100719 := by
  have h0 := BRFrame.cov_init 148920863
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148920863 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 148920863 ≤ n) (h2 : n < 149100719) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
