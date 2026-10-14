-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0216
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:30:38.423158+00:00
-- url     : https://prove2.me/submissions/e88eebf0-b395-4251-99c6-ff17cb3abd57

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 38669069 ≤ n < 38848925 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 38670319 1250 38669069 38669077
    0x105040b0c0106050d0b0a0501060f120e031303080d0c080106270302030d021f020a230d050406050105040c02011b030c12020403030e09070e01021002091c060507030b010908071a 78
    0x5d4102c0d006880440600c09440e881510404614109000a0740d80d040c080b0f8000742915495000540c844d80d1030f102580e290b8010503154028603084a042c40c04044104207030174070070351044400007000522081004441e01400b0060744160400030041d62602c13201500807100c11071030031092b6071150f2818014680103088a405550042d0481c0d5580c02c5200000c0c0d961055613158120700004040d08800030b401a0017141c890310301541d80e41c0c040c03140075111800c00c0000002030140205083c040b00c0003d80c114402c0c3c40c0b003140950008070322945800107000032a24082c482000316410910120030010840c1c0d0043c848071694030300025180150f0384110360111214082807211400040c00206050340f201c51544481001c5508903040d4490300c2d400e407011940c1d403200a02607003010b425583c8221155000e049143c20103407601035000811403011042841d004400c481c840d071b647c818000c20350340c03611a1160703001081c284540ba480c201846075945c0c01080c452100c90039800140c402d50f401452083e6 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 38671569 1250 38670319 38670329
    0x80c010608010e010b0a0f06030509030d0504051b0f090f0601090801150303030507050a0212030c04030501090c1a0903060a0b0f060d050103020f1012050601031b0801030b010906050105040b0c0106 86
    0x20000c0d940c456001e070340030307288900306403034598200500340300d2500c2c1c08080c51003158440703c4001d004500e02841540070b801c00618540c4203000a0011745c80c80f0000340100b41c8034510071806003c00b00540c0006c1c50055018808260050060015002c0c164881c1404540c0000384194503020310740d2160300407558a5000d42005000e0b5081203520000900d4001440d03043d80d101b51014807440c3d480c5607003114a401004100c100692010881c0814045958002c2d9008054440310901d050307101e80710182542c000b1030086400100500013001554a100d04e480800f04400c0d10703213841d0402d9000000c3e070300c0c2405807400082a564404d0242160340f0f408000c1c00d0900b002d85020780b5254605200001440248020b90081180b0b1039403208500c3c0c0310140c0324250b603064032070740c1c0c0042e4060a0132005002c000d104a042c1030340d8045100341410491000c1b0608400741d5184006503041d45004909001e0607072004580c1b9040401c02d210581c0c0040030b440c10340d05103001140c0c54110213048940035110320790103 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 38672819 1250 38671569 38671571
    0x503061905151305030105160c05010b09160f0203030105010921060e031306030b0603130f2a050301061d10030b070807020c030a0b070f020102040b0a0302041a03040c12080c01 77
    0x2088442c680c1540180c0105030102d00c1c0c40190300d649400341030a0301c00450780506070000c101014083e5078001c540d85050f640c06500001000c0c5070b200c0106418100698001b899061000e07404800f40f5480007001034000c01903c0035504651618002a0a948207801000c41e00c160100c00410400213410b0b000800d01c0d0800e60034014141e0307240310301d0307180c0c5d001c2110070030603425064022640c0f074000d021794414401d0152220307146a80d00c8011855200318810103c071188084a42d250120340c0c40072404003c44d4400078401d000203e20340c1d00d02982d01d026401240a6410a42e08100503543c40c0f40c801d1b20303005140c0d008030300d0740c2d101040c1c80c1c42c0d81c180340c000600c003d10600a11140d50b900100c0544a2a619001c4030f21040c6104201943d911031641d0003030041c24540001400f00388070311404440719000b030002606081d21030036a000c40d600941d840100180d4045401c0100403982d0b018842101e006040140c91030806440d81c00316560140561044004200e52944c10461100c0031195031340b01310f00c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 38674069 1250 38672819 38672839
    0x118030504030302060907030f08071e03050d18080d0e033106050304110f040e07090504050607050a1b03050c06190b030c09011203020106080615090106030b010503061905 75
    0x9009085500300303000640051060400082040e44001004415250801c5242020040d565560612607115180c1180c0c1d4100b040d48001c010248086001c100074401e031501a114520000410203e07240c0450312903c00740175020450124100c182121190300140402280f8004c948003903038a10b105443c40300c60341d0708d005584641c1414ac11036801d035410045090340c1004951b01c070011601c0d800241e130044c0030034000c100d0580441c03501542c01a64240f0140012803261001c20300e05003403030015480203010316121002c0108000c824000d0580c42981401d12030f00b4218034040080402e01020415400d800d00303070407403405250140d4140d0f05244450301c02c8030f102e0300d08400c2d0489801220041090850b0400703218220304d01d00803441a106074409403403e03010b44c1c44c2c440d04a461072500d039015025550b940f140801c141105000203840703102c02802d912060498a81401310007031059122100701441c0113400b140c00e17079200003201d0700140c0840d917130320765494400401c204a0016078001c6501c5a4050 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 38675319 1250 38674069 38674073
    0x503070f0303020c12030a030b04110d06030501060501050c100504021503090d230a0815030a05070806070c032f0f0717060103030206010519050a1404050a0605090c0a020118 76
    0x200009080d2446903080d140003200d800d045c0304071030680000c001c00b50782040c480c240c5424400da200900050000b000844d0946403104403c0d4658400c1500c0086191504418403c2c000c00340140c000500d02840d0061501d0244845140c0b40c42d0b50813541d00406445001060a40d5502081144400b8011b41e040f6920309003c1c1d6170b2951040103175040d4003c100075040142260305121006101007511422062810307002c00c1c0100d4101134010600c0c1038a0f80f01890880160303c04112080e02640303d60b0007426042d0500a2540c81e00074000c001300104100351010000182d4080b10420154440050f155141d50110b032400c50740034407a5400288503c1560801d0f514500d002841904840d03900742001c0102124580c0710352116000d009c0640076034032210041025040c940c00041c1d03000103024036400c505880b440095180c002d140d0005510070011008824146050b108494100c01c404004110f55440c0002144030000014444890042e020807080d00990007900b007104690005049410400914 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 38676569 1250 38675319 38675339
    0xb03150319030f0207080619090c0306140a06050604030212030c160f08010225140f0304030c080c0d0206090402120414060705031012060e03031e0c180f0a050307 71
    0x14030402c2d00040c640301c6080041034004a40e030026900081e02808180d0344504912241c0c100f14410b1007002a501e907460b10211b513a224000700910f1040002080e04d058000d040d0140d000054900079005142c0442003203540d03545000c440850358140e6103450081428154141140140c21402c180d900800107440860300030005020309580c00e0b9014210034540320b0915a00300c0c09101c135148104503c01c140700054002018004911611401d0090449034401d02007501b0100724001c524419400810107000700300c90f11005034082c0c01c1e0003005105940c3c95100203911030701c584e1000b0b405800d00150560147d01d403501241c2041904182c2201513050078a00614441c4160604402a0280202041e10a8030070301c2140c1c003a1202d2800d1007001c50912611245200240b44100c0b26107079284c140e101e242d0010b0014501c00d1110b180c9501c90041c4030340d4412b5405500401c260900d9800f04204d990181903412200c100500c1a646002110113003004034820000c0d0790040380d0300d48100f40c000901c04200c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 38677819 1250 38676569 38676613
    0x16060501050406140904111504030b09060106030b010e0d1103030c03030103150501060903030f090906090b0a17190c090513060c020d0824090a06030201110303100b031503 75
    0x291000c10109540c1c9007a8656650391004a90b80007070402e010a0101f040d40544560285009080c0d034480c002d403802000095015900c200c07151a001020400d1294040c0010390040c8802d00b410b1100340c0384040005c01c519080030724184070b9010158000b0070700841c07168105d00400c0150480e40e0382e0360000d00340c40d44d94009100c00c5502540c200d1000303a120b4007500a081c100c0d000c549131281501d09550f41035a80d41409180081007202c2010000382c1004c0901500e001421000d4001801400c81d609011181c440c81d00b142c048070303a00b002c8195880b07100142c510740c214860b4682846116452400e0391381c84c0040d0f4000560315040509210091004021418005216160030401d00c80c40c103800b40e0b110090302e4a40c10101c2c640400107440d03072425007d03120070b031340301c0c14091155000481e00080003107806841c0c42d59801d030b80780300c103008558001e511128007845220066040d4a800d000c00c00b44d06003540508030011001001081441d0750100444000410040c00e90303100b031242c24415100084 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 38679069 1250 38677819 38677829
    0xa06030603230705090403030f05010303030603050c03160b090a0803030405150f01120201030c0507050d0e0102010608070b16080d0c1701090c0806010e0d0f0f050f120706050c16060501 81
    0x510101c010000c4404803802d04501502c00d0042d10b111842e200811568180040041c1c0525450b4000300c28290312510070540a103229881c006603150450910600c2c10342c04032400c2d1300a0344403804042c1084011030302e4800300c82c03180e00c80b01d5a904154001c5801c82a8940c803101140c0300200a201c2084400b28000000140000c80d030916507588034920300c0c100c0303428403502403010301c070107036074000343d4443d400c001c100341740d02c0c00c0282c81c100b280d5440910341041030520341c0c0060005101d082c160b60b420b01500c1e00030b2000b400280002414088080110700c1840c288880c0055400c0c2e42c1d10170000c800703007036400022456000700601a072000c1c014007018403001114600030203041c0041840c81040c451a040c10040390b07030f81d0308146e44440040d0341034003080116507448061484800006900710700d0030800309102e24101d41a107203440c500300e4944031518a00700c00c950059010100440902000c0d900340d2034000c032010905490780c4071b6117001d030b1203841c0c0707044401d400c6080700c1800d0001940280341203507 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 38680319 1250 38679069 38679083
    0x1902030f0a0c0f170a0b030a0506010501020c06071a0703060e09010204031a0708070c0203100608100b311b0c0506010503010b2103090301051003030e0307050604030308090a020a06030603 82
    0x20341942c100c41c0b10581030074110200f168548180051420045990780c810600d401c001520303030000c00024907041c02e5660441e0290301c460010301880d41d05200140c1c00e603105403a9a400c021107581c489019050803145150300c0e800c0302d000602c030035109402042c010110040f00780054103100e85400d01030740c0140800c0d14042c40381c501d001140d20358412034900c240d507150780d200e20301e403550f08003114080a8842d003668988560001070410000c144580c00007000783c84018802c07144503070078890603900c060720303658441d0b000c03c0290348072069400301c03d46030b00c8900b41c410740f6144950070144c1c000b408698007160241103213426686a10f034100d252014000d00039030489a4a0388d8072000c25003680caa1044103034100e48038030802480c00520141d4200506019001d80f4201480d07000031070b0031110111010f0700e03140c0300a1002c1051540001c03070014842016805000c856040001151062160340b10040400404000140000c4002d2040c002140d5006044021040c0d45050040241c039141c013050b20351b0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 38681569 1250 38680319 38680331
    0x40309061403040305090402070f0204020406020102040e0a060f03021003020c0105040b2502190303090b07051e040e18010b0d050d1701030c061110020f070303050a0c080406051902030f0a 82
    0x10001d0381d02940e02c216403554880340b410000d00c2c14403020707400641c030860700c50549484002c01a40c5500240014088907030006071107c1c5000000c0781e10440103060400810300d860024002d000091903c18250fa406a0361490713400c0c0d883c1c8088002b88507542c1d03000c5107175203410140010010060078180c05406229119034500340d110300041c40e0003410714007040142c0e00210b80b00c00910305075031000d05034078001d0400007109881c0713031a4031070b90311021222100080c100141420054074820b06445d042088400068201070600c46000c1d8440c201509044200e151084079004402094000c000c0002d000f500f0a620b8007068900b0a81d95440b5250001c0440e00001800c4041100e41d5811412a0780000a80300824949142942d2903100a5400c1d0024010b45008031100a40b600040400d5812098401d50310b40040c14002c2c02c030783d805000280120b04001103c20b2045c0e11040c0c0d0380e00030303811550019450b1244004e901d007a448142200000700e001001304506024556059845485401014008 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 38682819 1250 38681569 38681597
    0x6020c01020703031d1c09080f06040309120b0103080d0603051902040c1d04090c080d020f01050708040b0f07030f110304060506060703050301030602090604030c03050309010905060c070501110c040504030906 91
    0x1c102031720034029a62200f140302c43d10300c0c100310310072003901c0c4c180c24956a1035850304000c500300190342100c10b00039800381c1d007840101944484e642004011640c035415825501e941c0d691011a01132002520781040419a41c5d003140c03940e031104000b582c2c00f504440d9a004002504000301590b401d050b0712507032510a480c800701d801094402e68442d03140c80300608501c00b0500700700c0201030aa0702500d201400c1000894590f90402c00400b402030640c00a200810150310200c1c01d5500040c0200300b081030103c14800007640c0d40d800e10f0b0f04a180303a8000e00881d5603018044005015210380b05400c1805c00c0e07030380c8880352001c90040d40500d00625007172180ba0340d50401e01580348105000140054401c0004101041c02030f070160124100c0104624541543e94846458103502c2e034001b40d03280e0f040001c48000643e08800100000c0805880207402c19450402030741e01c480140c4030341c5041c0800f060000301c010b101030014450160006104100c5802d15060041005400e0301849010484044110300 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 38684069 1250 38682819 38682851
    0x61203021617070504020f0405030706020304090e07050105031914010b120901020a0804020909070515040e0906010302030c040b0a03150606080702031201090b061903020316050c06040f020d06020c0102070303 91
    0xb0048440c40081001918080c20310000750301030900c0c02c9800344180008641a581403122034000e0059030f00450719281005140c41c102e980305901e5555540c402d841c10490f598120b015a0352011201c0e16860018000e403402e00c020f020b80049007000da02600b00086400c101c110003501c84210340900e0700b40c0c9940c50440d0326080348a80b800c41000702d540280094010f01c1c240c10000c0d0b01050100603580f40503510b4000c070380d91412290140000710700110b418000d140b0064007a035407080c04403000f44259403450700801c0d240c00040e1143e0b03004688684814200f07840d102e0752400115401001003400321042c1c8080780c02030507135015460001e80504c010488951001055519901e51440806100d1b440c100e0304000801c0300c40d0704547c00543c00d0182e409074071b00410014450300120b45016036a40350041510007464003814003601801070a11070195419400601e0641c06544505407034401c400c10300003c0c2c0c4800d80600014911400001c1c600321090341034000d48011031080d207040c00100c0304040c10300 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 38685319 1250 38684069 38684099
    0x1110f0313091a040b031608010b040e0d140f040e01080102090901080d080c030601090305010504110102070510050711060931050c270303070c1a030403020316060612030216 76
    0xc0108003c0c144141413030660b001039441d1400808880f108003c50243c1b0503202c0d05a030003000300d079542d2a4400402d05150003129031080e80303507005c0c1c112000d00c0c28019126802c0d600310000c851001080402c100c5c4014000c0390f000d410300b203100310784542c1d442040c24040c1d404078000c00e01445d080800054000300010f240c08850710241c032004010f0303490400030856030300014946410040281c40010104c2d00a1203000d0041d40260507200e0f182100c1e200280c50400150b116034016002690402205680002900c032003a5001b0b941d0b04120001000065941c0100c00b0425800001806008018450007480d400c10907846442c2e000c0d141005d8a0314030490700708990400007502c0401000c6000c00c1740c0c00003503040b007104800904c03201c00d005000c41e1650b000301d0740494202c80c5180003031103002540b4042d1801c802040ca5101d2840c81c0c5079a0003500d03409108803012a1880c5101e01000304031160700032001400ca45102c1c400da407003450070000d40d101c500c00b034415030800c20884041680f103030300c220341 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 38686569 1250 38685319 38685341
    0x90c0d150f02090913050316110f030d1704050c120601140102010903120902040906110403020114030603030a18050607030917070e16030f0501060c032a0305070201110f031309 77
    0x1107001a030705d0886101c050307810500b007185c19010400071600850522a01821018058450300e0b180c03040c42800d02c01141016100305100307502c01c0c00410311640d4001c0d4a088c81c40b10542d107014164a80b072030440d00d0514070009443d8001c1c0c8050041131003003400900076040341c2e4461040c00d610146032005a00b03c07010001e0240005454140810105089410030008584040e000051054058035100100c420f0303080902051301c8000790400a42da0700039604401e070b1310016120303440c5051140c0002e07941d120b1160503400340510110011b842c13110001d080c0f40140009084141d5480e40740c5401071403050107010716080c54290401103003014000050f09010360340349559000c25a2100101a00e4a4402c81c0300401003680381c800c1e0850500b19030140900070101138407400356a840d5403801070a000401e1030a500807041490b0b4003540b40465203c03403114242c00d0f06103141c0c0c1d4103046c0012541080d601c07c074603038540b1400e40319941c0b414000004200002c0901e52030745550b9203c42c07140054884c05140 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 38687819 1250 38686569 38686579
    0x60305160806090610020c0a06020f10111e0706090302010203220203070e0a020405031b150c03090402030c0708070506010e06030a080d0e0102040f0618050411030a05090c0d150f0209 80
    0x7813040e09200304003850b041c0613801100c40c94115600021400c0341c031030b00b0510058000400103101f0104c104068918000400b03805d002c8101d1050741b000c00342c02660f004d81c1c064010705803030305004050700f4200c0300000d4104900f4007598440d420080e020b50310540e0310320102004030341c0355408081454400f608190f070040107014400d2410001c5040c141e409405451950303800c000014480e5402c100f50070090110401540701c0c1035240c1d0810103419408040120343c440100981e0b10110b4001c01123606516040350010b031691109501d05040e40980d410007413030b0320400144101444000228281251101d19040034965106d0041c96100c0c8078048009041800c2032041c2c0218040981090302d441341510001803c0c0703951409011103006044c2c0c444c2010582d200450040a5101c2d8031400151006850510806400c003e8010380d0344002092456140d640d603001c660700d404248040c00700482d0042003489902060709000c1c0b031a0311030a80c03800c10381d40b0b042418911600580240c80110800800c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 38689069 1250 38687819 38687821
    0x160615151b0c05030706031b020616030207080403020a1d06100c02040b0612190506010302090a06030b04110f0a0806030606010806010c0302120d050901140402060f0702120706030516080609 83
    0x30455140007000803a441c000640001c107064501304039031002068284d9003c18a00c100800b0044a00e0055080d6821074004030100a00c0744045c0c201303200841c6403460016510520f80c200108140030710780009500443c10304000500e0303401030410391098030610306042502d45860040200d808005588500810905159200903182c258004006100041d202e989054031200a02410100481c0c40d43c88201e00070044582a140e10320034554840402c0c01d0440c0380c22002c00c0040e58242240c8100e030205615454070380040c1d251034004072009401d00e20081c0d00d4020070106185941c120000c420009100329000600030310b000034449010307a106840b0410a5140c08004440f0510345e140140c082d4030951004206000c14480144000d0581180014070307070604180450a50b0701c080e101c140944010b506010140c1d89180403591801c15580d416aa1803c1900c0807809080748418920000d0046010010300160103030007152003082011014102c000070303620181e40041081d22055007059540c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 38690319 1250 38689069 38689097
    0x1502061302090112020a05040f05070206010e09100c020115060f171003031407080706090c0909030923030303040c050405091603030302030c040509070e01030c0f08040f0816061515 79
    0xc0d100802050000c6d00c1580099159130114040e103c0341810017196a54a1081210b080d905000c40742c0940342c0d8010f945124141510705590301c0c03083c508004243c0d552601c440c20381e00d00035400740161030740b2505080186603954802030b0581e519109403c3c003203900e60b9050f415000ca16040d181c400c440b8050041211030441e1811a500e490140414203010010000c010220f4150b0018140b1288600782c04515146070b4034142c252111a58030140702c91341000202c8000076000280d04080e203071030305a20300f1080b100d54441c4812415a4032020b0b0140000010701081c446609061829140151418049901c402520980e1003003c2440040610a00502480001c0c0b003034008613008040d00000034100350705c40300043c40d10718040d2a40c001040c010b920211080d6050f00900700c0e0403000c0d08080110488850018005220007040200703d00028030350b10701044404000d8030000440e180041d12102c80d10b01d0480010485610b04500071130000e000010306150000401c260310805507982a8228400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 38691569 1250 38690319 38690339
    0x180e060102150108010e01060b0306011d010207050406080f0115030c0306020901051209010c031506020d05070c0b1201060201140c0a0503090109051209010e0f030604030c060e01020415020613020901 87
    0x181485045005200703145100c10303096202540a403c6102c00007401e00481c1c4002401c55056034041e440c002070a000300140e9030303001046420001d80c8801c0d6500c483c80640c00403410320007690440c030f40c00f500d40400032610300780005d0841c800403124002040220300405505204149500c00203200599607a0107000180041c6c020789010030040c1041e5080085520071100d40c410100c0715090560f54503079840000c0303941401801951003aa42e417800e51282411030094659001030010b03400d2000009400c01004407000c1081c00038a03800d0352007929500000340d5811104801c1c0702d00c600542c03c042200035111241d1803028060f0103c0c0404514181483da8203403440d4100400d4404c6030f5581c2c12a22000c90014000c680784903512204c60b075502e01003440090300380e884c0100c0140c001e1030038034100f043c5501c0020ba20740c0c01c143c150802d5074030b01c505454414054403d420301e4241d06e50000c01c000031045a00c000985171103906400b6980150303100c1c40303801e03000000840080d50046124004200340c0440d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 38692819 1250 38691569 38691571
    0x10b090d140f010603060b2701091a0a0f03030807050c0c09250201060603110304050304030204270c0603061e0501050906070b010b0c060603060f0406050a090b0f09010c180e 76
    0x880d401d40380600b10411800342103a074103900544042e0b0719521200190718050758103165820705405412138640c1412840306201c1414021400c0c0c89a43d06605100d40900e0780980049560060480311f01c00c0e00c5800700d02902000303110860110701e0b6100412540c038004d0003034a11041c0510001c01180c0c4032102048581c3c140608883c0f6501c0f01e148410500d1681c0700c0311004074401c1500081602032a0501c0102192074401d01840440010710078080042c40102c201c0d402c490301118003003000118010001280000c82125a1030f440d04100d461080010418120040307680f00c0e1410811a90380d43d49050300e01904a050103194505142c00f0702140d80100c0140080c07410140416060451640d28200d0b040c0c0280c01c41d410106001c502958200c500304400b0f0340c0a4400c3d0090700141c282520b017920800c10207400103242c1e6484030000707400c48000364414000707940c1000c444000343c00c0c00d800c030601240098503150380c0c950030200064203082c0599074440b8080035a18041095514000080c180c100e4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 38694069 1250 38692819 38692853
    0x6050907020d2705090703050711010902030a0b070504050303030907030303050f0621120a09080c01020f0604030503060607120f030c020619051506030414060106030605010905040b012109020108010b090d 89
    0xfa03641400310b0075480750303800148603108545001605082102d000703400c80410241c04009030381440000001a107001c00d2104000307500810144480d291140d00780ea0501598101c980c0500c80401040810300d030001b60442124002e45003040b607611590068110a5070071110740d900507083c0d03511081c08010808100b40014148415100c1e5540801d01078002644203c000340005000b1000910400030248200704240509000800e04110b66041d566141c0704d0040003d07003445400b20001740715454110440b0700c850303801032030700c00304520a5a010b04070b032401e2052040001c0c86c0401c60300c03a15000250243c0200b0004401031900080400c107500a0140241200d42a50b1620a041201d072a44c0c00554002c5100b0007601c41e00c8007005400c01d04d0900160304c0350041500b000001c10240e60044506000d03600d050718046840444000141d44515030783c0392455002d54007154608402c6d40c954010f03003007203200340d03641841c90343d0310482d0310b040380144070300194001142c07856800001c00c00c0c0c164503030000b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 38695319 1250 38694069 38694137
    0x604120f1203200c150901090b1e01060c030201020f07060501170a20010905090408070311010506010804020d02011704060501140405060315090a0803010e01140d03120b06091306050907020d 83
    0x940700d174103032030188000c1d20028110ba460301500002c0010780c01e196540b02d030303941010071000e101d84d0021541d0150184a24403d0180000036042031500c01c2d011a8001c101d5044207031355405035460001300030282417060b108500300c58458200c4041c008a09480c5064219458840300b00644032040075581c40b11403268140309030381c440060240c0310115150310450041403201c0d01c0740d4003414040c103945203080702c02c80540d140c10100104d580c1c00401c0250840c0c0c0503502501090003e02c0161403a001e00700c0d0a40304040840c04020401c01140c014505a40c4000080f02d1305132040b0303040c8010b44000340c0b0510b501d0b1300541c00c1f000b550500941480d6200340141c2c11140c0b41ca02a84480392542d1081e088108c6480c400c0300144000e002c240aa120074401c02d4560001c07101d5035881c000c0c000554500c145403829252010118540d58990a0700c50b083c0c401041d2103907405c190304d20400144401c4c4203040c054039102000801c4103001050000c42d00790903480b01c1d0040c16207030a00000340c1c038169880c18201 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 38696569 1250 38695319 38695333
    0x306040b090420010f1b0602120a060302010e0307030c05240409090501180519050708011118010c03051209010f090510051008030403110604120f1203200c 68
    0x141d07980030402406140182a412545003030a4041e0300d00c1c1d01d101a1042c140b1001075403581980c0e1b4809445100381001101b4040d03403840601c0e00d040a031242e291400212078411040c0b11402105a0226007140e10036290000c10100e500e05041e201d103ca0310016107494000700003003003075051044505994040305d900c0c0191080b0312801d0500b081c0c100340c02511400d5174800ca03c8040140c01d00c10580c442156283c0c94442041e5644c0c1d8940c0d0302c1040342c462445504154890040101c200130100c080c0250760002d0044c540c03008040d2000c0e0300080c440010a001c42001e01100354018400d80324070395007680c3c5441c5015501280300b500080c0252482d88152361701e61b6404145103181c411201c40720312510280c05907408a40301d43c000d4400c090301e14a840e0722342d000100321409001040321b045962141e0001e03090035402000405c24007031a805408140b0040c4002400c01039042100c1c09420f110785003810540e501d514088045070785070b03040307410369109000301a80301c405401c02500c80c0c4400601100d0304 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 38697819 1250 38696569 38696591
    0x203100506120f10030206030402010c02180106111005060303041505210613140a09020406080303010909050f0106150309020409140d1106063625020109110402030604 73
    0x49580128105190b80070258107100f0007140f2010030702e402100190250f00b0250031034000514600c0302420007030601600301d1407401151902c0140f0001e032140804455015a03403040040d1613502503103105443c90241c202000c400c03200c2d621682c3d01910001e00190f040038200f01c1c0c0382c08408100c81c6a1001c2c031005110442c10f4010860850140742d1411150300000d00b488418444007032000c20032412070a042070100844d0b4103860b07015a51100c42a20045285101030010a00410701900070501e0b85c000000040f401070504d412188040e4070590441d000400c07000c040728200d43d0a40180b00c2440380c00020800b40d00c0c0300780c10140100d80010300000d0181007641d180706c50280c07210004c0030030303401000c0f50002c0740d90081c84008082c44030401519a1b4a000e070005144400302520074202121003060201070501d2000c2e4050842d131400c08a800079080c003281200c1c840c44182c0c2c1c3c1089620303504401d00000e901c18020200b00603813141c010441e4051010401c07019400040115810940d40c58446003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 38699069 1250 38697819 38697829
    0x90304090e1e0a031d04020c07030803040c060914060a03060504050709060201050705160206070c120503091009080a0b180109060203090d05120a0c02030904050106080f01060f0f0302031005 83
    0x7008445009000c0442c20103150030100351125a00c401c15000410340b180801c1d004840f224203d03101d14500c150070f01c41000010001d005404005000e0f00ca2a0700200070040400300850145005000e118041951184100c0c3c400c0314a01500c940c00300004031902042c1085070142c40211064180408c0c615280c0700864101e4408440c45400903c2064042001e643c0a00c9240e0300665145462440d1170003211069000624003e40240255400504c4805200000300070b03002500030561424501000c50400d0356683c2c1005d00c1c400c1c841e4042d10020300f02ca500a410765011500300300050078803a10b00380c888001928000700064484040c006036105510400e2041c2c00361284149001a140e0510010306890042c103000010280301007005034035242e1468106030396010050983c00b00c2c4800381080102e0950054403000f0360001e0030200081401ca4100010911035040900151210703070b0381e60011503508100d40d00c40000b05000044d003010701171281c4c0003158032200c007503140304480d0b40d280f006c12 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 38700319 1250 38699069 38699081
    0x10503060c041701021215040c0201020a0f0c0804051c0b060906100818030f040f0f0303050f0a05090612070e090c09120a0b0103080301080f07060f0806040f05040c050102010b1206010e09030409 85
    0x4110b51480c038074030302c0c19240034800d07901720003274030320003113091070202c40002d8800c04409200f10103210fa078141040c20411078200720b030017406015000100c0040e8040086094411007070003240c0c04651034001482c54100003032103612420000b400718400c120302510031303034405030003400400041000c145080c0760440200010001804405142543c5030310b8110880da5405039900801454601114100046544081079401036000c0194203559041051001d4505201300103485400501c04142d01c0c40311103034040e0491240711075803074400e2641203000c100881040211200b0113038200602049041d030a0140e40c804c0546400d130115529249691926040940300340d0040703600c01c0000006010001044c0402d4059298600041400f1820031802509045000080b5404c0242450002e889c0b66965004a4601c01c10b40c04100100d0800d0b052504602600380a094095824801d1013202c0d424480d5048160803002000351400d6420051150034080002c1d00003996844207110108450200b48218 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 38701569 1250 38700319 38700331
    0x81303080903190b060603190e0a021002010b0a15050702040e07060f050f0a1407021008060316030c030605090f0706020d0f08091b04021b0114010503060c0417010212 73
    0x1080c0c941014900301803800f0b030f8120b10401550442e144560020307010346509030300a41e08407401d030b41326a1b650820045d241c640744442c4410318207003d8076200074034010458040350f50003940c603010101c500d12003d038241c034402000145c00c0040064108204c8005401c0382d4880c040c2460003524007800c680019040e2000164584250b80041c03108006807030f001702000309001d010781020f80c102440800c00c01864020060200d00b4801d0241c0102000c4208008403080740740d005000d0b03100038107000401060944121030703070703802440f50003d07000e840c04a521144044035400740400701403d086035941806410080d003003840d135100b90b510320200d00320144410400b42103940d0003008900f91150b0300426400c040444002849046001d201c40207101141030398016100e5010b840c1405005004280284a43c0b1050038001513019a034200045040d000103140410304240c40002d662a50209916035100b50b5401141f42e904100400948208400034a801c600318800141131203190002c84444103412204 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 38702819 1250 38701569 38701583
    0x131e0209030106050a050105070602030603070e07030e061b0403081e04080a050106050402030f0f1005030d020708070906050901060804030c050318040c030c2703060e031c02070308060409081303 85
    0x11560950800744240f2000b444100c48503000302d403800001034841c0c0705814000e0f088640001c00110180c808100007030013020410405000780ca880c220080c014a207a061283c400d00401011a82c2030b00c642004c90840c100c4a40b0040c6401d18582e281c1e50554480d80d02c144060741001184100700b40e46c50040c00041000744080c00000b1300b0303482c0403401c68045800c414400e501c10300c144840d005900140d40e906c4680e04200114680f60b00c007888481e041c0680c05a58544200c0c5050b180b125408175148045440480c00c0706c120a0312170f504c0509454490080940140850004002d06881075090642181c040d00300740b10314020548405046510984100c1c0c01c14000e4013006042c3d040a11504040306440d2030100f104184103000185035407151610107074020700c03403035580c0341400503021140002e5074459020400180b1020005880707411090120040a0f0000358445019005008490005070325517204403096844008100091198900680e15400188604a40e942e550702d8054003840c01041 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 38704069 1250 38702819 38702827
    0x81303020c061803060703050408030a0207030c0204050a0e070e01031203020a1b030c020a05011106041112010923060c09011b02040e010501140307030b040b040302160b030108010c0e060306131e02 86
    0xf040c140b07442e10142080042501c2c000070000802d50003401d032504030002050141c2d4490131420100da802c180500c0195000e0f181c00c00307011210206600c5441645409810385003001c0d550795030b40554020903c800307000c014440303000d684030383c1c400d40c02030600f61010b041041c81da110041e0042e143d014890030840100e030341c04400000398500304940d000245001d01c2c0405106c5019900d96031100005000142061600081718040e0b503100c43c000420a25580c00803c81c8010034101000580004102c14a940d0180c0f41d684100301d1001c15074030301c80c85022581e0792410414000440c2d510507005070018a032040c41281d0001603444e0700804020030a00c0c800800c0d194107010148480e400480b40d02031007644010700030000103541201e00b03a030060b0000180c8105541e2410141c0c24280c666030b0352040d10703050120104100d45c0c1000070b54180c0d08090000c02c40c8200c82c20b0241c40000c3d81810035a404503060001543c180b4001460b070090141c0a4800314030b40340d11f241941c0002840854500c1500d802007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 38705319 1250 38704069 38704117
    0x90e010e07170103051f02210f090309091f050406090c080106030c12020706060e180c030102030609040b09100f200304080a0c110901120201110706081303020c06 71
    0x342044031940d401078502d50740b54555524a03035189000146403d04080d0800e02d246100d01e41d505444800d070204482c100130b1340100741c1c1205220b4084036000c0082c1708000204008a800006407421084054240d1707401e921018211280e049041102c0c1400c03c026240c00b0545881c5d41c0a100d00030891110040749100c0030030300160141700140c11581c20540703001c500066040c0e000c40851030340c102c00c100040e5140001e0134028007815150300f0139008800b0790002d201c0c8010305034a0b441d500100d90320640d82e013166418205800c0c0d10064400942c041c4111010401040ca03100c039603504a00d400c02219106850012100d00b9510250109841c441c0c0e680c140642c1000c500c41904082d41050715500d10714505595000030074040c15a5817000c0280e00c5412504100342501d400030640c0006107140d81c42c0da510000000c0c520b0321094124002400c15204020700c4070b00190349000d480d410348841c5026510041060241030542031305408602c40c4a0070140d4580b2001e00a140b1a002e0041300544c41c1254 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 38706569 1250 38705319 38705327
    0x50f010c050304030e01080702030307030f020403230d110709020a03020705010614030c04060305070902090105040806041b05040506010804060203060a1706010608090f030f0d06090c0e04060909080910090e010e07 93
    0x840301c05d410b02071031500b0041090303400701c06c0301d620007050700f40040c0e200c4005c0c1c1003e009020b02d81000b0006104400140b11120003102a64469444c0000301e92020003c2c40003182c000e003075104202c00135880200207020340d01e0560041c00c00c2140f00c1c5401402e207a41781d240c040c20364895500203c40741c0f02c038035502201402e09100a42d4a0001a50188000c9e441c550f180f59840f01c1074490720422550203c0c49529507880b41d0216402018800200c2d941400d10f401d2008541c0c0503001e080c02c101000c607000040b2820f040c014103116110503117400c0899a503585031680070303501c0208141e5000c2d07050301000c504290300c2064001844662002050190306207076000e0000d10002d400c420040c0e2140094a00300e00e000000c54900b0078200210070b448003010040320340540650741000340d04038142407a040030380780e002c019007007030000c00c48003801025620904d400856004100280444c0340400c90483d0341e007441703a40c10000058500d0400d6100742c3d1071140d101013a100b0380001c00c8503074120003800b46031540 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 38707819 1250 38706569 38706587
    0x41802010905010e01050d0506010e0d0b070206010510020a020d08190e03060703020412030e03070906080604020301110903150c0706020406020d1806270512010b012703080304050f010c05030403 85
    0x13802c00b5100010b900c07001034001d0081600050209458200050705c41c1d00c520301c80a03066401400c1740c10160514581441c800304119603180c0107100d1031000203000d1074046042c20112040350050000c0d110580c09022592076044c6d42a106070508000827003052248078400a081103c0341e41c2e010100c1c140108141c14a40041d0a58040500601090104140d50ba0140c0303401540340c00d00400d0341da41540400c0c10221b1503840b101020346008000181c1c940007040c610b01c1544210020010450140400d407510700400344500d81640c0001109032130710310041c140c5500004c42c0640e590a10381660703100c800382c2e800350b040f00005030070010f84404510341140042d075070540303a01c4e082c12000b4285000100500140144a05c03844c140241d154210140710305144003401020b804250980b0306850041d001e410005001d07400241d540fa02642c0d00200c41c4803040e04a041000ea1800080c0b540d261180c19410241055030b80d8000c1d41681015401d09108401900130561605522450181000b42520030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 38709069 1250 38707819 38707829
    0xa0b150c010b180105060d0906090b04020f01030501060e010c050f0105070e13060506091e091f060201020c0703060e030d050109050a060501020309090a18050303090a060e12070b040f020418020109 86
    0x40311811062641c3d624003450642e00107880f0305441b8280c4a0144010f011840d4010f410b240c50601d0720414000e44a05081c1301f2402030700d6061400000000450459009108080000e075103018201e8844d8842c841c4003501900400c11034a4581d400e140c038600b124410b90709100030604085000005040c40c03141401e007500382c0c0c1c20400105240401054441c40740700d13509807003050385100030040998604240c80b00d80c070f0003400c0030b2001d290480400720726840c007000305108080311520000784248140210b64a484203a40a8000f0510310381c0c8410107000c0380811410180420f2007904d490700e490740b040314000d20070250045824104844d002c0c085420070f030009411034004019014880e1500307507465400201386200001d120a0600304c401021440b0352001380303103000000600124078000101b12100c140210001c01006c518420120340e141e000b1100c41b0039054041c40f003540898041d8100c90307070040c00345240140c098203990006044800041000132000c0405d00c620055503880041e4901a00d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 38710319 1250 38709069 38709079
    0x60806010909060f1406120f04030c05150f061e0607060908031303031a03030307111908070b0f0106020a03030e0106090e030c070e060d020f0409020d0302030c0111090d0305030a0b150c010b 83
    0x9000060041c00354008261034440c501c0c48c0089001c0511410502c10a00e401400340c2da90701d6482e42844603242419034a250f10242100081030301440c1180105082009410150b860104503c0520403a500159000e80c0d29a60760000724000c24140d1000354490b004803981007810407450f107070280885401792443c420030024600100c000e0345002081741c0e08610a070905d0713a03400c1e09000c921407070007000600c090b102c490041c034500100700030600940081442404983c409640750003116008020911404005900140380074011a000e540460303500000c0c0d0001144250b00c1e1040f660035652004e0700e03109640e000290030351000c2000c2c80800043c005c2c0409a44650601348000f4441c2ca014000280c441d002200340c91140790344079070102107199030140807800f00b11580c0c140651a07410900c0d000042d94203007404110390a21071001c07501a018003c2c09000e0b014400c0d03d044880340c10040c50b8020256641e15001180c0c1da0390311080c2c0300c0240078944503541d60340c00518035080d40c178001d14184c052 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 38711569 1250 38710319 38710327
    0xe0a3203040b090d14010c050904110a020312070207050307061106070305100504180516030506010807060507150b0d0803070e0303030112020607170705030a080f0709060806010909060f1406 83
    0x40400707000c50300c243c01d01300c2d01c48841510324248641d08640508590007558030340f04079003444a800002174a1500760454040141e09002e04041c03078036200d88000c07500144c00c20000c109411204d09103458000381c0318030480701d045442d0b40c046880c000141d0451800f050410039032250400742084180e52042c40e03880c013070046003058060400a2201409854413a03a21503035070b054404200c00300c680049403c03404448c1c850405441e070500e840c409020588841c06900000f10f5005c00c0042c220b412980307266241440d003801034803208025030418080c510707034944a011910f0240d40b10410244103c0c02044031940c1e07424164400f42c5030414203201c0d41d00030340042c030040003114004a407095020740c060362010b985504911700f03030704c02c4841d89603207840b10540400c014040c0600003019003910801078407072080f02d8640783d900b0b40800b0b0007120301c40300241d08010f0904ca128810140d2642044040c1007500e1001e469000310010b43c0c80f290450064205444010440c0305070200f0303941200103094562501d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 38712819 1250 38711569 38711579
    0x6040509030a09170109060f0504030e01020703031209020a08030a110c030d020c0427030203040303090b0909040f29040606050105030405030316020a06020d09030806010305010b07060e0a320304 85
    0xd14044d01c80c080740210380c0e010300c11072041c0a41010400941c08079040010b0741842c4d691000405007610203400085100c220345046500000e151800e40740c15813941140302440322440409031000e00c80490300b00c07040c44000505810f0401c054802c1440340e440e03080c0402d070703401c2c0c04c146400300750f0644074480c2d0f000460902900c1d1b0045690031115406890100e610f041840c0c11800f552603c2d0810f12007034403044920720901d680840a40305503482035031400f140715500e03102440103002c0c088600c1e600660140204001480032600218000e105e64011581d11410400c01c0c0e5101c3c5420941c9100044407100b08001c00140e803140c90081e00302402c00350708600f000e443d266505d0000034500300002c00d8400c1c4d111145070003080085001544107a06650fa40a07190801c00075094855048001c07492480c0400d00c150301038051141625910482242042aa0b8403204080e1142c1904240540511174180c4041904036400408031b00802829140084940c0e0350b248141c0e41000100c01642c00900c42448 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 38714069 1250 38712819 38712827
    0x1506031a041a06070f0c030c0305060106080c030106050901020a0b010603090501150602030726030a0609051602031804020d020304050604050f0a021c0201050904060e06100c0b0a150e0109020306040509030a 90
    0x2090441565144e0b107401d05131510000100c90f811010b8038100038003100200300034120f079450041c4c1e445081030b500300f0703641c13100d068528000983c0c007103010080910042c030145100788042c010308201441103c40e1040927031107940b2000c49c20b8108400007521040c0c003800344442401340c0f400000b00381001c0d0a200e072030484025203130300a2200050071903601c0c002c14002d84850308504d50007241c40b920030380e81e43d0524603aa04010142d0b44034075036045d424400017030034403810004072142d8400e01e500510f02d040748480c00b284018003050240b5a1160f800d10000446209910107148100c3c456001081182001e0404034503102d1000000c01490b404070000f500182c8448290303c0011400082980d01c07001d16100681c2e145c01104107541c1c01910341200003030300c581ca64180c00d01030300c010341c0c241101c00200c50044412100003200a0101c20310003010402c00c6220340d009000500488100e070000755100d46584128503001c3e031146c0706464001c001c0c00781601d4288245034020b14444011490010b0140c0090 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 38715319 1250 38714069 38714111
    0x1701060506070f030806150a0206061201090209010b03090111070c140306070504030b040f050307050c01030614011d03010615050403050613020d020904140304030c0e010506030403120b041506031a04 87
    0x181081711035804601551078031070f41d411040851813140c54482c1181c20303000f9540c100841d42c071845504a400c07042e044000c184240b82c0c641f90064081c40681c2c1c284000446c89078030160001c0c070300d5940c1c0d43e00b500c0c2c41c1e0f4140014041c0c480c807920202090600d0003410b40c101c0d004825130203110b0b030414418002c035950170404840407a90710a00640315070f59103042c100c0b5038050324000071341240030004201041007c0451030b410018800d032001c00009498960101e07490740d0203892280810129800c0760120783d41000d0071603001c203008001042a6407201801e40310326881081490200b00085024010000103100840e4415814000d914004140ea0005035021062240c064020074000300403a090004202a000b004009001100e9840303560b850f150002061503c105640040000004a0075140800c200c03805150141d407505a900300c4011000c00402d081001e01c1e038002c2c0e0361041c00002ca9203004030007000300602d4500107400c98021050082d00150400340a01c120316081c10103d90b000400448 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 38716569 1250 38715319 38715323
    0xb030c0a030b030705060a03020c01050c030705070b220b040b06010c0c150c021908190b2202102f06070e06040f08010615050a0207030807080706061701060506070f 72
    0x414102002d0740070070704051a81d0007041c0c0020f1300240f810050b0350160010100e442102e0002c00c280d41e6903013007200da180800c1e247c4d100058010007400c3c01140321744000a400c9000d940301c41e03c0f04144a00c40c501c400100f0b44003151540c00c0031080005008022030000d510031400e007020307101c0b0b041a030b417000f075441c01c28001c01701c821664030300300000e081c418203a10841c0d50b4060302681041c4900e0301d9000340c44145101d162902c1c4140d031011559622074a502000055000e014028161101443e00440da0f0441c0a0b0700c020320142059500580e889040c2004460b00c0354817508950414140300803e80840d0526072400d24030368482c061504580050071542c480380503d40307513660311015000600d00d4465680300e140f0964000c00046602c10040d44440102c80007024078a80400c0c03112000e84150103840c001c440560042c3c80c0c100301040034080108030390b900c28840a4500503881d6544030850f4100d41146140c06040354003140c82400910444028100803294035084c03030150359032083d00f50001180 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 38717819 1250 38716569 38716571
    0x40308160e030706050a0e040e011a0301140a02073e031903030b0f040f020406020d1b020904020d020603040605010f060201140105040b0102010e0d02160504050105060909070e0a030302070e010b030c0a03 89
    0x820034507141f01f900590140b14004006100201101e0348090207480c00c2d0340c0080612006004c440c1052805215811b4207540e40c4058015991783c244a220003500406000d88012640700d101c01c1445c88403e9807040f0110250f854801801c0607501020030159480e607219000750300600d002d03103e4035010b90040c4142c590529012600241980105036003404125a09420500741040f902103900b9580103001620203aa0885294460b200d40440c6d4a03207104c5440d00c0c4034402c0300a24000350819004450b4804e00140c00c515540f170107903011030066441290300341d40b0241e41c0c038010300c0300e6020044100d00420f0244028040c1c19030500401032030410620903203100d60b603110341000043c0d00039045523280c1031040c01550803003070300703280081c0d2500b40c100c41e0f400a100c0c1c107d90200b650326081c8101c1d41aa01c0141895040000703040038040700882c09001e01083c0030410807030440c140e85074100140a10720035405000f565241a5a41403114010307000610314010900c20058044051ba05856521810303142c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 38719069 1250 38717819 38717827
    0x5011212020f12040e0f0709060e03010204170607020c010201020c0c010315030f1203050a11040b07210c06050603190206070f0804060503012409140315040308160e03070605 76
    0x14040c0d14040305110482414003400541e003c401c41802c014004542c6095000181a614584540502d039401c46440d4081406d0b204c041c04902d12513450074003000b501900062134151900741301030f0021441c45910019900220401c00c05030341c14130000c140464203000035424010800452078459101131081c9041558030052084050350144408000b19040902103940d24050b040004082c88000d0b400c6002c07a04000124054260380e1003541c484d41c0c402d11000f030405092605c604517651082c0000d5aa1182d00c3d04028902050400e42515401c0b6036100c038404032080e03180100695900401c614400d4000d038446980001241e0b90b89550326604503000b5903201d069240550048248081c0604403000114001c1038485d0000e000314141c0344400c84c8480d6244142c40400320911b45004030800081d072002e010402e0303000e030032059415014000c043d0380e1030000a40001061038001c031001e03000181200180904082200a03004d40301c03e10b441d04000081e21382004c00c2da90081c6110303a00c10060002 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 38720319 1250 38719069 38719103
    0xd0b0102030f0d1506091a031812030a060b03060607030507030c0b0106030b011704030e040c0306120606050117070509060d020403020306040b0a051008121608071a0604050112 77
    0x12048416203082c1c0c102668480f108100301800604500c04004015414420081081402041480111074904194000d0455224510200f64001800601c041d101101c81c0303074074a120a0084261180380b0384544d94880c07a103018031500755285a801850320890070010f003c0079848a0003154800d41d018103000e40e07560968601110700502d03901d0060321000b5040000310b015580340d04000b40c1600d00f685c0d0003141010040c9201c40204054400501040b61000e80c240389080035004454031469038140020901e0751541d0441c0001c8030104c048645d1696a04180040d68015041c2d0301c1103004c0c401080c0c098074100780040c0c054418019003d20a52001c210070301429074580441d00607583c00f400740d8071035081070701e494a44070100360b8070400d003581000000350700008000c10342800c54200800410781882c41d000c45165560248038512441c840051035400410b40c001e000346040d5202d200380c2c00d0071a00c070084141c0e1044014003070703070b104605000040005a64510310031050541040480540707400d17003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 38721569 1250 38720319 38720323
    0x903050405060304080d1a09040303051506040f09050c120a0504060f0e0a05010b060c0d0503060604150c12090b0406080a090c0b0a0206090f1519020304140d0f050d0b0102 75
    0x3a41c41035034401000800c1008005000c1e024101c08a0780c92024040407800b00100c1d01e02d800d01203c4190010080d0000402183c0f098101c950407001d50344803030a403c903518012803105c0c5d02035005443c1068500ac0100a4100c00307106296001c0c02d2040302d1410249107541c54542803201070a442c1401e92601c1c04a414080684d02c9003c0c80100070340d0401040191003103103a21841c4458060302d680d4a0550400203504150f000c5a0604000b10b01510490b0348000d81511260400b40480d81c00410620011600030b9000307641000c1c8140944902401d03c0300b600c0c014000e10005070000c0c042018240c07040200081034001d072019580d02e0b05001c03540d6039030500c1c0d00005000881c0d025003814075141000682ea04010700810799502c8036805c1c0d81a5640c2c0400082da110030341b12504605a11400e94494944401c07884960080c02c203401d4100ba43c00104502c00c240d81040c0d40c103844e520a01031116001e080100101c000c1714005060a10192200c40c0c40540540117402d8001d032820f071615400e82d00c0c1ea1003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 38722819 1250 38721569 38721577
    0x7080c01060f03061a0405010506040501050c101508070b0403150b0310051906050909030706020f0c0f03040603050702211602060304060f140408030411010c0b0a0903020106050604030510090305 85
    0x140c0120701c08500d6513400d21202078031420746090f280b4018010fa403952030070140589810fa440c0507000ca0b00e064548001103a0b56407142c290948170b40182c56006981892502a5910784c0c0b61010100c0042400d02140d04c0c10404580c0c0700d000300d884100402c000049442d5401c100c083c030310000018403c3e1150001c00e061803000c40b51076a1903450001000b01e400c08002c200050154041c1003000000d403550240002110151110030040c1d00c2481044005121500140103559545462a0401c444242480e10305a008481d101e600c5c0c20104003840440d40c980700b0b4590200c0184000c219281c22000d0184c1e9141c28194041301c030080004078244039650300444200d5040d80500b03450381da4070345403c081b4003c2c002c0e641d1200e0345a00700f45011001204c24094140140d801c1244946151601d0ba075544818144064850500414048202c00b0808440c901403080d9100400840c1000e02e03854028210344503600110310401c1e040c001030010403070000e032070340100029000000b030a41d86402c090b60316002e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 38724069 1250 38722819 38722829
    0x201140f030a0e0d0903080409020d0209090901050f131a060105041a0306041409070e0402031203011e0e0112080d020903060108100f02040e0604020d0e060702031e0a0507080c0106 79
    0x2030000103001c61491241e0000d420319107030342e080d150181e507156000c4401881603c00030b400d003c03040c401400446513590041007010840030005140182c80c2c004640c0c13a038400c0b20b40080c240d54039020055000b420048407035104a4900c84143d1b0703031002e50303034000c0104066050503030440c45900001d90264050011035000d44000c103010303070a8084403114134401d54001c40b82c4600580c24443c001107010000140076003d504040f0141031342d20304000100d000186c00a00c182c1e414410782e0070902200040c400254060003428026042d01c10107610340d6809006030780d110f11030110720700f80100030134001c0880103070300d09600c00341c01c5a40d08a070782c28000180c0110307159558140110800012060380c0090840000e0b40c12200070b02c010301032001030307508034021131040d03400c045084c03000645586441e038001c02503000b00ca000004c185a801c039903180703007107800c44030704002da0b000090320741002c450545a40942050081d11914000681000914500500c1c0c0700070000e200209d01e038070352108203420941c0600 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 38725319 1250 38724069 38724097
    0x1050c160f0312150303110a030509060f120a0c1d030601050f030102070501050106020a0b1e070c03030e070e01320402130e090a06050a0509070302010e0303070b01291204020114 78
    0x240207841e4802400445d00c0b0450103c0c80382c10a012198001280b0046c00716019218181807042510601040d90710460f40c0d01c14120007007000307082080012400740d0080c00311100001d18402581c1c80034080e881144044000d03114940d492030003030342e000030b070007415242d0981d100307150385c0c100d82d0200f4068041e00717200520070750030500085240e43d40000c45005082c00740d5090100c83c0c840c46444130580000340401d900702c1c00c1002c00540300c3c030300030701d8a00e1900d8032a00d000510f84400e41125410460b554012440d0002402d004104c0d0050f03d103014034400c200000c41d0500c2140400c1e034049084251107505004d2500400c118640002040e081c0c0010100c05011824510705051080e454030f01c0d001c0c1c2140d0395403402000c24040b00e594403407107200b07800d1000140060303801c540040d00d00c00c1d0212041076140c8020821500001c6290300901d000b41252020f645c420400503d11902e60003400d12030600c00e070810f001143c10016440c140540294080c06d01d0100c00200220240c850310641281034012 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 38726569 1250 38725319 38725331
    0x307030f020c1f06081219090e07050703170f0403030b030309010e0d02030f0d120f060e24030a03031d01021213030c06091514010503030708220e070201050c160f0312 73
    0x2010400030580c00200c1c0c7c1c4d64032040030080034180e45c003030340c03a0041e64402c03041c40000401e414000e2008107000d5020342030014000022411448010008417800055078000c181400f00b0184c050007004000300c4120082c5080500820000f0f090400749000c091082007080030420664900b4810380901f080e801042d51010080715074041c00d01c060a1250348402807408410f403400042c1441820240e48134625100e60390b403200c5140c00a007004004078400031001c100e4403c2d0b11070740c0402001c084c0501c2070324080703403207181d0340d2881940c005035814403100381e40100030711941c11342110303510350b0b00084403007651008024130b040440d181221a00f00402280ca002208418888680a04405070022400c1800341c90640f09414244410a11910350554003d0000d91b0004051201400d880e1203040b00014004500c0b0b046c00395101107540c4888507005208082c01843c40d428011264410704010510780780c48038500313050311107460180d1b02a10300c4c0b4801c525502003521850802d030314108058410b20075 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 38727819 1250 38726569 38726593
    0x20409050702031201150804020f180907030c080d08010b0d020904020304081206040902010228020603100614090303040501050c1906051806060f0f0d080c01020307030f020c1f0608 79
    0x142e0303030000941c480701d0f0b4130702d800000d20000711743d403030582050865440340b440b6141c55081c041554042986264040d011503005084447c4001c0c0441c07103800c400b00201001e0385541016044d88086803c89401ca8010060109610760400c000a046401c0041d40b140d84070320107183c01009000e9a0207055100f4000003d201c20b21803000080c0c0004600c4140e1100c06499080c00c02044640701100240503800612142100c1603038250702d070129503103102e40d909045c0702d00d50014000d40d02c206c941c2e480c1025101014003500754810141041d1108940c0ea4070324103280000061303944d001d18032400e4108100090b00c82640c0390240101010150814080201d90901e4940803000d40303001c80e001c04074400a0140780411603000500d03940500c10280aa04000d030b032000505c500c0781400004140c010398901a4040003d00c02d20043c103041d2101400180c0380d040c010f000070151400038404041450040c030281d1003158012901c441c00060007107a803808c090030304103004040e1140f5170041006001c0c0c0400604 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 38729069 1250 38727819 38727823
    0x30906010e1b0315120a020102071809050a061413030926010e011a1c080c030712020a0b0606040323010e010606031a060301030c060305070219030f08060303031513020409050702 78
    0x110200101c441751110411309241a0740c07061103040203401603000f10030030851410f0405103e04d815512210100d8058a6900c500d89001203901080301c0f150795490f00400500d00030f107400c941040280b00041c01d603615640f00100754a07814016020755110514403400c0090a607818502c0004801c1c00a1084103004280345000300f4101c4031805140768124007079800c1d4a00001c0c4401c1e440320407190110f285209850302d03801500510901800c0d480f040040c04081400c42c9051181e200c1c45074000d00d41d062540c40c100c3c01402c4090505030054106002c1030001600c0e91201d0104158900c42c40c954550240440302c3c09090440081d88055280c03503004075900b90b142d0444500c94101007200d0f2a80142c104c14010303948404d04c4042c1ca440e0200006000051185c2c2100340c20000d0b0303104440c1c106c8506004804584440d240440c0400d81e0403040351901600204400c0d07101d00220060350445c545180143c000e41c04a00c082c1e0301c100d50282d860900030540394140c0d070190005000c100024900000065 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 38730319 1250 38729069 38729101
    0x13060903050c070e06060f0705071e080c03011404060509010908040b0d060e0421020304030206040e070e0f030309010e01020f100e0f01110904050a18060c14030906010e1b03 76
    0xb4503a0140340404035513405040300242c0201405005203240041d035045102c1645c00ca4001182ca6025001000a90f4034aa02802080d100103060190000307141005461811071507490007070199040c04102907070311b0f580e9569036074015001a4046403a5441da030415004100d1180300901c1d10402140102d02d101c00100030308100e8500e44010454107071108014005040c0455000f41100c1ca0800001496004020328500755071460045a00303040d208c0e40014103a80080e0171a0621000103001c0040141d4090b0800300c00c51015208000c00f110200c01007a201e11a0b246803505010701a00c4005080e4820080046440c42d24816501054240308118000e400e03000800c00d03031449098850101084107104d01071030341c1285103000c0d00d42031410081c072004c2c190050503184c1180e901d10700c0c408a80120900c0803c49032080c107001901824244000d8425000048818603807070050040100c0101c000a03098151900101040d425a42e80180c031381034618114610f009264020080c806000b001d00072035 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 38731569 1250 38730319 38730337
    0x40903030e0c010801151107150c15090c03060b010504030519110102120d0b04020d090c0f0b07080d05060f030304080c03070b0a020c011805040c0c020406050901060212031306090305 80
    0x10301c1e08000b1980046070b8403030080c09401501c04148107100c0c04e1900500880243c01010003d440c00d60b0703a950580c0700a440c1504030040801e00000081c0200480c1d402c8100500f108042e04100c065142d0b251603488001c18000242032650360012010700340c0c007403c251002940c5c0002120240c0000403241e0040158901c012240b9007011821880190300101e90b8071040741d11881d0080c205204050060701408014161940043e820040034030141400d0094806003406a600882814a00301c0700d070540d01e00359400310020701000c0c0024070000b0148811282510003082e80880c0791f4650000080981890411055241c8000100020000b5003c038102c54030071001c0f01618801580c1d100e100c4032a1080282c0e900041e0040c0c803d0000039800340d492101c14040000c45103143c43d480b00003260880d0040f032841008500c04036805011440c0c6405807402404c03042e20b81d82000e526081c0065690004209440302e90380000c40040c0b08081d50440c00100c441e00304000784043d40160a024190780d10400e0301c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 38732819 1250 38731569 38731573
    0xc0e030d02010501120b070e10031415010c03050315040204180e0a020a06030c110318091303080402010507080c03041508060d0c050f03010e150106090906080a0305090609040903030e 80
    0x300e42503600620500e8100d8107928040c85075444075582d08980c080c40140040203015201441c0078464880d168903024040e0b1586000483e480b440055000e09038008003035858200340805a00c046980c41049040d10710303031504000b0348a44900d001d030b0144d0a032225040e600584041000219640840b9520086182d519410014218440841c5445800031031010750001d9070305c04108415442603002d002000c0c0d0502d01600c112901600107400e50744030340c104e82059480f40e4290406481c10421141d088580051400b4070f940107903601610104004001a062200100d106402e2051107405ca079081c2c201c00c01500d941c0c58035442c0103c90304107030b0030b4000c00080105000481c18201421200080c0381c0000c01800311501e08004c10182100c056400781e055500c40603c0e4420715000c106050340582203040052823503060020081455107240c0c0021451414500d04126411022a09001e8142c052404594405180c0c001c41c04601c01e8143d416005803600d00c0d44828180e155014499111007401 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 38734069 1250 38732819 38732833
    0x120903021f02040501080606030408070f0308010603060b0c060106030c050c0109080403060605040207170a0e03060103060c141201090c03020405060a020624030714030a050604050c090705180f03010204090c0e03 92
    0x21000c8101e0190340503081c01b190f0190041003083c034140e0091035119114510a602d0076013580e82e080782c404101c19084010950280040c0401a0103004440180c088140f4150030100d102e40040e640304c0c0c040c403603041410740ea14090641c00e44a00c0c00c95134140704101c004d00007402d45140403100e41d4041c2c802a90118601800488c080c070307090080351441c541201c19521840d102c1c410035403c1c0d40c86a480781c0b00703201811001000390b860610016009500404000800c5040001c014101040707040b10001c10711803c01128030b05004d4800d4035410b554030b4443c00110807054a400398024442d60300701d146d0242000c07402c0340909500040c4140f10703005c4180e14a04030a000444944044902404558503410152045c4003c1080a450790742c8010010110b0300c240016880b45070500b04192800d456503002140700640904102c640d4035000300940c1342c0640780411000100707084040c1e40d0080c03849244407101862140d9025015036001c0d2000b0401001041c00c40100901410340c0041d4007402805146 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 38735319 1250 38734069 38734123
    0x60603020301120b0c1b010603050f0d0503011208040b0d02031b040b0403080d1401060804050c030607081603060315020c01230402060f0403050615030f060105010504051012090302 79
    0x10090301d049030300401c440c4080b804555120340c0c100031300034260002e00f9070520030f042e0504041c2c5072180c610011a000001c3ca1070171824a9400c01da90007c0c0b1070600e40c4004c2024441c02d41c408112070441d0360a40f10410205124135011340c082c45030b90f000802d0721344003240c0c1081e440c5c1d8650045014542e20307541d21400082c41401700040b17000354070804011400038441040410041402003004039814040014a641100c0c5041c60100d400c0cac0041c00010340c1203041004104003044110342c045000c800030180340c41c19080040801200034041204500d40c1c0040c118101d0090f04440c014650040d030204030031004032403981c002e42141c920040a5030804040481c070340c0c02010000341c0c0c032070701c8641059030740d59640910256030321000e49030b40c409104000000100f502800f02501072003404503588411490341d0b0030145000782d0301500308072036000500104403981c0c1200481d000c5801c195030170303880b81054820170385220014608940308103082400e01c8042582c0413a00340070707481c44a403030210305031511 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 38736569 1250 38735319 38735321
    0x5010e0904050615030102190207050109060302030112030c050a0b010305010c0e060f030a0203090304030b0103080306010806030f0c0405060102210c06090d1209061803110c04110f09040e030f040306060603 90
    0x10759002d0010380104000c501c0516224500c1020400060009480e003803407403480143d5500074261450058128500501256034003c0d02c8000800180c5025810340d41049846440500d040800409002019010b0000c011007800f040c1e08454005610f590039603035030f0030001c1c080e05480680c04002050344202111502d001c100b0785003108400c0326600c8c03e40e9110300004000358030182081c641484240000000540d0b01d0401e50701841c480d2400715220b00b0180e0000d8007040e006088144039070041842c12001e000c0c0041c020400700e600b150301194903101e00d40140e080c03081020030580c0742110745129403241090080104201c000c04401c4548668510840704c1d11401d00341c0e5580d000500302d0201104a449540200d90914094400011001a08051000c543c042e100044020684610808030b21107070a000d0301e104c24100750350074048820340d0b242030240d40c07003400442e00301c8000216203c241611030b0340c80301d0b40000103c400c8a40d5040c44026252164100c0d100071681c00c0d0800c1d1020803c2440307 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 38737819 1250 38736569 38736571
    0xf0c030f18110109030f0311060c070818012303180a03080c03040305040e07020a03090806130303020705010f060b03040b01140a060f022e0501120c1205030c01020d0605010e09 77
    0x7a107014440e020a06560b00c010402200101d2410031454000102c08914038811110300980b281c0c50b00190a0b0350043d599051400040c601c502848007842400c02080c00e04c7c04035411483c9050b610480e040b0001c0c0140c40820f0207809a00d80c241a001c1404000001030004600a210020070b0043c041424613801d55103100c026070003000030b00f20401050404c00310030050360300140310b0709015040131b45800482024000880380400141e200c445400140340d081444a405041038001910051810207607109003c46185001020907500050990902900790300c0a040074007003a005210b401c0c2e0f0740c510341d02c164100303a03401e8803080610b400005101c568031800c00125900500765150031890304034185d410821027104541903024400444841c101c2c16040d00c80d0700510640c0811034181e240039220100d500580051072040b042801036404100c11880c040d046400c0d0810508650b00c4514045027036001d01c3c4681d4201d9070020039004043c1d85142c0068044d501c080c0e94015480e1246400c210748524 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 38739069 1250 38737819 38737841
    0x6060f040302090403020309040213150801030b0c0c070302040603080301030201120e06010501120b0904080c1e0a02041104031a01050906010c030c0605101d22031b0c03060f0c030f 79
    0x1404000c10001401e140d591a50700500070300640b414842d401001c10140d0b0301c6280d80c50101c104283c4140704030790901e109166840c0d000e20740040150306540d540c01d00319401901d50914450041400d4805000411070740001c3e5034060710074054142e5900e8140e001d6002030104030b010078042154042c0d1500b0798400d12002e032850360300a101d02d9103858015150f075003100b0400c1640f140c40300110411340d00c91111075030107503203d1110b0941d0b5102c298150b9040001e01c130a00032a0b00c0b402c2c009180381c05000201d54000540449001401c5d1444030345198052250303620040c000719800d412880d00c4030340b4000283c1250010346e94040d6a6440c4d100449004a03d17240003000314021410150109080364009540b00b18540212910a52240c0785545055445140c092601b00d0740320400180c0005044078003c01501442d090080000381d5a000e80b0000821109000101c170f00041d000034455505900d40045801030410441c155440c2c80340d5025154030890a07012909082e042032b1005170610030001c103c8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 38740319 1250 38739069 38739097
    0x150a0206011a09040915050403090509100305070308030a02070b010609030c0b04051003050c040503030d05190c080414011104140108070206010b0403020d15050906160516060b04110a02150606 84
    0x889a141000010310050301c080c0c80f6011406041c18028095101c4e55008d94000d0304c2c0e0b100520b180c441000310506c0e00401d880010044807800301f000032000682c1c00280c3e0350100c0481d881e5580c120013903000b400340c500043e140c141c0c0c0c0e1000260450b008244401600e010700c00c20f03007580342c94080d981d841d8802c0e0300c034954220b805e44c41242d150522940c01180c0041c24100200d141a035684c000900c2d58204140a07103441c1d0380c3d481445010425580e0803a10340300355002c2440f18600d075600103040c1c024014006014660b002000d200140402c1d0b00c903012141c003c02d0516201c03030f01e40d2101c1407404c00c22140a80480d90020100d8143ea0002554504803644d80c8044c1d4541415030342884004074100c0340489a1213003900001000b00268090f00d071090003a04001c01d82803904d900ca00034010458a0180b05200d030402a480c510380c40070a50001c40c680292000c104d074109400130074010946040c20300c1005002141c0b00b403403940d0201e00710004501c864102d1446803503d00070451140f060301c07101c41e00c030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 38741569 1250 38740319 38740327
    0x160b010e1b0f0904140a0605040f050c0301050d0309050301050103030e040e0c060d0207030c020a03110a1a090409030c0209040302030a09050306010b09010c0c0905010e061507030c110609150a0206011a 88
    0x44501e000080c0f1040001a1000c101300c0d08120309941c508030292120120b40d42c50320000d10003030400d845080d207448190380342030156084c41d498074040741c8418003400b0302400c946070440080c1805080c402e0010705000d07008200c6036940b428001c140e012190242442107040c00e401d16140540042c0640300070b0b000404003842d0280445c0713213038000e5218441c11014085141d481e000503a50341c04000000303601a499100b03842e051242080001c642c113401403181100040007071030321020804140c0f18030301070540b00007403540e00505095400154075a0003e500c000c044003040304259020000c0d043c0c2c1003298441c80203440d1248100354850304240203da400c004140480102e40d0f204d48034086e030071401004038000c05522409400107075002604104c6414445506104242c01c0800643c1c0c420001c881700c003824919103640c000c1c02d14000d801c010340000ca4150550006a5410040390132601004040300f40319441d4444a070b400341c00a045500c0980129000007507484c10101a03100a106a107214502d0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 38742819 1250 38741569 38741587
    0x1050c0c0f04090611040603060e1308070f020301022b0905030d02072604210201080a0510090207030e0a08070302090a0c050403150504150e030a1103160b010e1b 71
    0xa45510040440e070050f203e03003419010804a02c204010f130504c804000340c4d01d5050074009030940e02d585d44401c0568064500f080302e0541115a0140c0b4190701c02d000641d280d1090030700290400f0f0700f01000c1c0d8954400202403507a0205425041d0018420036100100b0850259003642105c641d801c01a200303400c200814281081190700400d000703071181d40c44080c0c141d00842d080e84100c0c60040020354107480000e0601540d8003240c0c001c58040013403060105410700e0ad41c0020b105800c05010f4410031a151008143c1140010600300c01404140701c0840d15810f507410010001e4811041d0580598803491000c20107450101c0d4040a494010303110003103d441d03040c1a1700003403565103d0319080040030b110200005041d043c0d200003c11000b0000f042500742414001888104076202d820014a080f200c01241c0202000b90b0b103c0710030780c1c2070100c4038444006c1c02c07505522480c0c042840900d1084502010040613003900c9042c0c4035500a0950aa40c03000a0150241700c4886603040400301030001c842 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 38744069 1250 38742819 38742829
    0x30e06040501051b03040f0602060103061109100e040e030a0314100305030901050a030615050a080702010510060c06060f030c2102010c062301180b04060f06050f120406020403030e01050c0c 83
    0x204c01c6038680201e0b032134141c0e140d0301495585119000200180c000100400a100c1c0074040c80090300d042841441c0340200110000721808000410541805500444840d99980740d0b4405284410b180701526524222410020b004040c001c03c011620b201c5c82010801d11110b00340c0d00010380354044000c500d46442c00c001034813a900b00302130344400c154a4007808a107111200512049002203510b40f103850b500c0e4650040d202000040034030303086a2400c3d0420804110030850001200c03454180500100d00f541043c0c400703000b85402103c0c6001242c1e100004000c1c002d040c003012224120b0400030794400780210304000241040e0042d000454001c11040450000ea02080e40d840f0303840c80c58040e180412a182d5034001d42684941c01400915991840c01c2e405c6010740490004201c0d01089014103000f18003c0001c110b0141c803080010105030408088880c4081300e1030300350034111244491800c0d1906c44082d504c28041200000e01707100f29000c0c0c5500440545060031200c8002c0c012151004043c06 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 38745319 1250 38744069 38744107
    0xe0405030703030908042c01090507020a020909070f03050705030111070b061e03010f0e010c0203040b0f1e040306090309060e09071101110c070305070b0309061305030d0216030e0604050105 83
    0x901d01c917201300710008041d03082c00246014030440410340c0d040401c0c6025841c200b610160702002c20036092a0810620540c041840d0749038650450709014030380c4030004490710b892800c0e045400e40302030250011080c0000050101304840040740248508600e0048032200c2c2c3c0116040140445103420204043e803805206a04d4603000c0c0c007031246081680d030800a070075a1300e1444032038141c5580f42d054000b003100c02c1c081c00a0324400c3c0d00086184c1072408410313140e644030716052191403000202e010100d0402516181d07100003090382145450f80d03200e0038000d005014044048012403142880041d00c20300806011074003d00c000d280d107406030780b021030669540c440e00e405401103540c0c038105090115403a80c09000e0b464840e60040000a0035454880d1420150741c001c10508a0140200034001c500080c0c401e0707000301c145041602c1100e0602d8142d1450248011000e440d070300108502546161161001c00502c0c0656681010080e1800038000c0303910440c0200b50000f18200a10140c109040302c640e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 38746569 1250 38745319 38745323
    0xc0f060905130608030d021804050c07060b0604080c0402030604140c220501090902090f120714040e07030236070806040b0907030908210105031018110301021b0c03070e04050307030309 81
    0x2304032402204000181190b40450710030702101c4005c1806c00c00c1c0030755807190001465095801a133820f007020100c0355500c10400c3c150344280d40000c002941ca44540c1c0040011144a003180000d03804e040000280366042000324200c01050041e80c5203400082c00c1d581c204803101270311451041420244030318040d5101403046a042095080410361030b40b2008020003400480402916400b414081261010107101502920490500c6861020980003186c4d440880e40e04440b00291a2b00a81c00c0540e83c00312404010b02c0070b121016805511501882010311541c02d0383c0c0e5035401c0b07540707510800007200c0e0f0031000306411690300e00004e59040e001c0d51000c40020b0007100503900f0881c0742c100e10194850074519100c00c0342c5091004000d2400d00300641076540503542c50a11800001202014048020312805030039400f200480b1011500c082d4111411010304139038103452203810802469840301c205403c24000e11690300c00090811848007010f01a079481405185080318a03202100603002060003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 38747819 1250 38746569 38746597
    0xc020d02121f02040f0e060622180609060803030f012304021b010c09080a0303050c07080c01140601090b0301090c030605060403030807080609040f02010c0c0f060905130608030d02 79
    0x500d0b40c181c450410b0045903a00002805a919810030403080c08150071944a07409164043c0306119855540c2e1054a0702d80d00c0d5100910700c1d0318140ca030f1803501c69000b0f81c00455070545641034031038220401d030891410340b8540501031050035a211360b800d41e00e200884031014101c2d8607000500016013140d40c49810f0300030a030600800303001e00c03a000500326803183c0751041c1e10190805042d008401c00780a207031407180c203a0a004c04482c1c40d12941c4d0303849083c0303843c00508240d074031000036010401c03150923039050541002c40103880d0b190344e00e00503008101c008080c100c9101d60600103421036103d420b420090326141c1c45051306507440e00c003400026020b03207000002810b807101c1c00031640da01e13444060700055009507156242030400001c0900841005041540501080010000402c4880d0100600c1d03643c280f03400d6610b6211803c1c803141881050b04120a4211106c1c00000d0719a80600c140c000c5d82c0707040760700c40c0446d044c43d90100b080314902d00c24801c2030342050110190540056018041102d20050 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 38749069 1250 38747819 38747833
    0x209041a06121f08070e0603010b0604060f1205010305030c070b090f011b080a05030f01060309030507021c02090a020a0e04020405010c2306011203030c030c080c0d090506090307030f0c020d0212 85
    0x600f2901d100b03500400c203544c0c05000c2c108112800903001c1d43c1c004005400810100841c040030030940c0c85903000c0c5c44207109104042e00e035030301d108030003181c4061580441044a56100c0c40c0c0640c4952251140c20040e2240c6d21000c544d840d044d40803610ba00e10000c10040b000b0307200c48010b40f402d414008013028a0402e042458000c14160707070040082800584e40d00d556483e000350060181107041c4c002804040c60014403c000940100840f502d0f2901219085007500d02c644030301c182a90305040c025004480d60090080001658001d095030500a48075005080e00306414803089008601c50680041c128080140208100c208500380011224151000349800400300f5490014281e111100040895185205155042c402d081900c1001e00d8103202e4149600c000404a410103418007030215000101c00a031801641d10254a8681c008191401843c0c44420239499402140b001d41c0072078501035103040310701e03c0b52003090032007a4010103124102502c2d40a2044c5214113013902d22326449288 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 38750319 1250 38749069 38749111
    0x904090311030703051201060207050d0605091c020102030105041406030604080307050d020313140105040c06110c041503032a06021b1506120c0102250302060a030209041a0612 77
    0x40003c000041c003070b45649681d030568207201c4054920503401002150001182404550349120121180e10342040001c03900f80ca840b0030080c200b1003110458401c000d60b00911545050b010f40155040759401c480c108288010842c50013008181100d20603403681183e800a40000c9040e400365820040f80d00c0c00c2401c1074803c95a6100300d80c015119201081540c20101c010030120383d850560410329107000340541d081ca130380c030100101140c0c0509014400c0c08030010003084010015500c26080041c01800441180b146003084981240020340c0050303000c41043d02c100300c0300d0541c00e40142c403c0940e04940c0144d5124030000b5088603800306e900c6804440c05050290302085030780d450701400344620a0a06007402040311f910240002003a40e9000560305003190703a004564030407049030040d070b4507484680300b070701c40304107003445400c0294414008540c1c85a240e500d940a4441640280c4d010000b4542001d01e0008041b026030b00f00b54400401c10040c0c4000c90b82600154200290300340c910183e00e688 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 38751569 1250 38750319 38750323
    0x702060705060a0c030c0804020d0311030d0501090e0f0703080a05091215060901050a060c06090503030702070906140607030302130504050a020a031a030a120207080613030f03050c0904090311 84
    0x410016900e551140c2d003480550320291007040100c01ea641000c01c80359200d41809482e900f001080640700d4030310824441d0a050107056804100d200e014107483e51000e04048920042c00280600e004403132800980d0300c004200040c002820014180c020540e1a02e155100d0180d6131040c85c00c00c00704031042c04075426540380d03a40c00d0f9000907030480c0988142c4101036031560500078000c0a0600c42c1003900300400050b100c0400d100c064581501c0c0880480c6c031107080040140610710300040152000004010031240d011501d20305407000d4440600c00203944210301141d146285060310350082c0e0401403d000a0b0183c3c0c001e202e035211083e80d0440a80e0341c2c10018040f0380e01210420b001a40006a0303111066240c818680358030103207140c00c02a52950b0011a942da461100000d041103410403100d10420300800c022401011900e00300c5490b854000302e0207071113252500045011030001c810b20071040303000b4001e036449281441e5009003010341c541e0401001e01056401030b410b01c44c585504d58401101 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 38752819 1250 38751569 38751577
    0x31906050406090209091e01090b12030c060414010e10020702030a1506050a12110d02030307050109151a011e0311030f0f1308070f2901060207050102010b010e090a02070206 76
    0x8050b40c01619810050280a180030300140807168018080c0c0b10380a01f190810706080c1511805a000194100040040703401600d03000c0e8170040070711020034414500240003d42c2881a80b1851011019807400007102d8282c58035035056102641102502070524544c030381c058411140007d085810410382900c40340004248581c8515566448000c01c2c801420a888071000901d07080d41d04004220306030321043e9045106031001c2c4c0c81083c00000c043c043d55000c00c01d841203150410000c01c2895050300d01100145948140182482c1c1000c2600e50300c2110206407611458042c0c54004c40c18070807510809001c1040c10281d0140b6a66140210034102c0d03d0020b1481116050354080c0305080c01e10700b076821608010b00c40c2001c103082e80903050000d4580130a0f1000154059051804003d41c0d2400038010120483e85400c5c0d001e256192002603000007140b1360494105400381d41846854034012402d031441c00ca80e0034041040c1c500c6548140c2042c00304c140e403190305410018100010f90740002d04541c4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 38754069 1250 38752819 38752829
    0x110307080f13021e04050601020f0a0209060103060e071d0105040312110f01021204021207030c140609090f060108160e0d17070503041502031e2b060608060d08031906050406 76
    0x1c0c080c0d1a641c1c02d0625100b447e800507000d000034003054400d4202d507135841345080300090080700180c001c55500c3c5d010303421050103080c600040b06400d1901000050202103190381c001005103480000c04079950068003100d040d00d4004c1c1280c4844c461451040d40e401410000c0d001a43c4103034440352050210a2001c0c082e00d0f2046c281c00d85603410315004102c0460120400b03c072442e048002c081000580c140254422581410801407181c200c42c0b001038001d0050740460758003c552002040020070708050003610402d0242c0301c000c61500d07902c000d0000e000240d4148404500601c0c20b09d9500d103014400b075180c0030320801c0f80e1103420b040001805981d070420082181c0a91002c40d06101003003600e607480341034105910054ac100510032400303030001c04540c0485410083c0c0020381c030b9442e034030f00709208071804d00f202c080c2201c140400b00350300001c000f54400c0d0000070b100200401d15510b0205e441d41d107000e4100380c0b05c504540382e140400086410540b14820071994441d00041c0c0e03600d8500031200144 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 38755319 1250 38754069 38754109
    0x24030a060503070e0106090e070c06091208090c0303090d080403050a080301030b0c0a090303030207020102010f060608091203011508060a08060702010606090e04120807020a0606030c030303110307080f1302 90
    0x58038181c14586401c00d0b6800112076189100014420b07154464900d1040302c003010144981900d880c0e6082e1800791031071001404042c100711260303007480b05011100e452035020b0342d0740c9102c07a9181c0b1031158a54204210071685500104002c080524021480400d030074028121907160540d00d65600d481e06a8a040c102d40007000400100180441200b015a000103048ca0b024a46980003031300a0507201140002028140d0104031541964400d5001c0d41d2a8a840e8078100001e645505014004000882d40080c0510a0003001d2080140440c103907412694070403100501c80341003260644208000912550700300e015030a00281207403040200c1801082c0c20780000401904041006003400c020b9000815000b98440920002440340c1c501140340100a20b0440010f85404d10100d0078000d032010042c004a0030450083701340f1151015040032039111303403402c0010b2190301c424031220740004c80b01c01012981000010344401a0501c13429440842d1030b42c8159664070581c00541040076102607903640d1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 38756569 1250 38755319 38755331
    0x130f0e040b0705040608040308040c03200a0506040e0a050903070f060c180501170403050405030d0e100804080f03040503042409060e031b030c0a0315060e0f0624030a 73
    0x72081d00e40c901900031140d0b103000b900d4542070404c0035100f00d03c0500018204140c100009042c0242000183d003d1030f4803d100f60024250b0314203050040355070804480c031810442d000042c4510740802103e0496140c2000c1c0e500f666a8040841c0060170018150300c1c4502080000100040c0f0442404403018418403000901001c2100c0083c03200c00300b86403901c481d80c07113600d0601103aa04100d51007952030454440c03203655038644c41d0869281c06030f980150303014410401442030890f0050b10701590400207482c20fa8001000c841d04031002c002c140d5014013400f804011415014100d00300a60307000d8001c00c100d0303242981d1501c1465254a058001401298601c80000d114a6100301d11070000c080c0c51a213091240d40d46000251074495180c404450b980940960700c1e401d4030248285070300200010f140a00311940c0b420400343c00384003e18807601640c9403d1001c81c1405c0341500b00c9005213070340c00082e10f2660fa140d0500c00b000c2d202c00d412401004650280e0460051481d00540c4078100d912000700716 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 38757819 1250 38756569 38756573
    0x20304150c050406030509071212020f1e1b06030c070516030c030605090604080a0f1e090f0b130e040809090a0209040b15030a0504020d120e0901051c0602130f0e04 72
    0x1b02c1e10003400003500f90f008140c040040d918000c03083c1d0303005604102501c4031601d04c802e00b0707898081d0314026042240100b80c1c0700c8200c0362000b4041400661180d09440b054958031018a0f06420b03c1c24909500040c00d0002c941e80c03107a0031002d040701904c2035040324080255544e40500c25010355104031104002daa0042c003c0115500070b02d41c003d03450900400113410aa03894043c1c6004401090007044000c880b2081542e101e0b407610401040710780134071808800032000003080340c0340c58010700c0940e0007040400102056114211911541008000041581804804008030b20045e0095a4500092015000b01d90300c0b0000d2602802c000c80005036174a48420602c000d036014880380920950090800800010009007160786c454026840001c2d540da030b610005040021034003015100c0e030320040040860310b400140d00e5000c0380c004c441c0b040070741ea13942c1c080248080e482c0a40c0c20600c030901d001000091f00315005000030050786000d0140c00760f101c11901031501d1080d0700944a2440c150103102c2 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 38759069 1250 38757819 38757821
    0x11503110d061b1704020906060f04120b04140f07051306080d090302100323040203011107050106050a050f010c030f030609180b0105010905030303010315110d050601090504051603020304150c05040603 88
    0x7424480401ea4201d03d8140c00003000000d000340b0b403600030f540c0050088a0003040d501214045d00007403901d03041400c001d037000c17414000d003242e0480704d5880d2400101722001000880c03042074403089006240c140e00740010310891803403e01c0b4180b003203910b503c404103022805200c104584c2e5926610f402ca081c0c83d41c0100034091310368000a030700340b6240040341c003440b03a42200c1d41e20002c0700062464150f03841d94400702e4010051400c1508100e0000710300f4108200c01034015000b200d00c111041d6000d19124010454821803801c0d0f09808240740426401c00203000e01c01d480c90070142d07800c0000c1c000d03603201d00d80350644550720380c000a03001100a43c030080003130403040c1c140034210078a0004042820075000c25541d01c0107000161110158000000701c030305003500000303e5101813210840e01c0c0c818003081440948000e5800030302141e0019400300310342c01c0510030309204041d48090714902a02d4030009500950020b0020307107680024800544140c8041d028280c5480ca0030354440780c0d11407801c0c030010 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 38760319 1250 38759069 38759087
    0x611130b0703230a030b19060c1709010806041a1f08010801060506090111030d060909030f0c03051902030d0207081903060303050315120a150c02011503110d061b 71
    0x10000d00c1d400b20f114020103002c40305943e030510b03103402c0000d00301450000240c20410300003140d60601a84403000701d401588030f84178204141c42080c1400b044084091401201c0c01010012400210b540001030150314150300301c0d00c1e0716403400c6524082d1401450104c2e20700034246041d008681c20341c861004c2d0250b80300507041e0041043c0c0c8000c020b800d0410000039036074400d260300181007002540f2100390808041c000c1300d061500343c0c00104006683d0f0b001510103001290002d6003c5501c8440711403200e0302580450342015070503540c0920b4280c64030001841d0444003040103085110034880000300e05403920080c880780d03008908454450101c0380c0380c0b0380040c1407001d000302054200202000000c0d0080140da40001014011701310070350a5002154899a0f0900d1660312440b4610700d007001e001c00c008840102d01c9104030103201340444000c0c01d901f030707407452190741010317220700b1000708041400e1040c00703800c405000349600c14048058071a0710071383e5a68860305191703d813a10303c54404103800c58001c07 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 38761569 1250 38760319 38760347
    0xa05060f0405010b04060c051009050705100807091a1605011b020a080409020f07021306050102160311060f09090115020c09070e090403030b0301060308041d0408070611130b0703 78
    0x5010720342c1845030020084c045c51083c0424044013104203005c026042c08851100843d0600402c60f01c0361030700b402640c40020707208541c0a8151080c020792610700c00d500d85031003004241c42d0041842e2410540b444044171034011030400c41820721400035106500c01c9001c207601e005c1c4e00041103400e0070200c19460f028060880038255444203180400042c8110161011100100303001601c0b220702c00e06910181c800c81d4030080d03003c01e507200ca01d1040350580c0e001c070701950b6003a800c82e143d03200b0040f45490462000c0c00060034420082c51040d80b9442c0200040c50306126140490b400c01116801060710351200b07801403000050080e41000555504220a01554000301c40558507418111f502810b1070140f69000b80c0260804400541450b000350030214220f0b00c050000c00003e80e4a0920345116000743c002c8418140c2c03034503e140701400b10141014003a5410a4a491070451039a0b6400b005058513040ea0f0120b050078000c1d110a02400e46680d4004c04d040780d01c0c00c1c0e545000d480c000b00925076064013 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 38762819 1250 38761569 38761571
    0x3090d020c010f08060d02090c0a1106071205040c050607080706110a080609040302070308040b04140a0b03060603040c0f0b030a0b03010c09050f010c0804060302130801050702330a05060f04 83
    0x401c00741a070b030264403014441994200008181c40700000715460603100c0300702941152221041c084a94004001010a80d0150391248000701c418486140c440f4416500d16000603491003041c51894801e5015607041441101c01c032070303503e903940c0c00b10b403658011303075801c2c3c0380584003041c1c5405000321030140c205516200c119941c034201050601900005018240c00c0c0105a4180041d0405000f008480c0141d03400c8482c0316120b40d500d21031002258040c0c05803a200314071091121219040c217120304410f03501e84e165402d0450b0744000c284003540d0002003040d140b215042000040c100055103d0320040e0a44a4440780e891a018400d201a500840781850190380b601003c0c01100e98000192402d0316422a055846101c0c4000103ea401c80852809007444130005400501c01d0340542c000c18804001e2200e0294203903507036003598200ea2003200c0c0d800168110107910700103407042c8400f041c80743c01d100d98103160b014500044204240c104841f0341850982c0d0b18244042482c00102d40c0d850307104101c078 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 38764069 1250 38762819 38762833
    0x30309170708120703230a0e06040804090507050d1107060c0c1104050901090209090106050f0312040b09010c0803040317130203030405061803150a050a020405010503040f0302010b100503090d02 85
    0x35416429105142c0d1000c40e491145002c1503809210f07820006503058a0705407031080c0220758080c0b80700001d013a11f449003446c0c50940b0702003000c41c0201f1220321460f0419071013410b092805d50040d0203070000810003c10018100408803100703080d842140c024000b41201e8545032010751620030112003180c0200320034032103421a1000010b5510b40b0504d441481030390b012600340c440300302c514050010140000c1d4002d400b0020081000c0c01544600210386080724802e14034401c0000b070546454803c1910451050b0401080c4040e083d0080288087c01e01854101c01c1e2400c90f032200c00481d0004c3d54100c00203032190f1140c02000910155040d00400d10749400c3c0300c40c0c40c07071364000b0341d8a01c250f00c50729016020204042c0c0055900c104120340902e005000e0700d0f030000c1c0303009400001300d50803244c14010034509008a0b001000601c02c0e00c0070b40754103840b1103203503072500d80759101850340d0504100c0440d0740703551400e050f0740c8900442600c0c1c00ca0584683c0e440303040000480e41403441281400d421036011803 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 38765319 1250 38764069 38764073
    0x60507050a02010c0201030b060d0f0513020d060e070f0b0903010e0d02031215030717060c0702010c020105070501110a0903020111010b01090b031e0103140c0307053a0303091707 78
    0x20440140082e030900b0400c0c4240064401a80030f0202016481d5001501040c000c0e104400340c0c001c01c6d104d242d0400304100c1c6907100283c5248801d545c010294020406c161607400040207548046040c0c0034000480b800700b907a5141d0090707240004c0d0410160f44602042c0c01c2c140341401d005102d1142c1241001e02600c0404680c025568001c01c0384045030b500304d00d004190821440720091100319005003d03600b1603512644501000340d000020b5024505c10b0b400003d040d070200c1d0307055481c4954160f4032400e04032440c1e00116016009540c040e203003035607102d07105160f031011240103000740c00454490308002480e6000141004200b011081c00c40d906120900038603a81c0b00488000352030311610039640380e8480101020412a5680140311f0418090b4004400d01c82c0c1c9813804041605d2180484403145e1400040c1a260715151040a4000c15100e81001e008484001a00c001065404c4680350040f4480c0d1444000c9050036401e80101c1d55490321078003400b4496240b49101007050400a182c40116 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 38766569 1250 38765319 38765323
    0xb01110d03150510050405030d081e0601030f0507020d020c09090304091d0a05011d01020a170c2a070b0c10090c080a0b0105040509070503030702040218030316030906050705 76
    0x200011004050b50740c030090494802c0003814101500010380b280001c41810f48016006034454007a481c0b00740714101d40c5103c190b00c950b80c0d203445145c0c0b0010201c141d418603104111203c2e400380005040c9901d0702c1954400c0402803007142d2141c1e03150b90081c0308906e1844406420030a22b40e11044c0504850f000304001842c0000454040310a51400040c00e5000018008030074801c00d56840c0960207451030a0701886015040201d6a034080c420030104c2d0369440154a0803841115031041c0443c0340c1c01004071000c03400b020116840403100403282d141c1014030b503031820689044038079050300081008598075100c6040100d10068424561a2443e00c070b0300c0c0160950307c10064002542c50798462004004100100300400006c0c2480d00403103000e5090b41c03400ea03d0060090140f280039600c1d240001d0907107940003030041c0c103e46029014502d403450f1030702444065403045880e400d40500280720300b4481c0e00c0403c01400d02cec05000c00000781070285407034000c00f1140c55501c00d004000382070040c10007040c40 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 38767819 1250 38766569 38766583
    0x1501050904050c03100f05060a120f02040b04090c09050a05091b0105071403030a1a010903080903070509070c03030e0a03121d06130308010f14060304060608011e0b0111 74
    0x400c44a103203065580c0d00e040c07071416500540440c1c01d4059800302c2104c2d810b00380c016090410f0075000502c040d90301c4109100c4030250318030403038003c0e5140d14442004a100781c0c00340002e40d4005880801c3d501c1d4000085015511100000c0350001d1698000f005032025074410a6084111800c1c148002d04045d06265070310384a0740041000040f00142c003004580c05101100c2c3e0030f50b800300401c448699092540341e160303081103e1850449003444d1130b40ca03a1010503c2c450401c2b40c8140c486008050541e00c031002d854024030f41068051041800125a03683d404510511410b050350361a101256140f40040c2600d0154050300000e0344034031080b030300198010304c410001e00101c84000514004280c1e540091a4030303c0c2c90000ca50065400384900001041e6104101340e010b41c55414403643e0390104000c1100181c0f20342021500e0360420004189021401150014007131034011a43c0c80e10381061320f0860b501c4603000c0b287c04440341e4520101d01514000e107821420242003140c400c800c032010103916011 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 38769069 1250 38767819 38767829
    0x1080a05040c03021314010e0403020d020d020d030b010203040801051303110705060d020705030706050408130803030f13020d0803100311120c040e0f100c030513030504030215040512010902121501 86
    0x1c00e11444088031245a200040c02c1c4041d000700e14465a54140b52104488e0640341600103008417001144004d0001039030003011000750303008041c4001d14001c210000c002a420041c11804100800201e54400740a0680145a07045410303070403410038900900441c40044c0b540d00c0507044090100b040341d644070143e5201c244040c0c40580ea80d4981d1500c503085200300350004040a18003010700090000340e001a000d1040c10300b80310b800881d128001d013903480c0400c6401070804880040054184400c02070103105491010340380005114059076560395036042210140400d10b2080700070028440040a03040d18030030203603001030580d100248016201c0340312003211b90240d034070b80b085900c3c1401e0030000d90341010809001d4074001800320801c00c0c060a851282c050000c2c0c01c0801041203940741c540030302e00195140d11214070701855139003402582c01c0c83e60808a2488001c1c4800911510f40880108000700000300015242601d40b04209141e00b0070384900100d540031803021f08492110800c0a41518 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 38770319 1250 38769069 38769079
    0x303010e040204060306021303060510210206040807060e03070b0c0a030815150306030106050406050303030a1a12012901051c06050d08030108060f0408070303020a20070501080a05040c0302 83
    0x1d40d580c000b2901070921070340010080d520000b014040d141c10004076006a92169805000580f40c8403020154440b0380d00030503112100c0707070260040c201c00c0340f11090001031001d0102810700313a54a142e641415050380c01000441c0e1100345540c4140b80c140407680240010304580e9007803810350307281d4580c0d440001e01d0080c12b20095a011a61940c500b01e80980000d000a219018981c00c0c00c078001e0803500140c1e10140298201380000c01d030340c44c20340650300684101030003d40c110b0340d030300d221640074010851081c0f0014080884181080d250030003140348100c910740c0081254001200a1071591448081c0041c03610b04203103091a00341e9000007241c0b200c0350400c0d540201c581c3c240c001c078801040c00d640319aa020340b441c4031860400241c5005941215048015203403603650b04254000c2c040c00807540180742d02010806080041d009601800020241c0d241a60b031103070112880c030340c1d4200600c4203c4040e502c041c2c006c214669000c0200c0384d20503420a02170000381001d6850340004590f0b804024495 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 38771569 1250 38770319 38770321
    0x3080f03091c020304050a0e010e06010503130203070f03141b0f1c030816031a0d030c0c080622080f03040f0b0a09060606030b0a060305190509010c0f110303010e 71
    0x3441c010080c0034034406600207440b0100d500240040c1d96076200b4414503018610940000030100701c07000306907048600d0801c10000703583d43e00303004642d25400205003091100e410100704002d604c041280002134041465540c60560450a21018000041101c0706481d8000141207040d00001101c40400000c250f07844d4552102480001c2c08404844000034101102c451400f0145a0712284090080316103024081d201c1d444100100c3c1580c4c4c3c005000c2034511032001202010b4145911344040d800d0080c0b070440b007040903590f034000d402c24203a884203080d580000306110501204481005c040014904800d1913923680e42e0302c0d40360798020285404424100800042e060080783d81c0c00c3d20807154000126007040c5000340701c0d02e005100011043d900989031840c08900c42d0b0080c414410600001805940c8442c9465001c401801c0003c2804019103020140d01110781d8060003818040d00488001189952403040300801502d0410340301000c20542c508034800d01c0d80080116030548080c2003040840e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 38772819 1250 38771569 38771581
    0xc010e0102010e152a04140402090402030a0903020f0106030b0402130b03030c0d08070e061b0c060a0309020907050307050307030c02030f070501050403030c1d0105220e18010603080f03 81
    0x40c01c0340f040e0218a07000d0040180340103e0070b618101d204540a801c660801c2d02d400499141031052054690124602080180b0800c54140d10000100c40014409807405807040013240982c3c1043d144504103545801208003095010310442180c01220320007004a01d1a43c0c5415449180161000c1d0013108015080507240803590403a02082c00042e048940d2105d0301080b50342d894005070350200005005070040351000d4410900c18968035002400103007001000201d110300d030800c4c4010701503940305403500210030740c8640b0080d0a40304216100001e44001d640103020010a00030840400c001040040004280d00003040d2600042d891500151b00718554409a240d845030b9441ca200c040004100c4500700801508844e1007588a80e8050044181c07003102600c5015800e944407042541480d41030245501c501c020f000030314000881120241c2c0800100921030300b10b604601c0c43c41e8141400c01400115400546c900b4083d03000003000302510b1912102d0580c002d44200340d022003000004610 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 38774069 1250 38772819 38772821
    0x30403021302190504180605010e060904060302031b04060b07081b070b03012c040309050607020102010b040204030b09070608060108010306110c01060605040f060903050601060c08220303031802030c010e010201 92
    0x103c0004403a125800318400143c4150043d11490b8101050403402c41c4000f8070501035441101c00c1a1603040c0391a40c101c08001041d0000503190340c00584d80c100000c09030703604008141407003880310007404440d00090700b4007003030302c0385904070a142c1942040006c0000d0040002c50b249400c210b441030500d000300b440840d0900c1c03030b1a8024540300710040000714250044c0501402140108000c0503070a4161440740303410304108840140c0814031480d070411031402c1860003450114814800003031060002800181280c1207900183d42c010000390400c01c400c102008464054059420111034514003000001c000e4541400024040da860398a99a0b8205c402e2064800203006c2c0c0d80280f289035110503004007103070880d11490300c1408000764000307920fa01032078492087c1e0781c00c8400390499a0911605a907070f03003035841080340d407c0000c000459000e8080901003851001040e1240101455400d0003002e5400901c0741844078075613045180b0045c0d03000140d40c02c00003030a0070052129110400103034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 38775319 1250 38774069 38774077
    0x4050312040510020d140106030c0f08070504080304180b0307030c031707080a08100b04260a02100504060306050603090c040c11011419060e0a05040204020f1204030806040c02030403021302 83
    0x5024900206121111500c5c3e9008104050041101058941ea84020403010307036104a10b0000851980004020100d2190104540c0600341d41086440c00c2d40c3c60076058916803160b4011030b0303010031032100ca40e900300d82805401c50b0000110f0040001904648604043c0c00d46803200070700048640030b520894110b100f0071b46440940000240b42c881c503174004050040482227906100740a43e101020500025a00988003030b21541503d030400070b1100300c0c05a880c000c40c0c1401010900c18070f501400140da41c048000c80c04003141d50f4654039180760200c0a01941c0e840d42000340304010900800100c208005407641580c6012540031078040c0d01c02000380c5100c590038100e83e040d94288030989070507000d403902c03550260310441105000c156144841d0411510305000c1c400001d40854081010107403684c02482e0880e000910052400010403a40e00f025800300d600070303461060340783c1084281500801110fa00100940f0184007414170844029140e10407800000c0c031800500c041d1a44c1d074480c95050b9 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 38776569 1250 38775319 38775343
    0x201060909030503040b0609010810090c03020603010b07060b030105041e030c0204020301091e0207081b030f0706050106030e0a02060a3905060a0e06070503060d0b010e01050414040503120405 84
    0x200070803815428001c25a90003240e0684440020401160960034080e0707049040f0365419024105000d1650164006850303201070070398145d0826100840503a4035500190f000b0190901110758807200d601c8c00c40156990754915030310992614080202048240101c40c506402c95441202d0441092a003030355140240c84c0080d40141c0301000100d18011550711048021119820000d4040c000c94004d1040c0e1203603a000925812040c0080e80ca10010b0f149003070b503040d42d03a0042d41d081a410030700109082c3c200c141d055440c030b031701c641c010441542c15110341007001180304040c0104000b5600421400e1003103410f000e0070409280014601e48860b880003070000f0102c0141400c5d600c80030f9900c10b054080901050b9001e0055402041085020b40704481c110084000501419130790030205031001e42004140e56048a0194800304c0050708034001c040c060311100303030005182e50501e014030044070a02504440351564070010f020124200100703542c0c04041441c01e075407055840b4030785030f410300d6500701c65 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 38777819 1250 38776569 38776571
    0x20907031e1e18150e030708070b0609090613080901090902120402030607051305040b01030207060203090105010f08010903020c190314030a12090b0f0604151403070e0c0a0f02010609 80
    0x2a100030001e08150b0064064240207080c07091540c0240506400340f25403074000c1410003d1000c1e40014106904005940c5064205aa0030400180c44403602d5030300c50101120b011950400b040001d140c00b4051540150f0008020301092602c14160130381030281755406410360102040401d003a0784170300c50000c003034542110299205c0121021054802c03005840c03c901c03a0060b200000c54161040040d198544c0c0340f428100398030b43c50318060000030018076084038100350702000000003003010340c002035000350608c2c000015998503010200d40c0380403098104005a904010108001c6940011418041c1404035281d0003a000d60344040c150107040c0e40d20041000445440b20604028040080c2c1150041521400b070481d240110aa0803560b2082004058245810214a41011034800e5940c800c1d40a27200007001c402418880410b0340d0940c8c0050004c0e02e4207400d5000b542028898031000b88200204031100381040707074580705140900c080c050300f0020755000e0030301c03664400d4010354000e03c190f0300c4c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 38779069 1250 38777819 38777831
    0x506030115030c140d12030c02071a0c0607020606012f010e0706091d0a0504060e0609070501030b090411010807090308040f0617070801120203030c07091409010603020907031e 77
    0x40c0c00c804465452044c1500742400600101c2c4c282014802c0900175139100c0a09003c6408003101036000305451403059003188141c00021030070780c030002ca184456030050f108660300c0b0415500c006107412070052551046401c11005c0c040b2590700a802c04c42c00015180c0c94841e5174102040000b2691f0398800007950560030044205c05402c80070903500250b55440e990361480d641c540342c6c2001c409020313211003484810307840d0004680105a0740417941041c8942004124034000903002ca24003e01030300c20280a42005004001c40d603090703c11003041c1034040d0b961482900d05074803242140e0b481e040c0103074103020481c8001111a80b040d11400d014550090140b500c2c1c50321401d07803c0901c0f115019140106003003481d1030810502c842c1c1c5a038400c03c4940d8030101036a0038482c0200d050740e0b0314a000c0707030140300c148001074445d0020f00c60b00001d000d910300005282c0c003c04204480811001d080041141d1400a0a0000d82c071a4500540d01410900300030408007003040c107402000c0d403050241c03045985004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 38780319 1250 38779069 38779073
    0x50a0209030d0c050d08191a2443030e0303190e0307030c18050609070516020a05040e0a02040606110703021203070b010906080706080613050603011503 67
    0x1601804203280d003901201e84030400540166462040b04502a10030381c09083c145607018400c04449500c1100d03c1c0c44e901401301400c0c0fa20701902c0460359030a510700d94000c2145494103008140903040d110b44500d00c2d08030740d001d01c02000341c0e03c501400c5e10080107041c03008000d202a4028080c44d40c030300a003014045028452302c500f06011092004500254103480500f449140002c00c0d0760080400303108841000c90341c070300240e4400408480740c2c6e41500542d5000800700f80d42c03032414401841c0e4003007284810104441001c084070401815144182d0040040c04005035004090b1080b80d040341d1250800940140001054240d0b0782d4010b551007800e0030300300084032402062600c4c82901c00e541c2404526100ea0081d58220b06032462050560f0256504201510b450040030f401902c034001070380d182c039040381c4940345204802d07040120201d84400081114560410118000b040a40344c024014104940090f900101d111002c00c585a21180424403d070b0f400e600140c0f00401c04000700a060341d9038 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 38781569 1250 38780319 38780321
    0x2150103060b030c040207021c21021c03020703020a080d18050d020f070501020a02060d2003010f0623071a0a0c0206100b0f07150204060c0209060a0e060607060906050a 74
    0xb1440c001d02032a05184000e040c00d0007a650071581c01071500a0b01d20034a5000d220540340b440c815654604e001c070a9001911031280e1400d5551480d6010340602410161281e82d40480c4076810b0082610422801c6e003c00c3e8045800cac3d0401d6885004141d8070f05c2030849100162080d10003101000914002040801c4800141d00050b005103409580c0ca890400150586460040c801e09000d6004140e01d400146040c1c00101502c0f001400c0003d02e0300d403c122007013440700301110a00449000040140130307030410b0440d00c500901c030a180c900030864404c2d04298011851158090111381c0c080b42200c00c10444010014108081c111425010b25100c00580f0281400d0b01034040540154008107030341d800d2411548045e602d0115165207007818941504003160f001c41c6050302c0803a40c49600040302242800100010300d2281ea40005242c40c0c2d004100d200030010b05010301c0b0f5005a00b04201000504202c0e50303014404440d41ca88030762140c188640a8103035420024001440c0900b004401c20007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 38782819 1250 38781569 38781581
    0x30c0c010f0f050714040605071b090603020a09380301050a0209130902101412040b060a1403060103140c0627030318060a031b0f0807021218010215010306 68
    0xc84400c3c8040e4403501404c3c0d91044009010070740b26074040000344002d501440c000c2125500c03451548030f40e00101e03042c440441c40c0c940c003c000c465445140810551516640d04c40c0a0b1181d00001c20843c0a41036850b02c0c200341000e821a03842072110090b102060748542e42071440d00000e8001d0140c3c1c98101d0103a0020351114090f1449012801c02d40d0042d03448078810b20f0116a07000e03081106600050300c080d030304d140510180b800d0740c82c4104085460000500710913401039201b200c04045a06041c0104140d1a00c00d410101c05190301c6512a00e403a900001c503141101d17085500f600015403c8043c2900b05980074454540000780094418422551035040d1138010a10403590900030511108054981c418070702c2c54021483d41e442799a0392031030454002c010240b194100060503c002080122098040c6403080d400b050706c0c10081c01800341c0080354203078452038074405000c1184e40c0722080c4055002e42d00340c5020300e48a40454640c140d00800440301c402c90074130741c48e5180f50b035245400405054 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 38784069 1250 38782819 38782841
    0x2116020f030a0b060111010b030606090c0408030d0603020f010c02030618100e0609070909050d03020306030c0a0306140117071a0f03010b0d0b060708250b070207050102010506060304080f030c0c010f 87
    0x1460f2140e021b1090040c819484000d80060141445032694810040c8201c0080c100d100016020040028070b50004c00040074151500c41010515501e1401082048282403001505218942e082000140e402180041d4800d50701c07030b07285810f140c1c0040040c0c81c0188019001d5001898800400c42a180018043e03110b041030b407040f240c15988030b040d12401d5800c00f0a00509540c0882103100420b4003d402459101c2400307030403100c001c41d0110004640900550040c1c0f1110796030303800680f6036214601d0940c007410080003103035440050a0503542c0e88001501c100a0f4103241c0406100102c3c88040403103072820b9120300150780365619400112003e07800003e012140a00d8000d42c48401e04000c01940c511541015403142007401c0b0181111110107a0254a0070b42010001c4070000520544045401481150700514015060500283c02c4800c0a003400340720f000c09004100008010604a40d640e034500e144c0b540c0c0300c0d1500303080541c03103004082d9403001c10f50074010780f0844104207a00c00e0954a03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 38785319 1250 38784069 38784077
    0xf0503060c0a1e050706050f1f03050d0e030106030212061801060501050315010201020705010603032105010506070201050901020f0a030201020310050402070c061103040b040801020c2116020f030a0b0601 89
    0x2403212428480e6520032107400c1804103d021035a03007009030740111406550061402c02c10701d003405035981c980440304101d4498503d001d0714402d00c00c490b50f6451300b0410020014480800d05421521025619500ca000010800020344a0b01c002d40d102074002d10000c55010300f612860b0400c4015039a102e410484000540c811450007841640c40b05005c6e10080302e0042c1c540718503540341c41d4030000030340342801501415503408101810025000b407048600950095a40e5482c07a841c080b2a24044081d02c51221481070800006010f656501c00c2210a415424240b00d80d41d22400c40050381003106143c11140305010f840000024950107400542c899031103507600e03014550700c03002000304070b015001000d40381c00c10110301070181c0f5004503184c2d15864420011242050343d20440040594065040070915075000310340e260b0300d40002c0101e00c3c45520031f002000c81f180314412002181c1d000d450301c20021020740b0701550302503407504405024100400b4007600c80d918071a00380360000703034010f8030903074001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 38786569 1250 38785319 38785321
    0x809040c021b0105070201110303090705040c0521090109080301030b09010501150203160c050d030509040605100c0b040804050d0305090307050108090714060904060e040c090207020603010303110f070f050306 91
    0x2480461900c102148030107070a0342e102040e60045a16400a201c00ca052189070800c0d8041188100055440748810100614209060006100c1078900703080902042c03000c140116444014000040142e6441c440b40000b0300d507840c0e0f00391a01500c0780d2440540084400400441031140c403041403442801d184c8024042030b41d941d0f82a440c1d08030303014072820041c3c0040c04400f003001c14017003003510720314010824086142d4941001900c9418804401c402080340025a21114206405030764000c010444002c0c40d82a802807024106500f8a100103050001ca100081e040001c00c500703980242c400a0214400d11455180c007420aa01c5162000e100c1d02c40c4000000b400d61064480c80d02c0741c031040c800740581d079140102c0d1211070b01d5124010380c0d0261040c41140d00a4903284240b070000c0240701c0700d0002d641058141950040340c82d4101030340b203d00400c002c10240c0c03078220499045076814640fa0010312504517840303003405954000314a0502036110300040c04007629007110b003075900490654001e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 38787819 1250 38786569 38786591
    0x120f1b0909010611070e0903070204060914041b090504060204031505010303022d0d1809022106030102070b0a29030604031107080303010b0a08130302071a0d0504080904 74
    0x61402a0026a540200400d0050000b94420390200541e140c4540c11aa0401c0e00d03000040c4002404032120800d03079001041c80410340c60240119070041c40c080c0c1e01002044205801d400100c18000c02c09441c007a5183c014404102503074001c1401000c0e0140100081e04040c0303071a1019600030f1000341c0707080e0301c140701100701d00d41244655030480350301d034005014a0011030201101481c8914054240d002080121040000c06000040d00d611242c0d469549042c450492680781d0006070300301d10402c902c10701c800c03c640703101d00d440e00c00116400443c20031641d650300b0000b0f0282c400c1c4600100136018038014011202044d0308078048554100600048003c40007015180103c6002201681a4010404a0007282c09283e42c5280c0541090640e140c8540b0303041c5c810f207164400e82c082c40e4007000000e6040d201560010040f5000100381307122941241a80e00c0003540c0c0e007020301030301d0030000b60400c048041c0c208034400c852001150050501881c03a29041c0f030f058a170003104c034090049050095180b4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 38789069 1250 38787819 38787871
    0x31501030e031204030e0d05030721090e06010c110d030c050f12120604020405100207060e0a08030304060506190314060a0615031a04052815050904050102120f 70
    0x1860f0140c00741c0c010b003552140c40c11500b210b01d029029412131054520240401c00502c014101d081c064221210610a040701c260307110b440d500008010401401020301c20343c405142c2d8a0b400c00000d01c0e014681d2101e40c100a1001d000b0082c5041e40601094449000c054001d2600c0c03869902400c20744a8048c5610340700303912031101c00382c10b01c0750344000c100044c075001680e00740681124014000504040c0c48102081c0a01803040c0c400000d42d0286030200314080c0c0c005660640c0103800d440d030710310b42407405541968031301000c0c00082443e51140f002038025110ba2211680f04801000240001503690405188449000c0c5045903140901c0000802500c201c1c05610200d461041046005030300e561000c03801802c80e9480e060038150880360f540c036190382e01e00449010390010030320300c45029002c80e000000c5101e034400b48400c1d1401d01c954130042000460303041085500a80c5e00d260b0390b03a03e034a001d50080c40741192580000380c0c2c01040c40b04082044419510138150902c0170f045800035081031b11 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 38790319 1250 38789069 38789077
    0x10603020f0904110f0f1c090b060904030e060d0c0201050a0203090a030c0c0b04030605180c01020d030b1206040b2e03030e01050c01060b09101106010b07080708031501030e03 77
    0x20400740c020440d01055040660100c1e4040629038021810007400b000c0d410520b42c00f24480c000145008a800d170070108820010100e490088481000010920754601d02c40a20051040c0c1c420780d0001c00040a050065640440d480380040c0300c0c90755504031303144500040c00c50120620040d8604030018002103500e1007200d0003248124010649591180d0341100c00d004e11140440d100d400049000841040d01000b81c00518031130310000c80c0b06d14004100b40021500402d50300c0d00c0d43c2c001c0401a4069030013040c4407104120a18001c104078068902140c0703025180c1043c12003d200c0e8000301b1040c00010f0021501036403110916002c20800364200c0322468a00000b40310303c695000c5001c0000a014055107480f042e41814981c0c200b02c104421142152a141e0201184410025161182d450807114150600c074540c104014649451000c56503560320501902002c0b100005802c0c0920031084240c400e05a0302510090b5030f803074404500801e0000702a08503012904080b00e8a2217008040152 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 38791569 1250 38790319 38790337
    0xd02030307060e0304090912030509010212040209070e120604020306060109030317070306090e060115050705060105091b0304050f060c03010303020c01030911030f01060f0506090307061d100f020601060302 90
    0x19070030a9619215140100010040c003141407000700000a1214aa4020f1049250041c0503010910088850207002e98000400000c8964410498900090040300c60700f07405c40d80503956840359a4541c2d0054031800209080641d100b403810f03451110002c400282c0c148503510030f800f91001503c1d40d81c010341c1e864100c1d010040101d809401e0b8120580c526a01d01079110325203260110301d090346c42c80c80070112040b0311199501904001c0041c001c0035961003c071101002585001032070400c5986450342c65003010f0145510600f995004255115048107540000100702580030b80c3d42d00345860199560290000d21050074018407002076120314004d029681200d0701038019120130f11b6000011002401400000c541500f4070405a20280d00c080000542401c03405000040c0d07241003003480c14488007580d02162150008002c18859901c0101d691130440300d01d820410820265248418600c6410070780b07141e0040c000121410380140e0141c25500942c070150240c642ca0f0762102c00071000c3c1d2250748a2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 38792819 1250 38791569 38791573
    0x902120a0606090e0c160c0303050d050108031305060702060403080f0301060206070216123809010b06040e0a090f0803010e060a030201140c030f04090207030207090509060604020d0e0106091a0d0203 87
    0x1141700401070002c01202c9105e0366070004205041d51030f07020404240e0400c1c3c0004e100894002da6401080c4200f074050055080154200300340403280a42c0a9081c1c010039004400204102c8215160502500d01440d445103003541c0743d8011854120844d002403040400511420380800d07032440c0040f8081c000c0404041480f0602820107400385007500e442c9c913080f6905404581710b620b0841c14540540d40c40c0040c11400320350b00b00c0641c400c0c842100041e22342e058591400310b00c4140ac1d96810116421100d40310103d11407070b658042000001d0880c1200904515010031b0303076400f00120740c4019416600301201d8041c00b03032100420710401200c2808000e003c03441a00c00301e05c00800c200050710b0888506000c6900c0c201d90049000025041a1b100300401900071900300109601408044040c0400030b00400207171800c401e400c0d03698440604014040c031340c009850710400e40e054010380c034540941c100a01540c1e6888420707500410a0001d00041202c280c80111060f144c0030364107003c40780c4c000300 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 38794069 1250 38792819 38792821
    0x232502010e0607140f011a06031e09070909031809090512030c070501020c010c0215090303011503110313020103050a020705030702060a09080d050a0201061424040902120a0606090e 79
    0x500035030b54003062054501103500c00c8030441314001000b074501482c104d0703c00814910481c0c02e011212a0347d440560b44124000d004210100403c2607903038080c0f90071000e6822440d2a010040390400d041600000c1d5840d00340f01c410000d054102d54100400260b00e0180f18046a458180343c2c1280c034100c000030040e4001d182c0340014400c2ea03c020390341000e151a24249804196690542240e01180705210165103e0000c42d100d80d40600014140b410364034060fa0041c40d10500322900c03407005000381c0c513190346640e10b20041d45110f940141d90410400043c10b5503824915401a60410030b8442203000a040c40c0001d038104034207000740c4040b07983c000019404c1c10f031541e080200c1d94100510120030072411402c002404501000004441e880c01d448180c1e8610b0200c80080c20f540d85d0313030468140c2c5000d0700e42c00201e507221551940d070301740219000380030b641c00c4c0c002030400c040c8903a90082c00428004545502010071621641d07001c0c0213400802c10007155109825100c0700b0251240d0910f00c21000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 38795319 1250 38794069 38794097
    0x18090f030c0201052502040b090601051215040c02011b0302040503030909060409050601120b0c0406080105060703090801021306020c09010803030121060c050a0e04050103050606040c23250201 84
    0x42181030100b84141000c90802c011510b4004400386001c01007480222000155001c3d418a48980704400e441a02c28131224503124001034414411010014482a08007001a0100340e03007521003240214004d00512410072200d80c024040c0841488022141c2402107403070144900900c210390031034201038090342c2000014801c000a10f50004d00581c0c009488101c2800014024060180030b030503459800004c1c0c1015081c002e141c40e100900a007007048080100340030080e003000600d41125000c9400701d682e06018902110800a0b560000240390300100d032180000303800050b240181e03a480e40c21181c0340c141440800c000d100082c41000095001000117018480d008501510320004a0b0401401409140d03903503000c0b03c8002015100240c0c0c007080c42c0d114158030034020380b03040204903001e0010754107584600d0b44070304020b04404e02c15955000980195030042d82d107a245145c1601c0090540c0051000c11445079201c00e50b150a005400111801412040280200342c540c040e5152250311000b2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 38796569 1250 38795319 38795327
    0x1020a0309060e010509030d03020304120905090103021509090103140f06040b06040902031c0905010306080102030405060609070e03150a0e1f020d061509080c01020d08040602130e010605030118090f03 88
    0x280300c140c100041003104c0d14281c7c0b410403015811400960340183d43c1d03e080d01340324068240404189041190340101000103607114503800781940d4048031605036046190081d41c4852048290340e680000c3d00c9400042801002500004181d54038401d403001d4100d503583c4a91100000c80e03000b442d140b941d10214480b414194085c100b41c42c4064122410b103c03007004e07841440e403483c480260000d83c1c0f45405019951b4540191001030503604001d50850415949041c3c0b40c140003020303140a01d0a2100040030f0380c0c89448006400580039090301c0103417090060088505000701c883c480920b0030802808c6048070b00103101a801c40c0d003804c0c4040d000543c121190301961020b044040c259840d000003140080010101141d0030025490300781020780382c102c58078140b03182e82c9042419500f20800c4000360507044202035600560059005a580201514045610140350851050030046000200c0c08075085001107050700c0000d003824605950129580c0e0690b80821001881003100900150000b030203 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 38797819 1250 38796569 38796587
    0x905060f090f1506010318020105031b04050a081005090307020121020426010c0806150d0212090322050a030605090f06090106050a09020708030c131212080601020a030906 75
    0x1e0064031158503803911441d00d801c4000341640000703031144003840069a014071600e1030f60790802c20550b080140580010746076002c001c06c00480890010f814050389505c0c0c400b2540a09401019581c4d00c40c2c030f45c218030b6a200300d4031030403c440c03c0c54203003ca41d804400100355034009505030344001240c0c0520340d000f66003d404c080c1180f042ca03005c0c44085600d000b0146010400a92042e40030560000782451600795804051f80344140050601484036a89030006008d20034020541d1450f542d03203802c0380401c000d103e9407080790000c1c407041c03040c4800300d0f2010000b00240c105010306d06842c250303035000c01480250b5074030941e5401081c00304100005207031500b0907540302401c0015240c4401c3e001040c1802c0c402c003142c0c0c605c07069545403018040307480c000300d5000c041d060083c0d003103040c11070580e20070200f031002030401c400703c5d0004180d0410350030a003040880504882e41a00e0304805040c42c08270080380c5075a10000c00b041a85c800940c0d5540300246400409070140d803200743c818034020040d101c20032 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 38799069 1250 38797819 38797831
    0x7050120010203040b0f070314060f0a0e010905010f0f050307030b0a02070605090c01021e030403030e150a05070c090902090402090a060305030f030a0606050a0e090c04030204090c080601050102010905060f 90
    0x2400c4a2101018034080c40591312a600514410b505803601e541d000340034120007045041418502440c2d40c00c0583e100d08130340c0d4800780966075103250382040741c000327103050a41798003042104411500100c0c006a40d900168120303041e01c5442c105450f22004180400340480c002e25815600101d070030004124070100958106010540061402446031504000d5850488110032140c0c040300b003600341c55a0401c60725503404002c0f000b52000d01c040181a503202c3c45148005002c01a00c01c011032459a41c00740749078201036000030380c01c0c6d5684001c00302500c107401030003060b11100f6000c0c500140ca5040d6014400f00c041e401400020382d0b0740c90b1342c00c01c050410040d0030b040d80309542d0b44003c000514104001d0005598418406850b171800c08004020b9238030a8003c6020491f044c4203203084150400c0305c2007400b4404840b244d0079aa10b810041c183c5006903403010b5401401c1209110501188884510584500c01d090740e40c80ea0b254030059090310790a18000f031603030f4005000101203105500410b5007140f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 38800319 1250 38799069 38799107
    0x2103030402010e131b020d030207050a1119060f17040b0402010c170d0203060910030b040303020a030b0406090e0c011b020603090a0f05102007081e040603020c07050f03070501 77
    0x91020304407030b402c540c40702e8088170801a01c0f40314685442c4d010040d000f24180c0a00d400c0d881d229007039540584a01c20100c0007080020304124074407682c0c0d40c1560320008012480440d0440559a03103000b003140c0e4028010001050154070603550803e080c1c04684d2103035410500c18086c540710f550044507030050a03c415a144205046540000c1c503001c0300804c0c175404100e01c007503241d05103001007040607280542018010f0404101c02c00018201103041940a078040c240161185120b01041d4040c090007800158400d103000d10200d14000ca0368032401c001040401111080e50b6200f00646645415101903c94001da445800006241580045503c11000700503203c02486a0f81e428200c0700841c4070880b242d0300804040c6649240d00c1c80351400090030b103104848884824054103099200e0701c1005002c0c80000120100c041140380c0484003420310b610051984c89940300402802034100e103451512500440742c2c001900d1522100420120400801400480b442c02d0300548003080740424200181c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 38801569 1250 38800319 38800339
    0xa0804061d1210060b0a1b0302010204050a0f0611060f0604090609051e0609070e0601080901091406010f0503010213060315030f0501020901080105040213170a020904060b2103030402010e 82
    0xa0320341c485075820442c2541e00030b03c2d21103003825401c01551016000102e100009000e0380e07500139070295641400407080c0c01d444901003164201240a8460b0360005904008000c10006584c000e000030001120401d5582040303a0805104032515428107484c0c400650300c554020518502e442c1e03100d051101d00c901e900040c1c9140d2695802c0c2040740103131404c030703002c043c2c0140c400c550b240901c010b5502a80f02c5015101d954184540001005002b61400d4100442c074400288034003425841014625040f000d42911302041c0b51050390b88242c240a1a16a84030b08540001c0c0c40c02d0500a482c810f40409960302189418400120001c0651402100b00b010750b0304800804100c0040c40d4880407400f800016a880340c046001400c02c0c0b03810790050307024510400038000c407001210040700947da02d00d00c01d4003060711680c110610303140644501960052040060004003d6180d005011a54041d206484404100b8950306110f082c0b940c00c200f9242c0040000900541c13080054042c1c0140041c00341d400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 38802819 1250 38801569 38801627
    0x1209030304031509050d0207030503120c07061406031c080103140705131b08010302090f060103020409020a020303011a0406020601290f030a0f060f120f020303031f06020a080406 78
    0x800710301c03c10002c4075540758013103001d00006128459880d16940014180c142c6035070313600c3e0b45c0c900c030720b03884001c00100d4bc401040c21030195108840b00683c201c00d041c00004540b000c460350a46d020703195107210344148010103080e0709000c55039808050003900c414209a28544503c2c104540c0b440c2c06081c5030003856804510360303864800040c11001c20000004a0706550940051003403560b011407000d22888d20010001640d41c40003059211002800100f4191180070045e0701174040c81e0060940c007030004c985110036075800400b0354100c8000c1e4100c1e1807007a0149000903142d100b2806188010b0b00b080006100703110318510307550043c0020b00c0401c454070341d4140d04a2001e810080500240703410000034041442c1d0309000e00304000550700d078104403861400c910b04402400c41c0c45003c02d9156024911402c0c00056000008400c1c0c006e010340c1c0e070328a001c610007903420080b4140d601c81c004281e400810304a10000760021010760254803c0d04d403d00b4120107450f06089010300340c4451b0040500901 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 38804069 1250 38802819 38802833
    0x10903032616030c050f0405010c030306030c09020c0c0922030207051c12020d020d0e010509040905060402011e050301051e040f0f1d1c0c0501090c060e0f03120903030403 75
    0x12051907090341d0810000c51602e80201903521000a010800c10f0900100480c02c21190031601102e40908291800b907442d85403d902410203980081c1030070300700e1040022000f070749400400200c918041940c1c50340388000c3c10403c00c0310080c4c6070f40002e590220b41000f00a044640319041841c000c0c011500e07015564000100c0d130380c0030454100c010b40e585c50030308000c102e445160446031345183e0018000000e00514000c2d52a9400031080f010005803500100c50780e40240101e0302c2c0c2d0b01d80a4014802d0003014208556108001d941c07c0780001c0012403c0c0841c0e070040309038409001510399034645164607042c1084540100038046031003024552140b01c1c031907681c1e880303501a0a2000c000124191200300d003144100c2c0c02200c010b20380d1b40b107910307d800a50340300428040c88400369a91109070603443d0780011500300072140c00080541d80f07005425000e01900d11194411200a0b81e42c0000588087e0b080c8014007030b8240c0f545405a0265030381700004841c2d000a0801c0400103000c40341000d9407621048 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 38805319 1250 38804069 38804071
    0x40303020a03031d10020a0e27010812032703030a050601090b0a0203190918050a05060607020f0405041509060501050307060207030b0c03040206070f081b0105060109030326 76
    0x90150344002148030805405008400c140685840280a11000442000d40354105500701251099000039940e80503030207841642c5410b10064045800242d10f1803401c040f1003511280043c00701c1ea281c000103040d8000240c28254004004141030a548030340380e2518544c0803106030080d203450305d010000742d00d04040010707610411440f500402d1034281503001500310b422580050082c2e600800c8411549a00081100d2201d10f990702a49000f42d03100c0300803503000d040d03a0010f40c2019101e81c510f8014401c240c0000e4002c07c100c80c01049039460782000c00880f8401c0c41c0000350000c1e00920700070031614069002c039a005016103440d13000003004c5203104044800486040311240e070741d007006001504041010344050103582c00100011400d40d01d030622038400003480020070080c0000081d003151030317800965100c44d52000070140030b80706614040000e50006001581c040e4151441d0500300da105018841c018081a1601000c1a0441d00c1c1103c003441080301c0c66002c0e440d25141070f02581d82d14032080d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 38806569 1250 38805319 38805323
    0x30a0f03020f04050d060b1e060703050702040615020604030f0509010905040c1713111215040507050a0902180d0b010515070503040321050909070503071101050702030a020c0a08100902060408030403 87
    0x347e0703400140100300321202400ca0b40c1c0480180c1074482c0d1400d0700c80a003114056501401d160b521010584001350103040150441c2910038500d291201c034139030700018001d024074808e8981d50104403048100711100e0145000e00b0340054150102006141080d0703108905002c0d01d454015025111075900c1c1120800c00e0f80c2c1c103603039554036440311000e10200404195908808035012407520001c480c1040d0390f0101002651901c1900401003420007001304450ba000385806064116125514080080250820103404050083c6d1a004401610303001d4035041d10181d000b0074500c0b16034289400d0040036801040d20b00c80143c030400100010540c10000341c001544181c100403030703220b014620400b4002020001105111051002e0002c1d41d40c3d90081a41c020150f142841d101c0c1d954000c00c403866074080d071a0865075480d10b0103108901d94044001e1500741456000c03944410340301004e201020305548540800c5411103a81c11050703240c641c100c411804c1c0018602801c1a4403240458210791081d841 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 38807819 1250 38806569 38806571
    0xb0d0311070501051c0e07080f070504140f1506040b040905010501090605070f020f041404060b033901030e060703050a0b040c050702040914010e03070b0108030a0f03020f04050d06 79
    0x45220034440401589024000030f10303280341404191854040319484140343d04100b02e48030301070302217124000c116200082c0b0014085403008014a5140e0b40c0780c034040e004080c001d03400c3c8040c2c00000341d8944c24660054124111400b000d80d00c504015840c0c08000f0403050780b0035410000094240da07020054005013620b190001095450031002500d400000e9102000303119050010b07802040c0301d203139403006564059507040394030405c1034001001001410400c41c803a00f0448140b105105032680a0030a44c4070540880707110f048290003a901281c0c4e01c140204c4800c101c101d1501a07003690b1214041c007000103050205204450030249410000d00304c1da2900007a40d80c801b00014240b45002d5100088030a0b68204903180c10028010303c01c2c411080040e0165482d40c1e03910b4204050740c19014039602e00c1c403000b000450804000b0a459038072100c82614084002c0c4004554074801008442c00a0060b480e00307181605c89030815406034000401111000400b440002079544907020f0300701d203180c07003598 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 38809069 1250 38807819 38807837
    0x4030810051503180c030307061503080309030a0306091b1d030105070f0f09030206070803070c020303030c0a080c04151103040801020a0908010f0603051009020d060903020307020a09090f03030c030b0d03 89
    0xe04a132540c02482080351441c4d00544075203000da00c000c411100c0e40d42c1c000d00d01040c01814040c0403040c1c41c0c0180e1004002540020400004c41004000b82c000e2001594050040760b50b5120208252101c070000603040c03006018802c0106c0707000700d10152014a80b401e5908810115400013800c40d034044070342e04c7c04142d28180300901160301c40307007403040c1c42402e0802c05019425500818010301510074010280100007010a44a03401460103100340380d4000d048950301d10704000400e200c3d800540c400804281d04101050500d00303560161820b64112001c80780940955000c01c03141d42a522120800078001004041400e00c0c0a000401c0e00d2941c54071044400f40c9084074003421912500228000303035140502c144002032010803081d06210a40e08086445c90040c000900d007a084580024555481e02d440c10302011340100c00340950900840d4840071040d552404007080c1e86e0744e420002c00c45c03901d00040600082c000c0d03000344565100c034a4002906c8821401040581c08050000c2c1c02007a0511 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 38810319 1250 38809069 38809081
    0x40303090b030103030207060503131209060f1706040b130903090510020f06151302030f010302011e2f160f0f080307080703030b0303030f0108010501140904030810051503 75
    0xa00880040a180d8038003450341d8513548000b5281c2c2c1031070040a08122001011641048044458000c040d404c00c014a20300441204081c11408491181e40086042003a40c45044c501070803090a507015080303a0310826603a504100700042c41d4800b0010341c450100034881c0d40d1400745200d0420b04921036280c09a4040c2400c04014101e140c10030014110351000031420b0000b4400300310a50801d591200311070000c18103000141082d40300810745a1120b00c00300030018000300445480307040b24000e0322015000d80d0101003001e034107000c003112140422781001da0031142d403003079000508080100c611014400b103a032041c40381c20304c1155080595007001d41a0207010080e0060603d0f0001d006090303801d0040b0b45030030602a100e0040c0c43d00a000c0e0080845c42c0814580240c2041040f001d0003070a41e590303850f0101200044180030300414800d9840d00002040d40c03c0d0201d6503005e6000b00500c0341c0070b155034540d811507092600030a24203924042c00c0340040c10351180c0c0c3c4010000c81d00c101744603403a40781030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 38811569 1250 38810319 38810327
    0x61c050906180307030305070212130f080708070b0304020d02060a03051501050c21040e070f02010c020610030809040b06161b06321306030b0a0e0105040911031002040303 75
    0x58004810402ca0b40c4000b840c6480001c00c951034158141000b05140d035921006a0614440244100381e0381c00c006003a4a001c900d07001c004007541d0440c2c1c450409503480c1c00d0350607529201d46c0590042980000418400b03206c1110217598084c0c402800c11010061076804145d00c0c0e0801004880800c0d00c41c1e003071040700c6805869983e800402132800307505100d0245000ea680301450211440e03c240701c50900c0c034010000100300e40c00f0b42403603032106002e41401d4900408000e0f60700a840015440c040c80882810301c007059080c0106448134200001504685840c2ca856004411444d4030a503620a400d400c0e866500150040981d070201221014180d420712281c605102444203000740803140041c040140c0082c150310040803441c07120f110342ca100c0142200b900d8411100c001d46004049011440b80c05180d1482084da0030540d400d05c000080082404290605801600384001e134840041c02542010351050384918060f000e1144040710b00d5000c03c0c200201d00e43e46141d0507030001010b10605400c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 38812819 1250 38811569 38811571
    0x1b051209011b0b0c180307081c020d080a0c051b010227090a05100e090c130b010206160c0204021201030b180a030c1112010603030305100b09040902061c050906 70
    0x980500d00c04400c2c1e00380d46150040000410101c5006000f0400c50f00d0b03522040150010305030046c00300c52110784c95400203655610308800c2c0b82c207280c10b807210645440784042400006008180c40c0d00c0016142c40303248001070080c10000104208081c811102554480c400d10008003110304001640c1e0151403041c28070596100d0240c2400d011050300c60702c1c10f516400d0b10b02c2d90140388010006684c0c9c8441d01100600800e940c00070b140300b1003043c00d0001c060804122445100380855070f21928810807140401590b81d040e41c180d000d0303042400060f84003071095165a15182d84c03031a0079000032a082c0d000034201c0e00008900c0102020000041c82003250400300990482681144444215600d4242542c0e07421910742c02010443c10101841c10003200c28240700c24000001d001e2210790a81c0c103441402001c4c0307032100fa40000d09050200341d035400302d042a081528180000ca0b0b20303020408040c0005400d0a6000300e03002241004840e450300307014400d8101c0500070000201c3d90381410740d8500e24006d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 38814069 1250 38812819 38812847
    0x11160806011509030210030b060a0806031905150612070b041401020a0804120c1a0309010528021b0304030f03090806150f0a0810021e0405030d1b05120901 68
    0x5042845082c401c0d0402d0012040380e0341128004411509030900314007410444c2c4015801003c04141307501c886030400c2580d07110b010700b501201e4181c0c0310803e808000540c0400050010b0300045075440310b41c4940c0e02595404003014108c140740e1101300b141903190140c01c0d40051510f19003c141880b03d1101c55150b1015207030248014008103807075466150341c074441c520422900007a0600b2800130002c2507007034900180a81404041800060390701c1782d81c2c0743d00c1114080125460080041c080c51282c22030751400b102c948000c0d070260422074050800a41c03051008282c0d1040b0030b40701040001f07003000108080c600ca5850840540620701c3c0c054111401d5803c0000309800420812405a180c540f44e0500c1c414100c6030312210050f02000715000309044c0c1c0000b030035400750740c89030201031001d42c005200110942c10f5441d046007c01220000138000e500600b03616410501040103d54415650700710078055090035084225642e07540c20307180a142880f909001c2d180401c54840c2582c0080c04c1941c104 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 38815319 1250 38814069 38814089
    0xa0c17060f040803010e07020a08030a1406030a17090109030c030c051002010605090403030c1106010306060f0608040807080306031609050406110901020c06030910020c0a050606060c06070f1116080601 88
    0x20802d9510794115003c1400340c424456200340c00200d07803038400c100720703045581c116001c0d80e42ca0801d920f8203c081d000400700b05011841c0b50020549030300380051410784e865001a02c035848200c10300d0302d5030b4141e400b0b0040c1034100941004007101041181001800841c4140c102c1480646400f00b41b2108190110582041da40342200402094860b0300e11194010792602d000074098035442816030f46201003a18190141c232850001001b001035650004c3c1c1071b0b50990300b142c41441c0d950401141c03000713021100144001010301603000040d04440103035400160040c140c800e581010001000c120660368008400c864603601032000b8001ca03403250440301921021818504018940041d5688810020f0140154030010005412110a009491140c860008150756031800c03440740036903841d886a000e503128003a20020940d0f515140c0c1c100c0b81ca002585000d4813640e690401d09035000c030740d0311025000780a1613200d88110700009000f0024130320404070b56100074a081c00740d664039142d07050304483c00300 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 38816569 1250 38815319 38815321
    0x712080708041e080a0e1504051c0f020303030403030207030e0103050f13060f0903020a060b0402070b01120501021908040311030c10050604060f0e010303030b0d020d02060a020a0c17060f 82
    0x20a51100040c0d41c0a40c1190f0741c1c05a050219100c071015940c00c100184c0246004220190403541c00642d01601420481d800510420002e13a0910070384124850250720421506910b0000c00d44601860302c5540101c12040b40301000d41c0100f400c643c0221401c43c0042d90024155007010b800c02408c072910082842c0810403883c4c03c04404140d1400544001e200c2c501d844482401c02c8015040a640c080310300340d00707010328426494041c0d82c1f18051030084404909000c00d00c0300078142442507600305a0402d8142400d030b440e118489140c4c3c50b460b40103a500d55001c102c02d401100d803410189030115907d6980660740c2c641420010103080f400f20000c01e5a81040103150150040014280100158810005420f40700c040001e40204900d600c0500300c40415080059100c03080c508080c1242d009440502c15607403500100f01c0790408514000350b10001c2202598003600b4030300054180d50581d03004a54101c0a9510341d4041202d03554048004101c0000301c14881c108188000c0e60400011644168a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 38817819 1250 38816569 38816581
    0x1306090c051201080c01090504021b010612020a14060406050c0313060c06180b0a0209030c0a03030503010303080c030601020703170721090603020f0d0c0909050903090906030c0a06180f0b071208 85
    0x1900309034848c00d0710481e000324002d00c00c0e140c0c0c1d40d1407103201182c120003081519540c1c204074520400d804000c3e845510328040001c4d040e0741024001c400c041d07009203c1c074505800c100003611581c00c00c011050700b80c4014803912140240300c8643d00302030301454440807034454191030308a0946030b0000c03034000b503d400340c212711002408010340c458211701101d10160300c403100c0c2d20210303181121256810794014038100e800024141c110700118140c9000e40d8800c100c555440301440c41a120985116006038010070040010904590b00c9503041c4011400e60392405049840e0303d0425881e428042e80359501c0112840400c0345c000300000d000704501d040560900145c3c20004c41103000308080d540680c0e88400300d011003207110300ca0100182c03000c2c400421180c02c2024070140da80c0c100a1507580101d0032100455078526001844500045000b00203544060600800b200c14000c080c07405030180410a90204e1440003284014005c0c1c100000d446072240304a0a288100350174880090702480301d86414001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 38819069 1250 38817819 38817827
    0x512040510020f101a0303041203230406080403030618060e1003081801030b0916030c110307030f0e0303120a0f09020a0e0606070f030f08070212091306090c051201080c01 75
    0x282504c10f03601c0c001402c24042103e40b02c001240071103264140000580410002501584c450b03006000395a8804400c400e0f00c1100d42d2034104002980e110074090008004040c86000c0e5554000c1c407134500400c00c1ca42d200c07150a510786182040c040000d03181c1106011750080403120030341c008c000821002c1c0303503451a1501c190301e2060300d014a4071201485403090580e4029000200100130207064180c840ca041c44a006010101111190003e420119403109807441100302202c03129450010b18030f020380644d800c1d900100e400464000b440300c15141d4801c0b594050001d401034083d42e9060003560300d00b83c00030b4011504600d503017240365841c014000e00941c442003d80c2054582d402c038075440c0d544034800050440d0240c810001d00310003200725400101644825401081203850b114501030b600c0b903607402d98498003802d80038103052105008012030361a044d021101f03401040c0c0d200149036500c607c0b0840030307201000d90200215034006100e180c40440002002c0c0101003031030180a412804200081c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 38820319 1250 38819069 38819083
    0x33a020d14070501090503040f08060a05010506030a0911060a050a0305010b0414090406060f1202090a090b2202042a030606080f150a06020d030e0f0606120a0512040510020f 76
    0x1041c1403004030b04441002002d601401003241c02c00d04494031143d50313a5040724468014001c0c22040e000b10008550416214000c1c0b50581d10000c103850b085565000040d80104045007090354410000d44014107a82c41c3c40005001085460391031507a2801000d4000e0199241a8044041440108410440b190202e1010385400c1c0c4101c4900130f580d00c80342032510251420380c01c403001d540d1186070001100c00444e00f078003281c0d13403003524003036001d43d40d5003124070840b05403042c05041349002e640000c000c8030014004498800b880c0150703090040c40c0b500450100c58100c412800004c03800c44140a00c2c01654801e11020100c0e8030301070081d14107010005045c00405008010002a040c01188184021042c10500c080f00600410b00340d83e0f030b402e002955041085005000b080c60414120038000010400c1c0b0a001c4049009008a44030394050122042d09100c01517a103000d40c0740e2980000741c0901444403000440070a190302c80b070a110401c48040ca0f040300c5c0c182503511840b03c0070200c0d1000718040f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 38821569 1250 38820319 38820347
    0x60e100c050703060e030409050c1810080a02090102120708070201110d0f030203060402091206060a09140f0403180806161d0d020604270f11030c09033a020d 69
    0x1c1215030605c10524613601131a00300d61003460901040042c0e242e000e0b405803c18901c1c002c15600c0145030386090141200345061a0400560038200049403140b10f90000c040318441031040701d0b407610a003000703c4071541001008031001100080d00c04150b607403208c00242030011a9001e07000c00d200204000c0c101da45c03401c0754201031640110000e000c640c0d4690544416500243c40c45160250007009035444e401c1c112180c610544464001085030420f030300c02c5031181d03503c0c0b00e1302915139114034040600085000b4000c45c100b061a110354102c0d2050001050000c0500800800f01410030009124921050700c0c20700c4100060f002480100c1c503030410040f0441d800a0b200380e080640540040703080c5125079040f0070f50841c02644251411880c003024a21102801c40f030070040003074116280415034424140c035021914040c000b181213019810f0083c462180c00504403650b03881011584210f03202054182805a880442c50f580a180489640c2c9030000c02803002d000410514503010700580094814 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 38822819 1250 38821569 38821571
    0xc060507031401080109030f110c0402070609020604080601090c0203030c03010e0603070302040c05040e150f09132909010507090b070203010e031219020307020706030203090102090406060e100c05070306 89
    0x128400300d00a9010301956102c0041c500455a1152001800ba01e9240c0c0c084000030f41da5050360b4030252040104032450800e000c0600440d003025010400a908908070645510360340b41108001691541d0080c0003d24108010301021b40c940b1048804030b034044035241c2c09541041003041804c83c00c19044034150703040d809040d58140c4482010a16200c16500001d4001d40342c029070091042c0c00034042c10440304204074a0113180c2d100e4441ca40700400c120078440d04141d001c0c1d10000e41c1d1030826a860f0748244070704a807a140280b9501c0d42000d00d80c41c03440c00d50041c44500c60903981c51a00e2840b003544100e0050003488681003200004003000740ba0f01ca000d40c2c034200800c4010841d41d0a40201fa040d1098a089070313240d20615007000240c000a60b00a03541000140103803d00d041d15000b40c0303100b01d5860b0083d1403203614240054000c1d500041c54840315541c20424642d066450744509405000705681d80c0108042c010248442003041d44400c005220741019488001080000c2c541c05070b0f035010b04 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 38824069 1250 38822819 38822821
    0x30206030f0a021c1d070308030109050702120f120705070507090507020111030115180b0a0c030e0d0b06010305010504060b09060901030905060405060402030706050a02101104080106030c05100f0c0605 88
    0x4402402101112900c49481d4100790700401501c1c0c008200d41075905c2c19102c50188241d02442d41c0d43c143d4400188003400500c010025840c040d4000355005081d801510742c024861401040e05078031800b40b016220002080180c0007035400c82c0e00907801003103130800d10310309100d5440c0e40c1d688401c07502c0b8802845440b40002070b0401c4c801c3d0800c3c0c030480360b0010016101d5131681503902c0e451200c4c4100d840002c64006103c2ea039424011111b504868495040616141082c0300c2280e242c11160f9040e01480540d4069480584030030344803103030f854041c2d10300146d90700b0100001020f42d0b0040c0e008a2007a400c040040c00886810811640c1e02541201d00c0e5581b030049a0042c0d000e015641ca024080d405024100000d0100203e14148140d208400f900c55140e140d01066030f0501885601c08016400003502c1810342c1402c0c2c1c00550131440400d4050304055035580c01e9829682e880d001281c000c614001c0421050400710b107201c1060700e40e03003032010b40010b4526004244417407401c80a00101e403500 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 38825319 1250 38824069 38824081
    0x180d0302101104150804030f030b010e0604181b09120f06050c0a02060903040303090e06031c0f020705030604030e01141201090504140105010311061c020a020a031206030206030f 78
    0x3000c10301c1a0251803007030000094202d0a141a60458400c0034100100940701010980c422070000e48a0b641c142c035010026000c00c03600714020104255264180584446002e50594400014200070714802c40c00a1298000c91590010780704405020b8490442610402c00041d422945090946611101c0c41640c10081d042000100c040c0050260041d8601402c0c020411049070052901c40403c0c1c007140c00c10307105c0b072001680d2403203144006000101421000e010300c50740303129044d07000700c0e004080f0f60040711203600000803100e0002c4520042481d401070005100e80502001d00103210450182c11203142546018020122107283d0380e0400c20b46d034200c01c2000c0c800b072060710034035840036003405115070711054020010b102c15607040e0b480512151880c0f020350340501034107060b031307a205c15814691401c030b0042c010179401040006400c100b0030101c0d110284410f10190000300c0040d40201358504040c01c014252044500150100781c0c00c1c4082400961208000c807600b0490b1502291025900d02c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 38826569 1250 38825319 38825323
    0x7060207090c140a0804030212031302040b030c03101e020403050c01050c0a05010e0604030e0609030a0b07090302030a0804051002030301140f04021c0e010608010c021b0f1c03090b180d0302 83
    0x500c01030f180e8010302140c0428103da00042e9184960f00c00d8003160400e0303055810b844000d00040310340404281107103d006005007003d81040ca10f808018044071155140c080c002400e00c0c46103c0100e08041d6182c541c58004060384c00b80c400c028010030001c61030039040d5241c05845880ca0b18406040c8000040c0158401400304181c11150307070010001c1001c00680704030143c5840d401c0d01c0550010382011081123a61510134100c5045500050080002e50300f40c1c0c1c0e40344002200140f45501f8044000c10001c00f50b2824800003010911560700583d84a050104100c200305000a00004643c428070040c464030030540021000950111034142100c594900081d020748500c031040740c0b07404e007036030001580c1080702c0c0c00c07007000711303902c80000d014143d00e48504600721009841c00c240103a001596518140c03a1071070b8000704260303015080c0075685001c1008144046c0001c080381080860034690b6105240e03200340f8040143c020004150b1905180c604400010a5603c08480c400d00c5001602c0d0201802 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 38827819 1250 38826569 38826587
    0x30212010519032109060306120b10080708010519050402090c0c120408010902040f050c0702090603030c01060308030a060e01121203140702010902120109020a0b03070309211107060207090c 83
    0x4054160030141c0075500e0108114180080000085089005c0102d1503030302078080c8006031141414240444001038642046260000d800a0240100038070041840d00e400c5c008500548041b10012506003040d250100002c19440040e1300381900e48418400180d460194441d0030008070748040e0b440d204803031035190800c0b0041c10140704070034001400184240041d0400d451580c02111b041051002800d40b00f000d42340c0031590305d080e003442003054a0041c508400c00c0c030f400039030240859051013259400c85007101e40c1c039042070382c2e00707000407041007441c001c1340c000d900c041e111078401202c1552414a0616003950400b0000b800d00413078004240ca03c40c0b01e40d000c0700401038015640611828100c0002c0d009090540003039000300421b1000707022804050140200041d400f403c401845840c00130441c05580010b49182d003016220350788400421034181d00300d004038031003607160b410205541801400d50303560310040f07074035030b40020004100f0280c022422200311400c1803404604c00113144821079003461 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 38829069 1250 38827819 38827823
    0xa05031e010909330e01020906040b030f010f03020109060509030c09040b0a11090f060c030717031009050402150d060512030a17160f0e120a060c03021201051903 71
    0x340500002200702c000d80002058a000c0c8030f8209210000c0394501d0b28030b1a541c010840c0c6290904a145035864043d884914184006000141060020340004001da40a503010000000c0c01005201c0b4030300c548441140101070322031246144620b07550002c0d10340c0343c0c0ba10510050040101f102c0301c09403000d104070104480c000f490880986420316154010200a440c000318803480c01000100f200003a10440348400b900400300f440301800101005070a40c1b10304da00450720701044c403070040000c0714140341494001c036200b1401c1c0c80e41740c0085200c1041d4440d0380081c89013070500c0700b40805078032070203d19501010f036251510b940c0e40e400d80b107200c098282680013541108681c14103900280020002d040c070001a0794542e114012007032150707982628159000c51681100e070881c104206c1c0107c10003c0c0103411070070f0050500280c00001440728144007050001900442d00003c10080e0a10071002c030000e150800310300f48088038903140e00c18481400340d54001c4002c40280842d41c58694100310080da = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 38830319 1250 38829069 38829121
    0x408070e041e06060303120204030203120304050a081c110307080f040804080a050303060a080106150f0905091f06050301120b04020a091112130f0615090e0c030c090c0a0503 76
    0x400b00d1910400070406480140c0000c0d180c403805001441d014000c4508903500100201021200e00d03c0d02c400c42d40c40030b00211601d106010a207400514920090401003005544030210804a0403e41d825111420740000d200c000c1003040015403a044144640c1100c103a00100d0643d07540c0b882d00701c1d45071241b034116008512500d4a840c040200010056225001c04d9030040985580c41d0409800da480c2c40c09441c1d003000708411410201442100030310100d0100f0329201100c1a82c55010880101094540e402042e20104c00000d060224048840040080b03141c041d01c0d6602d058822540c0a25001c4000c007034159a40208040d90313680120b96010b0710104408120700045020a59199170012490b03000c5030380d00100040e60b8102505501d00000e8106155510160340c0d96605802443c2d8000d041c0d1906010803c045006030044c4582c02c00c4d99000c200810f05c00052904051410b048040001d100b1203032902040140104842512040d0545080190700c0346c61300f040008011030000d0b0414080 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 38831569 1250 38830319 38830373
    0x1060b071b030209040b0a060e040c03060e0d0f0509040e01060e010807080a0302120c011407020105010815040c0902030405070b07080307090b09100e010207080604060e010605060408070e04 83
    0x86064a4000e0008610036820a41000e01d00a0020820000e51002a510404610020b40030903010615164441c1c06100b000030321a484400010b412041034900340c418030309016080c801c000701ca102d2503105a00321340003003100c6003103142c000741707800184022003081101c0419450240d885941001444000c0c550091191176120140b24800c0c0c030003449100c0d02441107405c0003031404404a601c1400c0e607055409042c45808500d000303401341e40710f0403a07040e0b030359a513000f201c20b18004800491300458030780d030001c181c2d5450011b00c07038900b640350005880100d413002c040c4030001d48a084941c0460f102102c0141e100d90719418030504281280d488104294000540e0314200301d034034402140700b01155180c1d2180c407519114044401d0040c4901e040c0c00022510000304c1c0c00e4040c0701c0c42003103140148100c840098440b04070314100b101c1070b00d0881e943d80d2500700311804140280501c4001d8082620154201881c085c242d50340c401040c800c4200308a5641c0105007030082030441c00c0082440442e100c1d041d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 38832819 1250 38831569 38831579
    0xf01050c06011202030706050408030a03020318100504030f17040f03050f040f030302070e0403170603011b03020c07060804150c03090c0305033601080a0905071706090303010b0a030506010c02030106 87
    0x34102090012817203806032100c0841c0e01d6002d50b080ea81a1a4003400a60901c96454002c0e030096002600440f8442c4646c003003e0a0640100040d14042980b12004240c5003400d203005407580903ca0010300c01e110040800c21000d103084503005600581282c564580c40c8014101a20b051290300c00d680036609002501141506000020400b182d103c0c0e802c0341c41d01550341f1704040c0780040a07940100000c0558103600305104007101c5c2543c10074001000000d581c07200c04164188900000c3c840da0100c2d402290025031001d0510035134000b4072460a000000c4d01e002e5440c039540c241c00941c04103082da90340c012410440d1199100b8034105034082010300190791a400c080d40d481d00007c03507001107405c100c000a8203140c40785c010000100c843c06403492990070000c006441100c0000e1901c0072040e607500c1240042003040040200600c1c1316811103500303060190300d050030081c1c001e040191503407040004001c1081c04400b00d800704841d610b00000d43e51104801210b0a652040020754150f08040c0d02040d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 38834069 1250 38832819 38832839
    0x1b01060605190207050108060d060e010218030c06040602250510050301030605090a05030f0a0507020a030b040309090504031e0e090907061101110d0b0a0b03040b01030b090c0f0f01050c0601 83
    0xc07002c103407400100d58501445100f281d4a40b840d015050010b0308100c0071034814140040484000d82c42003102244010005881c0d500f243c201010284d120194000854030604051282c0c141c150b00664506103401d080007000f0355200c9540070f682d400300c007074503038080c4068441041000103001c0092504920000729a130003002c0e600f0030300042e6003141c40c040205141c0180095103038a240c0d80407019500b800f40002c0c0791030300c94104001e110107100c0d08100da600181c0d110000e0308040e40c80342d5004049401c1500b00201080e4291300006e09451920b02488082500302030010f5507600c0b14035014a2080344403600b00e0702140d02005042d08001000309000d60b05401080342415940503907144010110180d594600f610803426011b088000f04102ca04100384d116013014140e804040e01c041100d940e540f994031040d134012103050314041d03024401401040403000c20710350042c02034801882000c6080d80001c5a82c0c0751420b405200b107503605075444141c1d024005813020f0743d10074004d4032455a941c0301151 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 38835319 1250 38834069 38834077
    0x904080d0f0b0a061b02060f0904050901140c0403031205060a09020a020609240a05060402070c06020102031509010803030f0a0b130912090b030c07020d02130209090f07141b01060605 80
    0x251140f8055030011444910656200038248003d000710780d0300c000c01e40c0a020b51503100c20a00001c44030704014104150710340e402041c1c0034030301000001441078400400c10803000ba001c0e100c200d07038200c1004204046540680201c0d01a80306c41b4001440ba02c2d00000078004295a80c00040a6030010400020b09a00032038024030644d40603041d0b51515041101c0c2d290403811421201c0302000340300000c15515640d81c0d001560004018000602c0c0042903225208607089550240c00181e400008011541c107039542d00700011042600c8480031941031802050300c03400020803080c403640c46a000964aa01c130350704041d0060740301400302d06030500600300150161200704010303180d105240086440309441000c1100481d1100d040490031f5403100707503041740c4650260406070390220b0012803107409030fa0345441c0c42d050340a50380c00050b60381c0c1a0509203d48907030b000b80f080c440780010b001040300321504501d02854070000100019a10701c0302c080741c401d000c07140d0341c01900d9562038000003180440d0040020 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 38836569 1250 38835319 38835341
    0xf1f0605101805060301050d15111306021006050607031b230f06090c0d030c0512120601020d050901030f110409060303080f1506070f0b071d040501050d020904080d0f 73
    0x16071401d0f2601c1c10b001107031200f0b10a49400101d41404034020036480c5040348000c50700303880003240ad03087d0020f001c08590000172110b104051600710030030079550100100c00355101103040610a01d8508400550035018101c5c019082c0882d07080c2001144048801c14608154000034a207000d0000c55004081b24640d844005c074148107007401c4800c0c1c00e500081d614410000e100040a2620891081c03044801021070107d0601c40070344064400144180035507000380140c141069140c09000c9041402d409010303040e039041d900412032648490380e1001c1140d098240038240411444014804075000b01106500045c40c0d4402082c04186030070180c01100440703009540300300f102e85502c9100d1402c071009640c01c1d00300040c071600141c014207000e00508003881c0103002e1080c0d80c01654a80d8000b5010880b000d5000403c00e03500010b0180c80180310b12804007065804000340d40c14900403683e2081e81c000e000c0c0c4544000d00c0043c042040ea24111007080e000d488043c0400440d440d003810240811001c9 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 38837819 1250 38836569 38836607
    0x3050c1c1e0f1401050a0b1e0f0703080f090a080a0c02181b3903070c060801080f03030c03130206070501060603141303030b03030405030f0604140f1f060510 69
    0x401000740c0c405210070f5043c1c501c001d007280440c501c3d08000d100c040e403003040b42088001d0135000810346c00680070040d040e4240611001603444805183c000c1480f14001c142c0e41d10240c1c6581030154003000050355041c6d655111600981c0c40020080941d01c0082c00c0000945c412141e07084009503229203101130303009102524a6058170300124005442031300800c0450f070b200d800c009a400041144500d0304a8502c07501ca0b0995402c6010314000d90f0466000e11030039214011780c01c00c1001019846420503004101c030002501c4030445800922b81c49100c082e00c0141204030100100300c40642c04141d4108503940100820f0f615021850020b0180c002c52203a800440d181410f410000c00b2550724052084000d510201040f1b0000c0c7c1c0c042e40140380b115109909403101307002c082890f4034100705034400040000000c1480d03190920300f2900005101c500030040ea04130080c0140815800102c65000d007009402807494000c032100e01c45c0081160f030f441241d00814030324105030300a0304810138600c15000a55 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 38839069 1250 38837819 38837831
    0x1060806010b070215030604060906030605040308160207060815030703030f030506030a02010804060207060b19080f0102120613090b0c0918010b0306210109080c060703050c1c1e0f 79
    0xb851000c41c0500040650451100c0300d00340101d00c0c0c0b1400955001e0070003040001c0c1251681000000c8403c0c40c4c004070343e42650354041c0f10038541c100388003d9010800003607860341c0a486a074000e4554400344603050621581d50089001400c89400110105001504503411640d80341001030550840e25581c0000c24900070208030103080100c0ca1081d040e4068540c0082a152541c03100000d41c00804151a010380d9900000c0c41a521809031904441012090080c01400c114046d41800400020303030616030310402800340c60b50700c88a0010f5021800700c9414811190801c1540080d000c40c001c014a14072408003081180d0382e100e4007030401340d002910614201e03461070608039a07050080c01100c903ca5024000140700d45042980e0000c11071008071905038020b9080151400d480a824044500080104140c000f082c1e0400269920080ca031905014a04001040e20317107520801d08100c030420f9911012504e00c000e513400041c240c502d121905910440700341c03110001020b40401e0b880d00681440307 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 38840319 1250 38839069 38839079
    0xd080705030c0301030311030702030d0306061202070506040f05030f130e010902030910020a0306080303040506010303112b090509160801140102030904020a030b0a060503060306010509040f02010c050f030c0106080601 95
    0x40c06503481504002da00c2803440c0d08503141a1484044902d03607800b144402c00c41140183c6040c02a1180b20525440c0491031311304040000d4000c20080d200c0161303d51050100c1c00200f040050200d4200c0d80284560100781c1960405030b007544588203001034141d50000da046614000a8050800c642c2202d042c04980e03605e070000141030380300a903084e541b580e100c6003980920041c1680144044a00c07400c00094490f6603d02d07980c00c0d5002103606440c55080840100113050b0046441121040303040040c0032160010302c0d10348a030275003417000b1b240050030506909440b03900548101000d044002c00c240741034605540a00114200e0880200000d070a80000250880b51100c0c48007941d50160007030740c00c100c040d01c10701009411041100c030070140c81c0d0640c84401d4640a00c1100502656030b81d0355600d02e03003481403520340081070303020394091041e04040001046401140c4000c03a0340c246804480740d509400c0c110310b4100000f01000e41d0b800002856064140c05600010441d84802d090b10203030381c0d0b21 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 38841569 1250 38840319 38840327
    0xc03050601051206030f07090f0e07050102250905011403010c0201150b0f0712020601080f0a03052a07080c0a0801060312120e06042004060321030f0e0d0807 69
    0x16140c15002c68418800030560000b500d07103095005a014003141c030119a190001c62502d505540321094042c0d8a004074100420345010300122104018020444189003400007035a417240c0a012030b15001459803400d032000f10022924004010880d001d21540d41c403212010b0300c0c048081c41e450b109602c0d10b100781103280e0060103207084e444032003030420305001d18010b25106d83d50301c80c54040190f0302e070401403800021509d50114241e090750ba8003c007429818008060701d01000b0084040c41c0760701030100c80780040e52020450704a0401e90003882200700b80d580310220040d1100d04142c0640c016071901103209240002d014090200c1241c0b034200c2c0a584060803404c80d00e0f035000141c213543c25030485c585070b280280580704440e800303507900152100c1400d1440341804e80c11342e4100c49184080351001150205140141c4500c3c7c81180c080161302c0c55a40d40c950000600320340c429903490354140e1800014001c0e07120f004402500c0c04180550461811007980303072a140039040010440d5480800c80d1a445 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 38842819 1250 38841569 38841571
    0xa0b010809061302010203091f0212040317090d060c1805150306010f0c0501050f04020103050717010612060b0301030b040c060504030506040206090411070b010f080a02150304030203090d0c05040c0305 88
    0x800c50141c01683c848540103401c00800ba4401d82c15880200301c590381d25264500d550b451002100182c21016a03942402030a01c220349505c0402030f4800d01c020710100d0004034a82031107242c00c0e0721250303540c502072021038480c410480c0c000d0000b130702e404110410150091000748000b401c0222801c559078641c01002402d102038100d00c051060306000040d00fa501400150201c0320f8141444140c1200903580c241c04d441e41211807c40e0065424144001c5580600031260040c855080c109070401c3c405c840c900303008505210350810045060b010280304250ba0340428040c0000079406136481d0703101c1c18150744540055074101d42a000c0d01e940094072511401c260b8040d00d0f40032001d02059122038080100340d41200100541c401d5441e2240c91002c103021004201c440c1c032640b094030301503140103e0703016402104c2d030101107507820400b03151700183d4511440c105014124040280c1305d40b42c0c1e082c01c03459409401c40c240e0b008503d00406006000c0729007001c1c2d04851040700c1c02d009008524400701d00307980d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 38844069 1250 38842819 38842831
    0x504110301150309080d0219030501031e03031e021c021306050309010f06090e1006051c0c0b07050708060618011710022a0303010501171504140a0b0108 67
    0x110900050100c625814071900c001102d924001c14290760903105c002d815405290b050b0180e5500081c0200c4825100b0700310006042641070411080d032550b100c41c2036061003000d80070310b581c900c070b0825400c01d40254046011321807a845074451f014124400003000354044114a8041c4525001104c071220ba09c0c001c65a151615581d03900110346810400d03180f40c0c00203800c098482d52900c052102101d40c3e40b2450000348644100441e005020304441400c05201c48100c0c0c1200c1c0c14154280215110001940c4403810320301400c803220031150414190f0458a80c10159002e140017074030009101c4001040410f403280e0300709490890710380d441044148208862440b8201681500405c0008101c8000c00d49509441c1c043c0e0f41d0019020303011500300e9002ea103005080b12960381c1c01403213903040d00001051169041005514650510001a00b449c1c80094803641c0d1198102c005490001e11002445108801920074441107146007d5a00b0010084a6580b50189014444bc5a03580f2403400140108 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 38845319 1250 38844069 38844101
    0x702071505120403091d040201140708040909080a020d0302161113060b0d0608010603050c090709080d05030411010302071520070c050f0d1a15030303041b0504 70
    0x91420100402032800115450140036080c402c0d01d09080c1c44448140c440d07440307555071114a605082060451440c3c1405003912126581d042000603600315000002000c00c0c0d10055444401a1422450a20850f00051410b50518460208101c4c00d02d002c2d122402c07098007518172140500104078102d00482e204003540b094031548103c08905128503003030104901a206004014000c2d103060151011036012034406000080c0f40e100c54208c500c200805054900c0c001d00860303103140c9840d0f07aa1481d0050991140101502103039a01d809a50301c0700c01000a001556800c0e43d400102030205d420448040d40c1c680340c500c0d4a004d907580700b80308a4040b40d03806049011006100718150000785032400c9420754a01c40310343c014400a4007480504502d074810660581e400b401c0070144400808a0801b541c0541100d41c402d0340041e10b0703c8060490000c1400484095645402c200c241da03040210380d081d0140400014402803159400140300a0b802d1069400701013a52441800120b400c1c3d8164450b40d0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 38846569 1250 38845319 38845333
    0x20c060903030717040303290f01020c0102070504270602030a0f0c20030408250905040c03121b030807030c020d0914040603021005030103030905040207020603070806011202031503060109050702 85
    0x4131850619800c240a0314001030244038180e80c5003401c0c1c100e040c0140c000400b965400f85103152142440c03d80002c03c0c03014143d80e626100000c1d40d248514012a4411a03c6d49003096501c0e40d840fa000340782d140d050500c1c9400440c9414030000950003a40e64011660038901e650340c888005000b00002c011185d40c44101c800900c100007a05080c880c84110300900080000060004040184210310012a0002c043c01005d0a40301c1d110049540d100300ca52900300010080030403500152a011250007460410003003c007070f801120400c8880102000da80b803074140d18020f00d9442000c05200f840c151702d08200b0306030644010780e560031002d5691800034500040a004e0f0740141d024101040402510118015031a80e002500e01030f1000d5000000460105c0100141075000c0051401000113440462410540e500810701e03500c0010400400d021240303010401036440344044110583d140f101c03c640b2424002480290028981c61807031281c45004004100300d0110710856014150b43c0e0002d12034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 38847819 1250 38846569 38846597
    0xc03060108070207080610090e01050c042601110c0c0a050f0d0c031e0302061b0906030403020a0c090b0a0602190b060a0f0303020106091b0905040f060302040906020c0609030307 78
    0x48031200400100850250b01d0b000150014200801c2e40104040003007c040c00b030810148201302c0700e40c1945a425603050030248030400e8540d80454081c1d500b911009c010f5081d003900d00f980c40e00d1010508940d2507182804a0701801c40d03c1018009810700c10b000e45030188a00710401c80f80c41c1160052560010380305959821034540000c006000d20b02c181820700722540d80e501c0e002d03c2000c1d42071491051044420301c4404142d4184076017035011440e404001102d0741c1156040020b030064004060003850000b0100301854020480501d144d0f07400700c1b4510303a45458140343c00c00760488000403809462300d0000410718500220700504070480194001042d060b841d2a9020f0040c009083d840e00902c04501c040b64001040e50701e0009940030340c001080c41403800c0120300491310108407a408401c05040c00e13120303040e40306124200301c81c41268041b4442e0b1003180c070b20005020380c0c2e000941c040d00d845a0b480400545070003501c0c0c3d00d02050107468003503880c0e103c1541c903440b0460b25100021102085004 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 38848925 1106 38847819 38847827
    0xd060306051510020a050c01050a09080303090705030c060703140f040e04060203070f0c020904031211040e04020306060d0f0b0c090d05010b03070602070b0a080a0b0301020a05180301050c030601 85
    0x1881d17a848458441c41d40302c00c420b040010003e42e8a000c244a151034070003a14041051342d07940e040c81280b5686e00c121078481d4034082d004007902000c00d80381400c10b460070a50151984080000300e11040c2600c1d61000d0961200d83c00d052002107400c900040d50a4800c5118040c0180d03281080b440107090b500c00c403000e010400c2031030106900107031074540c181a00030398941045c148a450036a181d40103080c81100500080e00c0105e40010000c90b042d00c041c0c0120b000f902507039a1a1524020310404024030b54000d018020342401d8030b000514586055544807849402480c14480c000340000c08803042130109442c140e448840d0080745117000c2c011600104814002032090a02d40b206c07903202d074081c4036510014441400009200540b4580000804c004028000c5595501c0c0300c40240c925002048a003030405800300c180400c50805110b220301880541d4071050556461000440d = true := by decide +kernel

theorem cover : BRFrame.Cov 38669069 38848925 := by
  have h0 := BRFrame.cov_init 38669069
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38669069 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 38669069 ≤ n) (h2 : n < 38848925) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
