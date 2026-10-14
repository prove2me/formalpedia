-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1928
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:11:13.839531+00:00
-- url     : https://prove2.me/submissions/7d3817de-ff88-4326-8aac-5aefefb76ad3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 346582733 ≤ n < 346762589 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 346583983 1250 346582733 346582751
    0x90405060907020a0f05010b0303131809020d03050c100213060824150715020c060601090303022503080406090513020a080f07230910080606030c0304170705060406 72
    0xc06114802e4880c00050380c410021400010a4080c10341d00460003600002501c0c084040801c0c21075211444102c02030442c09000d2002100241000504440c003840412000b680740d408203185141002000e402d1000209400303c11103000c01c5140704a0b41590704c02e5490780100c41040c151910745014240204074618005440740c0e08101e510b08803460003140c40c218080d4040e0a000ca0500c0c55501482007090400ca280301080118070552440040c0e1a170044e9130358600c0700c0c600c0c10580702030011810000103081c10008250700065211039900300302c4100309540711415040041d04820751000317100120110740014100d070441c8000c1300b22348040d02d22407402c116085415007244650346808000c80d031280c020405020908901a9001e0841e080c8000290180c1e035455226000d800c0300c0c1140d5000010751003049007000c2ca003412003011541050802c40c100780000450a00009013901e4036284d0100015092118111485031510082c81b6100c1c0e9a103004d09155480310800c860565a50341081d50038 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 346585233 1250 346583983 346583989
    0x140906180a140103140408030a0908120f0f0906070c1e022701061418060906030a0903121e020c0a08040e0a05011d0403030902040e15090706110d1202040f060509040506 74
    0x6a40f10741c0d03100c49558551b90710102700e4030091004140c15540c00505011040d0301101800c04603019030368541041c50289011210110300c468001c0660840d9045841032155598014032900d04041d4003d1010041000c0000b42d03150703608189201a610001e074103400030326904007640e0b43c220700c110820500016030300c0b01025640c404042c8019219170b03404000e294040f000343c0078a41d403c41d00c020f003032074640f03107500c3c000070320907007059079117500c1c3c55903071035030310007010780101c1e80c10280086003209001c402c14004246407908007a6410018558000911401920301406801c4e25583d0220f9225212030b10b4511280118404440003212285001d00100b008078182000040c0c0c81010105c0c0e00c115030301d036075044025111a450072600581c4408040850102c01d0050894001d0300b030004211518015946c50315226242d0b00c40014402040b8010030306020201c0d013030059800504040501d00c03114079440000b80b24940c0032600724843c01e20081481544a0004e00b018042201e081c03100351552010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 346586483 1250 346585233 346585271
    0x6040e031b10051e060f0a14130b06160f020604030804170c0d1104060906060f141806030c040b0a0302030405010e07270f020c0c030d140906180a140103 67
    0xf81c02c07a06407207002842c0ca101480d44c80580d00110140668000203005004a2000401500141203100c0c140c15030300254140000172030480b031040b48060000b070071030380b0106130b8510520b04280051420817003e0000d01c0708016003803103140e60152950b680d40b5a2820400c2d695005802401294100188441004100003401c505580d40082194652002e04c0e0781d00010100040d030101c0e0403e0319203000290040031031003070400034001c1d519003409071000b0782e80c02452060f50326100c0b0b003030000030b0020610080203100650303075010056079115500c2d01c484441204600480d0300c1000d00383c0300000c6007140c43c3d40c50380183d4010b9100b50020720040510714840742c0c45881c14024004040c200707408071650b810050001c0000c10100c10000180c00002d0801c02c400d9a1100000c82c042e0f901007058440035050400006100194070701d0070751412102840c0c001d1b4180f04e030921262140e41e01240200d1000310240300305014000051003401d286070358000d0100050402705100d070100c0c1c602075614100d802c010308 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 346587733 1250 346586483 346586491
    0x4080712141801121406190f030809031903020d08010e07080615070c030c0515040b09060304110d0b010503100c020703020d052103010e0601032306040e031b1005 71
    0x2409414441200e030078502c00d60482d440d142c10406284001c4580300071900c5a0001c1c4100b1000b0000285400402c1c025200621140c1d0986c4403c8034108000103040c14540d070b41030baa88404165652b94186d80020b1030110031240c130503011a520564142010f4002805e40c030500d495031254400350ba60f41c000f80c0400f080481d007840224880364000f800f1341c642032181000e08101d1103907003404c0000c1900c5401c09041b160700125868113034148280708034178090320000d2200b0f615206861625083c541c002c59a030142e96080703406440c020001c24200030454403c01d03154136002d043d20442c89039030f007822898502c1c04c1c4580c9010307000c5c229000c03548801900030040041044d80084c00128950781c20b00411400340eaa00380d402d030189a4404152a03401c11006005081801025413654140007070340600b00e0300a0302040c141482d1400c0341c40b81a500b000146507010340d107500000740350303510004078002c0e051a605c4007005000c001b6a400b845802424010b100201400031a18403c24854880080b15801c0e1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 346588983 1250 346587733 346587767
    0x2130e150d0f111c0606050f03070303050412110402190e0307151407170703020c0405010509010b07050a0203060109090b0a2007051507110c1509130209030604080712 73
    0x10291000300384151640003d40d9405410a4002808464030003800018808119415a00c6034800c02c86031500c1212016440001c60150010501c2e42e43e0242152140d03105602c8108884541d040038094009082c4146140240007995580382d0104074400d10240d0981050118000d000c88502500780083c0100030b40d4842c490303400c40745200540039100d0031030701c0c070150480f440104500c100041d04a01280702801c00c003000305480d1543c0340750207401e050041074218052454600100030070ba0710301d01c400d0b0450303131906101c96072860301d400c0c01c90038103002c807001035010700c1444000100c101480c0c1c01035201b03074051800078426855aa00030b40960b1f4003590310050002d211840380c2402c071100001414030611403001c80d600c06c01340028010034648116140c4010440e40b0309507040e020028062125071200c00c851101c541841ea54044200d40900c00e10309001d10440705600b50b8801d0b0a81c125502010001d0845002e460715241142181e4000341c0c040703800a480b1043c48110358007070064001400f64030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 346590233 1250 346588983 346589003
    0x5040c03020301064d030c0a0212010e060a020a0302090a080318120601030209130f030918020a020604110102070306111923070f020d260403020612070302130e150d 72
    0xf9074944400240e48008070140100c182880c60351700e404000402c0e038400100098610000c0c6401084255281c00030914080e034100900540e543c0c0010132a10ba10098000300140c0b02e1508040c22070003405080381d0160000c00c41c2201207460341000002d0082050170340549201c019248cc140a9180c1d00301d201195158400f50042c001450440c5a055000c40040041281004a03840340e0300c00d0302003107405902003030b800c200c00e0064003030726800340d0b284c0044054154134000d00c4580c0259110401400070340209629809060341d03a20030310900b4011500041d061022000008910720254008540c2c80b24103d1401c24001080b401403400140e80c0c0000c0d0040d48101007200c3c3c0c2012190300c07440c0100c502903c00a0440016507900c00c01e029907a00580d42024215004900c8800700f0401c1e001e481d4002c0000c1c44200016500d42c41102c00c8a00340c074040380ca245c3c82d001800e4010380911000c0c44010440240081100408059554403442248032840c0340ca81511081c03000303081800708090440482 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 346591483 1250 346590233 346590317
    0xb15070b04021507080703020c0d030e090907080106080102040807081908070203120f030a050a1803110102040909030c060b10050315030715020d031b02150a0605040c0302030106 78
    0x640809603000b070002c0e000c10900400c0d0070791008254000703c0101c408040104048083c50360400c551111840c0640e003108003030440c0d0318043c00310300d1260803181c4520240b4001686842e03003440a4001032101c40003c3c0003068485603403a01030740241c0144185403207419000150300c500050809106101d10030341010300400d41e1600e5060781e0100c0ba051342c151040ca03410380b1048001c10001c1010003004c00c2000d0f22401c103010301c0d0b001c0e0b13a00034040c0c51902d414440201e1803c00030207070220b006541070505071020100401c14070b000e406103502c00c040240c5801078483c103043c0c22a00780703040300d0f20a10041015880301c03c20418100c64219999002600c00e00c0000c114551150116545007401400c0f0341e10241d40700b5a54441810700d20562006801c00d80d034010340b540d014003030010b06552802d00002c03060010f031402907507101030b82894103022005001040301030002d80e000c1d0002c0c010240041c0108102c481000e006503100380b040780001100d0168011542d002140351584001c030b1224210300e0100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 346592733 1250 346591483 346591493
    0x3131a030c0301050904050316030c0212010b01080703020a02010e060c09090108030c10020a030209150d0e01060503100c0c080a0801030c0b0324010504050406030c1d0c250b07120b1507 81
    0x3c0c000d2041f5200d00c420410b02d19180b00024030010070b14480d60f00e01d82c01d91114410f100c0629542218500542e0500c0d09107400d9070380200000d640034410f440c00689901074420200d015141810002c3c415014034800e200c002c190f0540107082e21081035550f2005a642c3d445419564442c03140c915201e60040c031042e403411741d0306400500740c0705014500541040f2403d40001c175042d1301480e46403498030700050580d0b0340100c40d00610b59442440002001002e10b0080800c0c1c0b90703403102030700c1e946451343d404031040320b036020701c02c4c140c20107400c074030803a0f118044020b001e40700042c28041981c1c0c0600c0385000061701500d640490b0701c07075082e800b2180540c00328100d140034a450059040c0c1c1c1802000d10000c60f103030b103984c456100158060504e079004585084103441003c00f58244842c8890040b0003000303581100501114001243c8044010751120443e1021108641010b001010b00d20020184141d2a034002d03c2001d804200580c00c10401c201c1004000400e01d401c0154104e56005100c0b040c0441c0c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 346593983 1250 346592733 346592749
    0x90c12070507080f0a020703051212060f0a0b040905091c0e091012050a0b0105040b0109120203030d05040506090105071b0803090c0a030b04030e09010e060405040204090503131a030c030105 83
    0x502c140b07266400c00104456030004d03a040200b80c000141e04c4070030100203000b81081041407000310602c3d40da2801c1c2425906072000c840040207a40607803100e00810282e6100c0c000200000e0800610980d20745448001d500050202550505941c1c49810300e141c1d00e05d9440c540e1007a0080042c0c60303d1000340c00d5007090003008030009042c04001042c0355000601840105c8002c910148200043d000d0400149060101e074407042c0c01140c01a4a040d407200c2190742c000341d140098030200c0703802c00c0281035180300103032079486901c900806441c2004280b20800200180b047d0042607020000c4c085a035580c50100c401d01e206400340c0c6400e40110049001140c0d03a00020350708807a146096130b61074440b040c0402d8400c48076501c1103c02002e4942007006045d44512007a190500c101c0b200344283d49071800c10035040340f000d420705200710b95070304c041400c6603100c0c0c1c000d00d0070580c401e0960361a00c110040740e00c00c0e029544203060300070b40c3c802000e005408044040764030811400741018110790a0a05000700a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 346595233 1250 346593983 346593997
    0xb042d090506040605030f0d090801050c03070c0f061a100807050a030207031e0915050a170c09040603080a09090b0a0e091609050711030c06040b07050702041a090c120705 75
    0x200341d13141d0011a00e51814052962150110801021511a50f1000410542c1c141e8008541c03a458002440b58034240501260b030801d0240c54002280e02c4503040812611429200043c580e0346030004035034088080600424000300d048030717031900d50510300da019151050112000350008004001c86440c2500079805085014002d141071480c0250000000b040140080d0f00c00011a440420400001c18010740c003240503409881c0250500800017406001219020075010018540034002902c210140c0203a501581d00184284055a0740b030a00e042c05034000303c400b100041d8010000300b141c00c2140600c0d034041c1006859601094a000019403403032a02420008803801204000103103540c25000c100050101800005194100444060041c404101121403960014403080014580114280e9805a08114041460758840a04450038030034118025801458100a01600303190004284100b0740280c0b0304c8011030703c0340e424940a42c002c825100e40001440e00c001181700c0d00c10006425071b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 346596483 1250 346595233 346595239
    0x80102090d0219030803040b181c0807111e07050103090f02090705040b13060305010611031c0e07080a05070f180c030b09041a1803220305070b042d090506 68
    0x203c3c41d00c030358078551507500980c1c0541e030f100c00301c4090024000326036030078410a040c050300a1000c1003100c401d12152445404128007400340940004006601903a030840500c00c1c02002d590715049243c000c141302d83c2d400d480404451180082c0810594040d22540704950f4201704601c0a400380d46c1d0070805c5d0058000d00b15402c20009010000e920300c084006841004c0e071250018010764203180c2c008013202c005034854010801040725607078003000301100300c80c03411610790000f2500304a80c03054900a8048003180340c005116002c00054004000310311450140c0c03081051350000c3c1d59800a24403860818020007800c3c48441c2c1c000521f80d00d469120701c1001d2191705003c2114411440081c18075030086a00fa02c8204070410b0b203003a201150500140d01056081c0554a0840021314260342c9028850714001240c0b94140c00380030409441c1070344001168410122800d0a031590307002c2c2000e801603c034207004a1080c244240440008017443e10349058003904004246142940d84005402d002d41b501da0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 346597733 1250 346596483 346596529
    0x20150307030e030309071e0905012c01030b040206090301110d0c12060308041503060e0f07111b040e120708120705040302100c060b040912021005090d08090f0114040606080102090d02 80
    0x82c0072a07127402041c1c02004801010a00003601800300500040e41e8005d0140361200c0c0710050002600070001c0b960800e4040d0380145c0c40b00300c4103001c680108214080e1801002e800720303525000c00000e40004070080b841e40c3c1c5515090710102004401c2d190710f40401460540c00f44810f1080720740180ba00e4001302003515004c074200350b50b18809100041c007926121962611002040480c903000f0140d81d000c214504c1c010b040d0100d61527100c05114544000880c03060b0348942940e0a50501008880316202c00415000d56654491900101d035074404d01400b5007581d03c00002542c900d024030169000c503034025151164815401c40e00f03e81042043c00300b115113941d500c03040c28003900d9078414801d081e80300c2d0300b98504412060384080c2c6041448603101600c107051404001c0114404117800c2d680300181c1c10440c51940b10005000d06000315440201039661918100d580c142e00100c190314090b50040104018480c2c40c1c01c045030903480780b5111709030009048070400006060400c450310100c021200c1c650 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 346598983 1250 346597733 346597739
    0xa0303080405120a0507020114030708010306020d0e062a0a02120a05191805060c1009021203070b0609060901030b0f06120d051809040c0320150307030e030309071e 72
    0xa00d05030800320804c8005071001c00e4210840d41c0140a01e104100301c003400320308500e4400002084580140401018035801048600c040c40132030300000c03c040900000e503070b85890080e0780d000544185840058140b020100d0607858000030108407803030060760768090000b8608016084c0b8146d0320000140d001c008041260344205500f840c450780c0c104030541e4801c5d00c003011207440324940c00c9441d04140c0c46080200310102c14070000003003ca40b03044000764081003026450002070520500c1c0000382003130703020000c2c0820800c182c07140303068031998040701e01040b0390311aa8144a40c0c44001d000003007104950b02e01103040b0742c80806800b54000c0c4d004100e900c1a040c00d64100741010b0301036086101140021408500c107044e9040825a400c0080c0c6000846282c15200d0a208806612005d000c81e0448881c182441c2c426001943c00a0f40182c0305203d95000c0518010440d44120b48500c0003e01c2c1440c41045140c1c040f00316409510004024030013503082c43d0100400314140b01e400700c6400d880c45800 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 346600233 1250 346598983 346599013
    0x40c050a0801020a0e030f03180a050d0803010f080d050405011110020f04050306160e27010f060305090d08071407140a050d0804030207060c0f050a05011e0b0a0303080405 75
    0x40140107100000760b2103801c1c4030005041c0d001140306242c400e40200010380d100d000c000068500359046208451601c10005004c40c01c4a0b2103900203a070400099200d6005022902000b14100c41c045550103294941d200c1d106616800041c412500180b010081040190b220721004241c0d03880041c2502d910064090b042401c0b644400440060701e440820700308000d01d0144130b0154018080c1104c2c0c40c07400c05540700244010b96600d001c5104202514400341012984501c0300892407540a0302c56503940c40c0e0310310b0540d0100502c43d000019040c41d001501c1c40401260107903401d00c041e220807015440e1a50159990601e07100c44014101c0288060004590000c07842c03a01400014060400310146003026400d168050903180140100702d401d000c0000c0c2e001030003000322482481c06600f02206803800100c04010700c0c40140003441035840842c11b02c43d040d0b000e840c8030082c4542415201540300115024ae4040300c440603800004402c2c2080405d01071080c9590151194064440c0d00c00842c0c09 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 346601483 1250 346600233 346600249
    0x316030f0e0d0e0a080325050708010209041802100e06120a09020f180601030f020c1b010e0f031b01020307021905090c0301290426060f0c03070503040c05 68
    0x100407103590001410ba00c0e5079800440c5180301c1201500c40c0d03289582040c0d01c01707030707644030310441445080d8012011540001104001d0384103141e2100903a81602d60750b60004d4042e40105219611651800905400d95070244250410a9602404e6820b021185080581ea90950000c01c40d41040d8108141820340c0d580d9144240b00740040c4200042c088050b005024010f0b21340d07494103009a9086031810300c405121002c81c1e5220009103400300c2c011104010840c0a0701a40c114a94944212034079100702d020605101044aa0b0a030317604040031030900b04010519880351000368058021088040c3c02030551500b0940240041c01182e1404800f54085031155901c3d440c001c03030f007059101c0b051110b0702e0401e40c440e03081081070460600f1541851f00f001c10442604045a00c900c03a04c1c0104214031709140103841c000e020a480d6a0040c4d07088a541c2003000e0003040c10848607024100004880601902405c2d0207407a0700404a8203694420305c0955060b032010380281d8420002101c005510380d0f501e46 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 346602733 1250 346601483 346601501
    0x90206040909081305010203160b060102160b090103051f12020a0b042301031506080415020301090207060e060c090d0503120703090b07020f060a0207030e0d030c0c0e0c0316030f 78
    0x91800d940d4205507460084e09035107a04030328119007040000355640c10b081d80c00494040d03046107000318940c84810050307281c8240c20a0028010038142800543c541058019051a44080e241131200d40d5540d418810000d00c4099045a90b0302070f84400d012088600116034440c5202810380000c0c43d8441c01001d04a0f086580030b00c803440b0b41c08800540400b448081c4600c20301c02800d003400141c641e418059110191400783c001001030000005040c0b040c2404455907007194a5001c650702e507101d003034060103940f05417000d41c0d0035802d1485119440c80001035a03480b600100b500103090001e2030382003041440036140240c0d00c5200c01d0001e440c03400340c0d1542c014001c52180e00d000809250340d10700501e114200a1a1a0654200d07040310500c07001701040560340070505810050b603900c03540c0b80940f01e041d1540e0f4680d8103e505000f030201050382184218a01070700030904000e50641d1038589054040049640620200c0c0500c003154605020340f10381d00041c90a4100410403941000c00b81d012036503000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 346603983 1250 346602733 346602743
    0x1b02121c11041e14012106061e080c090f0d0510060612051e0a060801090b0f10120312020c06130204061406091020070303180612090206040909 63
    0x504100d420742160300c07a003001d04043c601020082c5085000030b50312010048040c1800f14581240c040180c11a91500100f054030408025242c1c030340500034445001090450b00c40036a1215103400540288c0031144526826502a443d048140041c807004000c1c030225150484c0e40700700c80c840003400602260a085000c94400100c80e440e00e8030090451422341e5040c082e141c03030035007030203240d1030b54900b101411464840d6100c0d45440e5400182e00a02080d4841d000715442e1031030384010400a5944140180a41344075050680c030f429404481f00d641c3c42c405e58240b0700705030f000c40c000240110042513010070f04400c01420101d040c0141810f10208942c04000005081584421446c291140e00c0262038001c45881b0705101c450041b90140c072a0703c07091071007000c00b200c64448142c07090341c00325255503416035904000f803030b43ca214507a20112404103c02041190445181601e040480d400c1102c200d035803104248a0003c09060007458284010303a08044208000310300c00400340900340d0264822 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 346605233 1250 346603983 346603987
    0x7140d0c12050f0a15050a060e0615160305041a0a0c0b0402060d111902010b0a050f0616030c0605060f0a0b0c0f0313050909070e0103080a09030b10091b02121c11 71
    0xc0545d40c00c41e080240000c0038246842000c1c052103883c0070100d68005000d40d5070480d00300702544401528029a9030600043c10b00138040802c150703216024100710392094841a00201d4120b111004d00c0c01141b030150001034001c6004404503039418a0141c1060020380014602a048441201655044041c011681000088100310400a030080300c5582202c0c2c40200075058030300c40091a807142510a041c03142d143c0141500ca155501d0341184c0c281144003507494292411450050030014640c841558140d1904001454508003200d100307841c03000080c010001e0a050440c0080c8036000844110b01c18030404100b51340310901003000340502c0900c005c1c03082e1010b1a000c2007004060f002407a02d0351a0b08031a000300049484052114156980031a00e1511200c9600080311150400d82c000b03400c803082070b000e0060810004d00d004003914041041409086110001c1100760f41c5818400c00060b803003a2042c103040078000e03000c2c00034624850f030408034190503000218107959a541402c4203207400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 346606483 1250 346605233 346605263
    0xe0d0807180e1902040506070317130804030b150d03180812042c04060f060e040201021b0a03051608070e070504030201050d02040905040507140d0c12050f0a 69
    0x2910100114952048a07800349060181d400a15040035040f408015000305100c0e000d0740c03568065a000c0c1001800c5103884030709034100105a18a02e908100c44159010003040400d21004245040d064124a6040c0742a1856413400660345005101600e058141e447d15001c42d0340c4d4911800c0744500994a4140d034203603000d5940400d106179805442ca50380701520140d90307070000e0380030b44040340c000c18820070113076507a04103a11411100142c10340f00030069500b08010860315a1211030404000c540c00c001d25134a4119409d218076003070741e010340945e010001d404502001c0d0a98000c146001078615681c05e556951005d25188080c0712480e580d022040c0c0510250200300314440080c044e110388030072181401880a065441341c1d000107410000300280e10403070010f1a0701114001c081c0d5480c1004a80342c241030194958400d0700400390180320b15680c40d0f01c1440c1888110000030f810500c8210120b1401e40d0300441401140c01c1164180124070f074003480c5142c2807181203c0d290060150244001c2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 346607733 1250 346606483 346606487
    0x70507290601090302010c080f0c0607120f0b0918010f0606030f0c020c0d33020a03060b040513020313021011120f030c16080408070e06060c030304020607060e0d0807 73
    0xd03000306018104440302900304007607a13004446200141d04007240c00c1d0303a101040c14012503881440c7d205107240c0303e8803090200c06d07a84002c25000c020045142003001c00802c030b1582c01940c00303402d1150750081005000c102c00c0820001110b81e441c40354400042d4620400b000c2c3c00c1aa2034950000010a070b50b08140d10070441d517401651008200b03440901184090a800076040c40c0101501a02845a16a0f080078404000324940040009290348007818003110751070401a60182c03108100080c1417003000940100341c00b06883c00d82e10020804040f10300c1d0581100001d400081c10030004004028400c00075840702d442075503444c00a81e4909040d001200c0c9000d03d0001311240720900880f04001c141071400420050305e070880c9541250f65507411050480104030690710070041d1055400083c001246400001d42604031116000700c17142c179a44400401c90140200d00b40c0d01440c0c5c02c10070000e40103280000050808a106180015107070031548001464800e4810380c0c94040b0300130409010000e5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 346608983 1250 346607733 346607813
    0x2106030c050d0201090608090325140c0609040b031009030305100611060a09050a12030e0c09040f06050439270b2e11160b03070507 58
    0xc05a801c501c00c2c00455000034440b102a100744002c000610010480d000800d0040f18001303241d00c50858085aa60140c441000040c028100d40403032990324200c18030b0202107030f5a03a90b0030009280c981854044820302c400f820700d034400a603260003918110013055600f803142d10607041c065980002c01d450182da94440800007a0000700078004112400101c42030300042817940180042c0002c40d40c003442d8a4070a1030030710040401031800310103441c017a261560540c040d6400c01d031044119800e4000300c50a00070050801d1701c01030200441d1046000110f92290042c0343c102e0301c07801c0d070003101034000001140e00354010b40c0c0444030881d140050248070031800e58000c000c2c0110402c40c02d4014840c0c6101800c107084a003031105500d0b03d4450100307081e910742e0080754010084d5403c60740640c980400301c40d10b03105421401404036655021312103010000107184507044a801820030712041c20f040301c01102d0f400c000c000308200a001c220080c005801c0e03a05140c90700e440c0701c4a1025002c0c620158521030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 346610233 1250 346608983 346608989
    0x6050301030507060c0f06020a0c2303040312020f030c010b0301060605310902130f060509060a1107030c030b0603070501031a010e04181406010b190e012106030c 71
    0x1050900060011820103da100200c60359824540e905101d00d142c030600261881c040500401e20100d02007101980000c003000300f2502c079108a800154070318000c40302150140c002080c490f030003400b0900000d0341c6492100314100c51401180c02003800d515646155510581e150409079444040501d99410309004035805800caa04244e41072801481d03040c403d0407402241811036800106c2c1500311a034032a500303032000c0c1818a0055580f00d0b00354a900750182c4030b501c40c0ca140507100e2480041c40a210760243c8a0031803000303100c146130903040e001c06c0350101a401c0c00c084440c003e04200000003031004640314000d620550b816613583c544030003014240740703540d0300c020305050511414205484402e210104540c83c2401c08107118400400464028110003007007a2110098241d80310520071030440d0628010b01401c101d070b60307580c1c03201218030940c02424030301034102e0300718001101614056038110070101010b14002180490402c910340406050b0344003643c1883d0b0b541414070900c8001c00411001e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 346611483 1250 346610233 346610237
    0x30a0b1023060a05090d0206040b0c070e040305160c0e04060c0f080c090d050118060e0d0e030309091f060504090c0302070b010b1303052a030604020d0b090f010203130c06 75
    0x380c0040c80300403605500c610010f04003080400180110030f40d40c2c48540d640364030f80183c444da48898039034912040c00e0344101c24100651081c075500007035956182c1c4140f0720407031341079540c1c504200c20118220340001046130f0440b00941050008690003000f8050705109a0050070301140808048502604c140486910441000035640c10041068003178001c90307241d00400e943c07001c0010710741e0810342d0042403410456040f4140b400051014414150032592020414106440005600d003505440c850021070300c00703401d03410a0104074458078180c02550384c8040f0184c1c00d40e1016055440c0721401e0800c0340c00c018085400800c0c1032110001c20f1042c1020442d803410b0840c6442c019480d4003400d400144551071007014005080e901d0780d19904c903058029948401145c4941c0281c0164aa021103144d80420340c90740180c0d090082c80c5070000c0c01c1405550050001030111070603441b164049500180246481c1c41190048a00c5203000d00c021441a22107840040113501a842d10305d1134a2130301d42c42401 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 346612733 1250 346611483 346611539
    0xa0e1513051314011401090207030305060a0e060409140a0501050f010b0708030123030f030901080601170a0507021c0c0b060114160507030c030809040f060f060e030a0b10 75
    0x824186070605451189410000706000140c0f510b11003405000f004c82c03d041408005030001645440d150050840e492003520140226610341052207940f1000303101d50801c500e0b43c0c8021076090304103940103c890500540e00311340720420b2a64401d1602e400c280007100c05a56030070030050303000312149026000d003042110892404031103450728002e40c001030244c501d01ca4040007100d0052100c441d4982000030300901510703061060007000c0703500c07500200304039030108412170000f448030340c4180651003503040394680c414640d480e88486403004010041101c0c0651040c0d0f4078100d82030300020304100700c80701c1d0356455004a02251404507640c0c480900300b0350600c03101e42d81c01007461810809a41e055010800a0351120849041151034407825600103004813010b18808002e000c0d002000741140081540c0c00d024081c0c0d40c140c4001112254418006030384002c00c001c1c04264450004107100c49002012591411616244d1700a01081596009026116250100a083c20320084001150640e541ea40703 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 346613983 1250 346612733 346612741
    0x90904080c1606020d0e030c121605030316060f1d03040303090801050c19090302091503061506030a15090507021e070f030f0318170f0109120e0a0e151305 68
    0x6955617640314450300620402805000081d28104a81d5003107070401071205900020001c481525400c0300c1d6a05905c0b40080e95012580341000021117100c0c0e80c82500020942c1404e40715a401444030341040284a9103c54a100f002008407404071101c2c1400320185a80713a2a40c0340240464a0540c029a4907905200c100101070340342c6801c1d03601058901400814801400301c040b900d000181d0802076000c1c0c044c40c1031000c4295103020440c0b09803c103404860442d05c400341c00030107000c25460f245a01c8281000041c0c035003c01da8021044020890047c0b01c08940c580c02c0e98420780d54210b0301d000040e0301c00501500c808090000d62100c5401d403070302424042c0c2c205101903001a00c00d00002e000303c800128504100f500c0b07020420342c0740481d5641d01e6210764540481d10349180c411002010140300d00b6000360712810061103007061082d8081c0100d040500e017544240e540c0707044002a168444542040050440e00340d0741c003984241140f030060703000c40e00d83c4402c1203c0e200b00c4c40454410203107018100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 346615233 1250 346613983 346613987
    0x80a150f060f09030c0b1c050a05010f1e060f1b0b04050706050c0a020913050a1a09030f03010e0a0608070605030604060b1c050c0903160510050901080a0c0203090904080c1606 77
    0xc0986d110701c49056030755145143c1124412585c10548510180740408001a040d5694440da0580710001291841166688030040491010542d1303c16030529055042102038052464a0344420050515202854407100741c20b4140130758940c10780d086c480da0010030041220030f002c1c440280070a41041410005106800c03940c484040d48000c0c045c12140700800c5040460044003c50903a010b02101d4080c506481c05c40d9485450040e4a05840c485002080c0c4d8424044262002402d030980101c0c10350386040721080039007401400c0e07403945a40c1d894010802007001c1c8007540103032000d80c4a0035660f0400c541400116038883d488981410414028080c0d0300b00700a6400c0e0b011580802e0200700344d1a6080b108000380b28034061070340d03d44943c0581c4d0900c036040d041d202089890444442000c0e41246009503550710505181e580041d003a0400106408401c4d40814000c181a1045071f0a1290710f1011500305001070b1000d545212010a01f1070400c072b0100407900765000814000d44219190201c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 346616483 1250 346615233 346615253
    0x60c031506050a02012a03050f06030309040917040e10050d0b07080a110d0902010201050901091a0a020d06060e040f060308040603180210031b080408030601080a150f060f0903 77
    0x151904110740000d0b1031200074402d40103490340d88222030a0a03882c0300640006e411b82c50340380c408040400d0400c40020f201340320501c40e242c400e81020300038510348281402080002c25000c50110341e100d03c2c420385400990131078800b910180000c1020070f003c900700160040382012050384041c2c45400803a580700002115500c507180c110f01e86052422840d1642000c042c094680c840201102c0c0c44007042d00450580d03240c103c84461030003a002000544c69070b01c440c500b40c504c560005440004170718464204040304038180d03540400310707090043c20002440a6039066541580c0b1102c00070310000843e10043ca130501c161292682e885804220441c5590760305040742c0158411a002d06036280400c510121022104100b00b0b54020503054032003918810143c02840c2441001c146034074811140c0c1d425501508126001d01e8100d0b50080c07e55030340740300440710b02e600208220b603603030f03201c4c94880184c2c08440e24110192250440e64034500781004c0000b4050986544141c0401c811140c04102007810700070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 346617733 1250 346616483 346616489
    0x40c0518060a180b1009061202030603031204030c1e02090a1b05090a0305190c1508130609061a121f0e03040b03040c03020301050c090618120307030c060c0315 70
    0x20076000800ba01c3c10b02200107040009240341c028a6241da1400c00a500041d42030544140da01e81901c210300c50b01015049003c103c800d80d4160b0700c100186e0801c01a00e848081c1e125200307140c00c4810440c25600c18814840150404250310b141914140c1149800c0c000c3d02c2e80001d680500b0050780e4000317012060448018840001417000009903443c20351522402030f0041d5820400b115200340c1c013010008501d1801f444240d03404490050f002c80c0950100031000c11000b0030f40e40d000031350340758002c08840c54030310250100c1e24155104c013050005000c42c06001e4204404550f01800b0740c030704400344200d41444803030882254202500c040020440c1191500340960043e000050028162248510390b10030360308005200200841008208070a555106064034403c0c0c0081c0f00949072050f604d0030a004041d10203502040c00c0c031080981c00006090340780d620000402d040c036105540541c1e642940c0c040c610590000e54903425900600000c0c0c0140c20004200740340800c802032040000e1050f15100340 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 346618983 1250 346617733 346617749
    0xc0a0b0907120c0f060c050d080c040e0103030224091b0d0c170d0519031a0619080f040308181618050906040809040f0f05040c0518060a 60
    0x28012501604041154401030030148810b101074180c503040001500d0518400c06032000341c6104046200352145801030000c6901c2002801020300c242c00641e903107400101480c007491400d00c00005c00c140d080700e03024000c5000f0780150405d41c06641480e900b0703440c1d0030103e030700048580b02446401000003c10030124040c107150640c03400035503000280701c0050501d001e0a49688040b02042d03100d04510110840069002142c1600001d01720583d0103000710340407100c41181740036120f102c2900039000000c0810001110403d0020401c000a9a580003040b0030301c00342c0d02c2c0031401d4045d0b64020306202d401098604080c0500d2415641c001c00a00c40140ba040b03c21010941c06c0c0200304080240d802c0150b0240c42c00341409490b440f82111b409106c00c0f0a0090a08090100f01c00c4000403840f90f01884e00900c0a600d8039460000f40406040d10410b00b0228a60302d07162603110030011720803280a01d116a0040c17000034500010050603190089403c1d940d241d102040c4003865844c810180c00f142d4144d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 346620233 1250 346618983 346619003
    0x8010e07050702030309032e0c020c0603061909060609081b010c02060d0903081e060a03032102030f090f06071b0c0305030a030603060c0c1505150d05060a110c0a 71
    0x384082815406606e1045425103c1c81c0703041c03092030060314a10314222046c0c6403180e03e40b20a2402200c1618401d13507409000d40c01c0307100313100282e0802000440e8400c001070503100700f8411600304404001e4040d071010380340701d640b03900c1806001d5221980b00000d0450f6001003042001345820500480402100c0328140404240d8400c00c41d02c400c01547d00d421000301c0c081001103030605024181820072a00140e4415440d000c00513074000d210119070140b1000f514031a50300782950380a6641c2094422800800003112052051001e6680002c2d84940442460303240c1c1818881c010924090301055003a40e01d400c00c50800404031740c48803141c0c0e0103401c07241d01c5010f8044a0705001c520300079183c001500501001407038061164042c2c10180849109100810a00340e0b142000c07191030848000091030360311002d0000c8000a11500200e400c8000c0f40640c2500344200000110742e00a4060220f5141c0c1220b001c02108400c203224030142c5040407606245424048010303191078458043d4002c100504c1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 346621483 1250 346620233 346620247
    0x518060a080a0b070216031115040f080c040c0503010303170408040512011e0506010f034107020a0305090405090a05120403021c05060712020919090b0108010e0705 72
    0x94406440c0040100c0350584280c0d01e01400d200c8100142150828007520400d0020203082e2102c90f1024100c980220f00210340d0070003e404c10080e0f03582d08150200d960800e0101245100d04084a24002e060f03480044c00001004824001071301c058142110901100740010000700344c0041d44500c036046114035070314050741c452400300014005c2d03030400d50b000350302d000819030a054150710520014048003040d9841c03024040030b90050700e0084401d240011100c2d141c2800d0769020303800241c420840141814040e21850242c0e00c514070035200e0190340d00400030380030300d04000040100c0703420a0b014800707048002c050380c8000e0000d204034243c05006035918000601c00001c184403041c10700d0362210584102000880c104180f40c0c00034003080e031092150300110720302c0014440300c1c0765066078000b001c1c1c4942e42d06c2c828165001d00a4400c410f11581d0200601c50450b0340311700f07a0344500c212002083c0300e00c501702075030b03c1c2c216100042c0b40c0381031240d01d100501007141c0d04100d0b03135070019881c130b1b0503566100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 346622733 1250 346621483 346621489
    0x20c1207151401050f040b130b040603120e010801090b01091412010903050c072916050a0813290a02030d230c030c12060d1a0601020d0504051806 64
    0x1250115100c01e4606450001e07440c158010560482d10212070f03942c0706a010604000482e003280c0010f551003e03624603540020002034002d1800284010000210070b5039a44510311a030031440c802400041c0b5891060303001d50780203503c0c0d0f409000100c100700440196000043c100803901d01403400010070362000c00b45070b580c2e45800c0781145816030009001580451034081c0090704201100c08090080841c08604c0140d80c4000d04020804400701802c0e08000c01380f01070250780301010001c945090396410001180d03003000342001c101c1c0700d160b00d5550b4808003129081007004541045d10000050304290001c200d5410a0007001541c00010603a20f801c81e01099180d4429008034008040c141112102d0907100d581a040503e40844904200341e0b96001c1440a03a21084401c500101024044c0700c1040c158111000d80c40b03140500102c650241c903845004c25881810041031203080d000e002c0112550341448a00d01d481d07820b0030418182805d000000d184818251864240ca4403c035000a240e5030b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 346623983 1250 346622733 346622753
    0x30412110a15091509060b010f05120a11032d041109070315060903020f0904020a030b0a02040b0c100608160905060303160302060a111e0d0906020c011e020c1207 71
    0x60f481013910b030b4450001a544806400c40e0142514110f2401d2404081c5500442030100110600e94070390f85400003c5003452082240504551071040d5100d000741c5000e1070920096001ea0180c501440c80300f50002c0c05c0c4070b0b550490300525048040e0f402c00b84070004140608480702c0440459211490b6a2501021002048105000c80011202030000910300b5081440300341075a00a0b20094807144001c020720103002000d030f600a40082d0021802c10201d00d041c02d45a40150804401600d020f90b91004019960054a00c5465030b8100840c0714601d1001403080c0c400030068140900302008140703c4440e40b0591511607940301688800c00222183d40038030403180c94880e0014001074031440303030400039910710f82207903914200e031301c0c210710711a10904141c01c6e1740c40400d031000001440342c2d0f01043c0501503042800c4400455440303070701c10b50014141d030001d8800046c0c0c1c1d00c00024080a0742c0d280d030380c02107400e005098a992041026110102d0f001c598011a003d0000200d551081c0f03070b1500c00d11030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 346625233 1250 346623983 346624001
    0x8011502151306050906010f030213060b030103140c010311161e03170a0501080a02040b030a0c18231b04081f05070e130b0f040f02030412110a15 64
    0x501d040d1010448552112400c408165000b8803041046640d0200e2080c0d4411003801003080c0310700b41207020001498002d02100070811050300210b2040d40c0d854034641103800a030001c854018062940c00d80e421b40800c0490887c0f0b0342440c0a01840360000142072051042403d80c03d90108500400410301c07001491401428441c0d00c50450f010480d82401000c00040703d2011702d80032a900c0108620000d640512810f94440070301038802240d855003080003c0046888413501400758150f40c1c0d001c18907416106000f0320310074180c45020300790500e01e2000c4504030104454041220b1290f0240d1078011883d075607001c4241109903c2c00c100380b842e17959040c0555445a240d51003140c50240360f44000c2d581b03050840c82c4804040c040c81c1c80b40c000580700c1c1c6070381d10701747e5810008030310320304c0380c01c4d01c0302d0308900c5580384041e041d00d8943d1802c07808101500d00180398601100d070000280420448000c6141c074100e941e41c034104080601103060503844c0c0042001c0038040386c01c0300b001d0000c001c0180c3d0144c3d200c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 346626483 1250 346625233 346625263
    0x30318061314010b060c16050904030e060a170a09050f01020f07141509030901090b040302091b16030c020a0504050903070809060d02072103020c030a050c0f120409060906030308011502 81
    0x11b401034020000e9841600d094103498030648141c0c00682814440389182c05198942c4034010609082c0042c015203400029140c1c080180355041106030301c00c543c020f00c2c014160a200407070003e04500f0f000b85440c60605000c0d603160300c10086850580c13001001c1d60807444d804100c0020303411101045c58640251582500c3c05000c80c40300780550781b200003004146100003a260b10000075502d840c002440d00652001030f401064a10000b000e221600c0260010410020080c45c100b0394604020b601820a4802c01c034003292104c12820b042d4038007401316000030f01c012134040c08286415000c0544a000300e000c01400030501186004140d6a584142c43c000c10100c2c40c115240c058506200008120448115441010300324508000c0e52280c021234281e440a07034002c501d040180c070b10441d070940c007840c1c1441140c041d4610080c1e6160040c810800081101c070441501d480c1403021030380841d803050b4000c0c0e45885ca00a002c00000c0d400102c003504440520001c083c204c1c40444050f070400c4c1840c0101c2031 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 346627733 1250 346626483 346626487
    0x30f0804030b070503160201111b15090f100e031b010204122904030813020d05010204062f0a08030411090403091e03050a12050d020a02030318061314010b06 69
    0x401d994020095840b404c81c5a86c10444007508200a170300325a98040001c3d058101000004102c3d42a079010042041e011400c8a04a00d001006d01c80c1c0390304241c82511450300040f1800301400030070001348406000c581d404000f46410341c007001c3c1e902c9c481c1884044203100407500d05042c500b400c0d030540f0300500c1170501e00c02110040d460084000e070391500d002d00200100401c040e200b62454500d9611070b55043e140e491207510381c0100c03041e91858031882240d001180810b00c1c03001031001e0014000405d10bd4035041d1181c0c061a00039a001d406542c1c0c00a840002c6144100507039400080038016039811812040da42c0d1180d0030804001105080307087e82014100051108040c0c1c0100082e0449910001d5242c0c03640403d801000008400d200c0544035500618214010441007211915001c625003083c5181c099120350703030f200ba60040070003c000b503003001c07003000140203a40d1038108004407000b010341010301d85003500344410a03070071502402c00c2580c800c01c8440b402095208005820000341015 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 346628983 1250 346627733 346627741
    0xc01150e072a05160905060109031e02031002070b33130905100c05070c260607020d0e0105040b0a031505040609060518060907032a0804030306080f07030f0804030b 72
    0x3603a42e4200c0d04080220b114444c4001500b484c0520a0901551059441c200402d195844081e00c5100e00192082000108104500140e40030084c2240c1031424642c0941c42d245541451140d406000b8401daa1110101c82641c3c08030501d03080c1c180307505500c07007c0f100c01d9a1030b50b80861300d03961203a280020403a20740403110703087c04000200c848000031120400c0c482d0007800e2034103d600e030040c203d00074600300041d00b0510607036510b800300e075091050b000881d111104851008a183c04000d50b40a00580c000c981d001d482558000c00009041d0030a00302146003500d07040000000b0320510792820300b09940c038903007030011943c440c400303d0003021300a0080c0180d40e11120369900030001482440d11500c14050651307098810186810711070400284150800d55408800b5006050501030314049002d04145014041c00307e48460040749845955190031450145400b8084643d00e80014040303500001c0544100180007a040d41a00e500c000c05d4084445141f0702722040d405290070081c03007280000200 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 346630233 1250 346628983 346628993
    0x1504080c010e0c06120408210a110324010915020717160303050708090402040f05040c02010e1b0a0b0409020901090f051305090f0a06020c01150e072a 66
    0x5841080a40002001a200e021860035039440c3d94408042d001181400b0b001240c103c00c07454164040c0c061180c2d00d01d40804d101d4480b844140c00145c202000070200244071070040d881c4208441c1000300c0761810310718203050b903e1154060b5070400c01c2080d00017800850301207902c20b40b00d2500070407540002e000010003040300603458102c3ca00401000802c1402025410100020040c1d420038202005003d0b29041d03840c110f61651080d5401d85074144100701000c100d4903503200900c024007900c0c0760f203807905042108000560348081030790411a8105248002c41c103501003244c21090740141320300300301d103400040032410390420341c3d0148070301803070205001424080e039400419034450246e03190001e42d5240c01c09444522950b001d280c2d0030031540c02903201140e00662185030060018011104030403450000b40789450074030b040840354640c01242c002c503407103002d0081c001d0402c1d9850800300d4a50a00544021085006001c6000c200e1603d88018111410000c0d6075159003100504002e00141070400e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 346631483 1250 346630233 346630237
    0x61d070f03060c2d140f07140304031203060f140916180906080717190f1202070e010522110c060705030405100b0d200303280906080414150408 63
    0x160501150302d07441c5040305d841c4240116a02e1090485060381002001d80b13609034100a0f222007501140b0003084003001143d4040c14040b1444100c0c1e80206049003440510524540a40e22980c074010341d15114490700e40d68803846075844100000364000141c0c0030700e02210000031031040d070a0341c19902034000c164003001d600800c1c255403140088130500c17607031620a1840908000d40054290300501420541c030760505482c5d42c41035001d0b044030008504d40d0384035400c10064500308100581c0c8220ba00b0020103629800741d41c0145001c440b03210854504100880e40300100d03441001c0a581c3e689036150030b105071041131b103440c40ba0314001c072640c500e8a038401138201e500c1920165600d204050380e844018a0030700501c12000005428600b00016035505c50706526507a84084000e20300e245505450364808101410907014440c0d02c821030204d1400c01c00c000c0e846000310b00030800c40040d1080c84995004520560080c0d031150741c1c0d02c0881c101401c2e4609000b607525001480414400c00e20082c4145100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 346632733 1250 346631483 346631567
    0x305060310020c07260a0303050403180801020909010f0803040308070609050a0305071a0114060901120f0903171b03041b0e1e0103030f0f09050409061d070f03060c 72
    0x10918142d20084844400031030305130005c0600c1e44200b8111000034407903000b294216103c0e00709108840a00c0407103501c01600e80d00b006285030750101c1e21308018542860010300501c0d4901403161814102000c4030780b0b030310071404003800103800003405000300702856010400c06070704a010b03170b81512500d20300141103501801c1c0a40343c01d5020301d421010301a215400034109c030303003104141c03a8104007031042c000c5a8000341021418040035420319003400d5014065803035008d030048000140c456013440c010303222401d001c07903868249107103004201c41d44041d65906405000100c1c221134480c1d480b481d11140100c08050f581c3c5d510100c1900001e4100b123102e9500380114135081d0101000c446240c50141110f40074800070700001c50400c5020189402103840710112400c2d07281c100b50f21600d86021906035900c0381c008440c41d039520b41e42c0c4020800c0420710421505504400740044610741520b5028840036400042c00840c8d0322500b08851a0040540c14000c103405d240032108046401051010080c3da81 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 346633983 1250 346632733 346632749
    0x1020309060c03090a060c020c040609060807080a0c062f060601081f060f0207080a23150a0b0d020d030c020406140112050a11040b04031b0b0a0305060310020c07 71
    0x1d0124160300410416680300e0b070b030001c000307107010002c940704c46015042075400201540210b60b03111566850303900401c07015280110002c5a12461301c1c2280b8913101d05d55110100a41141076110006600c1e00d40001c2150f0b818030342450002044441403550740f003c41c841201c15200c0001010b82504080b400510450003600e031182640d4602c65001000c40001071010340109029a0501025000360010351041205204540100352900300751490125003400903900c1c40a00c0700d000180c010384002c1c5060041e0f8503c0603291040038001101200c0e1005011183c00c56140c4014005980790200a03d5215400424040410081d818094851041200c059001d5400c014020032010290b541e20300d0300c14010f9480054100000d01c80c0350040001174204540740b41c9480029003c00100c60260014041d01d4034403660341c514502d08690410301d6100102c040c4800d03110104080e44a82d01981c0701c0e06004c0c1000b04603540e030940024105441c00802d4181c03d440810050104100001d1882c180c0b0051 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 346635233 1250 346633983 346633993
    0x1103030405221d2a041409010c0f1e030f0c0c0309091b20060103080a0f08010e010b13081e011a090105060f2b0b09010305120a0203130801020309 64
    0x40e900342000f0031000341c00007440e42d0201000100c030034511048000b501108003048100244074000003001d980c1c08a940c95591860030080c40300400c420b1189076111441800c00b00c51005045202900110a00b41c4682b14074592250118200780250060210b80c4480d2004104807410701c04042d0041c102e021090b000070759106c1001c14594010312402c81504d01c038505910607903401c0d200c1121102202c40f400c02c6840180521342c41542c0040100501952040d91459152405180c1c014400d01d4011119810442204010810b0030801c0444a06403440e00c905c0703070b5841448c90200e8990258650103c1e03034510843c103200114603801e040001c0c100304080d0007807042c1d8000c8402401d50400302d4400a07801501ca1004000b1403030040c000b00451402c0000d002c0c10802000c072240c0d00555000d40045518403441c03003820b5480c1c890b10859524000c2160510855411915420b90b581c10946a0103118000018414181d030f0003007042e910228201007034414900d80f0744641a0103900240c0d07248082d4410 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 346636483 1250 346635233 346635251
    0x903030e0108070203040b07030e0303121b040302090a0209010c140616080f06010c05120301060e1c0f021309020604030f0515090c060307051204120e120604110303040522 75
    0x214510060050300c0c00e0b13000f07508181c14050840f03826407080c2d00c1142404001d80c1110111b4409001034035410129120955084c41c0000ca14882c0d041042c0301600142c104000070b00c010380d2174000e841d400c504504401a140d060140059030305070700c00c0d0400780000b1a000c4c1d10700300800d80020118480c4c4000e440390079820203180c00650740c0c01400d5903c408490f50b08000151103510a0912828180c050130440388850b0300c040e0404034a520030f800c8180084d0300d1501c001a82d081480c2c03c50078420301841e500e00d03201041e4480c0c0b1011607002100a02c152040b0704a12010642d80c0c010201300c50300100415076881d1340e03240034846480081030031600d034015a80e5000c04022080c06aa100c1c0403801c001c0d00da002000c0d170401003260300c024600406d00800380410711240d102d041c0100e1045104000c03d1101c0000580d028190042c80301119208003038191021026207000b0590390b8100d40e200c0100f04007507144e24006411809140c002d242c01c40302c95400740c00c040743c90143c04c40035000319940822080035 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 346637733 1250 346636483 346636487
    0x1080d020a0f0206130e0a02030406110910030914150a060807030804121e1104051018020304051905030304030e030a030503041e06230c120103020907020102070501020a0903030e01 79
    0x8044000b51660082c41c84040141c20050001c0042511804060010544581281d0a00c05080c0c600d00802ca41c040208800c1011510500855140102440d401c0c401c042c2c0c0026042011040002c1c2059241e061b9030b01001582c0d02c4504101c80c01c1802c2c0c8446c1c0d240c443d030000d00e03410112000c3d80384504040c0c00040081010414106480e0060022441c060801040181140e021001110b207801500310001c4101c520760656003419100e8695845082408002c10041e01d01c0a86049042102444c4c10000f140301c3d403201d02010004141d0141e00d9988500b040d40c01d242c0d52501c0e45130310b0610f1882c8902013103401320003140304520075110506035410040c20306984008500f001408281e042021401040b401502d4030030313070b110000340d501c03c00c94140d4a0b48203464098450156400582c0300343d400180858500c03e501c40c00c5410901e0814030240a844d694a8040c40003901481803000032480c0e4503c02c0d0100c8942c5500840207540ea142c4541000702140b02c6880290005418503139194101e41c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 346638983 1250 346637733 346637743
    0x60515071a011401211103011806080607031d03220b1245070e04210507060515090f060109061d0306010305010b0a120c060302070206090d0b01080d02 66
    0xc0c6900603c0c1d020321181c100151813004220b110b8010b550601c1104c0c0c010380007180140c00c640301c1244540390701c0794500f00d0310380444601c0380c00c850380c907a04040c4144000300d4002106070b4030442a20300810503058001401850400e42c00d40c284c994000002d0400c42d03000b03505103c03807001d0700c04c1450000c0c80d03550f040301040a0040d43c0141e400000030308080f9107d00700b21040e00740600c504031850000810b0180860300880203140ba02580030360341c41d154031080b202c180800c00003030040704520402880c083c0e81e60548184c66501c04203403090400c0c4100d050341c3c410001d07150340e2988680704102509000444004261051075164801d1301c3d580005543c000d039401102e8040c03001a103599451600304082a41c00c80c03040307032400d41c581c0e45003c072130112903a042160034021400f41c000082c108611301705100d4aa042c82c6c210102d54400190b91a0004120300303881c50481d0010703c2d0068580282d4030001d5164400e96900b03650010010080c3c01c2400144020141224031110032600f0f03100d12030070166154 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 346640233 1250 346638983 346638989
    0x7050f1b250e0402060f120906090705040c1224090603152309010e010908030f010b0405010903031206050a171b15030a09020406170f0a120f03060515071a01 69
    0x100240d02040045c14000c015180803144c90a0481c00c2040d072600448007820129001011640107500f4400300790000d2001358054601628140b21b035180308080581101e60f400c0300316a0311507454622107501c0141c81801c0c0d074000070010102c3e00d04e0f66180307014005040d4901050300c10440c2d03c0b000400c40300c901d10031841c180500301000351410801d05513020b500540203096a00954841c6a504e65451080c425401c055104104a03912400e1040d01c80a1089050b0000c08400c0c000f00014040c0e6030300721301154202c80d454546040c05d4684040483c000e485554002a044000c00d100405c03501c10701d4010f54901700300502201c104024034003000460354206103805400c40403500b050021021050019580205103040105618030310f0350210f412904258480203030036850100010b05803100740041319034480708400406445200780c55001040d84500d1525091201e402c082015490027600100000d0000600c88403640c0384900486909a000c10000c0381c507a001c20940140c90785000d501541a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 346641483 1250 346640233 346640249
    0x606020c0901050f030a0b010902070605010b040b19031e0905011404120c08070b0103050f0f01090308070c020d02150c071d01060827071a09030607050f1b25 69
    0x756440c100c10320800710b0000f00116018003e000b000d030b020620000c04c19000704500100144e4804140c10000c04807841a004044a00020403041016044c800c0036100444181c01c42d105102e05031030f0b019002094581c80e041c18102c801d028920300380100b54003885243d40101c00910950b007000038002d0369210111070003003030803c50306468000ea43c4503003021002d035486203102624105840d26000b0800b03009038000c0b10b8591104015103d841c030140032031703400259108001d000450a5aa019080000080640c0104140001002c2c02d541d41d0101c6120354540141c40b2214802c10302c01410a20b500070203100a032442850750000312050583c50b0000c00e000480103812840e420107408885000e0702512800049081d04d045031aa02544290700310f03000e0480f0700030419149800c2c02a101c40382d41031110307054424144100007407a1004240700ea4000c5161400380e9682071203c0c2c00c00c15600489155401c22070f08101104244039000804018124030002d64584403a58000794007005075041c052110 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 346642733 1250 346641483 346641499
    0x2b060b04240605030a0e0a0f061b12020306010507020612150102030a09290d0e010f0506100e03031c0b03100623060906070807020901090c090e04230706030606020c 72
    0x21140d0311030f8000d590015000d01c800301e042402e4505403841e1030420503041e40c0ca4140e080d44d6104002c101d10480044440140001c000c0e0011404040c1108007401c1078440c03d103400100141c45a0b2180044942d902c0d401059aa180c051103042c140c01c01800f112582e80c009a40100319103158000030a0710380c0914269207250b0480d08011030000000b14040545404a520400440c440e11404010344505004400c0014500c6c111a100c00e080d0350b4185044003802d480c080600c5a2510748805490a04a40e824482c038400c0030100403d11314811818012841a007030000000d598a00b07030000c0030101310450850344001d010f9008001104d040e82703d0703a180205841081012800482075804c1170207001091070f0309008245005c02d1259008000845020100054000c11850880c0a4a000d020f091f2410801c12002c040041c014400c00e00818005020768000078040080d03040006082e1101d081542c1d9203080f079000b8031507407400507004950119040120105416200081141c094400280313012 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 346643983 1250 346642733 346642739
    0xa030b07030509100509030703050706110408030a180f060e0102121314030c0d02100509030102040f18090c18021308031e0c0a020d030329010f090806062b060b0424 72
    0x500c02f5030040500311001602ca02c41c2d4071803400c88102600060660b54042c40e90f41030a07400040011081410318901180300070340501c0b0030000310300300e441611003504002c0e00c901d40300b40050307141c400044000d11070b600e40010f80c044c41030741c01701d20541240c110747e1842c20214136010030103841c0d0105141594102d0080015a400f5142c500241c3e00720700250705010f49803452020200342640d02c04c2d0080801d000d1011010011012a1441d0f04c2c00c03a4200070302046500400c0c0c0c1d520304403406520078903004d06c2c048084849012129811a041010003070310311180241d13103403000c07522a000074440070500c4c10102c03840240c03455000c080742c50011142014000460643d4200080e030724018a0582c20995a0802a099a40d1120803058400c03a040640c80541c01c0342d200041c041e00024001004000c641c28040002074000604180c1015007203808070f401c80342400365620400502800c03a4584001d031a641c1c400c0c4009a0301035101d00c5410f4a052150b1040b000b9200b0a00b12070104590054407448020 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 346645233 1250 346643983 346643987
    0x8010f141314060a0510080d09140303130f08070b03010b0403020628031b09180902040b03031809010509040f060e0304050a03050606030114010e0408090a030b07030509100509030703 80
    0x1012591160007000c14040e8011100b52401c0411961804555595020300011202003d2608020129040103050b04507011500400501c2d16220b00702450036440710340d1285030390a1041d910759021700940c5410043c1d40e810320b00700140e0b442c41154607074002c4880100d1000b07100340807603040e01c0f103992070b1a0bc1c5c90301e0340c1c0c203102007a84584001c00c90310100000c40307103a0051495001e08441c000b0740d004100c00c034450603904e0740000c0070f0a8010502074050030402807c644104500d140c01641000000d6802d0280040f901811414640c1c0e0390500000400001d0810104200307080c40c002690345904683c2c9a01c144820f102c4280d4000e40304c5106101d03640c00103034045d080481807042100c10b403824555610b02003003000440750400c440b6134100500700701d01411709200e220014104001e9a00e003651419901c0e0740800c0000e00b01a18010000810041c0c81d22210070310001558009034614040c43d0000c0003d0003840706a4810109008010300414803101c0d0780606070140401401461429580b6a02 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 346646483 1250 346645233 346645261
    0x1050f1303061e0b010f020d14070206040303180503030a08041e08300f010302010f02160f2c070e040b030a0f02030609160501030c032408010f14 64
    0x850100655103101100040680c00350a00d583c41c5034034000e06030785240c00c4030010340f443e402c1a40c0c104030046080025075540046c6501d910340141c14801c1c100c400b00450081c880c49444070203034000707000040000400d54840c2ca0380b0160000c089181c0140d9484808068491103441c9280d00069070b1180401c01054544504081c105201c00d020010f43c0c4c416916003445811520000751900008001d580030002c10001d12417440403c0c0c041c000ea54540350b035031013944600600010b4100f001540d25416198002c01c80305140d030b03403c039002c250360664458515802c0c04c801d0041d80d01008498158031007040d180710550440c01c10030f0b8518100e83d51040340865002038035034846540141ca0f07140e43c110a4a00f4400085003900900f101c2401e55003030300505103025005032038210151b01000309001281018500c80702502c0c0c00340b034042402c5003c0705086000c0c1c0021420b850386d448000744140c1801c0c80c941c0c0c3d18400c68152000034010304050404000450300074031031a48414030705e030340000c040b14441c0b44 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 346647733 1250 346646483 346646497
    0xf0a0b0106110a0512042112030e030d0f06031e030e06090103090b040f1110020304051909051005030d030b1e1f091a0711010f1407290601050f 63
    0x101c0301c3c4185151541842e100d0840410601610001010b2110104181442d49003a030035420744000360303545035110a10616450780d4581010341da0035003040c0b0f00c079051003100d500300c007607650a1100150305a0044002e02c0c1c10b00c4100c502100442080600b0307904c40c1c030075101003905a1030303000c0311007403807404d001499002521a50415544a01c0000010418aa103d02440c0035040246110b01726180c04864001e4800c2500c1c4501d80510803d95115400800c1303d007034440a491880461000307542c4a641000507400c4503105900700070070031905c0050744221104a540450845076a605103601c1a011266160880c58010044e440340f4045000c00315498484448c1c068080124001c00000f18911040501e425000040044804015900b40e1030310b1181c1030121481c0051415246698004090032002d451906000ba40c41381011058081c011031110080b81c0211207641d1060f070301d0407206002c83c0c0c00042d081600b40d11544508001c071180c0039445000c040c3c441525014000803407140302e130003200c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 346648983 1250 346647733 346647767
    0x21c0b010215060f011d0a08011506020114040609060b130902040f0b0307060e031203070f0e0402030709090e0f1903020106080c030604330c0806090c19050421050f0a0b0106 76
    0x108030740845469007c0804010006000006007411150440d86032000785a40300408581c1000302d0710400000d40c1c58203e030031035400301c8002104d0601e45400005404214002644100780b41807100724080c6580010302c1e281d10840302007101c034171003010b00000c131100022240d405500228042c0409030194841410100c001800c550005860300104043c0e980119154000104000c62050006400020540801e04100c0c0c065046103400c80c1d008040a04c10b10550500703907242d01e41c05a00000600c0110354008005090f6051031544503030301400c1081e000070440042d1300c3c4c01c0000501080c003041c072500f0200024040c00c05034076103445e001c01d42600406101054201c08c01c3d41c1044034080b2013034140d00d1201c030f180030030329400803200603041640013071120b030181090030100803218040508131a49401c100107408880d0701c141c00201e4490055412112082a408600b10080090402d200311400d10910884001c00190f4104e05c2d12241c208030b000b0055201e100040c8a600d0055102400740c2c0c03114 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 346650233 1250 346648983 346649027
    0x11b02030105070e13020406050d02090d020a03080417070e0109020a05040e04030c030314060112021305040207060617030f0304030e0f060d1b05041404090303021c0b010215060f01 79
    0x64000038210b880c02d50b1440040341900074040201e0603d540c8a035408081110110704052400c0c10250407403041484144442c1d40c006541b03084c0e07030748030b425407a680703a0058091007003540c0301d00d4544201ea006009420450550000304035000100141c0142503038404464812240d18007041800690890080305051220612000c2120f104007007802d80b1550007981c0341c14032007206050141c1107070100041d8032440244101000b00c075903040114031104000c50000140d0351248900e0003481903480c1e0304021740c400d0001404a080c0410b581010060340d0b8004022042407445c000610f540380b2840f01040d0111106000250100b40120055a008079001d806201000640d0000403500e50000c0c0451952590b03030403e80701c01050300e5425800c0110b46003406480c01c2c0c100340b006c03c540030141440c207126588804030402003512a03016507400040c3d05144a902d40400760f840c0c40079140032903000e801849064140a001844000c46901440d000307003440074000c01100046070a20712111121040c4010 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 346651483 1250 346650233 346650287
    0x40203100510080a0b0109080c0904020102100612140a020108011a120103031806031a271608061503010306090204140c0414090103020a0e070c061509180b0601 70
    0x441c00e0b15800309400e0395440c030f62490103154400071107054641550401200f02c40611a82c000000d4222158100311801506a601c0b840100d1070001c03480b03500080c09042420001d000c40000030340c400e07a68469120440417070b4050760184d0303545800420107030004440e13900412480480494800c009041c5203086490b1080301000240e00d41c10a0b44100c0015101100380d91014070380001c40d6000d00340c6460107102e0500a00e8403030b1029040c0710040c910800b80d2051540b20100906060541c1e0540c55042021915282c0c40b907141880084c001d910202d28070400140d0b880c9440281c1030b800b109215421030840e400d6448400c001c02888804a03081a0354210440308007003808030f03161180400980311541c4a0030900c650700f03030a80d0006404e001e81103490050005075207010b5801c0984001e0121910543d80b2100201e80050329a00e015000c64031f0b10040320000f104154003903094441c592420302052101200d90921030780d010001801c4100310b00d0104240790b209680501540e0019403100d494084 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 346652733 1250 346651483 346651489
    0x1020702102601050604150201090209041208090609031c181115160b09071d07110604020d0311071701050601030c0f0206060d080c0a05010e070807060504050402031005 74
    0x8910801c101291100001150541480d01074066030800044051071952401010500c2c90003280a2003000c0aa003204da0240c4c40e2003503102c100720540040200610703040c070781054198805060064070004566900040030100f00013415070003900c00a00031071404211368040050501061040c4d8000c03900c4110118144d0307886245102014002e038034000c0f0780490b803001c00c0b5070000d4007460310807110f0040c0a60071740c2180201840300c5240d0003030f040c00d44a9031805000ca040c00060780060200200c0d404070b068224491072101c0d03210308025118405044444a817007640c03400704480003540003040103a07040c0064801e03400705038141503c0b0103d600082e199003440409a061068035096a95260f04100300c543c2e140c029034041000c51706250980e4403458600079128400203110303500034459583c050701004025022981d440f00000250340c2d41c03030054600039010340304010020349980704007807000c140507201050b4403040f107407640c44084c9000c0c90304d01800041d401c000c00400000c00c240000040e40c0d2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 346653983 1250 346652733 346652749
    0x4080d050a050601021b03030403260c060f0106082e09180501060f0302130e030403061d071512110c01060803070b071704150b04020a11100504051e01020702 69
    0x615036071004034851a00ba00028904101d490808404410910201e10180c401200311819660402d000d2a5040d082c03450003581001e030130102d1002034200107511f0708031800100b500c0e03009203c0050940344503642c0d0201140d401000307803001e0207802c184844000890407510300c1807071428101c65682403d507591742c0007201260051800900b2403e11040e02008000303081c45030320040c24034199081812401c0d900458641409039411108407035503000c0304200040c1c20000c3e14010b50b03014a040c0310302c03040a80d44150300c0c1c42c210ba2040b0503105008010030220b442c00c2400142c46555a5001c609141c4480b0002c080c00b1000d4150980840c2040f40d00a41c10080c050f800107442c2c03ca00440c1d490380c0768503001010301401045002001074001100d0b030403503003011003140c205402114100782c2d18141d0440030020402382c2030b40781d4803510014810b81456000a41c80c0b4183e80040f00f65105204811444001d640080320700400c1038104903001818158003180700010360320184001820b111030355000c0b810368 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 346655233 1250 346653983 346653991
    0x21606151d16050a0e130e010b01020d0e1c02210d051e03041b0312031113050910080709050f0603010b0a090b13020f0c1501031a04080d05 61
    0x86410040500c50344000e050040361600049401c04000d20349550040c004005406107581000000035034051010b00c2080c0c080b42025009210100222000100c0030090503e100c1d480078550905404481c01e40c00490030030f501030f030715880d205c00e2800c282c010090341000c2c04091502c0042d00c81c0b605000b50b200c49d40400301911440c500b1124051101200314540492810883e0030050100312448045001e0148085c620400d081e0140d220f448510303141c1100c0b0401104020304e082c00380c0c000018802801e010044842c429181002064000348030113040d407080f6045802da60000c48020411400c20300c0103194001c0301c10464202064071491b5403800c00503e544401076072030722030040c405145071005403180c01000450081003038000007400f04452803010b01c504503840395541d07030003440c640b03a50038960015002003408645d03490712207034200141e07003006940004a20402d0760305540e51403052211416a07401a40700f2407580010340c0c081c106108001d0086a000a061003090b1518205000e41402 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 346656483 1250 346655233 346655261
    0x30b0402210f10080a0210050c0f01060302130212011208040302030303070207090c0e030a030f030b1809010c11070e0705090d03032a09140a0f0305150c0319021606 72
    0x140e003030100340180c0703031500030f0701003252254108003c01c24a400001c2d0140c41c0b5074140e95820f0031802c801008d850764040c030324060100c0e004508416080308010340c0020162442280c0407180703a103051101e0313000c0780120040c10400c601424010321901b87c0500307042007624802c00740c00d49400d850b41d011038210f401c05e0b540d0002517402040c0038800d11082e030141860f0380596103801d43c0c9000074140025034a00154401400b840110725528180320710981007108000c0303020745030880043c1c0c0c81d10388448200045990b04c0c869440d0030054a0340358400d003070b021a032803800307001010340d6400d2032500740701c540000d05688280401044010031a843d00074a040e915402610001040704034030180180d0000307410b14950008511240001c1c005801140c03200c25607600320310468803d603941e0045003001140d03800140e844540d4134030000c20810009200c1c0b00341ca2422404a14546907a00000da4900040e56001101c41c551300b201c08030110180d01414660792807849440c8034030455110f40003192400010590 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 346657733 1250 346656483 346656547
    0x7050405060d0f090308040b070302070206071511040602030a1b020303040308031009060e04051c080a0c050d050103050102130b040308030a020706090b0c0405030c012a0f210905060901020d030b0402 87
    0x144030200c42032340e40c010700505056140c01803940c005243e41c81101c00042858040c0d040e0a603000307103103074840b5980b885200716155840f40c0b0b56001a50380c1c0c010310070030000101c9400007180c00ba0181118448016400390082d814541103a84520f541e40004201003600395214100142d07111550042c0e0b8001c00c04100c401e0020f0416003007580c2804840d8140303000842a245602e41d4103684099020743c080010000001c0481e45038034100c40c148525641e04868070300f007000105c00e01006600500c0304c2c064140c42c00c43c096a032900c07401d0850096103c0542400014000586074035003507001405445d215000c0015040d000b903848030410042901d03860104100402c051100c0c0c00c08006000752031800742000013050541d00d41070404030340c0380c511001d48482e880100304100504c14003849403c50303211061001c18400412001859201e4000e035500040c0a40000200c40c1020720131561080340603406424060304405040d406450300c01d40b00e64000e0f03802c008080c20744050101100003500524403440b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 346658983 1250 346657733 346657741
    0x60905011d1f0e090c040608010f03030c11040e15040c06171501050c0d0809060610200c0a0b0318011817070c030f150507050405060d0f090308 63
    0x409048640092801140c085005800c05030b45620010825121401030555590481641200e0240d25140001d412203a400203024204030f007903010b001a1001c654901d003c030381c1d0b40c08181145020920025011421107404003011840755020790f200010301a1011030141d0840d0a811305d0800901d41c0080706110b894184003c120550310603030010842450034010001c0141481c020202d0302a0040c0c10741184500d204119074094004d854581c0300120a072080341c0701024028114401c115484801401194000390751841c06000c0a0701c034107180c0d42e40c0046105e190300040c0c0000180e00019659118252030f000c919510500640041d06840542c9038603070030224404242015585000c0d43d8590501e4006514442c040b0700c4d005545401c800d103002c00c12551481143c4078032600c0320141c440100303003070048140101d80c00340d100355a01ca01409034000e04408071401c02c0b02e4090340d0402c00680c0070001002176160200261076561001c80001034481d451501c0c0c08100c4100c55000c50106854030300300 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 346660233 1250 346658983 346658987
    0x5090309011707091a0a0f08090709020c150c030906131e03020703080c07050f0a0b12040c08070303030204080606030d0f0e04020c070602070302030f0f030703030908096d0606090501 80
    0x2034080100c9040c00c08c0c840c01e189101c02d27115501c038018601540d90118902d03814420410518400e01d00c2e07040b480321a818401040d42d85907004448030b0000348039160202c2c030701000c0418074401040c0c1121880c0809521110108202044084280c0441c40390501c0270003c2640308008041d6510004014a18540f9040520240070b1200c04101c2c41940300a50070001402d400c1e0881f50808480b0740170007103d64580c03400c02409001c541200c0c0d010320402e5004010180c05034002e0040c3d418440c100c903241c0d40e030301d420550340b001c3c02802c500004e9409040308507a03034080c0c285088410030003000942407142a904081c681003040e486800140d020341010010740c1801e202d100442240c92001c1d04c40451000760301a078912070340328001c041540d226450414014503106845a0705002800151404d5003c180040c824519000c00c2c1042e90080e00b0090325107042e840310103220647c68840c001c60747e071040b00c8030403907014103030449840007880105100400c00c0380c42102c001d000380303032a44c070030035030400c000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 346661483 1250 346660233 346660247
    0x19020c010f09050a03080f0f040306020d06050402180112090b09010c080108030f19030608060405011d01090b1519061101060f2402011b05070605090309011707091a0a 73
    0x7000144010004180107903100d541250b025250000446a69040c1041d2504040e01c100395940c482024081000700801c040c5800070002c1c0031070704000340b00043d00d40d03003044100e100d0460307210200807196902d642c0f154081c100e5100085c030700ba41e000440c8581501c0b030041b0781d80c3c110fa40c40c0302a5519030354600d086e038200280c5409800080000c44c01c0081310010710b0040d01c01d65080c1b90ba84800e0440808000307100e40c100710080c001d240107880d00c82c2407a0bd05540640329100e9124017051220001403a000c0d014883d950300310750810007091507503c41c0345484200d0240d200450f0327049200d0002d4800030385644103106004055a5542c1a0071046040c102800c458254012040503030240c8000c020500c107045c81800903044041c0c810140c80301c2c1c0c2c5401e9005106030f41d01411000c1050050524080e0848041c111090080005105c0c0f5641c2c00162500d0f44900409103021420790416503104403050345140381d00056505290440c940c503180f05c2070094603c00d204030480e2000107001c102060384606 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 346662733 1250 346661483 346661507
    0x28020910050a1d13060312030c020d090504020f0c0304080f010f02090a03140f0d050406110d02061305071d180111030105010c0c09020d0e0d050f0f03060619020c01 72
    0x14225040c010b4440e00103000803075106092510403401001901d0300c0e038810701042c04120340400304108103656403403d0445400a82d0a07000401e14041014503440c0c0007080781c2c06450450368951540724100000c1000030341010b4076107010103606000c0110010020030050000d042c55100805081d0030415a4509490220442c15421401032029a901d611514030030320603a6480685800b6500c1051000b078500700c0800c0d251102440707250031070710b16160890001d0040d40d5250b42d801c4503043c100f11610b555460319145140059119000155201c03401d5000310b40340a1090341640c9009076901e96050311159030040c84402440c1041c10f118040141403034030000940d01784003e200a5150800700102c50005104440c184010300c034001d810003030103800000180c80d0401c000c42d100c00e03c07105400c004003100340c555030f09441801d104601e85400b600c2130791003400602d000b4503c0d150f440d0907404030b560000382210750004414042441000d250740129548035500754001c0c0503900c0c60900041144d21490 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 346663983 1250 346662733 346662737
    0x1021303051b0603061210052e08030a050f04090f140604090c03060f0e06130b090303091f02070b04031205070f021002090f1201060906050f01050a0828020910 70
    0x2c00c6404561103c1007a43d0f4449421945008105a401000ca05004014500890035881e010411100071031200324000d0204076104c900f002010740c0f1001c500421121b005001403640244640604184118008c006402e0b20300c81d110b0403e65580040d500762524280220318a50f01e9035401a4020f405a68040e030040702200c0521100c41e50703880c3d03c41c440c1190b000c00341c450ba4552462200d1045141c00c00c00c00c126011046540c3e628004104582c9010f2001003100d02c410303048042240e200001082d60300030200b120147c0742010079014031b01009065252030700506a001c1c4180c0000c201303408201ea200703d020b5101c0040307026404d840741084400040c502d5041c0403591030300e001c1c0c155001500e4614204419401607643c011040001e041c00c1558180c81e41c00351032461a0780700c3c0074040d0802802c80e203944d642841000c0d01e503800c001c98020f0002c0100d000a00920046280c03502c00c60f0666003003042c28074910305d80340100c82082c0018410303031115900c19400095815880c181149040c1069a048c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 346665233 1250 346663983 346664023
    0x50105130c0e01080a1b0c050c0a0f1e030b09031309020a0903171612021501030809130f050114010905040624050405030a0b04120905240c0102130305 66
    0x514006841c0c0c910707840d10300e410840080700103800031082c0d902c48a405650684803c06240921b407000f000e01055060072100740c0075044110503031f418210141e00c10745d00e0f800c01c02c208550400d40e144a10340d090003290080c0c03021688001000c2024400044d0042c040346000c1c42d0740741c40410038003031000100d52004014520421072090302c590300001000950340d0100c000c610b400141034500c0300354010710480040c1e500110101000300904a450301da0490b400d034080c1c482c0340b415140c00310801321017480054001101003000c0401450042414000482404400030f11010081842800c44200341c0101c0d25104141c25112501c1d0781107000c50b0000c1070708881c2444410f0510307440400d550710400f42004001c00340c19100c0788180c00b440c2030301d01818016044901c2d00e074042c10140a4080240c40030345400e00803164a00740144501c2600095500240a1003014983c070502a0141c08c80c500005c1c94140d03050140b006c0c024800c0c0002c12401201c1c200c10524142541072250804160982410088ae00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 346666483 1250 346665233 346665251
    0xc0b18060a090501060302130b19141203130b0a090e0108070b07020303121314010903080414190606060905030d121a040f0e12070507050d08040e090105010513 70
    0xd400d591003041d803680072039040c45514085000d098190002540000c540002003101481c83c2c0c02081d40440c1100d110300080322040c00140c0382070190080030040f4021000e6980a410903500ea03c1d1070500b210103c80c5041758410f001d42d003880f1550020303070a6400000780d410010b83c0c40007400d8098035001210300825458a80815501c1c512441044007000022a6003419550280103442510340750340211003036440d1814014070800c55007041201c40801100c40102c050805129424065a140c2c032070003645e4231a43c4422001c588401c84c914118804d03c00c824000c46059807940402c0c80c41040007051050802c800580860701c00c4d08014000d42c03000c3c0d441c81c50540d0103c078852500ca011140020140021032441c19810028080d15400a081080d1008170794030035845552150120382c29104098184840407000b4810004064040da004a0090100703240040c1401040c80c842d1140f40d251940c2e0351182c03158284d08450101d81b40e551030004000c203040284048c40300400c012410000c44c15 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 346667733 1250 346666483 346666531
    0x4020408060f090115080a050706031a04150f08010f0c030e0d050c030904051320060d0f090204110307020111032e0305010f09050106050613290301060c0b 68
    0xa402040d82da01d00e0480d20201d001007100394005075208990750500c0404a480300262a500c5428000031601032003036080c0003995902c80d02c0740392500c02c04101503500ba01f9034002004060960700042054a144131840094103100000421004241200c00451980490741841c03045480c0000c92200745070419030b41d24041c3e4800310743d03c94036060a0400c15200c401d001c02c400d245028020a03913070403074500014400f00405040e01184010710400810601009a01030004116809644550400070038052405211259086070034030002d00d010004445c025030300001c0c140e610200b0881c8034901c00200340f04a065080c0900042001c0c940202c0340f45007048104070205260208185441500d081158000e581c440020300b002550098024041008900288001008081c0b01201d49600c2c0030400551800d10906031041d0307407030344000111307041d1038001326404c90752030225541da008a1402181d00c5820380c4a024602a2500d030343c80015804162070f0001907000c000c0c001e01c00d03441040841d11100317a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 346668983 1250 346667733 346667743
    0x1024050a0e09250e1807060e040207050106060504081006030201170601030e070b0d0605042717040305060601080109020304020306360105070906091a0906070221010b04020408 77
    0x240c5901981101035482000d141e060440894614029415482d0920029000c2c04103074001d03104925000104d80c0c4900c2441001942004054902c0c1d81241c1ea00308181c1c0d00404816403214006040945800c40301d941c1c0071300b1200c6580224001c0b8101003000e000712501004040ca1010000004002e40c60442e00043d02d140709640048072900d40705030004003181d00c039400c640881c8142c6800c880d205502c50351080180e4014500054034185494000119490a03008001840040319050a440c03402141041c42c1c4400d10a4181c48800c4860812106d501d0a04001c100442c061400b50005050a000042081a042c3e000c207030b00c10f005205220150350b0103e000350300000c13200307030070300f402c2e03003034041c0024030100710201d10030385004d0002d031200f0350441900860310a240c50b54410100949811042d10719070014080c041440040c80c40c5100c04010800043c2440c2e00014003450411f0565070002d080003000102c0c1080d2021051003001407002c0900440000c801c003120305608190034040701c256a4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 346670233 1250 346668983 346668989
    0x41d0f040f060905100b040e011503120e03030712030501050f010e1012020706050901050106051e0a030908041217030c090603061302070b010f09060f090c111024050a 73
    0x606900700e18410000c1981c800c078007a66000c1d003030711031a5400381030001c0244055903556015508040154802030018410b4000c0004810f00c0b810301c19065880380c40708140c1000750740042c415848114100d1380e4081028010381c911940302c480c8503100688008003924010381c4607034000d000f50350907600f050380c01101d0041082c000762801e032420300750301c0d004450707806600e4120075409100142d0b0350180030094005a115042c060002d1003541d0b038407201151144a041a001c405124000240e481c0060441c024149000e4a00d03010802e0402c584442500c1d0344540c0c4009802462668990100600c81d0101000e14846003c00c509500c0c24010018581c40344104103441403100000080c0195a00562046c204011103801c540f18982032403c41800c030002e00501c12200742d156030000e850103d40c0520429150b034002d15405c4140381051440290403610901d600388584440510a00035041050440b0103a030240080703091400d03041134128103402c070302000d00081503518050095840d035080c45412 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 346671483 1250 346670233 346670243
    0xc09131a10051c060216060e03091f0212040e01090507140a030e1e210901020307141f05010906060302071e030909050405150c0304020901030b09070803040b041d0f04 73
    0xf11041040000843c8901800081c1480e201007000404000c01290300c00506119920400107140c0e038103000340d40c0780240c010103a8402c07451344140b0b00000151103540009001401110800c821040e49079101780c001e50811040c10203490010061420a8010701c2c0c3c106607541800c0e505040d0158400d00d00344140d007070b59800d26868541005101808205036180c1c171410b608800d90f05030381ca04004d0b031030b4185a02001d05003084100c40c409941c814004903030003003005800840c58040195034170030240020100400c0b0602079091000c4a00c04e41d03180902001500850010b65503040c503081d002290043e03040b410416205100400000304540d1041340e071000002014800c2104c50325084031141040c1d001400001e013020140030800c080010824680d4050034800c1e1102e94900c00d664582d4001140e000e540148101700400104100c0820282c20007481e80507181442d458001541c5154850742c06040d401c0d1002504019143c0c1c1010b21903140079040c0340d051b4450a2540c22980120340242010302 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 346672733 1250 346671483 346671499
    0x90623030c0d050115030e060f0609220b0109110403150f0e030a030c092115020f0a0801030c090615030e0109200a08030309030a110c09131a1005 64
    0xc6000007510a80e03030200c032888024003003581c5070140c401d84d481042c42d440d004a41000d580301030840002c240326105592070441c001e800d80d645010002c8850002e002590311945a00e4071010781060100700c8962640165810044e075403401a80d4000c60350a01c0c100d040400b020b001c1030000506a00d00e002440507101070100300c1c11030303200ea48001003854441140262100003401c103401c54054000c489001d03607680798160355075990810780710501045e1440202070305400c00703d20001a42043c4420405e250100c0050030003241d01c81117296039028207900b4001c10302d01c00041080003003c40181c3c0140407228402d03c412444d080c074844042608000030010b064880040000c081825882006025040080205018420308800c00704c245650343c500d001e0324151270041001d800000449000300f000e14010761518040e61000c0307034060307103024090400380a000c20b0200e142d9150340d045401001150b008404040451624240d082010b056041c8203040780020010380012070200901102d80039513083e4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 346673983 1250 346672733 346672741
    0x309100e0f0a0f03030206090606061902010b0a0f0e0c0c1513020d030522080304050402130b12180706090b030601121e0f090b04170403050d050a09062303 68
    0x4100e2800086642c0d0000c4041c0c0d40002d8050608140c5411a4065000c1c0c0c1c4042e16151507558660000702e44080d0028400c01a40100e84400c2c801c000440d11203100008030b603000c0100003010a0080c0e8000681907a412000f8842e21503410b03030341c54024122840d40c910301181c42003181c0c0c6428446401402c520614000600100c0318070f000c01078143e5004000300c2e07080c02c441c60050441d402000440301e4807090305216001c80c000384c011400c1983c4040c001141403602d88800c001c06584809400103289200c00c000151550008001c0c104c2c900031500b61a10350f00e40058006500c02030083c00d06405d5101072001c00c0b6480d044101030003a51400c0c82021341d2aa500303001644c51104021440002601d0701050b1500c1d850515020880b0380604181448248c1c1034001d2802650807078138003c0c045140c9900801d000809803441d903545428007a200c1400c01e541e82d00c07054104031800d000080462000648000c3d001d84c0714100c900508030314100640c4400581d03424003075908184c5005040c40e00e000001ca = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 346675233 1250 346673983 346673989
    0xa0b0a0215090c030145060e030a031103040201020709020313051605280509270a05100204060503130c080a050601030b0c030f04150605030d05220e0703090303060909030e0f030309100e 81
    0x340700c41f60404000d000e010300030646642c0d00d6204225403800649049264222580c2d42e030b00b1603000300e805a0080c060345060089003c001c1d0701c0900b0101c45d100600303041d40c000400500c000310440304203c181100c0903141009018a60615251201d03030104162043c40c28050300c01201c50540e142076404042e5a5564085408070101d0999154204041c0804007980000c1c0000c00111b020300c01c1066075048031047c070010b816400360f0b01403640880e0041c400503200304a11815890902d0161083c4040103945000141c203002000c801600c00d0b400000060003881801180c4179003000b04031104c680f940c503140000208000d00540020402c4960035100d1035a80c0711030300303c9000741c030300101680c4550001400c0644540d00518052003e106900c0c40154000f42440c0c0c2c01c000c4a81c018140803080e0796646003240104034084007141490744c1c40340042100c0c3c90074820082c29601c46e031102828901c0c603c081004075519641c480d032007688100180001603d032581a821313501c1960a03e00c03100e43c1d400b400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 346676483 1250 346675233 346675361
    0x402070609080702010908011802010809032116051608030a0b0a121e260d1802120d05041205010920100c020a0b0a0215090c0301 57
    0x6400d6a0800c0412410700c2000d0004048081c400d07201d210020303550b05000ca0982c0c0c10114403c0492014684480165001d0507106511a00c144c054a141501e0341e030b60648814030000283c02e1402c1c4110400c840030414a81d220b199060504119082500c0341c610412498500c101c010010381c0003201144070700c0034607008084c4c085402418000600d894200705d1855245c804400d5900e040001c07068080003400d001e421030103582000d0420704940b00c014608585290b22106424481001c021017036581010388101031506200d0b130b080d01c0074082c80e0b00400c02840700c690003204e81a0404440d02d0205500003040310103d40d4219070103219501316061180c014403071008050402d82c0c80c2101e5154840c14840391404040303007102d50f09140307203980d01c00301c0d191511504000e41054160005011411a11002d017060000c18411101d150360740b4013100506900c261490380c0c00d1f03400717482d501000c2e01e028000d0b90200a0910815121170740582c503d40e4460140700c43c10103202620700c550040d04130170281 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 346677733 1250 346676483 346676497
    0x2060c0f0301331d010c05030a03021605010e0c100f020d0f020102090306010e0f0123090a06470708090f030a03090503070b090108040b46060b04060309020402 70
    0x20341c0503c0c210b50142c050070400c10f0010180094148078034900720b960103880c5a00d15103030008002c6013403190355038041c0c001f90320401408200174908004080040c0e02400b03000075288100000d88030100805081c0901c0d0240c8030f0310b01c2c1c14060412109c0380d5480d4005076080c11160540750404d0751044100b2f05900910919419070703098003d520002c00d10007840c1c1d00103400f9482c40003020200b1382e41c800c00043c0a40031070038840529412455403580e5803418540e0250460220540000c17129038400d805051601c074480700300144c02c0c1900368000c1461032942d484801070b2207001f042022100d001042d511511035070310001c068080100d06440243c56400e107400407603a0290860b2482062418013a080106500c503451291151050100d41030304800180c41c56034070b040e140c0d00020b868907a00c402c500c0360010400c250400c510f15080c44001010054060000f09042000d985408004000c05031229000782083c0c000f42050b408100960059089a0480d140383c60f00285e0000c0c548002006071051031 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 346678983 1250 346677733 346677809
    0x30102040e0907060306051f032a02060a020a0e1302040f06020703061b120905101a0f0f030d0804051908120604110313020307030501110a02060c0f0301 67
    0x3150100704849503144041c040d2200008903554140c1c1c1d103408409881c91802000d802051070711404054030041060800024075504002c5860030f29807000914034130303c0703000ca8800814152109100c040d010b02c0507541100c001d43c03081d4500000e40c00e0140520723140c110703544e00680150b01000841780761a415580a0911400c0101c446035488000940d00c08150000381e5005280c40005d00b0003080c10b0340d07040800c56154441c066811411110a80213200c0364500b51501e0084008540454900340302c0d29100c44403070a50035405002c00d4040c40060b459100d05c450080c40c8001c0076503840e41e000103c800c0d0151503803070564065541d0b8500300c0c0c01c280c0705d04550305041040922003020080500007500f14001c140c07641d0724582c2d54050800040d03c948104c0710421190030400f0518078689105400001030000d01142c0d840c039070300d9540c51700b1a8020203006003c075001050580c40b031036045c482183c0140c68908114202111040840d101d4441849514000d08008103000c0b000c150314083d100062200d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 346680233 1250 346678983 346678987
    0x13170a0e100306081213120203030d060906060e0301050405060f040203150705030402040c0315051c0c0b0702150f19140c15060307030c0506070c03021201090515060603040b070509030102 82
    0x30701801818a40c01900d5544c042c0305450507406800c1c4c8192054480826507074040c1d54a42015040e1842844030f0a90300750000700003d0b05503041900400d0010b1100090000b078040c600700e4000c0111003062071562081e4140014080402c1300040d81c543c020f2089034aa00564a46200003407401401f40b003004810802582040103107608500590f200b0f6000ba42c050116540c108402c07411150600030352494481e1350781041c8403c0c00c04910030094105401d141e0740030b07801c01352111040034811390720040c450407000410000b14240040710491f0000000c1c0410305102940c142031400740a030108d89007040c01552042190a441110010324490141e074505e961203046211a40c0c8070381c21110f4045803aa0f80c1d002180c4030b401c001507080300b01ea402420802089040c58200011a07000010550741d00162800100140c0c0c0c500c8a00282d660781d00000085d10b4107646002d90903c900003040b080300a241c00d0401c00c407522180100d070b500a07408071402170716980c0c00030181c42c0d50041030308840d00f542c80 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 346681483 1250 346680233 346680259
    0xc2b050712090f0b030118050403021c0306080f0105041101020c180402040b09040501020703021b0a170102220f080a0809060904090b130501060509010302030d1d060a05030f13170a0e 80
    0x32002c005c0d816518103003400030004141c0c2e040c200a030362066800900580c08421090713076000c0441001241c500c180c2c80d01007141aa2462198a030201c03401d50b00c00a40d5640040c4002c1014000340f40c2403d400a0000d481151180340014907400c599030040c0018105c1c010020f811965107500000000100420b4002c01d4101410104d00039000090104c002d882051143c04030128000c5600d5502c510042070401c1c094100244000307074000c424005402903400780190407012560800c018210b20b050301c1882c0c040c03071400d000200d11807441d81c069010341c1c1082408402003001441107840c00704095810340c1c3e440c080000030800810300e2034400341c1304080c05014000a05180f04040942c070b030060f00284005030300da00401100c1038080c0300c0294540d0010a403420a68020380070f10309080d403484441c0300f003030040c640400c0043c2e0240c5014400910700004200f408176121800c650800440b040305429032446a039100c1c0000c1d160040303510a0500800d00100342441002c21200c0c0c807001070600c055203c9 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 346682733 1250 346681483 346681499
    0x70933090f06180504020604050f04140103080a080a0212041e05070308030613061202040518060403030c0f0302031b031302040207140111032401090801020c2b050712090f 75
    0x6070b8010b070700d03120400f14001401114213001e4903001d20340003842c1034645442c000421100014003413605810a850f100d80805980340a80028001e601407950b45d07999405541c0001d0140200411901c4028030501c80300c032014008040f401c3e40702ea84858255450407207640210105080d8a100030500c0c0f00301031021007041400d402a5004000580b420000f68244c50020416101540545240d03840340f051030300d000d032a042d008030f50405000030b0b403000c00c4c0320503050607820024110b80503800310b5210031544840341d034017510348070842c00075103011825410301c08050176403041c1c502540344c0c140c440400030685065926070742d081c9140e8001d004540d075041910704603501090101a06815528019a242e07051700c421044030b20420900b4944000c2a07000011508030f0200c40500e981003095016021590708000d10007041b06401e1040100304080a6901c62200c944203880d170700c0006184001000d00310380c3c020054400c0d46900c0741156400740d5006504841004080d84080d6000ca401d410001e1070b22 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 346683983 1250 346682733 346682741
    0x1030c0b070602040b03090129150304021c0b1005090c031b040b0705010e012403060c0207091d0111090307060305091204120b01050a0e0c03130b010f08070933090f 72
    0x20b074a4800002c0030f200040b02035070703e000482708a503042044500d488078000f0b496030045603c90b100500400d0010388a00c610340b418486180210350410b215014030490414071401c840050078101c411103000c3c07824280140440c04050a9008e01004c1401204021942001528085c1544207001a203034069801d185010708007944006015510307100c58030400d0001c00c00d050500350348518100c590245155107000041090312076039400c50259540128000d0624003441c007035020014070b1143c45180081340982124100801041c03403410800011aa9481c040361030070840c3e0490800080d40e40e0740d10221418441c10b0507a0526041c2d0018000c0b4400b0f0344d00000144040c040c180065a982c1c840062115601e0a030280c20201c3c84020001602c0011410085a204c58426550f9003441401d40d590703c0e8251003a0050744011480404c10f10251004000b130400602811000f801030114541900c0f0b443c03003044007880b04000b01104100368500c0d081c0e40c400b0013094010300070042d00300079240f818018 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 346685233 1250 346683983 346684001
    0x109080616120b01020d0c03090312081504091e2102010606020706090807050402030a1d011a03031306030b12060403020c0a15020601050613081207031701030c0b070602040b030901 79
    0x454a25403060b64003403014428040303040c4060f001820320700d0200d4825140000b13102000c4040001914000c000101845141c007081142ca0701c3c0c01c0b85504001c0d0001065009840da00b07801103103000c109001207141ca1000414440d00282d4100742403d0a0500001c10b40c001c1c1d090107010083c21059486081e0305500200c201c65065003981e07141525024100d03200085445a2600340d0702009041c05103107410703402560005041000004c40d844124511780034003403440420052650340340600e0240303800400e14443c00043c03c4024614158040c4501c10f03544901d4001c4404250ba20316403407034152a41c1c2c0400e81421901001c64105240516000b5620150840858003507002e00c2c0c4c000a440c450f481c440008620160003610180e801d000501c034454000e0100c8008001c068100000c5404041c4425510f0090120f0380075640c1c030072414060f1588a128090010044c640c50041000c501c0e040c030004203482c4480c50b01c0707a4403d902d0800801078011500711000324880001031110451301540141e01c1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 346686483 1250 346685233 346685237
    0x1305041109090a030507060c0306180b0f19030602030a0603080d06051c031e020c060a05030a0506060f070818090108010b01020c0301051006051b0d020a03140f070b04020109080616 79
    0xc00e540d07401902d500c1c0d40b4101c60082c0070401c00d0207903000150840c0c000450700085450f00050056840c001500c40c140400e000b16541666069042018100b480c80c06408904c25117910650492413020541506040d200c0500b47d01c0c2d010000c01d01d54011600400000c2d500000307031300e441e601c020b01c43c04010026485501e11400740e40002d0b011f02c1286116814003250140c07200d0082104081140c0d040400d080192021806415015200b565825020b4014221103a0310141c99140c4000d460007100e03c06052148109400c0c000c540f40041420116111540e10000b03150b298132194450b1040c0c01c15005071150f1040c5500b00106d00394605601c0b40b41384c07035001da00b11056480b0742030502d0300700c80c015142030003241980001444102d00400003040240190280c3c40c140101940742c45044c00342d10101e0400580014040c40c043c503502000c41d42030041c0d001c0303d407850315000f0103038030909101e40c16005154001280000e010b580c042d20a02c00100101c030161002783c030745400d100e0b450407289114440 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 346687733 1250 346686483 346686499
    0x801050f01030f0f02030c0909010207170711131e050703180c0918050a0c0e011703040501032c031b01050136020d0501030c050609030601031113050411 67
    0x204400500800a040342d82010940f03040d00e010f51196128401102010b981500c42c0010740200ca8960000c0705116201035800162070319000d02e44080d80c1c881c07809088001000510860000c648051100c0030070301701c200c41c00c401410010507400c0c0035002010040618101e01c3c615000010a50380000c3e2086116690402801810b0131081c5505412604050440640e4000a0100500a0380b04845104c1c04e040d841c80c0000c00b07540c0d0300c1c1c60700d25842e03070031202501c0c15201040898184c41c0360602414640801500d0400c46501d0b16a9a0145d44944c5040685420461841c3c0098841d0301c1c001607002030040c49400500c011855695000c40c12007c0382510700b056403030101d0010301c03803a4180d035900d80303401000e80b400c1c440c40c0b9903c22405014010010b000f000c403810001032071004061107240b01c43e010a40b0b41c91400c103a0380e000c0d9164021070095600b0440480c0c41da8000c00c40c5410340b5804440740c1e540e110380f1000705090b00402201116135520b8503050205210802c0a0b10980b500103c070485 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 346688983 1250 346687733 346687741
    0x30f0203070f2603040c050109061407060b0f04021303030f0e0a26060f010303140301150305040302070f03050c040b03010204050a03080730030f050c0906180a0e01080105 75
    0x36568850150003901100b188032012000401400d003441400c1022201c0004681c0001c00714402588103a80448030502c0c0d440c000c100a503040041c2714014500e90a0454010b00850f440982600c40c098000300030b180c0e64021941d15944081c0d0220440d132024204544808005000c01560074840c0010303408500c6107034421003040c1c40b840c0c3c619000d0030040c141000f814070f441c0100340e03401020000711040c16203c401e035030130505040168038486e219610b104041e551441c01e025000261662881120032810030050088214605e40d01920b480240b600207415511428202c0c14540a81c0000440c10240c0500000707002c3c0003d04125200e0382200d0030040204801c081500300e1180d48109504000164400c1010544d1031703026110907800b44c1c00c1c03124800464111600114503040c41818a541c40c1d9070043c90303066141c031890a2000403c00204440e045c90510b66956000d5402c10310300c035070400680c0c440f00a01d500c20450800c02c000c0d003040003968450600c0c019556090050035030540c6020005 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 346690233 1250 346688983 346688987
    0x5030a0510120305030a0230090d0512060a050307062307050d2102040e0f07080702070519170309100306030b04060506210607030b030a05031207200307030f 69
    0x80c0441d00702c0c00092904408960741a54107800041c003400c1c4242e824000441d40c0c815448400703094110120076010440c655400388050a000a4001400c90348000c8648640c141c02004031400007409480304803130390b90344000140c4260840e400060b00350040120000d4030701e410640480521002954000116100c05100131544c000da000142c01c560180444d0380c00580143c035860300c2034400f140d210118110381d41c0c9101c01d81e4040d40c030030490350784a581081035079480011100e402901501c1c10b0400c0d42890b810081d5580d03001d0050501c5070700024408103987c08107039004402403607440756010508502c2031030b05840e43c103c4103407140150a00309656541c103101e4491318040d641c0c4130220b52980c0c0c4454507100000c05000300483d80100302210038031610002054055a94581c203001849036141003075000b026a0044020b41e4041c0d40b008640d6000184007200341c0d40e02010f4000390185503170f80d21204544014a40404005844008200294140c400710090001d54000d407a29400000e0011007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 346691483 1250 346690233 346690261
    0xf15060a081c0305060d1a0105180610050a11060406090308070c1e0807051005010302010e030106050a05100201060515042405090111030409060b030103050c010c02031e071505030a05 80
    0x1101c11982d0501d4070803010305010b80d010036005480a400200b08074404c1c2e480080282d400030358540316044410040200d4030b000040b141d9281c203408004116401c0403804181c4400300900384c2d600340040810300180080c13141003580741011342c08040760920704060600c4c40007031031a80000da00107100c3c100000d4020b03001d2807000c01500e51180c2c3d0341d07400d8228034031a1180c44036014070880b1100410007054000c0758040022204d4034602a03400902d5525500c009046003161518142c000d2b4144a0100f10564401407070000b21030069440b60a03c5506102c00c80c0100001c2d0405035120f222228002e0003266854043d100756100e4400314010300f1034100300c2c0911100c55030b0710000044e900b00700389c82465110310b03800f40b441c0ca1040d00300c0b0b01b020381303e6164405941c001d40181c90300710404401002445030403c1813442004d42801e1074100341146401094448903d03810f08210101c000044402280040001400030041c10f007100e5211040400b004186600540d0080b5a450928001c02c2d580091424 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 346692733 1250 346691483 346691503
    0x40218030f151b04030b01080313090e280b040c03110a030f021c080408100b0a1d09030904020a030209310c210603051204061409030f15060a08 63
    0x9803061840d41c030204900c9043d0038110075030b4081d400502c0000002282c4071203240c0138101c100091501c40c0c41648444003005540c0d40301c0c000709800c140b600200c009000c9400300146800d42c510680358030743d040c1c0d0f85130b0b00000243c0040200b0b08500c00c010a2122440380b400c183c074402c000724803c190398142001b40300072050002829140c0c0c1c0f1840c040041c58080001d40303018007200c25120380c200f11a102c40010f50840d03070000065800ca000e901c0034603100b5100d45884c03c00704440c40000d01e8241081302c07000c07000d4403c8a6011070001c80c00308010000403c1543c07400c0d4402401550303542c19000c4014040d400050503d8010901c03da190300ca01d102c0d1801c8002c1c0203900000c000040030594841c41c0c080c003000300d1035505018032440c25041c2d00c00ca80003a03102d14280b0a8001c280c1918602d82035181c1a1440c41048030b0b40e606020920070103600c02ca804008010f031786070365511254610002402c150107038100788a244251040c06d2a011920b6100c503115510072541010141c0da180402616010902c03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 346693983 1250 346692733 346692763
    0x702030d030b1507051009030f020c060c0706031509022205040516030c0507050105010b370507080d2a0c0305120a0b030a0303051005010504140907030209040218030f 73
    0x3541642c502c0190f0400b038141c0a024900311805410350200b03020481d18440c1c02a0000f80c4002c0c105c142c102e804000d202c107203000580c0d115140503000304695807211054000c0741c0c20141c58100c0c0c01012003406040e003014104408c4119030341e903002115014200580000c0100d0010440d100049a151034402c84d446140c40d400440f0b0340040c4090114010491000d56000344441130000d080030480900c51140030f01200003000e60307107002e407000c100014041800214901d514000d05980159060710b0000c404041500345552585650301d803c02c010700509113010300c030b503107459000041410040e0300001105c5440f0f004648174010140215036032250302c1c6001e00891410001c0b6440c1694030f0401d02d5225105801c005000ca00c0040000e041c0b845d203940580c0040d0302c58081c062801c1d00090803100400f801d0920130300c2c2c03514041404144120000c18075119446600002c2c0380a030190701241c0c41080c004104640e202c44a41104050081640d0418064480e2021a2200b800c0005d60341303406144070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 346695233 1250 346693983 346693999
    0xf1a0105030f100807080601031a0402100507020d060218040b0103060803120a06080102191d13090510110c060a0203100b030a020c10020901020c0901030b1f050a0603020702030d030b 80
    0x85103100b0000d0300280c001d80c400381800800140a90060040344042c2000101612895155040c15095548414022809465441e05100c01644c442c030140c0c000d084282881d44d1500b0b000d000181c0b603c411b000010f0090f0340001411161501009042c1c01100380403281001000a11801141210054021541c0c0e40e0300c200300c0054400700c94122140c0c05600395001103021900c0302c855a007660400300a45009038824400c2c4140030360010b802521000051180c0c0c4072401038400014901d042c070f070082145080e920b0f0b03280e0043c888103204a0350101c171861300500040c1440500b5000d03c3d480383c65841001c2c040d00c004102410058001c89000303854803100c900c040b03414901f41854aa0000e0106050241c1c200030f00c5490110510035002450105480142c40744500710002e41400380004c440e03803041c0c0c200001440040d40d05480309801541948041406040e08880d600302c50145800582d0320070140d100000301aa4036400811a43d8030980039102d8805d0f40100c00d80550320b52520031036001d288 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 346696483 1250 346695233 346695241
    0x1c0f0f030f18121403070308220203070501080c12072309090703151a03150102060403080727080715020303131217040f050c0111030d0b0d05030307030f1a010503 71
    0x80303405a01850701a04c081e14118003001e0359145554400c0c0b9044000c1b841c9001080401a0740b01d0100024140384030300040005129400680c4486e02c9001d02d0381031003803400109684000e050181c030070842c2c003284480c3d05070814440181004824803410090031204940314085d101c02103040e581c00003030203800880300d5111500300340c002d840300c8141032016404044002402079070414040c100d890214048503502d04250865401c06400000880d05541c40700007400300280d44040c940d0340c840d4003441e1902c0380c0500000030354008854050030401d040d0395203002045041c2d0101c0c160045840066901d04a080d40c1003080ea2a8003044813680b12121401d503000d008150742c6030450b0b030a0006490021a042c43c0c0e004034820380c0300c0580b0140d0300c0e0802080018204035040003c4c0000803000d0802c00321305440d02d55855a2481803c000c4a032203600e801c052421507d80c040020074043c1d11000750782d102d2610b10002030050801010450109083c04000c0401034070403400c031001e00806070750b5146903035a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 346697733 1250 346696483 346696499
    0x1e030305040b1014120f100905010f0b0919060b0c10050106031401172a0127050409050f06040302100614010c110d08040602010209012703021c0f0f030f18 68
    0x12080c1c078491086c010200d4800d03940c10140110715580d11300312030010700300785682003290031030b04841d101141c5585040510401a5074105d0400d03402030f44031000034041014141124040d200c141d200000d548030119100341e800c14084ce5560101201002c03c101c660381e60703401241910811040075110f21040801403002021100a13170290400150848404c28064181c1d8043e010010605956980300c40090b01c50960b4040c8421010300189240b040103130103900084103011809102e800d125680c0d408462f020000207001c0c80041d415a041075a25500e820b050182d01d910500821070381e0249000c5001c80c001014003150046420183e548980302a590740c0e031080c40c6010300065590080074002d010002030b20711001040542180d81c0090703140c1d40c4a00c00513081600d2001c5203079000700c040c0040110b00364042c0c41c0d0b038212501118126030740b103c6161410b461041818000e0441280c81000d002808102c00003841058845c3e03407544100c560000e822900d044201ea40141c94029610040140762 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 346698983 1250 346697733 346697749
    0x12040303050a0e3001060b0d021e1b1908030a0c2313090203060d0b0402013509030306030c010e01212708030c071e030305040b1014 58
    0x1401c1d03818040042c1c0b803060005400110300c8403400000c8421000401c0302040041c480841c0c90000000901000d41000084001c40c00340c1448d5261595001c1851002d01c4090070080d09c45245414120340d60300340c51401000c41ea01d0684c9c4030500351050048c2415440521142700150381c0d003000c600c0741141c41320700700c0d80c01030145207a5050811150424116115440048104100703010741c402507602c042e06282c00800c0200d075448054541d20600c10444651200c0101c0c4812030b90000f00254075981e6840182c82090b0a00e245000d00000880b4001c0d00c50701c0801007602c1601301240b1081d807a40c1e00b10741c0c981d5034070080f10841d0b0503801c040c00d100101d501031540203804030300c1410080c80740500006480d060085455250826640310040201c11034030100c01c903080da030030080603021440c0b640d403149035441c800030b880400ea44a00241074000e000903545a0100140c1940302091407804506008001c1d01042d502500c01c18150004246810404280f600071244c0081c030071041d03241940100700d946 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 346700233 1250 346698983 346698997
    0x619151e0f03030813060b0636180a0e0304090c03060e041a040c09090807020f0603091209040b0a0e0a0510080c01110a02060307020a14010203010303050904150512010614031204030305 81
    0x503480301c10070b03400e942e5814041c20403100004440f203030150080b00321041e1184101814000600214082c9d40c0c0f40c3c44280001c050405ea5614000341a203c0c01c10090040c03280401d601c202d40000b0401069154140e000400f005c410b0780e07000c1c08020b4542d405800c500106890007810701048030b2840149011a10210340d01c54050307840000ba042d5201c09000a48080f050200d890000001c0c0b4041140b07048c4413604203004c1306440c8030f400c614003440748507640c200c5441100d00d5480b001c01c2d400059981c2d070700501d0088901600c03031640d1540d40d00841d80304041c155001208030b81048000740d22030b0402d081050446140c04001c29404a0240c01500c42d442400304410050203006030482c0980c485400441c003c0000b0b50003880e44503800c1c20030864a01d40c0c07a0503014207900400c01080803991000c142e0b136048a08440020301090f056001e01000341640c2e2006402c60004c10f01c00000506c1035000400b00c2c2c4000d2544030f06405020100b541702c2c038861464040d40c1201703120520100e8031580240c012 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 346701483 1250 346700233 346700243
    0x703060614131d160911030f0414070f091e0b030309010c060209090f1602010b01090303141201140112110406050304080f0403050319030504050619151e0f03030813 72
    0x3000503035941d06801d01c40c100c00041840c0801e4101005145c2e610721460fa04082000c06d81401c605100e02001850b007806040940701002410f1700195603142800000000c202c41d40040108540c0c2d0000c40015201922941c030000744612100e00c0b091701140606540004010041c5240109142c01903414504d540403d82e11181d003800700300001d84505032481d010307841c4008016001e02e008401c61141700140d0006000313390500943d554166084130070842981c1d0300d401c001001c04070201072110f903070103034000d180c00303a4003008000142c242c008410781501081c00e070f8403415030710090140340c002ea8080a02c8941c030304078200030410285110f24081c5400a03c281030316860280d45029000d659042034005550781d410002d091245003200c003984114181146c10240203600d03b58454944500d8021300c00070015105040144052038540d0020900070407034101000000d48407040260000090500c0b490000b402840105040e00141070607012a40e05031782d0094240e0702c01a5400c05400c40640c2154 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 346702733 1250 346701483 346701521
    0x40317060102071e080f0307020306240405060d1e020108070509031513080703080a0605220905010e0102040e04110d050d050a0909060909060615090b0705030d0509070306061413 78
    0x103600034086c040c506000d000100216240c155030b004240c1800006031800307413407100d001c060202e08050401007402440048800044e29030360380d000318070300440101006001244c0e40c2300b0169545200103c120700035000380e07a404c500341e48100c02a60f9074030603080081ea25502c1308030012a9541141d0280303602c11603a50514140ba602a40c0e012001d421090342100440d811608200100c1701074417405c0000c00041b944691011a0340ca10030250441c00a4020400383d110581e80c802c0c00825003140301c10007a928021035855581304009482000c0959045032044800c140040c1c1500e032000310114001d4122000d80100003000000b0358444c1e000d44201424000002c3d8000f5103c901845114010220f00e000840c0324a12032030700307008541c4140c03c001609071030001e96007049030784004c039481030b94901c220169a5149a00342585940034010148941790704000070030244420114204003203a10649080c0f148548907080f0051920207400c900d604805151094031210720180c0004500c0c0440c400303d0740e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 346703983 1250 346702733 346702739
    0x105031f060b0c0d02010c09060e01111f020901020c04150e130602120132010f05070605040c03120305010501080f0601030e01060f06110c0f040b12030a0206040317060102071e 77
    0x141c050b0010340d91620f0303581103050b20b1402140c080c002e040360482035251804141c1d003070103401342184102c501c07075504100d1015001c0c10508020800c1006200003186000340c003500740c03068000a5400000e5407070042c0503403280b058070790a103405442865800841d02e80344080c10119603100d00355004100c5528031150311b807140e02203140b0f48000d0103080b10b0240c1a1400c1d60420749000c2041d034120107003044001303e07080481d030514915612284c003d00c09182c00180c103480f41398115041d005c0e400016017200d00d084140f00801c400c0c01d40201c1101c3c8600c01c5040c9504e41d0747c8003581101c00910903a404039000e1800501580100c0c402143d00206c14140000d00c42600c1c2240d608540140d0400044644004824000396801101c0d5440e6440301c50b001340015020800400c4805404e1000140107079201d00005e40245d940f2490710820809543c216030702c454445100940d65103081d182580440c60800f810144e441071018841d1042c45d060b0001c00b4103c1c900100c00e100b04148003400344041070012004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 346705233 1250 346703983 346703999
    0x60806150313061401051f090603050601050705120c190f060203180604120e220504021c05030d1104081e030d0e060402090703201e040303050309010b01080105031f06 73
    0x82086106100403c502c4c0f036060100380844040600e0102c221000260740040310070358031029070800d40c0c0540c42e000c28035459200059071140690000140300d8084c00507043e0b08800424060502c0c1020041180d00b503607540680d80b01440c400305005044080d07803282c850081aa15001075801440003143d855034414000119402d01106442c11190700c0d2800d02c4010703146622010544106400300c422007000101694040c2c068502c00800b890441d85590004055540384948a488400d00c2c4180c3d00c4030022078036080e5100da000304105a080d0785840640d01044140e1025242600d06203801400c00d4024195101c3e4420b41c00b50307401485100c200a9201802001e0240780d803085070341e42c0104a0740c2000d20401c40d104100800314010140341a008902d103041c1941803218200131100e045594142c86200400d1030041c0803500c030b0180c0c2000500008051384a0011403242d0703180c900800000c0d609400440e002002882601d0b4198060400607203280480641e00c0300b20344004e100011000e94510318 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 346706483 1250 346705233 346705241
    0x11070b0408030712080603190c0b0f03070f020a1203090c03020a09020a0806101707050f1605100c0e040e03040f0b03040201120b060f0304080c060103050c0a06080615031306 76
    0x70142498102040c0001004607140307040c0399038510b13410311503240c2c03400c480401e81e1080c86400f0401d061040c2030304903062040500700c01000c4d00411000039901c1111032400c07402684243c900e040040c0007542c50350a600d01c0411200d020980c01040f80321040260720088020341403864099030319400504c0004010b0b51071000400c000c000b05000584c5480b404000034002d081d005041c20300903950401a2145540d0003020020504002c5032001c100343c0f5904001c5034240a2405045032001c40051109084040303400c00b0102684903800312600c60b104003041c0c1d070a40300c4484a43c808143c1f50707102d8010a2616412050614601e18201c034201030b552000c05c050b0034440e5000c0e44201000209100541d6806044d250801c4002c0c0d00a101c003903902c82c0030550318443c158005644540100c00f040801403804201e4034000144c5d0111540b07540c41c1c1c2400d0362a1586682000d10440140000180c030034000d008182c400c4800a200b000d15141da5100d9488a80c4002c2c0400c1070546500a400d0008803203201d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 346707733 1250 346706483 346706489
    0x30901020d06060816031107020603130507030506182e1509090201110303041104090602070209043801170c0607030801050f0a0e06040b03010b1305040b10030203070611070b04 77
    0x604d0076080c0c02d01081001c00071801240c5541010300f030000c8052600d154804641c4a25815540c140d41c03230b541d00038a0002101031481c01040c6008200f800401c4c00000101c05008291582d02c2001c1a80c09030019659056005600da0082d4a04000071046d03a00c01803d042d45400000000f142c0150340025000304032604d600b111400340e694542c84801d41d40d1200d01d542c0c440e41c010008502d1410680c881d445059800300b480c9200710745540c0c4100030442d80e50103440280740d002c2e0a615107802d0510b010350701c080c8200c00015135442088010034489010001c40038055501007404d1641b6401c2108681c4440c5074002001201e02c280101d03c0301c5901c0d144010110300c0c1c0a036803081c41a50620013085484201003e00620a507031001051000104011031150030101c2103a0002e803031404030380428050705100800560202d09a440000e0070081d50b0406d911076440740c0200d40440ea180400b0f4801102240000f82d09580300302c0090004038056107e40710310080000498030402e5850000700743c1c55125070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 346708983 1250 346707733 346707737
    0xe1507091214162301030216030f11061b030a1104080a060f0603030806210f15090d020618010b10050a30151809020108070207060c08030901020d0606 66
    0xd4400e9100744400c0c007004150903011441c0c203810618009030900860740d614446150020303d8984d2898a0f8043d604840c0c40200c40180030304400307298100a000d0107140ba403501c1c04203445004041d4036031404a4030310700c07030759514801c500d4980f0801d648800c181c10052250b40200e03611000011601490700117000101104402002c0c010340c149440c50a0b5960f402000a800303007080814400290494942c80d40061700b9640c440486401030f10744040c107402265480700c1c0c0d000304044201c02081c04164004006030190b60301c0300c5519120189a9075100305d110400c0160000c1d408121600da21410000040072004000f01d0142090400075075601007001014010410009940100b00d40181c1911842c008030241500300d603807007000c0c060050800d0b41e40f82e1075007a65850300c526008290342072180940511234601c00e91105040d4008014a02500309034040b822507000109654130001d94032080d58425034030014220030603a100c450903040a050305c000340d5001d01400c0704a10f11486101d0003040a5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 346710233 1250 346708983 346709003
    0x20f0d05060a06080108060604091109100f1410080c04090c0807030e01020c100c0219080705060609091c0c02030607090f0605090102070b03090102040f03140106090e15070912 77
    0x5400c02c03414404903032150050090441c01080402d030085042035204c2010b47c1d002c107074003000e45806000941c83c15051070f80100301505005820030b003e020300781a03810b0614640107180e100c01892140b05003149100f60300044e58080720440c103106405040d0824840b0001e03d00301510f031500b00003610400c17442c11000585c13030070400c0719245c3d140c000d80b0403102a050003140342c08225404c45441700e500a90012116484003800c58295100b00a00404003030380094843c2000814a00b1216a40c00740703400f0f031b1311445140d000c2034803450880b61050040a01400418068415402c030407958040300500c48203100010f4480005038805204861045c0059500c040d03141d820b08046e00b001c9946504a2004c024090220800603600065160203440a44894540300c0e03840844040c0a4407580e00700303208180e03d0282c004208034400041a03145270600009002054440070f003030040340c40e003216444c20340c0c0c44540d08205040c014040e058000e0814a131800c281500c9691141b40d4031040c84040f5075030031f08 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 346711483 1250 346710233 346710241
    0x10b0315011d090322080c0906132004080d02010501081603030507110406061d0312070f02040906050907210203070b0d1b0801030302010b0a031e06020f0d05 69
    0x911600002515500e1924032a505007060410040010110701291000c0e0b1004580c0104041090701c00841c0ba1a17182d0f440c89071001802c50b4111200e01c10110180705000034440da500d01420903074401c2c080034142a1064402051a00c003804c82e482010b44d500c0004c3d004c00c10a45c001c6001440a03040348402400d22544400e0300900b1030f44141e010b00100e400640c40540701d035205c014450101d03500f601d00940c40b25442c0c10103411035a841032045502a103440300c000307000d43c2c00421f800c181c0c201c940401480d140d4410b00380b6031210103000840d036a02c00100a040e0001d041101c80001d8079002420000e0001400d40e0340b45c040b90b505840102c4681d010550410907514034002d1080c20702c0c513107004a01b5441c0e50f075020035956001402080d90340c90303020a6003141812160311511800a000c40359040e0b10502c15005070541d20300303010a0f070055003060b00d80401410702082081c1100d1323000d980224181c42c0d80312034035034240b0005803c481064080001001912040c00546920036000600198a0030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 346712733 1250 346711483 346711489
    0x2a0f0e0915060d06091127030d03090c15020a0209090601060804030f0c02101d1c061d10060e070516031404050910090c0f05070314070602030a0f05090f030405151605010b 75
    0x481c2401e80441102c0c030038803002540c03030109c4e044100120710700300481c08903040d14160095503010f41100340411031909508642503030026000010314003d031a43c28150f102c004100d910ba040900510022411280204000a215441c1558100303101c0c0b030300740c113035181e1a40018041e1403e02c5120b4002010130714000703070401402e080740b00c50754412100030408040001d5400c00300040d980d4007610b51030713643e207804007c00031a03000384008a40702d0341523a4050388040c0103180200a207014802040d02c2c100c2c00103411070700039000c4960764a000c0d40251613122056808403840d03000c0c1001d03441c002d2014440001e00ea191004014040c1c100100b180030030a0a180102d0102d4030030f504420200720401000c0c000d09500320045480300c5800d4940310340007c00403480030265204814004212030720002c100403da000690042d2584880c5400900c01c80e11403140440d031300c041d2401241d00e2a0000c1008001620304114044002c2030194902c0d07052600310208020320900c040002d85141e512100d80c40c0b0070b4a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 346713983 1250 346712733 346712767
    0xb0f0a06060c02010c081b0303010320040507021e160b0705011109010801030b06010c1a0604060b2106040e1207030807090e01092a0f0e0915060d060911 67
    0x4441842c0420803101c5540000f0312080c1102000b4051010004060421644403120540307241e9002d4101c80da6940d403403400354012044594901c0c0c51891000700d00b8603a2030f00e405440d0045ca104d500a010101c0016949564100d048111030184d00c900b014284c864001d20384100000d19060311083d4440c00f0500b01603003135402a032184429031004100c03001460383c028041d1410b482d0081c05005442d603459005a039254a084400f401d400035900d08603911080030740c42c1c18804e80c030070385051080507135032070b1601c9050107460340c40e0f400c00038110340b0b040c406111207100c2075000e02d00034030105079a4000749490703040480e00074007035440f4a0002032075818107402400a47d00440c107403902955007842e11480c81c1200c5418043c041c882c54849010705101a4044c440704c2d940b006d50701005890035003a10303014008402c02502c00c80410100540300700c0910301607001f20320900421504100c800351200c10020f495111140388880180d076070002040c0c4188a02c582284019051103450717640c180080030f60018 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 346715233 1250 346713983 346713989
    0x6020a0b0c04052103120c04080d020d0f1d0a09061d0106020c0d02010c1b060306060302160f020d05030c0c150a1713021305070e01020312130f0b0f0a06 67
    0x394400c02007007007a9200d201c05115000c0f00040c44e108a1281c0d003c0031400d51150070038500102903040c0c10f021011b514040144200c458420444000910048080c3d0725000b0140d000000301c2c2c050142c222503503014049100000105822048840ca41e0300c0000c0c03803010a94100400595642c441070080c03844803c0d400c80145400401021303550300d4228029a241031051006004d002c7c84d495002c1103900804401c08402d501005440e070841c1742c40c0883d101d0348190300c181c0c000030b0b050000c001801402842103400400e100080e10030003001c5520340c001c1d11300100500303e80000c9104010008600180090100314981c1c4003d45001018001007002070403420302d00d100c1c15082003144071000ca8020071103007415501d4400c040101c0d81c0d44942d820401c051000e01179008540d0310162071207664590302280c810f00c5107841e07510748500043c0049980e4060080c0f0031008c14032003404a21000400a0b03c075543e179100c0c0350903042040260751540652013080c1c03815658171160f5024000c8055041c0a0500a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 346716483 1250 346715233 346715251
    0x906030405010929040f080d05160e0d15090512030c0403020306070512041502090402041205070909080f0903120c01092f0919090803221a0a1506020a0b 67
    0x194131100140c2440344019100074014051070f107490041010b21808d880109440034030400640c98400020595562000014400208001c025611a00d001e1181180084d00709030341200da00150840280200b61604050b00c3c0b5105044420b034802c810310008512409007042e001e80c9031403035423051501d40a0050854024448113020181340380c400180c0780c680c03158100c12242800000c482d2040001c0c0b00d400080c1d600203000203030106e1f20b00c0c00122222055841642110016035841155804503002d4a03801031031500c0030410b41448004500140202220041c10380b005020000100c403401d500c0141501c8560b5100c50716181030002c600801482d01c9074044441070007018a404c40310000c00d14020441c03183d076209000c9000d15000c402d4100700300084030010040300f0804d04040346142c000b21101620f24030440391007a2602c1260605c0241c2d950302c05010000664440440c035000480241801013090341ca01194400d60816100701c00144110340152200c00c40504108070351240043c00105 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 346717733 1250 346716483 346716533
    0x605030706080a0c1106091617030910051201030b010617060a060c230102040e010816060f1101050f070e0303120c0a02030415050a090501080f010e090309060304050109 74
    0x104540000d48258003440c3e4550026020742e101d402545c0825460b00c841c0c4c07440c030a0a042010107000018421500c183c140d188500c6d00d503946840c020003000c2002d5802c4150401d0012034900c0c24807c01d510855209800c001d818004180f5081d1400c001c01d0b401a81d0b408141401000303425007005c00c0c1c0c0c91078224488034a00d0342c0b60200c0800d181130000d201e5901005203440201c014012200f600400d44d003645503413905015090150b2901035040b40c044d003179580b12488000201c1440c0003a40040c8a8003401c0204a858504082660f4500401c030400c1d05102c14030f1000203603ea400c2c800d03544625030403c00d607102820701e80001404940c14002d101d009a00810080c40410845605203a1000c210b01c1a02e540340c0c6050800c90a5000300c2d80044a81d60750440001c045581140c003400000d2400c0d980c0c100819035600c0111000c03103082d6031410150042c01c006100c0d5032101152103500984038000c40349481300d2000421150381c01204c090b22165541c0c04820204840d03120030940000c1e010300031b40 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 346718983 1250 346717733 346717739
    0x2803080915092a0d08030a180b1b0a0c060506040615171305100c14040f0510050301061205090c0d1a090c1f030f0515100203040803072301061806050307 67
    0x24007070300c013503a030090240540440081c40f502c0c03940d0044030319401c40280e03030350201c1c0c9281740c0448004005d4074095044a90120b96604e06a14001994680c44190759284035140c1e107611508000c21016003000d8005c1c0e111080800e100b114440450110034466403868000ca0760480a083c000030013404030b03940d001902c1001c0c00400d00000d42400c85021107140081c20030450202601c1954042104100c40c290100d80020b2840036900d1840c11201d00341d495103a0b080007060700304d905200034007880d40402d0081d43c01104413105a07012030352001d441c0048828407260f8200141c901c001e5403104a5800b40020b9011100f0050680540d4000c60008001c0140441000020324156240045058007852070022005018429000825020043c40c03040020b801c0110b100c1c4070740001d1919041c0550310140ba0740104034800000c0b1011651140c0103103060400396a10410040b402c1006089610440000303140d039000e003807050303000520640c030640b85ca01204043d000309989031648400d02c65004820700b0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 346720233 1250 346718983 346718989
    0xa080a0203072a020a080a0c0819120e03120c19020102150a020f0301030b090d09030b06100309050d0504031a0c070204020306030a050a11032803080915092a 69
    0x512001c0b440b480400800303030301d242c0c84003640f403155001035030000846000085d028000b1407842d036003c2c01a60350030f06c4941c60744015640c2e2404403047d44000b2889094031804500300d1798000d480c010300d030301e40f0f000100381e000000382c40c1c0200c200398020004000240d24180c1a0104040b0038030213140307407900c01070511940000c0c0d150415284141480b800303040010791400c0b00f960466100010480b003645d103d50b1070382032102441008a605515502c14002c500e02154016100380c8110380c0d1183c246020b503601c1405020030300c10300159080905842d8884040094070030701168401250550302c07107448501d581441f03031102e001004580b50411042d03007800000d251010440d040e80d03070140c0340941e40c1e4a07047c000c68078141c608103010700180107003c84081040b9035020944500e100440880c2c08851555400d6071902e0302d040c1640e202651010302910000380601500e0342e1004664080e9541481110103444000d00200c4540700150407111075902e04111062586034480c5250030302412141c018804 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 346721483 1250 346720233 346720247
    0x210305060f030c240d06031220070512010e030c15060a0b090d08090409060b0109090b01051602010504031e0b1006020307030e0301020d1109030606010c0b0a0f09080f0a080a020307 79
    0x9a001c003480c0d10000201c05513994100c42944880c900c0030407038180e80f410031040141d490b03e00a0001641c0240030401c1000c04495a40c80f25104c0018182e00c1e80342c64108181c03000e4075084600380355211114400300d01400e0010785400c84460010340700001403940b40784003082c0e00030240e500c00d04c4011401c0c014081700d08203480440c0400c0c1c0350800d0031006400c0c091000c3c09414641030b48181030030604001c00c41117402501d145c02082c1c888131041500e590500c0e094034802007899002030001d07c49501101d29105640031050b0060400070b00d003a03200d8035a020020059010312880c10358001891017040086c550050380414040100c901c19410414025240d04c210f06015003046000e11049000e0340e001c0d411148051308600c0208000d9121100c0b9126a8200340550382c401c0c040c581c0060b51550082e1030780e106c915030190503031403903940e0581c2110003407025543d00c4084555030101c000001c0c2112005005106080000d6a119504900e00420304240245200111401401448411174225603 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 346722733 1250 346721483 346721509
    0x105130605060a030f060e010c051e160605040506042918100e071d070f1206081504060f06030308180f030a180b180607210305060f030c 60
    0x480070030640c554400107003103441c803a000541030041400c140400c0042687c06001d580491000034881d52001c01c02c2130f101c3c1d018920364071100c002c4221114521282e40c900400d203060002c0745ca11070035165501c5850490700125411207896012070184001d001c1b440403010440010700301207003000c214984c003004140744060720786032100d081c40c0080c1e100c0c28400e11078001c100d0720581d410410fa6002c241d82a0352001d076889100c030701c1c6a013000312070712074000c180e1010300c91030b41602d0326884400c83c0030302141c03040c0c07020501e0410507a80d240c021030141c80c10b00c034581c83c54940c180d00c3e01590401c0e08140003161040c107041c0701040c1c0742c000304000003034000303480300d902c2a642408460381d4080310700380f0340c2031401745401d8a0090000043e0706407110b4000e440e0020300c1c81c5075101c100c2c3c0c650f124545130249125099a402c0303070f1102c000c0710312510303e0120000c00302144074140c80d0441800f080403050103d03039501e00c004042601c0b4400c02155080014044090441c210001c25002c0e0151005c5111076a50310 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 346723983 1250 346722733 346722743
    0x30c090103090303020d0c02010b180108030315180403020109150905060613061a04030c060504060905040218030a06050105040506030a1518020a0e01140a15082a0714010513 76
    0x42c0d081024903000b40e058800380e1104c0c4600340488640310a009001f03040004c0f4080c499130070803d4035400b041104140703605803001d10004604d580c807500686068000303048145680071484544181e0101180b40e0390758003452290b000410b105505150404031070208250741c0f40740d10310f00106880801e6000500603080301003900e500060162030070546000c0c210a40020b03090a900746a40400720010100800480303001c0c881044107903071580e02c1111284a14455540010004007041c001880c040e030050a0b8401c10004460301e1103984004282885000c034400d0300c003165203400420050402e40599580a08121b01400d00c0e68003070790390301e00140c1007560010151030b40c076140304042180310f41c1074040540e0001c00c4151801d640780000748100b13000340120340d07414503008010b64141c20030701ea110050380c0301c3c950881100c210300d40085410000041219081d46080250400704010f0120511a95100352600b59a0341100c5c1c00c0128071f4090b0152280990b078034180c01c1006d40648400840043d0f9405 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 346725233 1250 346723983 346723991
    0x305010b0c2a041a0906031501150909050a050601090816060c0c0506070b100801090f0303090c0b190e0303031312020c03030a0c06051510030c02071802030108060c030c090103 77
    0x30010020008096800d42c1d0700249810b040240f4aa0001010b44003c0d100b21100049580c801c01410303154891402c41c81514034464006100d581100d072110100b4800b28a00745001c941e0b01e600d10026102e094540c00c007030b0341d9030f1024004c070303942e000c07a408014100c080024155408600c2c0c0071101d01000c0e10810301008071080350901001000a50040280b100510058a80225080424a1080507141603070b41180c0e50070001407403001800350301081c41e004546a01005c886450580140040900840d225403400c107010400300c03039510141180c90b0441d50000005031075110081d0034030700030500c0c4503c01e40c018810404803008000080100340e03440007980ca0968481a401ea1a003140d01003540c3e8103020208190103802e500410450700c1e1030140c4002d2040b5190440410000380070180645d800480c6415030034201d42c0a84c201e0802c00103a4070486800541e108100036151403400541c03000b198001004001d5044200143c5400c03110a03d099480c41c01c180300c80900d54454248501d06058a0f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 346726483 1250 346725233 346725283
    0x61d0102010617030307120e0712150e030405032a04021e0f0319180303020a110303040f05060105031b01030b210105010315020f0717040312030506010305010b0c 71
    0x20030b401100c01000c40054041d0103a0149803200e4683e0030442c2e148000800a182ea60308460460041c0d015a07050b0b40c001e02085414002484215100d2040c03d0758401c0342072007440c000c0c004901c141c06d02ca1141401441e21203040408260030807811241001e0fa80c090040e0341d00b003038105050701c00c540e52802c540043e0350b052b81d11148440581e018126006c0f984011540c0c0c1000f484100095208002045c00e0704404902d1174100130880f07140c00320074248104003090960009000e503004000d40c0b8140d0500d9403c0c2c5e0803020301c01c3d107983d004a4007110701302d00361481c038410440c1c02c00c20540585000c41c007401440c00c40040f032841090f00b00389010304058885034145195198200015600d445070250200d0180080302c01c1b50282c0310038841140d800e40d4000355210391203168801c1c0d8060190900d00b103441c01500c3d8039000c0d0164100c3c0840c80802c0d80800001000a00b400c034a101e61f034109440c04991881c00e5800901100c3e070507071105501090404c011070282c00e01084001100c0d41c00354260403c011 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 346727733 1250 346726483 346726487
    0xe0d0b0702281e0c031a010306150b070b0604060902180a091107080a0519030b090708070504091109030105070f11070f0e151201060f0b04120f141e0c0901061d01 71
    0x1203e0342c07001d401110059115030742c50788840b404c3d40c1032302e009104c103021b0014988480301c3c00071880c1c41500440c0c1c41c188556000a8200c1c4100c2d40c00000c0244003040103030b105d003640d40490784030020b10150030130450503801d0b243c14500c85980c000c0c440d40c0b00421101c514000003a20030b1050210003080e030540052024411800f078025a41c0848010304881d04910701d1007000350040c800d0045440c42148840009a5418852120107204507600d82e6490b040901e4203416001800300d83e0358440d070b414001d00405020740ca00340301d960301c42e41c010b699035099102110405070180e020345041c0006074020f68004e00800011840880444135a0915941150b9800d5030005180b407480354015030007115000b031740c640007034150040400d80d4001d1154803a40395a55502801501c10791054801a06140f0304400220300840242006107000d041441149201400058105501c2840e04602200300244404c0305017070401191100341c40944402d035181d41400009096040f02070031400621500a21401c1164 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 346728983 1250 346727733 346727753
    0xa0f1b0e0d0606030501110903010f0c0905011b05010929060303030402060904152309100909080d02040305060a050f040201020a2009010b090910030b04030e0d0b0702281e 75
    0x26400c100200b00007902c240c0c4480c00c6600c152126884ad40c00c1c40d07c0140c49440f00e00c14604034040f1030311038441e40307840d050054510481131204051104503e0743c0c0300300424400e004440220f84154205407031b992050100000c500b808400000002504004000c050384002040325085501114441d0302c500e4a0130014003c1c002e00d0320b00070a080c64140b00066541c481002e82071904030115814418a91130300300b070051030300e0105c800200051b5046010003418001c1d40c00171217100e0050401e90f14001081446406136400740d4000c0729150300c00c00800c240310841d4810745e5000030040703074480200e01305500002e5840303000c40400742191900704070602413140c2c081d5610020b0880030701492051360303440161203e031b50016660079019a150500140364600c50521035800c0d01c0e440400c40c0050346613600c0480b1140c1c04500102e81101c0c802880102044503800c41c0d900c10182540100100d1b25010b42c41d2000030a0504103001003610f400e05440085c415010300c555070024106240c3d200461401c2c05450b070 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 346730233 1250 346728983 346728989
    0x20a170c09190c02060613090308130311120c1504150c050c0d03020c0c1009180b0a03120e12030901050d02070b010305240c160201020c04050a0f1b0e0d0606 69
    0x10f8a083c40d42c03d5000e0f00031441c68401c080c111498494102c0070340b07116095642c034000040024a04200245049209070380710100c040c060710300118680c030b01c0d488003440d200c0c41003070240313038036001007840340120104104002d088002c503d4100780714142580c40040c00d400d00a1010b0a40740c4030709407030300d07a00d1288050340d0310010744804035500d45420880180096200b2521000607000f0714003041c0150400f218991080801580d88501844c0350106035480800b2260f02c0e4200759865102240c0c50381d80318000d00b005180544035200b003c920420000e00070301c2e10031b05294000c14065000d000e60102c0441a0b0b81212000e003406683e492598020038001d02c16010024070348503203400003000f40329001485a0a210600d01480164141510381890b20074048400c1d1132000e001304003a4404011036050207007020301c107004407906003142d01d0004003643c20448004052580d03c0c681c01280d0a4980201c2145060001d060501003072038000041c0300780080900e43c1d0103100400108810000150300050007 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 346731483 1250 346730233 346730281
    0xf07030c0203010f0f0e16050f36160e06090f030a0803040501020406200a0f140d0201150b120a02092202120c1306180b1204020a170c09 60
    0x480e051024011b000c1e141245040b40316602010411019140a6501340c0b00001c00c018090144007003040641822803001c03032500324161030320505000a4010740100714451541c219154544240c020740c1032523a41803041e04002100d410b503001c0341c80e604c045a03040d0000b541d240302c03400c5c4158040b908c0e01115407401010910008101710a120b0194094400e0301c8459460f100c11205160303414001e5004000d555405070891039035400000c0e1010300d085071652184401c3c03a420310206156034204144080f071100540d45803007800b0075440068400202030001c4e101d10908201c0b08031050b11400348020b0903c0c105903030026600300595120303484038208640395801c66503e41c0e400303070402d03000e9085422805081130311000440d4040800d40c080d078800c01d00985147c044949040d2049540c035601240ca403101113058440400e8041c40c0c40c0c0100705450303140d2100c400f5400d00d881403080c02f00b400c0e401402050800780c0c180c1c86040300484c804919080c110307011790030790b11011801e42501d00102038006d1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 346732733 1250 346731483 346731491
    0xb0303030a060e0c130509190906060801050702031303230a0f0201031508150703240807090504050312040303022503090f0630060803070b0a020f07030c0203010f 71
    0x1074a0304940e003040064810324900070242d034481c90b035043c8550180031205001c4075202c91040c0710904120b95084d03440141c805035070120f01c42002d02c442c00c035041e601c0207980c9141c643d0b5060152030024000d00da000002361004518019001e858500620b045005c01408210300c164041038180ca84020001e002005405940c0d00d00243d1808000c407100b8500124042810061242c44003144036079904c044901203006440d01d40e120311252408520020318440600da076400f100904d41c0c082c40c40c2140d007103410403c240354150419014a01e482e00d1030740800d903074a0501c0e0400000030004030a0b640aa844441603842a44070ba241c00d9010703002e024040c92001c5251700041e550f00c070070f1554000b4024001e0311901c1c03c81d91241c05003200e1020600407180401e01c0d00643c514420089107140c40c0036030b5080905250072200c91200300c10b030b68440d4041584e0b548081801818000094151030300302c15102ca0451803c1300401543c0d07424001d01d900034003807201c203410240940d1070a4100108000400304104 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 346733983 1250 346732733 346732741
    0xf12170702030c0c040e280b0601182d0b070302060609131b12030e010f020d08010614120f0108060903040303020a0f08120f0108070807050a0b03091e0102070b0a1a0909010b030303 79
    0x4404e0a001f00e0341130300c142c006079010845550180c1066804810f200c1101c1c092641000c54607080c0c04045045c04c2005020a03021108490300c076a4100041c248100304140c2d13490903800c00a14011000c0c01681c4103446031024000b04e5246011844003131a841911282002e10154861200c0001c503804903038207000400b034140806502091240d120202603e81c4118600c2da1101242d45051607010000407481d200d0062005900030441c08107460403440c0494038040564013000240c15007580d034685070440010042c000300d00c00340511644001003100444c206491918025036030f0865542c058203440d1811021014001d00c0c004444092411106018682c18054600c00d006c210900c0743c1401e0b405078030400705629030007182e40d1007201d500510071008036080c000c000541e0790000d0200300042c844c2a000c25400384500e100251103800c00c0d000162a2801c03400c240b1040c0034020100c10b03070186030403800d11403400c00968003180c4240690340d001c0aa43c0d416035003801030a0390074075542d040c80044104 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 346735233 1250 346733983 346734043
    0x30b0906010504050f0f071202040902120a0b060c0a06050c090306130c0501090b040b03060f0d050c090c0313030f030e0714031b09040f0f12170702030c0c040e 70
    0x901e04071401950100714030340d100403111542c510103503411010000441c01041400b0322513584861182c4142c00700518040d960107000c412030f0700803070f0414034860402c0208851100944114200154151030705407514402108403a01c42104400081c6144e9449007c41c02c0081c10000392460240e0160884d01c50f030030302d000d2040341d054a8400403560510b080300e020507154400d1011800700ca10380c65901d0b0030542410030f207081a8100078505034200401d00380da41c4050b91102503403c141c034007841c05400009003420500c65014001001c410b1148420070030300013003400340080b0490064141c5400c1c003281e518140d04501401c16450000200e1264030404680700e441a08003402660084007280c0d80444060245038003160880f0150382c0c8000403800040c0131400419904009a21489030810440d01ca0358a0240c0b00c43c40c070b44070704001508000f40c5010140d56001441e040403281c0011410441214800c0d0791303d10401c00070600840d1a12080044102c040104403025502000d1a500d0f42007140d40c2d03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 346736483 1250 346735233 346735243
    0x302060a300b0a05030d021902030c04060e0f0714030402060d0608060702010b090f0108300a1215080c151201171009030207051017010609091a060d0c09030b09 70
    0x400352040f0201040002c20345800215004452043d40282c07c200c0441ca00c00d50640c0d403c4c04050b60540501e5410620607621440781d440138044804a600060828448801a899005003840306101729050720800e10384401e8180c07035105904866480c3e0f15070503244858090305403540400d0a91051405003c0e0254041d0850030703521509540e0f0340d10545c0c0c0c42c2d624002c4000c2c00c3c483d14030a48c0203c00d120303002e6207481c100c40e01002c00d0f1207040b02264901c4000021582d100701c070b803c1c0018000018900b02c0c64164084c100700030443c0e0054060090404211a440b026804100c5e4415a1103190400d020700240081c0c5400300c4030548180d241e90303590300c50765018030901014000c10340101726021884000d10703c13031103640540540c001d00d101820241803007251030050b80c0400601602c4403801c03892503200000c0502801030b036a00c8400d0315141441120903a410480c1c5407651192039245107515480380001ea589802440c0c0c8081a0340071581d409981040850f0400303001c840e680f500f000070941000034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 346737733 1250 346736483 346736501
    0xf010f020a1209020f010309050f101b0c030e010e0d020619090e010f05010305040303180c0503070b0c0c3303040506100302010509040e161712040302060a30 69
    0x103a5080d003250001514044454041c002035005030b0039405c0f171085520035440501c080d8482e0086480703d10030100340c286010401400c1e00915900c400d60290000c01540c2001c1c0d4400503070034001113070316066602030071030b04401c20901d040095040c42c1070072640d95890405252a0040c0560350360340c3d0f040e00039160300a8401500d03c00318029600019181028a03201030480b88a5803040107010b041000460241030040c1083e010180c0b211100ca08410085050740c42080c45580c0c1c00829a00e0303c1c0502d030a001169100181c10b40c4280300e48180010040703104a0801c004650101219003000c040c0e120501c0f41c5070781b8540c0380030a511984100c0107440002c40c0901d0042c01224602e035245010301e00341018900000380012414880b54145040582007039218103402c0080c1c41d0000c1d12444480c0a0611583c00030014410100c100c3c09480300034040710301440150030311140b0f00303419600461818801c54040f0410805c2c11044509542680241c01d4400507000000614920f240144240507040d062 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 346738983 1250 346737733 346737737
    0x2060f06010905090406020d02041a090f030607020c060d201809060a03060b0301060b0a0c061503020f0d06060519230a170a0206030a0501060906020a02060301090e0f010f020a 77
    0x2000c50348941c0030301c0401d0225035005200201c00ea0343c1d951000c1c06900005485450b0607000c1c0804140c1a050100310303580c9100d48280582c988080b08204400c400028044d40d00070b41161090000b12503000c1070305011180141e80d1190303110810011940140a0044800b10500061024242c10903c10307004101003d0080f00b0205d40b0f0b4188400c120701410251207543c1c6c00038400201f00002440350b00310341000c8600500010302c1e19998505a2000d61107076103880000707238035400c480d01040075900c00d0701707a0481d040c1d0110880c0e900f540d003c101003030301000103688107200480c5200e04210b0550030403001741030302134000d28100c85900c00b0800c070341d80035004410000d94950081c6689000034000340c0e034160401071408001500d45410208040c0b080740c140c05241c0100c03011580543c0ba03d20081d80151822540041c3d81c0d0b00d0144000c08141d441e800080c115004402c41d040503030f4402c030a581c1510903a00c0001b904501d8130411514201030064443d016509080200a45a503558041c05040410f5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 346740233 1250 346738983 346739011
    0x8070b06121506010f031803090501090914040206070c091401032003060402060a0207030b0f090d080f070810150201050a0e0c1f030204030b04050a051c08060405070509100206 77
    0x602141a01c4005461804072240440030003d95150711580401c0010390030303402d00007890075001e4012402e2201803842a0045000c0200c10826564030240c0c06d0f00a1070005420010403c0303108601c0c0d40801c000d0000f031300c202004902074003030024140420b0000d20802108201c96030701c02071000040402480240c40e150303211440500c65880701d10080c403003010000c1c050205a80c0d00c0c1c0c20400c4a400590140c0d045204124011001802c0901000e001d2503c411090307a442c5481004186070142c1c031240d02d01040507440c240a40c0b40f03004d21026802000d00e003844080b655905442e840d0300020350b80000364103850a02c06807a59078043d4400e178020b40d1480300c03e1000c0c65103008503030f69600205449941294500c2240e80d181c0d0041a0004805941890701514240d0340340c98012400e0026101a00c6c2c54000c0c83c40303141004002c120400d8000da200b03900b86680040080050305041c03000f05910f00450701c40780001e13251440f401c11a07411203402000c0c030b910003000c514001e40d900811038214a4401d20 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 346741483 1250 346740233 346740259
    0x405060a050a0e1f0f02120a1104030203030a1103091804110f0f060d0e010e150108010504020904020d0201091701020a080c030f07050c03070f03030c08060d0c050f060708070b06 78
    0x9500942d4214003019004022204c2d006005640c2540322010341d10b002659440d0714403168030b1a00080a1090140b5030340e28240c201140782c00115603104504d00d503140000c02080005840200c241e80340c5000d00c1c142004502400f6100500b1423186051182d4840c00307500600f01c40c118001c41690245004045846951091034140f0626411040940e540511030310a40704107460000000d00b4900c00c803403000315400c2c207010082c0b829076403d060a10b0a9400c00711007060740c3d142c0c1940c502c3c01441814000d002508141c0c01140410602404c0613025419907880402564010304245c002081c1d6680380c1080950b039416214001e4105d192101d00180c0f4400100e4510030b0010103a0b4002c203002101064591182e8505071155885000c0201e041c0c00284440c40210720480038007458203000e9200460740c0f00c0d41540040c4580d20050503148650020480d02000c20104102001030ba5029114200c60b42914000141030b4051204020709603c1d002920311304201d9040b0f50300e8004c4805913a00600c00391 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 346742733 1250 346741483 346741501
    0x60801060e0907050d2307080403080f062101092f0102010207080937090b030f0d0305070e0402211e0f1015180503030a09090906060e0405060a05 64
    0x400703642c6a40000c100348280301c0654150ba110015200e030032030f001c6ca4030004903021840280802c88400000c601400c08220074903401410640d40b015070001d54140c245032500008261401a90220440c00042d4400e100c03960425031055000d0358006000c120500b11141132500101d01a200c500c800786842001800c695005009440c0801e134000c101c1d50825200c0418007040400f0031020145d01b20540c80c0a440240074480301c1c4880c10300c03400c5203404060602c1e4548043c0c510204245002e640540503030328204101003005201c1e04002d1038045455140d0030400c8500b80d904180040d84a80f0000d02e001948054800040309010150450389056565540c0b6142e0960f0700544929400c00f9000001c008009451900b82e00040f2050210010742d200ca59108400c50045680b80100790510110506003030003c0d00a002807a00310003c5180501301c46004007202440d03c12007500c10b440c4c404000400c00150444005458034400341c0925161074100185c1e280c0d416100c074103100e0b03d01004550008 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 346743983 1250 346742733 346742749
    0x30b0a09050d0318020f0a05130e0c01140304060c050f040902090f090403050714010f0f02130b030105010c060b12010921030501050d0305090312160311160506030c090a060801060e 79
    0x161038800045000f44c0540a20082064208071540e2200d50100c010034a0740d109060310f03180f05001100041c5004045000171301d40300b905846541801128440c01810181c40000c90f98000e03403145d00450001200a801d44503401086c004d0b040715038020601150303880307a42d0701414201310211500d139114800f03d0184800d00760140e0300a40041c20070800f001c003003a18000800c0100710b00e84000105c00c0442d104420840c4c2c0007035030703c4805a4000070360a041503072040c180f00142010f91002451941b4010000c2c004000c085401401e03661075504200306c0b540c0d0000d02c100701d14036400003800401c8461400051036429454038011110383d4840e00c2040911902c038103811303550080d101010f0491503403402c0c0e4940d0403040c00e45a040c401e1084802103025440c4c090f0507401010000c2004a00701413802070060381c1e619201401c543e1046021244581d5400020702c102da4040d00d100303650352a201c00c1d1030020300c20002c080c0e80006811000082c4944e110040c039040f170f151613607007039585082101040711340 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 346745233 1250 346743983 346744001
    0x110c0105010e090a030f180320010327020d051c091a0901031e1a030f0316060902060c0304030503090a080c0d030f18030c03110a06140a0504030b0a09050d03 69
    0x142d002c005000c000034002c90f51101b0b60940d03410700420002681020241c10030040d041155041d00380c182ca45080078411035001c410b240c1c00d00b0140044902410629880c03900c0030003164030722800031340c49802d64590240401d045134105e000e0340c0303004011540d01d8517109060351080d00080c043c003a0000e2211901d1000200750758000d0344007031524481400440c082e040c0f0100e030300f0f0340c6845c400040d0300784802d91140740040f2071403203140024504020109800c2164005d8840c40540082104000948000686107400ea52144000507021902d001085a0740513542c3c114141d07100c0020302200384000000a0100c0c2d0000310745140c02903490340403140c0c0b100f65101c58a034100c60490700d80c1001a000384008008c0d903280c4d01d080040203d00249a03001c0a240c1d5000369000c05543d0000d00c01d014059003000101442a80c103000094a0082c0061201111205440d400312000c1102c26156110707078215002150018500c0c500760809200030001020440c0c81183c5500c189079521034094024082e403111 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 346746483 1250 346745233 346745251
    0x302070302060304031713061b080f07200c03120702031e030c070906030204150b0706090f0605070f020f01060f060311040812030f060d02060406120f110c0105010e 72
    0x10316607400c0c880240c201038022400c0c050781d106280d400250340071010f842440883c003011107000050600700101c90850110725003400100007452803e6800140c01904100c0940c0b01207420f40d14180b048800002075403c60240c8143c040c90281012070028a0440c80c030703c12000d03510460007140b0b05030700c14880c61030025016088000000341090021400135aa856070b901500c0c41d00281d000942d091140b03542000340001d660312401e0042d401d0501c2029510000d0b2400f401d002c0341440305201040c050520300030900c40c0c0360304144003003198060703900c4540b0384e200703200b8012420441405009603514100f40e100500c02c8d0384220361680c4050040c2021509810460070300d250610314210003904843c01c40d1200503c040000241700c14040280810f0302c016060000e89030306050100740300016000c0d10142c0303e400400076400140c1d44450480d0101d07040f034180503c10f85050301e020000341c0b1020b01c800a5143c90080800000107100c0010581d03d031105c8000c004681e2140c1000c00c104000340c442c401 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 346747733 1250 346746483 346746493
    0x1d060d1208071709010f1103011d0c04030204020f121f090b0a0815011e0305030313020117090f0d080f011502030417030405040e011b05180301020c03090f0d0302 71
    0x10680703001d4140d00381c00c030440749040103550b401011480034152060b14070120301e0f0342d54100020ba00e1100e21855428094400f10603107113500d800413241800601500c441d0003490745002059540b844001194001d550103003055459824034140c0c0c0c9110340000b0070303000c540113240000440d038000b2180c034040d101250b1188068140c0c1043d041c0c100404118000d90b40019440c000410405000c0110701034400c103a40e503201180d814002c10701ea40000d188840740d03e2404109041c00010800301c00c0d00c1d4000100d03c90309a8031840b44c00100c86698020420280c80d049241c1071001200021a84840ca0303c882c0d41190b001483c0b5503001c032100c2504036034007007125420a005014000c004100c424450440e072040780d0820303846440701030000781003011a021aa0000400300060b0915004140b41e0171b08090081004002c1d40c141100c24040c0c007150a403c110300040d20345103102c0303500c00420325840043c000b10b44951489800c0f6503254460304050303200b410708202c140d0280c07510f9009400d8850345507001e03003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 346748983 1250 346747733 346747763
    0x150d0e03180d1718030109050109120906050d0f180302070f270908090a090b0307060c030e04050613020a051201050603070c061a0d030c0323090d0212071d060d 70
    0xc2844d4226058000000940c2400044141c0e0240208180c03175004130000074503043d00d0318194403e00310302000340b4180214441c1c2041660b4000081d078002e009c3d201e8001c102400c02800307080080c24039005d44d01904800071031a80034590f00107516000d8a008448000400341c4990200d40c0ca11440c4408060200b601c40600400001d80c2d003001074501c1c881d101c3c1600700505800000c408a209403c48140155a032980d0103907071504102002c024201d40c00e08500c1c407405520004c22030609154120f0083d030b102c0e8003180c1d058480e8110a10b08042100c41117407120104000107100d64041011502428184800800c40d8500801160b0040b0720541310120070400039596030026140c2500b03240340003403525074410990740742d4940380d64205100307584950304000075103005823918034081c0c140d0070525140c41e89007118294040441c0d080b01e80031602101566458070025440c0c1c6100800c403881e50280c1040060000c1101d41c43c0b84101c0e20f140030440701c1e66204014040714a1480030040c0c840310000c0d85203 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 346750233 1250 346748983 346749023
    0x60e0106020d0503061801150216121410021908010504021315090e010603060f050a0806071d03071814010e060111010609021219050f0109230f100e040803010302150d0e03180d 77
    0x1a0007003070b6241d000d840c98dc0901c04103260881c2c10040e4554015109607080328081980442c0c481d001d0842204c04508203081002400c032081260300680f03025003888414030680700e009880b40c81c014000002800c01d550f850b50b0001b00174001a00c52844a19900a000b00e914900320b543e82e01510350201c018071072565110b401702e413071522054107002d05c07030400019075070b040e1030600100000d01402d038141041c61101e0b03990300d021501141c02c1c803100400201c005020f4001ca241903036400400c2481c00000900c40c400542e1300400403940b00110700c51001810440c80860300b04100d104041103034007881c0354408030701050f0a0300c204641c1080703544007010041c0300c08540d0785e20007801d050b01407070f070b41409000c0c8008004080e00d080c0d5407440b001c0100d000b0003150003805512003000d4029000b0300480d50800f559608081d01040c0002032050840c1102c495551000c00c050314600801d06034240894500d440100b41c0b2540000b0782030544e0340b00440d040c0d030141482c0d8117212126034804640342d0564214010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 346751483 1250 346750233 346750253
    0x14010320060c0a1a0601230f1b060618010303050d0f0207080a03060911040614030c070c15090e09030306101101020f0d060e0106020d050306180115021612 68
    0x40703a01c0401440020704081d000c109242c0345a1180703420420046012250188a5030300921440c104050800c010701c1c403d04407603092a101180c020b070356032241c1118200d05258001d03014100d40c01454440250030300180010f41500a02e015130304242c00264a009041c2601024003001d00454010410440440c2103981f0441c54181c2c0803d0040c1002100d5a0744880c550203800050002178580741c0501c91181c0c1e40c800c083c4400c0e041c65403949000d05d0000c014211480707015144035806004400650300d02d00c0b13001211416980115203646150311a02030020406010b01450001a1001b00100d070491201c0c20050240c150780004508580c0e414017081740c0030702402c0820301002051107054120307404c240040c0051401d515480b0f5216a80d050a10044482d80d034000e4100f8000791004014841c1c0208840c85e40e00341502d0103e90300d03a90301d0041500011000410900045003100004100040d44104102c004150b401d4401c66084c01404100c412480c2c01841c1c002010131080c60001906558 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 346752733 1250 346751483 346751543
    0x100e15180d0f0b070912050309010806221119170705040e0f07110d120e030f1b0f0601170c010c1e0309080102030106180e13080306040f050a060801140103 68
    0x50700301131090725040318540302c171b20407807084440d54004113204c0081c1d0b81040b41503a00860a891001c8070790b160000da0801715000c0b0b80e40555040d6179102c411126505c03402203403036103801c10104a16182031040b000301418a084510b40c00707420250003040d9824480d1085404507281c003918001a03444002c40750402c01c03001340c4841c00313024210401c0e01e8008000d0002003540b10040e25042120100310203428240c0e40316840860307458000300040b081c54003844042e1600460f08803060703550480e4840003030346000d0100c00e41e1080c500c1000000100034014500d501d1038000310360140c0c3d42c4109882e0065444000052004122910046003031404c0c02644110703560f66802072070100070b981d80c0c40312242d0881e842070300030340c0c0040d03ca00d5000c0009201001580028104299104150310340008004242521041d006001480000c045545a5210b81007200c60600f42041008603040039890040181170074030590541d5406c084881c0402ca803032503103030742c1226002250045002000010340c1c4031004540 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 346753983 1250 346752733 346752737
    0x106050d0b030a1b1a0f0a170c18030d0207090b0f12060603010606020d02060601050a090504021b0f010e0a1e1506060306050d11100e15180d0f0b07 65
    0x1d8a0400150303410069504228044c44036038003490200500720001c594a504001c04020405044034040d080510481d10b86441c0d4410054440141c4001215044a29451124545040703000e02129000100040441000c204ca110f000962604241522040c4915064000d070b000110104840e81e160f400103018100010302d08036031008007000107000e440c030850001d58680e003c58108285401d0900c02c1c02e016000c2e03030004106550504000070740c1c238107008040904015000c18003e441c103007e14444006800010001d544400c0d076144a0211031002c5540c900d001e220f5100c000d0b99015040c458200841e43c10409007500301a65284e030524140c0d1300c4040301e001150b2407101340120704401c4010041c1003221002081e40d600e40203008050b148940c2105104c0e0311040c210f8800039008200d4080524802d850264a420200909039203442004543d113030003070390151741c3c030089400d0000100061014410a8030300c000b11101030003940711003010000d101c05400000345003c2121710202d50303131006044c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 346755233 1250 346753983 346753991
    0x10e060c0f010b090a0b09160915030c0306050a080307110a0807030b1e0c160c0e09070e1303090515070602161110050d0b01030906020403080c190203060106050d 71
    0x8916a1480c0c00001c004885190b5500c003c01c003c3d510b07100000380d4008400803000d0103901c4950780065111071026005030001503442510703040d0140190580b500406000c142588511048107025014106c500e402e1400a403421ba408140d500d4078442e038100355036810000b5400d0001e29501e0306450300c0c0e003a011541c80101904005241e0030b0800481d03001d1803145843c00b0076804c001c0410080d021006420101501c2403908024000780c40905413089589081c08203805039645081c148092151900403454031890401080980d8000080c4002118825104c030000c3d941e4242500742610800d000050019680d440100710b140b85c48486400000d400141c1140f43c09200e40d52042241e004840b21101c0c1d40760400d2040070700c2040010740800d41c4042e00e50b1340c1d0203003011400030241d102c2c9a502000d030581c0c0c0c5250703140070707442a480242070aa0140c400c40d602ca85a0070800181e41140107048014481d54016100d41d6001002c000c84107907000d001802585d091000585854111035409824036940d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 346756483 1250 346755233 346755247
    0x6010902070807060203011d010b0f09011209050a03050307273309030b1510031505031501170a15090f0f140d0c0c050f010512090106081b030c010e06 66
    0xd05d100035030003884864503c9007216002a900807000714164051907400c001440f400340c400c05030f1b40c04c41c2c1c0724040c07d29048c21000c00900b181c170700505003400058060f20036225275004160f04030008500a201a4641c04c200103503448016845144000f021028100300d0711007081490120411590340d03844e403e000380501c0110b180ca0b03030801806000c0704000140b005404009003c1c1711130b1244d411507080351802c001e20070088049100441c022071520101541c488a00c18800900d081c1d09010b0700d0000e081d01e20300680f0003803a150303801702070103044451003c54020701c14100e00000c010a69a030f1012203409407404021074200204007400003034a400c100624010000b6000d0309860245511501c9049440031260442c1458451810064810f102c4200c0d800800300e40591102811240b0864115a504254400482d06070042a03e0004100180c9081c40742021041d0092801e446030309084444030380d0700f42c2c0c1030840c2045010904d60035401c44021101d155226030810640c042000d0841864591 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 346757733 1250 346756483 346756493
    0x7050307030f080c0f06060f04023903120901180b1f0509090307031d010e1324031205040506030c0d06030c06020c031011032d040605010e1806010902070807 69
    0x244c06049245c490700310508000d41480e14800344e104044051704d0450515060100d0118828410001c0c0c90030b45100c0780d800f40b1000902440030310142c0904040d00c2d242d41c90001000300e0650241d034000055401d1002d00342c004e80b11030f00c403511407a412280110717180c0c898000901c8541640103400384140c520240124403625408034042c001c1060030000c560703403840f606005003070042d140104422580100c0c02c042c8a80e0b4010a501d103001811201064039040401528000340b16001840b8100d00903250301d07140e10301c3d00c099030341c0459004008140c9084030901040b90329100f00e0180726804101807010620b00400b1901074115010745841c009100b0344c5030385031400482107641c01180140d10802c08070015050a0000494070441d400c030a014204400581080358000207010010100c41141d01004000d060360412418665145800415080509142d0080e00090080702084400d080201d80c58041b1800380c1a40040b0a40180c040c50b402d06002d100a540034810170386020505103d1880420 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 346758983 1250 346757733 346757743
    0xe011b0c0501180b07031a03071502010b04060f030c0e1e04050c031e0d110d050f041a12090f1b060d0f05060f010207060903080307171302090907050307030f080c 71
    0x2d025130341620b081d1505100007020303203180d500c2ca141070302d40c0c0d8810f4075086d0b140016031400392800071003d001c2d00d074001a8120b004281048003907a1050a143e80040c5140c6000390020660340102c1441d0400d030307101d800d0003603407030429100a40655509001d56440e105602d00307064009100303500740c46c2d04000d800f00007490401c00202120090244402d1042c032210200040b040014403400d10010300b81c51100c529454541041c000342c103014000440700015452202101c010381950780c104085e11481130242c81207500450301e1800c05d03041347c1e40030919000c2c001500c408040310002c01030039084250711020300e00108680800390007500038400300122040c5409044402c0c020048001072628060041081840d520240707681075400010043c0061680001c07440140d0f82c001e0405540d0352201001140c01104100281075480554414802e444100460700055603000710f504051301c0e1208a031980e15501c1511410350305a01c594420800204690201c044450148140c2800c0c0344600356298140 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 346760233 1250 346758983 346759031
    0xb030406271101030506010311040302040207240618050f04020d021f08060f0d02030a060507120207061509050907030314091206010f08010219180305070609090e011b0c0501 76
    0x1124000b07454404550f4503104d141d9111100b440d040c4130a0980250707208030341c401c901020780100e800092403400d00024045124299040d840d410110008600202e0000c04281c0104a08061401c036918010100ba000b0386001f10262009208142c4940e42004166900e82600f242c2101480105004045003000717105801c010a480d0284036140c40000c01645841d0b007500c55120b990b03d0002c00c00035031000039102c44a158040800505a181d00d0400c3d00c682002c0c4244135a440e000051300001c0010703d400c25100350308290030b40175015880d00c9600d8141c4000302c07102c0d09154844902080803a1155441e031a48489101d001c0340b40202c88001304041c0c5805142600860b40b081380100a075442400c01480148904c000841c1800302c034041c102d9094440360201c804000b10071011401c41034a02034101c00031a889022912420359500c1d0103880380043d0f02c00c6185c014a44055060b1001c418050000b20304c03072051008040703196040040c0c401e8892a2001e44096581e48600d003084125240d8036155 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 346761483 1250 346760233 346760243
    0xb0a02070f0f05030f0d080705130b0a050706050a0504020102100f0f090c0515093001050403020c0307050105160f031103030901061401020d082706010f03050d0203040b03040627 78
    0x10350b0401c2c080c14034080c10600f00c01740c07650054080068080d8000c04c0207030011003500d0715035503941034240484401089500460040d00c00060044269500b000003400243c1c402c8a082c03081f5500c092210003110006c840190140e001078180ca41205801e510134405801d100100040e1792600400c104200e035030031803040b0344031444800c0a11840c90400b00d0718840c42d85c1007841c203141c00c0920000c00c1643c45020b040800441c01a0319032401e149080c5000340d4400f942d40c0082000b07107024180255035160783e809e114000c8c001d502010800794498003c40784124048200580303262003a50f40d807003400703841480503004c0040403002c1c024000400d0000f940546030000000c130700d032810100d101c01c050030487c44260555025004031404150081240c640c0107204040441c440c00030200151100c015912681d020b5004103030000c124410700c0c8400074146c0c2c0c05002100c0301c0c800d010740113030b940303206070700561031480814000070b80000d0b416006050281c1d42e400e0341824146039a000500002c00e4120201c80d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 346762589 1106 346761483 346761509
    0x161e05030102160605060604050a0b090303210a050c040e041403090402040915151b0804050a121506050d0308091c0c14160b0a02070f 59
    0x10040201a009541c3c40002800207034084024940c1200e8a42c60840031503201c1c14000b043e2416928082c0401c09444d00b09205c1e40e00542042d92406ea040c44108030949050f045004d2020748440c41020101c10303401e0003c800c1090381c01c0142034001e2800140010040c41c00b101c000d1940103170704411211500c2128951380e030f046104541c2159086400000c0000304a416540020034803500745601c0c8070340e15159092aa00f00300c64100c60400294005819a41c4e22402802c200134540720b20001032500d40d4800220f00d6680701d03903105040b00000d04400c01c0c20f02034102e84541c0d0b800c0c1000d03010024242054001030b80d2815601c0c000c0d040008a20004103e11010001705142c542e40d02008907424860307400003040784d00d040008030b0b46d20f410480070b000d00e03000005e5080c1000300101d03042c0d14154100401c1030221340140f51181c085121b40b210006544a021f05500301510b041900c0320 = true := by decide +kernel

theorem cover : BRFrame.Cov 346582733 346762589 := by
  have h0 := BRFrame.cov_init 346582733
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346582733 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 346582733 ≤ n) (h2 : n < 346762589) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
