-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1086
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:10:55.278404+00:00
-- url     : https://prove2.me/submissions/73a7e8fb-4e84-4950-b58d-9b5d8290ce99

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 195143884 ≤ n < 195323741 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 195145134 1250 195143884 195143909
    0x30a0f0201090f2105090109061d220c05040506040303120b040c02030406020f030307080103020909011e02040303110601140d05120406020a0209161707020309030f0c13020f0301 78
    0x180018400d5002001c55600044058420312403424a00e007214910f1000281c0701420b03914101120b4060b20032200414410ba444c0070315286044821107004581088214161045140c84d000543e2a000300704449102000040301d0b40e0b2900c05103408545801820340c05000040c0410041035540405490031a6058280420748440b00301d00c07900186098000b81e40e11a141010300c82411f540000500300b503600d16002c0711008a120121642e80e40811101d03680024083e82c018001404c1c00319100303400519050001c908400c019151480d00c8440c000540c3d4065404a020420301d58404075041d9005a0700c400740445506065807d42403641d440201402840492880740c1046010001d041c1c40c20300806507180ca803500da0300000e468100b801c800b81c1c80b808014000c43c13080a181084030070b01e401c139901d0b000c0e035070307940400d6121200754014415015800244801c0400f40c81c2444403141d10f50002029000001c03c0504010f004100e6181744c0e10501c1c41400a02d803030300154005c90381510404003080 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 195146384 1250 195145134 195145157
    0x160e0105090c0a180608010503010c0e031e0a0f050c0112021c020f0c070b030103030314010609140f090708091e1f02040515040504140c0306040903091e0906080d02030a 74
    0x2901c2078084c504407400e4000b8841c2c80024113a50140d2140d050b0b0320110b00a10100d1a0705104035000c19038420381503413541100501550b020200c6601503404048a41070314408442e60711220a2121981c0b002d844a80144407002d0066910001c0c907034407541c240c07a0450910010f254045116148000e5000110760b00140c070106000c0d90030203450042902c481154010303a1524a1030324150428802200803908026106c0080b035410840709040c0c030681da541d0480c0c145072195000e0341d400d05050700703130b00404030b04400d1400d5250506441d11894403a20358480300d0604c0c0c000680352a00700d5011240800c0e612150300188000858602c904492091400c16600d44451006009206507030002d50300c01c1d4601d010744a00b88614020f081107500886e0108000310880c50b00b2503c002c411111344202d80e81c100002000c51419602000300b96009180c481d5015880307460840e21185134800c03c0c113031300050b80c80400459846010700e4001e8440c1c00082c2c0704070440c0100181d80ca00a400500081c0110316001c0f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 195147634 1250 195146384 195146387
    0x9060b0a15020d08070e0108040305040f030c1401050f030f060612071d06040f1703040b040e070e031204090e01060504020301120b01050a0f1a1303060b1206060105270301020a02160e0105090c0a 85
    0x44c1c0380076040400307c121010b134ed02d140801018040b807040aa00c10009544588158012800d9a0b603d1150300c6816185030781d00042d210b4802c800900c010f0f4007550910810810b42c40d010040f80c41101147c0790002031000c0310040808100c802100b641c4200400c00090240e4407091415000b110600842c050514290b0f4400c142140130b00e401c01c0300c400c4400300d03002507400da03c192168081e1202d07460308004a000c00045c903071a40c003c0028061f81c02c100300f10070820008e03503900c8504003907404000041d0903a00c400010b01aa402a401030f0303038290340030070a042440801c444160050000710341b031440349031500204d04030140881c0b02d200321310340200b40da803043c81c0010421a45034035404980240b03002c0d22841c2000050040607000c80c0580111502e41c3c0c21a0030009090b801080141c41d02400d064007107001800070842d5003555640d00c0c0300607401d10426142400a000d4850a5402420b81c1a00301c0381045075200b140e50007103002184a900401086e00c9500003a42c0002038009000d5403070030010f90 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 195148884 1250 195147634 195147637
    0xe19050c0f03030d24090606140a0c0b0115140702030601030803040203190c0e0c090d02120f01140a050f01030b04080315030a15060801090c0909060b0a15020d08070e0108040305 78
    0x4111804d03820602c0451000f00500390003018600c44c0ca0780d481c20280ca0b201c1c0c1004483c02401030002090f03411503440000d105284c060a0040d415192a10900c1d110381d17921450781d403080c1d0010490b007200000101282ea006807459510b190406415410941c0640000350388400610010b000002c0c00400710341952000c1c404640521910088440f070f1602a25000903254a54440d82a0103900b500100d10000d141c00708480410304002e1517080e80030f0242c2c00700012603924a859483c684220103400d0f0040134203004d25426103c403c2c2d400032903440c00e1101f41054841c01032448a060202c40300600000300c0003400181c0040c4c0000a05440c1d66404c03001d800540c1000359280da140c4101065601089041850141c11160545040c00710580e80c0c0442403e80f01504c00003090300311000828085071243d07074410300c1558014000407500580580c0858500030f500e401440310b00e41b07400c200e145400d4041040000c82801807906442d0340c039195600401501c904881d113810400303c034001c203013890300c02c60 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 195150134 1250 195148884 195148897
    0xc0f11010e030307150c080717060a080129040b24090a12060b09061c0503040e04210e0a0b07021206070c1a0403020d0f0201020408010f0e19050c0f0303 67
    0x40c100e944d58401824144a0080407050704801d103410912144109071003080740324000c01045d1908807070020010850200040002d0a19420545501000604242c24045c0200c2a4400044103800740d00305501c0c001d001410030343c1c05001d0750401c0a601415121400c2a503002011005000344403043c00c440804a0b03c14020103690068465101103001e580c100600c0c02070358072400c403c1100d440c1c901c0911040880440e9210341c819407a00c510490030802d00312441c40980b154081d030b440c058031105c0c24015a182031301c082d240c0031004d1f8104003403818040000c0c4410041414002d43ca07a0416001900100c1c607409400021b80c408100e19007103481d0301301c1080416a94178180d456601c1c10020081c60190307031500035941e41d0b050142d55403140900717009041c003440d0591702810000340b441c1c0081d9a00c051140407442159401c010000e402d81c8288103054a030101c130a408510240d008030510726150500c2104005101c1c0440c20a00081c40040d1903d412501911041d000044d1728000034250300411 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 195151384 1250 195150134 195150139
    0xb0901061d0a0b1911010915050907061e09050405090c1509060403020409110904060f230604050603070b04060c12110727020c010905070605030906060f0d050d090e01060c0f11010e 79
    0x140043c1c2080400a008c00642c10202070802581c1d071049480384d42d43d49a8131800c404542e2102a41404000444411160b80d0781380c186105501d170380c0c4000c6801c441c402c842e40c0030160030150004440d49031030403480c081c01c2030b407015040c140003070742c0002030042c4902d01c0001e00c16a070750668842080809881940c0010f0010300c81c400a290a050000280006050a00700145012480c161080701151140c1403481801c4201886554060a020040c41301602c040e9141c45408030008140640200410141c01039996250f40c001051400e9111288414800000c5c0618070141e0100300200181a808484081c40841c0c3c1c8815240082c0044003ca0324091480e140001804d000029054100984003440741c82100c0c40d003540d612040359940002da51100315900b12002150280c0b0780102c041e090100300411525081030a0781d5668501501000c03000041050b01300c2c100b040450500c8200c2c014036013405d052040d8242960380040e03075044000001c1440010003074100c0c0d40d0340718030604441203002 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 195152634 1250 195151384 195151391
    0xa29070c061b0812010501020c041e09020a081b01030f0c0206070c1b03030216060e0d060203040515040b0702010506091006080c0d060609090b0a14010809010b0901061d0a0b191101 79
    0x419044444e1100074080e480c058400d00c868240103050502c115942c0114030100c1e00c40d00f44590341200043e000c1180283c0c0c2c0030307982c800085101a02486403412408041040b4850614082e001409494912400d61001840c02080403c50794001c5034503036200440b481c0c030414058a91a01510361346218090031403d60f01a503001c010140c0010360b10003070310b000540c03001030181c0e40c04007191242c09005035160000700e0b2180010014895070040c58006200d0001e4480c40114607820689a80044405480c3d4215410602840540a1003055000350003501d92407003901d8684040692074181e441041d041000e284005110b0910701026904240d00c80e01c01402400c2d500c0c100208080d07038074041c2d403000d40d203001e8880d030045c581184614102e810812905000c1c0c4144001520b82840c000e00b509102d54852187c5121591000021b502078501500d84851040003a0409040640805040d901410cd401c0c4c0c1440f080f500001560802e0344061481e4007100322008045548130483c00d85500690708 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 195153884 1250 195152634 195152647
    0x5040c0306110a09090c20070803030a0f0b030c030c060a03111614030a14070f02090408030117061312020307050307080306040507020d0801051009050a29070c061b08 73
    0x40c100c0100329011096844d0a2256110218030342101d01c0e81960502140c07400340180306003043c600380354650b40809426118030550751910300741580e00880740d0b0510942c2d0b8580c00000051503200d94a10000290010f000381c080c0380c03000c603030f4590900019074418400400c880c103800740303e81c1003040e8001426488649408101580b20620080440c0c11101c100c1c000c424850082000001d841800e43c2a6864403045a010040300d4080d5003303040c2a9800070400d421040541c48504001c4c0c055440340503195500d6241c002030801c1c1024801e000c02d42a0004d406000000400c0303098000c43d150407050342101d13010144400d900e035101c6c003a4004c20780e010104994041c88003100140d03100b148182d405100c1035a44690032600c0c1c04441003100301140340c1c0c3c4014009410580c00c841071404060a2008160380c4500000d10100007660056509900540e903d0100e0710003051016824220074883c641060300a96500c1038000302800354004100075908407103040c039001141c62071016003000456030b0728030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 195155134 1250 195153884 195153911
    0x60609060c010b01030506031203040209041e12030b0102070b1207050c060a0608011407051b0c151909050d120302070804081b010819020f0706020a05250b070305040c0306 75
    0x3e000c02070201c0d203070000284840c1030200b030418110307800c0b0001916540e1561700b0407040301e84c098000d0303401c07200301c10740340c03000d8011800d091088900814407050f042c5600d400090568007030041071411500484000c02c1481b40072000d81d50702c0c803015070243c1c1b02940d650790101c41601411200c04044c0c4584000d00c401044103901200c1510f03882402400265002610301000f01c40a0f034200c0300042c0b041005000e001c1c41d081d82140080c120380240d0b00006646000100b003156008454031b0628000a4405078643c1c901090747c0c480401d03414842007251410b00003407440703400010040e096503c481c54000441388258121140e2507400701e5019111a00d4142e002d036503140c000003000207800342941d40d41c115800b548901d4400d200b0030540c08003105100f84068069000308003515000c041c2401108002640d07400600002c181079a280d50f00c4882101402e81442058500034600601180710300e400300e12000d04c80355000c02d03d810085441c1d192403a0124401d025540042c08152901e4840350258 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 195156384 1250 195155134 195155141
    0x715020319060617060f12031c140405150403050f0301090c020c012c060c1b0310110f180a03080a14030907120212150604060e040f030503060609060c01 67
    0x2841c20344041124545842040d503030300ca00b01d52108041c149920001d051490002020b00c0303011409402c800c001003100300341c2c5240d904001c001281110200520851100352440b8848017845605074061050600340c44450310380d46c6890001e5241005040098141402801215031a00015201a64a40c0d50368902d0000b0030106400d100103000c1d08141d90000d61250a00342e10402b5031a00410a005000c034981c1510300204485c29040541400710403080e40040c0850450485440b101d80d021410460415040590807445660700c580360415060907084110281d0b034442094421055840302d42100700d841d0002c07000c515a40c000c1d4001c1012013002703864006040b007544140c803068881c844450540c1c9150004654507081d980c84000c082103031420083c818070320980046c00300d10340b01425001142c2000d41480340c8a4150101070705000041c00d00c0c3c13190304028140c81241001504140e955400b1055038550080e0401001101240321590f4540440b00486c800410341540d80d044c400c26180603 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 195157634 1250 195156384 195156421
    0xc0a03080c152a09010e0609010201180507050a0b0a0228060c03090b070309020904230604051c0c051c02030405041e0b0d0b130302100e0c0a060e0f0607150203 70
    0x200303008018191000043c4200b40d86070720300c0c142c4841100c1c1d522042440300982101201c01e0441d904c076500950750149450010300c203180940c000d0603006060809105142c45154008030101030100008210254046030910300c001000250540001c002070703800340a1044000080c00c80d07440d0225010030113400d50700000c040e600c038200070142a614548103604403540301d5800794006212000050009101e10b42003096954020200019460213904480c5401301c210380480d0b5680c8001003101300091522440b103118801e0f40307062016801180c2c0e415460300c1d030140303118807c00704d101c01c0d503a01140248142c6025100140c000c01c581503849100c246003d104840345207145140048000090604020316482150056480c0f402c0307803585c000c107400207501488190114003038446e4004802180d4001c2500010401c8020524010764034100715550b54658056401d02c000d00d0f0140703e50340c480021316155510106c408039118075243c00d0104140c01c003011140a4144000200000305014100d02c400 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 195158884 1250 195157634 195157681
    0x71e020303041a060f0409021809060709140f010e01090801020a03020913023a0507171f0512010f0c0503070f090302010e041e0906020c0f0c0a03080c15 67
    0x4940f0300380e8844495001d026121682c22441c0c50344000124205038102d40300b0644090011040219840920b00c50110b0a4031001c03447d402003005e10070b4069111000700090b001101c0c801d00001000000104e81907a00c6001c2c1e8180001d039005403030340380c4c0074048035402401007038000d56031501807000003002948080210743c03045c808078070400c40030310440c42680c0b0246002c2422045508401999001c10011a00d02034804901c160191905400d180500780c0607006940b0740303002811403210464a98003000f0a060307c01d000c0f10254031001c440b500715100448009440030389515a5060416014001c80c0c1910240c2038103029294254590040055200702007669450404082e01c810495010041d0711004c1d00041301350545200901c2d140d40064442000703c070310b010075410001c0c80c000c00d0b500405000d550700b41e80483d00c85404d8109100c102c0003407295034050000c00d0b10134000a001d00030140009841c0ba800480e0840101c41c0400200c1d00ca40b41c0c01500455030b00d0110ac41c00c0e001d12140c650b241c0b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 195160134 1250 195158884 195158903
    0x90702010b0d1b06090305060a0e0a05120304030e0612010501261e060306010e06040209040609090f020405011a030408030901090b090606130b0d1103030d0f05041202060c0d05071e02030304 83
    0x55045c4103031211400d0360307030020242c81d05465401c01c0344003070301c0100b050b42110b01070f4003542000104200031403611007480c0f18902d6201c0c5042c1c1805806401c0000d141401401c04000c1e1840c0c505d140780307031b090558809082048564800d0303014501d4a80b00700b5052400052601c090021506402082040c00002c1d40004c0300181da96030241074462f9020b12840203002d503410042515403070150041c004818019000050160ba50001481a140c4e800381c01e8591030380b920b2141d01903050600035140549141c40c50a80c040c1103030140c84c5550b1200420181c02d001003c008110307016020741100480d40d4000034200e289051100086444d0003065901034461800c0551601c49001e080c007039450a9940100590000320726619200c01c4841803210155050200b0401e0b074030148410710480d100c08e5080400000c6620f490f24010a500300817042040070740d4402003c0200d140100d070101c620008041001056545940740240e852003454104001542c9141c01030110141e40000034611450183e60b100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 195161384 1250 195160134 195160139
    0x150f1206030507141c120509040c05030a110414010c0f02030f060123010e0f0a031401090c050406140d0606030b010b1c0608030901140408010204080307030807021506090702010b0d1b 80
    0x110030051100041c0f01c2d8950417400580c0494441c10180c00c440c005802c6c0146401d40a000090031102143e9180317001c1a004030503c55806400d21440311200c170070500b510310703203170400500380d01d441d40c01d42c901c50400c16a501c0c184108400c002088039035981c00303001c440c81840004542c603259902402945800c9039000e108810071002510300104112040e100d00800004410602921400c0d00840b560440c4800c0c00001c001102e9102d600500300200000003102c4219240c0303000e152440e607000510560501c90140402024849020b11031981110f4004844466190030301c003509903903001800c01105240005107100b41c0d08001c140c48540d01501c90f058035070001800e000c503042ca009080c040c3d8000c0c071500e94154081d5801180b00c0840c1d4012a0910741c1c0c881c030070380c2079034043e40211074103030404a404010550807035092038001d283da00180002c6032400310000c40350301d40140407a102c0e08000011414441c000c1d44001c0c94003034054103544407813440c1c4c2000504800f14111915403568000c000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 195162634 1250 195161384 195161389
    0x131709042301061416030807020c0d03080114011814120607050403020f10170a0902042a051e25200102030702030316051507020a0516150f120603050714 67
    0x7240c2254400040e680412211506e04036280d0100801c040c0541c460700c902001155515924802842e2082c0e444480c1581071148040004481440c0c440c11301400c199a80001048000d95000f541d981d0001100c034806000b000800948105606480600810040c007203213980c404010400d590003a501c07040c04207041028400d091804003203500004805034100f071034500d1032010703c5400c0050000042050303c6180c00060860700032021124040c1e404688982c22250240c00e200f9440700e550401d00d0502201e503c910704258041107041c40d04080020340003c100f1141c0e44208148205555010808081442c0904511701c400215511840407103e0f00c440b150710000031107085a6002e00a1810f08034448045c11900d881a10221543c1c0640707000d440e1410745d030901c0e1074800e640e141e00130b0201d0609070422a00703150040400c0d038207440d41050306200d040038040c1e11219200891811032a900300503901240c00c16070b401c0d01007642c0c5061410000a00c140068001c0588140d0034000035164171903c00c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 195163884 1250 195162634 195162637
    0x4050f07050111030913290f0409030206180102040f170106080607050417100509150105030a1a090705030102040f0501020f030306011e090b03070909051317090423010614 75
    0x1100900d035100708500300c80c0c6d0510700141400700c40d80c6407001c9841c4220604c05000315040c100301c56a00ea11880f1300c1c0001d803a00090000c4460001c1e02c08002000c02e81c0c81c02900c03880010105404000071029216402000b5811075000700103030781102e11250b0700e59031b0054020840c6101542c20350b0134154041510000464443d004d03003901d032995440d162400061400034088201c00b00707003902860105200c84203181c0204c5100720843c00103081c500f07011060390401880c060300607074040ea000c041180c0c002240c010200d00d100f40742e0b12020840d5911891450704d001c01d50f412a94041d4004200055090f900e91054000c2d54026001c0d14428a000e0080e80d40c4ca00044030f03c140007510103141c03160740382400b00c400010b180a0b442d004000946401403000c40d0782c010b03181b001c0001c585810400a82200c2d2207030315003262040060054500c180d4540200303291810210200103040015032004c1507440b684202046903c04803440c880d5984850700c05e50140f001d208100c04a81d81c90192405510010b0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 195165134 1250 195163884 195163907
    0xe010822021e1305092a010f020a1505010e010906050307090209032d1002030c0306010f02030f0a0824090403050903070302031207050d02031c090807020904200103020903102304050f070501 83
    0x35200141e141b4404011150044090003544c1503009445c1030030082040a1000105c5101840010410354940110346111000582c04040c0d42846c108050043d9903001c11480201c54417028096115103001c400281407100e104101100350310203e0007440541303040807091201d201c3c50070654900c0609440748600360701c02200c0b14014140d0400000e195580100c40020780c4c07503c94411203082c601c0b030305402e04d101d911986003940824458020001040d039070090039480c1020700c24110246048080100e40c0003800a40003e045c0031020843c2c50307690301c0820141e001590000c2c2200c1525000507482c00296014810981d41806185450f070074050002086400b816109202c1400700620300c44104c00034502040215034052003082081e0140c0d071521540c40c06180a03092809807001c003000390f1205911407049080c10b050061182e07041c00e950208509065003d01d03000454050060302d419110000407540302c002486d408000d04c02803050001b02100c103002100d0031030711015284c1005442c07426052 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 195166384 1250 195165134 195165193
    0xc0e010c02090406062102040b010f02030711030c10030509010e0a03080714090619110d050403060b0307150203031806191d0106060e010822021e130509 67
    0xd8900d200500380070211940c031600a41e000200941c44100c01031035100d0502c11101c03414412034000e000d510300f52156600304902424611040307040f0307840103034a900603a00042e1000c850040310044070b46013400000314101d002090100c0e0180700c2da50180081000355962071440d86030031a255802800040d07a021441c1e01500c13650840d0342c4012007180c150048903078402d1541c074280700241c80d60300d4540c00740410b140408800386607101e00300c200400c403190408100d0040d034001140c0702810345e00542114140c1c0c1d000700d00850150380b944007007031038001140c2c01040c1d20a002c1c4030300354206030701201460140e00c3d00c01502c425400000700580e074460094a0b807410401c411030700c1182c41c402c0c50340040040748103807002c041441300c08140982115040c1d0300050224842400c1150550380c00450b03a075011303a58031070100c106406090035007418141420024010b045001c1400181104203d00020410b0003c1080000c202283d40b004040c0c4801d0391078007032a101d1161042c0307031399803076104500303484000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 195167634 1250 195166384 195166397
    0x40504020105090d0c0e0103080405011106070f1209290a0e0d0f0e09180f120a03090312020324090609070f210606090b0c060f0403031112010303030c0e01 68
    0x2c41c0c3c01c00c00020b1000b181129801d40407480024140b04002c146402540540c01c0c26482e18a000005007020b084100c01e00000e0700110100004590010b51410748107038540740c01071407281615540d1005108a010240c0300d0078001100c3c40c0803040d0b82c5400c0b005200d4040c4000d0f295107c2d00c0c030801c01d44034805900b1500b600030164400156108081440603080c851800c1e202a04010002c540540c1040d11400300c24901c101704e50348648010007900040103d07143c02071452150308d43d041ca840707000d03200300c007400c245c2c9808514090500c40e0190071640140c50ba0110341e20300b0045440500560300c03030341304008503580c480c2d0510186010000b6900c81c0101420801c5150b035003400850f00b524001d038150b400c0c040c110449a45084110a0b4054000000070002401904213600540240e80d01c0d400741104d600f08205480c51680082001070f00030608481b0700031107403503e19080e409003c40e500400403030b1402240b5007580291001c07c550403680680c40401443c0060102281c4240a800c0b41d00d012401 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 195168884 1250 195167634 195167647
    0xa020a20030405090a0914010c0219080904050a0608060c280e0f041d0703020a050d030507060e01020d02120a140105030703021e0324070c0c140f040501080318040504020105 76
    0x3c0c1130a56a621043c00b0b80005603145840c0e03036101d41000c6144440324969900c0c0e080105982c0c0400000117884420018240f03482450350b904020391094160300c5001701d44032400300b4071b003585a42104014020b85401c0e1240c51400740103c8940c4d070132001080300030712900911100518508030520310305010715902c1c02040d0a0110500290014140c00716070040e0380ca21341c0c0d0508043c10064020846990000707003800d04e156004119080629400c103603c1084240704640011b9004800c586860f5480400070420008808d017103030090051b403180720007031400000d15650780591009050301c280c0704100d003080205004054106244024014103030143c0c07200c0e0003403000d032070540581e1000c0c481d50301c2203039440030307507040482c2c20001284043d00075642000041d103482e12040289942c810750070310b0300b1880c04030188c07620301405032140300c0c4110f42c4002d0200001c160300c9012001c005d240c000390045c49956921203401d42e913a80715110322010300340c00002d40d8070149064021540550b030140c1d00d0300c0c14900c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 195170134 1250 195168884 195168889
    0xd0c05030106050f0a020a150e0609060f040b0a090203030708040801050f0c2212060203101502061302060d142e050405070908070803030a0c020109050a0308060a09050a020a20030405 80
    0x14842c0318105c0c21751180d20030a6001036040040d0f001c01c03040b0203c002c16003030194003696281403400391050001790801c03000c01035000582c81a10350301940021071841c803511401721142c01448006800b0f9094080004c150041c808460003c200301d501c2c0c24002c00155848900080702404103940088540004000c00c03103030841c05d0030380311404d10031419810f1401903841c0324189c0c550b80040811104207030080701300720020b428500464018446501c0e01c800d0b030300804a000b074540800819061030903140500d11815900c94506881041c0700842c404c0025010f01440520007030340480c1e0006c40c01501c1a04a1b6403c00d8008224600300745050305d0802c482e00702000c00c0060440109000100702c3d1140002890700760400c0b210300140480d00c00343d80e0b44e0070052102e00580e02a136504c0420340e070400b00404005640050034540c80c03500740c0ba280318103860300f000060140c1e60035402103d510f030511050003050540ba80c0100418040f68a907000d0f15140911f001e040e20013200e400d1683ca42044c0010800360 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 195171384 1250 195170134 195170137
    0x807030515130f05011205251505070206070309030b06010f020307150b030304092c03180609040213080c01031103071809090501140105040501080a030302090d170d0c05030106050f 79
    0x2c4100240801c071030f0301c038149040444000760b101c259200035510b4140c1c103028083c041d240024190750000c4a001c40326041e44c111030070444c8110b10740014041d050081161052003520305496004108c5660b402c07490400801c5018240401d407103403503580d0007144c019030003040d510110620030740186040449070b845480310b001d50042c94889035922012020740e6690207000500107007854410008081c070080c0c00320f10181e0213040b000f079503070000a2842102d510000055448200000000c400024502400304151b400b6001e610b5400500200381090003070300125080c02600e194808440f034014401d03004600b030700c00006035450340c204100003040242d885002000c81e00904054500c40c2d1950b02c2d003101040750f03401c0206543c244d5407880032004485240702c465005017000c031818060380d4100301e805612a031b10100020249030340040c4019241e2140e0403039001c0141c003c440d640440b034100d070520102d40e0082603200030f40d52034100d03542e51407030040b41568140e0700c09aa5807400c0440002a46105 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 195172634 1250 195171384 195171409
    0x180605040c030203070e07020c03030f04030209060a090501080a021302090105070b09030c06010b120604090c150e0607030c0b1e18030705120903070608010b121009020703020309010807030515 84
    0x484201d40781c08405610f0030001c1400500c011592201c203440c0031070000341003800450f00c0d0b40c40703a01304100f030b03c50391414401900e040d00d404980c064070302d480c0e040005003c4607140d8440d0440c20704000000a2807100401c0d0942228000d90f41d040d003a421082d04902244550924107011680c2404143c5c0407d100d44005070307008040c80100c0f0310700f002c61400503180403001d0b13100c0c20081000080302c0c03100e0401c512040ea00000240d4040c0184242a44c400050100350300034451224130b07030155500f5003441036000b600038841c003400c841d03034884080c10014a00b4030200d00c151112811000840e131820340340c400e030354003001c1c91420b00e2040340c542d1003015212915900e81491144000c0c800ea0011a03403d1006818241d92106030f5507455961605050415500c1c2d131141c070500005500400549028004494817012011101c5c151550344075821a40030410750408101c20707201145010400d500040100b4541c44241c03510000d540d110f1008405440d02102d07412500100e03000300f10414205011803240 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 195173884 1250 195172634 195172643
    0x604031713030506040f030306172505060705010c0306050d0807060c03020c011508210d020a11030d05040614041505040302012304060e0d09060c0602160b0402030606030118060504 79
    0x707650700d4841901d0410143c1d419181d03d126480701c80205038052040c070340140b030b402c03240c2d484000b80103580688070310b02c3d800c00580138280310380c504481400b1244144094100201111346034900303410218002c000d80e840210101c0d01d44080400d89280c00e540180380aa03208107103901d002079940c0c50760003500d41c90240300b041c10380a010420200000707004603015a000c245140707000300d00e05100c40749002d0310703500005080900c40030041c45071751204088610b44d0700074030700c0036950b4402401d0440303a03840208204129404042401c0c1d00c407143c04d41080d40038038090003051060040e5010428080c520035200184400b842281180260180760460b50340070f0f000b8000016041041007a540c441d120300c2c000340304005c440e001000304122043c480c4000410f112001804085140c11001d04069114041d0609201040c181002044983d03011588008a10840310610360520724200304a08801d030350403442070080c0c0c0c0000e8001c0c1014410000614601034111031420742e5615800000d001c0544141e5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 195175134 1250 195173884 195173917
    0x5100b04060f02070b0c01200a0207031709040c050301170c0105030f130501060609050301110a17100911072f040f020708040602031209010605030303061002100e0706090506040317 79
    0x2885c0307070001d02a2078018046400816081c42100312110141001c5c810070306240c2041c403061003135550014004003030700e0740510306042400c00c800c07001450b405041255076200d400c0c1200880c0640d0700c00060342c1295445402c2c0480d00014083c1d003520b031034280703c0640c0000e40a03c005500503a240c003000b0b4205c10f131040300c4460200302d030321000d09491182d000203000c544100030810590400744582c0310060485296242002c01b1280c0081040d1540b41c0c002c8110301e8a04041a03d641d2103d1485000340080c100800c140111420814100e4114003c166121002c810940a585024030038822200c2100700c02d5000030020081040700815084950002c003d03801e001d02000112148001c00142c040da07001581c56031941205000d840600501640b00c1342d041440c10081d941b80003041d00c0c4c000304121003007200140c207058102d1824205854441031542042a85d610011010400b202903d21b15510010416140c1d400d1007910b100f40c0c4030042002c40140b00d96640e8900800c041c24500c03030081c2484 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 195176384 1250 195175134 195175139
    0x11a091f0e030c04020708041202010512040b070f0201090b1902040e0c030a0e0a08120604091b05090123040e0102070c0306020c060f04030f0e150d02040905100b04060f0207 76
    0x40203024400304040000c6407260290110510701005001c02c034101c01c603415850105182e4601140b801540b10f07840076490030801160440e0b0251042c0c4002c801d002000211034035040c20116000070050740c046c00403a94941ea4041c0091040c02069072150700f210032130a035900c640c1072440e0b68640c040b185d4a110365080c80049501c11f291a070307050003041d5100230184c6030300b020b0201c2403c03111224044100d036070080c1c1180c0c000406910641f602d8000340011000c8543d5281c0c00f1901170020800010410100080100c0d8030305000842c61065231000e0700c445090b81e80b20346410f00d0f0305c0b0456002c824074940c80c1002c65960f00e4581c00c1201c01010200c005400c04450759984448414550401c803240e80e0046a22088842c04018807940200709540401060500d03840290075031300041280c60411005400710406515518000c602e000031400419a80e00300f840f0201c030003500a8000d140c1c00300d040c03101203000910203800e10001d80d508805003a15003403501300f069908200c068034841c154041c82100 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 195177634 1250 195176384 195176419
    0x30307180515031b0412030e011202040306020a02011a0102191a070c030f0507110103020717030109021308070f05010c05070806010311090601080f060d020301090f080901090e011a09 80
    0xa01d8005402d5000c1a01d906040030700074140726000c80c0075060351006010070084c0742151034610a0f61074050400680c1100301da40122050209000c9020415000040000030005180e001b4500390340c281e4001c0040300002e00c01800d65240300300003180141c1c441c41c1d00f00ba94031250404100d00c2071007800c039440c90700c44100e60000080f40440d100c1010420340d400384400c4c19006040c90034650038a00d00301e4039260040c3c1c1c0b03a0301c0d803090a0403150304241c0e02203042020020f1710741140c1010759400d6615500ca60f900c003d420060b501030103103501034244035100010208000134110080d40c007803184200300e844c201001150002c2d000300c0e06451500c0761400000d0f81d100140a010f010318004c20010312582500810310822a102400701c40c101b000c0c0350100045105400707881600198111581341407004540000790141020b18800b400070b80d041c0310001c0030050418003c00700c03a42c1c280c8885244550718010790800700800d01c00c0e814008c0c03603042010009126100240506040100811000d81c07080780d6 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 195178884 1250 195177634 195177649
    0x4050f01021507030c020706020601080d110109050604060c0306090209150901090e042f0f01210203240102030c030d02250b010e0a020c0717033105040209030303071805 74
    0x41d203c001ca99a4804030030615030520444018221600040c20554980354506643d0f05003016108200801c20702503018505082d00203202d0150807800300c80041c01d05017850300c0200101c0c1d5105000c6840d10600080801c414000d032582d14000030064070214241c0c4038244141c0d4812482c890410041c08008030310b2103541c0c81146c0c002d60044507082001c180c142c0341d07141c10740740300c40700081c0d582e01c8210018a1a80c03034117200c4120100a18001c9136000c0030081a08080544010594075a0300100810920740f04d80e0010756055054042244400ca00ca80b005a07164491000640181d41040156044441c0507030001d1690780b01584642d0411702c0180a04407580c107020b4022240e400d0b0752001085640140c218440e045080342204601e41074580400315941c4000303109841c1c5210080d9421502c071041031083d10103200700c192040140710844460045800380740301c1d0700e1000da84280c5c07020546050600c2911620b10f4040c0085196803103203041560580d0840c2c5404200c410740001c086400e444064 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 195180134 1250 195178884 195178891
    0x3050c060907060329100921230316020f150c0105060f0d0609151d01050106051e0c0a050f03090f030606101116030f0501180804050f010215 62
    0x780507110302420564000d0a5907442c8440e0300f84228118032a450368031411039080c100f00011100c2008916203a141520240e40e154006841000d46402c2101d04001030010941c0c080c0c86098031a0780e0103102c02800450041c0d0180c1d9801641c0244044080000d00c1c40c10241c02500081001a03140b000c80009000a01d20131503d8900b01804036902d160100240240c40e0001000c503901900b002070440410400107600e0f201400980d20341c1031040911074241c1001f8008908207405110030b200c40308018207158000c0050095941c60140006003e900c100181c441e012015103c2d80400d80e4007034000716071500b0444415103d030042d03240090004100300700450424010f40080c1d512100901d041100f400c04100900d806900310101701f044d5a1748001540c1c01e0b1000b00d0800c00e6003d405042007515109000c001d40305503d02900d00401070121560782080603d01c0745009001c4240e0110002056003042a0b0041031800c00f840b09101614003960155000801841101c0342ea06448071520300412082e1b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 195181384 1250 195180134 195180151
    0x2120c0418090201020d1d0d12020d02060f01050409240e010b150307030504050a050d120b030c1003110f1303120c050307110a080f01060608010807030309050d03050c06 74
    0x501045408001403002481980501d410402042c0ba070300041d4035142c0089000042103600032030000d8000980940006190b0b000d8007011210807a17181a0010401c8248210058481c058280c00101d00c00038502c4d100310b0452040941d0750340703000c1c2444003811900c641226a03c4029684000c1b9882c40e40841030042c61001010540d0034052200390700310344903071582c42e010398903006a501c0c9000114048030b400804902c0c0c0014180e56a041280c02d0550180c00100240280365440d04416800426400744100c003e40c20400c6118610416541d10922503000303400c0032000384940d40482c02944500100e0340c2d06107405203072412502d400c21050340002c018298072544001c1c140180141901850219030080c14407901c03081d41c2e40c452546d640540310008049150314810b5131283c0d00c400e020b203401000ea01c811110b07484d2040000c180604030600448000030310301000082c3c034041c0050410100c1c0d4053322002d128070700b00414800d28540f00300c07054040c00f5042119924004040103000e02c18403d1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 195182634 1250 195181384 195181387
    0x140d02010501052b0f050a230d030c081306060b0a050706050601020102030402090f0a0f0c08071403070f030e010e0307200a0e0a0c12050115090f031e050102120c 71
    0x1400f0812200e60155030607014603400400c22142d00e40c0c860b92924011a030031018500c5140220f02d4102e24004507650001e0404442c83c4180c401d00c08100d0b501d2a00705d80c04419500c000001c400124200d4858600c828000b038a01c0000c40e071491112290095146c1c0903080c040381058490040c440300b540444003160010303000042c0c00003032081a01c20f168001800340700a529600301500040d80d18400034215040e81c000303000100f9000399256000c1c03080024500c900340f0505a06241c00b50103a00308940080204501c0400c200c2d0300d43d4030381e044138030901c03a60711001040c0070421710450060124002d0341c05590340e981072420b01c002c0c00300090705d20781e80b04240c0d0200c80c01d0440e01d42c202c46503000341190300620101c0c6050001c05c40385003c207a4450b104c000d00180140d080701c411601c01d07003500b801c420a68034107400030074089411811820826803d842c1c95048030740d83c0100e110007405500c4040c10742c4100881c0c00160000f042c200d40342c014000c10003d41065081400550000c8041c0d42120000b0300 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 195183884 1250 195182634 195182639
    0x6030a0c1829042304080a1707050c010e0705060a0e03120f040609060908030a050c1e0129030c1c0c090501090c03020a020706030c11030d06031109070207050d140d02010501 76
    0x741401340c3c146201281da0310342c0e0340540000d034482070340e00040e00041c160680451040c640c2d0381315034001100c0051246410300d040c100400c0c0a40b144c0c1c08000707803443c19420906030f07a0800400040d403400310780707016000502d0081450011916104440c5045505000d00362140c205a1942c20242003c48a0007002a544528045000e0071300c02140d0700500500c05000710030088070340040241c5a800b0306500302565515042c010481c180300c015160a40c0c02e2400d2801400c0a03881540400900c4800c03580c801d40c1c280c0076400268201c010000e07000d505502aa00752005403c1140303800c091009450541c5088010682e030302017140e4080c0c0c208074035840c0e13208010008419039004030a2002c0307850404620b40b002c180002500e41c401c030b000b9001890f40351804842050b1180e03020012035003000d02074944640c1003940504c094910303032005550300030682c80301010501d003840c0c0c0d190084615030001d084082c40e10060141000003003000743d032490790141240300b10b48000d0040c601346080c6075000050560 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 195185134 1250 195183884 195183889
    0x301030b070f021b010507080417070306060504140a0e03070b04050a03031401030b1602100c0507020a050406050319020301181b300807020411070b06030a0c1829 71
    0x242600b0181198882404101d6070440038001c407483ca0003c0c0703402c0341e6420f6036081204162080ea032084400141c6d0b082000340034040400c00c43c05892080d01c2c141728060342d4004001c16641c580e10307000c24030504640030490380031041c1e001000c0f8050b0131041e24201032994458035501d010403030303007600d090b00300604040816902d8418028440c082d03920070015075046480c0c91015400c000d1400714026654958004594020420401a400910000d0061555a80004042e81c1003072034101d00410400c0350110301c919060207544160380c0090000c0c404030500000e0014002002041a6059540d480c0b1985003d00e285a02e440081e01071000000c8401c24550100f40810050340288148121350094440400b4482d070450455480012116507800c1c050505c00982c0c03103410b074025802440e0a1480000c809a04040c040c45030181600b056680d80c0d040900d5290765007420024191a6001c1c410b01c05c0350469050000c040d440190005550741290a505144e442900c3d010101300514601d00034051 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 195186384 1250 195185134 195185147
    0x904091208040507050103091502030403020a141f050606071716080301150c02030c010c11040501030b090f01020918040311010c0e13150b07050f150a0c03020c060c0d0b060301030b07 80
    0x8203020b1030100001a2380e52589000d00780c2c000c405c41c43c0b0503000800f207000d00d807081111a01c1190402854800c0c69460641d00c3d5a4592816502e01d11540403a48404c03241d01510506101d032501a2003145001031aa03038801c40d00d01b9549107130310711040c02e020303c50003003046031303002080f07603100d9651a582e9504111400403404070545076030040010780c03001040142c5010400c040c000c2028200300100c2109450315105500d0400d4260345c200b4070b09000003041c040c0013101c03c3d010b1142001500e000c1d17140c0e203264a00340c0c0f06032510a600460180c00c00380a00e420042003a40c843c0c0249400302540351454045070940704841117800000704400d440e00864034059000511107003103070070100100c2c003e111100703003141c807a44154104000081014418850280004101440da6006032140e0742c2c03039440c0c0f40540c2c40c2c0954804492074a05005910b41502a00c03ca8401c440e20000400c0e0b20303070300c4005982ca00e0740403540811585403a900b80c41410740310403029501030351080a03601d28900d0003c1000303108 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 195187634 1250 195186384 195186389
    0x21070f05010e04090218070306050d05010506090705041a0a030b0303130f23120f07090603150e0c04150f060305010311090105010f080402030703020a0303110d05041a0904091208040507 81
    0x18900d49080e040c010794071b5040400c1c03910f6400d18a00e003603543d000c201f40e008000950100c3c0d0071503d0003100c42c2c100300041d40401d00c00d9030121089030711a11909000c0320207010b03600682121200748200c0340703414451000a009012000d15020410580d80c01c04641590040c603101c03440001150414442c4c02000035054028000c0d20104654845480c42001340c040c0d18001e091b40600c0180441c03c900c28814018107001c04403100880308642ea417000001c0003045244000d82d00ba843c0c2c485090a600541c3c028031416040c0030000b4100e0502803020003008001d4914070750352140c001040050070030030f521202e000420041d100000c0640c0343d81080d420507114000f4091003102c1960051000340e800481441050080d4a000c603041e03503c608c0403074905105900061350107444032000004142e070100b900300c9101d13040415a18030780021203080d10700d8000da0054034240d03441c4002078030a51840b94040c1c0182c0030001c0000c250501b050f11303070b1141d0440d45600c2d0070008901d8410802480001c02c0f08800 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 195188884 1250 195187634 195187639
    0x501020111090f06040e0108030a09080102070309060e010e040606020706022b080c07170d0b010305040506070e1f0309020135090a0c080d110114010521070f05010e 72
    0x5500450041818501c102c42d60700303115114030210203080352034500943d001307004803401c40046075840305d40b15640c2c2c0d0811194540080c081078000f00f0300d00e07418025100c1309a4942c8030b1b02002030a01030183c0d10320102d811300a04201d450710b110342150380c90f4000c8100500154002c0e090607410040000d090510100c100c070400c0c0040f650042c1041d100c00410341004005103010000ca48529240c1000d07441010006022580800e140303000101840004045405040204001a81c14980107509880c011500500300d90802e100080f15036000d25404080c41c10018401c84886426103140880c10070f100d6440d0300001e07980c1a4004c11560010001218200b50000800a06002200100e1409905010181140c1c02c00d80844c1d10628100980041c43e0b40c442c22400d1515203d60210f42d450000d0138a90002401c505441180d421040c451340c1108004044a0304050307003003c0520824482000c85041d071003144c041c07020700038041441145d02500c0781d8503929400c245000001800301031900d89191 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 195190134 1250 195188884 195188891
    0x605030c06030103061e0204060305060a060809060a050c0705030313020f0d12051605060901050a0f090b1f050d12080a0e0309040b06040f03060902040609050c0d02031012080309010605010201 84
    0x599036440d0140c83c11250300a1011510b508240800c001c5080c41185400d034450003c14007260803a0103030070991080d14181c3e000340703266540d007204460b50341c2c060700d4404464002a010580c8240719800ca503600000e205030340c1d890804143d44852131584111400c00e03121003e48618000c52400c130120780c0d02e580e0b00311015088018207441d0180c2105540c4032103000e0040000c0c1140c001070031040c000381000c0d00103040d19580d01d840003585004c1c0404496090546241030f602d03032040341841c8034000003941c202c04a0245603407030381040050103038001048108203548a100040c642e849040c11030b080c44c8599144c8948140183c005800f41c0c6014003604d250130700700110060300320000800e65200300c0080350040313109159180419001d01c00d541250002c0d00c2e00c4c07000441031000c203421107103034144207850410206a0706c60407141107400903104540058010040c2d00c200c1d441d10707000380d90400c0903c120051215032325a4070708101050b41808407a190404020031040050a20403200248403e00091 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 195191384 1250 195190134 195190153
    0x403050415090e01060806150414090a060504050117240708270102040611030702060714030d060e07121506030207150507030204150c08030103080c032209060503 71
    0xa0140d000d80c0c00780001c40312a07810703903104151150071114028190102003d040d9611014002c201e404100c401602859403c600b2266800b98038084400f180e050050b236038542c03243c0508100d0350b80c10150020040316101d000c0450b07103a4540c41018002c14440d507140c2d90407aa0020510306105401da0442424003112101c1040b0602d0502030725803080c0c1c1d0345000503140c0c1d1503140d4556010820001c002035a65800311240c3d050030154000c00640b0303030645846c03502c054080540390380c030300c00e0710070094000e00c0a02c41c48000442c0592212030118151098a0a150004046800300c030301c6688406500b0302410300740b0040c150081d6402c2410304141e5024480d82000480c03c4400711200d101c2c3d00100b40c0d0005842c1c0910259015400a0044242080c0701504240d40000c011350030a001355280140e0103c6c0001649001e40c002002480d4040e0445040da803030754441110a80058207049442e0208104591100750500c2103a90828201d0400d074a0036400e01c80900c045990740c0c0c104038040d62190510 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 195192634 1250 195191384 195191387
    0x71a0103080409020f12010f080708060103151d0a06061a0304020d02010f05070512070605071d10051908010f0801020906030c07050c030616020c01030c0516051905070311090403 78
    0x4a82c140e90840d240940d40f40c05d080c51049051241d0480500d11641e81d80002c108a651020b203542146c4144089070000fa07241c100c05500d4043c01e102c01462080900c81280312a8055000201c81800c14000c103440e50404a040364100369000c00120b501030342c4c8140a000d00410b0f8400c03400e2800300b104076181145010380c08290012640c000182c140241201c121101c0d501c2401156446c5502c00182d030005101201405039507044003a04903141420030001818481c8526000da0301d03244100b1185038490301c0081031140c0640424408c1c41044802c000202010304002a0815122040d6448102c0d9603d4010011850446030308032a9299004200c443c1a603540c3d1416a500801150f050355900c2d119844d0441c075004d1106400f6030540070311400c108100303250450300b44200c6e18580a0f500060151401101161400c19107040403403c10310411080b0900c441c0d600c18001d204100311214110b980b00e02c80120341c2c1c4103a0444040d8401d08051003000084c0165481140040d200e0307409c107080a540 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 195193884 1250 195192634 195192637
    0x222080c040b06040504020f040e0618070f090f0e040c080705010f11011b18120f030513080f010c12090206040b0a120f020c06070e010207091e0c0203071a010308 71
    0x203606110701d490701409040c1e542c0e041c045900605000300f0842da030f0b1000303c0d0050400e820620820040810f072400041030b50804503114540c070340c12615110784696408000340c130381c07250204030141005030220000c07030030403c102007010180146a4284c2d4540c41c1c28a8000b010007240d4100a1300c54028070000c00550341c0240036226000280c0c00c000e1001c01e02e03448900c0c0140b4240190b80070180c901d000030800650032144110242c2d000c403d102403010b40301c0080504265102d0001094410005004d40c0445d03ca04090080303580890309104c0c5081e5281c541d14a411091000d0b84504d96681c8500d0542e00c3e008105a03001d405001000d03c014115a00001c0140c02035100e23644c20303103000043c1c880745144605040000c4151040701004400d0b86950302d42e0013904a220104070900c07408020031612802901c41da080808164000c0c171044c0c2c240245040501840c00044d05801160096034911111b0303802005203150042d802562170303441c1400c141550141250411100100200050000c6882d550 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 195195134 1250 195193884 195193903
    0x3010e032502100306051c050304050f01020f0a0803103305271e0d02060a02121603030b0a1d060112140405070602010c020c0d020d15022208 62
    0x6000518402070000ca0700314406200740080d400b0603003801c92800c2c80d8255011400352002501d80e4412a07990b103100365141c15011b4006401d03544148800c002d1468040090858a031061040d2a2116500d000b20340c907140911004a60401000c000c010540b091700740b00300c0003014526070451151103e4007240c080c28404040d07040304980441e80342a03c003409401150b040c0840805500c05215034102c4500c0280300419800380718440c00b081072112107501d1840c4003c0e1403001480540000e42d26820850207a0007040000300b90b014510350801108802005042c1c0a0b4050410682145903490001c0440d0580032055218038120b0034140b00e00c4e5000c0c000c51b001320b907101c0716800544d00c640d001a40c0409402d440b40080f03608000e950400d0040d0501c80d280980d00c90401c95002c1511104260f0076034801031040350040c0d101003140c03016444c1103c900440d143c000303442e64040394101e4950440ea450600c04d003005983d00084c443d80c9a01020075034100b00d0001c0061108010708251107543c0301c0c034010 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 195196384 1250 195195134 195195157
    0x20609011a06030c121003150504082d070308060405161709030f0412020f03120720120d0807020d0c03030c140c0a02190803090d06020d06140f03010e03 67
    0xb00014181d0340c4000300700c461172151700c0f400e4a001d02c0c10000052091085010032075040b1400c80c0c881300e241d500d6005403401075a00034540c81c00c00e04907802e032540368006041c041c400c0144034400c412a03a22204010300a60b0300035954a405450100180000d45030013a01d061b00207540464070352825640030700c0b00010005400b0700b0507955140e00b88210f20310300981d0003608000500084c0050500c41d0391456014840c42580c1c1003201c00008001c05480740c0c1ca104900085802c20043d07000041d076103d218005000c0c0c07800482410748044c1c40440c0d41c000c840740d6111328940c41103000001440e0090720301c5501c00709a10041c49407410f240700051070700d20754880050915499401031200140140102c0e1203106001ca030300d5441d036400780f000c1d65580c01e012009a0003034480070014550b48220b10303000400d40380e5a00043d0700d000d1441c0103014401e01d03040e00985c0c8550342881607010400b403600034607001704014004142200780e120108072101d04103c8401c3c0c8283c0c5440504a00c2c0400031099405d2951076 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 195197634 1250 195196384 195196387
    0x1b05070b040507090507051c140c070203032118010c021506011b03031b02191b09050123190519080f0d030e12030f06010e040c030903020609011a06 65
    0x40d460030520b403c2071504a81030301030600041203100f40e8090b000d000448a40f0100c03001c0c04e403207604000d0803143d454a5190382e80b4100000640c9101d0904001c0002610150480c3d00d40490044440a15028080000410700e000418010404140d0305d0703101030145007800800420456140295481504104102928540e40d00140b03d90780506021150000d4011911040d8400d92a00500503d1500f000410304c0030b480c50824403091002030204d10400100e07031487c090644540300e0018019207001e03506150035114501040381d4a032401850300a222000c02c58505c2481c140360745181488c4001c0990144100c0c2c208000d806215058140444205680d0500b4800803502c121640d05419000103034184619500c1c0300c001c50000541c90009200c0c0d5404100c031251a88600b500c07001c1c1240300c9814030340c05101081d0b10004400326290400814100078810300d40740e001003815111030110400c00301365104500c000b410380501c00b10b544000c80314020041101c0d51032402015589540e20113004a10 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 195198884 1250 195197634 195197641
    0x30d090b09010c0606180e062d040c051f12020306011d01030f020a0512060d240f060b09042d090227100503060f180a020402040b0406031b05070b 64
    0x61941c80351002c2e041c04203009103059800c6021b08040c1008400c01e101500c03418000450794095402004002c03542401d0f903560182c1e14000a42201001030025500c11a5141c00000d2643d190981384001241e07150807d044001d011801805500582e56180c2040b4010410404903a912203c03d140300d8010030b00c0b803146585401e00480040c40303072043e206a481c1c800100410810340090240c14170000040c0e1782c003c07596a020521003140c0c030b91b250040501040350100c0401c24640e50003030108030760400001601d10b840d0302e400c50642e00503034003682c84181d0011b4a0b000310b0900380184290301004004090007a15007400311440101030140300c03400340b940c0d0f4004004542c0c0d00501c1941500c06003d00034001c50b407000a641e00c03510241c421214070110200300046a05022030710358800c9003080c98840c070542e13600300341d9211408008501d0403540180c0300060016522440a44058070428001c16207450074424050704a0b155450215103180218130980b403e0b031b074050112a129580070440300320b942c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 195200134 1250 195198884 195198893
    0xc09060d15050a02090a08010207020117040f08030c03010816180c02030904050f101a030601031e05040c0609050d080f0703050408030a17060603040c140112050a0506030d090b09010c 80
    0x24146a4407040840c01d042c140400e840b92a006490200c4007126455039140d6103240f468202e20803010006d003c01e150714042c0080c01d0055000c690711600911002a41c6804e903590b013001540101d8403020f0584020006101e0326a0400583c09401803211607100c0d40350030400e6010303a51000c031404030001a16440d0100c09140b0034026502c001a000d00203124a040503404d000c0ca00c0000c449024004405000020b42c902c1191114040c0c02480541e841c41c50311a10011005010030034190484102d000214440d407070700b1031003414862400b512013803c4003400d2100088c1044919032241c0c0c803401c14920000c0c049641d00c411650311044c05105a030b5501070a14007502ca6009030b9018480754000401e07400c1c45642c000100010120442d01000c00d55652030b401c11419000a40300581107000315002440050600c1003544480760f0141490b4440f0043c0ca5001d0040d40d904466030390340130340c40c0c00a1016908040205e581c42ca416410500c00b010704103040009640a0004098100b10b0312108120622 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 195201384 1250 195200134 195200153
    0x5190302040f0b0a0306060501030509060c03241201050906070e150904110c0106030c05010302070b18030c0a110a0f03080f03040602070c0801090b06101d0f0a260c09060d 75
    0x50f400a486490883d90b01c4c10300704001d102903c00d050100f400c01c00000c0d101c820200f402440750350012072003401c646885038990301001c444e010500c2503c0d036a55034503610782d603001c0d604408003020310000704607460641e8405044c9400900340c0c005021100c3c034022000c2d80c401010440d01c0e501c9041094941c50701ca000180a40840c9000398860000024452442401900804180c90164015606560703451004404178490020061f017104980c0000c1281582c0b141c4601e2848405030003124204140c80b14070034100306000c1000c890720500c00c00d15148609110303078520700078800011140314061854442c12854800c1c00303102e4003200c000000003410814a98142c80880703402280c0180c13480d4a4144281c000c00b10303403200fa01c0303c40f08080020304902d880d00440039600680c0d560036030802082c05040d08041106550315921601800000d8031a40780c0703160141c01403804540620041c42000e03540c040c43c000d1820712900d2034004100c440e95607211010f0384c1e60807060030350301c0c2c8800004c28209900300 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 195202634 1250 195201384 195201401
    0x1a0105090d0c1703031608061003020a020703170d05011505070b0403020304080a0b0106020c0f0102030f07080c010c05190503090703020d020402190905100c0224070c030803070905190302040f 84
    0xd828900f0080381d04918000050b602c2903041110785510310104900039681540200ea40540c010944100e140b2014401d4020f0907d0403038900454490316213959910503804001a0001c1d224030002c10080350340c9980b40038140c01842a0080030700800d0840304010070500c641d0b440070300350704603404c04a003c0600c20400c40300141548026030b450010b0500d8480050074003889500c1c0140304601101141d89440581d58040082c142c0086140c00c02d6030480c081c0a4004000558104109000c054902c0c4020300a0344400003807560391a5403840103206600c2c00c0300d1410160382c208001401001901c8200144250540b030701200d449010078018070005010348240002c1140201c820314816030000d4200726003806451080f41d07074242041c0300c4001142c80b000314001c042c0d84071001d000442c03210100c00c50312044c04801105031034a042c2c83c544500b540401c090381704a44020000040044081e032044c000e0020b00701c01c841d08095201d1000355400d1410aa00020344030719a20000710020440c141d220825 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 195203884 1250 195202634 195202649
    0x1050612130503070b07080108030310170109060e012304050c0d02221e021e07030311120103110901030503190e04060810050a020c0601030f020312030c0c011a0105090d0c 75
    0x5130350b000d41c038001c01e1501d415101000401c0480c030001c03905060100c03d0b80d201303500d41c4034800f07007492600d014502110000003c0e5003c0d0f540c0c50b00c5440100703206024a000c40d9603c1d1001281445501039460b0f80300401140040040d000701003800005078011404100681c42210940f400c0c203558000900b01481d0076074211041440341c0c000b15400452500040e1318801a500302e981c0d00c607081d0818200368071601d501a00c00315050038010525182c03038070103803031601d000c0d140000b501015041410a1a480750a5840381c00c00c07030b20010400c0101c0d1250001c0681c405035034080e40b5501d1540c61961b280110406003401030220107041a0b6944030b8045911400401001440701d50360b82c001450700c6482c9410204800d0f4101400160701d15014000c403464004035000030080c2d80e10755142c5440e81d001d82c2004a900d40141c40380c8144025001000c0c0d4002c44c005401d81d6030380c00749005a2800c4902e00712812060f02c0502d074840d103640e81c016050343c040d000c0564000311914900d1234810103460f0183c10000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 195205134 1250 195203884 195203887
    0x30b04140a1a0607021c050304081006080706090b09011107120b16140c0a3309030504330e13052203050c06010303030b130501050612130503 62
    0x1203051820318021401601001c10400266804603000907000d42031928180c1c102c0320404c2108014148900300303c141c500410680700c816021940c51508650281d07100c0c140c194080c0210b81000035181c420000105034010007411031501d04480070b00034804501c264007041c8000304640c1e100b64040c2104a108906000984600030f442c2c0301205c1d0070001c048419100b41c41307000b00080024602c148183c001940c15180c00d864614001c0c111038035a400420780720410b00038a440b40d000034403503025000e4401e0703020004040d0504a550300c011005020301d480145031b4202030030ba60100350001d080700c0603610b06a032000d2281d1070f0144422038800c40c90780f19080ca000042d0362000c005174001c0e0b001c0328541c0219852a24240034582201c141d610685250425403000d131802d440e50000101e000b1420b500c039061150030020110300c07090404401342d2040e004207131180704008503450042e400aa09001c1c40780c0410665060601240751409500b40d2441c501041c0780c041111801c6403440d00e2460756028003103030b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 195206384 1250 195205134 195205151
    0x110d0207211202030d0b0105090d0f030c060c02072c01051002010603020607260a120b010e0d0b07030c1403150114030403110118032c030f06040c0608040213020901030b04 75
    0x9540c0c5c0d200c00030162a062400014003c00d40c400c0003107038826800100010040034003925005800f40c0e441e0b004405003e001c1281700c001801074065040050015001381440707614040a40034420461308004c4950030041c1204030080139001002d0f41500d0098901d0074070100701344016801403446400280d8051030220341101049095444000003808600001c02034a41c08508051140180d0781d03a640401d07040202c81c240c03c00943e00c01c020301c0805141c0644920350007804200c009010040540b05a00218104410541c140c0124403204100f49482e0404120390000c0013828040034040042504002d03219031456841b50300f041c4034400c008050942e90382003178038000d07040b28000d02901405509112511f0071843c0504042c001c415055140e0740365400010032021441c1d084421a1848442052850346c1c0035141000030a1080b40414001c1215052506069a40030b107507620800030001c0c030760b040100588400c070050303070900c030008805a03d0341d2a040c0140c01030003a4180f4160441d25003800c8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 195207634 1250 195206384 195206387
    0xe01110f010501090627021606091110020d141605071205070e0c0d020d06091e0b090603121e03070504140904020f21060c0703110d02072112 62
    0x21904a0384442000c001499039080c20a4445208401200d82d400040207006e00c0c0d982c90360000c040c07041c10049100741c8a0314540d00c0e2002c40310b078248103031202003400e103003039501e810001c04801d00c4801c0307030004000708110340300000c0000d1448000150340460114148031310f61004040043c40603400419160000e840b000c48200000c010402511148500300c000150480300340040b50103464004121440d003040030030507002a6000400d00640c842d51650005006051417003000f001000084400c0822000f1449000a0312440c2603030b24450814101408625680040c0030010202d280000944031812080407641354400340200140b807201c00401c0090b00c2c1d52050040042e1801d80f05110400340d414802c3c4001020200d400035040718040d030b0740003e240b4201c010403400402d154141440052081945400c0c02000d40d09240303041c86c08a00700342090307042240c00002c40e07050300050404030314084009694994a10032000c1031404610040c2c01c101c100c00c0c100e0602900b21300030718410040c0060 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 195208884 1250 195207634 195207641
    0x23130b030d05070317090c12030904060e0c0304030305071112040e016806030303070507020405060409081c0f021e2a0a02010801060e0603070e01110f01 67
    0x59440c424015100885201801034007541e00940d050744d00c842c1541040b00d404824030314050b1140b00c0350f2051114070195542c070211f4086054444102035501c0c1c13280d1006200546002d41c101c001c02080300c00411242c11312040a90740e003c0c0d05454085010f854280c0d042e1900000502e08400e40e0054525000340310806000400489a5404a1501c1e0740c1e40d03420030080300161440414a171040141107201100708202801c1c07008141e00300c802d002d48000c0c510345500e012500d15290240c24602001c111425160f252455002c50b0581c041c503e14079007202c00034904c0c0f10f5104005e10075540c500200c0c4032030b00e03103030b000712121035000642c20760b00d01c000d2001401c80d10300c8400b091001820800180c900001ca802501d100202c0440c440810030403041001c3e41ca90006410f441d40700c4e0369201c08006040300f503140c1414401c1103a0240007000b520b0f0000400000c0305030841c00a0103135800c6009800d885617000ca0b80e10008901d015100c40030041c00480b210113242d02958002d05c506201c507040d0034810360 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 195210134 1250 195208884 195208901
    0xc0513080601060e04020301031e05010e0313090b0604060801180906050a0506030c0418060504050f0304030311060f0f0103080d0605090a0c080f041a0a0e01020a0503041208102313 79
    0x45031030004031300c140100800e0780310074003000348480e0030180901196000f038000041c1ca41d20980012a007404451070107860758000c021103210200e2003803010050007455100d101c1c0c0317a480682e249442c2c1410b02c0c9029262000c1032184203070b00820111103002c07281d0720341d0095801950003030040c07003103040041d00c980242c030007924103034070070301038a0107200c0e10389000c0c03003146002c0708001c2c02c84601c8074490702c0d02d00080400400a0350a8001c081349070446040600040000c1c41c440c3d107034000402800b0f0049807801400501080311030441205104c581c0003101c0005045a9000f0f07003150b9103600c0c506440b00945602d80c4820740203000e00c2c0c284007604115402500106c0c902c0d945203081c82c0e607913040400740c4940948006d07001040b8001480c01c00d030350718002d5552103c0200c502240861030750503001d0890340524181c3d4002140801400104045d061540d04035424515001d44142400795104015103c0d80c420408241e10a09041d48004560501d40d406081d0092000c3da00940c1c1ca86071030f020703080e44c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 195211384 1250 195210134 195210137
    0x190c030b0108060d051e070e0907031208060a150203090a061e08010317090a080f0a03030e0303061302030a0f0f09020f0603090c041d010e07060813080d0c051308060106 74
    0xb00c0c0058124201103280600c41ca81250007028144015625800e540b11211000803c6001e66400031030290f881c004c51502580d4444024a001890350500c10303428000c040c11102001205024817000f5540c0d140c959080da0300a0034601c01d180d56501c01640765105418420384c0043c001c141c001140ca4100103e0052800c1802e9a20300020b00288119051402400002c0a002c80307503d0160351070030a04080e004035100507040a441307a8881c543d2915102440200904c56407002142a00f015414060340c4500c5048134015070a5041c803d0000c0c0c07a1030300d01d940046225601100240381840550040100c281ca2400100003c410416440307000d4200014107a010b00e0010a001031030742000411640300b40421000340440468010411000d004108441595008181600509000c0a03c218003485c0003030303030080041c00d2501402400c1628000d0800c03500c600d0001048000ca9849411101c003c400d01c0c100146903a8180001e988600554a005490740040c01020500c5100080d44a060390440e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 195212634 1250 195211384 195211397
    0x12071a0d1407110304050a0b0d02160602030402100c2301110406110105132102030f0d0504030806030d0504090527070303080a0203191e021611100f0503190c030b01 72
    0x7a0490f40c1e6882c401c921859030002d9205100300112150314019005072140a14090b2a1502058040c04410301c401e030161021580003052100310300e0305800d40d091010301410f250140c40010f4891034902c06440c1545004500c100c2e482212010003940700c6000c10450548807078540f600c1e018001c015402000600502d98a07000c04070b411141011078942881d0760001c1000d4403407650021810085000b40c08103015032000b44146600c04a0201c007520b0040e4811030700040c54506420b00511440c406070005001ea002001030407400c80d8048202c17026030b43e44c29808141c03622401046031515040d0400000700e80705201c990f580703080005c220001180e020781c4e24031005446020b285402c82c802540c1c00d0700d90303003174080806024150f181c00890803495410390804450703090f0012a0300307903030064102140101c0d499031503e003007105855a520300c01e45c00f41c4410303086607100c01018040344c81b022680c2040c4080400061154401000c00050301c0c000311500f4010311101d804c02030050706040e68010b0204a9 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 195213884 1250 195212634 195212657
    0xb0a0f0e091b060c0a0f243803030d05010614030601020c0d02041415040f090c050d0c0b071b090b01080a05060607050307050a02030c12071a0d1407 65
    0x140091840c0d002a402e078400c1c5001c00506003040a02d500c42c501c1d1400c68010301c200803000c00d4203810b46010090142d01410080d0300600d5801c6200380c5c065101144003031625000c810340e1100b2512044a00c14500304402c4041d500f404004002c440168030107a05100000e01550a40851f030000c504885064950f40f020b080e0010301a02540002c880301030041e0300c00c0100045a14000b000c0c0c101103070014000117100d00b038042807041802002c444080054000d100d0001c414109031044221320900e030030040001040d01d5a9641d0354001620485110300a0340200340c051180071011013004010300e4011960f1208945030180030135074007010002c0102c00f035010004052015014028a40780160340700c101659400820000134100075143c039801103c20301044001078010001049036500800090a0711a02481014980100c00c0c080c5070040c0c0d0080b8000040347d0002440c0e800703840d0038040a05e03e109041d000e61030b044c02540b1800080500780300c84001380e00340b000aa80d00400c401d64039540d0000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 195215134 1250 195213884 195213901
    0x5040e010f0615050d0c030204080f150702010c0503010b030a0209030303040308150d05030a030507020f01090305040810060b070f17030f06030606010f050f030c04091104210c0e04060b0a0f0e 84
    0x400c207207103e01c04500200205400148070750f000d4018048641401400c00e40c07541c91700d5180c0400940c551803140d10841c6944c006030b0064060f5a4864600c2c4000d20081d0b5610740020402c2c0410704c586048220040049400301034140c06491f12128040c044030f881e864503040040c00c1c0c01e016913803070301041e100c02811030050800304009800c594210340114030346400060101d0007050014540b8046028410481e41c20072028000c000400d40650b0b01d8a4995043c0413006e0308000c2003d40300d060313580c501001081031465401c20b84241c5504042881c0c252100303800c1100440070016001410360100100700038400c1115000140905819000c45074141d4443c0015118019a03814410106105220074100800040001e540c420f141102282c00c00d5510034512003640c446800c3c89a00aa01041c184a02c041400070084046840c5200d100a00201e4840803a0303284240116040904500000741c140182d6030440c28154101900c45070445a5541140c40340e0506401100ca11f95408404151100d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 195216384 1250 195215134 195215159
    0x30801150302030601080c0702040618020a021b01020a0b0417030a020406030b010c0b01051e0904081e25061b0206011401080114091003140c100804240605040e010f06 73
    0x14072040c0c654446c240c4400300b0030480e58108030390032a0321035107410010440010540307070b880c102c0b880c26101503210440020040d080019421030100241c0148498854681c0d002401e1100c0c41d400c0345184d0b05030344481c240214044030300b00035240c3c0410000700340001e002c4035030b00601c1150b6031035070708005010061004482d1180182405406500718100500140c42c0159860301c080800050344215515828041544030354101c0e400e0300c25001c00318034000c111070505000308001211400161819590740c0451608540c1150820001d000c41c507000700c01c000301ca6000c941074429400140251410070080250758110900400100c0c40f5410114011540a07000040c142c0d14852668404004410180207030700b40c004014a400325041c0c0c4000010640c128424881d2102402c06030198101d40014031a1108040307144038204840340f001c11010641007410300c42c00c01c0c1c400000380110b000c6981d148015041070b800040d4807514000410072120307415070002007440c441d80402d0180d203a0f41c03000c00464 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 195217634 1250 195216384 195216391
    0x18141911160f121701091d15040302190302030a0518030a05100c050705060c0a031d010509120c030a031e0e010501090501080708280f1a0108010204060906051305090403080115030203 80
    0x204c1d081c2c2005002000a0360031414801c0754881e03803c504030050780003192501003460b0702c800080ca17102e41840b0a1503414054982120801483c14100c80469a0004d641e8810325425804100d4049103620359901001d1000502520080032580c0c440018101143c81d00d005158606d221440c0c00080702416009400382d840f8142c0120250921341e440d0500380d02a0390107000d541040640c1d4050310f0b00c551405002e842e0035000400000945403610358091840c001c040c00341c0244025040c032a04007048400012240030f00c91501d4041000703e48809040742c5a0b640000c0c0100540c10320800c1c061401055108074100c6242a90074031260760f07036840f407039110100b07400b51010a07001088a4840d60b200c1c9020f013205101885600c1540c0d5030b0030b80340c40090404490045404d10200071b01d40071011b241c401c41d00e014102c0c01c8002c6107014686a4060030707084580c8075a009000010680d04e03407181000c01490014000a000c40065150a1400602d01c4100b40034000c0350307208903100107a01520910980e80b1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 195218884 1250 195217634 195217667
    0x20d1710050409050a02090f07090503030711010e0d05010c0e030c0a0501050702010c0f060c05030105040506040c08181e06100b0a0c11031618141911160f12 69
    0x48034107110601000d4032401000341d4061107117030001001a00d903282414400c403c141030b01716490030720360300080c1003540aa1046220340d005000f680d003c50844002e03020015405d00b00b018540301c0940101d04500b000c8000503256510300407044001c550840b109031001c070000c900742c0748090000802c1080000c00c2e4040d00b4001a01489104019401307923101075074050282c903940300c1d111443e0b610381c0192400c4004c0b400020340c0210041007581810f00800760014400c49090202820f50f241c0140110390007400241201440048034210301010b000c502200c09502802026146c180004141e03911001e82e400c07040c03415020400202e4006040a95598907a9941ca4401c408055114403501038041c2c02c8444e0301d13015147c1581001c5a8088601c0020207482c01c82000f0300110441c8042160341506154450040200811080a51b013500114006000c108d001458130807006079905a4050495900003034044031115000740507445212081e604e10801008411300c1d0703604001c4850340c42c070203403280 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 195220134 1250 195218884 195218911
    0xc020c0901080a060b060f04120201030506090411100c0203030414010f0507170d0e010f06060e031b0d0501140106050309012a23070803060a0602030406021b01090510020d17 76
    0x400113249078210400100c0c00070320307582c2801e0500060442c0e42e40309501c00b105a450803601c0a04558250040a41c07000c41150900c030189071503210000d400e6010516144240c1d0620200402c5c1030080000b0315003981c01508603500c2d10b449829083c904503000c0100c0303010903a07082c052a2000c1c0700d8821105520f45c00002c008500418005c2e040303140d00414072045115454040e50380084400f4402c0c01400c4403040c0c00414603601c0e000005c0c4c80c00d100829403034000d811110b901d032003190400e00074090141d010b890343c012001403412f00d54010142441c5110010065070000541e0030b5100300a140510845802089103a022103175480300c58114100c103048041e94500504140c1b400360000c5442c901c00300f900e0381d000f149200b41d4a001680080d4089030140d001000340034060400f01000c90190403140011840c0c40d090240281d41ca8000200d16111800300480102e080d9100d540000300800b00030700100400342c0c00840194840b0803a49030b2a000a80202c00301030708800c00f148032030140c1241c18940 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 195221384 1250 195220134 195220153
    0x3030304051c0504090504050606010905060c25030804181505010c08030405010f110a030f020f0f1b100f0e0105010b0316030e0d05070c1413020c0a050f010c020c090108 74
    0x214250a1030307000b030400b03000083c0b0002920388094021144101c0c40340c8007034445807611800242a48c4469040705020344014411443c00d5800080c05032042c1da03c051204120422481c05501c88061582000782a5078012500190302c01c4442403401600349118014414480300000141c0c004030b1701d108150004845070b180340042500080115003086c0210004162025005c8000064400c2c04050440301c0f1000654602215032600c40d4503462901600e080d0300e4141148100191130041000d01800c2000c00071f0b65203e00c0000c0412038610a001a090b034414581102d0b4801c000c0011941c9884001d0400c2c0241481010610400c3e0580d00d040e003a03d0300f1030722075400f140350f00590b2800c09800d02d680c8600241c11240704000d03800085d10789030b44042c0e68012900e03024950f00400d40c40100d140d80702480442c0f49903116540504001c102c2c1e6801a1501185800d1900e001141c0101610a02409210080351481900040b01c0c00c05c03283c01f110b0320300d0380610030310160310b1091050020355000801034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 195222634 1250 195221384 195221413
    0x10c080106050c0606010f020c030f06010611030f0f09130f150b07020102150c0c06010b092713020d020d03030f1b140310030203070e10090506011709070b071505060303030405 77
    0x25445407c924411228112101d5003c40c1c540100d0451800c07541c0d000f04010082c841e4070005480358110384a01850500001e0001c0ca4454014542c120301c42d40000704002e846070319290304240c0349c180c507148140030082010f4003000c010f110b04000c031a00d5603070014002c5606d114100c00c03110000d81c103900501900c0340100c0e00306a03a0a0142a034613041400700300c0e008211004100d40c81c00f82109615084c0c3d912590004c00140d0210554240e8840c031446e12140d50b01c44000e40d500340d01c00b48240c030f41c0104103d0380c0f0004d0080a0f00c80c2c0029030107201c6002036807d041c2d050b401030403402d01c5520104900142c041c19000c1e6a00c0b0750740854000b0700148400112080d11102541d08500805103001c0540c0c0c481e8002400c041c07468001c1c50b075203502d01c000c10542c5040035420301c0060801c1075080202e0f08210340001c0c09501b294060100d004c1d0403c020131002181048100c0080c04107c84044c0c84070028a0300710a07816050240b440c4d4103003004042840d525000c41180d0003250700c0780061100300c4c80340c1072 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 195223884 1250 195222634 195222647
    0x1110050c0c07060201020d0c1704110627031005060310090203070509130303060509040f032708031e130527100306050f010605030114150c010c080106050c060601 71
    0x4041610002801880c901c02010810040034100c1c1e03400160300e40d031545040d042250012074001007042002c04042038010f9620a142c2c0d00580c10072101501000d14001180c198401c6914101180400100390700d9404120340507091281021030035907880340d0504d2501c03015110151130507945600090003940701d10401c3d5000d055114400f40c02d80348950750768000030300b442c80d04840385109031801429482c00c00d541445a50007030001150040f0700f505007902c030101c46410094000703050110649841c0d9482c00e6507510f0110000c4d1002490140030340356500c26440b900b10f05890851407404c098000c01810184042c0c0e6000c030b0f0450b421820130f0b40341c4403c10201d003481d124001b10446d01400380381d544918205100e8802c401d40011081c0740d615502d0300c0c0c412580000e1800d060b00302c030030006201095119080764110b550105201015940303120000e01d401c0002e003030303282103900002a81c8000e0107040d048a120140b05440780b51190303070b840000742e806100d100b00d11003154000034000341e00c2e58042c20 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 195225134 1250 195223884 195223891
    0x429070c1d1012020d020301180c1e05040b011b150e0c0f011b05120316030218040b040605120a0b0f04031b06020d0e010e070b070201091211131407111005 68
    0x5c2c08040c16a045801190840d82440c03414120500e0000003042402024100e09008000c070301e9145065452048110070003c0450103090300c80c5807180c5a03a01d20ba8450002c04010304500390718044030540900d0541045411a40c001c1032241c28100198031035080815130f0b68040030080c08104004681000444000705405414401c2403824407080340400d502b00405c00c0c0b00d005020f0301503600d043c085103200d507608403403d4a800b014010001e0142c0351703500200990225005550201d080000d03600054083d0800c1d07000660440d000b8100d0030700b001000542103983c5d90196092035425158001c880b8800c2e0070464000c0d0106880c240c160b2070138820300070482d020b603000302070042c00c151946120a00765580c1070704100c9140c1d1079a142c6010712a0900c40b00340140368010380c0034905199030f80064180542d91040450100304000c5000510090860207000010000d003042110760700c40703c82900034164124120000703a49180050040c070f000305103d44011510100401c801c0400040d540064980103 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 195226384 1250 195225134 195225139
    0x5010b06041406280203180406060c060e1e100b010906020307080309011d011b020318090a02070f120810030201090b03070905030304090209030c0f060429070c1d101202 74
    0x4c2c0d00907600b0001e400d507001c40c0009560302450391041c2108461080301c240455451140703203041403c2010582000c403c0104035030001000c1880c4018048440c10f1207070301250328451001980800c00070410105c4c880990391444071041204442c000c00454489149010b2080943c4c010010000030448060186510200a50012800700c440d41303092408420010103084a9a449250b1461070000c103101070000b070303412032000b50701348221002400d4030350040c0c5040038081c8070385c6400300d01c402d02a501101c0280d038010501c071030442d00501c1c1503040c44c2890441d00340001c0144000c540781c80c1c50754010500303d0b90160340b804504d1f81090401c02055002a21031030038002500c5001a00391014400b8100038a011000142c83d8820113088c54100300301000c1c1544031b003841201c111441d6031b0310801d841c2a01c502100310714004401c2500c0058011068140361841400880c09100f0010000d40032030036501d0f408002c00c825a03003c01100c9a0a00a03107a407a0004031000c001d100c40560700d021280c09a000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 195227634 1250 195226384 195226417
    0x603070302010c050705190305060912160807020411040f06020303070507140f0708101802030a2402030a0603030e01020c01090302010e01050f03011502010b01050a08010306050712140405010b06041406 88
    0x21b80c00060060300c500e87d0703855440344c581d00e02082800000d000c255071101b0841c01425000c0500c10b410090380c03140d00c5011110860120198090104041c25200780305c1c1c0c003400800004120380003000752600036100e8244c2c0000444000b01300940f000c000d5a00132405a00c4083c213184407640d80300010111034244201d17510a0408000c0410410030050000f0402c0b18080e010100032a210082990038007408600c040c036410800c4001600c0005400101c913030400e90b114070460f00e0031903000740b00500099158210b40044188040003041e23510100803284039480d1100d0f1800d0f50300040e070715260b10801d02800720b41220720070000b55001e604400500201490f005103413680032410000c20360001c0c0c10105e94207104600c035050b07c4d5024810140c5c0e11314242021410070700102d200034018001404024440383d00c07000402c0803240224076507001c102d0550820b0213045d50f00c83d0310006034842210259000d60130140c044232542408001c882c04d490004c0d44089444140c60b00b8071845070710015544008421 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 195228884 1250 195227634 195227639
    0x50a0c061107060c0801060906020715020c090a02090906010c020603060d030306050d060207142d03040b0711090a0b1e060c0a0506040c050108010b030105040f141009060801050603070302010c0507 86
    0x10100080044503c220400510240d421000600000050b088481480190711080c0003490300010604226503081401c5e83d0489500c040480c00c0040500e207154101c84064248214180250050405000242d42e001e40b80c0e511100111080b80d07100760301030340280d820804100141080c2d410030b00320902a05001c2110b6a4450108500411a0700262041e40d03000c0b4108080003441928010190040300c001c0c110141d440c030315140003484a10480e060b034601084080035040d021300c1924000c190004c0d81c141c980011341082c04000100c1c88510b0702c0394401800080c502c8074548622502148060401894240346140004a0160120075180c1c00308003801008001503081044901d09441403014007420b003080d1400520014960700b109040c84004001030141191a40680381115422a000700f503407454103900f00d00800390400f03660602440e400801c01a03030800d81f40d0104880c1c0c4994100083c40d501d10607a800c0b03500554100d94107030400c81c02003025610401c64182294001c100350f586013903 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 195230134 1250 195228884 195228911
    0x5070201020f060c04170105060f1003060b1308151501030903021f0e0d020303040f061802040e030306010e031204060f17040308160c0f1209080105010f0f0f06050a0c06 74
    0x42c0f040714182d15420001405004040340352190300c01900005009011320b00300840080c1c05101140052340c0140c541042001102e48250031020003042c0380d020703a550b6250315900704d12110840d802810420300c141c030100303082120503c50840c420b901d040700900d00320900000440107060081001da045102e24059001800e401640c0c2d0105000c52000024014040400c40c50501c019128080c0564109008100102d009c10040c06500c540c401c0c00042d210300c4012000d0800e03a61010041d40040c5000003243c0700b01c0000000314016031090300c1d0766603514002000c1669810503038003101c490342d1082c40100074080c040e00b000c0c040130440703050a8603140306142d031002d04264210340590010300608123000101c80f200b6441d6501c07070520b01c0c0051a20300e0076214600503000011000341104100101c00b80154811100300001c0c1403510b009210384c0d43d4810550198160234028001c90100c590300002d1310741c8903050014200c65007529080d040840b1040107503064a0030203429145282c440c01c00c0b1301d414 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 195231384 1250 195230134 195230143
    0x21005010f03030306050603070c0b1012030206040506010b07020315070201020403140106150e0306071d0d0b040506161e090e280c0203090409052d1b0f0105070201020f 74
    0x24003402110410711032640c2401401d0303e516030710840c0509404c10901c200c5c9030b0f200395428200e5400844981850726105544807002d2210b070b1100d442c980e80501d2170310406501249150003980510210346650340c070b84070115030768842c0ea0402035050788003c8001813000e00c0b9034032141d800f008500005003056625280d80c00394207010414108542d64451081c01030500c2510100395942403407410101c81d004010101c0d0f9500360180407503090000c844042c0084e20140002d004e030540300940701381318440003860309243d86541603078102e170785008850002c0c61414071261450a040b490350340300c003c411a0f186003c2c4002074002e0b42c480410142ca2001f1641e400b203030700028003c036543c0c82d00124400707040b0381c08a5515184841011304a0030044100c401c00d60020179202407582c21500060600c200340f03000c1e450004266445010013000c10343c05e2241c1c0c4c04a104152012036210203580c81c1c0781d04036080118001601404a60200d4202d246241d65440b0300701924950340b060044070700419000040c5843c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 195232634 1250 195231384 195231389
    0x3050703081e0301060c080702041d01020a0206360705040204030305220303020606130902310605012a0506010b0c100e03090105030c04030c09091a0405100c02100501 73
    0x210001801000400b09048400d0040c10805026400c55040a81c0144424503a98001d4242e01022844c030007595110347c082a1a20001551004a00d150800c6240130350411038100d40503004103c00205d640c00110300315501183c843d403d000c0c10321030400d00310642c0c0142c4804004c861140721004111901c072440104043c0d40213071507a6845450105545450700c641803600303c8683c14844007000000d400007506504a031f4215200c54144496001c00d0008041c2c56a000e036008100350b0303540582c445001c01740c00301403e002613001401110b149402c0141d564510800d80040c1380a00c0d2998003e088581c0c0e0940c02c846d081041140da0391544840340b40c840300303800034035803800005088404504100200a4681c64002081c03008500e03404041c0d8a0340200d04000d03060020000000726130441c03440481d0013030740e40503100c881c01c1622110000020022000b04807112011503555042c001500c08805104135030040090000070051003141d401745c884041d1b90400c0d407240702041000560a402a14007 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 195233884 1250 195232634 195232643
    0x302030d090c0e07020a030804030503061306090905070b0f0d021810021615020601120201090e0a0f052202010e13060608040506070e130e10050114090703060513090c03050703 77
    0x144a04000f5005514107003c0c103800250350256511000082c1c0040340c10b54003a0700343c10400d80b2a0790354070119068400f841c10023a8040e26001001c9003100d080d52108001d180200201d60405455107921034040c41740000b00140d40b181400800300390f40007500180400200f0b0a80c10701080c203c0781c082903007406034060420150700302510401d182141c0708043c00040640c5000c222401c0c2600d02c0203174a404040c0282444001a8940c0c8c07030540e402100580000d0207a07a64044251804406010060441c1502080d5241c1440f0205000005110b04050200b111884001e841d0207154010b440c60041c00c0801a0403d41588943e082200940714801c0101101e1300c6091440c9020f103025130420a004000e0380c184400079910249a48a885c0c1c1c9580724040c4500c0013402d07504400200703144c4160044024206402d2038000310b000c8080a00181e1001c1d42038840c0d500301e4440d680c09a0599420703005940d0452000c5c205094940455000240a58010742d904000d0607102d440d86410030445070815078 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 195235134 1250 195233884 195233903
    0x301020d020d05150105030c0414030c100f0206060f0a060c030c0b0703060602010b0604080a3309260a030f0902211506030303040312021204030f02101107020405040302030d09 77
    0x901d2002c020b4040004813000d2a14030300d1842c2c00f1000c010b06009500401800b40006e62043c8096103003000fa8a100701001401c0148003110100c0c01003a80b1310342602a401801424040341e180c2c1000d03040501040e2005052280360780c00c2000480c0c001d00704c60815020002c06417046004141034401150040100340e6000ca8030341d05084010f0b09652034894410300850041104214843d004666a99050746c0240001140e0031403951003003020200c0321003280c0b60402c240c40180440c405500c8141000c2c410039081e180280050134801000c0c2058040201c096410040042c2d454800e5020402a40342c001d00080e0344955600418504400311075042001c001401e50400c03000420415107124007110f00401c9001d02c2c2c0040030945a02001e007004084c8004485500308026480c0c042d600042c1c61000c884803a407429003001021101d40c10788074805409901240c00b600c040f180200310301da152150010346082c00b203909101c02028000d00590442c0000c3c040e416514a29010f0503410500515009 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 195236384 1250 195235134 195235141
    0x7020a06060902090f0f06120c0d020d1b1701170f070b0909010b031003021e120a02040e010e1f1104060305103005070f0b04080111041a0304020301020d020d05 70
    0x2280480045c116180b107078090b1400c081c160356481c0e08540d42c0c00c42c541e0b450000b644070014119954020070062082150000c42c20900b0700b88030703510003c800e0010000c1c81070114901502a41c0e042903041c99800104941401800002501ca00700141005d0050031034080c035400c6031105080030748a41042e40061000146d0f00400c0c94021440c5002d0032804020601e07504081040c1e41a6070354601c0004e0181070a010103104465001029110380ca9025082601c4c120540c2101078803100e40700b00032445107140040b441c002800500ca078148107094040205468441204246c00d414920801c240b003031900e50306a01100140c0b4009800185101c0d1800b00b110f042200d0070040250b1103800a500131605c0146096450000d07650142603c582105c0100030803c1c0b600313055041c0300c05600541402c5e413001030000780c4041410003d004407000c0900800c80310240e280d0405080c803823440345207a0110320825840038032500b90010740d0001d1008000501d85412027240006a0300488500d0780346503502e0040 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 195237634 1250 195236384 195236389
    0x6010807090504060320060c07060c03051b0c2e050d0f0c090f0905040b04020103021605030c0d030e0105040b062701090e0d02010c2109060e0618030a08010e07020a0606090209 77
    0x500207606c0c411511030341004d021441d0b10750303540d1840c407a104c104480c0209100a041c0180c084440d802ea27a1400118075140700b4092a13035810021900300e01403407070680e019803500303641c5070001c8840d4650002c106444400e54012500f0790030401e060580d007030344d42510088210540c07140b644070f82030344d454203d41e4515000244e07102e0328159108240301303400c2500b00300001d03041c21501c42d4055424200140c5070840040543c02c2d21080701e000425521001038034030f00c0080001550b10b41014541da00340709009600503403909803442907400a1000229501150b264504040305556618400364078503100103141042002d00c0a080c0d0048801507070720740c080010502c05000d03039045104203000034030900000d0480103160000d6918280c07411525081c440403506101d81001c00320941100061010940300400c7d5070311a07006440e0002065071040b140040582d000c01510507040c41a250743c1002c0e843c10701081741c0c0c468028908011070088101070030004869108480c05011802001a1a103920340103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 195238884 1250 195237634 195237683
    0x81e07151403010312110714040f020c070b04091d190201111c17060a090e0f01111809091002160b07090f0b04120602180d050f150f060108070905040603 67
    0x41b44940b0b0700000d4040c40710819110b101c3d614000147c500051424402041c04003c0c00340741000c0080b4003541b01b0020b65005441e010b841601c034903034000c00c0074000080c4240050100d14460704180d0b046900d12505004082c0311a004c51401030505c12542c007003005480781081c6440c40b035203103081d04801b843c0c100c0d158044010000202140301940c03450400700c002800c000d2a9204494109440b800018503401c81440790003111400607000f4441d46c20303444010541a0400804511440440c40d05100c0915000e24454000c8816101402c07e0107103c24110011758814001e040494104144000028244a6409100e6555a07882c0c0d40024100262652800707281d9115034400c420621050104003a425103400049520460060f6222260384504400405204990703510288210a51081c0500801c40740c2d10007040c042581e00d070f81c2c981c44034231401040540c5d00361a0f507e500300010302030b940903802d416001282410304556150740d03980010140d80d010f8000711520440c0901e425010f810408 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 195240134 1250 195238884 195238907
    0x405130219050403051b190905060f1c2a03050109051b06121008010204150305070c03080f040222020a1103280903020307090501081e07151403010312 66
    0x70b0028074043c51521119603494142120000c41181c05904004594884408402800309021030412940d56640c1c1c15004107021240d05000d00d03242e00d062617180c82e1945000004031806614002800c0c101e85441000c0c0040d1034604101002410030000c00380075400a42000350b100e040081240d584514040c1d06240d030028400300c9011072014819610360b200002d44600210038120840d4995421f16841d1062075240c4c802c1406500c0000c0100390840b40801140c2d40d441c41d500c05209989500c88101d40445051030302400081549010a2010b89820f1801d60040d00040030a441070a541030554030080312840800c0c0020303070005641d500c26800040c401e24441c040701c060f5040103100002003c281122600013140503865500da142d41500800c490000340d6009012501d03160784480b4004003e000a00076a045c03441a9941c00d0781ca00008401294903000801c043e0580324a80700f040c1c107203003504007912020301c0540104c1d41060f080003c00745000f1400380103035400902441102030f01ca00d8521 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 195241384 1250 195240134 195240137
    0xc12040309120f1514010b071b060c0201020d08131205121005030118110105031f031208010b092812111516030f120903091503020408060109050a020405130219 70
    0x10341d00c020184003c3c6060f0445606002d1540e60fa01d0a1502d4003002c0609601202790074400c030b1011407410ba20403091403900e4403c1c4c0856080301150b00050f500030030110b42c001d0302600e9a1021000144410102d81c9166a150030102d040c48030081c50301011200440740349603812240c0f40100710341d180900070092a01c41c4a103002030400b895031183c4036041c4803c104c4605000300080401c07522800340040740c003070b5143c2108070031070152a46001641d010303401c1c415400150490001081c10452a4101e88611074004d08000050a41c60b5280603c01003d080640c2c0b160282940081c08070000403030407107090720070a034442c00c80711108104a6000c403502d5031b04801c0801840010103d83c1c0c030b2043c0590341d40c0c00d801c080d90300b000e0b24481154035080010040c00204d003001e920404054001d0f01190070399810072804404203541e031100300d040740071f1403007442ca880d40440010041039101307501c4240c001d16141409840d00d82c48002248c11900500401c600b12070b0300054a03158200c60b80c1c134901851049 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 195242634 1250 195241384 195241391
    0x80a0810050d021318120203031006030b0906041a03010f14010f030206040b0903030d2406020d021b060702060c030a0807030911060d0b04050a06030b060303030c12040309120f15 78
    0x10b0f4011400740700460103c040c0140d91481442e000e165040c081740961680310388100c00307412110780000c0d1640c2040d600391031040034003940030130024005d0240203640100500090501c1d56440c0030440601a41e01c91808801161118201e0320b49080c0035030030303c0e10814080843c00040021603c56126416071140100c0d150b0983c00b88010b0340c5150444d4100c6964541031912040c1000000382184030303121090345030b14540070046411848084000d007810200e40000d2448540c1c45100f6031300c61400784803200060700b0172a05480801008039080e065920301a05840c20030005501041c5a03034046581203e02ea031005ca00d140c0c94070b070703c40651a8041810728017407002d8030132507585420042042212034401c0074082544440842c040d031048800c90780041060281e828841604170050409002c1515244046000101d147c14004204c0c1c0c0542138003100f50780b41114581241c0c02c00310005d04218100070840800140d1240342400509200d40102458054004030746040d9041c0d05140301ca6201140c207 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 195243884 1250 195242634 195242659
    0x7031406010506041e15030506030d0201110a0f18080a1b05030c0108130c0b1305120312040309090903030f0c021902130b0405010806040314161e080a081005 69
    0x1200011355044510504514031003c0701049014030000143c3c200640a15001001107510b59150708541d009080503002d071008200c1c94030040b4243c500e030044034000300e0350030000e440c01c2520851503582c03920300c6450926440c4240c500130001c000846e42c012980765009540c1d82c4207003d01c070300304041c1201540a1340e9221506d4030300441e4990200070401414030540100040098401c950341c411120ba00801d000225501e440000b800354014031070070b2843c140c034240c021480382030200509802128100045040180b59416041c00d0390000303001310f04000b4402000146403505001c0c000380c4500c01c0e1001b2480701816070078902110701c5855203108560000700104d00c0e188814205c1198250141c03114844402047c0c83c11003c0c22000c00d425030010715000c0001403000021a02d18010f91203640c070518850b41c404922034081c0520208031400000000d80000000ca240800058806030400308039580e60303840e103541d480c54002802d4840858010000c0143d92140c2c1c250002c0604012220500300c0e0a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 195245134 1250 195243884 195243889
    0xe0c031507050a050903030a21090b010e04020301090b0c0d0c1e0305060118090e060601051903020a02151f0807150305040602130803120606040e04030813060608070314060105 77
    0x50800380501c900000c02c070003c940302d02c1c2222025080602241c1d6126007016006140304188644130115042c201007043c0030360b00074000c440c1c0881e0005201340090b402d00c1408503d03500c006d00200e07803666076000c08000081c00d0100d0948500c0b0100c44032030b124605900785505a0300d41d600c0c0001003020789500d541000c50320740c1131013189000ea4640015160f45900059491000100c0134062400c003408000401c9c02c503d03048048000082000d50344036841c0d80005407084c0c010078064100c83c00d042409003648911a0340901141a00d0b413040f164496102070100b002c400059941c080e1090640681804005c0c1c0c0d45920303402441454000e0214524000080064840101d540c0d0b04058807017020030107000203034041d106250b003c03000004000d0368900c0610703969840f0306075111442070700d080011601e2810b034099404560b2075104002e00e03030b50344e075038110340e8a0750042600d125007000c5000000407480c00d200c2d01c00500f00703a20040003040c0c203508002681004c804050f00395940103000500284c3c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 195246384 1250 195245134 195245173
    0x10050a060c0b0a141602010605040e0c060a0c0f0b0a0e060403080622110310140306060103020714011103010602160f03110607120206070912051e01020f0408010e0c03 73
    0x1c58000380c052900b078940b800748002074203140700c1c01888103c00e141440f070640740d85941e42007111000d4000700449981c883c140000c0c1d17180510a820b20b500450a8103906090910090007407542e64508240f0064242d6154a825140030400741e0b02c1790488410010800000e1080c600888a0207004005610f031581e002005004000c14103405180b00c810203080c1c40c503200b14034841d4000520028021071094651482c000d81080741e0440c10305550002c0000c8180d0305c3c0101140400028010700345980e901030040d40650310614049561122585070001450420300c9080308070300400c0b034402d0352949407000003454580b000c1000c009074034098001304101103418081004499101105441010028000070703031501819802814881c2e80411000b80258040b07081440340c00300d03441740030302c142c0c66261609000220900080042c0d01c40120018148020041a50560007060015190255814689215401c19480b0b0709250b9100ca1950780001d1b0103016402000405800030401200a6807100600 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 195247634 1250 195246384 195246407
    0x4150e31060e0a1110020709110c0c1c0b2509060e010311180301140901090b010f0803090111010e010603050a170703021f0b0a0612271e1a10050a06 65
    0xda481d81c04c03840c41c0705d0700a22101000382801311080002a01002005000c0c2d402180800c00b1030041da00303022014540400312086000280340b01c440041051345d188043d9041c054405504103520800c1c00e07a01003020071160b62490059503440d03555515004020380b10390074030720b08681454100b2000068186801050318000c04032044819402a8410301080c01029029041c003402242c11040101c1014150031004010b48035516840719031b070361086621229000c0c1d0042d0f01e1141c10401c4600703002d612808400702c050f10501c0000544010144a050031502740381d00403209034206004441c10310035a0628910990f00c141640c600c0e003182503400035150705885940c2e5140e4024404c81290250460f400421606005071645c01c0d040e80700c1c28068820861900c0c0990410300305404001602690a4192980c980c04d54a81840c214140c3c0da00384101c8405524400c040c8540342c40703102103906d10b038480c2e035060503400d482d1a882c100240c180341c003400940c02c100c1c06101d058004000c0980c0c0130107007404 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 195248884 1250 195247634 195247639
    0x609030703030213030b0c040303020c01020c06042310030b0a09090308040213060905100e150a14030f01060603021b0c090105010e040209040c120b04150e31060e0a11 73
    0x1d41340701c2060040711000f075940000d001840002d0802a02c0b106040003070013a40e00a0302128501904003004a03916680d590030701f13400c54800e20041120700d0743c1d000a200e22200b460b1520f040700e800800810952002ca080c82070000e5101c40c2012070901300040c894000c0c5c101100103010319144c5403000740800c6809800240203060340041c00c0f503030b0740307407540050042e002d54031050010382080703165001d00c0211400713850300f00252500442e0304104018500c2e0710710100580321055040c40c1000000b141d2003c10100c41d0940500308010f2281c030780038403a0501600c555140142c5520030340d9802c04540c21303541307000c2a0952007000c0404003551021185130440c0c0091814040c20f03c41d002c0400d01034090030840136002802d05200300c2c01b498002070b83c00b2081c8160441004095151400c120644034845495400008490024844164040d071580d62083c1035035074210a988454a40e1088140c2c5644200001c00e504590b00c81081403500440e804800071600801c800106505d8007000400311105151 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 195250134 1250 195248884 195248887
    0xb041e0f030f030e09070e1e09041b08010e0d030612020315070e030f28110411070218040611041206020f16050a020a09020a0806040b13060b120702010509031206041b020d09060206090307030302 85
    0x40da0041700c928132f0005040014024030039141d4101399156a0301c2c04400610100741041c07004a00030f0207171582d0b144825001002007002054034403a58158000182100d410004220b4030b0740c07040d0b142084842d41c046011360042550714607040729401442d80b496a400101156240c0d00000304135410201c0c51102011140002d0564a102c13400100f8800e0b80002074005a034804a00709405884c01c00510482c0038800a010360309144031014607512440c001c040355507110814183c042a5142e01074640c440c10034180740d02c0d06004102c1d1042a5101c01e800312144e91140c1d81c200218100600d5090041c04c4004040d810440301000280c8000d0008003400e000366074034203182806542d42000500500d200c62000c200030750300d45480d6100d0f54089021071041c5101200401c0e036007803051143d02d214441481c0598203260307101041d08607241c405440c9540c041e0f16499000c10f04845c100e014994011180c00800400e602003101804001c2c842c0d0142c030541d00440204a80030401004039a009030b03042c81d006 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 195251384 1250 195250134 195250163
    0x190b16050702040c030e010b03070803071e060524030309010e0609031e0c121c080901020d14160e010f0f021002040b041e0f030f030e09070e1e0904 65
    0x8403858060054040d6101381410f54a0072402d8165200c0240000c60500034000c0f00071200515a88101c280b0503490709600402186c800310351020301d03d00032111000054801c03103049803190420380340d094038402041c40481e0803001c0b81500c00d400724240c1038400d03030280d03043c03806070400a04a440b02101d0280240b100040c80165603600344403e103050300c010050302d140302201040c01a0380f440c0100c880340c0a219100030610200303400085c4002e00785140c812040e0076421029040340c20341c101a02c11510b66409012142e11104507000311041c1d10082c0000507424a01400902032120300b14503a80b0901100581c0142d00ea40d100c051001002401c2c1088a0a4602158100d14085c0c28405a1184030320110f00032491422000c028001c80303202440c0e40c20030700c4007200c0c0da481440f460f01c111401110903c10800026079260302c0300c079416009081950904500e01702159128408680c07030300008614590b299541e117001048640c030001c0320071440e02c003034400c0408203041090252001d0600042d140d400c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 195252634 1250 195251384 195251387
    0xa0b0603071b0f1214040e0606091206280b01020721020a0f050a0e07020303071214190e0a110925020109061d1504020f040608030903190b16 62
    0x281c026a6400f4042140098040c2003c02d81c0c082040420000078800c0d145450200d480e00c0309940680d040c84001d01019281c1c20100201c0350f026014071134001c940f02c192800a50740038040a4815080540314107030b400c0b000c0030107984504080004440e018640458003100e82d9001582d0380c1a04d401002c0c403c0300c040c40305080130f500000100000d41c4518a40004603107001c15031254001c844080c0c030035040c47d503103170b01d9400079009040300c0c10340050740284001003103284155100d0600741070304207001411289803c00c0c0314070b01d071003100c0e07a07076040c1c0400341d0f0b6101c424030911403003924141450242500546c2d5030740e0700842d0100402d106100e0716020021906040c003000c1c1002d42100078440c84026650602c6000c1e001c1c00d00b400302a82c045203843e0042d2420510a0f0484c041c0c00c105c08080c00e100c1c809003c811809180152059802082030402c690864940f031190401424951001f543c403039140307a0401d4038001884840303507034642d0010411780001d43c540341d50a4121551000c52040507042190 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 195253884 1250 195252634 195252677
    0xa0f03051f1d0705040510080a030f03090c0b07020a08010c0c0803061503090f0f070b03060112110307020705031209010c0b0c070f060501030212070b1e0408100507080a0b060307 78
    0x1688184082c21010505110740c00084050464100740c2d8103000540d56510306401c9805148100b1080781c01408540b00064810180700a1410a41c18001904080d0391075400c2c2c41a0260007034052540000754060075440e006076160020a0143e0081c813039041c07132001c0204805508500100f05a0002c0007044160f070342c540142c40c410f45060051500c9141c031003411552158603581400541c0200c0c1208c03e078221000c03c4450507281c07580310b4145962034075001101c04400312000c0c0341c00603981d07881030845642c90000650164101d80e00030001e00e401c01e000c2506000040c0d0301c3d82c803408000c01001c0226604030700000d402c0c907003150131140c580e50b030100101d85074031a0460040012030f00c40c0c0507900f00720860340700a040e03078020b841c0c4c0040d202c084903146548003228011116907a900b072140c00054940a1001c40c00a0002800c00d4140351f0f40385101403601042c80f0102d0000c1307403154108040c040c0e00404056000e5003028040c00302c1d04c000c0c00032030840c1c800500050200700c2100071032011000d0010 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 195255134 1250 195253884 195253901
    0x6050f09030f160b2a03071a010501020d050c0604110d0f0f14060f060609040b1906030c0f05070206300105011d060301090504022106060a0f03051f 65
    0x909841080350303041c0756a0749640303280060380034071140c011002c102840f403142518042c0c0c0e40b2009a500e85c0041c0d0484c00403110b403002c545190791004005080000e01002d18003010715203010852240340d410013001a040850565285040000070300c81c02400c0100004d229400c140c01100c141c6c014400003002c10032100845501070002100151000c040015008251845038060120640c1210001c0b03080ba40f900015505c1450148604000c40d62500d0a88000e080c01d1034001c1c00001c45801480108610320300d40e4160f5801000071900800200b9090b00489081120718509059800c15111000e401d80c000c6845c0a0b0040b003010075001541414060300c80c12014002860355910400b00710301407400c007000d0107810300194407080c0c03009654071050149001c0f0340c001091942540e01b0101d11400816008206a0b40300d036150307010602601103601c942c0071550031040a010645402010300c249680c881d8007641d05820300e00b1040012441c00710b091020b91425462075810400f064403008050310445 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 195256384 1250 195255134 195255139
    0xb0d0f02060703020a12080115030b030303040605100812131d070c05030d051611030a27120f030f051306030209030c0a0b0d05060904020607150f09030c0317070906050f09 75
    0x6040606c0c2d100d8110300320ba030480311b50401d00316195804030b004030240c4844010440d01a442800410300213031450300840c3e40084286c14045a13160780b500618502144511940d42c1d6032170000700500321241090400000c2d0840d0341709c1e0040180c0c0d12200b4164140024100300c200041c0354068010064148100d807108042d00302c041c48a414514860442208403404810101e0308905103003884107008030507182c68a00580301c0c001090310820340e60102c10080c1c10803400d01c0b0b006c1d20b0041360481290500c240f03014020360990100061929015080040409122040c84414489140300410201600041d1402840c000da00c0e1000307000440c0c54000720305801030340010b0b011801302d0080e5450001c2c2c0500c09801009008070f40305c000a00c44804030545007c1e400c240208007142c04508240c44031440c0c1404000b002425224594441c4105c46900004070001f03406030070303014281a440b40c2404083e00c0184110302c0c41d402c0c1044050400007092096105000002c2450004074400909640310040301 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 195257634 1250 195256384 195256403
    0x30c0501050c01090203070e091e0d0e06090405041a010b090d020111190303052403070302040c12020c070303120b0a06030509030c011103010504150b16020d0f060b040b0d0f02060703020a 82
    0x540d22380312460305e0203c0d40210180300d02c03070390365041c41000340c06000001e006074080d201c0d60b80450421206864201c080301d40004c4104040c0c012501c0328441c20384144c1c05581c20031018041c2070000068010183e101142e000d40c2401a8205a92444080b5209581c2420110b0508180d80d1007035080c05100c40103481400000c60000d418180c054000324800c0d1160501c9d0385132107021840f0b80c0c0c016448160b00c6500b6074808142031005082c540d000d085019100d040041c4040400600c0c6400c0e0381c840e240102c01500035510800c101038201c105034920b02c280c0e5a007031001e000500040741d082601440b035941096280c201040e9605001d008503804201000c00034071014400340c0d00f12006030b000303101e0940540e140440007540e44013a80c035120155246455090702c0d021900040d42c0301e010000340705917230108156030004005030402c100c0c02c0040b8410760010801c0d02e02002000104c1c1c5011000c94001c058110a0100240100c0804e00c800380d811505580c40340c446007030480c500403816000400a401c0d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 195258884 1250 195257634 195257639
    0xb0907030507021606082a130603050c18090a18030302031501211512050c040507030b060708030c1902070e400602190801050901030c0501050c0109020307 68
    0x28160006031140030700f80c00300d075184031003d070703144680c0c009a00c20f940008074500042aa00081c0060300100c0c0c030600e02500400800b0100065540e43c000356038101d074001400010001a50140215a405400c540c00a41850528158502580c0b10301c0c030164801c103400c40000314844030030317802010b282001c1031008150000a1030050002e41c402c1c2d412151801c503207144410b080d8072402d041561000d120250070500c02c00300b00d260018140700c0000c505943d00d804400324040054803500b001c0700e8012401861000b01030030030310044810107080001054200a81c50005031508822541169480b04209613a0fa641c030f040010103024100c0503a22008128420003011940081c981e000e50394a0740000006450b100404500c200c102600302c0e03030080391512105840c50099a1400d4201c40d4140310408408040e0b0300c8000b268000d01420780001c010314100941c46901c10b4a031400f40c0b600b0340da8101254111344030b501e4046c20507c100b80c100140081c0d00141560290441c0d100903501030b0880340b02c0d54 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 195260134 1250 195258884 195258887
    0x603070c060915090b010b04080309011209080a030204090513050d0f09030213061d040b040209130b0a06170f0303040b1b0307020a02101b0b0a06031e050c03060c04050906040b0907 79
    0x101c0030001740c078050180000482d0283c4568210360440d99414011842c0c00e04000041d203a01801c000200070140d65100284049000e50700103124020907940c1c0140d5941c10a100c0c00e0445001900a1402d482c401c08a4000980c002038a841c44112606011810034000d50040b1940c00d150f40000b03400510020480e00b4000380d50f006001551151640300b520344981d03400e042c400580481c1c010b0401c110314404a0007505152585a40103c1d8640c81c1010040050701c54040c40a070656200751603540d00e100400c40703410b01041205e9403e50b0b490103481c580c001000a41e03501c0c000600050712081e5800e020500c519200d907815100040300f0030510b51241303403442e4081d49405010b07005078003030160428030f1380c0064400d280000602c0400402d4400300140b41e00c5042004500600014403240d407a20040003141c14030b0701c5801a0240100541c3c014403841c07400e5402c05a00c00320300c40c000d0f402007091150409103202a00d01342c600030780b05c00c0c41d59a1500001005071007240c1c0010b400c020b0300b80500132002d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 195261384 1250 195260134 195260141
    0xf0a05070e0f0c030408091302030f090c060702150f0403050a1103060a14070f030f090501053c0a091502030a062c0a0e012a0504050603070c060915 65
    0x880c15620901d00319a507440c4060001c0e101160020301a0804100060018002c1c00c00b420748400040d152282c0320f500d0710f21040032a4802c0e00c66582d07909444080200c8001300300460078070080265111424049036601240703500c0021040c584600c940841e0381e03502d004500f81914020b5410100301c44060800f8101840e41007060000340d400b034018040081e1b480b03100b038060641d001040300303c03050046c1c0c0d409900311028130045180d5001c140c1c503900c43c0b1030a6002401000040c602650001640303003001e559030020142c844a564100c480f22072a0380002030b0720f0354020a081d1080c0305104096031756421800c002020355590041032010141c800085401269000e184104410b1034200142900da4150710b8840f01d00407042100d10120100d2001404000c0c0b44054020014002c04620174220300e0500c0d013556011440800a042070403200541114424141c1d084080c4500301649018180000b01d2140d20004104070203120140c018002000015880450440e4102542c484084035020908025 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 195262634 1250 195261384 195261389
    0x50a0b0405010e0d0c020d0516080c0a0509090a021e040c050a18230d050f0d0206070c0308010b07030203071a01090b04020313020409051203011409181005090f0a0507 73
    0x8961818001070002000000e2801d01300d40e442c3c40e07610301c1505a07402c05c118108005012540341c040c02c04080041d8030151240f00107080500701414042c1010000d21030b40c1e4219501841c843d00e402c40a1045a24001c140103241c81d4054807604681a48840a503031541d49014900d50000c0c60040c03541c030000d601c14042c00380404159a0031000d003440c40760540d41401c7c3ca00401028003e16800110040700c0c142114102d810080d001d004040b405484881c204030080d64003060541000740c071090220741c140017240d840001401e00c048003d5140d18024088581401a4900218001109010705000708207580360203a01131040982d03030018100c0789046d04401c1c45050702490038180b0302815842d050090380c1c428228a0014501c9844940822001c0c0a0b1084203661078024604480612034880f002140070307145400c0d1480d148500d02d4180402258003e01d145100000d0310020f40242002040c02003d40c0004040400c030b0781c817205001410405a0f0400c2d103414031662014004101012401c1e004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 195263884 1250 195262634 195262643
    0x304050901050d0506070809070b040b030a060f0e060607030519020d0801050d03050d05100b0703030b1801140d050f0a0c050306010603180620161103010e031213050a0b04 75
    0x582d03a00da05119040c4016240100345403c080d0008400b18418200c150344410403030200e038521a40c0d400100e0031540700360401c0400c60400003c025581d0000d0041d00002e144d030303200c101e4800385802910301e041e080240c501803003490000764407400d15109a081e20440d0701c0d1050507124280d001e09004e9a00d100a80801c170200f50304c4000022039140c03800c080c880464241d210540781c03106e46040348004003c020590a03800c00c0c00c8102003105e105032800b41c180c035813094500007551600c502c00c2243c402d1030f8221007203421408400501400f80c0c100e1485c124900b007500c1e600c20003c0649060b41c20500f1030012505148036842e000014080302c450460308484068050b5001662540d000710196410703001400300082603029800b00007030f007507801442d6040b9206031007032031001418a108030544c040301641c005800180e400e0414000c0c00030203030700e802d1300c110f00070411042c5615040c0d0312400754030409405c1d13400394400100300383c107108114035405034014243d4440404a24150041c00030648060700c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 195265134 1250 195263884 195263899
    0xc230102090f040b0d0b180304030804080709061203080403090e0a020d0f090b0c0a0302190302030702010f05040308070e03010e060106020109051b22380102061009090f0f0302030405 80
    0x144282480d00c2100d4035100d010b0445055081300e501c03110306c038840250030040c03500440d42402c00c03c1c84042c00500b000c1c41c4036100c00c076500c81c0f0309080f1070b140c10131a4000410b01c2e4640030b402c004c0385140c00080c40000b80d00d414848a542d079582429030300703030005900c4440122555420045545141c0d80101808007101d402001001d003000e6950b0112400c6100040618140002040d9402560400f5008418a9103005407074402d040c443d440c50717500c1d0b80e5660000b181d00402440509034081c01803402c14084c411042109190a8400600d00306002e001e54062043c01001405151404c1d0003000401c1e04c40d40403600c00b540c1d00c4800a000702190203054603c0e0080c1d070410381e0221800d080e282c41904005104a45014105028826a00d2f00d40084030f40a6984d000c0509041900c40c05a086000c03071100807411900c15000c0390001403d03032148130f41150041c074100a151038000c02c103901540d44032403000a0360405840c015007911078040b400350080f0b5940340f049040580c001300030020b440c0243c6450 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 195266384 1250 195265134 195265159
    0x120d02011103061005090d05012a0305101514070503030103030318051522031106221101020c1809010c08010305030a030504033506090c07030c23010209 67
    0x1c4403240801c1d20410b5004500301e40100c00d00e84200d02034918a0001040030840e003580d540c60600b1600303501055424000384403d00ba41c0254203100034412010235003400d002600d007004042111006500a201000c0140e01d42e900626201b46d01160001082c4014507030303500c1c0641081c9503650402d01c402ca00090500c0b0140c601e4950b40141092ba20754810018042080404d5188089240c001c01410f80c000000002071894481241c5040a650180c2c039403501145d40d03605440e091002c024030b0348460008141308540701c00d9681c0c4203104129000104010031400071030040f8117003120080c4d56603021b11003400051020308503415990080102c10000c014008507014244c40c1d0003024170015025400c144401c502080c0a070304000d51191280c50100c550a488140c1803a0034208580030140d4000da940071000a440303078420701030700004201d6081001c0c1c5400e2891441922844500804220100d1458001c00c0300304120308071004504165900c034403c400b4640c40c000d4102da90014405c00a85606 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 195267634 1250 195266384 195266411
    0x7110313080d051c020d090803010b070b15010c1b0308040f090c0903030e0d02190602010207060501122109091a0102060609060622030807050102041e06050d05070e120d0201 76
    0x41364421100c1100500341c2c002001440002501b1208020807620b407100c0365400003d801600071400f822100740101c0d01d407803503410180c002d01e10040c20150030802c42d0101d0403041e03070800c46413043c40b81c0c000111305405511b240c1c0c2002c07103e20b6610041206801050104503052515030f60320580320040c80800811000240c101d810084a10015012074401034240c0c03024100310120b0306081e40084c1a200100d4042c0b40b83c402089071552010005075408103880e0704112281c062030b40140507001c00c840d4800350545a58402d840c1d41c43c0000c4050100c0c040c3c06503200e0041400b00020240807008100746000c071041191030303641c0808000e00501540c0b000990ba4070f4840813003802801c02030070050520b035090741c0030200b1b982e0f00810fa6620200003c00040000c01e664020308481348500c00150300d8600d0300c1499012030021074035100300c60800800501c05154402c0c15030300c590f803108101142580fa10f401c1078844250012403950800da0180310000b0000000441100d006200e0b802008610001102e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 195268884 1250 195267634 195267637
    0xf0118060225061202070807020a0e070923060c150405151e0103080c280b0c0c06060f15070507060f02010903052d03010e16170f07110313080d05 64
    0x8420105001c1c40036650741c4e101e540d000d450054880d224051502c90140c00080861040341e21505c1030a8040c404c000c5010f40c02000c1400800e0500484080d10b071201d007503500210201c15401d800303a0004500c1c070030034101c1004060700198003c40188514141403e0041d16110203511594401e40d030400440c01c08180003504d0b04500c1c00d40d086079440c40e42503680748013640e030080080e440b19100b02c204515102c540c3c0c186140c40004600a940c075035030983c1c1b03410100b00030000e00400801c2414030000d00c0300c00020038a164050003c8548240665142001600113a19442c14a40c8044042030030010040c00003560030a0f40d00b01c1c0c40d010090050030f003080b0300380c5001c0403006001500034060101590f240031100c0015020080042c0c92070405044071182d1504240d0000301c0350040441440461a6503005140040440b8907014521001d2401d0748410200c1c00340c42100007a105c1c2c400904464490307141481606015401c1da035131040e00c19101038984426004084403805403c080f500302c0da02500 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 195270134 1250 195268884 195268889
    0x30914030a18051008180d18120215160f080307020601080106050f0103020f0906160b06030703020108160e03010515030115032a1806080d031104050f0118060225 71
    0xa14841c4c000ca00d2500c00c451511001d8103405400000310070860b40c1540c180304034500b000c80c0c1d1340c0c0c48100c5481640444940001a88042c514403041d0249070050780301d5810042d141500180425070320065424150a600c1a003075000d0621140900f0a0381081620401140650b80c203078200e8003ea46c0324a01c071030803601d0b144121503014141024010965001e90080c0882e1165000703064207050352040441c145174005e20b21144210040740d55201080303c3d01140c185c20000940003042500d0560380081c10014015001e000c1e0f01c245150010a440d1092443c800208405030003400315040180310540d80060300312100303202e0350070691241d5524280b14442c0086070f030008082c11490010700858803819200301c030780d8404000b4040000c01e40784041140c1041c00c03010010000b851a1401c1c200501700714801d9848002c140c01c1c040e54000500d043c0c4261810780b1030445007498901d01100050f21031819a844e20100a030710048001499034003c14030000e04070750f040b08082c07030101600884d4944441070 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 195271384 1250 195270134 195270139
    0xf0c080406050703080f220206070b010305030405010f050c03030613020705010c05090a080a0819090e1e0f04020d03030e010902041404030921030c0206040302040f0e120f07080703030914030a1805 86
    0x7d5205204001005800d44e440e14001742c403140ca451015110401a200e0903081034949910014003000740e540e01070904458011240f0380181000540b114081e160310000c1c01442c85000141b149117062803141d0704440d10300307038420700030420240320400290944d0007820695224503c0c0030303400150b2040204039080c1e80d95026040500d0712a0918110820030702600d600300c100400c0400200700000219a5140584078045511420600c018801d1101c810010b01200000140170113100c0107841d5101c42101469060401041c503a0982c080303180148100d01002c0d5116060040d40d08035158115400c5010300d010365220340080e501c1c0c81e8128030050403204072001c0102c504140c040480c2c420803410920500c0203018510301503881c2c00160070386154041820f600740d643c045082d0565420040b6154a4101c0d5451501301600800c1c540440d00072294040e00395040000c00e0010103119034441c6c1c07540340d4070802000300d1540c403150340d540d247c04c40980310012615100300b011145410111a200b100d100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 195272634 1250 195271384 195271411
    0x9091a0a061d09040521030402040f0603020d0624030c0e060d0b0103060f1b1d010912032a03080a141005060c010e100c140301080601060f0c080406050703080f 70
    0x201d40c14094083c4000b0803d9801d409010443e051207100018011a10301101504603207030f040c180104022070324440f5103403030003520349001040141c8860300c0d054032154104100151000c1c200590900c4000d5942041740c40240b049008010011035124603001c0d01e00309a401d85460782c982c0c081c003108c2c03141c0c1940030b0402d0808100400000380740c3d40040c0500564103102242c10410f0300c1c0d144615140306148480492410f01c40184840000420030340f490340240781c0b002c5034038945854034941244807980034080009881c8610040d043c001c605544a409110707026101c0442400d005108420590f01000f040b400d19104000256040c10300a005140036100c01d60050f203000d0802800c0d80c020329140d034555496070b0300c0d40390000b400d0210242d060424440444c02c28141d4800400191440f100c40d003c41206000500a91500048240c19280181400c043c0c1440c1c100d01602e031804021402000da16001501181d0030b54880040d203010741c825180c00103261204032509002d00b03405c69080b1400c1c00c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 195273884 1250 195272634 195272687
    0x10b03071205030409020f0903060703060e0a0b01030603120908060901090203030d241404060909150b120d020304060f020a030c170d0207081e0301060c020108060109091a0a06 77
    0x895040c0e054051180b01201d19040c4d41c1c4555400740d82041e000940c0300f0740d0101d11001c00d81010701481d58010224942008001d060001d0045003e001401d642c4246946076211600b59010b580810003440d040101780c4802255050003c0c0043d80e0350081003000d0050401250444005001d9814260ba0003000b86041c000c0040720000106200d0300c1841c501c0d805413050002045440040700080c0941000160240b90304109010580350154000c04c0302625101030240401e40d13942010131104e051000102d40320f1000e5000504800d00c803400325109000f520350f000d090680004c000c0044440588407520b00b032500160990700c40c40070b00300c050b01082d580100100003c00b84140440501c04880d03146080a4164007a5000c07a00088022500342d600000c803521240c850175945410010820070307031481c560610344010509940014001d051021501c0412501e0b0700412903c406031940c407a003002402c01c0590f0002c4040c980c088254041d403101600402d5041c4900e0410424200042c190b480d06030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 195275134 1250 195273884 195273899
    0x30a08070501020a200c011d040203090a02040b0307060507110a05061b1603080a03200f12010512030720040e0a030e010302032707050907021005060402120115030f0e0706020609010b0307 82
    0x1030300240c0c231100d1058110440c59580d9940c80a9405070301810000c01c20340b1b08a02c1404210744401081d54401d41c8031440402507075902604481003683c0c400a00c18a2461100205d1250509030b007045510905c00304510841003881101d0303c1001140008a55056610024000c8602c4060101828050302008920032290081d000b902e04c82c060301d90000d201e4403004444007019001040d041d03488150000341031440e401900070b401d014203070486002c0c80c903030301c8080d295640384501e0a00410780b00708103c130740c0f0a01480304100c50100740040e03c01d000307090907240b100762112001e01c002c0700411507070303150303902c1c154424800d881c4140481d1880035420100516140c1da50410303105084000d100d24100442d80e5190300c0b80b0341e80107458580050110200d40341218080d5203000304200e0160748140a000300280d02c0182590442e0100c4030500640d000d01c0800300c014025510740f4901403414041c1ca83c3c109040054802e045441d1942550200d4940c84103660030307900036441c21903150b480786005208a0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 195276384 1250 195275134 195275147
    0x3070509010e06310b04031e02150702031506090a0e031b01020306010906030c080601080c0c0a03021c020715050310080d0305060f0d02030a060b030a08070501020a200c01 75
    0xc0c40141840659104010006002607104004010300c4a070f40781140594002000301c6151031244001e40510620305014884141e0301036840083c0c00e01500e0084440400e09070f410740c9141d540c01920000324041140d812440700d600c803450407406072142c0c0b50a0784441c0d98030740e405e0b030041d00c0c002c0540c841070f1580c245c0d031070141000554540b042d000410000e25400e101040d40d0181036a801c00140c0c41c0d05d4601d00142c1910442e40c400c00030300d4205030a1020380380d0f014038404d501c103500342402c0c00c0b581c0319940d0307412660050302c1c400f001600c516102c20007816000100b440351401c0450f451120b100160604a80341e0740148030308802c003040306800c655048d0280000e075612220310074034402d615681c0c4001a01e091000c841c0e9402103941c94040c044181004000405003030b5084c0c4034122044400e9000c250390780000c01002d001c03559034082989842d039003442415412034010300c8003900c80b801410014000e5022999800105d080ca68008012a592003000050100004050811041c0000046d0b580 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 195277634 1250 195276384 195276397
    0x1060c0c091116260c07060f0e100306030605150607061d1603050601121a040804120c05040501080c0619090909112817010212070c0c050402030606030705 68
    0xca03000c0c490782503107203d0b5015080010740070b00300c01d15004c020045601c0c0c582606800460b5144000c2010b003104010000c2e80380d086803002c4c50008840382076080220f445000e2901142da110303d418014400b1380750302d6000502624000c401c200003a40300d081880140d414003040494200303205009480104001e03901564481c440c084104081c011000c1c60642031040c07081c0b40c03c0308190b80300d5050040c4041001618007401700400500401e206c1030303c1c0d13840440d8484404914031044800041d00300403801081d14002c00b420702c0c2607001804203280400c5080365030301646020b1031a0400000d0246800a1821580440074000c1c0d440d008500030790014400070202e5020610011407030002e07000a02d4440e010f40703070f4010004160118407182c01c0000400806940c0c0e5100190303c2d840894180341180000c04a986108150361040407013241c0a01900600020402c0c0302100b104210f4101e412950400c0c0301c038800c40b140c1c07011540343c5040104a010a5502c16049130081c000105c4060103003004195 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 195278884 1250 195277634 195277661
    0x2030a020d02030f0f240906120106090c0206130209010b030403110a080408011d0c010513080102120702190302030307050c0102070b0c130503071404090c0803041d01060c0c09 77
    0xa0881290715a0701603a2083c0d581c0242c00740321900b003013034030204184440c0d000090080c1078014815514806c0032100e040381c84142c031602403080411181d0340c0f02c81032a00d010034080b00038131000e42e940400d50010300c2c08100f0365025008100000d030400b800301d91615211507000b044d50760542d0902e12880007641004000b1802e0180c40d44102e54107507010030041c0300940c40b40c0c1c42c4075500d5040500540c01c0d1201032000601d41d03049001002c1d00c0040105c0c000880e40805c1c60640e03101c1c088050740b030145003860743c80f070303501d81d48001043e040d421200c00c406072250000750216000444088065848036981d120044c0040e04144003266919108500500c9100544400503080104d6501e400301d1000c0140e800588070707040000c7c83d06441c5e00c441d048030300814040b005071184038130745002c0210101c2c11141d440c0c840d40d503481500007040504040310380035040714000c803501c0d182c0b40d4828000701c040300069100303440b070b442000189691141c1050080680c1c0407805202d26840c040c1000c0203829440c0350b011 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 195280134 1250 195278884 195278887
    0xa061b0501090602070c051c03080a0b06070c0501091203050306091510030903080a0b060409050c1b0d03050123010f030f0c0818150f0604110c0114060103060f050402030a02 76
    0x200411024018206190b020b800d0040e0398001070314001e0b02c0c03841554003082c0992100c00d1411b1281052403021080d06425040002403a0343e100c2900000385041c41c07034113034402d0300031401c0c6040c8001204580d043e1002a250915a55260740400c0c01a0920f0000140001d1080002804504042c1c940a03000300080c405003480003c2d030f00000c0c02d000c0032014810006581d0300e01140030715a119038401c1c1c1003080050108030500601c4040307445403243d0f0040f84c0710180c13a50041440d0340381500403101d141c80146002d4915036021041c20792a440783c00491800a403d0074004103aa400390308074800310240406180040408550054400030f280940f800103140d5a0307a140c003816044c2c4c1c010010b07002055514003405180c103d590a2a90f891061151050391240907144d00685991400a030000c907114082c90540e0f0700c000025000d0041858101c08808002c0340c115030150054000441500123031041132526a0b807100114221041407203494000f4240600801460a29a00541e00820340802c0075 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 195281384 1250 195280134 195280187
    0x20609062a030f1f05010507200301050906011505310803030702030a02100b0108010b030c07050703060c0f0c05030a110c030a030e0a1e05040f0f1a1c020a06 69
    0x805a50402c0f108941c550306040e00304501d001d080d2007500c41900340d9415800d441820600024514050820700503d0a065203800032001080242c800007017501c020000d000901e4141c411507241c4800384a03607000180000d02e1100d026000380300b035490745d0304501030442c03000109991415800200030050b02090012002c0842c18010600040d4490270007900150f503280300342038000380f07023066041c10419024588140c0b48407580e403008a20303044440041300309840351034141910540344181031006096118400700001006441e82001100100c245ca903500d40700681c0300700b40c0354030b07100110081c819042044002903103030041207482000407100040390066407414002ca4070700400d2040c1038020911141c0100550b1420846041c0034109900c1e400310203030200c900702038401c0c1e034a014581c03140317840d08200030417414a580050001099128140003819000c451003211040d240007150242607800f01d289848104a00c40c08061617000d4814101e203450510100e4031070b0034100c400c50020801c8601c5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 195282634 1250 195281384 195281461
    0xf0210032304021c050f2109060c1207030e040e010506091801180f0c0b0408030306060703110102180a05040606050904020c0a140312060a0302030c09040203100f090606050102060906 80
    0x1070301c0d84500c05d800400c1c8480d40303030401c81e1500c0f10550a2109240e0451a01041400402c0c05c1c0d903131400003660713040e484047c4070003c5402c0c001c2152501c0c06520020541d2020f165000e01481c0c40b1170700544081103840d05048100d402d07101d085a5164000741c440e00070078a40c1e0b1000348440c01b06002c0d40000110307101104600880c1418100c402d4600c0e442c501400c800f40301c860401e49005000304502d15181c180b03001011034890000424040c420b030390206013070051501030110a500035411078021036a41c03040c4401d034540320300d02e50185401641d4620000c0349909140c4990340a8500540710705040c2a105410440070354805401444103026400e030b0b5900141c4441d02c00042d80160382c000d59162440e00b01403040c0c2e84030050240d80f040602007410005a100401c440394149410b841e1651030b9070707039400800d29240011002e041514071300442a820f48441758003001503284111018007402e07940b8001242e40e418241c40320495030300580003080c030000d107520844050b0801c1e072801140f0900f007080e1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 195283884 1250 195282634 195282679
    0x4050429090a1b12050c0405030d110313230a0515090f0406060f1106010b070305030709051c1103070f0b18090c09040e0f031902010906090f021003230402 68
    0xea003008074036201d14001043e1803038003500e41d006c5d012400142c1483d11b420002640e031341c0b4803003c0f041405040d0038002c1d00540144211102804d0b10340c048800541c0d210304840345c0c1070f241c5110866200e074020500000d4a0710040102c1102c03002032503041c0e1021106a03800040e030207a100076a008021452803c102d0f201c1c1d0003545c00418160322042c3c0b80d80ea0aa002901d9040c40580310102a0000f00041c0400014002901c0ba0a901490850b44941c3c0c4c8801c20356602456421560b800500c901084030f14050340c008071080c1521441005420a601c801410b946010790b00941805002d01107062000d05104c1b00500249d2412f400000000c401000118078000d000303030703409110a01c00007013510950505001e03000d50f407442030004000d0011610286500c902550010618024840c00c0c480e08952007504150303001d0f0b030014010003080050307203843e01c007104100d24124001d00c0540841020540688244a8448035032412010070404017509280002c500500480c1c2c0640110280f8900414200 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 195285134 1250 195283884 195283931
    0x6071e02031b060103021302090901030f0f1a09070b09240d0f02090a051f030c030608240601021f0b04090b0f0106020606030a08091c150204050429090a 67
    0x1070140c40c3d15411401402074a0196a607034402c0d080c01000011629215401007a0441e608600c21b80303500f1040e49000d50311042d0844002d8407083c1003240103061641013078050f81c00f0300c00c082d0880d508150390703081c00d010501840d2030030356000c0704800041c0d0099040802c12001d081844252a180400048103002103600104149203a16070104001c03000b800c0900304000504021142e02c0c0812010180700110164000d1500701090307200d0039126183c0e4000e401c0040a40818401c0c1d070052402c480066038031600c1c02e0201001c0e12206c001041d0154001b01e0600c0c00260444003541d00c80d070584041d030380900680038400b500180c0e41c510b0040418035002006024100503d00345500c0d5140c6a0024600800030709420700c2a049241804005102e220407508000f1055035440391008110b90805484c03400504058684415010040c818400503402441030755130849007000b03040c4449524541c5040d001c1c4d550000801c00000801c16882c10080d01c59001c4903840c00490103d1980c480c0410504441 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 195286384 1250 195285134 195285187
    0x17090402040e0112020f0f0f130b06120405010b0a06020d080c0d0c050c010507050a0e090a0e010c020303180703020109092004060c06181205030403050708030112110306071e0203 78
    0x44c414046161208000d00402d000b2180c51100f40d0448000682160a41d01005e04c54812402d800208090740d03000008001e20080c03070103848142071f0440c0750340030004990884495190403042c82d8685410340701c404c2540d01e1035000385030308041352034150350103603010300741c1c1321562014008000d941c0e42900038203250f8101c40c0e81e01030722111360b03c070301a00f511000742440c1c081c0902401100010744d031022111420704002c90b44406180c81340080d56008042515500c90554280340c10010026000001180503901c2c00d115002c4500c8805c8190703458800ca808020b0004080000802444002c4d0704803107500e41d10240e039040780c41074207803654038140d0040e4041c2001c1240755801c40c1c18041b003441101c0a103541004400d070010030079a183e804080400421400f801408004102854414405c0c1d404003580414080e03660f503141c070400406107100c24000c50b194503000b50410410b00700401c842c0d02803007498440c21244c2d00107019400000340f1400c40315086220038412160b0190b07001c41c0001503400c08 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 195287634 1250 195286384 195286409
    0x50c030f0c120414010e120f0904020c1005010f0e06090705030915010f170102130b0a020a0606080304170a050a06051e041a06060a020c06160b0f010e100317090402040e01 75
    0x201c1040c1c6003541c6c480780226040307400610f50907040c000000121211070900b00030041ea1101c402c0f00050081c091806411520b102d10404042004070039030000b030581e2000782d40110015a9004104108601100c0c0c0316009030381100810289030092001d981c104501da41602d400703170180e402202805500b6846601c5900034000100407105000c1030168182d82d402d8003d52a20b8401008020303030031030b05d1081080c0c0d44c0002602c82d60242c8240410300c100350348020180140c40e600c102e100e80c3ca410074020348902d0f03070560091044030385000404004107540326024140030586a21204000e02e0001c04800c4607081c1c4048440c0f04042620106120301e1082107540c180803502c12548104207401441a800360358100801c02d003042d0002400140024111600c1d5960304520001003411a43c08100070301e40c002c1c180074007031000242e41100c1d060b520010b698400c0f65882c1300c14a00024070388d1101414203026520800403451406000300881240940050326050f55038000428a81090b44030b10907c500 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 195288884 1250 195287634 195287663
    0x803070c030f0e0603060d03020f0f0c010e010327021f051e03270703060c0507020f0105040b04030209041e03021606090b0301090902030a1506090e01050c030f0c1204 73
    0x2c104403a9040320b1802e00c1c20305020300d0044040f03540b0f40302c00b500d818801d032000d0301181c1c101071081044055884c000002d0341e4403441030380c1034944c2e103451200c512404540381d10309155a42d44644952142c50301e2269602018070100034111003a010b450784166000021415103030740c940c008400b01a4200d0082c0e90300d540e200f0710101c2030490800c24a440c070402d1030303041052005a2030025040094981e100e0041c00da8044070200c2585010400d0384000d2441741000d20007482103401c04040d00c07140d4000d44d0066034543e012801141d2510850041c4c3e005440140428400350410451507540580b00300e080381000040c07000c880041e9640a9400c40040c0d01c4500340d64040c600c2200c40c88000c0200741090b0006605060846080d030105005d0000c8850362200e254095581c1082650407060700010801c0c844818084600083c02c2240600c800c01420044506c070202014441d241c4540c0e40700400b03506584a5074480d400848020349070901c41002171100074110403102c580c681c029441001a00303413621 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 195290134 1250 195288884 195288887
    0x30405010e120306130b22060f0e070809011410030302060703050103080421060e0f0d1b0f03020a2103110c15040c030c09020307080a02030624041d0702010b1e09130803070c03 77
    0x2902364205040341466401d0030410309050f603034015000001420240e619075500c0ac201070042c412844040b801789140420320440c40c500881d84016203020340e0035215207030760701c0c00c0540c00c0d19401c0c400200b030481c00304010041002c00039005d100400c40b0641c0005c10503080c2e213481342070300c481e419034517201c3d004070000051800080044050f006100d051034a0501103084140300303503101d01c2c480900360100803030b1000c04061090180100b00d55111003202026104002202d10104003282e2000109280c94070000341c010301c180a607444020101c0c000e00c0b2085081d0402522003001500c200c5d4000b101d404080005200c0ca100380c4054000e0660041e01c82c030b80341c040107200c1da01c050181201544100103005441c1c849550700c1c4070400c90b070803041c101111078140000441c130641e4005a480f030300e0200b9401301c00021542081c02806140e00034081811002c0c01c001d4803840c2170010b1500100010214282401d11100e865803002800d0708260b114441a160110203502c101c0fa50304c00926052101b40030036 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 195291384 1250 195290134 195290141
    0x4080f06012304090c1805060a0f12150204080a050f010c050711040b1203040305150c120a0c0302040504090624060e040e0703060e03030405010e120306130b22 70
    0x420b800d0000d407410a2024180d0552094050344a03030195840315420410702010304400c00060410704000e0380031071080108040240025200301d4815035981c600040c05008140a400035140402e00844001d00a65502c4219645800221400c60f409000010715003d05118154500b4000da02400360489002c8145086851010000342030003021f1080c14045404d9811441481006850002e090010740c0000760803070b00c8241c0004482c4c400082d0201c104030003c00e82090f81c0f8240440039880c2d4544002c542454047c04880031800000640010308041007500031540485803410014645510341011a0035070b80c202e84240d4000707840b40c2ea048005840026407040c0c03c0e603000741c10115241800b100402080280c64502c7c8180c0d00c501440308540c000b80f168000459100c401000540e0403201d00c2a00c03500111403d846552030440600440b0300046100030840560811051650707131640d0400c0014074150020000356030740c0340003a421584a01d05603e81d06071041417a254800300441c51642034 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 195292634 1250 195291384 195291389
    0x5030a090f030809040c021e030c0f030928030c090605090a0603020a0b1305060c0d080709120210050715050115020c060702061b0d0c0b06220c110304080f0601 70
    0x381d0410318081011400340010b42e0040c43e000c403400320b144000391208078504000c1c02e17680d07000c1e21074450089a10000000041a954038288161864840c41060311074490203040221034200c0a044000721803c0641071a0001d000c10070320306048115100d454a0040649030780005104554400d0700f44030380d14001406503072080104c07d00388600c81c00c540c04125003034001e100b00582c0840115450824400020303510010304400b8009507164000c61003c0d9544078031010814003c41c10a401180340c09100e000144103403120701400b280005150b6003072114040320010000d08000d42840300c035000481c21030341060404107180740801e8550510001d25400d069920307030301007903612800d00c000c0f041d2101c50a84d0038054044400e2900c808004c901c00c03080c15410002106c0500400a003032981c5600101604080c44c020407444015654640c207014040300318100011984400143c01c0b0603281c00d5400c1281092842d03c3c00511b44610088081c1c5150819004a03690303400621194840d00000c00401d0300 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 195293884 1250 195292634 195292649
    0x180105070e01030b1014030c090d06021306110703080d0e060a140601180b130f0b120f0108100b030313030507170c220b090c070204050108032506090506010305030a09 73
    0x20020341501500341042d5400088901001000003200220001c050b200d5809d00501481c025070700030714001009610400719080c40044900700843c80d00d00c00c0d030364088100c860f44010000c0c0d6095440e1a041508140c5d05124403540702d9145030861b0742c085c08041e0081703518000100300c6002000a0203000c4400811044c10002200c0c0c0310707e41106000188800c030351808150f550f941c03d00b84c21034038000065810500400b410703d0340014004090b10014400d04406c202c02c450343c0e4231442205e403d014000c0c030031807040d81d001c00ca00c0f0f4a0303c81c02c0d42c800c46406200604680c03800d400351307400407411644e941c42903800390002003042045082e400c030040c03481031040000d41035100d01c21001400041840d1081c42c462403800c0c100c0300c07059a543d0300c4404054802031240e092454013200c104020303170080c0e00403070085082030000105050000203407031540005c000143c0441ca600d030b0015000000c050810350b44543c07210600e902140b4248681c1340a1800341c009140e0768031032100e000e0050701c3c0d135901c00702 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 195295134 1250 195293884 195293899
    0x105010212040e090a020909070f0b090a03030305060a030b01060c050c0d0201090605070c0b04170c030c030718020d091b0e0106140a021c030b0102010c050f0d0203180105070e01030b 80
    0x41d031400000490b402c3e1440c40300190b0003500c0301800385152a640c100020340011110003840806c900008004d0119000c0001c0c54041d103480e40d8012030140034071415187c114040140a10009000c2d8000c2030340031501502c8861450360320785540e104040203034884808951000300840600c10700380704003208480141c031380c3c142124480d07000070301c24001031003142c3c200301010801500300100c000840340204011800541c5881e03d5954044012103d20942c682c2ca1284220030031003030901003000401624000d010b000ca052030104103101c2d4110f100300b1310f0081582080f0b00d8080484520801c410103004a004200303440441c440b8a088500b9600540c1d02c07031010a00410003d07078800f90030742407072056825540d1900c01d1100107030b00e0301900402030405800c00c2440d14418030783c140e02c81408182c01342d009004903030160506440760700c2000041a101d0000708207400c0300c039885400558101c0314040d00f03035095040f82403040f82100c40541c1c0120000c0c100c100c10345c0441d0380c0750007405440002198240b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 195296384 1250 195295134 195295153
    0x20c0d11010e190b071b06021b010309150e0a0b010f05040b1c11121b0a0b0a09050d030c0c0e04050106050103110304030806121f0e0c030d080a090804091401050102 72
    0x483c0d500c0c403601c500d4003034090000300c400c20891000008034201c0d0031549040e00803034441501130345400c0c40ca6100782c403445182401e006198480e000e1020b00c21b0300882d10545503c1031542600c0940010104000c0d10b205d03001c0e05100248810808038000c140a00341c2c0040d65041104000554040cce4040c1071050280400d50000d4503120124200c803203030b1041c6490707422034001010403082c2402e407444144900800b8540e1480c05001500c00129071001c407000c8206030b0b200d903408a001e010748102c040c000f40f04000140080c0c1006040240b02500901b2301c40382e80407699403601c1410610b034100000701ea8880c010300c010071109000314005884242024020035000300c190140b18080200b003e82000440310103c2d1540d220000c1c0100401100000c0d20200407103108084a02c0100f003000100183c6440c06480101d14049003290710300d1802805445803111341c0700700f01c0b8685c40141c461100c5c0c030b40e2070f014480000c0a0800400c0108801d80300840d10300c4c0c05e1441d284a11805901c414155000000c41 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 195297634 1250 195296384 195296419
    0x62b020403030f05031e040609120201020429070b07050403031101110706021b060c1309050402061207050c011503060c0306030b06040e03090301020f031803070305030106050307020c0d11010e 84
    0xf03114152545842601c1303a0b80e00030400c1d204a03004a250340315a05040034403050040a170081c85020b405400c00c80380360741c4800c104900f06d106038850f10301e0000d0801720740c001c50401d400b1860322030501c9810a6041041584a14488103025a01000443c02c0040d00b00200f5400c0f500c0005080c60190003007203c030f50070340c40c10111841500c030001c18096001604102c0c281481e04030350781c0c50000340c0c03c8030340c0c80c41c20f071185840950201487d01c40b80010504001010100c1d4007410344a02d50252039941854030b18030b501030020708040e0511050190a1044180141091081507542281c0b292644219895424507030200d170b1000c80c01c0b201b0941000400d20100d04504200794000d001a240080c010f540180d80509501500b401aa81540000345241c1c03415041805540140c1c040d25000703a003415a411120340d13034482c3c41d20003008141c09000401141780108061030f400901070054400c2c110485000400b00e40304035004807044113201080613031950740006801c5100300c1c295451002a4408090b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 195298884 1250 195297634 195297647
    0x7030b0a15050f120a03021f05061302070503040806130309061704020f0406090501030f02180114040203040c05030313060f210b01050f0708030106020c040b01120515062b02040303 79
    0x361500511204a4180c1282c0f04c50030301120150f8000c00350749880c0341301d1400079101e041ca20324001001d8004081d641510005100b95801810001c0408070040384044000002c1d4101a406807202e020600c400226183e090001c0791040c0156940c02e000c100482c0390280002c541034020707500700b10300300f812210782c1c2058001c00f03a0040d4044860700c240d0f241d15800540900110b8009400d244d040400000410010030000100c071442140d80600750b8144444071180e4078824850402c403400c0449450f189420503a00454229000c0c1151003d82a100c00100386182e001100343c05180303526480c02c108665010700e000a1040c0c07a4600819442c04030b4085610700c55401103800c46140d5146c41c800043d1780a101151354108103000ca1907182d51050600e00c049400901c60031006d4024440300741284e28041c0715541c18080161900340307141131407400b910300801004068144100c0c200d406258a551384001909a0709507141c2031464019154040348104030a007440854000c1c0103010500003c0d80146 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 195300134 1250 195298884 195298889
    0x103060c1e0e010804230102090a1505270a0308091207050f121e1b03070e04060209010309080c070617070c12051903052a0a0c0809030f07030b0a15 65
    0x40c001c64503072124101214115003003d0080b98001d0101c6e2090704004040d0050810f2400484201c0e04c0c4654030b1f401241c04090081004000032802c01528003000c150031b5000016a001c9003643c0c0d5a00760340000325002980c29007003a9000c10f808509080307030349041d100303028034011a000641086868180030990748280c5210b110b10548440d01400c07a42c2c40c0400298404180d050012040d5442081006403901500100c1502407030200101d40c502c0e04000131940c04aa140481081c8075903559203540000350000440c2a04244d100e20003000071504a0014150000b04180035040b8240f4018001d030100301d044e04104044100241000700b40c80e0000031900b0204c0e08010f0240c84103107680e20840f421701c100b400c5507000102400800841982c5684021700c654080702046800c002405559050060f1102d11b4680c449400c02c4680e101070f10034996844080d1052881e2414050003d00081c00c3c10603860b1301000503070000780100248250706002e00d400002007141040481481010f4031fa06101c40d0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 195301384 1250 195300134 195300137
    0x17060a0b0a0e031c0509120d021b031507050408150402060d1512030c12030207120e011403040b04050c011d1c05010f0506100e0f13090b0103060c1e0e01 67
    0x10454030001d5103080c40051a001c084e4000711030050fa515401130b0050308001e81603070041e07120500034608420300040c10100c00180781c00401d003504100c9070501d14900040b2000350180a141c13111100f29800345500c1c1d014001c603031203081d01e503400c111440c0d107804403886000719000072550901c00075032140c004441d090307943c0031404034002440360405100d0f452503601c1030015409050066003415804059030000c944641030340d505141d40303100c086040c0c1c0034208010300030701c20b40d02c144070110340200c0664401c020306052282d486e081d100003000c0142c20031a0160713240f18030481000301f0014248000711154009082c40403800e0000c3d00030f10407014290409600403141401610319256000d0321000071598094000e001807004031040300c01034070f400c0c0e41c201d014000446900c61130302d008030040d840050700a0000c41c07840600b2400c00400c08122441c0040260f61109490081403503160b885000e18003903040440d24503034410004000e00d0510f862030501144910780007800c4e9500c883c0005145009 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 195302634 1250 195301384 195301397
    0x1e0309080313020a05120604031701030203030307030c09050d060902240f03060102480d0803131b0602070509130f150e0d0207050a0e1b07050d17060a0b0a 68
    0x30b071020460b44c14060700415840980400b480084d42c4000950703920076840f1741d032601c2c01c000780d01004003081c04080c0002540b5800c14000076240301e1003a401280c0c41c595903d005441c6a41e41c401046103009a0302e81601c2e0035841d515190309504102d0405080c0706407444401e480040059181902c5001c2d0740114030041e50004081802a031003000f4501c015100790144684100c0325140c004100803440c1c09102c1e003034106007020120b01d4080440604952800350100500803000d5403080711561005251903410403200c5001030104040352000128442030707003030000380c4a08005000e4a4801542d0246101d140024200b04174046070510402d0b100c0e40c00b1b08880c000391528982040700303a4040000d0300c0268903340c010b8980650010311041841626000e03a00c0340782e110824030510700b015009200750841201c01141d80c0001c80c1c0744444401c00d4155440d41046455901d440c201403030421034400107410340044a005540c05070600d5040042200c09940c104d01c1e210342400680141c0c1c414000344000c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 195303884 1250 195302634 195302671
    0x14060a03150902041109100c030f050d0e0609010c1b051005040809042c0a0209071116030803061f1707030b0a0f03060b060304031d1f1e03090803 64
    0x1003a801c00c902d8954010024050200500c0d4402001c1d08280c0c40c080c420b0400440b446c03250340c0120400c0360303056010355078400902e88114040c0c444d42d00102c1c0200c102551400510b20fa07010a0002d107005d0240303403002090741700000a0003015542902d0f50041107100202501000580004001520b8660b000000c1915074582c00c00d00c42900036a4680c2d40c000342804441e1400d440c17203418809101411448242c2c001040c2e04007a9511412000f00a40098803040401e079500d00404250a007a107100045440030540c1c6901c080d03495006510840d1680404424040e15152018140c00f0030b054000c0003003101c45114100078035841e10307003280f060386416200226500130b1003900503144505001d44410a81d60381c0741d0070000d0340d0540c0c0c441650b05600d480c1d1510b03004d2902004580c0100d42540c0c036501000e81070800c064198480000f0280c3c0981500480c101c060310102c44815600c1d001d89412070310b618070112284045626681207002c0600c5c1c00361a00006801a0030f41c1e4220200c3c9014984210 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 195305134 1250 195303884 195303923
    0x1020d0e16050d11030607030c0305010911040b1e0a0e03060124030b03250e1f090b0303090a09050714041802030903040b0301230a060503010306050a06031e0614060a03 74
    0x240406926034046c080c04003000002c030b4141d000009407500a58081149030b80c0c1e02c1d803100840c0e40c0090440d10314481000104502d01340741780508118104610308640084042e06120394a5119450150108610b200f9042c40e030315050040a0052201c10b0400d013040703d444002c518a02d000825410505030b0301d05c80b0088548081042e07074800c40310455160b82140d03c080c030f092401c09852180003074000450000614a00040c800e845071508a04068401c2604010010001c2c19901d40040d80505c42400341200650360b0781000e078010042c500b000100c50030141402405141518500855024108420002081806030014024064080040e00d0303480348441c550441c880c41c0c0c4a1010a24044004916061044c40e00641c21241c800d2401c1d208642a00344482007003188a940042072051004002041d40780d00203c0d44040c4414001032810b480e69916004003c003400c1c2002041c8000211604001d00b61040140b40c000801520500b0328003100003034000303d00c40c04024002090203240c0315800 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 195306384 1250 195305134 195305153
    0xc032206080f180f0706051b0d020a030c1e060203160e060415050c010204060504060f020705030a060c050c070e091b030d0e030f06070c020f220e071701020d0e16050d 73
    0x9084e105a4091395510743c8014402c4e0410280000f45514110b4400700440380002c045000d0142c41e0003500c0400000d840130b41d00e101111000342c8140c601d00602d0a03034a2040801c0d950700c84e21a40005031a0b081000c02c1100e603844022111080c0450314041c0262035540405480494088201c0201203038603403903040740c1d180141c1e100032a89600225020410b01c1c0c1007009807003610700c0c80e520103401000c441805ca0740c1d21004d100b6990181c02c0350b800940400ca0a410404c0314030040e050580c5010502c0e0a100d1818800307074041102c600140c0140191b500c0c007444400d8050003000a0411600c070580000f0f81c5440640354803000340401c04440100d80e460134050008080f07205000d954007464943c0c2c02400d20001500100c0c800c00c2c91000e6140c45107000080c808080d0300c02104005014000d103100d0005100007010040c00b4400c6450000d01500030444010000c0d44020016031641180810329050b61083d05000000d40c200c00c186828040140311305000301d078011150b80e5008030340d40c1400c440c3c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 195307634 1250 195306384 195306403
    0x80c1e0c010605151204120519080901150503120702210c0316060503061519030618060501141c090f05102705030c032206080f18 57
    0x1011412400490040d800b407000c56200352009022000b400c98031842e43e100d0352200381c410200020215010582c00c0d041000e00c1ca207242041d5190966000c0420101f0500040a800198450003045054035080c0100401c400140c0350084100f4281030000303031601c9011248000c5000702091403030a544c3c80c1d004807001902615074501c810b0f0418000e4545400c05011254002d2045d0110000c075110002c2c076101c101c405580d6083d013942c5501c000c001200000507030620042000707110000f50b9548025221503c08000e440c00500d407440c10075000c0108641c244003880083c606841007010366004410a60583c04089140b50b440380d01003582d810001c101074896100603d0044508100104050ba4441c001d0040040b6051403180d00485800e8800c80c03d5080f00b07403006040c55007682c6600e1200510994498406d9a0506020074840c40c41c54000c0240d05030361405501200c486084100b100328080d0400e89844582490513100c604524100500a40242c011030340c0350320000e02060006e1600d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 195308884 1250 195307634 195307687
    0x6060d0608030403060c0e0a06030911030709020904060f0f050603042d0203010b100f0e1201050c03010518070804031d0a0803090307080109050a141c020312070c03080c 74
    0xc0c040d203801c1e02655940143c0022105c00f450600440c00c02405012100c0d105076000b0a5148044d0619100720040d02c00d0107400c1b21108500194564513540c00d10061002e041c04460050b25122520100010364078a039200180d218a410703801c3c4a641c5c00303022050f060f60820303244540d40340ca542c90106110004074011081400c0a9010032950104080020120710300880007803140418070000c00082c0c04000e883d19011464842d032101080e4068051045d40c03081c001c0959603801304c1400181c1c05c1d100100c6043c00405000001031140b413070410041c6005044904011702c1c5807800c81000303000042c1c00350000d4144a4000b11644131402c0194100001d03c102501620903a80c1d110340351a600d03005804428806e010341c1e00f0200304600140704240303076642c0120040018004903200c00c1c0821100185807800360084c400340a15071652003904002501c11036004650f103641c1d031a5085002c1c0c8002d001e11040041507596000441c1d48124040e0300050b0541c040c564518035205842418120501802c8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 195310134 1250 195308884 195308891
    0x171501090b070503030a050601110606120a0b0f1f0b03061c061e050c0c06040f03030e0a0309030308011d1f05300a0302060406020d061805070306090b03070306020306060d 75
    0x1c2c10440013101942c01a4440c0c1424070407601c681d0015180391480fa101c40400342e02c8440010300c0b510b8002c20031004022030742c041d503510f2196522004102e82d0211440151940010140200c448500081001c100685151420603c0c02d207800750149120203056544508410a04c061200f981244040d40c0507501c01020803484c44001c03084148030503002500d8001600c1c1c080064501910401254188030021003c0c0006a5960741c403000d900190641c26403c0554070010702150380780c20401c90300d0060207900c0c5c0c600414950300c2c2c0105150016045001d0754011545142c1c0c80100c0c1c000000d0b040b05002c440d454992030640690100500c1c80d503c03955200e001e0b80031491300e400001c101c007c00d031500e241035400c410071090380041c0e54034031268000b00143d105000140100300194068800038000d400040341466807026400f0f4040750005440003d03560710801d04c00a5501445100001e1505110501c03281104500180d11140b141c80094170a5400200107141035942e803007107500c007091014080 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 195311384 1250 195310134 195310147
    0x607062301140108060a080d031113030c1802040f060503040203011b030608010608070503031c0e010501140111011505060708160309030c0b070b0115020309030114090706171501090b 80
    0x204010352261102d030108032031102158041c00d0603241803094078103010060031140750315601100108101c00180c00b80c40824050002c07400b20080114004601625074212264104040c50b400c2c1000c518000804500c1000100140c01d41c0c0e55002003200c000341403164403542e990001c2405003c9444c6020005156184010002501544004e0030f41d500400200546070311016074a541d003030340e03000b01507065100b8010310f240c0710000340310040319481d40304022445030b21210149007074be034081e00040120301448010503820750340000300a4244000300c0080c000c041000d034044560b8a5180206805481d0015030030007400420707002c80c0c029210860564009110b1418000e0040805010440b400c1010410004580703202ca070a40d07440036009007038803105901e0941d050700d0342c001089a90003540024007040e08a41c0c0d0030b226118400c0360010343c9004030701d0080c40c150b0400034103400150911070070f102603a0282000458070f941c44501006014280490000185c41380341f07441e44101061603000511 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 195312634 1250 195311384 195311399
    0xa03080403050c01050a0e0d03020715050414010e030322030c03030b0103021e03010806090d0e040b131802040606030c0e10110607020307120906050d05040c410607062301 75
    0x140b107005a45011b440340ca0f038070641c040700ae900c10464042c0003e240c1c8400303512140125804550850310071420f20702c0d452140a222420348800c6003000d030164001104005d00d203a6490103100341c184c0f900004420b80d04643e40c01500b04607100300b018040641d5140480c082e80d00a0f07044400211440106000c5620105c0c0f80078031907402401001c100717026801c04a04a4240001c01c13441201454948a6818000505001c0280410310707007550f02c03441d00100d8800c118154031540f400f104000c07000645000c000d0042c030040e035500c3d901c01410180b0300281030156035481455146900400c9809911280c6552800c0325001c103040b850380c0b8075010303442c140300c2e10640010081494038400d25041c0500c25405e002901c210303115200d0000418010800021020b2840e480a68054810b4940000302034680c3c00c1c4103005403c010502c00c280c0201e0340144100000340c0d040d05031004141d10303842c0b542d1102101151480c01903840050003141c9031070701c25034000000003039a0405410006500384541e982ca26 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 195313884 1250 195312634 195312641
    0x206160309171b010203030708162d091707030303020702030c0301061715070519021005090c030c04020f07020d0512071101031a060301060f18060305060109060507050a03080403050c01050a 83
    0x190b0040030f0b40000c0080c01c0b103500200a4a1280c022078440071215602e0528190101a4a25140c41001085441c0300c102d900111600c40003200c0d0210100d020700050701e000381800205420034070342d5045a5060301c2c5a803400007807500580754140380140c0c5940031440464502441072083c3c80c2e0550802201040054811031140c0302c8a0888003190800340d410940340740312400c29038001c8002002004090f20140303e034200121000d11510480b03020f045004e03042022500c003035960312540d070007144900d401460104803220400314111001c601d03020080c020241540305583c2c009000c1c565a0300100e090110501620701440b410072440c1e5035400a80c81c1c44085a804051824086898101c002e00c2c0c0f001420311401160502406440ca1a401d0803c2a500403007405030315020046421580851341c0e43c04402000100300d19180811a810002c0000d410903200b604100d040003828840710010a50014110340907a4050900c020151030b43c1c10304444500c070304005030700c056007803405108081e00f8a40c03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 195315134 1250 195313884 195313903
    0x1b1119090501030b040213091101050309100608030306030709290102070902030f0a050f090a020103020d060f0314070803130605131d040c0b0c03030105330d060909020616030917 78
    0x11098820701488087c48001c590410401405030240a481c40650754050b0000b10341260303081085a1103015940056010f0b281180c00043d0301d6040441071154504040003984003400741130000303201040c114080081d120b0300c43d400543d010000001085010303402480b80001138103041009554070714142481c94140402070b544802903d10300300000b49082c900034989800b51021034013600c407455080c0c004501a410044500a4507a030381e400018100010f41c0c6041c008522400d00003120041e5030710b1540c10303d00d480d88481c0c2c00e034004102e000b81c110b030440c9586060340c00508106460b04800b90003941000c8180d00841c034222003034200091840c1000c03802600c11441103900b038581d9916030252807038034000c52010300c00341e03030041c0018001c52910900c8143d400900076094511b80071180c950341c0ea010891406581c060400183c68203140005008500c00781080c128180003214060340450458806e10001e95400d00c402001d00003018070603c0700c50000c100c50000e4040c101c40b5661115120b84101 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 195316384 1250 195315134 195315139
    0x1080615060304020d0209040606050d1a0708040804030318050409080910020d0e0409050f0d081506030c19020a0210020705090109050f010605032805071b1119090501030b0402 77
    0x844031495514101048070b20456003c2c00c0021201815824070003103034000b0344100d0b003250711158046025180e030044001c14601441c04d850303000d40c185440c83e50066001c1c0401c0e0800442d88100004030ba9140b040b1001c407540742c503000c180745820301c8050a00d030500f504000d92040c1048020403d01207014040c085108007200d007909007800808090742c1c1d030304100d40494040351114507a45900d1410381e1003c10724602880c26290700400c0f540955061800218a8401003a021001c0c4003c001c092820360003100c80540340140307581456100001c980c09201d204583c0b0785901c41c8950044c0d803082c4000303904558013070300070001104021300182d125a032600509019980c214000101d1110390702400380681512042c070a0207900700b0328201d42d640c0c4001e000da044002000300340c001182c3d2180506080646d40d07200080c0c1c90801420084c00303089070030310424001002400f02d8012820007107004422010440d108000f8040528505481c1d024079070008820518000002081c0169a9045841f80e03208 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 195317634 1250 195316384 195316411
    0x90204060b1b0c03072108130e07080408070f031b0c090e0703020a061107170601140607032a0803180607110601030f02042c0d02030405150702010512010806 69
    0x7200011a0754000b6000002e51542c4402410482c001b600c00c0707041c582204603190041240c0881e110300c8541c0c1d0210741c82d840d040010040402646540c0f10415400402c0d92802802d58289602c40c12000d01130414080c2c205c080008030341c0105401401c6206000e154020316001c80c000d03d0518115981c4c03a40326500742c0b40d08044404101c01d03008205802a80da006040300c82040c01c21408554900c080980000c030380c803460002040e212103602218003070084a2005040c1d40d8180180e0840c4105440d000f607000c2c4009200c800000f941005600781c144e0b0081c0e040d1f581e80d0300d204400381c040d0403001038040c02d005400401c2c0040842c1c500222890030101c02c0843e421502c1d03400742181d03000440c0c4030350300071a00100010b0001440310450817000b540001d001203400c46240d070101d1a820010f41810000340c100504020f6000000d202040320100c4900180d41440c4c604401700300d400d084a01c40c6214440001051011a80607000b60f850b805201007000d01c0540e10b903c22155140030503200082000e10 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 195318884 1250 195317634 195317677
    0x70e0405090c060d05100b160201020d05090d060e030d0c0c0b090f071503110a03020705100509030d020c102f180603090a05030c0a03030b03010c1b0303090204060b 72
    0x1e00003002d800c0124041c1c951803400c20f0085201e4002c080250030241e941c0eaa5080001c0c5009151010301a80d100104003413102d016103200180c54820740000160030701c80300b84207035001c03541c40050038417480ba08100c01048040f0101e60b050300f10320808080000f80c45ca130120b4640103541c03246403000c80c02d2041c01c80c0600d41c0c44044007a6a5000b0f1000380c1c03586503100001c2030014008095290b112034036a4203010602802c2600c2055164009070b1440300025404100202440404c0156410406130310100304018280190842c4e168031840d094000410380004194149440410420400520001e8200114000504030700d0008456610350b4400390760080220720b22011160403203400c000c0e0403c0c1c159514035900180401c5130001021031005c1d001d4a05940c01044080c40240080740c0040084c015400c030354503001e01210103810080d400380c1e160003010004280c01400c401100c00c5942c041d540c00c044c241c42d0031070150000740170094006042041c0002c80003004800b074a014451546500c04162 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 195320134 1250 195318884 195318901
    0x120310080f060f070c061413050607030b01050a0e0d0204061d01090b130c18030602090109080a1e02130f0504021c03080f06010521090f0d080103110a050405070e0405 73
    0x22098410034034103c100800716031901d00841351007030440c0c0b29540203c0d14104036440498514070403504c1d02c502c1100548000c007001010b00c10b0541c010440e0070304104e00822040001d1640c09444200e80901481d10f1141e03a2568800303040785462a4024003d006060312041ca110a508013107140c9910000752000228006a440c0180103c1304000f0b04900e10494840c00500c02601c0c90744600000d000a100290420480c02c010240165004200140e501e003018000142503502540c0112a150403c00584001845120320002c0c40d141d580f51640310307541c00b4000a010701071f0380810062141c0c640703102003c2c6040700307820084c400c5000b201c2403200049080040d03111241c0c00300004001612031030020f2603d1980462003500107006260440c142a1814441c110715000e4034801c0094001240400c20018020000401c1ca110f040024115034118210054101c5606000041201d195001541c407940c803602e0b103074001440c00401c00d00150a01c143e000d0a1036100701c0155004a050800045004 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 195321384 1250 195320134 195320143
    0x70813060503010b031303050f12040224030c0c030c0a0f020901050f10082d0609070207030308011203140319050610020304050111010e0d120c08010521120310080f 72
    0x13039040d85079840c03456550700030080080c0c4000c1c1044040c00300c184502114032a001028001546e0314100109140c18580104508482d040465140c960381290080b4401c13807059041d81e8105e40e000f4001521030756075115007400c40c003d2295104036445201019010b0004078400000714500a076241e0b55540d03240e200348280c400b14580a1034004aa42d89002c0307882d4403410750154407000040c071100c0d9106c0005000a2940d0b00001070035006581d1206000451500003e090342129403400140019440c4d960702900e00e900500c6200700c15488441c099040c140240c03060451192107000e11581e17440e250445051002603400303040200b52805000070942c2c1801011003010003a141c000b141010701d480c004590010000c548910323503540b20b0003071580e10300c4104408001401c40352191442c20101244031002c40310101e00c040100110381e401081141c80d01d024260035600742484400e40512a126014901500907000c4e0181c2000001000744200060821001f46e81104041e684e0f144603c81945585 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 195322634 1250 195321384 195321389
    0x80715180c05010804020a17030d050c0c07050904080909070f113d020d05011e0510050904020c070f090b04051e101502031c050f0408030709090207081306050301 71
    0xc500e407034403041c02658012944181d00078401400c111140d5100d5051010064984108080aa0000c905400251340c280a1194881c1e03c1d01187c504081d007401c0d0459230750b00e003841418007469048000c5800e2000d21022640d102da005400142c4e81e041000340104031988001603607000400e01030f401b8041c1480420b03155402600180810075046078066a038040c491203030354403a82510700fa581284501c43c0b40c009082241c2d03e003040000c50b58500301140c58a00c1d02110a54481d50b9007943c00d20495480d4000d20308441c0d0301e890302948503503030000403070020310410803101401d100c1e2040000d11110700615003001d03500b4202003406103007107910900003922415255403070038812a6001c1a041c84881501d02d5221458038051940036644200102003411003c0080d40141c000068a0404c101e80c488031000c9014200b008100c60314001c610081d003a0310180c0024844040000401d00c010b200e40d2801020307086400741150b55100c40d20305102242e0140007920350340c90f409400001d20501550940b0b04 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 195323741 1107 195322634 195322643
    0x30709091106040b040e04080912010e0c0111060a090f08040902040e011205100902031c020303010e07090e071b1205070b0c090d080d0908071518 64
    0xc22140c01e100d01ca0160400b04810800e6411000449080302d200b0030b01d15450341c80700d01d0400c41500c65080345560160300d900e05800c0e01c81065100054400001003152140300c0103400540d05400c140040c00c10035000003001483c1280c00e40c1040c1e1456100303071481c040e1745038640c0e80c11401c0d8105404c820845036002c40e050000c400c43da4103a60160610101011602400d60340306541c640e401d00c550016661502006811520104078040c14898501c800503240c00000364002e5483d00f003442000800c010210100d6440c500031081a416500102100d240907a1803c13401d9a542214440c909000154842000c0201d503c800320764280c0000b0b5a00c559489040303050006d040d10024050740c45a000400251400d540e41c20280440a0b610a10860b21070202200d070200410140c84042c00710f40000500038100001c0d1b110000d02100307010800c21142c02401815107106429180c01071 = true := by decide +kernel

theorem cover : BRFrame.Cov 195143884 195323741 := by
  have h0 := BRFrame.cov_init 195143884
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195143884 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 195143884 ≤ n) (h2 : n < 195323741) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
