-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5394
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:43:17.280328+00:00
-- url     : https://prove2.me/submissions/c431cee5-738d-4d2b-8081-ed81f8fc428d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 969964028 ≤ n < 970143884 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 969965278 1250 969964028 969964031
    0xd03030b01140406170709081b0d17071109071e0c0b0a0207060e010506030705120c1c02040f0c0e060c10020403050c010807050703050403080c010207051c03110306030a060b060d 78
    0x1551500000c00035100c00005c0554081500c012569151080710030340c003902c0594010784903003e05600b507900b02d4006c00354010307001285140341c2408120013120b800100008141a55510409803410041480812850030f1045660001f4021240c0d40300c036030800c0c000c00f403906044825058a0050720758160f00e44006101d21000301c00c0004c2c200c41c9401602080340701d64130601010160440c031500340c580072140c0c2074055102e40410482c501c2c12184202c200301d050010b07a41c0080450b0b010990008140b26031003044880070740c000d01182800d10459405a14080081104641000d80107003030f0302041a140384901800320341c01c026042c0c10b0201c051010112807003156941e640c1d15040e44c80700c0100040380c0c042008100014021405881124945035055442a16280c11a40da12220340c100e4207140085640c01e01800001400821a49400704a6402810303030160400c80c00900f960491411520342000034002d005641e1000699030701e040d170f4400404500c1c0600ca40c0400c2513030085060110009 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 969966528 1250 969965278 969965287
    0xc0e090a20030f010219080402011404060e09010902032725080609060f2a120411030c06032a031e060114090f010e1513050f0d03030b0114 61
    0x158401c09410782050310940c19910b074100b0b4120760074201d008452401e0b03c1641040c941000da188240304d1154018030505120010700303035491342448150800c2e041301c004610009410365052034510b03031480c010004048103525502e0701111030030521101d41c92104d19501042007404880c9028030001406040310b0072518440b00c0604000c18560380b05101d6011035000390740110308401300206d1161b214483c03280031001d40d074030340d400b600340a044a4400c100d08007110808801d00400c040300100304042c1d80ca0061500c80c200b90410303620590122500c5440b03039020440401482d21080300350781d8000c5c2c54071440c0240300210040d41440380b400001c45400020008100b0040102d030b004100038009809507032000c03a58440006461072080e440e40e940080105100c41c1c0035074600201985c040c1c000614203c0f5228102c100800d82485e5100d071580400040400e480a00c1d14180c0c4107180100012561070303603428a50000303e20300d400ea00130b000e01055100da54140c06640280d50342d83d44100250f000030b685 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 969967778 1250 969966528 969966563
    0x524091306031e0c140a1d0a1109030c06031008030a410711061c05150603011205010b09070302030906070c020619091d060a120c0e090a 60
    0x500710350104451241d00c604240c8a4654a0000c40c1c040da0350190071001d000d401c10103e6454040c10b0006158440f10000340855580c0f90000c1030000703800480380c89107150800c028000c040c1c90f0040100c2c404c3c0e2000780107001180d5000120303800c004a0603a0890741c1c0f81c03607690074054211159000329120384000910f0344d21195000144d05410600c20b1602000181048107680c1c582d034035414918046860404890003034007140e0001c0c90000d115030802c9120400c080042207454004204054040c903041054058904950088a82c0725281001c0c11044c140c00e2000240940010b0041d211074003646030804040040035400a081d43c80f00400d42d8005240054008019610807103541c610b5000c0c800100384468000e082c45200c45500900e0f5904200340704000d14495801c82100008018180d003000544489110861024509401030080307280b51000501a008450b0303400000e070040e4000038030002c00c00d210040c10a8a80c00e03c844542d9858191140e17280400c0c0b01070160510400c90030710f1300c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 969969028 1250 969967778 969967781
    0x15080a0305040f0e0c0307050a02150708100b0f0a0516060f0912030504030804151d061509071e0e060c07060e0d05061609032109050a05240913 63
    0x11180c0d0b0b03da14088240e141c0311842d448990584502e0260355090001c200348600a81c0a0a400c2c021481151f544103140041600f0519080c0d0b1584040b03149441407117400780c800d803503117000360072014409846d1103190844d00c2c180e845181c0018041180c041500000c004010545402054011006021009490382da00000306228142110180080c00e407107a281c5000703008007407060340c25440302c3c03c0d90b544644514420141c4080c068114a50f10b480c00300e210042c0301d0201c0100c0c00320034000c140900d03140d040440c02c6281405000c1c0710300360420810815035406007240c00c0200b1040701c400c6290030713508400c0d110240a000e00c160321440104ea204902180015504219600f41c0c0e45d032008480340340144110040454800707444c90b00454000b41100440885d0a004000103103481c65545a8075214081d03100301c0c900c0c01751340740340d00d154031042c01b1030f0b1101d1900064003007121140c0f5114901030010300080708400c090980302218200f10440a100c0e0000d072440010050006211358203145071000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 969970278 1250 969969028 969969037
    0x140903031005120a2604090e060a060e0412090f080a0303150617090c04090812330301110d060e010b0c0703081b0d08070807080403090915080a0305 65
    0x1c4680841e6080000c0501e0240500114040301d01c02626502800303403115080005030480035400c814480c4c01c03144074140e40000900050040500000d44080c0a0700f915040503000f41128880074203100b020303c034540e030980071250499030181416040d1982c2ca40240c3c1c052500741c1c4144280e1025007400030f0840c901041d0b0001a83c03290b89c00b0007005014141c644481084c50107004005051952146000f41c101d100300b03508000300f54103da00111059000034203480309100d049481c000045509102207041109054220b00b0318042d5403013105a101c480401c43c00303281d0510a0f454a40240103c29403401e6000d020083c000d0740044cd500d61013140c0a0000d480c0602c01d12100041120000400000503400d46200d03600389400317400b04918549230780005411100d148070340d803e086400f403070501c10100500842820b81303840b00d01803890120f07409440040010400c20600040000b080300103075101c8402000d40d80106400182900d01c109208815607458004050620401f002a0145a000740142c03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 969971528 1250 969970278 969970291
    0xf010303030c020f0304060507030e1005190207030b0a0902041e051f03120507080d0f14150a060f0c0b010305061503030c0d12090615050108060402160f02030114090303 74
    0x6204010050b0000ca98840c400d15110085030000d00c8240a03440c0b14100038100759000f0300d0700035a000851400a100c5094603d49040416000691172140404100a0341859001400a00000ca24584410110100c000d10310003515a44480c1c0f40c0c115079841c0e020b03d018072400108042d181c8071203018400184007e03240102c131314190a17013641c00c0380e008580075403d499120401008100169000342c0e2103030040001215121002e015403081202140324080b5400c0c0398000201d000324107a40240046c070030251950302d40b117030380c98000ca0309901c4042c03d0034100c850b24641019821001c071781c200c1e000d00501c0401040c900c510300001040c41030000b1803a00070030740015084064540842050303680e200348800440603410840980035990302480c02031200b2143e082020071041d0031907841c40211000e990303031241c41e20f04d040414016035034003801541c0d20100c03d8404501c0c201c2c00e0251030381d000d00c1d160f00003455507501107011801c5440c203400c2064006603803106c60341c550411000ca00d4490708200c400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 969972778 1250 969971528 969971531
    0xe0417120a0b130c0c290408120a1107240e0f0d02070501140a0212040308130506040f09020717070320060c03162c1903081c0b03060f01030303 63
    0x18442c0d90a18403134100c01140c240c49440c0d8243c481c0d540d9200d94102c00300d1030701a070007008800c0340a80100402840c400c61140780c4d0b1f039668208030000c042d038140002e0107041106162280300b2041151a202b2540115040b0015501441c1460004059a145090010341c2c0f2802c1000d645850711300081d060558101d100181c440740340a0040c12a50340340d641c03040c03e000424420b01d0081d040244030081540d4074151044d104409081c0a5100065004c1c0c1d204882c02900010403094400b621701e8504040d03d0200c510602d03081c0f620100311800760050042c840c04642c0042c0140c00c0150781492410f0500c0300185d4181c6901441c00c0243c242c6c8080000024222125007400c0110340020841500c0345a0002680d411515031014508108030300e61254028015000b121035400c24113240a02c0c0c642c01d20032000c1588818000c24000180741008180d61030400d100304c24000602200141ca00903950300c0d010b145040407050780c80024040000a8541501664091018034210340c0c4000d070680b4083e840 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 969974028 1250 969972778 969972799
    0x19030c05040209062a030301060503070e0a03240f111209030a050406110a060e0309030c120706030209012a060b090609070810090203090d03060605040e0417120a0b 72
    0x18002684140c1c80700a1340054204400c17801c43d4001c010300d0608011103035840307450044403100185554401e810100114002008010b01198040c2c0305000c2110155541442c651441d0b4400a42c88059000c8100340342684174404401c014a0b44180c207030b003030303184814010030307100724481602540048680039119002c9000504083c200204a0f8030310503060391514500307841e01c103040303800340f8929090100c54050200d810020800501030045e030202c40350051a07580b9001d40404d45400081407666004610004041c0c440d000042140b0044030018140907955a0340d0b540101c1d10350140c048110320102100c00b0a0301c0300511146a0b2444030301c80d01c4104000e0200400700400c1100490391294001e801e1000103108600c10158030750403181490740c02003059100d0404134181d0304201c1c1c041241e0350120b01048060760380f50092070010000c50515600c0c1508100e05448071600091024100040c1c0e49000040c811903101100c3c5105950b00395680030341091001d880141031001030403880b0f13170240b01 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 969975278 1250 969974028 969974039
    0x40203150a0e040b0c07030e06121f030c090b0102010e0f15071704060e0c04020705150f01260703020604080a0b0901061d040503070c1206060801020a0c02040e0a0219030c 75
    0x1008540110340203001a556a5692117450286a108100c102c0800500040341c886079103420020305030301515074080304264a0100341c40c1c5e000d80820b190340812404800030070004500c5500012080c1c40c1046004500c0d070345035500603030250010203c20a440d21820741d255450b440302103407d152600e105440c010b50390300c4920b0b04540040c051403454104074524000320307000454640c0842c90300c03140e800544152409a01c000b0781260410801075072103800030308100011490244403517074081824002c410440d41000c51075240c0c4000c0c05082d003075415503c40c8107e039081c1c08006609c0115401443d2603a200c0d11445c140c0e46521001c0002c40c0d0000c298804510000810b0084005a80946c1da040004e1035003254200c81a00001d441500c3c00d020030020940842c9244282c94068104600c0c80c00340d540d0f2515059040307480c03581c04500513910610101034119400b00072461102e40489010400200d0313070004500b0f12210f468001c0d845507036115004138030341410310040c0441c1d02407807042000c2c1c1e50302e0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 969976528 1250 969975278 969975299
    0x60105040303300203090f33090a0c03060f150302150a0309021005031609050102070323010e160e0118110f03040b0a0c020a050c1e040203150a 63
    0x180401808980d240d0042003401203160032554854000f0304207204078043c1e4a202c0310881c1c3c02a40c0412191700035000440011804015007038448007815500640c041e1451004d04030205005036600780088003001041100004000303803070784d5130340001041c0c400540d83d15264008003080b844509203141000d081d042050540300307a000071a0303006004800880303160318000380702d54442c5000e0001d15548849602c003584415105250480590700d449559003028103604403104c031808582c604020b088a410b001c030380d03808901d00084960084007613802803550b14249101400303124403030103a58130744001170201030310015508450b40c04244000f401c0b030391580c004c4403608070b0034050100b5581c0c0302c02c0190310310300c11680301d02c1e04000d01180160910883c08803001c40e80e80300344d4081e10000c2101060001404091260461405250004110a10035940d40c1c0d40c9640b100300c1c0c80e80c0300340b500141c15820446240032140110400400c01c56880c5018510381c1c840d03042402c0001c1c09500e40c0391000c80c4001d280d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 969977778 1250 969976528 969976537
    0x305070e010c06050a0228020106051c0b04111801050f010f0e0f030f0303090c090a0501030b061908120c060c031b300603010b040c14030406110a02070e060105 70
    0x180e40b0340d218010a512800f01601c000360020780302a5080100020404040e60f946900307800300c1015030b848000f501c034000d0944e40c09802580c403c80b044140400070011420342d400c5410b50194014001355182e0a018000c1101c0200709600308252000d230807158100b4043c00c81c1650003c85509506c0c006d01801118074002d00e050b908040303010000340c480f1074a04091b0002600c1002000c1711607031400c175151982103400a40e0b0317000c00341d070080180b0761051810f1101c036580400030700c008000c50344c995200c0504000d0003502c1d06000b86003003410031001084050108018082041c100c86100289280901480d1301001c00050680240c0010981d2440300c0e0040b68050504101014000002e1104045040c0c2c015211800485170648562502200f9140c4141c0e8141c1d00b13080009140ca401c0c800e050a41c1c41c0000c119118600e00380101c2c0101d50026005454247c000f044d03a501e940da03c2c87e00c41c00628201c6614100f0020208020300920343c001410303030a403482001100400d480714070043d540f5005 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 969979028 1250 969977778 969977807
    0x1511010b101b020a182702010c0c05042f0c0606371e05010203040603180f0b06010f140904020d1b05311412030c0607030507 55
    0x72240358141d4528401e4903840c542403071012400929002541c0015208030003580074981e080d40b92600d200302c075060391103902c5001d904030026203400c1c8503a030407110a5440c0e0b110024180508500d5030700030b100da0540d448000c1e03c0c0c05402000700100110a4090880110140400115900144403107108039079054500b5440b849000340003a031962401c02c800751503d45185c8400f00030081e02c41c0c08080000d96004035800b005100308081074101b44030b000c083c2c00307190604580070b904400304220b140d900100300c0701102c9040c0340021f40c3c030802040132074140450540262195203000761a8003805214010607005d00030988824200810500041e05c0d00b002000c008002d410b0244010100c0703040c15001092a45030301c46002800c14030026110403443e0b036000700400068008540117280003e00488072047c2c1020b0304119800303d0140651038031079142406003411070300e10300405036072507201c03004449007540980303056980b1005402c4609a42c0c04040b01c034400064105804100142d024480030000d510 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 969980278 1250 969979028 969979039
    0x10b060f040b0304051c080f090d3906062402030a0305060105040306051906090e1903050c10020c0114090a030c170c011409060601090e0c090603011511010b 69
    0x42c981440d221032070304014800e40d0103016445440044003003c2c854a14600c0e19519422140e003040c0a168101c01801480f03078103607a01c40404480e031150410040070307d51155000c001419140000f415441800300c880e09018030035061134500c200130164000170141c882c40d43d00005218030420000111000002d00c20780503800401180b02c6951081e04415840704041c14010325181c0d9039525407084580803518001c4490010700000e2045085015100c001c090f041010700000c01c461304841d4580e040304613024480c641406660007090702030401d55898543d0441510708a045100010000c0d601007821916103500e040104220b0151283d500d600030301d0510004c14401e03003640e0b0162000d80c401c440c19100d02e24420171516031a01940000e026580c4001c1c00450784000414a131041c941c8041c00480d82e80d000300c401c0000380d9900c040014219025000408504d4558064800d414404c062070300c1d806c10300000010810303d10040716004401c005580342100051403407485170032101d00c1c4080c0c9034000b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 969981528 1250 969980278 969980287
    0x901110711011b0302011b02160501080a06031a0412080c0403200901060f02011503030c080a030f0609021b120d020a0207080f21030408030106141317010b060f 70
    0xa0324210580220101070400c001a070007a0200c0b43c1071280f03000e41c100d00507910b424002002541c16800147d0065184c001401011071940301c40d001401c4500a860402c00075100003001d41c0c01ca6001003001315003106c04050b01c03d484850340b20f4080c8007210242c0e84420008000280b00f482100c0c1280706a44070f0980d24205801d5964a4034404250181ca0209203400b52060500f5602c0b07061060087c00e05445903069105106406420343d01071291010001c4003041c2c0c1080869000030f1201401070f400088103507180d050005c01d900511b81d544031145110310344a00403c40ca501c5600400d0303001e41c0002e03100e401000d007694031580c070307000c020024007290400e2008a1010700760341c0250140c0b181500540304400c0d111071701c05150080444200c4000c1d03102801840343c4001b903150304142c1740c1d48960420b1462070035440d6042584010702c221810002c101d00304114002480c02558102440d889a41b00c405503201403280c2495405040c200c019440c2c65095805c1c0d260281c00c07038419204442c2c019040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 969982778 1250 969981528 969981533
    0x160c021c050f070f180b09070504050a090e280b090d030e011a011b1515080f0c0d0311030d1401090207020a053601030302060609060d0b28021209011107 67
    0x1900e41280300f4129580d211186d00c10981d07140300103948103001c03d80d292921640b42104126038801c02e544980c09a07868141e0b40240303102c001c68080704030040400b010105000f0a01130345200344583d4005006084028244a007641004c40d50a1100702c80d564188426410700890314229040f06003080180d100003d44000f081d40100b001d40003445c43c44445001c08125031301d9031203010454900424010399103c035401d48100014801c1405445500d00924008100d17203038042c1c2d110002c8807018441c0032400e144104052142031091804004c4c2c0042d66101d91401206070040d044044034004e0594851340046a00740082c4260f0710a1ba4006203507801c460316040074001260907000352401101403148201d115404200c242400140d9000044191517155060090400101800e01071140b00a0700501c001a03440381021100186c201d4101c100d6910b0746007590380280200390110030a4200b48044520390740c0568098001000341d042e514107180d468030405030888020b03e11200004000b0701c8114007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 969984028 1250 969982778 969982799
    0x7060222120f0212190614040f080309030d14070e1207030215250b01080111030105041a03060c0706110406080c0f04120b012c160c021c050f070f 64
    0x102da074009450108031184d030b040b665041c064045d0450703041007110b6411600700301a51146c8000340038940d010301c0c2d090400d0b030b542c0360303115031507980c0600401d4000c00440c41c0f080060080f2144441c04072010803540d03504600009261404884201c04a81746000504a5042541c3c0707480b401040031020700307609401e69080044045581000c103144220901c1018245040681e4418040c0124181c10240e84420700e000f9028820581141e0000d9051180d6501d0010700030059074191181118007003405410070020440003030400c400264903100341070500c00180007d01c010000d25020b41014031880700d5080700e440c1c00303105500c5940006544480081d41c2f00030880064000d014004030842d140a9450400500980f060702003910580303810300040200860350f580600c91110841074004c5044180079040308542c030010101040341c0341d03807180081f6075441041200c0356160700503c850581018200800003d544100c0112070520688900600c4d401001507910129400f2418603540036041880c03251 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 969985278 1250 969984028 969984053
    0x11060c030d05180d32070203060109050a2003040b041a270f1213050d0b0601020705090907060309140d0e0109050f13020703090b0706022212 62
    0x194940000c0c000030790003031164000c40d0b01451103080d84003030070900002007900701401104c0b02d80a00035907450803c61864040d030204a15201610001100c0301d0140e002c0409128090380203515008000000c0b65008035a0700207405540310b4401080264202e009410140700c0007007459040d4841070000030005401031031030692040c8104002030b01e003007489818110001e415200101751158004c040c014584000c40c0c9c0e00034a4029400038180c0c9548458420788030f03400b9800c0c03000c2c03d1070000340010202001a5a060003000050a00070310a403070b90919001505080d90a6030050298450001710317803a180c513102d4010001d601c06880d1031880c11000b036008080000b400c4403941c80400d031090032810f0a0016140d01c003800d440c3c030300c084a64600010031003025600154800c402565880c4820b45507600704200d20a600800140e4668542c10241e9000c2d500e603100d00507003e000070b140e404010b6142c0242c02200c40309540002500c08161780c04002030f00a00a8400c0e907401d501c94040800c2c0e01149a0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 969986528 1250 969985278 969985297
    0x5090114070f0c0303030218010903030503240a030516060203124006060803033304110d0b04091122020a0f0908062802041d04060e06041106 62
    0x480c030081c143e8640000e548140e2065002c40d60115a20700c0544403001c0d00c0c8078504007441c010040c00d04540d0003501c28000500311043c1d6518440d549000e00c030007480304290f40c400084c400b4075015541d16020f561035100200310901c5003012400054558000015070f6455170760300d43d402a841d56035144900081d503100d407104072106240d00710007a40d48607540d0071110405505038020640400c03820440140d4000f80d001c0110b075441041001321040403500e1503044c48480204d02031400310204007818041002c401942d6100d450684030101d05404840140b40c5003007155420b01030b0b00c90340e0302003000300c2d5410305001d0078a4004110340f0400f45000020002220f007c2c141201c460009000c2141c100d80000d41303000c002c504c0d03e111801c200d0303801000c40002031401800407d41b61400b01088142003040e41d4400168220b50306201070441da140d0140d6014007030400300350602000c0000c1380c0c010000b064a080d201107203030000d0500344407400704609214542000101885054200c1480071950110740340 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 969987778 1250 969986528 969986543
    0x10b04152301140c10020f0904140405060a0b030c18180109020a060309020d0c031101020f0a020d0605100b0d02041410170a0e01060315051e01150c0803180d0509011407 74
    0x3078052800e01e840a01f20040c00840e0711612104c5041c1803004443d069441648a0b44141c0c04020014800154a40d408804403d000c240400d03004046031904289038801c5901c14100c862411441c2055413205115124094102c0c45540c26040141d0072a6045440690800c9003c542842098040d8015502081c409400000442941d850b41840544c00c1c3d00200d41c0c09030b10110940b030075a410040c0852101c4448064030144605a002417800e817441030000340429141c80c0000c001c0c04880840000812a000290755038202462084001b5070250113801c0703a0030f54881c0300b1007090031b2440301a0301c5003d1a4513200d64445000d041c0c1c2c01c0c204402411201107607101c045107034410800380512401903200d519030a45001a0740c1900051340e4008000b0175809c90070030800c1c40034414500c596811101c0e104030700440036001da13004543c900c0301d501000e402040300005103d00c0c17984010941d82090f18200a0304c00012001d10b084400303118404405000504e0325980c00b08030801c840090059070300ca41c48 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 969989028 1250 969987778 969987793
    0x1b0e0d03120e012013140619110106060906020a11150a03050a0614060403060c050d1a1306081b04061d0a0e0d080414010b04152301140c 60
    0x700312041d03a0640514002907516131001814040102403582581141010a9420414084c4c40c4d00307104c07200c510a6800303465454a00214603118981125200090307200f40300d005541c0750601030000c1d01c0180f03200445603c0d00100103404d52040b40b401007503500b941d0103406208580d03262410184601a601039100112541050103811168000e100c0040380f51404500d03441c25000c80001c54556610003522030206000880780c1d41c1e10038003124150380c3c1c030680c0011407040e1007100301c03028007894a010300813514080781d59200a17401c15015090b407508030307004250150010b507410140d5206214847d082e600410707189104801003580801e640001410004e03401e941d40c041031410902200c016a081c6505005000304444c5030f0107034141c55042d1070001d00000c01200030041440c01c0c01000541203445000700700c240c01000303421085112100038410b10582c0041d204280074141c03644508003a54004901d81a1701d034a4520b08060070b040141c48151310a009211001c401e50300205030311125014428 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 969990278 1250 969989028 969989057
    0x4060e0d030c030501080d050a080a14040f15090804050409020f03010c1806020c0112050703230a0b031902060f390c21010f0509010e011b0e0d03 64
    0x42599034a04841d580411852445000a002c9400c103800800d00b5412000507103c641d60414100c1d100d0961a1524080684d40c0c400010002c00c441903400d50510030364030511043c8013405049190300c034040c04d013000a640c441ea41f00d00486a035a8001400528188420003940c9083d40c000502580094a424000750101c40080c0c01c551641c140840031403888000b4488021002004901801c0507000908444e102c0b41d00103007010f00d5010b00b003201c0c2074807800014490b0340319800240e031054807a8000c01382040200032000b8010b00407200030240d0381c64240316200502d0006010000080701e28402203022596409100e41944039003032a80003110304001ca400101d82050b0311000c20206911a024070322100070782000c00e0003141d101440a6444058030f031103280e50700c00c5880e0204607903000e006101d030103000c0c1d4140074118a480100d0f8041c50700040105e0000d040d0883d542c0c1c030b10030030001c0180701c2d0084800d90800e1900840400040c030305450910300703401c0143d8000b141c0e90181c144003200c0442107 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 969991528 1250 969990278 969990283
    0x114030f010906090c080604030801211401090b0705040b030a020304110904060e1903021b0f0d03030207020a0f032604091b0f080108250b030c2203020105090904060e 73
    0x21041114101e41c0d0310401014421443c10150140031b1100c00b50115051a4030000d2440078180507444008182c030b2010007801c2d0541000804690740301d481c02d910281d241ca5168000d181c0e08006488034a50000014039042c0704808440c15160030b0400b5900f1611544407210080d00020700c00c950014603940301003c0c40e541c403810507204500c280000710300c243d10790702d06908120305482510301641d0203400910000380c02254011280000c05001a001c03d0f01c00c000407040185001442e07004214240e082c01819855002001340c14004c0c0c8070103040c070fa0380325503060341e80d20948000340c04586007446100340c000009a40c014200b0014032490301349500c80300d500045640314548140000c40314444e5002007034002048945d419490706151006603d441880780e25035101c000040181a03116600b07024141e030050441001e003a441c04150380b0b92800d10840301d071650081441e0100c04410500150300c4010484048e810380754103030b6503541044128000d2000c90b00c4040c1044529a882d440c0d90f11312030008 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 969992778 1250 969991528 969991541
    0x309050705060f0d0e011b0c0f14071a070215070f0c24030b300d0e1201051006110102120a0c0e1225090207050307020103060503060f0114030f01 64
    0xb0000f40341d43e180070002038000c465091030308416690410b5000e107540818409001c21082c49802e1810780e0f1109490a44590840008028a600c84260800c0c584480014018099480ca00b9070b5510344501c12001c403040e40140340d0000d500076142d803401d204503560740000c0e2031b40d640f040008100082d41d03569600e00c4030360726030017264176104011400f01c001c0c1040e80c100d583d00c00303203400c041003200c2d400c001041103801c801c086501c1084d111a07603041c201c0c50b41010711120b045c60710203072801c944482c04000e10300094204014401c035820103200e10f4019040c40345c140100c500c4075802c1d51040c504032059601d640011185001950b09001031281000c0c100d103014421381c0e101400040c1c0341024280a0a8983c0c40300341c0320301032002d00c1c0700391100c01c0c00051042024909071025040000c0e002420000803030f000c0d04803905060021038503404119000000d081118800d8906002844c2c441c02890b0307032500208d40d50407a40780340c00010841160426880d28200c0ca020b0107483c292412000c185082d59207 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 969994028 1250 969992778 969992797
    0x1011030c190209012c091f05010e1008031c0f020304060b150c06010b031f060203040815091e011b0e040c02071d0604090f0f0b0108061303030905070506 67
    0x421000c0740e000c42c81c04402c0180900746500d46030310705540e4103200c81e0b50300040c2d0001c000c00d60b41041c04603041020401040305600b513105071403400550585c5449014090030b04ca03103030f02e00000001007114000b407000303964207541c04400210705140701002c02100074032a241c0e00301056070380c82e00d194020000d1400114411409400c01051050340c510902c12007e0440b0340d0041c1c0d1079000d0054104079240070038914110707144201c1d001c0d1a0f403201074815000000402c980003a00e0801040000c803950040060300440e00c00702c003a902c80c0031005004080440c0c04039040c1026411540095110038031001c060b5014200388000003503101207003000c0c4c400c0c80c0d103450102000b0a0060860300b240c1c1c038090042c042d004d0f40c24805400240d01c0d05020101ca5002d070404001003104141c0040c4d032070707200c55012040b900d4104c01440107902e1607080c214120408003500361603550160b4000700311300c007000a513030380964411020360740e031a649910110000d21144c0c02c00c54850180c044006182d94404010340180318 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 969995278 1250 969994028 969994063
    0x1d040606050c12130b1e19110304150f03090c060c06110f12190606051b060103050c0103020d0f02070302031201140d02220e010204060e0109051011030c 67
    0x1440c224158a001030585403000f0545042003000080010b080c0680100c490710822035031142079052016074000320a0542039003120011500c4d515950501c0b104400810442e00d9500904039500e021549910881c0030b0b1804010240c2d05441c0e890344241c0d0501081c1d0032920b0300150103406030b80d0300d00045d00c5a9105400080326000c525043c000d42d40300b44804c2e108103407a958542000b203030b40d8000e640911000106031480c0600020581241ea1a42289140c5001d90403c14582c036034201400c2c91b0480c60070001c0e074041c0744000b2030000780d0000d400343c103994206c00103100303800800700110040d501c000c0309200725549401070442100101e001074012244650051600e03040b44828500c0040f00507842941c0c44e682c0c800341e094160300c41d410701500745901070340c0c020030302504641301d002d00102d10b40c0d058454030725110440940305019400351042c0d40003a91070184005030007004542a41c5e0900407140c0c4104c0420401c2a56402882d444d21815610820b80341040b031240402410040040200071851 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 969996528 1250 969995278 969995287
    0x7020a020316060906051806071b08060a0f050609011e090e0303010806090610050f0d0803040309050a050114030f0915040303090c05040504051b03030d020f04051c050d1d04060605 79
    0x10381c1150760072015001d60711b4410305009a1001351090340c8a1070119900465000800c2c1003407001804030140800c101210349540c4e5955000c155968840499101008a1920600380e4030085203000b060300901004000070056402c01e46141003014072800c030615540440b58002410030447c3c0507401d5070780440f4010b07503101e626010a1303a04007100241036038029000b000c10400c0080c0100a007600762070041c0c40e85002901c8080c0071442041c108007020b810b0740c078040200010540d101001c2001d03101e0076168401072035528001510a00341c5c00308008042d400610018800c584140101c40c1d0100300101114444036044a03980210348068609a0000740c440030040103000070044004010320064030100b0491500d500c40171744851640f40e8018413400c2e5200c203002d007607504006844540340d4000c0115501c0200900300c54056000d4071500b80202900c2c480011803400202c1500c014503040005060304a0a111044030202510080b211040150407440c2e2541e460328400c1030090242502d426694 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 969997778 1250 969996528 969996539
    0x9061e063318040902030d08070210020c0c040f06060e0f04021e0c150c0f1c060909031206060503043804031d0109170708191716080307020a020316 65
    0x4000384003141d40d01030f034288003a40c3c3c0140c40c001000b50001c455850000701d07948407007c00324240080410041d03d55400415080c05448022505e480001c2085400b08125064a061101038072214801e06c8040b400000340b0b5040303810035900528404100400042c40c20b40708000c1404a010182c1c80203c40d5880410b00309001001000221001c0401d05e200b01c2d02840c10311181d06440c401c034500c0c414480c1d0041a0002084906880f44e0b01c01049403a05000043e1079502c0c440040140e182e0550009a000b1400740300d8080510a0070f091720743c1035442c2c03071855036580c0b90140c000700024100302142042e0b001d0040020301125031914100c40406114645040a0034003c0c9504100c002c81c03c8014401001d800550781c00000c00300c101c072030254104040d40d555a01c6ca07800c080c41350380481c031a40160581c0300c441c590305110f002e64852007030314840d800a2007541000f9060242d07050a0400c240b509003c0804110b02c40003850744a8264030490b02e01000c540d0119080080d5420740310210300d608a007d101 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 969999028 1250 969997778 969997807
    0x902010e0613182f1902030c280f0213020d060e0108011e0b2b0c080723280603051803070609050c0a03050609061e0633 53
    0xc01071400b80c0c00d01c900c811031914138000100003094540341c0c4660540024003c01c181041d01d140a22803100d20920080781e000107916544890180c0a040c0510640040c0443c0c009104041c21a03003243c1d1805280c0e03003a034070f03281c0300321130728409030303840284110942117465250004011880c45503201007900c600e400c4a640e1a804180c000f03a07207a9041070040e0b40f02c0740442d83c01888140d8045002b00b0004c4d48031000c52108004007064038a90ba404e00f00078034050505980c10002d96100f00721511701180e90320300035504c4084900502e203800500302e045c4480c42d400141000101c12004109141d40000b0159100801c2d0580000040806e04440100b294a070180301d1a0b42c086400c80702d40203a4003c420101c2d44034400c140b002440c080d501ea199400780041080012040350f0060a2002041e0710303802c0017039550204480ca205d2030300c10000011081c812803a0105413403030300c04d42c00b050162500c01c1044055000c68803001036190002c3c0d200b0394101852038208666142e01801180d854980c1220441c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 970000278 1250 969999028 969999059
    0x201060803040f060216181509061d13030807110c0916023f0f031e061801091a030106060504030302060c0c030322210f1707030902010e0613 62
    0x68204500d010407848440603003c082c00c0c1c0a01c1f1f00011400c1c0524003000704413185410900940340b50940110700c20801d001c842c0d0311040013011559099448400f9a100750f400d41c0b070000c0000300d40c4000305a07014041c40ca042d11030f525801c103480c0381c801920041907000c581242c10340b18145004000c802c2c2c0fa901403214041192500394002000e151580f890401e40c03201040c201c401014156040302e4000042054684051105d861103559060a11a4014811810101e2465154105e0105003145080c60847d03000e000c0f49140c041c040e0f0b00e0102240001c11103842c40c030486118078000428659400e11990700030700200d4440d6030301d61381181002890070900a050100f400d50170880048050320020580c2ea212030411140f034114682c0680f00e45034001e11032002851000d5203422408266552110125400a984d07542111200943c008491440e072014251842c01500e80c041161503210703800800c0c4440c0181403190303038250608d001c200c05920503904020319a02c9800140904002601803c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 970001528 1250 970000278 970000303
    0x41a01030f060e06060f040f0618080604050c0f03010e2a0a0f030f0201050f070b07030c0c020d021009080618070602120405061b06040c060f0906020613030201060803040f0602 77
    0x20031205090001d0f08000f803602400704c5210308404500c580100c0c14101c115405801103200108403d666494090402000c0c10741158010a1088020840400000c0c1c0d40c1e2180e50440024000e2460402c02e2120070f20444e8004c54055480350000010440200071080c40e600d026003418071204100442001c40302d10940490b803180740400c000b00b05100c607031074884040c3e0b50440c1007000c0048907440140c9281c4100031500155280c049564010300c4a40001948111030645092080c0d0b0845001122031580c3c01a0080d0700c69021854070700581080c42882c1c411149908041c190b09844001c2c3d14540101200c04002c2c000c01c00c0300d424800700c0140441002403000d400140000c0110001c1c3d442140182d000d110b0203410003003404100240e0003c0c03c100c0c099031800c103840700c504160030100746203075a5000303280101e441540c442c50203d01c00d0070600100c882e9175015010b10b4442e20f036540725461850400747e04564880301f000c42c2c0440188000c2000f400030074220450f031071401d40068186030449240c0c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 970002778 1250 970001528 970001531
    0x14040f0b07030b0f1005250c05220506060c190212060f01140402070c030609171303020108040516230103050c0306100207360b1c0f02041a01030f 64
    0x1c1c3c0c00a444d0a00d881001c0c000c12103070f645e102540400100d80358090f005020394404204108035000380d0303550121050841c002c070203180d001511881030181151080c081e0000d0380c001d0100400c481e40c5140d0141e078110100600031403030a4040003203140380124440207081007101c07162009085281010040c0c5421191602130046450b183c24080303a0300c40c05100c3c400e065884178091581c25907480c1d044a200d198082e1540154503201d00300900140b504082c11182c1e10719440d8006404c4450342c042d075210401d6420010ba0240c203503401128a00f0000e031044506125030040312012004601c001c201500002186207071719802c091210004107030025009040c0340c5080c0501035098203100849600c000c00b910241d01a40141000300c0c030340040b60b8040000b00b01542c0754414034200011020055000404050000100c00014807049400d0b820126500101b001c11040c00b4107501307280c1003215070003002c542e0b2090145801140c142c441c07820301c015202c090300b0440c100d150b0b00b61041098103605801c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 970004028 1250 970002778 970002791
    0x40608010c020d1112030408030108151b070c0e0a050f160503041106090901090c09140906012a0c150c0203120c010603051b120d0212030a14040f0b0703 67
    0x102940f1000c07404849810050307a091441024501001400c4020340c3c010141a42c80c903090400721950b42081c00303007000c00e010714008640c41c2008041201d0151108900c1c0b41242c08401444212a611102d0100d40d260003440000500ca014a100c40e0300c0303448a0980400d241c5481540580c0383d200040040800201000b41000b80300d41c02b0041c0c0358469405410000003100050000301d9500a0410042d44115480c00116140f8040d030030503038105a040d01d030064a2230b01c2da01224001c1c1e2868800b1034000b00f0000014120758424020038076100089104007e9907102c01802102c030340a0003400b900d1628602000f04408813003034181080341460743c0b410420001e00340e40040e460701c0000e14109403d4102044d100c80c9110294040d0b40190361080880d001d20210721900b24a01c0b1400f5084c80c841c030305041d050b10ba90b080100d09501141d5403030b4007900602c6a421440f88203130f00082c005081c101c1e540c010355054002124159406503004500d00c090300100d501d04204203220080401c001c1604000c03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 970005278 1250 970004028 970004051
    0x90506060a0c0602090607081611150d0f0204080f070303260a0905030d020a03060503070e01060539011401150e0f0414010e100b090108040809010c050102041404060801 74
    0x1a482c62805910110140e6140750703000c0011128001e0a0303000d001a00000b40720015400d069841154281c81590324207070a640382405c1000910400c00010703100102007001645200203030380040101c501401c001401c00d9103074000503140800c40ba040ba00b01c0c0c2e1103410300b803051640010030600841c12200070044108407000c000c401d40d40b0003070f1420803102d4590441600b040700610558540da0b40000e411501c4100c81e040040150609215041c06170094150100340d11b0b1440d41745505030b40d030a4595616294407400701031040c44a0720009885c0c800106615403014010044a180942a650012440d5400c02e00d841002440681c8003135540180742e080850b0858022000a0350b0300c1c004c4544c02400c0140c0c00109003d0441401600812801d40740081002c010b00500e03035000d4030030b25600200546d25074004a40522405c401d05010400c01340004001820f031100400c42880c1c185010140342d04e01e59600381c01d81e001500004000c20805c078000400b0300f054401e0100600381d400090040c2c3c0f0104 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 970006528 1250 970005278 970005287
    0x10c050d02070204060302061909080111121b030a02220f0b0708040f09270b0606070302160620060105060d2f0702040507032c16030507090506060a 65
    0x10204030100c140c0200e4a41c0075981c542d80a580115000b500581d500e80600c0001a8498040305101012801100000c40c140c03205214124420750a07803c400c1c500014140150040f0b4001007402c1d08003110800c0300c150158201000d103008000e40140541c442694071001141602c61010312030802c0d01084040200c3c0c02e006118200701c0e0761001010b1741e41d41e914185240c0610607501314458010320224001030076000c03688414207041060782c4001c1d500105021000403001d80d24000741c00250080049900d515100c0d00034220148640120340003550065400000804603900440108106075840e01c400600310310030202c2c030301000014003030660402001601e540140329015100c01d40c1c1c0d101c6101e8844007041c0403050400460b0703066070200301d1000c2c08031181d030055608a010745d0502000c0b844580c001d0240030a41c83c41c0c01d9003038104038085600c0c036603091605852a00c461183c4814110107401d0007861201070340c05000944041410213840c50203845014055901694081260b1030809502 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 970007778 1250 970006528 970006537
    0x15122436082a0f0c0d080306060f090405040b06123c0708010504030338040b121c0906270312030e0601050a0b1c3b010c05 54
    0xc080c054803080084007000d1622104419840b9148105550580424000030071014101002c2c0480d8088920103091040002d00d011009004130410b102107840e910300103014050205c0910300300d03410031020900282c140c8030145c8003a1250711500080c0561030070611100007403803502030000e0070b84610400c007220000c450501b039101c05041c00d040d40e02d4209502000710070b01c10301e040219190152140740079070080800752001c60110b45031400a000c0480d0010507600740c10440086e0807000f621410301040002400d880442d8050340c4d502e042d811968803031101e01022500100204941d19608040030380c1150345001080a1040c45101004100c3d8885070400b0070540148150503000c0040094080c8000c2d50b400040950200e0706a1560940d8194050500400520120381c2c1d1a640c1e2014410204424042e200d40100200301c880c203021089034050841140341d602c00105130340e824140320011070303c04e003203406800114096161550a00d0490505072048403000f04070219200b000a80b05108 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 970009028 1250 970007778 970007783
    0x110a0c020d140d020303070810030f0b040c0302100906120204050f100c0501050c09190b030703110403060e0a0210090501090e07030b0a0906090f15122436 68
    0x110708001da00b000030001410b8480b285000c03c0720092a007414001e900c94204880750800a20f07690300207442d443c851104002142d03040280f0184c080e0031501c030031100d1103005109a550307402224002005842d04a00d20740e45100a603512104981031080c0100240c040b80da16480c170350700500c400c2c00307030303940b4001c900900b001d00f03c8283c9082184500191030b44d401a02000c0c0c85946000f04002207469004010b10084100321800c0c01000f00307108809080d90202d004440030703804180009041030f40207510a20161501d581d90038142550707607480300192041e00d00300c4a110b0704422040011401c0440d903038602040b850030480c890506000c002032001c4e100d8400c00da8500c0c1c034031000c079921034080d60004503d2031000d02000c500300c0d12440b0f030302c010348040e2150803503003884e2001c41d2a9003140c501c908868103412520031a000380c50f1000303000310f540c4103080699008055a00d50309200d01c1c2d41094580c50f2541d43e1000c595800b107000703084002c6000050034041d0091800c42500b0f8005681001211141d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 970010278 1250 970009028 970009039
    0xa060c030b040e03030f04140d09050a0503010e06010e090102090d0c050a0b0708071709092509061b0812040c150c050c0904050c0a060c050106080d050a0f03020f040e0901110a0c02 79
    0x260703541000d4140014a4071080e80d0350241d803502d1070050742d1050110b0282c0740241d4410013326517031030030302d400c0300c888c0b141e03904503038100c0401405900035507984285c005c4111030000d03040c15060307400240c0310081c0105c00c495140007902d0070441360400e0303484040140300702c2c2c8601d4101585603da41c50148223210005150603050f21102d00c03613010000a54072030381000703084030010b490001c60b040c601c3d485882380780340303005410603140321154820410541035680d103a403469002d0003000141000040500300c1110141400e2001080640c1c103200b1951256000300c072000000ca00e4a81c90080b400e5844200d030041144100c1d240e0041840003500221101040d40c0c0482540c0c1d890400900380505484241e9000348000f000081642d0f000700802d12241c0290001c1028070350b5000300707076541c030601802c2c4004260203000034a0218020340c40c07160743d429107080140c503059220005420543c0260409407140003241c042c4865001c013441207814800b000c010403868906e895074040d04920408000a03c501c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 970011528 1250 970010278 970010281
    0x70b0304080915040e071d28030501140a0c03051005061b19050105011706131a01091a040b06090d030e03010f091b0f090b0d050a060c030b040e03030f 66
    0x2610781900080340000d24010f965182c0341ca8164481c0603100940b9201d002601c3e1a81e000f50480000b02c200d000b0240060a1402c079202240380490001c2308250000380c1115003c1000010131020b0140f5000400d072003042011510340006000129050300f02c850003054500020840d131511040f45000949100700e03451a11034000074242c3d03e03290901d44010b403e40c0039a1945900500c1ca5064100405224400078400c60ba00c0c4e40d422490158224000d000550210300030030940fa60440080080300e0080c4d180b0400a00002c0015403500b102380d00c146003c80c0d513180c0d848a620110f11840c080039030116000d005181c41c1400040c4580555140a440703032141c81c0c0480105130041500c2160303e40094002c1c00300103401200400207003007202064a5242e64148512002070b500010f220a0300c1c0801410300f00c00c4d0508501138018039100a0b002d400070304504012010400800035080070078031508000c14680c0001d003004040c9c801003411580903e003003681080c0c03c0d000c0801520b0f0300c0380d060944154075 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 970012778 1250 970011528 970011547
    0x3090b031009240e1503031606020307020f06040b06010f0807120b0d2a050d1a06042a0912020d0b070302040f0306050a0506010824190611010e070b030408 68
    0x50f8010900071690310842d000c0010b8801901200c644c0308001c0a080c1c070704d00f0440741c002c0c580c51380b240c018485c144408403544400000c82c50390145030804a50702c1120445001c40d40203d160981c141c2e0251801141c0c03000300404d540e844070681405282c4c61030a8506410040800b40c2160f1003205030006840d110141d005a9442e40310250144503003000c6211442c050107404440d1088014800399201541250042082d0508c1c03181a51a02d40c008042051010f407801c030424280e10140085d0b50040e00c2e81c450f00200380b5000003041803407030581e64480546c11050310140140025034441149240d107130321804090b980d0070b4605002103811410001c0986d40c1d100e8110000e11071a003049020604002c03012041c400b02e0b0380160710841d40d6071402c0089444400c015100041e003100c8503001101102c0c01c8440790b043e0140841340028014041d1402080d92821003851950745030050000100c0191a1981c840340074081c100080800030094541d490030700300307640c80920000740041d00407440001c0c6142e0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 970014028 1250 970012778 970012811
    0xb06010f0323010f05030309090f0408130b0a110601051c0c052d03160312021518071203021c090504090c06032a031e0507080403090b031009 62
    0x206030098400c102c40c00700302c540804040d01002c0c020485503006540e80880c60742400011202e030844005c000c1c40c810741d03900341111070600004000b11098441030008102024100303071424041d01d4202e405580319242003100610499140250840941c0001c004004030340307801526500d03000a82c210b05566002906001c031050140c1d074866900030144160811503a0920b8496100c0400c045400041c01443e110401d561140010342d00140140018002c10003c0c0c0005100e000220040c01038401c8a019841045502d060848005440da10a054040c603036039000d00022002e401140000c0e8a00c00090318000d40d1003a05103410016500700c200802005030240442c20010140280107100d50059440c06000c0c0b03505611804010030304080007940e18107001c03074100340240b124803d000c0b984001540708501415410041503000301d500c8801d002c11854500a0501c40c1e019078990fa00c060415140003050301e11560310802c08510103106000c0d001016070440012140022004607404150108480 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 970015278 1250 970014028 970014041
    0x60a030f02041502151803090d02010c0c090f0e01021206040c09180f06060305040201270906120309050907020309040506121b0910080705040f0905070603020d0c0c0b06010f03 77
    0x1148002d4040c02900f080e800980c1640d80300760410401c603d510b80d81d01000340c000307801c41c001c00e5640047c410344255050505520140600502d44110005000d49510f10701c6440740d005040380c181c8400150350010359030300a072299141220003c5140580c8240e9a2040102c040d244c20701c10341d1100100c0b61290702c01e000d09405800014140e40ba0f85d100c0c40c00c4d543c000c04801007a03074080b505150000a402d0301900c00ca501c03890301a11086a6402c443c800c0e501141114018001c0000e0309800118012000348201409840303000c8049010f100181000b60500960380c3c0640e01c01c1c081c000c02c02c058a980030054a224410a03940422641c803200d0028841d044902c0c5425030078425202011104030600d515509c1c008800c0e9281d4501c0d49844102e00f0150619000b8003c103035201179402c01c49401e00f58801005a080b00600040c0c0c032415a0b02c1d941002e51303540c081d0000a0b00824181c40740c0c211071013001c2a184986c10190041030030790b610000305a000404a07811f010741003000d609024007030380050 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 970016528 1250 970015278 970015289
    0x5060c0a060b0f1003020903071d07120204080a080d0b030706140c0309130219021618090204060f0906050f0a0b091f03060e01080a08090d060b09040812060d02060a030f0204 76
    0x300130000000000c009402c0001d00500c28411520001500328a070903420301c082c0c81d641003c030100ea0310b5a03400d03202201d5203801a17814503804c0200107a43e04061100b115030601c600002c5079160500488072013620340d0010020300c2074020007410011039030000c140d100c11602084425803a000c2c601c90040c118002c020065401405109806d003611243d03900070b2802c00d0030050f8010105914440882e07035011090302e5080d222103c2079090019440b40c0d1003091550303400a8022840c1075450703000c2010754142c1d50040d0801b404da01010310060102c0d000b81d0004d0282174584200100d5602c1c0042c2e001d07611445440e5070840000744d05a20342e121030345958004c078201c900d200215810108001c008043d58460303103c0d500368100000c1680d0703c0c0882c2542e41d10340c00a8180f410301401108010300d0324010f001c1194607550381e810982940e10303200d414a02c154006c03074030307551651104040003902040041400388a8000d4040b4880140d4920040d110900028900014081c7c0745c0e030f98801c002d01c00ca8201 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 970017778 1250 970016528 970016539
    0x3060711010207021c060c031116020307031a01030c0e0903040605070f0f0503190201021303140a05070602010606031d0607030c050d050c0a02010b030304030f020d0213140603010605060c0a060b0f 86
    0x200281e107514600aa1a40344215420010781c40441f6045044400e4400c0c020700900d002c006400074040404944011180010207032660141e60359a600d00c040d00e0000501c08095400004005003c0b079003e0f0b00c4020054001a90200c3c6054a01962a4401d502402052209c04601d150a1207641c10009610b41d0784842c1042003084a030500c1c50340d13074105148212100003100d000314225403040c0251707081c254034080003041d42d84c1155100503952103480010040380c03290f40180800f02c1d904000712401421b55800000d84141005001800d0b56852090088604030407010030f01a0003001841e50303440303e0f0600e4002000b103841d01c8122090320402080070085030404050207100000351005124400c0c098000f0484e6488600134145c40e07000301c0c80301421942d251040140542070489604507668402400d040003007020344102c1d0116401d2100c5040c0c4401c50004114550078240319690282c03d00f210080e080268400350240e40c1d180c16440140455114406500d094a40704407100710200c2c000c00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 970019028 1250 970017778 970017799
    0x50405061c0906150603020414090901200901020610030305030f060a080d031506030b130519050103120f142502120a060f06050904021e0910061404050306071101020702 74
    0x10004050000020710b913001e07070050300c00012a41e020b0f108a03022105030400c094424a240310401c200003a0080c2004640d5490300f400010041e42d000c4000e6001c1b01e03080318540c0f200140b0000900d4420020f00f003020f40c10070790206001080d046400d980e4400c024a10520803a0f03241400b0404084065220340c640e07100741481490302580540007480c140800340700c1c102c00c250362548200d060b11645011140c003d0342c10a40c6550046140d040951301881c00c0d544440e902030341580780300c12660240d0040e01c4412218039421840c9074050f440c10703404040e40c41c040490058550703c2d280a4424030000304200c00c92284210750354560883e01c180726503001800e0812402e03140c011207803109076010007111294030380040e10260035600e1160505480d00030700b4180b200c0d0703141d90a101c2990301550f640003400420300000c1e079050b5640349000d4841d42021914000d03507440d241000e000c00c190004500000d0300180b00910440d180000c4169104802e8900080a07011750400310f4020f00c900b15000e50440c040d000d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 970020278 1250 970019028 970019033
    0x150e01050f0a020708030c101506360905150301140619080106030308010f061e08040201180b0c0c030f06150a090507030501180b090c03060423040203160303050405061c09 75
    0x22030392030810003080244029027154001914811560007070701c0c045088070141600e041082e80c2d0303907842141503aa9120b10020854004040c0d00300c0b5510100c0d03030b2502c89041004a00b0b01000e00c85c036451066000b40300c0800e00d91007a40ba440ca0003030109000306255105144544018003c001c028036028008000b000d80307074140200f041000740500c86458411400000f4102d110301520611094040781241449007041003c5924800180043e4100407058940005410b01c02510360018104401200e03a80c1c017450700742d80d00f07050400007801d20075004030480e084040c1000c40c05981c403040c2500b980d200380c4800306c0003803580035850704040c414610f8603013040075440d00b66100606032024400c0304100015490041c00036113400540107908210001c0c0030a400b040800003554111500030804205031403454408107004107401070203c058004003083c041581800d01101d8101040300c4c0348040c500d41191006000c40c4038504c5400d00504002880c450041c07001500859030504110b81405001070030f0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 970021528 1250 970020278 970020283
    0x406083f18120607140f040801020d0e0d0c08070b07030915090312050910050403020309220b032a01032a030c02010506030d030207110409080301150e01050f0a020708030c 75
    0x1401110b01540305110344151126000030214400c1d006a0740d40a10700309204010b521907084100d010249503428440411003560a002404482441480c005540a4100380141c54209484050410b100164840c0c2c00810090001c490000d80c11180d00d0925803600c140480c010141213030080d01003c1030125040e003481036900103019140c0255201d4000320024802181240c2d010345d4030182c81d40c40340041c025103c469170402a80140a0b0064a08100390303880868000e4078401c0070501ea83e040301440111030b100a12a852041901350b000302100450b0100800942100000f44002ca441ca054400c2241e88240c208107035410f42e0f081c0c4501c00b21030740c24010074400c44080c4c03840042803c00411010051051040d684510740050040030050140e6100b50000d511600c82521000c00303141030022241c503980101c4601038828036441f940d1750301d01401030b0080350006001004020406c0d9105119a82c01070a4510080c0c480c0d01d07040ea5020000d1007680383c1045640007007014003002c43c1c06071a40350301 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 970022778 1250 970021528 970021567
    0x80c070c0b0a0e1c02010c0c03021e150a0504060c141f0c020f0c221107020a08030a02150a090c0332250b03090a020406083f 55
    0x2600c8420316065403004002d04c0c5002c1900e050031002c0c41001c4200990b1250f0307506070311240540c001500598403070b0081103448032500851070851a01850000ca18144031203840c44c14007002c4496400d124203c4002001440f6910400f000c20802d846002e0a0000362030301140480c0481d4200c49486d190104090311f9003a42c2420f00e1051031a001c3c8141c400360021541c010140095005400704500003410802e066141060000651800c000c04c0c101c0b5104a10a44111261041e0f9150301e450403481007210100ca9500300e00b85130b070424050300083c1d0b03400195000c011542003e071300c401075039120341200080c001110007070900794000d0400418007103a139040b100303404a01d6014040340001c40114902c80018607000c1426135001c00118000c900642d1312000c05541001c542c0322126583d25403906050f001920860400e411951400b02189807501c2400010103d80002d840c0325a00031051b484400606480e200c6090060502010035841c0c080000c200c22940710106d03521841801c4462109507103 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 970024028 1250 970022778 970022797
    0x708150106080f191a0402210c0a09060815040212041103070f0b250506010e010e13110105130902121810020c0a0c1503050c0f0901080c070c0b 63
    0x40c00380119000b05840d0f2600c1d40705150154071940c81401800002c00100740c05508200003100c182d281307400030394860008200098401603840075242d14000380c1c0c070180718042c241c048408003c00c690400700b500f000c450000c45025007480e8105035205400c0001141c9081c40d002d91041c0300007030f0501106200a4003601441c001c0c80c410080c009998107040c0e1702d140c40d008201d840c20b2149410062070340603c0c0240580c41012140b40c242c0100e501122a00444190045401e600010300602c400d03620300a041b401000300c907402e00c5080c200881d210300303220f42600f00034244015400540000fa4028000c4880180648842540d019a034129060007900280402968070b028900443e500c03100d00c550003034043c1021400340c140c413403108000c14000d50120f59804c089000e03080311080070821113070842d40109031803041d4600385250944010110b1384014a2148860014414013890350510810740302640403c0c00e10540f039846082c02c0020302c2c0640c00004050351007100000c1040031012018285415 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 970025278 1250 970024028 970024037
    0x30b0403020f0c0616020411040302030f0a140106030c0605310609050d110d050a02100302191d0d05070503101e02040b070803061c1415090307140708150106 69
    0xc05007800c01c0302c2171207070341d82445e40341078607040fa4805403510380e101a6210603080055460316660390301003800d001801948080540000410809120724207011600c05204000200681c23810b50742e509a0340480c500031502040300102c3c204c514405400e81d0b9280184060003820080c6900300d09000c3e400500340210301c000307081c01000040ca030500d40d440c1800c40f07074000d0604084050b00c1050084041c0082802c1c0d40d58416045001d0150f10307202e44a8408000710341e00503980d1410b119030700001c5000000e900b010061041d841000e203591a008440c000c480481c1c401e0f00c001e031103041503490080300750440ca60602469241c402a0b50303050380221141c03211031135880524080e00200d401240110b101700d28143d4020040300f00000c1c60f00006641c0078030010220000402d442c0030400d0030810f56482100c4e0f001c0f00b06401544100100401d407448800104069034034a80002c140ea207034041c1d0311000b45602c0c080c4c03c034443c982c101032000001404141b000c80d0500d03804889020894182840b034003003c81d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 970026528 1250 970025278 970025293
    0x406180b01082509111201031b0816090f020909010b07060c090f06050f0f0a0306090e030f0f03090703050d03020a030b010e011b0606120b090f010203042604030b0403020f 75
    0x11149802012104061070084565504e4101c0c0c60014050b403e81c506401c2004000d0b01c10404070001c0c40a02a500401c2041d600040f000c4400c007a003403c9030001d950a6004604d0202080d54a4000c2401c1d0380362860041595201385540b000640200d5030244d070700c0488180007150b800c00e00000303000070030b0041006200f2100340010589103c80f5074054620816440241800140d00480051116903180380f185441c140422051b103030309410150010000030f131078000c1000a803005001e1014011801e03405076103041e8070740c500140c061007070701070020f03050b10301000041d07030a1002e0061710010340c0c0140540d041c40040240042c000d500003164040461b2400240b0341c8254840d17012601e40010603105c01420b044c60901824400342506005c0310310980340c44020034010320740d1032007414082c4540c60307480e154280190a01c3c00c000c1c3c92182c00c19181c1c814010040850702c0f041806444c40d110003402d69000d1000c2d0028100b51103a0f0304040e240e4910b10b024001010b5000881d500312046040036200d0390b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 970027778 1250 970026528 970026553
    0x2b1b08060301141b1c021c0b03070503030d091e0f0c060c0201080621030408240f13140a12020f0a080f0a0903140a03021005130b0406180b0108 63
    0x583c5025620642c9030f000705140400c0040180c4024001602c00040902c0d43d0383c4520a450b0580e030050150030b1411540303242031460740c0550f00401c0540ea1085014111241c00d00021030f0ba01e000f00c003215050607464072031070030500031400c052511100704008018445c0c1c150742002a4002115601201c1c1c40c22031200010f206845180008105030b8140e41c0e4545036101c800030000d404141e28000d20f4822582c40c031007241a041000100020500304020b00804102c01d00081090b001483c00e02200f14640010424a10110049aa800040b5000f03285080c0030342d05169050071202809a680b0303104090101c01071107445c0006a5000c1c0c4658200c1d14450310300c403103040d11007000404c000d04d0342105110501c180c0b101c4001401d0300c88454540912119642c0d00c907400b108c42041c481300c0003a00040500b40c18590306001307021080c0c2031800f050007a800c11036100c0006155a0401900040c9010081001c00105420180e10301284010030900094207080900c8400303c28030861116101d103026143c41e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 970029028 1250 970027778 970027811
    0x19140609070501201c020d1403070c0c0807030b0402131407030c111c09060c08090f04020f12010602010605030a050307060b010513080f01112b1b08060301 68
    0x490300140d0040d004040c0340c040155001c0c07244138100360060180140403801034008004003800035140c5801c041c00c0345ca41e0000681040101c0003043d0420410341d49025580b10b098048a8002a1900d0310490706452070516400380152604040041d0082c0500001031000e0181c82da03010764022544100411086440903080b2200200251040d01018000421440c020781c441c2d60720f00c600342018101000b01d000c41c01d0401d5441d401040c0d5941000041940e10f55101212402510260904402030a0603450b6907095004162036588200c40d484a41a4962202c0c0c054860101c4000006d1ba16410954070300c250400090081000640c6002000696807900040f0454240d82101c0914038101c00d58a030800508150155181402401c100b40b08040100c40f06040050801e200a400442502201242541c05103909007400d03070810b0091081d019a01960318914444220602d04420080b100d4a0043d0503c03c1307481001910060001460075007141040d40300d0030040700200036041c442210710381c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 970030278 1250 970029028 970029031
    0x3040203060411040b0a06120c090b1e1b010b10180506071115031608011a0c120d0609141312030b03030a030b090702010504030e100c05191406 63
    0x29850740c4480086008180580140d00c3c03510320291010030151200d60111740140526445080003030b5025204010f401e2041c0310700000c2140ea85408821549005164035490041d09000d85441d550b508200065680180c1203940704051809100001d28020503041d00810000900f20f00400320380e0807255010f0f1241201040141005100c001001d04201c248031045e04100c40031503401c40b10030222000e981d10113103400d403040c116a034241d07175a05e0101c07c1c901e445100c03041c10703030180550305005010701000c00328210140518085166107418144070100e241c09510080c9403c80d28000030844948020381c0c10800c00d0b620340a00520280404031408140d681c0300302e0f00d1100134209640210006848c8031140d07140100c880c0b0303020580102c1c220000c0d04561081000340046a50b0715201c00f50303420a00ca0a651010303d0340020421803606071806030525084071001407081501e1030040010354000c103116026560000202d50135800c1c80010300701d003200c0481080c4c44a5907149030060a00c0400584103 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 970031528 1250 970030278 970030283
    0x250e0a1203022e0207050321190b010807050a210e1902031c120e0c0a0b0703020c09091501030605090c06040b0a030b150703030603030809070609142b020310020304 72
    0x31400c00e444203e4100079085003404403074901042041c50740358108500c0c10704800c00c4d4020380824500301204035010102c210f4060340708482c145550f501c0c45d030b07030050030060740503189060459880d00f00c0c2004031741596a04c8001d03585018100071042d040801da9212010b1005c0d503404840300080f0ba01c0020b031122003d0b000003136140c0d01c2203000c400c140741000344100e81c04641b41084214030f65030486d107100790b800308800903210b940050701007581458040903d400904179004181e04d004040d0310b00039155481c0c20b503110f001c2d0911038041014050b0070040d444040d0045210144a96102e2610002806040e210403072a0710402d9245d02203454440700b2502200c2d0f82340d050a250034002c420640107003116900c000c0c0d01c82e03020030340c40c10032400c003200820310148603981c0055040c1c01d510700036042a00c017030071186d11688102000c1c004207030004c543d00f0548111004e54941640d40b2400204c8000f40c800c4011a884c0c0c0084041112860400e101080c051084050301d07030440100306104100d000484c2e01 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 970032778 1250 970031528 970031593
    0xb0304061109060f0a030b011d0d0302070801020f07051509151b040315060608060a0506071b060f11060f0106080910020a1d040203250e0a120302 64
    0x104001908a40c4103421003491401d49a040c0740760b03a400100d05800c00b031000b400907000054240d910507410700c2841012002401d02900d8000c40e800340705007220410200900410340c2400000515000b040344000908040c3c0081d5568080ca100084007a000410129003a10034408240b40e4102880451841558a04000d180c424140310a800e403501c0007500303907501d2216440b10314081c0f00100c0c004201070b46c001c0c030070b07054a4802c54804000300d44440e44510100b00655052100543d1044000b00440d1011564951200c40c1410070146007055605000c44050882c040080e4007a0040c071524451000745d151110040c8140d20355585480c01100d2052039500c5410040c041c0354000c01d0116040400b00e000c6404031f841c40901442241c0c441a0b158002c20869205072030707886103a00080045c010300b5601035041d810100c00068858043d5100d80c1500700d0440704100205118070001c0c64880c1005284a0040e907581c1500c0c02d071008107110590043c01803984100c0e81004440307071070441c60000c620 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 970034028 1250 970032778 970032781
    0x2d0b06030a05151e01120506150a05060c0102040504061205060a0b060306270a0509070f030b010605031305060a09230d05030915010e0105011e080f0a0608010f0e0607090b03 76
    0x3e9004003088003d182c40850b0a01c0f06540b41809906118280a003204980d07004810605042080c60400000c01944000001401c0403413261511400c45c3c013150006e851440c1c0b14500f950346140a406141c003c0ca0308980341402c00070301d030110714092401c0d460181007694400e8a98803215019103072007000464000c0000c102040c00c6041204041044201c0d08580751010484440450b003401d1094801401c601c0c0c03110140300c0900c1d0180143c00003011420031000304946590782e842990201480b902013840004400075860503200410425070540c800207507220b610300b01320404020f100d80c01e03055660811040e8040e0406802041c000307000038640000380100d40c42c084003121b40394401400c901c44c501515081c0c54101d101880400d01810031031141420720360401c0d0004140d4260b0315000c185060100c40c203120400d401100c41c507003181000003010980d5440d00001c1c0d01031709a41d4000100d07980303803140c000e04222807640030540d4524003030150303400354881c4c3c00102d134a45094000e240d0724040400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 970035278 1250 970034028 970034053
    0x60b060f070f03050c010c0c170903060a0203060402040f0e0415091e0212010f1a150409020304110904081209030901090b0309100c09081c0503040204092d0b06030a05 73
    0x5200b40d02ca244030b49003040c900742140701c0003801d680074142504086003080d44110100040c151400c1000146031454a040140402c0041d660312030240103020010341c0040403489544442c4c0448014020403121000c1c002e581e0080800106000c0310705646c5001c111107400310340281d40c01841e61544c0c21021249001d40b40c40039940d511000c50000326448401c12001c4c491540c0c00303004640044411880007e10644018030407090208115589031040042855083d69010350b03506580c20703108502c070011789a580d18a0701c0c5501000c1d04002a500540c1c2d00104000c000c0e10000800e004401c01803110550b84800080607613901803010581c0c04030341080e0041c00315603051000745904c845040c0448000c210b4480d0b03004100c41088501000040d602c40060200da03400b041070000c940005400d5480c8050b80200003850740c080600000d00c00d50b25000c0d1709040c80344412011581100b60461445d43c1115000d10383d400c10078000301220712440c1d8100068003440c0100300151002e800101030040701076103d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 970036528 1250 970035278 970035293
    0x13120207181104061d13090506130b011a0c0a151d070515040906030305030106081006080c0702030f1002030a0c0203040b0304061508030a1805031606111216060b060f07 74
    0x191170320301d0315110145038080160b030b40030340c650541901c0754800034a10800d82425410500003c1039850321581031032840700050031441074603045a0307400034500510744201e480311896100741100b1120318880d90580c10140805014142600105420700708510340c03001d0680d003140c070f207204031758292900300f00c504204605121180900055941200c40d2516403188056411550940c20540005801000500200b82c0005c4820742082c0283c3e40d4900851500c00000c1503010b0040100c010940041ba4410864504010340811a00824142d422290740243d82800030f40089440031030460911400401540c00030003241e054814445203a0b04d5640c0b903480d1400501446003402d44030281600700080c0d4104217001404103549107a44582c024094a01403568282194005500c0b9402a003130350034024802940300d00c112219400c0036508041c0c040c5125040c210400c1100310390030300005800305044416000ca0840310b01c522010083c41c5040003d00108c2e0164038404454002c00b04108070119600 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 970037778 1250 970036528 970036547
    0xf1a06030613060c11070b0702010305061f0e1809210c061807030219091a0102100e011d0a140d02030a11070302151201050111151312020718110406 65
    0x83c2800201705215400070381c649403066210601c0790f4000301d216801c560707041c020b544d00084103e4020f00c3d241d40603020740b01c106c050b42100a0134000d009181c1001601c90801000900c004410b5150051400703003405902d900d0484030000b0f0a20100700606040c2010390b081c3c54000000070006c11241d95460b80141c103122034590503403034a12600c0340c0000141d0b1610318030b01d1100008a906014289054100019103421031001090803801410100b8141d900080448620250160100e0300c444608101030042c550b0840c00904250002e4841402d07080c000f82000003640b2811000e0504071511180310b484503005002080184c00401c02c004102d4441c030350f414513442d1120140c521169480d40091900e02d1440311090701488040381c40d038624032140602c1c60041a00b03003003d07071a41d00c0103920503440c1d6007404007000300c810007076000c605080c001070750070a581c0c1c0d13102c001582c0314091041d0113580c950b917a00c074130008284c0c5000d2070114084c3d24007510000aa002c250181064100070060380d01d00f20 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 970039028 1250 970037778 970037801
    0x60216050f030a200a2f0f0603150f030111310b03090123011502010b01080601110102040807091d0705010c150b0910050f090118020f070f1a0603061306 67
    0x301c481700b0b40401e5604540d40da4040319049400000c0c0b038400c10740000c00c010f81c005280301d4610340ca8008526240e000c1200d9015100800700b4444201110000386c5022031090b10503010741c42d0890001800700b42c000184515400c5104128107607a6029440c490134009503000440c40100e0756041100c0d201303410185800007042000401c2e442038083c06040c10449104d0380d042c2c206c8525004124415203c41002c01c012001e100900294201e800003030700070900a002c007410441c4007181c0c05030300c030029416540500140c40503105440d0780e40c8040030181c00040031522290301b04500c42d2464040005009080b240d040c0c4036100304c1c0249441e072022041440a044645c01e444001d0068150740f11510144110281502084064280800e100394801e9410406001c0c40b0070800500c0f411086c880d08403d4041120405a51455441c0400c0301a009001000300f41d59645440c2d0340130007550f1200384100703c501a4606449584950400d56a100e090b80c2c0c55845c1c206d4803070700e180070401b250441c403070029 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 970040278 1250 970039028 970039033
    0x703030903120e0705150307020c1e042306060c060a0903090e04210f120c020a0209130219060e010f02240a061403030421060216050f030a20 62
    0x50350018a0426180307a45640e941940103860240858a13201403603000f020f106e030600f6030031441e010501070f607242440403e00f846400384007185500d64000101c010311090300600140001070001c00c84196510f864003c00032500103190024045e42404005e90345400042801088140c880722480320050800303940c00e0301044044500030800500c41c00b00d45003d94800d075212103680b60001c141444410600c0098001c201013202c020011a50140c150070280900c044002580d040040d8107a03c4c06580010003900046400108842c030b41101304600003650081d1a005441032100b845807294841342d000303600c04612141c04090307182d446101d8041e50322640e0300494807001c8414000180d1001d1002c03903203295a09510420605410500a01009224903e41a600307410a0000240c07a1300450060590b00103040300014a10180d01c0d05107080740d07410100171540c50034502d88000510814603410b0f1031511680910a08145002085442c2c9540c0c0b03650700100301c00c0062241d4a032800d074004003100ca2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 970041528 1250 970040278 970040297
    0x1c0503060d060c02030c010b030d09051c060e1b0102030f0d0527100b030c010e01051e0a0c0501150605041e180506010f1107030830010f0e010b0703030903 68
    0x203060b48070b0b20f54040d20a07001161641c0350111701e00c0c02d43d86400517060003504604d01d440f800b0303904601143e0039039104031006c0381024510943c5c450600718985024244a0901c0002c101c10400401c941044400107001d400030109a08010b90b90b03031082070040b00f2a03140c10812100440119400030790041260340a01f00c69042d0174402e00865100301058a001d50415101504c1d6464584104480c6510640281213203a0a40001800124058060b1418460001481032440c0101000030000d071089584032512003404010042091500403c220341c65881c1244030340d103c9400d050844100d80c41035032014601810311108000072400407404c000b01405428002c00c050410040f44000c9000110000590380f8016000600b480001c2e40101c050110624407031040c101c002c201c0000390391300541000d64030100032000482184402c41d4640000c0300e41540c1015040071706440034100c80349c0a03030b55000c003511001ea03414050000c1c40b8140408000300720200009000e0340200d4140d5000e03040800ca07a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 970042778 1250 970041528 970041533
    0x2100f0b040e031803150a090c0e090307120806090403140922140f07030b0f0d0c0603061707050d17070602031e060607020103050c0d0204091a031c0503060d 69
    0x180c1d070b080c07000c2d0402e80d0030100d00c0b0080f81d050712280002da2842140200311100c401d4200d00511075003c1c007140c0300d0a407184d6070702c400c0c05000101d1030700030f02e0301b81c0301d9881619051058a440e60840e003400c94000340c0078201002c0c414490320001d40140c03c001c2904001e6121658181ca6a8421068140380380d00d060200720080d07a90112030051071411200d03280f10004100200f50b003102c00407042350784042d0008080c42001d2842d0711800b0781c441100d040020f446141900024051004041140d6000002e00411130400c25a401c2042c01c445a5840c1444070649402121220015085000c4500c0d480054200210310b81a03045088043c003030082c0c00045046051454841c1e8007401c0b0070340f1101d40002c00e10070b100b40c0e400d800090b0030612032204003440c1044800500e5a10a01102904150711507003c10980103200382109c0007409a100115a03071940c1c4d09040c0023400e440301086c0b0400e002c10342604414180800e01c0d8005004181e040100441c200c5015035041c2c1002d4010f9410082041c1c22000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 970044028 1250 970042778 970042781
    0x1017061002011d0106050f1c0303090203071a120901050603250503060c180d030c151d0a171e0a0c02210d110606040902060904050a0b09011502100f0b04 67
    0x200340500fa001040c0daa0418046c0048902c680c41d05074003a100310581d1034680b81e1000000444613900d480c010426600b9030000038904042c0c0c2c0c120000350464091025055058036004121135102c1c1c2c000c0301c1050352088400e500300d07030342121015019001100b106011082a85205034000907403004801c03115250004a4074080382200e10b10328440e400268445900746211110403614003c480e00c20b0071600300d030350050502601c00001040c4c0a041d02e5205e0302d50382c4e142c101e40d480740fa1400080c0c404c1c180703030002d40d6914004081d040e05c1801c9407a41e2042c031546c00d202143d012203140407141c2600c03019041c5180169010240b80800c1181103c0b04200580c0e85229179075600011801100003860003040083c100030b059080107080c099220486551004081055644040c00720340010741040da900105a60740710f24075009a000c1d18000c1000a008001c0d0301903c02c042050b90210f8181c1e0703c4c1e001d05844040440304800150340180d0001a000b0802c2c0c010042c000105080401c20710541d001060 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 970045278 1250 970044028 970044071
    0x7080c01060f030215160809030a1b1d060612180a03020102030f090d020714181006021c0801031121010c03050a060501050315060408030307020309101706100201 71
    0x80344802e282c00800c194505101c0d820303030713000402e4030345c915102e8841c1051441c0b05410070000d10500e004124141c45940903c442c0035080e410040c54425540b149a640804030400d0185410342001c1082810126800c204554403c000180400303240a021903000054280000e006041c40100b48810111000e001d1108135802403198002580740c2c20518803000050400808901c002e6001030341030841e155000510f60110784e01441c0c844d000020070408580c1a180d07116140c00d001504c0320600c44e0101e9000301a03421900107509503800c0c600d005451003040b4041c400d4140002d00e81c1d1005101044011000c01c60300d050003801001e109110030171010703c4031076400461020b65074410054001a805002d80361b407050103200d0402406013400006071150001030018030a0140d1483d800c0170359142e0300100d9001d01401001c407038613890000d034000d54a03030040c021540074081c40034142c20300e14000e805075002400789401845403aa110001c1c450912500b00040e801c6640b914100b45480560f40c2c0b404 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 970046528 1250 970045278 970045289
    0x30606270123091302040504150306050c090a030b0604090f080a0806090613180512040305070902040e040b0601020a0804080a0201020c0312120709050901060507030806040603050d0507080c0106 85
    0x81480c0112000050100061421054107800c0c201c02403403408910882101c50301907003101c50b800c0494903480e06000902894000c4c5822600d05901c203031610079012601d00c1201e22070070b0184810381d034103107500c920790007003074600340c3c1008191500f840040c03544160103501810162001500c05861b4403111945440040c0681e032580000510510b43d0344e00144079030780030105666658080c00c0c000d0200d0b0400004402c00c000d00c541d514810035030f04202c0c58150200641041c2180c10188000c1040c002e9030303006e0310046803a4031032440700144200e003900035036007110040040120295616210058190401010b050443c02625180800200c4d50300c09480505030400017001090070034130001e460501c20200b610702c03940c00800c0000348010480102d521424210140107800d8540d540c0598040c0451f81115610145000001c034050b580f01c406044040d0081e540da040545400c1d048c031040740e4140c000a00290007a480c5121480d00910041007070324401c5da85240781c4a00842507500f101d034240c005 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 970047778 1250 970046528 970046587
    0x5010e270f040b060103050c0a030209010c050f01060e1008070302062b1b020f0c0d022707030501060f02060a02130305010e0d18350f06060102010f090f020402030606 73
    0x5010500280c6020306134000c00c2803c04001c02d0504521340b9446002e4044103000b0541c0000e01190583d119445502c00c456110044680c3d15004400c880c1c080e00250154000c148134032000543c6140c1010b8100085070441c2c005000d00320700b150240612a4841450000751120b99040f01000000341d051440c5000101800003604140d01030581c11038240088502c01154080d42c00d5007520b0f4004201380d8100d00040320100c40115561001c180b5161038005494003002c601402151a034680b4001c50784180403030b6808005980e2100030542d194603144200c1d90041e440000098001131150307005040001100c888034a5141d5241e0301c1a080d0b0b03444ca0341c0905150400714a00f0102078100700824015101002d10b204403a0400e000c450782e2440762100c84061b00150110051050100c0414801030011441901d140c00c1100441564a000c1a500c41c0d0040d8640300c200c0800310094070450308181d9003c4000c4854295036020040690000343c27031b02e42d124404210303a10046600c040030510a0381400d81 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 970049028 1250 970047778 970047781
    0x60b030411090604111b0f100606081015080a0b13020429030703020304031e1106010b0f0f07080c160317040609031b050a0f08070f05010e270f 63
    0xb44812454003502c00c9000300c1c20442c40380b0a031300e0004195100c05044030800380c0c0c541b40d400c00c6a80381507142040409107005010070360b84c03220600d4005006403002511194455191000700c1d400c3e01800d84105c007042190440e2a440441c41180c16a0b0080c0803441c1c00314004101034005151940b0310a0051041c03940000d0800043c5104800c80d10840b100000daa207000c281408a884603100c010030007410160b001000a003014041c8403a515a440b03000c2e0a0a4102c200480140405403841c1790080648100f030f000081c03151055003211440302411418505011041008040c1900412800c4600d02e0061103e070710482400c00515034000d004004c242e041c9440c5041c07100224040700b549081c50181008240300d0a600440d00704101d03640b185620706560f11f11181d0360301080035a0001b80d40038520380300004a44040f062040140c410100a07540660764603020041002140e200d810b011400140900401d86801d00e41e0451000c0890003002d00d1f1201e07000c183c3c0742031104803407100c0004212070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 970050278 1250 970049028 970049063
    0xa141f090501050f01080901090f061a040903050a03090f0b070503010e0705090a27050c030105012012071a1f09050f0c1b0604050a060c020d051c060b0304 68
    0x12540014890820100300075410031000c1903821071205601c070f041c0500000490103c0700309500c0040709640003205280d500c22135180c440050044c50781c40243c501001000644145002e2103240d82e22a81904c480e40742c2420300b24150007400c2d00c000151a0b03400090050400704250b40400d038440e0900f596441c0d941e6042240110600002414001c1044414442d502c010317280e08415506890f400228043d0124003140001c4a03480304541e841a00350501007402800b01c100c8028605031102600d4042d41003514030b01c0118083c00741250001583e106903100c01c000604c020043c02c070140075140000642c0c40d62241250701e10002d50702400040300c0c00e01c0702006c0440e48030490005c0c220b0303c0700c180f1090805103007030281d00e00090282000d4020008078440f2100400880801030201502071310992310b01428001d8440c0c030940001d440d080d042102e0009007502c04200c0190b05141d0b9100d0a08024290500c4030041c140a600f0700c5506540301008100d222030302020f948140d03c5400110f020780d9110 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 970051528 1250 970050278 970050331
    0x1909050c010818070902090a2112030b0d0209041b06020a0b0a141501091d180109080406051309180204150b090613030b1003110a05180a14 61
    0x1e120901c00601d010352480f44000c0801c400e411180c0b40d80025032504007038000102ca000869208400b02851030700d06010300c038140140c0d5100c0f2030254482c04480030b140101607050700d284462080d4014482201d4100500c1c0401e9240d8109010b02c820508249014003404001901030b040b40002d6400011007a04020a400e6000e0344030b81002003d0000c03000300b03800004500000780804808142c1e212010741540d114071180e100810800d0a0000c44603100d10414100f1304098a40d08844c2030060440306203100d050040442041e80580c10500d0980f80c554110b034250480c2044400041e0400000581483e09008107000d02e01c1c6103c180615920130f1040008441d031540141082d00c1007900c0130003102c14202c042e101c55103800e41c0c0e260b59410184100361141e01c0f0740d4000620301c2000d942440880c03c1c40b0304411040d0382c85017410000044840b800c001446d802413084982c8811102c611450300d0f5003500e0015000303c3d1481021450500803081071082400844420780d21078161180d002195212 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 970052778 1250 970051528 970051531
    0x50a0804081c0c0305070605070e0303030c0d1104120b151e0306150306010b0a030212010e01081915021c0606030e010c1803020103091506060c0b090c0a0e1909050c0108 74
    0x1906000b40000310f01e42c2c000d8214000c0b8078000d080d403551003000500090059a034075440c9200202541d40d2854070503840c00954206000040009103041c0340e241d2040ea0b02003c507026100312541c0c02d075082455270b03105c3c407030224020300b0705050180012980481c0e80712901440451100000c003551002001c0c4181403801e003000b0711480740b40028600c20179180c0c401142c0103040d950100340b041d64401c01203500746c02910070f40c0200a42d4545400000030803040051803641a614128140d4000c02c114040c11085206018030240c10440c03001d070403214403036060b03006200c6280824151030301480d909028604444480e0321100100e03403907410144101000703110704940303c0d150b4208000c00f85414041c66241c0d907401e000082c145607075080b6000901281c50100741004117108024446c441e02c07a500200b90300e4000c102200c150000320040f400d500e0021030f04624006000e81035090140c94802c0900000c02d014010305082c0903076411a003455038030b41c01152440c900804c02008200704440004000740710 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 970054028 1250 970052778 970052833
    0xc230603100501080702011112040506090307081912140414010905030d0b0607140d021e0309130f0908031e0103080a030c031e0c17011d04050a080408 66
    0x10410821901e08110741c45201550030a10b0102003603560501c060f401041413086110010380081070042114030300400051140e445001980c040f912984440355880c02500f000600c1010103021041a18020101e4180301003001c1c43c08043c0c030080b110000e42115010500000070902002c100414460b00a030f00c050303d00101d00c000c00c0780d00043e131100c035100d000c0e034105042d80944810880c1d58035511030302564603460300700e05401804800045c455980356181c180b03a1001d070040020195a03d0946030b0b850b00354002c0740029615041801003009400c400d14407070890581d5440210444031102031042455a900c169400c3d5501e081051608040c80d0b84001c5412072940d400e401400010b44010946040d001c9074180418200d24085055000e07000d0200d104e484130810180303109520400760001c8050f06019110009504030f4207400c3e01c04d1540900980d861000c022425400505090400a5000c0d0180c0240c0b0058030069441440a03849640318000940c45000d24407806010f11101118040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 970055278 1250 970054028 970054039
    0x120e0a0617090c0d0f0819120f09020d030f0306080105090c01120902010e01050f0d0513060f060501080c0d0609091406070504030b01180e0a05030c150118180c23 71
    0x1020f000000312100d01000d4010100082d904500c0100b017809010344005940f55040c03450350404009008040300c8240c0c6c1c0c150306e0b80341081900c04142c01d091190320031a40e0060003043c3c0d40c90741078500740c0f01c8025211502041554480c0001000c1000780f01e400d00030030554000d40700100c1c800c0d000420710440d0400f031214240c40c050700040141e030024251a00d981e002e08005131201510280c0b04414068042c0303c03050682080200045461441c0268520310301c0740e202084600c2d00000d4680072141c00c0e0103103c1c0803906520125600800080180480d0003581c540402d4003038881d40d401090b6502803008031401c3e80010300441720000d060040e603a00105915060f401d1510715111441450b0b010b05c107480324041280c41207041d1007160303080100e12640000845991038924a00303903a40c5d90040654800300d004950b0050705a2454259541c100d400c1103003401606c404518041c0c0040c404020440030245210861000281d860040000184080c2004403100001139260180c59080090340602c02c2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 970056528 1250 970055278 970055293
    0x30303150807150e032407080a0c14090a1d070809120f07150c08060f03070e0f090f07030b0a050604021606050402031f021806070807120e0a061709 65
    0x8000e001d0414840c3c4070a10702501441c0000c0086800c0850341d981301c2d0110242290f80d2440d54007000d84590145880707954034882c40e610400c4c490100c40c281340340c4800054452450101c400540e8020382094a4000d10180d80a555601d244440e45880204040707070b20341d000f0070072a400ba0840290350307002d4030901c003424201802044120b100d114003820034103402d20108264050240703010040103041c80586040040d01c0c884503010303080800480d90b13240314580020701b107900341c1008116002107483c006160481c0b9120401c09100010004010302003512500600d804281300420504004500651680d915800c2c50041c000c203030707000141b440b4011801040050744e070388010050740c80c1c0305800900c000313281e480700c0c400641403044035101207006030312442c2e00d1248021103074001d28030200401146c8884000348020b01c0a64040d43c007000e030040205216183c0451010619044208000c5c40c01140f8000075400140c030000d800c1d001040083c02c0d441d080303103100300342105450b0006803003001085003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 970057778 1250 970056528 970056539
    0x6180f0b030f1906110a050702030c010e012a06020a0507150c0c23030c0c0f04061a0c01060b030a0f0b012c131103040320070b0a0513030303150807 65
    0x48007144000c3c1c0e1443c0c403650703001c9824048243d10500220001c151000d40c1c51a01d40001049a0055501a4887d01a99548841c03642c05028200e001d55010303140e40b8020300c218002039a0018800344030801c4144016000b0340000c032140b000300400d034040d40754551502d803a81449820012810180172101d8501552464419000b0500034000e5501c1706261070040c070404081c41160201480c0c0c01c0700c0b4400810702070001c560103d40b5a80346082a56200f40180280d020802030300d810b442005291600e0030340703101a10b4000c03070003441005845000231a449a07900c0c48820f0a0b4001c403602040c13a81d4030707038080101c044a4000c100310070109203840b034421040b400d04821054242541e800300d1950240001c41e95856003118543c00c40c0c4540010020303030410301401c52555104690440c0040c291303a400071258409104141c802c40a0b000c000c00d8000e041542001441d4800350070703c030034070505100340840341d042206a072000d10711965000c034242c01c003040c040c0ba41c584107030041c80c0c0580104005011 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 970059028 1250 970057778 970057783
    0x301060917070905060303070605010b190e06090f031507080406060504090b0a0510080703061b08040f03050d020405130b041d0a02041814061009060e041506180f0b030f 74
    0xf525002140000c80c0c0e00c07402c0c00a4a54441d82034020724003800d1800004041c15908042d2100c868440240c20607050040d40899404c440d0405480d030050060002c030f0380f42d09112980740030385030010782240c07080740c64410358010400d0200c420700c00003a1060100020408507000d04e40042c0b0050760144800c0c2c10b15134070f8508226004080da80301ca50384e8400148032420800c4028001c2945105448a0039100d08020300034107178983d9850101107401d900c0745034003482040c0c5940300303641026807034480484580d0100e0305035105035a0116204e0b005c0c40046501c5c0e86507000c04580704882840000e0352980081071200381c82442b101c01d0074141c421459000c4060010655410f10380d4100d0700020103590422402008803131700380014010300c6a4010740c0d48210000200c490203648164944240305980c1c02000b825210b080c040c0006180d004030200e00040d40e4006c1003001e91810641c04640359448046010078680510300e04050261078417035600380b0503503d2052070700d082d105030302521000003000a0960b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 970060278 1250 970059028 970059043
    0x180504081209120406021005071407060c0207051e101b0b0612011b030506090601120b150a051809061518031e060a0c0906140702060a02030301060917 66
    0x40c60340c05040098141c01040c00043c41c14020903618070340b580e0b1111002981e610904102c500147d1403c0c0104441600440041c803044485249481c6000c100d40e4545016010a00d8103000354418007101141c01d5445d2140c016080100c45000b1008818201c2040011100101c40c03406001c0a02000d100d02c12010041c000f01e41d81050b14500203440d001e0120310018207402e0469025413170101d0180f1034a171100441100315000c0c1d60140031307540340c400811008650a07500ac501160850384169807240b145d401046400c2002000c070354421300210100001c1e03074404080b950001c0c00010300603442240f002480082c5032419200c000041c54840082840060312002e2004405808129050349000d80c4120010212004d015111800d244040481d440d241120713542055008400009104540d0780c812400d02c0c035025035805814a28101040c6d5260030b4000b100300d00400c04000035400758561b0001080c9201695004640d690b1401000a2603041c03070750400e600c2d2050384a100b9840b46000034420 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 970061528 1250 970060278 970060297
    0x516020615011206060503043e041e052a0409181b05090702030909150102030918010f0f14040c2a030e030c0108010e0709080f060118050408 62
    0x218400751500607100581c2204102118604003240801c00741c5d0b0141c05140654400c25002c03202c0d032002501c42441101102d42108680326104410b0210304c10340310300240105d00a040055102c0348294100001062010311703910864a071010b00010503d08900302d50341080c2e4503070405080b81e40024aa940c0e22451054800080e103941410070311060143c280d04103d03600c00c0315000c005001e0b017844110001e50f403003260f11070341c039180010781d50703d001200315001d00c803000746082450b0b5036a2060915204100c0c0b002411440280700c04105134441ea029900d034801041c2a40e0090340c501104402c0f00c8c6280c0d0084280c2e100c00c80410070100100031a0141001c1c41210080303030046441e441118080640c0700382a44106141044c02481d440009007020040e01a940d0400b523101c1003802c0c19030300c03e022020030b0300140c10b0100404c034541000200d541c10042500c3c044504c40d81e41c0184515007083d460342c48285420060040015000d4403840f01149148100b040c005850301d610b90300500d00446404 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 970062778 1250 970061528 970061551
    0x30d050313060e100902010801090207081e04120302011a060a0f080a0f091101020706051801110f010603051605101b050106170a06050a09020604060c05210d05160206 73
    0x740000c004241c2c000300340002aa1040304ca10288000c004805802018426400704070403200215841a17036008881680340c019222501c0d062010044907142d86000300d205030903600c2800f0101300380c060440e1610400340242c3c0013041004504010211400d84c1c1c4041610404007004a0000c0390341003885054030039901c0c00d0000150303440041d001d02800c0c111141011061401c03405604008900004071510402030342107035129526154152440c2c8130b0051007505166800b5a28061581300d001110f0303402d220103040e03494001001417041e0030754000c0d03001143d580d040780d59206445a6240c2603c0010103046600380001c042040024000c004803a0200d0030f000001c0f210744080c01025003200c0700070417400500918048440c11440d860b91085002120500d0910010880c1c3c2c54031400b032008620b0b001052140b400e450114281c40c04420950212060f01404c01c4801000301910058618541007010036076840d005169003000300c0d10010030b0220320703600c2400b140003000e2340016802c0d8008040e016 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 970064028 1250 970062778 970062811
    0x6090906160309080f0c10151a070c030804060f0807080403080402010c050601060e010207080a0b1f0e0103080a120524040618021b030a0e0f062115030d0503 69
    0x1c0850140c40020350103080d94200050000d40d28036008014540c400454007510100030b05c151404003581c0d4000d41a01c0c0c81e8154003801d200c0280d0b006030000c100061100c410b840c00d140d07559401c020b410154803c1d10710304000b1404000440c0c000601c100d88080614005100781f801e80f602415203000a400501003010340700c000307001c59014095801142d0307001000c0300c240d907035140c100400390b8589800c2c0c0340c01801000740000300c010001400c01c6d81e081c4e00c001d0308030480d550a225425a00080d403104081d1560190780000d5003240c403d61036000e14003d21043d03580e9420480302400308074058001c810002d151104020f1148010a0a42280701410040241d0440b001000034080d00031b5070030149a0200c00055205441c4a07a4002c00300030382440d03a40c02d2091400416507031a4020403030000049810440423464626000151619030175000380f009007414888014041040280e40d0f42929041c1c00d80c1c14400110152400f0301c0400008031f00510200e1401e02000340075000141002551109041303 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 970065278 1250 970064028 970064071
    0x618151d070504051e0301061202150d06170d02010c090305030d0506040e010f05040c0f0b0a050a02010216050607030b031b06090a051203070b150a05131b0504030b06090906 76
    0x1d00301c400034100108406102c8175055240c142c00c00211080078030075880c20b0f80000e00e285040704d40310318a580040070101c800c9140f44000c4203035801134403860300c03441d0341c1c400204041110f91245e008c40842a00102420b0750983d00107802c4920b418032110911540c807404200144001040700c0114a4414011030540c54400110700504100308460b61a035007445c29086040515174082440749020f03d40c0485100d42c1c0746540c0700c101e03c1070300510040a00401844108901403801010040fa1503c001071401e1000035402a6484640504035151340103402842051035041c0585109080100e014140360001484100282c1f40c25121460040002280602180d60b035448120000c04010340801c20290344103580940b20b40c04410b0482d02001c5034400301e210807403840145036100401a00c01d100d46400d080400066840100d5240c5200752140030340d6000389074005269140ea00b075038445c02c2d112800c6140c5142001001000c25000354510401c002002500050a940002122403074030311138455079 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 970066528 1250 970065278 970065287
    0x10f0909030216140f0415030f0f020303190f14040626071e050301030512161506090605010c0c03230d05070b0106171906090618151d07 60
    0x850707203070448515015002a141d007114413058008403045400c03042c05210202048119141c000030040c84e0b400c82c400510001e481403c1c041c0707411b4000c4256083c04011135001034610f5022981900c00c0c6400c0028030010785400c43d02c5114a104035042403481000c0380d65050183d03000320320400c6d0403c0003407072582c282e00303500b1003c1c0c40c01207080c1e0060300130714034001e100504204141840024800292080101c0e00c5114500341e9041e02d50001c060503802422000450b155000340d64080c10014610b510040051604c00c62601a4100054040f800c41c0c60320314143c088035100d900050600c406640c0313201c0000e100b41604400c0e41e5200c4c410803081e41c50079400545080c4c00c82405c402c2440341307440c508407061300440a402ca00e4819549076103245e807544030032144000d1240034014001001804101c40c1c0050301c100302107030513100700c00140c407030340d119504804d54540798080e107030350750b00040703440655074140c028503003800300050b4060360036031800c3c40040e40c174090070140b800c0d51442400440d2015100b0b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 970067778 1250 970066528 970066543
    0x80622020d06170d05070f060515100c03180b030a091a040f020405160c11011b0b01080708060c0427021c06140616050c09010b0703090608010f09090302 67
    0xa400200b0160b911055070b20078592400c0300c468003d20420600310b42252050046800b00c83e801905080303110708941c0e07404040c01d0301400c08009002c40902403122901d40f0510914699019514210140c10380d040207007400520f04c004078403913500ca10081c4552064a4106c039000560340c08002100b980c1c0781442042180701c0000c6010601220040c030051000211400f2030ba14001c940800403078a07905050900d001c100594607000c6106a01164045032882080e00601181030501900350140c2d1000c0d5880640e41c00b1045445149200042c046041e04205d235001130000c11000700928241502d802e502c2e8001c900c03424482150707007101c01c0d4080b00503110950f4840b10f010004e549070600d51184500304c40001620849151604c42c00140302c0410030210035100d280a03080914140348031f403580454003401d141c161103030310800c602100251184200c19000309502c069254a411840c80c0081960740c903940504200442d0b200140110112000300100301c64035420000384080040c681603041890 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 970069028 1250 970067778 970067797
    0xa0920100e0f0603091f0c08010302040203070915020145050f01050109020a030b09070e0f120d0309021804020109090e011503080d0e06041505040807060207200108062202 75
    0x10f000c010f0007440d0a000900f2490104034810f1550480c1c0b407448400c0c100c441300c509084c00200714000410140c00c1c280d0003160071141c1490300e007418949030b8045c01c4d0f041c02d41002040050395501083c100e0300450290045150010625030180005001d07200d1800000510141078410740c240910010040c0402a007008040007030001e00c02c940c0d40b020b10200a4000200350070200c1e007007a00301209440e00450701d51040c0c1c050744911a00b02010b00a22011480c940b8603907401c0300984844000d1072504100520140c2d000c2c2c0e03004258401c061061220039403441020241114015041c000183e030007148080540b201f039040080c03502c440c03240043c0900003100300c180c8003150214011081c82548401084490880c4800340000c003000c002042d52007100322005844454040b0740501c0d1810160019034210740500d044906005241e140c2a040368042201202c3e005449032050b4200ac4480141e05e16281003401d04c1c42d160b00d0030202160b40b10442c9440039080780040c400c0529403000365810f0310800034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 970070278 1250 970069028 970069039
    0xc280501050403172a0d1106190b0102010f110d0b0a0b030406050703090221281202030702150913110d050402041b08011a1e0c0709050a0920100e0f 65
    0xa0800c4069156158440784000280580c2c40441f00305000064082c00750405003407406115400340f03c1600117012800f0011b0455498000700b0980e000c00e8000e0700071303810b02da070f02c800d40e074011007111601110341c0440d4840c000c90141c0d07010403880c20740c90140d80c2d2254000401280c1641c40704011401090002c1d0000e40c05a4060400f034902e104c01c01e6003214140365441107400d45092820030b0050714100c0c1c1c40402d0700c0d0071700000d4000012a940081155801a40100e134104000c56000425441c5100d0061544402c08180ba0000d4940008200240c8070b4200f010882072040d0180f90806100324032624400e262a0000310301103441e26885282e0401c41c2100307007024010f11810083c0041c0b028494070160b0010144002800e20000c8200c070307251034004d11717107401c009111154102150081c450800701402110000261842c03680201c03442030345201400200030382203140034406d500e550760282c450911a0000440c090300d0300c901c2300c0c0240c070307080c2001c001300e28507000040d10640300c2d401c1f02900301e03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 970071528 1250 970070278 970070347
    0x302090d0b0115180f0b1b0105070503040303110304020d0f020a0e1f081203010e0901140406090201020d0f231b0a0b0106020606010f110c28050105040317 68
    0x80844046101e02424903944c54800005403a04e1302000070490142c0010820100d508020f40f10005004003618001c2038401c11300311841840d401e08441048540401003000001080209075041c4142070200d4442e1b8809801e46c01c2c00e8021494070144800c0c01095500c1d280d4000e4190342e00c0c52019402000490321501c00c51070101c00d01e000304680f50721480700031071000502044039000400e80d210a101c440000b01c0c103584c81c0c26504c0c204900040d040100c15503807009180c42c41d0418000d6548940c0c002c2c800811142c5251000900d45035030145854100100d441c2a40d040542c41000c42c3d02e80c400c2580d40c02028042c080b26940c06101d407424401108460348420000e484010031035515050182c24915001c2c0e80c0d0b00c50a0340c81d110212150707800141b4107489500d4843c064040310f1440554102150710b091034540104100c100c1031808044003400e0084001040e1080e0403a0102512080c600141854a560f5481b0a40030781c00d002000b90f00c0740894140d03680b4400101907030192201d14040c0404 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 970072778 1250 970071528 970071539
    0x30e01110118051b030f03030406050c070f2103050942010f12050d0c0c0314060906010b1305090606091e0301230a05040311070b18030a030f0302090d0b01 68
    0x40e41c09002c0d44e41c80c0000582e0202d0b00600d004138280200038102c00c043c40c030b165110760701d90000340402003650209000c20300603140440d005100006000b44100d2601000b5665503007185040030081003050105810502040b290007008103117120298201014072071800b00540400e0344401201090f03140803000c00107000b00d1500d21820300e170304840c41c201c0c4008130207499a00b005408d40005801030900d510071180410b006114040b003603030f102d0061200c80b0300181c0f80d540d01e85800201c0c44070425507902c1001403003500c500600069005000f042000c84c64065003034641c1400d08003511a151103036403641e00052080c3c80f42c0c411502481d82c003d0400f160150034000c07a80c00820000c00942c0650b19004800301031140340c3e054440004c02c0c10400458651710000e100d005040c0041c0704404005d0850103244803400108034220141200c00007550700c3d20305881076001d01d80903071500700c1d201c0e40c0030021503008242c004421450511031881c01598407680d800c08905c035503490482c0208404c81080000a0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 970074028 1250 970072778 970072783
    0x1b0e1014060313020d15023103020a03030c061506050705010e06090703080c030d02130905010e01060509040c200109051504080403140c030709020403110d11012601030b0405060a09030e0111011805 86
    0x1441c4010010242c0441c48c6e021807030350400c207400000d4102c1000401400480d029100c10401244a01000308a46000840c070340203000c1103500400202d00040384c4001000801e00408503200d110200400c83c82c900008841c1c1e8a0350740303200c040e10340440000c40d03400f1800144100c0b03004001589003955100e01d00130420078018054401c2c411003529000010584000f642001070486c0d40560b115420148000304110080440141500070710208100303141006d4280c035448400350f00c1c4040001100c00352402c000c0c0c2422040b1000840403401e2001700000036503076134203a03415a0340005204c60443c0c1424101e5150004902c50303154144100395000039020340580080080ea4455207100c44664110341c10f211905029950051030414000d41441403544a5480480544081140c8100011102461080c80c02003038105030351052108041006100081003602e4100350405001c0141410781d1f10020000c44010064604003c2c0c50454402d880100350000403043c40454002c409810041c0782456 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 970075278 1250 970074028 970074067
    0x10e040e060c18030d050c151603020f271003050c0708130803130906080a05070603050a1805030a0e090c0901030c110610080609191b0e1014060313020d1502 69
    0x1c1c44c0b4420000c6c81719411031010017460281d40d84049c040c0c8100605c0c0385c19006500000400560b540c014000d00a10240c03c42032000000082440c2c040c031051071030180141406100c15540c14503040c0303014003070303c291210700b19652540c20818264583d136002c41842144c20040d40680103520021500c409000c000700c042c402102c101c0a02003204582d1500419104d03447d411000e840fa0300700074001c01c27100b03000c0d4024581c424104000020300c00217500003031900d40100442516103500200d44050380a411008194402500704d482d00b08a00d402c0c03d20503140d1042c914054105504d510420744028000d1400e203813007100328402c0d02e80b07902e07104c001c2c159011554410b80078103201c0c98020035651140410300d0030003401c0d80020000c05044507181d41c0f01283c511034440420b443c0b008000034480450702c100b14040c00e10350443c100c0f180d2074103032644420604400c0e094401e520030014445800c110307c69000b4800d0b419224010040109d040280c60036540c01c9400f01c9a60000400d00c888404002c601c4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 970076528 1250 970075278 970075297
    0x3061d060f150d050606100912022b0317010e0105061804060b0a0203181c060b0604090c08100609050d021e030304060315080105010627030510060302010e040e060c18030d05 76
    0x401a0f1120707007c101c407061000d01c00c41400c0d4000400f003c0260074184c900242c2030440102440011030b110000900c4400c0040c4142d0002d094403255403e42d100c0a000503004040d044071541e00c55042c0000540306d88607a140b006e082003605160341d0059211500141c008000345e5070111b4603405802d0020752a503028001040954142c490007003028600784d50480580c03840340b40b0a00d00009555200c000409200c08026400b5209100014200155008900c0f0903040c50f6100445400c1610180e5010340894100c002072048410b000d10090311080d0b490b00d989034044505d103010f40c008511101d0402e120041c150b4040c0000140444c2d600d400d9000744881a01c001c00c0388695640d103030251404c0302c4003800380000003041d080160302c40040031001e0303050180075010407240c0c00740d0302d594483c6407030460350550070665150b800420966800850030203214400343c0d01408080c841c000c03403e80b2000000d1000c001d00c02d000c980e80441e60544442d402d03032000c019049403003154007100d0140ca182c100344070a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 970077778 1250 970076528 970076539
    0x6010f0e452410030b0f0909030a030e0c030d0519020c06090907120509030c191e1407141309121d030102070605040203010e0307110607080d1503061d060f150d050606 73
    0xb1080c03c0c0c20b140814520238164240954100701140b0000c0b40a448030451b2038200e4458001500307030642e001d2003141321890302ca03281c09507a07284984488682d400100e60641c1550002d07070b04000d1540304c0400b11602e0350f008076420030140e51910420b40721000380c40c0800c01081d1030700c030400c401b844000009041210780103044901f03055403130203202c500e0001441d000340340100e08426902100e03519207104030640d2040c0510049210b0800d0790754a000c04541c401807800200ca001e24215040032a100e400c1545106002c0c0070b1500c0b1521021040d009e0313039112a0402403c00c00d41840c29209110155008900800035580c1c7c0040b810108040e20041d01c2c140e20035480e00600c402c3e120340c00400c503100e6035400301241d440301c40d2000411800d5040f0203029a5102c00c10000314000050310710940801818901c48041800d00b14100602100d144040fa0100340201c040703915581d0724001415030b8001310101402001d0b698034021400c4c0f11201241094005880d03a0800041100125200e80b18400a50344e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 970079028 1250 970077778 970077799
    0x115050112230a0b09100608070f051207020c0a030602190305010e0103060207050a02040216050d05040f0504180503070c0905100b0306010f0e452410030b 68
    0x711401102c5041d49641903a46507040c00e01c034400b00b051111948220300c2c0d900081d99100d80380101d2804034003100c12605c050560201402200d81000c0d030b95401c10080d24206600002144025005200701c1c581034060b2007401e40020301d458800c012000686078081e10b01b04005680e1b10b0304c1c1019411a4842e09800300000310782d044407d1092140c10b0403103181c03036000d000c00e0f403a5851f100c00952001000303541e180141001440961264002841c0b003500c6042c0c0c94420207281d0900b21700744040c40d500503003002401c000801c1803500c4174080d0310603504101d40024608403600d00c1d80600000304135008295000c0800e404003402080581c8004445214a09000d1540c1d602001403201c2050700581320a83c2c024000314006500c80e2022a00e500c0c0c00d400e088480c103822100007285181180410303400c00b660300f6003901c10104201c9840b0842590b08855607030703105002880c2c44c0301d10741c024019084210617100300300b6601142c034105503032f102c030281102d0898400820014058550409814043c440c1d400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 970080278 1250 970079028 970079057
    0x5152e030c0e040b100809010f0203100503060714090f01020a0611030f0108070609140d050105151011061323010506150c1f0b1507030f0212040b031801150501 70
    0x61490b001200900005c2c0c1002078840a8440c02c201410b401459944c0c0c0700040342082c41d5100440c043c0040070800c0c901c40b8036000405203402801440c4000300000c409a07103480c0e52892080c4d8504840c1100c503c2580f05140c00100d15001100350301600150401201c1c44070fa0a5101c0114014440c1e00c46003181681c03074240b516540c0e00c49201d2100004c44a25041021140300035903448210b60080c0280352005054035410709640e026203049069282421260715a1b1400c0c103400c4824040790304200c180c00d036107203002607202c6500510416007002c55000030f4041001d010000986541801c0f41040d0291003918514002c100032120715000c0c7d081d1300c81c514011140c10f400d4a4201c007000009103140e0404440d11084000303044680c2103001e8640c00804a1756481101319014090a00d49458480040d0309000700440b4504a510080d03401c07501041901c50008421202036a201803d016900e1311410100c0000b0004d80707516aa15520740841071100352111101001200c1e02643c814240440300d0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 970081528 1250 970080278 970080281
    0x501060f0f0503130f0302060f22111f1d040905030d0f0204150806150415030902030a1211150c0a1d0a03030c05010e0105152e030c0e04 60
    0x3660180100c0c8010390411540380c0720303000440e8011090942401c41c1e00c20382d610000d24240070841100541c0080d402c01200c8200c2d101e409074000400354080d90305207242c14901c43c2c00540c411001d4400421405140c03030301d803a02140e0104448c1ca490180210a006e124010101c4242c00c00b0b101812a02c1c1030801200e25160041e004980c0c1c001c406103181c1905028414000c201c0817a4000070303d5002e00001801138454041020b02e40f03003c0d180c2c426180f41403c108642d5104000c00031040c68000c0c00184a699260054400c80c07414038200007034001c610b400040d01e00b4810403801040503007001c800d01e5415a02540c0c1e0240414280121444044a5001c0544645046070307001000102070002070201d40c0b0810120454800300300002d00041000c0740071481d07428107600160042609100340e002004005d100300e4607d92400c100810845c00d2140780c501d2000d0404502da0703c075151805103810b40344038608001004400c40e03140c0c5450364004441c080d01424210220303001003104859003c1c0c0600f005e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 970082778 1250 970081528 970081547
    0x9010501151706010e0909031308070e010e0705070b040f05060601020105061e150f1e0a050418020903010e100606030504120f05040b032a2a01020c060a060306050106 73
    0x854980d00c40d0382d1070b01101d24100c0b62000341414100018001200459100c1815450042d121030010703680c0c40c0c20000c0c01c1c4403e410f440d805070300b09a104200810202c04602c000b203054500c050700c5c9150342d858110003150365004690014292580c0322040c0010410400504d1600741e110700c2c1554080d543d850016803c0341c40481e501504a208c0c905200e200c40203014a04180d00401000101e070003140c240c5000840d003162150707011400c400180c840e824070a80c5685010307000041085480d0000350400100540283e200340101e00078900f0410304011030b107030162a030742c600c0a80200400110784c08156030b29054040800a0540340103000b00f0369038031a0007694440e907044803001710004000388044600403071480c030050420400384008100c001c940c0f8000c60003545031400315803e44100308203510241464842c20310302d10204020130100f05210700d244030741c00200644032000c90a4200c0103a80a0f00c600201001e80d40220b80410410014a80c00703241901d01684080050b6038072800300391000f294 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 970084028 1250 970082778 970082819
    0xa1502070b0402041107050703060c200709050402040603060f0b010912050303011505130f050306011d04061a03070e010f0e060102060c18060a050a020f03040605090105030402031603050609010501 86
    0x40000100541410741000035402e4030141d17000d140005039200c5c80e007400b0140d0801c03101d40d6143c41c440301d035035540104086400d90b0490340a802448074031070401e5840020b0b00c1000605511200001e040d0f41d103640c49003000b981c2203803007840400a0803800f20014044a0015808201e00d0b0705c01161800304900a031100c1d0368400e00462841e402d01c08240300c626044000b890401c0000c00140c0d501e12403440c4a50024101022a01c42d00c1d8244820103080c0750050300300381d9017030814040c0090402d41c1c1c01d050982041c2c0250b4001403480102017a46210701c4200805501803084030800220410780000041c12503509008600c02162940b12400300701d10150383c5c8a00527408480482c580b4400840105103111000c20b075404500240004940c2075045a101000441d50105049842d0380d0144402204082c0940c0a98070f405e04040c405021400340724840c50401801000260454408100b50081104114280010b042d6a032a0069440d1000c82e050202542054000683c1800c0a64003100451 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 970085278 1250 970084028 970084043
    0xc030f010219080c070804080a05100209010c0822080c0f060c030f13180504061503080a0c11060d0e28080a0c02130204091808041a0c010e0a150207 65
    0x12100c42c0d00700e40c51180a40a4180754004208000001c1c0d90400100f000741074000250040718110b007840c1c1e00349040401680f80d07440c010030110384a680d001c81207840e22680002800e03103441c0d0403a071128000024403040305502140c1000801d000f800000c1d8a25100d104035880303c0055a441c007400380e68010744140c10600d5006200d03015203429510040c0c4080620950804c095598a820314240354804090311071001d40e8505c00c2c0000d00410f030007031411a403540b25944070624650f540305021351180d500024200104294814200700c00020b08284214000700f807603440d052012804002000071420f40e150602c00c1c10300d42071746040e00710303000640002d24409905000718180c9070702d62254000941c8a04000140003600016640d2040011001c580c16200603196400d00054504032818901c030f200c0c5041000844030300141c0080211019205400c4405040312740d10810041d49001720342100d42c065081041c03da000080009642c2d4140b405045400403241e07244001004030b12a03880084c01c0d40 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 970086528 1250 970085278 970085317
    0x50610050f042105032a0a03020604061a1906170c0307140702030102030f151e1c0c080105041a04050c040924060f060201050c16080d0203090c030f0102 67
    0x40b80d8400c8800d80300340f00c401d0402030400c03591114110340c4207500103103803910981042454103002d2003000035101094401855a8540740d20003942c3c0d03220003080204019121410b00902d10150300410341b08e0740c4090f110810000048004040005660180d440056294021000e0150007511410f00a01c00c4001091441d110844116400e0000031080d100340102048050700503107091008500c40c10000c4545080c0b400d005138119070f6190000c000c14801c18030024140941d402c5104034910803c81103484a0b00112902e0450350303580100c08018080e6074001c0c100045098064229038030680c4100521072400c10b140e40c061144450503034001c1c0169001c001043c016040c207a00c1403500380d0150304140d101300c4d002429034044c00281d18007005055100c1d881040203603041ca1284014240600003072125140183c0c00404500401d1030302900010b09016140600141c1000c940c075180000a040d980c4c0c0c54084a03180d0390300ca107044200d0203880b8502440003a00010301c20340f149010b069920700c029 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 970087778 1250 970086528 970086539
    0x3091d01030b0c0906272e0c0c03020306070804151b0c0c2606090109082512082220040213032105040821090406060201050610050f04 59
    0x10382d004041c4c01d5402c200108a4051160b08101d00314243d00070b0401143ca20744500c4007407100800540d0b2821802101d411068000d1015601400e4800646c2d4a04090103103501e043c110140186d03684040e405004a006021090394030001c0345100380d0041c400c4c03105400042200a003201c4010280b000040b8032400075035251481546400702e40e90141031070a0095485a0860803401002c030b031560b02402d0000000c03102c00e002400100e0340103044070020480c1c41388a456000c07540c445c850564182c0c4030b1912094611300d140360010908690801ca1858440c186140c018200140139180482c0011203c61509640c6d00354200c045a0310761b00000c2c5050410709046140108100c012407076911540a00113000e43c058610340510042d801209000c445450054025020000a0b4508010840c0c01c01081c0700d05800002e000e0b030082540c0050700d14100d000b0048502c030b8054a00500c0e405401c00c1c1d0005115681500214040e800c112446484200c0a01c400d076880d1003120154175581c2000d1100301310 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 970089028 1250 970087778 970087801
    0xf0201111321030e040f0209100917060105090103140a0b1e060306090a080a0c02220e1b01080406380103020c07090902210d031a030c0d02060906040303091d01030b 72
    0x21440c904500503003448c07016400141c584456000f101c0c00100c0c8000c0401c9101e0b00401c074148100441400382036154100008140807441c140006800311500e0784031021800410000c4036142034004044400c1414900e1400c000e06c1c0c805000d1a0301e00c46c81a0200d4000d10b00032404e540241c48140040103680c1107581d60010381c0d001284800244104c5030000f501503240c02104000f01c66194007100b50350500e41c0d00680c2203441500728200245c0c0400c4441040c03080710350918426080034201400300e9901c81c501300c2d000d046410102a420070010600301560b100307200303260003400c6c01d0b19112450404003000441c100d004036440c1241980c00941c042109100301d074007010710580050400c401c03414010645480068003065402c103540e02c0720145c0312140744e05200e00c00c6500d4044600c12500e0b94080002640c1c1c50308410414400c00c110b145c00001c43d941c4004a8080c190081c8c0b0881c0c50325601d0074050905000c40c0300c2c0108034240a041c90440400c01083e450603641d00c14086011500d400701500c5 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 970090278 1250 970089028 970089041
    0x18050603010b060f0d2004061d060a2105310b0f091b090106050a0e030111070c090e030a05030403170a061502060708070f0201111321030e04 62
    0x25055540c074030a10b040c5031540b500070200b4103d550b000f01d0352507882c00301e1281200c01d00e000415011544124a29801c0c070008125011641e0074907003402d40143c1c03868011a1006180741c21980428005801164207410440c1c1c000b01e00300d90300701c0810341c0001c06070312801c1c1c0e2822181103031140400002c2c090703d40c80c4812798001780720460319880c1140f0b40d165140850644151141c0e5030340050300c420048612420800b201c0c0051002d03080705098a60500441ca450320306000701d40600c070010891040c624400e1a00d052403000040c001d200018450207200f0443c5c0c001d00d42910660500c0c1000314401c0d5050041041c02c0d00104001e51400c1000c9108071015000580103d0070000420118905104c425201c540100c5101d20002544c6141c011050500d001000300c4030b00755080b03101040300298110180960105182c1032080c040c02000c1e00413401001c180c8410314000c4404903001c0c9800c0c5820607514241c07440100401e0414020000c11203180d552500c0c0203001510485500303021b030910ba0800c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 970091528 1250 970090278 970090291
    0x919090e0d12110d050f0414070608040204022b0501360519050f0a0e060412030e0a0c0b0405010306062c010c060e0a020f0d020d020f030f060703020c0705010305011805 74
    0x1410804135035001010b813241564904003404200d402d00c014004007210311482c641d40d140080c2180380c6007081c082c0c803003800144060321666000c6001403107880031100754500d00c401c2e1049076100b9040d0078101c00091800703002c5e030702d020300c02a1083c4a41e10b007288000e400300078040c48000c95005040b140440501002030000d54a09800d401c414114041401a540100c0030204400b441d031800c808074004944031b40c142114694002000c0c40086429085501311001c02450301140303e61894612500d010816100108640403c41000405402850240c8290b8209a038280f00041c2e40300022074034140021050302c00340080084501c42d840b0f080c20f4848203000103061142d200d0211748c5590f411180d1a548080107a004011000218500b08081e05031986003198810307628042c46c0c000c0f0f240d941014000a00501140804042c199800c001905040003400221082403412480040107034004101c240d54500c40c100b0003041640c040d0003118160b0301e12000b800b41d40c5c0146030b1040007400020f00038 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 970092778 1250 970091528 970091561
    0xd09062c03190e030f03270d020f120f060901140105030d1b1e032003070b1f27050403082202031209010801050301060305150c0919090e0d12 62
    0x2410f203510180214918040908041d64441d030145241030304116903802656a10089107500200c9551100c3d04800800e40603904141101c51210106a84a22224044649100c0c495000343e201000084d5188110b170410300900251172070b9445104085000c2c0101580b507000000000c000b00d101c0c030028108100b18185c2400390b065103843d80d02c5c079982900140002180340021003010b00d60011804c49002e030035609a03520035803000c0703c4152603015452000303207940c000d02e0228200c030240d10546052080d06210703841c21281c0d10703480ca03014120b40900c003854100b40e40420004c41d5150344203a9110b02d800d85c680c202c69503521007682041e0b400c0311030880d410b41001d51002d00135807410130108403080e003c00203d640e02c03200703107001409006059108138031982c1880014000500007045028049d401d1804104242d205c880341c0802c14025114101d40004035442e80d0800c120031002d80800b00d502e00c2c2d80030404606a01c10440d01c80284006042c04140d10a01340c16803088185e2100395160024000f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 970094028 1250 970092778 970092797
    0x50f0624070c03110f060910090e0a0b0a0812040e071e050901120e100c14030c0901032405011b0812060f0111150a020d09062c0319 58
    0x20401056003080c070301a14082c1c0d20300720610820411040045451104603655100c54414000207007291045803101c6000e039038000c5502000e640112075050181514490820480c07400c0c42c115002011601e00c1e09110302001140012503031408160302c11a802281d0300c140c40c0504001c4290202c10303004d440c1340c2c204800484003464150700d1205940e980d0002d07648183d91000400c0004221548440d1035040da2031501800708a500c100103206500904090401b091401110300d040e0390505006101c40b001020000400006203141e0009002c5003000b62002c100c0048800f03080e00380c000c144074a1460711080f0410031701003980600340031f020090100011491800059490001b603411800c07060303031680c400f00284401458101c1c54480410700a181c00c6295082880a041d950750002807840300302c030040000300b00744000d0b0360121000d24071066414009081c681c0b0b030040052403500183c1810340e940c10507030043c481540d04020f01d4410031200031820311410034609521905110254400e20401d1007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 970095278 1250 970094028 970094089
    0x903080913050906040c2111010309020d0b040204061418040809060c0105090607180e09031603020c0f0405070f1107150206070f05092107030b01090207020a09050f06 73
    0xca0b80304041c3c81000c2c20060509113030100551846801c5611600c0075500210f804072070442480724002d4100b0f81c00e6401980100040e4000e210b00310010303400812107100308d8140034001580501a40c4280c800b00310f81a5580058114191040c0c0350345d600051030800790030212503a40c00300b9041402868118504a00900000d80540c8100410546651201c08001c40700c4420b200b0070744d00295a00b8405010040074440413500403041c014080d018680901107103910000b0003c0d11607000ca10148400aa43c079810041d54805007008450b22402c6561b0003281c0c1404c00e0301801d03006203e96101c3c02050428814199100310100032010b00c40d1050701000614100003404220032000581c000d080307281085680246602855100b8500f40070b010001031003140c903021020031324449240e82c0250300040b805082c40c02c2c0b401301d2740301074501c0c0051000030a030680d145e401400c0c031500c00c0f14005101030f83c0d803000e1025100211440804580150001101810101c8044114503440c03282c40034200d6214 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 970096528 1250 970095278 970095281
    0x5060d0b031f06242c0402120a0c030911101b0309150c0b0f0711010606090602010b040522080705030703080411120709200711030705060301060903080913 68
    0x1c01c1c20340306440d142c0b071042108580d1101911343c0c0c81c1240410034440562442e0203041080b5a400c02e01109440c220320310403da014401807044800c00074401d40d60b0303072103003007600b00901415200d41180c10700d0405101400d44c041d21031052220740c004040354050901d5010004a00303110210b0f1424041c1084130100000500000070300c109100e81c90b043c1d080c07800c00001c143c0c480341015a0000307102100b902c0002080d8040e5100e9407188180703503010303000d5999040440d0303400300101410007558200071010035400c0d08920031350180c81d4154000c000400c090010001501e400b0b841d403401c40f00100b903e050798545c07916881f51640b801440c5c0d16180544554441d45958484007059000549010600c810061304280c0f1040c2c401e011075030031840521143c00c0079160003c0d480f441c00e50325542d0074891080a4242e17207201e00140108146501d8040314208107100001c0e01d107901d071081c0103445005c03a191400b14107481c10780d00a075540f80416030450b51f03140c074254000801a944040207011040156119 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 970097778 1250 970096528 970096573
    0x12111040b0a08010614030f0606090405070801031e1509080403170d1503030806131811030708031303110103020d06090b0f06091003021809090303160203030105060d0b03 75
    0x50031800c2d40c0c0d18100840100f02c0342d8180c206404105890102101c01114402078036017260111811101070348424001030100c2c0314940c080c07a049814030040200050f0020400c0c2d0480340500c0d4050100525801c070010349001b000c100030020b0010b56652102c0d1082540560107a40c40b0300040c030b1801c0c0d12910b880045050a415461034036100041010040803980640a81000c602d1705030209582960b034050076061000304018001c0d844040c0004040d00c2e5504000b45920040d0035140c20184941040142e404424660500900c1130090009404000000f103401d1903844009242c5918190341c0d55003416071081c00802d04040d003d1043d040071414038810000106240800000c11200700c10130f0102c0047d880c280c1511640040c024050b194071801c010000f98501e9180050741c0d200165440a00c0794040b400047d0010030701300801155600000056010f0120030800940c210801e4404903541d12090207201c0c1c20400522000d24040520b400901403428001c007501ca5882d02c014148440c1c482 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 970099028 1250 970097778 970097789
    0x290310030b100e16030606020a02010906210e011d0c09011703400f17011d0307150c02030d051e0a06150e0d11061612030c0e01211104 59
    0x40344d425068141c0305801c0205154009810307940041c0c1c0004c0c1c0340b00d04910550050000404008040b107009070a050b086254509040141491100c5003d00910b90403010540700340340d00700c1240f441c4000244016040500a145090303680c02c10b1621078101c100c0d034180529600c41448644641d90a41007104c500c4808601404403c2c8150154848609141030024158032004401800381c4040c000300071060b00c3c21039500c041e014881d0241d0500500c40c0000804a4120b154590368980e40c003c0001d01065000740e840b41504a059095182101d07e0a4100400340e88100721200300121141c02c003543c0301d2aa860601c1c4803203071600b200c2008c04002c841c217450b507955802e02844090300864150303003074003034500c2d00207000c0c078458020406450465501030804203001c1880d0030580d64400444e080d00f41e40c440c2d2221043c0c1e991030602c1d030f11810710725500c020030306214102c42041e20078082e140c55280142d680707141000000d0717000090f02c9101208241001e42343c1400c0210000818000c200500 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 970100278 1250 970099028 970099051
    0x3020f060f0f01050103020a0225080a0b060a050a060804110d14070806011403070302040f02190309060506090402032a1002032a1f060e01290310030b100e 68
    0x34060002002c1c1100c1600034605161050010510f0f1590008021800140080d922108601000c0062100c511141d001c006907209104a20040090f10200079010720010b0394824031842d129420030031050554003d15000500c21800a0042900c007140c42805840103844c0407107021007a06c5e200c0298401e00d0002d1901c0e40140e204000f036031410000765006025100c096a66000e1040000e600c40c0303200e01c0007078480d49c0c642c00702540d4480294101e41208181c4078107403800456110000d009800c0034441a41c1103032500001800b282072150304d20744070302e80c020054040c0002841008128261001c0003111074900c0c500b46650f5500d44908040d80c9554030f030020b58032000ea98100701403503030915500f500041580340c22001c2c3c5160000d4048540700030050050141c2056000c200010442c41c1d0000c00c03034144940c00001c5004d20109062003013924801c410109040c0801462010b10042e6400c42d141c880ca0101040450010741e24070360480040565041700540d41c0364480d11b818016a041d00030031 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 970101528 1250 970100278 970100281
    0x20309010218100e0112062103020c0418020d05011401140405130203120c1c090519030809130902060a35010b09010c0507030510061a0301090903020f060f 68
    0x41c00c1403064003819160880741c0042240076400c0080c41429944913044c14032010032140340c208500c940000303020f02011108051203012034410441803140c5a0420313005405100214521070a00c0c3c02181d03119208903080d40601e031556424022140807421042e10b081d5070711b40000c1c0000408905180c028035041e020440840c0c00a030400080b20400360840e2080922040b0300001070b02c010455001c0040d44005498a940c0e000f0308041c10400ea1510089003040302061041c41503130402800010ba0b94203a038100c40c902c40700ca0803c900c81101c1d00020305003c40602600c00b56141c8242045640701e82d2541c0130942d018682c1c086001c6410010008011426140c51480074038014800043c2c0c1407501c10000c43c00300001c82541d030541206001740c40b4003040001e078210143e402110a041003030361200883e1074040e070302d080464480443c0462045040d0070117200207041070700769000100440e000d004503403845c1d10b00204070000307105101c01102540900c00101e20b25400600104c0d2141d6602c14040d04107 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 970102778 1250 970101528 970101547
    0x22e050c160905010918020a0b090604030f080d060e190e2805060f01120201121107030f020115050a0905090c1503040b07110a03081005030a140105060409020904060207150203090102 80
    0x41d05d402c2218000340c620f51b0300680c80582c0e1030031840000c5071060440d50769643c01c15404580548210303000540760030402d50135241008040c00040c10421301c103440c100311841d111b42e484249044250303004e5200d003413100c0c0300104031301c181d40c00115042e841c402120300d043e001035040003080d1280380b0344c442c400030181d01c3c12007031290511080d40c1c13050001d40030301c00c1e80d0b0500482203803001c0b030220082d04010b0500304020298445034050895003020400603074480c0034038a0f0003480d540300110310340015400c02c649080c1402d2590403a1083d16402010115a1790800c5030090042030002c140005c9442505149002c64440c0c0300f1040402c02c078041e1990f600e161606083e501440054200c008003c0d000901d10250b450220780f8000180e81403400c11156100d40340345140c8a001074108642c580204071200c01002141c80005444c940040001c1c0b00c20f91300c0004010864140160103904180c242000500041d407690042403081d200303070108121921807030340c518100d13001110700e021269400600f8141 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 970104028 1250 970102778 970102781
    0xc050c0708010209090c16200307271a04050420030304051509030a05060c13080a050d12020415030203070318082505030c0a022e050c1609050109 64
    0x1c1c2420800951a18880e08042002801c004011804482e0007081c410b0050300d038089140000b40d007140d68480182001c0c42801e01603084201d03c80d02c244103425000802302c0f40800c02c03080b48a543c403148403001220320b03180400703491608030f51030030340180581900d03040d40c4038460039000358081c0040d00210030646510122921540916503c00d510174801042160385d203081580b8050341001e182e5880d01c01d41004a803915204441c0240306010340420840003501d010090150301c0500c441c7e10051943e1890107a445054000e0094a00c0e000469804070392409411211030011825100514260b90741c1c044501510881030000c0c0007a8000080c0060345515028400c2480c2102c189600540129622080340b4800d600c0420008000a8060740880803080750b011400358100f019070340d9801c914a01c480d1500a458000c0703104d801081204481c40300500c480454030300035040a00d84048801900b03407015000040e0440e20781c4155807407000c1462051301c400d0010201e141e404600365050030361500 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 970105278 1250 970104028 970104043
    0x1080703060807060507060f060e0a0c090815130503210a05090a0201030c0302040e0a060f0e04110904080c0f2a0105070f02010908030f0703080c090117190c050c 71
    0x4101820100280100b25002c82d4240486065040c038035aa03400750b18049019007070951200c26050f144c0440040c6810111920030b20504805a00700902c41c02c0c20010344130754030315009000c416401b05007640000004d102c07020b60400e085100c007001680d026a45c851941d482120000d181908100e1050b050518511b0510380002d12110180320a1a02440c02a5281c00050002c1d04050700c45400c1154540640c0c101c0d4040c2100c4035844481d8601702c6440c031b0141c0540d106901c480302ca022400520406280099030141d03900400030f11920f1580410071015000151050300c2100c0100070301f104440b01040031482d450f400e100038101900024000c0002c807500b541c02440380c0c8144401d005c00036a031150032114520f5110b00d40080301c1101d03000403103d00203140c1000403603110010b925100c4802080c0980081c2c1e100f44d48842c42c41da9000c4200215001d40c05885000c00c0d00d042082c0c4d24144102440e6511494208400440700361040403c1c003035401311000040030800010300b0400290082c000d00c03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 970106528 1250 970105278 970105291
    0x605042003151e09250f09080a03021f050408040e0c0f0a0c0c0803040501090314120f03040b100e0a0504030c1514060d081e0f0a2d081f050d030903020108 68
    0x441654040068800581c280f10040001c06c1030298078500c0d0307107000362501409004448201c07501c00c425450040d41d6400303c0d5061101004004801b640d40304814065180310f6039120003207504140c508000c000e40408003506d1600c07411400e000e0100c801030788402410340010a039981626030805820b000c803a00c4400d800c00b0712950030403c0240002c0c1d800c40c00100c22294000b180c4c0c02d881995811060405520411045040c0d2001030940206200c0d040510700490259036803440035101e000701d4a400d41c0892080d208800700c181d0001d0465a070395032287c0c0d072141c02400c040380d8450413a41d071084a2411030306140c1d44250b90b00c0343c1c0d155040803150b40592115066500d2000c0034800c1d101e001090144941000402c0102c112640b81e800400040d0b90b10110f40240003521102000006800800124644004c0b80d95481c1c012a2001c00000c46000135803c0e80c64a08c2d15840c0c0c400c001074002b00700b400c01003032440e85010001e0951108005072555500a60300c42440034214800144016805004d0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 970107778 1250 970106528 970106551
    0x51e130522060b0d030302030712051e090312040c18020906091512090c10020307020d080a0c080c07060f020f060112060906020d090203010605042003151e09 69
    0x100045841d40e16904101d0a103045100c10380035a8524094020f44a2480055042040c1c2d10f103600406406401860190134942c0340c01444600700e4400100321001101c0c0c000d40480300107508800c030b807682e00081750031504c3c030403e03207103400b0b4410449603034980240c40403a1f0255100c841080b6041d0411850500051042d01c02c0d490000380b200010000d00800b00344a118038842d88000d105100c0403c11101106180d0720b90b00c0c250f18203a00355940b1a00e042c800c103409000b603054808500340c4040300701c8048a0b40207001c2c0c5008412034580030003641141d61101c00b8400c4a6505d030340410a69800361402503481001003840b58141000102081c80d815440c005550059101445004020600f103041d900400702d9010904450300f0218090041c0d40c0300030b0007181c800900340c42c0110b000e40048030600d0003a0020300c9482d64030307001d010495820207403000000c0b4006080707400c203e070040300440d040b090014028516400032000202213032584003040280b007014440f000030500b020554644c0c82a6107556 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 970109028 1250 970107778 970107781
    0x6060f050d0e071d160509090403080a020d0609060816030804140103021201090c02250e1306020c0714040203060108040602070302010f05100602100203101806051e1305 74
    0x1015180d0301a184100d00a90740b600d40d050380aa10400c9448000c00c0b044a8021350000300a0402c212520f007a2070b0750282d2100110303c010440c2c02103003200c8000703e024000340040e0703a8503201201e00a001900c60039595030200002c031400c200501540e00a4201a0b000041092900f0713000d52611103806910b40c580080d0f004100082052002514121500200300d81021142c0e4001240244038074400114190702031000030882c0d2140c3d03404070b00b00349202e4086880b24000c01b00505180d1700c80602100410084000c10f10040d03445106440c2c2092205c1c4605016528669a0b1310a82c0c202c01c000c11141c1e4030008003045154040c2100c05007020080e0740461650401d0000206144c200601c0a81401c2e00083d203e01010700c00d40c000e20000c841d00b08200280d0400c8010040313a00a00e2203140014447c101e9a00c1030021140308690066400381c0d250980c0d203143c1603a441943c00880c6150710041d68801c80002c07562a13104d07200c1c0e40031400d00c03182c0c188090b844d070402818104030a10500e01915000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 970110278 1250 970109028 970109057
    0xc020c0306040809060309030d0f1a030105061311210f0c0f0a03090317010e1905100e100b03092a1e0f04060b09030f06070c0f060b060a0207090606 65
    0x82240c4d1000020359095940c1d03036500300d030985175106400000004c40d140014106c2d0340e40c4190b108070fa100e1080140300d0102a0030504242c281c2d0000e8400d030b6800300d103032000000c61100545c80780c10108203100c6c0540c10041049240710502a95201c2084001c14a004001d10001952a8658848006415681080241d9140c00c55501500c0548818195640d208009050040e602a4104109160340007460f684070400080662020b5440384124000c28142e01c4a031009802824840c448040600001516024117404500030207410301c45000410754000c034070240007600443c441c0c41e419005021038948150000201036003040c150761035008040850360141c2e5101241c0f80100e90101c0c0da2501ca03c1400002504503071071200041e446443c16000042e000c0c244c9000c1c1600490881c00e0300d00c0202030010342511804126009000a4400440381000485803d00035014a022348400180c908085020843c180d00c002040b50140e40901301c10002c40c2098041d100c05000a0300c0c0440060701e408 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 970111528 1250 970110278 970110293
    0x80a0206011715131e060609021c020906090d060515060724020903031204060513020d1401150308070b01060f0e040207020d020301052401031a041d100c020c030604 72
    0x810240c2e002e030080d0101c0c401c45040c4c0d803c104080d40004010500081403038207003d0094100b08100c0d00c086c1400c4002503e4000d034802e590300412400400c07110640f1082e40b92000358010401e10380e0001c028030055545407901100a00010702c07840000540b814480c20211303400d40000324441c864501040074200145070f4000c580000ca400c100d0001c5c2403180c0800240180c041e14280740d4051001184440360441143c0030b4078005d9004030410407103a182d610030165000c04008020750024100d00603e000034211b07500d0049101c1c800d4000281050201c410311105444940c81a220a100450240d0070322041060315801005142801051041d4254000d4202c41c0b181c50340510580d40401c031001551590908ec09040307074010001c02030f52402604040d521440f02a203489000444008200e0b40d50191113210610115030b0f8841c0704003200c0100300005081e810341d5840300300c0360910341c1c48100402044444030740050480007168809612400929001d402c2107000d1007039115406100102e0f00f40b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 970112778 1250 970111528 970111543
    0x3051506061602120c1005280905061b01050c030402120c0a0b0705070306050a0504031404081e0a050601030b1e0f04022413231315050409080a02060117 67
    0x1a44c1565444100740902420b003900300c2503041e0094107808107103c001d42d00c41d00400489044540e81c4606000407401c519007904140200c0e004900c41507000d01042c03414401070300c401040840081010f220b0320300014203480301690354030134240b004824881180340c03140e004612294032200070034079401000002088003405100e0304841d8240010650240081440780c1c80155070008820700050034a00410b1008203804c490a800040c2c041605a4422603588121011030314210024009080c840c4582604022100e404a081c0e03c619880d8500062050100c02d00a500034498080d062806011044141c1001850041d10b42105410070030b01c402c02c98021740d0010340541e40841c4c640e001c0601314003403000c141d22211140e0030105149182c2d20781081e0b100280e81c0d55400000c8002602c4400d0070702400c124640550006060760608201d1240c3da02c601c80d07002c6a620401c00c1c00b1354610216085034040742043d9500040012842032480c0c040205600600a066020081134500d04a5a032525103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 970114028 1250 970112778 970112783
    0xb0c032505010c1e0507020f3a020a0e0c0406030c030b030a0615080114010306020d0902120705040609050702030304060e0102040b0d060828030e04230f0603031303021c0606030515060616 82
    0x3549d030440702c0304035455100482200d2a4407080560120446111016510b0f411001c0744100600c10307020611000700e51125004044000c60281021300b82407007900648448101c0c14105555083c0d0700d0303175964041020044003030280d0710000308001040710210400c84175810481d02c91303042129021100c0d070341c1001e10f411a44c002c040182c60b51148841d00000c0c02080348040d6000d0700d000c030000d0307580401040000448004440401c07209981c0c2014a090350b108a03084000342e0018030025000c189990050001070b0f00020005107015110b80142c500b5411120075111340651360701003405040d004000784503801c01c00e0345d602c44a4181172080b240c040c0c004508014200440180050300c5074480340c01050100340603942c10344a10b1100aa4001080c600319088041074030031001095140c1004000c0718030350700094481e400c0650654003800000f000000e4048441e440301e01414000c00d84a02ca01c00c041c0d0700c03d03006845412400b000561b00c114001d428a4400c00742005010000c00b01020040d1403e40d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 970115278 1250 970114028 970114039
    0x3061a040b010e1302191205090d0c1e0c17071a04050d0606080114041203060e1602070e070c0506160507021002340b0c032505010c1e0507020f 63
    0x4e44851098000c1d02840082c006500c0c0200a41a6443e0b0000c0c07500d040c14010740740801440e80c503414810703614043c01203481c01240190002d40007007041ca168801040d5007170400c2021841b038903039031024681407691114118008030030110840380710600c020002440790000b003010152040e406081c541c491442171070721580074001a102081103d401c100018083e2030000c00c8015011501c03801d1a480454045070601d074042221688207002e407044606950503110a40700c1c41c2e0352229540c0c4400342040307508056209200000410340c1c11241d0080c80f4103034075910401e40c0701b600d140603450000c0103046a080300040200100607154024282c0d5592074045840600701524540280d041c1142a05200d44448026404443c0031040c010a80c0542c1c1e00340400440aa690b210022400e010390b000c08501e0b0781040000c411000303c0d0181f036105061107840250141291039803118219421703e0f40b598041014442e0051000b0340106030300103d90f0403400d03d1494040c0660000d1103040c0d03807145451066 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 970116528 1250 970115278 970115299
    0x70501050306150703032a0e040209040f18020102012d02070309091a1c03050702040506031606110d09051f02160f03120e030607030b15030103061a040b010e 69
    0x80d0b0342c0b14040704100f9181c8125607a1103001d418000c010741280180c82d15147c02c0303024404070682c3c2100914058200b160380c1c2240b0040c0540401c406903000502084d0300ca038640003611a0300c0301a1180f80c4441100c411003050100403072001a0945940c1c01c00b007020017070484101c1049681e0340c03000d5100d003899a94016904c3c40f20b45030541e03400701150009a0071920b002007005902c91941c100d18140d110031141e44000300300894403070200403991007000340028010f0209000500f0140c002d1500840c1c000c043d50b06401802c00c824059908980c090b00008036a05851004100d00388001c00c84245207107440c40340c0e07a00380b074040341001c20021a41500700340d0b422903550700c3c075100303001110705d1890100c0030081013556001480d81c0036903180002e4a61018240b500d089160003100040b4004030007074058640b036a80c010341540103107c101c403a950084481c42c04030710f4006100004601031481440c00140316002804001c0e0f009030303e400428001d40c13034006e0401d034a81e08a25002001101150800e20340c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 970117778 1250 970116528 970116541
    0x106051c0302160b0a030b09010f0632031f0e0c070c0b0a170906101205010902210d140f0c0a060207030801030218100501080601030b0a081c110705010503 68
    0x40c060020121282ea02451070007003100c0b41180700404445c50940e1b428869804038000b0455504420300c40c1d01c1c40301ea4608070404c00a40200c005028612800352030090041c08080042c252980f13000e50b6a10301500001084030200300f1006490445254005c140b541a00b8004850348015019102440b5044007142e0b40c0d003040119840440945544042c3c9911400814405007240f0509150303603040b9003450001800d032203800205148100c4c20b0040c9039404c139241503906c03802c1120300030081d1804d5482c0c1f040300015854003125425000c041c108d0000c1071810f1640c803903007820400b114078010003028901030182e554404043e03504803200482c0c2e195903a4440404a13203420708000000b00303001d0003ca488d806042d00041e469040307074000e40c0d2281344203989000f100c0007120105c0f5000b040358003a4006014551003400790560190060500141441e03108000400c0c1c0d80e0305074401806984164883c044100c014522415446e20303900780282c076040281d40c000e482c0c80603802500e0402c0400303c0003411 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 970119028 1250 970117778 970117783
    0xd03030f0e160503150f1302030a05010501180e010209012106050a031a0f010f0e07050d0f06030311281b0b09041d06132607060e0106051c0302 63
    0x51405550844581c0c0710015041d6030184407501c40c55101740110707508280b0f4040c050b408507104600f038801039100d69a81041c50300b4100740b1410142d03010301c203860401001602c2481083c3c081c0c980d0045502d080428048001e090b107001c0c021413161a4014812000325036080000b4021080d03103080326580900c2281a01c01c0285500d42c000380e407141c0074000c00402e026108600280a58807200b0a074a1030350b130082c1040f0350074002e00c0340d5804c607481c413401041104e010100960300a0070a2170b100d840c01101038026020340e200074007010780e0503a40708020410503401148518091340b1040251030320500c02d20240030141d47d0300d1810140e080035500b45400b0008052080c0300c2c0920349407041c46485441e01d211011542007015880d01652034610303184a2507110264030003200a42d80010074250b074844800100e40c600c1c0900c01c0307410780000102142c40740c0804054101010406041303644501042c1480001d40b818040181c4c110391400e003003407003e034441d400851080350090454544062242c03508a2 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 970120278 1250 970119028 970119041
    0x4050f040612060f1e0b030c0f130504150c2006100308070206040306090308160c0b01062d050703030b040209030717030f070f030806031c0f0203161209140d03030f 72
    0x7494203a10030400241c42015480750700743d007106404450060f61000305004aa01d0754964450740030307400d00701810ad1003c254100550140c03140641e441803070f505251000076100003d045001254040903014900e4102009145c4404440c3c00181101d00348600380304400200c500010b06400d40002e10341040d501c42c2001c032001580d0202c0300300461101d0f4100104460230580f102012820303100d51504045120390131010001784c00513181c2119920303245003a100840a610b8003070002d10709812101c0031021000789020040d403d42c0347c0a40d2008180350060450b0280c0184d244128410310500300552400910350090300c40d1200d40d550b1124a58140e2491800344101d0760b82070510010b005070401141d02040000a0f22a0700c2c0e032506515160b04040d100c420002092000b0351000d80e451405a01c10741c1d154a4051407801507070302c2c0c41c4064041d120010341c0d010303040d00c040c80e101a99a2440f903004044c1c00c024455680c941c3c004100c5440041c18500d03c20501804064844682c00080660780c0d2246 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 970121528 1250 970120278 970120301
    0x150f040506210f060907110a1401051504110417100509010f0506120a02210115171515060405060a020a1e1e051501090204050f040612060f 61
    0x10307440302c0e41c0c20b0b20341000c404285a000b80a40d8041c0108100500d80ca00751805401c00a185040582d0703040e000b00c0b0304950381440c400c00c0b4454441000c1c007095150310944111101c0800201e89440c0c004401503d5481411442d405245002000780d25000141c0c01ea0b01075034218112b155100502c03180c510720b00f0303145030481501a40f0305030074003800c000c05501040c05170b007410100344541d95030b1408000004588004020301078020b25165001850030301e00c04100445000e14900c44100381e103c02d1401c496019103040302400c10ad1074248242900011a2040d040c401c03401070080110341c01c02c1c0b410b0500c0c05440340c5044e0780c006052610349e9450300c003518007030940549880d8035089405002507554841c8078040d94442417160840740d8500c01d0303030f5901c01c545070030048040c4854403445024080c88106241501d0038000c3c000c00181004113185003600900260301c025840d141030204100d45019039501d1a4030031031402001308200b8901142100002d41c000400080c82c0c80c03000390040c050007811010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 970122778 1250 970121528 970121539
    0x40b07030c03320a111b010e0d0305120711010c1214010b0a03151a13062c030c0607030c112b020d02060408030a1101050c120901140103080307030f0605150f0405 71
    0xa0180000c4e01000e0f0008406e426a41c2c030455079950070030300c50750307030380c0a003000e00090b000304008480c041580f1003854011005281500748019075110007400c44000300d05c80b40000d045514480040080350068642e409100c080c51541c80d403401000700c4251080030403079001d042c0c0316a103040901c400f98101d40f0043c002d500700780116050340e00041d40c00d035002d0340103140b5048855038003003146442100390758010f0700c201c11b400d4010b44220b40e00541c01d13404e240000c0d5042c840c43c40b000305603495410242081a20a0b04d442d0043d1081c0d1400d5450b07544140c1a5030301a6202400400f03103010304d0040c629440d00780c01d182c02c49429132800492402c800300d40f4082c0d00304400180002c0d54000000042441c045c81d43c0d140340d402101700554034240c1d401a60071a03640c4000707000d4818100e10075526560085011f0b4000103080101d00280840b2410036401134a060300c0100070854900e4040c014044400300d807070000c00a180c20040000d507015000383c0501400080403944482d005040b10446d000b52000410 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 970124028 1250 970122778 970122793
    0x7091203050318120904020708040518010807150f0305060d050610061404050d03081008010911120d141b150105181302010e06040b07030c03320a11 65
    0x40c040c240ea4010303601001c40488900380c12422240100700303151256940d0001030301d040c110b0400c12000c1c2d044040259024001044002416602c40b008045408010141201a90f140412440c20b080066000007001c1d8411881200c45540c8410441a1110780307040015050716a000442d00d0201c0180c0c00804500c9200c042c0b1a201190f45075803021203403a9030f00c60440250b81100000d0a000c2d920499402200ba18038220009019074035580d0700041e40e00403151210b41e607941140c00c3d42c10300c0c43d05441480e810003148401e400c00034550b02d40d0283e82401041c500036904401491000340041d6848140070103d1100d003038120b90014291350010350001c480c0070055803d904052440203200d0306100340c0640c1c094440d008440f030201d0340300d5441c40c4102002481c00b83c006480c00d0714140e0708183e21000400c408540881e0300005090300c0c60196860a0103448540385c040c15240d020000840c2284c603010203641c500b240605400c5c410036a440c501900c6100f04c8005542444a0540224032405040ea = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 970125278 1250 970124028 970124033
    0x17131502160803041a0d021c05010e0a0b1011030c0f011d0a12080901091502120609220f050105040813060e0108010b070f120903050c1f08070912 64
    0x108940c1c004906454980003907a80d1480560b41c2c800c500c04c1710b21500020940002c4d085144001c0c01e10000d0402c8094034203200110b2188030f030482034044045141d0b07078a0040c0001035060501680c00100540308001c19604540069000b1001e03000c020100070302c0300803414090a0071310a4442003a4a034044681e1424103101c00da000e0700380b0205441505c0d801501003940264000390242c052604540300c241c00c02a2860100c4d030703201008040398003031743d00c41540d08000769030702821440700e442c44000141c503a10b00030080303003400c02e001d0003080c03203400c145003070242d811100d11480909420321740707118052840d1482d1075009103000c03803000b5000354609010801030048450082400100c0e000203441c5041c3c0381d0b0030580b051a200151240080c03180c20052001e042404010112a80141049aa4041590780720320329070450070005800610880340c10810000f00700034409585404030b400c150701e00c516541144468005c08100410800481d01044e07880303000b02c0101010b417a01f426a41d0621441d070 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 970126528 1250 970125278 970125283
    0x30c09011401031112061c0b010906050f011403010b07020f120312100e130f0501050a0b0a080105150105032203030203070f021501030602030a0e0f07081917131502 72
    0x6185002c03e040548000901da080c03004c65100c6004104240701c0750306e03102c084c48140e0080c8141003000f100e001b690140072803120b00c1c2d058002d00e824440822003505103020300400d01400d4080f1810302405000d0350401082c5201503a05480c131030300b029600c9220701d0000842c00078000c084c1c1341e0004800d0442d4403498001200902c0c01003242124241a80c5940040e038020789418403844450380d050380003007a048801030600b900094010450310079644095124507084617001da9080d40c1095407440c0c0030f80c49040c4900004014060100200140d14003098550050004800c16a0400c1760000001e1a408408800d043c00c0c6906442c20700040141803801a00941c0142c0b40503000c110f2a55100008a100045650030743c15102c83c0c0d0b05003039103507a58000c040c0d0009001040040d0b251602ea807000181000300114004842000f069101d160101c080c0c00e0440c0031b5240c0c0c007401411500b0310b000c01c000611140c409145c1405655490f1500002c04103000c0054000018816500012180480d0300 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 970127778 1250 970126528 970126559
    0x60f060f0806070807080f06040c050c010212010303021608030d0902011b1506150c031d040c0c170f043803090f03031302040e070f1205010e16050906030c0901 70
    0x541c0c0301e0300200e407186501a2884241101d440e034201c0e401f64001146410a500261030300003041c00c05505088003002c00b142aa0070002c04400c9000d6402c00420525504018404482c02485040520103081004240e240d200300081240700540b40c2003268216489109211113525481c11034608204082c542500e01c4003100343c103106500e0030100d0100704640c80c0d001e1300d0022140381d2104142101c0590b0305440c125958041c0846490f03c544195980b921079010383c00800516680300c098a000c40e01c0c00d9030851340d100b00107003012003042c08034103902d540300012034040e41c580703221844030007a11924202c1085101b1070b84103206001c0029014500031580080c6006d940700c041a60750f0345500365507079603890104450a0412840c50b402c0000503080c44d5118640005450f826158056251808d29045071070550100c60311500340d0202c0b0003803003401c0c0300740d138003c84049000d0021104400110f8030900c035107002d0607101d401443c1c04150300c0e5404103d0302124082c042c0c681c408641e56100d417088440300c0d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 970129028 1250 970127778 970127791
    0x6051303170405041e0c0914010315080d0e030118030807080a0f140103200108062e0203210606192c03010b040203222a1d1003060f060f0806 62
    0x80c02404090031f80141e40100540750f80c0480b50f0305d03440c84000114068024000b00300d8921a02000c081850301043c0950407111748141c1b91518802050707030034075003140c09800205800c1190f06441100003544148826000092840c01c03c00e41c2e100d400c3c03450020800c200400f00c0c00352614203c2c0703440400401100c0d04032409042d960b10003480c0b44008094041d10f08c480c6074006443c2070b0010b4101d140070842c1080041481c092040b111175038810707503100d62061014000260b030020411446181da440b00e508130003041030410003ca0708203d008520309004100c001e07002008540c81c10503201c3e210740402800100b14520a61611480030101200050b420f0301042c041e5082031184080d034180fa00031280224101a041d500442c02001802c0710003044100880b40280e034945c560540c40307120800709003020325420541c0655454480102c2c6e0340015a00c1c581103012150040144140744865100304582e000380010620070400c1c60410000c1400d0f402c4103203c0d0a411070040341000000075a50720821 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 970130278 1250 970129028 970129031
    0x70203270909030a0f031113120605090715030b060c0109030e1e01051b0f07060e0f1804300809010606020703020619020c06030108031306051303170405041e 69
    0x8682c54491034030780c0b240446480100b0b0341c1c1400703400030324030950200413242c0d031485069003030100d011a8030114917060b030f00c40504d16071030f1840300040c0300b0f8130700c80c540d00054040002c00506e49031148070788401031310410300703014980d844444601e5070715240200d502901c3c503c1c00800c00940305290140421360100b600784d0003402e4000180040900c15101c00b00499070584446060850780020070205031030300494040180190300500031440f0041242d400074041a846140c0c8006500f018840511146440184141100201944070352114000c01c0d40003500480c41c7d03d02e40780350b030b0000015070fa03e2400410010500152601310260700801c041c2c0141940b00003401560f9a07a4030880c0e840c8864000a907100758108101c0b075410340e8800c104461018140156644010204002060398200741d00415554000081d03404d4030f0b229030040c9502904850a1050034a49160080140458075001c010101340c520400350b500daa21200503240140401001030041000c406c0461220359040100d540406 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 970131528 1250 970130278 970130281
    0x3060c0e04021c15082104030c060f020c0306062d10030f0b040c05090607140a060c0f0c03121d06090c090c040312030b191e09060f05090702032709 65
    0x182d048409030784c100d40d10100148500f40c68a2545a403100b00801800b10341c410800001000401c13122070b2900a010036258044009a080c0c0042e00b40600611998800d401c04c4040149941d103a101c0d8014565920000e510700090351820740300103003203070141c66a0008248901c00012641a040807450380310405082c010482510203110903142c0c08026080401c41c1171203140c1c60360501d40090040c240c01222202120240000cad01402c2642070b000c1503070702949510700c0c10841782c5c202c06000100040c51170046021180e58500400e0040046c0c1c0803070909880382c1d030456840401d0160801145c0c461750540383c0c0342c02c00c10030080d41d88120064090107407503210001410910908282c90031030f50441030401001c50f805500300d0082880d2130030598070650918a10b070a01920140d117902800700507400e03503245460503840c1d01aa4441c0e030700c41400241400b4003070000b1583c0f44040c0048400546180724503440b0a08180e08500400c00c0604005008040080c0005082011040340b01404e60301050603 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 970132778 1250 970131528 970131551
    0xb030603010e1506180903030a021c0504151118130f05010e01050315070c110409050303041505100b041517090d09120305160c1505041703120103060c0e04021c 70
    0x105c40206c40e00401a001807000600807000ca40042800a0802c143c0c980d801ca000c00da00d000712502520260b50b06001d0102102d0359807464403a00000002101903141000301c016442c200041c00d20301081d018030034402010159889030740100e161440280810300c80da43e1514030016070481c0034428540310b440380c1d14540c03448880c410181402074040703903591101c060031502d5842e40103200c024020b030096990747d0a0302c0420b1003840654001c603c074546040c00103020540d2a0142e80b0054140580300d064050204900c0402e402150121013580ca000b0118450410381901d071100f0059a40303401c80400004c1141c0c103040410408140d402c0d6071901242c20303487d59070100200b13803508401004550100040854103c4c003204c5440c02074428601100104e03190340800044c0d104c4a40c4030400b04101113014481407e00303981c2020807092410003542401c0744a05501e401080610020700056074401c41e10328028820304140c014072101800956a640020400c00c0300300e038004815080b03003858020306081c0c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 970134028 1250 970132778 970132819
    0x506040b030109050c12090607030e01061409041b030f0501050c0f032a0a020a050c0f030d0503071202160539181807080601030503040b030603010e1506 67
    0x3a100c00303090203401d607800c0402101c010600036100207480442841091102a05203096074403803801140601f00501f005a4003405680600d4500d100c0c0d039042c1141400340c4031440704848500c040c1201d4001407515241810325490b00b51341468400003801c800c01100b40b1070000305e00356441b4880c0008100554070a95111214006e0107001c84410b80d0800c082000c2d0556001c0540001c918034000380e180c4440c0100b000f01c15441341c250103001da00500c0300203080c0310b010300614449a41c1540c070b52003502c1040c400641c40703c44001418040c0b01020000c69109803154642403240d1080a07421556021188400b440722054140221483d01c90317014030702c112100e14017072961880400c04105452040d03001e0141e1101d6a40b8517582d4001007482018080440560072590066030803121b0340740003042d1642101d040100e40d8000c4003223680008010400180000b0403101110440703149680c40743c4031040001c0c098880c180082d14984542d40700390700e101e411110901e000c1c250444040c0840c10240a00c5030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 970135278 1250 970134028 970134037
    0xf0605161d0306010b0903010f09140c0f03060c0a110303040c23030a0303050a11040b0c06011a040608060112050403020c0f012a03210207050610030f03111e160506 72
    0x40c2c0542084004014101c403130b4000d417411240003400814244502c3d40100c0885507106000c2d6000a03540d0074050840600f0b20146903e0401a01d05090300140c0c8408682c1d500000352541d190b1003c001201d41204e0300c2104041d0740b601983e01600d83c2e905103424101c0031102c0314041e501000060030500715005890310918050a24090080d107005181c60b24194010480104000c08203510344a544c14017403000c10040018007a500501910381118080f001c0c540041600107407020810303409002444023800e03098a003220172918083d440740c0d542c900100c07051582446a06889801c2000b84420150081140c9040440590714820400d1300d036801120048004901181881c80c000200d0000c181e44011919800b0b0103424445502d104080d40d075010200e13003290010005038007140c0c00040290a11030540c12100040a65881c282107850300c800602c0303055401014415540800d03403170f8410900c441480d034042142c981165402c08288582c032030301c0507980301010b4581014049000e241050688 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 970136528 1250 970135278 970135337
    0x101214010e040b09010e070605071101141204031209080c0c01090f06110a05030f0c06060406032120010c0e100807110a0b0c04090506090415090f060516 67
    0x703003200c0e11035440d4030110582c0504008025501d459015030707000b0f4100a42002405144c1d030345036481900c0e007400e10036921018002c80c1049105004106032110750403d0343c02d0351009540489840d2038603c0e082e00d01c0c0c1d100c01c02d07800740e4034144024042409844409818040080415507044481100c01183c605180c4d01511021013032811051002520a0f110800f03100c001c902181e1400006071101455504035200000740d4642c0040c007400c00c072005100391034008006481c1800018110b80e80e01030942c41401c10702d5141e91541e9034010400c0d11a82200d107c00383c40075848156103c0301814140130340100b000d040042203a852554400b410108030450340e5051540e00c0d220962294441100d541c01906030615052094002d8140407402c03001c1506d000c0c9031b5040300e0781d98441c500b444040c03d0b05c50003495107100304107002c204000f258134050604001c5240070400a001a110302d80001140c0c0101405000b03a03207003600300b140c0210401100b540046503500e6400d4240141c100640c60440c411200 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 970137778 1250 970136528 970136549
    0x1416061e090312020d06181512050a0308070c0c090e0c01021b01031113060201060e0a0207051209040905030706020304110307081c030225121103031b0910121401 71
    0x202c4031844801c1e03002c0d00b05c0d4003640e4808288590340740318418550002d80080b90701d86540d449941c8010a408100e00010800200d80c001881004e4450940314001c2190107810710031000001400d0300c1c031070410411041c2e448503d07440e01c1d9844a000304014018001c1c1c201e55882030b0712002500351300014840071000b140350720150a0301e2500d0011000303003003044110390060100344007440110042d040f090001e001142d00000b5824030f04001075030300200282030503148038810002d0b080880d4000c80c1c07a5542c40411085a40c0d14400400820000c015820020700507010200d0b0050403c44a500114003c901885a0300c1f18002030100301511030a04e4410300c2c01d40c3c0d03c8200c0b0a5002d0281d985101010580d074200141400801c8041a1800340c003441040c0a000700d034034906041010300300f41e400c65076075145480c00060484610300c2e03a0700c1c400982499034400442d042e1401c0f401c0c0703a808641428101403c44000704070721550103008400154910030620f030400e11034900c0c2c0902c180042e070484d80007111 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 970139028 1250 970137778 970137797
    0x10609090b04060c05040315050a0c0905060d05150402040b0d2301090509031b0d0f0201110913060f0b0421021c02032d010e1605011416061e0903 64
    0x88140c001c00c444d10032501400000c1c4400400300326954406460181c41716400b00b26441e180d0340c3e030300445401000940610813414000d02c40c1d03403525026503e0302d024003280010191511070035000c03005c42c8404295031042c00040c0c0480d003500300401500411000b05010b1010b08d681c0e920b1441491140465051624103c000400107243d40c1d03089241c210000074280c03441c14440d0303a40d03a100401c0c90780b0301454075404506a03103002d95104120800411191000b001002000400c151251160004e65880340c540380000300110001644103500909036420704620403071f03550310240b0050300644501001c2401910350062400104002105035139130040916078414040d0b04100780403108810706070b80620841d24940c6ca4403000b1074500c0d010b030020410f03034240001e80c200007a0940d20040c448880c9a0880c011036900111409188025110242041603500c8114101c07070815001e07921781d0031912001c1690040c180041e0f940140d8240c0019070b4920341000710346008105a644256000703000034425032 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 970140278 1250 970139028 970139033
    0x160801110c0a0f06060317030f070810060c0213020403050c09070309030507062d02091002030702030c010c030c0602040b1b01020c12160c03050c0906090103080f0d2705010609090b04 80
    0x1034114404078803c4000143c85d036120703115810155054a0800c0a8035000014048599142e44d2626486052880c00d680b0034a0450a1810320450300d10815007408082e2104204560300c0c08071520b604081480215200d91703072810f0059a455040540502841024001c110480c0c0300340620507400c0c0d01038030303101c0c9807041641c0c890307000342050301412464642104444000d0061201e034240a81d07054400940c5404640d000c001640111401e13003000d66004000321001610007040001e5949424200310b04200e0840c203099620000c002e100a1085100003004940c0283d100003a2004000b05040c620640350b000403c0c034200d1146901c1d800e91a40305180710390107045094000c280e15220a001c002480302e4503640c10481c03600c3d03a0800c031040e80201d440141340c3d04044040c1c90740400115060620780d40b450f00ca04c8140c0c440c014030010524400125890700e0b000b10740018910181c201c80d501d40c0c2030000f640f00703100710441e60000c5031554200740002441c44828050340312900e4000d52080241c0c2c80e603a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 970141528 1250 970140278 970140293
    0x210a0f112409060d0e010608010b180a0f02071b030c09020705060f060f0409030503041505100b03090703140a060e0d0207060e040f0c080f06090106050306010f11160801110c0a 77
    0x145006900c110f040200c9114901d40740140000030340c00b8030001c0390740c80c200b010840c00d40e808200028000c2182d6103c0c03d2200c82c50700007032600094041000070303c155040c49241c010344640c803000b41102143c2a640c1d05026034400010040b03900500f44482d00c1350300d403402e00c030a9101e4980060402d510400c0030450b400d850060080c0c0080004041d20200000600480c080d03514000b42900403403404001c00003030002d40c04540e64080d2420f10208968944106100c03690b00040c0543c80f408200840007440c803000070002c10380559040f4080204464045100c1c81e500c100410088070082d007040c440d2030790b030351000413070000382025600500031003402c1840480b480602481c0c07540d0b0082d10742031121502c0b01e007171107403400c21000d42d543c1c0505468003400000001034064041e50146a45100400086a00c078040d00d82203102460700100003000f070f4000f22a02081000c043c03095000d200300d0180642c1c0c0c90500ba5003180c00318bc0003440900c40060086016005025114010750002241032000680781d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 970142778 1250 970141528 970141537
    0xe0a080a031503050106180b0d08041e030b2404052806090606091a0a090b03040809210d0206040b04030f1106011404180f02210a0f1124 60
    0x28100900001643c0780c40302c5094680c1584284110302d000d48100000c1c100078003230300c0010042510451041807903655844194803aa03c14261685004124150900348a0845400941e000902c8a20740d0918807551040460000c0b07550090740c1c6e68060600e200d003441d000f05441400c3c1070980c00c818000890f140036042c22203007141c144d4150350b607001051040741c07442914054990341ea1601c281c07a050900001c0801500b60f0000000d140c02d2004101c040c0e84989840705680c0b4040c4401d8036a2203030320700070174640a0782d050903a000003da140303860b0711803c030004000841d907540115159480d0440d0b0a0303131201404d54011382100c0d07010000501190180003520420421032418075100700e10f5440703032801c0c00c2c130030781100c400007488400601103031030b1078041c0c502d02c7d541d16080d0f0b1910480c990b4a03201075180080c8000e028200070924145808900b4418215941103e030940780100c595241400840989000c00c07140d041035852408603034200909545010313142079120f1451010388400c02c0b45242c21 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 970143884 1106 970142778 970142801
    0x7081801022d07172503210209030601030b131703100b042108090a1e0902251e03050c0708030c10020304060f1e0e0a080a03 55
    0x130204500f0440900000407240d0700d0744c5083c91021904082d000e008a40640e401240c400d05811045011885042d03c410310440400d0420710781c03c03030060b1347c0c0494140d4404001400001e107030313100554010110004c10b0800346100d94030302c03040c1ca16500d0098503406010003030041c60b11101d03400e040078100d681011410700e400c05242040e80f8010100580d504034102c02c035602440340c0e040486d803440a018102110103078541d45110350311250b0340c401e0040703255a04000940b802803482940e0b80b5909003001841009101c080e035040f02042c001d826a4400e982500500e043c404003060102403500c2a116a0f440306800c1b43c4403802c024940d40030b5001908108541c4920f190042004500515107060050b01c035103da0904100801c0c403000301b001d6031b51410801490300400700d61100b480c60040c0c43d081c40f4a0070b50408164440c04080802440c02d081842040e40383d030b0080c1c100c00b02003403 = true := by decide +kernel

theorem cover : BRFrame.Cov 969964028 970143884 := by
  have h0 := BRFrame.cov_init 969964028
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969964028 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 969964028 ≤ n) (h2 : n < 970143884) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
