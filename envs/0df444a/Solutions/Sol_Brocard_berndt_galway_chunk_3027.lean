-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3027
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:27:08.874128+00:00
-- url     : https://prove2.me/submissions/ea38634e-57d8-4617-9af6-da65ba756c55

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 544244604 ≤ n < 544424460 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 544245854 1250 544244604 544244621
    0x6090a12021233040c05040213150c0c05120c120102090a030804030308070e0f0d1a13170a090603112703010f14040f030203070b1e07030c120b011403010e060103 71
    0x90448500f040c0e0365002091503a40103843c019523001ca1141c5040c50301141c0003005140e44001f2240c101486074000700442c6110109403061130018078005121705007030072000e03645c150107030141980d00d02c80c5c400c03c1041c048000740340103e59001c2c02004442c1d42c03801d50781401140301c0c0c030300306548030304c0c62030040c024940040900d014031010801c1a034036912040e0801d0701110080b20038410852413440d000313021481c01c400f0313135002007200010001240d10203924401c080b8050300d242408141c4c5110b244003503206180160002440c0000c00300700d0207010341c0040b200010361403012428160080780000c0d07002417000b8805c000c0c0c01c1d0703c510f042d03032418203226002060381c5640080c080e0340c4103600c90028401c3d000d04000d14248248000d00c05040c400e100761881198818029000c0782051041c400d084e00c840d00c00800130110a078003060282d4040d00c54009418510746450301010105440740b030060a0344d040e080c2c103010b0b45061101e08454032a0055001c0c0000001c00c0c0707294201003000608540810 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 544247104 1250 544245854 544245943
    0x313180c110606190f0b2208030a0807110f1501080f07120302031e03010317090f09040804050a0815090a0206032208070501020a02010b06090a120212 66
    0x1c03201d480403202084880d4041c0d4181c0b00d100c0303505210880114511200d520502c00c880d4450350100340c81044600a00707004c81005c2d00341c2d090743c4060010000441d01846150f4044e4410051840b01c64011403400da8004514200404c0c100d0721007100070305028688200700351f00d03000801849400188510213902500002e4000c00040358502032050303135400780b4024414414403190041c000c04d13100f0002ca8918081c414001500c0b1000c8882a42140e0028001194000074140920f04401406c2040c2d4000c000010050741c0702200800c1840075950000d04255100d000c200f00c0420341c0d84402c04c01c14001d00082d001050b81c001c488100c1d003807142016201c2544d5400c400c0a540c050396454064a41281102c140e0311f1720b109540f8603034040c01e004503c0080696201180e00300034000194081d001c0d0030f80341e40091102030894010401644984102990302a202880501c5201107009a14121520180500c41401c080101c03562a0a140c1010410140201c0310702018090a0143c1c5900c8080e1a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 544248354 1250 544247104 544247117
    0x90a08010605030d1d03070f150f051207020a02090c04030b01140a0b03090309030703141e2e020d050105150301140904020316141809070b0901020313180c 68
    0xb041c001a403101c503a9914402000b00c0344402c806865441c1101054509004040300c00c8039590340d031034460103290740c0700b030304042a50010a606510300130180418403030410b958151804922403040b82845401600c410110302c91b8070b80f40390040c0c07600c030303862405402d0005c0429102e0345903203002591640c0582100304401c00c094041c01c41520f8801005065a80710401c0a032a0381c0d0b82d540007407450150314420380c0d05108140000084c8000404404560b080c9107041c0c5002c070700314049850003903890b0740d051240c40d8400c01094030040700f224031b0121031280880c00360780f00541d036200b524243d0b0041103c40d487d55a0f02c600400071840c04076991001c50b018203048070704661510011300501000c00c40d816003c1c405007000902156010700980700d6903584480340e0070f8043d4039036004e0070702040741d140703010f000360141c0300410304044010008a00c11003107070000300300d01414240c0341c1c02c054102d42030141c154401840401208808051030801400900c401000100e81c01500c0b881960604600030092254 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 544249604 1250 544248354 544248359
    0xc10021603021315090b03240c031e070302070c0501050315011b0204050903120906041a10081c1b0c03080f040f080105040308070914100519030f0c03060e040b1e0c090a080106 77
    0x10808c5803507000041d020041d80381d81d81c040a55003142078041200700c4160303c0d901084a481d82603805000c905019151014010361140300648440c4000e66000d10a00c44202180c46590b215240c1020146044910b0303a124100580c00701b02916010749040090780c20110780c41402440030b003245c0f6400041ca10040145041a8942022003041824014490500b0b10000307a032100c0701c1c10341013000b00314600403103071103000c0282e0f0b49a02d01010f4205c00001a854a040012400d81c01e96030001c0c0798024031914060307465a03894505544c85440c407180c4810041c04001034100c92400070070010141c0100205041c0f410b0701d07006146840042150050109008040c4040360b040e4042a002e41d009a440c016000640c0f802a100c0740190b84443c1d02d54015403150410f00ca1341500985662481c010342880700e001007813004d0b01076403d14050307404114001b03000107010580016845410000040042d00202c0249900c0040344c141251302024a103000100c07510b00b420b1405224005194040082103000d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 544250854 1250 544249604 544249663
    0x207080417120d0b01020a0215030703050c0c0709020c1c020f060c0f0a081e0a0605090a0509031c06080106030c051e0105090105070203030c06090c10021603021315090b03 75
    0x40e0f00c3c040b10f01c050b40c4062502c0c1d16402000740811540c0c009244c04484644081e1040180e44200e0b40c60780000d0900005c03509481402050b14a614440070207008580d00307006000000350491800d1242d10701c07450307040240381c1c10441d01030748450b04540c3c094410b034585404682e2900e40040c00c044000c480c104a440100c4100d601a0b5101c0e046c6481c025010380c0711481c001060f9000c0c010345002040d140002d00c0b102513110b5003e4801c444040d1010712040c0d495100060403110111a1001f031234100b0040b945030390000d05070145200a1a240000b40d054903070400500311007a0360803c49111800640030701c41850b0410000c0e42d00100c000d6100160506030000804034024190068103105003c5814011950240b0a4601d015008012107080307140860302c1340d41c1e50f56001a11802190300e0701141300b142e44003044010300e40d002c01254014451440e806e01000c640140c0a200f580b99554031b880030000e080c01c03099001000a03102c0030a04040c3c203800c050819691010a01180540784c0030042241d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 544252104 1250 544250854 544250857
    0x150308030f011e080c0d1104050901020c010b12070312050408150a24050f0414130614010f0b030a0e01020307090302120c09060f06070203030d020a0801091a040c0909020708041712 79
    0x40000e1b10017800100041c1760103244c0c80340d6406602d030300509040c05c010003568154043c00c0c0880100d00241310113100401848481000e400d042901a0054501400411101035403100c5c18500b03464038030300c1c00d60340d88002410586104d444414a0843e141400012205405622040902e0b0540d9400c01101290311403000340b4180f1030f05006501c402c103101c086e030b034407135102220b170300e4040c56426400e2800e01d6051807008104003040721250314000c0c09007488a046920756059420b03e060001d4a1402d0211283c0660001055140d800e030b16250100c8100c0c100380050340c010207540d228000c0007815407040104070b0070070000001f001d81c00154003000c035685640240350400f50136540b2018988144c0041a21b1344a1003070f01030340600c0002620b01034040d4a500805200300b0383d5070360342a07a98948403a0002c0e04c003085008028000b203070001902e03e280503801802a804541089407445680740908001d82c2c000e0f920030b450410300440d040060980e1140d520505030140700141248552480d0f01c034905 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 544253354 1250 544252104 544252123
    0xf140604050d0f0e09042607050a0606120510090f0c08010b01090905090709110f270307051e010306030204060b07151104060c080903030409050a0f06031203150308030f011e08 77
    0x1001d088143d400c6400350ba28048022407048a007c180d0301c001074140f681c0c0c0e400c1903901c11681186410b00020384c443c8082c0c0f000d8441980203001d07100b0051800088030243c0f05804c41660f4070052001003c0c00038903140103440040010900209456140c0b0340098484c138081c0e406100d5080c10142008450040422441c050b03454a520016a02883e482c881c416170182640344810b0440020b21314131004e13480000c400c80102c508071414011318840c0c3c00c0c1901e8440d2407107002d40082c1035540038543e0000d0b0b58105010319006250005c0d81355a20380024080c0d941c0c0e03512000104a000801d2810722030b50a802d0380c90b00040800a012240b00c268241d50581b040340f0519040141d0100701030204901c541c00c80e81c1080e4002e0440b910f450310744041000a041c180e03400003160349440c3c0c01d0300110301d150040c001100c3c1c10000d03105040d840910168050610a0b14051101d100c400000c4009403440300950300031007081044013040e40c100204125001c1c80c084802c5c2100384003440c2004a02c90015030100ea = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 544254604 1250 544253354 544253363
    0x509010309050316060b090115080a0b120d09060f080f01210c09020901030614030607050306060d0f0b030606180a09030908030a1d010e0603040f140604050d0f0e0904 73
    0x90321100c0341071150540c040d20000e1002403040131201d038180071182c1c11017805940c003100c201a541e41c1e034020003d9003903001c030500307800315402070006400c4a5585e070107100d4200c030161080c00306902c0403001500389050740c041c00b00071602510713003070102640c0030079a0ba8174000302d801c1c88991418082c451843c10041481045662104180707800c01e4584111020341410703512040900110352620b00b008003030b4010690460000c0d207400c80000d007440c0083c0e0710901503040038000c6c2c01c8946803032904803074945c4000c040700c0e040002008444030a0300c1901c51004d120304400c00c0001c01102d0001050b00f0000051301580c4500c42d0500c005050107031075040f840c0c0208040000080e40412880c0607601101d9035842103007140000329a018445401c180c428203440460748003254038070050350040d1000420307220465000310082c00090b0004a8074084030074458000e000080b00801440e240074a0004206d404aa05410117000c3c400c1860300841074001d034100034140030b007d01c01d521011800c0440c00500103071 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 544255854 1250 544254604 544254611
    0x10240f0e060409051c18420e09010504020901050d020c0712050c040e01022a0708031b070b0a0f030506010e091014030c032a0d060b03010b04090305090103 68
    0x262950b44982c4090300f0250311400740c500c0b1040094a500700c115900b03140c00c022031520800810710320382224900c0141d52182000c03410084200300a402d40035003c144076180e040b00e08811004d2061050814800d02446540f41480b10700c0100a00c001d4032010f80c000c500650062064001c160b80180039102080c2076140c0c0180c5a09900020340c0c0b42c042658400319160070b9200890040c8000410820f00b042d400781d03020700010050702c841d5400c0b441500a080300c0003015004d414401500415811006c841c03100450f15a29210001c45003598415804444040105144000b03082c80074010707080281a136000e0182130041080c00540040650713070600d020103507100c0004c0c0f0b80c1c0e801348004810300303500905155024641b0500b06c207a0b0300d00600030860444030510005020340703000940000220400390103080000200380c400240841010507000904a01d00c3c500c074165140c00c05071000303c1e0f008400104600c1100d030241402c40d4600c11050b0302035400d005413800400c0c0c0000c101c4045180a10300013 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 544257104 1250 544255854 544255861
    0x30402060f040f0b03010617010509070e0d080d0b120109030503040609020414011512111b030d1112220209070509061303060c0809100b0d0510240f0e 66
    0x100418801d0b50000e1601e800051070104024130070202842c142c82c682d488086888440c0021001300784000d204690303015144030002003081c4c0c41020180785078400644003842c4608503642c2e400340c41d080705080e8001950745141020061504065080d031495000c0c00802000d40a605d009000e484010405841c00d5280c0c1c01107004c548455004900e040f1010868102c0d41d6103c0700c0c0f401070303961a500c120000501030f001001007407009200346000340408400b02841e00d2038031300075040c22401c100c649080e42e02081c4115400083c241c010441c5010030350f00d00c0c540d40c0c402000c00000d070400250498410300088410307800401c4050100321140d0350100e070b0040c80c2e0307910f054041b1400d11554291a40006000c034152403004403100a04c0b003030f203100388000c0c46182c49410044415550032120310b1155800450b80c0c0b110300200d988464100e5501a1000c44d10400c240c50385880c0088480e42c002d0b0036980c0e031081485000103019001540ca01c40e041009480b4601030540c0d0080c400e0b0302030525585001d4012 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 544258354 1250 544257104 544257127
    0x2060a0b0d020303122509120302071a030109110c0d0c1104090303090b0603061303180e130c050a1208032e170105070c060c02120414131103040206 65
    0x22201c1d080d40101104d0f0f841c95450300300350300d08100b80d85244a410344031481003503890000301c22000b501159910300c03410500c1c00500940f14620704a0903015805801004034007160304091040d05403400340b03201541d951402c0244412941a1220154089020300c2100743c3c031840440c00c9980784c4014a40745d0080240b9040072108600c805007840e9015192080580405400d50021f442e818042ca62020760755903420705054332050202d03442100d0034452040440064044e0003007000240000300c02c0d00700b02c1e80b81c541100c040741c2c0554400301c41e44289203281c01080b140d1441c4401400d401c0c1c0ea110150f5150040301d5440060581c001403400e040400024a8111000782c1084250f10007880303606004283c04010401c3c03030042c0a0380d0400c0302011404d421401c014000c4038065a00340c0d0b180300b012003080c3c588400902042c246403046000d0507150141031000e6002a2000c0c18a4051000f060b82089007048045002541c4006003242003140040c4100a00d200f91307a40103030180d4120340d84a414000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 544259604 1250 544258354 544258369
    0x507090b0c120d06061d0d020108040501060803030c0706240522020a170901020301061d030a0b16020c010e03031e0c0a0c050901050910050121060e100b0a02060a0b 72
    0x20788031003030440400c00f5031420280350804001c846803501c1c0c10504800c0f003400c8013a4401c0034240d80e600010700103404001544900005030b40300340035000000d001511007019508560058416020341080442d540b0140410f92240807008a801c26840540d80248401c052040c20b9a10039107104403422844440d10305840740111135042c07100d10085640c0c042080001d0058000c2c5030300e4240080b011000030706848014800c80c0c0c140e48003900d40311900112510009041059802c101742c02d805110030003000542c051400300c1c01030b43c0e281c1a11444021300c0314008d1404030402083c504000210b42180c910341c41c04812100d24030100414800d03079600c841c2c4400703220702c54001003031054441ca4242800307200d0b0f280c044406a80044407400d10310790b40c4400b00000b071542540c51207008241d03da401c020f41c1d8001d040c60821700103040030742d80b00c203050081100202c4100d54000d4041c4001c1a0420420081c5481d418015044a842a50400b41c2044008ad50744800400c032007411a0394041110245d030b107101 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 544260854 1250 544259604 544259623
    0x420030a08030c1308030301090606210c03110703080a050c073215090709020a1d0112090c05270a0905070e0916050303041805040c080f030403030f030507090b0c 71
    0x1075600b20f02c05d58902c91255170b54401d1140e03007201860a8004a0034511500c5103220101105809001522107420300c200200760751243d04050584e601034015080c4440310207840814081d44881c1d08034a41040d05a060718401840b00419800c104501c1000461107400c450710012040584010f202090b8004690034881d8182c0c0c0e0b56620030134404030b02158000303032650322a105240590350030b45c0c1d49046441c01d0340030302125070000c00e10b20155107032048010701442e03203503410500d8540e20305190044904100c41080e02c0595200b14a030400f070115007400c0052503080c6450459501d01440e9103500498890006460581c6aa4a480c90352060042c1004144054035900404140074142070340741d2036031035814000302001500403441c001211b14000c4141c0e07040b10b074030300d400d402428920550000181401041216007a1f00a05c010460764001c002100700000d101008580d210b0460401400003040991841e00301400e00041002c6d5990001231801120a00040c040c0c5941d101c401040c180302406 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 544262104 1250 544260854 544260877
    0x1503090516030f0c080c01080c0711130902010306050a0b03010506030a0608012c1501063608060c090a03321b0d0c0608071403010303080420030a08030c 67
    0x6041c00b00c00d1000820740310f2a4140b15146011500d5500d2582d2511040b40c041000e02082e604400180d2800c8000010301c0503a10503040030b18001c6220b00010b42981e5000d402070b40da00d940f00c00a60465030144540c0000d01f0040302d1202440e450b003910584030f48414090180134400c088040340c0380f880c260300204c02624880c1c00900202c02140000842c48200e4120402c669002d1410010201c0340418440131b0303086120b82c5200c2c103a081c21000d503034808141e046245004088900710b10102e400301c1d50780d80c1d058201b0240b80c2c40e403071804500c03518040f800f40811038403a004101865140d9240c2001d042201d82c060284144040c0c17220081840e041c80d107695803035000b80111301036251140412403920486001d92004030b4102d86500740940f08202100041c01020b0390301d000d000150164140f240e00443c41d03d4100102d0540b00d41841070f40d0420f0307204078003044480d070510080041c41c2e1503901c11400070400c0c203102c004800c17000035a5548481c401070004c44001001c2006406110200c40c5400b150 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 544263354 1250 544262104 544262143
    0x7030f0c080711090c2809080f1c09061b1109150405090c0a0e0c0c0706051c110a0c17180906090601090317071a0405010e060115030905 60
    0x82c0c0c285511103d0308408414070440710000090f144006240a070341c002d11050302d00c09188800c00c60740402045c0480110800e202c1d01844c00256001c00b04081d544d4074020b08090310402c0b19503580364090b91100318000c010f0007000c1c0e005001081d408407071241100c0891080000c00d207118102000c1080e626a8603a4001843c041001195010381801c1d01d00654162402c1100d07030707a4281080d48503507615565a5110120382420459940300350041c035000420402c4082c5814082040c0514226941e446070000c64030200d003140c0014240004010201e0f9075540070320001030640071488192003912100750500115050f508140301d007951120802c40c40350044296950071030124251062807240c403462140526400280703070703418000c100031301036036068644030b0006045584007806d10320000c4051102450602100001c0741180f04401c00d070b100c000100324a00d04041c00c29070b0956599055400c0d582e80030b2001000b507038162424000300400c541c0b0700041d030401c40b46092030411091000301803d0b040c4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 544264604 1250 544263354 544263367
    0x3051e010801020c0c0405102309090708070f0302011416021e040f0e070b0c01090b072012031605040e07020102031801140c07030c02030d0f170c07030f0c08 69
    0x550013440c43d07903079030403c50703924504604c03c12041c1c50044070790800c10318400404110b66041d46441c100401c842d901401205020701d40800d481510449600c071155000141c200f14040050180e1b0018009a80c1100703622803c680000c0d0840c0c00325400b0389207801000a43c405464505011900c0d000d6000741152101000110000c1104a0301c2c00362511507032505500c029900d081c0d1041c601e4901c5010060040307240782c900420780c16041120a80a15505c43c603103000040c0b000140c9070300c65020354840d0140303182d85064521440c04205810251507001c0105200c1c1c40c0a0803058039032103c050701c0f103402c012040c18011074650280e036100307241444004080c000c544d501074001d54071911200f92100783c158400300200c0d0070384190000001c2c42c042180d02165954908100400c1224060b04240644200070b60110b0b240102da4641c0300c001076158800f000b80c81e50300280e0300c030b100406ca0101d101903041c4106171350841d120f100e42c01018030803103140c00c0a1080c01000310840c856080030301e00341c6071b00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 544265854 1250 544264604 544264619
    0x1092009012d0f0302090d060e1f05040c0509090705040b120604080408010522021e1801140a0f0e091c1e05070b070e06191d0117040303051e01 63
    0x10a0201c0b010a1000c91005403440c8a80300380d500c400d100410040751818035480740c400414118030401d00710301074090780c50010041e0f021001005850b8035800660740c030300343c203000c003250f0b9868022502c80d04140007400400540000e40f441520741c111800141d00142d01d00155041d00c502c9010300301401604100024060702401800c201c03401d030710081c810369880c65a14800300c18803000001101807481c05140240c00c18a64242d1240c90b540040f110f204070341800a201c022141c540340080002010061042e00703881024442c21480550b410181103050240c0350386c41c00a0303805000d042902c10000151324903002c1043c0c20030301c00380d0b41c02c824444407100030051030029605602418200b07034580700901c1c5803081d0100c450950704060703008450740303c1400c1110310203a1110015800350040c4035500b03c42d0300018003140c03030180e02d03142c142d44400820b10000341d180c44241580d0500061202c103240d0000c00c01c1150f50f0040e4540b07000607042c1d541086460b078140c0c8450748a8502c03030140b0000301d4601d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 544267104 1250 544265854 544265927
    0x70e0d150501060512041101142d04051e0d1a04050c06030f0105100e060d0c08091203060d0309090908040e0a110d091713030b0109200901 61
    0x4410308442844a40e032039400c1580d2621a090762800241280f0b8005000b2680d85c0040190510052420004030009003954008a0300302400f903140d59440c002c0120b8910011a1014816042e00198142884d2514001032280704010f0000c6206240b0440000350940c0c07039510302421141c0c851982c0130049070450f240e4900800440d011241442420f03084c3c0468540b61080c0ca10420b011604030580d03a080ca814418010001c2070001c0512080c004060315582d10781d4040c210000820800081314401c035400140644000780c200f442c183c102b012b404801c03030740c01000c4980c0701d40c040e6140103105405140444100410794401091545004005402c01021038001c0c0b0803540e18654114440e12912420011104c80d280d5002e1241d408200040124566401403491280200b07160242010740c2800a10743d6403100301403000000c14804c041c0100101982c0007400741014400c1040104401020b1030284042c40e4200a41c0c0140460700c8044c503886102c4450040500f81c80709069620b02c00e0300301134076 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 544268354 1250 544267104 544267133
    0xb07080d0203040c30110607121e030b030a0b060604090509071406130e060409060f201305010516150504020306150a090c03020c030a0e0a0b071a070e0d 67
    0xd010061513000c1c1e210a170303441d01c44a885540084001d021450317a80b0381151085001d00150050340510160020503d040c544196180081d144d0328960043c00703802400d05487c01e14130f041410701d042a061340c10f8400191034140641d02c6900c900c07880e260080003949900031039202c11003980c1003200b0486010300114461082b44c50314668010400440d204120041c0a035405230059040c80560811200407080d4a2941046000d0030002c4c0303003002c58559005441041507620401d640751100c941c100005070055a030301c905000501e904188116032240c180c50464803c0c41d0400201081c80034140300082c1c020043e641d484618401e0014510245402401040f40d05902c42c0c02540c0009808032404000b940a1542c010050400281000c5d1200001c000d89003214081540c2400004d40b82a4204000c120392031403511800b0700003611204002e100900d9030400742c29610217008210000d06543d400c81d410780f4088103402120360300c5000803600c0f1846c00341910b0b400242d2407075550510200201c40c00c00c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 544269604 1250 544268354 544268369
    0x12120807080411040908091003090506070f0207060c020102011103070f0314130303050c091c150b0904080702040e0321090d14070c0e0109060905130c0b07080d0203040c 74
    0x221036440080c1580d209000b1240603110fa00c450340c103c111843c103544405082481042d0306414041d074030340443d001102150407000420b543d84283c1040c00f0f01040441d0303000210b441c1c901340d6030408500081d02d4881c01d2041030140961071900104580c001e40225400861b0807070798940740d141240d002084001c1040152020a103031421500401840b01d0308580300f0b448108485400c2115aa4120028034005044d00c9684c0400c3c48040d03403c3d51440070103003881c1d8181070800c0400005d030401c1d031080302c0c1c000c50200300d072031410100c2c801c152070303940404d50b00c2608810800e8803520703d030001c90082d00e49180043d0b0070703020000ba4400c500307400d040d0445051203442404410356841e840680c0c6d032624040407a00110714001c20003481001c0150040c1180b170b10540b10060807955889060350a8082a081900301c1e0b078548000340140c1e002482010760103094082202d8054902c4d40f690032141075240a0b01507001c5d0006040f2007480701480454101c540006002c660341c0c64242829080f9403002e01404a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 544270854 1250 544269604 544269617
    0x40321020417120a18050402030c07050f010606020a0305091206101403030711151207050d0c02010c080f0c09270108030f03061c0b040609261c061212 66
    0x620400000c1d4400100c0301d0f4554603144c6010311000782e0b40b1900042070a100d640d04841c0100301922940007560082c0024240c003a04c070041c40c50720a003810000202000c09038074202003001802e03800201258a15054240103a03191686800702c1d8030780040b1031226505200307520a100c480502020303070500f240c440000c41c50081c2112000c05449128030000030f0120300c1003500700b041d9454461003410030411034040030340c0340241100007401e94010894050740850004a45210000d010307001c0d15103110700b80d100802c10003030f5107600030b0030342a000b03089076900d022801c00160503941c4a03002c840402ea00281036000600c4004504540700d8000d04041c00394041c0b202c00040c03c03681c0042595605003c00540c1802c540d94402417140e03076500010200303008660061001c010401110749030b400303180201004145031101d424104040c2d422841c0403031489001d21000c0d4040c503049000e450140c000400300209070400c2002c29030280c2500c0e040044c1d400b1a405220f801c2041e0307001d04503841e5000c0e840c0d69 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 544272104 1250 544270854 544270889
    0x20a0201110d053106090603062705070201060f12020a0e010e0403211e050106080c07020609031e06070201060807050d02120a061b0e0d0f0b0403210204 67
    0x140d120460b000d80000800d80a0200c00032800040000c0c5050545040c00c1d245180102e410380d60714848a6032218010402e4003d0034021264140241406462901c20003180c20105011180082d00c200720300001c15641d40001ca00144e20039080113005229010020f4181343e100c5503000e4800c5000303607080388540d8020000040f584e4000d2007260413210002e698003503543d6140c4064030f00300380c902100c0100328441d030400c014103000c41c4030320b010741880c21000c00d02c02c0901c070303500000b25130040e0010000c0c000c0c2002001544001d440c22030714000c1c2d054541a440d070025601080c6041c0f020420350181001c0c060310044e03e0f200010b03c4c10302c585040d50007070005e0741d075520801d0740792038031380c050705821854100c000005802e01040e0445210302d030304201e0b81901d50503180c81c001c683c1120206082590a07007141459075038898500d801c0c1000803501040b000e02c15585154035107400602c002e0490a02c0300c0010107041c01424940a4041c84401c1a880e046500e40da441c02035015015000c40b092103031600 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 544273354 1250 544272104 544272137
    0x9021b150601021c0216091b0201050603030d020c0a050a1a07090b0d1e0608070501021501180b151602090f040b0403140706090f02150c030f0306060c0d020a0201 71
    0x6601411040c0c0241c00b490144e140110002142c944844055104086000b6510201184a9002401500000101c2c1003d1710000345c10b0011803540e41046a040609001d503a0364044101c415250700010010b9449820030219030408082c1c2c040a00140551020401481158158a210107003c581c50211950b90f40006555075070342c0e40282540ca40040c00180d2401c412584180034200500554031b4980400081d6030080e04c0c00c2d60020810368000c140c041006513010401248a6045880315113003649c101441800c1c0020f1220300b140d041d5454041c44c8078291911030100419500f21900c1d265646c4105486140040c10561f040b805034109200280e440125503614500490b8400c0310f0942c1d507215624120340450001d80740e0800000304000c0f50001a54912071104102d2141000307041000050040100b211680c028203c00716500300100805010302004850328400f08480b02d0340c594680d00e011840c0c80c02159104412442120300c9060242d400007207880101d40301741d07501d49200024064 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 544274604 1250 544273354 544273393
    0xc010b18040f120302090909070501020d030b0319140303070513060302030103080909090f0718110406020709020d06030b0901020304171c1a09070818010b090103020402030a0609021b 80
    0x9020308030b80c0c0b00840c14000035411454803003104145107030260900c80e03440000790401174103942c44001c9512186040100e941c06002c21810003031141004c00804400c0004207840390495030040da42034400444102c208030841c81000400031510003100d4030391801520203001c5a000c401e4840c2d800f40e01d90b0b000105548030780200ea040e2607010160302d0a08440d0740900c048010084c2c0304100ba400b882c0100d0701190820004080207054244c1e0380806c4002041084088030070481c15551030341f40c10071040c041c01d80c0000d422012a08034440c010395070f000d1400a035000b0b248682000b0511260b0006210b045c20054010b0350140d8001c454015051510983d100c200344140008101200b004000b035004100d4642d020504c00c116010b070344081c000c0c8140000d9268a011504540454810340a00800c17a800300e15000003005004003c0003500804c900059144105200091042d0b40000c0041d00a600982000f001890440015500c813206a40004507030402080031b20000d2150a68070300c035421078030b030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 544275854 1250 544274604 544274611
    0x120403030b0913020d1401050a020703120c020703030c06060e070c0219061e020a0812010e0106020c0d170d06030c092409020f13060e090106031416020a080c010b18 72
    0x41942070040c0f081e4203004d5080c03030f48030040c3c4541101a4004084c08000e0003a584a8440001e00598400392460050400218940c2090607149001e1401d0405500000d040c0152a0141006102c0042d1441c7c0300700a0300d5586c0040c1d060004800c144124103800041c051034061003194103c2040d0a02c81c06104040c120b44208000541e4005c210030507055040702d05903a4091034410f0f50000031990f01d031407450303070300c403c0c00c0f01480d1581000400920320000c164074050070b210b01c0608919070140c0300090b0365020500c0c0103410460004050b407206c084000031500da00b042c4680c2400250740e02c0c2480e0104038600d10078500303060b05060f1400395003114950098035181102450080e1903042002d10710080d00002c002010f81042000030400030510f2060340790081120b6910654040188024007400302c0f0103078010003d0606100344041c0d8070502d5503409621a0101072803c501d5002c1c100220314003124444080e1040d400000e075107507901c206400c600d1550405552070035019001e6200d41500304400c6 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 544277104 1250 544275854 544275871
    0x905090708060f0636030705120607050306120f2d0a080309070f09050108010b09090a02090601051b010b030f0a0c1401031b170f240411120403030b09 66
    0x14811030a1454068040c156208030380583c2141c20484881180a00c17a00084154400082010b070b810340389001c1003480054282aa0780200307a085541d10690354410282042c03007402000705c0092103a0b03c0d214003008864400310122b44001044100c0f0355100c901500769403000500680c01208900600b80c40c028106a080006116020240d1102402c07500040c111020780e008440d030000b4003007201c4804602600a0f0b140002700c0d54900101e2900b1501070080c002d024102503c10040d0220001c40c0308084241c0540d41000300780e603051700480c0c07a44540035441c80c1154240707042c00307405070055000d041074440c1030b004c94880c80750886045a13204c09807030000b401145280c0007403140c00721900318660b0680d410305000c142915880300750500f048208244100280a024804a411100b0301c10760b03820a111b00c0c1090f03040d0400e04217402c650344130500c1b5400f500350058566801521150b1001d0306031000b54940e50f44665480d110706041043c16102940024242144402c0078030b08201010b0040004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 544278354 1250 544277104 544277119
    0xd050a0b030330040819080105010e0d0c0503010e0c030c030f071e030c030305030f070e060a21150515250204021201060201150f030b0403030525090509070806 70
    0xb285003020a98021407883e0581100304600701032240243c80c6082c051440b414006468001c685000024214003180c018100311a9800400ca035036003015941758404001c0c0e51580d51707441340f800c0c54074840040d584030640562819560301c800c1400401d10003032940044060780c0d201c4134404201950303065455203400c8950480030081151601d51424558a40315400040992950300e80f26111080c01c030350300a4011500c0002046110701141034080d03400b80c03031400c0804035424000c001c9105801101c15410610000c604c4107110003801103440603089800c03400c280900c103c06c44003000d440340c4511030b00e070041c54582c10b60080c5c07060450544000400d40c10b003003c00107500004644105050800030707608240c0c2000010207080d81c14080c140641032035000820002242000d03281821000e921100c40b000c500402400090704c2502980e400030f40524022801352203409400c00401c11520010f100600c101c000c0702a05908045800c0444800300c4050b0260f40c0c804000307903251101107030b80b07a601140c03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 544279604 1250 544278354 544278367
    0xe070e1f1d06010912030504180216122f06091f0b0d080d0c0905030106050102120f1306030902030d0c030804030809160b130b13060c05120d020d050a0b0303 69
    0x50000a050340102d05140c00c01c2c82659a8050106401c60700c24154001200010284504022166103103074640f01c4a034110f1509000107481040e40d40103000007080c0000104203c0401d601c90220510504500d21403d02c01c00e09024a500710200310100c0d502031801403000051040c48082003004400b5248107807621207202030072000000700131b1210002d9000b022204c00002052013a0f01a003a0440304080004034500341c1071000d05021603c0d484580300e603040c40028003099030301280410003890b41401c015107404600c80018214040c80c000f03100b84140e4038000144155060308070703680041c000d50541381000c0406404032030644640201034081080722002c200000c2c49900016800742c900016600000074814103100403030030652008550340404508a4401c01c000124040289051004d89140c890b184183c1039190480c1d1003030100340622944500140402804842200c0c01e0f030710a100d80d501814a0020006d40064400607040d03850400043c0c44c041e081d101d0403482c0c0000400850602d01e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 544280854 1250 544279604 544279649
    0x2d050301050c07120302120f09010b091e06030a06090507060801052d0102010b030d200102180616050a03030501180c0509060d0b092502031206040e010e070e1f 70
    0xb020404000c08161b82001b449000744071080060780030f100c405290f4078142c240100c5040c256524425046e1240078241c00341700d40c080c21410304011450f4040e041031407039130b507400000342808500300d806001e850921000e501007260204a80058a00b0354840c6005a62a071081c0084500d045c9150306120ba041440d80000d9440d2a41203441c00b0b60510012510303c0300400800d0520b1002001040443c00904961741134843c40b0b060301c98002c8003035000314207010054902c0102e040302d8412041c003035100040d0402600707140e0310a00b503d00b40c100c4200c80751410203180007001001309110304803803030600452021010341c036405003c45402c2d599032480d05200305042040341076403004d982c0140a558903100e07500e49486000d0350303501c1409560200c0113104c5040b01c3e04500c00800c0600341c8115001001176110848900c10030642080c0103a400050f8268940381070750040810a1041c4224800c29030002418031003c1003c0384a4620300031142d01d1000904405482c007440c5000d208807001ca00c4481c0118030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 544282104 1250 544280854 544280873
    0x3130201080415060b0a09061713140f03130506070c0b03060111010f0c021905070612020403140a060e010b01080f0c130b030f06090c03040204090c2d050301050c07 72
    0x1406404a03e2214041419140031541c10b40d010702d014a0011508083c01034020042030010703c005e040100010984000900e000c12005040461281300c034804041801f80d0030360320001c0d030908032040360008141c00b07101513607030781106003162340158a03460003007540d08002068424040d407080d940482103091074000c408680009100d14100f00c2c0d441a40b00c0700000074000d2109418900c01d00080c151550340c2e00a040c440500031100c080e05884a01000242c0c0004444085801c0351a14520f40380c81001c2c0f00d00030727101e240c0c00a4425540d43c001c0c502c086802184002c2641d1280004103d07901c0b242c000b15080c2d410070800c00e40032600e8240003c141240f100c0049600203800c0300d03c01d00e01992840a0401650a03400c86165048080104030326030724421081d5401c400112521041803401c02030415a5200c0200001c0c01162943c0b094020008034182a0020b4500500b11003103940c2400c040c1c05140700900f0108115500307058000607681010300c52180510001e0101c1c624080440c4c072001c22a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 544283354 1250 544282104 544282111
    0x30901060302031c30060f080105010e0c03010e040602090a271523040908040311030601050d140a020a1d01140f10090801050406021801080f150a0b2b020313020108 72
    0x564085175140080d0714100d02c500400307030201e8110071780494204a1403e08555058114058110304e88050200300c02c041400d5038110f914114031807030b1a070349920381000a402030826a54100c1030001012500030100315528100030000104100140e413a024050f00395003044e48010104001b511061040d10300e440da19106040e081540716072a13403414408142203481d04078054400754404601070042100c0064010f110000490003400c0c42e50400d400125031a4200e08024140071201080003844041070000700d4080c1e800415464200780d540700c080098907103441c1080d070400000000420f05011141c0312014105000e0020750720000904180601c8006840004090182c1c1d044005000f83c0c0034003800740300d14032404000d03032520717070381c0110341a001001c081c03080c14043d000007089050340d0389000d038560040000c90070122080e918408030b1030b079000e190881029030350001a060710b501951a0042c014800b01c03c0c0f2a01200c420000321022408151000e024440c41401000051b40c841c0c00e580e0b40 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 544284604 1250 544283354 544283417
    0xc0910080609150a05090a0c12060f0501200105040602030a0b011b0311030403050f0703060b0102010e12031008070909050d0c030906050708090405191b0e0405100b030901060302031c 80
    0x1202900d07480040c1400c0383c1243c4c50705c2e2623612051003a02c40c560001c4003a100c020180018801279040c9005511400201d00a250401c00d04a04003505025881040d200c8114044008c00060505040190280d8001c0768001a101e0810b100030140d135109141e411060007040807100d0040e5616501124214160b05181046120620011000c154284180200c403106580145811851442e014040d030304081907050541e4545440026070600214819051585020540da582e6031065204400503c0d203421448640c402d02402150004040e404403140d54022800c48040d03185003a421a41a01c00311802070008003030110030041306000720041c140440c80761078000c0c1842c0301403011500321001120031044030f03c89272071082800422885036030201400c032074054244014004015103680e030541c0209001e207540d000050002d04001018001a15810840c00d9880c00d000314098040e15060200b640300e4018a1266003484000032050000b20007140c5035040210a40008101c445241118080 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 544285854 1250 544284604 544284619
    0x913020903100b0a060305040b1f150e13090c06080603070e07180b04082d0d0914060a0807051803070803040812040308190201020708030c091008060915 67
    0x119940920015403080041e80c0c00292980f000e508000321541d02d80e0090050501c1d10090001042e1490455a400150700c2e0789802d40171161405080900d02c10307800300d803514403800d010781d21065222271000c1064104865010551103200050812a02c0610006001020284041120900a0f0760341d6a2003100101500c1c00c1550780c0d0030080f20082e003160300340002000700003c9034090345070281c0d18019220350742c0d002d800c09080140865841510070704d500010103654420240c0c9680b80c0404021100391903058480352034100b4002b0340400c11901501700002c20312900c1000c40d0400c6010b58083e5500d65552202e50b03251301e05c040d11598880e400c0c081c924403014030302910b00d8030104200002020024011036680c0d10300f46400c4d0130800c0001405280714010001000800e19840a540c410072803105802c40c101c0e21840283c3c02441908001048044007000f00700448215501500c1024000d64a02e450103116500484031a881103c805501200000109581100000100d00e40306e20180920 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 544287104 1250 544285854 544285867
    0x718060812120c0d11030601021501140f0427051207031425150b030a050304152705011101091a0a020f0f04170a05120913020c0601051014091302 64
    0x1015608141c854a0b0080d00000c01c0c01f200e560304106072043c910f100e205411031135061281c05040614420170361031041c501104003020a0795564800400e583c040d40302c0d002454002e49c82e00b0400e041a0606aa0030301807584160b140300c0c000030454201d1581651510803040c0e1356800e0300300c9500301100010300080b07102c4549401c24012082c104010b401144804c18481d142c48083c2c00344d809664000d0b00a410100e2400300050f0000191001c1c0c0e400002c40300244401010100d03464040c034080c6000c0100c4c0034810fa0751103107007a5040420b481c000e0740c428884c00c420742040e43c21f841a801c0700404160082e800c640b08400302c10849074001c4015a0302501e8800c10900c0380003590801504881c1c4204009000c021310034040043c00d07000d00c40040a800030b035000c0e4481644a20804201c030b444c0400c00288000d00d9500e46035800c0701c940c00c0c020115200d012698116075500024001c140c06060300400441c2c00c02c3c092854600380701d900e210040d2400c044034050002004aa1440c0d141c500c0e000e0141 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 544288354 1250 544287104 544287127
    0x130303060b0d0501030b0901021608090d0b1e0c180d030224090f06090316020316080115060504051c020f061c1802010903230718060812120c 62
    0xb001c04010400002c00d0950540c03c04018250000e841c52a0a0784104603403c440301d00014854030041e00a55856103440781000803038049540714000074084a1403800700304028100801d80110203010303141c50016a40e502c002e04842c3d2003031298003e02075103011031001591402000d042d107603c2c400d10560302c8100c1030b414024000f4690482001d01c1604030f904210203040704014030140104914001d10560406030f102988a1191003070140140007601004030964030b040081c5061014803c44e080f06596403000b400c1e008000884c8800e051500c1048000341e02d0f417250094900b0384d20b00030410070a909416040d10550005c5020483e0004050040c8910315074030030300034041d030361601910207074040c0d040011501150b007002c0c14107000041c003212460240c1d91103480c45007941e07400000c111808540340a02e51708400d81609100ea40c0c85540f4000c541042c0c02c0e0f60900001144200501c01035071030b207050766200d890444186a0742c91051000501e1141c044801c290070042c1036400c0351070050f54058 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 544289604 1250 544288354 544288357
    0xc0b0901060806010b04061d090f2208070209060907050a0c261b0706050f071e080a020708030903030d0203180f010b132c030f03161403010e130303060b 67
    0x100c05804000f107020007c050304034924800740824203001440d900c42400c0001c03c00c0d400134000c80303031901070000000c078004010700491072514640c2058041e0b1002d2071a2100903a80a030000301d0286503100e000c12aa8107295644d9030240805469082c1804c4245000b1600d1055010301681e01c6011455162560052900b001c05d0120104040e0741da5980182c86030324440382880310842c0740f40c0c00705c202081055405400c1e03c0c0c0101c021342040b0340d0b0394487e0802c041c443ca044c000c1341204401604540342003040000082c0000885034003078481142e9203040154a90007100b18440c0c25800400918410060582c0156072040001901da40d00030510300d10700385485802c403c101000d03955904400a10320b490800344040705100d6000784540120142c1c0e0303940c4c201340625444801a5030f51107841030318505005552822001e00c030917036120b00e040041050084100c040400205818410100c0e00b2442ca008490603103021804a00c07541e12005400022180c09074001d40c201565550701140b00300d90b500 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 544290854 1250 544289604 544289609
    0x313172104030207270c0e031006030501050c04050102100b1f02060406050a0504200127031e030c031107030b0103060f0e0c100302030a020405040e030309120a0c0b090106080601 78
    0x5100009241c0352401a00d0300c540703034000c04000503002c1882d10722000444940941c030603c440e000705140c0c011520a0f81c0d0800b0000b5081c1d418041c850021035003000507413119048030701840003889280c540003d414002e01c903070301031280141c00800f802e242000483c0c10502c1c0520300500507044084000d8900c0c0041d1848100b201d0068000a041c0820300c420360241c15007002c04004100910b040035a102c150081466100007822408611102c3e0790341e0040f41800e007868071118141c0301c40201c0201500e400245400110380500da4105a112140a031030b40d500269585912061f00700c89c0682c4003601c403000c4502614449104e005400300002da2015000343c02984100004102548110320703a800351072031007840107129800a14414125034400c51000c00000341801d00581d42d4071035059000c0071388074541100d9003180c01c080a0a5a100c0004011031007070640310700f5140140f0f864551a00648507411181c4c00251184035990081079940c28001e0f005010500001820f035900c10209003010001d9 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 544292104 1250 544290854 544290907
    0x30c13060f080601021c0c03090e090717070609050618180114010809031b07050312040602120301030b0606030901180c05010f091a0f042d0803031317 66
    0x502041c0324660b000034410750040004d0000d404008513580000212845801a0744c0412010408040078980a4610100640040c0c480c0d404030745410303004181d0320030191140703003a9a1444e007403000785980041061010303200c0c0c0d42e4030b40305814544002c000b116000468159841c00109070700c1951640c075074811614107080202c9400701907143c200f07081084000c1814140c180400081000280c0d0804001c652550414881400d0036005c6000c40c180b0341291030308001d0301482030412000450b01c00d4400791003150b8465085619025a2560702038032800b0030322004014100d07000201c1c00910301800034580c42400c01000003109844140a114103d1102c01c0a51352111040c0c3c0501195174481c1c00c42014400b10b0a1400d04540b403c1001211030384c0b004060000301e90b0204276821880d41a100b100d000b03001c010607440d800e0300001103080754cd00403400c00010baa0100d500010790700c0c00c08005e680c03103603200b2110140101019180d071840e480b000c824a04080070b0030040d60004c501e1214040c0d400c0f4826 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 544293354 1250 544292104 544292117
    0x103081b010e07361b030207050c12010908030a09121b021e221a0a090b031f0608010c110d23040303050d501317040503070506030c1306 60
    0xc41c5c0441c0140240011408250041045101003070001030686150b0b070f02540c1242008a034501c043d170051054032002032101d0000030a01466025903000301c220709006804407098842d05c0c0c00c068615401c251801200010700031420f03800343c6410380107134081402c03030812004004840400600e407000400601c041e541840d00100100d620581b0800c0711440080105040ea0700c5448009445540e6510480340c0d42d544030303440340d00340e40c405001e000620449010b038401e20794644451440074000d00c0c0902129913181030100c1c00700c1d901c20f55003851040a9103005d4403000608010071030784c0d843c0110b83c280c04a80e44480e41e0110b481c008008100450180d60741a031030703803251004601a11001c01b02c01c085190304030340054201e0410706200d001e00090804012401609108032a5111001005008010b480000700160462030fa98411204d40c031641c00004506241520000307180030300e000721038140c0e000050510076414082c000f941c210340c1607034203141020503091314851401144d4101d503000506c1d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 544294604 1250 544293354 544293371
    0x503040320010e010b06090d020402070203030903030a090e06010c020a03081e0c0304031b030b0105010c030e0406140319030e0f0307030c060507260a030519050103081b010e0736 78
    0x17031065240c0801c044400a1911041c2000a610321004540191059a00107080c004550301001140d0704440050b0a498a0b40034010b0702038000d00e03162140d95150320030303507001400a6100300420a00c15078010407804015080d5144ca10084d00036079076108182c0024409003411801c0000a0240011003070021030355142946403160100584841c0034040c61030701c2c18207000050b881d01200d81564028a0482da81d00c0c82c07420108c03084204a402c10b03401c6440d0550109043d0b4102c90205100a01581140c4080d021180007440000e100b0341c1c0030b000610b00c2c00d0b4000c40c1f4945140c1003100307004010201c0c3c901d47d80300d8440d80c811100540c031400108034000b403850f0405c00c24120001046e1100d102210000303411280014041c810a00410209a92000002c0841c102c941d0950001220030804101d42d40c1c40e40351103040daa216241c0c1c000001c1e10220383c0f41040105014162440100d90040c2034000d2422030159135a010341d080c08814103001c076266280c5c807040b0b801005000003080340c01082980 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 544295854 1250 544294604 544294631
    0x70f0209042108010315051b13090b100815010e460b0904021b0a051606020a021c050d05030106140304020d030e0a080d0e03010e01140106050304032001 67
    0x7a03a506081032050b800010000f0840586d91050f07030401c100404146680c4644000514060050460035848404904480d00f0107040105609407030274120b080090960340c0041000135000202d0b62400103801c00f00082150264021000401106040c1901ca0f00300b201d0000b41f903d5400150481882841e1404100e525003402180c1e092500e02003500b81007114000080320b801c4114003c520b4640000984c00102ea1219411600710140f44001c0c8542511001c4845481d580a90010381c0d40b8400c03003005004400318481c5000480d00700b600103081c540e030f6030360138014004040361201510302d2000c10040003188080c002c51407802c0041c0e0f031703542d0b40c1e60408001805e1400c00c0d0038242440c0c01c05004003c01030301d49030b40c11f0805d640c0508251000d00c44420000d07014030116004081e13140a042c04131a011034100c1c500b14500c140407002403120f0108028100d080b5003d031100008031a10341c00042060900800066402c0390003880c1c02d0940ac4e0010440c605c460031f80c10441405603650f0a007021002 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 544297104 1250 544295854 544295903
    0x62c060402090708040203102c01020909070e060904110d06080a050609070b0d050405010b04020c01061404020c030a050a03020403020301090b0f0f012303010e330108060408070f020904 81
    0x801814104d1080c189a00402d60f107049290f4840c002558a00d143da86c014444001b8002c044075840c1e40d060362403c0d003034030503010303420000407540642c5104001c40c00b114003400000c661301070054883ca051011000810016154010488580050030850340451250b00c0c081c0c0300c040c2070208002c0006c440c7d81e01c1c0542c0350480003001034045400551081c40b44a07603083c11900d00c24034540000c41c880c0c480e404c14034010003820185a6000d4800549041c1035a419001401150083d048a468440d030b0a400c0c00240d01c155030480200350020000000303414040c4010308188201480c0042c102030310307a400709084640070340c0c060300c00030404800c000c4480720400b03000d0703444441030142e043c9551601040540590000d54900345641c10100040c00070745095011859a0a1a9048940003401c84000d0394051100074034813a40f8040040010f40e0600c2443c109038103e80e40c0c10000d0080d0b80e40d90f1a404a10f40000c40c0c00c940b03c071020f0710003901690318403045602550080c40c010000c2204110a00c004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 544298354 1250 544297104 544297111
    0x902031e090f030307260405011d1f09080403150f1a10050d2705070605031009090609211e08040b0a0b061c05010509040f062c06040209 60
    0x1180d00c00b02ca500d04003038012083c3d9801c000542865075035081012045001c1944c039902480b0200c8841041109102c03054001c0003084041d034a460341030500006034035403250700c44600c1c002007244040311070441c11032613400b010140d03008844090815842c1d07510919010014007200507003607190444900400368604c5600e69030049142400c04d00300800c404580d0707000d05107462005100c40403c200c2c0e180c0b0480d81001d05180c90820741945a020300030017100500c01580d809440b144103070840860740d1801241140d00a0724403040703048070380307103881d42d1600075081d140b80480c0d40f5515509140009a0418180941c19041c40c10003a1011030010001303120103220240114404940b10242c8442d07078106205603002904845201e0301e5607540240c03003001c0c041803d55130350880c90000d4662801d0703030820000080e00c00b00c2c402c14070640c0d903038004110302100107842c080c1c40a041c04a0590008415507c00d0141031202043d0000c92866111801140094949040102c0d0800c1c420841146804021580d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 544299604 1250 544298354 544298371
    0x1b02010219031e1a06120411010c1e0c0f06050901030516140304020402090a081c0f0909180c091a12031204050a05120403030e0409050d050d060902031e 67
    0x200038024a20804020040c5140810059840019aa1915062420404c900005054140c0e11040c8000001b0b02d900708803020341d180e890300102c41002e5071042e640b10152541282e80c1221400096440d2807824000c86030417144040303d00c01c00203101000710312007802410385d5240c098881410ba00007400f550700c014100950510814600112190007207411101e00260f06c08507510b070ba44620104000780700b10481540d000210303580005105500180e10b0a55641902441c40c0c54150640306648140f0449404004545100d00c18001d20100e58801d0840c840d07080c81140052b0b90a4580246410807504168180385d2201814040c00c8a402d076010102c107030030f136010700d0700e080d502e0442d9449002d440e0303114007103443d01d1006c2814410304014100c1c101d5005012b852010348041030503412a801807000300d01003050701c00325125628280c401c051007035800c40b014204080305841704403000e074841a14080c1e2141d03110307030201b100300d55071005d1842265103406400303c00002c10440b001c40c0700f00504244 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 544300854 1250 544299604 544299611
    0x903050a060b0325120c031b15081303050304150c080a06050105040308090906060708041e0602010e070504021c060f0915030c090b04020d050f0a110f0301030b0a1b0201021903 77
    0x2c2c4600c0c0c443c5850011940317070042c102c1c60038416250900e44400d640d40081d0004944610341c460710200340e24880308a44049142e40c90040d040e10b4250781805c0110754000b001804034401d01c0110f0702400083d0b45c401c4c4207c2e0034044580c01d81c203200003200c002079010000201b1200c100310405459204d507002070502400d0440c1881d1071581c0300001c52180c082c159010304400e901140c107580f503c9095844255114103031644590b1100c2c40408121030036440f400070000c3e8500c0008002d801031050100042c11b40c2c0240990314100001e201c080d5020219081034400c1c10030840d5250384840c4101400f4004050300117503942d140c0f80e554425101c80c400c541a0282101808000144540d440c8004a810b510070100341c80c0003079030005c0c0090058003040301c40c0c142081c08220142d151070004600c1401d2000d010481080715003420301d0b441c0103843c101003550303c0410060010907102a035456001b00007030310100e9040580005c80d428803a43c1c14504015030340118910071201c18030600710030034114514040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 544302104 1250 544300854 544300903
    0x2010f020703170703110609010f0506040c0215150a1d0106080708041412030106050c0610050d020603180d0c03020601080307020a05100e040501081e0a0309060f0903050a060b03 78
    0x80c0710380d60301880480305000584d0a0070036000301d5070102c94078a10020303540a45040400240078210441d50240800d04d0a4001462031410380315600c461038a642c000e08254218480d0f82e0300380d8001034000d06200c418a603100d404e50b03032079074600d4000d04502050a80425801d4000c0d8200200603040401480184010880e8080e401754a2540c0503802042d6041c82124800441d410f0894076076844c2c150300b1000001050658104000b4155004084112000d0781c3e83d541e41d51070328443c0c0340516540003400031080400361400c3c0016541110628034a00e40002c0050007a61400c0d04006840300410942c40e140c000b45601488124010701200b409503160089503070000d4100e1031280a8948610640f031041441c140c8030340c1030000d1005015004014950f160110507a9803104d20040b40121192402a400340c141d001c55000d00b62030341034a460095508101c426a0302c0d044550074981080070703041d070000101c0c2d010050030008500440000030040aa1001d15040201c2e80040340c480c4842210031 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 544303354 1250 544302104 544302113
    0x150411160803070c060c05030402010f0f050d09080c0a060c09080c010f0f030b030a2301140a020a050d09080307080c1612050f040b120f040f02040c0e03010903020a02010f020703 78
    0x518401039807196240340ea039959403006540584807504003500140c507090301c900f03a26800000441c042ca000b40c0b034a07500c01c9460349003112080042010600002c0b024441c2031006211500b181c50001e04c1078075018101345000400d6894240303030080560703801d6110342180d494640c0000c4044054100700380506101100701c0c0c006000c1240c4e42280c0c008010b1680382d9a00b005100b82d1000c000208000d007690b0440c0a1410000c880c0403500a20031480d000c040107035004580d0503c40d98061300e410342480e4901d5a00c2c01c61000081d040f0300400014481c0c10001442030b0a118410381d10068442c5004070344908080034018100d84d40142045448a41000a400402d807981c071034000140d40304006103070a0300040d8080b03907180030300c25540000113004a40400c050b0400d4001d404050340c1181000310590324a000d080d88a0000d85010b00803546101c6048052300b0280c20944405140c1d0030304d1001e0004980100c1d00b1200e80c580f080d00183c0028068004641c5d1003090300b01d0a0000d8801030040c1800c0d80c03035 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 544304604 1250 544303354 544303387
    0xe0607050a08040206250302060c04081213030c030836040e0c1309050d0201020910030f02120414060610120b030a02040203070503011406160308070e09150411 70
    0x29007009000c140710008045503100c40495a1248002542c0c490740800100c0b80122064450300440140c000c00001a02d50569075050328202e074419030080616103214202c4038038681c00640e0b14840c5181c05030b0b020000c02e0140500e0310085100d1119541d0310a4603006940419001390902e0020100240042903866072110080e414510308680c0001c4420313000c440940b0301011072618a41200e090f00c1010a10ba8003540102c210074001c2080d0b40b040142c100d400c03400c0b4810801074030b0b4085802e0b00454803043c8694000d05e403c105450005117000c1c1a501040701000c6d040714225186500021600201d81c814016203412a00c03c3d50050107120502c00c000d0802028401c0300e4041e42c0d5a0b9103014503070342c0c003000002c0c402600074004665a007800c1400504640c024080c1c00c403070104400360400d003070400740111511051883c01c41c2e1540012aa0708a8600801611410402c400c4010141d45c135500c4410660051054440b480e005102240a02069942c05070350505410003e00003440b8400c1e00b000c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 544305854 1250 544304604 544304617
    0x11030f090906030f100e160509280603060605030c0406180e01180f200d0b0601020f120a030b09100e0405030f0301080105040209280b0102030f1204060e060705 70
    0xc0d040c490903070311440840e18010712a03035600352602c104602170348019080e034440e503407054a02c4142c03078050244001c0c0440010031403180e1900599080c0018111030780800480008100d401440b03801d071003a0149d00301c10707182c07203820941c0d201d40c1e81c002c10045131a00300311101c1184c400352001e206c250b20707003581c407901002034140c581101900d4001c080001c6000b94895004400c0072075481c0f030030400c2030404160411014208840340d150082c9a914ac459071900c100072401c2c0014000c0c00c1030320455036007071141880503203024103500c038001e000c103500c600500803030f0300700d800859046484114000004007a60303002d00e0360b103016104403400d100e42c01c40d0556196054880005502c1c1942c0c45620f4900d195102d0b20712580101180480040341e0403406410081c0036a0003164a8211902c1d5030010504900100410640c110035442c041d688a1599030024900840b050043c1c07420036a44250300c0b12180d0201141990f01c032920307c100000c2096070304c6144103026141000300301610f019a00a0960b02c9440c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 544307104 1250 544305854 544305859
    0x100e0601021b0d06090803091203090c13110a030c030605011103040e0c0f0315040f020f030610090b07210509031906060f080a03030e1614061b0a0311030f09 69
    0x5440b0900c2500d0389404164200d500c00002c002c420701d036081c841c03115002580d080c45603000e004178105000c12442c003607038001e0b40700201030427610038100c0c10401070007070a4909030b1046485002e5996501030103000703803941202944000c110714400040050454449400c0b40d0305028400c1d8020890110000542c0d040d00c50303403c10a0f40e070b80c5569a81130402e001e4407410800d012800010407084140450b030504c00d403c0182e41c01d00c00c5a0345412002c0c264001d044004209003000c2c030004032103240c002945400d0031802e0611a848646840e00349a25a20040c03044d00c030112507005000c0390113424000301c0c00524541c40d000341012102d00000351034a024044411940d440d000440d400e0003200e0340503000800ca10100460b200c3c0da180710417030320740d420407405901080c50301d00d240303222070313000b0a819641c180c195549031450ba0508038600f0907030401021458000200f4000d00c0701c1140b0854445079040c2c42100140003460f0285002059407842481c910b0141e0001e20480140400400a40385504000c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 544308354 1250 544307104 544307143
    0xa03141501202401050a1211040603150603170c0a080f2209052401120209040606091503020a0215072102040f0f0803030a09020a0905010e100e060102 66
    0x301d40c80441ca40d01c0205000290f0b00501220510a00d00030032807020a004010304680941e984600b0440c0d02009481000d00c5c7e902d40c1c000a80c0010119440f80c4008200107000040031512a00d503210315800c1c3d014000d40081e41c5100500906c443c00c540303d10f0f8401d450b880e140c039141098514544030002ca0100901003440841c0351940101000141c0d2888548048500342d50610104160b030003620a102d025410391900000c030b03900400304100300c0840d400300c01e44074050344091001100d100060152117005c040d824441d1030025aa070340202c4000b0141343da21010510305088085003200c3c0506140d80c1810b01c10060b5842e0030b41c011401030411103182600102035070740d0341d109541c000d62060350001510103907480302c0c0c030007101c0f0350140c020340e00280d03d80e001c82d039129813a01400490b43c0c060031495510070310004503480c80d80d4001c00b40e610720291003001200e550340010001e4560a805c80e09a800c540403c0044074048a4890f00c010682d00d5224865810b00c0e40020b901d41c0048040c0102a070030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 544309604 1250 544308354 544308377
    0x71a181b190806070503010f050108060d0213090212071d0f04020906060d0203041b080d0c0b04031803050c031203160c020102160b1c05010302100c110d080a03141501 73
    0x2034000c025401040b0802c156225840c080500412030750090060105c0c3e4074042a0200c0e0a52051202c144155005400c2c01004d40d40c0e5000c018601106a002c00d044a8443c140500141c0316420410514100c180c0240000f60400052006401c1600d013643c00702d06100c010400d0040e40c24000c031303401c82d8042d0703103428090300c1c0e2a0128565200714104101040d00000c144801c001d26000203582d624120605400800d44890340d050700c400b034806010001541000045001c0b502c0641c1050b0014401d041030b1480c0c440e2030001e006082d085620581e039507000208400241e090074040300c1d00c0460317000103c52440c1b0303090510503000b0914011000400c108038108504690007005091004078444c4654285513907100030315101544803141000d40700900b150200f408003050b00800c2c0c1030b41d0307008080e0480d0102508003207a1449a004003a10700c506030400c1000240c50f50581c2c08c0e007450140c240203646101426002e0706039075419800000a0201c0d030304102011440c20304c810040030091034080300d00031 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 544310854 1250 544309604 544309639
    0x405220515220618170706050f01050a060e03071a040602121e0a1107300804180b06030a020d2a12020403060534081506071a181b 57
    0x507550760044c0200394400c03245c2c0b1591441c2002e40903691190005100c1c640c2c56480a2250351400c0c03003071780d0300220600001d000d818000d5003228031400010b400c071207551f642c07072244040390f00108114009074680002c0a00603542d0512112060030902615685008550464407564410350113030203101d01c401240100d9101c0c40307070085201e18400401100d101d01d0720303400c40101081c035462a0801c01c9141003031542060a0364034204501603085603100d0304181c0303010102c80c507208041c0100c0381102d903030b810815420703600c24015500030380d032840c00186c0b158800c0918800311162100242c01c016201054000303000e52100844800403982d06d0920240701d44604810f01a001c2c5820007403403982800208507042000400040100011506002900c013403c0341c00c0d0709402c1c0b040c50110004032040001810342d90310502800084d100a082e20f4606a0b0f113071985840103010654081c0070500c3c0740c1c00d000c1c4002c1d090030400380341710b000e01c06080441101a60110143d0303d070000c480c011a061701002840c3c2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 544312104 1250 544310854 544310891
    0x7050c04020a0302120a0c0e010c0c052b1203060b18010336060b06040f050607031e080402010f2a020d0c030b06130903050904052205152206 62
    0x401701314000c0905103e10414040c0451100c00d02c00200c02c181c04451540c81000e101c0d503810340090000000c1d90034a4144405c0c8100705c40250209010503000c892648980401998507502610260359920503c0d00300400350750069103c0038103c0003c0c400300c04901040d01140c111003d090030000303941605124410642001c81d01018445000282c03500848041581d02c0000c040c03007480b041041a90304010030025000e24010041c0b039240001c000e025a0614100a100c00745c0242403281030134419080a240c150011039910002076546001e00085581120b680280f85426080000c0b80062002941034903012079040c2252108004c0013860a54540c01c1e03e0034804c0340c1040e80405d0340303070720b034100b00c12455030a40e041e90180c071800001220281e440c0c4038401c0425410b9450503e0010300d4030800025010240068410450a0a1394207020b6481e140302e2005602c00c0001d80000b038030782100704800c20380040c651410600c180382c05020707407180a10729041003a840180050101008040d003c01c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 544313354 1250 544312104 544312117
    0x1b1201020c01150b07080406210507031406010503090c0112060b0c160b040308040b0702030f0712020a08150c0703140a0305010503010b041a06070f080a08010806090307050c04020a0302 81
    0x951002448880789101034002844000400e5030010300c0075030303c5486241900c106003005d0310301c0400f031005002e407900ca003c02d000040d000445941c107a0200b41a4003085410a813a4007001c6551762200f06214055480709650103202420464114507100c8103140e00c1329500c0359020304022000a91400d0040d0a40c8880c01800c5400c40c1240c564105811a698035640c9801e101401d01c107106001405604440454007660780c00329240d810070385005102c420f03940016804907030500030f4101c880d40620007049042d00400350400f24111000c0d02b8014050004225000904607410802e0300250322039030850410b8001c030b1154081952001c2d2400c040314100050002003d00c410006491010980d15030400e5068070b80c11802040741c00321020401048403080f001560000c0f101c44048078007850b10310003600ba8980a10700030155030109583d210180e900c40d46244010828060040c042c4401c200000c40e480414030004520381545612440e6440054890451240b50002203294245103e501990720 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 544314604 1250 544313354 544313389
    0x1803040b0a05040608100602030405010c02041806021905120105060a110601141807090302010e030c04050f0403020c010c030504050904140a030c02040b06090604050904140d08040203070f06021b 85
    0x301c4640c0544010020f500c640b1800000404003000324504c09914030400040b44c0b00c6070001c6107000d141400540f040c078000d07030041c3c0c1e0180d078402d40c0401c0c003480700c0140d81115100b0f8800590398800e055410314054420304421080240c14400400c440c4400001207054480440c1c3c0c0603110444202d0442d00d4019020319044a800352500002c0e01c401c2801700001c001c1c2e4100c0344520180c07400d44043d615030b18112443d100054030a1400c10165002d4660228070003805800d841103800280046419620203844080500741920104024140d061190300002c220901e44400081c0e155100102907001e24081c00303201e040200042400c1011414020082e10001c10990351030344540c0c10007031318031442004207a00480c14800d94240c2da00e441400c543e0400001000581054101018007110090080080b80c6007104488010f03200d00080085002510b52940c420500c4c0ca0706106250038002964020868200310600a0018075008542c1010458469014261122000c0d0000d03c180310420603400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 544315854 1250 544314604 544314607
    0x909040803090c060403030305072309040c02070b0403050703110307180b1c05030c1203061c02030703062a0309031d030727053601022a06060d08031803040b 69
    0x7c05405420440c07155000ba260180120f040d01054841e502801d00f04802e0794104119401c02d600e816445245903002c1841111560394031402006110382c02070704280d80700e5210303942c1003081068503c1409066101a00503241d071920b800d8010050040c00d804240b003c54440a000400fa101d0915101700c0c2030455520b604480701a0410607202d80c0048910f85030760140041e80c1010400724003c41380600b101509410303008501d4419404404035006049905002715040003000c22154054000c80072600501800000b5081260f4500350b00040f41d2001410300708410365001c6604009007007600481400b0400b25001c0c814000307428180580c20003007810f044998290842c10040c4082079a41c528600204960346401b4815801d89600b100314103000042d0545082c1014a45c80f405005c07a05110005800c0c0124000d046900c1441400d60314004101c0200d4010100c404001d01508024141c80c90402c01965440d054114800107183d030480b05903208030b810300c81c5001c201700c41c0100400551036 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 544317104 1250 544315854 544315859
    0x506010308070201080a0c1b240510120c090207020f0405010602010f0b03060c19050f0705010b0a0e2502070e101409070f08071e0e04110909040803090c0604 69
    0x14282e08100000da00240450300000e00004c09885604205045500c654580d007000041510800740350150032181c0d03d682c0281120f200c0808406809900c25003200404c03146004000170000c0400c55101d4001a0317882a40c40700424a8510313400300340c503502c14001d641c5240034008174118040c84a203494100f8900f01c000101181d044d070010264544c02c0300f0034040c41407000c0415681e12010340d540081e814080042e152030240b81c0004128401040c1402800d0605035800742e480d94100050984069446003840391040c0791a211107070280014070846005800c140070015803c5144c050700001400c1c14890600700705008201a07001000c204101c0d80c1e0502c2c22186494045030300307202e01c41040102e007040060500d03202d500f681c41000c19075101c08101c42400011100c401c0046d0101d81803101c010400b000ea2056003808030081d84080d202d40b01c000c1c03000400d000464200b8560f43c07401c03a00070f0290f407040d40d490508082d00a900301215948903140c9941c12400e0a41c1e9940c41035100b600041d00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 544318354 1250 544317104 544317113
    0x120605042105030a1d0601060f08071704021003020c03180415080d08071701031a0702060106170417030f090708120909040c0e07121d070e0c0705060103 67
    0x414030440c03160400c401c0d01c1c40c003041c00001c0d907441c25100700086401407001030b4010700c544c0d1000900703140504820303d5010000641d00d080490a0b0000d2002441aa507800c640340e4005c607026412115514003442c038841148020150208040c0c00280700c0c0300d002c800d001c0018030a40540e082c01108000f0340341e50342900070490480280168080c1d02942c1817548554021100c207014002306c43c142c20180c1042e044807002195041c00081c401d10500c6911034000d801c2c2d440e401102c070b0285100b9207090f4058041c04410185124000b44000110340c412030042c0441076202d28899140d1032504d4500440b500c0b103140040b00c070248a0b0007500055000301c2007000202c03403058024042d2800c10f0945002c0c0340c4428495449401c503024880040204100c020048d08058101951250190510541194490020418007841942d50740c0001d849a605698400c0c610f120b0b1131038580c50016000600c0840d45d91803038480004d0311801d00900c400100090010703c00c142200d5807280c0c03180c141d50b0b079980c407442c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 544319604 1250 544318354 544318361
    0x90120010b01111203010e100e0403030b03150118110d020f0910020a0201080411010302160b060a05030c1305060d08072420031e0f18070b040515041206 67
    0xc0c01400a52108074262001d070f001310714600c001651800e07a61a580c00d10741e0428000720060113806900e05201000075912080c01d00c0f0314001c52107590b0108040d90401c08041c0b0303100f40302010460320009e80004000c1e440000c6001c5080b01e4a40390045400000c048103402180502d40c2c0003404580009038140511007100d00a01c14001c0480e65404490758000080f66113000883c00240400c42403004a00403840070101c11f1503110052401600d010300712825103085d021000340c21100680c108051040e81e20300030404a0240805800030894465603000158501e00c14036080317401656260045000c42d19914182100c840c1c10103c3d450346e40140d407400c1d0388c140d14668140e007038900f07000c0342d94140103556015500e603070580c000c03441758a036214804580d40391740f014052203003101c052a902e03003684904000540c400c0c20903000d410303400d2401a0034190b111420702c0701264650410401441808607c13001d6a0545205951810820109050801c124406c540101c06c02a407004c04150070800f4030342 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 544320854 1250 544319604 544319621
    0x70c29010e100f08060109090f0813080c0d030e0904030c020a03050d1404060c031101060f0905011d09030a030506060f360a0303120b0a0b0d0b01090f0b09012001 71
    0x1c40e80c120790750f10b085802d800d0165004891194004000400104040f9085000000d000700d11001d22819107603180640c690051401c002a00e000c80703410400c644043c021030b151040709555a00c10568250342c010150f440041d1040e1280748030b08013050a046c819400401c00e264003400c1344820f1a100e09056664001e00c0490100051001c07450b01c602d24000390584080f50101d403181314103644955400da4807243c455015480a640c7c030f8000040b42010117013104001d1038090750000d0954140008010101c0c0980a0420001810000d1104d9180000122a1502c0140c6000a030649881c0002030040c0700325950303800c0044d00030032103001c1000034031442d28405c103032501c008003035505d01c5807405012500208181e40c081c1c0405000c0000c0307801116015000c0c0307805400010036100960014207a090743e5080812182d4000c1101c0529107090b00c1401601d0000b420048a0f180c600b6402c603075001440c0c043c8003201e00700403d0b00c1415034054407403a6450030000032a40352901030b4001c0c0324000c00420 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 544322104 1250 544320854 544320871
    0x4020319060315050a0606050d050a0b09011d010504020a08010e18011b3c09081b091f1a1603030c180e06011116080a0c0e070c29010e 59
    0x280820b17421205882010116080380c5c17a01410103001c0b4690500a04004250041c1c1d60307164103040c3c005540720340c0308901800e000401014910300450701c04400c268140c114502580c8100400601c3c9604900e407907045480c0350401704041c1d0344540d038864103031808103180c95440d07090134003140c0100303014000b940030b8210796030b00d84030048840034900400306aa814046030018044140c07030050900f00386141c104080509282054554906605e481c016018180e40c3c03202400113080c0c001442c0c0364085a80000c0c411702e540d1440400c1c40c070001040141485142180c030451380010040c005840b0686800256444188070f4040442c100507003e0904c00c1094800602181c441c201d400e400f0201c08010f69640a001c1c03083c40e600c081c0155045603000c407007080b0501c60400303880c1604900081441c0503120313020240c90145990b182501c03446d142a0080e40c1205641e8081090450f400442100c81d00e0f0003220450340b50082502c0c00011642d01200e0a0202440c0c00011807401c1c0c0d01101c460140009 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 544323354 1250 544322104 544322111
    0x50a03030f0c051603050309012406030507140d0203040c0506070b16020307030e090c090a09151d0708070509031e10020316141903050601030b04150504020319060315 73
    0x210108a0f8103100c0c2030b455903034031881841d040e0042071007140a10780c00000324000103103d8401c14811540302c89003905030201510050760500010398035004440d080300281c0cc0a1007006c02201100116000e5080c5012442d070b40440010280304004609000502019001d55a00c1c402e0342001419a50103c0c2c040d5520003443c00e00c810903d02c008112032840d9015a90185554685010400e1440c80607014031410780c0b00703000c0420941c1c0c03001d460740010700a800c2c0000b900c0c00d408512081070040c660040035403520a4050001a021112000b5401801c074a0100d500f940e030340d5810f40302d500070750081c80d405201b00034035000e00719620150040030030369000c102d0300d0008a140030384041c3c5c0303c02c90b591589a540006540800750040c060142c225401c01411418090070380d0129440d645500d416000094440d000c0c800c2c44e58141c401c80d00c00107400d840502108440108178070b01d031512031054900a40c0c2c004002035050503407070b00000e19154600c6c030910a2550300d0034a44080b810301c141012a1500c0e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 544324604 1250 544323354 544323371
    0xb0102010c0801210f02090c040305010e03040f0e07120e0a02030c0d11060307021f050106081305060705090a030501020a091706070e09041a1f170606040209010903050a03030f 77
    0x24042080c12280daa01d0302c4c0000c14084081c410402c20009011509080c0b16a1460010780d903150015104081007840952900d180d030401900751540901808981e4200b0007043c0315821200d4241416038103000c0500c800d5441c1e00c01c086032011203119000101d189040b1078a00c1040002c90400f0840b8021003c0b62035000c120307810443d036085c4541000781103601c030a030550300c141041005940d0101c200e0040d078002c2030910f070f0380c0614000340e00390440c3c4e0345540b507005000721504103e02503005007102d00035007105030855540c140d0710400a841f10040c002d001c900c640e120303a50303c1107003800b940e4080001e54594100f100c0141400f40580210f82d034400c0a451821840580040c805103c1c1d040f580d1a00315401f105810300403e480c0c0900152003071000c1c051944100452005064003c0082c0d920f4001485a80310418020326600d410a008000400002c0490b00400103400350b04014126001652a8040e600591340c42c19590320041541c02168288824180c040c1d102100141c44040c3c03d000c8041f = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 544325854 1250 544324604 544324607
    0x2d010333060210060b04051516050a120318170403060e010b011e0206150d0615050f010c0302061501031d07140a0e07030e030c0a111905030607121e0b0102010c 70
    0x40c1d01d0f029030744a005c4148030401c650328161349508080300141e03d40514140f00402028240102068182d8a42c0d10007001c1d641040341d10082c541602c4401d00e020460210001c1d80c41c46002c0c500e8102a2094406036910411914a00e0481e402594850300c10811030000782201030103807804001440c0410890b87d04124032400d40d130001d0904c00450b6015040c20b64540d000d40c48180840390219800c10010b80314100001d20900c00d250310f401c0c001400b018114904020441207203420b0b182c40e070400403d00030100001c0d40010300160080745921141c0451024000100c004003c21001083c40000400141407003280c041800c0b070940c0d9842c0c2c000c038500303a4403105001d484a480e00c10f45007191510030014003554802c0d03210100c0607090805980c030b48040e43c514146000c20340f03182594040720303140740100c2510b401024086007000120700580e00705c0c54140060340b84c4100500c1002844008603108042030603d90007141240c0888032036501c00c10b411440e020050416141c1d403800366103009074803034065 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 544327104 1250 544325854 544325861
    0x512190e01150905090c0901090507021c12050709150c0f050a03092405032a030106050406170103050d0f0302120c0712020f121c1a2d010333060210 65
    0x7000041c010340071f41d92a0240000040200801400c118003c641840e50460710000041055800e5070b44c403440c416511400c09030880b40301402100900484410800840b101c0c064a500c001e0001d007414101c903102800e01d079818245c0e1400080590040c001444101a0845800c4007682c9500075059042d410700c400099121704601080d5011403420b00001e00400c0c00e01c03404190f010024052160341b60903080f26000d1540081e00600b0200d81c0204040c4502540440801041d1b100d0240740c00a6514507210316450710003285406c0c0402c041c002c0c1200c85c0c18000c0e0112842454004040089403800580b04603054110000450f428803401d0340340c6442510008a194050760f4510107052001d01c0c0540c0156603a209141e84086412521025041c0d0400c0d44503401e03849000340350898800c002601000251503078907445200c1c0c0c0c4c200d02c196507540c075421151540652070078200011072440d551030b0f80c4c0d080710b41d29581c865041115005450440c00920f644400c130b4840750201c03074685400c204d110058 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 544328354 1250 544327104 544327123
    0x90f010203090a0209060f040507320d02161e141506010f021608060901060f120201260a150501030e06132a0f060512190e0115090509 59
    0x81e075011030f101d1009440d00d0801c0c036802000c020410060f156504001c02c0648004496040101c0d0200309482c1d40035902c9082151040c5440800c0b1030000c0325029007081e1400b4400d045070540364049038031403036484218034500409070000c00b90144480045852031401c4000c4000b1102c1036044512890756440000700140e194884144a80d85a9940401101d440481415480440c0b00316804290000000a103d20240199502900503842c20300c800509560081d442003030540302c1120100b024090b5100d820781c2c41c41d4246413000200c03210000c0038402d0390b03045194021303c041c0300050202d0750b1459800b5034042030a01084403991070340c800c015000c440542d921001c0607003041d000618001641c2d00665002c911074049000c1c19000043e000803506181041d8000741c004e441414091560180d90102c02070205262252922000c041b60040410014009243d140a050364a45210640f0b401c04096215188000c10005000380710340d00801220740706d038040003484e0501040d501e40002c00c84166 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 544329604 1250 544328354 544328371
    0xb090f0f090403120b060711030c034b010c0e0f032119050304060e0102090d03050c07031e020f040b061b0705060f040305060a0c14090307030f0605090f010203 70
    0xd0a950b20b40b002e482c845600002c01000a90720040400c090340c40318050120140200705d801c801010a030245803902d000381d001c1d035110360702c01d0307101c505110060450a1a850040c000a184540e0064242c1402035014030300701540c06d4480806094142c0c055011040132481942c803600104188001d010600da0009003050701900a24026012010f543d5822810342015115440c5841030341d883e401d01d02d0801049110000b40000180700a001040c0512041c4e848020300031031420800e44001042c461a00600a003484804900c2c41c122400034085580110703004804c0c030000003070701f01e81c2404003810514120b200e1140f42c00d01d0000d9050078440c010702e88801400561410411481d019401140a55460890301c10f000c0c3c040303940c0c0c580101a0585911014001c1c0e1a5419440c185051200043c4030403034062410b50001d24042e40304818000070310004c0c818a0345c544080020a061022581015024a1074440314000b00149030b031129200d8900c15090315a20607211400070b090b88000e840b80e90 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 544330854 1250 544329604 544329619
    0x90e06070e1e0a0504050a0504030f0206060306130302030706050c1308030f030408091915030506010c030206040201081f12020108100614090a0e0a0f1d0709050903070c0b090f0f 78
    0x1c0d014203100c2c8440c1200c4100a20703104406580c3e100003801e84108882500c2034a4076801400201500711103655411003c600161200b17241c007901080da80c1c24018078912109070031507180c10600d4001c0c41113444054010109010354a4050072904070b95001c65a08410319080b034000055000c0088150b580310146d0050309451912180c98100b000d4110442c21507002da4040c0416100900c5c1c403940400806d03085c0804802d110b00404090101d41000b0701c1c0b2418400d1880d00c0c440000d50204003164007c0e42400c00351b403a600c480846110300c1307094058400300d401c81003401142c81114411134214080c801d9031103519544d14071000b03003080007440c41502c003c200902c03800e4040c09000d034054450810040c1107040381683e00d034038403601034a00f40c0f00880410b59400a1207100140c2c1c0c01100325000c07041f6074090007128200b41c140c2e92071f0403d2148031941a80c481c0407e25000d403e2045038840e5400c140c00111041d1610103d01140c0d000f0280c085c4030720084441c00d01c00e800e0030801100003003801440e81 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 544332104 1250 544330854 544330879
    0x40b010501030e3415030f02030408091e0a0303020f011109061806070b070528120f0603210201050106030c050702060903070e2403030c0604020d0309080304090e06070e 74
    0x109034510044044e03944c0045501c440d42c5441c40d40d010403002440c801d260799241c03042824014040711121281014500e00400030400850018400c4810405090320707102404100007011064640200c1d400351380c00322654000009040e0b0014241e40d03020005402040300c03a5103a00d403040e00e480380c007c566401141c00d0100048061940c1414520036101800d0545008000e5943c18203a200c12504180491004142c00d2010070011000d03424104140503425001e68100030058107c0c1280a0000c280903124002000c403030150b500610025030744230202d01d0080c43d0040c500c036420000c05640700010741c6400300004102e8803d02490516180a4807098901a55a02448216401405116090b100b030b01c1c0009900c108807511540304500034680c08000b0a44020740b04003a1051050180c841c0d8400d00c400904400c0204059400581c1100d41c0815494140707401c0c7d48007070741d59101c4403c601000c1400142506180c01c0440d11038021810f035815541c0340e990540d124206507103116007200404e042d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 544333354 1250 544332104 544332133
    0xf13020a08090a0c44010f0603020a090b06130e0f1e010312020c030f0d120204140616170a0801080d021209061c0b0306010e0c03040209150315040b010501030e 70
    0x34400b8100702445d1031089480c40a0360849001900c0b640d1003041c0d440c0c010307040c40c00c00082c450302d041c0e1022604140401c91850300013580384001d03405034183e0180c0c0c070044d070001ca65810044841c030350030012070003541c07a5466105500d0b0240c100ea40741e030a01480000242c68190800c1500c0c2d00140150344a0000d900311307250101d00903942c0a0342ea040d032080b44050180340d50200014030000e243d0100400c80903640301c400518600c0c1c03007441060900d00602050020b11200c0c1a043c90841e810f807500d649501d01c4c40e901e1410540c041001500c0c44d03820114040c10b040680000700101340d40d0b500c40041599a503098583d84010404203d40107030480c8a02c009144c81c01c900402880c140281300e5030402c800440010240702d05070040303e81499540d0b400100d1400e0502926004104001c80300c6480d1408205400d030380d110060000f4401c4d0140c0c80002c0c603044001c0c04020342e418001e006c440c541151491505000d007000d9800380e0701d91103800300001d80b03036209000742c840261781100900701180d40c1c44c45 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 544334604 1250 544333354 544333379
    0x7080406020a0504170d120b0a150201110304082109100b0a050a0801090c091b080c04030b040b040302010605030c01050a030b060c0627010207020607030c020f13020a08090a0c 77
    0x120010000100030000d603d6400303403000b0070650840005080488103640f80601481c5644131404840c7e403c000c9040d62036541d01e40c0b103c00b101c10800303031118903050f1004120300625031425007030000c1c030012041c081803154000161000310100640c0e0001c00c1403102c0a503464003011590f82d841c035440100c00b070590350015006105d4034035010f0417501001d9141c4c0000350a014007074112140981d52064400103200200961b880180781040c800c0010781910300f0b007546e0590b1040158400d215580000c43c02c041400d404460045401c01c0c149002c904161420000304141910180c00540c20180e0108607450041820380b00114140c580514007411844184d010303205032541c076603109000380000060001c0602189219100210202c081800e00c11210f14064011a805107481d07881400400d00507150702c0100e40485415091602840c1064400243d5000d413440619030040c03a40700ca00c071224007454001d084000320035261441c0703555600490580d40d40752940007070008000707843e003004042d602c2032 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 544335854 1250 544334604 544334617
    0x3050f071224020a0203121501020601050d080919080139090b0d050403020d080702060415180c0504060504020c0309040e03130806100b03040b0a050a090204050a050103020405010e0708040602 84
    0x151003000d0b56049801ca50480e049202c403400540c20000c5c0d5800c0301050a928142e228410700303503080c4890f00400000f50354140500685008070940f80c039203010f0101240903103110090083c41c00910b00280d601c00b00c00c503050392081104c5903007000020180c4c0b06241c10f400c0000000300c0038415590746c08080100c0301148280040c0d051140c004004281d0403072002c024007003400303070510101c0e039410241740003480c00090300340700800c0001500c00d001c0425804941c0e182c1250700840c0c9504001c8100d08000c009160081b5003282003040901d81c0c0c41000012410781c8121030f0119000c001c4280c2e1042800103a1168001c80d9841e03400030016911913103407503845106102104800c0301d0070244e030030300c580501c1c50071034018141a9010208000700101070740e078140c000d0a800d00216086050541e00d00071243d20241140c42038503210300004520810f254002190550018810702a504121000c030004050a000070b074017903400c0200204109070800d0205000b8011695090f84a581c2c07a16108000d4100b07a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 544337104 1250 544335854 544335893
    0x309030c1733010f170a0519061b0c0309050d0c120c180e0706110a02040c0516080c0f070e0c0d06090f0506040c020712141c0903050f0712 61
    0x281c5002201942e002d9074a002e464941c903299012800d1201c6401001e07204400466030364030101c50440001c101040c80b00812140700c040c40c02c88041854400007400e4042e02100c03503d0051480314034000c0c0d0001c0c580d4442070103516100c194a85820505c0102800554040c100c1e114010081200010040c0d511180c0380c000e038540041b881e1240122820248a503000198903600e40da2880e10b4544144110717802000a82460880304c5689500b9544a41524201070321803540c42d403030b1181b003601035000c51f00c2ea10003120850400502c0c0d4904420b450b0090864649144100000744407082000200c440c282c48190b0b08a821315a210042c00e401a8001060707480e031a6204e103800545490303640604107800e50b04800104440c9000014442111400c5042d001103501080080148022460401032050f4000c1d10742442048408040d9240c00030300f510000e15000b80010055150343c1c8101c5000c1603c0c403500c25144d1411b1002d00040d03440b038031401000c03400301c04000c10500092105101441041d80d1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 544338354 1250 544337104 544337173
    0x9120c2d01051c1803030506010e0a1203120c1106010e010e160903150902040b0d08040605090414041103060928020102010b1806211506060c01090309030c17 69
    0x811240b50039640071141e50300c0c0702c10a0113052010560540521a4068400e00e000d8001c16900c50015845010758484c50819807881c0c100801414070404110720b05045808041c0303c07101d0b400c1c400820241034052035003100d01480c0c1c00400c8008050080c541201d490141003038103600c482014003000c00701041c02d08240302a007c4000002031003010650000380c0403107030003d583d03031180c01880190384566407038a100709184a142800201004141c0c5d0030f44c0c5c07203454401d84409840c070104c0c004100d0851080140628a8100010000c84078004e5950043c180c06440e60b42e200c200a03280e417010100030490302c0300e0120001d01250086a15204500c500500c00880c03403404240208a00290b01d005645226400c001000950b0409000803031600903425040c0c5c166070040d480751038450380c924428884240c00c40000c55110350302d09050722006003101c00200080401403030050018811031204450400c3c0311003000454400100c092030802c509a03000e000d00300d60f44028055040c0c1c90700e2142542202 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 544339604 1250 544338354 544338397
    0x910030506010806010303090501020105160f03061703040911030907050907140a0807080117030414120f010c081518060112021c06050a05012309120c2d0105 69
    0x4007041064000e000311409081c1550650034001e210544a803c91415681400280114860001c86001d900045450007400000e1440c1c0c0c11000342c480307135010040c3d1b50459801400011700210042c4112148a01c080002d1003040d40b421aa6000c01c8448008580047c84100400d00380003c0d140d60184040c604284004941050880250403200044000070500001c00c201c01e078104401c0340c05400d80a444100860040748019903038803860140101c0c4403030081101c052529880850032400030ad0709c003512040070804080c24002d00d03031202d4007000160b80001081090701e42d0701141700003e0010301413002007040342042c801903840181545040222441e403076480e40c21281f002c3c0c660442064024603081c1c80c20b01c640000d9807956007085110310700c00141000540c2c0c0040c03080d000d0349a0902c1e0300c1c40000d46400714100c1801560043c0e600600c1820664651000c049001c0f0703c803210132640c5481c103d801200c41010f1030400000e59840d00380c1011050740c650700602c060700d01600c420308040e03400701c07 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 544340854 1250 544339604 544339613
    0xc031812030414010606080c0414150f0a090e062d1906080c040f051903150207060f0903020309040b060d18050f030f030424060b0d1811091003 63
    0x80c800c8600f9035400441c00d0b104941c00c48203000e244010145c0d89081c0116003440744045040d4401c1d80324400c042d002c01101840309031510380994055455594100d900c950b807610021040b6031100c40c40c2000030795100f0380402d1018259264500401c3d01529860440712980d8503a5112120107240901038920310350110b031207503684081c1c884520215030518003000d2628502610b448409440184944000c4c8018841400840074800844008071502600c8144807200e00301d80390040c1e040a004803c6c03e4403130795240310840c0c0042c0b54071b511a0404020525211580c1c00072108410740003001038004000081ca146030941040c400000c0051003d403400f400c80300d15108441c1d560b00c200c0191105801200c0074840c0504c02da44a628009021f0361030305000c800b040792030303100042008200c4088141c07001380820000000071602c068000040141540b1b41580d01d0b0707550400005640f80b9070500500e9246160b0110501062550101c003451039440c0800800c0182c0c00300614611001c0c019110000c04107 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 544342104 1250 544340854 544340857
    0x2a1b030c0215090a0e0c03040b06060c0102030a1a1009050f04060503060f07021c0903030f05070803070903121805041d07270513140c030a05011a03060c031812 70
    0x1c205107082c0e40d29009503041c49448491603100b8802d0301c25040421200f0088a02104e921681c40a04c001c030719071355440014468003645515410130362000c81040942040d40d444500c040c100c070a485007504008030b00b0410240440341c120400104561000c000e9400c180071081001403000300086415a112400300380350100880302c010054440c9410f205540303030180504d582500304041c42c002103131241d000103400e4429601c0018108108000c101000c44e04c0ba03415a22515400000340c3d5603420300010003000c01003240801e88040e0340c00c4020040c0d160207012143c3c220903450203400505445c2004010040a4031802d0f600200c500402d03004040300c0601040000e802ca0602c21104a05803138296a086c0305020340303503044149808180032040341050a81d000465025048985009503207840d2414008040341c40ca825201d40f0302450b081040c1074100803401d2045a6605103102c00070010141d0f2000251401d9513490b100b080070070240d00c149880d0707117021f60340001100c0d80714250444140c040d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 544343354 1250 544342104 544342129
    0x30d0e0f0d03030b15040b0301171005011202030705030708070b0705030d14240f0d06090506010f05031501060c030f0c05070303050304061803270e04062a1b030c02 72
    0x380e44d075003030504103203811403004c1e116040c03146000d810300e42032210700c0b02d040c4018014140c0c812059804a4003203401040f201090400b460380901c01c5503900c96000c483c5403120300c0101d00c03a0240040205031414005520310841d5039450041c84510300e01507a540c1c065124139000d681e18042040300c0800c44015000f80c1c0c00703004d0f0064000c055442e09607180700340c1113188044071f00d00412840d246a05070340c070703011100c1c0209011603d01c0d240110a00c1c01c0303c002c0c0b00c4480020400c4c0601000000da0400d064018001c5420985c143c038071b980d03d00000c0070001d0b003090050030040340300c101d07501b00441e01c101d4181c0c0c003052681c14441c2c4200481c2c0c0b605031525031503130f0040f80003500001c1040100501c500442c00160000b008081040d110781d94050100c41003001415640a15a00280040ca009845d194024450542c1000d041d050a0a14402600660114640c031a414080c1c0882c2800480c114103210305059413010810b01d0326039840707544200070b5902901080880754508015980b1a40070002 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 544344604 1250 544343354 544343357
    0x170d0c0e100f0c3f0503060103020f2205030d050705071217040b07170901020d03020c010902090103110910030807060f06150903030e180c070201020a1703071805030d0e0f0d03 77
    0x154400e03a075121030040c0c1d4561204041303011950300303004203058125069030f410450900b000340e1a8110340c1110b003198007542840740600180c4400740c1d1550b00350481b05c04142d9a041c1d041c2d811740003012009580c54410700e000140980e101c00e10400c03041081d00045442140701d07082c04107042c0100c0c0b5882c0140c0c1c1040d0080c6001c207500280720b0040024176510b1501e40307094000590709282d007000c0040d4881d207200b000d01342410f0300020202c100714829400f910354582d0080c44029656160309100001c40710880c0d40c0390283e400d00c004200040c8454180c40b040300e0707101190758503001c580c3d80d441c0b011740300d40e850104100307031201d4011424074206d60360b15604510310b941d000800d0b031840c140140f40e012400c5200c0e00800215007140c51f40003015541e83e521030162803055a817070f406440101d251450400300034200903040c80d1384400c41c14082e00258000c5442e0359654142c4224a10b20078091011ba00c40c0540c181e110800d01e0300028025403e10311010f400502800c01601407074081a10b001d00c1800450 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 544345854 1250 544344604 544344653
    0x20702120c0a05010309050c0409030e030f03120a06051003020d27151503060209031c0c120503070804060504021224090105040206090913170d0c0e100f0c 68
    0x1c0389401c1c41c0305100020407003482d051281344c000e80c8035140c8940e1582c2140340110f466400040c14140520040428500c02500f21001f40040c587c4070754481e0002100d240e1a40038840c081031002d0300c90b02030241513030710040401e50010900360058009500c46100b0714901074a880503180302d091140ca036011102c81800d00642e0740761a5142c0944000c0d1070010956115191860b40b1300d08040b2540c00405503136009100682d12500c58000900c0c082c650803801e44910f14504075138903466448444404058031484080340f00304200c6200fa10742e4002250381c4000140d00c1000200403038200d402183d000350002e460202052400d540311030800f01d12030144184511006020f04048400d00301085d407219000700200140d0401d0b038001407651040b0004030703118450b040041107449403411620f0366036030f034440204940ca40754002c0000700c41c2c000c1c4088401d8645000d03a414102c80c00f841c0c0c2c0c12900e001c01010705600b0306810b074042d54103040600a510801000c2141d9000150188514000484821400303c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 544347104 1250 544345854 544345873
    0x605031806250c0c0b0c03130b04050a141003020f0d05040303020c250306090c080a0309090f050421030f022a0f0304180f0c080a15140f010302070212 66
    0x38640c035050700400c2d07820031007000c910b40c020070f50440c2d12105840080f2403c0e903540010031001072440c042d046c080e8440750f10003074001904081540c024400c5800c00d80355841e0244d5a0800d5840044000a42c66008000520068155880780e0700400c0d00c80c0494090b28104640f03400c451040300c0085904602190b8000f0710321020140801c0404091115401140c0c08000c28010112110b07010b4400148401c1c1c17516031910801c0010740c0c41901501080b000c440c144241c42c1002000e04c0c01a12035555501d146c1000c0b041070315840e024075446641c120220510101c1e2813550070386040301c0350458000700340c0d41e040000450000d90004091040f80707081120b650341c1010300d0340b41070f09040c200704501551124011803020603011055400321135440001c450009050700d0004064041548150380c0d0524248a107007146801255a900960b1800c07008c0121085801d0400d01c1c0744594021141510780301d51704846035190402075841c1045040c034025061804035800300300050710740e82e0340811503000010710 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 544348354 1250 544347104 544347151
    0x3090b0a0314180a0b04050304120b0604050f150f0604150305060907020d0c0602070201020c1c0506060906150c1905100b031209010806030c150d18030206010605031806 74
    0x543c00c5a24414840c6022200d62825541c9103d24100144180401c500060a001c010700696000700301d50640c62034190755520303007101c0340d06044035654491032810000c02d0208018012452049004074070010110201104019803480c14051940d80b0000c00c11010904060b0150781e10f8800312a500d01040c981021010090143c000514010442d4080c203400f81980341d2104c0080d0026402107001a03585080c2c5c00100e0528861004480c0c210060075509400b202c41000a0034403140184240da45d40c0d200c40d002c0150100b001d44116911064051900c001e40c0178100040050415940c01c454004454580e4500400d050700e40030b4442d0b40008891800c401814000c00401d80c0003140544801e80340000c00090764003444a6440c10804040002003064a0410090006d070f80000d002c03214040d030302001000c00340c0c40658003030403103402c112882d1495100490341d0084254190003a00041c0e0070440126042e80000f8010200100960b1130b04000e82e50a0003102c1c015aa14816080c0d0107429460 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 544349604 1250 544348354 544348391
    0x10608100e0a0308010b031905152e05180a320913020402070b15040606050405100516080a09061d090f070302070218060f0a1d0403090b0a03 62
    0x200050760341101c41d1078400698041940ba055a1100d41e00c10341f43d8503905024041301d9403c0050210641c1b4220500070105480e1150804480080f9150404440302600600e0000b4580d03101c9607000780a601804100750041018254004440c0504503501200900284410301c055001070480d10711024076a1101d10341c103004480c40001c01c00000c001e01d00c2480032501c0342c003008014441c618803420f5890308540d02d680440781145e07040788020b5650700b0030740d261000074098040420708c503514180c000981a401002658204c1d28001d00d072064482e200340c01910b699021107102080c400e00d94540710006000c000292070071082c0e50b5950790b54030303080600180900034500603060b481e24960744510104da58401465902c003d03510a0b603401500d4940040d000782c095008003e60066066024520128250348500c0c42100b040304c00700c0c001458442880b41c072280704d010f01228210a01c01c03020a0320b04c100754a9400a2003071401c1d0118903030f100341d81c8000c2d8100c45120f00001c1d88510390a02030b01c10042 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 544350854 1250 544349604 544349621
    0x1c02010c050414040911191707080604080c0c10090e0a0204141012090609111f030b0105040e1825051311120106080c04030201090e0604060801060810 66
    0x2403203803510b410802c00c4041046a0f40e0140e100d0381d1a42c1c0103404000c00049500b45590b00503000200300c007001c2120120151190281c00258400066207112300c1d000028100121801d0b0005001e15843c0d83e221205ca941c80300312070f0b804030700c19640300c0c20450702d4060350050142229614080020b0a00340c041c0b180b0180075084028060041c4424400a40f005214000b00d0f9400c850000d007040440d02c040c0d030352440c018a8118014504001481446043e800914030203208415502d03050300300c0010842c1c6400c14044156400c40445200036100780613a201d031803448414102982407d0f615011101a02c40484014075020071000500203040c0040010940095103044031265181481c111038802000e10300c182813142450b0480e0040c2d140e43c070b41c8900345d0300441e030b0002d5903610060750622003500000c3c0709100c0017980485c00070f0700b400f040100b5035058a074165500002240b0380300f051441d07010b02800c11548a43d6401001a020f00709204240041c01d840001e4452040c1e0070004c40115a201c4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 544352104 1250 544350854 544350857
    0xc180a0b01030b060f03090f030d0e0f16031b0509070f1b02010f03020a0909021201061409060409091104091202190b0109050415060b04140d03090b0a030e1c02010c 72
    0x59240c444681c4d0303083c140d0790844200e2207425200da4071081e030303d4500125405101005c2c0400285065012055004602410001c0c030442d0364008454800c9641c41c00818800c18012001c030a09000056a01c1043d4030680da00c0b03d000d100041d00e920003c0c21000c0260b0741200420104c141c0410210b41090103018110003040202e59a0b402c5500083d010441d00c882130000c05900041c0003072400d02950821003e0000345404644130548843c6403c0c00007020302910001c904000e80c001e10403900602191015240a0305060400b440d00300c10f000648055941260000148503c100c015151485000da105000703074803402000d002d400000c0e0410603000c400d46400c040811070500071400c025110790460301c3d40d034070008065031039040c00c400e801c0c03004e02003030146402c03c0c00000d81e043c40000070b002601c13109660481511b400c44200011000ba100c0018041030a0310010000d940c0c8620182074401c065080125074500d41d21552410010440c0380c0d07500c0d018145500f2400a40d09100e8200c054009 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 544353354 1250 544352104 544352111
    0x92102030c1c05072c0709050409150510030204061d01052404030803150402090d0f02013b0a060828020a0c1103010203011202120c180a0b0103 63
    0x1500800d4030703450800030307841c028607100803094100040c00d420703141119007210a40c2d0940d038440c45901150388940e1000044440080950502140f4854145d409200540c94a81000c0d2a01c42440040c000180c82a203050b403151031001d500060a02990303108845e903480e0300c80c9a41c114810002210300d1500700040e484200d01c1a80186451a020386055440c01c4400f5110454000320301803d0b80c01100200074441030125001040201030006140146801c003010f0b05504004024801240079804c0d03001c0d032001300551140b0110355000e98140ea0203006242940008009508500e508048001c141140c88000a55102d2400694074039481c40383c400c07180000e80da4a800d03002000680c01034030f401c02c06040e62019080303815440f0312140103100078000564481038001c0e8058102080228256101d42000b0311404880c581071003124103850070550011072020440e0284112541e8180707995860384140c405084a0b40e0780c070081020440381c09072607104546404c5000c2410380e60014000384c1070504 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 544354604 1250 544353354 544353419
    0x9040507050d050c13091802040c020a031b0b0114030c1504091103060f13022a1c02030301090e100e06071101061d04050a14160608060916110303010609 67
    0x1049210440300040e00105031140b02070887e1190134100c40000750300a280c991203180540e008940d0b042d0180c02074a0700d10f174500548050940200c3d642c6401410002010010310a0180c0c030741c1410f4a41300003908592281169070080350252a110100c030395a0400400c08001c00300711405040081d01d41200c0150650504c403011030b0b0300c10302d0403550620031160741000740a108419070503612440b6440c11884000003290800b4008250071404039404d0b8013032500b4490f5040c1e045540e008000d45140d00540c51a072030705191000800c001070301e004980c020000c49503910032082c014020740002040140025040c04d58000c2c003040350881030b801c0d8a90600300100282002802c82a07941291101c4410303042d80d86147c12030130301f0005200202a07008684080301400700002d90541c48600046030300c140681c84040c16903640000b1641a40c1c45603121000500d1b0b0140c81d841d8000c0c032101e50030603403000180c502d0b0a03415034209030001000a1102d0781c04000c00c0314011015500550901c0c4421964503 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 544355854 1250 544354604 544354627
    0x902101b231e07061407080f03100503031201060305070203400e0c1e03090109052413032313050a0503151005031e0d0206071205070509040507050d050c 67
    0x10010f01c150014401c5c00282c402e0490152011030704000e030300a010603980c80007070321094055001034810102c100300e0000041980c0c203001080b11304006002082c09103681c60030200300d0203810024001000c50105000c1c3d4000c00724000c1c4c2841c80c600d4842000c00c40f002e1061004121401c10f04896200c404045a0420004046008180c0c0008614802036903607200107400301100382100d00d819580704400070401c41705e00419400119141e21820030b903000c4d141658400100d03c3d800384080c141420f88800480d14503c080f44075800b5085c440e041440307400c0520300b1701424000c50b0748840240e000c00011f0580b4000ea041c0c042c04040e010450310003810f5414200402e544619030140d05002444120100d01d036108003100440042c100101140c1b01d041d51410520020010804001c0c3c4512810210420142c00803540c80d2040d055960385215140c5218492006031102800300e00c00c3c05000c00c4000c01039156800350a110703685039240c140d0381c0c004d84c00544e007c9450051804510400c103000c810500f8 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 544357104 1250 544355854 544355863
    0x40b0a060c061a061810050f040e1f0e090f01060b16060603050303010b0d1409030f0f1201060c050609070602031902030c010f05010e09010902101b231e 67
    0x102e40080e000902c1100520381201045508148103a02c4034000c00c641000442110719401c05800070b83e16501845a44842130317a0f0b40c080c8a8005064100c140801c0c0080800688040e600c24045e4000000c680020114080804596002042021120000c1059050b0100620989044440020445146400c007824000e02a4142044020308440400420301805400030009140c001701680d03030702e580d28154074031a41d11122145007224242000c0b0100101d080d801148034110a4000e1440e1030342c03040d00880164441148101c401100b4001040e4400d4800710482c0a0000358440135050910b60804515050005003407000daa440450188101d91703001c0b0540e00d858440200259900840c0281a4103501420884940c59880d00710400030042d4290001030489815450b20341c415100c80c2000e41c2030303881c0035401a4101c2400c50844001e81d101d80341083c4091720641c10700b01c0e526540d54030b02c2001c100039029030b4021103191040500b4424240208045070360040140d84c0e041214101c0d46458 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 544358354 1250 544357104 544357127
    0xd15121b081b0f030f060108030d0b030c150913020a030501030b0f0412110a140319020a0305090f0a03060515040e0d090302060c030c030313030f0309150b1f03020405040b0a06 77
    0x200f1030450545440c0d02c0400c01c9072070b5050b401701600e44660b180d030b00050b5240c000c1801101a281080c64501c0503060125220381145809000700083c1c0000d900550510b030f0001ca41c55402914250180d480c0d016a440035040d45103135a034001ca0694510304001740c0701000903069040307030b07110001030000207441c1d0908411f00079110305080d10310003800030391207042a8610341c0241c100180c128820940b0b00d4080010141c42c0c04084d0b8408208290309000c990341c0c2d05017040100803c40c10080d04c815864011005502c8040c01085140b50540700d41c3d90105613102035a40c001901107000050155240500a090310805808028043c02a01080052a19400f4880640035150001d0100414001401100c41039040c443c1107960340c1c28205121035040c40c0c0c144081d000034480200d00003a01c1e101e402400340041e005443d0707580087c070041000c001400718628060f0301a49540016801c2e0084090b04000e0410360340300184c503549480140804c1e507120030b40d00740c4a03130041002841403a0b04400050203 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 544359604 1250 544358354 544358359
    0x2a0111030702010e040b1306170f151918020f040b10030b0a031e05100203060a090e0a02030d11010515010c031209050601150f0f02030d15121b081b 65
    0x40800034440403500504813040c0851f08044152598040c0c45001d07001103045406c003d9421781c059410f040250b8a507216044103240380d82010100001c2d420490b01030503000040c12000ca10028990307814403088465064100303940c600285480c9041d031074010008410100c1c1600c0a000000c0303c0c0700007581c50342160310840203040d9241055005078881c13480d80c0010f150320100a000d84400794000207400030150300100d036244107591210303038000300c0c500a40c0c0c05000041d119281050401d03042c0d1029152075040c600d020b120340ca6072040583c2d410443e0414213505603d0340350040b0f14418030f007401d660005000303803071130081c00c0c504101990340311711040703030440d05450f01554034090407500b48080c00750303108040c00d544901000880c06201040031511010031a8484082d00001d203002900c0d0080a4000c15001da00140070301c42d5442d411b0380003600980c8600715072600380c030748500d80b4442c16048010207480c20910b01d8042818202c0e002903640240c03581100408a854180030103000800041d2112130 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 544360854 1250 544359604 544359617
    0x5030a0f0c08031828020d0311060a060801060f0803031302150a0e04061509052b0f11152b050f1b040612050709082a011103070201 58
    0xc1456119006908a00d42e001d00119664181601031a5407507442481d2405140542da1000040c40020303001c081100c04801101d100c881c50380c4d000c01082d611010000d8041c40311030084681501c4050003110f03c07603e50031000280321707400d21300c2203400c44106400c030311403c0907501d205000c0d405000040e0b0307a1000800200c140710024501c0407030400740300041240300c0b04401180f030014041d0810641071640106072401c11015554010140074002c09020303880203e0360095045c0000d041070601d001c0d842c2007e0714060114041055810190f6031503031b005407268040074450408016500c0e10010700304408444803103400c1a1000e0402041c81007283c40507200307055611001082c440c2c94a0101201e0032803400f0849031a000d21101010300007143d4401d048a82110f040300f000c21000e095074151000780d070300c140b0241440500c0301c0042902a0441d824000d41d060002900c0b47c1c10440840c41042801082c06400b0040a410281c82e80c05409581486008400b5a00424000080d078052540918000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 544362104 1250 544360854 544360877
    0x170a0e120318070303080a050c0a0804230f031b07051c0201230304060f060b0a0e0d0231180312061802070b1e010501111014071b05030a 60
    0xc821582401c1c0002d02c0b50050300000814075811850844c03284070300c0072007800a07550380c034a03596280c89041c181201049901001c140414145101e07074004000e03020140011a070030042c52885c049080c2682a110303440015100d180c050407400084200742c0031402442c1003410b040010f881220b81e51900350460f102416114250f80c41501a0003050304014801c140e0390040d442590070551080700c1c01e80d00d0605214140003a40350a100b09403c80b10481e02d01414101150000c031100c0c042d10035400d5020084402c00b83c00340c4e9562803103510307544d00d801101900c40c40b003070b0213200c05411410b0214a514580702c0c80a204074200f4010044050749490304000e100640a9010024045600980801040f021142410841c1603005042080c040d03040074503251b840c462613140022034041c48082c610b071021700401a40d40a001c592550003004020385150f46c000003941d004448100c8510313407000c0780c1ba07130a000c41c240d003002e071030812012200b0782880e40745e1868480c1662032081c20780310000c0040e0890312 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 544363354 1250 544362104 544362121
    0xf0306040f03031e020301090c0c110d05070801140f070c11090405011e020c0f1902041d060c0711030c0102071a131508010512100914010c170a0e1203 66
    0x1808041010030202c0c119080420985000350000d008c0c0500c0c851a0007144000c85d0b004007000709409a00906107a824a0b10030300780490303516045400c981c284541c48011401c51000e0141000444100c00b00034614500905010f5040001405283c14465281d4500000c688104001c07260f0710f60941e94285c00d0303110341c1303000fa00404280e00c0910400c0401c00071501500242e03001400c1c1c60051000710307155001d540d0321040c0ca85145403a00081c0c500c1100c050700043c10642c0200c2c44104043d00d805049a803540701030b90902038115050301811400140c0301082050410761700d56501c400340c00924404080000207540c23418a4010b0402e01c1d004660074600c1c1100050485188103400071a0013085540c031038950349600312039007a100101d00c030f020001c911410446c442c4c504103010100100080358898460710003c104040c019151a10030340d2000d2040710090283c00090100341d81c40c61024000000098980500a060070a105080c042c2d858210040010005a04402042041d55940381c4901 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 544364604 1250 544363354 544363361
    0x2060307050c0114040b10080a060b0d0f030804020301140f041506080a0317010b070c150c020a0e070e03012f040302120d0311040303211d0a020f0f0306040f0303 71
    0x8035400560a03c0b50800c400607802013614041e9100d04584802c60300e07602c005d41045501406403030f5096000e001c1134404140170b80c007c850300e540054454040032035540c44d640e8500a0840090707002c500c00304140021800c0034481d600740b202c08520701100030304144100070005900504060200c00c214400c0b0781c0b004000f075100f8030081505500300d4141421504e00034042900c1c1405505000402c18000079490720711a0403200c0169204c038102d8126801e20010b01c03100044694043c00708251460650010303140d45a40c2c0c006040c070760b40b14141b503180010006041401c03049085009134105a04107480041c07404031040055140344041c010200300900103400c074001d50703201942c40340201e0003003861440046a00c0759035180c107903010b0203071007252041d80e0210300c42d03480b00400140414012100d40d10807590707000d9480030742d250049042650001424824500e01c2d41ea070815400c035240d80c50442c600800108001401038032044032030801c010003e61103000041c0041c245152078084482094880e50 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 544365854 1250 544364604 544364617
    0x604030305130b1602040509010c050f03180d050d0c0e1c02030c04020706090b1f0b0306060915090307060305040b0a0c02101a1206092107080301030503070c0515070206030705 77
    0x9003c680362030100d074081c03481c0301d0345030402d80c007540c50b1001140d881001801010940c803015211249403e48601e0303100c03210b0f030004002d50300082c034409031000040c0c000e0150340c640c80d480f652100e07101c2008130701c4141101c009540400920401c80c0c001e5200380c445080410220030680b0405c1c00b20040790003c2802c010310140c005a00074400503554040111551040380d505004041c00546551100c0010340288001e50240c500e00c0c0c11305004003e5203180600031940608050022401c0c03401c44408500e0210300c2420001c450040400d1a040324282000342d04e000381158030781489035041c50b48541240b814050040804141c4825003110820300030050f03650101d920107001c00208101080c207031040c201d15282c991150611400950700440e001445600496035500501110880081d801c0b409410406800a41d55030600c650408100e03800301030740c000c6000f100a1640e0300c0c8180741030704c0c610f91140c211f14410607460201c1d40030801030000380d6940e10b5040c0c819a9603502c403960107403001d00505 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 544367104 1250 544365854 544365869
    0x30c17010612110f0301140a12080901030605121018030912062301082413020111030f030a050105121b180106110606010305091b04090c08071502010506060403030513 73
    0x3560080d20b0f01d180001c50484845480715007000410908211007407a5038462130403c1c03107100d030032708000c509000010b00480605040c005400741d620408110150381c1035960102e95003185003465403001d1540685c11825665001c079010000642c3d0b0080c249800500849040308108041001003001c960720180c1015802c40c0d440a40700341c94240d00f59000424080c4101c0c60254500c1c1824410007081d0528411084030b41e0342c0603035134940140504090766040300340d04010401004604020003400240003003aa20b9603030319524648116540c058803410392045010340341c40003c0448000011401e01800d6070f856061403010708030340c07001aa000c903400c900710a02e011032800010341c658102200040c00c034816010354a4603900c0c2d03001034085490032106074a00c1c2c0c0206051100f07007501005d1800c003441c0001c2c000200d002c05a1641c5608402e6078100722482da01000060043c1000501c2404510225200034485071408601003034560050b44801020301002244507031180190f0152040a000417 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 544368354 1250 544367104 544367107
    0x110705090108030a03242c0a0605030c090112031101091a06031006050906040b01021005090d020f060c0f0d09140c0a05090606090d020d0f03090501030c1701061211 72
    0x45080868076944461420801700c1c0c030340505a50903000c07a6101c1e28841e03541801d4640d06038500441c1000318903009400b0685144017283e40031074103101c11040c034010011048002407060811060620b41075580c3d800074840d55840700100492450001094142c0b6450700e08070350b21005e08103116014000a0310024074bc400c464104100b980316401c0b0040c49414218101d4450701e0800d0000001c495003400351a81000000c00003c0b2181400c0d003080c401c1ca40180304440007404046282d5089038829035081c852a006010302c0c005503a41082709601e2505100094006410b01d00c50152180c481c03143c5012249601191204001e041c5a0244c0a06a00700b0f41c07421601c64241c90716502c924980d621a4441c882d03900c0041414141505201d12070540900f03003618000b40a420019112074910381280d002800f0000c00d00018000305401004030700c40d40700c4030402070401c00054142c841d001c2a00007041154190820f040b0802c00380ca03411101c4508200c07001241c420182000303801c0d880c8104215a00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 544369604 1250 544368354 544368359
    0x2402070e0406050f0105011805090c1c09030e01050c0304120c0801090309050103061401090302040b120a03022121090f03040f0302030706020a05030a050c0307150b180105010c031107050901 83
    0x42c0d03412941c4219030003030b606803141ea211001501c0d4018402c2c8280d07944101c103441481142801a2071a070000b4088400310306002e0f0364102510142c1c0070a00e140d50b041d84031100c0d81c04041d00b001b400620603501742403a500705841520302907034a0196101c0c83c0c9658610662120610810007042005428400000d0200301210f0a01810b008010310805000a10302a80003c056030901a00303030442c0340581d0b0340254203145800700030160143e00321150340305000d0f203480c50212404010b030807200d51103034000d008070032511407200c0c0c0f85040f5041024921141006040c010300c100c807241e1001e40002c03500412403900c0c2c000701507241850b41358a64074113100014021030403030448911442100e100700e046800b002c0c2c07a284126100d4007090300007800c0d80e00500005501c180114041d1601d442500122810042642c0b203010040c08505600038119540e5514150320f820108020a40c48100c4420b4119651400c00024580d44180d80041c08100d1641040c0040c00d00c10b118030307402031000030b1030b070300e200d58 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 544370854 1250 544369604 544369613
    0x60d0c0203030601140c1002030a02042d0b07150e0a02040e0a0c23060c0f0d030f0b030f07120606090504052a0901060f050705060408040f0b042402070e04 68
    0x82c410f0741e086011580300c40f009010140341c0030031600d12480c1140581001c90301884420041d41000d003950015503028480412a41d200b060b01104107844004074010400c200c40c820303404040030390800e0a0410003044480045074400f030209108020b200400960389800c0c0d4202405c0c46600500207601504100420003601e40000d851151302c0e00414a5521680d610300e100e003007035a00c0c507001c5241c1b076481c0c2c100fa407250f107040c0f00a40010907040341a126800902100daa040034000142c030004a81d0300d49821080030394610603250505429001040b280c4800000700d69a0741c0507200e032a0f07000e1200765041003040203a801201c000e0a0b280700500440c20701386880c5494442110740c555204181801c01a1055100518140340010260040c411130b400e0071400c980103403030054240300f41f003020800040010410082d0b980301c1d034080c880b110740310b50620140f0300060b6600d6110035900c0b10f0078001803100042c0201c40420320320201d4225250380c0ca5140003a403c10300c2d9907000e800c800c0032075000c000600 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 544372104 1250 544370854 544370857
    0x50d060e06040b01050702030a1707140607030506121513050303090717060103120503062709010f0c0e040f0605030d02030d06090e0c1201110a0e030c040b0d060902060d0c0203 77
    0x40408031410300c0300002c42e0f001190303103004103a4003940c954041c01c28880400d50381541c4a002103000b1410f02d00e061819103400410013050410307115a03a1148041000040d407600c80c454003c4000c80307140300403401c6200c01e0381c2d441c0f03403052042602440c00804203010480700c001b45081160300005413516071400d01c0340c041d1141c0c1c29201d0180e11440c00041e001d20200040b84075810fa0381c0c41b88490420038050300045680790001070440760014800000c50106611003031040a401e0080011130b600392429490560a544070f0074000d1000c1401d02c0c07a03042107250000303084038410b40e055400041c1400078115101c060203456000c00e8242c080c2114204d00301d1307408801030140800e0380105102c22552902030004407542128490300641001c155004986420021054401411800405e009441c48000b441c644d00060300e510103d0520208081c03030341424452500240c108603800c000040c20003010405081c01e01200500d8290340c1c840040071075654006607010300c660031a023081026a104000b80d030340d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 544373354 1250 544372104 544372111
    0xb030f100f090614090906040609110d1412030717090a0b040b041e0c0510021606120509030903070501141c05092e2c06100602071410050d060e 63
    0x4104100c0d44d4007086040c4440c60300d000e00c00200c002c02c103a5907140c503403c1c000c00500c0411103000c1d9451002e050103554032802d11082d14002e061503072403108440829807400e10b0501781d1004003401442007000c85a008403412407032000c0d00d560f00100d90f641c9850704c1d084c14519903000380510004400d0100307000c02051600c3c0716501c19aa100c0e4400c0040300e12125009a4004c028110881070f003041c4a28100400c0f00d812403106070040350070b40252901180314180864200200145844a2840c1054020302400b600180b10001940ca40000000829103078016030050606020101c8503850322039030000c0c1201c110018403401001c0e0b500300310b040030014207020384503490345100d0f080d0a843e66640d250100c60480f036450020389803600350b8150341f00c050040c0442c4048400f590b80184e0790303200040a028201490b90001401070b502d0484c2c40203802400640080d01150300500e400c0c0484c0340c045900701d03404030003120030030003061151004a45910546840790441030074520001402500003810030b02 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 544374604 1250 544373354 544373369
    0x1031101110a20010c02120d120b0f06070c0b03010e0103060b0402030f0a0513060609240b070201031d010f0e0c030c090a0906090b0f07180b030f100f0906 68
    0x31080c141c0301c00c0c1980e0312040350019040b40841c40480b4003020760f19150a40320351060504100e010240e40014001c803c600003141c0310740c2c002c4020003115550050700c00a8280301a402000007100309400b01c0c1e200254030000c0c030b005000000781c45041c0b000100c0340b40001e04600c446142d0381d60b195500301c2e00010080c4000c60320307142031414101c22883c250099902c6081d10480144440d62401c90803009410701138280d000c5005034850401c04550310303002d400041d003020074002ca8031080b440b00389244058018500b190400c811070f002d00c00c4803614800c449410723409103804a503658044a8289260b10010740c1d0007580e600c0e00703c160303201044580107143c001c8001c90681d2241480c420602d41c42c1c100c21811280c1c001503407000600f010010358400d868880c02018000307000300c403d03522100b104d0000d540e4034800c5c10441c02004100e42d4040030b041c100c02c2109449181182c41d11092062031b000241c0038141c480722410001e0390b92004911150010300442c0d00c0e034074115903134190ba0f60052020707004100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 544375854 1250 544374604 544374617
    0x2070f120c0c121718010c0c0510021b0315011202060d06030b040203010c051801030f0e01020a050301030c050a0302060a03091b2706120206070f150c080915060f011701031101 77
    0x4101403d2810717541e09189841c050803d040d4010011a0030200400c01150300c400c0948021030301d0b46800c4146101d242d00f42c0c0041c804071070411180c554207040041030608c6503100c0342d060b595607410084c40c0c41c11250f1a40f00140405801d10001e611409006e594668a5203404000800d0001c0019250b0140303009030001c1181c1c070f9520101b1101807168280c4c0d500b4003440e4800c0b6920315442540203074141040c000f00013401401c00d0390301e5804d923440804402d0000f0000300050051100da100740d80010902210b250301e07210300c1c550205981c0d0023105800d10134156941d5510302803014614030740c101c2030341079a584444c0329161510402c203445200014221041d504c00400400c402610540d015a0005010391810800d180e00b000b80a41c0104c1040390b89002000218000450041510710b884040c3c2034080341e420414a8000e000900c002c01c5210340b0341c01740042c90000c014410b10f0541040c0181d800201d03003140e00d0016111803016001c805140ca8480300000300303103d00004210341c0401c0c2680d549 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 544377104 1250 544375854 544375883
    0xc050a0e09010807060f121a1503130305030c07020a090c030c020a050a0b0c0d0f0605040e0a210e09090309030c030607020723041404110402070f120c0c12 68
    0x1801041c00d00a00c40d595120007810b00c14907010317145d0039402d41c081c2e1070000c49503010300c0300600544061030007490b0343c444181000740181c601098268540d44042034501c1c1103140c04060f1038a0030144601c054140030300000491807541d0407600b2950f03942e4010f0410000380e0307070711405103000700829440c080c000f0b441c04070f40207074907440400d02c46000c41c0c00000401c1d44031426111682581303000780c0394036400b040820080500700d04502410000e040b203043d0006a080c600001e22065034822404298142c0112140800082101500f103200c42d519400581c0c0b44c040708041034451498040825070f12141140400c002c042c4000001c240c1450f0540555000c08405400d02da55540151290009600001000e0003000d400701e034108502000c03141c002c5568050032000c20110349441440c145003a0600d41048288000100001031500095804510b40b411585035140900009000140b8990362404000c0300144941c200c00800358100790856505da03178441c1b55a030b407440c610300d01700c903488040c0c03051 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 544378354 1250 544377104 544377109
    0x60a0306090b07030e030c0703080c190312110306010203220504090803040606060807080c1e19030b0102281524060309031e090305030d0c0e0d03050418020705010c050a0e 75
    0x355a03505001307100034190230b03003180e80782c80807038029480d80c80c66840352040441d01d000400581c00c40c1075019031100315120396800ca440c01a038428490041c88030004000380021a640002202c0000594071381c041c1c08000c0418001e091810182d010a07071041c28820840300340001600103600541c46030b041000030340c5d81d801c0c0961348540202d4842010402c6030000034060490300b0010f020032020b041c8914600d0500030020084e81c1c02c281d00d40d2100c10000714035a940c69800d8803c802d0521800d0005044195042110400a03841c3e0a0360700c00c01d540c40e4084004001c9202140d94404070817100a015000305a14181e00302d040300141d0f2584103a1590000940c00d01900ca00008250150703520415440c80d8807950301802001d02c2c20104011042c10000701041c0284040c010f140411744c008200d1b00d012050041001c442426094800e1124950040000740c1040480d0120b0706191600c0200c030307009104500003801005009821075013000070a500d221f5110005110054050700d6624a40c0300900a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 544379604 1250 544378354 544378357
    0x91b0d080304031107150e032b052107050703020d0e06030105040209061e19020f060411010c05070e010f060c020d0201030209060706060311030d0c0b0f060a0306090b07030e03 77
    0x405403481500304041004248240000d4039a030740c00c0c03000c40748800c0d40c0d42c02100b0b03c0c0c1c1c0c043c0103610024002c0848052145030074004900c130b02100d13031880301c1501d5240000030a021201e4441d8030600c0f0002a20b042140a1032842e04186a4000e0f1003421501e05200c0180c100d03800b8440880050107052444801d2034040e03800303100c071000081d10719400d6a090005120083d407045050303a030b110200b4070880c4a5030000c842486919050594a940c075112000525013403d0104022002550003880c203e00f60300398000f500300d5020380c0080b0403003240d40590005989007040300c4000746c501c3c06a10404281c6c00010b11246040300e403004882c200f56907940d201240d41d100916402503201c991051000090741c480d40103050300c000003c26552a0506980d0740701e048509580c0225401c1c0004041d01482e403800b40900001911681030000c10700c0c9850350352400c3d40b880180307400b6036200c001010500341d80350101c0d0000079640c03184040050414900b04009003100442d40713034000a06240c50401d07503200120 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 544380854 1250 544379604 544379629
    0x30906051f0b04060503011206091b030b100e0406050a1506050403120801180b210705090a091e051009080d11090a05090604020c06040b01080f0303070c030e1503091b 73
    0x3030303649046d80d0234404000c00305c5000c081c060b100e40d601c030030990020402010041100307812542d0300c1003c0fa890762800c4001e0140c01425010b080c480524108008c02c003c1780c07030030760040c1d2200c00001c0340d0b601d620090307004210110394640c2140800501256603074002e0300800a0342e0052407003120044000c8411140d2032002d019509406211000301c508480140c1c01c004c5000034001c3c0b110071015001c641c0e0054071400404074242d254001030040110341409031231250040d410302801d0100064540b00d08a40310941d08140301c40343d41e1416070005000c000d1040401050320310400f1b212440031070800d44525000f0b183c0818080740b030a07600140d0700301c1c88000c40e51004000717081c4942c064600b5041107240a00201001e0300681c08000203091014240705480c1308a10404a603411941400c90180c540800c40d008003005501c00c1040c0401e0720b070032a00b04c1c68500e51615016209040000c0450812a40c0380f4201074851004802c2c004200f00104501d88c030462002051000c0b1018002081001c0003c003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 544382104 1250 544380854 544380857
    0xb0a0504020a06050a11030c011d01020405091305072c150a09021305130203100e04020f040203070e0a14190e0a0902122d01140610030906051f0b0406 66
    0x100c00c20020b213030041c0041d0081c03050034108140c8010203041d0241c1564080880c0f00d440d6552190721905410b040700540d031702010007a00850400b4101004031300c440c0030145c03a000440100041030700401904000002c094600462510f001e9000307070400c003036200c042000d00032050000f44002440d10701d01c030b86006e20640d03008209490352858044000c3c001d508c41c410300c0407402c000c80004280c94441d410480f01d40e5408035001a030f60300c1c1c24403100c0a8483c0503049106060100340501016035182c0c40d464441d180121801a501d40300c0000c01c0c0e881c4d04401b0403423608030800c1c0c0b100250b80c440118100d008441c00707480c0d2504040142c0d101d075085003224000d00301d0300510b9102090400050780e103c0b8a4292001e0011502030b07540000680c070b060070400c580f03041c4075410840446034400b501c0182026480d840c0c000d12001d0300b00d0f05250017601b0018030301c501510121203075916a602c00e4208202190300000708004074180f034020283d044010784150a0070714050b031000540c040341c10702100e084070800e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 544383354 1250 544382104 544382119
    0x102150601110a0203030c070801060e04032307061803020d050708190207120b09010c030c0e09100f0902031617071412010b07050f070503030904090204180305070b0a050402 76
    0x440005580700d10031030b1102410b52064021100040c0c6080004046c580c0a041c01002998070f081c0d040c0342541c0302500100754102c1c01006100000303421103503207105092401401c00e00500480d00300b080d40e0051103400703000c0d182046c01041b0a45500141c0c15162402a42a00c00210701c031041600d15109105004085400411076001f05401404840c00c0380189441590721041d580c040ca40400f059007402034071640003c0e0103011950341c0074030451890849a0400b0b003d107043c4558050308800c0b19003411800355070140700040010200c08108030107891025819504903495028010094200701c60400600008a559000700d0f401442e9030700d01040c20540d8403540f075031581ca08031820001903c0b064003d2005212035050040c4100140340608a00103909896801509080703180241c0303400c400c1d005400c00902400251400300482e2007100f07041c1d0300854074605074404180140000400b00c003400302414601820598000c00a2251a0041510030000c0d2201904403080700c606581c000c0d0310151 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 544384604 1250 544383354 544383361
    0x21010308071106030c1b030c0f0f0d02240a1b0c0303050f040804150c0507060c050c040e121813050103031d01051e090a030b0106090803040503031605030c0102070602030105040b010215 81
    0x80340c50b00b44800306c810b9815641045465500149000c1c40c50188410582112102d0f46010804108446043c41b451004040284c1100c40048881c00b250324060801480340300007074407608581d00004140d4139100f5a10003044181c20004140b05541001200000e0600d0b0104440d10451043c45019640040c8000e1030b003440e2001e080801c441d62803008040c03089244c080c0001c01c0c3c0c203000c071000800a0b41c0f18449601c0d02c41c07410038180542c00306000e100342d103461040f03000e4201c0086c6001c8010700c0301e07811958841035050b4001009425031001980080040c00680c0c101c0410b8001398100e0f4443d0701e5001c1e49400c1c00c0e0000300c03084011070109000800c1030203800590700c0d05411007415407440c0070440d0700d000c4d400700110308107001642054507451207040c01045600d901008000040a410014500f82070526002a491384030b0a40c14441c8083c0e04c55000301404400e00440b00b914907120021036543e02e603480c0c8000a03410900c02c45104a14141a060080d40041459065451250150905a40d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 544385854 1250 544384604 544384627
    0x1b021c08130f06090c0b0a02070e100e04111c11190801090f050618120904060f1e0906060f0815030703050c041b0203070821010308071106030c 63
    0x110003440180540101858440032864001c0071010881c00b0b181d001c142e138602810b12448248440d407005004020800c000b014a81d4085040c1040d1007040510346000d80707814030032040b01035071500841c1c0c580c1516004c0c0020804107400c5070b6102501500c1c0b4141401a290700c0305210307442d41c40e01408072141c10200e0074a40c41e080582100424001c0343c17100c480d9031030341103880c01c40e81c09400448203507816407044000e10104219007684155907071140d9a0b0032460003072140e2151a10800302c0c03e03004001c213030b4854560f030b80e1704820054581d210041c12126a00c104d000c006000740758050308039148074080400c150800d4055a0107480c01e540710328110801440049820a5000b03040c0d203c4c1c10b005038950002d43c0d9083c040180114024001012075a1414003000215032070700220150b010002900d40d2525500441980d101c1a0803c00a07a02d6805100b02c0c900b81c1501a03218844844c160300001c0100850900904140703400340c0e0170003800705945424800c2d244400c0d5620517441c4018804140c0d8030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 544387104 1250 544385854 544385867
    0x110307140901140f2101050a050d15091a0a0207030801060e030106051306170a0b0705070c0905010e0a0e011104090e0319111014060f01031e1b021c 65
    0xa01d8189082c02900c000b00007072080a80100c200c0564440c0b0000e00e065010070400c075401001d040d031028103041c40d454100060301e82a490b02c100744c00f50b201c0e054000144102c00800c071458500103002405102010310b8100c6031810b500051300d180c80c5410021032203884141c402c2e61066a41519071940d664201503054919401030080d80d58590740f1140040b419031036042501c483c3e00514040410010b08260341070b002114002c421140591040c222540843d103d002c00340d403c00807500340380360340720170340e041c10b41d030001084d00641040d509000001821514040140340f2804100d142000300b80d41906100e8207840a422401403100d00a03c4180060780c141d41c40900c42c0c4c2c248108691826440900c1c20300202d44034104000450314903178049175840400c2c0000e003048a15428200700c09252200d400c41c0d0880040c0047d405001c0003003405029034002e0b84980c494204440d0100710007038540304070401030500040c1494141003410040880d06000007281049501c0000c40031007a031204400c00c48c2d44 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 544388354 1250 544387104 544387117
    0x170702100b030c040f061701020f0a14070b010b031902071101111f0504062a0c140a0f260f03070e090910060b0906090d0203100c1211030714 62
    0x150003900740070f440da55100d20604e110b0001406001c01c4d401e20300840d540803403089480010080e401081200700d03509020040b980075032980e003054540e036082000704400034010303010010301e01c0903401c0010507031150b210040c41c0719000e0b402c040035081c0001c0b88854141d0256050040c0170030501011162590f0050903422851100c040446890300c07840200710115040030603c401c22a90754205000c103118683c0a01c28146a01400c000b2003151058600727400e08880044c1c000412900c0204134081006840c40084000b42d100c080ba000c0c95494200b0342000304507580204c074011040206041d000c0f5585407100c542d640340404490902c0d20600d0192150344c401441c038803c2100c0e40051499541d5011001d43c001c111420052500c403030410580000c42d0135580141907070329030038048034005648401c01c03508106800c0e1601c80b004a01840460f1504185681c4403d00c94200510f01c420309078004c0e0400421940072800f40001102122104018841642c00c50b0000d44003020020104180314000c004 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 544389604 1250 544388354 544388359
    0x140601030b040e07120c05010f051803070b04031a060a150503060d1403041505030606031503010e0334020906090709080a060204170f19060b06040b0307170702100b 72
    0x800c50300b070700c0d0704038100500340c0c005c103884048030800301d0240415541d200000c0c00c000c1c01d0021040680c9540500213000b8101d030456000c0192006912540300ad0107060018007141c884103440329102c0c40c6c00114842c0004404040c1c0380c0c0700c400180c43e40707400d110441c2251003074000e000940c02c9110b41214990310041805801480d4051180001131324a41250982940d04025545407400d20603200b818140c03411216040184c140b05010031561004104d9030015140021240c42d8454080882e0240c00d110307801e031b21640004181030b41000b1142c050080000e2048030902c41c1084214802200c00d544410017079084503082001400d541031030140c05400408038101002e40550741c1d0740707540c94042101c034120354090300840d04020320260b800101c3c0086644c43e0207440d1210001e81281d640358007103003100324004400c05d008024803005030b10503a81c41c200605402c0d5101d0301d612400c2e0065105849100000c0c440480c000300300d0252070b03440c80c0250002d6001e401517000200c1540040c00420307040c9a07 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 544390854 1250 544389604 544389611
    0x20105090a080301151418090c070201090e09100c0306060f09120308130602040b0a0813020d02060d0605040911030c10120c0e030a121e05070620120402030709140601030b04 76
    0xc46d84144c0501a00001811f60781e21000060b11034103000d14281c01400404240c241400ba4000613a048a4108140c0d0004070480740385544a07103180385040c8070b0304101e42500c2e1070a2920400158181c019030291412500e464000c2c1198120031a8290481d108000c8010508005140024030440a82c1d410401d00b02c2400016641a2140c401702c1e4481e41c004941050005440d8650310b8120440a40c80500f100000604291980100b540c40c1c002d1a8024802c0c5800201c500c1c40389801e90180c030144c080644100051000741c41c1105081060800e81d510034072900c01807000c5450424071180c0b4407055540c0f80c12000c4100d090000141050080c0724041c04550040300c035040d2010090381907004d004828180d4015903440c2d000e03003036900f00240c9a131140c08195440c0c0c2000d4019088846d070651044c0300194015800c0039008071a0303010f40b180744002c01c0010b00145000307580300a4500580c000ca098801c6180c0d41c40362501143c1021b003c40e190b101100c1d00180196000382d0003140004400340c80403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 544392104 1250 544390854 544390877
    0x3030a02060c2a060a060b07111003061e0e090613081305101d03190308090109080f070317010f090b0f21071d011505120115020105090a08030115 64
    0x503005502850719000a130300003004c006054049001e2040200300c547e20451400c0e0b95501e50101e4280d18402140c000e1044d0700c1141c4201d84242d0000b8000c0888000d003400d00080100c0000001c00b040c4503d0b0100c0440001190705040c0100c1c6040c0140c0450707580d099040640e907506c1100d0f800040c440c180c01c00c2c6000000607503440da8080419840446d558032080c0000e000610502d002e8001c02c0c4900950220121550740e41003001c0c116590f94050500528a64503010a1800360086d080024680d0303401113240c004405414018200d017500c41e44424603030440d2140c0070f2940041c24400c01e0381903000b200301000310303204550005040c210094900c070801d807044804241201036803050307420452071071901d8507070000c0140034a0000e40110704030005581280500c410710102c06000d42e4200b400f8002c11030850324010422142d00902d83c0000340302940e9241c42140b6002225150781c0095400c2c0000203100720000b20312445640d038030295882c01c41e424549c01075409145810b4000c103000206108 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 544393354 1250 544392104 544392157
    0xf080915070905030f0106030b01061101200705060106110307020405090c09100911120a1119020303010501080f09120a030608030d091112060c09152703030a02060c 72
    0x341d1103041640ca40402a514040500d40390008200800b089a49841f40500001e41034809160460301c0500d00204141c801ca20300c1d42c0181a50460a03012050074240010a2201e5034064450785015100755604e80c1e84c1c400f02503500541403100158103400402c0a2001458240d00080d0400c11050480f0168640140030454001058900d4842c40e0131080082040d140a030040c034000d561041045803c00070304a820b0b10700703250040c0c008900b09172030707440a1501024950958221494024076041034000c24180a501c1e90710a01903039000607060000624042e003054019801014148010a0007440400c640001c80d000441d0180070582c841c040040c03000810000361910589a00300000c0302c1d51030f480c2204da103410b07402e94a4001c81d00802085e2900ca0041000c030307170204119071340548e240c0410001400c080101c0004481d16034000c20300990b8020741c0c0c0041c0711079616109422200d500700300c080507924002d01d0f072260010b038014070004140850071400b07091074000100301102c3d041c202c01c98 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 544394604 1250 544393354 544393393
    0x705070209040b040b0c250503070206030a020301050f0f0d030f0318060501150c0201120203040317090a0c09050c07060914071502010605241c0c030e1203070f0809 72
    0x1000e8400304040c00a0005021600d04100d42001c01c0d2000540b8090920b01e8040c07d0301d220507075010b45500c0c4030740c1c6081808024022698900e9006107041d90341d00d0b1085e0b202c40250000e000c0d0038020b09408015150500f0500c00141d041c0b40c0040205004003d00d0382c08a0748015031610b118105629100080e1111215076052101c051241c440031807250704107075078240e145030944a02020014243e08601c003503604065220021400d0180250b0359130b40d0350030305031402c0102110034501000000c00b000307004500030483d162807034440c100c042c04066685901c0030a5400031360322410004801c001c1301d800a90242c4c081f40800d80706030f0141080d44d00c8407840604100c1142c0c00075400782545d1103c201d60310750a109001c080d00d02240e504106d401c0e107030b090586120441c8000043c2410000e1082179142503a00380740b0041c0c54590003881618180c980041c00b4040154440b4181e10800190741101101102a0391003015555241d010075000701400300c0d132085019205010a01800c490b241d00e0b8141d840 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 544395854 1250 544394604 544394611
    0x71106031f080a15060f06050307050c06040c17121b010b060f0306120706121e111e04030b06040c0c05030a08040c1e0b0a05040f081e03031308030705070209 69
    0x1000303400f03010b825081c281c154541c00003114400518110007448801c0c1d11101040c1551b2844c80c00c1070b100e98900009564a12505640c010907110b400e00f000f00b000340542d002c40a42c0c806213141c400c0103071107030364660b41c079910401280040e50080c0101e172050600d8040075144020114000302d881a4190049074095020000883e080100003081098134180517005580045819004043d01882c0900c01801030420628080c0c2a0351150f40c406151040b00c2401c0c1414646040e080080001094542085511008520080c085000c0144405006041c1540e04490700002c80c80a070781d9812082000402421440c5003d100c4d410190728089001000030f08003505803030715503556a007054204015584000d03406144051007540740042d0f440380c034070300b42801c40c1c540000d0682c4849007510300b80e035240295000348982c0c20081c000000d500c00001810148500c4d1a40c1100c02c142d84515000d841c1d12049844070592001d000042c400114000021640194645440303410911035900051074100c094 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 544397104 1250 544395854 544395869
    0x20f040302090a0f0e0304080a062a12050a110d05090316120e0f030c0405090304050411031909080a0e0409020a0b0309010c0f020703030e0d0b070c1403071106031f 72
    0x4199a464000d264170640c83e45800e000000c500b050310301031800d5500c9440080c000e100355210035100d044245600a403528400721141b0045a1044801d80140403400c00b0f1b034180c90040c180320114249100760301c100c4441c1101d2080c03841c900030407501c60710003030440034240030142d100410843d50040d8400f40910600d80c400c0c0a6041000342080000307151050b0b040107a441841c0302d0031140b1483e41d002800d906482030a40300403450790342e180d0000d42180030f180c1c80940c2190504e004a00301500600095108160b03640142e640d951004c0c0c40201201e03000b2400034080d031000c01c1035484aa014030f5410383c201e0070050010075000c000b6030204000101c4ca512010b001d95000c410320480746003c0c02840d41100c074521700006172180b0a00300035030303844092001500b4001d40036082d0010751240b41e5511101d907004441c2c2e900a04012200410005800c04103541c08003d142010041c1500482160482da030800c80c1010300d40700f1102000001c0c0d0002c0c00000e40b040e0481c54145904210318540b40040145 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 544398354 1250 544397104 544397111
    0xd0303150b0c0714090c180f191a030f011a040f031128051212070c060801170606040e010e0111090117010f0902090607060e0c0109090c020d03020f040302090a 70
    0x10704c0e030307400071600c1580900d920940810041110309502c80040d90009240303010800804e044110210340041c80301c134582508900071103280544521500fa0000807240c03031000301c0000c02070080c403500c0540070680d84d1800e46100b4800411117181040e103021095403428015904e41a5118245440546190f2085a41580e00c00082d144c1e880c0000034201044142d4080768000c05201c41c1c04000709249005035842001c01d51000c00380c1000410001d120040c240e920301e940c548941c109407485030310340c0c400c51002030f03900c0c000402c07080d134103100c481d140c061010300401da2034035032004000c060b1a8400da003c003559a1401e28048900003409102e07048005000c8180d070350700850303000515400d2400c228040c403002000041000940c050030303201c02c580324200016118000000002d59074411110081d140c1400c06000d20080700f40456290724841d400d0300d0340c3d0300d1950350f00309460688405503804000368000c207803185940d41c003a400910304034007020035107490300751a92f00144103040261652071280741c1c5d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 544399604 1250 544398354 544398359
    0x3070c0203120d05151c060507180308090a06050a2a0209180d0c03020c100302120412030c092304020426010c08101a070b1e0f060d0303150b0c07 64
    0x340070401e81c1701d20030156854242151109583e03035020307081840c0280f2103540d074000241420311440c82d26081b154051402201e96969050520081c2c11040e50350f8400d8265801c00154103006008543c1c407995152160740916160040d0030b0700d8602d00e00702c035007149045441c8030380042c0d940004680c400d031181d07041c1076500311b4220050381c40c015041411038203109541d00e150002c20f4002840000d415800c0b135103081b00c0803801c3c104401030b0003240100c140030311001c0305001c01c10030f01369115003541e001598100321110f82c0c00000c49a502281c8103054170111000c02050016000c00110b09480c10003820261030207035200d410481260074039004800303844103580c01582001c2c080c09810a000300e189015102814008411104586c6d54419001031503c22001c04c0c0042420100359901145c20100c0311013a85400c2081c0398040c40120070461603500d103000003801115800361a03c0c00744802078080b210740b140a680540c020a0f04440800c0c41c40458000000d0540244005081084040c5d0140440c01e2 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 544400854 1250 544399604 544399621
    0x1f050d0501050102072907020319030f030225050a0b090705090109060e0708071701120b130c060c0201200c1e0102031c090f0b06131103070c0203120d05 67
    0x51068114504541040d85c007000420100c0d031000b0600c055100c0255104a0000300d40c1d0304074400e0300d9000390140a401420b44030340b07410a000c405964000d85414000f80c4050320210200d20407603c804603e02c85052280030a100384107080b6020500c10400c072034850300107840d00b003036104048a03010099884082d09200d6418880d91b1341c0e0043c60b80410502001d410304133030314200b0304000c044504002e5400c0001c0d00e510300c6440030340c40c06140e02411103001d5860313500c085c4000c0765070743c02a00c0710100500440c400c1018180d00b03402c1560000c1e40c40b081031f420140101c4201d00e00d000c06034104542d010900107145581c6a800c0356a100f59002892000440801e0003101e444020071100c81e4040543e030844581d0300401140c500f2900034100d400071a8459007150003c081d140c0c400380c4031100310302d909800c011500716182e000e410708030703264480c803103051110800791403841d045000c5850090001c544020b0182090101d0a0310090031b9a40c820030343d00c0e125400d50800014294a6a2130764140010076 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 544402104 1250 544400854 544400861
    0x1401021921020a11010309021302180a140102060a0510030b0f0f06010c2006070501050a0b0102011a150304080405060a0c0201091517041112010e0705030c1305061f050d 74
    0x80d0042d0000c1c0c1203140380c3d615207041135080300c2015070600d134540c651403085543d011100310800c02600740c11502d4010000242c0c0410711a00300090165000440c045000075061420b00803a043c141d00a066503550712440384058100039040003d04601103d0200024403405036041c400d5803e1700004000c4d11f012400c1129070740c4003811103418000110b00f000b02017112294690800e00b424418101c0903003106000c500140314011002c2c0155181c401840314817101904000c400e000264003d01c4042e00d0920704108208100520551140c448103110440c01c0840002d10ba01c107006001d00c50520b5600ca01290166101c07110800c0000d06c4200504115078005101c40050031040d80700c040321114002c000750805145a0b0f4141110b07903564002020000b01030080a2070f200054241104040142040790284c8000c4c0441d00190140c80004640ca003000116040200f100400c21903445415500b040c0003864040e12040e08902c0000983c80b00107441400542003010f03540d00e55a480001004c0203049 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 544403354 1250 544402104 544402163
    0xe1006030b091209150304110d060b0901050a0602031608040b030f04030908060415182001121a0d060b0a0b12062d010e031c0809010b060414010219 65
    0x10640921140565440d40300129444089062001c2d45c0d03910f480c08c025203410118008075034048401c6121400300009508859620001507270448001e9891b142000505186805400700681c024007441e401c0d03590102c2204280f900035825185041d0711410302280710391086900b151180401002c0c8000c1583c4030a105004000d004094060340c185607a0302c08100843c0c008000020740c44001c89201c0031030340c1c492900c1d0301e6070184c0d08088814404044110b160701c42400680400d07042030043c0101480ca014242c104c0094441e001440c00e8072000708800b00744210015945d480d038900c044a19500c0300b0030103102401034038007910b44a02c0034005450342108010041030282e40e410781d003900d004410100c00e031541050008111400c9200e800100c451441c02520150f052050780c12428102c1460075a0024500d001d507210070035603aaa41860342079602c0c054400c0c3c1c1001d81000100421500d10b0b00615a43c101481500c100300d03920305203904107403a003002c04c0d1407080024480035402d0340e2001020b6903 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 544404604 1250 544403354 544403383
    0xd031115100f031a0601050d1415011d09250207170307050c060c0c0a0e040209090f030708031b0d0b101403010b0a0203070f030305150108010312030e1006030b09 71
    0x5500f419542e40300c40d07008080c080b90180050400201d246030b030149090700c901d031059030070803c00146a003056801c0c145042da210007201c481d1000040c040d52041c644101c943c2005100440f50041c41d0040c0190b011000f0b118101c1c028041021207221110107580c2540ca0500b03900400042d0b0400101001c0304090000da08040d50003001500009100801e5a801001d000c0303030702ca900c601c0c0c500ca0f0342d402e0403038040801c1e501c004501342c08078042c0d070007805003070103103009840c12002650341062147e581e103c001030803202a4800d00c140030018240200456202c5502400003100b0300030900350852703a40050140c00c80c2551140c000c11a50f0800c41035080010803d450300c0c41c1105141c0150750f00a20060045000c07501c1e0010b82001c0780741c020811185495031000c0048828151420020300500e401c4c0d41160220300900c83c1030405600c21450607068907002510b5400c291030b2011305074001d00c180050605540140c0000000050340f5105000045019442070340301c6280201d922400c0c0714501181e80f1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 544405854 1250 544404604 544404629
    0xf0a020f1501151107090e01050109200f03041e03020c2407030c0204060f061112120a2016060e0303070915120f0614010e0f0d03111510 60
    0x800310701d0f26551041801100e003040c58400342c10502c028200a001e4010021540c104599000c0e001c40551049048407103886040061401c603500001000190510808840b103080c0f0486203100c101000460300684224640c50400601121001001140c04015409a00040c42c0780605082c01c585400b00640c0080c504040391007811002805401903900203020005001c00407030441d116940124050120100511402944c0d0300b0000c16403064a0303144070302c0e80694401d40d48884400d6046c0c0b2840c02900d144440256111a001001001505601da01d01920401e03004011170180d40140641030400700c4042d0f6290a41c00c1500c00d03152940c9501c40e0a6004004000f0210341c44205141611001c080300c500701d0030321045c2128511244100780d58514900502104103003010f61101c000c440018480703103880383c411070054035110341c2204450740211111340c101c00035103008902d00e031a481c4a800c00c0d00054250084ca9032915040411079200041d00100340b121099400072410001d240100d00700 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 544407104 1250 544405854 544405859
    0x150504170d060803040b1902010515090402031911030c121917180112200307020709020304150e0706120c0e130606030f09051902060f0a020f1501 64
    0x100202110380300d4280d5020030204665801c80c00c02c1d04250024080c8404903900d8a8440440c66003a0b0f001e0000e00c84800040c0030f6800719680103001c1c4510600035101c0c00c80d4411741c84004e000c0103d1008004030707458061600d50807900c240b0341c03401d18135041c014840c0040003061a020705d450302c011f56400030300c510754540d1250024000040c0700b0307840080e40c0941040e00c115030325120143c4411500000b030000008124a0654288021650b0755010240d03201c200940d0f182c40004111248100300b188141c0c1303055101e803550b5451600442d008600d03441101c0301d032551512030380101e80042c3c40844628042000305240042d5a000ea5860750900c08050301155260081c05080c15800c107928440344c80d240d9419080d654010103080800a201900e6014001e60860303000c4000d040da03001c0c0c14042440c0492984040c4c41030b2040c131500560080003025003240d43c40246052070049001280d01410800035203940001003400b401488905030018607036050f200704050306000c04c42c98105024080c14004 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 544408354 1250 544407104 544407113
    0x5040f290310020906090d0305090901090203010b0304140309060f070c0e091c260703111303060213031406010801061509052205011401120b01020d050a0e180103150504 74
    0xa0b01c030380070381e00c2200582e1240d9403008902c440c004c8040a540c84055100c001c41415000303001802c80d076104032104c408581e01c400a00e0100e000c01c0c050200e603d402400040c0005400619442ca170b00c072500101d90500b040d48000410030b911641a0100680c1c011803902c0402c080c0e0240440a0a5030030015000781c03070202101a0786500044103903401030991000f1500450180d0208004e682d003500d141d461400742a11014080581030703400d81d00103445d10824400418a09041c1c071045640841070041c498038603200e05c0c01940242d112890a005c1d04040040040c100080400c42c0a00800c040c04041d0325107904107007100c040d80e200201d540d0140c4503040501c0d43c400411410b80d1000c450059901e601c0345550200e100c1109600c0f00340303d00c2e10001056450340c400b05a21110826030b52013403251000c6d00704c1c4060b0b031210141c4d18050b0784901a030112041c0180060180c0c5041458a4408061200c1c005120b0301d1900b4080800c0304000401403042c4030702401561060102000240320740e05007a0b64 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 544409604 1250 544408354 544408363
    0x7091d0c221509020304030e0d1104150b0c07030506090303011206050408071205040503070803120126032d090a0b0d0b0d2102072d05040f2903 63
    0x1e50070301403520360000700601e502441041c548400120495034a4901c090b0080d401510190042007400d03001c0040c9150824a8418103540407000b505807825140502014100c109003414002c0304850703010034500019400340c41010446001048150f24504020f410140301611050207038104000511a4080b01801002c0c2558059000a07050383d450a00d01024010004018118080d1001c1c064a1940c00006001990740880950b00c034140d0300c40b8055628800c1400e62288044084010826521030900701e203151215458092030a0328140003450035540806600101c0d24085034807150300300a84042003924109100030342d85040c152800055480800341b04a56650000040e40420388120317030060901c440c03016080d41700406162402c0f0b0340c00320048806110003251200c0c01c1c0316151000402c0412122408840e0f251030b02d1458003070a16907141284500445080b0b1000641d58440744540c41c030003403000b040003807502c0f031500e540d03a06c2c10700450074409a1081c412080035070707590115 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 544410854 1250 544409604 544409629
    0xb0408090111070f0323100609050c04030b04120c02131401090624021e030315060a0504121a0a05060a05100905060706060306060e01090c0323100807091d0c 69
    0x281d5612400054003100032009a03480280d00e030b40039000408071f071481c0541209007a51a9024240640d640310700c0b2401c81d5004074800030b4411000a0082008119681c520b880d400c800b0f450400c0780c007422900450034803a5204800c080c956911001c83c50780e040d80340e26060140a042100344042440c2000080003446401001005101030005c1070994600812510586c1c1e00c01d05c452254080307554000035180d070000c55041240c85c00b0844555542d1a14000311603e0001e00e0b1601e5003046e00b400e021424092111008861105c0307192410300c1004030340350300c3c0c500c0b03582044004103962920704140b0960340380d1075000c14014003030003800341941500100c1d80c40580701c095034000c0e12081203060003005841c4550014007030750300e8081c0110b4840c150810481c16100303200d0061001e440380b04012402c2756402802d811042c80004444502c0321107000845030420740c0290070300000c039258110181041c10f2070707128540031551030640000b030220140e00480300440f070070080d003507180c01100400d08000702103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 544412104 1250 544410854 544410863
    0x60406120f1a280b0a0f090e0d1e030b0d0609060b0f060307120219050309150f010b070203030d0e01060519180207021305090a110f18130b0408090111070f03 69
    0xc4555456440303032030740030f42d484500080c5498005c0303a45401400d100c08550044060050801400c08a1900002000c3da02c5210998172030850040c40780720780031201080303d607210403d901d82100c4c0c040c55581c01602e40c203040c080c2c400050303100a145400003c680e0220343c140c1c0210717014181d5905a81c0e54500b0b0b254000000d040c101b445c04050202503001b442106000300c902620b40201b440c1c100d600c00c0243d4416104241240c002c0c00102501116403082103c6c85529450700c0b0005001c0500d071440644072040c8080c0c22607040c454480d400c2c00c01d8442c89041074110340c0d50380c9002c0200d882c140c000311894810442c04122030340d0030705d1440d000c4114040c0d03000383c03040c0d00010b44100b10b403108209803000c1102450108036038101421001d44031200014180d54070090307091014007034039000e214405c03082c1d4000c1110390702c0c1c0041400da41540c0e100a01c243e81059039209540042075506010344d106030301c507000340c654414050002416103840d10012400c5a4002c070307400d10182205114510580303420 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 544413354 1250 544412104 544412161
    0x50a0513060213030c090203040b0c0408030f0d0b0603091f0207110409050c0907120c1707030c03060b13031b150c0623061002120909060406120f1a 65
    0x3c0102110041034582d000404200065500062001203a8003541c0503a118940102d015120110485084d0003203014050b0103070005c20000341400740c900b00401740a46982c50110300c200380c160008449403c102e0b8030640300d07000540300d003a2444202036603021842d4001030031814085951101c040704080140e0b0903004e240c0c3c807142d65040c41420050580c8203d00244140740f03525240c5801416805d900c680e80801c1410544089810360080d400c06010703803201000c0c000c00b99100082200903141880181d424036030ba40c0400308440c50407030002c0641c5038810010f000392a242d0300e40b0001c405c080511300c071488080c000061107000c40104499505c0c1c0c400e450180d1074034555003020b400600c0414600003241c444683d0300344a60042c469221700c60b201c102c3e0318000c0805092016a00c80200c0200d03036801000030440c014091420000d0380d50001800b40c00016460b0311001c00900c8122951000d4a2041f09040c0d40390801414601070850035000008800c0c01c0d00b0564100c0f542c8468200040d9400700a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 544414604 1250 544413354 544413367
    0x1101030b10121e24060f0c120c020a1d100302030304030f05120307030501080d171303110106030615080a020901030206160c0b0903160503120a120519050a05130602 72
    0x711446008104401c1c0c1800c20903601c2a004400c03058041e0b14041c1483c04c0032500002d80b050040e045000a20381030b469540b2150728a6aa0314016000001c4075405d1040c046512405621a2401c0300c0180c100e1601d884d11120075024151040c440040be10070b920f001000303060006807404000d803022203138001d03924404604145802e506110031601c158400010120802c141c999040d007200d41219000c030156000d404444008940000b009554480c81602c1640407a0204c0c407466100c04206029141c4049485d111180aa0944e442d41d401a5000b581341c00c0c0c15826850b40b00c1c807038001000500e00500c00c0040c035a010654141c0b0510020f0712480f00843e0040b40c2c8510200500121a07200308580c2d4896200d0200c0703446500560300482c000e1142120420a400350560711000f0784e140200140001c0035a0008800c0075440002c887c4200402d458807000d51120901030355004401008116462458068032403041701c10040011400b903051009002070110f2040b114840325070460303070250340c808 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 544415854 1250 544414604 544414631
    0x1a01030501230615031e0411040515031e07180c020c01090f060e04020c01020a020604030210020a0905240f0304050d05030f04020405090304120b160806091f050d1101030b1012 77
    0x140d0811b4501c1a40220008110400028aa80e5000180120707001c11140d240c2c48480700300203031107107800d6030580d200c0320350459500000b506084440d041c0c0f030200d84401c2d8450900d080d20540c13206590b8082911a049512100d80500640c080d15800f0318022450030f00e8401a096415458800c0400b80100401d14411944582c0c0480d80341901000003503540d8070302ca100080d50b613041120300b900140030f400440200416240202c5040a101d5514040c4003820103040104451001d1b20300c82c00e195907524216074444465002e02071490355450f80c5074907840c00341020760a03c1400c1c00e1800c20080100100050444241c0980360402c1c0c046e20300160580c2d0320744140b4030314481d0703421405108082d0342c1c00804104000064a01c18400766000c3c1ea06a000a0703410b48060b20165002c1d0707800040c0310002905803054190703004d5144d444001503c4402c1c4e88402040000300b1a04041c4d5009280d44542d064658240c095440040c4003922207411340e24820000920140e4040100307000702c0c0d101c143d00300045 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 544417104 1250 544415854 544415881
    0x702010f1b0204060303020f01050114030a110d020414040c05060a050d020a02011410090b0f0a03031409040c110d0207081002130315230f131a0103050123061503 71
    0xd542c054001c2100c50749908000e951450060360168082d030a0400110f044010b204e80054004005001880803c0c0340d5543c0c0302c02c03ea58090075940112a146c50a40076a503940644d45108402074580052824581810501120607401c02ca0064808001110a955015080791025580803030010703200e00c0800402c0b40580404c02080d08249210030902c070180d865010404100c61b220301013008071101007824058038541004000d40d10907031002c41003000c00c1c06051a42254030b50401c110b8580000c510000d8203c9003441c0c80040011002c1505603590707541008180b140481d00c0c00103001891034038600e40e5485020307a044c052225008161011004080640306011310b500c04400c02150304149020402810b42e0550400c1c0700b805422060503106100410780d003d02160044007403955220150004202c1050000300c44404880e407051111109a60440c2e010b544a1030021500e116182c030112a603c450041450001010200b4028141d1343c290550320b80030f089600700c541b259550a940e02e02c1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 544418354 1250 544417104 544417157
    0x7022b0b090c10030b041802090604020f1908060f0111070308130306060801021e0711060711031f0516090e0405160b0919050f0d02120f1c050702010f 66
    0x29400d8800c1c400e0454150b04506035001c0246d03402c11800200c0007154640102441020750032007403210100d000c500f45500200980c205c68800140380581c2691035001c03007000d50404400003004141844200e18205c007000c4500c00e030920300b0068509241c1d900a071200824070004005480000f101c4a20300700100c034840c01580c10010420a03076650b042d0f118081e601081c0c0c4000801c050031089103031103100307800b07841413143c1000c400c0110090310001c1c8003199001c1032080d503031210070b0840c008444c2d4042041c4050350000e1402402c03000c0d081c400503000e9400c05800b01110302c0c480070903192401d90101d010011215903e05601058a81e401c00c9418409104e0301816010001c1001260306d4603020001c01394403400b40c0301c2d600014002c40c0c50f110444000e000c0c03103621489803001e641d82440c04034100b00d0014002000c5003503402c11010034524183c40b68680003456040001c00d1500944040204101b01e0f07032905180d442d0940c44e0340001c3c00c24405042c408284400448115850b12406299400d03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 544419604 1250 544418354 544418359
    0x3b070c1b06090f0501140315030a080412060e030301120818040c050403120905010e010507031817070509010b070b0907080d091401031b1116030807022b0b090c 70
    0x3140c440307000034040300c0705010b500d010000c0e08800003030325441603038000003888000320b2140c10340d269025901450b07180c18041581c1845000c00307190106404c01e00400040c207107645031902070b030101d191260940c0d11868a031a03454000344010450810010b1641c10180c0e840798915a40301174110b0a100703109102c071070342508140b800184d4080c00740c0290051060300d02420b014240b00c60ba02d4400c0f54507802c8c2d801058001030007402c5500d041d50194010f8107200c0d1090400ca02102405000404114855413205050b1440e40c240d0f0380030100d0074800e01c4090321003a1460130183d0b040c0300d90720000f0310456000401041c1510001454000c0a00c00c6901a0070844141d644c10410403600400780c6c845401204247d218174141070015601130b02c02c112020040603540d4000c0078103184159038100c0d4420405846010301192704d0107102105c41801c0140d40305003031454031019503005004000100c00050b00f03620000364500103050419241082c0001c0d4003862415207a030711500781754180000d1981c1d035038 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 544420854 1250 544419604 544419653
    0x15060c010f2003060315041a090606011101060b03040201050c0708060a0c09050108070206180102040b03091605030304061b02010318030e030f0c0a15030b0a3b070c 72
    0xd890401c0b500302500402d00200100c0040098626201552005581c2c2d0f6504d507102c00b01d0000b20074004070500c0d0b0b005001d580765542d0448600c400704000300381294035070b005401c41e000f00481c1c0d42c1c010100c6a40302061078020000341d42440310040c00b610020380041d043c0710000c1401d0f801194100042c8000d84210401e03140d0509160f182980604081079500c0f001c41c1b078182000c03c4d40e52044131860301c41c811650080403140c0f1a8011044d80340e04504103e1030710f540801022490b5880c810045000e60304420041c407921101c002c0b81c640707010442c1c014510a800800040103c15440950807408100f06c0c0c1d048034000d2060b01c0141d0040c04003205407d402c800c007a1442e8181904820702c245034080c140e00307884424620445444e25100c0014011341d0050700040c007070040b8082c41101512442141c103000030008049800141e50800960100d411600941c135150100c224030110f5190500d02d11521521a0520710f0f058082d24500410340020400c40105101c1444804070300031101821402262 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 544422104 1250 544420854 544420871
    0xc06070228030201030f0209030a03030f061a280203041707030611130504110d230f04050c0105041203261e090a02030721080f1c0e0615060c01 63
    0x1c100e00601d480140d01007403900c03000102c1824140211000c00200402901490f112650150000c0c10452a0504519030f600804640c40c0001d04507803501500004541d038a403900404c0300c2c03607204442036a01c0e2013800101c1047c030b80c040d0008107840c2615401a42c0d032014502c8028094501080c1e40e101034103070303800c0c030400071180b0403642c000713013081304030901c05603411900d80060cc4140d41010044044014080148650b80f188035400054042d0409a2840352070356803c1505414603070985800c1032400300c410622003005005c008071042e82d802800d06500f000e1400012020329108541e0203030602804e0200800440540031402410710980d8414031698106901000d9a1151041d05040903612400104103404000030b102555140d005000708080c90400501e040507140c805007014000c1d000c240e40c500000e80030b102420000480d290041c2d12454401d51001408402200071000280303001c05505003000c0101d1015401540109401040e1a01c0000325056101e20000c1000035480d00154 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 544423354 1250 544422104 544422169
    0x50d050c28020d050706060513140f22060e01150501030e010b130903090b0f0a17040b011a0f3c0d0b0609060d05040203060a0603050c060702 62
    0x16008403500004040509030140c030240354004110050384015a102d0050303c00c07440e12900c010000c1e117106d803101040c51b50341c0d1320100f048801680c19a003081c6440e001144424241d0f64a000e90104c5402d07504c1a590400008080d4540403c0400c50b0b8030b41064440c443c180300c01c035041038240d080214020826891115500c4002c58002d01809002a040c5055445008014010048911030003004c445652214040c048010003080900301c0c10302084481c0001c0c032012945c0603041d81842c10310705a80d90892004000c0903000c0034030719885807011500034400418070070b004060540300c10445154040c7d00740e0307004440500500c61100c116800020f1582e41c603e00c3c58a6121401c4550301403040651217503020a0902d402d0080f408261010600040c510480160480e5002d0319000e8150313840d01c1c600300301044440e8890380426003181d0719407041c00214281000728070344c003890f01c1340c0401500e07046075911038858028502c081d100300c1c070100d009010356442d81031011800c00c2c108c0e50f080000c14000d01 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 544424460 1106 544423354 544423357
    0x6020c130b0118090f060911190311070c031406010b0a080604060902030108010b1002060630030a080901050901090309031b0302040c121d0c0d03050d050c 68
    0xa1082003c01941d0620007400c003c007004a030b444a80400c1c10306a8001e6405980400d2400051074184003103001542e0954590a03100703450b070564580224050404100b21050741c074400121481000b504c500c085007100d220796650011400300c0550140c845d07100340300b0704a0074101080b60100c0a4450344420380c1c0017200800014500e43c58610210890300240c004070b4a50790b64050212042c0f506003d002d0410401d031004204e68500b24001c112261054503600e100843d04a580f0f407008606161030038000c0102604903034491000c00310003041d5003801c1d2840309441d4602400309404560600600702020b41580751040304074030b5551411181e9070310b000c1d0f4803104a139450f404070060385c642c01000c2c000da080d03984810f40360f101d8001c200f003180c0a54a01540003d02420b40000a242c081440d20f1000b0b070403940c0c182c0040507030501790340340d124424904021030300d00000c00604210314030 = true := by decide +kernel

theorem cover : BRFrame.Cov 544244604 544424460 := by
  have h0 := BRFrame.cov_init 544244604
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544244604 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 544244604 ≤ n) (h2 : n < 544424460) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
