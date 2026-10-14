-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1744
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:31:14.946983+00:00
-- url     : https://prove2.me/submissions/8c146385-79c4-45c0-916a-efe5fededb97

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 313489208 ≤ n < 313669064 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 313490458 1250 313489208 313489247
    0x90c031113051233090a15020d1b02060403140a0c030e010c2307050d0b0106050325020606040b0d0b0f0919060605041103040b010b07080702041805070501 68
    0x304400e15080307083c540c014141c1c0c002c2d40c400607000600240c00220250200e1030321310ba44480380f20550341c0072000c1c03544400800060064485984d4030b51811181d0800c420801d00d401080c0c2c2e06443c181e540c004070354008800c1101000041140f4080d4564200f2241900032074000b040e4402840203440c2126028906070780c9103940b000d0240c0c3c040c2c5045946a070f640d0f040024415040d00017504070460b0345901001c802c08062400418600246848042c0c0c11960140c503041da0100000382d0101445819101d00b1b00700542c4903a6216154540060503980710fa86148400b0aa0519030303801091450048a003078030284585d039600b2040c00101c14410728021f00c68030a01c80090401c0c031080080c2a000140501a2442170940400744280c0d81c41121007687c4071940d84400304214030b0184500b420710024500490300b14601621030b0101c81c1414400d00300045000034441042100007400c494034194001c2c4100222300e10704a942d402015480c004607a644120080410950301441c6000451b0421000d03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 313491708 1250 313490458 313490497
    0x1171509070e0405090c0901050a0b1603020f0a06050f130209130312150905091507030b06160f060c03111b071a07060b1f0806010e0901090c0311 64
    0x34000d460400411900410141d6202e24020795124040c0398011030120380140400d40c0720300e08012261106a100c64072444c0c4003c401c110101e0081d0607500c40c2418040c0d9081c0010f4182000c1e0b09120310b40d40a00902d0041102000810081c1e920090150b0400d40c0e42900e43c0d501d1078900e900c0c455442c00e010350300c541178000207560002982910940340c0d2081c0303890480f0704141d9040030700f581c1411a401980380481c2e68203001041c0281b04203035210240400400c0103600c409502000c16002400d004109901c40b00c0c4611035407038500844580d80c605203c0407107000f05508189070088251081120320700d040005000c082c6200740038180506466507010b81c40c0c40700d200e0b0110044514080041e801d4020786c10001110503024900c0c46940d006000c0d4180e0740c90b20ba160038811541481c070150b00c10504060340320700002011048440c2c14545081205241e221400141d96400400840e036070701450050010541d24800d0304100d40c0d01c0816281400284a407500c1e1000a004403001040f4201074000e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 313492958 1250 313491708 313491751
    0x2010f020a140919061706060a08040b07050403080f04031b030b0c0c0703231e030a050304110409031812020913020d060e0a0c0e190f0b120109020117 66
    0x400038483c02d48000c0484480324401c0803016240031980e0302c16408140100c0b80e1240700c0340c0030504035502207400c03140c40303203000881d20700605019000384c40076140d0506900065407503802902140c0c013940d040500592036070185075101c02103900a020440d14815041045605a0313011020300301a00e5000b0290181f5541d41c80300300c00150442c0d40c01507013034414881e0000102e100518401135548641515907000c1907405074181c545584052058000700310059040520031011064032242c4030245091541c1e41ca550034061110031030701603404e5001e1b00c0c0000610415822596400440c00c8050140c0324066840d516103240e50000ea501940201c90000042d180c111082428941c90388014407651078028107469423800c40702e03102c10000c0c80381d0040c0c2c0c001c8103019801c4002001800c0c4844001d220385407010030120008888400b010a003038888003400c0c00d155198011401e041d00140c18100f0344d80b04006c129002c2c0c910b84000740e0100c0e2150741c910340d00e65003207141b661054544035502140600c100 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 313494208 1250 313492958 313492997
    0xf120a050403080c010501060e120706030c0314070806030105010f0b0717160c1a0301060e041a0d08130506040510050c1603060506100305071b0f1b0602010f020a 71
    0x2196820031104100c003000042d80710014100c01c64003c3e000040d40d40c14928090125590a010710748240b1608100150101c00007076414281c41c91458041151031080c071059000d40191900811000c0e50075040041e0701d035200720303110b200d00c500b14004d00c0903990303034656041881454018004402002c10141c000b14501c0d51074500c49020414103d0b181c0541c0a03120b45103490a040e04860210b84803600b04510301e404c80c081d048011000011f545076500d071600140c84004800d003a00d00480d00c54603040c6580c12110f580c03e112035000340114802081a14001c000d550080c031a40301d02031140440070502e030818070191001e0314006004c110103140c0030300c0182e589801074041207001d4810406111801300040c21881c0096214680118003170600d1010000c45106c101044010103261004002e940fa502035141908400c0d102541c1c42549203e0400103960440550080c05440301c00c1c150009648030303107076800c040341d60315070003007107140101d024503010303403040f401c541c40040c40c6084604443d143c503 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 313495458 1250 313494208 313494217
    0xc1e01020a300203190201050c090103180803130605130506041b0b0f090f010f0503010510110f06100609030210030e0a02030115050103140606040b0306120f01060f06020f12 76
    0x40780b205039461940300d44405202c1003440200c801a040425074205103e58140140102210341c00240094074220399000348500a03000160b042580726510450440c0d41005a501101e030040805542c0e071610441c04825620017400031501a4501400207201e49607000410302000d41c0407001d4281d9455075128891095000b900307100107600c0302c07100021420f802000510b140e240d4030304080c0d29841c0030010001c00114582c0e00a040c03040079034118000035400403caa040d42c40c01c4852440c0444181c0040b0b4034a6120b403d500c43c1c501c00d5202e085001c060003c2d42602c03d0042c918519121134885e00121604400c1d072000030340007100b200c070007070016010f40c0044d000f11142d40b040302c50030012038000a080d60524040740341005007144040c056964036010740d030604035441052051a040c0f000c085011440ac034810144440390100c08200190764074220900b110740c4000c201d0fa00707401e901440394001c00c510312500b01041002d520001c1c07054004034955040301040006010f11110103254109113600 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 313496708 1250 313495458 313495493
    0xc0e12240c0a0f12060602070e090118080c030904050c0c120a05030703270b070908070f1802040b031509070311180a0b071119050306041212020c0c1e01020a 69
    0x112410780305404203480c405c220082110354000d01c80a86089403102000c1c1c070140c0410020f905085001c1c43d00408500c104018030761003e11103a40386402c041070b078158015140e1305540642044280110ba8880750003402c0ca8030012403e1750b6907001881403002c202c1c0300c1c040b0000301160b4144006030f502406030344403082611040603064507508070310401816507240000225a1561031200380000d8550140c02c200151001c0d10092220780c4c01d00f40c1c51540000b49202c1d40c81088201072840013407501e01e4042c0c900904c0320307079459516420000c2c40f01004424041081c1d015404010006034614400e015164035520503080e803914100c0188080312400217036450079070300050807210010351014060004c000503401050301d4159026002c0030040e81403000f02c0b10380c42c01c203a0345500344955640400c0c0d194110303500403501b040700302006000781c0d5013101c3d41548440107440814015420740c4003040c002555076048900114615503858502110380d003201040e40160b02070b8030300500041109241020030b40 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 313497958 1250 313496708 313496717
    0x60a060318140a05010501090b1302071b0f15020c0105030109051515040f0807052d0301060608070f08010f09020901110105070e12060403050a030c0e12240c0a0f 71
    0x40d80d0b92039282090200d01248680d03940a0728008050010030b20946015280104080c80064080000942c2101e0820401110250300154a404009018541101500c500807000000c2991440d011a540700341d0700c0b4180e13004140317203140f000a81c1b02040c10441c05030141c441314210f03420b0000031002000010712080101d4000180e414066a03298200b98100f01603100f03407a510343c180056101240b039030b64807180c40c0380d00005c0e00707100c50b41d01e00d0f181104861f1640b00340c020500203507a001c207400030f882d100365805500c4c0c48008a5419400700c0c415214011a0b12903010110305c0300f00c11204498248120014000704801c244000c0980f90018400120149080a0400203401d603085c02c45100b5108031000c24800c080c00160390901743c2140c082e448000b4003a1000380b5240d1409800c0d8821003090908066481810700b24250041c1d814107182c510241022180001401d811a41e0b807400f04410788100314544001421454011051440750308a21800e90400d020460152045224000c0417000d22 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 313499208 1250 313497958 313498001
    0x5210c2d0316020a02040f0b041805121e07080d0c110d050c03040b130e0c18151b060601110712020d0303060810050a11180d0204061d150603060a0603 66
    0x1a500d43c011002501f6001d400024580202d10400c400c5444200c3d901030080c0344020728102180e0081086010711441c0d0314015a2260a01c0a4072400300310000400c2507410f02090090510200d01c02801842180010400c4161280c020a40703010124000e40036080d44000c2c500c90500f4070a5018001a90000c41101d00b031940b40c44441007113070000ea0382902d1115401404200c0101104039464000425001c071786c1c40c09030018010070000e141202014010a05400e00080d00446402102c0c080218040c0c404010f501c0e8126081e103420003030b140c0e680012107140d001e03c00d150700031888800311051180313408000f1400354284442c00c0c80d24001501403660ba44000545240300b07110044120354900c03000a010300e0603a1300350045138800745500300c4c0d030070082c04003280d461304c5105202141d05048550380d611840c01d200003000f40c80160003686009150491824110030310b00c2155000329003a441a02d6444101e0040c09202e001c12100a507001c0341c8110108640d9000394040c4241d9400fa08204801 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 313500458 1250 313499208 313499213
    0xa090206090409050f031605120a172805090f0d0c030e03030409110c07120b01061b140d1b1101140c072d080c0105210c2d0316020a 58
    0x21030300f0070f55549060b80000d909800420205100040402c1c825070b1308242408110340d002844c001030001c0388500c038201c0748042180c201d8020189000c1c0c460cc0202003154002603107250016103c1542d00400c81c3c0b00b0a0201441c0307640c0411015a03880403556405a01c100c5038030110f0300100031510b82c64041c0420400030500318041e00840c100f99000000581d580c40c09006401d06e00300555104d4034030030030840b24203000640034201c0c0300e0459906143c06100b000040b44100d01d42401800002d288041d804c0450544c0d030b4000c00c07942540303142900c4169606412650b40c4000c0c401d2904000e10340400341c041010b05602031a4070300341030810115480c0c20b204801c084d442ca082c1c0d5540008004412443e248040581c1c407803c540c3c81b00c0c229988900607185028640d07039071500c3c0d4a50150600001048080040c2c60f01a02e044082003c1c01c0506100e0914005100c09540b00c1c15030042041d209400340d15181201c2d2403425075a07066090103a1450340e0301d0703c408410031307101004070307046010701c00c3c1c0c5101 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 313501708 1250 313500458 313500463
    0x12080c03070c1a070206011e080a0b04080d1514010809070e071407030e0f030f07060f05070b01090e010b0d0309050609060d05090c0103180f08030c071203140a090206090409050f 78
    0x420050354004106d6941031107410910050320043c04101168100c005000f224030208001004030b900030702100c89500c1d2803901c2c107001c2c002e0004a007001c2c2c0c644900302440c5440120290121001e568200716018102d01c011108510112640c407401e83c010241040500c02c89480383d03a2001c160700e00721032510aa4440c40210360310200d0150f000500c0c05c96411010318011491014118007140105201d03c503951140d40c40d02a648103a0040c003c0198000c0400c80c00b900c102c03003c41d07034031404640640da1038080e4980200040007030350a056184c1414000c55040c10398a8501d46501620307540392482c9007804100041e80040012500040c003440054460342150081a00901c403543c040d061520040000500322000440c00c40480550700c0000c8001c12036901a40201c1508030b4143c95032075841404e401401c0c407d00000800c0c2e241f0014009070300d658103511440040d620440ca14169459a2801005460840001a43c82101040309810900d000c3d8040407a90b485003090310f403084801ca01071b60 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 313502958 1250 313501708 313501711
    0x111030717010e070f0809010e100f0b090108030d0b130e06041109100e0c0c0706080403030b09011a0703090504111b03030f1303030b03120712080c03070c1a 69
    0x9010030141035a545044140001c924050500c01482103020720b44040020500c0f601e51440c034051080380700106001000a4200b8200c094095046645407410400c0001c01000c0c1e17070012860440c5400600000b6107003040003103040b103103804011070510003522501c00080c1300c94507006a0003d44510f4619000045024030260040110003070243c51500b400d10380040030100905a1042e04041c0421520702078180f240300a0342c4000710640000d50700c10042080d01d00c80c0303101d84022441640800100da03a07020b08490b1085c1d200760350512281c965002444000c201c01c1c090041c942c202140000e5240d50400c002e082a42e020f480d002085503641c80c085021900c851000240906000a11400904041c2034105041c0c00c000d004625501c0c0010200340408005010500c4102607410850180b504c00d40241e0072101005065442088010100c00100c0e48004000c03507468030281d1845c1c004c0d0340180e1070701e8450341c00100010301c2c40e6100c4400f16405011040d04a541c0b2020355a11182a106850710380d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 313504208 1250 313502958 313502971
    0x5012c09040605091504021c0201050408072d08030a0c021c050d0e0111070e2503020a0e06070b0c0d11120403090821070606091a0a12030c080705011103 67
    0x303a04c0c102022001d0801203070303914032a0402d100c217003413200588031206501102d0141c0c0501d5110022607100485480c8a103a003c81c04c00c0c41000380210f5681c44243c4c0c83d1520742c0d003001c2c2e16410060b4900c10036102440074400e060103a00140664419540281c400311890380c8002d00c41c258092860304152440c81408000b42d4080e881421400c06c40307908011038402010003420501d200ca11500342080c7d0750318560042c540f07209080800310b81176000f02401c400e00250048002d4900e4003000c10010700a41220103ca07000072146007504605081c046d00300c4400b203410460b030700016034138880800c00e10b40c40108044a031035034810a6110048607031003d4400d10090114004017810242801800c0101d180c00949035030300315003038164051b840d00402c40a50751170041807640710101030500000410095214034100ea09060327010398a491644409100b9042c21900c580c860743c0c41e00321024400c0c05e0380c46d0003808681248070100200e03008401400c00320f44141d0001c02e402c483e400d00179a1540003514103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 313505458 1250 313504208 313504211
    0x180b03100606020601170a12030212040b06090f0f15030708070303170109020903030313080415020d080906060303070201140702100809190210050d0b060c0307051605012c090406 78
    0x81c4201035061150307600502d02c2034000075003100000d01b82030700c0324145000144545841c010410074140250150b90780101d00246007051490241042d424010703084a0052103a40e030000003a6015240c01110307400382c1c0101803801d039265a0510501200c00d406082c1540c584980100001c03250010480b00c00a14405d81c1c0f03114014110600d4240881e0060300041c41c0940140002e03225910f00100756580005801050000c1c01158102082d0b64469900141ea41007a000c005103101078000a002c02c0c00122561120016510748105a40350760050381c1259041c3c10401025000d036104400c4000c0c3c0e07141140d80c0c2894100b0325070004204280c801d0303d51001c51405010403400040c1806144460094a04040808071003640004c02081c60a079800c001e20501180584085095500000c800600a40040c0d954103c14a0b000d5880d04142c0c0d04449500c203000f400300d42c200e02d03441ca800440d441a1a81c2e501e003c2a00344c03010401e40799800355000c0000255000000f542d5420f0500c0c06280501b00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 313506708 1250 313505458 313505471
    0x30c0203010f20040b220b0a0905090a051006051e03090a03110307020a0e0406020c1509010c021b0d14030304031206091e050604060902070b010e06010206070504180b0310 75
    0x22210410005602c0d84182c0c2c030084c8420010480414200c980d084d09407003200380d8507803042c10184442d8071a80c2050f0440b030700c0400c04610403900044000103032081104c4036040c6568052074042070b2902103c001d40d00d51000e0030100030240c0694050015425984107001100110551000403a00100c0710341d440359001d04840d0f0305058009120030b1090304000d0243d860070f9559004125070350003600c2036520041c1c54a00090038408070b41d064980720401402942c00048000f410403203614010749800c4000d501e00702515000c5400007540d0421092245104030207881d000040001c0707080101c60a442d1100700c0c942d903242c0400140000d5100d030b803181d00da02c1c1c44800e1b4404207404481070f076003040001030f1814043d002c1c07100b00d5a00e2a40c0300c00d4807003004610707a51b0704800305010b01745550122550900115580c1d0800c151584818182c8410f8102c2182c0b658400d0012641c812050780c51030301041c0200401d01041e01321746029aa01d000c0f030f48012588080c18408245800f480c2010180c550b5074624 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 313507958 1250 313506708 313506731
    0x160302094207050601210204050406150f03020a05100201020712050703031104180c02070f1d070201060b030a02030604140108011e0b010203180d0f0b07020c090f04020904030c0203010f 81
    0x303412552840c03141c604905000d15607807a02d50310101800782e1481003c0c0a5001c0b440c100c4083d130b190074403e43c0503009001c00c0c01e041c642400940b0342c0500740340c2d402030140004206030141c2d003440802c4070380051070040700034540014040c03038a91071766000086540800240c2e0100748492a003c081303c240350364150740c68100f81401001c13260300011041144004110400010b03c0300107424640c1409100001240601c0c40d40907403a02c070403584410003500c8540b43c000384003003010041d8030800031008201c1e03190742d44029049080f0ba01501500000040603c0440c0660030b4a90140d41c0c4000c0140000030720302280c2084650400e001d0b402480c40d0781d162001c04547c81a14110a4211030301d044c02800348413032250020391240101c488019556100a01b24020340c1e80d241045103008d40c01180d0b800d807a4000342040924100d08440d480050b204000030340340541440365000d485030b00e0710000c3c24400d031115400c1180c034010280069081044800620004d6035013031203071070710b40801a40005000403045 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 313509208 1250 313507958 313508059
    0x1d0312010e06010201051605090a150309110619120b04052d1909061503030c0b09060705030c070f0b0a0c02070815010e221a010b0316030209 62
    0x2e01503411641060b047c450b402c810803002c42405012400d01075140ca8241c03020594400c2e15a2283c01d41d080e83d5041d003031344c1c103405901000c5803030701a410300075020750304400388000303842036a82401d000c0b06c0941c010500c00b8403501c01c0204414007410003140c5030800d0320004041c2e070400d8408141e458464020421070722a014202c84013000300543c9031034545414542c03500c0c118107408003003c000e03440e14131907030030170070568090044d582800100803941034590800505841400710300b21400543c40000c81c000110020310548141099900c05241d40c0d5203046905a6030400c0c0c004a03040d001e00c0c440540003c410142c024441d84c88800d0000c4e12015000c0024901007003030740b1061981d0800d07612300195960203d0100d064401c01c00e4a40059280c14000a84c02000e2a0a0401207000300a2070403c001da0a0b41c1c8948001186404103016601c40f644908144400d0b5143d0b10404082c54414008a000e070b0041c0810a0004080a4849180031039040d1050560081014010000402ca48081241 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 313510458 1250 313509208 313509211
    0x705011a0f09060904030f0504170304030506010b120103060209040e100e160b07020d020a0b03180c0a0612050703060911071202010209010503010918080a020d0e030c030c041d0312010e 81
    0x125000c5089007000c03c041039400001510140030482100a040c4c0b035180143c1c01c0710b005090261003903400480e01c0c4c00341a12130300140801c4400d401a4400000d0400d42801a81c3e00004d0305100010140d2856480c80d009502002e030b09a0859168101445500e0b000c0c00104001c0b166407502155147c0f0a03030415041024100f40403004581350501400359544050503140907580c10744d10744910040324000540c1c0c5103140d510924640d0000001c0041c4201e4038041c0c442c081c0040b504949111b19003a0401c010540c040c01070500184100032036942d07020f8030350071040e0010354a0500042980d00c60418005440d0201441d40d212140015410100100f0303040b22880d0741e0452000718108252100002c0c6148010f104050b0036680f625140080c0340d2880080b42000d07541b01c2c04890761210004400780d184d125140b24032002ca913010303513186120305005c21200d829500080103000c00320701350402c0000801e180e0409050f00020404228000c88003003008000c0480001c140030030030340c501602030070203580 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 313511708 1250 313510458 313510489
    0x10f080903040504090203010b03120d0b010f0e010c1103061512030313140708150702010b0a0b19051c0204030b0703021303020108090c0a0e0610031109060a050705011a 74
    0x5420800205804410b60b815140115004960a01a400000d0140249079142d503414094440c504606200b550020b000000000030217003e000c9002c801950701d40142c0715090f02061516008007000c2d8481c0e181041c80d2441081d858100212084c0070030300e4a030341115420480001d440250840c0d1504018810502c40310000540c03443ca400d550845050844810050105032400700b441950a014442071010785480d02c02c517060018201d020103080d5809940348005540383c0701c891240c506100803440c1c00e442d40342c01c91920740785919500c44202c00c03540000c00d0030403206110000301c01904880c04908486504009038641d429030825808100c005000d01040c10710400040c685118402d1440045a80908005655544004c0241d060661594985600a10185021607400c0d064040703240100c005864079015503010785010313411555508010300003101e0912413074448d03190040003801d00080303a1034a1401c010b0350355a91401d45000c41070185440e103c2c0045126141403071f8010501104 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 313512958 1250 313511708 313511717
    0x501170f071206020703020f030d02040e01050105120c0d06030c0e01172a1305040c1401021612030c050a060b01030b041b08150d1a0603010207050d0c0f0818010f 71
    0x28035001c6940d10310303410058003d0407940c000c5040010b260090020b1507501c28842d05880e41e81e0900d0504070029803041c05109240b2848000214955214209039000c0070280c4a180f001034442c0941d10446401caa1a1750940b144c45103004000506100a484010701401d4094641035040841c000107540700b49104180c0c1e030780940460f003908500700e1500414100c1d562407490035000f10001140e0b5110b0400310080103e400c0030140020000449488400c64200c51420754204100b2801261560340c140c0304460395003141842032020940090b03a00708420300c60b0401414400e00d962312360782031001c01b903426503034039a0b241844165560035025485103500200c03020007240140071905518045d032a0b800c1402c000344500007801a1180076440c0d80d80300401044601c01040074586109801020800003003c0c1881c040030907010304050080e50449030b80f02c0007038006418101e0040710203142c13040095514054100010010030005802032000c117500310104018031042000240141d21841550802c00c03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 313514208 1250 313512958 313512973
    0x40207050102030a0c0f090303030e03270a090c0903080d18050604050115230301110c03040603150302030606060a12020706050915010303020c1c05030d02031f03080a03050702030c010501170f 84
    0x1c581c401c81c62000d2303d60500340042c503184803031149031550150904840c1040d80d030111944481d400c0d41c0040f20307058011101000c503035444440e050709032030440c80000082103074800c007800007a1214004d40a8081a00000286000000c901e0610141b01c0702c0251101c0d040075062105000d001c0c068505030300025842036906501d080c03034100b0030400c41500c8520a9441c0b282d41c1485603801c2d003100000d00c0c007a14803180c50b48043d0500c00c1c0c4903480f034414500881d160004800308086000701c981e003101e0300100503003060f0303071560240700075903002e201c0980401c48002081000d003134140c8050310140e401408000b40720b15012059600d0030b001d00111042819100c2d004100083d40029113060b40141980c050701d002c107011902201d80ea1451100030814080450749042804055019511489424443c2d404003c0200d618103840481800040d0010104002224619020390070642e00518079104403485c00d841060705508407102a04004501301038400803402d500700401c00014a03140c001c4c00390809 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 313515458 1250 313514208 313514237
    0xb1309200d0b090a0b0106091401033c02040902040e07020a110f06070803150405060d110d0f050a0b090607050c0703020f0109030507080607140f27040207050102030a0c 74
    0x50300020701c0e00900000d04030300042c01143c401d01c0400011540102d40c1710003541c6500b00508100040d002c0d43c0c0082494031240c0095601c6805617002c40b41468180c503c1522a404800c20144076a0200750715150030b20b0201903c4c4140c1d4401080140400200142c64a05114103030951080207001d0000315030003040341101181f64640c4400301e9540498070742c130030f11400300045000c60007402c2c4050001e110110401c000704800400d031400e081e00444d8208029502c0d0340c00c000b038201411030080c252095072450040d803800c013201d000c3c608c5800365080c1030315111141e465514001c8035034401c6503180640002c0c000401c03000c00040b600480d440c2446400c0203001281140d45180f00d02c4041c0c07090314164040042c0764004c410150113550000140c1d83d0f101c0d01c9520302942e07480d040e1490b01c0019a19144421130400070401d5520074400310f0211361510286010080270055540e1540c0c0038001c1c02d01003020f8540d107510062a2040c071503800941c0f280f80c614026022550201060301c14000b0003880e03040c4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 313516708 1250 313515458 313515469
    0x406090b06161104180507080316120309061112010501140a1b020306010806040b13030f0c0302011116020a050307030b040209090c040c090302040516020d030f0b130920 74
    0xc1c1221400b46502030541a05103081d0705029880016086440c1c8143c00c00c04000d0303c01448200d50041d000c98990603503800396580d0b00e10401c140a00d028005504a40014813071f52000412040c441c6804141a990768880008440c1c480c80c1404034810005829a548100528200d00410003400d1007441080da801c0381d08a284034810345d06081114810400c002e46945029080c001a00074080301c007250f0310340350240d0703075600291001d450010400c800104150949500001805d9042ea14a000303007100360700a88031144038040c12015552508003044024220002403c08540c03071124940b94050300d4018000d409402e508014002c0e0002041400800c880900701343c0c201d40e0503a41440150748401c2910f061594014505502508000c2c1e40240c88d41e0268450095074000c840410403a2101703808228030079101000c940142c0c00200c1070000c5a0300a6100175822610f03024013140b44645240051480404501c84a620550711400f02091005000c0c1c80c0071005040701a114907038001100050 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 313517958 1250 313516708 313516717
    0x120b010e01120f09050115090207021011150705090a050f0d080901050c030408100c030209010926060c0c070e070206010308090a030b0412031802010e10050c060a0b0406090b06 77
    0x14144080440c9500c0c20b1081c40e80300519501689604000d09501407419038082c180c840c0c18a00e5401009001082d803c44920840f0300fa140c2c000d1100303c88007500c0d2020750f454011050300d10400d0141001602d050f0484072080c522445641d80c58580e9407160204100410a854201d18001d41580305c4a00d22521507006440840740c00a4031346031500803400040b905845484c440514038003000c1030010340300d10002104404d0b041c0900080c805c0c0700e481c0e94110124050b00c4070b80c6000980c040030411036030225000f001c0e0140b000f41308065000300304000107442d202003030b00c04508070305000800b007011348020300500c070180511484c511513600741301e00000d41c2c0301c1040c00042e188100008516032255035003800c5000441c0e20007040d01a0346030a041200da0a201580b03628042400d14041c9803002d001c07241d009000507816142d12016511000c24444140e0000364440103002c402c102071020303140d0810400c1d2140d048514046000a401000c0c0700680b04a5400400a5428100d10401c242e070740c0015203 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 313519208 1250 313517958 313517987
    0x50303030412110f0a0b0a020c070e040c14130509120a0929180120010906060b0406170a0f050429011202040e10060b0409150602033703020703120b01 66
    0x106c002e0321440c1844009100d645d01c00c88a030322801d00e0004018401c1403800b44a42d00079600011119924007520b40744501e06810194416414003107504440071940c44517410444540448410b1036281c1e105140c41c0c0e01c202010400701307102c004204035000600900520b400f4683c0c201e094000560320780c1442c54016110700c0720100c01c1c00d00115100c0c0e4030a44e6103240350600101c03100c03242140e14000c90300038403030a2800d4901702c2c281000418000b0620b0211400c036030003540c0b08094001010494140814041c00f000041a01c0780342101980c1024003403d40941e00441079000d415034124141b00003200440500a11181c41800402c0000d51017580040740319010340300424000380c10121a0b0030850740c1507060306002d00d041c4004c141d4128043c003030010303208011030410071907000b0940d070007030780c0c4c414459400182e004000c0361034002203c1d0a020340030220000b144080810b6550a00591000100e6071000664045070790000d040c0e0245070358101d5840c100081110043c81c80c002000890b000c80c04 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 313520458 1250 313519208 313519223
    0x915010312050c10050601110a05070b0a0504051225050d03110109052e0203100311030a06020f0d1409060a1d03030415050601082e050303030412110f0a 67
    0x1145080c40c02801140c22010500b41980c1040e44010f19140042601ba0303040c0c2d0000d4040710b14001203000000d0205a0142c0080c0100001882e1040903229684424100130030403400748030001e500e89800074070320042d40c030540107840d4012020f030703071940f0b640fa150651003c01d00305074804014030b0306c030f03150344008140c1c1614105000107902c8900c207014000d4020010514072500103802c220f204604803c106080f0001c1100c40d85147c100000810307400281d88803841c5800300d040030800121610441291101d02405039100310342c3d180c44030000c98003c0c3e0b1440400660005070b0004000551242056407850804500e0445c1480588180d5404c8000c004909960741c03a4032007844400058060a0689800000ca1f03a5078030301450b003020340000091b002c040090400011403000d41c0038203a5540709180c551644525010200032036038052413090300d0f0201404100101040d103440600003148205e000d907c4104165646e4007004000c00b050441401480d00141d900c08007020003c0381d01408175070042034 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 313521708 1250 313520458 313520483
    0x1030c050d140618191112011b030501090609090f14010e1b0a06110a030e010c02090c0909150120070e040c0905010915031509080414040509150103 65
    0x401c0358510703118420240c2c080c0314080130481d43c076030030b0030001e022a41d150b0b054a400b11110146280702c1281c0880c01402422034404040250400e01c038548400000032001013a441030203141f400d0900c400c42207920000380c5550050044190724042c000051114400030013102c1456182c0b031441c4251264002c00c40b031941060003d40c0c0600750080c2c0020342c0400c0a5520040000507000340600c52491018040d40c00040d0014656014400606852001034007401c00504c0c05c0d50111000c51602d820181031040315400d134405622541c0407940b003001c84c1d0b8403a590360019241003182c008802080c0124010800401c4d410590380480d00a8009038544103225509106003141c90808101d900700c0804000d001c000c020900000707801d0385085445c291001c102a91700c07080e5100990b400202c00140b40c600c016420000150480280115514540000900c540160f994020154400d5000c0043c403c01c0d0184030480349010b00c10180c00c034070704c4801050842c4d684000c900c0c0010051001800340c021416 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 313522958 1250 313521708 313521713
    0x130206071e0c0f050f0301050f07080901060b0315041a03030a180306050f0f070903080415050d0e100c1b08030402060c060703060f2903060103090f1101030b0901030c050d 75
    0x8501c103484a40c4062880c42c540e84a40d4500c61032002c1d44680e61141d002603001003954201845054020503840e2862101039403040025110300d40080c08920700c640d6034440000e5000380401c06140100c2c089420004c2030190f41c0104000c3c0c1d2587c8450030f04005010300d40401c0303a0f030004112005203031603050a86007480000d0b40c880740d5074000d51000e490315092904000e14800d248103200d1080b10501502da81c1510b40703c6085421041501000b4030746001040b00f480058402c1c006500710120b0340c980070340b400000c04080c1d8151010701d00002060344c0000c08040c1d8400c480c0c01114641045843d0212000c10300030100b1009100207000a4070400c00040030030155224003003125015134641049031024106400c00070020300e0248144071a031041c0e20800f080b21001c4501070f06d000c160404030b281c1e01500d114400800b95001408c5141416650700b420780002d4440700c00740350a180115441c4d20700b004404000b40a035900310403058421400c01c00140006090304040b04150748080e15600c50384036491 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 313524208 1250 313522958 313523003
    0x11a0907090f0b030a0e0a03050d0b0a080f0601030c08151b0c030a0914010c05030a2012030103060606050a120f02040e010b0a0914030c0f030a080a09090513020607 72
    0x303402c01440140805070104510410000030b6020b410740d0801008074400401e2015264406d5200c0100054810411404091240c0d0402e5603007040041c881c1c0300c4151b45009071481c0280004e8048901d0304080010800d20616081c46030050840501402c3e52840c0980d05d075140b03410050011080c3e020560080318801d4a54054481d01c83d190340486c0d41e96049117901400707420301c80c801c10004c16a00d101055442d4800e8080d0801d07164498021410202803c2060301e007240d034403920030300000d0f61010a00410b1400c10004a90000084001d0350701c0d41075041c003100365100c5800000c00c0c040c040010f084140d501000130100c144500c03000081060282458038080c3c40b46030301c040c1074000744a0001c5000e42c0e20300010080b0603001c2d140c480400b6505d001f0013048183c00749405505402c252441e02160030503001e1214040380090556078803c0c41035541140300e40107110b24200103042640c3c1400412114030400d50050a000050303036184d502d550024241d4420104001c0c10700c1d003a14640403015055 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 313525458 1250 313524208 313524227
    0x1406030408070c0b13060c031b050a02040507030e1504031715040609060801051003020a0510050c120405100806030307030e0409020a030b06030111030907170a050105040506060a0602011a0907 84
    0x445216825070743d982e42c8134546600400c50681d41320744031031070028106010f10003035040710f685611007000c00200c200d040141c00001d10310941e410700034090090016925441810700c244841d40b00068559401d20a152900c82c404c0ca6070242000c4101c1400b020035003101e0650010554009014001c2d40d501b09050880002c506100c2c2d001400c01d44041404842504004107540c95180200305990342c00c840742603865503600c00a501301d4a0000b05202e1030a1170080d40c0d802528505110b480d00e842174440601d01407801d50301d110062000700b4140014a000f03d44014200300720301d0003c0302414884c0c0002e44a20501000030203001c80071095208075112504807805181d0010700d6042801d40d071781031980e80c1c0c903412603e040c429441d20700ca0004202080d4252800343c000c0c40010700d921403c2c040b44000105200180e144184128a072150005809002d040c0c8940c0c4103c1c0540480d003004003d00900c003500b50865001d45e414a011108800150b01e040c4130850800c0f41c0c10503041e2600441502c11004 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 313526708 1250 313525458 313525463
    0xf051801050f0f0408070615031505060a03120203090603010311030d230307110d090305010e0f070504020a020307020d140705060c0d08040c05271e010603051b04060c0212010204140603040807 84
    0x40108c81c1c0e0300115039104100c02c40e4090030001c40524a5020740900702d4808503402544404180310a202282429154500032001c42c011280f0b004c007001c000070300681099000303e0790b8100c0e000715480e050500340140e100344060341c10b181d02242200f07001644801514800400c0c000d202000041c4110f200c1c503600341c03800d0b4051050b40c50010600400070b02e011040d0200341d82079804c1180c0840030f444000740c40340d010f26060000d03044007400c000400c40030f5030110100104501c002c1c4415000f581d10140f00c6100780348540d1545892044180d0f00c142032140303650120f4440c450074000511144030115a07280f1802c80361074000715594031441c0607442c1e21034036003103203070010030103a5690411400c40070b10000720301450f40301502a03500e9142c0301c0750300c082c859042c1c00d0f0307a00d500004018180c041d800454011034402060040a03190040c04019500710b54802d400242d444000b44082d410112040d94070018140000d514003030810032003909612800303074094081d840c0000041d09200d00c1105503001d503507 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 313527958 1250 313526708 313526711
    0x7050a08090309130c1707170406112a0606091504110a021e0f070e15030d0e0f010e031902030a0507091b080403120c030b040f051801050f0f04080706 66
    0x74030929460010101c2c5074000c030100300c64064031090701e00d5002c403461040207d541c1e0401407450041e0011003803a8040d0040b01c0d8903486034110800000010f0107080700c1e18646610000c482060070710009d10010131280c0d80d216420a04c184110b5840350646541c4c0032080c1640c1580181482d004140140400035100000b50400b0450000265010403c4403001980726080440c21641030f6240352510801245148107a0003070608000c050410f109495105008080405041c03072000c0c0480d05010100d0101400143e450010341402e161040c0602040c010078070b0a44403000107203000c2070b070781d000e010092040c010f0341d5030b040c00866904000c002d003500e03031080543c0d41c3c031950307000498081c0442000d650b480703904000c0b190b5031003807003140b01c94810741d01591040f60400f841390810b80103100d42e0719080109615400b00c80c2107a01c440c098410104010000080c8600e0100d070038980c54128460b02108507414501846604c078203034484c1d1740e008000c0d210140000d0301c6a1810b210180319000d40140304a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 313529208 1250 313527958 313527979
    0x51206060a170408040906080c06340303140f070f1d0414090f241003083105060708030604060f090b1f02190302030d18050c01030507050a08090309 65
    0x1c02c4100140c42120441e0741c0031f1143c1034884074208d8640d1131580385070f600400c0074403250401c10705020094124564428981c0e03940202030340070340c0700030040c1001500441e884084500e60352034041403042d40425550911801c5007800107000b00110f10080010f8100f0801c030f480c400c1410a000e20440202000130810490140200e040071412007086403020704a00542c0032280c10300a021901c04000c489080f541c18048204c502c00c4103d6150103030520801000c2003401200003501c0c0e80050841e545003050648410b016020040800400c2101541c0e1804105c0c40c01c0066850750300948401540c400c1240e82c0341e40c0c640300401c0003868070380d000d041003132a0020002101d0306194020301444005071043d6100300d201241118044403002d8801c0d005900c2072554000100b0380e0300c0200c0c8528031900c1901e00c0d240c83c10f425242a11001d40e02038a004030380c40c00d00c0040040401411415590a003800d0101d071030b282c640a4a41c0c0940702d080e4040c1700d0020000341003004184100d400c81d5038002c0080407030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 313530458 1250 313529208 313529213
    0x30712230d11030f040906030b060a030c0e090c0607080d27231c020c01030605060d0e010e030d0c080105040e0606060f07080a05030414010510050d02011b03050910051206060a1704 79
    0x2400d1f1500c0b0079900000d081011401e1400c1100102c410303a130308600400d48071890590211221070004181d003a05002d844480d140595440300204416402050041c1c0c4a81030b10840700101c85e1182c00306000300e90070800510031010f02181081000341c000032103121800050f10454080d03802070a203454180910018508103017008962003202030100d50894020780d40005c0150222000d0f07002e000d5000380184920003031280540c1081d0500210040040748110210809900d5034020701408041301c0d46820488001c0ca60040041c3c4c01003070304031000e111300b0500888071a201da1014100c10300441c000250390f81541c56000071070303003c664072002e120b0350380680041c003c00d82c0d001542e08481520254110b801180414012035016050107400804040c2c90041006201c1c24501000ca05000010202c1c0001740707004107808070810301940b1520b9444101c4810024200e04440b000c9090181c24460004030400000c440350b40818151901503840940810503110040d0800c0c1442e040c0b0020002c2204 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 313531708 1250 313530458 313530461
    0x100516020901030804080d14160201030b12011d0c1f0c05030307080a0633090504052409091c031103090d0e0103180b040c05030712230d11030f0409 65
    0x407207481b8010365425400f032003412181030f2403505031694503920a02004200403245802d450285205050005104100d032020546201c82c042201d4556559100314074003501c0d07040c0302101955091805482d6003e401e00c0010702164915403c0c003110341e1200d09144405006400007103a044d00001103a469140c0904010210401207404950090500e1000603489400c0420500e442c04100a5a0440070541011b8002c00410308011020040e81c01e2002969845601c1824041d08402c08031810f10a00c0003a510300100080381c4041c0610490802c012642c0c2002c1811140845920010840c1d140d010100f01c0181c850366000c124044400010f00c0443c031000961100c079210103480305145400a04015002c84500149100c0c2510340181d400001542c0740c203440d50f005200e4907100c5071164954010900d06600d03600301442c00310b001e503a80000d0022101108001010300150350200d940142401e075203070072070902410280084080a00168031003841034841e80c184606da1907844603a9400c0520 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 313532958 1250 313531708 313531717
    0x903160501020c12060412050d020a03020403110d12120b0a0e09070806070504050630040303150308040513060e070c06050115080601050a020a080304030c050f010b1005160209010308 80
    0xd000d44200600e0a030359040c440c110110100004c006048940e0782c4d0f40701c1c440355811408070340c01000020005481e2860031071024011030b030640e9400684903811440c04440d450440c5003d24800c0078071006030400107040301e2214003142d10314900a09a034504084490213800300c171499a903ca400c00c5400308110801d5020302c0d20421465040b2041107a0750414591209000c0c2c0d108000948100300602c0742e810500f0003419403182c419000748040010b481166070801c4441c0f030042d8101004001d200c00d0540c1400780482d80c0344460447e80003030349980e0710f114451040b4414180680408441c40901c4012070388003000510038240400c83c0c4d89020702d8001c003030b00b4a461003210490715060011541102190236480707050004d89850700700d07455070001560142c2003070040d941140f15501902001860030300c0903601039131181e183e07040d03001000e00e8074a04041c00d440208080e031f03241c030040800c01e80c0ca60035041140132945c100141c1d141068055400701407008400a90001c150a0001040040030300041 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 313534208 1250 313532958 313532969
    0x5030f0d020304120f050a1d0303040602060106020d0f02060609130b070504060f091d130501110405040b060a09090b030a0804081606021603080d0f1a0405010b0403150b0303090316 79
    0x407000e008207041960030003017400c0e81c0d40009070180102004640200341d1140c070103411042080802c071038440000d1035544641c000a0060700004d004205c0e541d0104185200c440c1d16007041a0071005100d0029540c10b401003076507200d030609802107100e00e20100a90400f0541040a1401d80d00e00468060311546c0607200303080006500ca5034640680f031184505509840510410f490890482d0110781103c4502401c103000d840c1a030480c2e100010030900c0788a038a109040c5a59440ba403601007040102c8003100e1083d40615010021720300c1180d806000e500546d440050b0001d01d00b841c0c917001c0781c50402e12150080480c0d50001c1d0102c2c04010000343c0c1c001811002e81003050013515260101e850b90341c6401c4020304c3d5428141c041c400280484040d08d80d416002c0000a210051b5100440640b4a801c406007024052040c05140f58107044c0151405405443c140c3c030b02d0203203148e80c0c480d05240141280140c0d296503040c0600540c0e02031040320354205005044031034a00c03901a600e10111621310070b4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 313535458 1250 313534208 313534223
    0x30530072f06090607030e100206040c060c08030601080a06080706030f1b082d0403080702010e010606020307110a05090c13050409030e0103020307090b0309070611060c1605030f0d020304 82
    0x4200c1480712031601140d080c4002e0a01030030012241e007030207015041241c04400744002494161903645a00c3c103408801700c99079004101d03134140750828256082e042e8102d14200310114502e0380201e010401100e81042080c40c0001c40b9070742c1c40100348000c007084c0d04005854000da030400140700341d05420100358140c6103842004801c0594a84181c0c0f01c03034010b1458003240c00500050600d040e14840001c0c0c0c502001070040c6105c80c1180040601c46041318220082082d8100303104c09182d0910460701100800c0000300070340c0b4242603000e0350b40d00402138000d203405488040440e60b51100e029040c002d00340507002044505028200300560b401c00409070a00d00740c09800011946820300640f80b6042c1c154503030805020380d01d001140698401031140060114410b80010300340040c10003181316060781300183c008242070060041402081e102c07410b03219405201030024101030103040f220110000c0402c0e96181415140550460064050200b0000303008103c00c41c407001e41d60000c1d481075109a14 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 313536708 1250 313535458 313535513
    0xf020a0b0d06050108180a02130f06030c1d0105150a020a05150612030a0e0f0d051005090f070f0b280203090f01080f01050f0a1802070201081003053007 67
    0x50b01c00c074a4510000c040b47d001503030385005401e100602021400c9088008201000303e6401d54064401a13401100c041c40100c80402800b000100d241e0312080810101c160a0f51501d4001800c850710a41440c200d40d0740000e05984050007000100000396010301034840c1c40351000120300900c41c0858804d03000c2d00c034490744007024220110440d040b202841d21800c401c0f28111061100060540d54022782000010400d0000b0035010041d4007a000f40340d01010449140503400c5900300200c2003142000390703001c4030307007840700036003642c80b4a00360b40006003c030b512010704840c003844482e07034000484030003a814481c1d040601e070702100800e80e40c0c400f03584042514070031400440b4030b41070403200003141e4008240144418074011309000100c1c800144114a02d60710741e203d004c480b00b01860b509280c03540c0002c64104650300642813580c0150b20445100c0094519103030603484001c100110042a2030b54182d4184036122200d10f101c0c003811401c000e50721006289007030f248902001101012000441c172 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 313537958 1250 313536708 313536721
    0x708190504050d0f08090d03091502030f07180b0301050d0501091415070908030d090602040b1803010c0e10050307170703150e06030304030803060d08031906081204030f020a0b0d06050108 82
    0x480c042c0289846c8004200c1c03480c00c10822001005080d0b0700712100420505079801900b4180042c43c01800010b2070301c00182041302c400f5100804590030714040380441401048007034190300031b0b039044400540d030170340c00710f06185892401418600700c000d20701d141d09a103520b48218001340851105640e01004030faa81c40b000800d417001a0317540304d038a0350b540c8100903501030a4040d8000d080114071441025090a481c1c401000c01500441c0080d0800c04410750104d4151500b4003910340102c50742d0519180d0b40340340c00f02140983d00c0a82d0010705100c2c0000c0810155403007841b4040030b1500500c4510042e040098005014190f400005400210310304030200b10b0b00c902800460040c03100500542c0340c00d24603a200036490304020b00da0b42d4851801110311001c2100c040056204080d00300401c42c13a0040c14101e0821030b80150000c0703101b03134890840030445001c10300c00c40b819a50000c4509101c81c51034030006820b440c89030000c101007000450310301c0c420045a0440400d0f00c400343c072000d00329655071 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 313539208 1250 313537958 313537967
    0x9231c0c0b0627010605090f0f0906060708070206030a02090f121c0509100201020417030301031709120d0f0e0315010b03070c060c02072105060708190504050d0f 71
    0x340c0090505049900070076403520b44140f1140c0c0b002624030f200307070f006040c0c3c0303110b0016042e099019602040c4002000342691a02c03002e132031034240c400c8a0311107020103500e000c1200c0b17100060083d070043c80001000c005001e00e00f001e4808840e402400c1548e81e141522540001c0c2d04070600050082040304400b4180380b82881004003850701c030070300504a100212400d0010246905104010300c4020404080750f078070794140004294400e500056981c51038003001c41403021844405107030b60b80042c4014400142c509840060100c06401c2c110380720203072007000904061600b1420304640c8100420f1080c40b40d04410000180d08481c0c5400d0f14480c00c40c010300d41c40345043d0b00390111040c040e100600c0f101d01c0d8000515044906ca00d00071421300346d00d80d105d4049506210341350025a10281c01002807540d86000c10b080c0c0c410107104180d822480d60755241c1c0d18030018164001707000114000030034402251040ea1441003c04c00d09020a003450b0400545a158610b500d41c00102148120b11860b0f028 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 313540458 1250 313539208 313539227
    0x30803150a0806040b060f0a0806010e07081b041224050901150302210a020a0b12010b0412170d15090b0102010207080313030203191d2209231c 63
    0x1745984a1070b98820040103030303143c4038460496000907219030120b0060406c1240c0d6000e0418030083c91402e00f0151805444024010000c441054961003200001e00e01001510120307010080c1c0b24203025000d1428000450a00025110904100100c50054036054104030300581120008010b100480c0001031000b100901000e50004600c600c0031504202044450100c480d081c8140c40c0040803560024404015603032200700034410105000c07003405020f428040c0145565594a4030307080c5802c3c0d18074000c40c41c00c20042c000b56400d525011141d000041142c01030100380c4000c01c54500b83d01040c0000440d18050419050b01d85990102030303500500c200ca5005400c41e03a03850561b505c0f443c503203860342a100070840c11804240804a4003810540c4800413503462529224a2440703000c001946e2849141c0c48a403180c07203030190b48000c004940144056002c196200400d811440e824031050082d030001c0000e04540740420900c80d0554081100b10843c0c5640c142080080000b0b6011a00c5110 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 313541708 1250 313540458 313540463
    0x31506090c05071b0f05091305010509060a05010f210c0b1306080a02130b0a030b0301020d0e010506010206071e021e070302010206010b030603030307030b030138061c0b0a030803150a080604 83
    0xc40c1c4100784036611f401c041d46940841d14040c001050740d91942c405081d1102a01c0c80c0400394403500910070070a006005081c05800e0b102c12640016150000c1c40c4540d10060240403c0b43c4418030700f00d0f0a00021781c81c44805020102e03243d80c0d4400c03d1000501003142140f0404001403d50b4002c0340c10002c403030085a04031402c068074981d24134240f070925040c5500c00365403c424540d0351482200640c4082c005840ba400d0f008030001a029415200300c1d094030401407840717046401150400c1600340d00030b05d0300940548804d5080100c0106600c0a0307291500b0f1030003400d000c0104002d0000109800940c00b02980d100381c1c00d603540703030340c7e241c104502c02c0c002038541c20b90507002800081c141e41c0c403da1154144000c006c00109081c020695002c000c0c0c5004888807440080c180d00301c50020800b84200d14265409445603442e10340c40b1a01c129500480455100034a070302c03a030185030541d8070050500f0281d5042642c40d9a00d003002040503503205101000c450042c062194006910700700413481510458 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 313542958 1250 313541708 313541729
    0x111150a0209030709050106080105040e030c0a03050a0318050105010f1203140a030204050d06060e1501081f0810200f16020a0803120a24031506090c05071b 69
    0x11684052080a904400b410a0305032154220028080000e805164000d011603110440f03154100000d04c400d0f106240d0261805500810040042c180002000c01da50b58140c074186403665180c8800b18050001100d0001412208484003020310006501440c107d600340041705114a5484142c400c10705c00c03410025011503040c0c00450200c119290051901007540d1500501d840d84550008540845691050b240c080e51864103000320b007448881e080e080320700d0b0000035024442040000b40304090052108111858800d00c0c40c15410300340003500c0241c01c2c035005480f84110107640b00c5004203602814011b1290307840640c0b40c0340020000c2110090121b03403c06c83d103008549050100c0754001420100d81050301c03880006980c0c42c00380007401244c204d0005881041c242600102c056810701c50a8150b8003070401003015a40d0b07401001a4102c1e5800009480d2040481c00010b0003003040c0c0e4020b00c580d41c1020400750758150302400810000344070308171140792540c07051001011690103025015860 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 313544208 1250 313542958 313542961
    0x3070b0d020910030e0106061d0d050705090f10050f0d03050c120a030c02160f0608070e0402070b0402011206030305220515030f0a05150d031814011115 67
    0x8901040081085000a41000d8503011440300440d2001d2a000e0040001030358401d10401c00190a009210041c40700d80343c00420510034900d003a0784481d0040c803551165191ba41400c0401100380401e0000b0038005018515500d1306442060121a0071101c21300d0140d110f400104151812111151132600003a2040c2ea405d1321554050702ca030780c081a44e00c1010f104c0d07131003840090704141c0d008200e1000c4d81c3ea0041584501e008020741340a800d003203002d12044428405210042660b0500411641980307031241d00386e1214881500d805803004140781d000360001641030103000108040c02e01451003030340c0356240c1c81449040e07001202e010303001c01000558100081c030040341e0130091070032203036041c3c81000340c480395102c0c0043c03000c41040d0303437050342240c0102c200980c21300c00b40301040e405030041d03100380001e1a0000343c1e0001103404d06c2405114580c20f02980c828188940c01e07400324003002c400050030580d1182d044216891140101c2400604405400310300d5200c04940601000050a40000c89 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 313545458 1250 313544208 313544219
    0x30c2601140402090a1517010608010e150c1e03040c05040903020a03031d01021809010f18020d020405091015050c33071809050112061d0124050f0307 66
    0xb40c02c0c040c008091058070f07050b0b80d104c0104401706d807500a001150060668400441c051400d550f0607034842401c0e80d01d020503038021144046544034a0000c8681202c816980e400041d10003405440703026810854602d803003080c41c3ca107402c02180203501819800b01c1e80c954039001c0005403074041c00020016080000060001303170103034022056020f00510007205000b08d0b800c0260882e0040d402a44a4400054050055003020207509014010500c40541d01600b40081e03000890560a40d20082c00d0b1f000540001d20407580d8140c80c090900240310220328102030000c140088124040c46030074505125131400050700a10440740801108400381848120395194405443c1c01d03891244600881e18000d5a041d19682603024401d4100d0740313602000c0f16005c3c0710016240b807140c100452107481c11006001840c0c84448041c102a840341c4041038044410364400301c070040005d030180241d0700b4102102c00c0103881e580198800b01850180055155581003007049180044c10030a4064121810a100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 313546708 1250 313545458 313545469
    0x31d0d1a0402060d11190212040b0903030d0f0f15080a060203060d050a0f1109041a040c03060218041401050f10020a0512030105040518061807030c2601140402 70
    0x2485030005040a0800301c10a04803070641c0e01601c1407101c45c1e00005605072440034015001c064002c3c19200401410110616000180c861401038201340100451a20010340d020000c4a08600d002181070241c1e4544140c204058812042c482c078100d4103051f0640c0100e61a804070b901140c1300080101940d8007079885e0440258406003509800c040401311410103d0340400017003565506c51102095114003a0601281200c1c02190302482907582405000c00719000a02d80364076402804032103000b40e00c80c0e00d07003003803502da0b681e000a100c140081685d09417424900c00d80508140203440900001c40700101e6a0340012090086680c841d501e804030340c245041400c0d15403040e030554011911742221940766a89030010000c102280c00070004018003081c02c00b40075450704021a401d4400b40948580025a1035001c000c01c0390b0b449502610b06020710700d00c100090401582c020050540301a12142940800c0d214600d02c84501d002c242c0c00781462101c144640e203040e4040c0300c0351180e0764035242d08201 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 313547958 1250 313546708 313546711
    0x160507030c0804080f06160206011a072010030b03060a0902010c06050c0307030f0905150717010803030a0b0604210f06020307020609010b0f06070609050712031d0d1a 73
    0x1020001c8041078980061800d00061025081243c028003400c001031403007910f043c200914503124501041d040030413040e000038205040d078003807801841c1d49949602d1401490700580f42c1c013501e03001e4000103c140351204aa000790501e08269581c00301441000c0d412340079151400b102c41d4140d404440098200c400681c841654244140340c00751040f42d20b0b0b00c8480c0ed4a609503450360101c1e40c000b0600c40c150342c142c4a0030245950320082448008001d449a0303440d410521007030b40c0e010102c98002a1070070710560f851700e0180c0c1c840d81000c0310765071182d01c1d656494204651395000c1c03524040c11401c0e98a0104241d9080301ca0441d10074260303412142048a0100c1c0c07582e000c40700180c8001543c00010401e0002d5031003145280e000309100d01c0d004800c1c600b540c00b61068140901c3e4682072640c0030340c64420456a00942080303000c00c01d82421300d000d0340b514266600c5170b400c01c261000e40008042d0310500810102080404108190707007a141013211550503c1001480c0500c00002c904c0603900d250307001ca = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 313549208 1250 313547958 313547963
    0x609070924180e06240d4a16060c1104020a2613110604050d0f03030e030306062703010519050108010606021906091712060108160507 59
    0x51a1000500c1e41c071a11045054000305071140183c000c0141c14205440d40b1140041d002e0803600a620b600c9045560038450780c2a1054040d44805426094a0030400f40182d207608401c2141a010210410075010f29401c3c02080322000081c46110000c005c0000ca406017441e1104000d441503140c03200c15521400f1030001140c0800700d860000700e40b13958510103441607440c0341e00c4800300140381105c010840400015070400301103064041c082144070341400000da20754091030344507a0307200c000001283d600541d481a035116018411080c100b2040d481c1d60031046101e600c003802805c00440009032071740811640a60000d41c00d00041419042030a0302004100ca8601015542c0e0954004213095a008592a8800300f801403000e02c0c11812070b200e8640101030342c0700200000d0703040010003900c6e034050070511000705403651290303401d0080716800304540940c050040c000c0394000b20480201504001d06914504003c403002910729406589068400c540550280010844030b4500791120b4104180a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 313550458 1250 313549208 313549217
    0x3160f0e0d03080601020f011406010c030c02090a0c140717030a09060f0605030c03010b090c03060a09020d0504030818101e0e0a0507150503040803150301140609070924 74
    0x10644103071140d20031480303074600a640e11641443d20a0000e40f81201240048203107038900000c0c801106041146541c00000c2440c02d011801264201100e46901c1260080d501140c08820f02100048035400301140580f5600c441100313000500c140e0344180142c400103080000c0c40e04808041182d410021540841e0031a0001000c0c0c240b0384801049961101c00d1800260743c455051089150070014607030031000440c0248448a02c04000c603002a401a0000514010200101d400b42d0b64450451010342035080c0115283c14504802030080c24055609601280074040032404d464840b049000000c01c04000034140c1580c50103001c4018210001407124281c10020303840c0040e013250080840c80c0711580003c03c0706905d00c1c02c0040c10141507501c8100301d0714695104d00c10a50300300050700e60098010035031171f0f2660743c0c1581c031041800800741c003681e25520b00152010360340d054400c1280031310020303030705410540d403404420303140e0103194028080c2194800c0c0c800308404180e0b0700c103c20340032141d142 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 313551708 1250 313550458 313550477
    0x408040509131b08060a060807120f0b040602040501080109020406050a0804030e0a1409070822080d0617010608061308030a110a090e0702241509090f070b03160f 71
    0x1075618254400030203580c10743c000041c0c208841041005180d80008825008000c035910700040385e6078540761440f4091450440c5131a9109014000300c40100041d000b02d12090b041c82c09140c4080258007600400d03000c91000c0c03002145c425018400d9406039105916140c1c40c0c081c03020000d546130b140040088040041d0881d010900c0d0b190300682d20020031401e4610340302000c1e44c808100444000074500d0301042400d800b000b003103183c8030085070701c0142c042c00e046030303100502d050402c01480380c100d05402c3c4c90b0030b1000c001450440034809440c902e900d03000030002152910041515480b09458401e254081c10000300c0100c1c88910003150480c58058000405448100750b101543c3c1205d4410400f242070410708208109622604980c0100984003400420160541040e141d405007040d001c48a455000000d07035244816014018100005200c210145050102c2c2c42e0b881c030144008202c107015900c0d0000d481840c0c003080d680250840c1c40b948003c8800c40c0c0c011104111904031120401c202110b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 313552958 1250 313551708 313551713
    0x8010e070504032a0f06200d0e0d03030e0102181315090b0f0901031202070e010602060109020a0203090d0507050f01020a08300924070c06110715051608040804050913 73
    0x116400080031181c50b6222120100c0100940c645036152502c00240c108030b082300c450640c0940310b00d0070f4240484000660303140e0307030408a000b0665032025a0482d8400214140380d102e140d080c41800b281e04503501c50b16038a1820480081d100e12506668009a07070310002d1244407019040002c8050024100c108200884000620821310a9200b43c07900180740c010b001c40c1d20307418090b403800b400704400c4441c099454a10002c3d40e66505207e842d1255901040307400324a8400d2084070000040140700308076815050402584400f0301c1e20800d44030303030f808028840c819400410f0b20844140c20049050401140640e08021024501d085071103151005420103100b0482081e1140200d40042c01020b0504c2803c09000750500510805582c011550301040111a802981d400406034801c00c0441c454440e99140e140b42c0c000c200d8001c00803420390088600c0048154861440ba200001400e503200041c2202641c02141c19280640a090100800e10241c10f012074016044101e00b2415a94203402d40c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 313554208 1250 313552958 313552979
    0x201090827060f0405010f0908010c081906061b0c0812040e06060304050c0d021507050303040b070e030a110307090f0b011d0d0204090f0507030308010e070504032a 72
    0x109070701668614070241400203260030611a040001d80c2c11a10b401c0601c0403000042c000c920915040241010682001ca8802e08050004242030070007448051604074000e030214138210b80b00d410803000d20310103903110020350044c00100c8d03801c2d071a00c2040788608241e05200707001020059070303114415000050452001c02c003411810340c248030129103072030401322204200c0c1030242c081c0f07214a00500034000890b002003550410048229411944000d051001c61540307001c48001c4119010081205414001d020005600ca244201c41040f01c1c0e54402800707480f4010701080c09501a840b03101d120002503040000710504440044c11201c185031b480f205142515186002130b045283c50b03001b06102560024070300440d07084a00c00110007454030002180311890301d404080d118545888840b41804008a200d16501d50000c0984200503124140900140d5003849201803402d080000140940d1251003981c059a0340b1007200060999402c20100c420307400c05000c9401c1045a50380042c512091 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 313555458 1250 313554208 313554217
    0xc010e03011a0f0d2f0102010b0f090901061a0a0206011d06060721030902010806041e0b061c05010501020601062309120a060b0f1905060319020d090b18070603050702010908 76
    0x4910101850807145d070145c03102c0c00c0d8400c20541035a041808128140c1d0301c11415190030101954050510381d138100525002d89956440300c040343c01c1e050086442482120010180545903408464460f6a21030300880449010303800c00300620340b400c010038160300d01480207128090003038540c00142082240c911044d080f117280ca08004c43e5070380e20740d40b08650300074230348076400481114104480d8000003110000c0700c1c03038980301c0c900c2d040d80c0c0c0300852030640d0741c0c5003034561401c6c0081401c11082000b91407007004000a0003180e000d0700c210f0f80002100c0d80320706c6064a407921840400e20356110180c42414450b003104e5842e60340140e991034154a4070300c0401c10301d001c00e170003280041101030401c004e00040300e5001c0303000340c00b860748129203113500c0b10211005400c4807029102590f0340d9450346004207500714114498180707113000050035540c00c031844d0000e8113800c0c043c2c091032110340c680c0c1040c14800c8950303400180f00c40c3c00c040300c1041102d0003503013b5588403040c0d00001c66014420f64409100394030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 313556708 1250 313555458 313555493
    0x120c03070c06020303180a0b0c070237090506130b0a0b0706061a0708160f0209040b15040e19230309010201060902030f0a0c09120305032d04060207020a090504050c010e03011a0f0d 79
    0x900d052101e0020070340d098100014030380000c03b0000350428001241c800d40d2070407401180075481d0300c1050a6030301c40e41d02d00302c0101000110681c0762901d83c60408003424151040350982c000340342541418922480803908190341c001200c52034a000074410b894407005140051701c4800d00c800100025844505186100307034851407a219061414058424101483c2d00a05006034030301070806145c65400150880c0e0303154898440a410400c034601300d014941c0c2941101041e80c00c098a001c12a20000301803c40703982c3c260003e0000c180c45e0381c940c0c07040703000444540326158451000318040c1c031580d52041705144928a01506096103402c88014030055042d421170005500104024031600d0007403070f08862107018003244106458080c0b05482d66000a00042c0520b80d00149000031036980160030001020002410b03c02d034545401e00d10345031002d00103103a001ca040c40c14520602d280c10700c600d501000060300f94001c0c2c00005014052404481545290048100049180400d01c10404142e0f01d00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 313557958 1250 313556708 313556779
    0xb0a0e0103030e0a23010825181a03130201020f030c0d080906010308040b0a110d0e04050708190b2d0a1502120c03070c06020303180a0b0c0702 63
    0x1000041c040c0c0155a58000c0e002c2460780c1c804a11582e03d41021072503880c5c02464040d03e2611040c9984011050b4540481140505403020342c80c01500000028030f4003178540c5419204965888089000402501801014000c10000918008040025000980e0040c412500c2d030000510380785185d54444071514032a5840240d40130036803540f10700e074682c2c80201d08010b002c3d0365155a44110241c0914051a085a20081085100c117441524a4826007410b030040312801c1e0050344001e460040b0281c0803900603424200015000c0c2c2c0600001401181d031108884000c1a206041d01c004003508401a036000040090707540c9651401644103148140c080722440c0351750440c0c010410703800701c43da0001e1400031303078803e085011a4000c02c0c520452494500302a039140c60f4400464254442c5500040260304a6540810b410781d000001d103103d50392942544003c20444030344030355640c020303110061900c102d40d800188040d59400260440610181510400008405085001071100344d030700d01000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 313559208 1250 313557958 313557977
    0x18030803060f01030612030f021212010303110105040f03080709170d110604050303040b180609010f0e010b032a0307080f0d05091c140304090203010801150501120b0a0e010303 77
    0x24070b070495280a07003902c01d080403c4044c0c6422917842d01d0750041e6202805102105200c0d084a9000b800b8140c010000401483d03a00d20184010b08880d40c03083c0016800a01401010030074980140324490003036400c004030131070862095030101c81c0034600034001000c01c444a40001440d41458500309481c2e240c1030301400038032071540c400400c04041d62030300c48156401b440074000420f03400f1003140c0c3c01c56080010010340f03564565011840040400010f0030714800d00b803c0000b421010340c001c00c600340b40c00b4001c3c0050307926454480c0c01c2c0c2c1c0c520000150315801c03042c240c2c040107204da800c9910220481c5001c440d1041d118002a06140d031681c001551074000c01c5114803641c005001e031405000c41800c1031414005641c0114182800c3d81c0b40b42c0d1140280700303500c50b0900a8621070000c0c03844105013100d80d616245d64003480a07400a22030303808c1c19820f0120500703015008880721010b580701a511544480c600641c3d21016140031000307150803041008010480c1d801d06001c09010754000c0c2c9965501 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 313560458 1250 313559208 313559221
    0x910120c031203060303080a02030703090b2505090604061d040e060a0f0203131e02060301080a03080a020a210e1204180606021c0e040516121103130318030803 70
    0x2c40031101200010546019400c1c80080e8024952a4000d2118980180c49550b000b9058004024051010308840803000810001540181301e40303012107a001c400c0c1c00d000003c0c0c9001d6545c0d004140360b0030f9110b0414042881490b201c0c0d42c6088a065000444c00d0f000c04080010070100c88005803402c00d1034000c1010447c60703c907580540e50200803101e02c01c600e50725066035201c40c2c40c09520740c02842c8000207203250390f096030524121009190018030315982c0c1d594614141e079481d000500300b24040389081001551302000c51080d00c10148030358907250290400718058698020803615592009030752454803415003c1d0400003000350380721403540709903103d0415201440c501580201d03049181c2c200384003400044d901040c2000240d8428030300c105c04c3c24604e0010754201910a0006400c2441e0004104000360120003030740d000d42058580708040a8628200d00c03c4c0e41c90400584402c0000300003203041c102d00c080c191710946000340f801c1c1c002c0c03544080300c0da4107080055100781c41085002c0309000c071 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 313561708 1250 313560458 313560473
    0xc0b0705120705070201020d0e2403010501020f03030f010522020c06060906041a010806060403290709030c060804020a170604140703030207050411090603010b0a030c1b020910120c03 80
    0x30005258100340781404d007250300003951001010140700804c648140d0414464940001c440c0c000800c0388108a8100f218201c0902c181c0c000340311b030300d00601c10490013558407000030007140e0180d40d000802004981c204414484119903011101401c40d1a1000703034000d8034107600c040d20034151707420050039032800c065080000105016290314840d901d0241c0f4440040700e04911200b85003001e003031200455454500240d0540155440a014041d0031000920340040f8055400d840d0340003422900d5594648038000c071100c080c0360100405403000240f09200c103e02440c00254080d200038000c0405ca5110030549030b520000000c41070b1982c2c400814001007104400000b03c0c0307403c1d00e40003030203250301d1524021341d982158411680295500e92840d40504100f40484410f50030103000180d072569a039101c50904e52080b0262400039140900e5040928403a640702c900c1e010740c408000e400d80b00503030204900080e01500d0141040c450100000700c20040701072401501e4055910f440032945541000341 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 313562958 1250 313561708 313561711
    0x80a0f02070e010b07060c020304090f0501030c0918030c020301020d0204060804051c0f110a020405161d0a030b0916080706090b0405090112030203130e090d020d0e0609010c0b070512 80
    0xa5070000d82e401440052540c405490250750014804144101c40c194160b0841c4110f4010014083c18030391518022081ca400150490f03224200c04501c555542400b441147c00540c102401510013008800120703200f525500d04850004000510300960010b14400300e91081e8000800b00f0a100108824400203200c8428800440800e440c00d1000310400208683c40107422081841903a80c00130b1100341e401c00c080a10b940c0c0c050020001414901818090000803035200400a03007194420481c40c0401d05a8160890f0003038070030080142140c0e075030a00100000c0c460601072045504400c0e02511203d96140104581d00140020320308142004110407881d400a03140d12100304810040741d10340e04003070b90444610000c090b0b80b0480f545412030841c85910f25041c50803c102002140005000008078099410342c030440f4482103540d602640c480c280c41084c0000304140c2000d00100e03042a000811006a05151208206c05a9031740c20321408010395211000503400700340b910311074200c0d50419 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 313564208 1250 313562958 313562969
    0x1606061e2606070315030b07021e0703110d020402120f01050f0109030b22050706050a1b0308010303080a180605070305010501170604020d0204080f0145030507080a0f0207 75
    0x41114900401c601940d6403005003000080541d55170058503110a11840039002c1c2d075105c9101000c9042448009580f200d01c01d01d9038100041803403108041c1440010719100303d9910110580d00340ac0d40d1020490304801290301a6003003a020450440d503102d54403215482280c0c1c520010b4881e50404013449180ca0550f048203040c428042c50070302c04911002545503120841c00701c0340b6030b0880c3e0300001650400c81050010094400d44001182554000c070240135101012313030341c103011550420071116012008000207800703d40183d00610100340318207031040d44040280b01c0400e002584000d4903d040c2c0303052106813070740c903942d4091145d140d615001d8280100720910340130039240010401c40031010301c0500302511603540081c0800d20203401750161801004040151000a48503913040340c041c09942000000b007144450901003001c0f0b2201d00c0c007200d0315003400b822100d40f4840e1480817111402010580a2210500c64400081c1034075004000092845d6100b1209011682000c0d02d001d04a0300070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 313565458 1250 313564208 313564259
    0xd080114010e1f03110406030618020301032012070e10080c01120e100501030f020123090f0a150c051c0e0904030c12050406120b03031606061e 63
    0x118201d95100301c4042c20000400b01e1400c08021007090560003048400d001d008202c00102c6e0010b00d154155100b0811505503072140d12040c01d003c403c52040703100902008010008007241e00e40041802011140e00310030180024038210050054180f40035403aa0040340080003010400c030b207690460b528080240b48480c010815290030b00c0020784030560049403c0f415941da0034140c0d010f0a410030100e142020198020001c5503100d0a00704010480c09406901150300010401600070f000446200103104030700c00c0e07078103080c0128200315143c40168800769200c1080341c030206400400000c00c040c00386894407981c50001c400c0c0341950a0581c0c45c24000301443c0404403028040d5000190700400c41012a0f6007900e40c1d8030344c902500c6440700c0c01c80207081c50b00420341500c9039542000082058481c2d0b81c40b50070550950080d0082528002149140c040d00700f40300c1200100324100c072000b1018030801d070200f0720350b4036203220807200c250f200750216047d1480c880800925894000c03104102303000084 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 313566708 1250 313565458 313565477
    0x1918110f030f040602040f06080f06092404020c030c07051302090d0609210f1d0d022403090c010f0e0d02130f090c0311060301060c030e010903050d08011401 69
    0x2010039081c00000c201907410341c00a0002002c201c100c0e4100d40c080c00d11990010020b584800c0f00820400040b1024100340312204041041880c1951504c1d00c85d200500344076071409488019802c0c007818130180283c006400740308403680c00c038042c4094058030202c44020302010703191404009410380c0044020312610b1040000280e60386504030080000b0390089000702c0c04204510f400c1c030001302d8054202c2d400d0b1450035072030049541e000c240f003191100140d503400c118081826512548a841151203036000049691400c014103188a01c181b04c0135100043c400012451602c101555100721141440c9800c5000d40182540e0045e529150548091825481c0c100c2b82d5804a002450620000f0f8810f200030802c3e580d02e00306682020340c05403684075080c880003805241183e41c00d6a1404111640c62000ca40d400d82410180e0642e81245ca01e07030307503d4480c8141924262140d2400c401810304014040d2004000300b20100000d12824407075079101d549a40c944410300920500d502c0a02e410400c2c40107 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 313567958 1250 313566708 313566727
    0xf0302160e070c021f090302132c161203090e0c031305120708030402041b020a06020d1103070f0f0206130201080603010b0a0b03040b01060819050402191811 69
    0x12a042d400362041c01c1c071907004015400000c4010200780f100413135031041c1d0b03003551201583c0316101d2403c4034030940303030411040400b0350034500766110310031410b1078406000900c9803080c10f44149512411000d13401d40344903030700c0c081c100900d04005401c508000460101003104060740f02c42c00f000180700f15666010390f802c04415041262102600812400b01080b00000a201c410f02480c0904d518110305195200140d140016582d001100d09074456880e003d4074031140303003500b40c46401840956024100c20516a40c1e903030025048050002c0e2403e0b9200c0c00303103018210000c01580240403a49481042d40380aa800804001c03140c0c000104540201c418041c00d00003000414008550900b00300a0540d20800868010a044d80205902070400c1000003004808040110f010720f0155400e44c1d80fa030303200d00c0c05840c05241540e002062207071661300c1c2810081e207984100d0300948000c121000003403072001084d10102c0903800c804000014a8290300c00c0000c14801c40301c2405000700000d09200804 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 313569208 1250 313567958 313567979
    0x50c1606080408030618011503060e06011709120708090f030c0604122a0302120d0c080d180602130806011203050c1006080d0305010b180609030c09040f030216 70
    0x342c001481100040045a5140c1e10b40c110720501c2d40782500c10070140d41e03440304200c80840300c144200c5c001c40d00e4008042180e89203140d20600c00c04040c3c40302c0c5a000d010101d4084283c0e8021300f1012135000f0481c0a03c2c08a510070020010745000d00c81068541580104204001640b02c0201e440780e403180300b9000c482d1b103030035041d6130442d0300704c16144840d811581006041940c0c0e0302c1c0304a08103e0382c00c4891503100b11811402e0103a0b80281d881c451107103000101c150383e80140b0251140441c401444107000101510020090b000e00c5240100d030704080c1c12200304500109000403501140c0105424048120720740d0000020004103008011b1545403480d07103d0301031054800503040100000c1c0440310305000300f1400d0013640c0d050008000103580c0b5040c0607142c0302002e0800c0d0019040500000342c00d034840741503e01e204c16880340d05400140004c10491594095254190035000c5c1d03041101199641e80c039010311450042118100c204410710b8004d041945440c050300e1100118003007848042c891 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 313570458 1250 313569208 313569211
    0xc090d020402030a0b03070f031b0803031f0909030c050607050a1205040c0513090c06052701032705060a02030408040303141204030f08070905061e0c0a03050c160608 73
    0x195001030b584d8403403e51082c05001c026440344e400d407085850000c0c0d80b900c48948441101d010304241030303440403c007201c405040058440c07001d0030752041c0086803903400070540070780f501c100c030010544c02c680d550410801039800c814002d80100f00e1005000382480424404560b111125281c030794030f4980c20000c0030f0b0143c2c1c680055000d449070b591000500300051482568003912000705400c00c85103044581c0341c05008907260031605510707044d000003440d601445c1540c0c92001d1988000b500c0e116800e170498503032803801d102d66040545076041240740300e81d040c2c040b42109041c0d4605010700c02050625500e0400040c05034008248100208800700d04a8000e81d415240c2c50b1800c109028010b21010b882d600131000910020351040301400100343c1c21a030b81400c00010344c1c41c0c800d016502c2d5402558200f0703461040a4118004102c41704040b003080203280e0610260418041c280190382111510307020346404128040b8ac00081c0c00610840d0403c00c0000881e04c1102c9121070714101440209000030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 313571708 1250 313570458 313570463
    0x3021323100906080603100e033004030309052803090b04030206221805041202160b0f0c07120209180d03111b071d01080d050a1101230c090d 62
    0x10000700c1c50a42d0140021f1141e40e00d0117809000d000000f0003441e4580d070105020b0058840b141c0581078910826404058080d403213500320500681c0d60b40c4041e00038054060089805000e50640d600032401a84040700c00300c001c0d0513803040811000c1c40c0c05020014103404c080000c0d542440304100584e00c0030f08a8a00746084000301843d141c0078441d84401402c5608140211407050010000c0d1044c0ca500003803056000f0003516a02c0d0380101000d80c0c680840700c94228841503000014010000c49d8402040b24403a4410494a07000c070b1a00c82c0c41c1401025007294500d82c640384125030662400341a150341082d0405030142000c0700d140032003030740c441496a070b120915440e401c0d000c4038a4411300c295440100800542d0101d44a0502043d8440c05580035074600c03403030b000c440b00c100c592165207442c1c103840c0f044004040c2ca180c1890240c42507002a600782c010860205440341c04410f003130154000f50060701480c4061094a150a80720b1110001c1c003484450000344140e03900c9030b5424159480c46038 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 313572958 1250 313571708 313571717
    0x90712020102070e04060207020906040b031b1c0606030308090610060f05040b030a1508030f0403020d1103031201050a050d0510050403030f0c0c02030606040501050108040308060103021323100906 86
    0x8100e10041c0d041c1042030740262030602a100410003403008680052a541c1e100300c03541082503031190100f00498240340728954055100c1d540422025004e1403030024541e00040407040303200701c0c81b012004081804001210400e0b1201820020141c2100865130805404000b62044e850441c0305500c1c40350311751040744100241c9064403464180504211006480c50300241d5683e40340112020015098030980c509501c0c581d1240040c4940d004400c0d508170708404642d26181034550b4007084600744080000b03588640440c030316801195010402400081c44094540c01590314140c2004648041c2d9071005004250b10900c1c0302c0000e4000c20318403120312003001d00090b036880c0c50a0460041128101181c10140f0381400c5460580d0011501c282107442182210b0710741e0380d58000c0c00103540013071086501180020300400c2c000f03400f8030030031648054103146c0107092203d845034a1f052350480b507000b5604c2102d0303102021100c00c50701c840200c0b4441c041d129401a19548c02006140c404544221801c12 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 313574208 1250 313572958 313572989
    0x303040305071a0a090b0c040b04030b0a0617070303030e030406141b031b0105010504110f0c0102132309071209060908042c04110d060b0925080907 65
    0x568048010f88041003d594100da0b4030f010303c80b4200804000300c06940d0024000300103407003048524116800d0300d81c50400282011301c0e540e549108050301038402e130a86511400c000c1210074180140340001d0520340c00030880c5030301d5424054110350083e01c08000c242c00c00c01003441047e4028544040300c14400b440c003950307941c403012400c880c64608115a00f0a0100049249200c1c0004c1c44800e4000400c00c002c01a2366a07400400044440f1582010444001405800c40c0070303d5010180817000704000025160080d2100c5c0710112007220f8100328001240e174070b00032060700e040701210720301d00000303030380c81c0c212030030141c0c2c2c080c15602d0700344418100940c54410032010002076801400245078808881c0b41c8a90300c0705c0103421003540030304a144901d207400d161901d8640031252110300450b0001d030064032890100007409509180094181e0307215490300da0484503922540080b03889804846205517444081104d100c244d05000f0f03002c0d2040200d2601404180800865800300f01c8410000d00f031000c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 313575458 1250 313574208 313574213
    0x20108070e0f0d0503040f0506160303050c041a120603032109121201060f09140108061f02010b030c0a0e01171c0306150836030d23010602030304030507 67
    0x442c2800355442d00900c50b012140e0401800201820646001c0d04c520041d403130300c0c0e0b0107110840c020055550a9400c0350700400012a000358005504040b041803c00d01d0300780c82d141e18030007811400c0c804c02c0180e00700040c2e2101d03440c1120b00298100300203d000d540340021156840380041484490b81d90721080c40d9004c02d01181c03040141890004000b03070030747d031a100140d494803048002446240d01044440040e0080c3e24071401e101816600010404134404800c0e03030045034000f400030000c5800503482e2560b0b9a21700e0b0f0500a1401ca50300c07d41c0081070040401c001c1c90305080420b00c20724000c01c003da0f001d0004403204428181076442c0e29070120411030965a640e841d1078440004c5840100c1100c0d5801480c03030b030607048142500c001400480c00005182e1040325024003c80e0f00c007070003100f905d490080d010001188003031030310201c0c2150030081450141075400c41e4803115906250503aa0605551564103005500e00030320115000e4a40c290b250850103074407440014002010050300049030401c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 313576708 1250 313575458 313575469
    0x411040e011503060e1504030e0a05130b04062103030b04020918010807050d03090e07020705040f020a03060b0f0a0c1406010b0a02061510050903100510170604020108070e 75
    0x10200c2044002c0c400300c0c8280100b00d40c0e08080f404141c560b28244034150743c0540000171414441c150101030510543d680f82c4046506681c1107502a03407200d2441c00002d2242c0c0d48445401e03607007500010000e0340801450811080b40c0e500c0d4800d02c00000c4c100c0d010551450b494030303031803411ba03007604003c1342c41c0c0e101d2000680248605000c5580c0b00c40e040821504803a00141918103072000b041c21240c62a444404010446540190003000240f480f103050141124550308282c10404d540121440191a1000542960003d0541c1c0c440076901017900c1144680c140107040041c004a178440b4a01170081c105d241003441202110030078004400b00032402c0002c001011f43c891130109081e103115503124008c0c4e1250342c0c00011070301c0051082001103030402d40c003144418842000240881810112400107840a400003414a0382c18000d1401d0160414024002c4500c95100c4070101621136003400360044000500b80041d0400d5030240d1708010040c0d030401c5113590071020505101701ea10110f0000642d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 313577958 1250 313576708 313576721
    0x6010e010519050405060d06080f0f060412020a0f110a09060e04060507050c011b11010c230408120c070803030403080c0f0706090f030306120b1602070e0705070605060904020603041104 81
    0x58001b040011444556400340d0f1055040d10082426900c90130044c881c0c040c0e49604034805004281c02180c00b04e00000c80b0400405480320350350069600800710303038072110306141c0e408005550074460304d0004400ca107010401708000d000505400c005140c100005116040c90061000700b2075580c81e0b0124030014000c50549200c040580000d0001d4401c00955580c0c3c20402641140428941d07104e038a1408010b0040040b07801040d603c001002c0032203001d0005040903c0350045401c1001c100c0800c4480d0b080c01081c1d080b15002841c1e0307907201c49501f6039070701e86816540300341440d030010f000b40400a07501044003608001d0900721f280e140c8003004940816480780f030b1001841c1c686045942c108100c00a4500840e45010340c604001e20b170350f00c60444507440f000d15401440d18450100040e030f480300e01c0c061200c0307400302481101d81003911600b0900c48440e090710311b5000b05002240c81810400781d40034941e80503030265141d0f490341c14558042a2103000203000144482400301209146883e41e50226 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 313579208 1250 313577958 313577969
    0x51c02220602070e13020603070e0609030304260604150b0f1c1703090c13021603020703050d0e0d060b040f060f031a1509040303060f061706010e0105190504 69
    0x15410300e9a41d10069030322000c52251520386070050000400540d500c20113002c0441d0050002440c50b900c01c001114a00729116205900c13820038060509c00da101000a0320141c038074485a140d503003150301ca010480000d046401e06040d0300240400002400342c200d81c0030030070450728010450380280340014207842c1488580c03a8022800e94800e840300c9100c1d0300088403031409810740c08205956441c1c46000b03844100c3d83c207940303640001c03c0858541003180702140184c0360040014203003428903403d007803040d880300c10942c01a03011107401c2c005d211041c8800b609916203400c1ca002e0348100800403038400340c010140901071507601c3d8520600c0382c846400080c0890340c58a01008415260110301200090502098500481c09102c1c462031204546601e40507001003051060310100718000c210488900500880c00c05844150010b198511103c414010700300940303078800c0740120b1080820380820001d2280d030400c07640720000742617644c221040301d0500f10302d05040510307001e00c0304081c0d4152045070311a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 313580458 1250 313579208 313579267
    0xd111012050a060e0709030201050901180305060408071e020f01050703120e030a030f02090a03060b15070f0b09010b0d082104080702010207080601061209020414090d0807051c02 78
    0x1000b4030701d000b0f603000c1d4059602019400e1810b0b114500c0c00c49008443d400001d01141042101e03d100d0740c040d000c040400c01d55403141002e1240c885c1d45560400c0c00c2034404481c04400492035008000e08071100e11014558228110018441500052000d184041c20343d410f02600203007210030326100312580c880e03900820701c0c1803143d9030b40b0380d000e0b0341c1d268040c0c20060700003840c00742080c140d040340c0d000b2590010401040c40c2c8400c1d040d501d4000c02491003008030346d13000041310320304614a0307450f5028001c018080c500c50000710106c1d04169001e0344e001041c20001e0307450201d0070f03c2d5943d00c014661101c5600403448586a60001661010320307034134885080b1110324103804000411007080001d1100e24403c0c0c0c03e5a86159441c5440c80e80c83c0c0c0213005450205215405598000c60700c1d61100c00014001803001c2070800035007505945401e001e950035002500305080806003240c0100510340c020700fa0b0310381a85081c2d1424801c600c0f43d800d40310780c82070721600010841d4280030302000b41d101e80403580e0304 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 313581708 1250 313580458 313580461
    0xe070e0d0b04020321030604020a03020415020601050a09050906150f030106030b1803030708040f03050f0d0b0a06050307050f0c0f03031e010e010b0702130609020315010305060d11101205 82
    0xc204040034402c50b001c07031282c441c500210f900c02004c041254098403212007810b04540310402000b000e5004142d2150825a081c40300241c1903184400c10220420f085e0040c00c0954107100c140101d41c201500b040340e4140c1020180001c1400001c3c1080e400030340000c4010281144400040040d004120041d902d5800d1820100900c51f00040090003212001c80a00031050920700c1c4584038042181c1903004a0301000010300810101c2e019205034605c6450154030784007110038003010340c0d0040904551000c0e41c40303c045560f402c100181001400301818041c0c02c600c3c100c40010594400d1421810360003501090110170f0100400c00840c6142d8001d058a41303900d44808030015503070301c441d04d500c0589503240c00002d0740c0050702125030680c1c801507181032400480e9000e110392a40300c0c01420b00741c0c1d551b80e040040c060001c0d20246000702007154402d0303c040a480d00040c25114081c1c4400d100b03001d4540ca00d000100c80c228081e08528050765240360280461006407646100030b482d0340806400c000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 313582958 1250 313581708 313581713
    0x1008010c0f08060906030a02091902040f050301180c0b07051c030e07060906050d05090c0a03212f0a1205030403031b0206071209050f0d091e0e070e0d 66
    0x1e200d070001140c42c0e44001d030355591a070410603c0802a0b81c00384d0503401403249440542007550160742c0c0305030340d20502c41c4000c80d2100d0020490380180c0c01000e0700c000f03010050089181c2801403010480e2414440c0030094070300d45407000818102e1040c005c0003040095801d0421000b403203a003c2148001c1311400c4c11821242000d00608403501021440f40145039021591034001c5464409a68030303541c520303040451720003040f4002d0101415102e02c601c220b6103c04c80d9a07513001411005584101380010f000030366490384c058000410840c00c0207202038002c0f9641d0704442e05d255803083c8403030203c4c50480d0a84414039182004142c00f03000d802034207043e41246c5800d822a00440c0698030039a0300704880000301c3c1c9a400500308008071000142c000700d010901d02d0f0310035240840918000c6c034000402c5aa990348a920b003007590361a85007150825041075140d16040b554400081096842d014820001107400c0e00707103888117024130360000c40c8800104202d00d1260710010a4110080d00310410010f150 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 313584208 1250 313582958 313582967
    0x609030a090b040602060105061c0c180609120215040503030f04150801051e0a080d020109060609050108030409050a020720090601050f1605190c0801180c0306051008010c 75
    0x18100e0001040c0e00c0080082e904020004403422510301c2c0d4060042a424401089146e900440c0c40c2c0010001b800c4a401d505422446414001c900b192614000d1b10003068161030841e000e50b11590500042240400c0558840030410700c0c03c6504503002d00e86c2105000d02621035010f5500f100f40c05200c0454400001000d4200500943e004640c1c410b900070742e002404c0b42c1c000d4090107219044072084680c101c80c0080f05002d442e030110300070607100940d03403540300030307480c1c441c00304a9a00143e440e055490b050046500c6088003410201c2028022581800081d940c0d23403166105094500355100d0000705038110641c19a0701c80c55001c4642c2c075026a4400d40d0f000100d00c0a02d0f0644142500e9020800d258050310468041e840d94445050600e80d494004072105080c40b034060750180544a01c00d00400b41c072403d2940c3e42d074801c2c040c5030031082c1417009140c21200065800720350801c2081128000c1204c140185046179031100340030603980e41700700644d00b07508256480303800c0d25820401644002c0d03810 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 313585458 1250 313584208 313584217
    0xf010e03040815010b07060506030705031014060d0302060f0405030427051303081f080102070f03081305070b090f03010f0209130203100504111303050705010807051207030203090708060903 83
    0x10b9001c8400a8a0350502d91034440c20a11031034508100410808002038455002113912445c0142a1400665600003082c1400685007020b0001070f903420124030715420000007550070101c2036694040080306980d0295817460081e0051001030428400038003002010000c072005011790040c03202030018505690801e0001c00d541c10002d1a0914002815107981120520344990309903403015a0303604c03130181c980003031440d85042d05d4004800080220b01418240005c10003684518200185480b207400d006100d05000741480c011000d00403490000b090b40060b401d0207032045c2c0f54103103585031810030000e11140f40c440306060700f55090000c180e1080c40c0d10303400b0700401c0b0000d40f030180301050709004250407807100b00c881c100c60a102c1d9106102c542071070f610050342d045101261510f841c504140c02c0305280e07003a900032105944041428802540c1c01481c0039001041411300900700503c016640340707030050040a030002c01d680440046d00c090020000d0780c0040200c4d800b07407030039402d010b0402a1250310 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 313586708 1250 313585458 313585469
    0x40c0f03030f0f03051312030e030f070203010c0503011a0a21050912070c120807020d0c0f0506070503030f060303130605030108010e030406021f11031509071b0209090f010e0304 78
    0x399185040c910790007170156038400c0450724000b10310300c0c181c1d03910300121301c507400e004408050f580c0200c0424007000f04010f16035890b03104140354407541144105403c1da01e004031a802005002d00040010000002001164615229a00d61501500642145c18450404080b4519605448030369904511540040e000c1c29912041d114043c15041071144140300d907007030003808000707100003c006440d01224a401e0162086a0304c0340b8000ca0303a00001d980b40050401a40d00580f0110300300085500da48071000102000d603001d9050403415290140c884c04028045094042060002112a50305000701c60f1a041038205220034030b40c80b00d40040031a002401802010b601c0d00c000801030280000c19517080b40e03003982c001c18080c40081d01c4840d80007004d1440300c0c4c9070b41d2110380742d006898583c030246100312030340300030303400c03c03036282800c215035494041d2900051158180340e80303210a079040041a42160140c032401e1540d20303405005031805881035540300095213400c42c60b194240c3c2c00f00c001c208aa4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 313587958 1250 313586708 313586717
    0xb0309031e090901090b0105090108090f07080d1206060c1b0e070306030c12050601030314190302090942120a0507172a09070206071b0803040b040c0f03030f 69
    0x5e032030f40507200c02c50744108100717808542c0600012100d903100c1e10a0700d03440301c0700905450003003014000440c81c2540381e8101505a802a1102a8425a005d0155041c403984600240200741c501003024001900c03118000d48540150300c00b8074869899040c0d40d100a1004030805506031604420040060429000859841d00c4000700007d940d40850301d944000b07504400a011240d00e143e505996001c150810455120414070004000908000703146000422540b00541e031012194100500610001c00010320003081840510150307864403216400500704500065008524550f40c1c40c01030020070a042e809180c296805170070324070206a030070f80304e0311442c201e80700151189038620314560744941c40c40450380a00751044124036181c2551102c1d12001c95080c0c000f442d804081910844100d40c0000541c2c440c07814800625800354040c42c045255807042c0b10b0402c402d5480c80c0981c400076001500702e070b00c0c00000c502031281c01b804d19002000220100d1000b2542c2c0d00e030180005100150f40720114 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 313589208 1250 313587958 313587961
    0xa0c0807051f06210b070e1c0602040f091b0302030903070204020f0403020f1c020d020a0801090c15050903120721020a05161d0a02040902040905011802040803040b0309031e0909 78
    0x3180325558002085c0d04c18401000d0350764210341110b0206aa5402550080305410320406d9160107020503040a03000300400340e070b224200740d018401000a40d2100c1c202e41c0c82e01c5c514401c1180d0000d81340c0d0b02c0c0442840d02503640d03199003004610750f00900b4000307580070b071000036030300b162040d54001801101e10070350307505840011038402c0148a42004000001c1030794420b50302c40040c50007034202980d561004006410711500d0b191b4890858451900c00c031400703501c0c25424002000801c0780560418800d160136898107001101107500d0701c114079207002e2034410102e050b404204400102c0311001500c0a0030104099682000940d90030540300183e40074092001c001c03030008850032000c0203468800750400318080c1c03200e101c00c0b04008000c01002250390300340310100301500980000d000400c101080401c5950501088402504901c002d04800510400041149140110a40b0125a00302c03000c1c6840f0360700c4a000608501c200340e5444191014080360858000f00c580c05012410b01c103403804081c6 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 313590458 1250 313589208 313589249
    0xc040c02160312020304090203040b04110a05030706050c0705060a050307030b1804140a08040f03021203031611070302031504030e0a0303080117070e01030b06150a0c0807051f06 78
    0xc071040a400ca0100c604441000d002040ca010900d40c0032124a1049038030305991001110101c1c0c03c1a0b40c120364480c004001d0006000401c40d100140d110200c450200d010b1400300029900c80040c400d6000713001c0042210032200c0380038001e940c0200b0000d030800d0f50360118190000c1090788100c0c0d140340424508020701e0141d0800241030320140c00101c2d011145030300c0790f0b210741014a40507074401880d403040704030f66000100c00c42c0140000740030801c1d00320360031030461040010926070300c450054264000e0042088005655001c400c00c20150f0401c15240315614014500349100d5400c0a9014801e0182080c0113038040f2000a01c2a80266511a1080142020055095158400900003407151001400340904452103e81d155004000300d0307034020340c0e40d00d032a481000d099105880b40140101004aa03040050224405580442c111894003820000c060701c015514003001d85010404030b111000c10800b001070108011462904109190300c0b841c441020b004a03000b41203400745000c944148 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 313591708 1250 313590458 313590463
    0x50a050307030f1d090c0d0e0d02010b040b030c01080c0705030f0306100f020604082b050a0b03030c0d0c0c21030e04090809060706090c030f0c051c12140c0c040c02 72
    0x603402c044040701d90441300d116080190245d03000d000c0021030002041110200c0d1290301c20071120310901000f500a9600b8840c0180c00c481e039640c0c206002d00e0600a02d0507150303401040b002c107403c00900704503410b601d0310200c000302809a200001c18070b02c070010715100b80d984514091846400201c03400b050030500f005044400220b14856240980e1210001c80d0000301e51f1405800000d464006a0140705d6048080808415542c140381405960b10340902c101c0c140240141c1002003000d6008500e41b011541e03103981c2d07a003810941c07103080040a1404204215645034a980144010141c50140c20104d55404001d408601000c4021a4140e1200703c0203003003500500f44800d400ca1020345c20b0200c041c0c180405a802003000302d60300c1d83d48031800c1c03000078800c4d4621809140690065032110f03120349032480c01c8141c1c542040c0e101c0d00d103031406519960b040c401c0180189a01c0041400c0840208070b040c2c1d21403181205161000a01183c011003881c03001a101c3c00d20a000c4405105400c4003090598 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 313592958 1250 313591708 313591727
    0x5060d050303070809190c031509020907050a030f0c0e090117030418060b31050a090f0920130c020c2b0b04020310061809030309050a050307030f 64
    0x812a8000348009032000e8000e50507a03505c00e900c14262000014052008000c1d198000801c549104240500740280a055502e840010080803010425100e4540020321449401088103040010004440780741c1071294100142d000c1d48440c042c481800d0078900980070450b29900c00b80240c0c101000011050840020318021514140c0a03518050030300d061321051505101007815826103888000a00f80000d40040480300e080c45816590042d00b82e07850030303c859210450100484040b6014052551500e412078100c90b40c2100000f1380101c030b007507010003904500b00043c084d00c509518a4443e90b84034066030b19501c008588002008a400c14501d0440700710291443c0103a001411001c00790402c0300301d0b2210001d448444040b02c030400751100d070b086040703110112903001600781400118201040b400040381c0c1d00400c10f0003030b03a0034503115403140003076a00e07203040b129100c4003e401418000c5d070210320850b40200c10350308000d2950406c1c90f640d502540c0e084002400603100c000840c0d21074111107 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 313594208 1250 313592958 313592963
    0x1050c030a0c020a05160f060e0604050105030601110d03020c0c0406120b040c0e07050702011b02030619090b310309050d06020903030703110d0512131a1905060d 71
    0x3415a00c58a50301c200a000302e0142c9030a51190302090380200b44c081004190700080c04200c5e1101ca400c01da50750302001c5a03070713101c441802641c2603a10695a0703070301c0580d4251031080c81d215849582c1d0340c0040316050744444940d00c01d80100035500305102d1b410340050408031401011102e2910311300d0184400c403041ca100c4c6007241c401048449002411074195250498088d90b41c1c550019180c1190119224007a1070420104000103a40c20840d40c0001240603460089242c031181030b145500801d4541e00010241040101c2d03081c1000e0f180c003104d500580b111500144d0071480303440c2440c0c613045001221003603a4031003100c4035407541034160040d482440a50b0b055a500100c030740f910f410700c0740440945c202280c0c02038090100c003005450400240601500980e50500c020900041140c00c011100b40000c081040c10400343e85848140038030503403c41010a50440102500e060440d0680030061084030300e40004070500a0014100d1140080003a000030108039607140c403405c10030080d103080d600 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 313595458 1250 313594208 313594231
    0xc03061003081e070804080601031e0b07030917040303050d0f0915110405180f09010b0d0201051804061d010e040f03080714030901090b060604122402031005030d020105 74
    0x6400c0001d0b1000f030100c0340083d080207a00b4400799079681e42403038002d0f4200544543c040c0004005102c50f04a5620701c84164541009040740716840310790007603100422030018075464807039080c2046480c0481c2c801d1410000301c19070300d860300c92030020015800300c54032401050501941007503a2089209041c071341680060069440e0100502000c00b41c500c0da211528200d40c00e2000050300d46400c1c8440e0306070f80d4040140001407900c15000e2000210150045680303a1410131034801c87d40f03c4090300180030350242000d075181c824906040349084a200d22443d0440d04010703000a03a41480302080622a849403810001a0f07200d1007c04110501140d01410064914102c40040390255540d1a0031540500d80894100c4c41007c030498242d2040d50420070726951207480005018120000326002982102d200d81b0309823807c1d64258003141c621102801c02d560f01030340401ea9504200e145801e01c002004d0035516441c2900c1c482d030f08100d6500c140d41c041e024880415020798418860244100d4641c0d04 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 313596708 1250 313595458 313595467
    0x301020c03090d42050405060606070204020409060605071709010503040b090a2307080f06010e09190302011a010804030c12050403060f050105010f170f1b0a020c0306100308 76
    0x200001c0315594041600c0007080d40c60f49510f00e404040f09842c1104c00400c4044020200b00000c40c41100310a15a1002d42c0ca44010b100000d000410060342000c0125540345c1caa202c41e00020300240f0840d070012040c50315103400056041d412802601e0390b0360045440b480440e04820a4240e24440c1322407150002e08200006400641a040c0494001641d4403c035414042d10780c2c0d800403680c0076417110038854001858840303600981000f510b0042c046101c054008032030780c40f44d541c2c1d403690103000740c2c80c10742d680000050844108000c03281c80002c80b0041d14140c0306130380c1000b07402000c05a468803103008520300410019400381701c0035400381e903040d81c92442c800f07980e48910010200518076181005401c100000101c1e4a0b4001d800d04140100000109035160000160920910000c2070742849200e920081200e0807013401c4a50052507140790300c1440d90b6050300440b070035070720040f1030701d00d01f5020940d000c10680c005010303000b1001c1541103800720b8450501c101183c04041c030004092610400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 313597958 1250 313596708 313596727
    0x6041a070f0602070303060512190b131a0109050a0b0d0312020d020f030603010b040605060f0903070f08060a0b0105180d0203210c010f02090612060a1814060301020c03 74
    0x40141038050080c91011007400d002e07620b003420f90f40030301415400a516007409000700c1c0313000c029544209201c40010910440303499082c03208195030020140050804000046407040315a84400250303600895402103100400c0c8962280f000038024413108a10b00710006150011501c104c0105250041000701c100040395411650300107a100c00d110300300d80030b21051014000e1400a4203035454030b14801034492505c8418503084803850354001d4480ca090071400c0104c1e866a03003c681000b02c4001070249d41c2c0c002d08c030109103486600c2c1d00c2090011030490001981e490040340c02401541c2e126010f1085201c0d900044034540100308064120344000e240150309460880d482c4040180b024060301e0000c44032504050321101c0c01c2140414120001490304d0340c03900203214080d5241d182500441c00c4c101c00c000415001d0003100d0a0300402040c14011031070036960701008000412241417042030581d103a800700b40140600c0da04e64260903044101185103894180240d4508450388001941003a5810 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 313599208 1250 313597958 313598009
    0x13030807140d0f0e0301060509010509280c020c0306190e010f110c060108070e0f0702010e0f0313080a02061801110727020309070e0c0906070609030e0604 68
    0x264000c5640e580d030610101e110700420300002804500503254020300448003500038000c030204c00b184502c20b0b403406a05204903030b911151641940c005a50203101503403481d070078102e4054070040c014040b0200307a10000031034000342c1100b080001c00d9429900091044001c1c0b507920341060b900c0c0070020f44a01031301d421030310b801d501c040d0150100a001080382040103505008644082d10504d07011100000d040542210800c0036600612514004006551038000880351080014050300d01c020034143c0440d01c107a1003500f04600b80a11041580c12419500c540e541c1ea90344907641c0c0d003100e4550554000742002000c502d00d10780340d030003030181d92800036103aa600c1c50701d44803090382e117060040201d010032455070b0401c0240041c1040210f29490b0b03070400d815a0100e90403120f0102d0b14540100b00700004110041844806c65a00c03114900c000d0312080400c003005e0080144c0c1d1074006034007089070803d0080b41d4000c068014041e44484402d03588041c2484420301c21401103075203034004441e40c012100030a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 313600458 1250 313599208 313599217
    0x150e03041d240a0906080604050105071d0f0607021e09060a060503060f030114071107050409020f3001020414041112060f04020c150601030216030e04021207021c0302130308 76
    0x100b80702d8500da10f038813260049448942114240380d020004200812800340b051640003103980c00c1089842c0c85506c0498852412104854000c6c0e11100c0811900d865100c00e0b50b00140c6d00078084850312084041c50900030800b19a002d2081d901d11000c4ec00c41d0502008940940d80b06a450514540e2108140322140c41c1c0c502d850303901076590b1b00c5202d812600c003080c104d00880041d43d840301c200703da1500f01481c00c4659000300c0e20075890300c3e400c4001a0b03580b0041d00c4001200f610655a025400d03014025100c080c4880c50002c0102c02c06012800c250640c018030a881c105000c001d145001001800111075050081015070171081180d00385109581444640c03201c0004e1005c2007040c50400440c082e07800c10358180300c250f80b220096660720b103241c03141c1552244082ca001c509040c0f50304280500c800c8201e4001d03050281816071003034540c0300c0e60101d802d45200c1c458115a94288050000d6850341c088188130407940c00c0e140080d001c41c1c030030700858010421110800c0c0f00300742540c603074120781c0e0f00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 313601708 1250 313600458 313600531
    0x100e011b050a030f090914040209100b040f0501020609070b030f0c09060a17090606090a0b0411070305070308011a070b0621010507260c07150e03041d 66
    0x80840da0240010401c110000c1003d10a907a115466401e04401030005041904842403a90504242814681c4025200c43c0c2c06901261888199140d1404496010041d60083d142460001802140e012961041f960468a0a0b401c4584035a10b5000c0700382c0b506540c0c0151546a007081005c0744c10141e00440e41d80d003256000900a1070321110324005040c5174000c2075241d010500c100c1c40c10040582c00d40714a58440701100140c0060324118000815420004040d4200140c1c0ca50540300191180e5010b05400344041c0c0c006c5946540c4c13801c0250260308102c034218005070141c1d0010407282241c3c0c120101040b006a00c440c104140c035a02d004e10010010502070300105041c003001c3c00c6918041400007c100604000103580c10706000091000c030208801903002c54203902150000419200320513841010802c4040d04c0d21414a0164520b25204840d0508135041c40701c0143c00c40408030091049890010510921142e40318581988000803581000d16141104c254421304207443d0300c200302d809 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 313602958 1250 313601708 313601747
    0x140303041e0e010e0f24010f0e090f0405060c040609050609010302091c0c05220c090305031b010c140304030815060c06011e030f11010507080408010504050c100e01 72
    0x2511002c0035000044240d00c460010301e26182030003401841c000005800a001c80400d140507004003410b85084d108140c0c102c0c2c1005040c400c1030071b0080c0300302e0303203100e40290040103501c260170500c0f0220103108003501c00755254059040840c1c81c224980702100c0440750305482e078503100ca151000300b20240e0032400030300341455001c00c88106569a01d1415452500320f02e810b40e80da00c6076605284071701c00d010b900000d01820510081c400f114081c803450000702d10b901c2102091040a03200202c41070303c0c82d5031004195100202d0b008540000c4041c41da0039a4113010000c203d8884d840c5811a500440010f2480c0c0340e000400208000c28401c0c880c0c1369114040703000c011824000440400c0c0264044001c020341508a000180700000d101c46071505110140101944254215117445007010030702d4000410b9030084011080340361340203909031094580c00249040d1110360b40d0488170b02919040f0f4040380c80f4080c80c41052068a01410803210300304072a600c0b00401c070084001500d480b4090a070849210 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 313604208 1250 313602958 313603019
    0x1030308040b15060304141606050904020705030d090b0405010b01170c031807060903020310090c06050315040501141906050406030b0102011118010801080c010f0804140609061014030304 82
    0x1074840c4d20086000302e02c1000c1c950803041480c542c0303030f00b4880c010408901d8140c0e141010000c040d8402c0544501e4881160016034074019850300e5032844c4580055510540e082526040034442c5601132103125a000390002e0096440d9003004440f916480c8100c209014090804039031010760410295903c01c0d4030301d10109600f4410f074103941c0f41440c20342c0f04100041c2214070510071402c1c02e000750b4030000e000f10f00a1185045584d034031600542607001d0081000310120000f400c900000f40042d105950281080100f541c555544400c0207030601004c501030f4404c034404884001400c01340300111100fa0392018141820f09500b10080c180c41c61190b8110340d00c414014060400c01d4000f040040b82c590000503d03903640f4000548808816800045160440140b00c19180d8009046041d621000c2c0fa20b0b089555031440c0020340c00401398204d9080d84140300801c600f60703c00143c0580a420030700a41c19100d0364030301501180558076545250507820a1004000303501c3c02c4203035110310304c02e070074900705e03a1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 313605458 1250 313604208 313604251
    0x118090b0412030e12030901060e130209060112140f060306040f02100c020405100905011a031609150306090e2a12032214032505060a031b0801030308040b 68
    0x806401c0c203805c18521200005001c0114000d1141400400d2042820102481c214180b840e00d0821041d01070301605402c4001400c5a100f5403007070a1010406200700702c10110881e00e510a00003c070b0714030030b04180301c0c00450f89609c0c0c00180184034035407141c0c0d03100c0300da8620b509100c0141c403400a0601803080c900c152000503580d6010700d40c4580054609180e08074a880b506000740d6006030710100f200740310301d5052807109641e1000c032944082c4055104000b0b016a820442d040d440550240142240240d004001c807507142e04903000f1103031070b070200344000c5007007581c103d03110440d81c0c040d10103c00d40720f07d0381804070544154454016900030040c01c400ba406003003550031584110285028240c0301c0d0f08000d5a0b0000c0f5001c02d014011001145110b401403002080c0d0712258064070b440801c0a854006403a111030205d0303000031b0070b4041c0c0031503240c89400314050003404036183c40700005120f40658030300003032040e00054104e98040d074034100d035910f0303544810701302c002c0150482c4282081c0c207001c0c5c041c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 313606708 1250 313605458 313605463
    0xf0114031306060512010f050106140f09030a02060f0d1406030a0b0a1407020f120a09050d110a090c1b0506010b030705040e040321050106021f06030b0f0118090b0412030e 75
    0x1140185c00000704001c5031800c1d0b140e084880c1600401d0a11884080402649045d10252040c1641c0b03007144950f00d00285000074a04000b15500a41c0108005545c200c1f82c00111f0140c02003d400050912081e05000d5480f07240c481c080320210707010b50080c40c00e0000302c0c101140c02d40d00450850300000c2c1c1c40d12003035800b01c144501110300b080582d129402e001000c000c101301840010b5a920443e50501e0326401c00240290154070401c1e1040003500ca0708801d0001000e814002c001c0001c000b40107190b9910040e0b8040c0844402c1403000c110f0141032102d03d0039081130300411641c0d22034050f2405030300300007034031100d40c10103000c45040180030b000100d140c5e50552009401180242c80c0e41881b40004201d4491f032080701030850191508000042040a400182401c00355103440c0e501c0d0041c000900f4903100404496002400d034030300320001c0c0f02003c190416018166a5008045d40c1d105886074000c0b0250740282a005150044150010b0045401046015041030652a000c070780f58140407a42c91 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 313607958 1250 313606708 313606729
    0x60b0f090f1206240901050f1906030c02072102010c083c0a0905010e220501090b0909060714040b0711120f03090603330f01140313060605 61
    0xb210380c44501480380c0801070340880180b803c582111001000401e00204000200611402c0d01890101d40d00c001c0a946088800000c40016400c9a207900e0b5228001006008400b06203c094000c4410108424118003990401142042810280c025440c2c2c011650300d1101c10094800701424044150041035807002c07020b580c429034250424041c582600240311702c45001e00d540c1303907140030420301020b00d41201484080b41c6007420142d400030400700100700040c181440b0075a04501e40c040081402200b58401416500b00800803c49081d08100344400f141c2c094a80b481c040e40300b0400102c402c1d10801e040405001200c2c0c1c001d0400340e403412540890781202c0350460f0724408400c42c40e9801c2c00c0c80082140d0114165008240010101d04982d440c0d119140141d03008200000029800c00da8484112108104c500c1c5034151940c0640750a40006141044442c482c030500c41c0c1c03d89841d8460071030840f0580b00340a40714a5a1207121740d4240040901e030084460f04d448800024280e540d00ea07134072 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 313609208 1250 313607958 313607989
    0xc0b0901060816060801061d010c0201020309130e12121807030209070c030e0307180b04020c0610030302252306040f031e051507020c03060c041701060b0f090f 70
    0x83d01d207402c20030301a2a6001c16084041080034181180344806000342d94803002860a007410130075280c01c0c0c00100d01f9071141c41f04880c0c0141c100f80e602c6640c640ca81c0c0c0003881e5500c014081c0c80c0d070208289050300403440303103c0c0481d5407805210046011845614402080c81c0c140208035400b00741c1d00e5010511003a01140e4900201c0e10780d419081c107140e0041c058131070f040790031805030403550300700444030880200c9449807200d0140d0b580c4051600b9120b55044400c4500000c003200e0040c83e160007a210b048042e030100700c00600801c4e070f82160b403282015507030703108040303024a0000031410f050540d000c00b03005004190f0500c1c255040c07055540c4481c4010009407042c001d60250f07250550800506018215155441590402c000380300400c40100340c4690306806d1416500ca161a00c0d01c0c12464034000c2c0302c0040e814000c00060200403c05200100210303141d00381403224860088000324200c0c0c4071441090100d41c800c0215205480168000307028503800204441103001d074003800303d03e04c1803014000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 313610458 1250 313609208 313609243
    0x4090614090601020a171803060f01032a1404090605010e0709060521130818040e06100b031b030406151a0405060a030207050a11041b0c0b09010608 65
    0x503a400c0c182080000da1100c801c4c0000c00321051640e541c03031000401ea414034180244040303000070309401c43d420001c0d0440c000908448032410149102c00b6140401c1c07000719502c10b21400f109050b062005440c104c1503200c160003001d12890100d0152600604901040d4016a649000070000e030340e5200c0d181c080d00c81c03200b18907641d00c0c2c100f8001d080e010f02d5401800c00c1c4031003440142c003101580c0788034103400341d4440490362042e1541c100741c00541d4540080180b5410700807580101045502c400c520389100100e50074030a42d14070980c0d40351194020754020b0320703401500d031050200c0311882c0d00541d00980003c01c1c1079040d6203030744185800c40e08141d40c1102c04c00e4466071909100503107000340c0c3c400381820001f0400c12a0801644131581e114910800b801920f004c03951111841c001d60507070302031a03004402c0e51802c00340c1d443d18010b10609800d44602c11031603c0c0d00c1d407192a003500c19001483e42162901900301903191a42c004491008001580710f40d00d030080846c02881c14840d022000c441c6031103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 313611708 1250 313610458 313610489
    0x80d090605100602070f180b0d0303021312021f0e190906080303010b041a07080a180e090c0613030203070605030403021b0117060d06020c0c0109081204030b0705040906 74
    0x1801e240d00c810b5940401c0841d84003200c240301607454188170204036a5030012244420b01600c0350040601920405640d001c1d03403c151500c203050701a0000c2c916040c49009000e0040e8407421841b8181c04016006908100d03400f820007180c01c43c0703140c800040c510a060140d105c1c19010000ce120071001d0f0118070804d41000000c000c0035000d4080c00f0050b00c0400095402c40d070502c143c0304024001c510401400034103840e2101094400ca108852850f9000b10742d0320f50307441128101420b50380d1242c282c980d0710301040b1000280036041c40c6400e805042404064411814058200010f9800624907031010b0700307005000100581d010410400202100e40368036859140905000e800c01c50148042c003c80802c01c0c1d440021a80d200f9250100400c2c141e80842054aa40700070500c03200e81103074000c0045200148410503000001203042e070001d0709a854680311910742000030348038207400c03c100441c8130080c0000c0c0001002e90100700d0740124146891818507503a0807581080c0e4a06520040c030b0b05103440c1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 313612958 1250 313611708 313611721
    0x3191107061505150310030b0a0603150c05090d050708010204080105160f0c030309060f0e0c13090f0204091511070204060503030c150a0b0307031202061b07060504080d090605 77
    0x6404221486008030b6882c05140c600468507400d444202000d11001c000300103424203261180d140c01a5421020b554a140b6184e0217200040c55140015a841010b20b21141d114008038040d00140d001c907559860300300704002d01801000f4030700030001c4615000340a408208180244040c2c0000c0010100215580c01c06502d448219a82d11001404010480301009041a00440d0a10503190b00d0b150001d899005070070800d0041103126070300002d5500780800c000d8040b80000b0204052070f000c0365910310951503010030504881c1c01a50007041e101d480d0001b81c0140c40c081c0c0c80761441c6409412260b8603101c800c41418100c40ca82c0d030100a03105004108001035080c14401d0380c014010a4004525041c9a001c015a54850781032080540c07a00541c0050042031068004245a080160440c1c81e050b03203d2900b400300440001c1044018800c2c100018000201c440120140206c507440c031500d0561551a003a01514008100750350360300080001c2c03612002c1e5407207040c21030b50140c0c200042c0b078100503 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 313614208 1250 313612958 313612961
    0x4030602070b01050f06280314040b0f090c011d0d0804090203090d031a0d26120705070309060f14030f04020f010201020a020c040b0f0d1b050a0f0b0319110706 70
    0x11992031b009100900c140b454002c1904080c00241d901d501c81c2885007039007500d0840251070f49480007414505124240010001c2031610240581c0c0ea94842c816255030b80400c0703d07910700c0c600444a001030440b416039070020a0130061711207180700290007107111068903102d00c80594020741c044c030079250b8000200701024405005940e006411032a05005118200d0340405d071440c80f000080e8440c0c40d41401c20340402038000700502003072403610b4a030f18103000e0295003894140c100c1000348605c560b00100040441d8490703402c4035403840e41030700c841c182c45041c81d90407620100c00020f8401446541c0d03004440d00024031015511480e00c3d01c8012030245841d10500910380c0c400e020a50640e030041c4943c0c0c400580114280c10080070a941c0020503031400350000340c250700b40d86c002035040040c0c0740850701070000e00842c5404c4201502d0f08501295540e401344294000c41c0d01c074028040d0281141480f03a40c591360000e6400078240c0510400550011210100310742e039801d003102a00000042a504200da076 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 313615458 1250 313614208 313614229
    0xe07020a03031b0e010e0409050615010e03010507050f07050309061c0c020c1f170907080610030210030c0c1704050406050d050d0e01200105010314012d0204030602070b0105 76
    0x2200c10004211070169018243c086141d1380702d070511141482040346c0340c46642c0038080c0c050f006011550700341003062018041c40803103490580090350301c00519460303045c14015a13000b48140d6980914100380c2d10280c00d6180c11502040342d25000422040c9100d50b100000703003140c401800f440004000d062011b0100f16090040d00c01c6c250340201d442664195a000649402d046482c00351000403802c50108072081030f10a2102d0080109441c280510400c002036a0001d031840b0808507440c1e07441e03258600348045642d00c0000e41c0f0004030f640000c01c43c0d200390400304101c815428040c2d810442903680041c01800c02c4160203c00320301040070000e43c6002d0003031900034041510004942000c5484007515072100012501c140042809265280c0e40306184031a928a803801a80710740c5844c17803d03401c0c082c09007844181c440407450340128002c282d06105402c01152072200103032845041001c0d428038004490b41c103080e0076509200000203d0182c3c00240b001c42d228900c1c4811030b604003400c2060b030090 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 313616708 1250 313615458 313615481
    0x7050310140901060f02010b030a08070506010605070f0602090114070b0a060b09130b0102030708030a0204060e0f060306010309030516060506090702030702060a140d0f0209030d030c020a03050c070e07020a0303 92
    0x122180e19a00351140e00b07000303055600c2031400341003890041e2010b80c0540341c159500d6800d880b9841c20b080c14082c00902402e0403038811000d135606a681d4140032a414084d55002902c20320b01a04140e0024189500510442c0c0060414200d5111242c0010903a07800614003038a80047c0c41d000c2140074003139803113282c01500f000501e240c10404084082030f0079205c01c00ca00394040b95556450340250b03000300151241642e0150140b03942e481c1181010300650094802e00300070514032000c03051589440b510011a002001d007401d41166a4000110301610810300305405001c400c001007280240c540440101a60140d50017050714100f01c000d214420000901c42c0c1d085400600c4070f5801030303854408840305800c0c9460200301c43d44002000100910803404446074843c505a1214124036164004c1c190079000cc80030307240e0b241c1c01c1c1c0009a050703582b030150f12001600050790400000f40904047c20342100715102700d94507161540c6060451680c03e03140040980c1c880d03910402091380c10300a28441c00c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 313617958 1250 313616708 313616729
    0x5090709150e07081f0602030706050a06121b090b130b010908010509071d01150f050d09030c060c0905150a0c0c0602011e0221071701150905190905070504030b07050310 74
    0x1450406c0003510b80c0182079005018540f10380228140d114540c202101a003006820b00d8140959450701010360040300c00507040d07440c100c05000542d00310b2403103103400020340a04440e80d04160311882400030b00c1c2c0510440e0502400010200c2c62a0091080e2803107039441000030b21005060004050459600000c1d8181d1416040018440d41989034400c62010038982041070780102d856006076081d000d0040c8a00f0781c903281051032b10a01d5440340c24006124011501084003001c1c60404a0f551040f42c000e00ba0460194041c86000301c114400904d450703101c51411380c241d002d11f55030310020311080d94020310050b9182c00c0442003140741c80904080f03100080c0b00c11454014681c46c41c40d40c0c9100203402c0713a003ca92810004012a000c1c442e08003402c07402a51034029981c40c2e00420700f40c03502641400001030302100000c01c09080c24525541c00c080420b201181e23552800d070320030b40945002010f00b010002b0501c400800107001c00380c0307180511040d03210350780c0700e2078102c1541c034004046900c82c0d2440e0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 313619208 1250 313617958 313618021
    0x62601110d0c110604050a0b0f24030307060218040507020a03020a24020a111903090e040f0507180b10170c19020f0d020105090709150e0708 62
    0x44690000c840710348800060200e4080b11482d0291091104241c40d81c920b80910000c1000300a00858440c01951203045d02d5042c589604220340f480e00e5084074980c4442c50001e01c10850142c005040b501a200000c04032807410301c1d50b40d070b448241e8020701c031514410080e2454100c0c0510f018022030f41c3c0003109200425013041f1a450080da20500c01d80b016040d00e445040c3c03000010743d00741c1d02d843c100460b040151b664860080005006a0b40c0813030742000f50090807403001a541300940400d0050f900f50352030800040c1840c3c09402c802101030000c952140e44c1058070702c0026070034800c0f00018269104a41605407840c802e0a064a80300c00c01e55100e41d55008001d64415080390340ca0b030080c05101d110b426966a03c03510341d1602e2280b1711040c081307070307407544514681e182d4001401a400143c80043d0741d00e00c50900707810780c26603005840715103068122000c1070000200544c0180c0e8521520010010b8240d56880b8440c440c3c0ba040e00c070000050b5502040010b031001c40c000d4141c5508543e4400c0c0000c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 313620458 1250 313619208 313619231
    0x120a05070504051003080310030f03020a020415050310110403051204060305010902040e0a1d3007170c010605040f0606081501020304050f040b030d09062c01030b13062601 75
    0x613443c2e07010007041d041c000b0000c20315115004410b180959030042420b43c204030103080c081d680c1c49080004a100314100150241e16103030b024401d0080750380c041e00400c26100030341014400b411501c3e0290400705d07014030000012400402000501420311030784280e5840c1407403401810b940b0160010f0a580e0300400003000030345a00c269065001c2008880000c0e900c003128094806401210b21807201171098000404100c0184c01918101c00d0800d02c40e0420002032501d840350900031003001030642d101e0b5141400018040c0c0008003c40b02044d00009400c5440b8000a0111200041d00005441d03035200188940b642004c0c1003034000d144c0c0702c0042c2400d00c400300000e59a120b58098640202c12088104416403656089401c3e00300000302034443c80d00d00a070b4010000310681c461180010583d040a8050420803904082064080b04012114260000046d00540044c054481e001000101c10f070642e000f16202d410054404018850740e48407000c0b40d10801c148901d2402c81841c0d140030000e840 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 313621708 1250 313620458 313620481
    0xf04032109120f140309010e04050609010e1e010e01060801060315050f010903060608010e0d0c0512280305060a050a0e0f0402060912100f0e03030420120a0507050405 73
    0x403124101e40041c0400780c0ca10341000d0b00480684010105031820160001340d690120280ca68500c1c20b0341ca03000c005640c1e008000540303405039a0a80c02c6081d0600520404000c0e0043d9680304c11090b8411030b080c094040075603080c8c8000d81c4219000c4801d10018009681e009110360300500c0685001c0c080ca001e0194000c070251b1940c822113100e0310281d021062180d015640081c01140c00c090b04104c00c0d55924540c5002e042c01e1a0042c1860041c4000e509036031b4080d8000800440e008001070004921034141c1084d1507020451038001d14181e52a10301e5084aa4001d10102e010542d4010855007812000d00c00d00c0c8900360001841440c01c0802030000d841103160041e03004044240c0d58840f9112030020034260300c507010714a50040c43c03003a101c14100f200010303601c0d401d014106040000e1025072601a0443d04490780383e5109800400100b4040b820064415503050030303501c003a88903040048001031240d0502d100601c03c1d500402c2c003030410302109011800060000355001d01a9190814950304c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 313622958 1250 313621708 313621727
    0x7050f0307080709090f09020f01030618020a05190f0f0327020d0803040b040b0f01060905060d1d100e0c03190302030702032a030c01050d0f110f040321 67
    0x1e0420080c1c0002591042c4941070b280c00411449504000b0120980120f41c080c01c0fa51409034000c130390110341c903959548648104000c40311060718140d1155090081d65010354804a031100410400b40225000c00040c1141c18061008588941d03200c0580c0e0702307000e0400030900301c2200a0514000e411000002016200c0c091036658201c1d00c00d126040344000790100c102400050f1a640c0080104810042c45030007030b501039809888030050b595143e82c40d140d5900000d001d00c0c0002101280c0c104aa824120080d001301840b078a40424101d501c00c07809100040e00e008a03901c17a5000d982988805121031003240f85d06800303032005c2c10701c41c100d01020954032011090712500b13280000245ca000d052091041e242156401030036200805400b01d850381c425a4a00080189a0000a8403c105103800614003801e1001038541500b00748030f224610000301030940841c00f1503500da48494101c104540014008050098480b42d02c55040d403c00721b0302120080041410b0034000011180496004070991 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 313624208 1250 313622958 313622971
    0x140114130e0d021905030d110c1506100237051c0f030b0315100305060a0f180c03020d061d0714300109050d020c0907050f03 55
    0x51091082001040c16030300c448402010031441e14049509800000c50900d40c001c0c0780d40c0c02c6400b450000301310850840f0a4290041081d4020482c140b4402d1141e0441c0220031141917600d81800138000740300b0f003480c80140d107000407d411113003040303010310707020080ea03214001500c0101000302c032509858552010366103000301c0742c400c1c61884c0d64040c0d032480d40c003042e2140e03c0001d84e149410315900d03451902c2c0300f04282c100802c100e4021000414406c0c45400000b41005009205107000f2401a510f1401c0251150603044210f0704084085041044235500a03e0055800144101585c1c4514105c0310010190922169140380c0200401c0c1c2040005007983c0d0101e4801000319841c0ca04000200180d6448010a4121060410094130007061100484002164a0740080c90b5002001034200203c1103141590390400c0c4030300c0310841520301d8500c1001002e400011600029141c00740303031a880302d080e60016880300f4107111690401c42c0160760807651508000c0c0c24400031010414982c000140300 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 313625458 1250 313624208 313624229
    0x4060209030a05070602060108120304211e02060a110703080411040b040501060509280b1c1514100806040e011e09063204151b0f02011401 61
    0x2050003659082c000d12440d10742c4001100d4101d980d070840a5102ca00034400d100850103654000701010402e54100d0388615484004064058042d01f0390141183c1c83c10b01000c1081040640714080624607040d5522082d601d800410480c0f400030a082c060351900c0701001d0240e0b1081c0701c40d0000030b402c20046900154002014a000031200e804a401064002c042d25805804d08000290300c079000303002480e1101d81510029800b01da4480300e00da982c070300c02c01525500c481014007040840b54141c0684000494282d80050742004005900140d80e00001e0b0320001da1070081c0c04100c406910707e141c413000304042c0d8032160701d03620904014000b1070009100b58001c5840d480514480c0710294040d4001003440d201c00e00704010429600c40051206c07007400c4543d503243c40d800e40300640381007580011a5086800104000c042120050000d540280088404d00303070341c0f450384144016901039011202c03201a0351044560b41e007603000301803441810015065925080c010311305202141e8050f8150317400c0e180c2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 313626708 1250 313625458 313625467
    0x20105070213020910080403021501080c011202040f0906050a0e2a091002010b1311161403160314031003060e10052d0f040b190c0c0201180509040602 66
    0x80c10003e846881342c441d44c005131108075044001d400494850166010780d0860300c0f40c02074048041c010311000c1c01010340c03940c00304600c010503603c1407550044030700a0b50f401605241c3d4648803909040700907040402c41c1c5440d59012b1005040604200c4001c3c03c0d01d10f403c000604043c06400e80c0c2c045c1040030480885081140341c0c12200c0c0725000c88809200c0981550115000b04100034028540040c9591240030a0700036101050710502440c0724103440301c07440d245441d02c00040070081c0b1400c181c2c11102c2c2e8911001c000c02800061001d44202440301d19808040380c140e14004045000c150341e60a440c2c90140103104002a552400c5002c2d2540b040000a001c1d80075098289010450100003140ea0b061004002142030a0015241c012500c010f1039050715204c54400e001d070010481d00d2921b0011442c00146c0419240440c4c0d68004843c07400c040307440c408618082060b80c00028889020030303c00b005140442d41d2203440054850780070801300130f04901780400030700e81000c090000b8103000d8003c40c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 313627958 1250 313626708 313626739
    0x105090c0f060a090504090816050d120c0e1c02090412090b0307050304060b1912170901120f0b06040303020307030e03010e033f01030b06010503040b01030f0f05030a051c06030201050702 82
    0x18210b03a50350481d034511205509c2640307003079507a400b404006000054410510b240f444402402503100c0940e4a450310007840c2c404c041488110007140c1510661040c0d1120780b000561a5109881e0003140503111070010000c080002610001e0710380d00032103074001c0410030440c03940c0d0b00c2000c3c0d9401c15400200400e0740005000052122400c80c03455a80743c0d0240200000c10f08181601c240d9000c1c450140090b8a0b1242c0040f0901c3d0300a070080ea07400702c2c0c20400400c0002000c0e611111040d10490000101c0507201c01c0421582d80054200b1000350740009a103a080c960868111054508210300a01035041000c403a1030700c030300414003600804c0c100080d035807030072442514040c00f90021518403074004400c040141504d8200070700c015039440707011002050300781d4410811a071103280c0004030200642d10396a03603400084903003c003c1d5604100754100d080010fa0034801040707054a155911500c0f0724504071040f010000850440040b28a8441c0420050f42c20405035082d02d9011180040c0f14280c14 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 313629208 1250 313627958 313627973
    0x304031703040f050f07060210091e15020a08040204050603070b0d020711130204030b0c03010e1503030904090308100611060103060c050706020c071d09100c020c030105090c0f060a09050409 83
    0x54000404d00e01514401150001000840d241180d030103908a580040c0008003c2c41122601c5502070226040f100d00030801d00728060b1071203646071181117009003c040c817081141c201d820142d0302100240e00c1c407007440250300d014001d041d00003804a000d003004901d0680320b40c0a600c28010030110316a00070840400340001c11008564540018111500068440c080e4100a600c1408100c460780100b80c04a4179210228003541c2c10303501e400e003042c6181c0e1503400c40d0560043c500d44e040b65042c402000542850385031400342802e801e101e40c44180c41c0f414030f0300d04080100d2241c1c001e00c0411007482005001c51400162050440341c0013840081c104851250440d820b100b0b07500090051800041c98003944540001c0c1141101c444800d58050120007130742c1e200c0c0707440c0152440342c0f5603405090010701e82e01d1300d40d2003051944250300407202800c0440e000700742034441c1210304034104c0c0c11944560ae080c1c107188120b0300300664200c803814900106c0c1400940440c00d00d010302800b40d581c43c9041c908101c2c40 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 313630458 1250 313629208 313629233
    0x6090601062123090d02070618082d01020702032503080f0409110c0a1209170a0204060e0601020703030f090e0406050901060b041523030c040611030403170304 70
    0x69000e210740200703068211426543d12030820f140c10a900002000030b400451125201300c01a40648142441c0841c100d42800743c54040350081c43c107450000558603000c00800032200c007010300049070000d6040314001c4070720071441862516401000000c0042e0740100e00000e923070301c10800341020303110b82da000701034070360001e400040082c030700003545403130011740304018004035003400005000c1829a05604a001e000d914509225079000d81e01044c00a01c00040500c04400b552078a185065a070306695802042082591782658001e2403070380041d414a40208000b0b05609410b91150b8104070b00000d6903501c20344800780410084022010007940b00300e0100f0001c2c90041c00074001e0381814140000140b0054514240c1c2d50310707043c00040c0f281020b000791000c03120a101000c104143c03a59054861201a0355200e0310384010965412100040d40d020b58041d03401e40c043c0300d0722075040045c050418200d110814505500074001000091250210342e10100410341d075442c0c503a00d4515200018262 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 313631708 1250 313630458 313630517
    0x9030106030f050d030c0e0111011e020c0601080303040812040f06110306010e0f220e0d2708100f020903011407090909050606010e06130909020405090609060106 71
    0xa140c40003003030020108085001500500995a1400c1d1018040d4201d81c069040c0102203500320250940340d41c010007103112029004400032580800391611030054440008503560001e40c01b2071a008d401d10b04100490140072254011890340c286515082c025001e401030200c00c848040000070204901114946100c13a4072031030a11018007401e051001c0354004a40403400200010025080c1d85003400c1c864a80107406442c0f41001240d014038601c90f1520a04c10420340c3e51100706154101a080041c43c03151051307a5640d950480400901d00400b041e80c0641d040d0080200105200401002c160700e8400d004020300007990300407078020b180c003a01035507a82030303415403800d03042024105941604500c111241d03503820360155140d0b031311042198038a240241c61030344208000348081d4000c0300c8030101d4000003400c0e641007061002860104021781e801200b0342e50340750680d5100718185070007456000074180025142a01e8180700440d96500d0520926003000390620040a070a1003c2e41d81c0b416248 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 313632958 1250 313631708 313631711
    0x51e0f0705281a0405150a41071707030905010e04060b070f02040507110c04050606190e01020616210b060403080903060702010b0a1403150f100e010b040303050708090301 75
    0x303c0f420501c8a1900180300c0c107805400c4a00403e08400720701001c50301c40c401251240c0c231014031b4140303418a40c908003c41c070300d9507050403005000305000c00d12900b05042c00103503005a0350316102d260561248150011000e03400c1002c3c000000040e4002804000b562000e00e0300300406031104000030041c200c1c980c401186000000f48071014400d8885801c0503043c0299828081e6407607400341100e0b008840c0083d040f07103400c581000d5149140c1500080e8000100a120074207000a108280701c1030080c0c540c01c071001c14026180140c2c07030f580502c1250b602c0303201058094444008450054400c0c81c424481002c100c0240007065901d080710741c000c1d81c180780d0141520f80c540b1788901d4524544da00012000388648100d6000ad15002c0c07050107415048100504100005440c2480c1c00c2203000251070b4266140c022282e5910f010144001003e22400c580000341c4040c1c18040f80e40c0310108007541104d11010425801440544c507040200d6007201e0f414074081c0d980d0001800e0017401806442101503055 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 313634208 1250 313632958 313632989
    0x901140103060c110304061b0203070801020307170906070807081003050f0a1703060d0f060f180308070807080705071b080a0314070b1303030207051e0f070528 70
    0x418581e0207076070290708584410070b10313244280115689000700d11602e000100300700410491110021200d070101e070b2020b021204d4494a0b00c01950990300100c1d4000d00242c2c0d8001200302c3c91904003000c0740c00c0b4511401902d15420403010080220200400400c18043d4180102d22003030380c031144010003581c00005865800700b80e030030010b17110581e004d0700344e50000701084039100b24460b21080340d001e144010009011581c070b680c0c0700b1150342405941035500c4e40d82e4003401080d112a5002c0c40013030100300414009800d0041ca005084582c025002104204a0004106a845d00080f10942180050401c031b034840206142481400c581d0000311240301c611000d0004611000040c0d0b17084c194802c0c2c46107108030104001e800020b00440070302a101198040100c3c458010041b80e4540d00e6020740340152600000d41c49151030f01d29200201024400410390815000e0300910040016080038409040309611703103c00540c6180d81003074526600a021146000c8880a1402103002031400e00c001c240103 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 313635458 1250 313634208 313634213
    0x71116030c1502070503100e15010906030b070c0b010302010818120d050112080403020f040608030a0c050f0106030506150a0f09020904060510080f09160b030412090612050901140103 80
    0x8403441d4401d145440840b140d00c007904600101d02038013030702c1000d00140441c0c12170300d082c00043d101c998002301003802214024180086041491806840d4414010800510f180707000c281c0d01000604207020481d1a80c100000140e04006180c1125024604400340d501c0f8004803001e07003d8070501210452056080ea80e180031000b41c0580802d5803000420081680d0f208150003001c5900f071401003c6400c10881400145040c1389018403c80001c3c1c000240c1c552501c2a46166034081c0c18890b0100702c1510f84c0400308001005040c01c0c0c056508002c4c00a1451139442913981d0002510380e503503884aa041401550b1030705a020b5000b040c426025803003041d82d9103d424020b510902d5810b02031400c243c004901824015024591800c880c0e640110650395540c0b001100b49015261800d503014025403020741c14003c800400c060004e15141942d2414945007001040c110790780ca400c03d00c604071204214090f00318268608420360108003003850b03030790013102c10300404801000d03008403840000040305 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 313636708 1250 313635458 313635473
    0xc0507260a0e0319020102100c02030904060e060405061207090b060f030f0106090807030c12032c04050a140121021008040218010b03010504020904060906060305190b060307111603 79
    0x10b0b991041e0700b5590319580b80b000c5228224031249000e405644940c0c2104049105a07001e5200c015083c81038034100326905001505507100d40d401882c1210380c40c020300179035103454421541c119100311074111255000a018540700c0140b4455524070581d941e00c20010b58880d4021101c02000c061015641d80c07801c0c4001401121003030107071074006502c800021508800005920003940c8d08802c41c19101803400c0030302c04209015010850401803501580b08400c1c004500b6a007030781c60402d20b4030401c03202c014144012108014010300103241840a002454081039114034199401d8800301e5842c00106003103088010aa014000c0d000640c490900700f0032030b4083d0403503004034070803201c0c110001d04201d00001752000a014003041d5400801c010007040ca49a40100b0113158050400b10300b1560302c42c0c00f182120f0b429400324001ca41c0302d400300100310100b01d8141d2a82080c501d0204a0a402000410f80c00e0000800420074001e203011003120600080040080d4850400e00c14141c054403850f1922 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 313637958 1250 313636708 313636727
    0x10141b03030405071202060d0b0f120606150909150a170102120f060108220501020309060a0608073212150943090b0f040c0507260a 58
    0x103e40b402690408a11145540100e207061500141801d0034114500c1000c03000700304050a10380e01c283c400303500074810b49075480c0a240791003a071006480d00c1c0c50800c0c20b0040d804c00218030300080f42010400003460359203007200b96802c203d9601201140010304000b00c0c1c01841e80d0340007072413071200c0101e0104030540150003d240e9141491140030300703520356000e91075031a801558828045012000014044603184002d11103c40009440d103c4078004c1c0d0315031a0032a44103460100d00b03074001c0001c01140c510240502801480c01e4030080c0001403608180080d503040c1c1c160003000c44a40c000c2c3c540140108040b116015900040244500100c41c1130840e540b1075002d50b01a1000c05648009050707914013081458103800303c40e0003c4851140360311482d0040300f04910007072481c2504500d80003400c0400c130500020b8040c0440010b41c000d031010420140c40e10300c0c0511803040d403c000103411055800f800f55889554040d0240d184c00e00e1103d23a0041c502003424425251220109544c0035080d401580030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 313639208 1250 313637958 313637963
    0xc060f09041116120315030f0219030b0703050403120204060302070c1410030e071703040e09031e0a0215070315080106141011031201140307030210141b030304 70
    0x422070414020301d0344040c3d0007840615100c050070005a0340c0425103501d5043c000703001514000070240380130841100c0b405007941060b00c04508041d014800c5082030840412001c4020b035200075068510390f0b9102800030010700e12820140c45001007001c141c0640d06541215109081c15034032a915094014029000f89105031440403500c0400500c036000e11580542c00800070b8024018030100351400e41c040e002082030580e061180820004031a100c1003e602d10052104024554403440c10a6840106501521501480d04204982620004084880e5090401d4940c40315100e41d001070042c0d0030510064100f49003501004d00304070038683d155206580311900a400018040e464005007800c80f511402007050740d0f0380e40100b1049620f02440315a003280761a00d0182c180c0c1302d55102e0641142c00640b0544540e0b01c8902c01803111105400f40b4200010080e002412000d1071a00003071404108000c80c0030501031520f00c05c44400888108690300c800084a441e4410042c840c1c0d40f035035941c01120705 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 313640458 1250 313639208 313639211
    0x20712141e1207080d050103030905030f0d09050904060f0f02090102072c0405160902070c23120c0d080c0d050304171326010b010c030504170c060f0904 67
    0x41c5403a4445400c003109030007075080300030620800e0440c14006164094041510421000d102c907001c0a1000c1c05918041c40c880e688080c411803426003810b00e8018101c1c152400794003c0402c40c805140d00444a00c110761003200c0c08441c1b901c881c02c1040c021301c1d01b8040003042d1402d04c00b0351010303951280c0080280c1c4500ba4201c6240d6551060f080d9100d104c400c1038850496640c030a00d10f60b448215101d250445c1c0200f040d40c0c14242c1d18042c20f4a0048507501c513140b42c0b600400d0b6402404201c40200009050300310060042002f10440200d10740c08030310341c1074030071015501344202a50b03003000160309461010388050f143d054281410b010035044040d112980f80300c0d202040495600c18000c0e240521385c072011010180719440f2514815401c900424000b14140320320000718290403102030b0503001c2c0e50581c0d01000c05245c0d404a030960301c041078020b041c000040392402c0041d9214003141d08036000025868180e004c5040c09508042804200551103040030886a40720301844000300a8503604031030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 313641708 1250 313640458 313640473
    0x4050c010302040b041203090e090c09010b0f03070804060204091a13020c070b070609080d021210060f0c02030c181f0b0f07020312030c04050102010f05060303071202071214 76
    0x440036071090340294070300482c0a05c41003001c40c0d054468980711500c0385c10212401c58544000b060304480c12581950640d2101140c6610390404171441e03030141c618003080c145400c1d81c1906040c49484054a08404c104840000909110130b95068ac0c0103002c10007018409505624000e41078003445040d5140304200c40d00c03542107e00c071a0310885120000b180d002d1315040e458400c2c954026044440259411516000030000195422004000408020100507100c4c0044d80206020440c004e290040700c2c00721100501a05403c140154142505407a11070041c0e122440404e0a088030901c0068010603804906030209800c4074040d44200241c83c0581d80d00140c0860407001480c0c01e110742e480030101008078104a181c030000034800c0c0d82c005001c81700000d81c88003d04281d82d20807143c10790840000309050089680c2070084030f501444003401407005092103000251684a0244001e02102000c009010300e54000d01c8a0f0009299441703c1c1b195420316810a031400030324440841c0b80d940100304 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 313642958 1250 313641708 313641733
    0x6030212010b030705060c01110d060311100e0f0a0905070302251214190e040b0420030601020a050105070f0f05030405071401120207080703020c012a060e06040303050405 75
    0x1c41c0d42d00c5000700400600d0968500418030180d6031110b02c0b800060f54a920300080c411a100c40280103807c04003800084552030360401124001101001a126a0407440030394442603101c405034152460440c2e8190300502501d00145550b502d550081f00300c40d0410f010807410b0390305980a1704400c00000240f0350301d0780e103a41d901c240d4084514001410030b5117504100e6001442514003040f0075002c3c4207910318020144180054080300700904000044031040c0349400d5003850b010341c041c000010740e8103011150b845003a0000881e040b40d200d0810040c04400940d840e1310800c58003040c0d50300030b8001c0040d400d044000605a00d0035540c2d01020801b16420a02c1c0c1d9486002180c3c0300750b0704600030784601420901c403c5019491203078054100644500025100b04951005002c85886000d249a6505603440e000e0300b40751503100f071036041c4200300c810b4102030003100005c0312541c807031101e80c1203080c012481c102d801881c6003401c590300c0344140c50030842016015841342d8003c03401007040380c03109100320 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 313644208 1250 313642958 313642961
    0x60409050f240f0103060b0f0d05061b180607030203120406050f010b04120605060103060512010510050102070302101b170a080c0a0e010e031011030114061204020607031701090603021201 82
    0x283e0311101c10071070210040000c203010380c0c407071019120020103501240c1406c00000c1c0c800340c051481075407182c01070810300c0361010501c5100c80380c14018807505418a00744003150745400a2708144903014120008441040500c01d20487c3c2c03480c020700038046201e0a1a051640017402d04036a40310b1400049000840d00030841c500b5902200c400d100c50f9181020203603200d601810000d0400d0b4103140e102c001c003081c103075204100d0380c0e0038802c2d0800019203440c01d007003582e051150540c021415034200070421b02c0582c441603c4102c2d22589c6007480d584240d041005603503405140b840141404c0319000500c1404680240180b505000968a01d811900c4842c2001c0e03881c8a58031051012031583d0000040c1940030300c1c10f81d01001001011358902250100b03c0400340d0b0f441000c0d00000000c000014011110f410b110080241e00030707111142000458680320000e00e00142002e0722526000c5081000c01d442009007860002c82e180c40000e9a50f52a8100c901038101d9000482c8103005586a000807980c05 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 313645458 1250 313644208 313644211
    0x11010b010314011815122003060c030405032b050601081909020102010e10020301150503060d030e060c010c0206091002120403032003040b01031a090d08060409050f24 73
    0x440180041591034021130b07504066181c8030440b20251500c5880406250a400c1c080050080340001203498000c0c0c909001c4810200d0b10115160102c02201c0d5129100082c03d00d41c000c04040700300b81d81e615941081403460080c0c80007940c10a80c008400c040c2c820080b20600f03101c0003550b40034042c0c0d4941c07400644091400f241d000300c0300c0c5070030f00e1000802145504001d000500600000400f1007455040500f0019580c00d01c403405074000004012144003140000c58090442c90424211f0030326000050400301d0307492010f01042003e020f4002283ea4045c112400b841e017160081088d5040c044020b07403035141c01c441001140c0284215240e000c0d500b4000c840b10010390fa00b03801c0e4a0360301c40c2d40540c000e080c010b403400606000d0b20342541110f02003c0085008a01540503148c10750303d9440c1c083c80c0314120000d950f00c168020310501c03050700000120300e000414036080040f055a5417902103001441420340c0034066218400071004482d00206031031710206401200b403030130400666844150b42c1710 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 313646708 1250 313645458 313645481
    0x228150507082805040c030b06120607050306041103070206190c0c1401060e101404140406110f070c0e0606070f0618021002010b030d0f0905010809010908030711010b0103 75
    0x1107000019903c945408140f844419035140000220014000380011101c00300c85c01c455400700c1e503500380b00307121a0300c40450740315208807060160305182400e0301d03881d40d802606880c14020040085071446d600c0383c2001da03c7c00c815810490b12444c082c4002503441c1401d841c0c0e81688102c410700d1508008142c0643e249400041c1c0326189000c030784e650ac180c20a221605500c0c0503560f0b40d800420340d001002802801203003900942e607019420514000846842c05407410b21135850440f4183c00c103040715500940c02900b1050020f000070360b914000e005482081400079400380700003152020420395003208400c0d41c0c1c2032603c840b46540c40c5801d002240c420381102078000801030040800040c1d007078011000f0070417400010380d80d404866022440103803030000a000503075107520360030149003401c00030540035014a1501c51240c3d001080041c200c00c1060060b141001008400503094101c00d40044640ba42d001441035a2450190001410038003032501210565003000308504040d0300c00d0003002d10061 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 313647958 1250 313646708 313646717
    0x10905191802040801050118050718030f0303060510030603050c0330070206040609031a040c060311090901030506100f06021c020f07030302010c11060c07120228150507 74
    0x2400c11240c0780d01c481c400c101c00c0c24520303001c00002c100b50340c00380a10f07802001003060b40140000d40001010a48200078900d1007080004110b000100040300890f008881c1c001e00d04c0c00c09440f8604044003e800c00703800081c0c1202c0408220302006030b16034803000880e4002c82c1614580d111340410141c0b51302c215506042c0c0c201d000d072180048907111a070000480103403003404500d440d00e5a404695240c000d9071003400800e030030000400a001c0128081c5401000c0140c1007120382c9410390320300050304440e000c0c080805a8542c074541d8850b03110743c05c4410410b402411020107682d2403800382d5030307154100e6841e00394660294000500349955015542071302c4c400c0d005401c640181015401c07404030107591a104512405852038880135081c8111400fa50281d400801c40340750740c90700a003120000035042d50840c0d1040041050041e90036003030b40c100da680076503880b0000564280480c60500d14034a280e02c00c1c203e000c183d252040308240d0080b0310f14890039005a10141810351401100d0301250301c0000301c1d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 313649208 1250 313647958 313648009
    0xc05011415030f07350d050a030605030c0d0b0c070b01181803081b21091b0d06150f120308060603040210120e0f010f0608060702030a0c0501090818010905 68
    0x25181000032000d103000620043d03860021400d07076900c1c2211b40000f00c400319800065880707481e0b48c10f00500c2c02900040c0d0007805441201d0022880001490901418045110003c01c03004040724049a000ca40c01084004040d42c40c1c2d14810006031400c20490140c0c0c1c0381c00524004500810b95800710b164042e115124190f40c6e000c000c0c04941300e880c0c501d9034209000c11030f0018203409441d18a901d0321130954130151501d48086494030b4400c4c41e2040c03070b040c010400d03426084c0ea43c500341103e82e0300764070450101d0796040c8880d01516103c82c640004511544030070004c20940100e44031403054601980e01d480490b02c44205003e1684410b40c1c0294108001ca00d5a5142c107001d00382c0c031024682001c000103009554102804c1c1019603403800c031411a5100c0204822140b21805810080c02d2a50f01030100c44c2001c0402941d20310811306c908040c010b100030140d00740305082d8850301c0c400390000d803481d642d14006034441e031900c8001841c9501050580d28041040c0c1000011807412810b08482c1c00c200 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 313650458 1250 313649208 313649249
    0xa210c200304051005120c16030e06090418030215040b010506090f0a06020a05120406020309010809030d021813060e13060b0d080c06070806030601060c05011415030f07 74
    0x20802105285009448200b000145685680c40005000e80c41943c174251152000304181c0c1030308101800d2640641030901050301c0c2c407042c4400c02200d180e454100481c414000340040340881c02240041c0e58810310f4050030355820b40184400015181c446e0382950a406402c0c2c2d0005102401500e020b0020900440140f1443c01c10b030380140400c500061000e1070010307000000805082054000800580000b0030314001c00c80708001c150b4940e07200140032030501c0e0500038000d580b4055521100e0401c50440c000c40c2c010b250520031100700741c102c1c9009543e038107418010041604140502140074004200844a221580348a00e8058810540300c0d21002e48411450ba80b4450030f00c07100340c070110341e036141c03186403030f1b40f52202070304080d01c02c041003503c604544100070700b080d900030a014140044c02c004c101b5681c0c2c02040190540d5a9400c0c275001042c5c0d2410700d5401000f0682842a0060072a07090100c90903d82c01c0040c400c12003202120180d0849000c3c0580710215807084c8200030001e094003415 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 313651708 1250 313650458 313650497
    0x15030c28151b020609090a1d010b031b0a03060f15050102010c120b01050f04082103070c120c080d0504050d0929090a06030b1804020f040c03110a210c 66
    0x400c1c1c00244100d05054505000941c09001925800502a0380307c801842300c0d40d20000c82030300e00d00210020800c140c00d80b00800d4070348403003000241e0030014140c20010255a10b6104901468004100f0064002d01c40b100b4002800900300741e002a0035800400507a40d80305008900c1002440c1da05c2c52034002c01d2445481c044c2203041d11003818030009002c0d5030318869645000c1c1c4005c04594008200d1040140000501c1c2c00d440d00c0d88102018042041104d690340040c0828081076215a90801c07440010354200d41c0380f12600d0004104640c00101280c81d60a0394024500070b9000c0c00c2990080604c044091700c00d120107100e0300aa403611002c52040f82d1100702c80b11074071000542e486034681406440062101126a048800402e6480f017501c2c50b541003004140034034081c2c40341c0c42080b901301900090003030345400072058801c40c1c47e48140d0002c284a600a6901100340711328154580a000c00c0150080d402c52040000401741c1c01250a418090f0707001e0a000602c05454480e00c09000441510 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 313652958 1250 313651708 313651757
    0x7060515120d0819140f01140319050a060c0807080c040602120702040b03030408031b0d0e0402180a0602330c07050102040b07061d0a0302030315030c2815 68
    0x1c0c0c1003020250440c1c8408405e002c0d070141e481420742042e44e42c0c50080050707904484107030088071418440c00303607058003520002400c40d14044440c501e40c1207901240340003850000c40c0680100303400e0815880021803600308130514080c81d00d40d11808004c1e0b4880009000c54040c602c03800b00140e102e500d6400b074544580c0c004003201da0002d003000c541000040003191647c1d2040e44180c3d296400003c00c0d0701507140014042d000d410220014100c0144001e4004040541d040070084c0b060750b00050b80000e50743d0b0f03c1508110a14003a110388000d070b56030b0101030340b103090b01001d4a9401440c10481c82011480090156100c201d50b0315562040c0c0740c84100001c650011582150b0940d402c01c00840c041c2c029502500f00c15100340d5012580c1200d40692032004400e68440a0803644072400d4440041d4010041d40d0744550f0081107032901029244c000303072401d0341d800c1c4d0307290300700340d41b8070f04962424100308140c4821511205107549403a90786075070003041d141e00c0c0b09103c0040c92000441e10091301401781c3c030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 313654208 1250 313652958 313652971
    0x10020f070927050f0f0106120204051f0329010f03030507020303130e01150203030f040b09070e0c0a0e0a0b030402060a0915180909080d0e1207060515120d08 69
    0x111081e0440310060241030034090000e071120b5115440404c003481d000c014009a031611900284046440c3c9046042c80514014009115589130400100760300100940e080e4810140d002d103205c032030b5982c1032084154524041e852421041485842160424400954100e80180307a020a0316861910201ca85800c11081268580400c01c0712411181c00440401d016040000100980e9403404800281d1682c0c0041740c401990001c0c41082816034820500c140d01a8000c0c211142c81d03914141d4050510f01e0a0300f240e0a801503010a200c007204e10980039103075207022500da02d1747c4007041d10100325050109101d214035000e81000002c0c014141304000d0a803030141410000742098940700010701041020040d038001444580000c0d800082044074a001000d1041c03042062800b1900c2d4002c503441402030078000300b611800c90355043e54003000321103119516101056140c0c0c00c01d1030182c0c09090241c514800c246140c900052040c903141e8201e903030882a407001024182d110034170030389007050001c159 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 313655458 1250 313654208 313654241
    0xf02010f0c150b0613241403070c05010e150f01090203040209011203021606050a090e060a060507020d1b031a070806010c02040b060d1413030c03080a02220510020f0709 74
    0x24207030fa0402900680600302000340034400410b907030406c00d02802d80901001c10450161024081460a07008480e0002c1040c60038000074500c0742080c44c05081c03240c0541440384261909035403862040c6501c81d001d207044a58403e05a41c3c1c03500103e059000070386000e90304c0210030004010000022000c0107940c1d00c24019101c842140c88070301840e000056005002103200000c40130203195001e11072002034a050007601c070050a0450103d20b0094031405604c0074031400142800955441c00c00107016907500c0b02c501000104520700500e0b104020340300c1182e211000e0710030b0000e01030031003007082e2150351150f07241116991404011141312200b210285e80042d41e516420005442d13800c000e14000a071880007081c0d90964455450403604020403001001c44899880c1000913442102c0900d2983c2501d0002c80680314121900003e00c1a0800600ac1030540c408000303183d071031070f1090000c45100b180c0028904140c0f46050b41c440003210b40d0542d59400c10a800c1c130a0140350741c056054004d00c03516 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 313656708 1250 313655458 313655467
    0xf0105160c0f120209161b081308011e020304020f06071a1503151e040c09090606060e040b090f0a0603020d08030604050903120a020306040b0303070f02010f0c150b06 73
    0x10140c44034110b4001c2c40180540181d0f14040d420101103642c2c101002c98200d105104001c00001c0c0070369201c13045071100c0a40040c801052007402010f880b840c1c2103985800c03c5199070354400340e00920b081c090300720609006c0012501e202142d4400d1368441c1c0c2e006810156084001c1040101c00c0e03010b220120b91802c14110b940d60903c0c0f000260500c901c021f01c002d228441e4200040615003180d4a03287c8010040950401181c00c0000d880c1400c140c412814041c040d031078500d80f101840089810003c1210301d0b020111007444111341144040f1080c0380c683d04160f20390b10041c030050303484d80152140c00440c0000490080041261040d41c084a03041000030200e40340c0c1d0000d81040c01d14141903604410100a0240c04d10702841465080304424004514101d810002842da4030002020520841d60102c00106a07494a40215405030f03801400d880c0d580300c041c40c2c49020030601c644103030700152484000c0e0b002d9900038000901403a4000d4030b104840115244000c1c040d1080042c5940c00c48400e02 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 313657958 1250 313656708 313656719
    0x606040e0708010f080a020f060a17070903020109092a0210020a09030c050603010303020d05070203150f07080703020c0312191409010507020309130c1403071d0f0105160c 75
    0x51556004001d660355110003540741090f1440c4540c0c4030342143d1002d41102c0c4011006988900c48a034800d0803c0d100349413250b081c0d5105840305c400d07202e02c01210717035256410043c0c0907074441d0442d000d0324400d0300c0f000c04003911050050704546010b40100060503810b42240c041a1201e4844800d00c55144100c400c0d5291144800c003e90304a44203400c04031300300c10b805208000005120401401d030079140030b0b065600d1518020741e980140c03685202030003400a4030809645052016100030500100c12624509088036402000802200c05000103a013080106400501c01d000b141c40d4072541000841c100903c00c040348607240c1c0040d00c0740b4198008407a04d0318800c0040e01402c0210300020301d10b0710941c0361070001c00c0d003540c400822803021034008000c08801a501c60040500c4501480c1e03000a00c81c19000003600c1500e8124200c411091010003001103071131340a0513680c04049550840c0131049541001c1c00380f4644055236003808500280700c540c0003500380103e0120980d001d882508041581c0d403 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 313659208 1250 313657958 313657979
    0x8061201200405011403040206030601050f09030d08040b1324020c1c090f051507061e06060215010f031e0f0302010b0418020307030308060d0213051e07050a08060604 73
    0x78084203054074408181081a503030032a150304950401c2107202071443c9060740c000350307103444003c00e140c2c140003011450b511202404015240100707406021114103500091001e1700714582183c0841f244004400080c0c03400c1c500e20040c030a910752021034040c040c103120150150070302c203c5503414506542800f0f0188040d0b42001040a42c259407000000381204c2c0e80c030014031429041c0c2207860f094103109001c1100c2d40b1004c1d14600c100f049940183d0b1181481d1074408090090000da2884c4e0141241031115881c030580d000348100c032803603000c4031041c40d1a0a491250341400748540c1d5148091007804002003200010003d1281c44080300407140744c520303039544110328400a5000c0d00181e6649058505500381845841c142845088003800540400d90000781d4801080c000141080302c01c038041003841c1c545000400755280e00400034080554080c4890300202022981624200c1c02003181c07000e80c003011040d07140900c1003907403100e00d80325a4200a03074032400003401603500410100700006888108 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 313660458 1250 313659208 313659251
    0x92712111b030d080903090103090c030203010f0b03070f03020102060f0a111c0c0504080c01180909060f060515030406090305070b09030903070501030606021510030b131202030a08061201 82
    0x10050901c5001d10988189850031948541071024025044244119201e001040d80c181050900e0040380510080c5400500040380e13500080d010340c00c107a07803400584040c2e004585490016006c403071425a5030751001e1000529444040c1c0542c03c0740c0003050102709550a415402130311584045004051000b910466500c100d1108100c030400c3c02562652400300c0c0036000140e800c80c60014185030030b1200d40c5803a903001c2e030702e1581030290440703034408441130a0124100610040508004074080c90806202030518140d800c404a0b06e403020109803031901412584600081010306421681c903a80c5a40c01000c1c0300c48250140502408035000080091050f188215030031006107440360711a10030b06160509607008941814203252003030100c643e0015aa9803c081844020b40d0070ba04c1e00c0b03491030a128190b800c00f034113600d10b5400f00881c030442d031061882124442d0700441200000c3d000120703102d0040502000008030081c000c10500d1410700748038a04551034030b000140d006180b10032070070028203 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 313661708 1250 313660458 313660483
    0x220609050703140705220518030f071b0e1b07050610060815150d02070206210703090b0a1a13050106020d030203010e010608040c0b0a030609271211 65
    0x1071081c18035800f068284100401001c00307a40661420040c03150b80c55a8004401551494039560030008640e07401104140641d80b04c2038055076540d440b202e640c01820b40c0700f10002d0750501c1500001c2d0801c40790f09a51002240d105070110380340da484002804044618002109003100d07014031007000480c005000d840e00850306070b202035040314131300740014003400e400408a020b0034101c440110020380b00c0030005c0b001504c0007030f1a260740d0311040d65808024010700340041e4001501084100b0210007484d44a05090034800122449550b980360840945d6606000200b81c44484030110b080b0100c0b40c1c112046001c881c9406200810700c0c4404524140301c100c00c1c207240f081e1038500421416805000241c042c80651400b90b1035581401c8000309910410700c00e441c20405540000350a01a1510760000070744501c92502d1703a1400b44403002406071000c0d0040340301d11807500059603d00c0c2d212080c0210401c080034101848225691500403800780200805000d0081c0b40c010803e00c00400d0215035500360 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 313662958 1250 313661708 313661723
    0x1401030e160e010e2d070c0b01080706080105091501030c12050f070f03022706040305060f011a1603030c090f1701050907080604080306030307140109050c010503220609050703 77
    0x6150410800b074418000c3d089405600140c1710241c900c1c007680704502080d03c44030844d050940c54000c012070344145181805803600f1601c07000464024400b280c000d04507a003607171391900c0b241d0329001042101801502d020040c01606141600b2550003074000e450084185c0c200341c00380960051030301084c1c400846041e0005e155081c100072a01d90000035000764044c1500d0110306040202d410360700b18461800c90755070702407100404240c4a940307500c201e40103141d003c01516000c0c18070400d031560501c400c0c0212100e45400c64944240416070006540c0d682e010300300c1c0c0b490b414100380c8095008100c00c0410704200401d0040c0410f09600b0454808010907100013020701d540300c020f80403401c403403024040c0041d40d0046002040b8600d000900d294203d500402219520344035540024a0740c030580400038045440d141082c14801c0301940141714a41c040c10a0725040c40c410001144ca0384030440c0c040c03032280000300003a100c4016010104055070f00c11000040d00d148180c803860700d37041c0c1903801150b01d074 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 313664208 1250 313662958 313662961
    0x21070f110a0815010b042601020c030c07080f12040b09010e03010e030904050a020f04061103070c060905211b0307050a300206030402041e09050d09060206011401030e160e 75
    0x18002d40c060340100176003506203040606000001886030750301d208400c0001a03c00d00364810100039030468041e450f19000b207030354441e40000380e6529002d00703201d80041401201005c217034114020484082049208181c546460b08000710406181c001030b04403410410b4030280d03a091034400348561880e100f0701000441d100e080d4941040143ea500400f24074142d80107000442c2c1c0c00c41030406841c2980d07030f1030801c05403007903203103407030a0bc1c43c0601240a000c044401c10700040b46604240008280d0380141c9001c00742114407500a0741000f042c6564002941c0100b4690b03850030360580b60b413400c14200400361181c01340e0380d00005100c3c10503908204100852108092001c01003d881084441c00120b46c10b40d402c0400d07000210755000c020401b0b8000c0391242144008005075010051095001a504004140d1942010340c0e8400e4100221004119104030209500b400002c01e0b0b130403910480c8078110034201e40c400460203030040203003a003002d00c00c0542d542024807007004042d0113000d01d0422910903 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 313665458 1250 313664208 313664233
    0x19060509070611030901030203040f1a01050a05012d1b080d0b0a0f12062a260c0c0a05070e060415080316020613060804020321070f110a08 61
    0x42540da0b900c880140800c0b155000c02e0f460010054a200b04001d0800503203ea84a0a000c1401c01341c1e00c00040c02c108003172035906903205e0324580342c178140ea0b8140d4008210030346a500565074200da5810328110344000c04246c02615152080d030300c038034003800c1c50200201c40256040e44180c0c03607c82002c0718100c10100720300c54140300510a60780303a25421030b55445083d21780440703842e441d4102c2c041e03420300f444030217aa8001d0281c3ca810010011450030100c16003010300100b181c01e16042000400005001c100302940c03030403080c103100300f20850b11840b600d4140d100d20f00200481c5d442500e1000a5004680809020403001d01c040001031000744443c40c42c510300312041000b1101e24201000403900001010b00c24400000146c3e2400720007002141080301140c00003411600603d500e04500140305440842d15079407241c0c116000780e00c240c0c00c5030600c8014880310703c61510021180340300b2910501558010604265120300b8407030041c064240070070030020104034411229081445c2c968400c191004d02c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 313666708 1250 313665458 313665463
    0x3060b03060f07050c010623031623030f060424021801030b030c041b170c12100e040308090d110c10020304091515030b01080c0a0219060509 62
    0x10040422406441d40e0320b00200c0d0541c00c4500a0803c01c20804045081544002d00758010409058004440f055168005540302130b0024070b0f0031103502034058880e10b08405508a400c00007a5110040444000c0c0c200017161402e0003404001240d00d4070481c15040036030f64090042078011401041c0041d9008100c89140341c1000d600c513007103001c05204218490070351015001c5440c030440f00746008628650b51f600004d02e0070401c0b8040940c003518001140c034103598000e001e415001d549495031903100440f4a490901400c00b100d5a514502042010764100c2220004132a40050400740c001c2c1c1ca55126642c800316030307604403021804107107400c05000f00c290003008175950f145000c0c03a007500386241c40461030b80c44490400d8003034058a00d600b240c4141c180280151b4015100c03455040041d0b900404440c07603d640725210b13144049150340002d030801c92003805084005c6406845e440381540b64900c00311001d5010b04000d50071030240c0c40c4c044003134035200c1c543c82d02c4490180e0808611828000400c1c3d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 313667958 1250 313666708 313666721
    0x309041b1103180f0f0901060e04111e0a0c050d050912011506050306040f020c01020403210203161a270705010806061b10020a0f1409090408040b0c010203010306 71
    0x2a05584240101c1c4840b1510f12441c3c403582800380c03001c1c00c0707945001c804180e90b21484c99865600c0a0808004030b00303c1d5004080210b03210701124284090059100d4104c0c0910803d0099804081203200c2400500841c20003001c0301032244c0f8044204481e9034440504022240c00c040d00001d1001070f44114520b0710f595281c8442c0c035440000c000380e07403000303000e002c0c1c2403054403580c800c0c49004400501c0d50781d900da00c2211512184d43c2c082d035503070b00b8020103d8001c2d800342c0030883d0307042d074110b146440c41380700301c4000185054250000d40c80c0501051030070070030398003085d0200d80f000200b80364400c08202c524001c50044a82003100341c000040c00300c00071101c2e91085c0c03106100790702c68032040102c3ea1344061004d8204200703442d003564912801d41d5603140c200c10381c80b0805151041e94104a06d1a6644d4020844580650344034921208140021600140215401c0035500c10902c030251940c50154130581c0c1144c82515558585072351740b40010380580080c101120107960120040003030106900825 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 313669064 1106 313667958 313667987
    0xb0a15080106080f2103090304181a030c030714130603080403140313090c020f1e011404021804061104150f090305030f0a020309041b 59
    0x118003801c9a407040c0c109502c2001404c0d5800107000c1065800180b01c400a8080c1440026413000242c00c0504440880d000410000a01c240248051124404404030205d007500540204c2d030f000c0c42103000c1250007500012000565a40c01050703440c25508030184079080a036240f00401e0540040c000792404092a020000c030500c01e008014000700d80c420310701800d00618072000140c0703e018a5803282000355801074244803240054100010000440c0704540010040703070241c42c601040e4218000c000c13044c0a15031410340b4401e008402c400584034040340d419081a6010500d203401109070368100812820104042102d0754100840001406da0700c1602d90751220042410091551351200118006500d621442800f034034421007101d400101540c10f1804035010011141e2040a1400c214001003199000942e114451300040c441c12042801c1400d20711074001e8220600ca00c3c64 = true := by decide +kernel

theorem cover : BRFrame.Cov 313489208 313669064 := by
  have h0 := BRFrame.cov_init 313489208
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313489208 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 313489208 ≤ n) (h2 : n < 313669064) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
