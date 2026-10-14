-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1696
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:20:42.394133+00:00
-- url     : https://prove2.me/submissions/74548ef2-d982-4af2-a22c-8fb21bf2002f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 304856115 ≤ n < 305035971 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 304857365 1250 304856115 304856117
    0x11030a061d061005280b0d050a14060603090106050904060204090506030a0b0c030a020408010c1d0d0f0b0c1b15060402040308091207090f0203010515070f110117091e01020901 77
    0x40362a0825081000d04154030012824003026800c07110030950502c0c02c800020286d06103283d849050b410180801c2d00c60007490046801c1c6004c59080c90035121034035054000c042500d2095498032402282c07400f500050b08541e8000c0303590303024042005015030090007140c00b803080400c01a2120020551224042400a403908424001187d1f22480c188025900405070400c0185401c1d5100002400e451400040c00081500040d40a112000100001c1d403070801c121451100340030150741d001940031000d8030140c9090007440008000c03030075520854181011103040180c6401500a0181d920020301c0c181c1940003150300b0214405040a0081ea4140da40c4007041604203c0c55605000b00d00b8854cc3c03100100e4410400e002036012034038460900d10340c03035080000d6501e60601c030600c0341201513440540403582080080c000400c0068550b40b50b11580500c10050002c061f20041711060b00c0910f8000298500405021350800009803515002901c070303051028401ca070b641158201d00542030994 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 304858615 1250 304857365 304857391
    0x503091605030d0e040b090103060e060903030702030d02070c03020d1202010612020d02010e031203011409090d14070606180221040209070e0402070501050a0c090902131211030a061d06 81
    0x10f0200d50107003070b0204102e0005080042c51104610014103081800e03403003652116901e08103403034241001d21038954400c45190046155080104000390349206000b5881c000560100b142c504005200c5401c10043d0340042484a1000107070400e48400201410010701541c6450000946540d00c1116084084e4000f005002180c100d90010b640e0040c550b140c4550502036142201701c00c4106501a40c043c1044141d03102d1108001402d01c2401c82004d042c0c101d00e5841140501c164540c09800e811045c0061040d26880d0030031440c000c8090181034100e1004121340701d80c02008a00540c0c040c2c6144400041e450030b42d00086a04c100785010241c5002c0d4002c880c0800241440d0b008500440a0040107070005107070096070740f509804c540c02510b00c11055a240e00100c44032651200c190000f41c49081000c61602a1918103010291468400c1c00c524004109085081c440701791031242c8981405015945030042e42e1030040000c00101b1941c6203d0b51001031008189440010303d117104003d518904 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 304859865 1250 304858615 304858633
    0x927090d08130312090623010e0c0a0903210f030b031c020a05030c0d140a05181201090c05011215030f050304150804061a01050d09031e050309160503 66
    0x14410b50a941d1800382d050001d5031008000c502c54a115051540c4c1c0181c0e40050004104e001344000c5c29090f024401050880c1401401440d4040206ca80c1102e4000381c243d940d150000000d03690805030741e00c06440c17520001c11446001c590300010480091065030340c410302a0312490294110b40943e4005605a40300c2c1405120760b80d40b5820844403090940116a580041e070380c2c4a40ca5940903140c44000c1d82c03c8081007801d010341051030140c560070303040c4980b4107241c0c98190043c054080e90385840b07a001e50030041401d035034942c21004081120b8013402800007880303504005194035264464140004e202e050078401078400351090350f12030b007110a010100285152510300e0b020402c42070a4545000401c00000c1081481c00c076140d0341440c1c0d07202d02c0014503040c1004400c0f5400264114400d030140f00c04881c0c180c1c0d01004661200d0002c104c0055420ba80f03084c12698109001c5c000c08062040c11903980a00c1c3d004400307107208064850455a08910550035600040e60a1080a40580c805030036 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 304861115 1250 304859865 304859881
    0xa180f022107030b0604031b09021c09020105070c0603020306030c01030612060522030c2a031e140304080c0406030c0e180d0809160305030415050927090d08 69
    0xc0d480d0007461514020820004e490300207199035015030310071030b001074803168040d202d0808a0b50480040c80301800441c14000305404005114480c40c1e4818182c541e58070b40d030000c6a0113071060b9803171190421001180303d511210090003c0d8030039620300e0f119101c0c490303541ca02507220b40038200980d040294418000146a542c4401400014102d2200c100c07820030719178844094401ca0a82580c0640c3e5106041c520310f00304a000b40c00c3c440760108480406d4055410070300c40d98034000701240c0d4480704002e203e100c0380c01c002082000e4548020100d03081500c11b0b010a28000002d002a034011034142c070018144101040115000c521005140d0681402c1c01c110144500307807055402603141d0b05141d100c80c050324400341040800b0252201241e81481448010740d8100100030407d8411019841041c1c00c0d600c840e60f403030146200f05540e0041c100c1850592a11400560310304000c0a03040b40305051040200804400c00c04003603106500110000480308480000c07480149102e5845070b00385ca0b224010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 304862365 1250 304861115 304861177
    0x30b0f0403052706120105090109020403080405010806040b04060801201c05131a15061204060c0903020a120516060f140408031314030703150e0c0a180f02 68
    0x20700c41c2000440c003900b81c203494540d0b000801002c002800b030002e17150b052000f0400380c2c1c401a000003065600c14002440000c1e40c1d0700845d010758409003800340c19551044009000703803c0445010350014188400013038014415000415a04001c8040e00d9204041440240079400b4895501c45982020a10144614940d52040f034203e503840c4c000040714011500e82c03038a8a0340103000b0915400c47c000400094445003103506070481011034500d4a09584104059140749001c1d0018120301e550b0301e03d035015a07005004002c029580900030003c4140e8440d0b5402e54a0717100042560940110040d0441e60020191200c05440c0c29855808807014840c1040350020986502890fa410702000049007080c0204007801c1450712400351080300390b0402e001f05909030308090206000b0b40c080d0b0310910000d001c5043c1d581c01c500080400084071310841109610740b098a030a03064100a07410b40c0420030007448103940c500d0803617110040c8002885c04220100320300c00c0340300e800070000400040c0841e4603803981c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 304863615 1250 304862365 304862407
    0xe0c1207080609070905010b1215010909090f02040b010c0209130606090204150314011404020c030708030711070e2203090f080d030509010513140f01110301030b0f040305 75
    0x1104680805403601102860848203550b402c3e01ca41c0410010429000140035840c050100d9407500c0e03082010104103202c0140b0040c244a445012680c51030320241d129402c0700004000c10201800ec0c0c81c420304040510181490090740a2410104ca0304001d50081c00c0031021140d003d4000c115070f5491403258880e0408521040f624503803150703400194001d140c0013401c068009000501c050340040749000c1c04a0710608019224541c0c1d13840100080c00500520000840c1c05890159440c04100086402d43c810150300410342040030081c004542e0380140c5903164080750707208490001e6281e00038501d51340302c1190301404c84a07140403e0308015a10078080070a85100c0e050640c0102d071101d401d0001c4030190f40101420340c1c0031011208900b07038075010b0349802070241d4000b0041802c26060b1440500d0140c10040c16100c20040c82d0341885404002c400c142043c0407008000c0b0108040b140d5106d40d00070b1200b590702e0154a40824480d40e454801540900e505480d007502d0400d0360140d101501103c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 304864865 1250 304863615 304863649
    0x7050105010e06181308040905071101061514130306020304031101090c0510170103440f07080d09020906030f0a03030b15030c0406080708160c08040512060114040e0c 73
    0x45c403003000c0005d4000d00900041c1034940404102c0307181200000b00b554001d2540d00d4401c2c1c5c18200c08004444e00d111440001001038584202d0624010b0580d07041c0d032049803121032029000c0c00d40041882029070196016a02c01d1b80c5842200040c48081c1c0d003030700d850340310103045004102000c00191078102c81541400505041900c111244050f0003045035409a100340c03810491200614034011281c079a00c503150540c0131960035403101890b00958100442804040d15120008581c0c50131503060040e501801e50101d240c1c1e65036220b2800f101d024249074a01240241d0403080450641d1070049100078889091800a2071045503a89044004c1c1040e181c4251b0020a160341c003d003070740f109000551281009802070b030359030361424000400a09006019204020a0100703015010185004801c155201403501d500310f4075190410041901c103503400180d01418441c00140da407000891268103c41d92645420003142400d000e01041d11801d0303800004641140501220f149003803010b6030861700c80 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 304866115 1250 304864865 304864891
    0x8121602010c0b190b0604140904030519020309011d090703200708090307050108060a1208040b0d090209070f09050d060e2505030a03050a050a1e030207050105010e0618 74
    0x700e5169441443c00a48614074400c0d100c3c41d4502d070100ca45d0055800c0e9442c1510130a1800e482c0196007610842c2c0881e08500c900c110201040a06101d0429540100e40401909401c074103c000080c0d52170b44402d0b915408100030254030118001240b400d4260100080c24811055441507001c80c010041d840c00c2c1c403180c5280e06440d0180203160380250981c2e52003210f005035584070034010145000410390146040040700c40800c04c203a260f00d001c14044a24200f40001d14041502c0c00005500440c0c018454440b80854804031081e0b0680109003e5802521941d00c030740c07541d80c000c0b90088810012200420b625000800c80d40c20401003041d126800b07490009000e4001401c80c0b41090703818413210241001d250350000d040c1055151200051904500a00320701865580203000d5010718130302d110a001001c00c01c81d25990099211138040c0f000390f040e0b040b00a000c000c0280094002e00c0c81a91a50721301340010454034503d284807801020020000502c6101a030740200b14440010014141c0c100 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 304867365 1250 304866115 304866137
    0x4020c0f12071b05031f090615170705150a0e03010504030305100b070506133002010b04050603250f030b0114010f080a150815010f0812160201 63
    0x4140300c409641c000c0c4200301a41c80c8900c2c00d0500c0d22025140a268821086203001c2180c0ea5000510006602ea0301c40c1e851251800307014450020118413102074119400c01da816400c0c50701e005203903070507618070b81c008144c1000d40c880d00c40d03902d010900455402c191017030448000010310001030b099040e05460080b50201c640d04c0400c2c25944107541c12000b2944400c2441051198021800041c0c404040b1050078205039486090703407044003800248801907802e440380d0512021210600609a2000f005002861a100c0b441d400700c41c11040340006502e04004060240752134020540240380060081000c0c65040110004001580250b03000c5040d02c0040010b403c24581024070007580074480b0000290704d0814032100a00c0301000a03410484002000407005030080b0718103400a24455000503c1d038001012500c00c1000c80d0410511b80c883c51064002c00300b070001c03405060341c2ca0240760014640c3d550b5501075031404c0069540c01884c10500c50255494551552060b01a005260101400c5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 304868615 1250 304867365 304867393
    0x507030c021e160801020910050a0c020609060d0203040b1009090201120e010204050d050a0201020607080f0406050402010e120318090402060307081b040303030506100e21011127041a04020c 83
    0xf00040d0700280c940d940214500c03665240042e0305d401e0103291814902d00d0840381703c200424001651100078070510004c13606003410b480e06c2e004c1e1118154494030440d80c90030030341402800035008481c901505880c800d404100715078a030140d41d15059042e101e00e01e01e80802e160300005001002c0d135450041d9400d00c8000f8580c0d8803407440c44081030040020f8513228640c1c0c0002810400000c0602042c0062002400301e444620030700070b54099008080002c0360b48a078801214a029544043c0b6071042c041d00f80c400d6000c0020008000c1903125080c411116051030b0180300011000710fa0180d4014824070006105601503000540d10403012085522901c1d02108100c2a90b0040d0f001540000d541d00200041806d0045406119071054140b1103243c29060000502c4901d4403072401e5800c810840b50014054000d401406441d00326801c026264210204800c00240c0c8116060f410442030555040c6142002e2150902e03000c120781c1070310142803180f41404043d601c04190782406200e000c007084050 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 304869865 1250 304868615 304868653
    0x9090c07023313030609020f060d02120901061d0406060e040309031101030603020a090902010e0a0b07120e03031e120106020706090b0c03090d15060b0901030507030c021e 75
    0x1c80990861280050621034036140040341e920110542e100100f042000b0381c007030315620004480d030243c030100380f0342d04520114a00604d041405900800081342c24400b030b020350780151806040c0013131041c180d60388891840e0309890380e42c481d0440500760744030010b00c100c4218110315803244c055600414010385d80c0814000346002140c1c10b50010700d0200c0144104100d0713500b100400e05091030280702ca00d080d81c000402c074411a01c2030000190340d4021040459000700d101c0c01018000070020654a81d503081d04d44025403040c80d0480c2d01c0550404111a058062405620462805402141850503510700b203041c80c0c0b40c80c14200c0350b403001440300031200034050700898080c5c43c00b980a4511107151034406440c0c2c480c3d80e003040041231828400024103407000425602030f840121407070780c40802c040c2003020001640030101a04281810307400305070408042d00901c072220003030ba010082c3d5902d0150480440c2d1404c0e00c180010b0700200000826580300205c0b0703190b01591401a9507015488544a80c01 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 304871115 1250 304869865 304869889
    0x3040f090c0809060910020318070306020712090e0a09080702040c090e130203030711040e15040c050d0b06131107030221030408031b04030b0108100509011109090c0702 74
    0x8201e880349001d01c0d10302e600031105500b0402c2d0350300400103070130041102600d80e03030406481403072141c2c04000108001100301064141c684040c0a41d4002516401d1110180d40080400e8039240040c1c00706640682c13061138588211940d14500404035100c6016500c09841000e0060701ca04070700303202141c050303030300c1d4416504803418070b884116040f454020134564024005101c50707420515001400c002d80c402000311204150712035800c402d02011032002070700801c1c40c2c50100d002446424407040e001c2c007500b0103140c001da0182040d00c1c241c0e0740c0c40d810800786910380800105050328450100e2014140601d41076160304200401140980d00547e02c10940d42100c481a80180d201140310326449a420a400c0d400c2c0701540e241034607601c1d1035250301f031481c4406426a0280002e84203c5551030a5240c2550040d681c045c45145482d46e4544045980f030304880d40c041c0c244c0d8904004618000382c1441000b1756031b404445410f04042020082281d041d1b002080c20104030310800220005a40f0f41c007403014 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 304872365 1250 304871115 304871129
    0x2030a09020f060301050114090a0e040c03052802011121070605060312030412090f03140c01030e0c100c0f14060a061a09190e06150717090303040f 65
    0xd508411801040310403507005060900544041005000b1039034040c041e10303a41e205020b9465901c6003000c0114150170b001d80c1c41016070104030402d220820901d0040301049038050000c80315011315031300710300b02403101c800002c48403013807544105401940184c1c449400301d00c035003003902c2d890060300990708961003100c1c00954098900040540c201700c490b2103003d401080c16002040e0b0101109413540c81362001500290400c81103e0b00c030030b09203201e41d00302e00240080c2d1150002c02c0780d0360b05e4103150f40c41080081c3c8805025442490146501ca0310807644561201402092085614014040b2036801c00011404001c144107000012134110046035651034807900d0301500154040c1415804c0501c090411f0302602e00300042004200c400c1e400810341c07d10114102943c611101d000501510080304002d90000e210800000368000c61950151143c60241c498004100c210803c001462241040040c981a800c584910704085400050038079821302400f102c0c45c154440905482461050340b000b0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 304873615 1250 304872365 304872371
    0x50103112a070803041d060d08130509060111060a0e100e0d1407080307031112160f180b0a0c020a09150f06020a030305150d03021005090d05040605130902030a 70
    0x80d0280300c1c10010403005010b0030002c0c501340342c14900c0c41d110b0000c3c2c400034000000015804070701187d48520407141c0365a405043c0c641d903446003d0250441044a10078644600ca286002071100d50280c003031040c8054821010780142c1c3d03a101c22000043c0180c1c9180c1c10b09101c0c036141100c21000c0c42c810050307607200c0c40d8005c1000b0004903d00a100820708000c0407200041444032100081ba44010740303800c12114100410b00314210600140e0600900d000c00c80420006c009110a0710300445201c1c03544443d82d5520000c8644601e070986412800e05e4111085003c503000c02c016092220010349103210030381c45c000b0011050b03900001c24142d2203030003000d503056a50b01e00320031a040848500c03001701400200442c01a01d040c01c041d40303a98003510060181900d8038000b584841d17603880345044106006041100c000214100290f032100c6202500940d10301e04800f1403100a000200090000642d070b0380c41d45003d040c000b0440b1150070860000c0c18070640110003140e41c80f46400a5442818403074800 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 304874865 1250 304873615 304873687
    0xb0f0a1b050d0609060303050a0e060f0d050402010806041a0d02060c07080f01230103020607021302030901060905180a030c140712020415031713150305180c010905010311 75
    0x2c0301c00c5403c10741c4818940342c41c000080002a03040002d4a40347c113094100525602c090002080c4c4500c81ea1740c013103c91950002d0f02c54403a1a1aa001301e004a0003030782e400c9801c3c0e9500d4140030480c1ca00c0203040340d1043c030520304100c00c0e240490920060620103843c00e410034091007101860010190030864598004c071094192a482c01d20510144562190281ca034000000980720030621040c0000390040200140c81015916903000c0b9001c000803880f0210f40d03900d002130990340200414040ea0305000d0811002c02c011244058881000e00b1810740646030b0f445444c0d5064540001c1040704a48000c1d00c0391154400c1c1c041484900000c00880741ca840d41c1004502c1040b0271154034050303400c4644291903041c000302e640001420140c14421841c95a1501c04071541854011254448039a5180c0c070040c5a514035415003085d4060741c44503eaa00010454a121a40310100301c043d40c2d000402441042055601c02c5d0400719030701c1d511502a07071420300b0110100081e4480c8104601c250750b07500380c1c5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 304876115 1250 304874865 304874887
    0x10902091b0406080601020f100e011a0a050d140303070e0f030d02100b010c0b161b030f03050a09050f0a030207090e0c06091c0b0906130b0f0a1b05 65
    0x1075221052a040000c48044000500300601540c000c1600300200180001d0180e40204010507442c0130309030444041c800c2a0211001800c01000d0034803081d4206100c03103d000f03078010035035018140000d000d403030a68140401d100c110149803070256180c8100d180e070300a9004081c401035004101c10f80d201c84107a620181072005e81203118240310701a50250000581c02c2d0703400b007401c2c08030111151012a01c0c02400b40100d450280c03103807001c3c0c0082000c0c000d12001c40346100008201c48019102c04485402c0b0700766100180540c0c40000e07010036104038405160910980c0030550116015000148000381d54682070301c1c242d0f00950789107840c1d01c00c1c4002810315404000e0b000042803070710000d1010290303ca4159031a600101d401e94043d40c40130030170110765511110310254110f110380c0c8000c00503619082c03418042d40203495100c0280140004034081d800c0e041928203040d5005941a045078072815402d001545000b01310f255950b0392140500609e210302e085401c01c6441d90b0707840944070851005 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 304877365 1250 304876115 304876129
    0x90803070b041703011e15051b0c04140a0f06050d060507051e0a08060303190c02030f010e0d0e0f060702191809020f120601030b070908030a1d0102060c1b0102041502010902 76
    0x400c031084403035012034006859004086484082900c034409143d40620309d203d5260840920100d039215080c120b00c1e07640d050380c0145640c0324010425040c0054011004c0c51004c6860380d00810740c100a003010514041034540c1c001c2a0440b41e03600e0040d140c50041d4005802d4080c000c0d1070010180f074001459003010b80c0c49030280c1d80001c4204d01075403414150310600210300109500350701c14040701d005140d095603000d021020490003144024400b00b51446040750b16445600b55160208409504801450821991507917001030044c1035203241c0103558007002144840d0b9441e94145145030304012803080c00480c0e1b28401c0f07010400011a0258080c410080c1c441e8480c070446c1e0181c0046144044820b00000d07140b41100c0d040b640454080d21368090403545680640c100c452103200000b8618034807540510750448004000454079041710b2450012070f00c0341d1069405210180003031015506203c509001a00c00f01002c40c001883d1940d91204c09001c0415001d24402503559101c0d2a015410040 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 304878615 1250 304877365 304877369
    0x5160612050c030a0915020a030501030201121b0e19080106050a090b030606010e0105070c030f170913020a090305100b0321070305090f2e090803070b041703011e 71
    0x290070300c86803a00e50140e204500005004081c2c5903192019102402545200c0c1e0090084000080d9130b05d285240300a00a00001e12080340001d00488030340d1150043d6114104004a0111810720169407800e412603448034007001c0d0641c0803125501460000c0385909003200204240300000c19814030340b204011044105a00880700181401582c500507900801c01aa010109081011564108000403100d42c060b2200c0100b0f01d101d00040801131003e0f448100c9001403144114600055895a0040981c0a0600e441d50000a11000318902902c6600a071880141619040405907502d442c1c41c2c0c40c0c10041c02c41c00d03015581c1c5800080e181c1c2001d003e8000c440100c0c11942000300300c82c21840c441c0d0b106218002c1c003001800300d48000282d40703010b0700d0024031500a0881100032608220300440080154841121155010084c0704090041c5600d0044401841c0a036050405503100c00d5a0300303400401c1102c03080f00842100300045003d1001d18041e00c521100700e00601c00c0c02451142d0f544050b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 304879865 1250 304878615 304878647
    0xa120909020d1a1207090c0e0607140c06160f150c03060812030412030b031e0d1701120f050102090a03080c070503010513080a030902031f110406050a1407051606 71
    0x5401484c850000025a4404840700042c00041203280914129505407054070350503401400055443c0c10301543c94200c49400312041d0584018010000802809205d24200044415000700c800000706000d003055801c42802044039100e5407109049a00444604c516210702103a0342c0c600601960800700030307035010074611342c41007072460909441c0c054100c0203142d0207008040c0c540c01f6241580d14180540d11004040c5980544100c0c40182c1d540e803a070b07241e0300585c0000b0b02481c1054000c0008d2a0301d40c1d048840d80b43c04070120f190a07071100b681c102c50641d01984d1964080006429a0715000840c000842c028100a0f446074001e0450070308100d003503800280b09070705100a1004004a00d40d42005499001445d540e03910616207094002d800c03d80406036041c010301c600c907411040368021100c0554009401000701282548580d421405240079680010308244080074240c2d00801c280c85c0310400c07000312241017080a0381d805140280703010414a481040081c2000030980040c1c06160f00720f49 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 304881115 1250 304879865 304879879
    0x6020d09050409030e100509150306040f05190c02010b090c0a02060106020d0509011d040f2322031701061d0102030705100b0a050409110906120a120909020d1a 70
    0x10ba4500400c2017204034000ca109850030010250300c1c034022403c6074103800340601900b4001e05052155105500112003140c09203080c040407600154180c030402c0c1c41901007a4001c60726016001540c40285091400882959030f039440141c5d10741d60340e200791403107103c10a80e0f01c1d030fa07942d075044024108001a0711240565100d0100400419081016540190780030700c2c0111401010005070f41c40070586460403900300e4900803000b0540e80d0542c0000e21b03c2e001d441c0720040300e08100604540c03030000807103002041802460300841e011314448540d00856000c1c0c0f9090101303002c191006c0b00010000c0c1e1010020070328124243c0200c1014804651100400f40080c6060a015407106034460f4803e0b01d1072602c05984106080c61075076444000400341602030010064211907192590f1001c1100013850320501903180042c0309864000b40b0014110800c3c4003030440c0a80a690f0f039031002003171001403014018003040204040720144082e01040c0c005000c04981d80500084000c000c10b42189400d01a101c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 304882365 1250 304881115 304881131
    0x1e07060912020316020d08040306051003050d210902150c060402040b01030e2d07030807050f0129181302150423060d0e03040f0e0609010e0601031506020d090504 71
    0x703c420602401c4d1501a114460000c0491511001c244140e82008000d80e1078a010b21500340c031130702400404e4034880c0c000c99180c4280310f941034400d4070f07031800380c5001040c01c20800d591600441e002020b00510140c10300f0035501c00081080502d411000e90510590300190401c401e40c6804d001e194040c0c1007e003010040010060fa500c2d1701d0760741c45526048003c80152846042c54540d5540802059200043d502003907140e01e046450750340014002d0b10203101c1d00c4503018034110184600011140c008201c000f00200107074010710300d2800700792001d90200070184649403011500415a01c83e2a04030103e90041605104000e00c20490080c01d40c000c41c0706100c01d010002c0300307400f55141000340750840d0495581d4400014584d100e4042ca0410b00c1d4181900304544180000140050f554403a05100c2c255443c0c04100855240c22101550303c0b0060100400c0301100003c1c0180c1c1100e010b2501144440700042030940030511503000c0307401680448480300d03099078445d00c5000500805c903000d005d080 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 304883615 1250 304882365 304882387
    0x510150b070602031801050c040302090f090a03260f01030b07030b0102030306120106150306060207080c031002180405190c08091b030f0109030216150f03021e070609120203 76
    0x1000784000180416030000100e80d20303070802c15081805550b110024000ba2030110301040300c580103444124040d92415020030086003564507001d101c2c011800c01080001e0b066181140e40d4858800d0f40c0075003000400900100400400c84075100328080e01c640e40ca2940746103030504140c1c0c002084030040600c0e0004001c4540c0e4040700b241c1d0002e104807000c0c41d40c0b081507030b0442d004210b00d0344075004501400780308040e010b1705900014101c80980d000e891610365512000d40e151000c40b1840c03685900418148450380c0380304d6010304402c1b00d8042100c2032502c190804102194020b45054511082040c101040401103008000c00c000803407400e14201d080408810307641da2150303c69181014810303184404151070400c00e4009140c50309009200708062800c01071b407944031100c080d000784000d081700400d81840030803601184840030341d40ea0b80030150742c0e8022002500a11154205071412144000f200194003010707001d010700502d0300060031a81860014400d99200982a040d9003003404040b06030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 304884865 1250 304883615 304883617
    0x90109080624040605040203150414010b07060203070314070e0f10050306130212041401060b0306011d01020106051201050f060a050306041e060f09231f06030506040510150b 76
    0x1d800184441501c2d801d8403000601030b02d0720781c01c00b0350024404820487c3c00c007500108902902d6003230354104029142c1e61261a5020000d01a0240d040010000c0000149043e0f008590140d61490000780004640c1d14680c4400c80c195002e0b8005951030400d0000307032610341001c1d07103406405c075400d045c0b505141d10080c04600006000621807901d201c040018410140c0450b6004001e0100f00c2a40e864240341800708500604101c9003990300c0c01e800452071032401000c49003d1081611200311400010308090001d405964007103045540703d140000c0c2c00d03182c002e400c1310242504030001c01d480c581008080d01c110401000c2e94450388880c0810040c4d6180482e549410640010001260200d0b05007801e480305002500100320919007841001c0c842c3c0305501800c16288544c812400089500407924030309507002080960941080440203410500030040000c58022500e0228100d030303072916124100507003280c1c00e9916801103070003005910418070a078201c903005100901901d500300040300f405 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 304886115 1250 304884865 304884901
    0x4050a03020d0203010b031203010311100806060901021509010207052506050708130b07020f010f0801050121240f0b07060b06120907050f01030501030b0c070c0314030901090806 78
    0x9001c4182c01400f591400e400070b10b9200c80140172610b030403c0c100b5070360515500c02d200070703103c018010102c0303e100d141c8103185110f0815541d90709401511010b080144c1075000040309030561203400a030626074103d00f50080d201e107501c00d000503119035541c00d101e81011079503800c0310a010741012140700e0b242054a0850151001864419107420706858100014460102c24a562a0a400780014910f9280000b000c0e154400e440d5661800c04171401910250f5010b1f079240040340c621001400305502c50021800b0380b100000302030901c01510042c0c00c007101c0c4107040d29030020702900c4050082208a91084008040600004000c14039020340948280a486e100801e0b07180c42e4981d140b816503542065a56249080c2003018440c00d20004169403150786100751070240e00e890703264181d15030180c4580390403260030a814441320395550884020651002100300c0d80d03030408000c0400416498080b00e01c14004800c006c1d580c07200d10034000360690026600c0480140e202c0400c00805400800600c80 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 304887365 1250 304886115 304886119
    0x309101e0509190c05040b1806130209060712031401060c03030c1110060509010b1e03090a050601031113110d110f0d05010906120b13150c08040b090304050a0302 71
    0x301516100c540c907040801040e4000c1a061403c81007009103d101300c000700031110110340401620350002c0c1071000d800c0700c1070402c1c1e80c001c0000340000c40700c5c1403204c240b030081904201c2c0140b901c00a0800a8400c0c0c00000007561302e2040081c078004a19054444c6806001c41704100090075894400700920702e00340d10400404041e103422015443c00d010380300008074690188181d1704140458140180108290321a09201d03450007800082c110108008540c030301241e1902003101000c603200316203031a5101034400c20f500e1058441c00d00c040303802401011301851145110115131008203080101e1403980301403110703003289400301041004c0750b2441154944a02450301081e00c4c1d50511240c0024050004161958080010011000c00c0355a00c800e0688401c40c04c1044025140c40f403840780440713981c800411100014000c00c401905040c850380e4101c1c85460200654409407502206540c12140e101d00402d014405010800026121460b48119240002d604003440d0400080c1d51080d10312001e4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 304888615 1250 304887365 304887371
    0x9050303130303060e0108011e020313081e0c0f011a013606092108040506070609020402040b0a082a070203071d0103020118060903141f020309101e 65
    0x1094041e4004000906005c0010081907070750744205806400214194429100490100782a05c011442030b00e0045c0300306100c1c42103540403075071030055507800380300490310f25010181b150710815804c0c00200030b0161a10050140000c40721b040a09443c0c54608a554071500170b0501d00141e68042da1321591195417a44ca4001c201d0200030780190b89101e42903010105940250110b800d9400c401313010115000c05011550490002c00c02c008850340b00c6100415605c2d04110410039403903c4406048051300030300001623182c040342d00080032a0300c02e03031042d6400000070074040001d90700420100d0344900e4211012094600e003001170314410b0005051161000404a09142551010040c1d04064107921800104d20318583c440314054480901c0101d0000e080c10358202c5c2d01c07a1b0315401502c122203180d00c5510019095586051800e40748442918032446007120f00720561500030707a2201c1d0164541001a84ca0400841c2c00b402d142104000c40c11607420569a08401104504100c0c00303010868000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 304889865 1250 304888615 304888651
    0xc040e19090209040803061e0a031113020705010504020108060d050a0303110c1b030d05133309030201080603030a0c02040f020c0a03090503100b03030901120b03030a09030b0a09050303 81
    0x2640102101c1c40c0103900300c1050420442005000001117000d00400c40e07007038401e00203031010204010380e10b04d205a0408500d0004000140a400f41400e00000c01050b80c02c0300c40c00124202d0481e0010301d029a5607030b44400921042d560001190b40c0c10841c20744804a18158980b40c030755840c0003440c03004080680d1040014216003504050704c0c070340c220718802e4071829000c01c034882c0400752590880611034028a110719140c0da014500b1203101d80d840e01402c1440c2468203880a20701c18002050902426424861000519181c40d22440c69034990700c402c50300606500004004050050000707000b42e000300244400d66400c4100388502e00d60481c0c000c118820700903501e0002e8028604031144901c40c01c141d610070180c0109801040d14020350032120126050095403080d030b4009101a90943c000b040b02203071f1544203184039034480305c1030523021850610001c0072038659409a4050360001c0c20391300007030040150b03000125030405106903060014140e543c41d42912880060425010030b1480504 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 304891115 1250 304889865 304889911
    0x10609120f02151e0d0f0b030706080402030c040c0512060a210206090405040c08150f04030e03070806070207170a112202030c0304060513121202090402040b120c040e 73
    0x11144449010811600182e4948078440002d420181c011170302d05050800b0240511a40e11074030002c4040180200440f9140038010b41d414040030340141e801d8002e1600e2050aa292402046043c4a595545031344d21050003100c0025a070000e030529100c4c0710519001c1010f4040c0280c0d600d04143c0340c04420500b0782c601c7c800241c0350710454410540160a00c000c110500c5118a401d000b20703164041039030b0201d0706810f10710300012760844114504070980e0021a000c2445030068001e10000a0304488500e500c40c0c510f10301d010000c40d080001031b030140b00240f01151620041230550031440004298940c074543d140260f6840d8108841d006403151400c0400048440710a82c00405c0307951021036980c2843d00603080168812101501c8c02810304010814541c40d13810000011391b00719030310810121651800300c41900c0c1d40c03060781010a4080c802c0c6005969284010402032200304161a50703000008642c020300701c07000340141d2400505002c101b001000900d01283d0050303600110940210725040c0e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 304892365 1250 304891115 304891117
    0xa0303090b0a2007030218010f0b090d0f061d0708060f190203010603050f1f030602030601050c06010b070327150c0506040309051c08070609052103010609120f0215 72
    0x480f040d400c0d03c541d100c40110f81c0b07011901c403081c0c84c0241c0c1e40d26030704145410040411803082c8112a507a003a00501081400d000d80058100c03060014000075035804203407100390104d40f5201d425140940d1341c481c1c0c00c414074003c1440c105440d4140001d00501d0386803c000c0da8440400030840c080424240340050514203181b50442c40c003940240045450756150000240100300403030b01c907094500440301188164008045902041c00c01818080d07003903013540c2d00c8201940014109a060090a0040c003003a075100380885806020b00140141e11100c66003401001034560f440d003a220115480a01c401074648150541d0a40b410340e089000011044603007110b4001140f0009002405035906200070540c0c804554821100c00f265080c86031450b600e01a01481e8040c00010032452082040741d0001d0365076041002024007aa0540d80e230840708140411000600480000380c4000010040c0541504800e9040182400d113100c440b041400743d4a03900001d9031640d010307100d04841c0206d88480a030000c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 304893615 1250 304892365 304892387
    0x140c04090c15091d010f0b04030f17090a080a060b06040e16050d0c080610020d02191121060703050c0f0c01110d02070303180809121c09060206060a0303090b0a 70
    0x140485030828444144c42441c40000e0140f45000c05034104001100c4003004285e0b030a41e6000760340300880025a50b070350040549036841c541010403052042100b1a41d805940800901280c07000d8800040e00e03241c000308503960380e40d40078030900c028001401207003d04940d0301d40c4210a00200c1301000021a01a601802610809807070241040846420154030187c010b0080b4003c4d60f07025044142d4143c181d859003420007032940103030300c90014841c10403001c400a024150140c4400c0c0e400701001c00114111100c0d42008227003000740070040c040410001c0002d180d02890603e810002810021503840c41380c4680d4455003c00070010465909010083d4000d4040c1001c0f0800c10350f13035409406880380031390896034050307010074a0a0304844802c51003041c1013502d564000070103482c0c03a2001080094043e0f04044e40d21492041c0d8905003901010080c07900128102c4d41c85006031035240c40710091030034030010100340c004c82c1603403c20400650090307030500c19240350641c460340760040c0d000100c2d0400550703 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 304894865 1250 304893615 304893629
    0x80a0f03020a05010f06150906050a05180307090207170306010207090e011805210c06131a0109061802091f0311070b040308070c0515070905040504140c04090c1509 72
    0x102607441700309140d882041150100200b91402c0d031650701c002e0b06c084145124203008101f041044e50070191266001700a000c42c40342030381c1c601c0e5407204040780c60019a43c0010702d20716170002d448024014048500d405904000b101d0a18510b407a1000035203d048c51f102e103404143d1607040305043c0ca4002c1d0410303002801038581501204600b82003050340c80b40300203e200d02d11070700010002020400881110700c0154084003c0142d83c0f903200342505001d81c80001601c403800b011f0f01418803000130944480c001e04038400c001c00c0140c24103260440c2c600400c00503480107481040003103000c1c1c4403040d1900340c41081c2d40840411100a0109401600702c0c0d00e1100001d0700001a00402c000b449500c480c0518004d940e145030b00e542e41c020548024242c4171026003142e01140c0b013803190b2035209070042d51080da2858801390844c0e403030011506544081d64200d468061110b14038114560400c070741d0740410f408890034008901540c4511140a52600900402c44180000040704078050600c542c000d00d51 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 304896115 1250 304894865 304894871
    0x61906080c070f121b02010206131a07050c07120b070c0206040b0705031c0608030403260706090203011a011209080424020c0603072a05030c0312060901080a0f03020a0501 75
    0x110700e03020048000100030718001c540c3e149035101e41d06100302485c050003681a0002c007030306d48403141842a0301075125400c079280042080a1032140038070800441c002c50846d1612500c500759900101e04244094002440d00001050ba03480441c9410094a400c40518108108500c80c5400070608034400d0780c02501d03d00c0c80003c1c4050070008000010310f280c032a4840c0001c40d40c4480c224032000e450191240d0481540148001d1001c2250400c180501c0c206841113120170511004192907a42c1040c0000c1c5c6480c0c2e80d40840c00c0550800307004000c003c24005020042841100d40042d00e040000541c06110a40c4c482403130f41000400d0040700c01400c031410651050115400e8900032542400e0b000074014041c00c41403045508044003a03a001c0c00580e2144031010100d42003c0d08451301918074500c50035111003108000ca8401d10090140c1b204101c05103985070b01202c1c810540140140169000d9002c1c0401080850004955000c00507032003146400e540100e41004c078505001070801801a5207 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 304897365 1250 304896115 304896143
    0x11509020c150106090302040f0603030203040e0a0212010e010e10050a090903021906021e0f0901050901020c12010516020f0c0f011215050f0306040b0103140307060f0203090105061906080c07 84
    0xf82080d900c03021030780b0842e0b0278000c50b032000c1c0083c8143c03545403000a000d64001d0000713120700d00203000c1170f56000da00e1420060070b105100520501c11f00d4203a1040138107003071280050002ca43e44d800b249134050080c2c000c4000003441c15010440d080d98510071503000030b03904c100c1e8104040c400d10140b55110f251880620b114402800e00000035400051035507581035070b2209204500384e00790151004280030008650904040b0001920140e1204d81c5050440c01a55040583c0d0340d2526507111091114800018003845d020004c2d294513810b0740c2e4141c00f550720450f80759000401c0042d00c0c2506071003c0d50034803215540180183d5881c1c0034040008409803c3c40c0c2c1c4c0035001d2607000d40c0942107590884e40e40001d800b01d54141a2240015207014191500c60b20050000c159a40c10202d1440c5001d001c0360319140c844e4584400711411b80e440e1452454000043c40880e4509000710340d00003200710f41d0b070b090240401002c005001c1c100d01c80c1106016914000580041118066902058020082c9000b840d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 304898615 1250 304897365 304897367
    0x1101060803130f03080a031a1305040c0501030b06070609060e0303010803120c030103110f030f150103020307061e1413080309011206180f020c0a05070f0503011509020c150106 77
    0x42c0041d8841000707900482c00000e407074000b4002d1a000c503608a00e000e403401425440c200c0203030100800560b041010460398030116151064901c003920101d0000180d181083d143c43c15000f5910750040d4105800e007030410f41950340c0d030011601142d6002c400055000c21038035044000e0120244c0c550030f140008800000e07003100c044002d0826a13204600b1070050741c2c4051114046000a01000d0401145042859450b0408240c0c9022000b001070440b0717100080d1f00702862174504500f07040803004905100400071810104184006003030181401c2c24103051495489950540503250030b8200910200c440340854030090480702c01c0607000c000000042d450365009542e96003c03100c0301d1300140510600661000681c0300707130025503108004406245003001c0c0c00380c02070300701b25041d4402d25500300600380c1c8040d420400c0004041c8914040c00032285011407080c6a15181c0e40321502a9041c10000803c0c8801c020040302540c500311300050300e030220f640403d841c24090219080351000c80340d001240207 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 304899865 1250 304898615 304898617
    0xd0615020a060c0f090501030c02010609050106090807080f03030601050a0306211e0314070303140405070807090b0a03020925030203060316140f01050d050c19020f0607050a1101060803 81
    0x2601480c070600c1043c450b04011114403640d6081c250015403408814403056121382c018043c5003100b44001b151042d2940c420303c0484d4002e81c40480407522083d02044900402d00102c0000c5c541c26028020044040c3c000d10b4592000500c814108440000d003000468000e90002e005084060f132081c4c1200b000e480f0000d01c5020036102903d00100c08044509842400301c207001000340c0c596a1258114050b1000420a0708840411402d0640b9941203080703075120588410b101e20f00441c001c010207842c2c000c425040c558540c000002c402d040c400107090f551502c15802e42140e03416035030030305d40d40d641c600d8103034005421611103d021149400c0300107403c0c0d07050300590700078802141a04c1c401381703003615108a8115035124801411401136400c080030710301002130b40350310003040c14824a0804440c032000c00b221811070f03614852403c046214032180d844103440d150002000e00081c8048441d0000c2c3c1503440d0401015402000000283c1c1940503100b20184007201138000000d04c021078a4059135138807 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 304901115 1250 304899865 304899883
    0x121f030312180f02040509010e0303041211071202060901090509070e090603071a030a0b0a03060f14150d02030f0d090509070c081e250204150501140d061502 69
    0x4250500c0c203050b0403540180c102c50040c03940030030000b03414045075003844058807004010303040c655600c9045c0c086400060004520039441400f140e101c1070319481c0d018008003c1d4030175006159001c1c2c081800760060035024044d101d60100c400607112000c02004079050b2600d50401c1d90000705a100380f1003526040070351a056408101c4000425a0b1b0700c0052568a2409100b40480180090304030130241c0e0394440156009820182c0202c5c505071540042210010654000c039185962106088481e2000384940000b0014100d0b2000003420944003031210a000400001d100305d807070f00c0d860307021550208807048500040806a400000301624064612a52841031900550120300026102031090620500255100c0c0a045c2404641ca821560840c00c0704880c45403c0342c00c11100c0070030068076002842000c009269190074003841d1040c8000c1d00c00d448034070385030004000014002a03070860002c01c6020055144142c94820610070300780078188561101c00c0c1310508450b2401408d5012504001d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 304902365 1250 304901115 304901147
    0x40f0e0705010203090f1c0b0103030f0305011406180409060e0c0f03030c030316092403150f090c050405040203040303050906090606150d090b0a0605010e03060606121f0303 76
    0x8140ca64840c0107a031244181c6401a0303100c94a8440302c011842d044010070320310000c0083d4000c0c5807805a48840580c80203070002d40c00304850150a910607985070180e1805046c00c0c5041c0760a00308604085100d50081c01d21150001c08a003040111544490340305d1408079030030040c24400454a034001c942c45e2411000c20718012080241d02091a08000040728140186c00c0c1c011072540c1c2e00c02d6a161028801401800100800d0b00c05c0010310141c3c40e04c140403203501d000100c0d0701403000c000e0064115040d00b1100c0c00d165542000421944040406400407034038080c602040c0c130070450000b210070f0320481d080329078020f2011080c0800d156265010303a1140e4604011141103880c2c0b0003c0c1c6a40e00ca00320b8500780e01421010603131141410540c0600f600ca6184d1101103152916541ca00c21f204004440c503100d5075a84100400403980e01c1009152402d074107801610490801801040040c4603980f100901c000840f000310700035031a0490760460450100c44c40300340d0503449140c000c004807200e051580e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 304903615 1250 304902365 304902373
    0x919110102101a0906031c0503072007060e06041a1809012102010e0409031d040c0206010515120406020a2006131401060608040606080f0303150f040f0e 67
    0x2100c071442d220340b0306401030524078900d140103002c080011341c0300700905d01c0380c0600401420724006202940541141c1d81c5607101d55480307240110000704000c110307011070100400410103403107040e24082075101c2078805070300d462444c414160001c28124070465120106d02c900c030800c092080031108000d400106424a2658000700900c810404150028099111505030b010140550030300058400080c03c0c3c0306040a61070955a64006000c68003c0002500414040300510194a07000800018120021241000021104c0f880255a004140102c074041d5034020409200c1c0703080c01095510340e08034800c00021601e080d00c1c051010350402c80c130384000704400754007000400307909942000481107403500034000781d40c503a5000c14944c03041c10404d0721014090120300740855402e000d0b00e03015000350f896150f20341c00d240c501481181d01550090743c89400c4120341c0c481e02c14011003120342150041c40309640c0c58142030000f89103141610380301a4801d18124941c000955960000da100400c0700042e6 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 304904865 1250 304903615 304903633
    0x71101060b0c0f010e1c0302030901110c0a02090906151219081206011e0e0f04110403020316050f130e03030a0902240405040e07030c08010509061f0306050919110102 73
    0x2c0c2d441c2030483c806100341b001800341d00700c158440d87c051075011014000100d000c20b0700c0b0f00c440381a544010b0640183d90040c0c5080010b50410015058001a00e0b20040480b464445010703406441c100d1000380c40780400d12610100d0344001c21107503040000c59061601240c05525100e15254043d01000a080640f8000a0810760180345809810303c8980008500388040450407600c034a16100700c554000909400030a040d190b9124600602606000d2559160b055004241c0350070207000d0707070f5a60048525000d115640754005164046e5400382c42000d01060000c42040241030080e546044604c0301200b0000742d610142c04c520350650094602960034001c581803024203920889210003032400401007000036050131361205180d81410016a2000ca880365a0a400e038405503101a2191391540e09000c628801071040540000641c001e4400b403681508075611501b0a5100c09841603a0b074800041a03040140a05502c0307000703003540c04a605031549841d900c000384070652140140302d1a105 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 304906115 1250 304904865 304904891
    0xe061b0712050a2a08060601090504020c0d05070305120f0f060607110609030a0203030d020403020a12050c010c0f0b160f0315090906020708070f020f010306030803071101060b0c0f01 80
    0x140c006265000760280030301005a0720340048192482c00c00d02c20030700c060031814400c00c41c4c0d264240094204840504424203007500014182a01070700064440c0e403042001c0c40100d007000840650408443c10b0582d00c0e1405c07810156502d0003201d8200d1001c1c3c0d00382003001425140700e4580c4c1d2049142000040d01a12400c052203090f0182c0003006011840d075074541400c51804501404034818000c040310740c4034070241d0110381142c02155031600c0c200c0e0081000d00c11031610f60302c1030000c1d0225440440c1126441e80300c1030344d1001100082d60504c1041802041408100101242c9060700304004c4503582c01c061403071042c520440c100490010f0314508030492254420701685540100400d07840c00143e0602d11040010800004100d4007203508101a0000428a4002d415241c0c004c015000600c0311900510007200c4101c031004d8101454000e05000207210101a290480114a000300c200a650030450b030040100f900160100c03600030402e001010000a514400b04003201c1c001d100400d60200 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 304907365 1250 304906115 304906139
    0x91e030c0e1303030e0304080d1706120a080310091a030f0712080d1b08070f020a02010c030507050c03100b130b090105060a140d0c08070c020906100e061b07 69
    0x303100c0030700881002407070b00032920a401003024065150f042d24506507070f40a15616201c0b49900007004640541d1101e5001040d00104a5100c2c80c107071080d40100000c4000f85446421603907000b8108400407022600c2c095a8405200161038911000c0045240d440803000c0d1504010030315078880d01c43c841c201c1c04039250100c0c20404861040003681300c0b68001d43e80754a00354001e1140c01c1081ca5440190000060240369541200f68040c0c5414000382080c200042c8220914105c4c00155440000042c00507640700059910305030700340c909152288640c1c034060341070585000d01903505110700c88180482003425404441c03206801c491483d96841d21090000503501020b03502036000c080b1000400517410880010012100b00b850703e031800c0d000c040311260958010300010300c60a0b5407103800c40c0700a40c214901580020b090708045882c0c0040e903000504480300242014001c0101c1462101c12900605452102d82c0000b810103450316181d801c03400c0b00580d4540500b03401d101e50180041d601c90050 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 304908615 1250 304907365 304907371
    0x304031409190e070e1c020d0c060c05060117060c0a030213141305040f0201030c170f062d060d020903190606050d050c0103020a11101d0106060915091e030c0e 70
    0xd44010b10a1b90300c0c4c100b13410901c40240060340c02103001c40c4c2010000e07204080d0301020b0062034403211711640d80c500b402e03031420310142c1120790010987d82404c0d48400c0c0005120358800343e4401440e9880e005440110007a01410f5005004010360140109440d02c20030410342d00d810064807802e008044211140050350410b0328094071100c01114018055482600003040c5122241030010349040b00e10203004c00041d040314407260008611091003128a4103188cd010248124404126251080300c41840710701e032140186881090300040c0e03000005243d4043e1002d4040003400d86086d072030000c185120b12208e19030100d40181c50611b000c0344a01c6c090303d054410b117411000400c2c107007000f580190025880640f50005000d0000c0c00c00d00141d20421180c41d550100ca10302282c1c11304000345e9103180c1d041c1a29000301d941d052440902c03030300307520403c50340c101d44152640f0312030b1140c141415142e101d01e50300400340091101100d0340d8080021242c5104403446021400301d502c0d91500b940500b00c00503 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 304909865 1250 304908615 304908619
    0x3120506130e070504450210020c040f050106080f2d1e0702070e0406060b07080901031d0d080c120408190305060108040807050c09100f050d080304031409190e070e 72
    0x680344402c1440201e162a520030445802c80003031760f803c0d6000901e06c000c18000540041c3c1c092b0511403c2802c080c0645403102203040800d100c194100540a4099000107180d0045004440c00244020780d903c09442500384280d49007412030140b00c0c0102d04401d0702100d00d0700ea10309010345c001c01d200550010080c880e503020350240c4032a90501d90060100c074005402074420684070b80011400d50084802081100d00c40e41c0d04690b611600c5002400383c0f01034480381d950104845418004140000ca0440342403002d910342903071a40e450020080450180f00d800354000c0d99548200010024050010160800c04010040d12140402c40c06c0703040d00c4040313528500150200300418001118040640300313291142c810b45450780d5280003c140c001b41d0880b23400300341000e01e40d801c003c8204982c60b10f40c00f07400b00340c03407181c0e914503070b41c945108500c0b000c0c000404000c0c0300c41e00c80c410f151040050710290400100007440b23003040d10000704d0320b038007090050b00081415000881d071200d0181c10100c40310840 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 304911115 1250 304909865 304909931
    0x180203190c0b03040302072418231c0b0415022502030a021503011a0c03071202070e090d080108060702070b0a0302090d0b0f0f0403120506130e070504 66
    0x6020315000e00c2e4001130000c805500c0794101c041207500602209a60340a08034425541c01c00380e80700f0042c11102000e03d03008095040010601003802c44100b511110440908034140025544011900c462600140b020f00c600c5038440384d008005200c81810300030381c000d0f01034414004150344110100d106048101c6815442443d2400440102c0e005d00d2101900040079101d08400c0354020400000303046c100c80100c1c0e080007005101304102212028403c0d24448007247c1001c10108016690740300d01c50010f411a500700c4000c0c441184204081c2d005030a55448501982c20000a41a6107106910041c4041250000003244491000490600c9212a5030092140b1890034040644039804000e060341019020841615961100d1301e2002e4568400c80c9018950f20b45100989048074010b091030311001500c4041c080403c0e4490200136600c5400c00c0c0008140c0c955400240c00001d05110900c4843d007803030b6066809103004100b107000c5502c20303207080c00911018402e5540341161201c40041c0685 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 304912365 1250 304911115 304911119
    0x607111519060e09100f0603020d02040e0316030c1101110319110a050a06051b03010306020f070204090602030601021203070c030503180f061006170a09030c06180203190c 75
    0x1c0d0103040c1c650740703448801c000800540f5030b0380c03460070050201c8415609a002c081003c0340c42486105244014440600c104205406c40e070002c3c0c6107098081c4040e12403030302d0b19411030503004203008071841c080354024000810303c02ea15001d044040c2054003038400c1c803c1104480320a5000355030072a52031101030080c526008442d031009034103001c401c00020030082000741e900c04007201003001c140182c1c069801003903010694a03140047c1c0b0802041c2e0200c40080d000b00c00c0c40c0300f243e1001d507810340f64002000341e1503040720301040d5401c1c0118403000c1c1d4810b050401c5441400080d5000b117016401c00e900387c400040084048562074402a2403850000c1c3c410001c00780803a00c01d00c0595001117050f0702c1d0350354140010446500d8441c6920010246801590a102001040c14801c02c01072003581085142d13801c0e580c01805a040009048803281d6403580031160816102d03455440003941d00020405c80003001b04420400302c0c028000407402403041052190070300340e60003001c0170559031007541186d000d4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 304913615 1250 304912365 304912381
    0x1005090604090c030c060203120a0c14181005191103090409170705061006021609020315091005011b0f02220e01021c0b030d0e0609060c06071115 64
    0x202c6a442680d0303840c108403002c0009845120b141780244501e600440d143d001c0c803600c222340304002500440e81c280c80d146040c0c0307920390030107401d0b194a02c0c180310f01512100e00304d0341c40d90520050300c101d5074018018902920040d400c04042d04044140c0158903075400d019400c161800042810124116402070180c4c401c5403800b6084844042e00c40c07410902030261000342001507800014080322940c0080c02003151003d00c1c00c0070079004151620042041005a4209041c07803949030241a03c425000400540c810404d080360100382c400150012180d468400756030504180c0c8ad00a507800902907150300e00c001382c000702c00c0c545c0568020384550080d0f031990382002410034554480150403002d0445445071500c003441880b20300c0b0300a00000d6a41c028140a09001005411011200d1403030501304540d07070b440018060f00b204841d41840300c40c1d0340103100000e1282c000c50071010b80c00400005c001c1c500c5500882c4950081007a0b4403041402c03c001d220490722072440a0840d00c3e2400e00c80c00047c090 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 304914865 1250 304913615 304913621
    0x6030a020d050f0601030b092509210201030e03040b04050618100e010f0507051005100906080f010f0908030c030601030906020c0d092306070219060c0b1005090604 72
    0x80451500018502046407080d4025100c0c2290324290021006080050558041c050b61300720300403c8628075500c1c03500f07502189031250303150f1040545604504528261600070030707103c0081d00c5040b5100300c0001c18500044000030811004a00190400040d034100c0e042c000103541c1030354810400d8905141c01c100600000303070412020180c071329501b070400a00d151290b0400c0b00c400c007401d65803051200c03003030400546090350202d016010003104020103404145c000c2004004070851410206450f141c0342d40490440d4515004000c0c175510f401000035452500141300c1c8488090729009200e0321010519190491f440400041c010b440c1c2040003400381c068050045500c0b5405040c00101d105c801e0700c500f822a0004000324400790300401820815640064080f0014140c0701c4c2005040400c00074030712100c0409002d200d0203140d0108580c41155600180700244000d4158480012a80c1d038034010f0503c58002d81c10381d00c0208100210302da00a003000300030309580c40946081c1290701d41009000003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 304916115 1250 304914865 304914871
    0xf030f020906120f060105040b160203010902030f01060e10081908040306180201030b1f030c200d080a0902030a080a1724032d0f010f0f0605010206060a03020603 71
    0x401a401c0024a40640e6114007429140d802d00c0640d2070540741c00070341c10b00e0300800a0001818040300744805c018468101e030884001e526400403402102444e4030207c0d002d8010744400a41c54001c100114542000544c0000c084440c020402c0006d6165100802126019070044920720b41007400083c001c00b076001c1204100034460340c40141307459070329150f0400300c40c0f0307a180c4195403013003a662a40541d03030b06018a0ba003a641c01c90740c24200c130942001404d25039000010300410700d9242da048556082c0600801032244083c0e44900001031180350003641c03038030038613145c1c0300201c1e9030100800c0052005214561072107070302900804510100d1746a00d10030360090344006e0204020004200b048807602100d244c01503411201222040d1608054108000703505050b26010b58081d821610b50006620324003c030300c03805803a0342c0c2e030004a401c20142c280035010350b10356059820f28088a6048a950780403404407000340404000c95034844004a0b21000e0030f645a03640b0104442017440585403842c02035030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 304917365 1250 304916115 304916141
    0x91403061b0f03090102091806010e090a0207020607050706080709151805030a050f0106141f05131202010906090b0a210618060503070812090103061a0304060e030a0f03 74
    0x10610880b45018074442d4012118020103940128082e56070341880d8a4402ca520602403c60745940b9101000034290003980161906c144124404141c0c00849903044906264024240030742c1c1d8103090500c2c90f82c508103803064030700041c00b02c000280359a21401107407003035882099803c0300141035a0021240d02c0c00850040c08042180c0c90300090b17594040041c44141440769000c0d004036400e00c1081d9003196410792280140001e2403848600b903a551088485581440c038902c0201c8035888401140c00d40500f03400800c3c0e6080180c40442e01c403901c501d8041c200c074400d0743c6401d86181c4512003111080803a104008800e03c00344003c40080b401601c0d060f40008952004032240c00751040b40300160780300c90f44003100e2088901d083c40c0d01d072083d13030103024040c080a5000b800e04a2801d07c51958036181c3d0b44081c40c0c40d86010609003880e80c03284d001280106130781c8207214241c00007400824620f41c002d56041b0780b100c0c508170500c20404070110079140340d503002d5110302215610910f02134001d440c405210701 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 304918615 1250 304917365 304917367
    0x30601180c14120906010503030306210c040608070305070819020907120c0f020105011a0a20011b030c02010c020718020d050f060a09020403080a030e0a050d030c091403061b 76
    0x80724006a080243c1124001c01c0000c03442800d180510600706030040e00040e000f90404c104021054450a01996022681111881070407202c10001d45c10244007006a40e070241c00e10800141d00700c0009070f030001780c4c1c1c010815220202c0e0b903066071961b164070501c003640010180521044c0580350010302d00d0b40c00300c440c3c140302d501e500222009a040300d0520f4040c1000c00d020b0804a11180c0d42407040d14050076094505031b0f41140140c020407414066880f0080c00c002d050680500d4014900c0007403000055100000c2c003c42214050070485015100d40030000207181c80341105a142c070500135544103c4042d00070f880410704000649420002c14a41c01002da50204800c0703600022600c90715114002d102540340f0207003084410041d603c0c00d580d00082c00300380107000501c0442c0451084901c0000e02d07042c00108860b0f40555241459540c602c050701d14060b180b1b01500c1183c158119482c01e1107640d4940e02c03096215040c00001c86151100c01d074040d445100011107800f00a4a50070044c40346036846 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 304919865 1250 304918615 304918637
    0x271a07030c050604080301061b0f170409021303120302030f0402090a09080309060609060d1713151206090606090e270d082811090406030b090c030601180c 68
    0x7890a4004c0e50100c4840758004010048039038400e170600401d1244101c50b0750b01540c0707600c5000c00400c04141c00351440c062905221800b00511044030700070f0040002c103540b9940300c4000f01e04004c0451006a44040c0190075500095210740f0071a403041d6040c50b02c4401e01c2c0c940c1d409000c080ca80041c0842d080a65030114040400d41d200069407240c41050000d104920300b0b0382c14400201000307030296004244c0806141c00007100b810715543c9848181c1300703031519061403400441e05495030342d01c0f005105503002d420300f03a0300c0c0e40080f40a01040340b001060041c1956010210215030051192000140d0505400c0c0030707103044038011540000400c40e1441c8035140360552001c268401074280d0940f07520500303040402c0313500184003540c1701031443e0761000d03041d2003555a80140000010741002d82c0b944e0340754880310303290b4450030b42d03840000140c410405503450386000350140c81c0564140880b44100034500d4843d180000351103060303450884078045e65013525000400641714203580d0304c040c007445c80700e2 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 304921115 1250 304919865 304919873
    0x507031b141b0105010f1202060403120203070804140f01051303080f1e030901140f040209101502011e0203012117030a0914010b01020c01200706271a07030c 69
    0x1040800c06070b000005825450b220020801552552012462400300c900040160f0344180940c0d0459402c038140c03040c500c4603844100d08502c100f0400421000d00400d002c2a140801407404100400a80307031450f04d031b003010005603254012440c0c8860500c00154041c40010310741d42c0581440700da81e0444904010180e04210b0000344925158621010f02108000d042c3c1d409010381d40b030480012204504500b89170002688545008101901881c00140420b40600054403c2d40040c09074030030102c41441c1c0d01e100240078058406005812410065003441807907002d00c00c40b41201c0300b44603281708001311040f07031064240001100b135a450807000305d010780c04c5054a0003984107181c2500c000401100620f00130090a14010f00c07522103a04d040c0700240e81d82d800042054405400342851030f07403c3c06615104481200c0c0d14090141400f6410300042e000c1d401c06820100c0c03e5030302c100e0b8500d03004101f460000700003171441340da04081411404001c01e001c5150041c100a8007924001042d941c05440d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 304922365 1250 304921115 304921147
    0x9160e03071517071404030201260709080d18090e12070501150803090f0913170705010e06070504030303020f04031221060303050d1a0a03080d0507031b14 68
    0x440580416020010303030f01d5050307040143d02c0d8045054100000700b4a1000c02080041c00745d400002d0510608903903078220701181d1104010288541038000300b0318540244010407010f402c1c8620943c80c0715610208000340e0040301e440c440703480300020840c1c2d41c1e841c00d4040741c007074800491810300501500030034501a81803140240340440c090000490a14040c1c0d1150f215481140d00040d242d0300280a82c52440c1c0e5880c885c10302c444030807242c1c01d1103500e68112041e0480300d40d140c006d001c420000d0442c01d002c1078501c06088054080c00082001c06004d0b018162501d208491000004008010510020b4002c0d4003030840400c1540b200c50070262240d49100100180040744c1c40858020440a100740f047c242001000c3c8281c41340c00d00c480361466802070483c0c06801d940c07401058441c09544007114018840d0749010100500241c0380319a00d040c40b11841d030100f850455514100710005603010700a000d0411030800c91440701502a108840c1201c0c442e182c581e003110b01b503004210407280980050 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 304923615 1250 304922365 304922399
    0x1106181017070207050f0103020f1c0b06070b0103110f0a2705090303090d090620010f110c060906010302090a09030908011113051903080a02070815070e09160e0307 72
    0x3d0010a0030508040400c6640c080d45150b0a04150040104540000c1018152444003108081512860a190700300f04007400707406450f02c0e0032480110b40c00c1d040c00005224a4101e030f0041c00c0e59454241003006104020410071191500080c00d12030400010001c031070802091014281d0111541c9450b042e0f03e003d540c000ea03400d04a550012050001c403600900c12507503014040d0404140c881d240100107400d40310003d0342c4118061400080024611080d0403c0500c4a24400100140d081040710f2848a810007003900100d07220314800520307001c00001d401c1781030341e800800c46001030760340c2007000000c1c010b402c0044041200700f00d00003401800c00d001d80004100781c1c01429484004110304440c000f80c5640c820b504ca07418040d012083c081c4a01300310016039030841400d036643c464800c001d92400d81c0561000300355116001c20004908000606603000302020358030742000715407140401c8000c002c29108214007a8400c002c9007400c2e802850180b80e120006401ea030215036607000418401c209034 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 304924865 1250 304923615 304923617
    0x1021c09050d170606090d0c0801090c1706040f030203092e170705071703010605090a0909110105090d02030f06040308060d030c1b090513110618101707 67
    0x9855a000700041800030b20641030080c6007a42202103003034403400603000094100c60040d030000403003202d01d844141800e0281600a14428a0a17a071104143d008144c008002d64485010385400b04e40014000b04d0035030710152020060200792510b84442c504284003036401c40035071004005103081602c81207180c19840394075000310040706071510ba1801e2882550103001c0c0410000d649850f450b082d0301340d10a5040001441c010b503c4100c14504445058100a00e4842e00e9401100009060b50301400400031040c2c291940c5007019a2148003000751444050024002c02000c0421101540325901401c5030340300051403c113801c1110b0300404d0800c854800c10600a8000780104001d0540002030b9a07000501540c0300924020282c0300186461040000104605004810f62009018140d0140042d00400e03808200c141042000da034134005400c001151842408050f81040340761140985d540d04807005103180c1030a01100401244200e0421a81c013800b001401402d045000c20441c0b51040e041 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 304926115 1250 304924865 304924871
    0x1b08010b0a11061e09010209180c0c03030a0b0a050a140d020316030f0203010509070f0608040501110d1d030306060d0b0303041a04090e06430f0311090a050d0501021c 73
    0x20884d011001020002c1144015038010451200d090300c03003070020134003c0c6401c28007220540729080c40c5d00241c401d040000700e1034800030082c0034810b1116802101c103030400302c4200141c4c0359640188021a50300c0c1c0704454044601074031060890030181118604948004c05413900c030841c1401005022074950010b440b410140300100b0110304003441010381206441c001442405d00e4214800c5c0210355501601003000000000305080000940049107182000d40000341c840c60400e0340e0800401c800200012040701d80642d000c0c0ca020040100c0303024640162019140840795034025014100100c05550588820407000402c007145d0b40c0405241d5080c0c241040c3d230345140c0540142521501c1000c1505900603405001507803004044600c0a0135040704000d02001050200561a4100743c0c241505161100081100d1030b078400340455200c0030740d441c100000310b038040000310315010f200502e84d04802c0d00c1c0401d01c2589072060b04000814814030001d032900036484407100c0658404403031480303480e803 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 304927365 1250 304926115 304926151
    0x20d0f050c040612111c1404080c15070219050703020301150e0703020a020d11160f0f08010204080a061107080d0501030201030e0f0604122d031b08010b0a1106 70
    0xd48090940e1390350843e050240899000d4202d061443d1040c880e00800c0c1ca0442a225024030074117400c61541c4c0c11905810f640c9515007400c1813541984101070484a5028000c68000e45c00c0c5004002c40c00748109500800098415082195507840c20399420f03a802d1244110020060f5424010205101c10491142111500c0e22514100141c0094040b01c141401408800e011790b5000801c072800c445a80b600c1800016054050350600d5040712031044580640100415150181130324041203c801013144401165210f0740207080b401755000d01e007025000b2030003d80200b50640c0041e040c03040050700f41854080c480d955100b5039480321a6041f1810f494200402c159a0035101c0c3c41c16140c0848050070714103001607080e540f0b503180200b0040c010850411040d880521a19905020709061a40001c5150320080040c41d070503080a000000a03040c540741c05100705250103200c40d0841652203c0b82580d08280da90480d035007010b41640d080001d10700908210007810070601c0e01410424612a280074 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 304928615 1250 304927365 304927367
    0xa03020d020a030c03030b0a03020d0501090b0109090f0803091e0106051e011e050d0f060504050c0a02070e070c0f0b0a051506070201120b0402030708090f01050c0d020d0f050c0406 79
    0x440d90450003401e541101c1c41d0782c0c010035000903020311119072501d0001010403043c1d001580c00c10403600023a42000801b00144c0030810158810445240240c1c032a0039140e03a1462640142c0c0e01481008140e0124090544c0004101401a603001007030042070780c5540072030403114040390b814109140c000f80e44491007049141031020340c0001801080d182201c2903134015002070444072007501350707621076441d43e9011140c507031241043d1600190b00031400d0014184c40200100681154003d840c841c80c90200407686c0072407024116400c8140b40d4020380142c80c645071f03950704c800c6802030002c0240031035603a0a83c0000c03021581c80722424407aa0582c8010b052110340802154001050b21309407007124100405165600010340c1c0415509180c403080d40d8070f00403445006440034840041e0414004003d01410380c0c3c0001d11f95101c1ea100d5400c8a0003220a081c909080e030740152102c0030021006c2050b100c000a017038004041c1841314460104444000703c1301d41007198403c80d404e0006881c045001c0c8100c1d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 304929865 1250 304928615 304928623
    0x100e07051315051c060f020f0f07030c020a090e0601050303090f10020a0c0608090c01030b0a050415120503041505120a05090c0d0b01050a0b0f310e1e0906010302012f0a0302 76
    0x180002d1b820440c209400382d13034990442d1165401a1181d03800208040040602c2030900381e00f441c2d40074101007001907a4056040150480c3d0307201c41c3c03081c0035240000c182800d00205680c510b020040002c0e0041c00700100b40150912805885001c6002d03280165002c10703002c01983c0300800250f6a40d441c24901120f1150921400d00d000034105401c0080c5042c043d518440c2d00741c15220115800034034512101080940702140340c0c000e10640b140b10305400180320011019108640558804118906244c84111018450113034010000100c0001145014030340358082c0760710202107000c881e40d0a040b44005040400386100032500a04008014415401c0000c1d10000410b030b0000d90600300f5034110350700f80380c80c00341001044400282d441c00c070304000841003004500c082d2028480441c141c071249482d01650301102c168070a4242241d0903481140d0030f454881c4500c20100250000364211b60046071325202c1d0345840040c2c902c2089140074200c000080e0900d07070711a100014407045142e45000b80c24 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 304931115 1250 304929865 304929881
    0x6030a05031602040605030c0109090203190608030c0c01020303040b0a0908040504090c0312020c130b010903080d05040303140115210c1805091e0604020d0e100e07051315051c06 78
    0x383c10851048c02e903640c200c1c40311002d503280401d0240e1244c1d1100c0001d0000050100c0a0120b01d052240005074414044010040b8422903810b684a81c4000001642d40384000c1c0e400034080c4d564000004c9814449901c59040230388116072143c68244e0340c00000e403d9560440054500c030202c80020410007032900403440000606001600d965030610000640e4078001200c2580d000d42ca444170188107a104012840203158404c900580b19640202d20741d00a09040350101c0110f440c101c000042e001011124904949135070240ca2180340c1c90700001c41d81c03240311030001c5241c080a4080745010842c1402406202d40c03050752001c1411004040c14506161280d2109000384400010300070025201c900000380c103141c00d1080030040d2034490109000b0b200300c1d070450364406c1c584500401110008113400081c1848a40140b109051161001e601c1d483c80e07100b5190303c0450100540b2400d00160059242400016409141a940d41d40400c1801f28003561000340c0e5a64002d0307000070021248a0885 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 304932365 1250 304931115 304931119
    0x303020f1306170109061d151c060c050913021c02030a0b0102060a0b03070e0c0d1b0216150c020117010b07021008070f200f0c040c08040206030402010806030a05031602040605 77
    0x45114501f41c03075401f080d2a24100c1c14080841800060340c10407480311000da0030360b00600f5100810f225450032030400d2400f150b00b1a80c060400740c3c040c2400c1d03c07542c240c40180c00700501c005031400e0744e084107100941c88a4140d14240904426440040c000d910207544070740c140c00c40102d0840303080d41c00242850b2000f48140d606515040460b0707420b45001416400751030001c0700d40c401588400001d40750b1402141c01200d107560400499041996051540c2c903104880e50302103406c401d5100c030101c2000070a0380580d102c0c4607101d08080f811248504942c4015600604145002e69001c00000051010036000707440f05400008941045061a1500d18540202071400a00c2030a002e00c0003030088118039420010801c00e0001c100c0b011014030003030b958040c80c036011141005c0040b41030584a01000d0089403055141c02400300e04540201c40030b40c400ca600900d618610b544a03401581c2c10f031006404a1341510401c00e034100015020402419040941e00318400070b0821481003006844003500418 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 304933615 1250 304932365 304932371
    0x1d0a060c03060b030f0f0915101410020a150b03030d1506050c060402040506041b0c12090812070501020f04060513170a12180b030105030f01180303020f1306170109 72
    0x1110303145007818990403044003e0481d02c60b8450007c02c52505a414145040b400003000602140d4184110403004451505c412412081038280410281550400a420250f0840002c0300000388513810a40040f60718084009503880528000c00d2a5400900c14011750302d0b51280307920b6008200010010041c4154544940390150f00d6540c2c070345070000540000d00803510340b4040380c1207607a150040118020002d00c1030b607203200d90307400080843c3e141c440292001c00c3c1c21442100e813903114040c83d509a0310b4000041421007507490081740c59501034401500c05541c00d021409803a15804c00074402003ea6075101525050600c603c098542e481c0e90248540070030b1402c08412080740840c46014485d00328003440800403408100342c4884144241c0c003140920b841d0701c0451094584009903041c1e400640403030b000340c280001070900329802d80803a02c0c0515000b001810000e03100390014202e00000d90000c5051141072400e91401100300d401a030086aa090102ea9002c44118925030040c0b002000038 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 304934865 1250 304933615 304933621
    0x70f0806070c0f02010c0602030a0b090705090303041e03080307082d060103200a0f030e030a0e090a090606151704120e04020913091e020906041d0a060c03060b03 71
    0x2d4000c0c2940c010041ca8401c148040e0019a0b000300748078000503810281c2550f8070f140c04039a42005101d40c090b01e030b104100e01800700304110710800941e40c1c1007401400030361416042c17409141b01c0c01c0c803010413400c001d510b804020001810031001f441c002c50f820b0b11842c1d00342c1856011420170610b001045100c20561040ca00d00446012050f19000482800e00080358002c242f22510a0404028003418000000035549041d030740c4640440d040c14003075542040603043d140500e980701c1c03007201064400124503d804040501d010b9000c20b0b08000d48004c0090044c4403075450400f41d406541c02400c043e005582c54200c1d858109200050f00c64810550401d00e15080e6614280f11401103405020440000c4c0c103480c46881ea68100c81d1b49140040c10390300c1c04030b016804800607041c2c0e5031080712448441d640d1113a0042c0b500d50000600b0758000c201882d590b40c0e0700144002080c4c0d108803581601c102071200801c41c8003d0200070b080c01d004900c0420158040480681035655076400a02182020010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 304936115 1250 304934865 304934867
    0x20d0609060905071a0421050106060207211203020a1b0b251d040212010e040c1d010302090604061d04021f090506070501020c1902150703020309091f0602070f080607 73
    0xc503400d541004e141d03403102e0300c142c14006608045c01a0008d00642c40c01702c001c1011500020700c5011940c8404190381304002142e0180e49a4146c4140101001c0822494a401c0380c06500a0b182000b468a080100c4000e90f209104e401085440142c0f07010600c1c030280092440780c4910300d155565242c06e682920740300c44c44018038010b04001404421150035061b90040d54407030701118403d504000c40c1c8980c0303503142d4841511100341a01d040340d00c2c421000c400030f0540351030007050302d00c107a5004070001e41d60301c0c41e000c0c07000741e010013040300c0da01c541c1da001c0100e5080d4403240c0210701200b0300d030b0f220302d020710f0035105201e6075500800801740fa924042e100f01c40d074182d0000418045d180103448440e100e030031a10307015019001d0072461020600076106c5405440300b0400d01c1107180b83c002c446030b101e0102c3e0101c4040302c9206402c00900180c0007040401c28606000003074541280c0c24100e48600f080400803204402e00c440e4000d0700050300700900410041c002d21103560050900a00038207010308002ca0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 304937365 1250 304936115 304936117
    0x30807110d0804020f121c180306110909010311010314010515070602040b0a020d0e010311070305090a0f0b090414011d07030f0507121b08060d020d0609060905071a 72
    0x2600c00400c004840018110b40f1617903d4185103200c05080756a444209190a0ba150503500c44a9240810f104001041c6944101c581d00b00d003c508900405074181103480703c0d005460801a04040c2003c01c0144280b15250201060b0007540030341c0041d0901e41e01c5100060540b181e003004441150310300c84c0103008643e506100d1b105003983c0b541c041641c4080501c1d00f100a070160350f105900075803000c52548541600443c541854425603611b20000420050065007180c4800c1c035080c4240f24240400c4001038010300080001180c02030250301c42607a2442501c804d8034440d041000715038804217158800c0d00303060007445200d000b40d2507000a690704184d08005191640c0d442a281240d024010504481c0643c2c030150980b9100c800600180c50180006410415038442c0200c196250103640b00c5240354016500c00500143d5a03810890b03140c0b1003c114201c1c0c000207090340d110b500f4004020009101d07100e0300344c240b44201c0d00443e00d0000740c101b450501d2035551117034024617402c000c01201c01c09100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 304938615 1250 304937365 304937383
    0x1508060910080304150e060703081803040e130201030e0609030a09050d1703060109080d080402010f02030307020709020f0c01091511120a05040c03051504150b060403060209030307081603080711 85
    0x190b205540411480c000c8645160240086801c07800002e102009d0551004110380303c0c1006510120021040310000c41d0b0701d1050380b0034241801a000e01183c0708420640298000500514010810846d105110b0303041c200d0a03514985560310001344d134001187c12209103c010003040301d540611144546494000180080300d00f4003031000000005d590340c2c0141c4d41440070380802400c40b0440202a6000b41002c0c4040e14168042588a02c0c840d841d140f0000450384161240c1d4040e145140c0ba01c0704d400003a411010004400b203605204c0001102d07030902c12619040c0c0224030702070040600032441d400311118034052044028082040340f01005041e15455081502010000340c941e54604044042c20140d800c000c000c1d01500d01054048000c8a800078060f80c0a212168541e88414215074100e4480d080e505410002c20300040020601d01e6001c0c01045402038207607850700089030703941c41141d80003032a1940501a0304008600381a03101c40004e40c03124039400c1c010b0111104001c80b5686019030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 304939865 1250 304938615 304938629
    0x20901090209040e07090e01050c270310020d050a110307083601050618060d060f1401080703050d0201020a050f0d061502030a0e0d0222061508060910080304 69
    0x100b0000703c0d1103940c03200740c081800c0b00c20b1381d100f540c40d0b400e800d0150818507000300c03266080c80042518a01c91000b10b07250b03400c4c400466141130307100c2c000c1580440f9010699540c94080c21643d01461200c170b000a2a52001d00007000400e80380202d03054080385e98404004180c024140700300905c050708600b80301d8220012003182d501811000401c2400030407890313610350180306060103280004c441500b00c0c40c0100e00440d10310381c08038101a40002040011540c1c82d43c030080e0b810801c0c01140d0307070f17600004000740310b02808203251105405135100d00c0720a91002e49158000b860800600a0038007003801d400040348002e51811800c004028241d0081c120031441001c00002c0f1414804000d501103401010345208609081c611004082d440360000c8403072602007001b080b0450319a02d0074000914080d03a0003080044585c0c00c008640e10711241c5200b00903001c0c0d41e61140480c0000701079881291920703a0340d48030b40d014a44a001d00c00841c2024150081070240d000c414800d0b008003005a9042d00d11b0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 304941115 1250 304939865 304939867
    0x80a05090c011101090510091401090308072f0309010f02060105060304120c020a0b04081005090d0c020d0b0f011d040c0302060a140706020c010c050307021b120105091b06070209010902 81
    0x7003c00081e00500078501c00a0083c49601414204e0300c14a4008558090198550600c00520b40c5403803400d89014000080c0090019000140c0c41401800c2004c8011804103818290580d18000014000c1250078a01a1a07201041c212501c1d0703800203c0451070310301840905080d5145c6000b042407408060f10040c45d00d4015a03070300400b01c0c4144035000d05103400620300c2000c43e0780d4041c003030502d6119014405450207001c01140303001c1c0c0c2a0080a00404c010401400c20f00080001190b0310324080508a030303c2095400d032000441c20728003409029050808941c4180e5141c10030466188030f10660007441da0004804020200b80c005407102d0442c2d030143c1d0000d50300c0d0324191080b5a54030501c2036000c42c0800100c0c2460600260f41e01801003100104000c0000307c101110590300703800101c52a10042c0d214050350613840045600000707007210003a20030070340c5440c5245e8281c25074604540014145e84180440740c040b80d4502c038130064800c03003a2801450500d280c4c001c20f964900500a4041070b80d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 304942365 1250 304941115 304941137
    0x90c0c0b2410080601200303250c15020f1b0d030c08090a14010609060902121320061209010b0a0b130627030c0305240406051806010f0501080a05090c01 67
    0x6e803900303155224030b0001056941e00c0c9042e03205000303030911f104400300031568004a0682814040c2215511040e040450501030203010151440a903104005904440300c05200c2c4410a280030140b040000300680c01915080c0001d460003030071910603400d01420802420240449004003041d1314a0070317a082100c0c1001c0e294019a0f03103001d0406076000101603072030107600046940c0d4a90203807030002200d0b82001400d89503028161181041d0350340190488504030b6201600c540060b266802140700a4055070520080742d500004010048851049a075144c1003004640d02e0030844180c050004105428104100301d81240740513040f40c0604000d103e1300101000c22503521000d20380e048440b40d00341007105a12850012411002440100c03140d215500455508541900700c030b010344c41e41c0658a0790715170780344d40f0380c1c5020342005000102400030762807655143c03030410320a0034082d0016028103085030345004001016282c0040c468121246400c00707100c4421130118680c04c070800c09203048034580e4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 304943615 1250 304942365 304942397
    0x1050a060c020117012c0708060607050c091003211407050a0f1b17031e0904090602030106110613022215060906020c0109090c0c0b2410080601 63
    0x100d00200b00c5000b95010000040142600722264201e40021500681281c1c948051b1b42c0501820741d018000326000100040150a0640280c2101d0713006038200d801c41055000881c1c000041600c03d410340b0f025181c000d105020700d82460388a048050142c517150680d28040082070031060052030144005c0c0002c0800c00d000c002c0000c503103065009800c0711020300061038801030301da05139104880404601c00f40001c031207244150010308100c0f5070f0091854441c0305003002003410260032030407201c1001404055180c2d2124442e80103840e00c1100016070300d50501c80e0187c0300800c0b9915044980c1e1011041092041900c2030300341c0425030551740041da52090703141d01c040b0042d62580001032180340c16030440a1141412411080322915242e9030341207526104100d840b105070800340d50220700d01d9042000611091b030b1108440000506d03050700c444425585480590b2001d80e0075848080d410040b0721800a9411ba118022a0046070340441303688000101a01d0300300001d040f2810f000d05482001011 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 304944865 1250 304943615 304943627
    0x30f060405100b0c0607030506010801181119030e0601050a03020f09060307180b0a121a0601090f1805101a032508090c090919110a03080703140301050a060c0201 71
    0xc2d10b01c0d0f114060b01c03080e0140d07281356244c00c112420000281000007003443ca5004101d0a4180d82e005100d040d00110490051006001125251014610200404000e01c885000f40c0207194100e5500401c4c00e000d01003460f03280220680040d44100040e02041005a403084401a2442c40584000034150b4440002a062094540c03040045003c045501001c074081035002e40741c0000c0440c1c407860280d8540d54030b80d6035040319100060000320f404941284e60703544c07641010340c4542e05140c1103142c0b54031440c941c00440b809502c040710540c2110030140c03020456024103980804e130b117800103045c1c0e403401d814016020107500303819240c12000008605c640107100c1e00c0280f0030442595400500060203002044e030707401110360210a020b0301a00303500c1031601d80507850240e03207144010005402425144042c961548404980215100901d0000c0b500d5402da070000841c0540511910340001c4c1c10081c0c4000707100901044000b00c2040180100e0ba10085510252001032038080c04140d180c1c80180c0349 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 304946115 1250 304944865 304944869
    0x1a1509030a11040e0a0b161d060d06051201020c0601120507120305040e010e0901180209060f030f250602010905060c07060209120715030204081504230610050303030f06040510 77
    0x1180030f40c1c2c412000f032251b1601118001d06e0100500c615008490004440501d0b00d0038641403202d6103540b800c2960300c0c00d00d020f40584d1002880004182e80d0740c20009410080c0401c203200302c0c0e50007043c14655510140040c0d401070560f2100c000c500143e5903140364545500340543d00032940c80e500d6000038148258161009003001c03e1a8810300d5850703540b5045036080456150201d1b609001c042030700d0303418100000c0c4156030301a01420064541c142000003100d07107050f003e03805219600d0f03000e00e11082005001002c070b1410710000702501020118030805c814a800c12000c0d60b041c0a000b4000400000f000c0368007a02000d040d648984203458801d001c0c0c450540056848062402c15000c00038001c03039040304841d0cc4549400102d0329440003942071b03004a2240a40a401c00381e4042a01428514415846489004450340c81020801070480300486900c6400e41036025808010052141400160241808a0040d0308510b080c4050b00e5906800520803402030f52503502241d0042c03c0c0341d50141c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 304947365 1250 304946115 304946141
    0x6090105070c081603060c3f02070c08070816140d080c010b0a0f050d060e010207080a0e101403150109151d0402070305070f11041a1509030a1104 64
    0x510041c0007144e295110865010580d101d9190503945a20345005241005e41411052152010040070311907103087c4001000050814503020f10382c0c00c42c042c40d05e10007416100c2c032501242d6034441c00c02d4401450100c031900591115448900c40004240164107810101d600800100329001d21a20104040d000b222200810703121020904280011041d00184403003c01600c2d40042550303078201d51094a201e900c11030303030010244030a510110724241c0101450711169800949017103102d540c3c010b00703540300007640c4001a20040a4000624041c5a00c4403a00d4040c9069006086c0c1c9040c0b044040c0b202509400f01c03803480b400d158400d6402150840001c00b0980088481501c0c0c4200140142500e00e8600c0a2042032288038a0303185040d20a41700710039090780c1d4a41c2021100c0d038400c540110010302c02d5410031036440c20710000340e555005031059030032040c0c07400c240c002001040c00518010354009907160070040c011401540c40c002030311841650082e44a44280d07a805012400410072012488 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 304948615 1250 304947365 304947373
    0x1a0705010615020a05010f050c09130902060301080d1b0803060f0d120504090b03010c170c070209150f0108160e010c050d03020a0212090607030305041a0a0509010c030b06090105070c08 81
    0x210289401050038130721140108001d2148085102009044407800c031100c42c1c02c0d400c2401011801c0c14441c07103405a1141501c40055803401980010344550401d07448603c10780d000b40f00075800c1582c08000d40c820542c051810203503400c0076607121207a901004040901400c0000c100d200b03695509200c0c0300f05c56800c002c00312a800106240140319601034051000114141040c0c2c1b402e5080500c194440d10903684d403000d03e40c000c0c216056800c4003002e8803101000109001690150f41e80040c0300b030040302610810088a4451014000742e41c510803070340b5042c04581c40810151007001b1040d1081c3c00418076100c403400190320016030b05041103060240c42c510400c0d0040c020113401d0f500420362640d15400b100d81c0f050040208800b5407044104440d00201d0600c141c40019006c0d80100703800c688030f00c041004a229048c01c8a071000d801300c3e50310a42036140c030140000a2030a202d003060032001450705101c4101100b0100d6120f01c00e142d006410000001512000c0c041052404806058440251 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 304949865 1250 304948615 304948649
    0xc070206070b041101030e0a05030a0311040f120b0f0f0106080a110c0109110a03050c040228030623030601052b03081006051c0908040b0d1a03071a07050106 69
    0x14000768107155090380e006c20314103a0106000b402c0081c1c40c071a80b0b030f1f0100c025443c011001d01c040b03014111505590550b014240030115101d864200e80c500500015801811404507074200747c59010700207030a401420514500344041c882c0c000c4c03131807415108079043c06203da8440898420061011540c841100400030600c04103a00040d00401001e03800b458a035040e90030281d04010124a8911004107241e110300140000703810b040d005080780065401084044007049100c0700f038032100344008100020703601c03d0240030400c608600c00c0070b00591303103121101200c00720020903507400c07040c003038144a070000d10040c6005185441d050203102040f100c105004429925010302850401d89100450300e219550114401c0d21401c01d441c0000b145140d00a0b400581401030001480340034010f8442e0001040041030110a24000f80f0242034400400240c030035160941000c42441c64071840d2094004400c2003082c2d00b18001201c41161640b00790a58030b1407203103440b5004250591111103140301c0c5520b1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 304951115 1250 304949865 304949873
    0xb070926010c0203030c031807150e0901081b0f1309080705010c0c020a060c0317010f0503070504050f271c0f3e01050103140f060c030c070206070b04 66
    0xc004044000902014810040c142d80303074002151040d0001c0e0060001030504503040c221401c00e8042d102c140c42c00103482e805d01080400c4180c00340404104916100042c509000700300c1c500420202003c0c021508206000a060b25400c030340052090b045206109030030740d43d40c80703071000700c0264a1041000061030329001c1800c1e0802c1d4070644155107018030035095540225445e03009554011700041e510b9003412400c0d20340c880c856209130b0810030100c01041d0b0a6501100c031902a140001903c205180380600709858001300c1d81006001714105814400301119500c10300340c00c02000340c0c880201d9a80d03441c1c060079646104450f18864800c0780a02202c0001c564020610466284d07900b1074905d000040640f843c110100d10300078803400100c4139522080c1c111103103040c000c1c51844080701c003051140d03543e0300390750f400e03001564000e02c80030302403070074840402c4520320481c000380c080c00f840e103031601c15002240001007540400420000b008011991a10100c400003503205c4200081030a103410 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 304952365 1250 304951115 304951169
    0x209041509060609090e0304061202070f14070b040b0a26100e0603010e070603150f0b0c01150f140409020d03031d0c151e030412021209030a0b0709 65
    0x401e10303012402c4e01401140c9480301c3d00034030310440d4203140218a02803420100302c0d80710464802c65907640340d0910461380010984c0e03480c00400c41c0121001524203010b4500181040d965602a600c00003041108010801e1130000781c44080340e0b070b410b2944124201012000721018080c6110166103080e1081105040c070711000142a00d030080b0313240c491560f40c41d060500b00c0d2001b4450b80740e2944850810000c2a1085c1c202c4480c40a1b1021009111550b510b1010901e0581d0707005240c090501183d0744200200034811010f5070002245140c00c82850500c0310700c1558860700406039a8030400d01c00d0b40890b226030300640f901960140c4002d4405c0c10305e041c020002d20b45040140f5000a690400900c0c900000414400010b80203120003031020b802c1901c030a40d40e102086140c100c0c001203961022403003041004d0f40c405ca02462400d11100c3d8103000090808820f240f48504158003030000c00100e0f200021011580c0d58401c1d40b5810701d40b6003071000e54211100c4d03403010b800301c0c02ea091941400400c0305 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 304953615 1250 304952365 304952369
    0xa0c05120c0a030f020403031d0f1201050103051b010819061a2106010e040b130c02030706150b0702120c03030408010e0708210304260702010e22020904150906 70
    0x16a013000302100b45802c0000b43d02c114440079002a00c1120091410f0b50211000d145400d001041c2c03c0d4001c080f036010134100390069500600c03a0759268010028010700f8440441854410203140030b000d58848006041444040c0c15040d85080704124200200d03035907480700c80605001d03c1c003925242101a0701540c1030344418030322400c818015020002e00e81c46000705a014800503101c00e00703d840880140401886c0c3c0c1100340b613000c080c202c1d08000911f500d10941c505210268095580c9003c00c1c2440000e441c02c18142c0d071035400070130b00e007080800442c0c4c0960361196030454508510304201d5210a240c0f405641941e07030f150100180c002030703400c1e0561000da200d034400000c1e00d807000d5480140c6074580c002483c03140074540801141070060003c03a801103a01511545401568800201029a440003402164000420005090015580c00400700d1100e04030403600b15048880c04c403249001011481080d0b1401c0360085005c4c1d6103a95160000000c01803c0d401c6000f009999902c0540581007038 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 304954865 1250 304953615 304953617
    0xf050a0c1805010e070f0c080a0e0a14010c0305030705070501111e0c0a1205130b0d0506031903050a030e0f15090601060c0308061302130509010504020a080a0c05120c0a 74
    0x312030241d0520640d0244a0499109a5031504c1c0c07559511000c2c2c50001c020300b0510100710304080d400b07001606020282100080355a0380e110200741c810180300900a154022585240d075403188034800744e900c02c044141c17040d45440c0403070300d070386801c1d10642f0f03e4098204010300c10350030030b50385032503075030441001c2d000360441844018090740c0781c02c030301d80404c1c42411301c01e00107070300009200b501181541c54545a800c10501e841454050000650031314004690001c1102c0e00300018000c4001a46002d071035000501200540301c829168000c1c44120200701e08000d003400004170704507a800c1d0180d4061600320070100b003a2440403001052403501da0402d482094102c25112010404145000076414107880e0a61a0480c2c0400c85132010b50712000000c080950000d0341d000d078071a0002c114006010112410000609418140f10411000e10016081140160b206105606030f80741e11074030701d82d0080404070000421040302201282d1600c58800040300781c40300e08040c8031580160200a04d030000d46 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 304956115 1250 304954865 304954889
    0x30803130506070f09150903080c0a020f042f090409050a260d0203041e05100605010302091e120105100306050708010b22090e100501051207030f0f050a0c 68
    0x83c41e441030fa084a2104200000501d1120f420f000c00380c2510b241d24491141c6040c0000810b03a01d54400d626030307001c5040c44665400995895086003000c00038000f2802e400c0341e05106c400d0140d100c03030003e005901c0020708005d0380301051031541c0e0800c1007203400306880030780240101c00650420588c0c7d0311414404550b2010125612940f40c2041300c001c401404148400304c2c0b400c4409070102029404c090800c1d28400180c80c1074000702034002c04010402032180303014001110a10390100c04581d0160b0141f41450300401c00070f0141d0395118644c46070408000900d900c0d4008240219680c1d22050b255880c096280c0000d02607015005560002203034403508041c0311690b0303802001c5070300360020312411034041c0007031118566503484411000625545d45c1c2d01402010b9035080b0440c00c1d140303000b40041103a009048018140203d90203001e000d03101c00d80d242411030404411745995140c25202c0985002060b086180400c1480302c081d140c640d03000f00032a070201e10304d41403002503141540305800255403 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 304957365 1250 304956115 304956121
    0xc09060501180b030105060c100603320d110a06020409090215090102060a18210905030a020a0303050906070c092711010f02160b030603120717070309030803130506 72
    0x450b6441d2601500c010042e0030b400c591900c007d01030640c0044141039254001c0d01828120303480c03203201d02002107001b8200301d544a01c8104c10500d1b005444000c803021920010a2110026000140081301c2d80c0c03249000d881034406100070030300340800c0d20f8004120034000a00003554505640150080030300840d00140310706818204441d19100388901c042c0541c00000c005490340782c040c2d00400342000e0980707404169003c5640d41000c1148000d10b10050f4140c88204070301070f981c0c49032580c80504410f0380103041d901d082d9000a2000f0003e4840102044000600c1102c10b840e4942502c000f0355024004101072526414410041c0c00092010400c040d998102070b80c08204d00031206102d19088100b4040d1070340d040004542c43c0f0b8110702c001c401d512800c07141c10541c080303580d00c540c010b1401809868407818140c08040c00c010407040c00910030207040c0b0a110101d2940700c10459144030380d0001c01d5480c100d6141c140c030303075140716400a08014804010400c0e003608100d03518040d5481070040c0c641d40c0e9 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 304958615 1250 304957365 304957397
    0x10306050603010f03030525060e070807060c12050c060901090b0a0b0d1101030e0a080c1603021809010b0a15080606130e0a0f090f050c090c09010315030c09060501 72
    0xb000c240b051100c080d031100001c002290041c00249000703051a881d0302811500c0480a01d6020055001114526521107441040f050140014800b03858a100508009858214000c1c29071480460240101110343d41c207042040c011000c50390050b0040c010340b403883c50712050490090600301e005a440c401c3d0140020400c401511a4049030300e00200542500074254607643d27008420003a0413814135646070b1071001000d030100030b08a049c0b40304405466680d103c02610b98104102c9002100c607000d5010b609000603548c00c0004410700c5c001039803901065440b168554050306000c02c800d50010020f54020030040c01969211032101015103402803140c6540c1c00b170100a101c1e02e58103003042c207019001030010300320742d10782e032030300446110800304504407008440306c2114000a4103c030b0815003000220200030040c8500c500c0384078102c8101c003007841d0100944202d403180c0c0800f18109075640038580d13010455412a0700c06940c1155440101c6070b12000c15800502460103060301041e0000e5240f0216 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 304959865 1250 304958615 304958617
    0x91a09310c050714010b04020f0d0608030c03070b0a0b0a090f0e0609070501030e2803090b0304020d2a0e060f0f0604031112030a02070e0603060702070e0c0c01020d0203060103060506 80
    0x50540d52502d140c010103407a120301401031280b080400b1754940d45099891754a600180ca2854a5181903030b56880b41a900303581200c5250b40854503e4000b401403100d501408420f5440b6260800301350140d0b80d9541060800a04ca6902000d61040801b0004180403480750300107008031856038003c01c8284681024280c0e664821180f4288661014106120a500c0791300900c5008210804503286000000a100350041016010742080384120039203e05142c0c0c00242c1d14014a44001407518504042d004500040400440070704458009030518000c02c140940342001c6040030b5400840f207c1d1203654003003407030f00c068421074031408444420005901c1e14440c203030203c040051549103083c2c6150743e16404001c3c085106680300f10b140c03114044009050000300758050081c2d025044150400008050000020344240e000e940a40d0130807100742d40008025090b100102c80d03480007a901c40c0c1c4d0300306107803143d0040c00c90154004510130070798030642d4019500800d42604d080c4451074850302031142c2 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 304961115 1250 304959865 304959881
    0x305150f0127090207060b1c080a05091c0203060c040503060a110714010e0115050f01140f0a0e03070608090303070c031803110a15091a0931 62
    0x100908040d18800e266029045410000324072002000c44a00c159010450305051548496a51900064038004104580c130a0186105045a214419a000300d40d0003400d0744100d4030040030030304c0004a89102c580a00306640c1d40a10060005003040010301b49103e9510020108900a02c14400440d00508503602503906a4101400070721056840c2045080a0b25020907541c1d40c4a500f040400c0102e00c05c1c40310380a80200407030000c80c1a42d045a905400c44070b2101d02d1201c4c13104402018002607946100c1c0740322031030007417912854005402091000503c1502001d840c40b4000044542015410540c140702019003102901c4807240c6d110015507402d1404c0700c43c901c0c3d80d0001c00c00600a1402052500b55550091419850071180c2c0e0900d0110f81e40180c109035182250004159440d203080408000a800d02c1422061004024407025005641c0c80c01554803a09003c921952450002c405803403600304000c02c0e034200400344a000704115192054034031000c203054034804402962034025012 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 304962365 1250 304961115 304961119
    0x60605030102040846030807020102030c16021503090a03032a0c051f14070e100f030e19021503070c080304060f050a0218010806030705090402030307060c0c0201030515 74
    0x1818801c94075070b817900d09035500e2100d034040c5119040b5840303001200140c3c40328100300b0308218500400d42006010100c0c004c0034001160300400421112030b1070b4001f43c030844200410100583d104070310014030000a940446550840040300b00182c100b000910351b0324140c020744081003040b03104416207080c8815a800485c1d28020040308144c4980718800000b0240e01075819110000e084000c0c094401050500115440780c070340e9070078000004007690729500094682041890000502c2c0440c0100d00c240301042c050041c900c6040090360b00a800402e603214001d800c0d502d402140c44502840b100280c00300ba4000d000c1c0c00c204031104400c020481b40210101d0f03e4858080c0020307583c07107016900c000c0040300d030103894040c54240903caa00905000b080d4089000d40c9454403a009201c050200702c04071b038100b00c4402c0500c201d68401045c1c00d02078401c16118100e05985a002191a41c420b90f03200820042c6081d00c1c0b480c2c13042d804500341c11101d02c01d0ba014861a01e6043e0105034504250090f66 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 304963615 1250 304962365 304962373
    0xd02010f0c0e1807052106150903060f091905010c08061822050604030e030f010908091203040b0a0203031b0c0d3f05070201060e01150203040b0a05070606050301020408 74
    0x9100f03845800d20290388070b003461a00514200d01103011540c003100178201c14040018007030901c030551401c60700b5114480700c4c011010381020140000031b540c40502070031030b17810000c1041c085684840f06205010745048000001600d0842928045000300003000b490300010b02200301240d4149070901400b00b9100e41140c0c440520345400c3c645110010315039a020303138500011080c02000070002d010a5102d00d0c000c1e01c070240d0064022042c142802144d2620000c00d900d812803860018907800182c9a0312841030320744141e5013240c102c10929500c00d0343c1180c10440c8001c15071083c1c170740e400002140310390102c082c048881c030004401002130780281003643c0c40301d42144065440c030328424007201030440e044421903002c26007035103030140c00e50704900710813600e01a0851103c00b4800c0d4034000d03150441003620003003105600d040300c15186000306005000d40b400c0341c600c032800760500c0bc105440180041c1c40071a50340d40d820342405080381c1c3c05144125900c5051440c001a18034041c400d80d0704541c070100181c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 304964865 1250 304963615 304963639
    0x1902150c06010e180d05030903070b1602060a0b100c0206090301060f06030b0103060b0a030515040e072c04350301051c050304090b030123060102061003020102030901200d02010f0c0e 80
    0x1a40c6c10b80006140c2501403109010b01008180c0c201d0a4600450b400c02c138090041513422002424410010484411141890301807215510317620280114148503140c007030401640703440003401034411034151960541c03d00b00042510010744180030100c540740d440c1000141050030054041d5880d5200b0501c00c0032061001801d168001e4010035409030f49000c03000740321040c42000900f20b51004100001541c800c81c418000589818055201d00750b450140c3c0c00c103c920003290b0200e9101c0100000c003004900e02451003000d2145c8590300415206241c0071140c12000307103840001360824441c6511410716030284030a0414046031940c14540c01801851405007000d050602030803a402070150159039170903140e201c6242200b4441d0b42140201141c015a08204000901d000006803183c51000d90690b070400050b0780000480e03441081c2800c101d5998200402c0c2c0c03913080d060241d00071000b8011101c1c02d0001550640c441030016208010030050881d0036002110821040c00459800c08100468 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 304966115 1250 304964865 304964867
    0x1080604080316120c051e0403020603070309020d050105310506070f12060b0a0e0a061218021011060a0e0703140c0d0c08071202031902150c06010e180d 67
    0x26043d258900e08041e00604249902402162804040000021404a00200c01885e10460140b20341c91115001d820541035400051040c4405094403003807540d41c2104408548036030100391081900400208a10f181005610715003602945001490300c1c500a030030350040c10180d03070101c8265007110003450b2669a00c00c0a84110036002000001d005a50003a43c2d02e00c0524000c17030f80a040c031a450503446491011002d0240c2c900307c41050f11030008a03d052140781d0b409810101c950b548140003040c40c08034140384415804941c2d502079000003001041900451300100b0760001500420100d03800b558404c943d440489201d1503c1902940000108202003607900c0501c4406400032400c1c0e40d042c00e144d60008480304001542154180111314080182c00030074000e0340001c1c00390f641110400d01c0113500182d100c10054203042c50000301a0400415501c0d070000080040c042042544ea4030016040072640d107001c05d2140d54582c0c100000080c2498036003d43c0019000b6083c8010009607804508c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 304967365 1250 304966115 304966141
    0xe0c07111017061c0302030408010f0c1202070309030c030305030609070302031b0d060906150e060306010905090a0b0604060302220602152a0703020f06190f0e0a1a010806040803 78
    0x10640e41c1c0801c01382c03501c50030700e142100390401c0ca6129400441d6510302d0320519900f503400c10000342d001c19103820900b448a039048650740309502068100180d550001307140a48420660342c101034500300929102008058100004501494084541401c1703075503007500803002c0c0c1c407003282d00344040c0c124048040942c640110203031564842c52440841c0e91500d80040f50100e4007103502c0751003002107488070f504034690801c040c048080c00585040b0310307600e030070000030785a0b500c0c0e40f0a06018602000000c0e03185ca086a0000420201c0144410354441c0d8861004019400040080c10300b4548111a1801c5072180710820382212503540142002c8090701c0f04001d1380d010020300008a0b0640921911100d40715803c41407204100401c20365201c0b003503410300a161030300421210761701e17038455000d20085500e103207600c0d01d4003802c644010404598282000c005800c134090901520311601d28460b081241d1546415080708002031051002c0e82d0b01e00b40c443d83c90348259806800500100302048400b120a1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 304968615 1250 304967365 304967371
    0x521030405120c1903030f022b02011803020303011802040e01050907110106031a0a05151203090405101d07080c090406030f0605040606051012020904060e0c07111017 73
    0x2e41556030540d20480811a1041501e4002004002504090041541010076294503141d80c0c8028501d0004d0414400c10f201c018803c450f54a0006120300b0034118400d40142480302413013601d2100041c03191402079503e0b0801c0c0110b420121842100c050b8441c441c0c800c0c0c6045541e5480000e80d144d1030801803202c655070140c602c0d000c1140400741404480c500340200f100851042d0601d5114201c00f12a60f13000302006060044414180001d0005815111100304a403c0c0d00302e80702c0350504042c00005185100d00c1d2a15500035041200704603600480741e01302d00442d1038820000040c070b42007920340407015104071061000f06a40c8000300341c0c1d10751030350f000d801e10070006080002c185460343c0781c1d000466016042201c105898004110400480c0d000e894018003058441038400410800007510b045103000d40b4030342d1704ea4081004411540d5035003051005003600c002d09000c50801d0f50b039420381c0d9406090309440c0d015100a4418050a00414a614622242c9d40c0c0c070815081c10707007013170030f40322809 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 304969865 1250 304968615 304968649
    0xe0a0f080423010e0105190f110706120b09040209040b0a0f0f051f0b070611091002160503030901170406090203030a020a06111e0307021f060521030405 67
    0x601002c10900a141c03a60300300d980e401182c1c48007503446030000504403803d03503084904021091001244400d01f454030b580d124003942c00e18003110003502004580116a000c0840c10910440d60005010b942040081240d035555400610001400905225000030203880081d0400c528800140201b10051406500003000640219110441650b0a02500c8100184030038183d0340d40c0a20412844540f51100000382010310080018982011107030f00e405401c4015140985544c1c071881d00100e401c0844041c010010140d003080000820000d5640c81c41d03101e11411030110079804201d0745000815201c12400594605000d001c01450058180c1d0010b0400c80e803c50f110304440b401640e0600c041d044801c9241d0040045600500301001a030300c0701c0780044800441080204c885088502503807540303000001c120340c0d0704d40326003000701d1810080e504450084109020640881c044035000f00045039003c40c3e00400301e105800102d41c4002e40005107140c0b03684100401c00c19400c040900d5183c2c0c01c12 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 304971115 1250 304969865 304969867
    0x5120322030506010303080f06040c050301090209030c03070602031201140d030c0204020904110d060e01050d080703110607020607140306030a11040212011202040e0a1a040c05061b0d02010e0a0f08 86
    0x1582c0d540034039010080e04100c002c26030010801c03240d07181000030564492301c00c960030310410201e0a4094120322040c09000031003500010f501700591000c0100345441d0380003404542d12142d407400700a48a42105000c059449880740000982e0a0842c1414202810040c003501020b0865501922803000d180012601b00d40c003808120041d988a00c555a045244040300c0b6550b47c3c01c0307074810401c50301650409100f940306040107200f46d0301c1c3c1251b8026516803050b54240e0790a05030405980c0040c400c91030401078896181040007141e404a80360740039080984038800c40c1d004001014041d030000321400d50705a0301101490010580d00c0010000583c4050401031900c1c0a502c0b4241f40148260010141c65a00c0d01001e001c6042910031445c4424480380a032104514a55900d0103048840c103044103428945400f28080c001110840801054002c10066852042c2500c0c03c15010403807507200180c1c01100301526100d4018000d0004221504d005040e14901503912405d034070b80c440d070050b5003440e0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 304972365 1250 304971115 304971119
    0x6160806011e0c0302010f0207030c02090604060b0a0c02100f170c0c0703050c12010212011e0909060c080108030c07090e03040f0e01090b0418020402090f0619080105120322 76
    0x28207001d002c40841da55403004034180c201d08000c0c0c00d407824010b00909280c81005118003182d80b20000d0b0554917411aa040c130315441f2880010064007040c0c0001000180006042c402e03150020150702546200b582e01080c40003e501e42510803402c0081040049980b00d005030034142600e41340242d00200210415003480c040985551400c8501e030002c4070b0035071180d03030160040d1604051a1a03001400c0d0002e41c03800c1c001c0501104215818481c000038510541c490b01245c5507000f00c6040038000b1100300b04540d803654100003014001424404005c04c41d21800481c002201004695032200240b0042895a19000485000b8001e5001e41d00b058081031101007404805500180d00804401e5034084113541030180c400c084078115468680720390728103440216401000412000511b80403240140c46100000100e10310070500f5501660080c0c000640702c803504111111442c0e10311f4640d0312961503a8036101032044078444040382c40c009600c184440d0742c006121202904040107446201c52400d5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 304973615 1250 304972365 304972397
    0x60e15010506030a1d100609020405010509010f09030501051005120a021011012703020f030703090e09010b04090b1b030c1905040803030103060219020102161101030b0628020616080601 81
    0x200c0010b5005560030503009046c0b8a42540a5100500301d517160851406191100280c4648124414141805003260040441c54090b41c9040000e507003200c001d020360b01d0000e495041d101d903e401050310801d031800840c040040005021004281d001d81003412041c086d001c20380d00ba2000f0b031000d07103c56483d013429070108100034010300c95400012026421240c5185000790070900840e0800d001544140034000102c0c0d480001041220b100c4c3d0194003071611412002d90151980350b041640007428408070f1005c10251446031842001c2c0881c03100017010106c900101c50380304c2911100040d9030184405d8540140341c840b10180441e0504020303203081d988a03e0300741503401c00d900a8a4040d40411151f0f000301101030300c080c25000c1480210701d80582c5848890409014000103000101c2d419140140c61340258007017211658024401e81c6c40300b02c0707610103103000c084d41085d4400d0400010004004a40005000c9009d562003440c0e03604183d01e409030071035a0343c000401c0075042043e00d941162901c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 304974865 1250 304973615 304973651
    0x512010f1407080601110a021908010c09080f010606090902031317070605010510020327041a040c0e031207020d0606080c01091e050607080405061204060e15010506030a 74
    0x10110891407520340c5440003002e84004002402581805203544019152400c0882c01c40b440560440341c00a182901000800d043c80320740d040396100750b00c3c01800120643c2c100d131030300c1d048800d4102214208014504800e090300c2213031240a0110344504000c1c401a030b0305802650340b0415030340303407959a60010b480d07221074080c60b10b005000d0040d00082d580144400c600416000d4078040d82d00035917190301418000d642c1c0c80381c0c1019502d00003000c02000c040c115280e45616007203100400c140708150000a14909880c0c1d0a00f80a1040c0e2600500e83c030070a000307800c1c00904d103800034090900c000143c0180c00040d408800101e81c083c03448805070000494522940d40542071890040c6110b14880001414100e40c5070050700c480501010040c55103503d40182c881a01d00584080d501c80203e0b00e0480000d025139080f05030f00800216280c442903480c18082845140a18030522032480c1090301c90f03481d1302024010100328110040184050b0070004004c541041901c60002070842c8009460400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 304976115 1250 304974865 304974881
    0xf050304030317010e1b03070212031006170106051e0d02070c03140c030c010c03120c050c1b090103021e120f0c01050c060609090a120e01031b02070512010f 69
    0x8582044103101c403030843c882215000d0000c0101041c0c05080004501c10381038000141103262810002c0040c03a85031007448004640d68100c5413440d240d0034110400e00007000d081c05060b0000d01c007041050303001c10309684000d040b120307251900c91a0191801200050f0407564105803400317401000440040d079a0340c8010100350f80105002d008075411494000301801c5070350200d00d03061b03020007541c0c00ca41da0045145020310a090074800300c044424581034030707091403260784010304500d4800c210411b240c0050007440c4031240002595501c03680501044040000303a031039030390084c289900600042c10b000c0550840b06415092100c00c0c0f20003500002c0c0c041c0144100340309150410076642c1310105040103520103500c03090038152708200c0b010b0111640d8000040c4082d00c03901c0141e0110b2403807001840a0b150103034100d1803610b03501d01c0b1214054140c0500c03200503800030b403611003400c05040080c0490080250941d000d002001e00d0401006225480c0350700c00381d295580d0340b0003151804c42920032a24 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 304977365 1250 304976115 304976117
    0x307030207140d0b010e0a0e0105040f0507060207030b07030f020702120d0905040b092403060702010e060c040803090f031f050a0e010509210d051503061b04030f0f0503040303 77
    0x4007060820084041901c01507880c18055101404460300051524507514103490741c10140c0fa080d991a1280c0001800d001045206c2d10b5190000340310602c0841200685850b0155046074966903036880f0807a0756519a20010702200001d1000c1a101842138114200403442540c0c090b04010194000a00c1265100300351005903115520341e50003550410302d8070000b404203c500300f1491042d10081030318814002c14524000c20f0a0000000c81c2c4950351030f0f550b40c0d40c000f5048a1461428450190090042c42d1017401548220340c001602a4150002c4a00390390441d0701841c1000c0c82c100c2401b246040d0040c0b020340c14002c4042e906001c110301c50b0500c082040780701c804661400c1c44121a01180c95007500b44100f03906100400451210000d00c1c421900c4c04801c00c0c040500c500c2c4011209409650711f0009454107103002e00200320f400c45c45202040104070140c0e10301d43c540b40400c1310603400e254034500c03004005002c10400300f1102c5480203402030048440c0b4502240a0b83c50900b0343d406608114 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 304978615 1250 304977365 304977373
    0xe0a18121b122606060a05160f05100509010207020a090c0207081002040512011406150705030d0204030b07080105010815030106080102030c0307020d020706020c0d1e03020c03010e0703080904091403070302 90
    0x3401c902401e0310003ca100007842c0a00081c1d061100c003041d00d80c80303025185414442c0c000f6100c0c4d034002001041d0700c1c28507000b0404000070307603543c500140c8403480310031042041030520022601501061003280c600340d60050005d401c01d17182c15040005000b00c030f182002580610800000d404106111400b5190384030840166524284030400c010704410000c4480168500140e04003540010a40150004412203040f0903101005212651074401c00c4c0c0010601d000205540c03401c0003040d00608141c0384a401b4805062369030810844004c07409120b00c0f4001080000480d00c01c01580a4070a2a00000f40000c0390890311f80c0071050a81c1c0c07040d10003180b1030740000100f055440e0705102d040d03030900652028103813461805800030f5940c019500c4061050401390840c03c100701449845105600070404811021803850501940703801411424038002d50030088400054080454100b00303480d070242c49541081010b6040c08001c2206101c01c03511841604e11070300003420100041c11810303101ba8010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 304979865 1250 304978615 304978637
    0x506040e180d0e120304120318031a01090b010c210201020702090f06100f0207140f04091b1205100203070314040809040f0203010501050d09080d060e0a18121b12 71
    0x10142c6110700444c96000d43d007040c0030900a004002ca8140d075030603014a03008941040000ba072240e005140e80c03008040741e518540c00e0713403401d00c04000d15040b5070348c0d00740c1008030501920055501c06030040008060807091540325490103e000031345600c6071414400182824860340c085000d81c0c0b403d69201904011207020403195180c80c000b007448000a43c9001407100c0076540700039580e440b4a01904810341d040a003105050740710181a0882c030b40c0020414446442c850406042103001d0b8070700e400e255070380184003042c041c1048003040820f9500c58000c14868005031007110083d080a050641019205e90034084c0003410303074460034011401800700e0b036030f0788801c48104011589803150400f009401800100181da81200980b0081408030360040b4141030f080ca441d81c803d119103882e070031945141c1040440d0520700c1811880c403891140c034080250790070503681702c083c04120980042030300440610142c1070f141b08260300c00210800c2c5001184111050361207441c030110368002c2d0300c0042ca0b1038260f = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 304981115 1250 304979865 304979869
    0x80312060612010e04021c030518010905060a3204080105060a1a13030606080136030c0f0b010e0915010803091017090a0209100506040e180d0e 63
    0x956004402107840500d4a6100100790030b0b141414441e1071309040700340001030b0542d103620801103440c60000c020035241c8801e45c500580f42c0c1d00b01480900194008541fa4907095003d91003440541d0750003000f190402c8580700c0c1c11151000c0003424100b0310400549035401c003895010300c14214140c05281942c848c4d0410080c1800c44100900d40c9200c0e400301d1104101511001c207071406002070172501660340300807191160840c1695580f0081140b450b08400241c45c48040d400900e0301140c00900c0e210031000749090811480c0042c3d161341e039000d40d081d44000000c0c007a8007009074107441222010240200f80e2143c0c1d803483d4007680170548404240341003200c2044180014080c99180d4013603000c4650500011039642d00400003e01d0080761440c08050715907014001c0b24078101000d40040f50300e4030b800300701c0a442c4c1403000d138128010965640421aa4001100501c0560301c0c042c1490781442e14086496150500107400114039540ca502809003440307060000b0032a41c141074a45201882540d01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 304982365 1250 304981115 304981147
    0xb060c1e10050c030408180306090705030d050309100506180709090e011b1202040f1410021c18030210030b0a140622050306090f0d08061c060b06040803 67
    0x100040724186000100010607099400742c1e070300146c0005280b0b8461501c1c04458500c00ca18a5207581e01d44514400c0041800f400542d20056502c01c0e002e40b64551011901a2010b00003680c074074642e600030300300b90345110415034841540302c0c800411203140002e03465045015004103850100018502c02400e10030382429000384108590203c5c020404425004a040322401e001c0740090200000c4910081d103030b44154064401a016121482c03104581d40c040c4112402204100940105980008120224001710b61544c24481d40a600ba045184c690021a070740096003d00705a00c141c00700c000b1001d61100da005d510051055180000e400660904124000070070380d000c21080c0c00c1224400c4000e0300c80501385d98241390000e01d400c4c3c10304046c0b81007000e14903003500019014440d260802400c100000354011028408109490304d000d01040c0440b0082000c031842504410200c00123840a821001010265805031400080c001078100006d0900e503c95807140c04142e1002c1809181c0c1a2032078 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 304983615 1250 304982365 304982383
    0xf021512011e030809040903030b030d02030702030f0f1b27190509150604060b0f0d05130201090b0705010e030a020d1103030709050d050a0f0b01031a010303080a0b060c1e 75
    0x1105070002d50300c0c41d03030f4a02c03e0b03124140416000716114001c1c1e9003014001c2c0c000050a500003020703078041c0c13210f102c0000d41c2d903080050b0603886889441d2426410300d82c049900519281000080c0c1400b0600030a0001130030304041199400075440942148208000711100300102c008814825482c14403401003030313a00c0311022140d600e4031700d4101445030884c00004c080703200e01c2c240841007456580e0440040d0081011758054080c4200c0000c5005a04800700014005083c2c01282080b450300e036403e04542b2114140e1009010402c460001e111020000c000b8000c8548100000310700071a030f0390b80090442c2c101c00000d03c0564004507075540d034603030071520750b168081c1000c2c010341c110f161120b03000b4100301c0f56100d030078010395030804008140201070001607d016000341640e00094040d203801c040c062003d22080d90300f812a65a03180c02d1950503040d0604903a0182e544088039151120020014035640141c3e40d8408810840080e582d203051040600348010040780c03040381507102c4d10b11800c1c46005 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 304984865 1250 304983615 304983659
    0x80702241806010b1b0a1e02011d09040b25020705040e1c03110403120507020f03010903200106050a0308190804080f0a0306170703030e011403040f02151201 69
    0x200103104040c860002e644001039407a0504800c40424030b40e0a040200c400c4c001f41c2500c03208654030b500c000c8410950070b1080e20030307a40e910035407140e5035a103100000c2d414070b0542c1c03240000c0d000c200414000c0c22031603000070b100d8032001c9031003d040e030701d00188804918248000d60000c4104000760710b031522a0b04901c582d06ca0152846001210821914080c42c00d5007009041e80e030b120080080490320f0584010307552080750b054610f9400c020113403660700038000892245c40030b01c1d00040345040602461003580c0d8980c69442c911136803a003071104c9401d009251182107640e1800d0004d6140d642e002030b1710045025900580d82d88600400710401c0d041c50110000a10160303034203200000388503104172060005020001a120144190210007a100b5544101001c0c5015078810308002e00c080792000c00c40740700c1d880c0c0c00090042c2d6401074858a00301c551001a4800034000070b40480d41080c42850b031f681c40144084100c0d40c50b03c0d012140e50b002080e501c038441d144040144200e0315003201c400680060 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 304986115 1250 304984865 304984873
    0x50f01050f0d050a05090a0c030f030302071506050a170a0b0c1c020705160302061c020d0e0d080601030c0c1104090602120708100e010b0d0605030d02030705150105030c010807022418 80
    0x1054070340c1050b0900920008000c032142b0b4848500f414480e0b0305072407000354020021244a00ca204007800a40002d01030103214292806d00040c100d03070f6092419164209040141440803465201c000401c10018108d070b403424010051007000e41040451400c1c1a62510801622007032682045071500003440703524584451105000d0000d40c0d2100140c411074054050750036405901e40b54100f000c1d014070b482d00403045082c603042100d40e10000c00c550b003010342d01e40e03180142035481800460582c2e000c0200380011030721101d01c15011900705010ba107100100603202141302035050755014101d074080120424945d15441c1840380c2103a0065055401009040315a054942004050200750300188035140313034050005103c641e540300d940c115000900009080e21054000108003944a62000004a40710300503d0040041c5280140569058501c05401800b018030741030300540c0c0511000d05000103511030240b0040c7c1800b201288180502140c0059003050f040541c11034105d02405c0c2031000f42070704 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 304987365 1250 304986115 304986133
    0xe0406080601151101090b07022104090b0109030b010303050403120f0525020307030606080106090218060304050307080304080414010503160f0e0603010806010e090a0c050f01050f0d050a0509 84
    0x300015614103540c580810050f158000100940702090100c200d00384c039500300441c0e54144000b880d2803501c24842c0350282da10700d525038500740d40303035281d9010b031106171110a200900480140754030046503801d06041c81210162a915042c007000703400d078401c0380081c0001a09101700100f400461b01c048010382480b415004c0e8240c00a050350281509003100020414660304095200d2007881c8a0103401400790313528070b501c13401d04801400071401049100d45c209400010400c0e510710841712094861054002e00d9280c03074040001541c0041d00c2528a0311042c05502e02081d4490001c60155101e4411203030b940d07151030300404400400d0039020f8140003050040002c5002d2803410f05290040341d03e4513706290358400140c4003501c200b4a80c9402040c04400400c6030640010b0b028141e0f0080310a4403000c0c3e03958150b05503101c50645000300303c802d603000100042d091010080058450504110341807507000c1100c00c030283c004a009101564440c020304c8500c01851003004d402003104005445401 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 304988615 1250 304987365 304987379
    0x92116020103050402040209100806011b020d1401060f060f0f140304020d02150c0106031a0603030a030f0227010f0806030c12010b090103052104031101030911030d020d0e0406 77
    0x68044064180360f11000000c1c21580e8503070488040c108000c2614540d0340100034002c2c1032100c1202e885010850b209400c2d2810042503c4100138194000d0080e022007999907a06680c0402d056103c031442e40d00d841c00072441384a01e00c2070101610048d42c40b0404030880035001042d0001c80700982c4e040c0710341915400d22a60b0420104c03030344150150380078402c0702981c2c40400d4a40000381003caa441000bc242d40103460410342041c41200d010300800700c4846402195581388283c203480e2162b05500802108080750f0194108503604007960304014148011115680088410940440080078500c6080d107003035a044100d10814001d10300d0400d610f498604082580d581c2040c5915208941070028418502002d41003080c1225018002e042c60b940c3d680b4010380d4030b0500100600155002c14034044d0035050b440b003624120b03504482c50b1200100c0c48401500200103d20007500d003a140d0076518001d84e1800c201c82c1e44e20719496802032851390507041008102917241c2068520485c18414100815 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 304989865 1250 304988615 304988647
    0x4140108030a180513020a0c02031905100b01050a0c0f1a0f090601031509051e0307050d03020f090f0310050c0d0b03010e07060f11010501030804030311060f04080a0201090b0921 78
    0x1140c8845e000503540c1b031244005607110061260700035818424421640100020303a03019440b0381380f14078100d40700290b04036550415079042681c00d600040c0e0512480389064420b1541e425028001c0005840c0b0a4042d11420000d41d88007a007021585481000e00c01d80c0f0300402030307099000800703d0260a1a5045690f0860b40070100007082d81c05030744802404061003814016401071804800c100c0440e04024039650391250451403040d1490f004403003851502d07500900883d201900c3c44030318545440006002c01c00f030b170040c0c8480c464144c890240c0600c403890461003502d024101d400001d0340c80d8640a1854403d442006004134000c2e41000c031303800394142c2c00140800c180c0d505809c0140e04010300881c00c80b0402c03004600004c4075801e00000000340003050000f8016640240d580410000140f41c034940d039400152403903030b9070310050400a0042444030b400f8100c00c200600c000310b080d9450307071100385840c0020340b08012107810010400190000e1107101c0096940e0702c030031860514000240751204 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 304991115 1250 304989865 304989889
    0x2070303180e01080f0c0108010e01031203060b070c0905010807030b04060506061306090603060515030f1b040603230f011a12040b0612030c0309010e04140108030a1805 74
    0x6020080100c101041034800052001e0a910116a0100d60391014880ea4417200c0020070740d624015014608081d5118900e030724169140781284020b04d0b4a59030390a203003102d6001d00001055528800414241c00803401011301502130707800c085026041c0500801202e42c10380c0451040d0b406040e00300700045651030300307039442500300c03400182e01d84c0c8003008501c16101d4005100725002513414003065071b503000f122042c240c6042d13030f400300009a15a400c0c4080b00e5440f5102d0001000b0900c00a03800c001c081d0401c1d0360180c4035240007641d01c280340050020541140c1c00ca0008070351660800c003c500303004480300c51010000c05080d40f41c4d040c044030741e281c0800107024420034501d0031490f10703c0f0010000d0440c0c40021080c18040441c0c0382a040c030000c10001501ca40e80329841ca084150303496034001056400014001c0d01561030500003c00554038010b44000d100c0c5c01680340d541410300d501182d13000d01c3c0200180e1003d0f41d514205144001c118603080c0d41c585040c00b40002d4184410340340c142804038 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 304992365 1250 304991115 304991117
    0xe161202090604060506130f0e01140d0c03020603011d0a05101e0503060106120b01020c03060105040b0f030703050721030e28081c0806030d030213120807020108010509060102070303 80
    0x107498489502083c05803559130016a0083c1c0005030700c210781c00c0d510804500715403032601d000320a241c4680d0a00400482841640f0302603880c511100414034112100900e064841c00c02d260303048d548c2c0d074082201034000340d00550314039206000c1c11042c08514015680c0c020003003042000b16180413985440b0304107da019131003284030b11103a0100a401110b5401c000790400800322202581d5401004148a010080c0d9000303071030a000d1900601c3d400040e4034491480003e000d801e00340c0c00c0406100081280c400c0c0c291b8003e4800d098014591410700501c80a1406400902120b50038402c1840a40886900318280c112051420700c010030b80c0518080ca164038200c8140e10748610400c82c545950b03410724021303400880c011200180001000072a4550b00c914480482d40c4101e410000f0b440003501207801c95015004694000c00d483e202c1c1c1c1c01003141d4000311680300401e0b911001070300305140111b20100c415041c00240b50f4203643c1c03c007404e540108000c4404d03103000c0c942138000075220390703107444010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 304993615 1250 304992365 304992379
    0x10f0513090c11060a09020117060a0b0c011104080d0e0a030b0c030604020d180c050303070309120317040b15060702060702131d1c050f0f09031f0e161202 68
    0x30324591080c14160020f601c2141100d54a080c011a00c43c0100581c001c00c90202c0d69051318820941c007a0301d030f07240c4614001000403800500d4004040540e5100c0c40b2103c03501c0d5610b020902032056810050005821030714010162401072400180c002c1015881380d030300c0343d07003402d40810004a2441035107a100761303503000e0561240c0302d09000c20081d0050207401100302d810084d40c802c1004200d0740d2544018010340003003881e2a40c5d081819281e2040140140c0000c10220003844488007034821500064440e02d000104242810200d00030188107403011240b8500c410300f0301190741482034054072032802c01c48480381b030842d442e0f000403204d21585034024001d90340321100c8203840c0b0023644061909014420a451801a480303201c613181c2848035990251004014a030480356449041914211941d185200785044054480c58640384c0004122030b0381442003451644002c40d100d002c583c5881481000401d00d5503000000504023819541c03850a68803491104104081d0ba0018940d2000c1d0142c0b821 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 304994865 1250 304993615 304993631
    0x6040e251a09060f0703050715140105040c0f031805030f0301060201110909130c0503010507050d14041e2604080f1c0309080708030424140f07021501090605010f051309 74
    0xb6600d50041080103001455130027030b001440c80064015040c84601c01007410302c540e803681d040104841242a1510011b00740302d9407c108180290311602040c00c0030b0501c1d40104920f41e480d00e1866200703000854a08030040010042c03290240101000403050440607820030146001150080c00e0003001c00300c1448c48a5019410700034030402841c05041c020b1f00a0000e40342079400940b083e0300c1140000056450f21541c0358200c8200e010450080d03030301800000740444580128060528900401d64503440604440043d044244820009260070012896102d41c40c22042c142002060003007030701c0d643c000c10700d407017034210080301c03810700540385420001044140c5007404078442c003408400070074080740001407009201840c030500003090321040c0c00286804c03000744030b402621680f5071610140c0b45000b001c140c8030951030142e03d61107000e0f441110303aa4281190725058401c403ea001c49111f0399120410320555a0000c4d144500c2e0210381884ea203000c42c0f20070244d034002e00e184620301c01e003542c50b110 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 304996115 1250 304994865 304994867
    0x50f060115051218011a1311040b030712020d05040b0f0708010b0c0a060203100e010807060e0d02040902040c1e0906020c0d021f08010801060f060806040e251a09060f0703 75
    0x1041000f804200000c0110071032203c0000c2e00e2911020140d4482d880b8507c0074a42e445540c050042d040000000d42800d1505d0803840030119000070b4200820300c421400030008059062010304100031001c030001c0b910703003080c0c1424010080040c22210400118904102c141500b00b40303c0c030b0440e5608501ca9a989090401c100c0c1818240c00004242500001c14415010035104010b4151060029409141d0341d8030300342c3c2d994030601807189002140c035200780110546000e6031407500b01c500181003c10340340ca95a0001d0f0031142c411140d9030201da82c200c200c8080054242d4414891040d0f400c0000c4680d04203000a959070101e00b4900784510b4400300200c0454540c612411594044190003080444601c0409000408240104d15140d0700e80440020344606a0203002c0817074009485002e050f440c1c80044c00050300782407051500a1240030f558610440c1209484019030482084800c8990b04084c40340c42075074028052204a02c5041c030a41d00103903a1a01210703640c0b295001e0043d998842da181c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 304997365 1250 304996115 304996141
    0x105070e0d1101110f0304170705010513060305041505040503071b0609140316061d04020711010315050a1d010807030803060111100c0302092d0415030807050f0601150512 75
    0x8001512401b02090001b800c08242001d90a074441d4441590426500e4400440e001d000751503e959442103d46410082140607038859504039028544c0110342601600c8290196103007503030200c4840d400050140c013802031404040042c080817100b400e5409107072920040c442d8640380100c030f08031528641d0504403503504201c2c1c1000c903580c01412140090781d686c40641190303002c280450400c40030503050021442c2520032a480700d588120038250b901c1c004c500440007481802d566500303003441d000d00817a04d541c031340c90464002d01c008020030001c0400803510002181c01030307104410b507600416003031001801d14000d8074ae21607028600b0000d161910030f20503107811100000c8401e03143c0ba0141e00c0d1b80195045d001456500801ea80c0d05100610398003030f42031025042455010701804824080719a0300e0203070030960305008241100003200b9141e8882d0812544072190458550341b00819460249006005150051240a080c80d041c8403c040c005041c40c4611918132000c5030361540000c2030b400c1c0b512 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 304998615 1250 304997365 304997383
    0x30f0e1c0e18041506030302121809011412010501030807020d08041706010905090d020c04110c03030a0509060c0f12070309050303160206090c01091707030b090105070e0d110111 78
    0x2040407030031504489048400001c1520b00752903142c0b01c0400130320040402c0c01610100d90b030640c000c0c03200b640400440c9259420504804081448450090001e541c0350060300d4040d20000c110b600c50b1800000401410f40c1c0b4156140407164109401040401c00703500903142d003941c0580d8201d05608152400044c203210b15085111100510351024041800014915060707503501e031005c00084d01c0380f1b041c0658401c25101c4801c01644034450458990a003500140c4400e050415140e090541600e205811038008642c12459181d0341d00801c414a034081080710b800c0b0300c44801d0030745802c001c00102c0c0224420a2841b0030302c1c80c1c9010106100b00c0c400da0007484102d410109884c2c50303062114000e55011405450200148200000b2506580c40407407642d03041c075016120748401a1a1201d18444082c80400c210b095000d482c1c000800b18140c801740900c28240440005014609017102504121a0740081c80c010119204100001000e04d00103241d02c0c502400d01425144200705032620304141c0c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 304999865 1250 304998615 304998619
    0x6091e0a1a061c060b0405070309051e0f03160c0e0f0408031b04030302061f080d0c0510050403090f060306140f240903060f06030604150921030f0e1c0e 67
    0x598080d40134880340da40501d028503002c86d401c0c4200c0e20313181d0007102a544008406045500090140c1c0a0728146080f100e04903003880099403503c0c80105401400c40e00040c0760850f0940c04100003034104030100000c1c0d005000c04812082070390500126a0203440030082000b0106070307000001c610b000760904d03040694581e140c8603503507540d038903441c3c02522890107907000ca111280300c9030300850400038040041e0075180b0f000000c101d03400c40f0b540c5c11924808441e00a440d1030040d10412a0030020764083c90388154003d0300c2c1d1030322591070002e1070b680c0094598002e800b0549040418000e0206580a40c00b85060072107c07808441021030008082d90515442c94180384103062000e0030307002240c40982030400088065480564491408026282040f9641c07a85a00314400080005520307400b0541c1c0d83d81b03905c0340001d503803606070340d4180c0200c0403030341030341054401103a8a0b00e107d41c90300030310700c584468000074840050340440c5a991504016100d05004100710004000d05106010b034800c14100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 305001115 1250 304999865 304999909
    0x150f0301061d06040f03060b030a08090d08071709090f0601020d050706020c0601030c080f070e0406050424062103140a0309020d0803090c0105031003020d0c030506091e0a1a06 77
    0x514805172a001d0810310080718032500740f21481d1400d14010610400ba070b90410407451a0404201c2000720304a42c240085844060521080021520071a88d078200398600c10300c41d80e908e9410104100036584010a40541480100204040c41e607020403101780c3c10000d41400349d2904164030700300c40a0301a1903400341152140780e000005000305903403503404962183c1c081e03402490f034126805454075202e0240600c816440310100d0002011644620f50181c0a07506401c842c01245965445010940307085000c915144c00003403210010340074807060078071841c000c4203251a25030751740a400c024808a4050501d8000b107200e5081500a41000040300d034000c062001080e800c1c902071201c3c0d0025100c80c1154400c05401c0c00c0154000c1044900400441d8000b05005156030308000e400e5a419104942711009400300200050341013041768050718a00000c0c04c0842c00701d0b06294420406c0301900d84180d8403165090012600b00020000c4604c07a00c140410305030b03038050100300849050256030182030740d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 305002365 1250 305001115 305001119
    0x30c0311010908030309070f0f0f1715130308070804030c0210050d06081c020304031502090109030b0a05090c031606030510050d031101060b071101031a04060602010b150f0301061d0604 81
    0x40740e81010f0b075500b46050803125427100d4500040a00d0f901a10280c42d50130700c01805183d91070380030340d041e44011740c0845500c12450a4100b10641c003c1d111101e03d440700300c070490304258000c50f070f099102c0740d2031410800a25084e00c00400402003910080d010700c0003001c1c0d030344401d40310b1800c40380c01040114007402060354806c1056070b18a01501e86800c9010011a03c040203440402140c04580c0c20280704c0404140c0661038070000e61041c5402c130b0501c074a404000000030074559030341d440344440990004c3c051070200c2195003410700803c2030920076006004c641400402d42e15848043e41c880f850002020f030740c0c000c0026010380e8550461540501c0c0c4485500406030310440c44001014090000e000d915a06c960203401c03400b81100040841004692006065103c1ea01c001c1c0c2c1c0c0702d0701040d101d43c1500114003150494402d0b07086000183d4560002a106080404845010024140c1031515000340d0942d0100140810300404003005008040f910702c14a0b00b0403441d01198004110035078940d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 305003615 1250 305002365 305002381
    0x807033507021201180314042706030204092a0b03150a0b07060203011e0501200312011e0509060603040f02011404080c10030c09180603080409050f060a030c03110109080303 76
    0x1030075460040b030001c0c0f080030300f404805281800340c50888000278005100610580010003d207240d110f0320591040d550a00000541e5940c02004069405070281500c1010040b04100c128980c1e100802031034540c20300c0c1080511500000c0340d0344500c12040c00303800c411a032400181140b20580c4008407200002c107032103091008a50045040700c03c00074580f80c035120f62507011842c8454600c40c090108905c001c0810f02d05440b0307104c1005101b03660342600d01d0240034211119000c2001c0e041a0442401c040145d0036620021074502c015140072200a1410b00c2c3c01130004100744030040c002007240a0304117018045900400e284500410448081a100c0342c40e000ca223903585090154142c8140d001e61282c0709258001e100e20a0080e03420350700c3c920780d141040d0742d82400341c071300a100e807802a6a80000001103940c0c1ea02820181000e90780216690a0007420030580b0078015000f40e10070501d40100b0400500140b100344100d0f60311000c00495070292900688450190343e2050015000c0002000011 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 305004865 1250 305003615 305003651
    0x60609190203011d090f0312071b110102060a09021e0301020c030f03090610032114070602040302040b0a08070608040609020607031808030310052202040807033507021201 75
    0x131032130031201401c1a507516000f1aa8580c1c0010008040381c00c108080c8030f041000069055000704242071022000318100100d10f50380c0880d20b8242c42d00300000b450400f840d87c1c107101c0c2d290002c0c40c00009102001454000504080c6039403a00c1c0441d075640046038210740c03801c1d0151800b1045060549803076121400d4802c0307441c1d0086540c10030601600000400400d6605116030989070088402d502d031540e141c40301014550f009012005010f903a00d00e0a44c8501c01c1c070004c2000500c80c88015071200e2440c414017059428502c038051159002a40602041c0301c0051100110303841071a0003e021780b99418410020040810040d403c03480006c1d40c0d03410f250304941c1d034001401e85440e064501603602c0205d961680401c1d00c0b030742e011005031a8108110718004a00001440100d051610f0304403000c0c08500403644590310401180d0804981041800b1488100c88190b03a01c507245544583c0100240c0c00000142401c1081b20100202d5414195190000698031445415000b0081e80b038010400d00c0e04c1d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 305006115 1250 305004865 305004899
    0x13060e12031b070806040807020d020109030b01081e0606030c0d0602041a0405120a030e0d0503130905070801092016060e0319020102070209060f060705030f040501110109020306060919020301 84
    0x5588100c54000513045400a03110344600e0b001104c49040500e560f0070004916003100d4145c0c10403840c52000300103d403841c07100b2030013130800c1c00007401c1540c41c081d030303004900e401e0902d1940f03180c00580410105407000700f0349010400045501d00d41501c8a803801d44001d0055400c070086070b0840002c021a10344100006006844084804101c100c92040d205507030b41411010060001d007180f65200c46038100113170b001c3e041c113101d00180c9080c00c0d4400c410342c5c9084696071000b031805445030144014650000406809024540c40500070181314034507031000c8115000c5c0f0020045c40001e51a04c0000302c034881940300d941d024070217010588100881982d00d4000c45000e035116180800c0c1d401d800340c01442141c065541c0a03044c0d03400c0c1e03611a41004000d030094280b0a4001c90200881400200305100510043c00214049500c55040c04001403a4078070700c00c2c0200d042d80c540805c0001503070b00011503e500c14011501800f0683c0e5200000b8113a518064070075a030b0034000700c00450241250921020303 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 305007365 1250 305006115 305006167
    0x8040b0d0f1103151012050a0212060a0f030b0c27010201320612030a0216090c02061314011e050c0915070302070e151513060e1203 58
    0x4401c1c1841c10310b03884940300c2992013842c414812540c6126500b000c2511540d00380c13090504141114509502c20b060721030031620604e83d41d9000420790203050000c07812642003a01078540f00b034140c0c140513a1030642d44940c00054044e828440c00140d0700071111080303a100300d41000170100d078180e0400011200e118003454040c00b550078030032524800110b80360f6405080c081c0c050351890321600c80c40828a1000043c000c0c58210f8644421010307030000400040201c4031003503005141058905581800c00d00090700400704090070b1105103e00682d00141d0f441d00506100382d004169040c62030104100349140d12613a005508004000c1d200440c0b401001c020500344041c1808640d07940c641c12036541c810300d10351550150f50103145c61502031000c00078001d101d00c00e004231341c4603175120006000048070032202d4804e100f4510400421a091450710164191503d40c0030b903003815019503410341c080615000d00b00401040c0880001c1564804010389400e42520090b40c1d0703140341080705900f11480d0401c041c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 305008615 1250 305007365 305007371
    0x31802100512011a0f030406061a04030606080c0d030e21010f0f1103070c0318090905010e061b09041407030605030d0206010e0c180406091a0916030908040b0d0f 71
    0x4c442036460744030403460b154010075501e0080c45543c0000c142d08040c1094802603911080851013100280c01140343c0144030000e1501c461030751070a036081d112990403089840e0400ca6101c92241c4038000d0032289150316003401c03078000801c040840c504001c5020141440030b0320080e048902c40c8103500403035401c03428560912003110403914007000d5035080a03890007248010000640d1040c0702d1203442003124824a445071062030305966aa0f150b005640050710300b5565000100100f180900c10102002181d02c040d003003d1038880002405651903061110381403c0000711068613a55503801200c000c804c102c401e58a84c1010031b801401401140074043c024801d00d10270800540c00050381c2d504940030b4000c0070311035a0f610f01c852074180c0c10814111920318105600c02440ba81c90307010343c002408260100180c0c5429803025803e51841c48400180600c000c130040c040c2d420f0400050300600041810007040c08007480c503280c0c038030b445550700860f40e542004c40c808891940d01d0b00301c1c0d0004000d00c10b0038 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 305009865 1250 305008615 305008619
    0x703020d0c0206060a1719060b0901120213020f0d0501031b06210f0609051e0117031206030703020909030703090b090627031212070c1203180210051201 67
    0x1a0f90300d0301e003941c6a40e441280041c08009008150785405400f149980a81da59000c010302400e0300140002030880c2c4150b26202800540d08040c3d0380c1ea0300600c540c45903000650126001b150441d01c13000492025a03800050941018001500f03e81c4c110540d4001000300d581c0d203007001402e0a0455000b4501802c50940000303209115503443d40030008501540f05d500d005812002c00181840e54a086500380c95010008400c41d03d0312405110b10310b80b00ea00003014042d0072082d50000c0c1d0580201c2e440303008280f50502140000429101d851a4500c6107800c5503d403d40082e1409900d40d000940c4001d000f002c02c1510180030002c0d21500c1d00c2503c0d00b07801ca40d1521103410080c00760035a1180c100d0414000352651a840d40d0408024129059844aa0362010380c04030341001d080ca1032311032301508002031042e1505141010542d00107241c1c07401c0003a2041c140d6503010500c01141a51042544900c81d40d16506e22542c10110443e90043c86d60b41c100009c1c1c00702070aa07410000c0782c140101c0c942400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 305011115 1250 305009865 305009867
    0x50f0604050c12040302070f0308192307110312040612020a211b030605120106030317091c0e1e0303040b0d06080102030a0905060c0f0921060703020d0c 67
    0x1482d00481241d0341d054101401207081804900000b4002c0d0114420072000040750100171501c140030318000c00c62203a030350320301030844514032600d42101e0342002100c4290122000e04050b0f07146800d030f90000385680d00c128504100c09030700100795070140e0500510545d10480c011076401032044840c90345480100144401000040b030040400300408907810444040041c5880c9040350140001c80c000002c4041e6401c3d40d4a5800c0c1800403e8004a962800c050140e86002a8440b0402c035601009021084c21590300410f800110146450700741c446102250780841e0a000020001c44030b4618040c40541401d0020300d09070000070000c0c001d07130801d00100307100b185c3c500c03000d0090038010780294600f91810b032503071a10394002c001c0110740e02c0c0d440101207850002030009602036034103801d021480030303106c0c14242c1c101407018001c01c81d1800100001c1854882000690303c00d15001c903005580c10a44600c3c1b6581a401d03584140d21900541d81007203466038140d80941080c061110341000318420f0600 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 305012365 1250 305011115 305011121
    0x1062d05040816030f030c2316120c060807050d020a0c230703080d0204030c0305060103020102010e0f0c1009030803040b04060b030c060d0207020f130507020c06040501120b0f0d06050f0604 83
    0x7409001d0100b04050100b40180b1181f0b00140c403400124002c08200e5065046000782d040341d280da143c0000c561980710000f405001c00141c040c1c03c658003060001da5031100e20702035081c4100e200307205c002c0001074156801b900075140400e008c00300556903010155001412500d0801d0b044920f003144040c60000340307885c5c0b00c0002c1010900d0f801440c0ea10305588a40e141908000c0b55101d06903020000400020078110f111002580704400905655046d0f10019094821900b00d102556100c0014140107400000b24030b03041d40070540c0c02c607280320072200089030520340f26000940207080000c144405c000c402070500f4451400b481c410030071401584200754481c446500ca072988104140321502c40c88440d0750050003800e00c01043c0c441c1a100240203e0b40741300e019410710301c1040d9107104015a8940610141c200600100c4a44e0b1403c6d003000000791400c2400740720b8800f81c940d141100c840507160380340001540000104000c15403801442c2c610090b00e000c48601a4545440c000b041060800340 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 305013615 1250 305012365 305012369
    0x10909030210050402040b032b1b030503061503130302070e0903070204051003020904140106060e01210f02030c090a0e06010c0803101a0409140c0301062d05040816 72
    0xd03016101020b0040345403806407401600070b90b80585d40700000c103d2a07408101903829108156160118907107004c0c4c0400d1131000e0f50001109110000c038442d8100b03c441004c510751075906003801600ea84a18002c15516005a6084e040071500003085c0101006000304081c0090321950803501c60545072050545181010b40e090b06080d80107000c07050040c40d00b0740105520948a2401802155072900055004401590180c90402108403155462642801090050580ca0601703401041a0100007801d0f080403903e00d200d03199010400e030031000714640228a5444107640d06545a08000203d240c469128101c3c0a00c6100d180d00005840e07990b0b0900c8a01c1a40140c48811103122192910b10403a480200380c54480e81d201b007408120120300b17103448005148010510758547e0b0a20516800b102c00300d000c020081040001081f4030025a582160f041da40301c0d207001400c2c40c464100f80360450200c11040d0400640d4040712400c070a0340500a0700c12070343c0010480329104600c000c98030041d0407078 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 305014865 1250 305013615 305013617
    0x414160303081603020c0304030c0501090e060a05060a02030c01090c05012703170d090303090218040f081806190e060703020709230a05010e070f05030412020c1e0901090903 76
    0x103180003500c250b903540f05203281490340e03040151609542c0d01c4031074210340c03042d00110b41000c41408248000d507807014040010b03000d10240b5102e54240007002441c40c24140c8151445940c0016044440c03c0c400d0040d0303207007001c04400a020040440c5001c0d00c0303070050707030040c6800070b0035030143e44001008908500002507100504100c441e811921070742e000100d50491a811000c1c100140d007040482440b840083d02c0c040d9a00080314500c0d807040140070014050401d04c0001c6d04000c1c0f00129108100559101c0d5000c0c0455594103220969000f0745000c02d006254400c101242851100012425a00d0181d43e96a03400c5800b0a4507000c0040324003c404000e001603111800c20f0003980c0031a80306840b50801501e004040710400c114801d203d0700c00b00e6204420381d48441c0100714200071420401e0700305581c0d040c074a1101403000e000500b9404006c00240001403883e5405400e54020b111b80d400c0300d00007074000b0034414919030707203242020340980b0058044c031100000060410804e101d0742c0100d81d45 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 305016115 1250 305014865 305014877
    0x12041b0608060f0a0e01080105040c0608190f0e010c1e020a0507170715020f010b0105030615070212060403090807050f0a030303020307020c1003090b060a03050a141002030414160303 80
    0x1100c0921603200f40c403400301c54011100d150041259008251014000c0c800c000000ca004d103011703c0c12520400c0544d100c00240807101c41440107502d201e80d050310701d81c01992000101d4401001c5144003504500102001952a10804840d42d5601c12400105194403012102040000c1481260383d18100e14000e4511381111301d06002e0038100030650000b5080740b600300c8081340d0f00c440f6080071b00480c03030002c4000341c0c0c1b15107280100f081083c064110080824207080e811450b1034004600d910092010081500200042903000c55441c0c4030f0300704181c1c0020381102c09500d001d150103469000d0a0040492620401100151a1402c1e130300100c0744e003002800304d1901034950b80c0c0540103908007a021030194019203081d4040d507184d000724441c1c0f5103120303075011504051900b4801021200078000c107014008030f8006001181000070809070907031740160f0104082000c41242420f010b004400b841100c3d000009001c01e00000c61000c1c800c2004071030a50301c0d640c0a0a2003000c0c004518800100400c1d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 305017365 1250 305016115 305016121
    0x14010c0e09160f090306062c27210405130527010b0306090607030b0d08070209040305070c0e04020a09090c1a0c120307030c090e0609041712041b0608 66
    0x403240031805860f450504003146029101d6454809a804680041615094045e102107144440f400310111603048140400d1413070501e031110035032414a000302e1000e07140300b822401c140c00400300201030030b21454112a2201c03c0328026040c40319409403040d24810410459440d90814080c0724007405040e00380b191801d104d08008070b510040d410064011200d55a40740b030300c2c0b03040c4c8043c45060b114075242c00184c811480d0008016045400340030000c1d01902c002a0300900180c040002c40b00740d580c0440d03408a85075510f1604580501c03e2000041812890500024255062b040418000c9108603880110503807904400c80032074051603000741c03807880c0b018001c124802245694004111000e000d10b442d010700a14078520f03000200d607800c1070307030300780041080155030f850f2149d8195006c46141801c100c07880c0c0000c880061134080d040a1203240083c0c0800c0030041070400e6610301030754140500d03440300140040b070000c0c030ba000c64042d502c0c0e006003240072a6011002c5965010b981d05601e07028142e031 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 305018615 1250 305017365 305017367
    0x1e0605061602220f050402271819060906051b180103021b0a0b011d01030813030606060206041703010b0f03040813080616050a0914030a14010c0e0916 66
    0x801d4043d140b02900b0034015003050b50045a0040303140701c0d6035400c40401c0a05151041c489001c0701c040e0318014001e4a24010440702c0000c01d092a084001c0714004c0c2c4c05011405806400c11460070102c1c40d2420f20142200c1c20014150400c4100358001c07072003040039a664088001107000c5400442c100c481c010840100780d440b040000890503034042c0342c0182800d000c41200784201542000d220b0580d40840c820600300b04450036131a01611f615910505480f040c03044000301a50b06020081011b440421001c408052440c0c80100964112400b40041c640d00c04003e51038031030580b801e6811444004004020900e2031080300d0499114580c20b41c54201c0d11405410704d07400203401104d1001e01002003061402605841c44060314031103014100c982808a003503400751012004200600406000d980c00700d5030000f000c881102d09140446580c411082d000074102000c090008003100d90b00b6001500c2c5200c1580800c4611001380c8a20008605080030810b45c283c0407680c035254500c070174014461403 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 305019865 1250 305018615 305018629
    0x10c021306030b0a060e0a091e2a03140d02030904110f0304050102090102100e03030403030c020f010e0c1512070e150703020d1b03020616050d1e0605061602 69
    0x106690000000c0c850341c0742d80e1480f10701041650111001604c4a209022a0020b41c510740c0d0480e1441c803080020800c182c2d10300c48040c8140080303042500c00301000c001445510f418108100e06140f420f140c03801c040e0b100c0c13000e0340051400280d516089203102d0310242d940018012070318030390940007142032102140810015020705044001c45180030701c103d802c032800e12406035015038400e900142c0c88181034000249400882c80704144050308041c028100d0440220440750001e816250215012090503016840d00c0344100005070030398171302038940311a817001058250094004654000a800e0316210f44140c5010f8a0010440f4107196004500054000c01b49040f1b610b50280501001a800118000040d00712050507009a086038022580003075110b000e044c808009103070301400ea218580c8000b0340e215001444d00460351181180d030607540e030003481070340d034440030403142401460000c8060032462002c0c00070418050b404c2401c04031300b5141c120b050328000040c40319001110030041d001c100305 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 305021115 1250 305019865 305019889
    0x1d01080624070c0e09070b03010504111b0106140d080d0e0f1005060a060302041212021c020f07060809060a0519060e15031b090405070e01030b040b0114010c02 70
    0x350a06980045000385055001d4402c9502440301c00c11810316040141e0412240100035554942100c001031000e91101c0b0181e905566080d100000c03d040b24500c6c0300c585214052542003141200f014203003400c00150010000e4a00c1c4200d4181401031450a018841c4002c141c02400c0f80d100303201032040c4200943c425031039510344108440c0442e901e4501c582c20710380d06481e00340d58030343c5850401500e42000c40e40c80004054030700e4118a0107281060205080784196001000000428020403c1505c2004140c42d095103a106100340020030240196940304400344c034a105004102d0001180350103407d185111345c050101410355982c4d0203e013407008000c018140d80c1403030019080404100054072801000d0030b001c1200340071500301540c0c2400300c814850500e51003644110b0340d01401001d407651a41b00042d040d01d80c44035039103492500d20704101081d0429686a441c4100000a0002c0c40300b081c3d0044d13004811142050345c88030384050a00090300c8105002c60781460240e030042c2485501441 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 305022365 1250 305021115 305021149
    0x1110120b0a03080f0c010b030c0f010507020a0513020903060f06030d2106030803010816050114070f02030f03030115030905060c030601050c060a0e010c1704080306150301030303020a1d010806 84
    0x10003a5100d5903400c41d00c0e000503252131203020010501c03440315602440742c8501c0c410101c0c003d0402d43c07128030015100c00358042d1460304010f004602d030b900f1501e40b0340034038010740720013056075410410002d003820007074000340f5805101e80715030808203800002d00c440c11809000040c2c007030501c0c1c80f15004103035140b401803110081c0a031160000070350301c0c00981c81807030080c41c420030203e5641e5150078982481c1542d0031480d1020708200c3c0a0420041c0c0e007110340c0c2c0d025840c0206046071912128148031540340c80031440650580103400b42d0a251400c0030000b58182c0380823400403074482c09040804c030b00f221041c44004043e944800c0202d04030780c03027000103154000c0c0145045440c0010400c145030802c0d609803902c0e0700f2151900d0b4010928402030007035680c0c0b0340b15450301e0300c50001301c40310420040f1000b400141500e00c0010100703c5c1510340340100d00e01e030425516020b03902d5070742e40f800800a5200c044041d0004450034002c0c040c82c010311f803601c190b080050703441100d9070311020f0821007000c03081c1d10160 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 305023615 1250 305022365 305022379
    0x112050304030506040302031206090601081f0302180a060605040b07020f130c0804171201050d03110303130b0a023a060609170c0109150507020a0e041110120b 70
    0x2c0043c0c0d080042d144101c0c441d13405903454140d00d00c80003107103080c0a000d0300c3c03292030003404000469a000c0580d9521101d54015025289201c0b0800c56019500741c00294100e030000940102084a06030300c24003c0321460000c01c03145503070b400d0441d590300450190200c942010010b0401600d80300b000758825920003040180002c40303288e4907008a410301e0a50702c0101e1210001c100c24044540f5102000c50742d0212818680400442c6000c1010814003a45100d0f02010300d03104245841071071000741001c080b00c1265902e041584080c85c071402c03c144100c904150200c00a00303016214000c1c0e500100301965002030a0010f080725105207a00014009a0289100350448c400041400703010000c00d03007602c84540e0f032801c02c0c60b181c1c50300039145e21031036040d840704e0b010402a0760f00c104108115080301a4141c100b4035110803c580038800d4440195121102181c0805e80c42030103140b02d80114402d00341001412a014103000750400c81d00e00340f4020a000f11070709500081c1c160130030b03815800000c00c20 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 305024865 1250 305023615 305023619
    0x2010c0323030109050604051f0509180f030316030b06030f040201031116020310090209061903080a0806030d02061005120a080f1b070305070302270103150f090b0112050304 76
    0x1044842e04240d024443d215101c00038048581043c0c450305800c11450000384070b03001c071810207114001074184126801035441d540044c1d080203011003101000b0701c1e810180e27403206d5078510f0b03903903980c1d081654440c03201d0302e1485e986000240a0311410440c2e10005c1c00756030960341c07030003a40718040303000030000d906158440f4200c05502008000410b01846120a095017280650060500e4403030040c000c401114a008440009696803613101a40210215402201c0ba821a2140707814014541c4c80200015400700d84201201d4000480f82d02c2150b0a400711080b07103149840c00caa8401c42902c3c0c02c0620085803001380b05070309080081c4000c4141500c211054036907a03540f050515070081185060303080c00800c2d104c0d0240d6445801251b484c07046001004124210b440c0c842d00c0380300c58407000b489130300311503600c4081103101d101c150981060080801d01c00c2da0b5905100c40b08041d00400c10452a140400c80000699607204801d0345540101310180268203040c8a29280c00600c032050307409120038400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 305026115 1250 305024865 305024927
    0x60702060c1b0d020f0106120506010b090d080a031e1a040c02011509050a1d060121051b030709020406050d0b040902030d090305160303020a022808031c02040302010c03 74
    0x140c18a01110790300a12403031492044e444d0855412340c012083c4000c0180300c600c04505c000072100c1c1035458035034050342e544100c03200013141c011421030000c040c0f44001c108031078259007540c020040030703d40f81c00c010061603100030010126500c5524044040c00c4290950590f8102030f4002003c00c0704e0307800000f0321040e410322041c0380141207512103020281c0f41d004201c590001805001c40c402801140c0e000340100507a1241d4544405018082e07000400102c0320000004200d01640103e4000c0f0954500350341c4042c14624050b100a045400307442810000201d00d822882101c044400702e03900c0c20708114540324280d01809404100990151f00d801070340002d0f0f5800d00214091140a0300e551505914600d0b1075800c1861240c11102c1c11001c855040000c01c1d004141410165412101042c40450b00030042c162921600c4400c800c4102141001c5900000040201305298081c1c5490312400480e0817898141c0c82139001c000d0025040401c003600180c06042031240104444003980240c5552807d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 305027365 1250 305026115 305026123
    0x1b011404080102090a090b100c061805060a1103060f0f060c03280302040515070507091b021e07180608010504030909050601090317070212031b0f060702060c1b 70
    0x122001da5030003c1c0c11841443c0003245200240013400c1c040c0080c06c140d10002d810704090104c25001d210046448004002c5a940a080081c01c811011500640d240c2001960b40504494141d8202d10f0131014054505104003541c0c0b04183c028204181590101c040c012001c0b0303c449016000a404d01200f8a2540240b014115144008503400b100745085c0e04d681040c215481a00c2052601c108002d2080b500c0b4490050b0345517014050729580ca08072441c006180400c9548180c0c2c5080c038185400001142d02c01d2584684c0c000c40c0d08890200c2c100c503040010b00b00c035a00b00100e003a4442241001240f654103c4451035500f0380e04001640c6544412060a4030000c841c11070002c0c04000c001d0200c0d0201c3d02c6420342188003131803c2e0794041c1c11552106846e080a5100035009003003c1148011035507412103805020041800703031307030b1a10035070158a140d0301e4401000b034205024221040301c030384400040b03861040565500804141e01d800c48103800076441141e00003191880d80c08010042d1000300 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 305028615 1250 305027365 305027369
    0xf010810090809090a050615040f090b030c0a0f06030f060e0a0e03121003150e070302010e0409081201080c09090a021e0d0b070206070509010203040b0a091a07030212030601021b011404 81
    0x40f00454145000400c100d0f042d00f6201080123003071020302040c441044916195070a68440c0500020300811600c0000c0c645054440025071126031001c02007103000014070180d0440c1e1081e2400c1c440e560381a40c1200a548080c007441645402940009460001b00c0d004000422a500c0540349826003031803060708004021100039646c0703481d0f0070040040050014510b030000040b644100a41401d1082c001c1e01c0b40c81e28407010307040210b1030a00e199260b03590741c800200e050703105288a5607007103007072800c00f0440024441d0507124020300000d024642013150f1920320580703103d4048c0000b4004d540c20030211000780d4042001d88110408080b01c41d844410018464600a410015080c40c00c520020f03c2c190000b00314408101c0c0a1000c0c00d4540d0f00082906c1c192b556040141d80c9400d4007d104072928420756005000c107508000108450190000c010900c0034003d07800e03141d0700328000b0078000c2584000c2d60524010307070010044030120b844511803400c2c0c6a02c1403408a40c00f9100e100041e9075a0400e07 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 305029865 1250 305028615 305028631
    0x311060106210228050c070e010504060618061815030203090105070914090a0e191101090f030807020f030d0302040504140103030f0f03020f0f030406050f01081009080909 75
    0x2a5000245041030850b22008501030b45800750b107003c4500d6004182903850101c00f8010720000f50140207403502401c2540c00e110700c481c0403580031030790710084001d000c030003845854025845d149002ca60369100745030b846170203440e402c101c410f180d14115044545d01c9034407008100007080518040f65103494074001e000d0410351994050385905004040b01d007110000303801c16050146030729080000e034402e2100088843c0f0202ca03880d01c295540d48003c000b41280800344030701070240454141d814104580c00e112114002c41000320180030120056842c410207000d0180d9849601c40100300094181c0b00904c40d651002e840b40c2018218140428a0464100c2e0b401d8003103600418144440d0400d13100d001130744110000002c440e941365484c05000c1010ba4110b007000c101e1180c0801014500a40403180b10081a01c016a44c1361681140c0502540090354110745080c14007000c114a1040c088416050f9821440035180102c4c01c41c149400030402c43d11300301c551000c1032141c0036155890040b180e21901d03503 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 305031115 1250 305029865 305029877
    0x30f080702091303090b070f061515080c0f070f3305040f020105160b040c090608031306110a060513050c0316050409080c03030403020d0306080102160f0311060106 72
    0xc00d10400c10701030801046004280300d4070b143c00c004241d008081c5401c60f510401c0307241d03580419080c1500b0081c85c00c80043c080314100110300d240c10104015117001c550014410244000c0002c0045441755401ea40d030a0785a030040c000c0010005540004201d200d10a03031181920100d2603803000c10401440d00c44408a0086036090650142c414800d01c802d0440b100b01004540380c6a6038002c604036010703c0c06070401c90b01080c0d04945c8613514076040b165540045060034103180514062840010394060840c0c698108000002c01c91400010f550140d10703520212100b150824800320760814980301c0d10344240c440e440c41507002c40c403d4403a86014070903504110b0012861810f003d4900084000340341e00135485003541070306450500e01d864055845c1120045582003150800152501640e0b2001e030b020f010000500c01050380004850400444588041c844d00c4d0341c0e5503189080340900e8042600d1030681260010029010780000c0b04011702c682445080005000307201864508242c1042c404035403 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 305032365 1250 305031115 305031127
    0xc06150302190b0f030405160b18101715060703020c0f030712060f09080a0206150319030e04020c120705070b04030f03081305010e1e011103060613030f08 68
    0x140b1444400721006650003008103a440d0210401e00c80c0700c1c080003003c40090110105040104c240841444504401d00c0803407072940b03890618030240d21013410751030940112007441c100e50400400f414243c40d20754540b40c07110242071040080d240e10040c00b010700c0a0000516051942d074502c0600f140314083c5d4018210102c0d440240940714a48044040c440d600c07040081040c2c84030110204030080d0700c00f4020402144030b000003000341251000040c03003030700c02203440820a940000e0040c4101c4424488040030b00302c000526032280e966145101a00d00140121340200b800744501544810010300014501402070803c2410712035040e100103100e40c00040c21505201d800c1120201030007039070782018900780c03035940c900c085080d504000606000100c0001144001261401184140c00c48020720031008503071a09074071450004a01d00070741e14150820a003042c41403040d201c030544403404041c6161103000400c45182c00120140078903003107140c808400aa081311031a90064400c005450b1220 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 305033615 1250 305032365 305032369
    0x5130501060906141c0b07030f0506010e2d0901060804031116051c0b010308091c0f14190501020307091202010c0314121006081e010302100c06150302 66
    0x41e180c0d5100380005418018144040c215030300f50210303009800c80d82c0310013150341c001c1c00c840301d80041c401c0a803100844a0400c050190982c103c03101d41c1c0c1034080b04100ea1b82c0c130074006481044107191103603040091108240941c101d0015600d412015041086070b558000c1c0000a41e2074109811480006031000180810140c10040c2441900440405408001e0900502048408582c41a244100e2140c00b460a01d003650441d20300307415410000c13034034466031a804d18081c164801c2d0f0004c0d00a4981010401e818000c1c240c0144400344c2c00455a6020a196118140a0340200703a076810b05010740c1000448800c1b8481c143c45126100c0c40001d80c44e0325104001400d0401c2c1035002031218502503400c400147c0c1d008003140d0000d03902d4241254070030030400588056010f84030780845145007a1043c000d45225002c000b1045070307855a10301940d981c2d14801ca006025006e0031204c10311070101c00502c0140b50141221400c1c05c81c0f4a050100c00401d03443d10000e89200d42c621212114801c03106000798 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 305034865 1250 305033615 305033621
    0x3040b0408160609120b07090b0a02011515090b0315030307060605041109012304050316290708090f040504230610090b0604031b0f0f120209061305130501 68
    0x1c00f00b40c00d250030030034641000e1000520025000038121211000010340c00c0b8041d0300d826002e8902ea4000c1d980b030b17a08504001c2d0090500441100d1074040c44500083c1c1c07151041c01c40c650044a0703548450300c00f4582585100b8a81028102c2e8440e00c0c01140625030a490420141c01d0b0306000c0c00011807010300d081e0030300045440f41d03800300c90100e00c1000300c0620750342c02411808003542c14202d11184091101104110340c02180c0010707606005483d0211104501c000181d8143d03102c400e5504038444441842440b603200c2c09034240982030050010f10f0104040070701038284620050810b210340500076000808482040710102c0e00d8a11242c0703444224049008165031106c1d080c4010010340c1006101312003e10114410340f50402d859003401c0c4441c2d2074520039100110740c413070752140e04004a040c8507000300b60b00f80a0308450405425000a80541d408800c500701d8a204031010640c002c00d8003841840c5900a20894000c61146495907440c000e40c1b080350300c01c035000061205d14941e5403402c107081d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 305035971 1106 305034865 305034869
    0x50f070f11030a1d0a030f030503090a020d0b0a0b010206040b011e030615170a020a030803070c0b01060519020123060102120a120b060c100e03040b040816 68
    0xc0e4603048003504c0c07000d861091200c101d92501006000015880f440090050f84003a0700c4c242c0424002c1c001103400080280907195441819004620300071001d100860325007020200300041c041c12441001c404e40b009102403c0241030603204c00c0700e00d0f98107000c0c89106030b210b181c0041d852811800101e009660090041c0070360001161046400701c0a44681035550314070386e0394026020004038259071990f9008000d0000e460070764607001429040180f0700000e001c0d034601504003149031000258020000303581d03800c1e41e0300c0903001030111207544060418103680c10001070f400034000c6603401550280c54a501010744d0346c0c07030700d0040380b41904801d1030518091002952205481d440101065110462030090200c00c545406000e80341c4118a41e0301c8041e00203411003200242e058001c0b80003012400100c2e0300f02a00c1d031b010ba102c6a40654402100742d842000c0c5149408404603c82c00 = true := by decide +kernel

theorem cover : BRFrame.Cov 304856115 305035971 := by
  have h0 := BRFrame.cov_init 304856115
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304856115 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 304856115 ≤ n) (h2 : n < 305035971) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
