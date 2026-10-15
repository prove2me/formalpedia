-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4398
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:29:11.439165+00:00
-- url     : https://prove2.me/submissions/4c24be29-8407-40a2-a749-dc756e16ee82

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 790827338 ≤ n < 791007194 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 790828588 1250 790827338 790827341
    0x8030a060326031f12050607020f06090d031109130606021b06040e0705070b010305070924180e1b0f0307031e080d02180f01020a03080a05060613060507110d2103 71
    0x540328076509170b0b2100e64141020383d80e8000880e84800903100f262804007400c20001902c078480d00060b03005111100c0300201c110060b18655030f85841600c01400038061980c1c03450042000314407001800500b05152940c02454040c8501c084d100c409900c03003401146445e40f10448041e00d58080440c0322a40310328604503028483c00c2c0700907040f644a50004010071030081011412035003080014403400007030f9207820104005440c10100300303282c4a00c04100cad00311128841c80320040c8000c40000c00703007603043c03001d402c1c085004052030110b00b800c20080000e107082d03138a02c1440d1000784d0041040a040d5a00d10b178143d1101e00d2004c0020344440056400c015441046440b17034503507080c055407110f0b0b4040b00b684c018105401c11601c2000700000341101544002800703c0110307059520f20031640c481070b45010082c40058607060300314100304840d4002d0104030300300c10020f12055440c00e03600c00e42810325a901403103031848203100360514221440401c2300310783c80c98500001002d1070702548083d043c0550 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 790829838 1250 790828588 790828651
    0x30103061805250e0c03160905040e01020c060114090109020d09060c0807020d031a150d0c02030d0b0604051011010b15130e07140f0708030a06032603 66
    0x40c103620642480019014011602c03507419422524046220313074641e100308a11020441d51811461014030001d000001d00341d50241410240b400d01032109500c0c0c1c80480d081d518182c100c000b690790002ba52482034030f003c1040500408648080120401d017101c0000c0e1000b006108801a4540214bc20034193b00f00da0b21a0501540c8a06c04012488400002814081c011500440903014081c030880d80c40d40280201ea503e17600508403008803072000780401c03002039001d10006111000034005892480b09a111300103c0c1c5210303800443d16003080044c1d0105445400d042207000f4078081c0300402098989080908051400e4140701500000d0807442e58010098180d44650011041480d44500c0ca080c5005048405d51004011103590301c805046044030401d40324040002d071005603400d0001500ca01130004020500c2d00c4500c2c041da51345428480360810b036142c2000507501d940820400501861480b54202c1c1480004596600c02800009078080240040248010003800310660510400001c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 790831088 1250 790829838 790829843
    0x3091e0309130903170609011a1306020102090a060c0503030c030628061101050f060906060d050f0a0b040c1202030603070902030124140304120e09040f06150501050301030618 77
    0x42e45000011682d070043c1046a0064000c2001c02040c0040700140c0e6981c6031040300084c00000c2640d10701302021192541807403030782d2a0180240311110640f50300500c220010420395001607180c5075005c04019960f1240c1d40035106000760134411100240011003625407029000424544903035909001c80c18241481d02c0e0000d108080114803040221030a01980660300030f030b520014400406100a422913500f59190f451851a0500007905860000d000f5503208078040c00041c10100c000d400c12050f1a400e94100c48042581d2080201c0c01c2c5c3d052141c00c1012008807000d02c00910901805803035074144203180741da420340000c0003d69586003013007050001c2c40701c107008640d25039699006004c030002c3c1c660240c8500e03012086003400076108100048801480340003881c6144c0303456540070100b6070740207415400d02c1081240c60f40d860b9152444184510b004216444104800346080130895040c1068a41d0011042d0000e0045981c41003e481c1500d038062400594010240d928140c00c18031040c00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 790832338 1250 790831088 790831099
    0x402040510090e01090216060b060c0a050703051915050c091c15060501090902280809060c0f090f0d0512070c050303041428060201090b090303091e0309 67
    0x100e1807142d03030241d4440221100c0500480e00c50345c03034244000507841440c0c1406880308a19081c40041189a0310400c001c030402002c89103401d112900044c1442d91005046e68950000b03130702007040c4802408022800c44000b01d40619400f44c917500d684000c0301112605403526900c6000600c00c0203000202d1b0324a00f0000c04480303174420503003180307424540d80b8202102d00d9444c00c3c2852000c42c0043c02031409841c4141c46118020b4100701e019402500300342150b8102410302d04a1001142d0102c40b000f0005695a45405c0c40e4501404460724080014043ca110340c94100b1500d00310444500a81e240b2003021500b1002103c013001c0040d0125078900009802c3c0c1c040c024404d2000080d20008107417440c82802124002d9079680105078990095114140007052001c140449600d0410703486804000d207001280a5003e800f400350b035400c1855000354026070740d101e4040c0140403450035043c0d44001d8000080d031441c544144820b071100a00540070008200c0484140f0790100d00b4800d64070950f1010340f4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 790833588 1250 790832338 790832359
    0x5061813140c0a090c02031e0409060303050405210618070308190f09033f1d040b24040b1903050105040209010c140c03120d06080a05100b04020405 65
    0x1c035450308000d00310240f29101600000a89581c24000e04034601115005141411082e01d40590740320886100320418420410002c500e021080c0b040c940698003960f246500d890402e02484207402c15044403595a000906200b4540c00340081c01e21b40c070401860351560a4051040740515009494000130701c0f030200880c800100c50102e0464044d05844c03907464445400d6008020340341c88240b07010141000700846040d400e0500a202c0220540110000f00c3c0003041052131003904591801f002440010801884550315440451007044000c00c11681041017211030f20015194bc0d185000c0010661650454982e52200d17040c203540060030707070341d2045980752104400b40845945c20040388021a260400101c1c840c1014400d0b00c0c603204c1e040c2c4032201d2515061f160908102d0714051a028144503103103080320540c0b414801e00a0307584080c1c41075501d41e4031032880f010075a2401e422240c182d03400f0f44c5241001c1440060b9070540307012a80d20010300c0ba801040410003078492138006a800024541 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 790834838 1250 790833588 790833623
    0xf13060e10320f06060304020d0b07090f05100503130302210702030d050c0322092a030b03100e190b070306060504140f030a06110a1205061813 63
    0x10484803030a006001602c40c081c410094000b10b0a0064070307030b00d8000e60345000080780b80c1000741c01076400500003024406070f4540c940da000b888140484940c0000741041c407040055080c0fa03d140800340c442103e090300080311100c1c00030190700009201101c00c01c0c1c2d0b0108501032500900c0f000b03000124610709902084400c1c51500210743c04280100d000b072003910814016248640140d0300c0d05203201d40030710728095444421035201c0d802c0ba0b008032080b040501300090404185e11403903032204008036407141d455500704ea11148080c490304610090600b40140070a650703a020072814a88074080500103032a444429600e03140c1070013502801409880c1842d40800c0c030581c810300034841e840c2c82e0b4041c030038551140c1c1c040314607020300c0c410000b8203001001005424540488822240100030302103c0c1c96104544134007043d1070005d03180141d01000020411003482e44544030200d18000001b041c4014280311700031440a25003170480102c0d81e005000410210107025040d10031064100003c00006018074 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 790836088 1250 790834838 790834871
    0x20a030c020d061514010207030b010501050c1501060f020114040804051909021b100b0a060309110405040c03170a1d0d0b09011a120303010605030c071208040b0f13060e10 75
    0x17400f4000080c036079940c0b1140030350300c00107446056032b0348856507064591070700005640c281c03c02c0d140c040f00c9018031000a9034100d050584140204100d55980d8a50100144041c0c2100c0d01c150303500c4804e600c11003c00c03001c170741414212002c030740b01920090324050404491058204250300009496400020040e254014985600c84294002c0c2c05441325403a00519090855043d000d100e9000103480c0001c008003400b81d405500300c02d02460701c0c030f0301195100c00014100e500441d001c460481c1d42a109005000c0090390441414808800403407604024402c0a0400402c0c2d00000d41c90030010076965100f074584c200d2482c422a8800008040c0d420030280b83c13806021303594030101a00e1f01902c0401000e02e00f6860500f82c000c1000059443d41c1d0070050101d41d25400106041d140a608000c140300094140e20500507403000c580c2c40104a00300b5142c01201102c02600100e0b00306161070038004072810100365061410b512072030006199101d000141d003170540c0d04010114481c034082100110402c2d0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 790837338 1250 790836088 790836131
    0x50f010932040e060109020c0c120312010608100b0714010515100201061d130506010305030c1c0203090f01030b0418060e010c0f18090603050d02010e0d020a030c020d06 74
    0x5122480070340590540512003268049a81026142e2100004001c0500782e0750061120300d80c00303400c3d514005a040040742c0300788100f4200f500c16510000365103800d9090036040a0240002c2e15009a441c10103241414481c110b0703010751079661000003071401c00c10008909110b0940e024800034005440c140c031181222602c0c410700c050003944040303c1244894410300c109000d45042880340200e02c202024048003401d001080c2c1c107500315510903103402040c2c0030840e55009500c42d0008640d122240e80c1000c1c10286840c03101d05410f00e2100d20384005a4002c800c2d94940f4406454200c10320f4001001280509030b149c4846411900e44201c1940b1849151030004407940103175001d00242c0840204582291011a2070f50700003481c90644400304c91003100da542d1808800c040840580f922005c2c0001242c0c11584201c415500c080c81035a40c1e41e80a0050099025821003e04001310701741714065107800550400030201b0030389140180031035a860b061428490340122080100486802040301d00409 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 790838588 1250 790837338 790837409
    0x60e090c01090b04030f0c0801090b100e06130c0e0a08010e0105090c0d08070c080d031416020d030b0d050a06200f04090e0a020d2a0b04050f0109 64
    0x54102500965018081c00b0040b1460058040e10b49403079500d85082c0301d50b1140341190b05180d111400102c0340c00900a40c180140691580c84440c02c1809445202500300c1d88032a1800d60240100704c0c1c6960b401031004003803483c0b00310104240078900307000c4960384005a5035591000032244040f681010562246e80e00c60b0400d002000152204500590303607080030081315601000c1c81c07400100050744007000c3c1094078811f1080c0325920703031110102da040c00811282c510010350358012140441d141002982c1c0c0010321408c900414068185009403290003c0d103900c002c0c0344c3c5610a2035541d44070080700002454004082d02c40703183e0185880400352040d81e40c0070080d00b0030180c42d8698001c1030f408840507000c004042a00c1c0c94504035011025056940c41d503c9180181440c0d940540c503807021500314544103400710180c0400464200c2d180300c5aa200d00a06c9002055041c0207440a610484003a00e904442c0c541a06017a180121100c4440d0b800c10b86030015540011900314411541c6104000c4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 790839838 1250 790838588 790838593
    0x1b010b03030301170f01110d060815130305161a0c0702030c010302131710050709060c02010c080d09110918060402040e03040b0c010608010f020f03040611091206062b08030a020d060e09 81
    0x20366401034ac650300c1c440000c040c4143c4001e200481c80302c16001200510643c820f00742503080080d0800442480010901c083e10080500c4c0320207004482401015a03000d4bc01036032040c14000c142c1c0100383d403112110041e40c103065001502072600c4070707180c0b584802421404c2000e01409a1324450036240d4442d6070000e048a41003c01007103c071400ba801c20340a0b41d4050355030228516158004450000603c80d0603180000100704051000016009036104140501a0300b444e01ca884c0b824000c0f4280010698100604401003500700688d002c124150440c0c1c0450f00862005119103010b8110b110716030040817000d80016820b00e0164042d0480e0040740c12050080196000f1f80d51540240c2c03184014000742d204007040043d000a109070702c150703240310300280d074070303090401c0e94010441000c2c142511851640c4000d040082c14035000a00c0421102808289501150301202d551010b041c1400c0c020107030303100031001401c02a825030640d0200d04101c0400e100d210f23920003031740300c0c03610301030303030000c0340d60 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 790841088 1250 790839838 790839851
    0x4050304180f05060f03121c0204030f020f0a0f27020a0804050601050907200705041d12070c06081503150f101a09150c031b010b03030301170f01110d 66
    0x2480c05180001c3d940d40040d0285c44c441580084d44441c7d5807107103100c01e0401440c043c0a1a62100341d20140010318864540010008150300400c98001c50420140307103e00910002803000c02a1044c10034201d03801244c0c44a00c040024402681a00f800f003024155144041010042030790301a0700140039034014025280c0c540d8942040c0120b410302155000040346644e240d0b4031100c1a811408a0b1076625001a00d08494454002030180c407000d009446d01314403c0300040916280a2046412091408820301c1c94505541d0b5500d02c4202030380b0611050009110001d00c80c00d030b040d00e6514210f00000c00351088010fa810700840d482005640601045210b1300004050890032504002980d825210007002609000d4250030664010b030030b0140c02940b00c030441a0380f001e0400143c407826100101850711035a255665808510349007040001c030f6810554281e4050724040102d9040d00d6a1040c547c212030b14102840e0f280c40c9441e51114595031034040150035003030b42440508048035118a044c40103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 790842338 1250 790841088 790841101
    0xa0605090d03050d0b1f20071401170108060412050a090e061507060c14181903051b0102010507030c141b0f100b060f0d0504050304180f05 61
    0x140c0200e092540e000740398455a600031901030360107440304090840001c1001d40000002c1b4050a070b0845040d050001300c03030a880541070f0411201690008910804104440c03840c2010355114503502c2994103003205080080c003140d2003840c0408072218103c403008180e580d42c4502d150303a031804413819290215900c007401240d911178030440340c141d811560341c0b060143c10004c0000c4030401c050440d541c0035084080640320043c07c0c0010308140780c014440000c880c214003070041c151854000c410012800c00f0002c95003064000101403003480fa080e15101c00d0558241c0715030f000000c09420140c201d115030b000b0f84068200d41014802c41410aa0090082d6224084243d05840c041c540220205848110130f44484003c68060301900d04078400c400e50810108802d2030805201c411524515000024043d9200c003107405600c1000e14240c840d28a40361403210020602d01179010088e0030f103511540418180300c010003d071030140c547d01000385076600d46040154000c1060b1141c017890300c3d040c400042d41 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 790843588 1250 790842338 790842347
    0x8120a0e010c030806041119270b0a0807020307081c1d03070201144f14040b031c0801080105063106030f030816020d0e03011107060b0a06 61
    0x220350b90315841328005500d0f00d0082001801170341c84c81542c42e0b0400e01120051030401d1440d10b11303926064545003516900ca92190800100e40391081c5414003001710704010000c6040103c1c0c0a92a040c5840c000503259000c040381135106030071001e4080080800c058008603000d80001c80102c02000040152011030001c1a6090650312080c5120f40c000f40005009540128040200c501001c551103280005045003d80000640c00280c5198074800300c072400f650026036071b42ea0511081c3c00c0c101000001485410002c080b40340240419658442941071483c2c0b1250411f81480340b0003016100030015480020340403000160b185d0000900d0b030380001480d40070621805001c4c010282405540d640d896002191a520302d840d0002d0020280c200c0101da44094400c081c0903510030580c00c28500145c0c100241041d070041c1590300070a6100c000c0e121081d4000a10341001c005500307000d20740d10072031800a401071201c0c650718810300d0340010315101000a2a440030203903140848500300401d454605c11075 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 790844838 1250 790843588 790843607
    0x130f03030c180627090504141014060f060c1506030d140711010c0b0c09090c090d03080717010e09011b02060f25080a0c0f0503010902070c08120a0e01 66
    0x80421302164440d1840e48920200101542c03282c1e40921005980380754010031a82d086a050b24160060103c4074526003040c0188483c05030140e00c28085807481208840440c100984113510801e91003c065805850f040705546041084074140c0e011000c0d16040c2e0036211400f200e0083c0700303008075120100c1d40e0380074600290303038174903401e4160b801d0403443d950f03005007107451081850500c030400e04043e000406031500701c2e1281c90f0407001c7c00d8413440c10000b0b1000496018088400b0b0301c1342840101001d44640114102d80380e014a0004001d03241d6070010f8594100030010104900e00701c0002058155981c0740e214051811440200320182400b01c4903a0344009021108006800603800300c3c00400c802c500e41c079040803484402d141c0d078156030755050821341440d55003000400c58100c00c108500c5481e11503000a1400d5080000e0441403c40d40140103100500601c13100c0c0e5400301d9442c2c24800c1e0a40c0e00301c0034180003405c981e1115140400b216040d003006a00c140090558141115a94400c01070707030303 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 790846088 1250 790844838 790844849
    0x3021b060c0307080f070c061205070c110904080c0102070b15060307020d110c0d0f06060b09030a02040f020c0d05040905012111040e030a050c01060f060215130f03030c18 75
    0x210300f071030100d80c0d030000240d101c400100c10342c4000380001000318500b8860703d001842141c0366268001d036048410404c1c0d4600518070801e0085400b00807002c90741180f8040300046003140c3d030b4200c2d0340d290f00d8200c4480c01254030501c003961010501b0401c03c10040c1c003041c00389050a4072001c0d003041040400200c0c0c481155440d00580002c060125007500070b09480c0710300d504900684807510b00340e40105103141081c0400340c48050000d80040140042442084003820580c01c080f450460b44030f004c40c3d5a21501d490081c02195203100491042d480d95040d5801c40303a00c6000d59014902c8104020001d0b0003034010410021302d80700c000101d0000c06410450341d41c01c03040f40a207031840c05d9118151407451030b04d03c0640151b1110210b0310f0500d4144010a00300d5002d0300c80a8561685c500c4c0142143d042e81c210401040300901c0038080d00d07030005040004401c80300140d4100f5691b5050a019403c81c0b05002450b020001454404058150300405185942d40d522140004151002800c4111007032080 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 790847338 1250 790846088 790846093
    0x180301090206090d140610060f03091e0305120112120201060317030a1416030b0114031b04170105181b130204080a06090c081204090f090b0403021b060c 67
    0xc0b5158241240044e030290300032820f1502c902c0c0100580b50030081d044905001b020649070f424032400d504011000c0ea00f4510b460700b0015600140d940810341d20a01000200e504d2124038038100b0540300d4421280300700ba900303081d201d003541d403120159044001d010781144e080b004081b541044510500c604002c50390401d2202c21a9082c00c0a50582d50b4009401503060b542c9407407103c10421056003d244c019000411032124a500d418002005c46400951280c1085221600c040d0b403050300d03c00340ca0f0400b240c01c0c00746c1955070000d607895115102d2940134103050300f090b840c51034600006511240c0310700001d080c06d080320744c07448581c2c0b9160402c400145c22a17903412882c101c0181009140b2940d81402402c00619040e105c05100313103491a40801120003036145d02484003000017072603804000341035250050010070b00c800151000d0b030045000e040c00e169520311781c1090007507a0ba00305001c500c0e04082030070b099040c2410001e40380c0ca03910150030008902c154030030000e81810b4044810b00d0f50000003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 790848588 1250 790847338 790847347
    0x818030a030c12050711060c0720040204170304031e0506041209170c0310060806010b180913020420070f1a0924040809280902180301090206 62
    0x20a400801503040040200001e4070302d00c00030f403a000d210b042d0085d0029150041e244404240304c918040e030092003128070400510880000462080728201c09825040141010254010102e8000d0040740d01209000245240110340964080002c005682c0035540e05003004c09955514000d18a8a03440209583c3c0300d07000103000319414403081c000301c46252400b1082a580d540364500d03443d06c000e0385a6140e8000a40c40d403c10b2030100030001087e03040c104107025851070520141e072118814800c07174000501c00500090681e0881d90040ba101c400140315985604100b45611507031842d59504900461030b10581c19181781802e0840d091440301644620304d055a940d440d141d500104460458800140003a41c0c0d810406610089110340d280d50300170904540c0020712401045001c2e5502e04404a142c81400041800c0400f00e032000d8109131009240300b08510146404120420000984050240700c04a9080303440e400030852050800b006204016185003010700329000080002d6010030f0402 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 790849838 1250 790848588 790848607
    0x7050d0204051005030105010f0602010b0f10050a030e0d0305092a010c0c3605042310150528090c110d17090c0112021818010303081803 60
    0x80020740d2103c3d20f5600480380c26503501c0400c0c29a00c080c0c001440c1c07501450828420150f09100369458220100c4443d400821035201045010104d0b203031f03040c10043d001a1a440e024001e4103d000d408025504848140d14031600050041c034080d11a041c260058030400c62207140302c11403a000800b144030703068401c0003600c401510f000a00d1107003141c4036402c0074000241c61140d5400410a00099880c41c80540000c0b5182c0301188000240707080c1c828502400d100100b1011003603c02c3c000310780c6120f20310070500102d0b05458100f121151843c5103080094544040c00004660002c0b1041510036601341020b000c2c1c038800d102d1285083d0041844446002c03ca02c24540d08880c405408604080381c0303005810715624206201c0054803004140a20281035099203008800c5602c800c100010344180800c907030008011050710b030300903651141c0201d4000101e070300c0e4642c04803c1c1c0c85d00404140b40d19500305032004007035109210650100d0100340c00141d160b010340c40769403211444500070754a0303c1240c0c3e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 790851088 1250 790849838 790849841
    0x6190207210315090207061104030506040803070903050105070c120905091306090c0605030613060605070212010b0a09090c0b041203030c050f1b012406030b06070501150e070207050d0204 82
    0x403240c00c00305034581c008030f80c030b04407a42000000391039000d6000d650b0b90003a003040c00503504031903036481c03004004100c104003141c80815400c0c0c0007079101c1c01d165660b84034401c0845261880b50005410f5510784014409040d400c0745070440110310440d04181300303015100090311540c00d1881400e410400c0d00303001804098100c0c00c445030fa184601c80c0090003480c1511031020041c640c0e001100401c20000a1040502e030440004e0f240c02c0c810b2401703104003030810790003d0550045910090040d4641104500e10000070b4100e1080710401400c5903848036600c0407601c01405058605032050350a0038000301c0e20050800840e0140c404040050403400c044d0f55044008010300c6104c0010014180a5003000700e810000030320b2802c00081090044175000700b102d901f1203061152410042c10107400c0408d07140b8400d47c000301110164140040c10124240c0414130a102d065001070040d46020490310b041c0c410304045200303680c0040c81102c081d03a21140141d0b41c5040342d0056a902480306000800145000d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 790852338 1250 790851088 790851143
    0xe03070b091b012d081b03041104021b12071119060503102105010e010902130f020c0d020a0308071803110402130311030d1701140111030c06190207 65
    0x103810004009422058003007001200c2d2161136000101d2500a1020140415400c46100c20700ca8040c9841c5080c9592811101301c14105001d00450700494400c0c102c68684da80c2005c620401815030f0a00080c2c400e00c01c190380d2180704100d52207402000307800400d003407500026a40f01000301050000310f061100580e001d4100800c241b40201401002003400c21560b1a5035002c0c4001e043c10103240d01c0c192405600351184c500080b420b982c588a20070002d0798407403024070b00b20700b0901c80000d01c04c0110042c4c2d2001c5d01c503c3b002c0e00028421003810041c0c2c0340e40043c000110602950343c48186071141c10044580e600c2e400400d88a101c9030440904c049420380000c0c40380c2d05002040180b515034208001407040f0000d034016140490f501c032074101035040510028a83c040c0b10b187c03072800c07030440c01c60204402a041c000d41507940d20715181c3c0401d99004040030020f00c0226000c4039200d8107141c1c5080ea4504080320715071100100d0800d11821441d243c002d443d6001c0c1e10940f4920744840e5858001000d910 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 790853588 1250 790852338 790852367
    0x301052a0c070e100305120d0624120e010204170d111002131d090f03091e0402120109050115080c0a080603100e070e0c04030f030f050d0e03070b091b01 67
    0x44d207000100143c81040480d0b0030803034803078202d0344606440d4510021600107500c0100c003d2441c0ca0f07807140d00c458401c003103000c08540d0f040c8245c0740000d502c2801c005082d403c3d03c545980d0320009004c01c903041a1300410b00000f12050840712401000c003c100e070020f0241e0600040b03940310084082005005d60040c01da006000300d8003d22403541c40e4200b040c000380c0c2040150000c20b00c1e0301071050f442e5050218861075030701c62000314030703003049000800ca440301c0380c1034508031a0103424109003059440b42c048411213810540e00514558441c1d4110700100343c00e00c91460050164040c07403500c0c60042d29061b00c600005080320f41400710348941039400000c010a49949030140820580b6001d00c42d100d903125252500008103844d6050000408400202411140100d1801c0c40108009107085c00740344021075252424020b080280c410582e00b40c040c0c7d6140d410085d02744040242d84c00000005010064002c4103401416120308580c16150011800d02c1503060038610a059069400341451940008 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 790854838 1250 790853588 790853611
    0x307050f070b010b0901080f06010c0b04050106050a0305030c0105060405010311100306080d05130503030f04170304050307060c0308061203030c0a0c151506080f0a1a0301052a0c070e 80
    0x1c050380c4100001c0000d0b0000b841040340403401ca251546d10001070341e80210704190280003810300700b002038042c1300e10803002010400c3c0800001c042000a4001000402003d400c68800036207034608291243c20204007050b41750300e014002000340c501070041504994000c501d1408440500050000550b1194810720905448003c0010891802c011000c4d074401c1c0341e41c1d8207448450030302c2002a00d400681c0054840c1c2e10601c141d0b5800c0d01d031002200c040300e03a91040e615001310034202840c21405945e1082d0391600400e8800181c5075003208003940742910a55a80403180d58000400c41803c86e98a1011450740c814800204680a0400140700707400450500031104025540c550807000307020892444140e80710440743d04804000012003000d044141809801e074502180276206107640100b50144950b01c4154000317501d80c5002d0059039090006d0000e010360300c0d000c0b5071203100e5032003e0005031200c0151844068442c1e03071202618510141103000d44905031801c0c903100084040a45030030b1010 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 790856088 1250 790854838 790854847
    0x2e0f0302130e060301060503072105210a030524060307090909050c090702031204030c020f06210a06050f1302120703090209060a0302010e0d140708100f02040b0307050f 74
    0x128039540e940c001040012884402c07440c2550a050945260764807140c000d80c4000c600303200d501111203c4617820b185068000d0040540750409500c0d01011084041c62904402404220159204c000301641c941c10389060119890b150a0b492982d66620800c1009999030035400c2954038000c0002c50b0081c115280c00010f0700e480360030410031201001c0007122a517002e0b588424442c14014002980824580007450514084941c8052407890081c0001c04110709104448219624451941b001c1d01380078182c1c5071601d164000003e00c80782c03d81017411502580380000b4462404500035082030b6000035080502041c4103005001902c0880c3c034040d03580c15000d00142203c030005016252152085030b8012484a40e50300501c15540c01c0034240b60b0142c41001828400360b6001202940303000415a6001c0d03c0a901e0300f000c4501c100d141170040c00c1805481c07c0040c0f820310024030414050469082080319924500c1c10000303d04c00c911072540305007400c1c00001e00b8680180c0140110024042a180c40d1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 790857338 1250 790856088 790856107
    0x12040c120b06040c201b0103090c1703310509130803060a0305030a090e01210b0411030304120302060a1a0111030405090a0203010e09060919030e0a0e062e0f0302 71
    0x1881807106840307481b54011801d00c15007902000325180015800c2c01c08010126440d2240104501c1f1401804800003030031a201c035030f0b640100100d030f0000c4000410900b90f0307038001c0d10036420b9101d0100c800d540c41c2900b03c0c0c0460103190908902d03014101e0f588003c0b200c56010380e40c0700890b030001019158800c0d010311001022034403c0c40180a01d0349203075100e540141c249250346100da001038120301d01480111501c202c0c9821400c01040c1c850360400c04002c020b0b03941d803034400e03103969105042c19010301000ca0002041c10102103c032200e24480c1e002e40319696a984c10b40001c82c1c0c01c410161054041f01024413034294010230241d00c2100c03071070702600d203019220340c0825601c2c0030540760282080e074004010407400250001c010740240f90036000c0e020b1418034102c5c50b40d40d160301402807207110002c03100340001c05016404189404102501c40250543c0c1d813050050b06c02400c5034202d004910031540f46180282c0c1c4407101c2000954a500c51f08040b90f500412508140000003041c18540d00704088540d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 790858588 1250 790857338 790857377
    0x30b031b010e3610210803040807020a1e080102031005011107152a02030615130f020408120307080c07030309081603030f02120c091512040c120b06040c 67
    0x40409200d50760328094203052000070400030300340e40140d840d28202c1d002150003030441c5c5071030011140c000d034505460fa11642003108039840303101402035100c682c1542c00100c5502c1104151403100c5280c0c20030000983d12a4407a01303030700c801c950300040e58400d5201403000e580940c03120000c070740c40b610448003481c0d00c4099060380464021f0207030001c00c0202d9500481030b50794100c0b0300728080140f000b4201180080c3d021981d508030207000d243e52403442640148049c0c807042c14082d080ca8469405000c80c1c103405030400029071040c040c1440c1801004050000120803000f00c03406115a07030350b40085680c03603c03001100390308142021030800d605e85002c0d00100d0840030151800030049030745640941007616001c1d089451900038020101d00600501c0928600d00001990042c81414640e80c1c1c1c00b9544000f4181000d035442420f01410081807510300c0c1118034250f603105602c03075070401d40255181c2004a80110680e84020700621501001980e64141074100013101da0440c1000c1204440101c410704 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 790859838 1250 790858588 790858669
    0xf1309031e03090606151d03010f11070b01270f020f0c0c01081b0405090903070209010608190902060f07061b0c021908120c0708010c030b031b010e 65
    0x200040d072900e144000b84613013446064002c0000c0c0618280d404580b110141a51700130002c110010710b40c840150800340c034207411a00e801c8043d0130080150400d1818150b502d6005003105540d0360340c00344004101d0003481c071800c103c1c032080114007401d10042c8200240c0507210a0503900d030310320f80a12018105d00aa0710140210f0101c10000d42840c0d60b03640b0005010560007062260541c401c9050441050046403c807403c0d1441070780c4090866444240051451050b0900207400980600c00042c0d85640540194002c55407102c2031031800228955490a590000304c0203540f00781e08101102000c00c1d0344c0e000300240e03442002c01240b02e41d501e04030345c1c000500b800c000f5404a66049040e004514103401d103c4440e0042a90b1108030500b0b1808070780c0e0b03403400141900515480001e00040800040242074000e06104009208c0340275504402400380420841e854001c2c411701c50703284501d41d843c0071039041105042e503510341848103003001c0000280003401a40c0c03040b01c48100000c4040000210f08 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 790861088 1250 790859838 790859897
    0x120c090a0b03070f02160510050403020907200d05040e071b0506011e030b0105010f050d0509010204030c170d1b02120c0a15090303080a0f020d0b0f0f130903 69
    0x40e220f20300020040c008005803040340c8219009684000a1622a00c4012003510003c2c3c0c0c0001814000100c1528036105a40001e9408242ea030100484254425008a100d410400c1007440e0f500401c54100d98820700362441a002c60810702c400e0061405121845600102501d07041c4940c0c005000445400c4aa030203090b14240c21440040c410894a0350108008107115410510703401d1864560341503412040c01401d04112124590700f000320322600581b98a1b07400140200441e05101c6141c078001e50242c80121484010804006008103200303090380692038201c40a0055030414400c1119611340e840c40d00607055108440030310260b100d50b124a001d0441c400020a6910041010006c41016541c42015008602c1c050301c155141c1c00f148031070459505080054a54460911003001f820b010b41004000d140b0100c2d49081d0300303890303811416090301c081e103106650081000c00e21040310b407000c08881d04100305440c175050500c0c0740d51120881d54040c3c54014078594000400c40340101c0c166022 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 790862338 1250 790861088 790861109
    0x50a0f0e0a2c060d0c050f01020307080c0a0b06060a020c040f42081c200a021203031005060721090f05011e0c06090803010b1c02040803120c090a 64
    0x40880b2000890030150043c4048031903005641c1c440d65021000325441c001d050140448500e0b0008a034020400d582007680d105845903147c0c4200480503903602e02c10341044d2640d40020000c42c05038240030301143d103088131640c0030f00300e0040c00740180030240c030b0480d02d0215015074400351100c0240041c1103102d000784d0450400620328012800701003007504a248600c0910114000402500800064901d034414624013011110480390400b44d0b810480e42c41040b614601280c42a050524040b1780d110344c140c03003100c00e18261038202041c59540d02003140c02c00a00c110051081c4024070740203000d4074045100704100e001e0b0f0b0210308251002040b2103a82003010400350b80f03003800040e0046141801504087ca01001a815a01c50606842020503114000c0c0300880d0100018402107030800c105147d040002c0d0350b600d5039110000412584001030b400314948543e03000d400043c043d40203c40844040c0e030011820078071028400021120301900054a80d002002540a591100101c0e00000c0030b01245 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 790863588 1250 790862338 790862399
    0x504020f270705130506090609090a020f03100824010611030d0614131404020103110c0f0d0306090e0309040e150a0c0f020d08040b192406050a0f0e0a 66
    0x7680c102044c40d0040c9114160070300c150701c0d403900c0759000c0d20108001103c1580d440c0e2a04205e205c020300c20707014003544400c80003041000d035130107070850350040754441400c4401d4100c500d40c94030441003411519429903030042d0010401c9070300c9102c920414240510603a4505680185c00710102c0d5000d50007900b07490400842c40c00180380049078500c196480f042d0030301c074512241640b80c0c0c18a80c000e0009042c107642e420300340d0340d04028200750342008220300203c0380c0321500c0707224143c0e440031102c0314180040e04203000450155803901981d0314244000004504045ca0441040701a013410b0100b1000c134071414514286500200110f2400f800b061030300040c04580301e0b00c0003442c6150f14000c00080d5031209800d98540e84c1d1000740c056000350051200741640d117945100e244a102c90800e11034443d424601c0f907100c40400c8084403d84040f035000145540b0755035000644060046031102404a082460110101400b400030010420340c02002c000301a601c07551100b52160076a44100b007111400c25 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 790864838 1250 790863588 790863607
    0x3180b0108060606040303020d0503100801090507140f150a0e0a0b1201140913020604090c03060f0f1a0c07030209010314011d1b1c0b070806040504020f270705 70
    0x4402c41c3c0044040e00e441d0b14090441d100603555101d0541e040042080002c001120001c116003000b0103040d51400911a1031041d040c03259940c001401100c01d2021000c1c9405558500550001100107014117490a4100e0218007081c0741d41010202c42e061001c0c115000580780d40f03501c0d01001400c40704490035150400754080c5154148141c000420b104800c041c01c8409540f0183c0403544205181080d118004241c4080b031082d010700d40c006054982400211040b08c4d80641040041d00c000347d00800c20a81c0e00d000d2084510300c28800d100d01407450707405183c000b0030800010701641c00184202c1d07103000d6890380070900810f0264000c1c0c400c04000750320150042c10038000d801e4101c00307800064089907a1407200300d0b2100b0380b0360a00e03c22501d103a014540c558590030300080302c55420901d0318405100074240107a084101300c41c8800007500c3c0500203900d80c078061086900880d005400418100e869a061040e810024100c02c0a070500e00c0381e03100b0014a1580c941c0348103036131581d40c1c030b907c038281c01 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 790866088 1250 790864838 790864843
    0x210c0f0d1a04060e0106050d080a020f01110a110c10050c0a08070b040203010c230703120f060501020607180506280f0e032103131703100504230703180b0108 69
    0x40e080c1c103941d0412904207c15568104200a400d42240e10b1b150303100741e21071090385050109001da8100f5424072a040790000b8001019050104103915400c000c1d240300c880c156158400600c41507030040e009401007072594800c50203000c914080e48110344c614a02a160864141c0180004441c03041103c4200400c6040030300482141d0031b02402c124105107501c54002e0000a440340340500101e0020032154245481096455446ca0b0380c100308100101d00580c0a40160180b80580350252140c54041003910b48540501c0381c0030580035180c0c00115003080100300c5a41e205200b440712459800000300b8414400032013030500c02c0c2e03198503411030700c003595940689600e503e03440440c40780d00603c0785610709900701c1082e8000c5110140f900c6689980e0a940e52407030307448a000181c040a400000800e8131441300006500130500289895241e035502c070108015a140400d00a012180142140d201d01c1d0402c0c8040b500a4090304010400001200b0004c4070401245020388402220070010000b86809 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 790867338 1250 790866088 790866101
    0xa080c011a1c030e2403070807020d121104080312061c05100222080609010f0b010c0b040602040915031208090a03081f0303030506210c0f0d1a0406 65
    0x191009061502002440b2100d00d141d802c0240a010300081c14518650b5221003011a0f100040c808a03009841d840c400d10090304121020808501c0f2070340801c80c0d1301d00008005c00032401e240d541405114104010703502a124040c01820f20107070501010030710800074005840780901c0c0061400c804d1a01d54100188006086c4405090440704a904408184049610b001c08900a200507a6808019100460103101c0c90001c40321304020321000b01d1501d001052b442e018804090007440002ca10703011500c200c44148400341e0102d045036940500145980c030a40340d2050181d5001820300b940c40002e18280d84600c1d00d10841040040014020000044800040d5044600c1c0841c07841c94075401c0c0ca40da8820800002c0c0c00d11014500203a00c2c200c4420f146028003109000c5030010355540d143c007a01401003038540601c10180c490500f5007034089200c88050000c1803900503c0c0c4400203205004d4034000b4168203603041810841035502051000860fa0582c04808510611600d07090402d0022030b001c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 790868588 1250 790867338 790867391
    0x90b031605030727020304240b10031d1902193204020d0e0d142703010c021c05180f03010e0d02010614040608120702030a080c01 57
    0x4080ca02031000c0d440005041e42580c2210190300d14403120001c04507a4603222030008018240004200010444001d0814a4240c0031441098044648006c4142034502c0301520319041a4002030900200d8400d82010b81d224080d07210418074114060007042c14181000c020700c03c4206801003120440c200103415022903000d05c2203c101050822400c051103040c1c40e840d00401240444001502c1c0129800c0c1040e10300300188115034030304c1c1581c003407006003200c2a0170300a14014018207030000d40c002c440c030520605160a906207000f80c411400c0c5a4030000c000d03000001d0f03100031401041510244542042e15101e5001002d040100840600c004c0200702c40031820002e082c080d42f100010709446e606640c1c0011280700d2080700e0b02e0000701c0e0052500d43c004c03a802d4413980100011046d0103512020980f28800b0350310400c50341007c1800300b034403054411032800d540407003130141c4032040303e03409880312620040c00e548109503251200c001d19000a803031080075940d02c85240c074145c980c10703403419030100 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 790869838 1250 790868588 790868623
    0x151103030906070e1302030f34051b0a050601080607090f030206030618040b0109061703030f180f1c110c091005040204171002030f041b0b04090b03 65
    0xc1e04140c5640c60b0980501003e0038400c1880c200d4009075605003a5481200f80e420b011500c91800c03d07202140c00303c0c00d55010820b0140e0503d0b48903180700c1ca40842e64107503c0942c0004964412070700407940c9600c103101401e01101c00c0750392a04604130a0000d070a085000d14018149941800f503601d003040d00103030000d07040c0604207000700100140700c1440001c0326011214030761241e44860100380e040e00118102d144200c400400c0104000d05110141c0c10303030704404810000746484a4540e0039800c8054602d80f1140c2c070030b1002885610f22490407562080c072040c2150002060a50703624541510101c05240030741000100c0c03c0807887e00d0180400711002490910800c9280640e850741310955240c1d01409007c600001684000842125900030480604110340d255038645603041445251062141f41e80902e44003070070050703e0307030083d00d0044c10301819110383d40d00d0300d0703850000b5000800314010084002c01d10001c2c800b03281e00058002409061001328103542d0460406060460041e440500711 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 790871088 1250 790869838 790869841
    0xf03161202010b090103060903021501180b0108060a05150702100807030b0108010b2d0d0b0a050603040c230907030915060b090114090a080c18130201050a051315110303 74
    0x590b1229480c4c0d0442c1e40203900045d5002007401c0483c10807111080d21640750840c0c90001400c0401c1c03500e04600300400c1782d010400c2c400c00c04011240a90252102c60b8404407445003404a49050b044826801001108062070020305502080c404020010f0b81c0010a400804000910ba007502501c44c0d036100900e4030500c1503050600410a40c0a8145100c40310081d841c1420090341c00700c0500f0303400d48841b00240b500c42c0c0c140d0103144064040300740e65a001e4070001320001441c6c2004000e40780580c0e4015242461030b801c1606140c0c06440903007070001c14010a011111035500d80500305401000710340c0d00401d00082905100403080b241004010b4100d1074201e040100c0d0031b46500f516901ca2013480c01803410303030300450380d41300c0b500550032480c0e4402022840082d11140000c0c280420303680941d0004220882500c11515404041314824941e1080d000798000541c410300041003511010b0428604200c0e00280c25845204c00e60083c940c445a01c8010015158004d900d0028100b102c10080d40b55 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 790872338 1250 790871088 790871111
    0x1b1b091302030a0f02010c1b090e03091503100f030f031407110f03030720090c04030c06030c1103030f0103050c120c0904050708030a05040338090f0316120201 70
    0x2542c00340300f0007500101300842c05404580c403c2c10400700030350f00140080b4040d00650068940420303e84540306040b8501000c02014040c04015510500002001403910f00ccd14800da030142a44018151107104960b0100410f43d032881403000405540650007010f1104480d15010b8403080070740c9500e00030795005000ca0f0001441042c001e05400303400380d407000251450f090109146000b010701c010480b079580002282c02021101880120004c01c507000905515841c02c890001e11540c0030240806900314402d21169019400c03940b0007100905c2d040c0b010b41c1c440851182181c009507030206105c50340d41c0040040c09030411455030302002c103d45026800b102c4603440c075176420145071304a0280800400003801d1203002d1007071400910301002540e99030050302c580240a03074060b000840b402c489141d443c0a8442d40d20b00c47d01420180e01c4070080d00c1b464031583c600c0549400611008851281c07180c0c200344050107001804403400c9410a64101000342d00e400e69a8200781c1d07204408580c5008544a0b0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 790873588 1250 790872338 790872343
    0x160602010606090b1227101a0603060303030a2403111003020418110f0403140f010606140304060f0c1d040b240c06040321050603060c1b1b09130203 65
    0x400c800703508504c1c0c0892441d00b2240d0481c101d5113280351000c0c0107d4080600d0b458590300b040c1002c40030080700c0001a250f0900b0458640000e803607061b0198814000240340080940c0100111202074201e43c0e0b0b10f0b07681204c041031f400000e800440d10f009080b0b00d45c03582420204058100d038200b41c1415818582003c00f028010981944801c2e01ca5480394040c4190042c010200d40301030046100c80c0740c0d15612030920108410030900d0904003072250342c1c000b5507645018864502070303498a0342d500400011644d400c80c041c1d0009002540c450342e5a6005d0000715a041c49260000c100d281c0758030280c8c0107a038401c4140100c0c801081c5004134104640498a60717551040140312450f07140c50700900c1c035a000c0c148640c0f4003504c88100014855907003440149034001c4881d6401000e8400840000403144420300180e500035235a603078059119101080804503010050103000a000352a002d1092000e803090380b40c0f9204002c41d511a40d111846036440c1e05110800c2940011499100c0300b2001c0700d036000c46d5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 790874838 1250 790873588 790873591
    0x15060d062112050901030b0910030201120c02030d0b01170115020706020a050a08070c1505040302100e030a0b0601171003050f030a02100207081209010f0b030a03090302060705160602010606090b12 86
    0x3c00400085100c1c0c2c1c0d0b8020780c8103440d17040c0080d1120409281400309901e2203919404140d02186254940c1c41601c00075000c0d00b0402040d41c7c0c05582407d0702e10003071001800c4944440c9041c000008118007814440b040041d009004444022500c0f070801000a0704000c41a007203c000c5421081c00540880d100090300044c0300d500907640c80c0d458189080804907107086402c1840d0400035221204845a44800079001780c80c008c481401c401035055400b0381e2079010f08445d40750581c00076030a440215200410065000310117041060381082444c0d1713424040c4004440c000c2d0010102801401400130411282a80d003917020003c0d441c3c1480c502010b9038407500da00d0b0845603d030300003030b14504015600d0161000c0041c0003410240b40d040600110703003e4016440f42022181c41d000c480c000320325000034859106901511188070040c19500ce104641c0d20814080d0303028490b009100111220031000040241125800000c180d41071402c000c1c021041c0da403040b0440a41400701c030b145a2401880e00c1d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 790876088 1250 790874838 790874873
    0xa06120c03120c05030d0203070305071d041a04060305061909080d0507020a020934200c030a05030406090801062103120606091403070e0f15060d0621 66
    0xc00c80351000c2c075801c485030b0700d52110051141c00702207050201d60034507030051801030716103032424407407940c5040040300c3d079845c9240501d400c00e090400c0f6540c41e08140e8044515481c00325210301440303e01c000408d041c5c88075540125160341c810307010812464040c0440007580c13904c4102c240480f81d200d41303038101940a040000064036949801182545000b00200d4036981e80c0a004822240b03005a00c940035055208102464100341201c1418800c2d01074074883c1c0036424030303110a0b003943d810800d50000c0c07410811141e641845444640300d11507400300070601c40c1c03c1c132840055035260300f403500050011007a0f600001c95681480410f00910192040010000514003c3d08806c040e86090881d040090480e00912440c585074000c40d41c40ea11000d05003d41320704a0608006600100500d03603141003074401c0030450328044011608800c14030200c5038000d07011030900315400418000080240d840701c10103c02030355444004001b04042e150b080b483d8130303100c000b464260071050b407900307000c4079402d1520 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 790877338 1250 790876088 790876103
    0x240d1a0c070f03080702240114010504030203150115020d09060c0203011b030203011401020f0a0605060a031703060109050d020d150e1905151905040201050405180a06120c03 76
    0x5400c0d20001003910034035504a10008101101c80c2000f401250094440130014000d0613006445860b90540e250f0b40e003810f5240c0c1d0354090b880c104607000225a00304071241009400c000000141e60204840621140751102030506541346c0b01c0f44a8180c4c0f14120308409540019129042e195005442c2404503031007070070125040003440c07000900421013003a0702e85204005a00c031782c01075541036000d54142c81050355000303561440c1900580c1e8401680d007031030001782d012102000000c0c4030340e046290401d80160410615548940e282e4104184403121000580004420451310790380c4a4a4130000b0202980d0600c0520309035004181c01290343c0001920100c943e40d080c618a24031503100f0420700300300c107003600c500110000000c1004940c840302590325200740c0031900c8a0051105078540105549090241d10824410a2070007908000304140e05000d0240000500c035110031460410100124004040790302e04030700000304a0328103400510010601c480f80340c0003d98041c4910082e039810211 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 790878588 1250 790877338 790877341
    0xb030604090f080c06041403131203031508010209040510080312090c030a0b0609181902030307080a1101050702030c0c010c110a0605030405011a130b011403240d1a 72
    0x2044a0300c0c55003940300030600b9400103011144044049078090045205030700411f4070601880d80b1720303600d0060501c80110382c182c0e0102005080d40c0700b449603203001e01c6820080340c5948540080d58a001041e44980c2860b50009101c0129103824070030703164048001405504c9640c248034403141c7e42d0081150f180801002c0c0f0002c210400c00410049503e008001c0032100c000f101498070b55110101a40c02174090302000d80803802012000da964030a28090304001c049146501075004940503035110141e8040c0000c2041c00d01040340c0c40000c00c0352a103142c071031040368802c85464500b186c400401610854009200b02c10707201d2004100707614038010900c0d004400000070304114050070905850b0a5001400f420006009078004001d1446103009800802c002821240071003204420348c1c000076880004540d42c403090423441d5004110326203040c54895064a40b101c03903c0c14542c4103407070070315036200c0704410540141040c0030381c08650710054450540f0710000d9900e18500c3d02c040b08030b82c550417030440e0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 790879838 1250 790878588 790878593
    0xf151812061407020d03050c0a170406090519030f08012106020d060303020a05160302060904050a150618080a2d0b04060203010e1f06050901090b1210050a0b03060409 73
    0x4028802c070329481429503509040c03030a006540c0d04000c0300c034280883d09080010b4281e00d1f404c0b043e55190303d0f4584541c0311082081e402d681c081d990050041b10300f2a40c480094010820411076041c8080d540a0090762008960a01401e2070200000c0c2e401040905401401240c4802441103199148184400300c0b101003440c1c6000030340500b0b25020a00351405000100313060b8000f070003610f018001c030306548500c80c17001c44045070088a0301010350001ca081101ca0f0590a01c2d5004541c822150000024220350900c1180c100140a600c02d0780011028031000f016250b1103101d0100401c104001403032080d1099031228482c01e81c10314110307a60303800a00c8503006582428149801c440c0c4c00b01c1c85c0000c6190030b00e40315009400a003d01200d001a590000380d8800b040c100c10f00d480c4509c1c000d1443d33400d260450440e000c2e44001401810000d0180001a441100e030000d4403031103400310f21030070072450071201108048440d0b0344100e109402c10b02c030030031000c02c2c200102d1303822100070f480105013640c0d00d0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 790881088 1250 790879838 790879841
    0x7021c03020f130518011d10120b0106201c021c030207051c120905071701020c0c040b060708090a03080403050a03090e0907050405130c0f15181206 65
    0x980320140808000509050008503419400c0f041e24402c884904004403400100c041c001c800340529070051021036441c240c09056280307003a80c00304090805003101071b01c0e251000d16007942028200e9090080c1e00040c0076440e00a4407801216821070036040362050b104c0c0f80e09542c0c00d03100b01a0703480c22032465803440400d84284640c81001450408408200e1064030b00240254000701040c3e0710b9009031303d11038024101e607803121440c8100a96480100300c001d01c1c3d40f180240707407003501102e0601c194000050558503030184003541c0c090074400140c0310041c6120883c14039900d440c3d140d00c12464032120480c00e81d03031081a500c015070030038100740d01c0303c251a0116041150300d030006496000081800000c1010000b003034400a0b1203070ba1464851540da008001002000352a01c1c84682c000711810300c0341c1d04156002c0fa5000807005084400003140e516010401c01d80c1d41c00078000000d45203000c2c00b5a0710302100e06400c411242c030b401e031105c1340460149021086076014504c0d1a03203842203008180700d000d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 790882338 1250 790881088 790881097
    0x150c0f02070506070f140a11030318040e01090605090c09090606090115050d0203042009062101091b15020d05030a0203070c230706080c0d020c0312130c080607021c0302 74
    0x141090380c0b18071b420885540e4404100d0320845041d0340310900c004060074040156000c0340040040114100c0c101000c00010b0f01491040524070741d40c40e2031000c00309403a40034450240c80c4440c064001103000b01d0a008108800408082c243d030300410074014a901c0724048a411101248010b001e05e50440208841c14820714150b40c52403400401800280844074003900300740140c66014484501c0b40c1400d00511740c50441d0020340c452010740f850f403800e401e65800c104c10381401c20000034802c030503030350380c00303410702d03010600c0380d00d05200f0355092003144804486007030f002155000501c10b811582078000d11611009280e101016004800301b02154010000b9240a90740400d280340744a90040d02110440c07180f0030148a94480da00000900350b00541c41907014140c00b008080c613085055501c03401a40c004481c20701d8510013040861003e041c494807042c041e20005401a00448050821940134000c5800c01d034202d81010060040c2d082d000a483c09640081c090f44200d00d103c00a170030b600a028 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 790883588 1250 790882338 790882343
    0x50108040213050403170f151c0c0b090301271203090b090a06050604061a03100b031f14032508070f050a080c010f05030c090607150c0f02070506070f 66
    0x101030a2004141e0031120103408001007440c1148103030761f40c244d8a0540001502c00a8001c80c030a03400341c0c0c080c00c00548041034031180c0517603d541c59079507036030300342400300242c2c800701501c0808181081c203450300b030140d0f907540c1480ba000c2b800420601d0810010b040d28110005000203103002c40b03841d403030303000b40c01c911aa960050140300c842e00d000701446480f0045084129400c1d07140030300064041c600361041c401690082100c020320115500c4c0907840da603002501e104003860300da4400280c2c101250009504c030700ea550140000c802521210f03041d20120641140d940d80301d09a642e04d0843d140003c03003c2e03600505011142e0005042e8803181c0f00201c003030708680b10342c0c0201000441c02d81503410b5148100c0f030095442c01c5180d03a64200301a2200443d003007890001e15280e1540344128804c002035a00186246062450940600c000807626400350030101d40102d0042c0b15100c0d41c207418802c1e800c0749030a5007098050300f00c4404000352184420f0240501c245800301c0c0c2e07401800308040e000024260f = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 790884838 1250 790883588 790883591
    0x105100507211d09070c2003161409040b0c09210c0102250312091503090201230f0d020909090a0c0602010908030705030703020c010f23060a050108040213 68
    0x3046003030010001e000d150400c4210100043c2001c409080c40034110340702d40b41135030301e1582c4800142c0d01c5a4910110155031031001080b0545404941d80034882c001d81184012009400715180c0219805607030258140d9510501d00c007010040400c0c900d45809611000002c40d080d50b030000440000c0904405802d5926918003410074148489000109415403a03026000c4403141c0500d4580541c6605160480d81e6003100542c104000041790614032004000e158202201d016840c2e22904013120744000403800000c1d214855502503580003603540e40300c01c080008006680300300f20b51955052080e8024035040208c0003900e107088817680c2e410340d84004001030001010f82008500070365034803942001582d54032070a240010300d20380144200d072009580002d50030304607507900c4d8042d00c4541000b07210509054007003149040c0b071b24003842744144e400c0c2d460000145d0010704070074900706038030320750004c81e14000c8107c24055140c1e540d00c411402c80c0c8091078100c8044c0c3e2a0300c00316415034403004081a119 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 790886088 1250 790884838 790884893
    0x110a030324090614090405030d18080d050f090c0d0b0604090f0c03020102012702100c060e0d0315081002031b070f030323190213090b040b0102060105100507 69
    0x100b015003000b0212800c42d901c1c1c1040200d0031080154191080d2030041040d40108800a5222034640001007500040450005103a0341d50700c80b5031503507000012520b007140d0760750104111a08210703060f9800035500780050000c3c0300f091011410344440c600c00600701c0910540003604544d115000200416440b0081075030300041894090340705038403804200d000d03500745140c0a0420710b18100400d4055171000d005400411203400340303d43c41d561500702c0020400101c0350b00000c00c84a02441206071078100c02401600c044640007070407560b584040400c4003a11200412460000081e4003808412130040181d8986440503140340c0c1d40c2000c819440780710303000314600c0d0500c084100c440250b28020b0301e003030010109001c1c814510b40b80c064924582e84040e0004030704022880c003142c440204c01c9000c01031510314030040341c446c02011640304101c0180c48550300300603410700f40039000c0c0042007030004200950411002821000d0445040420042c0100e40031701403088030060303071940c0c50408100c80b0f0314 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 790887338 1250 790886088 790886099
    0x14010f111206010c0b0118020f03090c0f01050a0c0624170d1e0509030c0603090c21120d060308040905010306180830011212110a030324 60
    0x85400a03031044050300765440c00506654010207215544580c0081d42a800740c0c20003000c0801a160711040000c002e600340015280f10220b14001d40c01000620002c1050000303800401204072941031000d41040400e03c45000301355044582200e00c1d81e404400820714501c10311300781556403496840800d110015100004140c00d0b2a010501d01c2020035094030104052045c0944040d40344103042c210340b4400095046105100d80050303c80d0107801410346200c0b0120710002030712504140c910803802d0700410308200191074002484a9440c00c1c1000c0e603400e90041c0544a0784550040710580011880040c0814540803964072180c065580041c100740c856403111942c0d40203040901085459034030b84080b04403462805c0200703088950344201c4261401c1001320032104444040c0003c401490460041502009104101940a005a42403101020040f1308020271803049401a03c021700808201d183e07194000071451204240e0182804640d500602d41180d00440c0c1c6508900c00c40c00798072501280 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 790888588 1250 790887338 790887371
    0x129031f050106110105071e05090d080a2615130504030f080c120105130f09050607021e1914100e0c0307230a051c210c14010f 56
    0x182d0b203d075074803580c80302400203515089078000d1701d01d480030507417503403030401c0302d8000394801d45255500d407522070700b002c4c8401f011560b94040e105080701e112001181217020720394480d890300b007021000d240280b84600c07012040350803000c000d029000c1901c500c1f50408280d03160b5000c00d0005154100c0d0801203072415040040012a01d180d81e04005104d500200d41c981800106986410704040303c4003c06918103001c01003c215000014503549440e40c3c0e021107407840d1072142048207400359006e0a494a0841c0b4002d040c103601c20344c0744045440904000c6400c0720001a2141440401007440740310345118200760959004c02e04001002d40b003050b612250b01241a0003040070311020303400300c800c22004e05c4105512544503028041402290054003030702592100c0350f000c0007044c0504258462600c50012400c502c1b4880c501103100c0900c0e80c00d54007049080b8407000d80000c0c1041020400501920004200140c0c00f030014080119940e48280314100070351040c2c10060300c002041140d580550003440 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 790889838 1250 790888588 790888591
    0x1a0408042102090708060a12080d0f021c0b041e0903020c0109080d1209120903030e030c06070b060f0307140111010b0307061103040330020129031f05 66
    0x4084641c1070070712002403008100700d44407070350060240400e6075409208442c5200d00500c1d15500100401d0001400864070050507170707460103445a00d650340c52548818055071180c0ca0744100080c4104000540c03510280500c240d40c2d01407010215056401c400050090010003280d1000380703400e4442002107140c2d80c3c0c80090100c0c844c1d001d641818130071038010345000f100e920451105403c1111400e0100f13110748210055580d50100015180c0c88030b4072080444030b003448114001c50a80d5000b8001d154000100c08410b820890051000d07078045408608207010315807006201e0814a00031071083e644500b00300410b81006401c56004a58070b2500000600c04005424081400c100f002811460103024a1402c0c05010300100000ea161940456007001110400b6100380003c0c080400058211107101c0040300c286070b103412240310803002e14003d031442c21495405580c50b09508501c03842c0c80b00026440c03800c051551410810018010a0070300131414007190b107010500e090180003491692015 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 790891088 1250 790889838 790889849
    0x1210503391b1002150703021b0129010c060510260c0108091608030d14040b01061b0203190b0708190c0e100f1407020105030c071a040804 61
    0x300c0003008022154071001e01d0b0202250300240c00454459070304100d2103000300c00000d84104c806002a507a02c501c9048025601c0704000703034000810ba500b2080007483c12646500781c80c020450518513503860f46800020055550540018450b0701415030700448441c0c1d14142c100205002618100d5002c000440d1740d40070310f0314410703454035486444c00b40b148048041015400000c1c84406136407030055405030340c0105000c40d24841c0c2500c120040707451081c0c0e031004092100041d07840f00e080c44611010b481d460b440e500c0c2c80c030001c071007004003164043c290a4115400c03800c010a032075a1030804680c141d9960302020307415209030703103120f02d004c003000000710216070040e146100c41c0c0d00c907071004590030b6a054600700500c01145004a1046c46154400140d80703c2a0414480b04040000880c106025114020000ca407200a084074150b4200c0700c0c0b07800f40da0400d074000e89007030724030350010300701e03002c086c0004080540c003140c01c80800c00102c0e580c0ba07040030074280148461502d4640010b0690060260 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 790892338 1250 790891088 790891177
    0x20030d050723090402030604090c0f1503020307020c10030b030f06010302040e03070210051c0c020c01021006061d0303040503070e041104020a0c030c020a0e07120b060301210503 78
    0x110092401e00c0d44682c01c1100c030310049600c1e010340c3d1001c01003c1d400282219034041d036100040c4000604198503000185000419000f00d1490320a500030341d990388078480c506041c0100308218030164081041c4075900c03001c94207105640c5c82c62604400802c0c0281c0000d4051141465408400720b0000f4081d0490344202c9091294450f0300080c103441c1c0c01250340c004d40011856821103110790007180500940203d0554849010b00140e07420410703204405106009070b048060104104d507414450003041c001990020310243d854610b0051107140d4041c40700315140c241c008078480d6079130240111001400000d045684180d200d0070f01044802040e9401c9411008038a41c07092182400d0080e00e40c4480b003619190640103840c0c800b074802ca240010120307809044034602040143d4507141075405407410340c1d51341c03c00f00700412a03502180c00c84800d03a03100e00f2060004202c034800040502c00ca10302d00309488940d40704180f8042d46140664130a412105900401e80701c02512200e401601d100700e103005 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 790893588 1250 790892338 790892357
    0x31e120905120d02060c030a0908070c030b0601030c021c050409020c1608060403120209130f05160c0c050103360b340918020702010212030c0a20030d0507 68
    0x71030075a0fa600109041025030042c20018035403201580103968480d0390113001042c6901290759034183e640c4140c00494070007915072018010711280441c45a804482800c0401000c4111580656210312408045910b1510104040700c0036104205940080186031b03015500c0d08070310762515441e0042544c60441c0041106000500f80c040015480d0145405d501d0300d49000e00741c00340c9400a50320002d5090381200c54000180400f1800c2d2088205006443d003001a50382400b11014104c4c0c03400d101000100910b030304807000498800c2c07948404451007400c000400d1004091095401100d054100c1100181c4a07200204d5000d1720140982c080d1041240d040141d0b110f80b10307a5107840c07954070203400c0c1c20151081226080d94004840158009504020f0249643c84151000080c418140da2548030380100d1013104550f010402108d074141d912038100d0071490800780100580c02071503045020403d98551095a4420b90192400e03210752400c29a581c030017001180700d002d031000380c0365400080c41344807 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 790894838 1250 790893588 790893619
    0x120c0a08060f240108151201060509060a05030c0f03190b07080f07081b0903031c05012928111501080703020f040f06170105011e031e120905 62
    0x10308403540030801c04903c048255007200440380d004000344450002e9490030754500450b590001403519400402d0000308134036041c00140020104050030807401022201018031031030358041441c02c0c0c104030980ba011410f0403a400024607048031418091600e801d2060400180095662000d00c9400b0544030301c41140c481020041c810403048a070100001c800401044000c6151000400b03040e0a03144400d00706459840042e04645c01100f4103046104141100246009640142401407075101c5211701b02c052106030000711055444c206104031071001070f20340c40814404402142ca00d84000c19210343c0c909806028110002c10004030410f40f05110030420389404805000e03060321081000780006a10b0765080c80064289500c00c2580191100e44000003040c5074805d600081107044081381050080c5103850b42100ca041e00701c603401405480d20399013003004500402044a84c4950611a001d1407162060701d050300202000308206920103002c0c6840b03a2201c8204180d4800322000c0d601e080c0ca07031 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 790896088 1250 790894838 790894861
    0x91e05010c0f0915020a05030d0e100c080c0c0a0c031103160506041a041205070510020705010905060d0905010903030e0111031e18030d060f1d0402120c0a08060f 71
    0x2910071100081003e0400d0143e0070340d89180c9030f6600110700442d5010303400e541d90541140c101540c0b1a42e4942e035404038804d4881e040240300120080040104404006420300a1203050014020440d410700003c3c405206102044198240358001c85080b204586910384003100c0ac0e40800f405110340f055040145070340d0401d02903282180d10051010385028a040ca221090b00c505010802c00e213401031200180c904400b003c061642c611400c050004c850a10b01006100c00850845c0d20071940510700074400c50b40c00c88800020744508461064031185040e82034005085241c0c2e0003005542080031050030150076130411084000c2400003401080c5c1031142a280c43d00003250015800d0701000d042e04607000b030010000e60002d1200340c0c80c00940e8002042d651460313104e044240c0455548107800c03c101c3c401d2000001c080c044901c0c00c900000c60264481422007800741c4083c2c400c40105000d010b20360b401300608080072901a003071002c0b0380e551714606034854600321580e0302100040b02c00500600840b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 790897338 1250 790896088 790896107
    0x60705071707080a2a0b0a02040807180c1409041a1809010e03070b0604090201091e03030f0c02030d0f12180b0609040210030e0c09040506070905030f03040504050604091e05010c 78
    0x540708080c0c100c5c4001d403141100a0005007000d40825420080800c240b501405a040a48400000b0f50012080c042c1002c0446070f80785491302c100303c00c403800c8031940f14040b412585007010071074003c2591103005841522581040d001c01d5400340c104100c521843c61849123042c811802d030002000001c2161301190313100c1c89007403001820f0100b400d0020b0384601d49503020031803d070b0040c50841030103500c031030b209000344d0403030074140d40060300d031000400416501c03040d21040c640303403032030414035000040d40402d540e07000c00541ca50612070910f0180c0c040f11721486080b00006d00c031400c1030015592404040502080001d000d0b03c107048000d000444a05001d94a24052030380507201d80200a15400112300621968151541314015a8441e00301e5564615201e8041c074060703400351030700c1d040c042d501808048656203d1402034002510507800010b0100550301203134000d4034041000e07503450002400a140240c0024180c088940040c91a080c0d050f5000128038407030340007042143c0c0390900603100c020301c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 790898588 1250 790897338 790897397
    0x803070803100302100c0b1015080a0b1306030606080d050906030c04090c08061905010f050d0e0d0512010b041511030d06080c03070b0309060705071707080a 69
    0x204205000681040025640105940805111a501c076400a050f0380f41d403448a40c00240381c440400240040c086032180c0000d02c01c07890b141c01c0c901c1e1107186061081c0d000c2c110400e0155000010748180000d401800380a0b00051459041c0c050310986034000b40401c2c0400d90398186800000f1034061070010722011254425104c190915815000300401603000409020305c0280900000403052128000c1c0d03407417444140c0315400b82e4030300441132104540d141c0c0c424400b98a1403c3c000c2110340d030403101000c424541840c0c200e0f81d4610f10480300019000000c0c40c0c0001c1d1003802c8403034080c3c640c480068a400424080380101c6643d03203054030140c5008074011401802c40c420114012280140524801c1960010981e420141101002e0381100c4413079200940707917041501c41e80c445140501030389000d4110a90b40a00b503091405580c0e9481d01c00074000410310800054007000c1c0719540030198541c45e0408075485d5920000d141540698000c550a400801c007590040d01c4100f110903500c1c18180c1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 790899838 1250 790898588 790898593
    0x80f0c131112070507061112040813030c0306140612030a0305060409021c0b1609031119030c05011803110d170c06011802090a060f02100c030e1608 65
    0x400400352001805a9107840d6000710382084005100b5003407080082c40341c2801e464094807050242001004c0d80c0e181400a62184410042c00a00d103482d1240150000c1d004402e00307480d00120300c0e00113900c207070b03e81003d0101116800e0010070048190800f9118500080d80e01d1120b8503480140040c801d4484820300b455003042c00260500d03407284e840707198410401000800d4100c8107802040200313651209049541106084460502500010841e040710f500d52040c0c484030134252004041d4400d03800010034841340a03c429070645d491040c1200c480300175005140c46959a4a480345001001e481418042855038001605c07914006090808883d08000140d03030020031102041020040200c1c110345180100c061036410b405624081d03c8801445001060035504000308072a000b5514046455094010020740d290364486c02550403c035000c41c184640340a00003201a070900345400082c0d44100e140102540038964580c001012a4075030400f603c2108200f288086203055041c016145682d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 790901088 1250 790899838 790899859
    0x105010602300c010f0e0c0a09151508010906060f0807050307111902150c1905010209042d0e0615040204080105090610230f0303071704080f0c 63
    0x140c0c004500300b52182801c1ca660008030400080c0c42c8500d40025500c44600d0395540c070240038040b510b218149420b000c40008042d40c07440217000490700e010500641d000c541e2070780b091041c0340c00c0054141000d004204002807104000410080242e0b07024480c7d0381c42c2ea802c01c4000141c4d50f008e60b840075000d07100760303841c00b0b4a50b40d084003d40f1191710181800003001407002c1c0300810380c0c2c8180068892961408011460007031580100f02c40d001c4003a204400065041000c0e0b0b1203510f0008003102c99110799031840107041164100a4024065001895003142c100000d44000c001c040000b4003105210001141005080000601c03c852000080d20050b41c0940046015016401d4841d400050000e002500d0691540c0a883c00e5900c256069906944800d090200900ca018490000f4115400300c04031b114649110004195200525141c0204140b01d91151291801d01c215005140c103d80c070f00341d680350520b032181c0d6268440c5c071510b44a07014842d0070740d0320404041991207480c0c03401003c18200 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 790902338 1250 790901088 790901113
    0xf0308090a050f03031819030f050d1a040f14041403210a06080d0c15090b0f060f0415032316140a0b07060f060914180105010602 57
    0x42410281002645205a032a0800041c00411040031000f0316000030310380740d0910b40140141103546506d04005070b00250902104a48200c0d000d07020f064041c98200700c035030482170381618107102e03c8517058211070418201c2542e104c5140c07090802c0340802c2d28200a400700d080312081c11610001c20102c55480341a0105000c540b411142c42d01440981c8143c0340381800e1014450050944040b0908000300c1c580c04000254096228806c01801c180e800740c60b00381c0a84070014080e0800a800404c1d203401015100b61070600c03907120714003a5905c240801c181e41407040345d05a1000c4110303515446800c070520b00d40b03505d0411b40144c0b640864149143c640c01400c503500c0f11200c8a44101180e03e40101e00b5110200c840108401e188442202140951850500f68000190214940541d00841c0642d01c200000000303441140e00d9607030000790000d8505c0810007454085c080c2c03a030117220840e08005400c1c03031103072841403614020400700c45840703414200d031103e2a09036842441484050b8102d100100c61 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 790903588 1250 790902338 790902347
    0x12040e060f0a09020a0206220c090f060512030c161203031107080712140a0905010c030e091014030a020f190e010e0402030610050906010f0c0c0605090306130f03 71
    0x81c200018021010349480c0c150f100c080760030003840480113034040000c0c800c0359042e0020106094008000b00e1007036441c2d9480d5684072405900c12240c900342d0300c049100400500b9030200006d07060003801c0d806400d0400c8a0a0740c0c0e0341080c424540036009100c5540c800c0c9400000000444003140c002c0101d442c041e480981c004e02503e8814401e40e04200000300005007400d0040081a11800650000c8421114014400303022440d40400d081000c1000f4058980c022580381304035007091030701c80005000c2d803504490003110b4031030481d0440f40300005e21031040d20708460724040c1c804a100c102c0c03101625408160396900c001c10b01070340000c03062060302d005003040c807542031a0303c4d42c030281000b02c9642c90000e02a0410240c1c00801c13800000c6091008500e014070003150402c681c4600c642506003844009011400c0c003030f2085041c0034541c03041300b00e645e000e40081d06d0b5054000c5051741c15a507541c0c10161259000312440b511034041c2d100012026207000c90041080758200307507494651101303980c0584 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 790904838 1250 790903588 790903609
    0x10e0114070206280c0201020319020c18090f0307020a03020d02010519020c0414100501121112100611060a0209060903031c06090b031c090f060c030212040e06 70
    0x1020401c01407080540c40b400024000344d89075030309201d0800c19080910050440c82c41d00c1c2c400f00810130f00c03007002507030b03000061314410141010040b00f005803040d0244d141c640d41c007800503007081001200b050b03511210601144501031482c250b43e180710203c0c1d8078903180d10551400030341c4042640002d00260600701d80006040c0e10604009240c0b0145c43d001001740840c40840d400107a02051148555042c035015101d0400b100e029040b200b418240c114441d440c00301d000301e50402500365148020580207400019030242c80004c041c0d074507103101d00da4900b1024101c0e5000c03040704000000060040c4112400e0340d01e4032842c0d010b0304240d203c2117103603400707540104000e5078450000d210400b91507034240010030404010002e40c001e405008140002030325040d511124045282c02d01c140080d480125882c0c2203080d0915104a42c001c0b04030056649201e150420310310702c00b9019020690701d80091202000c0d9000c0c0c0c0807203c000441054500c5248240d0141c10803001c412030200d1424184042d919 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 790906088 1250 790904838 790904867
    0x5010215091216150204031a25170108030a05250c06031e050601020706030e24010f1a090f040608031305090907030f080d06050d150f0b010e01 63
    0x640c20315510440c5882c01d9006200411040c1e14580000e0080000f0401100700465074084150300709890350303d0b040158089070420841c4441da10b0000390440741c0e905400b201d11050f10b6081c2505d401428401416004a08988124420440c0c00070407540000004e483c9105019039546180903c600c2c90380075060200f510102000140c00300c1080020841e02482004e40810781d40014240de8140d00401c006802000580c0c0c000d140106009081e41c1c0850203d00b074506600700490199109020103141411101c0d84015003050205c0349000f054868018504807000d20319000801e54403580c000c15068515240030780383e010b041068096a0604200019094100410026581c0c0d500c100350fa0440c0d2240c3d071070440780c05400c5001c1c1f02d2413400080650300002d103074008220135802d507a214420307860031440103489203001049071551808150441005044064a120814111460300e2002d4418209500385280c0c202040e01400d4038441c801d02240140c140d4924541603a07070740043d100c561021101 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 790907338 1250 790906088 790906093
    0x9130203031605070801022b0c08270a030806150310261b01090f0e1305030c0709150602060601020d181a0702030f0a210e1c02030607090501021509 65
    0x140c07242e0070710282c801860048e001d0803100254070744552000d0448012000f401d840d001104038410b50008000f075014042401050010260030000c401c203004100034200740d80b0038103003c3c604059001e0700c2d06001349820384086000c0c508803d45886603000403204204641680030042084014420340488440800441a440e007501c4155050504480d2202c022800d102038903030340d889583c0141d4440007000c08801040b40340b03007804494054100d004c0c0080d40c00456000c02c0340144801403046038214000e200c00c4400040d902c0309084040c1500031241e19040400c10380c0000e0450010640e140f0410059000e4103120b220200c2c00d841440700c00b40c1201081c158100c0100f40d00c0152140380740000c0c0c50040b407684031003083c410140303002c4a0031001115604103090600000c0c100c8200c01041c2d8154840b4880220401b54049030600d41e45512160b01c0254240840d40c11802da4069009160080e030a849141d80c945d4404d0365542424821540141d000366080382d00041e810324075a4200c88818203 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 790908588 1250 790907338 790907353
    0xb0c030c12090f070f0602120a050c0601090c091a120411100c0203010f0b03120708090d0b0402040e0c060d0504050726100c05070f0609080409090209130203031605 72
    0x280c0008030422244460964840d07a0003031406401004a03070005d0800b40285900541403540003920741e401c0441c4e01f16014800706e40700660a001d103040e20019005103041700d0701903030b4802d40310000c2e282d6120072002244540d4004141092204e030702000300a00ba440c4146452900320898880c42402007090740c1603500b002d02c031030503603039628028604e00307100b1759480003408a140100741c215143c0101d0f00c10500c5c81c0482a0101e92030105040009050301079409880d01101e040001840c49090401d540c0200d90401410401500320003481c012402aa000c1004070103866205a9030000c4007200e603444801445a80451045038014030380c801d106038161032015a03902c00c078141d40103010b442988890000c003240c08030102c3c10041c0c401c00082c01201030186003030801c00035090f482004006031485401840c0d03102480103640040150680c0030080075601c0e640d40e035202c0c000b4450000120310501198020501c1603150b006518591500140035619080000221a2030341d01e000204407414004e460 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 790909838 1250 790908588 790908607
    0x703030605040f020c0606030c0306010b07060e1218180a020c0c03010912080f0106050f0c0316030f0e01031a040504050a06140f0601050a08040b0a020f0403080c070509040b0c030c 79
    0x6640003c801110003584502c059400d1900f0024014006030003903004100442c000d40e40010060b04580c840404903a48102d182021001f421450582d0003042c803511041c0080d181880f0020244450002d05251880020303904000308182002d0340b0319040180440801d60003401d4dd03008150400500c0226020800e4401c0400c6c05d50f5580e00059890b8410a440000c00b15049610180d0203802c041d481c541075810716030003810a000d000790b9020303e2203010034559401c2408000721600083d904402014400ca40d1400411201e2890707600b50009125441d074484a50290003400f0301300c415803203501c80c650000d905103c001c1c68000d02c1556a48102000b44003c950300748507403001d40084800040b11441e01d400003040740c1e88081e1080741004000c10a0000d100e5210360101d8001e6402010310384241c480040385c0c1c020b4014803510582d5908001000020040c1e500001e010340034821046d01c20301c41d901c1c41080030403001120003800b4a01c9440000b00f0302e50848004590046070724241e14100078010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 790911088 1250 790909838 790909841
    0xe16110c04060801090605060607080418021b0d023a0201141005090105011d19150203120906012402070b0c0105060a08010c090509090a0b240301060f050105070303060504 75
    0x90b0302035502c69550361003001c01d228441c05400e51044c0c3c10385004ac41c0c02030070fa443e080d641c429403088500c00c00109020302c40d11100c0e41c0480c0c1d01c14445d08014224200c004080c2030b00c2d400c1241d1520003520503d248084682c000501440503200c0b8600c80342e00902151203d041d40d04048903641003155a604044d0860f000d4508082c1d004810414a1143c09800c10081c0030000106809c0380341030150500803085412400c4071141031124040d12400d80c0090f42c0e0001110001d901e030054819525141752049a80d98004064802500c00c8000c9100503201e114503191030f80001c1c01070344486490712a0640706900700c1c2c079200c00c504590b0710444900d96507481c0c41200070f80001e4920840c694584042c840640f4000040710040c0000000802000c802540b01070700c101c00700d02c54a40034141e400c002521030207040c02405a01a0042002c50440c60541c1c1c02d02c03102c4a40c0107528013132413145842c403c1c00c1c0c00c0c14404e15042d101c003442e04c80c0303116003440d00655030f40c0c111440803020075413601c2c00801c030340e201d5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 790912338 1250 790911088 790911101
    0xc13060e100303020706140a031a0406092702030307020603071404031202060a060521070815040b0903071a1f0305061005010309081e070b04050a0308010e16110c04 72
    0x10101d0615214110310b0000e080c41250790001c02006003451302e600450b900e5a0848034404c0003403e00190500d0043c00307443c42a070070a1400c1e0381c8a460308800140c46000340c0c00c03480f815489110030212403030032598000724144000801035010390003800f0f8080181044801590411000d00306010071154401640c078903540a50011120340e40c0c2d00c07400810032034042100d6a0059a400e50a10001c0d081c10701155030315504442101ca4000c842940c0c8200301c0042c4009000f5000700c0c01647c00c80d40d4410300c142d00d0007a00b80c508032005100318000620049020041da807210780c0c04040992800c06000c2d207902c920002a001701540e03c030340e5601002040312090744800652051010b00590315000c42c02c50fa40b004035910a0f07040c181005181070000c0e4501b800ca6202044541e04280b0704809a502c51545020f1440001c080d004940f00780800d208001403404096482551802c4460381c0700ca100305084041035894070381340d68084c80701d440002d0180902c881040c0c184c004840307610460f05c0004d4207032a607 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 790913588 1250 790912338 790912351
    0x6110321180115030201030c020d0e040f0b150c070f060c11120d0903170403030c0b09011e320703050630010b10050a1b0c0303022b020c13060e 63
    0x754403c04000715600750083d049003201c28005803040014280004d4545403e03482450f11840e6210305000c010030701a840070601520203400c040da00302801e030a5401700da0002e0350071090352050460000304508000c03103d03410b65150b0360340c0301041c00ca13035a100d410035040658134603440502d124549180720340806c03140803080740c9540d03424216407850400038820103900404801030b581c200024400700b500300031503d5481e540b0040030700301030f40c0f00b0f260719004090340a41061108143e0100b1009032500e80c010018a0400940c029814403111f00742d80014800908424044c0d0160000108603034041d03031000340e00c400050040b450308140c02444418404074001d6003107103024140c004400c0d00400748902e0307040c6c0c10180c0e031030f01e84440070800c0a40345005910001e820400c441c0d4034503411080003c045111640d00c80c80a840a076101d00d0b0107074568444101a826a159607042c0d80c01d8146101850b01130861150003a1005200110900c140d8441910400d1482d030380b2000700042400000c00002c0c4202d0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 790914838 1250 790913588 790913621
    0x9090617150c0909040b070e0a08030717040b04080706090504050118020a02210705010509070b190302070218190b1f0c050a12080c0a0203030115020a0516061103211801 74
    0x54041070191042140c1c0d14440d009d110351401c1440351100000840702c1c050f410440361481440508404050380c8220b42080d0300384200424001800f51002442c80250ba0701a2a0124016258011b100444000b44070325290340d00301e0058064083e0b201e81c000c1085003036503c1034602c0011828042c0c000000101c10303625103080d0006071041842001c1c407445410a00b5500540038191500a41d02c0c47c5004100e840c2050700107034286484028000d42c100d4000641c041e0454103036002d03070409001c200c44100d41c900d9100e0042c0031806407141f011300c43d011a07440b005100c08881d40d03014840300c0402144000031010301000c100c030b81010400401c4401496403180460004084014078014042d1501800c000114001800041101034000c01601e0543e40d00d50416104170701052800c80c9010a40d000140c810702a0000904040b001000d5410940d1b206444100f680d80c00d040d0156528807078a800c45858205034110f0015422125042d1600110300c018a01007000c0341c02015070844440c1205a030740103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 790916088 1250 790914838 790914841
    0x30c040f02091e030f0f03070201030e0a0b040b010303081501140a090e09030304020f060f0d05280b01020f120f1305031903020111070b041112030a09090617150c0909040b 75
    0x185000c00405c4460310349000944801c80010303080d103641340a0100020b0500d80ca8491280a18100f04044105140c201c052044507040c20b0134800e811281c280016400102d900000482c0b071000c445451000c0c04040e5138a40e01924000e141e1060754005423103010070440700d00c2c0002440151070700443d0103100c141010b0740da83d0401c5d1040110404110000d140100b0081c004105400c0191003a01e4000b4070020020a05a84060946201d8149545401c5030300303802910482110040d58490401c11900ba002c480c001c80420100c241d942c500c40c020324400c01360821846585e43c002c0700250042241c42040010f0458685c4006400c21102104120200c001a08800c0516509008281410840c2c1d031b1514030303290881e260703610b01c582c00400240ca10600b03140b80d06031640b40d855112001903d024203a944175844150000c10307490b8544241003442e804c205c008030302c014614803403000c1800c20000510b03101d145d4103c07020320110001c0c10030f001c0c082c5c2402540e04584a60030000d00c1a4414207110016 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 790917338 1250 790916088 790916149
    0x50d0c0e0a0b0d0b04060f0219020106061809020c0c0a0303050307090f03120e030c060a17060303040f120c0f030b0f090109110d080c0d020a1a06030c040f0209 70
    0x1500e0004007010582400d05011840c070b81c40760301004600340d03003001000c038280e612810914003402d101c035240891140700242d02c01022003113009000d809502680248031060355031008072500702d80300c055003841c03100700361040114071003030360007000f0380041c04065818030281e4500117009440035500c1a008142c0000400100592000d1441c02500e4481c003100c00d01e5003035848064011801101c0d142c1070112014103c401c5039020002403050242c010000c07503131645001d00040c00c215104949a006941d40303400304820f0710b00401610203442c3c0710b003100e082d02403600c011440307004140c003419121242d400001080072418407510002a5001e01503009060800407603070321002c00c00400c0c00d032080e490803801400107100c0140440c44400f0458410410307002c942444000c511861011101a100340c0154180c060340200b01c40340764a008401514144209021a00d0b200e00100c4907031b64507030003103504c3c04020300c0e044d800040701034030340400182000190000715000b2006082c1c00800d00100d0500c0550 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 790918588 1250 790917338 790917359
    0x1a03120703090e010614031e040c14120a2a2909011e2109030f021b0d0819020f160f090f020c0714030c010f08070804030207050d0c 58
    0x4003210b03610f014896241c18001010480640b41d030b203081800000102c0c43c0250703d440c1c00140c1c04000c010070001800c19291031003411140d03101d41428103045e080d03041160310f0082104644000014040c0c030951407540d4605e180740c00483c44241c41c08480d00700815075100c2100c0144050003020f142459081c01c504040c8541c009450070740090340c0410080e070380940e41d005000b2034540303101249200080307044440076200c1c26a14010030761001c0050803510308030740d019003042507400e020342c4038a1a0312990000490312a514081418a40c1a403e410641c0b5424521204250940141c032007a0810b0300b552105248401081401001644105404502c000080c495020100e510a10b224051440d109486541910070b02c51017510740d5407142c0b0030004d0100d0740c04a0b14070b26180815030b600c5588585c528880c1040c2e0070f4800340130f03214080760322140b54012070352002d0f00307403103030701c403a000c0341d83e2994100d40e003000007001241140106617000a06440f0300c8040f2070030a1084c0d241d00300c113a0070120340f0722 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 790919838 1250 790918588 790918607
    0x140106030b0c09030d080603330606040f03080901181e171902060408060c22062f060c092409060d0b0a0b03090118020f041a03120703 59
    0x40c001d808002d83d50082d900062980401c40450070401e950380d980a00103402c00121024000c8407000007600504500d100110641c80031002c000324501544680051042c180924094000e9241003854180041a071001c050a040b001c14500804a1280300390507224081240e400044483c0030450b0520a034010165110094031303000c035031b141171000d5000f4455615500c05500287c11115440d2003000e640310b51049401030500d1000704c0d611401c1c02118500180d10468540c15804016a8410501010110540211007559580c808204c81e0304103450001c0c2c11450405840c4c984018108500c1c1070180f0505101783c404010680e2140150400c1c085d92000b6000d900e030522410362450440300c0081c200703031140b03028180c90544c2c40b14a00200080101180b0310700303581c0015201400910f140110000b90700c00d8080308000e01501d050b450301d013500800c40c42030095021071400101c2601c7e003404c4d44007001840112110b544144007041c042401c04003407081c0c1000020002958006240d000044203 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 790921088 1250 790919838 790919851
    0x11010809161e170708075103060612020915031807150e120601050103020c03090405040b060a050d0c0b0310080d030c080a02120a02090d140106030b 65
    0x10005480815680c4481c80e4240c0100260803003103900100d81240b801400601400d40700c0603855280803106022651440a07114400340340c0305a1802080c40080340905000c403412461642402a01e4401040000e1700007803d409030780c003140980060401d0100d49004025503039038800103241800c00c803008000351600348105459500420042070140c690000315140308011065080e01c03611500032400b42001c00b5003e0304520f2213400760101c0e0b00242500c6200f0015115103a51080304041c0080c000c1071600041c0c0e111480c0c2115004102550090b0000d0046007000401d403403404005100207401c0795810f907016034281a50700204030250401c04c1200c400b0f40700c11945030042c00001d550303840e9616024010400301c00404008521010382c0f441010000e044980c00380c854401101000400401a200ca0040011b00c3c00c800316042040a1084401d010700c2c4074851601980d601308404041d521141c0b04e1a0040030a00c5003034003060b421003102c00c102121500110b0007504d0f44c28001841c56016080 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 790922338 1250 790921088 790921093
    0x30f081320040c05070c0b0313020603010603410a1d06011706091b010306030f080706060b0301052103070b010608011503050f0403030504020411030925080309010c0c1211010809 78
    0x101710101d5680b00302d85003150400a002592907031052206086a070900c4002034101401000220b8040e426401c10302440545841d00d1061915442d40d0380301c00f0704240d0003803600c0040c5018400703400598000c1c040d07002c1c0e142c5401040501e428200c01c000703281c0076440b080058201d840184515209a40c0a5204580c40390080400e8140182c0b900e49800030881d441c0444040000c1800e5582d0298001c04015500300780035550307000b500e042c800450b0b0b1103103908844e80d0b850140042240840364040c0c074107868003e410700c1161040542d50078000200c0079512002d500c0240000d41c005154159498060440d03552000030383d5140079034600c080a19051210141800e050410040d01c00211700d140e4000d4040c03a000c18151658008540200520060300300001c80000802200302d40c0041c21520407440580b00ca2030302509a0704215220f0070794001d22074550001c200324042584150140c1100601860884c00700640e2260780d20608032040c40219a13241c28400c010743c4960b00040400c2d40080440f02 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 790923588 1250 790922338 790922347
    0xe06011203080708130b011212020715050c070b0406020c10020d080a0b04150305011b170f04140f01090b0f0f040b0a06030204020d060905070903030f081320040c05 72
    0x100500840da009007281c3c01c00004000081c0076501c800888400f0030740081402d255541c668402803100e0300e1000d82542c4021a0083d00c03c90a440001e14a00b101c212440714640041105030466495210000d010903a1051003000b1481c2502c15005200900e16a00200300002c440d000340031021096288072020b54018022080900da00241c100350b01c4051300c3c00000e41185070740001001444802c95100a103c0e4000d800300c00c0020546c000e03404041041c1410b10f080d850b08604490342c0c04c81d0741c0c07104100052400480c5100d90034203000ba8019104010f540a10600c800d880c80c6000322200304100c81d40e454561301824840010b61407500320140710706541d01d5150140f26010a000c01500050104110700c0010708015000c2d031103100510341c010400c4d50b489502c50300d1880a42940c1c055076001c035181001040701c0c6030040c0038a0f000c0340c1c0d06803160003c04003113080540380d100000380440e034070a034000004030000e0031101d0220f00301d08004411003180340d03506045c0310485007602146030a2040420 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 790924838 1250 790923588 790923593
    0xc18010609051f030c0c0605040f0b0c130e04050a0218270d120b0d060e06060d0201170703110703030f05090607022112010e091c05030f1017010e060112 67
    0xf070140009201c14140403030001a052400c4030b215014040c081c0c5003900d007200340301c108100421100340d014043e506d0301c0d0040e200c0f001d0410701481040403249000115040c104029001c40f6901079002d4061815a0031502d810f40114100d90107550020b004130345994100000301c0a007800d46503000360350000c65010358807103035000e80da984144801042480b0324040f094a0081c00c2d41c110000d03070000075040004800316490072401400148617a030602e4000d40f80001d2080c02d100410b08603c6030142c0d20040e07a03201902d00b00b050500c0240200341056180c400d0200110304200082100e0f45c03080d03800080f6a0b240c80d070304070100c1c0c0001e00501c065410540902c03240c00d42c0014000d01c0a1000e283c003c0710459214000708003842220094003201101c03000000d01150301140542c0308070911819140d0000d030303900c945144030000112610100303e0a01c0458490302c84044010707400750b00041e5044519480e071858428416000b0300305070300b60307440c1c9128040c01001400030038010035642004400e40400b81c2d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 790926088 1250 790924838 790924879
    0xc09060c0828020f010b0f010207210b0403050304060c020c0307060f110f07051003051312260109060501080f0a1509140103030f05090f120c1801060905 67
    0x401818018011901c41e107001024000c0d100401441d001034101c1d0140d4800181d00c42c95100c000e135246501e403050100c100e00780860620760041059014140050a19000403c0c1032019480c10072001218159000025031120b03e29000da40a03803640b13a100e04e801c3c41c01505aa14885d004011900035003032089050f2000902d0600740c0e41c1c24140001400b6621200f02c0b0060344c0102c07465154400d240d000c060f1072101007154401d54070291451030580c2c440240507010f50320251200c0c1004450101070750b001c04c10b58500d9014030b81c49850058800a0140b0410400d01d4034142d654960075414401005240403d201d03080c010704080c280368500e40b0380742000160b801c100500b5981042e4a458020701d060320000344803030203880880800c0081a0300d5410108008109000840100d07041540d00d0001c01c3c0107c0a89802520040a00c0d00344000340c024843d400448196080c9148103604986103a0303624040245900390f103814030a90759614000c2d000f4444101c0e07610141c0204150b1210300130000b42c5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 790927338 1250 790926088 790926107
    0x903060f02070c030c0503070b0a021b180a1a040b0303071511070c060e010c0203030919091a0916022e0903050d05010501030c02030a081504060b0c010c0906 69
    0x119400040c140e09188051010748640c1c08010401c2c0809035001c82004800c82c101000e881041d4100c904c0580c40714200007d5110b90600300015a201004060081d0141d416074109040c0141007002c1a4a1441c021164480140c41c03a0760350a0302c07000d00341c2c0240304224120394240710850b0103100e41030540b00403d0712482040030144c0003007081491a1381021352500014003804d4801019682c0c1e206c80d09242c61240914003401001030071644003c4c15a44c0304240301c8250540080c041c603e850050000c01511880403040b4040000766510300003120840e5108640601d070903541c4c0031300481e10f404200130000000038601a045030000c00c0d040f0506500040840400b0311140c1510301c4909807200d40c2c0d600c400340640580f41e007802c00940908040d404805481e00710b0f80e000c42842542d803907070010f406542d0900c14200059105015100d669480303207030070035040448075800c2080004e90b140801c098540c0303a0030488120314001400721542000f4890301520310f0791460070a0b0005d050541c0200710700b01 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 790928588 1250 790927338 790927343
    0x110414131103121605150f0f01080a0b0c0705160602010b040501050913290a1d1c03110c010627020c120901120e010e0d1701051203070b040516050f010903 68
    0x40e40010010401c0400c17051a005251000380c0040346400402142c03110341c01c48403d91012350590000880810000301c2034900c941c07022050350300759641103900c1c0540d002031100391694400c13440400200e01c00d0745c902502400702940041480380180082c007043d101d041c1d101030b010341d9590307007003062174081401901d14182d801189100d00da521403018855810b81049801101010b600c00c1c80040d034415031052051400d1000d01300000180051460703126030381c8000c0c0384c10f41c80c0c0209602c220988264041b49065070030400306410310f02d42280381401c40344650401038807000643d069508142040002c03003030890584000794078003085019640d0310360810045003c404100815030b126545c1c0904500b441048030400104a00c600d811903841c041d000201c10119140120070034070f40c1d018401c80386078002e48494400c40d03e45034648010b03c00320800703080c110034441c002840b84900140c08201c0b181c1c0103a0058000f4007844006040310094000d03154800342c4a00d440e40703132070415660400d203400200da4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 790929838 1250 790928588 790928617
    0xb0303192f100b0607050102030c13350111040e040303061509090b0a090509060403030c0c0506161103180a060c02090a0c030b030a06021806030702060411041413110312 74
    0x20f6075011030703554014600000c0c0130394004000c1000f14101d402c084d00c0208824944c04110545d00c1c000403010010411541b070b00140c2900c0192000201101c950040124800001480702c44494144a0540141d00f14000d081c45902c280300506034540681005859681e000b0048010040e4014181c2c1c0c0143c4140c01485458888144c8a0342d01c0800c540b0041180ca07105210030b10300109015141c03182103904170023107407502d4500c02c1040c3c400c40c1050b80a5a01038024030545e29050f0411440d582a5089001000f508241d800120081403000d01200c2c1402010201c0c0700340640c0401907105079940104040060b24000c01c0301580d540407045404c00301150001414aa1600085001c0c001130034185425201d481c2500042201590041c410004201c45882c501040c2c0410028184030545030310300181d10100100d008030f030300c5d030a13040c19101c001440051f012520fa8036480002000300d65061003185031001c65000d0001e46100c082e0f507040c0c103c01504c080140f0749211842401120301094828 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 790931088 1250 790929838 790929851
    0x1b0501201e01020d060e07050d02070804080d0908062208030702210904051b121906030311061006050a050f04080102070b180a030c060b0303192f10 65
    0x250014445080a00004100800c200800a41c498040e6005483c002842d510700700c40000e521100303d134802d010b42c88581e260341c0f5141c080082c0c800039400c0035109035564070f0100400504541d04000401c2664403549a910701986412032030746c1441001050040c3c030f495000c0341e1000020006c14400c0f01c10740e005002c10386988070010b0403468094809690301084220010180d011841d0310301901090000b1903040c0615a40c00c48a0030f0081c5245140c203102c203c0601c0701b103004a80c107050b206da005030f000c80741451003030000e1000703019109541d10580110780841d0ba4003a40220500a069115152041502c0590702d0104010154498880400c00308800403c02a44e4036206004843c028455a80255152007007420306500c981e0056954088d20411421540c1c0a014042440c1540d03682548415039100e10030703103601c0301070000000c0c80d40c2c0c10300041001c04d12031440e804150300c00e00880c3c2d4036140303888440142c0c0129010f00c402c4800c42500303010000d90a0080000b4600902000d942020400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 790932338 1250 790931088 790931147
    0x901030c17061902480307050307171c050a050f060a0608060d0204020309100e07060512100e13020108060102010b0a14030307050601150905011125080d05071b0501 72
    0x305100105c040320043c401005c071082070100c20826a0144e13054121001004446580d580c1e1007002c0740180702e60414001c80d000b15503807616100b1550a0a40c401d0301d404143c42d0f540d4600b44010280c070602ca85c0e10780500800d106544903140d03105800c0030003511181007500c0010360b0241c0034031031003007000000350010300c0c9510f0f10041301204640c0608103640300d0500522082d20342545032061029a4509031810007400c03000034001044070010303140d40d8170306405240e40041240d0004e041121145410500090400f40620002d100300b07010480c40345448036510004160880191000f4110b80c18401c00344510355804555808494040702c1088600c4400c0001c43d09500944401503d1800f40d4000041c003c410f25120010210441d41c8100310b60342c071200107491081c80450704601c1944800c40d4200d100a54600240640c0d600c00003500c0469900c929030781c6004803490344640002e10200d0b40e803040140352200400f0360500d000d46580c4080c1003200080a45980001c42d006070314002c44080c52 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 790933588 1250 790932338 790932367
    0x90409020a05060a030e010b0108070507082a010b01022109060d140115110601030b1f03060608031e18010c0f05010c0e03061b0f0a0203090901030c17061902 69
    0x9010143c406902c80f540500c003d4000c2402031041062075003080101d907001e600c038151092080544da103600307081c8034050300e8280301038002c50a115560200c800700e42060500718150364036858802e0300041a400300b14000241014071034010864008003083d20301c1c0c48000201c0035100c0c40003040d1051500c90030011072141c050710350711140c1c2d400d0114a400100300c42040c2e09100b1080022910b415403403048445030741e86d03a00c1d000d1001403d2003042d04046402012038030382003ca120f4070300c0180e00d240ca840740c503124115141a80020001c0d03000040751260705680180030041c030600003010608102d20320500703410480c004103c40d8100300c0201c1c010420001403000449085801030003c10803030f0110a0007410081c022221a0301c24131508000503c0754410000c0000e9011900070710a042c4030448902407102d80026155000303602080c89007039071039140c0f00c0509000f180a150001906407411a11007004802c003180b811150300080100221041d00d6a80100c12140150b401643c1d480409620300 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 790934838 1250 790933588 790933609
    0x160e03030f0f12090109050d170103020909100606050903160b16171303060e0d0e06030c0d0e01051e07050715090807060504030e222c010e0d09030809040902 69
    0x1440f041c1c100144070003002c05521404003280300310201c84004031121415151403180c680d24550700d403580300c018001400c0c0501c4540d0840b05003003c940c017007810301c0c0380c0100b5101d40303400060019801150032000d0303180400084114400044403c4401400c00c1580c03000792148803d010040f00020100b0010408444008005402d184418540711030307201c00003407084c002611040d1082d50400d40791347e41c01880420500c0c84031000fa00c8500ba5034118901740026500000d001e405400c2d002e00c0030403111200b40c02030807110f02d02c0c00000205450031050074500c2005803070070324a0880000c0100440240c00c4422a860300b60410489031140d0044d00c58000502807114006040c9000414050f0402005070881c41c00303903200e134480503040001007040c419200042108400c05035500810440c07190600d52060700c0e01ea803502c214800c814140840d2500700c901c100c2401e0701c0c40e907540300030303611400c020b0104a4000585182c4034280310300c3c549549402d4024126400d10036a641c580200865079103803900c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 790936088 1250 790934838 790934857
    0x1b0702150d0c050301081903030e0304080f0f070e010e04060f0f02030604050f10050409080d09120914060301031e05102003040506180a0b0f160e03030f0f 68
    0x160102180200000210340000110007586802c000912a0142c02501968107a0301c0140003404400381c2805c4500d035290000780f00303409045d696001c0c06031802c424402040a000072800800d80d803003040c00500e26050341d40f0100143d80d000f2100c240803036496022a2030450303817a0880ce1980d40c83d642003035001010604840d11490385031450360b0050012540203180304000c2281e0421683c2ea59081c0c40b00000800c5588071161202c00c0001d05c030030702d8141d00c03041c0c08900940d081414200d208070320200321044443c080e143c01405581c24008181c0c05540000600140b1510f0342e8642c4182011402502060200400c0684500401e85e56040e0004c20340480c0794100342180d01e2044001811001007020484021180d810703001582c0d000d00c0c45a0481c1d014991000003440560303500d0f9025800413403090240403c90080d1408840030560480302c0398080c251405540905061034a2401c070030700e481010101c248080000349501c1035030080305851881c1c21505400d95641ca03c4582c10f4094881c01051 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 790937338 1250 790936088 790936099
    0xb0d290f060306070906020d0318140303090d03090203210d1401090c050c12071502041d060909120a0e0616141b0613090911010806010c05061b0702 65
    0x308240200c0d0351040500954054090b02c04039100d100088500d6012405000050303841100b0610300b091095000324440c00d0700b120052130050b640d94130207000d003a08d040000c22540c0003000f0700c00428824050b101100b402810b003008100d40d140d0110344c613604c50940b101d4a1244a0203103411000fa10b5041b14961700c140c0b02c081011425915060110880c203009044d5090301c0c1c0704204250700c0c0110100c8086c045440001c09070030303040417000c005035404070504444c100100c0150076503410342c0c2d0004c0c00181c40303401d0a48801200342100d031150381800610391845408040d05004802e0000320b942d618801c108004241ea5038074075041500e030300314242c0311981c102c2400114032103884002044921074600c1066003503210829050344990350300d10444140f05041411061180030702c2c091006000380c03c00d41c2e14691155661340c0c000421a190240b09641d0110440d0700c0007595a400b5603420b030301030002d0070b041e001d038170a540b203090780c51740700038041c26195140600c22402076105205455a15074001c05 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 790938588 1250 790937338 790937341
    0x160605071e08040b0a0e1902010e061201050f0a0e04110102210d0f0b0a141f21020406050f180a150206130f06050a0b0a0b1c0b0d29 58
    0x1c005100220885080d2401c80d207400101e54801000d0041030440d80120b001454070840c2c4682082d85912148412070510114041c0c140541e282d0301c01402c0a55603204810704c140d03142205101c0c404c20140d50580c46511015070a02060840f510182c1d08076801c26646a159140340300107038a4484c120b001640c0d2500d0b905605080d120a000c010005043c100c801400303d13194540d840303001d440c480b1000c00c2e8803504021062210001e51120f903402e040340101040c0000e2008000c01d03040317031f5002121030000b4910112200401005d034110805070481c01074210f26143c40c15100400c0c40c043c0049407501114001030340c58541036003201640310b10400400301e00025513503108406154a00310030803000b600034100000c000d0015555112685134000034500d0a03020a55150401000024040c4442079600c0d520404562503201da084050603401850554039000c0108007006c0d5800c0041031840e840c20134114421907180c017840e00b4401d40e8800c1208915102c04101901c0c0781c1c1030707624403580440f070060 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 790939838 1250 790938588 790938647
    0x3030e12090319050d0503070306180506040b01080115050f0405060316090f050607142a0118050630090d11031615020c07090507021216060507 63
    0x200516401004804550303080c69405180e03c15840c1d501d0700a01140c000701404107409000d94000e42d40204585400074009032619501c203031703031220048e204202d555600c04001690516201e140c1c41e900c000d08017204190b240490541102c084030300001c04220012a8006a010740c02e8251406480c0c000c114a4072480c20003032242c19501038444044c0040d44025002503c030b413907491410203881c005410140b034455961074a0340295508500c0513201c1c8250503a80000f00390007103032060407003d00e00d00042400c20380400142148401219a9030034a0560700c104159a1401c04644000758500354100320b90203038401040000070382001e0080802e04a13020444034440120b00f036003091105489490340240c9458455569004064044900045091300e10b00482d00a01e481d450160003400c1c003502d40b01c035001c4014109546680320f0003045464005011003160140181d050003403610f05806c4c18031340b100d0905018802c40800c06030416a42d50f021881180c49820302c01c07082964030943d038245040c0703075 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 790941088 1250 790939838 790939873
    0xf02010e222316030b180a02090a17070f06030c020606150408030d06031a010b18030f0a08040815070f05071a011202031c05070b060d14032812020703030e 68
    0x40e4081800130f403501c1840452450110243d44080300d4200165041d550b900c150700000f540f0031000345911040c600300004003181e14000040c061050360000d8210540381c00c03803201107518a500b20500341820600110480f543c0000c03039a5100104490b0742405440543c65402c00703100325007015655010000d04440050b10b80d40000f004c42c1d10421288604d01040e80301e8a1104034203004144caa40010850320701c001e41600751801c5c0e0307904014150382c03020703a03030313650356450880254004c80b04020007140070010104c0a01031000680c140e01e0480d8020725000c2d0004002200c1ca6a030031087c04402324460092200c81c1c1900201001030410079049561251142000007803000c0d41240b10303201e03020100c01148443c09480440d10701301e840d40c0d0306104032030341c4d240001c2030001c0442c0e4111000a42c26004100c0d614003447c105459440a56501d80387e8003c0c8100725940300d0019601d480b401311485103c5c5170322070304000400c61003140041e04d0700000d00d03080303001d008490310b81e0001c5d00c45d81d0195503034440fa1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 790942338 1250 790941088 790941121
    0xf0c0c030d0f261f0506030f06010804110319051b010e1909050a06050f030706090510020a02060712020f0a0c0b0f220f0501091d041e0f02010e2223 65
    0x4d810044d90881c0c5d21020010b1521003180d452116206101c04100300c0d50082100da90020f1160760003124032085030010a140c0114101a074044100185102003440070034006034056040300c00783d503442c05161038000780001d1005044940904101700d000030581000581c0000a0000d00364144158242010740f000504030780c2c046e052040710f03194034600b007900d070015003001160100e4071600c80292400d41001010360b02c01c08200258001c0301341081c010394801c00148803036841060038020a5003070741002031510100100080d40b5500c6413900c0408620103059800031941e4410a1541d54040080c03420054090f81c061414807000c004c400380c12512a1034a00c10960359004120b12840d980c030383c011a42240240b00360f0610804803901e584001c03c940308030980c8140512190744a0010082c11403103d10180341040d1880d1907420580c100b15a40030b400303021466000c80d83c00100002010f501c18012041002400150360b8880d02d0314580c54180314030442e44030f080041018245040c20801911006 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 790943588 1250 790942338 790942381
    0x1305070b03250801090e0102130b180111030d0f0915331a0f0f030f010b180108070e0d0305090a06050f1602040f020f0c0c030d0f26 58
    0x954600403541c84034082c4440741d02140e03594a0040340d0b46040d00280061620424140313641d5001c00000c01c521034003d48210041c80551025691070345541081400c6075800d92405040065000443c4400c007400800d44001e02948076000400e0088182110001c0c0640e07540140340c010b181c0303c481156130080d40705010840000c0305031000900950500c07911a401d5210fa0810421450418000200700e10184203014500360716a5203082c1d400010f81e1003e4000c0b240c5015814400070812140e102c0740400f00d4010901559a1400c0c000200840c00e0102c13400d0350120304100d90203000034583c502c00c22801c01c50304070240c114901d684160030000c0c442c1c0d119101c03450040c40340d0301001505520071070440354000072221b0b405080a00c0200c6001400f00c4408060380e04c84d44848034060a00b03060302c000d03e40c00b041030250760b0b074555440b07034014141284030f040300b4401d03082040c40e44000782e009451209070840c03518214140b8a01c2101d81d003442c0c002010b040b100c040355102002248030340091520101070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 790944838 1250 790943588 790943611
    0xc07170306120705010207030311070f2402030a05070605070c1203020a0809061312030e031602090f0603060c070f050a111207060906120b1815031605091305070b03 72
    0x41d41482c1181e980f019403090600681c4804000c1010030304c41e405181c030250010701602d078002d50340d420901064006801c20310010403c1d00300011002c1c0001c1000120b80b1590014601342174024001501c2c5002e44800034003100c0d207407000100704500c41c61940050980c004a8141940c9a1030070003002504040e000101003000d51011459100b00010300c41d2194078001102442c0d20b410795a80f043e08e040b401101001d06d81c4600f4800d01c0510180084c01d5450880b41ca000c0300300c2d04500421410b40c2c40036040d010408174041c14000c00f40c0b40801ea0b55849072140020a50300d540b1803620040d011a06000503080e8020b0000040801c40d81c0c5408030110301d0202c503203024003400001916195800d903c14880400c11490040022900a602cbc01c680411808000280704c0a03550216820a40910401404008860400c518000c100c9510218030300164003c0a5440c00020750a00303502d15802901e103c0c0e20000c002a03488604103040d008100e0b4050282d804055442d8002c43d080d81083d52020b201d413 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 790946088 1250 790944838 790944859
    0x212010611100509120c070b0316200d050f042402010b1c030806012705211b040b0d0c06080c21040302010f1119020601060503010e0c07170306 63
    0x800140c056180a6044040074289403072620900c01d40340c1d406071080e4006c03401200300001c2d251154201552150861140c2c041104044c00801401c0311710018280b01e2040e1210070100c1c000320b00140400d50504d040c101036688801e05a21101036006070781c44001c40b85058030340c4008c80910b0f140c98180e441001e40003803021003007040400c000c41003c101c1c01c06554080b0301040001c60311036103420b9006141030421503105200c10000d02a0031660040400c400415000304104da0b041c4000c4000b40c20320620301c06010700c071407044220340743c0e034a6088034026011703c0042c0c0c0a055689510450080344000c100008100b0285003032003064100703100781c00c040345c4400002140300744501d045503907000c581c44071480c0303940550b10720b80c5c1000300c040d00503800c40d91303100900c4402442500c6a1211403160505040d1205500a0041c58240070003070b03013004640103400100041d030b8000b8241d0b0305660446c460002c45607128480d076001400303103140207000250b08500052800d41d41c40e000394022f02064032680c020 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 790947338 1250 790946088 790946113
    0x30f0105040b0a0f06030618050706020705010f030f0f020a17010905310b130b09070e16020c091303030b0a0506090d0201030906090309061713030e01030212010611 72
    0x200c80080310050712407071030b480010700700b40c045510904c0b4031882d50000182c19512612071030110790340070410070000310300d00d940350b41448002c1282000800041c4010301500d400c09000034a1914913400004c245512160710010078000c60300501da84801c0300d401192200c5403141c0c01401600858818140010003000214848007103014052182000748000d6910090046500d26105200800100b2540c121103036040025402d10007140108425401000c49c900f1030704180b130300c1d00f80c081e0020300709a012001c1080848101890250f01c030080c01c0b618107142400383d2040c0d0408003100846035020088008100038070040c4600680c40034029901000b6050b50740b001d024009010340680c980c880c2052105918a02d032490a00b4180c620614000c500d0003840c0d61044140c030300c0e014084000c50f151540c28010558411104a030b14101e101820150f03040503d85541c01c0c8074458005030422003841014034003640a901201d048095404031180300c3c0d80c0da060b00812155024481d40d4407405004c1d00c9694 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 790948588 1250 790947338 790947341
    0x310050f0108160b0307180801020a020c030c0f01230a02060708060607030806041e0203090c6702040c03061805060a05030f010525050a18050307090209030f01 70
    0x4008503104459514075040c070044c0d84050300024440401c100071a041000740c45000d0040c18001d04280b800580ca0340c80a12029040c003440d001c501b0700030b5100c8824011603640d00420010140c5081c03d00072101c1030150419010a24104c170b4040704040c000480c4a460755002035079520a107500c0e40e500e9070381d45482081141c2ca1003030407800340020b004080816040d00d801d60040c2c40080c1c00741c9078800c50541075410039040e40c1003141c5280d810382001c2007151450914548008040002c0350841000b24040c00080b0321804035500e0641c041c10003042c2061800f030f10f485042c00728490740d6a050034000000b070510010800300d41803c9000d1801c3c440b460b4030007402070044600359428040c1c110354001080703250200400c0c000340340940c000914280081d5a4030700784007400440f42880000314803441e0815002d4044d90f0a9825614548800d030500c0c48034a5001d0162410310000e40307484c1242019000407003005800d40c0d00032aa04d800340c4800041c100c00c280c0c0c02010172002c140e0039981d0648034005005d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 790949838 1250 790948588 790948603
    0x62212030f030c140318030405030a061b08090a0303020c0114090c130213050f0f0402070c0e01050f010504120516080703052406060f0d023004021005090f0310050f0108 74
    0x100704d40c184003151040490b01560100c0307041c01da04407414281d4510000f4500008220241d44841d6102400b01c0401240114091081e2080c02d1080c00b60904480c950b030396503900710002c1c04143d40820400e010910a40103030b5440844c000110031941023110005444212202295100340e80340030104001031114000c3e5a13030b01114039040c101d103504d00014044010088022035502c1000807880c3c141656862002d0f002c0385000d000d48802042c2449440000301006030007445c403900c0d5003200100e081c0e80c8401104c041d1201c0059124502401d85029441c01c40204038002c1751000081001c600d450001800c00200e078000c104580d80c5205040340640316004006d0860420001900018424100a03004003101c82e5114a1a880c1c0058035910000302e80081140b4901944103105600f1003920190707800088203812095400281055800290401c40e06a4250248000420b0805081ea01c1022000c080c0c200501618101c010000e859401440d00b180c2c0070015007280e40001c07806450004804 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 790951088 1250 790949838 790949867
    0x201090507061d0301020c16060905060301050402180909061e0402091f0306050f1e09100e0304090207320601030f140d09081209062212030f030c 64
    0x51a101e030412104945502c3d4102190052445040000307441c0e40b001d01c010310310708071001e01412900140e6510040c80101985c00f01040001c2c3c00700521103aa105001c40341111002c88005980c0d00d14105881200c3c0f803a5004c0c107900c100042c1c2040280300e030101c0c3e5240f282075600c08200c194680101d1041080100342c8010750408200c40020b5494655083c01b001041c0c0200348000880d603690780c440064030801c0b1504604e03a002c2c41c0c24400d56a004400c01030007020b111000c1c50322854401c0c40745544650329400c18450075154485854228020b00461300035111680302596610344609001b90400d40d25001c1048450860f485883c480441007a4200a007860f031014000592940d120600380c800d00140c141e591120386902d841000c00c0c1006015404e000d50b8440320680f6150850382c0341010110800e0703002c800010010340f0001e44d200b20858820800c080500c0c0303101140c004607214610302c3e90b00400d020386d08030950403041c580c0082e02544100c881d42d509000d49035441800700d40e03541c40e00119 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 790952338 1250 790951088 790951093
    0x902040f050d030e030a11030705180a0c0e0a33090e10120f020a06020d050f0c010603062a020c01080f070e2d06030930042402010905 59
    0x10710035803601c060110003841c042d18140482d000100e0010341044c1d801441200c10001d88203003075001e810b0610194004060489600450610019034081c0c1080000c08841c64987d49500b2652503a00500150341555009440213000340d854100a07c119000080c8108103115050802c0c0c0e1070001c1c00702040001c085550b02d030501d982c5015103000c00e006000d80b40c61300c0c2460000d40802c0e0004404c460504090007040d000118025900510a208100340c11810454110f61034102100f90030404440060702083d410a81d1954081c100e213004100c7d54200070a500c0c246482d280d0210000703020803490030400240d9001c40c548e008010f0380e80301d842104c140e005c14103400018554808000106501a000d4180013a1100c04040010204860b01c03080d0002521440d4001d50300f40700f142203412000b141a00d20b90b1441c04c095040580d10616401034a58610300186816100b036200c01140754141000840d06444030b48131600c110300d030601c4020b40864880c0c80d074813845100d80705016030510326810001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 790953588 1250 790952338 790952369
    0x1b090204090c090515091903060c05071a06090c070609150b031501080a0f05010e060106020f0c03010e190c0b0f0901030e03030403120506042403111f030203150301150906090204 78
    0x90000b82c00d034807244400d903c1d08502d00000827078200c0c00340410340300d819503441e41e40c0e00c2c05143c0081c45e9903240443d5144004000c0401000391170704c2c036619030021580120342c0c0c1c4440d513a28040c2c000d448074590052045001c0b6104c0403500310150400048018201d00b903810007501c182d881074200781e003446407004541c0726003010800306020203020f80055000f180040340c52640222038a240400a90005005034090321101c7c2003403c05000e01901e54400301d00911180c00d80c0c118075a0307518107200444840c0315140c031240042129031120000144803014845890345000f01901d12190000d100c0f041c0030078180b022484c0782c2d08010044034451356142c1c403030001403a101d400200080000401c641e400954500c255080c4401142620355681c101da80740c0c00d03c80e410b625022081d407491b2099240281c0200102c0c3c50f112503044107451154905140060b00e940e20100880707503581c81003070340d079802d94a0b1005503490184042d448006407901c800c014021035036100c00020480c4120b1080251084061a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 790954838 1250 790953588 790953607
    0x5101701120314071a09072d05030f03090405011a030424020f040302040e120313031e0c0c061b031b0212070314191b090204090c090515 60
    0x26041c078098020701c0c0c1118289140e100316209540306050949000240c2002080307440740d81c03039a156110304140044c01c0300324a0401d03045c1d0100b40d0703d20f041d070381c0040b48028144080b41c240031040c02408014121004007170718a901c191640e1010811a0185003010000714809559100c0c1030b40d008040b205ca1441c0d40d4035603e03480860203949441c800e001c9003403d2481c0074404d0310b00103004001000121940d48070301e0b51042100300c440380081209150000c0e440e00e8181084581500d4bc8074180400082d11150903103030444442c003280c5060310b8000c086000442c80a5406905100c109105a0040029030b490380c0040c2c91100f41c1589210104089005440020b84115420003a503000c20304140c04502c1c180e4000351450300001c040100c1e9922042081040c07005600c14920840300340702c090b01d41c0c1c010311600f000c1d8907002c001c0090420704d1040180080500110450801030091a02c00c549171131700c1e135030031002414031002081e0001d05008404102d629006400312410410300380070318541411300 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 790956088 1250 790954838 790954859
    0x60b09040c03030509240a1803020a05120a02150304020909011a04020c0313060f020d03050708010e22051b03030903060a1107050a0303061508062d0301090c05101701 73
    0xc175901608049024903500340d0300b0103110070b03600d0082103090060f102e4a540f04010300c144040034a44803000100001000981c98a4480c07000399501690501c0500c00e02e050707845e190403c0707000000c0d08003684401108000412401440c01030b031007110341c200d00f40c031102a20b074240d0741c80361685116500700040c00055031034a9401441030321503080035281000249500381e03010408650240c00810524041c40c5102a07051200d800100c1090808000600700414000d00040c4140036201c8411305010110350789410800c4106291840c1800821095100b490256140c041302e50484a100c19040e00308211803501000362802d90002a00604a556a6001450181c1206a00015007480c00c21000c000b148090294104a500030745002c640c0620f04142c003509a01c0c0d540c4803a08010008052160f2940c03480d0f9041204a0b80e14940c0c1d801c01281c2c0404880d01c410300c80010741c95880d2214001c104961219078408542c012111508580740201080e0f80780310740248981c0800324181c0040c450784090 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 790957338 1250 790956088 790956097
    0x51e16170d111e10060b0c0a0f0218041a0108030f030a050a060f1d0109050702103b0d0201090201090909031704060506090115090315020c19060b09040c030305 70
    0x21011686070f04400c01100891541840900a50b40c0050b00c81c039440e04030600442005021641c0140e1600c9104108191a10b00c3d00d04000e10007400045811709540e1210f06001440380c90492900c80b6040c1361500c000c544984080c42c00504014200024228002009031540b41c0001250390f480d503a03460300000018500108401070a0707940c0d090104401d040a0b040d000034081c030588040062021100400d0004416445a40403078288410000200d60201d40001c010401080c04078981d04c6500f68085503040310a0040000c0049254001174225645881036040b130208041d141c05c3c03000020201d00381d5040d958042c0c08030302c541404001000b0181d0281c00920300a2406011410f60f9010003000c1e01001e0b40c044e608136840d0024450240340001c0300c5401020503080070201d4407800c100c003410b51065440044d0184500301d0324080d0303200d0340350111558035080000b03607666103d40e640442000e400c80c0c803056620502c3d140c8200d0b624103248070618062504038020640340c80c03865070200e40d56400b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 790958588 1250 790957338 790957367
    0x80703030e060c0f10060e04030f030c0915050409060b0307053a0209040b010e03071806050315041b05030613080d141803041a07051e16170d 62
    0x803c01c09035688030741c00d00c040401441603001418190781e0410001e01a10803a401c006000c41c0d1200920000135040b000048a110050501144640c80340009580214443c0c0c030211210305000d68094a107139001e0010003e80d00d008104002c010340725422144240001c1b10b602c400300e40d08004e00010315200240b038000c1300c0300c01c00b440d1100341c00005540d4a00c4c80c030054000c1703400d500403405205500d0103000c2c01500c4142880d00c4c070814504240002c0e030300c40c054840c20700170040118a1001c0c200c4a500305d040a014003904480000030019440710440208660584e446144445207850700b10703841200f0740440e140280100040d803610150f01c1919035020004603100101040303401444a540d0007006e0280514240604040c81c1819145044550b0018071380b040340c008100c248119a8a6101c41c41c4007404440b41c0c988600c0280762440c501141c560400ca920012401c845850a02c00200c01d0004900b14003550b1080d40d640072288061054400c03101055000000c80d10300c010b1141c06c07040d00a00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 790959838 1250 790958588 790958599
    0x101a01030b0604120c0e0105100e090601260a0509070f06030f0b040f0903020c030f0601120206040e0405210c06070e04021e0915190807050712030b0109050a080703030e 74
    0x6588000710000c444220f241140e400600d1002044003151b41c5001c03c0c0142801c1c0c034140400184800c0017854528060b002c180300340000004103503c1c5c0d10480c10015290049000b81e47c0c42c4010305400001603070b044070500391850074a13002035140031001c82c0480c21216000b880b01c124908100d82034000d0078200e0319031403500d81d840400440c1c566a601813084c500702e108a00041082e0b960900a080812900c841c6000f0344c4a1080c031410010300180d801c0c1103070026500c2403100b0710075100040311481540d00178010750b0100d1303040c0024414003040250707401419019002e104030203844603080d03c0c05504408a66a0841000501120300404803c450100300802c0185400381e8190440c500c140101042e0449140200c0c4108241c10520364821060740501340c8503003843e2400d582c902801c40070249203000c10400a020601082c000d000f43c0304003650007040600505000ba000070010800c4866050015000600010b0341d400d0a401c2c0300141c070304501c043c0c1a41400c545058688007410901d058004 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 790961088 1250 790959838 790959847
    0x705071502041e0905100308090d170d14060a290d020703080112050d110307050706030b1801150f020f031207090e0613050711060c0c101a01030b06 65
    0x1035014070081010b80700c40e282d0082e045081000e000030654a80c0c1100c81c40b54540b0081c4080014103408840c1225072101da425a50103140004c144141c041040080884d10f00a42003450415641d01804860100c100300b0091204490300025402d042900c003e43c0010803400c06000c1001c9459030b002800040210400789007030103496503810742d8050a440c0d03901c194007098910405512156003401041501141c0c070800c1c206882d19030720b8101d0308003244140060603055004c1028188142c405070358020003690302c80c43d80e0388800390103031040b11403052040b26610011a0840015074505041c0e540c00e410110145012140c20f0341c1801203540844103500c101c182031401690104000c0105c54851000e070042c070704201101030201c000c0e580044009a403001d08101903501e40364a410000340c2c1a64000c501c58450340d00641e084544e10b030701280d07907000d00410001d140501704000c0040c0d000c0076080f20600340d600d00d8110107c5a154038160428070404d62000c01541c480e4000c010380a50041140707180 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 790962338 1250 790961088 790961123
    0x3060d0f030f0e041a01081902030a05060f010305040c05040e0f06091c050403170711030105070c0506090f060c03060619031514030c010c050f0a050a020307090c08070507 75
    0x2503900e6034000c50020380b1088050ba41564449420500d8200c255010310001120b20b03882c840b0020030308a814100903018000070f0f0200c1c02881c03401203a08480c1800c650368108000c070103024150446200c1d004001e85085c106e0554406e01c1000e211356040784e0b1501c41141031408100c00342c0782003030203a00e02c1d1181d0810004c441c032050041e107014100c4103008040143d013040740d01240f440103442d07103030038007000f8001080496807160341c00400c0000c90303428543e508070b586449086003c2d014101901507203001d04114034160000741600c021406071040f43e8207690303122400e56451110380f81c400032a03049203010034070994050002e0350304400c005017210f080c0f040d5401c401940081452042c0c00003520f4182440380a58a1800000901484840102c2189118000caa40c40311261b0409040208507820710040c40014810000e854480070123a44849015080c2540e681726200400c0c0e00c240294a00001c01d00443e1041d0280c604503a11030300441c0c0d441ea0750036074454100400c15034915468038a19041d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 790963588 1250 790962338 790962353
    0x2120c10050114090f0604291e0d080a12140702060f0108071205010f0219140a0519140a020c040b040204030b0106050703022e051b0f092202070b090106050d020603060d 74
    0x900c00c2004441c407005d051888100300360100361065440070381e010441d50529640b2b43e60b0981d0000e0390454099070380d0302d04503e0225520740348481000d0341c079464015441e09002185400718041e0080b0340c2211081e03141c040012480c0c003001e2040c0c0109502156041202080c00f84100c7d4826002f940000b882241e640403080990740900e0b01d620307031501c070650042d42054005042458820a200b0054100812107102038842d100344500d51030f06003a2403070b250315094441c1c12901d075000c0307103900c031140c8a40710311801943ea100c003681d1580c421401e182a4803c682820700c00e49040b02d82100f96440181d2a1030300694a5074171503201503045004400c3e2600c1c1c004040b03903080640300c908900709016110540740301c0f41140ca0150180041c002080d09240e800301c0c5a800b5203403510a007180e003507951112903001601c540c2c10114a8242c408440b50744000c0c0780c00300d501508007607000b42c0030000c803942c50045013800c030f540c54000c517030707006948a00d11009810500c0295a2081c0050700329038401d10503441c0c1c2d09 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 790964838 1250 790963588 790963631
    0x71119061407231303110a08010b0904060b03031c050a0b2d061e1215010801060f03060810050109060602121c09140f070f051302030702120c10050114090f0604 70
    0x4512201c54011b10703c032401c0000c182c0b0b004012207030003004050010000501c0c45031014001038400f54403880003d00c140d03000d0048805c008141444500300620480f0f4240c00b0744000c440c62101145042c1c400142030900c000b816442e200b040005444100b410010b019540e1022a2a01c1c0c00032024014070900c20710382004101015041c4d103086855444150b0311030107900380248580500c0011001d01c00c1c60742d030450030181c15101c4605003418000c4910500320003e107030a80c010009442554032404162441d40c6c0304e981603c00409040c001d41c1e48440080c1e07134440070b0044107400b120f001c1040e0080102055100f0126040074840030440e24800c2c2c444060240e91900c40440c2600089407500402c1c00c200000802010851852403042c2c2ca420000746691400080d00080e0a40000004030294401d02040d0003100410420341d848c0c901180030203076200d0480c541c540c50766141c480045144003d81d5001c04c8007100081444025940b01c840030380127080050030454002d510b8032008000310f0041400d20 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 790966088 1250 790964838 790964843
    0xb0a0b12030309010f110d0b011407060e06090d0807080405070504020409051e010b0d1d07150306061b081305030316020f041a09071119061407231303 66
    0xc54882c14032407642401c44003210324540109151a005603840f86001b000d41e10540f4031100c00207115900b240042c0d40c50349c200d008242001900042e08010024581c0c0300a8419101104584881e603810b03068598803642a05020040b5994a00003030300305102c0c0f007215603c11b00c01e20990304104d58034004a4280d8200d0f4200010940d100c400304402c900e00408081858a462080c1001c59454203629074100d1003602101c03c0300540700e017003041c641a940105611080b10810407151802d40d20b400075410a2034600d03444000a0030160700199292140d1f036144140d070340031540083c00007002d603103c2c00340f035010090031b141c900c0350030200140d1690244003808011140001c4480c40e0345107441008029090420721900c20361810b040100380b02c900c500514524001581c0855013915a03040955003600400c20001042c41200c075040c40010b5000407200055100f56004d10614080c0502c030000b000e02100d0050000e0319001c0c0812840ea01e0070f240721703066400701000d1f900d80b005560b18002c620300981c009 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 790967338 1250 790966088 790966093
    0x1203110d090e060d020901060c021903030507050d1e11100c0f0e030a26120411010809210d061a131208091005190c0b160c0b0a0b12 58
    0xc00641d1822150b040d80141c3c03c031000c402100361580000e1105c20107002c4c68040148840041c802c40d220f40702d0590a016050000784c2e00140eaa150040c0b144e4000c501c01c503410301605106418190041604900f1003681010780308809825044c11620300c444465004428800d00c21818000c0049105070480080c40b9501c1c0c032801105e080010f404c00c08059030460096000c01e00403408600c401c25499040300304014001c0d2020301040c40c41c070303250194441030f403c13262000c07082c0400c00054512000b1074045c20303224802195224007020741c50740507043c03400d0201881500d0085042c900c003030041c50082c02d401c400251461b124041c04101041080300b9004045000501d16642c0007145440c030010f0200c030703441e00c00c5e00d04640c2c3e82c2c2c807450149401c0c003806035250141203181140180103458929800b0302d411078000e01802c0004100c0080290291f508440304000b140c1c1c04213550104219041c26030725644105800c694841005407401814100500c2c1e490a040c1803556460248000403c0701400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 790968588 1250 790967338 790967357
    0x5061303331b02150a020c24041a0408070609020109091401050a0e0c0d0903230d0c020303060d03181205030d05070309020f0d0507050a080f06010b030606041203110d 73
    0x805a0250140c02c085001e55000607007685251140404460b4000b40e4084056155503c181607a4130300702c0140300b00c2c11401807004d02140549502007001d44518090b500d20101ca0050007004080d00c0e0054601074584d1400304696004640c5640020080c20300c103142c603610166889025208442c0100340d0910310a2410004102c0c03803030f2a416034406004003074200c41da1400d002c60030045a01c500021340c0d04040c0c0f601404002d150141141c0d00042e800904004c150f000302c0c051202c4c0d154003002100b14034030f140c0004540454800000d491042c00058034a1450b003c0f42d45055030303840b00311a11000c8580726400c3c04681d04088030030300c0c1d0555200341c00441d180c1041c0000081036940080100c0c081610701004400075a551a0780091811810764010540b126241801e6050020700d40100c1d40005114800280c0d400001a0345c90004401e60203440c2603980701c4080711a14402a150103510001c148001c0c0540240c0004001c2400e10905208003048400b65007141082811000f03080402d01620 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 790969838 1250 790968588 790968611
    0x2303270c120102030f010e04050307080f0c1b0f0103111606050601021b0105030402120f0105090f0c01090b03010911040e0c040e0903130e06010c02030102040306020c070506130333 79
    0x24245241e09080d03000075802d5260001c40e0503042d4205124040b1401d01160106051000c240200d0341c1c89034002601c542d031000d0224461080d41c2c001a000b4480d442640b043e41240e150202090140c03007001000e8242079444000110094a007407900120381c81c0040000e01055511465a03844d100c0c411400410946004000a81042401e5a03204806c0c0010441001e150713921038102ca61040d41100d143d04aa0780145000d441c3c200751421500441d071034201400518500011101522800caa003220240c1c4110f800450341c81000b8880d04081580900040c45554a9500000018000b05030400c0c186644c0e502018898030013910380c4e00040000140520469a82000d403681c0412010002c41c6400c40000c404950080c803403243c14035072400c42000c61801e81c4212154110290010025500c881e140e0902400941c0200101105441640310028450900d10140c51079500701c0441c070076056242da180d449810070341071001982c1400c8180034401c80d1071401c0300485216201e0f9400950b038034090 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 790971088 1250 790969838 790969849
    0x4091e0e0303090d080a020c0d0207030c140310230403051201060309050d120b221d0a0311150a020a020f1b0d020609030f1c2303270c 59
    0x20340602050703820820400080400019202045071220b180000d242d94810440f1802402144100a40d600603a101d1880c2d1541c006200c40603603016031416040070b9270b0f404400b0626000c1c00c0b84140c068100c000b050121200d0f60b48001444c850f0207010402c0380001d90038a01e020701c421034045022810200e00d130b070740141c68010114050a00c46c03c040050100030b4036060394490f403403500e16080117145040e810600405402503001d001c8040c2c203420024000151240e03500c940e01900c40f04861400c0040604225010b80361012601c02002070b0540c0b000d6910111580340f1519642c1c3c103103200707144140400311300d0201c2181c031800010b0340058441111404c007d043c007c0d0304aa442150f0f0001070300a1060a01640046110808962460f848a02c1c3e201143d91030103aa03e115502d401440c031601040d00001c1442c041213800104465001c449055041d1012100786a000c1c0250b50325080209083d03443c2002140c0144000f080c1c2d6030100c8107020908280b0740e00c20042003960300107030026889800c00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 790972338 1250 790971088 790971101
    0x30709120f05030a05180d171b0102190210150620031b01050a05010608190f0207060212011a0a120912020d03060e04080306010e0d1a01320909010204091e 68
    0x11948003030b03c151151103c44d201444404823142c900740000d0019045642488070700112051030000b07540b180c80e14008054400c0001c600c00c2d025005040c800324421580e0f1007442021120100c3d80310141c0d050103011501c1ca0425400d40c20f08140c23a81103828820700401c060b0407060400440e03e510881c0300d1031250309417400a00202d840d24140380041c400140c016440b640e1000300a0385801840195180040290640041c000700c1c0e10b1000501c2c7c4180559500204852492107500b041246da030303044010340b0740b401d03c1d0b0301a40c00e2906101c7e090000b881801d915650310311024000c50ba403080d0362140d600b2000390003d02c2d0050380c00101e40c5c0445940500846000b041d5280000e031082c545038a0b01e01c2e06101c0101034504012002070890390642d100081c441405400141140400c031411402c2d510b150002c1c00b924410009644030080503201c11500043d014001e4460400000042400e100351f070a8040c00c0603809540900c40442d48651600c1510300c1600b00d5041390320103030b40140011081320388 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 790973588 1250 790972338 790972387
    0x9060c0a0f0606061803110a09050c041a03010608130c03120809120901020c120a0b010f0e06040509251502010203010e0105060705120a140a0f0311030709120f05030a05 74
    0x484140007445c4004e100d8003822030b50010b00f00e9080075509030005015840541001140e10300c0c0c2010300040b40d440001500a9840760078100c1c1e101091002100f140e400240300d0800042c05003000a40d150300000000c8000900c00e4400c0c0c0d2105440e541d4521040f01001c00d983c000807800c000b009107051040282d0034000d00389600440c50302c00460b0000351250242940340d0300800911460383e030007040070800051102c0e0410105485941c483d481812842c13075600c40c1e400b1042d614004580546490320540307000b81d00560040c0b40340c0560b02e0800b900045005c0340700c2d000c0003000383c00082070782d8000c3c042c0e01e401c142075000503625810004903460020041c0c1040340124800c0c444d81002070740000d084090354010071440e60b08c41c550076000b181c60308122000b49048030000301c1c100303001c25002058009441e80546042c4aa07048650582c0028002102e81100050000c0d0003086004504036102403690b004000d01d0000c0c41079a00d541e8510b0380039102d250700160000404042e03000150291010303145 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 790974838 1250 790973588 790973597
    0x170a1a041104051911040b070c0305070503060c18032a01111903050c10060605070b0f1005010c0501110c070e07091d06030a06050406050a110301050a090209060c0a0f060606 76
    0x30304038003030508000000b850015403030f51900500c0c4c07101030005c20b40703008144921401c4e544003181d25003400850114401102c41e4031800e1008526171a0100d545849421030700221400c00065540d400101400140c016403d0300032819050b015600100f003100d03040d00b88541c624038001040000400c002c09000e100001600301240f910b1040300c009800d5100b007074151410790b403a00b4910301d025081a000141c500c610900d807110005446800101030b014042c090011901c0c1036444d51003418007404210341c81ea00c0c0303100d69032003400290300401d50403149500405c00000e85900d442c41d0202d103580042d9142c011607000724010040d54440c01d030020307031025240c540543d9141c68070798041607c218000742d080214900a000403601c0e10200302485078981c100500348070350b09160401c0c000419041c0d070104d640314240003649000b019400101d0b412600b02070080003100317190002d044006e420000d920748c1e1149040090041c40b071010004042c1e1b4602490401d83c20031454600201240d20a074054401d00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 790976088 1250 790974838 790974841
    0x60204051c08161a1e070507030903021e04020c060901060501020a120f050903150708070318060b0d050f1c0306120f052d0c0409020a170a1a04110405 66
    0x14610105542107010030800f546110070051074041c0024202d044020003142d031610801c0301d00440e1448121134103511590103100e40e114180110307401c0c4035550003d0042141070400300010b060290041941c00c00e843d6042c2200d007600c3e400602a644291002245e40d0300c080d0078000790820078440d1400500d424001461104010740c1e8408408540c4051003003448607801820031000c2c059022611100da0080941380220314000e0110841041030310b0b01c800152900c4000b40e4450f0091062540c05211b40390814116a85c40d0760b00c42c003070440c4400700d41d080b407020000d50700050010400c408121305030b00054001d0b00300f0039000a0054900340040820181031960812007003000301c4e4520b6034607800c4070003646540c0e40c03030074007524041e01000e000f4001c60001204000ca1240e40140c484100051002d40352041d2100781080103444000401942c00320b4110000c00a8901880c1c4013400c8519002c140d40b03056650303403180500505009025032031108504204003c0000107503808a440b1000c44040146 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 790977338 1250 790976088 790976093
    0x50324040f05010b100c030807090b07300906030c050f090913020a0f0f08070321110109120e040c27050d0c0e0a0513060f0b0409060204051c 62
    0x101000540094180d0903607040c0441402000e4215113a18140500044011410301e03034000d015101e850f00950001d611403002c55021845001c80c80b0071038442740034150400780141c48442400c9c06800c07090001013080c190307200d42c043c0381c00c5c6030ba1241001a00c448840616110000e41a03501c0c0789246010000704100d84803605824605030f920070301d01624500820b43e00d0786540b00041d81e800c0f101960201320305d2b1000417280000780084040d1142101c2c10200136030f0b44e840442d03652019002c01015095030003a4403548a56a41101001da04940f404910b110310b074207a0b5600b1207901070f0781035580015801d40c103501070740c0002000c0c0344418151010084884d014000501500c4034044000c10101550000881c0280c484200005002f00610034a29180c00e480e24080640807840741d440c0e0f2640b0480001c6010490380700e00e601c0303800e1b03100714160750074540d548a000404014400c00300546d0b03625407801164840c1e10849454910940c0016680c0d81003804000307002c100c41070501030100340200e52800 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 790978588 1250 790977338 790977403
    0x3030712090f1401090b0f063c010504090501030c090c020f07180213180b19030222021201091b0c06050621030712091202240a05040503 60
    0x103110f6004140d8510040ca0b090085014004074100a007401c00d0480901c2101c1260100e040d0040104039460b88910360f58003004a1343c0c1d90341a02a01882d02c5900c109403804c1c070b0308070090b0400b17141417412516184d26a0084022140d00782c109540d02501650148890242e620800a4003021030004111001168480941c4d40b81a40642c0940b0360417100310039005030454041d10729a44545e03000200080e1103800b690210380d26151100b0089040414495103400c020501c0c000c000a200410103001d03081d81c090000080340480010078412000c504250f01c008284040c11084010b2007000c601c41d490001a00203a032101e81019600d40c44042c2603c0c2003d4000880340003c0740e00c81004960799031080002810514040800e0400c1c2d125203182142c00341c008002420521310a81c21002d60710350748a000c0b100e0001500a489600e40540042005403625818000c00b4098192455a5000f164282080c0c1901b018280b10301040c0081010701091405021103036000c0328403200384034880e0b410a210007 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 790979838 1250 790978588 790978613
    0xc0a0c1406031f090204030506160512070507110405011401080105061c09060605060a180e010303090504050910060b040e15210c04090b06090f070203030a0c020f0706020303071209 79
    0x181c15000c6800d00c0f1869000d501c6040c0020100d5007002c54455a50381803d58603403508036a801040351000d080c401c3d000d40158241c60210103440d450008a64842c04d05444a81c8515001d403911000758244060954890040234043c10281003852200c0d13107000c001401d41138040e004280300355400d124207021021030400c5000091a09540401d0040050a2803401015150440f82d04594000350085141c2d801841080c10350103070411014100b90b0300c0890810001007800010002280030504200c0da1420fa0403007608014048291814449501c3d80364040320141d520200340600d010504010000540d016640c0c08100c48440c00722074038076040010300000c00b60a95103c802071b034001980c46004108a04203014502901c100110801c0c0d05014039031140488041d0721030307510440060070301d0f500301034654080c542d10f800540c00c507105c3c490101f0282000f00c41483c218030403680c0d07010021000700400402444990081e581c0c0303040c4454014010300d00e031050b229200b4200140314000030014203910 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 790981088 1250 790979838 790979851
    0x20606010c03050d110307120b090604110c010c1e0827100c030207020f0607030f0302250b0402040605190308130e04030905090a0902130504060905030c0a0c140603 72
    0x5a412128910b4141c031140140c1180220451600780d5414600b1000002076004e40095240d01e00340c00a824070b8074045d50b4555a22a400280d0200407503080d0905400191040489032800c0b8109480c030300c6c2550841e9400b00f209400a40010084103940e40c3d000c103196901c4200b8a020f20311407408208aa44015804800d80c501c0c94028040038440f01c014091180d002922540900188208000041c065001440d090384202b2440100c603a1602e410400c483c80660305407544528103180d40c070260000c0d0005034641c02910181c51002e040e884441d05030204447c4240c2c401312042c202401844104c40054102074050305c042c841d90441d0b54807000064084a0b803295900b80c2d201490406d10010381d186900c12541047e41d08184401c040d00074007450192074090350100754940d034801c2c250702500c0725880060b40103040c0440c03a1400f40d001e60412540640038010220342403d582e59107034a5a03002044460340391b00a140040704004070a40708000910300c5030800201400a0800030381c2030b10000c0c208 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 790982338 1250 790981088 790981097
    0x18010e010f120f062a0207090504050d12110a02071d011211030109061d1b3303010e0f010621020c0c0325170a0209070e1309050606010f02060601 64
    0x80f0300402409802540703101c6440800c1c00f94a071880130505044440316900071026000e100008105c900c02c62040b544103a41000040c04d01c01d02402e0241d65948000c000e2071281c030f8485005d442002c107880010000390050350300402095180c850700c10410780c2401d800c2001c19104c8d030010004980d00c2c1d0201e641c41c0b60032094486000d9050300c0082d00402c0503001c02001c0504000740151540401c2d043c40104c2c10a400513101100007512007001103000c043d11041e07000415940060400e4180c0f1180500d001c0c0c130340f02a041c1c0064501c4441c10f981c100744e000d090004488030421800d1030040741300d680104814182250340900b0104403c0258a18a200c0500968080344202185c5010850702c03216040141c140c50480d182c00520780c00001d00b0814245c3d0055143c1d00000d9800245804001c9655488000e030141e200558204024180c0160020701004881030048455560700078190781035401c070040015100075a8580a81002401001d1030b0500c030446100740300003a0041401607010318240f070b2 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 790983588 1250 790982338 790982363
    0x1d0a030b090f2a010f050d050c071110081b0705010f23060108040206091f0e21060103061d0d0e01031103061516170912030705030a0503060402070218010e010f12 71
    0x41c06c40d40f5028000300d50070003500b05414030042042c0c100c001c1200c03900400c000c5003405403100c00e01c1803010550564400256024000a0311402c016103a2514089000e10891411a1544134107003515440100c081c1229035810711462800130f6100750f444103841c0c85000c00c6140c60548006010704900400c040e00a1000043d12140c5583d40c54502200e1042e4001013401c0e2101628000e00c1440d0101c0514040e4002458038140d25501c100700003a596000e00c02418181e081d50b03078050161984403000781c0e00f88000070b10803000500a022003c0703130303240c0f0746d076a1002c064801000500f070700d40801030301c2003a003003c00601400d51030342030208801c00741c0d81410076503c10560300c201e00361218130600a00322258419400b401c1055140003410444411501c2ca800300f00b001c05a580c40b4814000d005046500402000c000280107001959000c4402000142840302640114005219500319a0554080180144800c2c48804403413405098141813501c0400d040103040c03200e000c104000940248004507 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 790984838 1250 790983588 790983617
    0x60612031804290f19140303130b0c1203072f03070f1518030f02160803030a0e12071e02040207050a03110c011d0a030b090f2a01 57
    0x10007842c00041000000d6202da00700c0d490000c1c3e02c01106240c24490103411406601d9031405840300810007490b44604203901c0d1505a0701e8038100b4041504903051701081c401a08203003c8020031000401400500e699031701401104d0754148081c100c8800e1140c442031051080c0c0fa07174488002d040c4401030003204000c9041c40c14501d8640c90315800021464400010392104008500b051180618030401c1d00414003403036903032105c0503108620000200311111000741c102091280c0c8031a080060180140c40b1200710442140c840c0c2c84140e001803000382d00001c01c0c40540342c028401d00c0c0c130686030f041c0035020b41f5400b0395074100288140000502404224a0201c03620301c0d05443c03214030194001c0c0215500c0d080d900e000b0392205007440068002c41e4404240340c42010000c00e072604054070517500c49061142c12103c841080b1801b8807a1904005488408000a01c10808a038040c02c4108004c0c8020180c09030740300d1401804602d00c03901007010713102503000280b8488222022850034203081c2c15034600311 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 790986088 1250 790984838 790984841
    0x31506070510050118110309031c090227090c10030c030605190e1003240b030f0c03010c180905180a0303150e100501051c02031503060612031804 64
    0x600001024030b280c08000100b40b4815172803000d4520004a09000c40e800740150245280011034800c0e075544c000300698541c50b02c0c015600c2c128121801400a030501203030300824807140e0b68025403480d000c4044800c1c2c98081070308640c01c0d841611440180400c02c444008140341c001224004420b040d1202024425035010b038110300c000e42406001001000c01c1103e6218182c001880b80c41050607103140890a0300000003811801c0d244c0005088072822401c400d0080000304001c0c0011405959005201e400c0e42c003070108103c2422107074014581e10740c6400c2007500f12080c00090740c050050702150280c54001c56124201101d00c22030001826580320030880b2044440e80c2c444d0103a9005100c0031600705a019405030700402c031944881007030641c843c035421019400945003138050001c1e040c0e04004940c460801401480130800010390700500025a001c1a6002510b145581c1c401a503040c0c4a2810104102e03644180304035805c040d0010304007648c9499103d55818a4480640c0c500e91039440c2d141d9 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 790987338 1250 790986088 790986103
    0xf06020c0a05011b090614040501181509050306010906031a2e06080708061807020c062b15030b0402010c120518100e190b03040f0b0703020315060705 66
    0x1c8024000c41d038007050044d9040940003820004600300c2440820300c10f00c81c9002c803c0c4050540340403860301d81042c4c01502d41c814074804004550350720038008248144441c00b80550024a6210001842d04050401d03003880016041128618a003500c100003003001c00e0200354074a951050050071503241c98140982c1c1c00200941c2e540020b09842d0030004d1000782091980c11113186a444441685070041c0c2168808419202c0503807180c0703610b00d2228042821040300ba044801c40c011210040c40301c201054107500302c030744490b0503030000400c0300100204d18481c0c06104810040100100e1030580e240c084aa0682e010151006030001d00180031640141448800f80e50082c00c00e0070741c0354002000500316801158468884544200b640505041046810300c51881035140c8468040c00b1900f03016112101e100d820a0051f10088006154800200258060350103000280c0b50100c860030508407010014190300200340c0704008200d407015508035100740a05084502503980c0001d4184540340604 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 790988588 1250 790987338 790987343
    0xa060e01020c070b031005100c0b070e09070906020c0d0f1202010b1e0103180803071b020d0b0709120506010608191a1c0c0902160b040602070209130f06020c0a 70
    0x200c0b44040f60351180341c0c4c05140300d0010380c04081101034076042884580b00501030000d020407425901200010881c07141d0a51002c407a2a104405100d80000207468041c1610054007244207201e041c42981d9041c405a0240d41040d211100381741c0142c4e0300c0c2e90341d01c01100d0300039150000c016190807519100790020403001e80c3c000c00000711811000203c4102008003150076011a150900c2c1c0b8500c0260710360a0054645c0290307800741199524001942d4903020000841844900300d00c0000040c0d4408144050140c043c042541292500400152508001d5001551415000d2a0a4000400010304241551240c0c5401d60031500e0b00082462410b90024101c3d0f201418030350042048041c042c040c08000c441200e100c1074803548003401c842c2285040002400c25070701c0c40d8080c08041400d8005107125009801200f282e50102d4498119007101a40e040b01d0750f80c2c000941000790311b48031461580005240441500d000e000b0fa4510150743c078030b40d0000f000c05401003a103040e0070401b0f210301001c00e038 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 790989838 1250 790988588 790988593
    0x131a04180503180922121106090304030b01050d08040303180e09060907050f060301091a060f09010206060105160f0204020d0e030d0c05040e3c0601020c03030c0a060e01020c 76
    0x1103d240030034038030882600c0254001c070006000a4110b8280d01041c071801c80003c03126042c082e042d03031a141040700c44c03111400e041c000c0740c2150751920001002424854242c02c40038540381c1d811450113103410308040c0d111520500a92801e08081504c19080318122541030512161940940102201003900c5e94030441e14000034408000760f401c00070a00300d119800300000c1c0c5002c03580710310800100390300040000760060000d20062040c074440340c4c8190400881042043c1407071100100080c015400800001d209450100d83d560055804101103904007601b4202941020b4000400c0d80400f11141c2e0041c7c0100703000380e4260291f4131a81e044640c8507101200c2031180401000c1e48030340e40d0b402404c68244403840c20304602c170414440c074251801e90300c510407015195282e40307002e400c12080780106584420302014003010011603d040c010703107412000700175030f066143c11800a81000c0544084902981082003a1100807802003520901c90364418000101440104c1115009000740c10180080e403 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 790991088 1250 790989838 790989847
    0xb040504120c0c083307050d0221010b12010504020a1d0301020c16030b010e010e0f070c050d0c0c05060304020a0b0706140114091003051f11070501090b011502071401050d0911131a04180503 83
    0x33042c50310000c0c030301010300d042c0d200e400340d80c1e802c244400ca00c03442452000080d14031440390700b410420711001340016002400581030050800000b814800740e40801c8002190f505010410040c0301800580108036551034403481d5858002c0c510300500340102240781a41034500051040341c02075a400080781e40000468040341d01c03044000d0540e020600e4203598501100200048510781001102c1c8503950203072800703400364a40a1007000f6500014000c580c034030b864605034802e051185080340c3c001c201d0018000380b098884000c0c401e0098003d072030800740e10819070f8240081600098264040380d03802c1110b420b440100250000204000703400f60820003c006500020f00805412030004107020303803001c0000b40d03030f02d940d00c02c0c80c46c0240ca003540160300728110403c582c8122140400640006042080c50180e0404001d8200c1d138840c10708541003202c10b401101c80d803c20003080314549113520010001007090452040d403c00c0c003104104c4c80303543c0320380da0103135003022844000e9125030340001100d484 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 790992338 1250 790991088 790991099
    0x9050a120305070e0906060a030b240901030609020a1d0a05040f0507030507022b12020705210a20010e07060e0102010b040504120c0c083307050d022101 67
    0x1505040d6501c400280441d50740040c4c80c6410748501d4056a0300420092800c003010000f9400382c010062003e9014030701c0c02d1141c580d1842c54400e0749801050800059031600c01000160031140d168010810701c510621407a400d240d08100907075000603400d41880342d030b041c4070320001d858004c25402103074019040c600d04144d0380b801a004240902201d440c14001d540e2080707001c030b944074500e00805080907240100e0841c80c20660700c0103101e540a030714000d101c8048200e1460241c0c0d100c1141202c6aa010b1022008000c0d1200010710b03040010038209841e00e0340b00040104540d09800703844100d02117003805040030031025881081c000e4046025903480d195182c801802c1548102186805942856103001061030148074440c420b0707a0140c1d4000c890400d050046071040c14910045031507001400020580180c1084103101e01d800880c00d90050300f1840d01034107030304200803418030406440350b018400c40c0b6400c102983d240b186900340c0142c503003140000300c140b03131080d8190001c1c004015038000302e003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 790993588 1250 790992338 790992341
    0x230c0c010f0e0c030f0717010603060e0604020f010306051e0325060912030801090f0603061104031a06030a0b0408090d0305040602011401050f011b02040203010609051201110d09050a1203 82
    0x6000b41a54161414000c0280038151103081c0d41d07404454030b030810780301801614a0440a001c140c0c00da0400018855282c0d030b03804044500b44095007605502480401c0114641038080207807554080c42c050020510381004a0803443c8500740c50540650b201d1207641c0e0a8a04000010340c0b83c444010030040e64400070b40381c07411113a150245a000428004021903103c0c0c040e030280740e0341d47d4156a05441c0f42e190440510051841d280c01400d240d40b2400c002011664038054036034013280050505aa40d1b02d1854400c00a0b803c0c4d5890060103400d590410256030303008200405060b81140e40003070250750b41d10713040f1164464070f0300342a400b200c074802070030a143d8802e0141003520140e40003080301528031410b481d807501003482440c0e0f11000d40209a1301c9035200b0b000a600c0040100800e40300d00b90a940002c00b0307078200347c00440008012140801192400125422034144044000c1080440000e90030807588a0030744602c081c140c0344c1d031410f070412004000c07054159030840307c040c840c0402d2100050 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 790994838 1250 790993588 790993601
    0xa050721060906140a0b0102071208070c060e01110a02060f030c07060513140c0d11060d3603080105010509060405041d010c030b06070b090f0f1f230c0c010f 69
    0x135036001080300020030310340e2544200f806203003058005007206031a0020f0300288201417002214115002c1c0f0031007000481c0303200c0303074030280c08141c40341e000d4035030070300001024115040ca03a0b02e000d521681c0548096128181140c0100b5950341000f0350342d0381c0c0d40ca1003102e02c2c40b91071001840d4500d440c1c100141c007200c07500303100c0070036114511484d04400c40a9030540e0b1001082a51548082c42404900000301160505000c00134040e061072305115a040381c580480e0b45804c9140000103a801c002c072001c0704481c1c05940640c40f9003d00c015400c020f03450041540b1414029641032100010b48031100d56228000d41d001010001d00600030311020408507042c3c0c84000140030269820521031406150013406041030a15007d804182428500c2c2c441c0c003101c40020342034480c24014a503480e207080806201d03842c603055644c001007000d031a850940344842c69202800c191071900e04128112000555590b58082151030035003000710351030b070043d0148544218a1411b0682d071074001a101394000940021 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 790996088 1250 790994838 790994861
    0xa02030d05011706150103150801060509070503070212071b09091103011a0402070623180304140d050c040612020a090204050906090a0b03070f080105090a050721060906 74
    0x24003072640e840204075402d100100c04210150044400261181c1040f9131061443d0814900482d81c0079144941c507100c04201d03080207845035141c801c240305d2810412007040e0001e041c3c0c5486407451030700720802900d03080d566a00c0c1da901e84001170b44c0d40522145030300c0040c5000180441c4a0301d140d42d9000b800082c00309140494000019002c4466107140601c6446040c80c1000c039884410140072081100039480301c102210081d9440c1170f900f100c586042c0d44000440c80f6005c0b41301d41e070b0034486030111359142100f1204040d41d00802040c0310f03170151001500420041550707480724610051601c1780c245038803a05d0450300a46001c0b40022204404200680000d00a44560000c01e03200e003c807409034400c50040c960451307218404a030b95030903d0151142d005141d0040082c080714540e0000341803a0465100c031600c0d4000340700038042018280308072904441c0d800300400141c0c22641d038690f01e84040d4032a032100280201da004100d0240f941207200010750000701008aa40c1500d8903a00618003007500 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 790997338 1250 790996088 790996091
    0x10c03020c220c1d1003060e0c09130903140703230a030605010203030903030402090405030d14071205102c1006091d2403010203040b07110a08180103060b0a02030d 72
    0x145143d560040004082242003900c00d41c4c0d280c2c052100780030f03101d020040030130200359449200103108111890b84034001c140444e000b80e030304d42c1031004101040072544080d000140c41c0c030807500300080e0091139146c19042d60011050f221002412b06551100300750034081001c5a100718112503c009400042c0040407140d24200103c036110307001207989000c01c50b00490b10b0b610030030205e40075240028000754480c2c800d00172030346480200300c40300307090380c40c450b5003100555004410f0001c072640080f007815001010503420030080c9041341490103101030303a00c03d9007600c85800014000c4844200400d40511a024082d11041c0c1044000940c84440f01d200e560009080d1403008981084c003e018012214250003240007581c8482c0000d900c4040702d894000c400e0019150040c000d620280047d6204500401c0d03042c00c20300d0400406000485030440c620740a0300a00d006400103161141a2a03031100e4204101000510110060b80188440d40200c11590b20201c0c00c140150340c004002c10410340b68050 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 790998588 1250 790997338 790997351
    0xf150b0306070c0804091503120e041d060a1a0406080f0d031103010b13030b07081014010f0509030115030b090d030c0e0616060615090b0f09010c03020c22 68
    0x41150f18000c032142c02401c941040008003c01540d542006d03c00000c0e50b2030344c2200715541d5a6521402da116000400030500c3d010021000d0326080c850401c2160055407a03105980610f0b44058482c040208a0f15142d40d603a180d445204161000c001300d0080d01a00821416031107090f80c82d6103028104c0a00303120b103c0e081314100100d20034040c020051a2000400e401d603401d003204d0080039007041541c075440a0034801b00101160314803c240380941d100c2d4030b0720401030603c680e240035030007180d4100040902c41c08540d00707840d90780501c1c0341e51700c51014900161038103001030000b0301411000d207105101281c5207602006000620743c10368010300300c0e0300c11202c14a401c2c42003502550f003014400c001003090500c0b0903000e0300b80741c4010b0148445690521165007065030303984044602d642c0100689403210100c0fa000942c0180342c04020307002801d45141001d5003c806440e10384155194103040140c0d810304030042600800c1040b28004004000301602e402c80410300c2c0d94115010310101242e401d001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 790999838 1250 790998588 790998601
    0x203100603020d030c0f05100b0111010605060d0b040216111804030e1513060f020d030510031103030f1801141303030e012303071416030c0f150b0306 66
    0x400e410403207501502543d007140042d24140e45910122906a0740c6400030700d000c1002902c148081100b10600900024028041400040051010503248034040c0e1602c60103000503920310090f2000c821103040c0201d00c968007840410064000c40041c6140750f42c2500b084000c00c09044402a02041b0640d4800d40f84084404425a034050076180a408124603400d410340c0c50600e08008210684074004403454a0790020003007060200c0c1758002c00c0095004681030b085a6410f102c4444241024a17090040b030804032004504000e1b0791200030044614085203d04c4e03a1014030580c0d00b0702c41e125124588545240d1286018604060040c3c0e00280c5101600c4414403014400c4d91016066000070030081400d40d03030150303006070001c0781550500c92021051f011a421035156241940d07008050182c4900b400030019101081228015007490003d0000440005140c40e2050101e130305460801985292410000c1c92036a484c200a4450800c0100c1000c4c44440b94000f04400001a000c40d101c2d40d9610 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 791001088 1250 790999838 790999841
    0x504050c1c030503152707090801060503121312030504050a230907030b150d18030c03350f09010203060d030c05160f1403030f03220210030603020310 66
    0x7440300070007140040c008544c10000d440d1103d49140790183c4000180e03021000030b14201540c407452800744000410030401e085500200f21001400d86100a200c03060038100081e4599140c2c48081080540116000c2d490100110540f0300030144a104200d0500640c100242075500c5401800e00a0658410004600d1052070103142d030b244030391014030170b07903411f800400085c1c074005802c000c1050384500d100000c654891460440d40d00d0702c1d034a02590340030a4210a419034070100b03125010b01100341c622102094100c500c1c1d04100d036140c0340c0765401c7c6805c0400000c01c1d00707000c01842c03130b190714050302e603000ca89007079001c1d60040c01a8000400a80e03200d8000790300747c2c481210a5a00200d21010070b2001030300070310344c0072202440744c000c2d00c11000340c607402400b00b480e0640c00301c0740c03090102d00100f00035460381503554010303c810b401851800f401c404001a043c17101420440e0200d44000c00101240401e014082580b94014039440e01070424800c0240500840d00040e44a80202164950b403405c09 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 791002338 1250 791001088 791001139
    0x32d0103030e01050702040f06080d030b0a060215101802040e06102a0f060b1009030308040b2707080c01081603050601050c061317120a020c010b040504050c 69
    0x1da41d64820380340e100401180d0903080480203c1e00039494440c2004450482c2c01424050202c90340103020604120b0001020364005001c440d008100482041c846164040385080c3d05036080c0c0c1d0648129250f483d81030052603511b034082d41000c070460510f8070743d280c0980c00030004c9aa140400c014180c8035001002000b841d402980d0021810046040040302d0401001c00089150b00c0e00b6001000c005440f605400c022004007110040e5442d5014103c40c80d20f2900c40120410038945241d040d419641c0107003100c000038001030216181080000e181c0f201c0c4100c1c0c4144000010000f0b00100b091920721a074a03e094000c0d48103a0040c151792000079480b559406100e40f988600035450210803000c140c0081402411300b0341000b001f0490300c05070050404c4198015510b0302008a00f007003a5050001a9501c0c1d02c0c400000c840080008588181146140c650880040c6400607035610012540038010f02e2070528654100d410070303042005101d400700f01e04103148003c0c0d0741d9400501e0050f003081d0b031000710b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 791003588 1250 791002338 791002343
    0x14060c130b13060e06160b04060e060412121b020f0f0c0607140a0b0108070e0c0c0c010f1803030302090907020102040303090902130b0712031a150903010f02032d0103 73
    0x40798003c102961184003514800352018040e50b02d02099803032103441e03290b1030580036964100480140010400c8a100d14890354103c0805001c031f60400d5521024500c1c0202c24001c10041200a00314007000700b5481284000d161880031a440703120250042c6d116596080203010740e00415284101c00000400c82004080c4010407580c9031008075600c2000c090341003140d91045104443c0c03a44009044507920b079020b465000010450780e4a0451224140080107080d085203110602080c880c258000883c00c421103800d08140340108282e060869050710965104081000700d81d50000a06400d5070082240e4001501c0e0f0540c1aa11034074141d0a0348034910000300003503a40c410401c140c1c0d0140c1d01505946001d1f0540503980b40d9220100032060b040710409840d000ca039500c020a03115014030800c0740c000800c5480000c80165100040d001b1030026021540c456400110016a85d90a500a40503550614821900c03414845001c41000f014101e5174842283c100000e03441050382d11017424122076 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 791004838 1250 791003588 791003617
    0x307120b011110050415020c0304170a110f0f061903050f01050a032301060905091608030f07080f03130203121804020a03090203060405010c12020408070501050714060c130b 76
    0x14080f4803494028100207000340d40c8080341c0b0300d010304041210b0000b40402d102d1070300155192070801d510120032116151407110143c3c040c1410400281e00000c110841c04800c490820322246040b0101d40a2820398203240c3c1c0c07149000482c01c6081e0400c1075000703499545583c04001c103643c0d0840345c0341c20350001c0c0243d40e07110703844000403c0003550340e4210b41300444c0000100070b03c12040d000480d00752003441d0400f1080c40e0b124010041640c10401c8403521070103c80800c0d07600d80e480d00b09182d0b100e2044500606e00c42100145940074050101e08076140f100c1c20700e02459032460f168503c0442480c54540481c82400703190344007001d6600070760903160240031400080708510503a0041000950001d0110030900d5110000917000d680c0502106106902500c0085851040400300500000180015140b002d205000074011304100003800c1090b034800382062592248a800c006644a81d4440200d08500c1014100100d6447c0700c4058541c04038110080b507803940d12a04c4011617802403881984104 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 791006088 1250 791004838 791004853
    0x4090605011d121608010515040203041101112a01141305220912020c030d0806061e030c0711042a0909020a050705071d0109090503040b0307120b0111 66
    0x1d240881e802d0f0241d00001c0c040b102100004505024003544950010034143d545000704032080d1245903881c941c03810100c0d0110300d54078143e0380d00540030010305105810481e10321200c2c00c0c03103413041122114541d1b0b9500207010f52154a50b20304101c524154103d030008000020003141210f110003a103e2441002d0109000e150500013409051a0036151703103a1700c0850200d00c07070702c0d9070085d01c81d2002c1d05014201c80c070828007030120068600307010050064003a9120110407101d555003c1482c0e5040101181c44660b642441144140032a03010900341c90040000030a015980311b1134001891824401c080301c1000e58065010042102c0c44490005400c00414100d652250096546690b14034050f040010b0441d80b24041300080340c001e0308100d80414400102c00c42480380402c41280180303059a0460340892004c00c5029942c04d044c03185800103a150035460040040510650303016007507a001031903c0f480c00d4600100a64840144464410716100071082554816103400c0c5840d40131200a00f0340 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 791007194 1106 791006088 791006147
    0x30103171c051605040f1a040302040c0504090f090c03060b0111010c1d0405010609120602090303030a093c08310f050d30050409060501 60
    0x5110f070520040203803540086c100015648072880b85510005c00b40e40142c66402180c000940c07160514a500d03050550140141040b40d84034003051246103614800041110311101024100b640c06400500c08203106070080c0c0074660040c03606080c0f44440b40992800c440c040103850f80064410100d41c65140740d1603800c1801403508880403c040d515241000d00164050300c510011071940e080440c00b400304541c10382c0c1d8002d03005401d1b01e9407480c01645a00c01414540401c0740c4207411401c1c004050400541f540b000b88100b081e400c59001c1001842800d0089440c038100c80c503441c1000424050003a40070803480700175808036000001411460141400141d80c0c1003aa00003462600030007007541c402c4410030030740e9040861441da074a41460741501c0401c000700c01004e10090320041c655503982c814020000ca6981480400c80030341c23a4001195116842e220380300b041e000b2940407a66 = true := by decide +kernel

theorem cover : BRFrame.Cov 790827338 791007194 := by
  have h0 := BRFrame.cov_init 790827338
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790827338 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 790827338 ≤ n) (h2 : n < 791007194) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
