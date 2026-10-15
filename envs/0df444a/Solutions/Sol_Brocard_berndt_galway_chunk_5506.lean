-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5506
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:05:23.353812+00:00
-- url     : https://prove2.me/submissions/8ad15a74-20b7-444b-a550-ca312b25250b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 990107913 ≤ n < 990287769 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 990109163 1250 990107913 990107927
    0x3030903091e061d0105041401030b0d03030b010f08010501020307110a17030705190b0a021c4b0b0609040c0c110303190c0c0e01060203070614090d 65
    0x450030403459080014031100341200460200d41180b03030518140c1e240a400400d40c600116041a000c0703688005000d0681c0c0100444088540f0703540c208240512440042c3c4c020218040a5900a40120030020805915a000c0e14002000341c0b01c11903c4a01800102c407505002d01903e409640204102d0022a9240c0e0480140c650014184c1e1403050f03c4558000c0803a13296034003040c080e840460000708110301400780d0300b04444001101103482c0810f4458009244000e0030f040c00c40759001034028a50f00000c02180d0341d00c1105101880380d10040e00001d0520740b00701d0030942035400304034240c2202520a0b081743e0312007007030508801506061012180c0080030030300d003090f91248003045002055116401101c240d9a1151500b215030840343c01d061242d03484102d9498481d410405c50035200b5030822100c0204200680380c1241d00100364601650303092520740009040b0510710300001895a4004004c0c0442d5100748005c3c0001c12400984003007840055a582d61241c006002c0d140c00d180c400c80c8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 990110413 1250 990109163 990109181
    0xa05070204090c030507090606030b03160b0a02010b061b0c0f031b01020717150c0c06150d140106141e091b0d0605010e0603092a0a0915050901120303 66
    0x3c0b10740e4540d60701d03503805103031520a0340f00c49880c41c0c42e00c804011058240c4920ba004e00803d0740034003408021380001545000c103c0c050b80c4000340303000c2103002c0018402d6000c9444500c0c0500b00d680d642d04110f000520360248400d60104510506902d002141071905001860800140003070903001d8030380400301c3c0c0c03c00a40007032034111f21445100042415601031780f04641c41c400b40241c0180d0704208180700f10303444003c1280d00358280400506400320000629190f02403541d1494111200b03c0c0d400283c21088a848049c0c41c2840005840c0c81007081075002c0011200b070a41d22040c078441210030f2241c035a40c40c0d07040c44207520031000b2040e0341f0304101d090507038414120112000d0019070300740d06d440c2907000140340c019159aa08000e12095030040110188000f04403507080c1189050030185985882ea48144001070703580b8046851b5001041d032407040c00c8000104007680854960800340010004110309058508030603900007000c0c206000a18180c641c0800d060449504a480a801810a0030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 990111663 1250 990110413 990110423
    0x50a090f14030c062e08030f090d02120d021006031109091504110a0f140d0201021603030c0b1b271e030105070329030115290a0507020409 61
    0x254010f40d5006000881c442c00c40301101864804076090170590701480ca1010300350900c402a0140560360b40041a645410701c0c4e81d074295511016400441d0f806004c03803000a410150402c04a9200500414040300c14aa960708884065517401407030b000360341c050721025084030004501e41c400e034140801d2641e400030290f000c8665202c03480d0344c2042030100c11035081d41c2d100c1115201c0005031401d1a015801010100c0c181c050403400c1c042c400804451001903580b08559a400300001c40e4028001e210400c0703a80e041b0000400e9585c1805040304001141c100c90000b46000003c0b242c009540d8400d20402c000c50441d428070045a400d5141c210020701040040ca0b244020450990f80b10414a460031884055200001e201c00052600b0f40710060a0b041c18141010710034428176071b800e00149128041c07088102c50a001c4000440d00618002c0764034a08000960b201003140d50b00c2101907140700c4255031480010001031010214a40a0f0025800000e44100301c1760300036203010740003807405074010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 990112913 1250 990111663 990111667
    0x21c0f1202160b0d06051f030c030b010f0c240e0609031305010c0c0e1303020d1e05070222020702190503070501030f150602010b04150509160513031104050a090f1403 73
    0x14000152640441007101005050f480703004580c0c00c2d23894000c0345040c0c20302e81001d002a03080000042c11440703680d0316100c2007001950748141130210f00c41d011610400d51003500d810036401000208054281540b08500c2446002e0110300f00e080d00004030355003034136182c42c040001818100111100c0680450039170301c020890b1400710305894103418040c00352284280d100b24058081c03030040c1c2403c0c204c0040e44103110a00840c6078070300d6502610201c490351030703180c2a070343c4d51090310009420345040351040441c0c40705d00c01100382032881c90340107060950003164004042042c4889000403040c0c0d41c06801c0d00364001803002c11280d402a00041c02e1122646c00c0850324108041d040d401940c1c59a00500050303454040312040c038107041c82001c0050079601d628565160614020035260300001d00340d8a1024a03000c07409410501c01c4060350341c18804251403407605652030528800300c03180403078542e21a5103003802080c0141454844c031110304e80d0002000805101d1501c81d0003580d52100e0605c00c0038001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 990114163 1250 990112913 990112919
    0xe0a0b184201021c050d0c030203152206170f07080309040f0204091401050111070e040807030309020910030b010b090d11010e0411120604050121021c0f1202160b0d06 73
    0x30011490100e2600d517a66a032038981021052060341c000d94070311000d052041007449501300320010070101946056a00b02000c5010f819110024001e072500341207000c0c03920002041e90000d01c048000782d04024002c640140c1d94035001251102d03803c0c81000c9031030341700300000440c50130241c0280510402d00300740141481d41c0d07520f4000c00da40810b00300725145440140148110b40e005000102d03a21400002012201d003095050807000d50050030161000310007141800030188290004000c0311360141181c0807030301349081c680403140304d0783c0000c80300e40148000101d24142803400b510f000391801408005120304a40300c164241040d0300645040200c09041141d0703584a90088929480a0751151907079148845590016464007424091180e8200001080300d5130b0140c00700404d1205008006101501e1480001d000842c90404106000c1d1b14481240902502d03011040603207001e154802c40d03025841c0303030803078036003a20080600441c48400028800c0501d5007001d40940c0a134824001110340e1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 990115413 1250 990114163 990114193
    0x190509040c020303060a08010c1d0a03020406180507020a030f05071b0b07020a090c050f0c0a06090303052409072115032108010e0a0b18420102 63
    0x100201d40d1201680c000002c0c441d2504012095000074050040204a0034110b4100100044c122004101d01c0d9480d00e50040080c1e0341c0d001c590002503500800070080d00b90341d20803400c51b070382590070701220407407900d030024a4040c0041501c28003158190b0790b00002500144003515690000c0d0f0007510000ea060780440181d8441e01101806080c00e80801612502d003481040305803107045d0004030f1040c4c00c0c1009000c0b87c03900074041c2d40d08602075420044c2c0300c0b0501c4a1262030220305000150885052a0707149042c140c059010b5401200d80088002400d400360800c090b0459011f07800f1074000340960002034800348202c00d07807100341385000996400c4841c10f1400c00107807680c008404111802c440c000b00200018160802e41028807122034034441400e011010b8104501485961864400326001409480d540d5001d40d541960040c080040b00a1410700401e910304200e9640d03199180c0ea611052640345021a0a04841c01c0c0c40c0894418001c4039449624012031000c00e64154070401c15140b8201c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 990116663 1250 990115413 990115421
    0x4060305091528020c03030a390e03030a0f0807020a0b01080601060f110601051903060c12050a0b130e190302061b03090c040e03160b0117030f19050904 67
    0x154110a4403520b00b034041e03210070800703c2142070140006104004080303400e04c01000ba241d04c40480309000070341c50480104020003001c1103a100548a00515801d20050307005002c0b80340d2200e9030740e1040c83d2810400145541e0344504016200070520380200130f00758130301c6894820750103021031050300c40483d4259a40c59080070282c0203103001d60003000060092a42c81140002100c1045c540560030310380c0017651035200c00c0180910340c083c9070b5a031b4116402e610b00f8070032007000f142e2024082002003100b1000900340c81020400318095800c16000c100c819540e401041c8032420000c00700f0780754003e042c181200400003143c540005001e40e010840c0d8030a80449621015406900504158605a1400c803a07690b04c6072041c038400c640070b109000e0344240c0060080704190040d6800513004003118426451405a10b186841504080490400300a4048981c50485070400d6003a201c3c0394a21010a451f0300400c0d8a032405040d00340701c0000c081d010084039110314601c90038982e10b0402c2140208040d6 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 990117913 1250 990116663 990116671
    0xc04051f0f081b09010308130b04090203070306080105061503060d0b071d010f050d200307020a050136140a210206060919020d0e1c090803040603050915 67
    0x8001901d40400c0848818000107000c90300b50001c01454482c00380c006844c010042c00041c110b8180420000301100c11116007170080d2802c8000c581d01c1d20342c2c4040c414043d43c811030704000083e040503400150803c0500405003d00001401c800b0036000150b042c841c40e8000402040c2c1c0807004010800100d8100680c95000f80159940d0501c0c000c0c1000710101d44000a07a0701604018036001c02a0a00340d2000c25111016105d030301c00304da10b40100e460b40ba8000d036601101116004c0c004103010301c40780c000500c8412588900002e024504d015011541049181d12404508101c00d03582e43d0309411a031849001d52a2080001c0c10000c14803820691402030303102070403200005020314000d50055111142c4420032103c0c0300030b206030700d00040841e2004102a26a04005400c207966003800c01c0d03c3e0301030341e801d40032058040103001d29207000300380d80345070300280c4503c41040c4130520f0107440d10510302001940c0203640114646454100d0803801864010a00e00c501d0091382141c41261081010090003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 990119163 1250 990117913 990117929
    0x15101407030207031e0b0f040609061509060e150f06070f1a060609180a1e0516050f0a0806040603060e0604210c02041a030f1507050c0c04051f 63
    0xf03240e0035840e10305078080b5000e042450550f10700d03482c03000140b00004c800e90b00190031006645c03e034a452a110024003e40c110043c6928180781a96411580079075283c4202d8640c0b880600c01e441c1d80c2c65000403840800d035102c60700b00c4c2041039422014140142080b02a45002d4801441d021094541d00b4181044100072030700c10005100343d00c004414000752a401101c100c03a9545400030001c001004859060901031594082e400020008141640050410b2501e4043c5608510020b050400102011140c800c0800410010307610601e01c5081541d050b0a22281a180307030001010066480300e0008280b150300684890b00400012800d00450fa5071200800007418a400c040c030b4020b040c4648240c1c0b40103144004256442410ba0055814030b801340c0695000a640208448220700c480c44440f1440d01440b4500e00c2c0320f046080014401810040384116080330340358a1001c803064415080c90130032039401001c00181901d0a64001ca8200307658000c0290310000030306542001c54a540c1c04070700 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 990120413 1250 990119163 990119173
    0x8040f08030717030f070309080409020f0304020909070b043003200c1c060912120513080d0510081207020108010b0c030a080a0f0f0c17151014070302 66
    0x1042000c691050303d402400c0106013030a515100342c10054408000b8100c804164649400c0001d1045840c2250043d120101081d50707145110702407d0303d50750060b50100d000c1c00c0c98170300003105440b0219014040d500c1c1c1c400c2071454a0303c0e01034661090303040c0e44071000c0601700890141c6e52101032001c2d0111694865111040494103920001d00c1d0b0180000060b03009420501580006030b90700d5075400490074040d081251640c1d02f07810280002e260010000b441030140c440b460740440d420500420010742c9030035051205945458040b40341c14151040100340d601d061007c0001811513400a561200c0015081c204080d45d92444610342000003d0151400300002500c406559001030402e024182d1b07402081e03e00743c02d0b0b100e19030f924400c0c4801141045a2000031a8640c1403580080c0108035443e0f40620071405442c038504010011031905401240c01c08040008141c99044040e2245040090242100304050244000310b000c40058608000709616aa42400b5450000c0e142090007a40100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 990121663 1250 990120413 990120427
    0xd11030724091401030c02030f040b030108060705090904030e1c12120203060d0210120f0501091b2304030c030516271503060509100b121908040f0803 66
    0x381c05010006903032081244a55003446024001003211942c40428030b0002140c20031504224114010769926421a800000300025100c07449809076050b2544141521030301d8403260780645042c440d01c0c0c00150018406400103011038055560019042070103080c0521b40380000406521809101c0800c4428400d050304041e4003e0780701e48080c0e00100c8203c4210b146041c2400014143e2000b500000c0c451044400780c0c4074001d10039040d41d08808944602403008138020445c54010f4802405041e104a19240c00fa4007024960302002005841d40d07124500e1100400700c07150b4042140c603d81c002507a004000000000b40224800c100450168014205079085d008904d400c50740d29a121031440c1e00340901650603c64103080c449409891602d0000b110b030214042120a11400d13440540128602410040460008180307074650001e1094100000540c000c10040c81c5840c05200064661009140b2005455083c00300c000340c5001e0443e0034240340da1440026071000403500304102c1504041819 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 990122913 1250 990121663 990121709
    0x151202090303030a09060612150c02010209060706091e0818061b0106081e10050601230a0f030e0a030e031203130b06101403071e0906080901050708060d110307 70
    0xd1006441442424501901c117030301c275841d899103600401c001305a5600d01c1c003482d640c003d60440340314000181c15180c99000a0511341c009250788102510f810f081000c15200c000418249454020750007412207040044031008180784807041c0c070003203030840d50030060000b03000c0b0060810407142c0503d800205155041000c440c1c1049011001c070a03c801303010200c00176565020500781d50b0702c107065000059580e40d03440100c48208003801414403501404010301e02c035440e00401410309410a03210000d405202d844118101ca90569041111b0b4220410850002c2d12886500342031141c01400c50720b4001070701a0314060740d84244c2e00548007501d426480810081454803550b4020301c203c0e14440c160021480c06081000d0040d11045103810010000f01760078040ca400c1c10440c0a1000018010089e145020703003031003079034095440407071312010024010403414024a0300c222103941c0c4400148c0c5403501404040c12580508450545910202884c9628200f040d1750040002c1c00034114005000c0380c41c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 990124163 1250 990122913 990122921
    0x3180906141309080924040b0409140105010e101202180a0e060609040c180602030405030c0f0312070c08100605040506030d0e01050f130f0302150301151202090303030a0906 76
    0x64410643c20403003c4800700710100161080d0140558207050b104850000303580580c00030501031012440b01140201d40e0310001d001070300944410b004100b148005650444c0000395003441110700040c0840082010380c01c0241c156007161134541040141640c01c2180c3d2400e982102c4c20444071548050031016440c9410f01d17000000f0600c2085500f02802d011001c20706601c46c41c181c0b0f500694070341c020000454070a102034101d805001690302d12950f00c0b00c0d8020740740c3d0f0191051900c24440c4e0340024400d49040206d09502c03180c020014006000e0440150301141c00001040e12440110200064000400d102280600024500004d444d80c2410108411540d0180c0194000e0344505256003400341c102c0a032440010302400c101d511550351081c025124070a040c10f07401884020280082c0c0c5410100c515070944c0e10840e0288410100d003d420415800240301d0b5080e0507060200032070125001c0c100c1001c403448519409403030072143c076011a14550007a107000c4c26640c0d8a0305001e09021441c0b10b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 990125413 1250 990124163 990124189
    0xb0d0e06070c031b030903020d060510172d0a0606090f0203040803070c0227100806091c0c0803010b0912010209060d02030910110318010204060c0318090614 69
    0x700009820b0303207034500804950030b040840b04203039074400c0b410b01814000c429001c021540100203c480c0b150301d1a0031800f6060a40d85084810400000491600c0161000704410308040c40100b56219000d003400300300b466a07081000760140d07150221103107000c00b40f14000780140120030100754036140c030365848100e848078030142c400070f44140107100000c1d04030400c982c1c01250614002100851900025545a807008000341e80900341000c1505020361001105124030034401c2e07010006aa654000c5031602411511901c15410a84410541c001510009848540e07039181c024001c40c3c0990728812a544280c000d081a16004610495603140035248580700400d0100291f09040100012a0085c014120b2903802c480d004800200003440c01c0040c60005a4a01000d0161382c00c00820600f0a07401621402c0c001c000d100d19555560790305001301c81c203c2d00580d440200c00841c0c0c0c1c60858201c810302603122000251100700040360b4015000e00800780201c4055811000644410032032a40701c652 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 990126663 1250 990125413 990125417
    0x90406031a04050f2415040204120b091506010c050307120806030123010504270303060501140408070308030613110a030b0a0308040509062106060f04090b010902130b0d0e0607 77
    0x1400b030108503102c00206842004150081c6003501c840c40c0f9009164281c01045421230b101080c000340750401e10441600389030080314040f0300e80d00d90b0704805071911103000143c6010b074040400f04d4202d521810300083c00354007500c05c1d43d04003107040d03031400b20b03da6015120301f0000742c01c0001e21611746004c1c444c0001c5501600e190381c4903200146c40400440e60148262881560340d095034181111000c0760103101045200a018815101450060300a0030140201400503603400035482048101c01c0c221015101140c2c0140071182c170350b070303913030441e80c2d100070007458025003440705103c03402c030f00b0b80207413102000030044040d00d807200d081c8020100c0b29009040c074441c5181050403c00304096030111400c0d64416144c01125a607420046214458034280d8001c500c142c0719030200c04200c01191031030081108a64020010780d40c0c0040000380c41e860720b00a0314029003203004000100540e07004001d200051030f8803400b02c5035100d2103000c00740c01c079080b4800b000d602c4540d0180b580c2e40920036940c0c030180754 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 990127913 1250 990126663 990126673
    0x1112030f03091518060a0b0402130e070327290f0103030806030a0803180f160527190605040c020c03010606020118080708070f0303090c090b03030708090406031a04050f 74
    0x1e41030b12170f074440c030107000054060796a00d60080e29844940468100030070300c41c00e42018669403100390350010000c468480c0007a141c2041d0041d400c05c1458500c1c103000103164000581c6d40c2d1916641c42c001503002c4900c013201403000c0d02d8400d0025a9103114810000ba0048001075855070030090031100004040c14465000121100c0000c0e0040094a4001c0660111912030039410390001385448407107404a405440703000040c103c0e08114464560984400703072030114140d05004040c03074407120b4130200e0034070520080001a5170124112801d01b1414801c0d08049001507407040400c1c111040341406000503000302000300c01d5400c0034047c010050419100030000342e00c12007160410010310b100300900d03c05001440205101044041e12403442c1c00111545080000e490068005c1007803207001c640300c10003074400080001c0c052103001c0301500080c014602d0039035240d8918180d5841000301d40d610566480001c0041000703000b20400740e242d0300b40d44100f40d0030a410078903e0042442800b80b159400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 990129163 1250 990127913 990127951
    0x70f1401122c03040b07050d120b06093007030605130b13060e0339060121050d080708011a040b0a0e03060901150806041112030f030915 60
    0x9044511400c15681003074400400300800c540b42184140d174020425070102040d01800c0c0000400d440e00500c115440703000c03403a02a05016001d49060300c00c130b0340d403082c000d00c5025864182a02d6030340c2c60113408040401259103400401d00e00c03503a1240805003551002000b401000214032a240e00400c034078100c0d5010003e59500c0e00540d9400404500540a4a4528108101072501b060101e0301505064035201c90103000d543c41b107503c481543c80140c500c4181c2540c20b6003690b10b103591460740c200028000681c02c00f8030300f411018448102419107180c120040d004200d0030b201855807699940d640c0c2d0014101080010200c50040e000388490200281c0040d201d02e0380081140c0c1103d10b40c882d040d460715112178060300d424450b00b9040c0c2d010702902040294050041d40300703000358000402d0075111036856a00159035154100c0d07005004015107000811240303410100900107802c42002c407481c003100488449940d400c145d421510f940d0251115442003a0100d0311030340e021042c6080d202640007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 990130413 1250 990129163 990129191
    0x230a21050c07170a05030d050415020309070b090a0801021207080f011d07050c0607110f0313051c0206180301050a051501112103040618050a060509070f140112 70
    0x6094402d035003107405006072481200f1010f1190008094000060b80d4403854a909a04080d01d0b040354225210405691541000191482520700034401c0b000142103280c2040388003002c650050fa1429403010707020800140800007400100703100d031442c09000c0f0180c1400d10025096074400b82c00700c21542c00c500014828010008003400008412070300c580300b181c440c02c1d01a0361601c180350740c21041d40654401c003d901c54109801d181042446801c41e600021070400f650389a021368100000440441d100402051030254190840407480d003480100c903c0d05680051038590180412030701d403609488452265280c28418079501c8205580c00b0301c804d150070401c40040c40352402446051094003030040550180c108852083d1400300c50501d0a0107100310002084e54000b1030341180c20300e003041c2c0210408100004800c4202c2c2d03000c0020400600703d41c0e906800380100800c1d841e0f103485074400c001107e41807924810008d040498100e00c00c502c02d80001028503207241c510030041814000c003101c03c00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 990131663 1250 990130413 990130423
    0x60b04051e180a061203051c050105030a0215040b030906100501091419150c140f0a14010b060d0603050d03060f05060d0603150605120607020a230a21050c 68
    0xba0a540865010b50f5600d180c0070010140c1c1e4005018199a4030f5403441050340007001001c184800c84034120550414107800c034103588090044540640100000c04014107080034038041101c06a40220300f05920b6030240300305500205d03043e03ca1a40040c091060780c0141d6281d070300141c90280381c0484070901b44085140102003120001e070080031101480c080380c443c400100b501810b038461a406040d4602c402c024501d421060058402c0200c49040320f40d05400015a9084c44c620324001c0c0c81510308503112292031007151300c4950015522030162a0300c030b640b500300500d07240003c40b10014800b4110f0074214903101c8600885410301d451f041040c081c001004130590100d500031030b0150744d2a11200030300301c080d2056601c0140324003544181c40090384201c2d0410b600b614000c3d11803070300d8103241c10300e610303612801a1503034005030b0401d4148e98041082d900b40c3e2040110f281c280909030144a100c090b00d848503802d002d86804000380243c56051080c1900c44c114500c4d00e103000c0341840e8811010036101c1e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 990132913 1250 990131663 990131689
    0x20a1a0906060f1305090303010603230115050c070f0e01080d020717010605040f2703080601081806071106070320090a180b03060c07031b0213060b04051e 68
    0xf800c80654003260301d54407403d00103081c41c00c000d0203000500380020190707030340c1d0000e004003800709080102460b00d11030b410308140084105a140241c06034a840d007107052442400150404000082040401700b1504001031f02c014901c906065518500d0f04c41c1050686406030081c007016004800c50b8032103280d0010b6100300f03880301d100e8642003080316152240c2c01807a0b10b502964019007411044980081c455103d480041d90861800e094039203407101980d0344288d1802c0080100703043c1c07070204e0700551107075100c41d51211101d100520760144081c0031624054044030301074005480e009075045020414040230740c00c00c40e241010b00002039035001000d41020405101c100d0f003440400d03281c5c11590380d5600f010040c10300a494555050340b0140d0000076284040400d4040c2c8150001f05400c2403d4000b15080d968042d034031100000101c1c84c1490540c1040d10042e42c0c4121110a14050213401c1c0c0301e1070300240103900295944914003002d03c610790482c1345c5080754804400e4000c144a03181c1e10507000318 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 990134163 1250 990132913 990132919
    0x2030717091e0705100c030203030c03040501020d0203180706020d23041a040e010609060e0f030a0b13020102070f0317031909031106060405040507150e030d020a1a090606 75
    0x42981c4503100d0038a88030081041d070060b188511410000c00401081103026282c0640d071041d808000c08105550080e03039400001c0c0141e00400c0000c401e00301620141da00107205c1c000261030f2000802e0400180d030000c0da4451844504d1104e000000700003002900d0050140740050411800c250741c0c00352a41490100039075500ea0400c01102c00c0c03014801c03c5174043c05403030755441d11250030b000c148043d0f034009003e050300c445030400c00413544a010b452400704032401d43d0b56002c1090107503000e1000590070160695054491808010001000c2512541c4103041c00c0e6441c605480041c000240b8108041d40321200f40c111401c81480403e0200190200702802010159078035280c0c0317994110f00140e0f090f0b05c2d44080d03152007010001c141d031140014032100b20003003c43d80e0325210303441000102c540030307240140180e1040702c042200e08041242f50b13042581c1c2d402c1401c0d03030501001c003186c00d105611042c800140c006035550310030000c44002000c00034a100145190905c1c03c66142c50307540c64083e2843e48 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 990135413 1250 990134163 990134207
    0x40b01050f01050717221824030b1501050c0309280b04090506010e0321070b13050f0d0207050f0619021011071502090a03020d050706030f020307 64
    0x69030764069021a48810b5000503c0b09048103c181e148040380c0200541c814103207500d8200c41406081e884800c6c05445480b00903100d0aaa13000b0a50002d102c4a0980d002c030b0b075090212013990000c9903a07164015400b4a03816a01031401d207111a003000039014920f41030180a224695201000009441d40c070709007aa02e00c3d103022805261540c10864001c100407000b0600440402c902000380060700131a100b00209124a07291000150345124070803036aa80c2603400911080500c203000d04698002c80c134a4081e1520b444070301d40341d50b5080102250321100c012080285e0f081004400c004402400c40c10a0140a20f141050802503c600b10351240c607205814090090301c00d651941704544402c5410403801c00b4034003101170082c3d00c50041c1c803500755034685003038080c3c0a160500c2d000c449115030321001c1c103541b02d03061114110007034000d042c0c100d0b04a008054040b006031510410081814044d030020500145050001020f40c6d403102e0340040d4042c010300902c000701c0d412100306044030083c550514 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 990136663 1250 990135413 990135439
    0xe100e07123302071101031112041506032406030b0417160615050306070507060203090f0d0c051006180b01030f0f0b0114040f170115030305090f0405040b0105 70
    0x7880b00a2a40d200c1d104580c003000414400750a640c01000342511402c400c2688111040065080351a0100300000320801080180c06010004410941c40341c4544111800d542e03420300e40384102c1d1710640045920f040c070001d0140035040144002404601d0b0404103100709401c60350345503403610b07024000605114a6039041c40308030b9a0386040e00c2075070301d054681c82c00403400f505115000e400600360b101036078181e04034041114100455038600c5013916032078161600d5000d640707100003544020542d040340c2c00741040341291040b0a1180c08280c100c169513840608400e41002400c0c241060240307903650349401020068005042280c2001101d03500000600d00e10b44070060307024100503019003020900c1e100c408004001642c0c0104d0f00d846080c0d0f294040041045880c003a94401c901a00507060209142002000f540d074001002c0008010000728030340b40160b8100b12154007580080300854000b082c81c01c0941004520b0702d4a4480071035040c4143e0509848561400c0410b000d11030240404000c00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 990137913 1250 990136663 990136703
    0x12060207050307080d0b03010c081602010b03030406090e011512181b17030918090f011a011b200f090901050a110717070c03060e100e0712 61
    0xda11815008020b882d590181d525101000d80e0103240c88050b041d16102c2e0740079103420148034101120f0032548031901b49030ac440e114400003565150200c011913407034404144494070240080c00041800c0e48560185a00340900b144840a058000c032030342e290b944885601170f03903000d24520100c0f0f01001e40064189010617250008079210040500700103e5445d4801d50f5160100d0107a0032540070080418070445c0c0c5082c0d0685034800d54012990050540c800c44005c2508070754000e070410280002c40340341590030762416080d02e0005042c07a174422006d218904082d60400601e81086504102c8540300c42010741d148840d02518664a24402022a401026903181c41642004899000300400c4491400d07507103441c0a0030084548000150803c290038a4107100f100aa9002e039600c80c0c0022070304005800280fa03550841402a00d102180d4040000820703030910031072030b842018134058401c80e0301c00c441140558400b10080309140c1e0244ca0b0800081c0907940b103411140d5408401a0038000041d510 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 990139163 1250 990137913 990137917
    0x2514030a1803020f07060207140603180a0c091b05220f17150c030c07030546120209030f0303070504031401050601090302040b0301090b0721020c07120602 68
    0x58200c0241c208424550002003541600303511008a80400c0d41354401261101c030300703100d2840349003850a061466458242c0180d6801903181030400c018610300710343c86181c461000c82c20364000251207000c0c0300d802e06500a0b444100200d6503480e112101001009100b4841c550842e50140e81684941c20501380302e0301124001c00d0007072001a0016100e4440000d00b080460481d805d500c50015490b0aa000c0202040c0c4640200164503055585a21803d0f5240d4404e6a0803010004208015151014404000740522000b1113820003540c41c401010904090740406c2811029107e0969240c810351012401764401000000980c0f24805a00880d1500001c9002e94501c1c0c0070201c01c01c5031280d4080050400c80380101c03200c4000030b4910890508031481030329a81c0c0081c48841050015080070b800020141001800000c0c01c800d8070749400001d6081901d0340780c00502000100c0410304145a50032000300f007022000c603d0451880003c07651240c0324402c80400002585400080c80303c81c0e81 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 990140413 1250 990139163 990139181
    0xf0c0911160c17030a0318030f1b020a09020901110c09150a090501061701090c05090418061a010e040605090106080417040b07121b03050c03040911032514030a 70
    0x680c0d0443e0120031066183d4000704200c41c000791400503a1210480b04031106982070347c2540700d01a00000c2c00c241140c5004211308000903060f02c0c545400016115403003100000d000061006894000700d1000621412000303004519542c0035103420b03c0b4942d83c9902460b04a40030280b48880300c80c1940216800704003d0b4009403684c0c1c5003400004e101074000d0b5641210384404181440580e0b291b8107444221102d10114a0010b84184122051f07410180e11800540c0807505283c001507420750b5450040d9400051744841117207011140c0c6c0055600049120101c81c000c0f6014031007181044040340c07503618144682401c01c80c404020406101502c8051108004813002c1c65a07103e0710b60810300a29401040704a542c0302e4104c141c146494403503800303000701c84080c0d21881c04205494a0031204e940181284840c280420040090801c2d440c1c843c200d10708070f02c000c0709501e032725000c0e11182c5c05105082140c4130b83d155001c1c03c03113465540903a90490030030103081310503100c1d1120300c50000203050481c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 990141663 1250 990140413 990140429
    0x1403010e0a061d0a0b150a1215150e0a020304020f18070e22091416030204050a09030f0f030b0a0e041403090a050d020d050a0f0c0911160c 61
    0x80185024030040d50440e0074983c1582e1011000c21100d5500a50303284800c440180c603842c00303680411450550440313060507000c0010203440c1d00c69100c0c00400300481011504a4a01c1084603058172907070568040c401c805403a010340306000364940fa034058110707034000341825000c1e40e00000040031942c1e0100005400b01000d800030404980507511a46202000c0d0307254004070742c0d0714100000301d03d4a4200c0381c1c041140d0394480c0003181e001c002041c018102018044440d1801c8038044040544200b107402d501c45540320f00e1f2009507242d40140401c0710070140c06400d0722414603074900042034008a44200c01d00280c902a1310421803840110020306c1c000700c0407980104a101d000032043c0107803407454091030058540e680c1c11b80469240a56a124071121982c11a406920420007881e02e241c0000c09580090111715017030406a407050308055084000300c840c0f10380021410203001c10000d80e0300140100c03040400c4036101410b0444101c0c0a10104540407249440503401002240810040140284 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 990142913 1250 990141663 990141673
    0x607060f140f1518090f01020d140c0708031b0405030d030606031404050d180b0a050310270b0d05060a230f0711162403090c1403010e 59
    0xe400750261068150b074030405800803030001c561000c007120010751040100400190718441000010031601d02c004020311802c0c0503207010300403680400e000402c82c0610b100c1c070020740200184040088801c000d003180094100500032640095504021280c00440c005501a905401d1020201c00d81c03042c0c0e00540d07090301903903100715a129003503045003090340c10300e8409016116482e244001a188100c40141559110340154440e403405007402d40c2c221403580e502c0600803601d40340031500c142d210b5600600010b0b000400c0000711115811031001810396500546001d105007415900703284031507903880c00d0895031654442140c2e1707544d0031071110465101d0309441051420540d080b0081004c7c0c04c0113155585404188040600050070f40c610440070101d200300640c0390076400700e0303d01c0380d9031144440e14482d5008180c07080c2e401d10103450081c4030034103030310810074040c0c1c4e80c081c8501851205002407604046140001452103a100e0f800c0d5042d00c2d500e44212408080080d024001d60501c1403014020 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 990144163 1250 990142913 990142931
    0xc0b340903020f09130b06040216050d02071a03010e07110604060609050c040605030414031608130f05130c03021c090b0105011704201203180108090c0607060f 70
    0x804402102c1c002c0f075081c038580b01480305201041204550025244441179100d00c0012429130b07115800c42c2024000604146244c1012290040c1c0c0303c1041d51103600c220f0402c0300c59641002044040c1821001a1003044410140c008940c0818040c0081000110b4001b90490740b2900580d50600d800380b08031183c44c2098104600100030718000c08510508000000704500f40030300c01c0320101c42c0c00f60b036040d18559454480c000c40541423010700c5040e000400c203809022480c0040c2d0020f0502076004107a8503800070601e201ca020590303000401c480500c16040100f580c3d5140d01c841da0700c1e10000c0107d8450f4800e00102e000344581c0d80e0103000e1003c624150780f8100104d43c811841140704000d10350f13069881c0d9005450407002203103e040308260f00700001e030003d10740d1a9895a500c030803000940c681c84050000480c250416050f90001c0d910200c2d0048810150070540724610f0300c282007030251800d11903540c5440d6182448030038059000010598104441c640c0000c681d03440140742001307035001d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 990145413 1250 990144163 990144167
    0x3060a0602010c2010141b04080318060702030a0b070e18040f03030e030a0201060302030f12071506080a1406071403161202030a0212090c1e010e210d0c0b34 69
    0x240d4220012140e43c00000c5605030340001108d0035152840f00840c280303541c51843d900b80c103101548030341d081700050001c000107032030410213100300a1140111602c90300c0c0440c001085444580e405611507100141c0c084e40210050001540140d08040d02020710195030406402030400303607500d8151072100182d0102010703070640c8001d094038400c4090314100482d14030556a6110b400480001201080100000003080d6405120449003489004192240c2e03d000c0d05081c40b070701101c16140641c80b0540703643ca840050001a502000d1810501341d0504401d00e0b070800b500000701218441c0ca034800c07090110794041c820f0014040c42c82c54055640c1d1a045400070041e42010039034042252050740466010400402c0d02d10320764501030840c0511000c140c507480c241d005082e140c18140700c2540d00c5220f16440d500300f41640300440441000f4826403880c081e91514000903415402c0085515800300040c070701c00007071500040c03c0100420000210318040c2081c044645410b40a1503444562a00c41a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 990146663 1250 990145413 990145451
    0x100315140f04050f0f040f0506090709051609030233070c080714060702010e090708061005040503032d070507030507090605210304050607050303060a0602010c2010 72
    0x29415580044800045414030040e43c0b419654500740c00040000560b4426010310450b90240c01149000f03604107031610382c00c0c00c082080d220b64030550031503041481300c1c03541405170b03a4000001040301c8000000c803220013801d440890000a21440350f1440d8000038800510b1300125940700d0054050f18a5885404860310368440700007142c0a210001c4000382060001ca1100f045070159120422080005001c1140940c010030080b4140054103c030403480d911090031640c89480c8139111010309007004010041c06201104480d010090f00304404c0c0440d84001c001d0360101500c01c141040c0d0041c0982901000e000b0b440004c801484000c074071402800400144101242d00600c02d85207020b403644040401d03618580130f1640c0040040c00c000c6241c0e0504c12200807500d40701c00a0300c0c1415150380000700d60703510890003500c07698404024010545071200084004003114002000025002c4501a0480c00801c40381c03070481c40e440319113a006a03028880b01014022801781049082e20b41400c000c002 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 990147913 1250 990146663 990146699
    0x801061403060103020a0e040317190b040c1704050a1e0c080109080406081005090a0209420702041806180506010b090105160303021c1a100315 63
    0xc0142201582008109030b41681c0d0054004031105050031500038000c98092300032020403000c203c201140203840e50303481d07014400b10081c038519041e8545904050790f05050ac054071a91811417811030082e004100101984040f841c00301c090f684506106041512001028003a4000210a42032444851702e0105c107191095900c4042e450700d50041900300e0b04891030090400300200414050320303000f54501c03513101e030402002d07404542c0c4072408641c4510701500e00c01c0000c2d4010807044014581810401c6550181c9120380d9441d0005100700c00d9111141d05506140080c2c0814100080b420f140c215401690090424014202c0d251241d1400e1003001d501501c041c0c0c50300340c9145001c00c098840c0070034142c010303004042c140d0904d030380b40040c0d0740801100c50511500704484414003200341d0400b045540640c40c01071311500b1001d148600300c0c000c0b043c10401c55203001c00c0312551080d4094288100c130015100c040c640100c1140a0b401001c0d4083c0490781c901a4050005605440c14003078001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 990149163 1250 990147913 990147929
    0xa02060d060e0903070b01030f111009180203090a03030b1203070308061002030c060a050a06050a090c020601050303040b04090513021807030f021c0b0a030c15020c0105310807080106 80
    0x100e0f0350380c4a65140c4a000340710000307013402c521100402c046541e44401001060080d10a50202d80d8401c0001c2e03046020306500d000841d0b10800304000300d14002d4010b5800060980041d455440d10400c4a40c40303c1003288010245580c0b95146402500d80a0340356981101e00002c403641c446850030058041141210001c3c0f1424243c00c07031558041c8003206803200c401c11000240340355103030b142c4200003928004100303074012a42c0b140001415550441031a00924403181e0000740c044081c0b0000742001c5058004a000c9d0b407040204200c0c4d4140a021581240d5182c4400111343c0c491100c800341106400401a600c02d00006241120054040302c10340a4000d94508011412072068002e041e4020f04040e00c9c10494409200011203081c0d030040046000001c18461005441e5a100c2204200c0d03a00400150003076401050006901040400c00c818024207010342401520300b1800c50042e602103044008068080c3c4442c1c1d80d2040c0d010001c064114181994030701600c400d0418000c000d42d2180e160 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 990150413 1250 990149163 990149189
    0x315060903110111010209030a060504120905030a06090314031603150b040b070606090507020f0c060708041e1512110c0c0123040f0521031b0a02060d06 67
    0x588500686000c821a07501c809200d505208000040d940b49003041c40440165400b0003045261b42c1d403e000d00700e5224401c107400245414141040c58a4601d030030880014482c11070070034001560002000202e19070301c401c012400c0079040c80e086a550001034180d40b1252804000d110960500b44003030000c504007a038040141e40a8007440c940040c480f03205012540c1c0c0e0400003441807038011002003544070b005040c040740080c0c1d0340c100002140e400310740d0a4010781040f201c624a8900500081c450b031003044502d0307810060340380c8806000d84218404c1401c0d03400d0143e030302c80d220f40c8980c0318500140500101039141420f00f81010b04090310354600a02c045140101c1d601d11382201c0d406440407492000010824181100015035210200c0800d400c284c0c120302d45803046c4071862a0003400640042208448201d1a040c14014080d80d00f074080c40022810306078070070b04036400000b900c00c80400c1040c02001d64900004003824003000c2e030000794000d00c00207a5884d1440c0170350807900480b011000b0100c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 990151663 1250 990150413 990150419
    0x201030c0206010515180a0b0405030706020f100506030109170a0e09041a100f2405160201140903010504050c10050f0a142503030e030a0c1713060315 66
    0xd0325082d0900500d544008901c04c102d9104541c3ca000e0600300303684030b805140312140840041d980c402142d00611038100c0014007805241820300180c001800980010441c85404146940d1154010b03400c0c0d043e50750b512400100c965a094110340700703041e003050305c40c001641007480780321540e071100b6820400701d0907074840301ca41420708400d5240329540242c244500c1e0f118040d03038208518805007000707182d060390340d001250b1243c40e610f0020091503640c420b80c0035090384c0462219084020300803201032280501c062480c2da90000c041c040303030b030f41d09181401035502c80303100058041c0500f05895825610b44802c03c0100400000c00441c0751000310750204080780040c1044605105d601c40070520b01505004043d5090b000c1e0544208140694031078a0603d208002e180b0014140b0b11449002403956071400340502d41c02d4445d80282002d6900a981b400000e01e40c00350030b01e07007000e000400f0300c0c2076842101c07401144003081d02c0022100d150102041682c54070014080c00d8101c40c1e444180310584800 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 990152913 1250 990151663 990151667
    0x7230a05011803170a020f0f090a090207030c020d170c0604050f0a02010225031502030a0b040605100e13020c07060f02031908040f020616110d08190e0301050408070201030c 76
    0x60b840c410303403595440000d040703032030136109044d01c0281c0718840198007806941100c0395014058249503100d400c001d5100c1c08a40c1c200005000d0070f500c14040d0394410041c680102c1c0e4405030f00c420003034056900c816007200070329140d0501d00181140d90003e100200702c907400c0340c80c041076842c00b4500840448412a050406840d12007409500090150340510460024401205c1c03c810450b00f540010290403980c82d20b9810112081401d001401d950002c108001c50f107081c800c1400010042e6000c00000d400e00011480034100c4060000030301040040312081507880561510407612829420f54440c04a681a0b503501c4406000b2000892500c42810103000e20002c161003100a8500140d80362035600b00301651580c02c0580103544d40300782d068034000903884030790081425420003c000800c0103583d05120484400c04c915480c860448100c00e000400c103032000351401004141c8070f080d40030b900700c0402d81d042540c41c2400d40d00740d400c0c034080000340260a00909841d5000780c03002c2c46402d48102007 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 990154163 1250 990152913 990152951
    0x2040501021c090e0a0204061803020112020d022a15070801030f0206160302030a110106030c05061323011d090f270705041d1207230a0501 61
    0x4490041e845006803460741d898400c030520302c01c42107051410000f5107a20b2030701c02c0b041d01110303421001900061304220507540301d24a609140e40d040e03810316501d801d59000802040d2204090111203401044c8000003641c542e0446055800b10481041c0c000101c08503c010801c810107110760070301481d440102040400d058a0748039075050b0f5035074441603007159034034080385405043c1660412030502031544c51000306504280c080d80607800650b2903000c01440201a0040c115400240b030b41082c00030000a40741d01e0640c415030310211030982c3c441400c00c4070fa9401400704e50191064540c1e94076252408841c40c0341c80c500f050f10a90b46c00e4410712403c07141d1002c040d40606059006011b0400040e000300041d60255088603100f10490841400c001e101550014080468042030304045010440d078035085c41144000c880761080e5240c0c280c680c90215803200d8030030040c034921070800514541080302e10b03550900010f20344107041c2c038495080c800041e6a41c1060f03508480c00c0d0710f0300d80302807102509000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 990155413 1250 990154163 990154169
    0xe0a0b0f0130090206030703090c050a081e16030309140d0b070c02060c030d050f0105040603080d050a02160b040614090d1d0301050f0405060f0f01050f030703082b0204 74
    0x1030b241d0b036a4042d11054502d0145202e040c009980d44940e20040c0c0e1454010b40c001c140c04e03603002c00e01c84444d0416a803000b4a035403000344581c0e20348504005084005c2030246207900d00b460312045003c8040d011a09020f500c2c000c110a4600b00900441010b40060f81e4000f5551220036040d072480219050050120011001030240341c0d4000000d80001c0c81015a6a0b015101601c014100340d281c4503001d02e50f8204140072843d003511035003084940740300c103008203004050844083c043d10b0f10b1600c6450b114811a09412134150300d42d0005151448140c04070784000540e601640d800b00c0c5a03040130260ba6070262030032107510381400c0c9007000d01080d42c1c5005018413200801303040c070000030b56400c1d901405015881e2a4948109481010540e000e1290a00c81c08800c60714000d2440d0620700355041070b50041a9a01c03c2854070180410041300c02031443c1960b10a0301d50741c1490030300c2d000003860803030303142e000402132440042c05a8100c401c0c00781e9141403d0006141450000ba050900e400383c0c01940 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 990156663 1250 990155413 990155447
    0x32e030503041806270207030e0604080c0f0f0f090c13090b040c090506160c05030d05031815011701020705120901020c06040506120408120408071103160b0d060e0a0b0f01 75
    0x2c1c001d1417002c1c8a43c01044058401c0c2028031503080c0b03c1c0702044503178001da40101ca03150001d010100040c02d05080304130001508489207405150150300054544c1440c6a809002e501000c0005102e900500101c45442c45c25030348a41442e03654400c031030f000e07000040c00c0d1809070b41000c03001c91403140154950000e588001348070505040740c1511108450103a44019604000509400101a242844116441703049550340760f5403882e042c21195412005010008002c0d8401c0c00c00000b04a103801c0064152181003a1010a4007828000f10f40a4010b090001e00769018405841d100c0c80c9401c0020881d0401c00c1e000e0382c814469000030072506000d14842c05401c4201001040741c0d680265032207a138017602c9140c075642404d544045214441c5e50487c3c0c2100c8600340095460203100f1990030a000091048005114220080c0544c48131107031184904460581c002c5070ba40c0308071446402c807074054036074030700c4490746450720325151000b40041200c854020008086945404e5101e20404000e45101c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 990157913 1250 990156663 990156719
    0xe06030601120203091207050d020105010b121504111215030f0c0603040609170d050a050613090201091e05090108070609140414070c020f0303032e030503041806 71
    0x40341c42c00d40654002043d422082c05030000f0031540740703070f810090130b01e00e80504001c00708800c101c40b000c0d0031a6410381000c0062841448072030703425001d08501590000145005240003485c500101d8041d100f520031807651403d000c20b00305411040e25005d47c0c072420984000d400400c0b0507605250310742c00a500240c600b6002144100100d040c8600115040f500ca010b0018041d07009407240c210000c225040ea910503200000d0017182900315009040e00859001020402801c03e0f000180310f641e940c030f01c0c0d01c041c2c0d0340340d0301840d055a02030820003009189008140c0034161001004119a60f03c030b00800e03103d07400320b10011a013644000748e00406c0d1900e60701c58a200d50b0404441d4903428098007030150380725444540440c00c008000007200e000f44000c4c1c8810024610074410040c404104510300b502940c018810050042112040b44085204030740300c44a448040c444404601c410581000c3d20a00c000500000c0130510307c82074007485410818100420fa840b408140007100009030081c40386418 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 990159163 1250 990157913 990157937
    0x909150105040513111c14070819021314100819030f180b040f14090405061803070204091202060112020108060108070509030f100b041806180516060e06030601 70
    0x2400304900121440102203210900e18040b205540c4620400300302c50540c607ca1007407000001c01c03c0914060030703090b0041d15021124007031408124400c828085e105070004110100c00d40b502c0d62028016200c480c015004070303c1c24840c1001100c2d00381c032412140f44141c7ca0f900540b0302c164071804010b680d150b0b0701c020042240c6601103408002403280030b11074103a5584001900c04400d40204014a90711400c24041803814038104414001c20f183c03903010310a110f0401c000a080810341e2503008400e0756440074076110500140b40b450141800017500b141c5415a410305210108000108894850b03089444a03030700c461813020601c0c03c0802c001c0c045035040011a079290700070000345074048420300c0c001e404e0a4000c2d00103031406c9594940d00c1040d03000b40503070101d600002d002d10501380005980034084a8850f4880c030b19441d281c0000078200c1680c812041c1600082c01c40c6525816400c60101c034038a40c980000300340c680d50984203200100c4c0c0404503100340d5051450949205e0181612060407003c4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 990160413 1250 990159163 990159173
    0x180124120c0b091f0f170f010b130b0304111207030f0f110405100623160206070506070518010306081504230307062f090102010b0909150105040513 65
    0x12032210303e5800840c1c0c0120003003c01c200086050300c80196a9034002c2c2c0b0762000c2015115000106810310100c08401c104040500d0303c050b614112401508180c1e510748411030403588880454115a90204000090200b44800b0044000e007800703045415216882d003004039240c0e00c009601c0001d08640c1c015083c0300100c0c00e0301c00800c001e5406000d40e131450f0480700c40000d0440328100c81c0c141291499050070700c16240c0c0b100303541c460f44001e0546c4101c10084051742741c5980c0a420311000f0000c100c2c074000303000c5413141e6058851450380300c404c95040d03080c417120282c8a030300544e1051220251084040400d5031080c0034001c11500504c0140c210307211800c0e80d4124448008006580303050403055034a80108582c001c850f8000d00341c20213141c4821142c64a04161001d2191982e61440d80c0b020000501000240028800c440401015940c001000040c2c0c0502000c4643d140e21900c81e90170000b50140c042201103000b4024180c148207a83c0b42c00801084801c1503442449041230700c0325180c0024 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 990161663 1250 990160413 990160417
    0xc02120d020705040e240709240e0a0515030604020d0204121203231003080301090b01110703030206070f1107030f0506060d03120b061b01020a0807020a03080708180124120c0b 77
    0xc002c2c64502081c580340c03268554200c0307506500d46100075900400914040c0d100780741c43c4ac40c4c03004480481046242000103070440e91001c102405819000010612542d00c43d030403212805d505800c1035440f25550303141c07440381501107181030f103c000004203111f0005200e413041c50250f1003810b584c1e0703014800c1d100d445e0780c98001c014030140700200c0c00f03580070000c6240c4001850080c4034030311000c5040b8840200040c11614100a0392115038030418003800001d0300070505d00d82c1725900786003c02120042c0e800884d8102c80081560502d401a95004020b000d4032150101220780208100c80707e41d207541d81480850903008070081c000035102580d2000c1d00000b60010b1000c184000c0901e820400c43d0b84035030420130401c54070f510703280c0e42c00102084503941000d0032070b0b405071150010b8001c1c3c950b240c901821b0140c004050600308500308000504010015003055022140038000f00454404c1c0d48408980941d2400041c8022910f1000002d22445205160545035030014441418a14101400c0826 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 990162913 1250 990161663 990161671
    0x220f0603050405120d0b04050a1a0f0d1218031104050c0a1d0303070501050c1201080703031b0c08060906090705030c130515060304150506040b010f0c02120d020705040e24 75
    0x24541b80c40084500da91a030007405d001c1c0075091340000e505100e20500039441c0452907646402440c900550764000d69030b500b0100780f19500320104121142c0b141c030040700e90003042d990a6042078080d020200501c0b9035403e00300c02c108415141001603803a003c40072a0343c2d02500120200145c0c2110301e1100401d824803240c0c000140207000c80c3d0404026a0391242910004c68540d00f140801042e0908085035840c941c40c01445400013400c0c0e02411928002c0c401441881240300090003154144100700e00130680388002c00005054074014200800c0842d143d0a081d140c0e420765214103100410342e480d010622031000d000051008054024280084014000c020081580303540d2405200c140c41d2901c01c0254850340c46002c40c1c2209a28040e68a41100c0300030b007500e0301541c9000c4034072005980141c0b4145203141c480c148485120203510001c3d016071a4010410300c1409005030700010b154002413050709450381160144011400b00d144a583c2d2286280819800e48140b01c0189041003070a040300c1d00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 990164163 1250 990162913 990162937
    0x90a0c2a030f0201060f141503010e0c072f0102010c02010b060904090809121c0207120209150622080f0304060f022119090e0a0b06220f060305040512 66
    0x8a0703842c404c1201c04002640240300121044503c20543d1030042301d070f0031420b0f4408070481c2c21135042401c400741c129001061040081400101d0000348002500c640003040d010701074404c0e0011001d1038030722071900700c6c40d02e45000d582004032a820560041c00340c80603078100507040c00e00b4064550200009407040c40410756440c401046105890f4480840b07240020000000500d0802d9041c80d1a110460301284c40d0021500700540174004140c0c0c880591f07800580458a030915030311380c00940d080c0602c080305195408134001501400707000e00310705070341e07007907400704420b03070a416500c014007030701e90403080c8240700c0c550000c000a104003802114414460906403044a030315078841001c90413078099802c50800c5a503401300d80100c1e8668410131500d1800300e149403030001f1742d00d42114441e245402525105085484001d148840d0311620140d416101000303021540e04985000541d21a115501603901c0340106104003040103130080c0a1240100c0d4400c0c020600821b5913111218650130001c02100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 990165413 1250 990164163 990164171
    0xc060603021f0816020307080901050c010524090103053406021501090c0215061504030c080607020609060103060c090806180c0d170307030b090a0c2a030f0201 70
    0x562520403825698100000d42d000c400b10300301e480a82410300082c4810f40f003c000d01481e09407182d0120550b40c040d5409903006840d41820001600c5a018145803495250302c0c00003040b50f003101110049800c4225031488080402d01f0205000c0c406509000240003940b0840070f80c1e6150702411040b40100b011080d808480302c424100d10710100415620034130059102e40903482c10703400800c891900415a440c070400449405040103919103401c0c66541e22031900041c001191078807050303107050100e0790031300340903903207649900d02155191a640541d0f110f91094000003500a800003c00b140501c0c5000000c0906a10b1a5994030252407015103050400c4a039800005411100700071550244000440c0d0004c0815140310240c6481511115036104042c2c11b125100810350789181c4500c40401c7d510b05070703540c0c0d8405400f079001e4000c2850f2290421a40410031102072a0340c2e0214a901c0b04564980441108807042903211442c42c40707480780c00d143e9000e100f43c00030b4007071b80c00150608020300000c5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 990166663 1250 990165413 990165419
    0x31a0f0604142d040f05041e08040b070303020d0b0f090c07020411070303050a0b0306070c0b2511071e15181d0924180706051b060114010c0606 63
    0xf902c02c00c50324101001a50300d0402d4000a86040c0c05880c5180340105c1040201d40b90541303550034144c2125600c07541c103005400011043c0241d01d01150098400d500c0460381e074032a680780c014000e41c00105501c00d09071900c40c401040341b07028505018a82001000140c030b90702d40268400c1c081d40180c0080341c0c4035546403e840003a00002000d0081d0398082d0300c0015a500d81421410b05039904100d41c203110750000f000b0440d180da045229205807580011010105e0303503c5d442100c103004a100c40010704e84032a01d994010306903000c01c0c0510042c0075501604e003166561040d032022092105000c4d006d408801e64180702007446220b40b05030340da030346240400c0c00050481207850b840740707181c00004541e1100d001c0f44600c0540ca00400350002e1588005040ca1aa4030030041d02034141c1d8000c18107118058004250181090408484040e6803d0180c401083e910280645250310403043e1200c4003071058110003200e00c01041c0c2a0407036044e03003034091500c91080c0044440d8444a081100e01582c2c0708004 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 990167913 1250 990166663 990166699
    0xd02040315060815040b16020f03030124050726090a03080a09050f030706030c0c05011a01030506101202030c0d11070b0603032d07060c031a0f060414 66
    0x200041d07210188000354031420807203000c0c200b0105894092540d41c1100a00c80002e460001030f5520401d000b201e5504803650b102c0072414402421013500540c840032001064601024000340c0005120f0030380d8810f040c825200664403070007400d0b405815042c0b015205000700721032001d100701b10940e480341680f803c030300e00d03000802c011410b8100380c07044040812050749090300b101c4204041d1a046603c1c000107000d00d400295901d1007030090900300b40e1104c0044c28418098218401a543e1200c000c0c01b03103103811401c2e000245904011036001906041c080f400d5414050524103400109555813603284243e07042d0301c0c01030340c070250441c1da20780d004003e85808101c044c4105200101d10a101e05e0b03403500301d4280711190150103487c1922036002084141c140700807011500f0b06500c07002007070311460204040c3c91078040c000e03403e02401e41400d00d901b420600f0340c0742d8460030702c11070170403800d464114a0a0621400c00c1c00d0030300701608008101310a000e0407000300c146400c0f003480101150040642c00102d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 990169163 1250 990167913 990167933
    0xa11030d06051504030c030204020903030405060c0f0705150304060c11010f0603120305010b0a0c08070f050d0f1e050f0d180b060301090201091202040b0306010602030423060f0d020403 81
    0x4030090359503988200707224078500b00071581c1451440c82402404c041c00d54a4101c05940e45100084c440c542c00907120800c0c0e2018400d40d002030200505075038035207960002103501d82e180680c200c003403030150070004100792500803031075991030820144403821940e641e515403000f840981c19075814040c00380b841801010b003d008000482d80c08020210700c080c91890040b4030420b4407003090044c9810a00140090300240040c0e4a80610300e03e00840e83e04128140b00c81244039851000d019904800450400d202e400500250901510f6942d00d14042c2d16403811200e240e55129110781e103684e5070440e034011a110f000075140d0142c04051042c9000034a41c10201180d80005010540c509051081c00c00e200b007074103015078070000c00d6000f4010410290b000a0545880d8026a04003440d642c1d0404150b46a03540300108000f809400c07500340303584542000c0d50304e400c5842504a0500c00144200b0807451401113602c074041c010300101e01b010303107840000c50070307801041d07a0301c4026a0a0000201003800215 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 990170413 1250 990169163 990169177
    0x60c02120307031a1c03140408030919090f0c020c031605120f0f0106051509150f0c07030308010515130510050c010c0302090a050409120806030705040f0b0a0e070206010b0a1103 78
    0x2a0420b0381c94034035025000807400d0b240c2001c9103a088c40b080213001004070849404950032107020a050401a241d0924540303550071030840c032031401c00c4103032200d40c2a44c4401510000d50f0200c54200340108105940d8160307048010480c01d403500340820250400c0c1d03241143d0b0186001c155401d18015906191070a84500b60843c811380d15047e00700403500f01421a85d90300b0781c4280c149c920703041101d008141240c003192240c0144a40015003d803001c1c0c1c9040642da0810994410b031446142c3e6405d00500c000d00a00800d8840d066940e95a13460241e400304441c10b480781c051040011915090401c041140940c0d00b1506011080041c0e0000d000213208d172040401180c0c07401a155429901403003c4940c4135003240340250300c1d03e02e0300004140450205501c0303000c140b411090a60340c0e14042410440a49e011941203818126030384810041c581040f0f840390307c1030f1505080244e0b07035044071a0004042c2d0303c0360007680004005009010005009000820b82d41c00d100282e100da0041d8240740d940009 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 990171663 1250 990170413 990170449
    0xb06070503090405060108390c010b03060a02070f0f060915051e150d03030609060f090b240706180f0c060f020d050c0703080301030b0103060c02120307031a 69
    0xc0c01c42d1480c40d10744922500000300f0b1070000c0c09813078600450070300402e11580240403492402556100d0940c015001d001c1c1d521000d0385030b0789407141c911345180a05184002103204e801140001640043d4510a403041c071900036840007401d8036580c9070f14202d2031000d40141e80c0c041e04c0307250391703004106c065440c0200d0540b1101c00050f24030388003114240410b00340307404820054189c0107224044909a1500032516800c07124649105020300c1c080e8000c012640c0603546103070a20300002031700d0440148150449060500500c51144510100001c0040107068103400700003d501100000800c080030b0310b0900c0c410180041e40e201507503c841400c3c030300e114044a41c00f04269140c404c01c01550b0b101002003809040144c901100558080d40b12140d000041040007c0840c0424000304100801402160000c030302c16600d5841c0d061a907408902400103941ea02d060003070541d51184000b42c00114401c03c0c603001811600d0b40c21048000c1e110201000c00188250340c0504565528502d0044481c0414 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 990172913 1250 990171663 990171667
    0x402070b09010b09060d060b0d170c0123040f150603080301180e07051002031c05181b2206061d01020a0b07050c030f0a0921020d150b06070503 63
    0x800700942507440441e20035024540f88401e200041d141c207190b9008840d844100444c0310815480481c01e00800b44502030010000701a0b07400c15444050700a1203a104810700034012010211a41d0401d200f10380d440382d00f01424000060041034009900f085114461544030401d1801c080107202599402c2e00b058800c070308000010018425240104c09103215980c0d01400700c84807004c101500c0e0750940c80b0b211300991108410441d614428812510740c01d00340c00a42c14104d01c3c8640e10740080c02c08071000030959182d42804058104001200d06010f03550028040c0e160440c1c4040c4000c030320340300b0403580600e44a5a4440d0032508a40121400f41c8420782e5040b509010400154902603d40e0488031b0654000107000008110380071292075020a03282401075407424400800c034030351f1186016081c181c91003c50711002c40c640c0540c0207001c070340210400c1401d0041c1101040c400b01f906d140001c0d441a01d041680c00061000161041c11080c80600003c103035420802180300c41d030241d50304803416000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 990174163 1250 990172913 990172921
    0x7051309050115180302010f020c0301054f0c0e13020103060f030c030b090307140321090a0303090519030903060f0b060a0804020321031005040c091806050402070b 72
    0x3d0074410700100c800c03528140d5480304c0136000c00c504100c0980400b9040040030081424454000c1100c0411500050002c12191804201601c0021100c1040c9003664002234074851000b4660103015a0103d01c0d000e40b0800303642101c1d034281d00400303d030400320ba100c7c0700e00100003908551240d41311b1055001420651851409200040c1158000e411000328489454014030208034020216802da03540a070384e07039410380c6030310386400d2441c003c080380240b20400140c080100d04201002a004040c070034018040604803c480483e035800c022140b549095104403203c4011a100782c100e140c2c01400360302524802c4222200e500003018107c04143c003c1200c540c820020000144202060181d0a65017085500b141d100012207620481002100300305440000c03a05541c0c05214444000c1003c1603010854040210265000d07001120100920325408100107880d0415010381400d612440d0f4410040c80e081552411300040780c0c005e08140a640e680011580740c542d4801442c220303000b001010224a8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 990175413 1250 990174163 990174179
    0x3090306011a04051c02060c1b0a030b060f041506050a110102031b03090c04050a1416140d021308010b1509011b0f051507090503190b070513090501 65
    0x26041c0c2c81024040c0c0c1e0301c403051001c0010b0078169825035078200c559000314081041d41e00c41c003004030b4401940c41030b400906d40c2403001000480c07038881181140182c0d01d0655040810009490a00c80506031508000000e122403804003041c5004c030030020700004040c815002c414551038460341020340030490000742542c41a1b041813082806c02810783c000e5241d80b03040e81c030526060320342c2240b41c680d403c40800801d190544c00e0140340f01da900c2c0903100700500c4c80c1a002c1003018101185102c4401d06848000c40c2c2c50040014640c40824626190703084102c403500101c031081d0340600400d51a441d424130400d510701100700b0030400105800e00010071400e109108200051545580002c0725074810014040503980000090121403070100e5020a200320030b0804848070700e003d41c80106a80941000800146404202e480c098095551040040c5848170141a9134000803144e0380c0d00c0b55a114040d10000b00e50076002e9070300c0703041443c2450500038106000600314095402511845840b5401801410 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 990176663 1250 990175413 990175423
    0x4090501060303083702210406060303090503370b040503071a19020d0e032809080c04150f1203020105070903030c0327090b12030c100507180602030903 67
    0x6610300c0145c10400380007110103d07035818170b00c0d8102401c1d00400c5524200d1800300e88080313400b869a1b0041d0803441c1514007080144801d000803404075844100c082800e0600240c04c01403c01c18081d54800a19130480d184040b142c001030f05031400301d0f00405140020109200c280c0128456002580c4480741880c15000300e0190814026101c99440c0401c200c039492401000302082c0b840c1d030016600c0c5c0c4810140c1000c0c00740f080f00c2c000d140c03100207400d50781400c018105010050320490a8081604000b0045031408054417a640c60b0340e11484190800e40740a80c410001041c01441101d2540d5841c0da0318099503440d0707480b102c413844240301c04d4002c4c50340a00a8903841181841c22880d840d06584c1d000c0c14000100300040c003040144041103101c800286807004200582604a42c1081d03500c0100b40003030030000032001c3c0690501811000104c00000a45620108000c058404403d0306603181c80140801000702d0704100c8100c032020079180701d181011000c0e22042d40030310b40e650850002d041c548 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 990177913 1250 990176663 990176701
    0xc030306090703050f0c07020406170c01030b060406090b0c011d0d030e16030f060f020f090a08010501032105070b040305271e0f0a08060103031d031b0409050106030308 74
    0x818206000c100c442244c1400705d035440100c0c0c910041d160320060001c1801466603421540a095003100c04021109c000203070304080d034100b66010b11520102c1024001e150190f0b1003642c000c0703250801e003070004c00161400383c01e5000403400001409220309030401d0300040c00b494540e2050700101c3c042e000c22540340c007808081611602c000d056030011648030701400406884081c1c403564101102401300300e0320307030840b204031a4018000e544600005c066107140d5801101c2140c46140d6622000500034410300842e8105c13034000341000090b01d00e004101401d0b4a0141101082120400c0504005581542c41500803406581c4141e1078550042520f5565a203200c09945200000c0c03580504e140e40d244e03000c440300c00b03080c503441c12000001c402050641003407403c1c003580305070300e64004500c200d0300140e128100c034029510800031072440c0400025020154071241e4158201042143d01d004980d9100ca609c80805040001c0c1c0000c95100d05c0d0071180940c00850018102c0c0b0240a81c02c02091744208034 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 990179163 1250 990177913 990177917
    0x60d021819060f080705070b010f0f1a04050111100507081611100b1804050f060f09030f130e0a09110316050409031107171c050901081005060c0303060907 68
    0x341d40d040800107040303015031103084800c100110300003c0340503108200f42d440a560000c0382e1216540c4544440e0f405030402d010740f40c50b1800702a000944a0b030380e41d940e0b41b00c4900320300d042807605040500443d0410010185543e2030700c034101c3d03400c240b8030381442200d00c02c0c0a1540c404005003444111002030b141141ca201c0704102450607c0100d0380300c081000b4851081d01080010101200400708952050141c050074000c001c8204100500401043e4000b03903001b45411741e07410341c0da5505112280c1800751a00d821650003030050b041100043c1d0010040400e0b100c0300b44140c3caa641c0c07060303135400ea412038420418544070807030901002543d034114032000c08200e002d009811a038001c0d8000b2526140303d45880b50344c07500d40000a150044000c0d2064181c004183d4008c151a156034000400000307858039004d108140b16075003c0c031581d41e440401c490340c0d5640c06141450144c01107802e5440070388907001c482441703100099281d8481008002031401c20010b1a180c0c5414001c000d40e6840081640003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 990180413 1250 990179163 990179209
    0x20a09020c191104090305090406060221070804091b0207052d040e0604050a03020c06090607030e150a12050109050f0708070512040c15090b030a0b060d0218 69
    0x6070504011032011500710909525004840b8a4105158424008081c540d002850712010b4002c1c19403160080103100c006407000d019203542c80c101280d55205860900b014924004a0f94098029420080c51202d0003071903e641095282d40202b4100ca2a629641c5442100d502c00016500d805105150042a00b103c441c25902c1c0c0c03805482041d64414410040d2a6004e500500070580e6142d00c83c200001d0114212200d030315107803034501d5403040541000e40140c454040f4401c41403600030304030f032b09026001c1d20640c1888880d65042d10307082d03028120658056480807100c10041074410150401265590390b800c1c1c5100d125400c1e404071441a004a84818100020481181d1280311000e8104040385008000303031b91160421621800784104840e800e01351b12042c0f00034032502d041008152040344081010824420000380c4041c5641e12841100d00c2d030038800211410202d6210141c10580608214901448030030400c040368015480c0c2c09411480343c01444082c03e1609a2454640d44031540f48 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 990181663 1250 990180413 990180427
    0x709031a01030303200d0e0a08041e0f081902040e0a0803150102030f070807080708121b07021f02030c010f020406030605010521060103060e040c0302040c090609030f140613020a0902 80
    0x1aa8442c070b42d40d20b0b61b80d546500015a031040e0400209101c0382d00402d1881d203913a2100034880e00180020028204d580301234070003040d4080301d8043d44048411050091460211805000f4551030400005076840b59a4640348140b0010a106000c0542d11803500e0f95030383e107401540c0c07140091481ea11701d811503109201d040401030a5004407a501500072100343d44481c214a000b081c1e0344206c44004085003800f0030000030304507038004a1030044001c40d0f105880d4410040181d50f40c2d01540c070019510160f0641d80304400411000c490a9561581c4140c5c0e24141500202a0a43e1551580c02c034540e58001010041c2d15814400c00c0050708007441d2451501c0b2110612002c80301130800030041c1090f0000109002d60700a0b402304004285600f80c2c160f0500d01810f1162200801c3c0c40141c1c0280d0522071296942840781040704159000d80c3c40b01b42810303007541c0b0740111360049000b0490786d00b01e0350318580484100803c40148501014280f1071604043c5106001c0081200c1e4403041c0b906005000d03007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 990182913 1250 990181663 990181721
    0xa0b1e011802091203190f1e12020a022505090a0f020403140f0705010810030605150307030b1b03240315070512100308040e0709031a01030303 63
    0x100d04660a62007105004011810004000c0c8602e452555100b82c060130b040d14840b101002400003464600900b07101c40100346025248070480403011000200850403604442c0340160800c0020b0800745445050f01e0201510030040340d0100d000000940c1c4400501c450041c90960341c0c84141220b01c590700c00d00f500d40804681d000c400504810100c1d921805040031151466054400940e0043c030400c0204090407000c0d0740b03031480c20315600403902440401240e81c5d401052480d0080c10681c007502481c9103581c94403001010044d01109111075201400c44646e0b40030010100503501941046042d814090340e001280312015007901c2c0e8580062040126185c0c02c80714151030a20780c21144d030880c4180138002030408899080542c0801d007003100b0301203d030703901c003015102c405400c40034181c1070384502c02d104044a48520000742100710820050001e007001e054825000400360406d650034503269640c203d50701ca8010349100040d00201c0040060640c1402061840d010702c60a200f4090500c4e060 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 990184163 1250 990182913 990182971
    0x1215060c05011505100f02190f0308090c0a212a060c0201020c0405070219030201020414010c020d0f1415040201080609101e0f1401021c0c110612090a0b 67
    0xa17003842804011100554024070260140406400400a04201510700031000c03519000d425000101104001160a44000b5064505003001008011801c0c6090038201d0900d070a25170058078045e8410241002072201038400d442148000d51190ba1780c1c1c807240c10741c210710071582d010710200201d8030b0b0b2020250342c000c15180c40314103040e100461b140d0b0350301c903041c0e01d840309010300c00429480411201e42410380c1075002e8010b444441c90301c0404c40b2548801190014000e0401039070104003e80d000c0300107008805d001740c1e07491085e500c10600158440c540c900f441d10102103c84502c69403c104811982c0c807c0405522180c01c07552280306050050cc0c4262402c0c45028190011111b0740601c0069075041d00d6800051004680103041e1588030010445040302c040e1441d80544101c2d90440c080c40b00a032480501611117075150340941c2d0854860b4003803070502211098010008001c4944a01d04030940390340710304031080c0284084030b02860702400394a0300822001c0c460303812801c600620800008 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 990185413 1250 990184163 990184189
    0x130b0c1b031b0405040215070f05240a023f0a02070b0601030e100f090c0e0702060c0d1b03050f0a02030108031803030412120201051f061215060c05011505 68
    0x400044c250749901c041100d84800f01000610000c012805208010b000d40f403001c0c00e0340c8100103403140400030707184c11010345000b005140071101d100800105120000c0c0d014040c1e01d41844140030b40f1150901a10f5041c1c043c441126030030502d4010308164100100c09425000201c954045140604a448880c003902c07014018904054440454291481081103d6119110b0051040244040305180c0c10f0040c00b0301c0c90300304e6000d01c2e00c481c0000c0101c4c0c43d80321103204a9580e0080c02d4150780c0e11402c01c450380d200315a800840741d900c000b105409882406100c1601800380c0b0001910708140d50380340d14a180007000302c80300703030300420050020007400f000380c0d0880080503107100f00e08d12060340005d09500a0b42c100108c51401d40c2000300602c40345442012601c0d026400070442c5484180440f0040040000085404210030908010303440c4103800c86041c0b10846000050110008030901410b1001c5a000d500007450311303480320003070150a01c12601952140c10031003c0d500c3c80d08000c0303816021400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 990186663 1250 990185413 990185419
    0x108070e0f0f0a08010f0509150106140f0d0c1805010e04110d11030612060702060103031b061505030c090108061f0905250201140c130b0c1b031b 64
    0x107048492502e9500c2e201c01c50420041c005200f040d200d20a103402000c40604040c0f0160a010100d0b00c3d0340c002041d4524105121415001c042e0f09044040d610030b4604080c0503603403a02000204111034040c0080c02080f61000390109080c0c0513600c1c010070006254986600442c0310312404c00803603030404049038a0910503180400d40600c012113669943c050921505841c601301748188a0508011000b18450a8102d90f85000300c20340c52990b40c0e850300e0494460015a000034010b1000c00e010704480070301a0103100c0c01c00360044c40c2e9a594000d40d0440e21504903852080c000a01c400c0c6024001c0c0003402c1c4056a140c42d140d0326010103d55a508042e00d10100714100c403c2032000c40304000c94150180104031380c01d0009050450000902d03c880b10102c0c0100040d41c288000814418007032103a80e00201ca42981c010f880d4100c140c603080d840a0768911818011620022f951051000542903045c0b03604060314460080c2d60b050000d109900c507469100381c01240c000e0081500005504260300c9040d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 990187913 1250 990186663 990186679
    0xb0f0132030307020402160b0711060403121803020c010806010c030909020d0905030f03010905012111040e150405070807051c08070213020c070b0f070b0a09021c0b01050108070e 78
    0x6480460308502c03901e03c000c0e4201d4000900c503202c41c001c0c454001c82c828400d661641055881d9001203803864503002901899400840200e400310344103402d0084201101200041c4480300310840440c0440031480032405608a0b007a480c8241da00441d07110ba02c0303002800c0c500303e141105d40e0014140811401007803415a4086050300e0034044543c00110420340c0601241d40d035085441d503030100c9800910400c0c11880c10480045650f00e000900484123800c24048a0000d0115541d00c0d0250705802c568503411503580e074150201050100021403507423442894504039400c00d81010380c01d1050641002e48258441c1c0e80400c21a1030350302849e002c10001c543c000d00b0301182d52400300041e100711034020790720a8000c00d41c05949a0140d0060503450f10070400c45400781c0d941c05160005029074014103007602003e0041c0f001041d04104190f03809540b048000034910399030350006100e24140484030102071b42010720741e02005a020342880c058807003400d11000b6440c0000c0d00074034640c4100c0320503019940d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 990189163 1250 990187913 990188009
    0x2011d011815140c280204060305030d18080d230a0902040e0f12070602070512030601020d0806010e0111011d010212101401031d06091c05090901050f0a0e040b0f01 72
    0x1d4001412950300031f02c00c1c403030f19640b82025540c0760480303402650380c90f1900a01a8074040318401d400415540510520b0625803682d81c6080241004100d03401c582c0204004003401c07004400140d485604420400034201d0410300600049401d09000d904040c0d02a0340601032078800083c0c4154150150120300f0340d201003a10346030001e4003e40000505038862030008032980400710010303503c00d0b04d0030fa00f12130250080384011940c0b0001686c900b4082103025060700c980c0d51242181d120041016000441c803600142405055802c1c603120303d410a07540441c03000b402e100c0e001141600041042c4540072030320b0400503c803165141e140040ca052503130b1051700b003c0d034000007c1d0492400d80b8100a49401307140c04200d0688031308150740d1240b1000d140d82c541001690064068070104c540c00b0381003072010b0b82840e09006500780c01d83c020545c000340b08980081c00d440c224410360b1103584034880c0307031482c0e08203111080f5032518180c100c083c21009010f411040d50701903900c03542490f448908080c1644030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 990190413 1250 990189163 990189223
    0xf01060f0e0f101128020d030c120206040b0609270f07080a060b060a0f0c0f12090312090b030a0f020705030f040f0e281506030218060702011d011815140c 68
    0xc914004ac80c65540c0409000720320f40120b03070248900e000c0c0d11050800c0d5a020100003003c00c08840168151800080001071800720a051140c0769100300110717244d90101c007104031301d008410343c0300c4807003640813600100c1088101e02440f501c401e010744240741420048100902082040300801082209a40c40c56007448041400080d2080d001000341c401e10a9146000784500801e00080d928402a0465000c46901c6401108100c1c3c403000c40b09411603c46041590150100000340201d65400748828408070b5402c1c0014440c440075190850340c3c0d2031405881c0c00e1450610341c1b00c07206540c4994100b10600c40310200749441c1c0400c08200380555002c01c0800b80050098204c02001702e170008601140c50303600360340180034000d00154a9481c100207901001035611507081d0084c0080c540616429400c040008170300f02121050504417030350700600c0f2000d0403280c1507a2000505407001c0c588920110b402850780c010806503858014548002041c2c203075a00c210050301888680e0030f0b40003c0007411 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 990191663 1250 990190413 990190427
    0x3091e0303140f0615091011120a020a20060a08061219021f022104050402030c0a081f0b09010207080105040305070b0f01060f0e0f101128020d03 64
    0x108401652085034100790243d42c00514003140c1c0b450056520916041685407050140c0d00782902c021b11030091207078041381c1284c801c4580140d1000340d1049855405c002046600904500c0b41154028418103031613040016a040352241d8050090300c0c01448aa415100c0344210b920840d40781c2050b4100791284004204c040b81000c0710031600b40070700b08500451018030b910f2003280394022036032512603d0000d44503091128000b1078801c0540c0c4041d4070103c045141c442c1c5400e03400126080c06041c203541c0c44c0402c0c141c9e40121a00070110380e0002d100310080d0f070094180c40e04150800701001c81c500c1d4030f22070814091641d0045421445000c07520035001c0c2e20801c035080180c08144000c0c0021304041c540a051600031520403680e0041c0000014074210030702410720b040300d40c240c1d02d040025103440700984113660030684550b04201109840007140e111002c145212522039a5915103044081c0c0c206403d0041603840c614507000f00348006000359030070210810805404440840c2c08101c5440d060301c1034 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 990192913 1250 990191663 990191681
    0x1b2103020f0a111212090d140d0203090109080609250506180a080a03080c0a0306051002160609060c020424030605060a0b03071b08040f0b130603091e0303 68
    0x82c454021039204000e00341001100c0000295455204c182144081075282c40d10100049000d0909202c0d003400340c40c282d00c6640a841c05178484400601202e680d6505158401c01c05401590000030315061301e59200e00035030300500b82c2001601c014103104442e65191101c01540345000c07017811000c060040c0340c034000d07c13008280080ca0b860351003580c28180c0003224a00201a440fa00c0036103000034800801180d20700c6929415511044103036104200310743c0310341007240304004141c0d40f0700300480c1603194120303031042451145d002844030410001c41444c01100980000c801c020050500301300139600030b14440c201c1035045401141028025684221000f030700040032103403011404002092094950001e170291005545110f030194854503407060b107110a48109d00022800303011000c4c42c103e004a05244144240080c0e40f41c01e9540080c84901216904103003c620030001c0c17140c9698050b00c040c0001001c40307043c00e00100d03041c0e885221000159150725895003540480c1441054820360003144a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 990194163 1250 990192913 990192943
    0x6021c0c11040f150f14010537020102120711030a0525080409110306220b10052203050d1209050d36122d1b210302 51
    0x1144580780070f120a13804580c4104c00c9040f40444010032071070003410600311140e030183c5a0030304c2d2441c0941f4090040c00300100108512440880f03510b9164a0032060107284540c40d0b001603201c08100801200d0f455015141c40144000d46000710754218010040c0d49e444134480c00c14640350f00c118504500411038030940390740f200c19031460200400c14420041c2041c0c4111034000c11000c1d892001104103440140c40480c0e0080c407969142400c000c2403a01c3c03107502c44038880c01007181c60104004c143c00445560054000c20f00c003060f2007081a0301c680d29006140c11080c1c040c05800d18503110151100a0b001039401045090000110a520541c01c40d0b05440c1d404400c50784080d510110003440210b1b040004551a00054002161481d20b00d00e00f2642e110980c000142951404420350041c1500d0701c0119102e235007501c60500383c01c0c00b85001c96030049038490a14a6540a880c0a90301d19040c2014800703115180b20701480120303841b0301c1c0355252010074101120510750505040e46001c10295070703060 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 990195413 1250 990194163 990194171
    0x215010e091203010f1401020a1b140306040b0606031e0709061403160f02160305010603060b09152407060c020d0309150b12030409050106021c0c11040f 67
    0x14020044080e51449402110160b801400e03064800c030350700c1c0c48207100741024041da0030300038042c01c58000c1481e4484141401103da03c04015961050074004c0c11515401d405411141040000000e030b400d19070001c000c07005444a403806554111004802400e0607009c1c00c0040f001802e81081c5010003546401144242409882c11010040600605001d33080000c2c3c1c0b49901c010050310880196030051602d02c00d0079000202403041180ca00065400d20740071482032a480030400c450740340402c00914080d4001254584c11130900000b40c45901100c14040e51600041019040401c400c080040f90216880c06502424084002d036420000f0400000308500240500400c41c0035801000c0e1240d658003900e03600460038505804070742050750041d006405114018164880b15441207006090007001c03054400740c51102146541c2042d002645840c0ea80c100500080d0303010800c01d01114849240a1488510030000425005005000800728082d080060751580c0d0385400c440790049299100b04 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 990196663 1250 990195413 990195419
    0x60f0e0d06051012111e061617071b080a02011e1707120606090b2505030406051309110904021606050709050a0803030f1311040f09020111070303020c10021501 70
    0x105110480710424410100980110400112200344244016005100d281006140040d00460545d110802c45000303d103c8103109e82001c00c007000d400c1c1c56015204403241e0f0090080d02400582840c0c0001c03a107a0700151410700107030ba010f50407152403021001580d90b114901d100c00e480604c40014009882c0c0420410090080c0d4820031a642d210050701007030054503a0b8100c2500c0485542c02203041040d010024081c40010b50704651074501400300e940d1f40c401015445143c1542c015400400000c1c000142c116408000d02e4240d03805010621410084030040b40e06194107449a800228055174000c01e0070210102f400181c1c50183ea00b241c0140524608044014191000d50088522030409050046440c000000980f8410007855102d0210b50302c907441c1e0040c2020403814101c43c0d920303908da02031816403102e0003003500c03428562201041d6079101e440090001d0760a842c14410380c1c3d01000c010000b1950000c1d102c201d80406480c5c100782c0c0d0079901402c0341860070740c0c0d85c09085c2d5107183c0000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 990197913 1250 990196663 990196673
    0xc070902030c090910030b0604091a0c07211b0807021e10180e06060706110d0c050702010207030b190203130501051807030222050f01060f0e0d06051012 67
    0x100801c1404513a42010f80c1c1c1c0e0f001c40b86290750f0183c000542082c15900004180d400c15600c080040d500070080c2c58189002e22212420810013161f00030320801700400e1000030048990000c10015030200c0d01444801446240144641284c040300c02002c545d40c510f000034020080112030700e05802a02d07924241038908049000342d000031a0142c010300d00040345c40e0340c0e17038070401005800da02ca0200d01c0c10802e150181351088060050036060b03000000304802000a0001d1103451a0815100c2020b512200781d1405101104c0701448080d0600ca410000c1d50010f07a40410b420050381d90002d4132548607182c0d00503c0001c4071000caa51164903200205201482e08100000c801e16032080c80203010940c1c800303e81c01001c0080e911843c0c056406102d0900040c5094000c00e10080d81a208554000481c3c41c01c000998005030355810364461b800c0014002250b2292401031180c8103400c1441905588402040c4010170800000e8495940d0b000883c8800a11494000c000c0804400d4407401c49400d043c1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 990199163 1250 990197913 990197917
    0x12200405130c06020c060711010e130e010c0504030f12110d11120c150c0f0403030f083121020d110c09041b03061508010e010b0303040b0c070902030c 66
    0xb0b4401c810000400202c00d4800035004034000c402414441c20b0110703507074400c0c0c029801404114140700f9280708107207a5455182245240c04c5c021000030468521403441542190740d01c4201c042004400c11040c00400d8000350300d1001d60b03038015019885005482c100b1103910680010410f298082c0122140040d0b0780640040c04101d0b443c020380701d2029001414016a1003154041003d94000c0009090b40d1110039030381c664401a00e003003c901d48041c2116aa8103540036420460200c2d04028100b0304240d40410300a9000e6440690803115252400d12001380b0108907001d24854041008210b08014002ca070b00000c19100e092901045483c44001070b488050141040000481030106040c04100015144801100241100c5095201c0e5101c0400381c0c45074600610000c02d8060b4000001510341c440e00348a503241440a045450400d203615085d922034100d48100c682c10807496001d283d40c040300b190101d95040640d41d070b592048110f414100309059021503180c91020042103003081d00100 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 990200413 1250 990199163 990199201
    0xc16080d240503070b0f0405040f090614150d05100f050906070e0a061209051e010c081509040f080309070f050301050f0a0e0307020306090a0201030b0a12200405 71
    0x1d5020004003a030002103904a14a02c545503060340420410005410260028200d00c103d1441c99841c094942c1c0204003503541284411400700e43c0d6011407418449140709803010000d820005019500f0011141241a2443c0c0c00640c8030702952445101007000800c01d8034514030024106020a800c07030f40007000103000c00c460301e07507481c0030f14400201c0c290700c00c203c061380340140240002d003024100001111101c2d421030706a0038076940c0b1102500811420090402d46002c205502c0709902c00c0d0042003400d443c00c0003003480c14010980d0500101c0d06030804900341121050380c1da0a00c035615420071040e0201d0540e40908055000020300031701032000b0a94909844240541c80001561241410700320b03101100d02480040b0184080344440d441c03a0400201d02084104480c02c110032500000e007092030948600c0416841480c0d40c0c1e045507018015501203440c01c40b11340c070110b0320701a0484a6024600c20081c40c0664000307841c0c0e441c02d00e03040c000e5800b40006d8410003040c80d1020011903001c207112 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 990201663 1250 990200413 990200441
    0xc0336090420060405030f0c040b0d0f080d090c030606030507050d0b0a320f0a050712090c090c05070b150a030f0c030602031003120302040e0c16080d 66
    0x501014590308003400001e00a540c0558a0030300d080c00c1d01900724500c01d1640e562640300000308000200359030b0130082c2c9121004a0000351402e02c0071202004100e83c00008007a0042e00c128410780c2c003140c02c0070500d20109401201c0142c0d11514a00b0180c024005228020011041204c000c0f003400040e40c02030081d2403003401155001c1e52200b0402c000e428401c00c00925454101000414100c55600301c180307003034000d03007135420b418858520f0f02c01181c028080781c8803500c04440c1045540c03035113030284940245038442c2c00c21903414912002058030810600c58002c560311041d1090400a44c0c2041000504094204008003010f03120010250b0388031f060144c1d05401c0e210041903058031030100f028a01b07003004055440c16842d40d075500499107030700c650036100304000f8100000401e0f80d80c002180700d030500c000c1c80441d00b82146030007030b84480d115521204140c0306000c2030288141c0981819004154100256100c0e00d9501c01d580307103409507090041400c0404284100705a400f5045078517400741c98 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 990202913 1250 990201663 990201757
    0x20706080f04030c0c03080f0921070312260103030e09061f020106030b0f1b0403020f1e1f030b04050903191e021b0409020904080c03 59
    0x2010212011501a100708040200c0705000c5800240910381001c007241c820100c1a50455590719010903d4200c007003e44140400042c50b42420b10f440e80d03041c241e2001c1540c0d400a2003c0101140e5617822682c04000c1981084c64100f482e803074090720b100030040c05000c10300002449036500c40c0700c1000082c401103010a2003204145401c0c6400100d0030312501016141c0c4521120780c1d440c4c00c0341e490081d8840030039550b881e200031022400141c60280302e80200035031580b036800d00203542c211400402c9040044404d081c0b10a200580e41c039a4130240503001224890310041c0301c1350441e110412070a0700c07198080700c81f43e076008201007481c81c0400f40700b02c00c0d18200000e44001081c0720650b00e003240e04c0304160704108401c8104c00d5802840d003030003040c0c034500b002040c0700124100d00c41d10000c3c0c0807040540d100d1300445071003111044080c035590006a03801d0007d40c94942c00714015400148c40140100c2c408980d2460900f030800995404c0c1381d26148031550403400104a42e4002c0c984100c40c4114546 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 990204163 1250 990202913 990202919
    0x60305160b07120516060509010b18090706140d02030915060d02030a0609060b0d030e09070f0e10020f1e0d0801210c350f0c0d06060e1003030207 64
    0x200140c2d041260060600b045034035400700102c3d080d44c40f60707502140c200e0800c003008012514501c55144105402400000c0e8485c00c0b10030841e0a0b480382400b60300165491702000811034020030b209044501d2820f01d8008294001c41280c0300d40200f080c0140d4492001c03040002241000985c4008081c00240445290300c800060190100010340040e405901c117601c1034000510752341c003210070302c2e004420028101e05000700064a901c503110301038000030110034005401d454000580d603007040702400c044009011440c2c0c0a4400c10400001ea841802012a01e00040707009001641d042100f04080d02c1e904206c0c80401413113a00603100d024428030480342500881806400301354103a5000100702d030406110760103e082814076150301100e010a100500042c070b110303400010b100b90f02c0741c0300c80c00803801d68040e66910070000d40e211001a0741d000340710101c112000130071182a034840903100b911240300241008400361045500104a240480d800c01035544840006441500d12940c00d45524030b503 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 990205413 1250 990204163 990204179
    0xa060503010b030a020f121e01050702070609032301050c040305070b03040b19020f0403120e03060615070c0b0a030e0d0302122403100b041d03040b0c1006030516 71
    0x400c1c0c140f90141d00648100d0050329115902c108645402007611080302c0c80d0808003404c0a040c1104d1048141200c1207803140c0541c00c1c02000c0d80542c240c030007403015070b113480d0008124074502e110141c0060b001190000054070f0b0f10794803040804100009010380c1c10884001841c1c0e0f482840300303940c540244880403448521180480f801035402040d44201c6480701c80070302a032254992120b160250b42002540420340e62200a00019801003140344852405014003405407a495110144280c004a04000c1c561b681d0503041e075585200742c07a8094548400d450001d801c80b4040c1c0040c03140f10408681c0c1e140085d0715800403000440744a041d41c16640442d803050301030b40203031258800007440502c0083c03488a800b01800710140d005100120790301c40d8000c0428200000085101c2c1c50907102c90201e400c0341041e0060480ca42140002c00030840c07035044445840f40107a018034400c1c09800101000641010007030800140d2880d48100700d240c0c0d8070720309603a4a0310b06508540103180c6001c00058001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 990206663 1250 990205413 990205421
    0xb030106170c060f040e07020a140607080a0902030d0302090a08120a2a060209010903020612040c05010918050a24091a060901080c040f031113050c04090b03030715050a06050301 78
    0x20194030040c030705142c1045584002c102006047c502180709441d14000460009070412038080e02d000301400d40c0f800c202500070120f81c8028150200c0038104407801c3c005840019005200c0d01b5030349001038907072801038001460040c059104041d03d00c43d04200210500000008143c0c8890644a03180049180e1090a00024000980283c0300100303420040100d0380c1900208505001450001c640d56201c1c0d00040054000350b000d107015100d200204810002e140340c1103000b401090920400766440c3c200742d030074025000e100c0348104940390000304000f440c198004070452022182c0014900c410003000f068000280d105055001e03090035910081d2418400c000c0079171140c013402482c500b480da1001900c400d100070740040c5030201c0c100070000b24074078a201c007130020314400c4d80254144a40041000501e11079485101105032506081c45540d501317810072941150011040400d02d941c0c0280060300754000e401004e0001100e182140306120070076800b0502c692610030f4104650368540302414200d0b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 990207913 1250 990206663 990206677
    0xc08160f14070c09050108030a020708010b0d1103030c060103051c0f0906110f0601080f010b1903140c061317060c0a0e040f02070302030309060c0c1c030b030106170c06 74
    0x114411900c0c1c0558811648024198940264043c941555448103100c046072003d86c41800c0503000415030b0444107070b051082200070282c1d44001d03c41c803014000010501c141540004003c4001070482e01c2c40b58905100751290040783c40141d501543e501c0c1000740d00e41103406440d5480840303c041c8031000601a07000e1710390351000d5588000e20a400d016042e240c041c801030000c03002c2d01c00c0e1869001201004c000c0c4e0380c080c1280c40e003d01050120256400e00795414a0300c543d108d04000e00340d08190002c2210000b080b25004a40c044082a945015a00300864070407055080000010301203148800c0315404000c85405d0031840344c0983e01003d8854841509984405c2c04880400182da6070f40d1007100081c0c103802009100003400802c60a2840885e40041380c1140076801c003108009640d041401500d41c0a0103072000a864800840103135501d85544514403400b803064454180316007803282c1d101c0812444040d000700319030764172624152080c200082c4442100c3c46407041800f0360f030809000740c8001d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 990209163 1250 990207913 990207917
    0x3091d07050d1119090914060310110f13030b0f07211103010e04032d0804061d0601031424090a020a06050c0d0f27090c08160f 56
    0x14280c2005840300600700c00e0101025483d020b1007283c001351002c00d004035040a842d11104005898911420141d03201810303131800748050303402048000d4502240803103a602c0c0b5a140054030f0900c1d400d0030300c1d050103684802c5480010100b0a80781190180700010240c034082c00c906810b554a400c0841645a411940400045e110b844800310031400c0d20000300300030305541d03404240190801010070081c3c100740d00c85082b1454000c1230105058005200c0b0385011091070100031480210b800d030071a4500d0f191404010003841c0e90015091018551106044039003c2104032400e0a090502c2541c0e0300003030005440c41e111603030444184900001c1c0c03071505260600e9460301d40c10340407a00c50803003440050504045008400c541401651400c140030003801c0c5503158292200310711460705140c50b1101900506102c1490715280040d07401500704405c04400c105c040f041040079005e8940000210b80c0140c0361941005c158540058214840c244140700c40d00c5612904490f0000860f24103420b4905800 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 990210413 1250 990209163 990209167
    0x1b1d0603060d020d1e3008010e150406030f060e06220507081c03060e040825390b090d06020f0a0f0807031401120510020703091d0705 59
    0x5060003c88100c0d6240160751105c402c1e45201d8600009034202e0078204c801003569021782c1d942c1c40041c0801030000706101c440040c0c506503040c01070510038060040284444030300c800100110200c4075581120b800203403084c0001652449c0084d0b44035a02007048a0f8a0700307211088080c500005161803155404034621050648080c0c601042801014005d4405009007a00401e80e580304001d50301c0d100c0c00700b103048905070340e0340e420044c1150030701d40003100c064405400340300100b81c15105842c480101c800340207030101e1030000100c07404061910000c02501103c0c0c45100c03070300e005170402107081800d41d51407a4100c0190003c2c1441803454003810200110078070413049981084801000c03918445d250042c03030144440a4070096401041074080000c8802e02c0c01d554071b41d0310480882c2c01c4559800d06000c2c503180450a40401c41050180d00c1d01d80304254423400520104124804440e00203003011540c40c1101d0074020304c0482e0500030001100030212202482e1030f50602482d10070000e030355070f240c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 990211663 1250 990210413 990210439
    0x70f05090a1109040e03070b1509090705130f0b100513060c050d0f0c140106050f0405042a0e04141e070b092101060503010f0e0c0f03011b1d060306 65
    0x1100505c0c2048a000d61440700b402204001105089024064400c2100c42d10307078980c1c4102082102c00006140071625048a1420441e80d241c0e80749044d0b101490711400716808a80d44001c03801018042d407080e610203111529400740f590407070000c0140d1058400405403040d1030741c1d000e803032150894000600c01d52000f501d501034584100032900019070f6500d0443d0380501c0c42e071030300180d008254003410f1890b55100030400143c81e000400034840c3d034090703406000c10300d81501c0700c8514001510700a908090700207100c01d0034002d01880301d07024103802c220411803402d140c101362200840000d24001c081c1300307644588100941c100d0421011400b80801840c15034200082041036030080000303250480f01c00c94020403c04084012802c00e03201920000030201d1828040500b500d550442200745c580c5803c01d0070848100210350b40c00b00d40c6040e10741515103508034010a00600b14954120004c4400b03400504ca4240d003c003092401c0b101805050300c10860f90070404c0124402a140140e01c0074084d9960 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 990212913 1250 990211663 990211669
    0xc111309021207030f0f03020c03030a03140f0c030412050c190b0f0408030a0e030f0d050703050601230f13150207080d0f0809011401060e0117040b07050c030705070f05090a1109 78
    0x80186c4078440d105640008a0280201e440e5402041c2c0d5030340841d4840c0610000700f46084a0540d20550b5100482c0150504203001013035440080d00240141c1401d0fa00a0710f40e501800440b2582c04130301040750001200220241081e070902c0700c048070111226408a002d408500c54020701861b004511149107807111810b010045c4160b800240460000380300b500c40c455560380c0034140741280d00b000402d061802a0005040340c0005011505206007100b1a0301207150076903007040d044110f282441d540d05001c858044143c0685403580d85140a890808905000501c900e040c100109400b2074550a80301c0c410f0549030350140c0c07200700c00903c11640e5440424403c06001d50460300c443d00001d0200300c41c212009000000342c01134804910b411825404a50340102c01c8800352180fa07c3c00c90306400c1a50701d40283e0440a000074003045004211500c1e140e0040c0b080b07d08055002e411604aa03980700d1201d031101160f40b00f02c522075007641001a0f1125101d0050010394411410f00c2403070b01c2807081c10 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 990214163 1250 990212913 990212933
    0x1b02091914041a07030902091305100c02071806031e03140909060d080d15050a0b071104050601050f070b0a0e010207020d030f091806080106060c120c111309021207030f 74
    0xc504c04054076500000050b03114422098003c0c8028525000f4200c4030381000c1c0c2c030309001207500780a40c038075121070403045941c04681d40f000e8400c081215250840260011405004a43c001508110300408074081d4600c02030340780404640b10391100c40e00c9680030444060f49004122451f80c104610200007503081c54a12090309400c0e218a040c0790404007288107860031100050702500c0d0203013100c0c400307202d07a1070321101041c02000d0710f00c80d4070301e440819991a002c090300003030f410740119100c0001c501680e0280c420342c1c1ca5a021040c0040c1c80d00d090b4140718449030703400d848080491341340941030301100c4810b008841c2d000703401030620340c4d128105907070403114603400004d5581086508131002c100140840300c882c00610ac010700102e05603080c00c201a0840b06070ba4044014030100000307501c0042c8d50480f1008596603941000303283d82140d82024551445000d100c1030f0710212502c5800004240c6900c40e511090080e80c2494819060150160b5180402c2c0009032410201c0c010704030016107602c034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 990215413 1250 990214163 990214171
    0x60f01030803130f0605040212030c070b0a0504031a041a0c0702010c02060d020403030309231f091403180406180b030102070b09061e0601050a1b02091914041a 70
    0x18501000f1103154a41d68a403035a0701c130303044400603110010700055280c4090030707404010741d0300040c0d40b900c814034101950b83c001ea03124071480e4480118600340f00700c0c042c01c203840080d0780200c035102501140e00700d1094184022102100d0281500840c8000c00c0b0006050fa4403d86107401854a8400140c0042d10100c404c100c3c100e0380903404000701203440b90381c0d0001c0c0006500c80d440c0815004403030b1604030740d81a0f840a848101d01035460011240140000340e034240d1902028445180c2840300000101603c101c450290a15810f8100009402d10001c000c040305003244000b40c04103050320003000140c48291040e4114403203000c0e60544110140e50000e00d51006c01030005280c40065583d680850300c0445120550350450300130003000800604404014401080080f00a4944000042d04500500c4110340030458810b025010351381807003a000b201e0740c0e0002e107108020b00e0f000008481d000d0540ca1a06030090400a44a0f0b0300d60003038000d18029680887c081044c400012280018400020 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 990216663 1250 990215413 990215431
    0xd030b0a050405191a03070e09060610020a0203011b020c0f09070e180a20091012092f040204051e150c0d030518070306111c060303030509060f01030803 67
    0x3404421301c64182c81109807080209050359407a100c110f0405081114552201000c00011410012a20004101c45501100403a001c016a281c009030403071410407507e0340203400d50701e40409900002c0058a05018250482d801c441e0b401321468103010507144480e005a810035100c0c804102d8040c040c00d040850420050a22400900c1c8180c0102d203800b4207451310290240d9812a0040560744d14103154032440600d100c3e1071030609107802142c1c062481b042072208210310a9008445d40d0210342000348850380042140070400340558407500400d01134960403940d801c0c00c4220a03000d06080c001e441c100e40000f481c00e500084c4c5d003142c40c3c1e0718030342e1810400c3d40020300c1d00c450035840c12000054401c480c060801808415030f80c48000d000c481d0050310301301c001c2c01c066120403003030440020007400356a400540460b403d0b056641d440c0b40da004480826030803400c880746401c1c2001d0340d540031004a030700a581c1070019843d00d810841e20f81d40305491880400010000500104003200000c5401140e18 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 990217913 1250 990216663 990216691
    0x6070503090a1b0f0f0b041404110c0f10090305030606180607030f0e0604150c060b0418021f0c032307081201050f28051206090d030b0a050405 63
    0x2a41e80000301c0360b1150034803161400b440820301032010130414a5003d450f800060400c1d82e8100800c10686005601c10b14000050700c0c0c1d011381c0162956008020441c6071a030f00c0544a1040c9190141c03560850310711030b50720f0710802c02a414140300901501c2c800b01d405855461440c0c4811060050980c41303000500c02003044102c0b042000c2d103e540040c01c13103a00a603941031418900038030062420307980402c1c45214100c207100c10704c0320609078602802030708d0325414500c441c901646024005441031080e1030f58042d24007054119071202001001e00c08030b01c04c80c0d600e8805014040f09081250340e1101843c00603542c1c106110019002d00900d015190000e0145040d078510f1082c41030b40c503400003100f02c0da01d810100f00d400d81030b5440c1c040c040c05040d003110840101c0b080d160205e51600c02d0250303820700c0f100030079985409445d03d10511001a0401605000181103103600440ea079186c00e440600451095205010181340b1074400d411000000400c5a0b124600e0301c001c21019001c06400c40741c0d0383c131031 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 990219163 1250 990217913 990217933
    0x1c0911060a11070906061707120c0f08061008131b090902030d0e060904022101080c03190b0f07031b02010606090f0b0301051903050a0503090f0609030607050309 71
    0x5100c0541101e203401d590308100055040b0b031107418901c0c1540203141c0142004e10a00900d904103403040a145180c039040502c42d541c0700c00445590703040194052549144c100003a0219500000104a590281d16034001e00d880d060700344001101072004a000140010300403440e00b50f0351901c1251018014600074003544000175820031155103e45c00024242c0d60355040d0011410148003080d800da405081c013800303106c034001c0460068841e05001e07a10840d400a01d5941000400c4100003030450000381c0d83c0d1056071560100b50380c904482074594130034420325039611640f503481043c02d0b02c0300794003043c6200541c480c810b46000c02900036142e80245502d032000d0007100c11407000c2142d1409001ea0011429615040003d00814565048840c2c7c100c00b00c90b05000754083c01d0100d278110f03001580c8170141814901640c005d800007035000204940a54440030b020b121001010317101d40b02c4203d802d44d0011040c10200f04940c030a910010742c01d60800400100c10710b010340045c603030141c0540162401c03980 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 990220413 1250 990219163 990219169
    0x151911120906071e0c06020a0b01060e0103021605010c09080a120c03050405030f07150302131a04030c031a06090402010f1d0316030c0504020306150d060513020a03050c1c0911 77
    0x140b103030300b46000501020703403003018040800703849402003805002038070320b150305ca4039949c1131000c2c1400b074041030041520700090369034070079811586c000700054014800c08801385003043c0078000c426a0000003d40c20280400c1c0d0305008103c6002c0076903c05940803101e5104841a64102c4c1104415000c1c08420b000004041d2014402141c06440c0d28002c1c2c03c1c2c607030410088200b01001850b103e0101071041c00700c00310000100ea1042c00392250117090410f0050405011101882540c00060051a02c2040002000f21a420130b88006441494045031035441001f0f2007a00e41c001c84010740091000061181010702030a82d1103c40310703144604100d103002c00008a0300e40080c0d01d81c1c061040d49038280801c03e200d00b03441e4910140c6800c5509500e03504180000410f903664180d00070716425000144001081c0c41d0380d102074005d10010b07007101030ba0642004140000d41084284402007810000021070f0b690a0310304a900300b4800355099800028ec414129004080d4000c085500c100f40c020007001c99030b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 990221663 1250 990220413 990220433
    0x2152212050f040e0a05070905280b120109060e100b07051011071103010506030a330209030f06010303051b150f01060f022b050915191112090607 64
    0x102010750307840800c5c14444051000c0703a9005180f1000c1040f5241c05100740e40e651038002403207816000c00e42d00420081d00301c0c60710061050f40b080000d210b00050740d04081c03481c02a00ca049170427000e020030200d80e6034180002003a0044034132078041c212890003844a0900000504039890064044a10075441d10b4000301c100c0d81607403031081c2d0300140030075401c00b041540f900000396080e00303a00038411403d007403000c00d03030700c0c1d04c40e103402840105800101c0007201520107200800b0303207a000d00340449145000c00d00e8001c0d840503032414003074058ac6000040200300020514100e99255175101c1c5000c110803100044003c940506203810300030400340c00b040d42440c0f08914001c0e4000740406110b545001c401a0402002c03004440075504502d01a1406441064402c0624a12900140c5180e0f000840468051080d800c1c1c0c00c6e0b10800d61742002e005480008054048512168000c400600c02c0200039120481e200d40c140407954001c440716042040d058005d09640354000e0f003010704040c1c4030b42c1d4542941d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 990222913 1250 990221663 990221669
    0xd0f050304150903051b210a120504080405120625030e01142a03040f020a0e040b09010507020a0807020d050a020603090d031a0108061207080d02152212050f04 70
    0x80d0000c070b44e91b9140d020071032000300703005030a00040c40300901d61085031400e007801d8106510100f6011170814a0345001d022403004a81804408000a150901d400601d035041750041714000e0703806103002c07031940f100040c4c194010850703508001d1010281049560110414008400800d51104c5021070003100034003a0b82513418100c10302e4481d80c45c01e44040c4058241d40c0c000110004a0b0300001e0010f24051000c0300c1c0c1083e040488042c0d0309000e0300110b105c4010940c01400302640030001c01051211100b00f0500514a02009215a48072228226581c4501d4000501070030420400000141307400c5059200b9a8440c0041c1c8808070200e40000e013203034104841394030094000803150007d0651510400401140341d00300890384a10500008203503030002003d10b40100e00b45a000b0400c12801c100c26001400401308950010b500110025102c040c03003016241c030701c6280404240700f044920741c0500c41100700e80006590341543c1e22181040e0304a9112202481401c01401c403208414500074409 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 990224163 1250 990222913 990222917
    0x61d01020c131d21030609130c030b0a0915110a11010e060c0403120201050408090405090111030705040905010b040501081609050d20040e03090f0f0307150801080d0f050304150903 79
    0x44c0d520188541d40c001d002e0007444001e5000800410031559288640e00c1c0c0c00460840352020310002d00c0c40c00549420740c6820203840f9040d1202008102003075503700800703851040c402030340c0201240b01d0000a0700d0040781c03004150796043c00a1442d2a1054103000c40420001c400031407000c03644044503041480c10340740b08281180000301482480160104015040c0951000b0040da18050300c0f0150a80210070003140b003152200d0208074445003d4001d50190780c0501c074540d9890a242d81e0142c4603600500c903511500e8100000010186403007130540703044075030603103d44506070340d10311030412982c010758100001d000c50300e10007080649540b0301941e2464803500015860501000b0041c1d0304405800c0500d115604203810303406113140104c10b65000070020394480c589040041c0000755401c00b0070b0050364052054050000b20074440c080c841c94101da50f5155031000d40d0700c03a07080c0c641302c0704020000d0011030b4103110842940c034807603801154000d0094441d0780c10802d5a4958000342c0d03500d0001540 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 990225413 1250 990224163 990224173
    0x60911010801061d060a020f0105250323063f010b012106090915050c030907031b0b12060a0f030b1605130f061d01020c131d 55
    0x646580002565000d003007107083c02010180c1401ca804480509074040341e01070a404110205a18020044100709040c50390081c4034614000c04443c42e00f07a14a07102d01051031850400d85001800303881401000c000f0030040004a0300b2001c0840c241319001780c41c0035081481102107003400300c070445520007181d5050240d659240816580c0d441c008081c0c0350b03143c450342d26103502c943c0d05070303000230440345002c0c81c41c0400d152404132410074400030011644885045410898400104030040c01500c4056603450420416500c032203043d070340c00c0c0c0000c848041b00b6a22001003400801d2400d820349007200c080c0c004c6840201c0d2128000316454008001c03041409031518240b04031403800310740050140000786e0318030100721716684030440300c000c020f0072103420603110400890074184510201c2c0c0030028030710450145140d469445071404c9005205400001e080460686414403201c0214420701038141d0080c600f030031800040100380e082000d078200c481d603070300c0c4078035030040440c40d215901a50109020300 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 990226663 1250 990225413 990225443
    0xc03070608040b07080114090a06080f0a050d05031911070f0b2e03060b040209040903050a090605030f010512101805060f010605160503040905272d0a0609 68
    0x401c2c3d43c00c000c1e00301d0041c809070704014084410861a4450489411144400345440d601c19084c010a2942c0080810740100c402d03543c0b11038800a60641420700c540c040b120540c0f80008200d03031a01080e0f40c40c40806024482001c00048250811190703000a01c500900d01410390740c419104008900040383c081d40e01c401003100711000388032442550000803855614a18818545c400c4d902003901004201035541c0f07900951030f486580c186d5a4462004d002040b905200c2c0c18094010f812441424000a1060602060085c816802c1d41e0141c2d41c0f500d149141c90342010304109002d03a040d01901150f1180c2407007031114090500500f00e004081c072060207040740030750410130704284e002001d40040c1d25002c4010441c04d41e106048a14400890a130740012407000c0c6441419071089510411a180c20a401d1040514149801c0401c3d82c4861504d070201d00c480488040d11a442031840001000341154136403680c1c442004078100c805608404d0b1352840301030b6550f240440c0c6150001b980c0d036955010040b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 990227913 1250 990226663 990226673
    0x4030c0b06040b0306071b0f060204031e051c021005010b04170a08070b0403050c060420180a02030c1e040302010e011b08130e0702010f0f11031302030c0307060804 72
    0x290340201c03054606025442d101004241e403900003070100410025a4920301c184195082c4000b82c00560022001c0c055404c030f801c5c824040c1d0032601056404030220000d20780050550000d80c840541e102002d00210244c031590304800d00644502d01c070075805000c004a01810f83c81c0f080ca800703804804a40e0b51242d0426038000f1028a41c0b10080c480c550003503000d13501040c4000c05a0340910ba1190801d01c5d10ba80710301c0c00300d900c1d000c1c2e000d2203222480307600c1c203020800141c0740c1004811055514440f40040e1801c04010020303801f2000300c0d50f00102203002c6180d28a058000390350003003c43c00c000d440c15003140d440317070115940305948000c81c1d58007190a00842d070344060f103101d00c40c4c0c003480c080720300d0300c141c0c0480600c01003a250000c100e07400c00102c40c0720882c0d10b2144507000300405030003410301d8507141d2400b9010f0841c2607400c0c0b803441d142c00c0d0700070b9100c80c5a1041042d0700204502d414219a070740303164101a000b0850050340d0510a004011120342d404004601c007508040d5102062400d141c582 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 990229163 1250 990227913 990227933
    0x1080a02160609150b090c1317030408061003030f0327050c15130b07110a080c0901060503010803090f0a030b01261b060304061d03070c140901230904030c 68
    0x5160001c1c2e04117072016280360345d011600f41e04802c2c9202d0481e40c400d108483e8144417107a0340e01601a6228540040c4403842000c4040c0003101c1c40f20b8203580c190394a8283e400b41d0318081d0300004000c2018010541081c0384a40e00500040c3c10140c4503581d03031b60b0784000244511121440480d00340d4801c9403061400c0c200b0b148045c5800010144c00303070030102d644942d044034164500074412044400b007915014045040700014500c500030f006080c02907246d001c0541c84060800ea21401903140b140002403c500c200108c034100c9401074041e6040c000c10208010602c0080080c181d4401d0409101001280720750412600814019028107010080401c02c50044400030b45481c910f0340042c0222028103000d0b020b012018141203a807560b9070350f61071074100020403803114502c0f034036040d030007400303180130000401088542c1c0144185e110f00b82e910b0004084ca030203c441c4068008009100411803450108403544818091070390071807108101d40d0202c0e0100d002220107500180300c0203a010144000c1c5c482d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 990230413 1250 990229163 990229193
    0xa05101a040209060715150b0c0f0a080a0e061e03101508160c050d1d0604120b040302101806060603020c0a111903051c0207080601030201080a02160609 67
    0x1e015070800325264005035050203005070241c16140c1c0c0407000412030701241c2c0100f11130a02c9200c08098991a61642011504600306110043c07103a540c40c002191000248840e0300e0368409031080c0f80400208007150b442c10b641c50b4250b0020014059100d415542c402e01704110741781c492080342c492400c106105042c6405900058003049000b00031015580e01144040d0300c0101c1c0401e040e07080c00d00a0703044079101c001c1c0c00b002c0d20300d0003050100ba1a03280c0c48100c0d04502c00004802d2140e011603441044810300c6030b07209080000d1300704162800007a01c800005617005000340107440b10140420503017001c2e1105444041500c0000080c00420400315210780300250a4600d011400c00c869252560755031020104080c2c01c50304042c5030f40791a070396501d8204a180450604202c0101d40d28a4110342da41c003040c42100381c0c2ea800e00c03030414655100150310011a803074203008220592039030f001500c04003405400c800348c0710340070005807021043e107240d0205020b00c1290002882009400c015042003290700c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 990231663 1250 990230413 990230419
    0x70c020f191716051012050c0f1318020906030610020a0f0f290604091b08070e0105040c050706150302150c0d020712140f0706050c010c020705130e0a05101a 69
    0x1c21724070707940c4000d65110710200c05400241588450003015114004c0292180c50b0b980c0005038402c0d1030044440410458140b0b10b0054405210358240300309034011014955084401480094418940013a911443d281175005580d14050710b6201d480e40b82c1a50041078440c250442041010400d05090400304041d035951903800920071003042102546019022601c201d84410440b418004a400a0380410203400ca40344490b030394030002e00c2e40307403442885542c1c003100301c03c0000500c3c1c0c10f003405005500b41c090b030341344d510f40603103555040028020303c850044500d0844602000588540210252440d03400e1613513525104000b010307515040381c402c081e2085404c44001080b2468101000007031466103d491042900721032071443c0d142c01e114003003690481c402c4000020345035403c41c00030501000381c400240260103510900303a07039581803481541d0300070341c1420032554842d0555019a074020070f048240c6080724156203401e85040b02030b446080b2940c0d591004c102c4220007040070002c0c004419 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 990232913 1250 990231663 990231679
    0x80f060c040302190b0d06090b030c10080a0e1005090f0d020615060c01180507060c051b04090203010507030b0a091b180e07020c09070c020f19171605 66
    0xe903a411014055440024001d1115102d10003654802c09150300280c414140304940b20020308143c0b201815062061040c15454103004900c0c0b400e011400b003d654501424403c40c1400180045602450003003400102e141e460100244c004824007020720925001400480c03982808000c5a061912013401a54540c0c01004036020141d000310301654004c0c0060000d060b010307891000301d295407003141000400c039440c0c070314105c0d0701281a6060002c142e0280040350000d07511000140c492466019014110f94440b8441c12298500e11021800b408809400440ea50145502207401d6a03025104540803e4440da0604103c0c1012580c900083c6140c14041c004004840406206403101031160420000019026803480340d400c1043d80051102c1c00c214a054501420025143ca1545500905c103d006501040c1001d20419800b880290001c0507001c80481003010440021b09440130171100020001001416003e0101943c1c4407104007070190009110800322459210200d810042c418116 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 990234163 1250 990232913 990232921
    0xd120c11060a020f161b050117010902030a060302091003020108060a0302060f07081608033312010f020a05090405360705060403061e020a0f0e0612040507080f06 71
    0x742241c01034540c0380016030b9052090b007031a8443c89040c414415002c00ca07100c8804000200e420f600041228902d10030610b622a001110a004c1d4200601e0900e410a801440741c05210340c011508081140b0000503600c3e50303680424030841c0201c03101180481000c2c010015940c0101c0042d0340b00400b2501860080d0540d80020200d008680c0380580c0b55030041486400c004090048800e44406050200c05504442c64030401550084400c2c118802000d00042d003001722036960141a400524403c0200c094144c0174007100d00340c0e50a1030b040360b6403604520701d48140144020725402e252079407810369820046081c04141d40c80588000c840144840c81c14203c000000700030750103904508044403a40154030325607490501c80d60851a40524000303000020090315510100d070805036511140c003528000c039652022030082e0003105004c114080c480084503845540d940c220000c0041405017031554030400281c045c81d003190111143d03400000c060154034800c101100160001d80000c008601d0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 990235413 1250 990234163 990234197
    0xa0815070207050315180307051b0604031a090a120f091a0a081302060f0304140106030503030612070e0703140a050c1e07210e0d0c150207080d120c 65
    0x1100c0f60006020103107103408500c0c00e00c619402411900140300807a23031030300402d01f003807a05c400384c100101c0c0c0c0c80d00420108100c0d600300001560308803500314501145080c0020f0161000300b034002c0c8201158021401c0302000036450382d401c40b00e507040315030310040d0700c80700b0794000703444076070242c00c440c40c01105400701104c0d504c503030021164802d01d10300d0300f8807058982200d150807070b0020410095000101050b000074100d0039102441c401e90003507244182d811406500e00303081b21035034000079107650804c000040302400c0810400c06445000750407a0310031641e44660f50002030b002d540060009480303030314032030245125241071504285a4401004a800c05060402007442261034020340460302c4080c0c203a420041c00306039991203801645501d4095100b003984c010340100c0030a4180410340d000305075016401c02019811020750300c00d2150310030505003003180d040249500c8915045100303655001c111440b01380254419031a4a4407011503800209181034140c5007890950700800400c4030032800046 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 990236663 1250 990235413 990235423
    0xa11030c0d081602011b200712021e030a02011d040516030501152f2506021b09040606080d090f05120a06050a110c07080f030c0d08060f0a08150702070503 68
    0x502107040801f007040a003000c0c1d5000c04944840e040c0d10303000d00540000c1d051100701410070424800c49a60a0241810892441c400119401b081d01a4031030b20706080154041c240d0801020058690902e09010000c0002c083d00c00441e030a21051503000000c20849400d03000cad4034054008103240800c070034901400100100540d400d07075402d40d83d40c000208818040001c2165510a2803420748512034684007030038003240b0010620300300e0072641d02030010301140f002c100c0500070a806800d90401c003518000700412030340d024200384d9049a0303844001905500410512481c51301e1070311580c02032850300d0309401644900b98000c501a8008040340240c040c0086210b1500c0d9a21820004d800c1e01c2d410740c624000c00310324140d00510030001036100810070340060b09000300c0d842c0b8003ca5103865100aa89031702e9029009104080e40d1181d0301d030810842c0140446540440041d0418040980305400514500641e0b800302c030382a000801c0c0721540060540115901841d180000c1c0441443d020101c0d80e11 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 990237913 1250 990236663 990236711
    0x1614010b0a21060f18051002040506040303142110081513050c06180a120c15170c0304020f09010f06140f0c0303100e010b0a11030c0d08160201 63
    0x1071084100c0708100c00fa600076040f04070341038420803201d0720960300f103100740b041607109488921030440a44800c0e00304d8000c071401da900140c100303401d01d45180d609882c558600c0b905240004d070240008003043c0e50600006908098580c404c0400d410012580045480d060300200996000035aa00104081013005107410548100310031072001418140b260038030680301007155000780001a1440c00400070040075555030300403650506c1c0c40d0b41d2032080840300c400c100e600a21070041d08c40c1c100305034a4004103412004078182001894401c000c40c1e2001e45041c00c170f0700c59101b6075021003444254100080700101641c802d41d102070242d410408003841e0803546200e04810404a011202c0b8200800b40c01e49000b503080190a949820154010684a0300304681d8041c05021000001880100c03003540c080c12908004046440c01001c0b1108995811145102c0b54440c401040000c01c8418100a0034001a500b0307a00c5518505001030080c11070003601c0c00100841e8105501d191003800e200c00701c0004 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 990239163 1250 990237913 990237959
    0x131d060d0b04050c03010e060a0f0b090a091b0909060e060f0c03100515030f0606040b0a0f0516050705040b01030b011d01020a0803010b0a0206010f1809081614010b0a 73
    0x1d9036961520524090020031045c0c0c1550030220541200b244c0018043d000d00e030801c2040c130011014080303041c116540c1c00d441c41ea1124010000c03e501000c0c0e42d200d1071159018018451a0340c0b4284290300941c25107600c2400e1040c0d03240443c10500c203d500c5010709031691400a0869410440d1182c900c1640c0a4400035807490008085428500f1400710500103000181150700003500c08440c11040c2d0300300700d80084224441800142652400f00129025100401c044504190032030b4000c6480344505581030307040c020b040001d08150841644840c0d5440d100c0d0001f40030560400042c04141c4002c040428103150506043d05503913030304002800c119104184281c206243c032400100c0c64003a0340607015066540c0000046200c68019004150b140750903001c49900342d0ba203210000d0344e54514441d001003094900e41d0381225004507000014561300911650382845a40c5051400c00c0d000d0900c00c5070a288061856064150280116241e4802c01c5440c80083c0b8500203140d070003881c000b44c410b00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 990240413 1250 990239163 990239183
    0x1021b09040311100603060b090108010905070902030903090a0b0a020c040213052e0906082203030e0f100b030c0a05061b0312010e19060b0a050d020906131d060d 71
    0x1202c600c00c04c81c00c0c1000d25209414031403183d580c14607600800c80f0f821100e010f810400000702e80e4140500640e00016880030080032894076100411009400160064846010030000c03a0f00a0f82c2e210b8070764001e0064030324980d81c1e40380b5248001c3d02d044100c00c4d1032030180f0700500000e00f1060b02c201c2088200c0d03070103450400782d005240d1000d4920142c1401015030300c0981002c0203a20a9000d0b23a90307026658103840d0b507840e603251000c0c002d200c3d07540d049140701100c000d00c05120001e4841d8206010000c4c40c401118100c20b244405207092543e200304135000e907503680c00ca149140c40c003002001e8000d241900e480025500f050007081a1380b1a1550301c11201c0311100704042c40040c10000c581142404402e402200d5840f6910000000e0040e01c0341d82c90b10181c07469a084030241e910550046844090640b464803500e4042641c0d180c020f020301b156095404c0c13040c1945031301c0d41e10040003d502404000b060040c1049a00e030302000c021058181c20003034403000c005043d20346607500d040103a04460481 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 990241663 1250 990240413 990240437
    0x10803461205281803052203080d0b0d02130f061e0902070309030803010f050405010605030603061f0302030303100501140c0712111306151b0b0c120702070501021b090403 75
    0x30f070281081e10300403c40030f039410381900f080c0355101e40603180c419480c4100050717007a81d01c000000007420501019105003020889021403014540c880020004050880b4603040d003540c0016004000040000302103e8541482c20880d120600c94500907140c0155031000c1480c01d914084030100190255680703159000901c601032500541c8004002c5500c40411581c945e150b903102010006588130b11801542000008103101c6d0080c410b59204040140081000d6507450034420300c0d450881d02a490390301d0061740d01201513113040c00103602c83c12900c00071880c80b501e01780c0018084070030054950760100060010910b940d901182003011242100c8000c00300491a040403145280d80501c40c0da030188140c00d40241040f9190410f03002c42d8030016100b0550003160b01c0540348590b4081000c9101d40c14082036000013101901f680742c04c0560741c0581420701c4c4002d80701080051003a140c08003d030b03100300020402c1d503904010000d00c0081001040c0c04106580e030204925240140004051009901c0c0c82c07 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 990242913 1250 990241663 990241741
    0x200714010209060a0207060f0801210303110d0b09060102030a0207180f090f020312040b04051212070302060f01050102030406170a0b03011a0406090203010803461205 73
    0x602e100000041640c1c0d030703880d2243c1c07020399030703012a1050a0100f01802ca40398001c50089000c0c604a46410380c0564040300220b4880208600a24088082c140e41d1484100313415000c0020b0000c0381214403000586c03241c0c03401001005a4000c10090455008014007a45658081400c80072503181e0750071000c0722520300c0c20b18000f4002da160405271071840c3c000c00b0424000c064084000d0b260007503058400c0701094021110540c0300d54098180e042e68100010030950070b0080c0350f19000d881039000e54580c2c05000c060900b1a6018100a4005038459000d0200c00e0000b10350f1b040c0100000d00040d407800b4034046d000344ca068401c00112030803203103180000e510384401380c01c912801e2000400070001401c440c1c000c0c0d901c0720758014a6a000e107103880e41c01715200400703208680c1a900240010350400601036000c0300458525074802c10540318440803200803500990341500c001d11020500001500b80c018001c080c000901605c018150074031042c050382e090341c1456030b01d0720399480d220404030300f80340c03012 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 990244163 1250 990242913 990242917
    0xf060a0e010f11150a1b1e03020702130615050c0d1b02030a080a030c02010603150b061905040317070b01030210050c060112050d02070e011211180a2007140102 70
    0x100c0300d8502131010103441540a60811500c250822441000214103070403814003021a840d03c039502155000184d00729040301510341d005045a14580503180c000c00d50301198a6a0080103148280c646a000a00c80a0409981d10898920519040b800d12030221100c9035522440b5462030180302c1107441410703502c070340c80d01058801034000d011a1111030b07882ca010b9446502c00041880001e19204048403114410300480085980145000b41c2d44c0c100300b94084d0060191103200c0f6401001041035000060300c8403014076021400e511181d0310f0350b1031800c00a140d0074050b070101c0b040f050100044c5d00080d00c5c0c58031140c1034940696200c035800c0402002500c1c0e500c01e800c3d421419202d10b03000010600d82c20848000c40f80d01c02d201303035844110202410307641d0300418000e034006410000014032140c5030000e0000386090094014000c5048228041202c000d00903007039591313410b460001c204040500d402034000504070703203201a130b10540c2e0b1082b0302c0742e40c000c40e400100050980341c0000084002501 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 990245413 1250 990244163 990244187
    0x9040c030b030f21161707120504050f01080906241309020a0b03010e0a0e07050d1a010e090c06090409060c0908010e190212011e0b0f060a0e010f 64
    0x1120340c800d45400c05590344081d0f4800c40080d244d05030a00903da100c00105030b0307101d80b03203a00160800d034041d66115100080e1281c001000e80c80184024000301d401c681c65040d03214440d88036281d5031030410341440a1500d1285045040c0614001800146003000506580c0300d04000304034014098400760b01c5091401745210194455640300350030721001501d91020764181c1c0308450b20b00c00e556403950010f40302e000c00d02c28464034010031070014101c002e054108220054088064030f5440f51038000041000e08030502c1a2030b070384c020100b804405840c9902c0705000d42041c0c07422240030702c0c003512210382d21303500e0000e100e000307010109100b881511150401d42e6500c0d800b420034070103030b022a08004c0000e0400e10610100c0d41c20820b508071078072004510a07102021000e8407121107001350b02071002c00c40301c05600003030130b641c0c5007282190304020305600c1c002400c1350600481c8c040340c2002081200e8200c11402071003644200003961915400c2960510301002c20308159450380d6a961080e2044001c035a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 990246663 1250 990245413 990245419
    0x5040c0e0618012327070207090203010f06120b0915010c05120307022406100507050105160f080c0412170304030c120e130f020d0603150b031209040c030b 68
    0x44004902403440000301301c0303000c403082080d11840343c030441080300403004000d00303a00300205000c684010140c0590b83d140e020195004403003610350356140000072a07009a200345041c01d03c1c4041401219071141007002603025900b01406042c40349070001d4011a405800030201804180ca9200c05074010b81000382c1c46900724080c0c440803a038005100405620844440703006008248881e40c441d110340184000750482488a840c5c1903841c901400002030b803d010780380c24004d00740710560004009014041c400d250f4136840989078448a4005172111403580d010909001d0040704118410420000b6a0126001000d10501f408141d050080261101c82411b6500c00400000c10090641060500c1040c0f4810301028244002001c1c00b2640081c8a1404c0da601051750740e00c02d4442043c5030041c03054030402c6440145420000541e074400c03144194404c640005103902e421030001034500c10003800ca00c095003e450806086d02c1c108143e4420007207183d201d150ba808603480303a14032aa0010350040406 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 990247913 1250 990246663 990246709
    0x1020c03010f02300c07021807020106030b09010204180c0c0f0501091112101a120618031603050c0106030b0a020913110708250c0609080105040c0e06 66
    0x101c2c201002a51040007800d449118101a070340034440740124400c0312440d022486900e5468056004c0c280790f01c415400d9038841c1204e20f05120300d10440f140c00303000c0d0b500da0b00001000381c594a000070903a0f000030040d45199206000c20000b47c1d800000c540c0e03403c584084001031140740da20043d107940346040c0c0060000c1c240c0c1d240080801c9015400091554010b049004000c45060200a141840d001c0580e009030805015104c889003640c00500750341d8114030020f4a90041e40d804641000d002800d0740d41c0ca40e000d40103004c0248010b00c0c40c44448071039600038601d0003403044070814401c84410380007003c000001482c0d0700b03007260a40c050000fa603442902c0300c4280c100940404080d4102c00c0d03070a486085000403501020300e49109010408100001d12410f11505442e1400142c00150b220319110400c10064032181207000640032042e07100e03000e914801401c2c0f0400a000c183c694204524a81c586424000416151b8449a048684004000e200360b0303102c50106c0d070005400090312001c1089 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 990249163 1250 990247913 990247931
    0x10318031103042d08010c0c0f03170a02120a020406020d0c05100c0503150d02090106050715020c030c0f121207022d0c030a0c092a030f0e030a120b01020c0301 70
    0x4850209128804441c581403041da48617610203080300c904074050b1021070101d02c4d0007070000e0006111227030018064100f04088508004680035029400ca8114142a500007050034030010311414654210220344411401c150820070301035940c15031990420700344800da038140c0040010801a0313200d0190b03007840900c0120346103040a81582c1069a05054100406110700d0302414900d048040e40c94000748039101603460000280d81941c40200251a60000c040526030702c03070746a0000f4030107030751684011541d4103a1802d000d824040182c400903416084080c0050310450314070140c3e0015034a0342048610340c0c0740e07280143e04c0d001181d846116098800400d549540800c40c0b07910b03006040c6034003a6100c0700d04030700800d85c03603600701b140003000740309032100510040649a120400c41e01e0b8036402000e0440340340c0268a1200b4007841401d0000740c607060100d554500e9405601072480b8041c0c0114202071210102a14048804044240c0b40d607031116500050b0b80300304502031458a001e0001c00603956 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 990250413 1250 990249163 990249209
    0xd020a020604120314010509060d02030105010f0e010e0403020309060d0e0607200304052808060a020c0d050408033403051e070201021905010605040e06100501031803110304 76
    0x220890b42500c05040441d075140c11103029000b00d0480d50351420424040d17a08141c1005594040500019005059001c0550040e00c5c00d101b000d0292480c000d20200d000e00e020b0740740080c0b50058001d01118117a2409000c0043e0300007090f2602074000301c0d5119161000308610364014a84400016690700c00e04061001040c0c0000c0102003000080315003100959084100f52b541c1e02ca1849216003001c960005264044900c440510500f660750500b01c401e5961458014900301058403103c0b03240b03500203400c5c5480f1404000501150245040c910300382031800d910541c99010750718404018622800c42c0492480100111103494404a00504104029810014180c0c1c220710b038210702d1000d24103800550f006102c130640380c1c0c3e035a0582c01400c41052030001100c048403980c00494240d9200c4030086465034450103060f2078107105200030301c3c3e240350028032040d001c481988441e0506140001c41c50b000a12600070311070054140c10900c1901c480c107226285903116682c00021036110180007010041 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 990251663 1250 990250413 990250423
    0xc0d020d051801050705190e041b0f18050d0209090a02060406030f180209040f03051e07031211030a0b0609090c0301030506250809010b0d0c08101b03110d020a02 71
    0x1c030080c002c020b560344d480410350305841b41c4510b47c07410751103c800040f450f500c601d0380c41001d00340183c40440d0b2145030b40007411402600c1c1d001080480e00c280390f4002099800306800c450304102543d042041803400b8003040c4c469014640107401011500f0006100c0c40c0104420101c50b41c0c0600700d40d0b41c940d80c50000800401102c00750002d2141800c45000d81c1d16001101ca00146400400d03448654860b47d81e4003070104442e041c22411710a0612182000c48010001c100001111001c00c40c0d1702c100600d002010303030fa4503078245c103401440c1010350100701d00d40d03100b42c95100140c0000090030b812484005142070243d404002e40c8203c0b0f1204000f442e5480e1b002a5040302c0c4110110707102900c410303040070000c160b890700000114800c1c0721719810007841504a01c4c0c000308071400004500b1040350120b1036071500c1c00e106803000702c10345504210b040001c0203c45545a4030b15404c000000010305000f184010f190043c00405840c0c1018030030180d00402150b003400a03400c41199644a9154065214 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 990252913 1250 990251663 990251701
    0x305060a060b09060f091309050a14010203090d051c110408150f060d140a0f030801080a020f0f0319050c011202090607030f020f0a0308060306010602150c0d020d05 72
    0x541d040c0a800100c40c11100c0c1900c0034000010721150911504031002d030803940154190300e9008030304840400c1c0f204441c1c4507501181d400b07000540000c4501e030911a03201c00220542d104a07138410010003620a2021540a18007502440c100c9e94a01e0f80301e482c11010341c080060401f22514105802300542104001001240c0045042c0e0348045900001c0416180c0121042440340f84c0c21400503282d46812411885114800d54890710447c1215404d6460440d405204684109520344203800381038006221600400b101c0e0010541740311645c2c08215071101502c0954080c0c5591911180c00740e80c240104c15980d030703a03056450940070850400a03503074945002e8560200c3c0c4802c0d1340c1001c0c0021800ac650000d070000d802c4910f0000140c2c3c1c1291540401d04048046000d01840c01d4003091060000841c401d000e039903244400d0829108242c00c100042c3d010605650113034451070034071610710b04916400824240f2290300d54040c011008043c0c4500080e1042c02d41c03030002085950403e000c0e1841c00c0c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 990254163 1250 990252913 990252931
    0x130f150f0e071a040302010c03080606070b040318080c010504030204020c010f290105031b0a03091712010f06170907031703090d09240e030312180d0801061b0c030506 73
    0x38040e81070403d08018850341c00007030f001420300c001a1020a004441140e007101000c0c2c03406281c00c50607121004011300642d02240081c555002d12203418024842e010040c00420000e4a102e4451b40000ba001c0d01c1140b00c02800742c0e03008903100ca0500c13020b50204186a41c0c03200103110440898400086074107a5207081c25155030303d140b80b80403951103074050728850541410016000388404405424640044954204168480404400056060810540d10514542c3c04e545480d01707903085140380b1038160003003003a008103038404103c0e03540d0018a5480100d07103031000a07075540398840418100f000540000d030804440921001c031035126040114424402c0f002a03d808651540c0304642d02c1a5031700c501c02c04000050401100179400803440d000c198103c0c10600c1e01c242136603003ca410354002d9540c0382072444003d000c10481103c17583d05142c1e26156840501350b0314911030000380105506000b21406c20401a0a0000c10b42091515020311a04101c0403202150303640307013880e91941d04a8401c81 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 990255413 1250 990254163 990254189
    0x2010c1202150903090f1203130e0a0c0e0d02010807090f0e0a0c0f021005060607150603140d1b1e1b06050c12130302091806130f150f0e07 61
    0xd80c3c414080255003460000404045c3c01341492001c029402d804020300640328013041058241c9241d480390810018611400e044405103080c0c03d1a80071500004e500500340001c02588020304c0d640e08050046003607090a048045441c0c852007128484090381015001048034000441c0c410080050148200b16540c014801e007410083c0c00c540c4441d10344c14a4016074031030244400f510085400040c1e101310080e101e541485420785030b001500f0f138840039520240740e03201000d006100ca03407144518074609103c0185001c5013030314801054510a50820026407410b075420f0400c10000702800001160380010804c03000c18907082400c0e595002900c000c0c030780da020050008981c3c1c0100d00b59403901c021500500f8048950104d010501d5000d1081070f04600c205610102c0103940d0894020b008540e42c1c0030f08101c000602010300d14209000d0220004d040d01c1101080000d1005120701040e1648035240700500015068140c0203841170b41c1602c15014101220b004100c10300164940c1111000080c9079 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 990256663 1250 990255413 990255421
    0x90905011b02032a031c0609022104020103060e09030a0801060944300a1b1509030206060901030506070c0f06020d0b0f09091902010c120215 62
    0x4101000c21081a000b580041c032070241008000f41c0d41007040d0b8a00c0008540315040740c0403481c02c503800710100408004000c905200707079030380d40c1c441d11010b4100704800314607103001c084405208071f4204594012140c0c490b000141164480d0300604020988420943c0c00350404c070b42b41d5070312a001203102e807000a0186000040440c071408200d03080715103044d0700030704111254610901d0f00605070078403444840424510310030b4220302c0e20105050b84005005e084404108000242402c10f1100d060205540700404075a10800750b2007201c4010150307050501d10b4440918250100f2000d008003c0c10000b605144803041501e96045203440a20a60a0b50000d554902c00c201c00c0a600380809841d03680b290300022a424080c01d9000c2c1440d001b901c070b2040d00a05940c914003682d01414002d060607482e1380d0f104106003132028403070b980b1001c1200d00c0640c4d40340018507655540c8070005c54014003040a00fa400659010301c0c2c0c41c8815940110300c60842500008000c1d590f20b5102c850000300181560001e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 990257913 1250 990256663 990256691
    0xf1d040f1518021f052d030c070308181005070215040b0610020f1506010203043231020c03070b1b070b010303231210050301020c030d020706060f09090501 68
    0xc019040844c1e103c060402c4080411381d5104606c07404075102c2100c070000c02002c002c0c0c00401940c459108032440340e90f90843c601d0300503c00d14003d800c0c00c08440307100c212681c260401040c1d00100743d00c10ba1000a0680d196541246000803120503ca109454882480140503551802c2071189809540c003240d00f5070b41c00300482e0381d540c10b00750085a94000ea085880b41407003039200d5581089051044909058a40c04803050a52002801c240380d4040d0350309220a0f00d45156040c6105501100c0d00c145014517072400c20340207038440e1100340b44004d84807a410307040c104a506640c6150300d80011a40c0741c0103079140c02c2ca6800410303220383d11b01c0c0c41d41c480c3c4481d12007007000444000962022040e41d1592a50350180c801e086081030030300640001d0b070b241030340d0407482c04c014144588411044680a080500013541d4162854010500a90040242e00d054200006c00c5580303604080d07a00503600d80042c1018401428980c000c609045401c0794006200b003100e400c40c1149900400c000c020f0101c00c0690303 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 990259163 1250 990257913 990257959
    0x4020708040506130f06170c07060905060702010c02011a091f1511060619060507111002011a0306011a0f0c0d170606040f0506071506060203040f1d040f151802 70
    0x550548200047c00500080c200c10050154984500008581c0c400ca90f507801e81080000ca0301e510060b9541c549410302694240500d440d84984003c3d0a6003a807a40e1000c00c2441d4001040c1c0394010210345140d185100d0050080390003041428984101c140042000508603d800d240c0c202d5644203c1001c180149020014500600120340c03001d20600e1800000f501c0c0c0f17401c42c41d400d4600c1c80002c10451019103030303000d00d4526800d0a600020351a0030290780c46181000a0b0441ca003e9881300700144103d04d10130f10203100111504100d1a215403250048425512510040880d140650516000402d4200354113541d80007400c0815020b596441040c41440e00981c840c00c40f02440d80740d803c000904107840104444c90062800306613000382031020300701f540c03000e9201e032005030300c0081c0405c091010551100c1c00f5080c1c940c4101c1040400c0038010510102c080c0025040c0d40d1060446c1d03041142100200c40321145101040c0881e00350000d0288602c070222030164082c05088202204803039060704 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 990260413 1250 990259163 990259187
    0x60a0513020d03030b131b0c0201020325050d0e013f0917030105010f020606032d06070c0c050d03020601090b0d05122508030604020708040506130f06 66
    0x100101003510a03000c02000100440042c1c06041d607600401400740c03611038640d82c96100c0700401141c2c00c40301100540c0f19468103507a200c00c210600c0320020041c0c1e804022110981c1010711490120442c04500c0d03014003030300b904014090f105458079500d1036a040703c207184518000362a420141a036031743c0d410404644100c009555055031164248028994404032030252001150016440e000b0b41e07541c0c0c1e07040c0309481d0401e446000200c01003000d581c1c030902010302c1a03ea072000d0103060901002003981e072060f00700740c844034103200503240c400700900800d03a540c4400c2c2001200e906042250000c0c04919440806461211070340350041050f00700161b950b2580755150b402401c1d44c2e0b29100d001c40c0201510080c0380d42c00854003404001050003081a88441a0f02101081d640e9035801d0361840c0410031460405071a80c080ca517564089000801625404407007500e01680d41d54107450110031610030344e003001d40e102502040c07440e0202e44840e084010344640e512501d0200c1c0e01c40f00e098424820600c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 990261663 1250 990260413 990260431
    0x90c010504060f03110c010c020a0b1f050d0f0c0e10090c0f030b0102030c01020a0503010512070e0a0b030a1a06031b0f130e121306050909060618091305060a05 70
    0x3d10034018180302e5401400000c60099680d410f00c180c582040d825505a00080300050748040e04100c01e116100c07a02c160400364071100125151014100901c403ca490b02c0380b00d115000340000c00c0240300c1100340c041c004e0b42d404010b411400f0b0b11014a0303001c0d04000d64500b07c50340c0c00064049400003c80c4100c14014010b84c580c0701c07825000c440101c000d414180d10715811400180103403242d05001740041c02c007003203207a11429120b42c182400d00c06d503100d0600b207110150740501010001101d03800105038101030111004035a115441c1701080c03410f285404020010041004000c100c0114a20454010349007101510000c284042541741201001410323580c0c46603804840303181e180b901d2180c08250064001cac002c60b0390098400100d050009080b0825040c1c8000140c8800040994404502400090403c241000c4c4117101080c0c0b01d00000b010140500c000207644440d5402400b645c249001b001821048a858445440049086551411141c038031803040483c11000c00c2d40a1903119000030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 990262913 1250 990261663 990261677
    0x20313060c020c130c0905090109142a0f0c070906090f050702070b0c0115150f03060b07080c010b0d05030a0327121106070c020a15080a32090c01050406 67
    0xe204c00344000c0000b2650b00091000280380012103840c0c03820954001c1c00c202c000010601d000e0560350b0031000009020345861501901c0303d48645105010202d92004045a055100c1c0300c102c0c403140181c8034203500034040d13100d00b010010303500041e07030014415214001014480014a00311080030341d10b055901c00096000800280507809068000d400154450400400c0340440202c2e038141c41c1e081e5401503a0f03d041844a02d0f840369070054aa407003504980d280070000d407417030241c0001b080c4c00395141c01411140c00140225800303400b50400003001000409140041c00d052400680e0307903000e0389400b40403a0610840c040308003007000c0040030f52039400d90340401c024141e03558910074a20f11141035052240e0f501d1103600c562010085240300314116183c41d080c41065004021112500e035000900030100525110481c0c2c0c0d210401a0700800404070100d003040380800c101048030101c0c0e00350b2125500c2c06502203070f040034581906e03010b8403156054401c910380304001103802c0c0c400c501441002c44e0394 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 990264163 1250 990262913 990262939
    0x5092a010f0c120819050f0709060507030806060307120c0c02120309010e1320091801080a060e1f0204210305250b07030515060c100915020313060c020c 67
    0x149070391540c4017600d00f0008040d40700d0420b4402c2152000c1e107240c21141984070400440740c0d002401000580303080e040a03400d0080c1950010000700c8001c00c4180030f0400400820503e901411101d45401403551042c0001c40c02d410380100150303114442a885000c10f012036551015001c001c880f102d4a040e9504480303d9011001c1c408155001400c005141c2c3e6034500c103886158110418008245141c505c4070350b00d490000c104001c0c0c1c3c4081c10340038010b11950b00100800c407800940c3d260141d40c041008034800b403041d200c060030088884480380d811143c020b11140d4001a540c000c000b5559142503c0c5030040d0094658030b406101c01000901142d0200301c4081c4d41010040900411300c09803080000381c0c80b56640300c01c484c0030b0650701400031946510a11008040b1403507072040881c41035409508128240380f04079a50380c41840e401c03e82941d40d11410f014000041110004c00c0d4224000395501d007002442c2119002c1145002d079070300e81c981000c1d642c4142c070100e00c241e01d60310300525021021708 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 990265413 1250 990264163 990264167
    0x305061e061e070c170706171305062703040e040f050327010305060f03060105010f11010510030c060212030109020d09020d0305300103030305092a010f0c12 69
    0x401021403802c0002e8106002051000381401400c0071031050008402640ca002600c103800a00c80c8240c841540041409114040d44100c41d442d04039080c28030301c034550b1546040c011010b50903490190950247c00100080c024003082020701c404202d4540c4031211940c030b15031649034025030290036082d508070004100840d110014441ca01d41c0180252403030002a0303502c2641c05514201b460744001003401695010b503030035201daa60312003025610102c1503d00e4500003a00c80e00e05018503410f10682100c9650554407401c02925034891030f400800143c184814500404c0d0f005100854031039041e0400414420b1001c80c40c441c2c0d11302401286401c5900f01004000030790042c0b4114500259030728074801c05a903503e04a00803c03806a22240d613aa449424007002d06455200d404134511000a58044c119491844441c1126050701c0c0c0041c0302e0711444001400c082001c0c0e81480c103409220542940100319503428680c685007600c0d1031031a0084101e0941b40c041e107010001e0601140c0200300003c0034 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 990266663 1250 990265413 990265417
    0x3030b191d0c03010e07050c060906011d0415180212150709080601061416030914060703020a02040209040e070303030606030f0b0f0906130e0609010b060309100e0307060e0d0305061e06 81
    0x4603400c0032820503082203003441c80c050040390ac80d082a8040401003203146440e8029072409030352201402160700d000c1d100c0c00003079140400c410300d1859690603141c41c0c1c141c1c40c0440781c0403664020300303607541e9803102c07030f00b01d5030740d13006d00c8600b242c1d44041c9404655014000d0408400303c80c820406000c0aa1030a00c05803071aa0f103114042035120f1040007070ba20130680040c22154124820f40790394071070703e0814086010428460050074002e00003001041d000ca40c001818587d81fa40c102c3c1c025940d1001000410040e1022400380100d900c5108004800c16825800c41802e40d40340e80c0e0704101030203404c00701d802600d0501c525241c00001803100c0682c9400c0c4408965444500a0000094410080c0c5204211908140540111307085081846003000702801180c0b42c0380402c40e00310781541032502d82c031a1a100003c1041d007049686201f00505060b0500685a005400210800c89507921001e11a00e035130b54141040006407030a00000d269184c800001c0800316042581d6036a401002400d224841d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 990267913 1250 990266663 990266671
    0x2030420040603081209150106020c090a0e011b0e0109030b19110f04060314040201140a031b0e011b15020a02030403150902090a140601050703030b191d0c03010e 71
    0x60b460302070201c0400c02403001007000012055a201480c034011040d1410720b0541c001c004040c10100004000880d80003031901418a000c0310001410f895102d494001000c9000d2103041300d50034110a259045c220100400c0210800c1d190048004501001103034004082d02000b4480a101d0020400480d8808264003400c078020100045074030016003810303a190000f03e8030a00740300c0d0000b1705100b982d030300d03005907841000d0751455440203040035030019000d90b00116829104207004554400081c0c407036008080a81d459099001203804001d00003401e0045800901e0b0100b61030408503951107140c580301d0400581c03c101a50710300300500311542d0280d0300001d030607070452000f48004404204151258411074845070310029100a040c8103104e0b03030820050012043d140303401d42d04000d0b4020580c0f030784e9004d0001d1800701d5441d00c0078030742a401407100a20306a0026002c1c42a02c0503490320b10490800d5400303030a100301e00841c060000c0701c0510800c540c0d25503002c40500040000030392801c445031708 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 990269163 1250 990267913 990267919
    0x3020f0903010908030a1103160e010212120f0c0a27180204091413151107110406091a040b0d05060c030f0105010f02032a010603030507120302030420 66
    0x140241400010b400d41d060848156520344001007401111442403164201c10101039020a0551410400790502d40c45080c850609008101c40001ca40742e1003402002017050140406603141c42480510807a402002c44500e111880c1200120350a503003074900303440c0000655516652001e070042c1e1340c042010001d426000030701041220100b84003d030340e03051810519041000603200c3e442c000c2d540050350780c4401d240c2000342a440501280c0700e194403070000102d4100c110001742c04420b04a0b031004080c06d45c034003500e1200201d103107010010109860b00a442c2308a0741886440c1c1ca40030b40b5070071912211004031680183d1192805142031603009908201c000074010038135508a030725898205041190040b0040d40c00008001112003880b541c0d5000d00380a04c1c004680441c110b602964038490303a400170512148800c914185540203561f6040012460002803003286c4ea070785070241880c3c101190442c1c90900741c1c00141c4010b4030034400d682c03103140c0180c001c1c1c0a4802003032402d526420012640c44d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 990270413 1250 990269163 990269167
    0x1704030f03230424030b01021908040510030c1103130e0604061e15080c030f060f0303180411030903040b07050f010213030b2a0c1c020606120a050a0303020f 69
    0x110600e901400f40009202da010004000460f01c505031030710035a4200c2c140103042c540f04002c007550740c3c000b0b92108000c0410001f02c00c01d4543d41895400c0c0d0046030303c00c592140d074013892014107d60580001044bd1076940300c0302c0e44000c01007001e0380c40e1700500c481924500c0802500f084a1411011811380100d00034200141c42c6488610701208507540071240306080c4a00d030020044141c515040000c507080d149030541c6a07040007203200c2050310028091182034000f500110744995240700b0200140d0400500b22561401c0318100c40c40d92407186a80f5a03c02c130710341040c0c0f0024070340030000c0302c0c480c03030017000a145441e0a152448803d508a0710742650644240041c0100c00e6600b4070045c01002c602c1c00307400904520310f24118242140040c20018419500d8240b00d456494055511103440707072101c071050b150506400c040385444a00e40082500d080c9a8500c03c45032500800d07041d01402d000d588070466860050640e07a500e10300400003e15503803009080c0320119200e1380c09405101900c0b40858 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 990271663 1250 990270413 990270467
    0x60d0b06041206020903100e0309040515101809060b09060703170a0f050618040b13020a14010207050121090c03291003170a180e041704030f03 63
    0xa640b40756a104100c075510b41c000340c0113489107000c20210441e61103641d0f0501030505035070a03603622401501c09050040e5110404254981408900009400c03c05041071143c104224802000b4503644032200383c81520300ba0703000c00c006a9900801095a4826600070300d000000d070144102c950104005404000545501c06d040d03000f45d20401307014040100010035000100d40d035440c02c660000d4501c921440c820904034400c0009250130990142d00300598008a41c3d8506809024200107600294004000c41002c95000d09064041e11100e00aa007100c0c051a1103100560f00558261141c0000c01e141d0549000501081d0308070b00d0074148940c0000c60320698941d10030700180b6842c2e02820340015441d08010380f0301c044000d002e502c100c090310710390001d40c55034644e40031140b00c04000900c00c8400080380e0740b03245e0003107003003c2250425100c6112a2550f880402c50725000c01d0310101e0b01e0343ea00b54a03030418803102d401640c0039a0740200d0724484010582d03030243c6203200702482d01c1d25850b00c0300306c0310 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 990272913 1250 990271663 990271679
    0xd050a08031e100f231201021608131d04150f020415081f09052214190c0501050913051f09061a1315110f0c060d0b0604 53
    0x1503400b5072046000da00440341041401c0c401c0003070303d8100c100204490b83c08402c100f191440c1c140113204041d9446c41ea400c403400c862a000e81b1500b15440d1000c0200e4581c6010000d0410003081c2c86003501e6080e00410f42c65041003503103004a0360365214612808000305000c03130241007218201080f0741400081844c03002600c0c0050342c11a5100d5056440a0b030103071604150004000d99104a2050080b028004c0243c80d480d01041140500814182e44800151100c0400452000000b1f0840d40e003200c010a00c4c03038000650416003545881170f00031039a03041c15041c41140600c80b50b640c4131018980c454141401140d0640216044a5004100282c0092480094030a8900a061030a10f0384414541c844925029550703940c03014411618100d0100f00142c4610052680f07a1080085282d0310305507112107600050150b0800b550a140301700348240e1054000105074084440503090345c540303105141e0003a0300d8881440342d55800003010010224416625840100c190760005c0080d802d241d12401c1c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 990274163 1250 990272913 990272971
    0x10510060e12150f0114010c080a050d2003040309090b13181401020306191a0717180103050901020a1e02030c0f06010521150a0608010c08060406050d050a0803 70
    0x511860136001c100140540741c440d0310b144032007401c2070904005408d681d50301c402c00d038802d221045007000004681c6642006132038103c0c030400e044072500f01d8826001101d1401481d070080c0e030200d010540a400000b031401d000d0160302c4c1030410003012440060b4032208510060200e030001201c02c116001e03810000074940074107500c14858071400058591a02c9820702c041185410340703036940b009506000704140e40c0010a2640c803145102e84281d02c80c035051600541c0f4200b041000c410125001c103401c40c2c0030790344440e4103030455026a02030146031100b02d1110308074440c405c07061000401150648070f02e103940c0101e0480000a41c81240e203044080080d1074202144050381d148183c00c64001000075180a158000d260101038020761012101c824406544840c28041d9440c00c500140c00100203808643c0113800400340c14009000440d08450010541f03101140d000344580d140c03103070100741803c02603540740c12580c1c800d0042016401c1d40d09c03410040e4000030b150f400c50740000301242010030751060f6 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 990275413 1250 990274163 990274171
    0x5030f180f06010f0f03020303030109022209020d0c0c0203032703010c0306261c092c3d03050a050a0c0b03270f030318010510060e1215 60
    0x400307480d030b035410058060000d41c455400910358071883c0c01c040c00981d601008590448042d0780c0c005940d025a40c1d1814501c1a05903502c50008442c403c0001d04414903400900240c46404020458512603140c00d680c03034055040041e4042e401031065000d0301c2040300d0403840a41c27164040540f0381070ba60002900307460001001e00000780d00c4610400c015000000700008104440900f040c60501c0290441d0396480f111031280485529400c0c40600c01d400b501441c0041d101c02c40c0040c0c141307071034001151000804009c41c4124420900c0008004640c40d039107071000340b01d0030900c3d1604811000000d082c0000000042d596620103018000f000036010856260707640c0c07058010301002003141c00c1a04062030640d0291148020800c1000810707200c224890034190303600e62403421a40010701e141c3e80b5000305d007030140b00148000414000c1c9200005075041c1c016241400034091541c03411840304014104d48920008240d0389001c400c0b00c4e2400c011440303000c1d01c900701101c154152001c916548131005032 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 990276663 1250 990275413 990275443
    0x10031202122b0c020307030f1202040e060925030b190e040510150b0a03021b030331020126040b161b02040e1608100b0a0605030f18 58
    0x140701120100078a0840712445070440c500300303d54542d1040294603445184401030400a40c5107403203000764001c034506c0c10301800170a01103486a40b81e041307100c50300da026200790f48600301c43e100080d0201c601044a0b004035101c0451140c5003034205400b600070381030014820360720010441d0650075160411348400f0003010010340004081c101400e1842c04c180c0030400366004103003000c0703a084007403034070185c4641203a1254861542d00ca201c050100c1c000e0040d80f841646222422070310545080c00000954062a10300b8401001503800c1e915910840e082007481c82c0001948034402800741d806100b00c640840c04000c4d6174045a02070a08101d40c005044404403481d00d1460b0a0001411441c526440c3d03e096030f0415142400304801182c2003c00c424000a2281c0c1d1a10028031040070184101924890407101a030381307050310303505825207075007000384254034a624220f00e00d401031500d0090401165010f4895500d581c690820604c06420002d100c100d0220601400c0c0c0c603040c0b03082040d440c0c01c00c2d540e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 990277913 1250 990276663 990276697
    0x3050f0a020103110f07030c030c0204140f01060f1e03020705030c0304090b0f1305040309090c09080d0201051012030201020f1606060905011d090f03040e010e06091003120212 77
    0xd4030014007129011820042c09140522509413144e00c40e1003165101070309800c00100303038100e81c03808a649c543d40c914001e41143c2010080340c1c01080d604e584602400245844801a030303203039202280c0d83e500104000b0001204461900440614840b404583c110f6914001d40b9000007600d54a196502c140304c45442544000340400c0304002c41d201b00d000c0d000c01180d03448550008100003404417940e071295900b00903035a00204040501411030000280304002d41884000c850050150012509120312003035800780354440c08902d03206204a40c440c40c0580c842c0070b10b00c5e05200e040000c8248040d030803419913508222129945009030098942005807070143c540b0b040b200c0c60700c042994400e901c0002454100b1005115050048040e600d8601c502400c00c150350342c3c1e6021161900107000c22121250000103800301d4081c41d1117125a060740d800952900301a2907070030901151001c200d900e0080300d0885001400080c4c1814202c6a10700d07801d1046902c0c0965600c49000b9030381c0b1110300b61081d0082 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 990279163 1250 990277913 990277933
    0xc03050706081f06051308010c0c1407031703070c06060e01140405091e011407200601030c150e03010c0e0414060f04020f07060507050d2f0a0903050f 66
    0x80650b42582c00800c88040120340c40c10705480b016030740d0f41806041e05021000c60442401e01c0c520f200c14004080680081c010001d9026001d009a0b4400c0015559885082071412140400003000d6085991003601949400180d200c41485904041c1142c02000300081d00d80b00070440724020030700a0071902c0404e10180d407402941642d0705240c00d00c1d144c040c41c2850100f00303404501180104d001044283c4154100300388064103401848100e140055a0f03c0400500c05070707a52044502d0000c220303042c082035072171952510180c4d0740c500920004140c400c01c10300c00d10208010300c0d0000c130b028259041c0600c200d400c0000017401d541c0500c404c44000750550410140500d82402594400c420f4008140c015060120110740d0603010300030200c2c040c9400040040590800408803030300c007a004503042200742032152005101b0340c011800610403a00b0120680c848005900a10800f17440c0d00803591912440c0701000d00c89038002150a105000400c0c0300040072400030700103080c0010459020f44130b5035031 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 990280413 1250 990279163 990279167
    0x18080c160815011502030c030706050601030b0d080906131d0a0516200a0c0e0f0a06122a090204080708030403050703241b03050a0b030c01030e0304030c03050706 71
    0x249038080341c80ca621420845000940000545066500707071958480c550455a00682c40c5214442c0300c80514800014200b0603c84103510003800bc241c240da09101c5003220904021182003080c60244c0340300300c02c10041c0041d103040c4001b0315101036a92810411a65902411700100d00d070b00845082030b02101e4100102c8000b20320410358802071001114444030b860400040040c10600078580111300040300d04c1124600400c1a0b5808641c449181e9400179110f04801c01d072410142c40c005070180082012405481890050f40203842405009022401040d1101c2c1c03002c41e030090040e04140e200c21a044800f01a2010f40b101070700701420003507a2a4505500285049080d9100100a1308144402d0002480114002c0b04581d08450300d20501800c918580c8011140b04070b406040ca80b4050020064403641040c0b4608065251800c102990b225004c8100391046400c1035940350b008441c0d826402e42c06544940c03c00c1d840c0104503030030b1a840c4c0da51502c1c6581c0580040c3c585038810041040050b03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 990281663 1250 990280413 990280453
    0x1b0a17150409030f270e090a240f020708090d0c0308220905070905010c1a071d0f130e07090e03040f12020a0614090a0b09010f030209030601060318080c 67
    0x1400c05a064441050384090305c28840e0550007100001da00c13420119040b4030040081480706a044241d0149084002031903050b04c40f00001c00a40700c906044d90181e0408251081e200300c02d402c602007030b14103150031007000581002c000d800c0340c064000e4080800031441582c00303410301a407503105480c580400300344001007000c05544804000c50401c810800d0160340300041030210381082c204605170246a14040200000c40190300d41e00b1582d0104100185a01030308420301881c0c034815030104104c0f00c805001d64908484001a0809001402c1003407030342003588004a0000c140007a80d10450311420303079109440c64100740240503070003c40c0c00e001d501181150100105401b11100044817425400b180340c190300c034440c40e003c0c0f1032140d000030901e00c490700458900e09402003c03071001540710104104ca98111405407400210041d6403402003600038801c50b0b000c45801001021307640e1901e5001c0f00640781000d101342d00408000d0b000300c00030740c1e0580502400d4250f107028129415120035280042 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 990282913 1250 990281663 990281687
    0x60e0306040510180b040b06040c031a1c080304060b120609100c1704061e0204080c040509010204030c0b0a020105070e060a0e01090803070302061b0a17150409030f 72
    0xc0e0001001d0000154001039504a2008410004600c580c1c025070074540b02c600100024100040381c40403c010810641c00c1d01e803140b001124104201440c0d40030450031a103000c602c414500b41100f41310500ca1a02c415401c01c00c149000003070410b50440e87e150350007a082503800711a080c0d1254144040c0c3c1c944201458041c201080003445180741c80e0005a81d41c8660451540700c403139a40c20362409062203403030b070325900d01c001b1000300714a81003524101000300a2640c00e43c100408070007c822010480e40200d404403910b070750052034100f400c101003000404e8040e00b24076003076508000000c000360342184e91100610f82c101c50a9112100010060b0035510000c10810230020b0013401030219698190903241d4111503490119100d0b80860010384c0e0f0f4020b150001902480003040820400d51300042e00f40c880c1e140502c0703040d850b0794040f04802c0340307000f103102080105062510b1b00d000c3c400c4407141541e100740b42604801d142402000030404852003203805500244034074020880454110a100c2d00c5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 990284163 1250 990282913 990282919
    0xd06060f12051b01050a0e06041d060405060f240904060618060206010605121810060f080613120c080706050601080f1b0a0507290c0c030a031e0f0501060e 68
    0x30188a90b00020506c0c464004001c041c004980140200c85d110b080036600984410351100200c4d8405156504000104507105403240782408005200380c14210000403140d400500300600c1480c0b1810703c520111841001c01c0804103050005802e00c2c0d40d14090140281500c0d11150002c071118142caa507040c81c0c64100d4010356000100400409038000110b0744c10b0042c010006646072180121102c602c20032003000c00700f43c0325880815031907003083da1288080b1180c4109028000d03a5410920381c07906002c450407018440d86040345000301d40710740346c051032500d41d900d00042c400c4003070313039940e1b2003070300140d500b945e940e40c4d102e0820066580000702950404105e900ca6400b031724024030813124030701d6007854401c9803c0f00481c00d0849280204140d41c669a41320319125140c4440300e01030b4412036046068070003005a40340209555110090444030384030b000e8800ba514098242c038054001e01484c0d50401e0803155021a0014611303014400c5c0540000000b0703000c20154074202c0300031310050940580b584 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 990285413 1250 990284163 990284203
    0x1807050603060427060203010f0905150405100308040e01060f0503060d1101050d020304060b04140702070303141c0f050105010e06030a18080a020c040f02070506060d06060f1205 78
    0x10340d1920292544108122408180301844810038a030f061400380c054581456010381207000c02100e03070042d50595402c10701d0081420790780c41a40d421354406480d000d520104428010300c0c903003001d40141b070307100a500300980720300c907a83e50380c40e80f0f0b81e0700c0343d4812440c5074200030062003800d40c00004004403000d01d141407070079803d065000402d44e00c00410001c203160036a2400300142d034020800e441e03025444c0d9074111f46a280600307285014000401d000d0b44918a001035a1000d405c069030700310300071040795000308503081c19039901350b03000e1540c0248140544030a0207048880d10304070425554400488001142c50600c0c12110000d1380c806070002814000c601c2c1010285880e504c090300e41c885101400850107050341c400c0c43e0744004004502600c0080d00103207403100d2039000240320118441c151000c0000c00c44141d1800100e01450400610b00c1e0005000b054444c40d110300142c201c2d0740110f00000f0300603500d030016a010780da84c0d40040344210045036840140101400100c011046c3d6060101c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 990286663 1250 990285413 990285419
    0x306050901030b1f050310231e06060d180201030c021c03020306040603050102070819080402060a0807030e161406040608010b03090c0d060209131a12010e01090305031807 75
    0x284240074010000c55070050184182c00801380700c0480840205006401c0e940701c00124800c1001602600a144444048095003a070b481502120941e10510040d07150200c0c07407420034564103c1d160081c2205a12407414003e000c0300341b00510940c0203910a140074a000d5070300728800501950815006841507401c4055201100602d01900814074441440d00580e03a0f03641000050040000e508003030312640c4089203103410008114020021a0004071190803001d0200d43d0483e103030501107800940102c1d0030300c80040300c00c1c0640003044d007002481c1004120031391225030461800300a100d4541b030514460004000e006d050341e1200a07840c0d400d0382c1541c80d00e420118090843d00d810b108554690f800000051116002807012410b441e074000d1aa05195115041c82406500110f042921490748041f0f030007090006441282013202c420440c0c4500010b0301820400c0401c9441804000d9540b50300309840509401e1107203a003800c0c4a40c44041c1c80b414031188d815410100790912110a81c4000c6080c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 990287769 1106 990286663 990286673
    0xa11010e03030c072d0609020d24271410091a0702030705120d0b0901030807060e031215150c0606011d0114030a0b0a08030a030605090103 61
    0x76100c2d882e1040920030781d03409017407814400140b42000000207a0b41c1d4000701941400104446000d60080e100d80c503616011114400300780d1900813910101f0403040c17080d0640341003000385802440c1c3c0402d101c5502b01926500143c031001c5074110b1481560010000c0c1c00800701450070a0145000a140640d030301410010240c06584515001550203440001a2420340e0b40180040c05480000d00700540c480d80014910003140b9100c80da00c5800e920780c2490180254403d007a92503540d1520300341b84048070515004500315400810040311100040e01109420211b60b04080749071582080000e89406001070507400d140d100440c200d0300e41800413500d2407182c402a20303040c40682480840301c6803480030400031404541c80c1903215102e20907e101941d800440c49030000b618064a00014280d0201540b112000c1d40c0001400716075190325014180042c8829284c0c000694110368031 = true := by decide +kernel

theorem cover : BRFrame.Cov 990107913 990287769 := by
  have h0 := BRFrame.cov_init 990107913
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990107913 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 990107913 ≤ n) (h2 : n < 990287769) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
