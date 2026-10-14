-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0854
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:11:02.973132+00:00
-- url     : https://prove2.me/submissions/20024263-9744-42e5-b3e5-45f608c63c7a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 153417266 ≤ n < 153597122 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 153418516 1250 153417266 153417323
    0x1030e010911010e1207140d06090506040c050d0b0c09010201020f12100b071a04080c150105090c070812060a120c05010801060e010f12020d1109131404 67
    0x55820000da500500c035208401140d42c0c0d000741ca82c9560050003030184003049010911080641e00712200400c440e180b1402101d201040080c00c0024224540d9282001c0b00c040a106440c2c07540040308000821102c283c00402500d01114400840d48030b0307a890120205004100d00d40d100740100c1c280c03100b03074000d40645110514540700c076900c0d01c401003191150b00c5005c0381c01c03030a40d03042c06000007005003085003102c291540002501040040300f01c0d50541501002d081201d11510030010b180340d001d0280003000f0003c0340000185855454401006a102030250071440e0003c0c1c20401d06001413401c100f12280c903840880400ca0030340d580d4000032001200d981c0081400b42c81030003440d040084c1004101d0a1b00c0003601c44074910f90300d07040c0413503401c890700301464081307000c024200b40c850303000d440c064070341c40c41a1310301514024070b01c40d0403400d540d80c02081181d41100841d03401c400d4613003941000d114902c00102006040808550240d080002074005009107070807001c444100c0d00d1b006507505 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 153419766 1250 153418516 153418541
    0x9051e0102100f0b0906040e06070c050a060e010c0e06160213020405040e0d1d0a0b13172406061605070815090606040c02060a0f020c07171203100905060103 69
    0x2035504100710690150604103039061281700364000144251070244074404c00307100200000e00d600d90350b100c02541e03140542d11060300e40f403290040a00c001401c901540c001c0d070f1596800410790f1098a10040d2618402d5801d4a10402c0244641010f44139492441c04100750121010000138006d01301240091260f81c1002d41c020f804e12010811400c00061920800e649a980710000034640b9007005006010100c0e003258003110881080010086003409040201060380e403140c4803558a80007002c820203605c280c00e110340c00410784002e00130f51551a0a05000031888004500e240c6a4002195485100000f2450982c14580320090100c01c109000161030301d6412100110441002c681c29501c00702d41031320783e81c8102c6000032500d00b000e0198107000e0443d034008003195100d081c03041c000b0f040310460002c006036081c002d01e401c0c2c0001b00400c400901600b0712810b058240c110145051011740025070040120170014444503070101409901264140000040c007a140c03140120701800c09080d00344c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 153421016 1250 153419766 153419771
    0x7020a03021225062310090b0102010e0a050714040204030503030a0216050a030206010f090902030706083c0708070219020103020906030a06171209060d1401180c09051e010210 77
    0x243c080042da984129446803051144c80c007011900f03102103264800413600c21804002c800001c20079400650064400c02c00b0500010514201c0c00300240d20300300900c8000d075610b40c007082e02041514616003070100500c0c02590207616090440d01c1d4507603288800f0345210000c1d64000703801c5180828074a42c40700d407103074490141d80140e021030070002e55609082c02000607401700008000b620901c03601c00c0c143e989a01801800d1680d01e002c10984810344004d113240a00c0c00401c55084011402e080384001100b2420401001102480c617604600325004110401748002c502c103100c6a1500007800801020041c0c080025031506440100c0c0a030142035078483d0420008410302100c0340c21034000780190b035409005e007242d024800c400702d582c400051802403401001040003019606060000f45810050f0341303004688038103030248042c0803108c00d80c82007405030102d1640c0601c42d2824054081d1600d250f20f40054082d08210004941c0381003800070720b21003c001d059030000b07a40288001ca41c400c0140804 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 153422266 1250 153421016 153421087
    0x41b0302031203100b0405010e0f04020405040207060219080708010b03040303230403180b12150303070506100501090b031807090608010f050a0c0e1e190302030607020a030212 77
    0xd401504203546200c990142044e004c100c080803002550704a800596922560700740800520002c3c1440d03046040e0004d80802000c2616115800140350141c8500001a03684400e183d0000013071110036a0001001480c2003071021003070f48480810f05450b5002302ca1a82c03500c0d01d103416401881c0c1c50502c9a4410848000744802e5030f1101d4105114900070b440c0c6025014451513a840d920601d8003509903071240074001c2402c080d00c094842e65108402e40d00129018800708002499a04a9903084840b54818010011800700f040c10040080c442804d008100b5030400c0032151040c08020a07a100300c042060302280040d5040000030001c00c0301040c10050151160030030f60290541c4240103038154100310204981e44007a1103000741702d441035654100d26040301400c00c0030a442c4140c50b900d0011066903400368076507408021000da0003c561100704510b00d144185400d080000301400c0a40d0084040300002c690041910000442030001072030351b82920540d042d04080620345c01403220b4103614207 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 153423516 1250 153422266 153422293
    0xa050d0e0a0b010e10060f1112040308041d0c0304020409020409060e06070f0801080309010e0d05060f01030c0b090904060f200a0206061912020604030803040c0e0603010b09041b030203 81
    0x1400c3c160392250f01e010308160340308941101c46108031320891001682400801060502c5003000d102c100c0b00d98009e440700e54103070030003040c81d64000d038002f0f54100c6000942005128200c202d91001c02203d50b000018a1610303400755005400000e0020b8000d0f900c1d002003804660702c079489001c46235130088040020400034407425a9602c011a0520007041181c440c4900160080700e80c5812a60030300015450700d5a04030046a2810420780b00341d402c540351004100c0083d4062103014032914041a2060742e540c0355041074000c035030f0140d111000001c0c0403c4a0b105c01e803500b168180d0b10039041580880c1c458400c50109005100b4181768420a041c0603501e5598149800020048990550300701e030350315200c48042000c001aa0104400c030701540000c00c21026138039240030300400f0300042030300341429980e491744c80a9500444d01101d90090000d414800a014030340c1c440e03004401500208440240c3e40d01107440c1580250001d050301070700012020150001100c0c80c0d0255074054142c1d00c00c02040d40 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 153424766 1250 153423516 153423533
    0xc0f0d06090b0102070f0b0a050f0d020307021006030807060504150f02030406051006020604030807050910170108030a0e191203050d050601050703121503061a010e12030a050d0e0a 79
    0xa1a10701810407020703000c190301c000707211303002c3e50441d140c06202d00f4a00100305015038490080c440c1030107018030040b0b10f61951100602240780e400c040159803131510b1303c1c001382400300140440c007880d4900441840400d50707080c142c91087d03500c0240080d11b1b448a0815041f0611040c034074001050804010f9200328909030069406544100320034815502e44500101d6000514015640181e111400082c00f1078880d0010f6500012581402860b140c0b2080228900718240d82802000c40c0d00e02c0031410140c070200c452203006044401c040d600300b0801140040c403640084111034030410b5000c0401d4944a4111740308002401c007510502c010300418079024000b40c010040c65030000340741100049141d409001200c0070326500d6503c2a185903045140e0074003d000d0703014a00c002c050f00c02808800034005200f454050b20165040c2c0d4850a9501d000424220301103403245e00624588030715000401001094552204842c20090f40722030011084d40001c0100591090380d038410000d05100703028444 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 153426016 1250 153424766 153424769
    0x1806031306060503010903021c030906090c05011205091207030210060e011e061205040f050a150b040b0d020103020c190609031b050706030b060702130b040516050405090c0f0d06 78
    0x10107080c0900ca680300e04050881e003142c0400340244c0c0004558040c000b10b0842c3c418882c2105090019140a040c1c4928080b211928401c80d0358189c0e5a40c01d0100f50781180c1c02d4420400d0080042c006450a604c2054680d030074000c111007603400c00f00d0842c0c1094004e000034075800040b000104101681d03100d0356040c860085c800c1104071407140b038107004c842031500858070079a002d13a154030895500482c0003000502000384180c9400ca0b2403420364000030000c1c04014501401003c0c1498000c4c011041102190400115030b88a9450100c1140c0140c445d03000c003003103d03502401c0c0113885164001c2558242110072400c480222824610b1000b04001680125211802940c4111138800c2081110003000103008c07001e007845d84011808c00010340309820510407850f000c1c100030b00304001c03540030500207002014a10a26074440e040050b40d410300c1d101d00c0b640701c1e810381840c80003c40352100150080c030075801850301480c05240001c82020049045501c0d43c501064125a5030034034408010007040c48d07 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 153427266 1250 153426016 153426023
    0x6040b0d0218010816050304170a0c0302010b010e09270f0304030b0a02040b0d0c1e0503090c030705010f141c0e21040e0417030403021f02040605030c18060313 70
    0x2100c00d000b030741d54803c4050700c0c800c2561a43c03d402c00010b0307280503a015000100115103004416048000d6048442c0c0035101080580d207c0c080c1450581c6000303402e654050300d40c14100719080e001d44640d80c0c1c1301c0f00e03a1030b000f5129100c80c0110800a40301d100c0100001140f0403040e104680c0750320b904400002c01001202c1c01040350228986a880200b400ea10441c8036405440c03500303200042034901244d00c4012000c1c22414007249118125030b900610a03003c041c0d01c0089a80401004041c80c001d01124000790f40450141c4891400c020002e04841e0103412000100010300f420380c98034810449c00c07a103010300300c47c4e032503204008212480f40241c031800c89203225500a20350300e4040b1700000d4210030f90405060039024201030606080d02e106510061041c1d40d0400c0740c0006003a005403400086024a0082d40600109582c40c0b54801070f0640d10620840820300c100020416590b1041c25290032051084006035528101011001a0b0350342c525102e41c0000d00000b0b000e18500c0c640e082d0101b1030710 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 153428516 1250 153427266 153427297
    0x31602121e0618011109040b0a0f0b0702091006080f09070e180d0c0503041505070c030602040503060705030601171305011506141806070201140f03150603040f0b0606040b0d02 77
    0xc0c9000c83d03a0a039800e8080d1840001c209121010151030b003600305c000910005086015007641d205558002440315a00c40300401e0700c001404425800d000c00c0f0f4541c0400076451000910f03107020b50040460034003c000554200d1001c0104202c90f40a100c1000141001c41c0d4403c05424400780490300c0c140b06a8020b0701e913100d490245100d190054800b000e80c035402c98003440c00c1c10f1034606002d450580000340501004000c120410020b1840891003014600917800140c5039030500c03051601e02807010b044002886803e2042000f1350f80d1111900101c83c040001041d1980c948070700590741d030145850010210f509180490303000e505412200310444519070754040319503074495a52034052150766540c2100600b0381011800e1400c10b01c00404002e441850400452044841d03510119080310307011004404c03000041c4043d1520300e408120402c1c02c12112245541416903071000359000710305004040240c14000101c044d5594000d88008114100c03805903110364070344140b002944004481d00c05040e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 153429766 1250 153428516 153428551
    0xb120604060f0c020c01270b0403060e0d1d100903060c08040201021b010507061a060408060106080c190e1c050c1201020301060503070c060b0a030303021803031602121e06 75
    0x44c80082d01c8146190f040e152514001480401c0e000011541d510b41c120412510000103203200345040104000d501844002074905c2040a005041c000c9800c52a0100b100c2c921010119508044040d07054a8003210f0310b501003000c165041c0c50611040d4000741a02c1c0c90000b2511002c0d40000300360340709034802d0742500d004103442d00b400c0e81001c940e4054580080c8050000038000b48183c2d10424422680241d41c490200c04c1c40d000640952140d0030004240d00b0640040044940012a946c2c09c0300300704207805c0c140044089109000400013420000b080303403140c5c4c0102d040e2241660704c00012031840b02100c1e8038241c1d040042e82d507105164620f00820301c007a00c41d4000c000c1072091ba0705a5500340d440343e00d0b50f2190402214a0700e51074030309403515640c4912400441ea10a00420001c505c251000b51f200c00c1f0704003007a80f181955205680c000e810801c824031090f41c0d4140ca4000c41e5034110340c00350130021790740045407808040211022929131465840d02c00904005000d80c8210811240c6841c1030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 153431016 1250 153429766 153429791
    0xa1101060b0c0a02130e0604080a020c060325030902041a01021e19030e06072010091509050a121e050a0f06200d060b030412030b120604060f 62
    0x2e10841c211854242c00c503145240062421000f034038000d000b402008911009105101400c0c028180c40440303003800005000000d080d010b0004000040741260018103500d480500702c94a50751102c840300084110042100115002c0d0f48124007298010b0010040640c10f01d0444152840e004040c4e03000d42300c1d80b685c880c00891440f100d00040c0803c00c010782903429006c2c3d8210b1080307900ba07404406111107604200050740b42c40e00a006403d01880c4c90200748a0202c140700c0480030801000e50080c456800705401c0c10b504040c54604542c2c8505200c046e82e4030300c55040b0b0b41e0700944e07040154030100c03c0b100050390811884140c411107000704240350914035100c51801e07040461503001422a001803158802007003802618120940c000c1e100880d09450000c182d414200c00740100c03200882c804161121104024032900d0060b00301400c1c1d00c0d1660801761900f00700007031086c900c05c0c201610b0f942c2455507511005910441c0c00e64040440d607a6090500c0d00c8006007200450301184145003d0190404 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 153432266 1250 153431016 153431039
    0x5030403051b0c130612080a02070e1006030b1c0b150604090605030d05160308180a0b04120c030207090902060403050f060417040e0a050403180602070807090e03030705070c0b0a110106 81
    0x1200c88103650101810a031f56a0344d04903070070884882e0254041c100c000144601803c2e40303107100b055044e6213200b64909001c005001c540303182c0403060103141c10620400244092070b100082d440c0c3c00140c1e001807030341c1e030320601d446488140000b5034109070042070001e516201500220b050b900300300c0607245134800103141103d0314007a01c107070b618240d010a100c46002c640545240c9070840020b2940e071110340c0001c94a10718240901400f1101c41c1c42034400c120510500e046904c60542c450b21700b000c024142078a000b0350f41c910364044d00380b4541e0740b1101d5108640c0c03940b0480c0c00440e400400d40d007030306480b0404961078050840b070603104032603003145060410040d00c003100d060300d2012520104940b2100e002200030070340104103c00740304c1c550081d40c0a840c0d80820813002000725500410701e160400144600b00b03500d65111080c59030400d0b000003900c21000c0180ca6000015241c00c80c0ca0310b0f070508251048004903403103840300600c00243e0b4a80c480d400312608540030002402440026230b604030f40c503507 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 153433516 1250 153432266 153432269
    0xb1810051504090c0c0c08150c0a050406140c07080f06060121020d0e01051008100209370f06030e0601050907200f0105220c050105030403051b0c1306 66
    0x751120801051104107415400350707036040c555180002c0080e4081d654034054008030b401104199200b1030f4013070403080e084441240d018102080441c20000c41000c050710500450047d00144a00c0100c940b844500403030580341458088000c65440594503203d49071940b10b050840c0313400f8082c03180014815401101e407062080301202000c1f02c820702c0c1d4915840203410808114069544400203550002024060540251007030050607000c2071511103260b25041000f00440f041500522513403140d6511614407440244100003003020021007d41001020130550401d0003400000d00070101b544d0000904180585005480400124142902d100e65641091007415030000c055000164032610a8103d20a6620110f110040160400d42480d05284c4900d421141c6a9174400c00c111700d5081d14041201941607840142901100ca521011440d022501816040c0b060000210b800c251050080314018044003058406003c0c85550780350301c0300c082c0003203030b80700d0b0032440c8501c07084402900c203c00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 153434766 1250 153433516 153433549
    0x90304060203040e1504090503221a1b10060f060819020a020c030f0a020103060b52150209060403021009080303010608010e070504080a0201030b040b181005 69
    0x600f4180390002e442c1c0074070001408000ca00340480c004120548840c0542d40036a4031480156484811900c00c0c00d01c1c41791801c0c5071071101e001e420400c00c01214544203070400b80c148401d030142c1e6115260700c5d1419100c00386518500ea0f1003509400c40d5803d02552100c000c1ea940b0000445c046681c0b0f0600303da8411044d11619448800c200b811107140c5000e03802403000310b010b401911072060000c40020f040c204550618001e5130031140c44c1d28215a4980700d0000070708051004241004034081003c030031703005011032250100c0304840340004c11145001c0070103840c5000400b40c40781c1004d00c1080390309900d03270720400f15a030820740341e00040320040038001d540342504050010b13410545550208a81c0848020300c00f42440748203400414000001d00c001c5003c0c000b20340b1b5010740c40d4508140c05a5069004240341d00701300b028801400095804038200712529024038020407900f04040001d402400b80c0f00c1400d03884840c041080700c40071410607003039114100c0c542c5001c001c2541c9400780400d01c80d1390f07030209 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 153436016 1250 153434766 153434773
    0x6200d05010302182205070b0a021c050a020a121701031202010e010219120f0608160614070206030613060603150f0620010b040c050c0c0a21080f030f06090903040602 73
    0x485407003017500419088140510102e5461668035506014294011540040103801c6540349205d0100d290500c072002c8145450b10618041c0c80300002502c0e05034078103005150a4045882d2507066101e19001810030743d8030403a000703841d40d40740340c86401da0018841910140d4280b0721400c070040410b201b0ba94117441a01c101c0c407a00e02d2550b01c2115049000c040b0f0071203043d5108200317408000c1c2d500c106005000ba05000301640320440c071140b06640d079140d01c40720030001a0801142e280704018140c450499060b21034903180d490354000174404c421544001c0280903d0715000294660b030541040814041780c0e004104403c1e1a04160796055825000c3c503030114150307484068001c994200b030300350b02001c02c00000821070341110005040d0340d81502c010340042c0d40400d60115082052105079110041140d8040d041da20307294074074140c2101020f02030241031440c1902d20a024082040328a0007201c010f80941d00e280c04030b5111156035080da0f00c140a400104001481c0da0ba00104a070241e5442d034006 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 153437266 1250 153436016 153436051
    0x201150510111f0903080c1804050408070f15060503070f060e1207080604060e060907090c0905180a0b0102060103200f120109030e01021906200d0501030218 69
    0xa0321000054104403a0310b12480051200814443d0540000443c200310f001c42c0c1201c407814020320b036a82c050082444080108030305540010074030714548001505440100741a500e43c28070003128024400003800c6000c491159000b004032100001403030f10380030542000810388800c24184c0e00c01703807402184ac03c06403000051001d00c0c05482d4074000380c5002003801a560305000d004506001455115000030f501c2070090200308082c5006400322a80900000e1902d071510202d91543d0340301c40d02c10051119558071415405900c101c0003071000d0140501000c0b81414161591052000100d9075506c1503460141154415880401c00340d0403282c024200d80040c51100c5240031648041042d243e07400745032080e05610070f0b03d071040380c40e003100405000000d50220324140501111200b401050443d0412a0040074030b10081120100700782e04403600240b00032504e2814207244a80c9203092090603804140c03880c0b594041d400c1641a00d2003900c001c00087d800941ca82d001d1182038540d15100c90a0803130 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 153438516 1250 153437266 153437299
    0x901060f0602060a2013230d0308060109150c0c050405090619060909030201020711011404090504060608120703020d020105010506090d0c03080316080c04080d11010b0a0b0a02011505 80
    0x1140401d04e008000c145c06400d01108100c80341e512440003400040640c50301009446840b04859840036010a0110b40720142c11000400392419804002d007400040c03000306141d644240e0000019261000310f140303101c402c0a0000c1e103404401c1a0440e4040c881070804a103604003809038a0003105038100911040d1103d003604500040d5049900d21050340d0b0b00c0700000d021640740500c925030741c0a038000583d640d2240c10440a40c0400781240d60600200520320181004e980c0111000c80d952101c000940d42c03074501d09040a00096840b5101c03038445c500700b142d40001d8140040020328420303000c94415808202c0207900741c0b0002d2241a034041c90a0114501d0340c01c200d071301d0b80401c0d4031800303002903015101c1d541c09981d9081601c03203070401054a429000510b03080b40000760003200204000e41064644030ba141c2c6daa044c036200b010100100500d150341208000d401821604400804580d220303500c0f0410106a0707000985e5140056003032005440d448110213a0103016200301601d0138243c18036208 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 153439766 1250 153438516 153438521
    0x4081c18060801091401030809040e01060503070b0c0d170402150c06040602090f090108060a0b032e05060409030903030f0903080c0a020f0312070609020a0302030d080901060f0602060a 81
    0x90006003800054504111405000804040a012540c0b200c224a5052840c03d004a071034a00c24004038103441001440413403481800d50380e400800303c1c2c02180c207920004841d40584819804180c040c4a41c074400b041344060702c40a4601200c6090445c1d23841d2204400c112408603068251116595030300340414058103001389001d090000c0345800728a402c1802c4d40091a03c40c04172419102c4942c081190743c1030346020041ea8080c11804c450003000c0f035040c031605540724140034040004c0d4550341c603001900c43d00c043c130000e68000038030003510320b20001000b6090303415880fa8a0f884482c0f803030600062540c0c0341501c51400d90540640c1c82e61001811580c040c1c401400d4650490140044d2100010028003564011300ba1641d002010784040c0030144144001040402609842904619081040300316010309850103e07810040c0442c11380d030030f800461210115500042e4050180d0016900c40d260441c0c40a40544d881400070042103070358440311401e44542d8060b580058129a0101307054940030f8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 153441016 1250 153439766 153439813
    0x806060f0403080a020106061803050312060d050303070c020901060c0f03031109030307060b030f0309150a0311030a0911010e01050d020d02250507051f0c03020c0301050108010e060c0408 82
    0x449480d46055140d89528146030006000800141c1d15401d050285560100e40d800b0312460700c2c0c60b00f4030440d080d43e440580b24091000c0d605461000840000e8860355a4a1180106900002607965a0404c0b400c0108842a60308090b40125444000055010700c00d100d5040c5103904800030388040a0b0642c1c084000e0003451081d0340803168180040c0940795814801850210711480b00052848a850203040c107003040c03401c0d1040203400034000e181442d2110740c25140c2600d43e003828103a407000c2c40b04043c1d0040c50090a00c0c03007800000f00405c0040081d80e401910024000c12902868805030001180d41c880c94040d45800107200307012041950b44550086d0803001c040310005810610040580e0340920714540d5190700303114418070307030f1402c2c40b20600c05040038020075030fa00c403801c0030004042540c03960006011810003018201c2c03282807510078000d041b12318600900900855070340c6c4d50041c0c0a00140c440201240c000c400104085660303581c110740c00c55450001800000c0c00c07000a046030003964 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 153442266 1250 153441016 153441037
    0x905030c060304060209030709060f090f060b030613020d020301030c0503100e0309100c050303070f090605040602190f0b09101a1309050304080601060503151e061305030709050124080606 82
    0x142c3da0045016019401b508000d040e0382cbc0441c824061902c1030b414195000c03441c00c0e850061400c46c083c403005502000700d0340e0007030040d101c49102c00c0f10b0403100d00003445400c0390082118404000481085402068941115411011109a10002c003800800c0f6403110545020645c400c1040700c2071400c015008410003c424149100c001c1c249458041c02c42d030080b1070b808001203400f04143c0c41c00350032140040c00340c440c07807030901d00301810000065508c00691b074103030f803455400581c1c0c0410880b542403224034040c0d02240500e84c90400c0150b05035a0800096042c00365402c1070400c80441e02140d415000b201d01c01040015815005071040e8000d00200c0300640d420b0004001c013080c50407041240d240200300315036940b0350341e01e840070010f010b1503049000203106900e022a410200213940741180340140301140c1e1180c0e1255541c0c01081c0307185603540990b4050058100c0001c6024150748060b04075003c2385c000c200f848101d5604074400000410702072010500705000300f0001c1c00c1c00406000c1c0443e0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 153443516 1250 153442266 153442273
    0xc030a150e011b08090f06013303330b030402040905150a060608010b0712021e03031e0603030418020904061410030c0e191203050a0905030c06030406020903 69
    0x10100025003594038106020903c4031412803803101503540000d04960001d040c0c000b40070283d50407000340d03031607039010300c2403017000032503402011707020b100300b200c0d09810791405440e25102c1400d05c500540506032804005092280013800710075480705140804154082680d40703443c0040c2000802c02203a04080c2050f44c0050381c3d4680b980003d4030400a21000c01c10b00c0c440c1c0142441c0000540702035a070142c20403420011264010072084220b402900d44c05c5520040740450b2500703180d012490092a1001c40780c2d00000b07c456818540e00220003940514401758003c803180d020010284010981980c00a406034000c010820a151030350758907240d440042440035241040340c10020301500d5082e040114040011103140080341b80c4440c0080103013040d03003810300121402190140121070a503101e0b900641806041703070074000161180b8400740030300e000729000320041030030001d182c5d8001742003040118400b1040031800386000503008440a01c001c00d024a1a69540e907403c019400030458181c0522 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 153444766 1250 153443516 153443531
    0xf0503070506010308040e0a060303080601031808030c0a020106051c02090702071d010501030c08040b130813030606150201021201180902030604260903070608060a08010f090201110c030a15 83
    0x35014000b607402035000701840c81c1c0b070302d041c8010170004110203004030a0341c03403411108100283d0400f40c8240c0c4039109090004242001101c2c600860342038640007022140c0000c00c01142d081510054030070341e14141c4c003c105041c2c40d079091100a10aa41561600284180c42da20061800c180c0c0c0c2c0358004410310643c0d261903503c194103441784042500c40216000d60781c0040c40300e5641886464903040e400c3c9050843c40c00d2685442d0032030341c00a8103400d80591040c406a0901001c40102c82145003c0c04807030000300d03640d040540c001c180074000c3d0602d03000f52050260f001441402038039a1210303011590713010b592030100116a0704692062148645846001440260390180402403145000e68000c691240d6001086200004481a18400888280100001034600040040c240d85041c1040300d92a21858006142007446c1d61003249103600b48030600340c41000541244500500c00e8070365a464641d508203075521944240902509584000225404644c640041c0c2c20b610030b40c440c0014405 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 153446016 1250 153444766 153444773
    0x3281d0d1412040f051807090308090d0503070c031a040804060e0a0503010e10060902040806010b0a0c050a11100c030806150c01090308010f0f080d0804081201080d02060f130f050307 80
    0x2a0401e80c400350b10103d003100d00b00310608100031980c66075084001d901091340f1f00f5600240c5401c0080c080903180c18008078206050303480c0d1000745242c40d03800a0880740c54212610381500c1c140c103e808100d40c100110040c100844500070480b5000710303408988103003400d04080c1300300c4440984c041e000e58400300c02c500000346502d0a11981c20b80620380c41c0944401240c03c10b0301c409139049075100300612841048204400349000c175100d03040d40d0140745140d43d40c0809040441e5030300700310f210250940c01141081c00400c1895199109034003419191143c00c0721001c401600c01c0110302d00c2c0540891941400104245811200d600f110201104e020f402c0c146200a40703030840d08a0706040700401c508000500586041d103028038000e101c030220f07900c00b00e03040100084c0c589404401c00702c144004100800c2c1048141801d0300d5160103d00000700e0b00d076030b4230381c01d6640d42d03d08004002d0160245501082100001c1442c1c60311032450600501ea4129407551881194208408150f613180410310088000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 153447266 1250 153446016 153446053
    0xf0601020a02061b0705030606060706050a0b150a1d010801050108090a0b0106170a0603020a0e0415020f040608070215180f010c0305090d0503071202070503281d0d14 73
    0x41466100061010140c1c220800d05c1c0c89803a8002911a0f4011403c0006994480c41200c0d40c0d143c0c13090011070380c0d494250000c0090038a01d0f0b50142d00401404881c1901903446010b000d656007980e59041c03038821030044a04a60010090742400034001000601155002d90f03000340e0800190390407128001065122560101c50a0300703c0c00c00220082806803564102011064200c05e401c00108115855a07000a05100d0035228511a02090500040034070044980f204141e402d2210306555561021091042c9507100707005240215800d100400c0b0480c1c80014a00364040003d141c0444c81d880707100c200400c8403c0242500030704d114890000c0e050341804e0007440140101518045054100000050706054003100c00004001c0140f0400840c5a0302a4038051090400e1100581d50841402c00d142144603e001513802c29003a0701860091990281101500801760707544d00324401200c4501e00c2c4030812901d03400d82d0200d101d000c0036010510500d20360150040890840b00c5510762408070a94 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 153448516 1250 153447266 153447277
    0x51917090303100501020c030303070e13020d0603060c030902090a110d0e06040308010503030304031d010e030307030207170a2003030909130302010510050607110f0a0e18150f0601020a0206 83
    0x40c141c001005119a030b021041c60300e00030b44001d001030a840340300c003c086aa80d000042110041100b40f1100d602651030301401e0b10140e904900042d50b446500c0f0000c00040e206902c803c4074250300e010040040f240c03082c030034003509941c0140480c80303940f102c005001c05000c4003000d01da102c5900300301c0e07a60045034038420350034010301d4180588000d1419003001340c60404142e2110f40a90010010000080d038804406200e9184030800c05440c15000c000490750740f940e000d906501032200080800c14180c0001707408088905144141c00340411301300c00b040e00d4040e403480041c00300b04000300798000d0039203030030752500c2100c0058222414141a00005200d040c0192858000b64071140510000d0640c203000f078991221030180b290700b0b45031910f03010550b24403c0c91000b80c14071a0a01e0824101c2e502c02c0311200082d40020401c014150f04d61051000c10036083e58100c0480e094230080d03aa4034a40485c070b64220155440c441605651581100303c0742c180014600d0b81107000709101d100041c0c0e2440003411 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 153449766 1250 153448516 153448531
    0xc010902041b0207060305091509030c0c0a05011b020d060606210902090c0c1005010f1d07081f03020901030f020301050702061015030209090c0a12050403051917 71
    0x1189805030041c4011a4400790342ea8030002001d000348400250001000c0084850758640080c0340e5803000c0308a81410b100e03481d200020034540090040140c070010182155000c0c070001da80040b484c640c01c2100603480351089501241e41010007079288802280c5402031030b400684500350605007652628125107458200381d000c14400354000304454048140510400c0b81c281e03080166541d40c2d000075049010090502d4042d00c000120000c0705c00e03090103005035406c8030f52000e01495841d00c2500b0000005030191042446481070f1107002c1000342c00400340250050b4580c00c01036140d10003003c03024000c8000050031b0b52085c80d40040180c540340d000d40e0085000b20031000d82c1070054410582075900107042102103520a00601c02c0101001c841d400448000c9800d540c122440d40703800703074007030301030b20b519181c0c0510759204200c20302512000034028000146d81d460010060401180c00319001601c016001540a03c50003402c41c00070709039090103074018188913900802180492001110485214 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 153451016 1250 153449766 153449771
    0x3200d0507090b0f070809010215042103050c090d020319061a03030309060a020a17010e0a050903190c0201090306090c030c050406080307020618030d170f0403051e0f0c01 75
    0x41078542c0400d005014040100703150b0310340b00c10751800d03030164007554a001e014550700160b488440da008101000c0c03820203035486e1480320700d00b81c1015900500001747c00c052040982510300400c0e0300c00c0c450140700382a42c20402c0d06201850040c00420f03543d00c3e0089030148a44000101c072307280c2417032000e122984100717804990214080c21000c20501044540c82c0607500a00902000c3c1c4004a58aa4000c002500040e22030301c4001049480c2c01c54101d101041017003840020801100d40a8100d124405041060149480d88980182d8a124902ca880b101020014580020500c0383c2410521036005140008406849444e12000c9841c068400c036800308065008008102e4040241380060808507420064186081c041036100d201c3c6000081c440c403000155000d0488810000c2c202c4a00090203d41441b0042d52000e8800c845c1d1a040e0b102c4401110009540f500c0304504092103245d06a0b996400c1181000e107020700c03c038000d030544500d50001e12816540e0f4200d0342c09041c5100245001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 153452266 1250 153451016 153451021
    0x5031005070f17060904031202070507030b0603190f03050f0d0f0c02120702040b0316151106060105090103050702010f0f02040608010b18060d0605030a0c0303180501090603200d05 79
    0x35003442c40701d012020910590f4841210340c50031248049074404429101c9941c01d031741d680380c200c4640c1a01c40c20701031024400b041c00014401d0001d04501924400ea01c06c8507180c69203000c065a4061a06107205d804803262558000101c543c1403a540c4648030307040190800f20308000801580c0c11401d0b403043c1c142da4030040f51500a201d4014100411040e00103000e80d607223030f4007441500d4170a84001900550b19908c40205c17545041040786156000422041c4041d40c0b9500c2440601004001cbc1000082500280304000d200100b0350500a4a0507180c1c103240008400040d00038020052502007903540c2c60310400e49a00c407130300810100c04058100113a5860400c02e000d4040c11781038020000462003031140c590000040c95100c0d250850860314151103080300b00780e000c06000d8540140d505400344100072020001308080300e40940b81b0076111480541c00080b8180d031008014031486000900303e60003001001d009501503030302d449030750a5118240380d0510340d880d0190b00c41c0c03801020300f642d00e204 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 153453516 1250 153452266 153452281
    0x60f0e060615031513090b04151802040b040207061d070608010509060409080d02270904030c110103090b040c15090b090618090a050603060703110313020a05031005 72
    0x505a00450454400302d018484000e00d032518000144001060304038a903d2001c5681c41034550103ca074504c200034803581040d403806000c1030206440403a110b4080d0740781440c444200b4000c0d02030f51011880da403107000f038290b001c0202600d03c0c0c1c920785401982c20000000855094007901d0f5180d010140702c4585490401340f080d00c0c0204030b9110786c0820030014018046070b62200e07840343c0c00c050b0448000ca00803c0c2070070a160144925103480b11780c988005021030b14044010080101600c5417441d0800d480d80c10028840112000c0790001c00107240c40c4e40020000d00050a0380340840010b00d0f00092882e00d0303690302152807038203480658032011450010050304c03600721003004c0740b04645d16004404914101d4491501d0088040051080c1e1001c54175080c108651030b0010740400000b4603091560030095444c100030041035815034064016140042c201030300030b006d1a078030350710182e03d40d82c070316600c290390401141050700b01287d102c0000980041c842d503080085892001e107864000415040000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 153454766 1250 153453516 153453523
    0x30a0c020111010b010c0f0602040b1c0612020f22060308120907030c06031a0a120627020f040e01050408041716031203061a0703021203040503071707060f0e 69
    0x10788540741c1c0c0c1c1400301042c4181d0740030325168906d50340a40d070f04d2003c848500d4a04007a029a80140f40010070204540341d06402451150300d00741ea070740c5010040707241c03216240d03900d510341040301940110b01450340c070a29003000c01242d200544005054200e8514510b40d820a803555680155442003000c602c0800e03042e150010343e500412610b0003040c94610b90f51b21041c0f580070742d20034081496680c00d103400711040040c811101c1c030480200001103241d110303200542c0f101081304042d9a414984140301a06503d100f0b8081e0300000c4442031150034691650801c0204906051003d400a844450040c0d03011001d00449000f9407040310090b40b90303410f1407040196989034170242039031540700c04020710b0035241c000042d0003503e07000850b1b19901034180d401038028094135031084048103400c030440340107500c3e4240a852030301c0c801d42c280c1d05030407065065401140000c1e2000750a80d002080044006424482c0e42c0c0040c94000400300d003010100e460300407c84444800c1e00701100e4403240240001c10050 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 153456016 1250 153454766 153454787
    0x80c01080c070b01050d110405010b1b01060810020a12021218030909040b0402241801080121050a080c010f0e0f0a02120c09040c151e031d030a0c0201 66
    0x40c0d04142014420f80342c01c10420018444c460203082600107050501480080c5503a411300060828030055940350051071055010501c0303080c03c04031a10b07410100c0d5006015100072904161b00a10740740030618103040080d813014204806116414110780d42d43d800ca40041c140048034081d103030285281042c011340002c4a0702c0c0c20f100080e00b003000185070640d655000b69802035009810582e0a50b964404581c0c903005031100000ca00c0f040d4040301000054420091000c0080b102c92400452910801501c04000a029100e006a14203403240c0c24400c0082841c1501d078010002c494100310a5104d25100c1c0c1d000d5003290321140d440300c01c1c146080f6030341d0041001c602c100038010158601d171108410703151400190020b120320315141040d60010810403c002104034010705101080c1464070340a0b40d0410310b445411000c4401100b2001464000c400ba0f20200c4850140311112506e000d03011030040c00c00013100032050b004c2c20f00079105c40388108042c00c0310760515251800b42e0f07072181c000505490000d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 153457266 1250 153456016 153456031
    0x8010629070309060c0809090a0504260f071a040303060f061b02130219050301050a080a030206070f02070b0705010f0f05060d0305030604090227100e1f090204080c0108 74
    0x1007101d5000264001c21030402c4454520303140c801d00049181c20340162013980440355014400e0707018803030800490792140e80100d1252040c20f1002d60320203a0000c06455420506002c800103001552142100e080100340a81c8101d43d08000c103480c200c03440003003200945050b00000d5a40d041030152024504400c40501003905103220083c8590f800514001c0701068000c2c0a1007048003450f00702c04140c2c0549100d0700740d0f48404614001d00c41c50082594209104040c883e138041800010912000703e9152803440c1c03d54003400700780e074443d5801c4e03c0340c505000a040442c440c5140000d031441c05580545185445032001080f0040098011000e0301c03000050000e2541c0380906000040d512420350381c643d954181841d0f522507075180b00090081680c41006500501224408000790018035855014031600c3c607903000c010344440000b08202e8801c0d0140c49105201840030801514a42011416074110395100c41202034440d500d60003aa0050381c002442580001d090300744941e04001619804142d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 153458516 1250 153457266 153457349
    0x80a060e011a0a0903020406141e010503240a0303090e091204170102090402070b040b0f100302010c020f0a06030c0f021c2304080c040b0f0f060c07080106 68
    0x1000d52819880e00400041c020030340c000038103001d040703000c0c500101c0111b4000380200409551881500d201d01c0180c140b40384118116544543d20307060425210300206c80c103a40d480d0031a6a4134440e034414052640f680e031590205141e0601e410b58414003504082c1d4420303952000210315002c42c1407044003000d4091090751700710307194401000481030305641c115090990b201c0d07d94592107951a00a110301c203000350b0043d00018205040c4142c000050b8011803080d001c240c51603480e10340703449904c00d007500d5011010310101010800b542c8101c03e0050b000d0f0004000308c410786001c00014022079290390284e00800d480e6241d10803220b0300440441600780340381c00036010300b0310300405480003141c101802009001c094a0b401038050034800c2032000080e03c00d011103540d10b4980009558a120300c09202d8400c508208241045080c080c03d1104861009031050344007004000411200360411003800a89200710900000d4442003405801c0c0208850020300242280b1030703003500441c07850348407a90800c04 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 153459766 1250 153458516 153458519
    0x540080d020f09180610050a0306080105160e0109030f060b061603031a060c15180d020a0203010c0302040b0703030c030f1503020907090605030109021e042706060e0d051903080a060e01 81
    0x101c3c6c001c40070f41c4544952600c2d6560380c03500704081c0c0080040d504801c10a40c40c0404005c500e400000c9078080d01d28844d05e5108030124110011070710200a4000240040c0301e092a41c000500540c0250040389402003129040c02510308070055070344c0c50024103600083e1504801c2c203191607140201000c091080c6c8045182c0f0140360061541c9103c414030f44400179207480c0008440110348881c95085036551010350302501e5401e00c0007907a80f82c459409074440d5107000111001b96010b4401c4800715010103482c6402d040c0c03a0b03141503004000080c034200c14151107010089a940e454070488824401c03540500c140c40e4110f00601c01c000400a160805002010310188011038100050301c2c1110b81500016036130304c00002d00b40ea00c0c0702d0380c43c0458031807031070124000c40c2c004084425030400d0492200907403031100801d403416041e24541d1007100041201080c0700e0780030381480d041c00c05d0464056003c45041070040e1507003903030a800c00c2c0000c0d00000c481d1420b0040b8000031740034050090901e02c00b964141d5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 153461016 1250 153459766 153459769
    0x1e06060a08040c050604080f0f160e060f0a2304050c030f040507030b070504091514040b0406030c091413050c010c021f030540080d020f091806 63
    0x344503031109035091000110000b410000001800e4002c3c0c1805040607469681d10010b182c0d403030192140100c0725009032a420200b140b00010492016410b43da005c0300141c1c074040740c1e0011400e000d41520341105814402002c56240c0c00c41c000000d1070301440103540184c480a00e03221110503603642d144120704010071311020f440c080040e2078015206c072002211507102c51512a1910006520050007048440700700550326030460041d01c1115901d01d02030007420114116110117038034030300034800031003400e0341d40f20002d0901d5440a42c2400d400b40c400181280c4070b8482000600740e5900009441b80c892581d10603071013012980b03a03045008840c0416030300c0380c91358078151034108440000f81001117904c50741080d03554403003030a15401081000e9018100c0140b40041c00781c00c0c01c6030802420124010428240000c1c503c905100070801e42c11410b24010351142031030030b401c01703641c1030301e60000500940380800b00c2031000b0011101c400280f980c0d1070096400748101c1a074500c8500da0030808181c1085510b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 153462266 1250 153461016 153461029
    0x10b04080d1b0b0903070b0403050409230403030209030304090e0102090102010c1701031104110d05060102061e0c03060105040e0a02070b360708010903020a050f0c13020c03070b0f1e06 81
    0xd155001c021030f16030b0b0f074038040f40078030f1802401809402c4001450912085c03541043c010702c00d40e5009001400045054800c194204007600910341030f0741030040005022074440d601501c40010300a0a0700d141175541c5809070103542d2040c3c0452840e075400034000c1015a024030602027541e03450b05040140074404402c0807a4640305110103030a01c07070424102400c964442c0e0100100d108003c0ea01c0d9210034812220700010030045403041e02500ca8040031030914401030070362900701c2c00b4444a441c1255110360318400540c00c00381c03030703607044c81005e200c049045038000340e17424420944582d006855108a0401c107004a001402015180b10f070601040080c2810361400102080b0b0b00e40810640c064890180e850f1080c0d03a0300c0311109510b0100b07038400301a030220340c6841e000d020354202c502c450038605039162644011150154001d0040094055075090754015001203002d0f58181c0e801c00031107456080403500115002d9032044040c00812982ea8101461941000102c1c0490f00b02480c101020070039 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 153463516 1250 153462266 153462317
    0xa1104230a030206041703070b010905180613110d05010c021605040606080a05060a05060c0c010201150503060105090703090611090414090318060702120d090608070e0607030512010b04080d 83
    0x40000144664490306d607810001c480307100340c4c4240034840c3c96a41d400080700a1038255485c01d0a0707000d00dd040b0a0140c0000356030360240420303024a80040b040360f61012001403440e90b40c183c02c007010f12503160128500b84a84034110203e90098510f241003a402031507810050b4010500c11484e0182c1400404e40c40b60350030ba0b210004d92400100340c1c0b20070001910f00a65903002030fa1003800000c08038200e8901150054040500307800174440c2d583d903008100c2e800b000a000da41d426610881c01040581b51060440d80c00c0121030800007410001d43d1211815510ba5440412001c04001249942414184a0b180e18a00c400e01124220700b80250416107030320034820045000b1a030705003070b0a0b03155582d03c200c2e2010340c0c1c010158030452101075117040c1c440030240203003404602c41a000080d01405242030300e21910071540d843e61207860703500801c04c068000c120180d08002c0140145015241803c00b514003030000610260303200d40c5000900351030111980e00351030400c40584002420781507000100341 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 153464766 1250 153463516 153463529
    0x14010f02091207030f14100606050a14120c070305071a01030b07030504050d05031e090c3102030a06051806030d090e061018121505011503050a1104230a03020604 71
    0x304030024a512003403901a00718484447c1d5864494002035441d002002030150030f8081d00c50400d0388400c2c4240c17044602a60503c2a010303d50800022151000c03000140f100911906102d400c2c00c01544801d030300328900003152008842500b0061060161034600d03107500c0070143c0380601203850950303a00d41c6c89809000a42040c4800800401c0400704e16140128401446d119240a1440c1469032281d4481040c001e2038000c804500c07912440034040100814000c01d1a4041c4805410340d41121340294002040884102c2d522607004c20513075500c8059441030b02c3d44600510b59400d00a04050070800f00300440003d01928020412001c61803142c0540c1c0b0602c2127400820410a81c0310a42c1c3c0011440d9a030502c3d10801c00020800500071012400c00718000e035861143d885c60b01c03141d01e044500030700510529201c0021413100052180d08a541d00940788200170400e00c010249880340b03601b00f608110321001c1040b1409030030f01c0d0f440500c40f0098000700d40882c840d03844d40c1c0100c0d400d8400c43c003408 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 153466016 1250 153464766 153464783
    0x1020c040915111206040207120e0f04020c0105071101050603070b21010f080d020102040635010914060405070801180b10031a0a2114010f02091207030f 67
    0x6041c00580d150944a541602600303000c8402d9070f060050a036400300090100d401ca400021076903a080c24402e4415031980000c200b600f80244034000c0d600007982d142d00d9a4821841070803402e25031582e0014140044c251000402c0c10b042403070001d0800c1040350604006603140c8010810155000505281103032850310405590b0700301c1912184c00c0c04131482d0300959948071580005000184011034a00b220700d01d10551314012030350f410403400d0b4850f501c980341c000740b5150504800d0000c02000c800c1c800c1c0c1200400010102031210300014003000b684541486550341c035000442d00c035500b42d050350140c000c0b2420000e81c649480040c08000c810b001c0c2c000d2a10a03d41d00d046a070403254031184402500500b1821110b0412000a0181030080003500780460441c5884075607080080c20b00c41503d490407480d0000d2013040c0c0f001480e50f28641019101c00c850a00321803540102881084400f420601c4096034030340d00038090140034280c0b100b204060340c2c04110708002040c44c1c06200c271007140d80819170 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 153467266 1250 153466016 153466031
    0x10501050702060c030a0804021008070f05031e04081c090c17070e010308090111010e340e010f0506040806070302130815090d020c03030d0213120f03170601020c04 72
    0x3c204180100903000c081e9100c00221a14400d42103254184114403c41b01d09046e40358900046510740340650b1184041100000c038a128140144051540010303a180d041c10300c0c110b180041d01d9200790030f8506990058002581104100300b00c8025083d1491519040c07000d220540e0303441001002c1e62180c07002c01512481032205081c81400080010840100550174a507143e00f8018800c0d0300510180d80801d02c10b0704912002030060041080700c2003900c010b044a0290543c0307003086000ca650900620703c84010205001e4100091010040c205402c4101102e60400c1e00021134100c0741e42000c2e01c00e51080c04100031040000038a5036104090f0702d400b40c0c94121002800031304440796002517016000c1c41c07060706030300c19020316151f07c0380032898203c0c1d0740150025400d90700c641c580c54a2a8254000300b00c6070005041c190010194010715898004c801965003110207042084410b040350703c0e113420032441081c96449900513200382100a801e4820b42060740010755500c0c0207481c0c407030050f601c9051 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 153468516 1250 153467266 153467269
    0xb091503070306150201020405090601110c0909011509090203010b090103020904140102070c03060c09060f02030723011805010b0402031003060e1507030603050f210d15091407080c03010501050702 86
    0x101c0d9006103c184c0b03420034511421040680030350054080c030f5029108010015503c0d602c034401c014050207014000d03180424005080c424100c0005001050640d210003940c151170300007100302c4000706060b160005010f5401e104141c00e64000880b2144112000c00040c80075035103c82e08240c03c6035012045544081030313407030b20b10f01a010b04840a003000d042c0c1c0e14000b00340281c1e034122140300c42d620b07903c2100300c94031039105880100030791070f00300016401403108030001040ca01561032552640f103c07a203c06204810034a080d80c00000410751080f000300690420481c3c01d0086a00d1007070700b11800d41c103600c2c0c5030346480b40703200091002601d01500c070303040c640d020307032080c4040300380c1d50030440b00300105280c03040300a40071b441d00d80f00440d030604ca000001281c11001080c0d02410984086400d070280b00414040c0c1c020381c10900c15000250399400d04500c0302103548200e9001006008404a504c2148003110b0b4640700004001c00117101c141d00030080c9100e04541100c1c10341d1b1007403c0c0103841c2e0030b0500 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 153469766 1250 153468516 153468521
    0x180e041a1305011b0809010c0206011203090503060124020706120b0409060f1508030306150307020708030307020115050102010b0d0305031017100b011404030201080601140706150b0915030703 84
    0x41c000d4202e5281c040c07840750103107154003410740c1e50b503290b2100b01003a110031985600700d98984c00e04e600160002001402030303200c50320400c0c49281c000c3c502400b07071503221000641000000ea00484a0001c07030112404040c0034100850031500d40b0380040c0c00b42e83d03e0710f80054020505c088400300c039a95108504d04a503540d41c1d2040c3c240f40d801001c204400b0f03a11241240042c0032980e03030b103040007204001c001078211000044034803034100a000d9404a401e4440500440c0d00050042001d5014000000c02d408104002840c491121540045482008860b507111004000e401290441e41450f09d12041d07500c850707020304405130745131518540c2c0b0713a188440111144041c1c1c000010a500820407001044c000203250000070108800811102c0301c06c40055401c40031201040c0700b940428001007026601a45d000c40c0d100b40107043c01c0fa2250382c501d0407450a60310021003107900d80d640d0408205d06007410100007000e8a1644081071174841a0301c00038468800301c451510500c0000000a0940c0d407098 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 153471016 1250 153469766 153469801
    0x6030501020d090302070f030312092108040b0708010e0f0709080a030e090106030209090103080304020406090507110111040f0b311e0b0307030c110d180e041a 70
    0x715103484002c042c02024040c50041980184200d080204070b540d404800001100d83c1a07d9010705084162080c4010f441c180c00309a4007000c40c04248411140100f10042d15030030070b40d8491034246440c4c0b41000900f03030041c100500300181100180094800c4030107554001424684c5010650b80d001011245a20160822241405841400c1c8109a00409074802c801000c4500c0d11080c4e0301e0390000c40c1240101162254080d01a0004102054000000f907070054000f400c00300ba455140d041060540342c090b03c1d200001108907c1c01941100c0a101c0c0303940700e11405404130314180c1707040060203607500203001c0d00a40a1000407042c05c0c142101c1403018094015030005001d030000c59407210710441051158000c0ca503a1483c0c1031318000d00d01c4d0002c1c010f0b10715020703030581076440e01d61085008020400342c120601603041030783c556049040082625000c0c0b1681c1d840440074120380c2d082d00d4019164071801c61044141c05100c0060301c004100c004141e01c3c0ca0888985548907650000c4c00c2046 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 153472266 1250 153471016 153471023
    0x50d08010f0e041122110d060e27010b06030c04080105130302061512060703021e07080d0b010c020a0807080c0d0f0b060d06090312050c09030709050a0605090108011a06040609180603 80
    0x409161041c6c40e00008060030112209280c1040415911b490b0404044812101d8008107800343c2c5804000d010290000a0207050400000800600f0003011660643c030a4a02c0e0171012000300d0b0400608000340501680000400c0104100741190303940a96103c3c0040c00f28451b0b045154040d00d0251a41c0700c44148080854045465034100290003500075802038410f04401c03815022030a0300c8122440889282c140d004028070328198006030200024000d002c0c08504201074034204e0400b5036200403500015002100240c0f0301c95240c031450707a01d0401c6600515004941d02d1031b0402c08030f503103540724010180c0c00c0b00840f400e5544001c0042c0ca2801900d0005000310b1801085070103050340448455030740301c410b2004111603101e00d5244250340c0991208542d0551240300c040c0001119500b0264000500c801c001c038040f038543e00000c2d54214240c010b1043d90395500680f0b02198082e0891810070391055540515150508000030a01e00c074034000d103000209080b442c03a0414a031584080021900b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 153473516 1250 153472266 153472271
    0x210c17091603120917100f0b09090d03050603010c0c021002010209100809060105010912031218030c0210030207081611060a021501092c0a050d08010f0e041122 70
    0xb100d10306031a020481d1a40f8a00180381408040f450740981d0820200c82c02c2c050f40288010134495641401400c0070f60300c0038108030746500070850151034092045d801144460050810160045030003404c0365070081c0824860380c14904266840f58104260a5500d5019104402a9505180706901a05ca0314416503000320200300b0b00d01815600514a03401044c0180c16a081c1e130340e803035004540040c040c0c06050400c079442e000002c000707809003d00c3c41156000280100308008404017012184081041c15008908004422401c41c50102c48942c107082007404d00714242162515185258011600054001c0d445d41040f40240a072080a04854620003441c0399a00d912209000352900c004002c2250300d085040008120380c1400d000c1d4105698a03440005030601c1541d00c024002c3c1590301c0000400d00504c1036070f001250041c042010459441d45880049524100d04025044141d038011804100c0c6001400f002500c4507891003110b420445120b158200011220705050070b80821418001b031 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 153474766 1250 153473516 153473519
    0x5010c380103060506241e04090606170108120a0207030602030a020706050f0402011d130203040308070206090a02010813060e07030b06010f05121b04090507210c170916 74
    0xc00d6408024103a900c02c14050245899000a001601d05c03c940042d00315840c0c14201c0c404689682c1c09030050440411700c4140b03200009030005d140780e000760007007485140c80708070500c401c58212400c811542d0307541154400540c90008036684840580d40000300450000803407030b1a50348200091801f07950060f004542e40d00380002d0860080d80449401c40320b4504210025145a0a81d1070301c81c4141d030183c469011041d00f1100e0040b145210000066000c4d826100f10f24a4003085c0c405188203510039160b2804508044001078900038000b8078500041c3d03c24404c010050741d0254002e078006048800081040c407091410001030b2aa00b100f42441c0d03c60007200105005541400a002d51307800c1e00c1e0108007a2401d64101c2d800d2103a12500d04103000382901003410312900705040d03540130304031a091504094860f410003043d0b43c416103001c800508080f15040c0c0040c1c80145104084190020400021621200240009485480c906030000301c0a0015500e42c50038403000720003020785840740c54002d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 153476016 1250 153474766 153474863
    0x30c1a070e040507050313081b010213030c1e0b180d060c080c130b07030e0604030303090c0f240302040504060612060807060804060e0c1203030714030105010c 70
    0x141c1c1110025105600344004140c4281c0035800b202c1c085ca080040f220b03401501e945071030035590702c142003280141c1c400021242c6c01c10310a00c007034509101802c50100f4954030f1030808114a0010342c00c450085010307207200d0740c91850b4969880c000c42e4244842c0580303a01c024016182c6428451901c1d80d00445180b100a0400642e5848080c202c4031a882c4c40c0a036440c1c000c0492103600a000d40b8403a0422203207801d00c8000e007660007400f056807092070f00794049907a5902148958100b50b00403000720b0340b986036440422580c4840c030409040b103510301c6900c040c40c084503003004e41071191000315088814144459124800d4048401801000d801480090b680d904000d001395100d1340a024031074607009000c0350002c0080303201401c5600710703680c031201d036140d94807003100806c0c400d04004100c0c0300b1044941e1a603250894030b0b280c0c01c1200720184da1686050180613140001c15440c40201c0d540c02c00044c08075a80010142015580000e02812a00f160051048070500c07540841256201702c48040c8651 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 153477266 1250 153476016 153476027
    0x171f030f0302070b03060a050909070b0f03070f0302070b04060518010e031206040204050f011b02030706030204262805120702120303040803010501030905340501140304030c1a07 78
    0x5a40c481d9007114103c82d40d40402d81c4a034002a542e83c0d81c8004038a9082082d80b0b0704c814000e4010280c0c2e020f46507200c0d074911085005607c07040031140c10b01c03400f00420400e6608550003c5a00c40641425071030120304e0755a04140d1040203000800481d0303580c001c01e680100300004454900040c400800c41c4008908170541d6030780001341d0f0705410004090000f0441d042c9402079908440e0003505035524021a44c0064401c2c488661559120501c1d0700449400759408020003070061050381c900607912828401e1200c41d0000c1e0103001074032018088001c040307080c03001030000c100e0a87e401008032000130081c04d1109403251208040d003248589004800801034031401000c1c130b00d108840e1640c1408600d150316403680002c43d006451400c0920040103154040d4001d91005885501550507403111110105404c3d01c03810351410381980e17410100480d0a42d80f00840b00900024242403070140c0e811250603140c2d10004000604200c081b041c500104600d00c0ca8848500d900359414544614060200620 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 153478516 1250 153477266 153477293
    0xe150702040e280c03080f07060c0503190e06010b0307140c0606031603030807050a110109030c1502070c1503020c060f070815090412020705131a03030a171f03 70
    0x959025072245142808020303c0c82040d042e8419280140c0780e265840e10031054200c80100590142c040106030001100c0b0304c112410320740c00b41c41d42a01d9003445600710a04214a0400740340f1149008421003030402c1c0015102c1c110345200c54460394a9940107011500e1840f44a01362820b5800803e503074070b0954000c1a59440303070100b54115041c00d001e00410b0700740e40441d40b10140119140d4400f12f031b1014401c0300100000462400d000c030302d03420201d80c801c0c00c480c00621f0030350006014110f118108402148550260315081d1015421b14007146c46611220042d481a076000c2c80300d01a40d012009c1c00b07501075862019605051b900d8600d0b1002e80212640c404540503000600303444009440c0041c0c14440c0013030154080d201d003420380c1e502e0b66100502a07941c8980b41c1580b184003000211551008c10550040d01640d502140e030940c0355510300c140000c54040c1520a8005100440040f6406503a01c0d00070b000c1083c6660850b100e1042c0c40c140f03003428441c00c01c421010060044140f2608812046 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 153479766 1250 153478516 153478543
    0x180f040f0608060a0c050d0c09030c03030e0306060f030304120212150103050f0715050304060e070f061713150b03150402180601090b070503160f02010f020307030e150702040e 77
    0x90b5103a5900081c641110403480c484004500141f0601000d4000c0d64044090080300741804103485440b40c48000c030506142c9d00840000d1440c1103200c0c01414103024454010303a06441d090034006410001035103902490180d200030600801440b001d42d910041840c6001c7c1d14002030340e85032003a50a229000d16001d02096480b031092903101a9103807000509102100d1940c881c0320703038072510782c401214150300c007034800d41d0342e40e0f181e2400c01d01d03564092082c4002044d444080c290b00920b0107401070200070724000e034a2005c03030fa01400c21104201000e00940c21036840300014901601e003581c5103005203030800300260180303e08030304140d94003c0c40c1500c502a40c02221020074904c1105000c0403100310407211719000403c0860100241b80b030900c060401c1c24032800549091000495140409900c0307844191807511080c1039000c15560082d800b070103c07103845d1005c0c614014254801500f00c0740310b0740c034440c025007a801080007414140000e03900e249500800c00e020b81d030140b0314a141ea030f00c181170420 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 153481016 1250 153479766 153479773
    0x180308160203120c0a02061b0607030c090501031b0c03171501090b07051c02010e0f0d080f010b090d02060702130515010f020c121e030a080a060b180f040f0608 70
    0x1c0c8040700e074201994281c0d03d42d00d00174400d843c03039503091140580160403214400610048032061003501070082e548070360030039500081e680d50000002454110998046414140380002c030304494820704820004155080c101543c01d84000c0c40d0803501300301a04400e2445054110900c40078503040c0e164201003400c2662070a940c2602c0b4424410390348030312240140590700c1241200e428141e01c10403460a041d142c0000501201c1005ca00313424010003c02205c0103400c8903c0d15015960044a0306030410285032403404158140f40710100b5501c6400006441800301980510842d5510401c0b41c4035290b01820b90107480e07412101440182c030741551004110108003a0000c0194460380503032403c140e01c1d40c000c05241c3c88107000d000090140d528045914080e05920b04680010048903001d0036000d18011a900d083e1500000c0c80010050445000c55040420400525650006880d04102085020307100e040051000030781006400f141a90803904140420503245081e0f80924201c68034402503 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 153482266 1250 153481016 153481033
    0x303130503010609140a1508010f0e01050f060a061112180301061502030d020d09050724030b0114031e011205100c050412290601030e0d0906180308160203 68
    0x1903c1c00c3c2c40360103041c01d1215505c440007500e0004180c1210510100450b0516081c0c1e444441c0c09007540c1c4c00f1a03640040989400c603060149100348a1154440e00c141701c0e210712400c10100040c48103c1900c1004100801c40c800702140082c28090503015000082c1c44560f80d001d442102e10440c0759480c0d120344071703520b444400a156918103904800c003005a901940c503000010010074000d4120440d82d0040d266240049400038804004030400f070700302000480b11000824001491140080710440e0030181015201c0c01c3c166004003400d8542ca03903420a0b6600e070307a58001c4041d24448100c02c940000a039610001540e245950001e14000c6d015805440c041d5144070800819103400b00015400120b041208100c840110b000c00404144907601100500044002c1007510212803c0312b81400c23a00d50090040541c3c151280e5082c40d65404040d1203c0c1c0014640504500300900c203074002d0107020365060300b10044c0c409005020716404000c250b12100108581c620051054008a001c1c0c492010f8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 153483516 1250 153482266 153482279
    0xc030a0f11150106030e03040512070f0b120114060705071707080609190c090f0f1a0d0201080a0617030a030b06071e02010e27010b070201120c0e03031305030106 71
    0x20240c104410b10000501c460f482d020048004101501d171a14040c0402e0101042075a12013003480600191a40100041c5003008140120408244d0040440f070b0010003d000010b0001090181107a0078562451498a41400412490f00c10680020201d004500010482e9440f0030b90800882c03000c0412141581d49032100d60340d492030b0a54818a8650194882041025600e902d25404a100d0021000380590b1200000107545002c40c0400055440d0700c048031480042c0c0c0b1900304909800b10841a08a400e076001c9160703c003120501a0400102c500040d00025480d040100141400b5940003030380c1003070110380380c3c890304208060400030713042c07040f0920300d4604401552401c9070409003c4c8001c4c102071000c05008155990101c0c10300180320f0280d4860b80d6000c41a00e034920030620465101e80031020b91075a003050582010200d01070520002d4090307640401c06451a0048400001d141d9954150541c0e04814405800d5030500c40040d44c000042034020700b40c03007201e5080e0003e03c0750a48035030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 153484766 1250 153483516 153483523
    0x12030f0c030c080f0a0e07080c100309110409061b02030c0d0801050a090903030605090c1305040618050910090503120705030112080904110a11060112021f050c030a0f11 74
    0x40b403501c001040c90700802e8292501d699020b80000101c0c00000f54483c101e2242410300a05074020074064010506c0e8204c2030070007070803e440718022441c04010400c2242c0d500b140e10310603241c402d40920768a00340e000820800b5441554685140102070144014911000703680f980440c0c1031060a0080a02c10b0300c2c410f020f51070241c140c40008000f11205420601d07880c0040c08d040030150300300341d11030a000070b584d1142d02085008210890803241c2e1100341195a51038040305500440c013079854440b0810844651240103000d100f240701d0080b656440324240d0501d0020120f000b0494585400721081c1000000002031040d2401110010956a108001607586001c2480350300b441c01260703443e01d400103003c1c2c402841d03070100007040040c01541c0d02040e00100d802480071140030500d210001141c150040000da40117000e50086800380c1034080c1d011038640b8590104c1100803c518026114420707000d602a03c098100407000c482d1102d06281e4000c00c800200d814a001080b800164010045d0022 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 153486016 1250 153484766 153484781
    0x7090f021914041505070b090d090536060907050f0a08060d0c0801020d0b0a05130c021504080304020f01021b0909031e130617010e1312030f0c03 64
    0x140404452065810000e03944400b050b0703a10284910308101c0401c400e001c1c1024844138400342e03514281c855910b450010504540586000b4640c0e218420200000d940603001c90240d803401d85900142031420034070002c80c00e540c4a08040e0000540c00550101407400c82100d114074400c8924500701d480b082c909541c0303440b501c1200b10700c00100300105104140505038141e007110028008652411164455072005070b0a5000102c1903500001c520541180900450f042007400b12138030040c01c4d141c400024041c0084211104034180c9407504e00c0181802800f20012418403640020120301d0f142c605840242d1044804034410303020300c490640e10b5480040c1d111500156550707030404000c005010050400801418444ca41c070041065140c01e000e0004c0e01007207600091302180e00d86600d02d43d00101071743e058021508101045684d60aa0404400054111880c03000c0003401c6444022034010003104002c4007604003801410350301ca049a065200c81e00f07d4842003070030000582840e40807030640303080 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 153487266 1250 153486016 153486037
    0x7020304050d080405180402030f07050904020d1a070c0b0a060605160501180f050105060105130b030c0d0218040b120705010818010513110d030807081803030907090f02 74
    0x40c0300510507414050420300c9054010403070306050558030400104620048039560044e411a50b00307200460600304020710440507424082c001031418a804103040140c01070000e0300c0346484540038001c0c0b15201201240c1a80c8850b01c0d0a018a0248000381045090000c00c60b08050070f100000c00100c0d8601c161429580240c0d2164a0010040318049442600e00000c0c1e078030b95a80d032441e240e2034003040d80745c0744124450111070b1420700703041c2491070031602d00401d0981402410094021040600e89802003607820408146031251240b0011401d240110614034200d54400100881d20901541c04084108070899040c420540701905028210f20300021003002d0b84d001d40820700c5107602400f010303a8416480d80910030a81240c42440d42500d00542d0f90f002480c800b10820307010b02c90651070f800b2002c0026103050044031030070742e401890060002c181e0700030000c890002c1402c00000a480300b00c09400307101125120b05045c080c0d103407500590710500c800d05207010488003800d40f0034020740c3e480300361 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 153488516 1250 153487266 153487273
    0x1a01050604061d0310150909110d140d03051501020703031d0d0605040c030c08010c05030105101b05060a060909020d02060a090909050c120a0b0c090d05030309010509070b030702 78
    0x1c1e003102a200c200d812070f100c10f60303140001c60f240003d80342003285010000d030940c1e001c1104500ca0502c0713000c0b071aaa4004c0c00c50715003440c0c104804625801e08403120101e090741c80742c075551000d00b400c605894070030402c034801d401401c048454865160b0001400750199220b42da202c60340400043e40e4440c1070b0300c40140401c04038203403990300b1404504011409800500303541c03441c118942e1144111401141d04403030a41542000344240004030741044080c115800080041c400b45070303006019400140300d82445400c100804041c001c0c030540d0300088a85c43c46032400785512041c035007251911030031910039503030074904200020084043e010f581031982d0094162040c0200035024003a00e0792101c0003260038860705420014024150380700d03205916002c1c00113029000d40805c01c010703190a40b00c80850305a8448088400405c00000d00c4c03079002088034908560740d50454010a1000c108004c008d0101d010120800c0040501904034611402459055a08440c0c44404001c8a0300041e900b120041e030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 153489766 1250 153488516 153488519
    0x9010218030c013f1d060c040509060a0b07060c08060a0303120e0a2003100207080a030509010b060a0c0215070305040915031202010b0f12030a0309060e0a0c031a01050604 75
    0x35140c110b44050440c800b400c8010400030070444138071a030200764035026802d40d10815010f281e10030401449100100d0805405035040800f500003a9008034041c0c42c2c42104400041050307691000540001000f5038284551a00c0850074040020700d2007502d0000807540b1400059000d03e00381401074180e9a054541400e02080181080300401c2c070388121204512400c92608081409600098070700c170500c5c072000c0d841300300f41c1042c1810101548442e020960041c0700f2800020b110324207541c1200003e190019172a507a128844d800341c071010100075000300c4c0006000d801280d100d1160f0f45140c0c0299000080c030500315040040c40e100710500070700010703424030040c480404103402440d401050f04100a980603200d4840d00c111020070130848000d40c1d907070424181182000030700400d0b2504204d50f0041e960021480c500d480b84600c9401310b040550714044001002942d80c8401c1c00014442c00322581003045103052042c0d18510302081ea2860035a11020a5103003c090883d030594402070502800d09 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 153491016 1250 153489766 153489797
    0xb01180c08090a08090406032f06090a1418090304050405060303030c03040f0302030408070b0d05060406151209120903031202070309030f050a0501050c0d0605030307080702060c0f0609010218030c01 87
    0x5805c00445164003640f1100000301103036044031803040c509510082c07403c950001c0c4c02c2d020241050701c103410f8040d6005108554881c2d540700001e01c1140c1c0c404060346045280500043e42c4449614800008003c0380c03805e115048c00c000001d0015604140d03010000342c1c48a50030155640800c90f150582c120303041000030001198100500a41c900c640100ca06143e01c500941c0d06000b0075410485410b08042001041404140502038202a060700d08000240c207145441e205d5038200703072080048c028281101140c041e11030740081e50300f94020402c0d900d1020f002d40000c183c1e07400d501c0305500107021844441c000074120300c02c807021240c0c9502e4002c8658515665009100b0001c0010340d858055221480040340e000c1c01803070310420703121083d00d03581c8018900c010115040d50b0016400f9600600c40c1c080000e1544049882003074048800719203401907008000d01d003104041c1020014040c8070140020400150003030481d42c1130203100c9011744650300081c55515100c040080380080d10034490013988 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 153492266 1250 153491016 153491033
    0xc062403010b13020703051b1b120607080c0904020f0d14010b16061b0206040233030a02070804060c060f0203070e09040602040510020303250203071502070b01180c08090a 75
    0x150710904002d810608c603410328007440b80342c9007504880c54110b01e560f051045020900001444c2c000c5034890101040c002e800c590f503d4009101030f00b070041c4007000c1010380303406070181c1d800d010004006564a9100c0e00410510750016001c3c220001e0910003001548444100c1c0071381a02c8114011034244109000c059411784810750064804903070303401114401c07082d2841d154072442c206800410340360a051042c81105c0c41c3c110300098901040b0390f03101e400910060403001e403440c80b50158684035203a0142c1840240306000303004200c00b0001400107415a0030240942c0d0140c0140000c00450b50310903004c0e400e0b88021140d4000250380c201c01c0740c0303080c903007200e1766600a40141001421716032a800800c060582d504000d0025902c0801000581e11004100000c8a8291111000550415907000e0341e680551280281400ca2240e00c80e400400c255040d02c01c420341280900b4840d503561344810b6280300b1581c0703000c409641801d0000080e203001c1c3c051140256084402415004803e8403903600 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 153493516 1250 153492266 153492277
    0x5100e0103060509010e0603060c0a1b020319050f19030f08130221060903040303020606010804150f020403060b0904020307050409080d02030403050a1d13020a050c062403010b1302 79
    0x18142e0b1408089899103075034180c5400b07420b040400740c890b4100a030815140000003449450380980030845802910780c0403110000c42c2100a100010307180301480020705010003100040d030541d580281c01c07428480e000641a64210390032080e1080314003a400c0200e80b24124900160101e0600c2d0124414a4131549219911481c8084040390040d420390005000e1241c50480d2000c81421013440842d030001804260381118048000b07500d03003031840d980130392608401840035050049070f90001d801e012024044a440e050044400c0140c1c2c1c008000b2a40250050300040d15164640360b048155801c001d040d0500541e0024020030783d8910f07110402015049024044440110034420130600b46aa8006103001ea4400e45841c1c0d2155413411b00100140a14040c40d020110242180c000310b40b2400d85040c0c3c2c0c50440c00003da50740507128000d844d00c0c4500d140248481c444c20040248004401c01c000700b070040d200902c201600c00310001c0500341c52403114015072141c0341d000c1102da241e2982e40140b5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 153494766 1250 153493516 153493519
    0x1209082517090d0507031104060605030411040902060c161805071205090109080310061407080406030c17070c020909030c061303021c0903050606040203070206061e1003021c050105100e 81
    0x1402030f00c140d40d81410000b040c2e01c201c61116809000940d1850305004402c00750a0b1441d045065240c9900e82c007541841c08140c0038056941d84200c1015522201c0032190840103420440700c0f0030760a104440701f20200703403007070040b000c0031000d00001b03840c45402541d02584035591104001d80e00c2800030401468060b0003180159a2071030311030001454500614440c44800d00083d03112032070801d01070060b0404e104200c50480040043d0b00001d200c2006036001e80c2c00b54980015420300b0440c0a4454070081c0754201c03011031080303082100300c96105400021691080d1200c0e0300300e0b110410b5007648d0307002d45c04c00c20065800040009480511410003604401d000b03104481d10200d03600c3c030111401c400d4178480030018018410500c1400410008150000e03415181145949071580c0025103404001e03000502c94260700c0e5410304032860700071103400232000c000d02d004220581c13400040c00a511265807240d10607007950038016000058400e6074105e5401070002c0c100da59181104540041040b80d156 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 153496016 1250 153494766 153494779
    0x3080a09020904030e011823150703050703050702090405010f0f050105180a1b020d0f180302060706060e01120302070f0303050304170c030304080901111f0c120908251709 75
    0x104008245842c03240c001e107502004a23a0224038400001041c054585206024940c401d01e075001b0820164111055a41c01d0f180c001d4480490345000c0340c01e407265201c080d40c00085c41c018081405010b40c040340c2c03c0c940c0000d0800401c6403d406041c00c0d10800d05c142a840b007807850304c00f0520104540c040c4e07031100700304100140c050000304c1c2e0711501d0071400e203811005034814520000e01d5030704003282c0c01d41005207003046004400d240c00c07503000d081d4940c040280144404103004041280f5908000040c2100c20720300314841da11041d407454907200000d020b40051044850010380141482d103981c003903980554441c2d2031669035841d40d0034800c02e0f01c009a00d4031402045001230000080c4090b43c000d0340700e0440c0513070710f8005200043c02d070003004d9003510841c0c10a40700180d6400d04004018003c107600c40313002c21b1070f01c0600d5081d103020401e1005c1d40049400c5c85808402c21900d00c00801c100151080c460f00c0744203000b43d0342e0307800c00380c034107002401c003811400341084200c0d9100c0a0180c034907005019 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 153497266 1250 153496016 153496037
    0x803071101021911010c0201180e060a0e1504020f0915091903020a05150c0f0a060e010203060901050111030c070b0d050c0703020a020d1e050d0201050a02181215010b0703080a09020904030e01 84
    0x527421085584a011a01000c4060000034603107448210300611111a00c51031a05002c0000c8410403c0303000310a10540e400a25070402a400c1c80c1030325840c0c04010402e0300c29040c4400e040100ea07009150442c0705451015101d13400039600d0074040181da4003d0306400342c00c0c1c240420f0102d001c1142c40d018030030030000c1c8141c400700d0f1070400410000f41d4051001e005180002c4c039250041e1041e403600b006c07050b40180200605c0c1e803681d502140c1121400d2070154880c81c0488205400c502c80c1840c03d00c2d03203000d100130104003456220010402805681c030200451358880380c0220060058440040050300711403004409485c05030001c0c04054050403811315445203482200b404030307a15483c100c84940080d440013045607028031504c0e41c4001c00440562411800c918002c80d0189810052449400642944402500200129001c0510b013240f004c007039507110702c0c10b8000c6800c8803001710300140c0120f000a00c600003e0107420111540501702c01840d40707072981e06440020a01100d1030410001500 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 153498516 1250 153497266 153497297
    0x4021c05070e0607050f012a0806060c070902220501080103240203070f030537060b070c0312020309060304021e030607030608011a0d1b0803071101021911010c0201 72
    0x4d280302e40c8960000c0c511040c0d403404031425104c20174082491903102010340c00c2c8003504810f0038611884030f480c0c5400e00b540d0340000113a50740200c6551110500c103a0700081014200c2d90300400c0318000c4800c0da088400410008003a89040718020603000400e900010030024014401000040c1c528842081487c003041c01410100d8000725903001c00034456800b01d03000541c140c882c00b03812901070700002c00ca01007007400540303501c5d4401c4040c2803c40c0780fa5410701070740300c1180c1c442806030401510140d581c2d022820100780c0500540800e8600c01244600c0010f00d81c000411a0402103025007214110364440c2c0810107841d144010400d020780e802109500c42d03135000e0164504c107003002d48000411302d0030409040e085502605203810447d03007522807001c0e541c0d03a104a944080f0352000304040a00c03420b0034450b403054210b80c0b01c0466440081a00400c0040c0b540d64013040020030703802c40b4001e00c0040b8000501c1208443d015090081d503100000a55110350310f4000703498018102801c2c0c0007034003003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 153499766 1250 153498516 153498529
    0x50c091e040b04061a0a0b090d0c080c0117060d0201050901030b0409210c020303070f02010c1209151b14071a030a1d25090207051b04021c05070e 64
    0x1101161901102c0b0200800c205441c440c5005030b0780c0030440010b410010f00f000c1101c5070352602841c25200d0011481c1e400c80d64070b2842c0009080d5104503e2a48280d84a81d0b07199102588003105011a80400301c481c03100e850311802c0c0f40700d494010510701c82030806400540d00ba034001182241015202c0f1002465615180104100d041c400c4410083c24200c54990751107807500130040c038003009160b40040c4003590f00003050701c140700e402104051404100d4801650101e40b40d500041403c26460207444800b90041000012649491002d404d1803c0203402100c61501040e5500030003a00949100e010400c0c40c0e4610000a030804101c89110b5258400243c0d003001c10384880c400013034000200303c1d4284d000d002c1c60054030340c400018412503200e0009640c0340c88100205245404040048100620507068410000c240c0900215038035151410030075159903596594908c0012840301c450100e050610031541050140f941c4d05512001107a0755402414002c0d00960400825131842c0820b5038592 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 153501016 1250 153499766 153499771
    0x3250212030a08010302010f030b0a09020912100903030614060d110d02040f05100203070f06090f02060307050a0e090c0403032f070603050109060b030a0923150f04050c091e 76
    0x241c99100f2513600d0740c40010000c004001c0d002040500301194280300341c0f030381e8203100140c540e442c00143c0c17110110740101d80ca0755500031200f001480ba20740300b904c4641c001d5020703050850103a40c0511185031039600101d00510051b11140d0415000c00c1940303445545988a83d0380c090358541018942000c03170109000780c2e0003d8100000d003c9450b0b001700b0a40c5400007258000c600140091400d00810381c441120050041c00081d00b245c0d250082e8908101c0c5410140582c0769000702660303142c2c248540010036607000500110085098450203420314540301e80158461b20a41907802d10b00350840c0d07011195400c40c01d914211080c1d8091800f000e415001c9914000c20300020000c03ca01b524040c00142a981c042c1e02c007100c150301d0b142090100c03580304411264006c00c0e041002c03a4918862400640c0b120030038141106010b40c81c00c1020040c80c001c54180d610141d03208101c80746846001103092204020b4400602c1544803034031030415800c01540c02a8000b040460b94902800b00b1405220510800c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 153502266 1250 153501016 153501037
    0x2010e04110d0f360b0106080609180303070309060b060301080123060a21020a080f071a07170403150f05071701090203060604092c0325021203 63
    0x2c030308103001c8240c038030420070707050440b010078060a10341c0c88400403202c94100c80303c0c040c3c484d40d0550f080143c1c188600d0140c20380e400304220b40550307558100181207400541e0004c0c45200e00c00045924003070f046a0350a0a1920940030314a50f8440c0e510603401051111402c4030100c2c1c450700601156513400c40554000c01040d8008100601d80c2600758000303107601d940140018030110107021094644400c00020f03105044110500c1034100f281c8401244c5c00c036107000703520102d1b0940c0414010b2020403005c005000f50002c0340d5465440d8000003421100850715034007108010311000c0c0201c0c11403030800840c10040010546429125201c050300369400d4850348044641744e680000c4041c0b81489256808074451030300c5001d184030300214182407001840741000240d0080007080d19a55001c088500500882008100102c1d0316610040080901e02c4024200401c000e4442a6804084116010592142010203400e50b00d6544040c20040040b000d9800450083c0c0c08100201c04100803d1030303a65 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 153503516 1250 153502266 153502301
    0x21812011a010207061209110603090d03051302012102070f030e010e0a0608191d060109060905271606110706051e07020301180b07090b130e0402010e04 67
    0x100c0107501c071450840704041074119071082d0b10030080031b54002d600400210310702c0d4000c00c0c5003659040500c1d0f191800c0b10b000f503000c080002800300803e40082c0201100e82030341c400380f1040d0346450014981c4004281d000c1c0c042584030300703480c0301c2c80b00c005601d05101c0d202c4d44006007040462313102c444036131051403004c8012030440d40c02c454466810408242d9141011a120010b490a01d44020302c0180068841218000742c2d18190141c506182c1100300360b0751004505081122031450480e60f100c0d0b0a20800004618001c80070401038560700803584540c00314000c1ca0f41e002d40000f000380780c0c040f81000f054124000c40212042d031000300c44545004103401d0360768598410500044034104140c903406102406400c21202d05410190541041c0010b081c0d040242c4a000c00c2c0040390141110788013035051901e4040c1d0001c2003200c2c05140c50f0182c0d6441c0c1c1d52000c02c64851169080a202e40d10b00b000311441140001c101c1403c1110350954070510624080209103181c1010a0a0300c01c00b4038480e00151 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 153504766 1250 153503516 153503531
    0x7030206210c0c0c030304060c060b0d050d020d03050903090a120f0b13021e0a062d18080c0102060408220303030605030f1b06030702160b19020f1002181201 69
    0xf604100003184284224080c526051174000f000c0d010103004ca00003000c45454030100650340d9200c01c500208141c11a00351812040520710085d250201948034402080c5001e004c1003120300000300342c9801200180042800c203007070480b02c00543d80000012a884026903540100080341c1d0001c207402a0b6481e2080c1c4114495441045102c8200100e02052403003c800c58503001c1d911490035038201c4415082045240c916000c04111095014030754000003d0240c40c01d03005140c0c40050f2081c2004051442019642c56401c81a110350390030382010b0059201101250110340d404008280501e8260303071034244000300f0086a00d05002c2d640c01503010a554040400260906001e0391070030901c00c0015000b045560b40c11013210b42c1c00c1458881c0a0040840002c9145008021a00d203044090341104d220980e19942900e0680c0101c041540103055200c901c201c0e00d0002030f0700c50352403049001030410740c0c4503072440703000075082540e100b061000c418001f6802e5803a0312600b1143c20310b609002180b0314 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 153506016 1250 153504766 153504787
    0x100807030312050f040c030219090915140702120a0306090e100c0905061204032001060f090207080306010c030e0a0e0a050c0403020604030b040203010603021203031b0c07030206210c 80
    0x703031401480404da0a01440400c00010082e24040301a640d04503001c042140d07010309050324030300a54104640d1507180002600c28003040b00d00c0b203017181c00790324810b00910700e20032002c80407900c0580d426030140c1d00c004500e1501e102d4a20252040c100c107481c1c00522542d881c0740302d02c01d80703100004d005d41c540c10104524001071000e0044030101c00c1039041180045240c0008140c851140244003990841c00001084c2050305c100015051900c940003880400400c20311458000c00c00ca1040e072440d07204280c0001110f0819000740c0302d20a811045041c21560b540e00155010203185000310108454140341010f25a9580c00d164003a04410101c031a243c81c205400c03408490000d4210515040e017070100704010380c0c40030110340680f90300400c1c8001580b00c034400319002d00441d400081d404116109000811940000550320a0421361382503200c0d0717005080e0602c254490900c1010882e00300c64424409030034040014001000c400f8840c2416003200e800c1c035500e104007a20070100c1a0000952440310 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 153507266 1250 153506016 153506021
    0x150b0c010623010e030712080307020d0e0913020a0510050c060c0f04210506040305090f0108010609121b0902030108120a020712140a030f0909140f100807030312 71
    0x9891030000d080c030819032500441c140b03400030307481d02410000740a000c40c600d40c800340611801001d1400c030b4911080130901d000001504100c0e06000140300f0b8550700d00449200d2842c02d4007802c800b81c41c0b41015107401803c0d482d60001d072a01a60403441c0d801001986844440c044540d000065481584030301c03407109a1414014081c25202001c1814040b01200e00401c00c04c650480c0c0b003880b500e0355078028054007110000d240e2100600140608010041459007207002007540c01d5086400c10b0524500358015200400300b0f004071800603502038018840ca2140a41411529004800c1c405507408003100342a0042d881c0d070800f0524503000b100400a50900704000c3c10303031a008400c184c0c00c0080f1428025901c001600c50182e400d000c40d0304503418030002c4e84000c17412620b0f03441610300071030150601600c2c602e080580e410020349150b030000b4911391030740324060784451101c01a40c641e40b1030500781c1d444c50304090800b00c1040e5894a0010f5120307410490200194801d4a5040c42c15035146c0d2503204 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 153508516 1250 153507266 153507269
    0x100b0a030213020c1c030906050609090a03030b06120114090105010807050904180f03031d0a05070302090402011b14070608070e01120e030706050901050a020a1205040204150b0c0106 80
    0x4141041090005a8a90b400001218000e640040e21002c0c507100740c610300f4070000606034140c050395400b560890350680000118a024075028841d5488000074094020000c40c2d64100c0d076080022040002071103070f00011158640204406d04141d90f000320900c031918280c0c0400c902d8440d03008408802d040c98603803140102003d0070310720028a0200005009407299200040c861a0b440c0311051001c0b842c0c003507032409241c1008503e0b200405072b1401500a1009807082411a8440419442c02c6840003811081c0181d0082c06055010b2455007803207101d10b00604224140040c0b00d0b14900501800000301034403500030b0980010009606200340d0030f01d01e1580000c2c003080042000c001c6020b0304200710400000013861700d4180010145484001410a1403601080f4000001c40c2814416240c2159005d0a41e20008110a0b110255400d0403885104c3c11400031904601340c50001a0080e845180c2c0300b40040c2002c91084c842c400c910440c038030b06400a00c0740f032402040c502c0440800b4840c140 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 153509766 1250 153508516 153508519
    0x30a05070804020d1b0e07020f0115060c06020306121204090c0302070209010b13080105011707080303010e0609040f0c0b180907050d1e0c02071a030103020a050906041d100b 76
    0x20709080035000b140c08001e10840c0030300002040d01c00104000c5c03007800080000e0031103400181e03442c02c02074002502c9400325040741c1029828202200c05504025a4502c103c5003c0c5d15204080d04c800d03600c00f8080c0d0001030015900040c0302c0c00042540d0700502100040c640d41629050380c1c0c505024030042107440d11041c200030144140a5600141c07501020f250668228141954a414178000ca80d980803500e5041100d95500703040c000189041044c420710703800390a80040d0b514964a6500b01a568002485942e040c1c0340000c001c942107003410303178445804c6809103644014241464a51411030941c941c01405109400101d4040035403c11131011140c01c0304a4a0701001d00709881c00610f80d005400c80011115504c100403003c00481318481c2404500c4028203210030300030064041c0d240c60b050f1103860004d07184021505000200602100d05aa6008011089031800c0c0010720a220500a25950304140d44c4d0222510560843c6104882c000b2410000e00c003081400c1034003130079107400300e070002d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 153511016 1250 153509766 153509777
    0x21204140a0e06130e010902040903030b0112050c04061407060501080c04180203070e0603101e0507020d140a0c08130807060903080f03040c0e010e01140913120e060c0102030a0507 79
    0x200d283d035130407440b003000d0418000118425403013401090041028050003580a40f524a200c07042640540095502c80002d0300d540034281101202c0b903060b540e049a4490842d00100010f22649000c0c0001c103116941695050b4100070165803028200c030f03005e0b006814103500800c0d105c0f9644c41e041c050f0070300c01d440c104c0202d4043e238440e5001c2640d40480e030080c0a000c0c03003105d00040d0142c80c10407034102c030041560024403241580c4a030007149480b8100d04481a54200000500a203000041c9811408a90703503511540308445030740200617030004801070040081201c04600850000c0b800742102c074079410240000140303004151461700105a0211081c4082c02504002041e803200c01d46018101c0f908816642c6d66071441c040a00c00e1140d00010b1801c910a070000c40c082d00c0c413503d010306903a11641003040324180d6400f0800c1c0100c00300d038402680e401e08c66010001558103007440302d6107506800c1104108001e400002c0c03080d00101c50b13054603a035011040091224135401100e4003c680c60811 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 153512266 1250 153511016 153511021
    0x9092406180e03030412030209040c03050609090105060d030e0103021201260106060207120c0b031e090a0c051908061618050609100215070c030e09010501080115021204140a0e 77
    0x10b2912800010700103010649010581207003103000b5011251544401001040540007601c00a00206070a0303030707024011140040001e81e08201445a58095200202542035140389a5000c0712410b200c040345a04050702807100e454800200060f043c06812003001c510408034205202c848100400e25070602036030304005003000500d4001c6520800c1e694441012400100c031400c2465110380715600c00c0400c0540082003010b00310301d0808040590140c403024071441c2d252500011355407184803d02400d0250001002c100901d08004c80c85130850310700c0d046128455841c860242400d604903a803800d100000354051107500c3d84501c44100303804207606000351003810000403c9880c00b0702002d4500945040d58464019402003040881c1100c518480c1021498100c0000b09022240d010231008607241e002140d00c00c3c9450010a03042e5030041c0d403007010340c3c4c2c640010701004002c04103a1606500996009a09008580d801403026003412001e10b04001c0f01207040c000440540c0e4042c44a03030020806 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 153513516 1250 153512266 153512291
    0x60b190f05040207020102070503030c151303020d0507030e0d030806010f0206010e0a0b0112050a150b0c0c040f0b030f0304030b06090103050a02090408250b06010c0206040909240618 80
    0x440d4041d25000c0c0d0300161124028030044c1e00c0c060017500442c0c0c0c103220104104005000000e200071444290190507002d9456404508410304049140200503811891070011240d1040004d40641402850704d5003003070b500b80d40030030341803110910709500050104041002c0ac1d60490703026200115a40f00400c1c00390303d000315103076251380080c1101c40c819488024a01c0c040c4e20402410510621640080060341840f02c0a1402440104030404440031082000920007000d03505590f4070002c0f12010f0300b031140c080002c10000f4601d03019803000855070341d41c50008948040003c105508400030045503035074110708084512000c01030242d8440d0655000500008001007031440400717a0658100c0c0840c1c6642c41c2c40c1c0071034060150059030208210241448000c038191200c0307c0b590090030101100d4440d04011100b9400841c00650003003000c0200304080c45d030942c44000114003c61414905d042e1400b00ea18240209862200e4101e0702d5101c14000c01152116103080d044560404000d4420204c2 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 153514766 1250 153513516 153513539
    0x2011a0904080304020102010219050301050411040e13050304080d03050a0b0a0612111213060b0402041d0408120705030403090506090904060c140c01090b06040b09061c0b04060b19 79
    0x4100034002c040110120303007164000d405540c0302c01d0684d6501000c280103000300400d6500244603080c0b1503401c0640100031048200119015650b40c041e00d9074890303440080e200305401c2d21042c1119a440104000115080d06220407510048186d402003100d0500d200d00300300b540c1c4100d0700d0034868074041408200b034980241d0703070400d403401160001c0f40b1590b980703100a400340a541c14806048030010f0400140084c2c6c820101e190600c180003c001541c0507400788030413030149000312212886074510f280740400e250300c90640d11905c901050b520703040040150b240e111005031140008a1004020301c410160404450307005040203450301b0f400e01c12202c001600803100504003400d055a40d80303000c282c0c213200303040b170038410b0414500b0155141c1107680a103000f0000c90f80c05a50041c0030707c0c08070b03200d0b180900403034a480c40700810030382840c1c551000300281103209440d541c0c08009500040c0002801802025202e580a86000106800103000344900424000b5494401e260403c005122900b00741 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 153516016 1250 153514766 153514771
    0x108090c01210f050c071406160e03070306021b060a05090d0f02192603090703080f120103150b180a05060f0607060e07061b03050a140a080702011a09 66
    0x741c68010004820210040c010200f40004806075410082002207092601c00100507881c03107903e6952400da144d00155403078900644021044c0700b140100305103c54801c2d50348150628000702070369007203592644c88070304a03800f051000e00000c400107508200c0b42014841e407136005c1070310300041c40a0b00d05a46400e84031030601001e2000e201e548444042d85034030030828100c0300c03c0e00b1080d490104c8030b182400d22600d525a2520303041d0080c01e8030516142c045440c19280513400c0b5400900b030a5040d030755003000075001401c02003100401030140d03035002c29152481c68001d40c040c903030012280744101d20140540341c03a4210a401810541e170203400c0c2e24801103460341c2c024041c1c00005050b0701c5200c0090354456441607103642c80540815104c0034440143d2006820014180480d4100c540d2a2010786e2400c402401100220f0844141800407a000d0301c000c12000c0307403a190044050800d01c0750000160020034554000401c05070403c40483d13024072078006c40491100100c4c84104410b000140c116000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 153517266 1250 153516016 153516047
    0x60207060905090408160308160c0b06040903030e071401120209010c0b18030a050903010605030705091902070c08060601030f0204050a05011103090307031a0703061d131b050108090c01 81
    0x94000113043c03000741c4080e9044c150914008581220340c504004105220a171104104441e05134246050709001d44001005107501000342d020704c0d0765440c100402004070003025018507844070910080127034244508005005a111440c09980f03548000411940718000355440b00b80c810010b0b80300e1685c1105c40042c1a641c0000354172450340e21040741e2860ba105202980030349200209410492701c0d001000340000440036030007003140d90f03a82e81c00c040d950409841441d401203500300205944102121001e00004d4010001510b0054140e460100203812036101c04481c0e00f04500780a205e69050041201c0341680003025820310342404000f42c00207520384151814080c6030190015040d0090003039070b1b12003070700505403008103035203042500b10010580060064440344000203502c07540207101c0d610650f042590010b00c460103e42c0d05a0b90804040c060007a60040c515114000a5107044111440700c0d1082c6a40c040d42d291400140c0100c0018010040c141c00905002000c0d17640300440001d035504 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 153518516 1250 153517266 153517279
    0x7030315231504090b0f0306061c110d140f010902061824030105030709020703050d0c02030d05090102040501030e031e0306060d1a12030a021c050f1909060207060905 73
    0x51840000d150b0b02c059540d46001910200b03000a50544070703032018441e4a41030f00c0c0c8030145520a02015103890044400591026031041e65094090002000c811079520401e82c103031103102e40d100011344c0031048480c00c4810b501900190031506406000c5080f407856554002d028052440d070020305180a5030807800d880e80c00e0814001c00c0340d070328407100f01420071074861042e090801100c1c21650702e0307009015903806072040c3c1c4070014410030b0610031249044d030142d441900780b007803503940b0002400c4a10300c00c100b14401405203207040310b0144240d41c011032103500016a40c924040c009015524505c42d203a0b403c0e00117000000800105805008040060030b88540da240d0715500086c0180c0289402d44040358903140c00c1c0401c0b0b5104110b5040f0219080301c03026811b1010301c0602d43c1d02d10600d10f014005030070010841c40031030a0761520385040940c6003482c034140107180a8203d1a904510b0f1a01070070306018840c9068030760000b400c00081c1c0420b1028204190a04030050a80b600c00e00c5914050b80 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 153519766 1250 153518516 153518579
    0x806010f12180605090313090c031e060905090a08040e101707061b08070f020f0301020a0306140303030903030c0903010908211602100203090312070507030315 70
    0x612034401950103110780d07a02002411104100340c0e4120b0444481198002e107030802080031140c0000541712040d01c083c210166850500018001170a40c0d080c0d51024544c0303480a43c610b1210b0014903584d180060440014281d10309a90001130311405000309440c0e410801984001c912010201d80559840700c408404039201c100301252201d00f50341c02074002a1003a1840e21580f8000301d407100031a1b20a6507158443d10903880c1e140005262640024450b007c2041035100017642400000c01d0f46000070080554100a640803d09aa0017030240c00f0000b80e85501c03d0101c00401145401c110405800441c00c503c5c00c0000140c1e42d1102402d4810890b00c00301d5440d030356560940020b20760340da10000f1603840f801d600610350091a056034100c1040001440065030701c40700d4903201c5140e40003e1b802041d00780c000c00355510003903001400c4c102e41804100a18242d098040c0e040901600782951002d0f640c89043c00e0080841d00061444c001d014240c68082111008807900803002107141c0c2468010340 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 153521016 1250 153519766 153519797
    0x10c030516050303010807030b0901150509040203010b0603150a090507051611101e030c021f06150c0201260402060a0302130801060501020f1507111e0606100f080601 73
    0x141c01000c0081851000100114002c4070129000b402c8074450312070701080380c0311261014266101e098412030100d643c01c0003080540f070150409508140007600004074114100c020900c954421120705144001c2000c1d0f4980c2410404400002400050b00c03c10030350501c0c910003841e40c400d2090141100c01480420b105015041c0c1c1e00180481c00202001030403610003074082c00c2c21240b030000d01c060b24250316800410303d001c0c0c040c44d81d040800368007508019040081001801d128440f0078001c480e0750700c1022404401c0008520030011440d00d030808a041c0301c0c800101034003500360001e40389c000c0e40f41c810050340c0c04458241c1c0e0080d60403200c840d00c404401c20102d00a00440035083c0701c052110400040e0001c2c1903010005071442a801d45203903420004443d03035102c22000b00202900c000c9800141154490814540460018000d4a81715522101d08000400ca203c0c260030060b040b007805c0c00028940503028504406071820040d4445400314000b400707100c00280210b0600c4100030544580 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 153522266 1250 153521016 153521047
    0x906030304120b040b0f100303050c07051e04050c04080c0d111309050f0115120f05030c01020d150b0901030908040503160509180d0509030309130509011a010c0305 72
    0x1425820070b540000b034009041a1000200640c0d0698514000202007031451800e0040d081c0316010784401040110f203199021100c030340c001c01d10320707581d03011b09600460b445c1c0c4d50140d8400941d000e01401c00c019001c241c00c2108030380300501030300100790081200b0400088045405034443e802103c043d5410040703401c0411010220400b4a035007c040c5451b060358088280d40001c696900079022103a9096403107810601302c550020300099802d4201004008041d0034100c40440c0c6440b421500b0303036130021039a0302469500071404140907650041250203011000340b144030007550540146888040c0350001036040c1e881270700d00c00d504160310b40c3c800f1010b028401041f0b030002d20000d03007198902e014100000741d04078903a01419100e103001c4000b1880500592500c8040c5150660140106038031060054030703268000000340b909130200380481c40d80d9686000421001401e1900045807034580b0708500d41c01c60703035142485240c9240c49014170180740d07030042541f00d000d43d150405d680d90300b00144031741c45d8 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 153523516 1250 153522266 153522269
    0x203070504091806050603010b240708070c090b0114040303031a03061017030a0e010c05070305060f06030c01030e0c0d050f0703030c020907090506120c09031c0207050d020a050906030304 82
    0x1640c03410f008506103002002c0c0d624500d214010a000c2280b0340315082054241d50f01028000d5012185410b14001c0b09032142d0507025206841528500e8681c0d1540e54038420f4000c1c02041c0c6240f4031241c3c080014500c107004a95541c5402d10300007a1800443c0d52911480c011800064201596921000806450340c0b0750380c4c1c03513100000c040300c501d8500072042c3d500e41700450252540d000c2030b03210031103090b090020940c6c8800c0e00a03140c1300642c0d0b500c42c0044503e01d08500050740ca5210340c14000000c40c0062045902601c42c0b00c0c100e003114600702060500d095800c400490401d860003103c054010008128800480c07801c03a100c2411042c203042c2285000d00c005c01c40b107003d014458001042607004004000094420381d902885540e07282d400345c0380c0100e41c5c410541c01400800008022007039162184e0362008007202d01c617043c180f2520100c4c0c03a1000d98a60005d516203811410b41a40350100034500042008403400201c096003540481c3d10910144100b034028814800481c000e40d406005490 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 153524766 1250 153523516 153523529
    0x60103051005150a1503060906080c150f030a0b0a05010206090d110a0c0b07061808030105060d020403051e1b01050714011e02090f0109060215060109051c1205030402010f030203070504 81
    0x2e5000b81c07583c0030605c400301d5202184010918001c00010801042d0203843c04071140a800f038076580313001c0c9003030046840709180000c0110600f00300c0045d01814a4010354050303010a900010080440e409001050719aa08032505540c418401c004030282c00095245403890586440c1100410501d0901d141c4800c1140c02004507284c0b902c081401c0f4240000b4010440c040d26040c0040c8a05d4000c01d48a00f21050002d010408100010f21280c14608020142c406007003100520381540ca840f558200030b9410201c4120514004061004800402144041c0310450901022050b82c2c4000a0504e1082c103000801080252010201c019805e501001c5092144201400340460441440b802988030740904e80c03294003c140c030401d095201c2c00d41601900c0c1e450300140050a1030f9484d903101100b00802490400280e03000104460300c17130f1804500d80785a00d02d641881001c0f0351503d01c40f40301c040079120341001418804c00015030307402031391021141a0342c20010b81d00e80301c0c4401104d2520a40d000380c0c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 153526016 1250 153524766 153524779
    0x90302030c07081b06190309150203011404050a05061810080d0206010602070e01030c0b09040e01020c030c0712031b30020c150d0e0a0b07050c0d0206010305100515 72
    0x900d90740c022800c510480130390862800b54007081d030f04114803401106000d0544081d240800d4140b68025400707504030786c0c010740500040800303a01943d02131380d1098014110000c0c00680030320440c100303409201d0304960310000510003850a1004a000700d0008840d1220700801080802c0240380204042c0029142c100d00381d0f80ea00c6041c20000e56500f00c00e100d01e40052140c3c28001039034900140002d8140d0744d00c02080e0006a1510202e003481b9002450240e5020b45c0e500034074286003900340f000b00303400034011010391303110f80b281c1c01014241659588000d416505a2250383e0000e580f2027a150034520210f4581d445508441c00c10303075001030655148204011508001c0d4240049050075484000056800ca0307105c0f8009006100a550701c1c1d0301c0004122205210554001c0e4554110940751f01c40c400880d1a100551788444504500a890380c9010650015400340e0585051004032350b0720700300740000c0219501d96a40c00d9a00d40042681c07015460b0380e840425030343d40119900590a03e1f006107070 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 153527266 1250 153526016 153526019
    0x90c1c02090f090d0203070b0a091b08100b030105090c040e07030506040c03021302090904170f220605030108152d1906180f020909040c0503060114030a0303090302030c07 75
    0x340c03036001c0030640c1e0f101810302c03a9030032948442c1c0c400000c8038080e660000040304541c589031000e101402ca200d00498100002001c2150700c40a0810108000c0c0403c4d0018104140f409030341c00100c6e0f003121416070090b418142000415080056006240441a640055203c0103400d42038205100350304000c009004010501051008000c140340a80313000312040e840c03106180c5468002c81c42540c41c0c40d90400b0b6007000044c04501d00d882900d090b0701400386014a0001c40801181e00c1ea80110a07903259503801c80c00300502078605401c0d00c40a80301c103080081c91541009402d9950f50040f40410780180c2c17594001440c54840c980c012030061510581160b034210000d181800911012141c002d40188040b170302c2554450a800340c02d0032100030b08120280940c1c80d40c6003c014080310b4030a4040a5020801304040d0703241d03440322611403409a00d00c0c3c0c41260a20003018107015040e0b100c99a100b0201458418907940491004003442d03050a00150408040c90140d09500459080d4002b0b03006042c1e0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 153528516 1250 153527266 153527281
    0x41112060c03010e0609010e040b090106150302190302040503030417010213120201020c030c06070f050127060f1418010e030c070e0f040c0608150303181008090c1c0209 74
    0x81c5051301c6440800074059541c103028000340380d00900c41c00a8641645007c0b401050140d40c0300b40c4c00610100001ca461522a0000c10903800c0800020001030341c001090702012070918402038200407103140552030305d46010b0000780c0d01d004a005690000c09010f040c100c400d5400d604407450071441c0560090403943e124030300c182030040ca0a003603015005a6011015510b000700328031f140310301e000b00340c281041559203c4404c050128041110303035642c3c50100c082840e043c09201c444101110044407015103451400740d054480900100f0245420400e481d030030281e0754143d440c0c0c07142d80c0c2503610308039075910100745000d071144043c88030840c00001840d03090784001240010a80300070a02e80609900d4031020140321200131200541407080d4480f05100300ba00c40d11800b40c001c090040304002e035045034000282180d00c0070388a00c818000c0d00c09401c40d0ba043c0180305403145180c4e81402881032500c0c00f9120349421b588c041040c070503146820346281d46802d81b010101c000c0d4016102c80c0d0b140c5011300 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 153529766 1250 153528516 153528541
    0x212040309090b03010c02061311030a11011103031501050a05070b0408040504150312050a262202010e01110a060509010c09050312091c140d030e01020403080304111206 74
    0x82c9082d85410000416000d04050050a203007042c00d50042403ea6103000000010b00309544046450400da4a54110741e40c1e020081e80c8245405508400169814000054000901850764003a80d0300140100915a81148a4021031000a0808568904840c0c4088440d44030b0700d50001c058042c0322040c4414420b8030800342c019620156402c02c80404688620b4a14418070711000b080b03003c101003410900c034400d402030100f401403800c208000c4d2136030590350b03200300003c21800042445460200802905011500c1b00c1403001c1600200240305070313400081000300f000100c941400b107901031040d01c42c4d104102c03014940750001340070080ca08010f81b45034060102c0215580009003000700116003458007041d0000d4010640806910389144c400070702c22006620800306614142d01e00c00700012922403203008500407c0038010384500605090058104e40c031600d00281d00340e205000c207200040c01001204d400903000501b6540540070107000075900441c6d28006c3c002c81c0588014040c1d107600c41d5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 153531016 1250 153529766 153529769
    0x12010c1101110f0403021e03030a0e0f010801080c040c11010216020306010f05010c0f020105040909060c030617070b130302040c0c0611160b04050a080c070501020f030310180212040309 81
    0x49000b8003076185220310105007401815514084800d04100410042c507000c83c20710410032147c40000c200300007002c006070845c2c00943c8014041403550341441803604d06550007000079582400c1c02c41e05541841d5002e50307100710360312200340030303d50320003000c18058001c640c0042c82d950f48100030341d41e4905500f40b081d04641d00c486c04034028800e0741d00202e000c410480390a81600c50694442281100720f45844054015691050381405010800410780d0845400344500a500be10004507000c004184011700b12119a0301640740c40c0da121907031141e55040440c1c428101c58020031050b854150003444411002a20350000794041c1c03030040540a40d540090b2401e038800e020726000c100350030007040c01410502ca950705080121280c6018400001d06115034140c05c24040e10840c3c190520070741d10b10f440f5512181185030b1a902c0b03220100320640e030400c625206261050003941c2141483c0c0c49500760f007002d0380140107190042c1c4000204408081e0b065885403014041c94081e142410705000d401c20700c00c0d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 153532266 1250 153531016 153531047
    0x403050105102d08121206100e010302090406050a030f120c030203090111031b01020c0f0c0307050906190603050604110a12050703060b04082d060103030e12010c 71
    0x24600007403888a00c0341184400c890410b500c0c4503001d0444038410f0741078030b00d4400100c0701440c0050080340d811401c000500101d029020075a654400e240f101d844c45480091202d80305001e01c940b0300c01c0b41f6034003240c507241d800c00a00f00581c0341c88000b000107002d0521034000e9908074203010b03800010303c400842c01283c080d0040004482003a5003ca0843c0c2c954228040034000d83d004100722022940f0400e10a070f004080b82065a0a0040f007240c03680c00340c541c40c4a445480c1e900443d8500340c040341441140481d819680c001d00083c02d01c00b01190f01c2d01500e1040702d2050010400007021902d9071200380c1c6200703400c54800700c40e541e20b40c00040d0060000342d40c0e55010307606d400300b0807850103a00c90845004e0310741c54035190245403056542c040900001440c8200709600e070200040c00800c01000741004c1e0030b0b00340144c03811040f80105d156001c800001212651400180f1503034002d41c1c04904241980e03010b141118041c00c91f000490b000c5901560b1142c0190302c0c110840307100795070001000303481505 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 153533516 1250 153532266 153532271
    0x3050c07061a041d1c030b0306040c0906080c011e02010207140d080f04030c060518030a111603120c020301180f03110d020c01081503030a082d0609040f050d0504030501 74
    0x50b03030450321411400b0645054865001c4401d2503451445c0c49148818100c09141c0480d00a80280c00b080c1400ca065508a03101ca092220a002c04000380c01072a02520191000f40302e0702c00b4200c0003c06050524241b5030340301c51840c070350260317287c0300390119004035402c0000746414441c1d58002c140d6032160320140b04002129040400d40381c6906020345406aa01980c4648402401e13460382001810050074101d8101c082041e13a41401c0400d001402c00409103498030702c01c0b01400744445040220310300f01c401c0040a00710042c40043d01c50842100b0031030301490400c1c01c0310120707c003281c018045084524001b221100c5d5a80422600c2041041001d1090781d81c002400081c100c980d580da1008040c15015070080c880c80b07030242d403094103a10b500c8860303080c0e89034802501a000c203045500c83ca0150b0005008101080768081c640c0c0711440002103014201186030000303100001110703802402d92031003100340c54003040c280101d40306e010b003800f038221003a00c0300801050f1010780a580b2030301c070450b080d50 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 153534766 1250 153533516 153533531
    0x1513050d0c15030b010507030e01020f06010611100b0a0b070c09060e0603010f1e0e030915030123060d0203060117010b0414030703020906150f12180102180103050c07061a04 76
    0x81c0f00e4002d5244030746040c0c440781d040c21016581079400c1c1c081e4020303207411849011089142d042040010794020029500d03001c05100d01511100d05000d02440b86034611030402240001580315a00b100080b15155404240c4480139460119140d01040d840719902d24100f00c000b1030100340d8003550b203000d410700320300800032010790505000944454400d040c003a43e0026046240c10503c40d00910700c540c0004007a6890013810303100069044003102d0000c02604008001440004943d45032011a8406400314180c402e0700040000c6007407254002c40c4e00781a4022010172616400740d00d000f888a40001303220012983c4a001104480d00148074a8030300001c4241071402a09001c2440d000343d07a0040c0c520360080e555282401702120300910070b0300f04504200710310782a65140a01610080d030048a0600c407604003546581d81004140359160304a0744108070001800c0c428086ca26000807003820041029518074012078054012104060310032410041e109001e030329815040c1416103400c1f038040000a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 153536016 1250 153534766 153534809
    0x9060e06091504020307021e0604020f091b091c05060405060a1112130b010906080d050f0a1404090e3a0c020310110c1b1513050d0c 58
    0x700540340c1c002c1d0040c44420445150806400840c3d11213a00d00440b40d801030800483d1502040d42d0511054540010050008602d0040310300396149004503201511424914130b410302d90314000c403450410020004243e5120740f00c0c1c0305070150b400c4e1240c0000084900714201f4580345c1200712003c4400d0700400c3d0001d601c0868600c10381d948590b1542d19241010040c064880101c00090324150040302c200c2042030018008054050191814290104040f40ba00c0200c07032510655411807418007a0030701800048454541c142e45810f07200d880d00e020746070003400c0500043d10860300306121031030514000190030308001900584640008850080c0034080c14070030014402491000c0415044c14640f0400321440380300d011031180e00040a5441c1c403060301c0c458508690326101e41c1c0c0303c829804508000e0a1406008845104030403217442401a07816100080c9564180008060342c2c00d400b01e04929890010320040000d002c1c00780c5490499502c2c0d05080d820741c659441194408220700503545ea10 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 153537266 1250 153536016 153536029
    0x20705060a050a0311040e040807060501210f0f050d05090a0f081f1526010b030601051018090501180204080a03030504210815090402150c030d0609060e06 68
    0x210301c01950b0300350070320407202c00441c060400c0042c0041c0d05042840041000d1540c03a211900962051540b295113201602d00b80c0c040e0746050380300c0c0703011001c9800f1401c04244280180030303000f54030000c4461094070758908003007043c803541d0001d081489007900d65008940c0180051000100458902e4295681c03070181c099020200d0107012900d402080d6840da591100c940d82d0740113412000303800300d2550310b1503408040000456201303002011822201c541030403007041001c000c0e032035008003c6c005015a107000c81da032908180300e518002c2c1211526009007501c510707154521042d03001d82c03480710180d81b00e14078000361400780240c060400441c1090417021442c1c0c4229003c0380d03101c40c040c01c120340c400c0d181034004140007041550b008103400000b92400c02c0502d8907501d80f8969032500c0c001c905000d504a00303132040307520b8400d00440b0240140300150752103411020f074090b81c000d0070b1691001814003060840c00360019814100742400404100352806030016000e9400d090722000381c0399585c8041004 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 153538516 1250 153537266 153537277
    0x109241409030f0c030f0a0509010305010b07050a12020a020603040b1b03011d0402060c0a0b1015121113030506010905070302030c070609020a0506210901020c1b150d050702070506 79
    0x10725070040060204503c5038501030302404c00744006882c01e01e18154401181035000b2108040010000103c1d0185981c041c40b406d809080c2c454242428a000c43d52803941d40d108111020340005560034806d03840d0f42c400c116420141e07501808254480c00d00d442d01d60340103007054880e50031640c2d18444031413400d11284180ca048510a4164100d605031110305034180160103001030360003e00402c030300706c6481c50421005603070038407500410541d0701d0180f6001030b10004035084403210f01980340040070426404680014a91000c1800055142c81b1210750b0f040d510960016043e44014584000284440425003504944940009112698502d00103d00300d200448440020a009206210105903980d01c03000e030342407020340b6080034141c854000642c203400110368540ca400c2e03000c40101005508031201604200001c0003941420204210a6101c60f005084800c0c00920200148410758448240c414418103982240c0e5440490741c0c4070034054402100d9000141c8552040007519003044003c030340 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 153539766 1250 153538516 153538531
    0x7050604030e06071a0f090d05040603021303050a0308011401181203091a0703030b18010e0408090904080c0c181812030a0606080a090206090f010201092414 69
    0x401940d850360700340ca901d85609052a0014400d010800000d0745c407009091200308111301d4a00c0c2071805028062142000130000040c51308440c2d541729807581c0010584094920038140940c079071741d031700d501c0b080415059403000e0058410040031400382354210103140d05807a06000c9074034400010740d00544948000c45c01070303170032a450f0a03c1001508250458034142500c0f9240c1250f483c0d65603200c0780108108980504e909000010b410810036405106000f00d0180a032406980740030303201e007003a076003440522418258852542c0024208090103013110110000184039021905250a101e032035a00181c80c085950712403d816080c0c2450400b032902100320079116028041da0300c548981c8271002c1c2d006400703d060b20810b072448888a41000140d4442c900020000031101c1c5400300080c0300f070b60094658410305283c00130b5040907849140484240c494141d410340912200880100c0c01420f0390f800150404d02500b09061606019203503000800c00c0d01e88003070100003854400700c55580b00654200 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 153541016 1250 153539766 153539773
    0xa091404030309061d060106020d090b030a0902030703120302070201080603010207020d060b01050706051302040c090e040f030c05032a0f0a02041a030d0302030f01060801060221040f0e0604060b0705 87
    0x140c0000d200790492510303079105440c0801c4443e004013070507145203080c812508139500030400503c4900e40c10400e00c2910b812500e485103505d441c24034902420312020304a0340f86503407224000300554804000700c40045610080c0ea101c1c0348007410b0020025040000c00303e00042882020803054901402903451842e00102455001d00c0c481c0d494900a01d059031040381844024010765020840610030780e840b41d001b01030038082a00140c4100002ca0381410740c104103018120b002030000c240503000081d40103078450000d614002c080c0c2001d40c1c4081d41650028124030001850040703130740c074a101368100c0352a8144083da00c5c0b200765203c991203040310100150680e1040a9010143c509500300780c1102804810b81c1d40c00c5400b22021a0610b14945c5041011176000000c0c0041c0d10380701c00d00c1500500091030824815414400c0003900c230004042840c20b80c0011410910041a4030401c880040160101da150b4180c4e031032400c0324030a1011100b06200d9450400001009461041161200d5178800c000c1d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 153542266 1250 153541016 153541021
    0x5030a18180b010e0618030d170106050f0403080d150e0603031c0b0405010806040b0f1b0a0e04061e0e100506070f02031515100518030102070c0b03060a0914 69
    0x2840081001c80205810085a0395084c0b4140d1110780060000c144100140080d9000840070715143c14213412961042120007604400d28010009005041d80d400c1c3c50042d80e246405441e4800034040d076000900407440014202840c06165802603046c0000d0a60410310b2640d41d840100304100111100750b0160070800810303c070341080602c80c007119940010001215486200403038105d80e000d03000f070f6001c0c0e4419402e11003800100c4c407400c1e0340b01c0c07201d11071803d0b14070701201c0c0c42843c04441198456a140082141707403425006511030114018050400c111541da1007008183d40f8000d250140c65400d030f4140c0c085001b42030500703482e100c1d00c4a0034420b078a182c5060103000700c55029100c1035a0000f100080e41005980901c46002c00f1740c14403882d03003403d0034461201d114034244d4040c140d2148000030f0f011640e440c0c000c000c0d1040400c980d20040c02d0060035401190180c0701d82c2000910381140343c0004660f0702c141201850241c2c2d419200600c9454596620a0481e021009441c2001c07034440c00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 153543516 1250 153542266 153542309
    0x1303021305091e0715020606090c03010302010914040912081e0f0408090109030501020d0501170102120f22050304060201140106050403060f0207060e1f020702010518150705030a18 79
    0x11401c44003c0d84112040c46640b510030318843d0f110310b600040103800c1041440614540800a541c01416820880745107525640c0080c02c8040984030718440e241c1c001b0000080741d0b0340d0394030012406400012040600054220040c00c849044940c9405034070035010101180141da40100d02c90001801c81050b507444a03143e48405e078200c44aa41d04000d91700d10040000b600c01c0c0040c1020040c4940041007950401c0141d800105242a488031503038070600050140e110408400c2d0740043c450040b219031611144065400c03042c183e2400c90002c0f5204016404005000005004659095008010303500320302121000d604400e120b604000352042c8011b0010840715405a420030350310280041c078056155868000742c07910070103004444c0c1c01c1241d0300314100300c02c9a403800840c004840214900241540083c10502981c0f4010340009014200c60303009840b4038186554010304001450385a03003c0d071400303d650307502810305040060000ca0042d9614a400291003040e503501c44800d280c0c48102c2a03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 153544766 1250 153543516 153543553
    0x702090402060c0a080c010c030b0607050a03030915021215010206061f092d05040b060d050402030708010e0f010c08070c0b0916080c0114030c040e0705090402130302130509 76
    0x11456a00f601409851000040c0d2110051003034021020000c1030418060b0000790490702444079090041d00701300b0802000503c003050f00b021007030703041c01e0002d4000883c3c10b040001d510b05500c41c58072544001110f84561518a1031030b0b20880980d890b0300f40c035004001c01240ca8240998019030400e60040c01d214a8403a500b00b0000400802d15066500355540c4d07d046c54003c030383c042031280d5004000840c220384400444444050003007a1401c0c040c03190320030017040340341c801c034880114903079629070200d01150b6083c00700000411a071402808014600d501c800e032903000c0666601080c0d031901a0041d078560043c4e552034402d116075150740c8504420380d11032175129a0001c0c400c00303050040800080361448080c1070f00c8090300c0c10b4001400b60056103000500054140b000e40c401c060028810003000c0c40ca2081100e05640080c019291940c80300c002c161114080d00e140c8940c450b0011030941e03100201e1031a02e1084900031292051860300080141003264016516000d00340c0100029170038100d001c1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 153546016 1250 153544766 153544777
    0x13090209010f26031b240106120501060e040e150a0b090a0b030613021207090606020d0c08040512120301080c09130302060610110114100501050a08010513020408190b0a02070209040206 81
    0x300140c1d02d0b0880c11800001006c3d0001c14000708401314080140a060b50012824154001c00303242000154141040a410302180003011031140e5250034600414080900042110074146500751110b803d20544090190502c140c509001d14501000a100300e2605e0040c1880c407400500a40710b40d407941c05001440a1460005a8020742001d0400e40c0c10941000352100820f02d0b03075400a1a1350525000a040c50581d043c50010048007021031b4001c510000201c50403135404466003541c8100d0542e030b960410007007450201e003490011000043c10070001c100d0600300e610884d0340122540e207045407e032028542120107001603101c00e000800c2400c218811400388580d46c05d10701c2c0484907a0442e1030940340900f079481e038061034107402d000506845141c2c01010300003d08010341040064100203246040502c121442071000a12880d106070560341201c0c0908212810344514280419511006000c0c4030740440303030400c0c1c3d5000140170f0a120300c29928007e81c000e0203c4041c2d1125002c21649804c503 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 153547266 1250 153546016 153546067
    0x406020f0702130906050709050634210815090403140a05040504060b04031a0c0403080c0607020706080903040b0702030f0f0d020c04090c0513090209010f2603 70
    0x10000e032030150343c442d020311522001c820408280c1941d60300d426000d0b15406804101440000401401607945030403d0354202c0c0f080c00e0270603100880c21018802da200a141d03404010003060343d41c071424001c80401d80401c140d540d248400103c882e100d0f00310b40030f0300201c800c04645510103803452800d141c071103c1c03107800900030b03d0404480c044104200f07540303910204407000441d000040401482c1030a008010003001c0501c5403070b013090303c0e58032607202c020009030f008841c4044500c0016044058642624003031604510081d8645003400b1240b503850b98203403a050054803440c4800901544524201c52103080c03c1009182007900d00080d44e03040c1c0d000900100d0f0302d0702820b07000c0f014610080007000808070044c80140482c0b040300102a003450103e00da014000c0c4c1c141600880810780c2d80c01d4100454905440a0482d05050483c0780000c000c4258025485101d040002803a1031500c8404015070b42034261072241501c00a0a002402c2211a42100103400074040541c88071070304141008003010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 153548516 1250 153547266 153547297
    0x80d0e0409150c050403060e01050c03070807020a0b01180e0708120703090b031f150518061c05090f0703050a08070c0b030a02070b0a0513080a200703021206040b040602 74
    0x35000380000070f8480100d0f1940001d80c02003001c005201c55401410b51304010380f070080000381004441d495151000820b81d4081c0221080411105842003203440c10b080c2e000044e40200c0c0d44c50350b0342200701c40c1c00340d4580440d4604041c0034010700c0401144841c1214541001410880c030400b000b031020350817400d02030341800045900090350790500b0300254418800c4034403190781c04020918005103840c09820510403080f044010410181d0800100c3e104100310008417061204400c0008609101d00e481c0340d00e1200102100900a0046402960040e00c41c1825680c1103044401215603980403480098002e0f404035849002040c0b003031004002c1c240c01454011002070300c403410390030f050703000703480d0442c40b40d900180610038043d07180c14440e0004c4240000b03204509061000030303200c041c401c4025204160000d1780051480c00740011040c2c0e61014000d10380502c2041131210740314250340c4000d0b40540e00340d1007920084040414498800c80d8055404d141c90340b21901c89100075044503824221808 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 153549766 1250 153548516 153548543
    0x601030f02160f061b050301030830041e0213020903031b070e0a0603080d2d1e06032409140d0908010612080304020402130303020a0c080d0e0409 64
    0xb50b00103040035190340650415070f850f042601e4a08210744020402909444030445100745890340b000442e0304680d007002c690381d01c2d640b03503880019010403002a800780a0000400341c000305a41b0300c0d9024030660081110460384241000300e000c540c003c082c0001c0d40008110401c0c070748207489074094407019201904890410600f00341107940382d008005032000ca6402900200002070210307800381d034020f60500d030a2000c00d01e55034400445004070101804100c0e03c03495114503102c0781c0040503140b0b48950880408008004080c0c00003480b90002d0149100c21440000710054000c0c003440003140da0102d2000140c80300381140320601000310a82d480c0385504c42d810100414900e10003046180d0884016198510b150300003c0c0000d03c4a6020220301c1e41820810020030b01040040002960400540307507590781c03148000f070000d104003c076405c1d0620704140e0102c1410790000d18a003d4034452036404c0c81d20b13600c4009c0950740f10300b001c10540003e4040c803821388c2542030540080c2a0140304401100138030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 153551016 1250 153549766 153549787
    0x90603150414061f0816050108131b03020102060c160b0405070b07080a0f2c04020c0a06021e0702090403210f0f06060c2a080f060a05090c03060601030f02 68
    0x80c3c01074903481c85140c0c40145198008120300c403410028140c160062113110344045055180d400d0174401d003414007550300e000410324180409100000d41d0b07c0050103440442c100d040c01c00700da0711400264010b02c90000041c070b82032942400c5840d03603d58400c501810300309603a500c82c500c0d0402070040301c1500500360002a1800000041c0c20390500c43d4000d01c0c4c81c1c0c14080c4008180303080380d400c05010400c80382d2100c01100c07a25a11020500d0b2021000b00d403c3e00c042c0c2c0443c0c003a00c02c034120000c280c81340c140e034641400065405850070240c1c501c4001401c80c9140d040051034040c0000c080e5208080c0008100024001c2100e5800038024016500003500f4a065010842e0340f1039503d220410340b41d80300c02c500f0a009201d00c0c4081c15850402400e0312545886070035011304008410405001c10040725844034a00c4103286004141807411242340b51424a18031f42c0b2020300f5074030b41010070309120200c3c0ba0030001207010b0a203100003a00600c080c1d80c40000450103420410042885240e00304860701c2c58 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 153552266 1250 153551016 153551023
    0xf23010b0d0c0903150603032d050d0b1c0b010501090312050306040b0402070501061a0f0301120305040b030106030204031a0702101a0d0c0302030607020102030f01060513050a060c05010506090603150414 89
    0x41c1c500010000382c0c40d21f5814050544031800801c0b0008003e075603aa500100c0403a0113014881c403072841d000345c03140d0b17510300761000401e84017100307030751000d1000745c41800310125103103600c06913101e813002c0364441c0d0741c1c0c9006458100040c00000d154906207641010740501c510081c45d84000000d10202d00314840c007000c6412070340003e000b518075945412003842016000b08401401d407510103a03141c60201248020310b0903001c180a4207500c00001d407886000d00d4440e4040c1d8000e00105c091255417540d40f40405030082d40306110845d0030501a200c550024180e0340400380c4160029006003203400c030100c009070300800205100036402a804032984109444164454080d03d10610404050508500416250071401051582160300400400c04807401d100040c0d81112341d103082c010b89440e2014403107100342a46801140d0880c03200c500020304158049440c20fa0140600020003003502d55506000030040c0c21030f90716030550700100b500000004404011039105005411656510190f019071a05 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 153553516 1250 153552266 153552293
    0xc080912030304050d0f051b0307060608030d0c17070810030507060f170112080307050d0c0507150c05030c0c1204081501090c090302120c03010f23010b0d0c0903 71
    0x4140e01c08010001089400c01c5200809045400c0041a682c403101c2c1c01441d600c2491184a104500c128048040c120b0810680310030035803000050001a84030111983e89401000d0050450380c105080742d03a030340d0701500c01700d03605000e59007020b078581d44d8991064541600140c404020f01701d0b000d80000c04200240801000b802c020b940700321940341405402083d0300321030301ca5544100e0701d2713000410130310019040e914420f6a000c22259185d5450b400291854007401d2031501e17000f0306000c0c2c0390420b203901100400d0b1041c0704041d462503810301c414441c8229840d000d81d0b074010030703002c00209240c40c600b000a0000360884000312040e1010000e91041c144d002a402080260f12081558441e0015284403c0c09411181c60800c0607402440004016044503c0064042c0d10210140101004144001022070402400034400a50102404001800c0e2406001044440d0ba0b50134030000e0403250600d4120361003c400d042c100b05500442c0c01c000c1409039419000d000c02c0d42c20020006031851550314 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 153554766 1250 153553516 153553549
    0x20030d0b0f030d050c0106052218080304030c0201090b030f0c030a020c010906051503030a0c08070c080a031806020705130b120601060c0213050408160201030617010f061a07030c0809 80
    0x43c1c1718004445002e0a45640d500b115200e011301e01c21104650340d00783c0341d400103030810a1000c100d400c0c40c1010000c943d0301c050005001e40380c00204110600d50420701e0044114800e986a00b0f000f503440c52030540b40c2c002660011240d2454001241c48103d8040c007941c1c20944d51000145030000d14059a4211740c8000c00888509845000300034001246040c560320860b01030380038615026054031300030a13070255101d00500700d10001c50404180250300d03c03044007804107041107a8000125003806045039240c100c500340c26286100d004154984041068011180c0141280c6041658900b005014054201300b040d00240031540805048404101142c0200340c607440381e218101044c01400b072182d94241c180b5040d40d003890140000180000e0441d0910025800301d00d2603c03005d81f004030040e01955008924405c0101c190100104040d880880c803c10218401c204040d6104d08411a001034031302c281100342400d00c07140780801d024064080b0254480c1404515007040840001c1440400030301c0035 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 153556016 1250 153554766 153554777
    0xf0f0a0f1d060a030f06150504060305060a2a110f01050c030a060602031602061b060a0f0e0a050601030201050c030d051305010b030a0816050f010203070e0120030d0b0f030d 76
    0x8091610703071050703450308030406403000800b880c02c60321088400c0c12990402800d055a501a0340c1d00e2151004400000c0c140c020300502c80c0e280d8a0424a035100d1059507052501803032300500888516070358142405403000d03c034030258005001c100650b992001c03030304800701600800202007181d034020f11030540b250f5000c071307180c075202d0a249000c002140c0f503942000080d0351041202c1100c1813030301010300c41c1c2c055044a4180d0344040350298031103000d06c4551404014850101885040740c06a044a200c190100a042014021510203d603884201c1240540a6000700c1b00503c0954400c000804500300080200ca14190f104070070350040b80c400700e5000c0388080d1184007140c10041300307000d5942d800d0070441c01440425800d4170b500d0898441c4050130f03101c400b500c2c0481d00422170140b000881128032000215140c0ca0080d1024245c0c561081c541800aa0341c014140010701440120140d2007410320700650908152181d420020020b00b81d0340c1e58015158126080740756020808070140310341e581d071030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 153557266 1250 153556016 153556049
    0x61b0206070306030302150903070f150b09010b0403030e18091c030209130f06090203010b09030628050403030b091e060d0201120c03060e090607080c090f0f0a0f 71
    0xc0c145100035000e60209400c200007000071036400540e41103505030070003418025442c1d100e101c80c078601c0754002c000d20356514248114280001c11500c8442070082200a200e81c0c040d4104010081e030003402201c8030b0101c20701090022134440c081c0d110300c0c3d010141c41c00902081000340810f007481700b2200942d06070300c03881311000329403154a036900d02038805007415420310a031140003032650300100092081c9540d8a900c46500700600d50880d000410009108540d0380d40c42d01800304241d400b503203581d4042c1c070807040401d0714044250f05842000b2000c10b80c00c910090f086080c04050000600290b0030161149820b1103181c3da00c0e05168010440c0d107140c1405504d041d098001503002c001c062030f2060301d2a030113510140c0d801c80c2c90224076004503c1300160420b0b0380d14059000300455004406900c030034008106080d0780000700749000f443c0b07a468080341940c0c1e5100d41c46083c4038072445070341c0243c6200c829402900307040079441c4003020000d2041c00100c1c0c5903045001380e101207a0200b804611042c0301d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 153558516 1250 153557266 153557321
    0xf071202010c0927060f090b03012403030e0d0c090506012d050c0f0a03050d0f0b0109180b03060910050f040201021c030f0908040503101406040b0d06 66
    0x6940ca04a03203d0038144115850020302c0407031149400010481d007100320031101ca54018690140000d481403100d4031080c4c540f2a0901001001c1a2000034041d61a0107075a00400e2004100070407205131841040c104a81941d508540c00341004441035004019541c0030340004421103c00d41c09032003c610000b800e8038242d0001802c0040c0b4111030589481644210100c140300341c7c00c0b030744260606042150b9188120007245e8a82600d11000301c255007d240050020141c0c402d0082c50340403000c80c0144508140324038110119214000780b85c0c041812443e040000044a81d0740c414035000c40d520004000964202107410040e040b205943e0b0f0b40c10404070301c66060942d10807a030300045406003c1900e0324003036002030340d6001c00d20959441e181505040c0a08103100c0d41140580190008041c45a20401e01d030881d0242c12a000301c6201c0c2c022007011a410804910070194010b0910b034049109444150030700000300b81d01c0300c44640002000a45002181c1d20380030704c1c061039030500b5061000820910 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 153559766 1250 153558516 153558521
    0xf130315140103080906160f081306020c0102071802070b012d030b0604090c0b0a051213050c04020a020c0a030b0618100302040b12060a06060e0f06030f040204020f07120201 76
    0x380c1a281400c0307104018408200c82e60160f50b5854000d5917030b16030b0b42c14200e41d10f421000d98110010121000c10310218104000e020203000240502540048881c1d284d21080c0e84070b0710f10b0030300280183d00610742000141d02c003c0e120558001170318401417400c203850701d49000e001800d810860700d459850b40d02c3d00101d402c85100d88190403000c800388814074119600c0284444001e07256174171982c0c56050000500c03041c10003403002409072000d401c0c0e4030400351201508641000910388c0b14102001c00080010020100d984c4c40c95034400d01a14110a201c401c001c020340000040c20114441c0c0522001541c403400b50280295000b80c03030007a01850500204500e408000800c0c194580d015810700c0741e0107a840b814207040c0c0340d045801040c0d2104045c00f02c1c4c403450381c2080c0c0c0e0302584100014000c81002583c01042580d603a42d40c0c10006109070130610a03002d907000300c400e401072001c0000444000504190075005440200054542000044903440d5500a2103082d41c041c01c1100b680d900198091 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 153561016 1250 153559766 153559781
    0x9301214240a0308090906030309131509060602060f1f0902070203100204030209040b0405030f030a050f0702030406050d02160515070215040803070c02030a0605011710200f130315 79
    0x80b6050460b660541da91200c8030b014001c401406074802c940415001d42d400e109a507140d00c00542041003c3c0c155041280240008214540c8001440d00021901c1041c40c0203800035a03885400410407034551803200181a01e000b0722010500d000714620801e240c1c0040d084400a108540015803944401d004041c10180900900f0015601c100b00400c0140c0790404540c0e030040d003005549003903543d181841815481848898112007100108200000b0b9040e840306008140c3c0700081c28040d901c0c1d40060781d4900c0760780106e402048050010100300005074001f0b0900502600007414200c032142d0703d851414060005d0342840110079020403402981c100041e400d00c1d201c01d1903da449040ca0744034400140f10107400d940c00c00000803455019901c0400c683c1600030f0b4000000c116969403103d8111400c4a1031a01c01d400703010344604111800003600440c40c100c02c0100c0794581000306410808001d50152098003080c49050101e15034090308100040e0046000c0c02c001c084a1b2510b484060403550070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 153562266 1250 153561016 153561019
    0x1111c1103130501110f16080f070b190207080d03020c060f0115050c0c2805060c0705010813120509090a0c02120901090503030c010930121424 63
    0x2030000c54203410b009400d5a00b00e400a080035410120004201410300645c07007520300031380c4280c0c1c1c440036840e02112400b6040310103020607518000c1d038415942e03850700710521946528132424000454550380b600490040c49950703004039013660350b03240038050034620b040c250680403e5001c10862042c20080c440c1c10790100c0050741341c402c1e541c10724060154a83c030304140081005004a1a98013040040020800e1110010f0203075140340c0c100c4003c3c1c202ca1103120170005c410410460002241d0070900d06998000c103000b4058503c460800004607460300004101d025120074a030042c1c004200d0070030440c80081480e981e02d9513a5041c9809206900074003518100c4138525080a00410540c00319601c621000144102591a0340b1200120346100c8513410030b0740d06000010b070080d03e0200551040781261710950506c4001200303000e290f140c1800001c10780c3c03d4045002d0660190903c01c00010f12005680e070400a0f503030000391007070110410102c41e1442c010003454038150590f407540d240ca58040c2c00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 153563516 1250 153562266 153562273
    0x21507020a0902120f400507081902060906030703061206200403031205180709020414010311120702010908070b0f16120e012a12180f0201111c11 64
    0x3c00804003068417500c0545003005c481d01000307038410b00d1013544030100e04a80b01541a00010742c06d062080d2262260b10610304030b8400d58841502c0c0c011081e10160f002b0ba0000c1c2458202119801402032590005011200305070307691101040801c09030400040542c001d0000241c2ca0104600020105071298498405e5090901c0200006540a05252040212060040380b5901c50000c1c8241802c880074522009008034900070aa0b414254090422550242c0c48000c6000d4548015412142c4601c6509601c030380070040524180003d0f52601c1d00807150f44000a166181c40c2c40f1441c6070b4004035011503422040009011504081f116182d800c0300e5411122952002c50050142011a201c0401c03c4a10b44451039410405e4080d80030340c0741092886003c901e9a03550076010812600c41c1000780300894955100351409064a2180b1840c01d424040201e06212440c6c0781c181c0c501d030003044103e042012401040003224814401c40d80b8000b0500d041060b507a844442c00b0b8042100800790744201c3c1d1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 153564766 1250 153563516 153563521
    0xa0522081e070506060906090c0d110c010903081b04050111030d18030e01080f01150203040e0109020316050403050a02011b0c06020714010e030d080606040b0a08010f080d0c021507020a0902120f 85
    0x203948c10061a00103030a100c0c074560b120311104448016011041d10a00201c40204001440b90b03810740003480054404c0c1d5420304c0544d90740400d444111071800711001c10030010301040c03100e5409a0080058000420200c07820007807000c000000f564442e24020101d5001c0c0c2c0078100c100b50700840401c92103042401c1c0400b80340780222184480000512661503c030300180070704004030b802881200c2c0540b100c4001c2203d03030340c0c40d404444083d610544445034021041004900c03024455001d0302d0940346e0141c0500000021038004581c1c0d02c00390700b0200f0500d40410300b4640062501030041c4000d201c180c01030710101d443d0101030000e001c00c5031009410300c410840041460f40d004900c2c80c54955050408241940b41c0c040800c1c854040ca42080f4040c44c000981c0d140341e6600710160504a03804076044555851302d5411490712114160220340c08100307000e900800520301446c0d03c100441051718a03a0402d031142e000180c28041c0c030340c001c60304580e000648040203000b1a030110341c0240420100600e90 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 153566016 1250 153564766 153564769
    0x40506010206071d15030a0204060801120b0a1a100305010503120c030706022a0a0c0902040e0a09140318040615020d0f05090409030e090a0522081e070506060906 71
    0x4104030b01213240030710999400040580d4072141440e800d8901c0381d052035224500007034018002e42c454011880440d2590000003180710405450840017940220608080e440d0700a030800a80000d60310180014404145040940c480000824101c0810f40c0e0102d21545030805142c20040e0000c0048a0000c0820103a0f019407000400c94412603403242c00143e03101c0c2e050310903c04840c0d0220780145145119030a205a0b048000f076a03134141c07030241d0429030a050392400d0080c224030aa200300b1429083c2c0c00005030903146958031070401039014420782c5400302089280e103070841d400b04d280f0203800001608e00070b40c2820584241405480c9003071455100e8400342c4400380d5070708041d040c00c004001c5040c0340c05401901c10403d0f10740a020142040c4444051482c01800305008041028000d00120340015020b05850044900940022201c0140581c40c40381c0350b0901044010103440c018010072009226154410000d03500d0a00003442c40e450745020310f403050901c0405020076104082c0c00080c03000307030b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 153567266 1250 153566016 153566027
    0x21f1e0507090e0c13031406060f010e040b21030a110c06030415060506070f1a0601091505130e1602010506090109020c01090f1101030c0215040f050f010501030f0204050601020607 79
    0x1a40c0140d0300e40380301680c4449041c44c0d1441281c0710707120f802c48030329400000c0000341141c070a0708072038440c20355165075503038028000070030303920440d07075000a86a905108440c01c05901c08005c0a1010340711140c04e20030544141241c078a45482c140c440d030700c0020480c5050b5880750541e0814400314001d8010f0300c40c200c0008205020150020b415882480d0881880103000e0f0b100000400001d4086038a5129500f004900d100c51440140d8400104603540c002005086007210700c984416110940c006050035110361182020100030010300100700895401a9a040b01d028002d0071403800b0b11001f49001c48441c0240c51003094400203580c100401c1c001541c0c2c800c10010f06542194800580320b410350410349024140e0b40902508030140c05400340103010a00f01c0c040f101940a8800f4803040643c01c400300c0c4e450f00d000300c40d004030424070170208000440d8140c00e00556800384045590070781c4003241060840300d0030390044802c80b88c480308401c11800e1500030707145d00200900161a8030310707110708040c19 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 153568516 1250 153567266 153567269
    0x4170601030c06080c13080304030209070e09040308070e0603010e01030318030812042307090b0307030302060604020c0a02120d080c25050115090603020f10020d030c021f1e050709 79
    0x140004c64001606030480c02e0113940c000c08810780d12592180c0d0302c0903481d8880c0d000780810b074000c144900008440074018144241e0428020308520700c0b654840d1401c4940e40c10182080b8200041c0507800440e90341d8401c003441c0a02100c032205070180d41f40d4900034050100005440d40318440206041010a40860a40c0c1c01000b114101d802990b4540c507022000e52a00603c5c41c03085c10cc4256090041b0100045040c00e9804207042080380305405c400f055501c50311440000c005a008600082c40c07400d054001c2d05205400f54219002e5440702d86c00510520402e0002075040d0784611040035001d580000c4080e044188010030300d251036983d1224284071160039550481c0460002440802c01c50258032007810442020240300d2404e46031009039020749103a00c800c0c0d110b440c20042c2c45900303162940c954000d1159540041c1003402c06210f00340c02a2804c4070304034095010303901286001007007422030402c00c212101000548111807181300c0040c4410401540d40b4149014100f0032015048580b0a0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 153569766 1250 153568516 153568529
    0x1603051608011404030e010e04110901030606050c0c13060905011206050705030f01030308060d080c01090c05062109010e010c05070308070201060b03070c0c12050c011b0b0a0908070b0c04170601030c 87
    0x300120081b90040e141542e1040e0800d40280c54140e2000401135144003402d0031050980c0c040c4141540c0b41d100311003c0c00b42001480c00d80e000300c00c5400071442c00b486d10003c42980d0322000f00c3c201d603075204000210303042603000c250007100c00103440c410000503100b400c0d800403481c01c060303041d8280350605100350344050000605100440011424503501d0100400a2991100071142e6038648011514027a00c0444800c49012180060100b224030740710f400d4031440800b20006c2d01c1c41640e0190001440400a00100025540c4080890b080030703082c09001030241581e2140e81c0d071401d892900400c103210081c640c00440e40340c4241403082c6803010341140c1d0041d840f0300c1e10403181d50460919030044c51250b40b08540460407901520704100d404106605c0007802600d851500c100c1c14100701c3c001d40301440f401040c000e5000b00090142e080307a40200400f50041840504100c0c0c43c0c0d4a04400c1c400c2503d1100a101d000301c0c00f0032000340c51510441c05040c50b007010380641c1d403441e41d40c000c2d20750283c080c52 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 153571016 1250 153569766 153569777
    0x30b0711100b01020f0105070e03100e0c04150305060a060302130c020c010e030313080f0d020706090302130b0d030e0a06020c030c04180f060c0f08010302130c02160305160801140403 80
    0xc90b40360704c20171203088a00c2c4c128000b00418100408050241c1404001707080c02801a040851601a8207110301c01c1c207244250081c100d507054040030800100f85190840c00c14440c031090100101e00c2c200051441980c04c0000028403500703600401401000800910307603a181042d81070a0090b5010400700141002820134010200c00d060001c0d04501900007101c100c00c82c0c4180008401d4000a00c5098401d8000e06072040c80e14040404c0f40c850800e4012540807808020f0108018140300c10f0490081101c1c0078000340091617a80082c5108040540c1a000600040c13010045864040c0400008000b40e0008120300c6441c500440d0310340c81d12424151060759074054070300e135a011081402902e650b000c81540c10359000c92910030010021010f0328000100d00c0ca8800c0d0078140240d102078144e03500184900080420303129044007611348041d98a08500402000480c80682e50302e04c00d0103540700b0780140a2081a07802805103814081e80082c085a04210201800c2d0041601da2504644c061414 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 153572266 1250 153571016 153571031
    0x6050a020405060d0b1008040c120201090e01060201020307090509060d02040f09020402030c070c120c051014160611040b300f150108010509072a060204030b071110 72
    0xaa100a01855101d03075000b160001e2410420551176003d1203200700d044880c1c0d0340d004a101411190709504a030010016040c030310081c44020214041c80e9840d070f205141844132640c40d8411a02c00d80800e038801c00140c0e40120902c402c154000f00c21802520303003510031415920b04000000e15602c0a00d0010f07010315555045003c0603a280d802c174082d40c0e0f40140003036503242001042c68109500103c0c05442c48a14410041405503008410345c0580e500040020305007800d12080003401c2c10000c01030818007500d4040404c0c041a050041d01200c48125810362168056003000c074256122408100d03aa03c00400040c0103417a0190305650101c42441240707410b00305c000410003800002e0040c7c1e400140e1212080041d406800305c0c100b031148005540e16902c00d9201e40054441c400203000b023640c0301040c5800200300d0b521680d10f809101c0d4901c9440c50842c40010000d038002c2c0d05030142590000c0c2c0000741402404080068160085c50030f240c1030090750490721200d911060940c100c4010f00c3d0301c5069 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 153573516 1250 153572266 153572281
    0x240c0b06010c11041b090803040614090105090901031b14130b0604031505040c080d08191107050a0c0b0c0d0e2d1e13050702030c060a06090f11070605 66
    0x2043d0368406019004000e034460000d0303600f0303002c1c01d00031034440000c02d08000410b15200c00b00c1a2000c440c410380302c54603041d595050ac5002078102c460482d041000c00d000d490191303505d818980c0e00850081c1c81410101050504141c540074441e040200c00182208110499490b0015440000301c3c40340000904002c43c00009000d40c4074552002d46940c0f00d629166280280c2076014601843c86846015046036840d50227644034072510000700d010800010002d8448410306889079151503054100043c0788030303248020780182c2c01541c400d40e61036009403010710807c030500240070007419017007413a45c0c01c00940610180d914008164070204104101c107944441e6100e030024021000341148200c2d40070010310051a0312001044900f0f44a004c034081c81000b0040b04202c9030b0121400905103185601d0348002c4c010180a02800c1802144810008000006010321209000e10946200402d8103898840c80406541341e40241141c0d031481c204c40340305101e0254040741c0b0300b640c3c400740c0030586685200 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 153574766 1250 153573516 153573533
    0x3020d05070e0901020a020c2710090204030503071a0405121e0a03021305011d040207020a0504140a0e06071d0109170102121503070b0d0e07240c0b06010c 68
    0x78000c42c1c074907141d88140440c16106402421101001d035003184d0000010404108103c1d694080501aa10703070041856103200340c803946d140c1e01c0158807038005104c40c0c3d165650000ca9010781c0c81680d00c0e400100301e22003007004241c410a14a6581d05405625082903180d031034480c10852402c50180c60001030b800144d1005007111642203041000ea151a007900380c5000e0041d41c0500607546260711140710210b00d41d03004040c04103032190380491324840c100610040c400254001d42069921400c8030500143c165114041e01a188a0400b0700c0300041c202001d441040d01c0d902c2d690042c40341c000c4820025801e912451058a00c0404880d1503200b0801c07a005030340880440e08490806081c0b90f00710064040d05400070310301e03141c8906c541102a51000d030030420014405411a5040d003119504010403940d5001401001c02c60000000725414009201e516101c0e0720340c01191410103100307080454441e42380c61504401100c0c02c040c040b114040e520501d00c8000144518140f14940103c1070902a650 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 153576016 1250 153574766 153574769
    0x5060303041517010f030b160509040b040f18020a0b040303021f1503080301151803080c190b011a1216020a0c080708010506010f0c0206030c120403090503100c080103020d0507 77
    0xa83c0b299006503103400c00c1280c0c00000e07000640700b604c01c450200301e99803041012000200100d640321410b014080c0100000341210b412a01d60254580e01c8109a10445115408180d1740c1c0c41c00004160030f552051141e09035095008500c803140512007000420b80104030310035140740101140f00f418204046c0e440c010100743c48101141090781034048100400d030b40040d8140d4144009410f2900c500d00401c98405146548085006820810410000f40d450019001240050060342d0513000940280c030601d1038104407d030355480c450b000420040c0340b128036144412141e00441854405020301d0410b0510011781840004260f040c030901d4494402e0208050441d8072100c0e41030700b030f541c62060503940c260380c0c090f1729000c0d41ba02d070201c0c04540c02100d01d020581c0b040d44421000c483c0e07640810140380c02c020030381016000704200e02c0352100c00903ca00c80c8954801e450300c40105084c541071501d805040c1c00e541c21018070741110880d2030340d0070400c4141142c0d81120150800f80b02c6144c101c1c18185035 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 153577266 1250 153576016 153576047
    0x50615060c01090b0619050105040510170405100501050108011d1911190e010909110403060c020a050d030501080c041a06070308010e0a06030c0603020309070b0a03090b010801050603030415 83
    0xb0041c030f843c10032116010450244004442c00000070000d00c0e81d294194650341301b101d020903400c01c003c020300e0074207c204004002310b504000404080c807942c6c41c1013262040b03404a805030440803142d00501028450f250143c1020b20308080e09605041213401d1095000da2400401110200014402d0f0900d08050a0403101180107101040c00e110903107440b41c00c040d00400320604030000445880784150041c0c0c0c4c00c404140d44d007607006403070b09881400070080740142551108040101002244090090303d603030310925401041014076904200c0d0810600e09a14005c16007490b004004509001607640c03000300084400080c580300d0300d00400c0e488542d510041e6000000820700409140d00140c00c0d40c121010a6030252090765903003600002c41e036050000a0070401c01e201b041c040c0e00c0c0301390301640c1e010310f41100300c964403503c0c2c00c1d0781070060704581400c0300002e0b181c90403042003003090580103006044050091106080050000e40c490085000c0c1020f51160480c5041e42c01e4815071003841e00201 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 153578516 1250 153577266 153577271
    0x18031e061021061805011d190b04020d05071e06020d0f0906050903011e0203100e09030406110a0215040807050607020306040f1b0303020607030c0c0201020705010513030503030a09140a050615060c01 87
    0x280c8006048224640c030b0401015809650a0050400031286940840950209d0001c80a90b61b2340d007013156400d5924030a4610340700b0104c0102c1c8000880d071300c8818015401c4030070003100b45402c1c4020b02e002074210f80e600401c903443e002c400c0980d8115038000d00fa2511401c04a0329101000e011a0040042205420005864140610300c0755119802540220341d000a0049015150345090340c4003c411f0341c0c1425254001c0008002d0306100b00612200c2c00310f4801600d4250440780c00095400c540081d85100000303001804214865082100c180203010940d800c50500505e5000692100f00040010300710184085411040011403904094962241000304007841d45a0500175501c1004075605030100786407086840c54030780210703001d40c9240c0d81640140145030a0a004540c1c0b40c1110000d580b80244044011000880a102851140b0004000010500070340d041c81946029004141c1d40f503074202002801c0800c03004030300c2c02c0d4021100c10f11014011171a8000c250144a03c0020068551 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 153579766 1250 153578516 153578531
    0xf030c0408011b050403110607081206040506010e030307150e1f0f05010302030a0210030b03010c2601060807030207030e040c1d0301060b18031e06102106180501 71
    0x5000400350055954030002040f003480310385041582807a6641d00e000c0420014401000051544006410501e8001c0c05050900c07503981d13552003080e0402c000900140e07140c20700704100b48c1010310550341e001d4800d2070441c420034041c102103500c80c030071008042d00c1000401240920a01c40783c000381480c5204008a071204054442510303207101068041c030b88201c0c01c0140100c041103082c090b1714180d0341c0080280c0003810f503503800c000380f2640c004070030000e044d21410741c81095a428451a0060603507a100d01c01d01c030580c0d080e15102211402c1010480780482c4005110580c0e01070640d41d4000881e040040c0d4422441c00e080c1e40020901c0c0c04580c0c440d085c9054550200e5024265090780c2071038030003000480c9421410107099418500030785d4034031407043c0b0950403059984d01540c0750b6028090141c0754001106240d005d1868508103001810742d201750240807400b0280000034008201c49003082c2c01c003a40d24070b1034003154a840380b8058803064407441402031078581c040396030070307501c0e4000003c10803507 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 153581016 1250 153579766 153579781
    0x2040912050a0306141c02011215140409231504110301051819030e031b01080c03060901050607060e1020090307030b04051203070302070605061c03030e030f03 70
    0xb5846206040300190400d0700000740017143c0201c4081100004107801d02034580040d8030302445500303035030686c100490250289040141441504008503a80e0500c105060422a0b8881104043c0700c40d507002e240303440c820300040b417403c003c7c14a07410321900004288405038841e5a1400040307400300309141c14004240300c100907d980011076022010ba009010b00ea5404400c4442001c51135600803568000d0020074103d501900d039200807841c440d00b440b0404260000100307240c0403007211440310a041044e0540401d60b003048400b40d10400000c0000d242d880c0400c0401c50611061180300d0007440041584d8003000340c45d41201100c10380d410111415a4902c04800002d4417901740385200360192404000301c8409103e0440f20846000b8006081e514a182d0761059016001803003520540100c007520103074906100010b5010301f24a0f9030240e00c62003941444002c40e080500894400c804d18000620400240002201c0041e0903040c0020304071714180c080c0e821445654180000188004200f2804 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 153582266 1250 153581016 153581027
    0xb0603040c0306020f0c2d0303041a19060b0301080c0904080d0b13020a0e010e12061f0e0f150d03020c0d03030204080f10060b09011e09090603060b041a011b02040912 73
    0x3e207041c00d11f00b03c11060707080415075100c0c030017901c000c1d1044c8029000411012201160560012100e03498940c07050940344c45007048030b0031a00046900d80d8004010007188008100c04d460806044980241c1d030309195551400603c980703001918540d444109540e210342c2e441d4461001c962513014150b50311100f0030341c0104413485004806000c02c4550303c000f10281040c0382010a404190401841e0756102c14094008100100380b0491884083c1c1d403002c662981e440e4100c1d0f01905600003041d60034200a010302c003c8010301c01c1e0041c01075841c084283c02180d80000c1c4145402d0098170068289561414110040e118030f400072001445201c69140303202000140500d0303004410001000041d440c1c11213108644034110701180000c4d00406211180607480c4001c9610303240508110b01420f5480000c0c8068440325030003903a0407030b03075441c080e103150a040c024101111000751448a070041800000303417082c030060340511520f10442c4103060841d120795001405098104480314807940342c140b0001c14 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 153583516 1250 153582266 153582313
    0xa02030604050c030c09010e0a09060f15020114040620040609080606031605100c060501090509010c030b150c071805040c060804050613061503050d030b0603040c0306020f0c 76
    0x15a20b0400011011043d440560380500541c891243ca40030002004481c030362843c070417065002401040001d210f5046100f222b008000c01103e1203441c510f0003000c60500300d2001ca00701d040da41841e0440c9441c44000e00b4590b4002d601610010320040910704060030000c0c030180110040000140100d8070700e400c9401f070f000b21030701d4a04803806540d0b0b8078141600c4440040b0003100960b40d00c2c1081c09246800c0c210004060502d2402c0320410030300d900c0c1c090a41d9001e9004c0e070192a5500d0074452200000c1c0030300040c21456042c1801a41c0b8540081a00403d50740084610240003040030b64064809208403002841c403404143c420721880380150b8020003061710101c850683c1c44070002181801381038140e01c80c03900040900b00d00e5072510195040070b00c09100440b409035540340503881050070407140101a40c001c40080422151205015088800944242e44180720500c03c020000309240c2d04c9034144c13540213801603140c1c0000d00041c3e01c1400b43c6803c04159010f0600b5150084005051024 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 153584766 1250 153583516 153583519
    0x30a03020303010f0b0c030702010507050f0109120f021b0f13090c0f0512030a08150907020709050c04081e0708060a02190311072a0816050102071d0403020709050a020306 75
    0x51307105940d010503400e44d00c180a07103001c507900184503a4000d50301803800340260703900441c01e442420111202c980c2c05c441c403842c000c0340c04150484500000c0d90348648000300e690720a0000b031079405038201c801c1121040c3c02c28541d12405403190f090340142c85a14000b43c0144070280c06001c1d0103040e10f04400d9030341e402d02850b074500418030400115464015041f07030350100a07002075441c0c42c1c0c01c0e40c030444040d140127128004042c1c24078900d00c4075032221101c103441420b0550281241a041044842c2996800380c40c01d100480f003400140488140031035a10032200140c600d901491296000141c10300744242d11051040c01130104208003400d0980051410300c40395000d404107003290480a03021070f510503030140c0040d0001e10803180019002c509141d900c000d6041d403104404d000c011000c0f00a4a0380c0c100d0a180d03004a2400205841101e905001130002400a003142e2828090092005000c003030010078000750b450003003801c0c14000c4c00800094041e19000344414940054200041e43c000c0e18241d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 153586016 1250 153584766 153584789
    0x110709052401080f06010504030c030809040e0f250f060c1a0c040e130602030903070510060503150705041208091002010c05040b09010306090905010b03190206042102030a0302030301 80
    0x415a4558960070540d03904050f151400a9129401300d1040c4500050059062190420000c008601003268071300c0103521030740d40c00e9654055a0103020544000d0100c1d49807039030048145100b05540400c00c0c080507800c400b0380328030028418a03214051070890b4081411212420f40c0440d59650054030107880034001c10141420b5091146102e1038180100c642c071218080c1803009000210281401c140c000c0888180d806200f03090b600d0340d404a80c020b4074040384039400000e000c4204002800a001240d20650040240902e0100802d0316803200b034000c0c50031408150001005e81c0d01500548014000702c052001040010707140054031079121445003480b45010050b0705007624030502500d2004401565480d061070700e0540c010610b034021245083c14180c03218070110708c204561040304102c80c0154008290180044280350a088409513031505840600000300d0150300d03814103c0d400c4840d0030b41c007070b2944294182c201d100c0c3c3c920110003d6150080e84142c000385613001015506942011401 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 153587266 1250 153586016 153586051
    0xb010603051b030411040b04020903011b1d060306040b0105040e01060e18160e01020f030d0912080708070f09080d0f0e010219060e01060f150305010501050918040311070905 76
    0x181c07070b0501003168000c20007900503003001d0442c00d06400050303600340007400160400c0102c100190035651009100f00c0348400e015018070f4040c1e449080a40e98408005540c04403010340004a002480010402809191036890176040d691049044400520380f140e85d0010958446030000c010b002c48158079403280340c00c0c241032240c44645a90031401082801c21603001400207081c262548101d4850107030550060f90314011000000340020322020903254800120988189000411008101859020452072200b00706a0301c1e0400c481e55048590f40c04cac400020000f66a04803070000b421780104c0c106000c0d25000340320907600080011550507140d118400311100504c012a03850000c000820a0b05c9600104540820603a5210601541e40c080c00440c002d0340314912032145002c5507000311800100b9a61151340c540d0306100da503001d00000d203016454801c5141c001002c1c0984a14062007116903100802c0805006584c01c070100c00b01034007503400150383c07180118010034007200c00355020a6296036 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 153588516 1250 153587266 153587311
    0x60405221407020a020906040f0e0304051201062d230a06140d09081308030409060602061e07030603140c01090b0f0a080709030807210810060f03090b01060305 70
    0x103607a80304408581c020600410306400308041140c0161449410581d40d01c4c0f00341d20146607000704c5078055410002503981e10300d46814003d401d00050075405a50745400400d10146002414003890b0591174040034090721007038000c1c0e07403485159030301062568403c10080d40c40e4030001515245c507500c0071240d44403400e40c0ca003010398401e0800b0826030750b201c40400c00c007400304040c0d920902c0300500903000a03007801c1903215151010708480d04044032a43c0085802c010b01003160243c10050f0905102508850419214070700004021f4451046094100c200180c4814071030b0344030f100195003161a8584484a0443e07143d11a00e07465003140c00500e82c800c0c00b240800003d0300b140c124117640203c00e4034080c0c0300350b812255218080c013220108a0704481c00804a84c80c0c030003404034140669843d074115103084500005510600c15441c2c244040c14003080440900703032412204583c00303400c004969440750b82c0101c00410803400010100b001a2001044d40382e070691095106500c40760009001c5080440c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 153589766 1250 153588516 153588551
    0x40e0703020a05011103090306182802010c150606050301090c02010e03090603090a0c0f180b01021209030304030c08011b020313030221060411010801120c0e040206040522 75
    0x20707402c0100c100e001c014135441012100415102ea10940e0300300725082002030304029050358031003500709200407140500340041c40501001c48041c40d11a1404a41141c03492040c0c80f421001381c140036448025006124945001861819030315400b04044ca4036660081c0c180e40087c003070a0b00d114609000905000d005106080794800000021400c00180100f04401070740000d04148a90144c0c001c404c001400b07070004a0081c080101d00e0f1418141001c03da16508051500d10700517003420100843c010f41d8000c20b600124071140002c941c0e441a20501003491071241c0e500c01404904061000a00301030306501c58003105120480490703c4601c4210107c0e81c901541c088484c007005c01c018100014a02034080a2403000d00d02d9007480c074141d21031002420160100d0b42500d1305001c03440791443c551390000046001d407052210444000b0240e0300c1d400c50080c0103008090000182d8400319081d55521800d0303800514005100d142c02c0800122482d1100c6a03803281b0101c0301d401d20078019007190905 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 153591016 1250 153589766 153589769
    0xa110a03050322030503030a050a0f0b090f150d03030b4014070f0207050111030414030304030f03020f06070e0d1e0501020406171602030f0a18030b06040e07 69
    0x100850030b02800420f07030303410350381c6000e89034801e020500000400108144082c41c8107480000c070010b610314002c1803900a4601c0c1002207042d0600c4c08114071115945c6040140d000850740c101c4170019500d05580801c1c1c40d18403404943c4c00101d8031803c4040541c0b50300700c10036440040e14603608105401e000001c0b27008211248403c49a440ea040d4135424031868007100701035a40100c082a400504080500302d06000d4030300c040010104508911140e4040104100a1070300b843c1c8044418041514183c403802a8040c00e00248020124000c0c20b035020000d4401039078000b0301c0000d14660350302e4041e6480421030810400e5000d41d00c0084c041d03900501720042c4420000d400c10b07200c1460355441680b282c0c00c0340806440c6284003022080410401d101a0014185589500040c0820030b402e0302403054000b0400c441444186001051040d4044155030404150750841c075111940d20105580040c1040b103200141c1c0c11406c000401d001607580303446c0c02100203880c00c11040c100c1c841180c0d01c4039140d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 153592266 1250 153591016 153591023
    0x16051207050f12010b060f0304050105100b031807050a06030203010f08010e0a11220b1c08300403120e0109020a05060a050706090b04050105070804240204170a110a03 73
    0x7404400b00319081400140d44000d5500000003181c5078010005081030300540070145101201001300305c00c007c02485800c0d0046504403c84080900d0010303024903078840207050311140548078241c284001003c000a002400c8002c141c16181ca44880009000350402d00c80e40441041c090b4001030380c0306062062000d281045005030616000399100e11406004a00e4500e400a0001082c10700f00469411140b0990380c3c01c207008204010004104100107000107100546030380703500e20007000202e100c0d003115903420f40c0e410801850124075003292800d098110307460690301c4044040004040e4401400c000311140c3c11400c005d024803a10f0320500b00c8104900007504031250701014032552800b8805401c0060080c078259240c443c03140e0742d810a4030401c0b44110344404112003803208100342801020b07030108062400070300525103a11490b00da0f42c24407024144a082500c409204081603030104d8010b0b1200103034003090b940d5800e0440d81d5501c03240074151105910300024094030314180705c00e1012640c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 153593516 1250 153592266 153592279
    0x60115080609130308150306040f0501050705180d0201030e0f010207061104060f030e031e03090c0402070803011a160f02090702030307092c010303050d050112030504090c02010e1605120705 83
    0x4aa41d019174980e480580f500d00e505550010407820f170f9400b00542841988640c407131003803c00082c504182500c8020b4618401c1c0007041c482904501ca060030654508042140c1030300c1e54059600043c0c0052590f4003200c040c41c01880f00345a20b090054000784049846220100141d000c1300091a8260203540217030000034507d40040a0b00600c20380194506260400030341349022640d40d008240d07030410030101a842e91010040003000441071001001182d01036030294940549680e540b40c0c1440140140003801010300070f14008400154165000c00ca4601e8508012403d90b003001c0403840e00300382d400c038460756030080012000c074804400d6a00845035a01d50f585c40f6420255924100e00301c01e04800c00c030050280c0c00b51415131203400e80340d000b140a42c03566655010a08450001e41c0d0050f04101491010b0f010701100007940001100e04442c0802070004a00d00500422030260540c04901c42192007081c5510052401e828080000c81e141150070351124103080c0d1030646c650a45d48203199110740c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 153594766 1250 153593516 153593551
    0xf01060b07062316140403080f0706021e0309010e0a0201020c0411070501020a0f0801170d0302090612010603020903010f060e010b070305070c060804060b06030910020c0c03060115080609 82
    0x115a60803003000000d40d28a08080005040c2501c3d00d140012110498982c988981100750386800000003005040d011061629060a54451101d03901c0b400003220341820000a20605024031030741546c081151030001580581e2900c0c080350707425003081d6403002c429482c0ca0759103240c11f1380000d0703a100c4080e81a0050102d83d070704a010000104116801140d07027402c00c00210000601c2880101040308645e11018900240c80000900550058000c400d80600b4201d00000f1142c0000d0b200d520742000c0e142c0581d031540001c002c43c80300e000e113400d002095010000003050503905500903081c802d100350000c005070803a00210300141d490780d10030052403800303010052100c3e04010008000c21030003418003618184865880151081881e072090000a088009010420240303000ea540042130488420b0308504008070300036152600544000076445d4006600c46c81110140543c0510070802015500a5039403038200f40d03504014000230f6400107041100094a9282c0101c0e0316005403840500e008060 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 153596016 1250 153594766 153594773
    0x40f030f020109050d152f030403020705100507060b0103020913060e1b040b0702030c030706180609030317060114070609150606050403060b040f11071202030915070c0b12090f01060b07 81
    0x7043c80487d2091a40301508401601c9480e580d044030158411101c4560b803880c00e800c00908081d02a001948500f6030200760b0380203940d1050544244503045580010790b410300d000144c000b032003161007264000b04880401c45030300d003442d4842000c450212031583d07010b42d94006680206025070510344e5520400740021310000f90f460009e450490310180442d80141b0700321000030b203044140e0f44031000050101c401e01802119a1002c1c1c0b004000c0c50803d000c440341955009854004060704122a00201c1d40000d01260701c2440c8542207041640d40590740e801c580d041c8280544000ba4040d28005030840000043c41058418407040300d07030580c0c03020b09041c1550f03100c0001e0314100c07800030f80c0243c0311030000245004510031400518001200301d59940c52515118150828150344001550001e1007070142a498010b81d03051840544c00c0b07055903610551030401c84154940d00400042080800c40d00c43c40c020b00c5284500910b090000c54a031f000a8207080c43c01e8441500800001d45018000f81000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 153597122 1106 153596016 153596021
    0x30803100801090c06210e03090f03031602010c060906022a2d0703051006030c0803040609050114160b2205070501080c040f030f020109050d15 63
    0x151074403030700d90003030308071315071082000340660164121000e0703100060307050741500c0600d000c104086509050716034035040440128050b00d07801c074111081e40380c008181c3e00640002c007460880480e0135401129030f2440304404a500c6600d0740382c03000000c1c4250014008503d000040c000007081c403014100c48200038503104c801250040c292400040700528030300f00000321403001d60b03600d40028140300780c940904c507407024145018000c61405140c2c21a00701c030080764090400419480c0e1100349841e00d81c410b5104140100e203640000f008154090b18808902403031210840781030420030f04200c0307041400c07105c080311507041c4a000c10162003200740b0022004402c041c4142e0010b002d60780c40580d18085401881e05000d5030038000b071012100e043c111400f400c00356a1010703015603645408001c1e0242c81901303d001c10745040c0701081c039080c5188084000d94020480042682004421400 = true := by decide +kernel

theorem cover : BRFrame.Cov 153417266 153597122 := by
  have h0 := BRFrame.cov_init 153417266
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153417266 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 153417266 ≤ n) (h2 : n < 153597122) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
