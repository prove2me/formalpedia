-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1632
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:57:56.048325+00:00
-- url     : https://prove2.me/submissions/e547ca8b-f3ca-4fa1-a85f-edb556f626ae

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 293345323 ≤ n < 293525179 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 293346573 1250 293345323 293345329
    0x121505100e0117090a0c0b12040215070b0109020711010203030c1c09080316080a02040b09060d020f04120618050c1020010f050105030c01051602040f0513110a23 71
    0x10b00c0c403c00000908090144070300f20001013800d2004d5030084801001c5107585c2d010002c01441030304a01c0f2002c1d03619a020a00628201c0245001d41003221034540c01c0801607102c070040c0310b00a03482014035a43c00070b906001c0040094030224910024000385003180b4048040701814454400d40101c44813090859007034010780e59000c0c4c4855030b0041619522850f2000c0c003d07200031464500070f00415021400241c4183d0304d8022034056034203612031181004082c005002031034000f00c00fa80705d40b58091001d8990802001c1c050301c0201407100305440343c0c6205090450459100800c0307040100083c05101c000b18030700140031000b1240588030101583ca10982c100c03441000c0244481622003001403000c05081e054002c5c05180620030784c200400d9070303504201350391401c20fa1b20030f90110b0340600c20103041c110f044404502e1140090404103030012a80407a1003210421114151440d04a18043d420700079175000345031403a2000d48150701e0382030a10340030030f046103100c0c58860840c81c42c8048d03212141e1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 293347823 1250 293346573 293346587
    0xb0303031b030c040b070b06090a05090316110d0804060e04050c0f0903100c09030606050607020306010b0a0908120c060a05040804090b120708210403030909230106121505100e01 78
    0x5012036826859074042c0c5000c9a01030411755a02703102c0c141600204000f000303140b15a81c000c1101600451500741304080082100c100024241c2d521417448a80c209a0780740e00d5006d50032940b041d80465569420400080e00d0703590310b441040e0207540740c2001c01000860a1080741c40c15200103444a0316200c01400082c50812103030070f86102c460070302150b9403903940c1003800074003070760710966080c00f40300d1300c0d0020300140b03005c0c0f43c5001c0d44c190311604c01049108000c000424190480b460011003407900c844455150408205050b80326960010f0066200e8000703100c013071740003610342030107008904281c1c55445060003580182e00d805a514080403010b40d950030882e445440c2410180c60010782d6580405480310040c002c00c803a408000381c0582000c82140d000c55050b20350607103c0414040c240100c5c00e005001140310040b0030326400400e01d00070808010454000c2c40c045d600c0c4040ca40d6552441815a040e403e03a034100e09007003600c180001c0c1da0310f4401c0c412181044c90702d48607070903a04004907458 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 293349073 1250 293347823 293347829
    0xe061803010b042f1204080903070e04030504030606050f010903060b060715050402010e1206070305040c03020607060b01140a0903151805060f0f010509190e1002030a0b0303031b030c04 81
    0x225180000041000c0c24058042e5a602a003100c1d003043c44070000442d0300d051103490f04d0038440d45c0d40030000034005004000600016a405421244666162000d000c00a082940d054010840111b020400c12445008243c080e14040d1000c1c1c01c031222420011700b903014280401040f044d02d17412803c40d25114502035a00d220340001183d5400d080e518048801400191000c0c3d00061140241c401d0900705000032a003001011001001c480c3e07030700701003200103000281c821a0b802222400000250b80c40d0b0b005052114085e207000180c1d801ca2200140004021034049825198203020f008082c40e000403980048a401c1808a240040000400c80c01010312003440021400050f11400034842c0020b10f2a101d0341c4258110045034482422800c0c0b0984240320b11640a00f8103030002c0d030140c52904411100d181e240001181c0c0c45003c2c501e4500b0030b02c0c40b1140030302c2203a010003044201440381c001c95641e0102034026501d0f60422030520402210415000060844000b01254201c55644211030003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 293350323 1250 293349073 293349079
    0x3030f0c0c010207080405040c090506031801090209090105061e06120a06030804080d03060905060609060d140114031e0316051002030c040509060a0b160f0b070507120e061803010b 79
    0xf5451301361500c0010358001b8010540514900740703007441c0340e500510151090f100000d01c0c4c503095544007070003031580400c0104040803554036542c2c0080142c071801c03280c5028040341000400c03d407070003800b803042c1c042c504061900220141c01061000791600c0085802c00094443c2c512959555070074480083e100c1540001d006020010b0001048413001c40c840100107600d940600000b540c0c0c10250742564010b58400354042402c0090204a1404400400d01460804008a21003400407078215a40009920220300d0344241007624a21303184c2800400d041d200e00f071115505516023852060780d280191032000c070070500b00852120034400100405c00401c42500760655582c500302102c48440e4025124a500840c90032010594600e0004804029180e80390700050a0000c104520606100381002c02e4035500c80468080300402c96070035280d4412541925450303618a801d281c40c40981404d0f1402c40100302030b4818075183c59a681045401c0640041201c0180450500c0001e00605005030905e84c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 293351573 1250 293350323 293350327
    0x51c021f180801020301081209010906050a0221031006212a05120a091101141201091d030a0e012613050d02010c05040509040804030f0515060d0503030f0c0c0102 71
    0x522102c15001507050315128001d491048a0300d400c4450240207003000c1902080313101000344800340c80b4402403d000d400394411940f0300c251020507010881c40f140d80001c0c0052000082100040c42e100c0da44000307002034034202d1a0486e4854920b9980c1c54908030380c400310740c0c45c2c0c00c2025035114189074041096208100403440c040d00d200d17000e4402d5111b1007401c0c00034141c80b030009600c000540f04080980360440715401e03514030060011030340500c3c541d5079215032440501443c509002d00c0d1551a01824008000150b0345110320389400c1802c1c2110640007880c0d008110b42000550300400d0610103600038285a8840114034420061030034007510412040340c2d907242009021680340030150111402441603403410a103d120407030036160500560008150104001c108504100c445268054050000c0c1410300352669500807201607102c005444c60343c4038108085441e6a0008929085107040b9080140c680160b92a02e4603808014142400369003244001505000c450048030800301049000315 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 293352823 1250 293351573 293351579
    0x70510020a030b010903020d0b0612011d0709020918060f092802042304020c0303090a06050c0a081611070f0e09060736030c051c021f18 60
    0x2402500048100c20000f81043c1d1a41015406001083c050369001f0300300d050020b4154640e1010201c015140039003083c01040a20045403081c03007911080300c02547c000c3c500da1551502c0078a840c000e0740148105620400c40117095568010b001900102a0288072441d9503903500015100340c15035540b142c22908003410041d07040c0340103003901d10100c609650158001c400d082250100d000d1402500b04500f02d040d11118031039000c000080729000c1c010070143c504110884e4250442c0c00070744904003160b01c4648800d0810800d8000c2550141c1d00b00c2080c1d00701a1308000050040030080c10210303194480c6100c3c91a02031044c50282000aa50000c0700d85140c0d83da116118034420910440081c031709201c02091004d1800710b519402100207581d04940303500304580d810764680c07484460300d81c03103445490002542503081c14051b00841c002d0140c00d0080b80b030b0806120f96900b00e1400d4592400d02200940300503500d4050501d80c0151040c48414020203d03202510010500e02d054600564040000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 293354073 1250 293352823 293352853
    0xe07030b04170d1b0309020105030105011b020604030803060901060212040b0d0b030607021b0d0506160504090f0504110303310e0906041a0411090a06090e0a1101020a030806040c050705 81
    0x113131300c8003d1280c0b1401c0c8040040c03a08800301da05442000f8009842003004015640c0725695040654200340c80e07003400c044256000405551250b841220500008020040c60707150040000e40144003a001030043d40d094103000b070040e4412800380041d00c49000c6418070311a21141e2007076003403080c060100d960074281248080d690720310001660981060a403500300641c01c100130400369a944c031500400d071544030f180380c000350221042c02e0a0300304501400002a508030310b006001442c017150f800024281405d09080611600d50f00302c0c980a0741c030030400c0d44500404895814100912401c4800344081c1000d800c5131043c0183e401444100000c4060000f691404141c0a0045110312401d9030008100c00030f500911004840103440010031900c1500d042c10803510f03281e4000c50700381000030348a4031200380b00f04844942450800c02d601c404440410045c601002c0d084408007400182072109072560000c0010344000d100310300407912801910803940c0511b0039941400d5206041d9280702d4000980 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 293355323 1250 293354073 293354081
    0x50607050a051b0d080f0f0301030f02010207091a010c020a1211091605030109050402030a0f0803041a010b07080c010b0907080f1302101107080706020708060108010e07030b04170d 79
    0x2066841d4018840c4505401403c4601658003510242c280d6002d0361141c0c40e1078140380c1244803006040c10701082054500c014003801140a580f0030700c0c400c46001c8482c00024541000da400210200d860446054003a801e0126074503a01031007483d10400300785c07191022a44005041e803181070f10240b00a44a01003002c01241c2400020083d81c40903420340da104c4005c0f103034000e050509400f10380100018000d0701400d400150340103002400302c0e0342d400300c3d50340c9240f10b0200e100c00580d2654404003c0c08200701030001209050003a004c000d8a66504100d503282c241e11501c1001001c0325800180c2c00c58000c400e400003100c5280040200b625032502c103030b01900860084981d003600d04143c0d80001d1800061600900c4415006401e881080da03c42e42d054499074041504601076206004d070000b80c40e6404c100c01d00c0508900c0e03001e41240d503e05031400313203010010703001a40c2c00d034106100a040b28400082d64030860b604000c90784101d071a0707070500740709220000d09504049000018003401c849c0032504 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 293356573 1250 293355323 293355343
    0xa150504110a1107050a0312140a030f0b040510120f050f0c1008040c14040216061a04140f040822380307140d050108070b16080f0405060705 62
    0x442d040f9000e0740d000080d88400c03080c0210f680c030400990081c00840d50b00d92840806102070b0034a40100c07914500400d80b1900195865070000782c135041c110401d403029006010951505803010b20007230600340c0c449039561005004030991480d1030b0f141501882440100080c00c0781e00801034590440510b03640989540c1c00c3c3c041305000d8602d10072142c01c3c203807003840400c2c850382d0060142c0030a54208035400f500c020300d95607003660090b005d202c01290b10000b0128002c12520540300082c0c1880007c088119802d60040103d200740c0c03510701c0760421600e5000040342e2000440b00110601d58031441d29402d00c0c0100150260308030584480c200c221460400204142c8000c140c608450b20104516400d21691010702180c0d140c000241080480c090000034640140ea0f0381880c200007294400c0c1d03001070340c1007031102400c81070311503004128244090000b0400340c01d0742c3c10305a1425a20280d108840c42c0440e40051620400050804246101c2c0c1e040e100900300081c070a56541195090440c0d8580344a0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 293357823 1250 293356573 293356577
    0x1a1c09030f1403011514130504052409061906050d062112030b101706040b1f0c141c050c0d08040510060b030106030501120b0a150504110a 61
    0x800e1841e121801455400540d080b9001d802d403950f801c000d0081c802c5558003c10f482844020300c1a240e224a071400580304c9880c041d225192200e2130b0408110554401400e01201c02001c1c180c01e0310040000b00240d0b07070500c0140c8400702180c584170003052680c828240500000c4450410101c0c450707500000500c0d003442d07034840034044140c0b01e0110001540100c0e22204010344061110800111034000c180b030649402e090010f441c14208011405000c51100c019002a400300560110a241c590300079800c0700003540c081040702c1000d03012802c1d6100a904c1c81c0e80c46180007681840e500d119800003d90141d202901c00c40808100107074991b2641041e03408550302c42201140154548600d0503110003840c441700504140e00880d10580703590201400c107440d207000c1c030701c8001604e10240c000e100c01410000700b426500e6160150003412180c041c1c20010103413070180b1800d00482d009807000c6400190549000503a2120242400d4074a105507010580150801c16903000d40c02100002c4c2024416036 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 293359073 1250 293357823 293357837
    0x3050304050f0304050d11040f06120311071a032503270320120a02151e04140a0f1202010e030405030604110310020c0c04061e1a1c0903 60
    0x9100d880c0c4c001d40c040c0c1c0f5080740c144c01424002c54801c0489151010015000082c0c4104056041e0192074281e0050102c004608140c0c2c0c0405910460044402003d1005010310600342240516803440c5c400c000c4e4580c1c0700200101d09541800658409420070000b0300240e000950752000d4090800710102803854407414000309101e042c04090b12005c1e0b40d0695500701100440000002c080c0c0346001a9456071203580c4d60710f60040300c40e074002d01048045130024048141c03800c0e080740d04218014110386001441c0400f285c9001c40b114040381d082030784840402c0020702d00315007961404034150000b4021020040c180400e0110300440414540e2003a8024020402c0d00b4a40c2d56072842584501c54050380142c0004012403004003503e0703c4032b1002415640800c1110a6681c01c0c0d0700301c0300c0c60000c0307900240c1c40ba4415282512850005046028002d8021140c0040c00080b510140c45110340c45102503144a035102503c100301c1e840c0290b88901407019142d0f07034114000404104100314049041 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 293360323 1250 293359073 293359093
    0x709060801050d02030a0213060e040c030c1a040902070f051501080d0c03020c0906030703080d0e010f0b0319020f1c0c0801050f180705180702010c03110a0302070f020d0305030405 79
    0x121241c0d10f001150050000c002c4141030f9824448035200b0070308041c411503035400c00426200c4444ea15940503a001d4800c5e8003c00e41103080241001c00664004081c2d034280340d092409540c8000152011915012401030300c800c15410811004501c904004000f8000c1c0380c0300b0206040f0f495040381c142d0b500081120800780c0e4840702a1090f645494014000d030f88444049811803824495403030384024058103998580e940c983c0d0303401da04d801204119200c942c4071101c80d501007109110b0104206802d5106000005210000c26140c02d0124811001928041003100c15912110804050918041c20214046040c10b40107112640b040a0407a0401800c00c000146084140200e030300401001e1003010264440468602c04401c03180c048980c103000f14040012a13648280e0980c00e11115610141c0003440c181034020f003140c0180c040c16090510f088800b40140d01c68070282d40c2d0359100c2d8100140c3e146141d0800f120700ba070078803000940c46000e05880b50704040e0b004003e140120b10907800c48001c002 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 293361573 1250 293360323 293360329
    0x20a060605030d230f0f0c1603080702090702010e0610081020160b0f0f0f04241b0302071a0c0d0b1306090e0c01110c010f1106070906080105 62
    0x24901ca003d0000566125644107284440214201e020820420003403620030071003103846060300b101d04115004071000c13944c01424070301444910a6240203214603c245821940c0f054000d01502d00040d010741c0d5070100140055000754402d0505144000448215291140c402c0031210b000313014603400743c010840c81d6080200b540c0203c41c010400c030040d403c8a555501c49012450700300c906015030590002d81d201c00403440300943c0c54001c10070010100040d00c1e00c1d44507001d06401c090a0580403450100401010a0780864010072218021920b14440042036440b04040c1188401a0390040c0f9a00c410241080e0140c5c0101004c52143d8070b6840701c0410346581c2c0c0e402000484071130642240802110050034030301d5010b203d00c41302c01010a0100691410082e0446490780c11540c50559919418120124200001100c030301d000d19143e100e600180345050b485152301e000b001e041c8241061076500351401200240b2520b5a100101c8050345000c441c010407410a0b4404c10001c05d80c0c140021465003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 293362823 1250 293361573 293361583
    0x70201061a04050402070c031725020d0602090102010e07170c010903110402071e0c170d0912020120010f0f0e0c010f05130603050f070509091801110a020a06060503 72
    0x34034400301c56800c00d450102840040d6110b07a4080780c04036407481c00400050701c034200d9111070110040c400c5440310148a80f1080d41c034040141041d4500000e00300f580140d07650029519542c0e4400d0300580c5600c5240c0050780500702410b81e034415401011400305180e110580e4020340f20700800201c0d44c0000c4c0c240010344e51102c0a006c0030b0841c001444c4141d85070308103a001801111321400902c403801510020b0081d081404040c11030b009900400104210a20442623150501d07003200500560b0040842c054a14220b034481d0f045a205011a01025a0f01444c988142c4407110403401319a40200c1010074020030801101720005841e105080800000394411131a1420b05c5c00001d140d00c49009005641c009244440b900401c0703070400c01c031550545008851401400c45072408101420034070580700c02d6801c01011101008403e00400506075541010a6080f841210720000c41040d040000c50146c841c2c24400510709100103800a1002d60015054000038020042007000540720010541c5503 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 293364073 1250 293362823 293362859
    0x81614150108120c03040f08030a0801050f010c0b0907050301050c0301090c020c092205030a050711090f01030f080c0318030f0f030a0521090304030c0806010e010902030a0b031507020106 82
    0x1640c030001c40c041c0e40f43d40003002868800301003001c59041a541c0e2601424120700c5412025050308040750880e03085d5005440d07640035000032607030800c84084e140c0000b40195041700026203042d003188049a2110801d014040140101500070320080c0352800c1d12103943d0b4428464002030710700d070518154202d031000c1100d00390040000c0007203c1d103464038076076030100c070b4951907102118002d03040310100042c000f00700600605905480d4652108449d007001240654880d03403181c0a11900d108100e41c41207031400c014152907002c14051030343d405a090101c280d00541d41c01c080a844009816400c1d1141c0003441303000644200c04940d160040e600c0d10980b12000415542c9456000f03000c00014540680040c080c4414000c000c3d0b42c400e025a210303000700d02000e07942e5003282c2e040028244144064800842c014241020007403149500d13040340b40322243c0051103012142a030100100e00e200000390000110300ccc100a00312007105e54140d4900d10a204140d0b01c42c80590301c1e1980006084103c001900c0034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 293365323 1250 293364073 293364089
    0x1060c0807330b0303090a03030f120504060501050906010e030604030806031908031f0303080112020409080a032414060a0339080103080d090816141501 67
    0x54182965035001454112101c2101e64501074094200e000e4203001c0d48034604003101c000001e00b04142c4041d40100c60300801500d000360000c00050181d0f0316042e1505003103a50501d000310051505a004a420200840f05002142c0c2494140030030700c540d603040541610001c0301ca2165548810b030040d40c06d003050034110b81c0c05421090000d4007180c044d030b09041d4051005402e85000c2e1141d481a001600e480d41030841d450b990200500c4103046011f00b05030110140e880f0269400d80c11034402520707105051090002d45481e0314080c204644850701b01683c555407094220352035462211300070b406021714505a100c0c80ea88030105120100c00056144201c40c1c603900042072010442c07060051580c04120001c0905440340070810013101945504022444d01c0d0300c6004c99520101c89000000300080e4405003044814001031020410710f004480076124520800110350301c2a01d080c07011030292080d00141c80e080ca21503038041c400301070b010720202201e10301507400d4100440781c0780d04400800e01913250 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 293366573 1250 293365323 293365337
    0x90c1e2b0e0307050703120e0312090339010810050f1206010e07080108061918140c04050a05040804120302030705190209091b0415090908120c030106 66
    0x418a4422903034450505110100030a5610340c001e0150b00e10390100700100c0d0b0685c060402042845800f560101c034014807840c192003650700301c0e000070380d6a00e03032031904445501d00080d000f00903542c00c110200203407503e081d415940c2c40c5604c0030750521050054803a103543c404039030088031962141e11000e1283d58000d1032070781c0c0d083c10907040c481302c0c100c6014556044080d104001340d10702c0003084140d00800e030309404035156281990700241a202c06921518040e80190300780f0440c003003a00c5500c413022403807103800140c400c00b821000e4072040c031030400941800c1001d60640340e0808045140811007030150b40038026601e0b82031031582203510407900a040c1c00c505000071300110710080c0a6105c440c0c0a40704403802d1140b10b84509061020f400301120307030031510914240440c1024054503620120400142480842ca040c030703246000f6000c0899842142c1c0d50100e46031100c10a26880c024041c85d8804221000741da04d000c034074543c8291103224900303503924001007008004808881c1a101160f80e180 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 293367823 1250 293366573 293366617
    0x30402120a380405121e070b0106020d030b091305030918070e0315060f0a0b0309030306040e06100614040e010f0303090f0605120a020d02120610141204060b090c1e 72
    0x41950481401a0b803985441b441e01583c00701040c000c5d044990058040380040e524180001c0d250030041d81c0d81c0401d05041c40e100d640c181e6201d00110784c1c8a005800610b003066201d15109003584500041a0342c41545a02c0c40f41c031070155800801e00c26505910350303001d40c90a4030105036640c245002c110b80781c01a5000010400e0078500750151807401c014000a1405031204c12240c11600f007110389180f1035001204002d039903d002d0103183d10b89001e810145c24181041c0c10142000038082c02140103024600c200c141110b48404122030050500d00325080c0e19584819070b0140c0200b89100503000106000400300c1c07103962000741030040310f1858446900d40360300f050860b485113800618480c0082e0307081c880e2098400e01030000b402012071658a00351079203801c00400c02803020088822040100c2c08155006005550302282e00600c240c544903039142ea100e1800c0d101901c01c08140c940c001e00000700b03100360b602000010740407550038400e82c503c00003e807210b181b0721409607914040c0c0c0c041d08480b1030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 293369073 1250 293367823 293367853
    0x1107050a080a020f0d020a1e02060304020405061504090504050f0f031206010306030c030503030711010606020a03030209040f11030a20031f08030315091308030402120a380405 77
    0xb0820207a980c015500b0f1000014880e82c24030054030701610147c0c1141510504200450358150440d9001d5000e081140d44950041340c2c0300d0000400090181e07580f0380214505030313a01000304403440c3c0780542286d03655440d0f4114001034401601c04550500c2400d00110001c0b401242d6020b0700c06442e4011424020040c440c004041d10251501f810f050740d805000c400328500f030242c2d10182d40290000c43c0e6a0070b0014005240786086248070200340d05d842400d0040e07960109018600315014a40961208101c42c0010010031104141c88056450045614611800803029501c41ca40d101130411980c65103003221880d407041c856108030400c80400001c0d0741d00160401e09150000c0300000c0c009101d45911060385158400e41e004105481c4407841c0780c4480ca0f00300c810960004040800c69124000780e55200c00303e000c06800207120b020300d072214040c9181c0030400e6003909900909140060920000b810b02542c1050ba56084102ca800608003d580303000c134040d50155a1010080920048456031 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 293370323 1250 293369073 293369077
    0x1205091024091b230706022205030319030e0a0c060f020105040c060521010603020c070f081b060d05070806040b01020607020a06241401020606030a0816020f030d11011107050a08 78
    0x30b04000107204800080021151340040c10506100c0c000040c2e40314a080310120300d1500c00c824100c000084008144100e407004000c0d01d900701000380703507210400c0340c07000240c016144014101d10300d44144070101081c0403403010302c00220381441c0c840f21446a83d801b03080b2300707a66007240c0c041c104460207401044107610400092800f50002d20340001c00da0b8506001d82100102a03008400098010443e81984441449004010901103d1010310a8541440661180146440441c1581e402c8540240a40358481152199102d0f44010801340ca0034803405002100103649a40c002c0c0c1c980a10042e555000040d1107004016070340007000308407420740c3c91f04040d007944820341c070001302420101482c103948842c89001400b50928507410741040c00000904e00b4800608a510961003110030902240c034150448519010792403000b94071031010f002242480310100903c035010b200754000200790540c002c500390038a0b0f40000081c00500540403a94420f0700034010094506d802080d0440300107950540 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 293371573 1250 293370323 293370347
    0x90213330e0403110321310206090d050109110d0305120c040503010603050708061006051905090603040609020a090b06090111010b0909030703020c01050301061205091024091b 77
    0x6400810180c1c1d110b40f4a00317503008a841c1040714496841100d42400782d01c3e007116405241103002c540c41c0c18400b552006a688128400c0d4600d10170541c0400540d10b4007412a8400b40303010f80030f05512242e902d48a03000301504107050301c11203000d40070f00100e1b00d1712410013400e49070560b03034440c1003085106c2001d40c9080d001e4000b0108110030840090503450a02503040191b00443c0642074051038140e0160804200522441241075040d40501002d5005400da03642c01600d02c9103a203d8107588403040d6094401c5d10041030380403d0200401082106981103056200c0c8240da880c40029900c09448060b02d182c242c642d64019410b01c0285025481119000b511078032420010580c002101e003c0740c03101c4400e6804149036003000414800381a01084000041c3c1401e2800d00c4c51585000b00c001c0149080c5000014911303101d5003c541d118504101c01103c01c000b80e901080039000e54039440640b03016210b03644200c8102941300040c10b0f4494400d010070014214511888007041b0780045a0302c0070030b4a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 293372823 1250 293371573 293371577
    0xa200a0513031202032104030212070c09050c0405010e0306010501050a0309020406030210021501171f020d05240f060301090b15131a0310090f090213330e0403 70
    0x420000b01054101055104024640e00650b944030400403440000201c560405a14038a1103003e01000950008120b0700100c1ea0f00a10b41d00d8400c64130300400d80480030780c0007400302401e004c280900251120b005004445003601c0302c01054008030b0a15448100900c2054007207401400750fa04054065048100b041c0c0c40180b000690355280c0e800034400d0130f090340d070290051b40b0486102107002c2c4154606030262120646100746c052032410700503900e01c650000d0305d00140c05510f190301600e05940545031b040c0320200f0207024034a4121104801a007044990302e4008408002134400c0741030140b03080c040030401409451642e0300b40b801d03481c00742110603002c98011241c9520648480d2251019088070f00300318140c000418a0440c036800104038220901aa2800420500c0168103075814003c0c00c64207604008a40e408406840000404000c08041e4116510034030501403404180d0120f0801c0d038071b56002244d6548841400282e654200b0700300140302d15101e0040c003d4488990440c1d034840e03c24 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 293374073 1250 293372823 293372857
    0x2010b040207050d27030f032a05060a0e070308090a030b07032a020c0d020a120f12030504050d0804110a0b09041103060a0905060d0b040b0a200a05 65
    0x5040440c080303a11014050382d143d080700c500b100149503c26801030500c0840050824003000e407001c3c4440754030719071000418030605101c15104050150405400c02d042846480c512040c00c103030140c074421601001102c05000e19400950b07a06040d210340608038032102e008207a20b40c110b80d5168210303032081c5091944818110000400142c900d0040f83c4243c0380c2d40d0340403444103510600003951001d2079544025021b80542c80702e484550014007091030000c1110100d68452060001c03407885d85440e00410300c12003200019000b070103060036418416a1007403190075104045101c0403421500b040c2c80041c4075401c0700303011601681c400c5400c1c0b90024081d011510b01c1c0380208001a500c14440d5000d69030000011480b5492803800744507510f4036200030070800d451031501c04002200074000e40101655940c3d50b0000c900b454480c03002c07550310294000d241c0d01c51804e0a040c1034464050844808080a041403080004042e015003e038640740e503040b12090509a400c8002d503100c2d000900c000ca884142 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 293375323 1250 293374073 293374091
    0x405010f1a1308030406030c0305160509040b15090a080105090a150609060f090f0b06030a090503070f1b08030a0807030b03010b150913140a0207020d0c090c0f1107150201 75
    0xe001d0070000104065402503039914039050001d403d90b0001c2300310205240c07610b0100580f0b40a180a1501040300a181082c2e0700ca00c03080004004009092a044d00041c40e110300c1054000f03410000d00c1054021513840002a07624462603003a81c200b1280c0080340c4d040306000400107050b4840c1400b040002c09404144a82c4800c074020031125035170f1101e204108480402c200d012034074814060585c07400b400600045040901180720b510024100c8282c42e9580d8098105000c2c00744152048541d02910030318844891b4201110003440c08002d8104c141c900e00000645510000201d034803100342511030042e1036859a0b400c1c2c00610894248039055502c40341c0c15100e42d41d6005030321220798801c401054803140003a05100400c0ca003452000300c582c2c980709074031454038443e021060340984200e0001d41d40791458400700d0040365507071000810500414101207003e010540013080342d110155070b16100b07240c002908507203e0202c4c483c2801c2a40010a003480000c590a02c680b1039130100e1300020840b045 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 293376573 1250 293375323 293375347
    0x7083301030c11120a030e160501200109080d1103040b04061814060405010c020a1a09010b060d0b090c0a0c060507180609051201140a05070c060c0305090c0405010f1a 73
    0x9131800d8182050400020310020b0560984070710250901044014443e030041003241d0038900025024a506110214100d80280e0483d051943d2000920000034410090b0f58641005c0c150040d2810350b2082e8103010a8041a030702c40d07000d580c0324030b4005900d24266143e90311401c0c01000070185c0a032046107056000700102d01305065aa41c400b15441c002c00305032416052050850706001d00010071500300c80705400c04201001d00a06071107034403200d40c14664030383e04240780c01000c410981940084000c00e00b40c03090a02a4042d035030b0f00c070040d51080c0999881041402041c8200e10701d08002c901c0e801d034280c0200c0c0e200d500c150b90010340313403c0074491466592070105900384a03604c42400a010708a0a00c05030501392516103407110460007c2c004400320248200005100504d06e0445540d110005020948258a022030040e00b248003003140d00303030380080140500030072940003441d4810501c2d60f000c2d078141485100e040329403c8c80c11442080c2003c0f102d084045010440d41d51000042c800c00d804a1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 293377823 1250 293376573 293376583
    0xa110319020a0303141303110106150f080f0c1c0609112206020d0f0c0c140f0108150f0103020d050a0902011e0e0d0201021507083301030c11 62
    0x40c510740040500038042e140c014207880c0c1c2c038400420400c10b0002442400000d810a900246030305041c01d9003c0c504104451740140001ea20081001c5000c4004514403034002118128242e040e9445c404190746820100e1800c440c291506048004200489401c40080070300d002c95400710703d60302259217540c43c0c0000003580c0030001d60350010304c4006200400c8600480700c14100d0f09039061b034048030525001000c0d440b10b542150750f50074044105241000c0f9031065085140a661244141006e40e807a43c920300901042d0a802c940540fa007070f0046441907000d0070109115040d019001c0404030082028088020141c2d0300e8030b8103140d000d01c62464040050f02401c4e116043c1e0110008141d58680001030901d0080c40d07003c0b07103d1380c807104210305403a072042880910440c141c85205d001c410303620040b458404901404540c4507241410b020f011640300140c280140100040400a01d804186201000e01c0e20180c0682e45010706500b0703030155000350888100350043d4203052014012801605040c0303 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 293379073 1250 293377823 293377867
    0x12070311010911130b09040209070216030b070f0e030714030a0b0a05060906010c080d110c0a21050906041a090603010b070615031212021b0a140105040302030a1103 72
    0x18030142d081498150404c5000d94550315200d58040c446070180700081000104080d0010303001d0f020b9400043e0195008104c207605008040446900702d84d0390b410100c040c604240c800c60b00040360b01c0031a051461081001c0b0362841002400350420501d0211030602046080c011b00da011701591020303201042c0300c100c115215110362a0b000c100740c07410004100244074005c1125061040f00a605804510303a04241ca21000d08211300241c01d541c0b22090030390314003e10058015501c590800d041c104201d0060b0b0500151311074040c2522001c880c001030308d45000e40a895508100d00b400100100c0c2108101c8444490f20003d8039441d0004880204000c0c0d8000d27006508100c00001d201c50801c01039128030040000401070301602c440c06c1d503940c0709182c080c0d00c0c4120100b000f18800d12903c034000c0c2d0b045039150205004205035150842d8506034454a0300d48042c2c490321b500e04078039003e425041c02024440c99156024610705080c02d0020f84500103070f03403807000051005205100030400c0301d401e01c4041c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 293380323 1250 293379073 293379083
    0xe0d050f0606090708010b07060906111215060f0d1107030206100b040e010306020c0f06150909030a02060106050f090604030606031b0308030a02090637020c03120703110109 76
    0x5504030220480c0d00e003090181078180a4a1a003003000b51080d44072509a045d02c02d9001c196a9590450034404007901c000315026003003504d03004c801d5410b03804d140000d210714441c070030b07451850340d40e6440109103861056000750341000080010324038240c80203000b005c80103800540046d442507140d0703960001d0b8100ca0310803005a8440c1041c0103100d40403480c1000248180c503030140c50f003801c00e04858424001840010700307803038022a104007c070f20180b1021b50741940d080308446583c90207201c04802e00810214081c054880e000200d1075005001c821201504651380050420f6481c02400300c4030355201c15007160805000340301c031030303180c0d030700c050040005602400f00070500c0d509604103040c41241c000c030400c545500d03803042040015009420340ba0f01c245684001602d0301c180c880490502d01c10560210105500441c0b070030350702c00300e40b81c0340040204055110300034001005400daa0354071171202841e078194091780c4c42187c00304260300105801c5101c2d2074485148225000c2150a65041e49070885e8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 293381573 1250 293380323 293380333
    0x151707030c080c010c110609090a0f0b06032a040801290409050d050a0905040e0a05060c0423010c0812070e0303070f06150b030f04030906030b1f0e0d05 67
    0x74862036400c0e101c082c0c14500050a226200800003a00a040d10302005140c218030205c1b607540d50340c41d80160303907003048051300c0303c1078500c0c041d9204002040000040c01142c1d2501040c0000b9007010002d03a4461040100048000d0004e4810b405d00d5925a4158070103500c000c00003c0703000701c02070203044041059500a04e5030282c040d0000007000c1049002c4a0103585020800c40105a0018200c0010016810b19a60300d002c030308411182e000103030700700c0d581150500d030b03031214005000641c2004084c090343c103607510f503110120041c0040c412441403510301d2004040650390724001840240c00d914050504c0d280c004069680e200700c5411028a40d4036071031101c000c10032802d07084440444095800c5000e14980055541d802c0d26201e26100040c00c07141c0d892a85503c20ba84080b004406815400105510b0740b0b46901c108a800d40201c500310f001402182001509070300a0040010111004004800b806c124000303443e148070569034000b042002922160a1a4451407581c9079800e01800c0070342 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 293382823 1250 293381573 293381579
    0x2041a0c19030f0e041d03030618040b010303030b060d09050c0111010e1203040501060918030306050904080301030b0a1b09030201090b030105011e020c03120417010608060703151707 80
    0x541031924070428140c400010328648000650f01000198400490b400c1c01000c050403400400c00410600d190741c0d0840681441807042030798000007651040310102d42c015580005040700300b007000b07005d031002017200242000600c0040d000745c2040cc3c24010107800d25003403a081207002415548911019a03268201540c1110035507071001072440f014140c0c4009110000c44c0101d4141c0d540c1c01e44901f465049130100100e01007000079040b61004101c000020b10070503c0040c0c00800c0040e01c42c0342240860715202d030004050404480d414070464208064a055070320b1078860642400d4004d054603402c07580c40c080f46601e141c403c2200c1c440b0400c030382d40d40302a4600310310014100020300d03044240701103402e1004110681e07100005003594009141032001102103880280d203490020b0380344660500541c914036014002010140c402c83d01c004480000380e070f601c0c103001800c8032901d01480800b9000400041d0303215010f038000c04a0030b42035540061070142d46099600c500c0b8070310489a0060b0700728080030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 293384073 1250 293382823 293382847
    0x60806010206060a15020c030709060519050a090507031b08091018140f030d090309090207150b0a05031207030e01021209150d020705010603050d05040f05040b0402041a 74
    0x1055008100380001e09050038003400040342030721248609001000e03125902d51910b482404a441c00550142c125000305407180c5da210090a054083c490044440100c03810b4001d903502460412182c024040e15030160401d00c020000c1c0c0001007000c8107044c1c41c1c81d0703040f162201c88413001d83d41982c10358440300d960922441c56400d01c00200ca101c09107900349661148800014410000d00035484114010507000c1812032504100312030070800384500011640810744d032065000400b00c41d100c0e43e11020016124040041203000740a00542101142410b0341c0d030481d804e82c400d01c001c080041502d10219941c1c0000780c501000a18900d41950021590508042e002940324080d44000d0001c0c040c0c20200003001d0801d4000c044020f482403404502c0301c07900c4000d0100322010201c080505564440b079608100e07010b44400d20045406105000203490014880e00a40742941c403041d5940d9a018078140810029010000200ea8056130030000003031520140f03202c080085401081098441c03000c2408 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 293385323 1250 293384073 293384087
    0x220b040204050606071a070c0812010e0610051b0c03011806050c0406020a0f1e030c1214070204151e0f3507083009010e010c03260106 59
    0xf41c0d40101e00c280000c000103241144450020024040c010704541d84c2d4010031100c0c0f07035944402800c40b103000610003051546100c0494107030380c0480141051506c4500502c01c1e0442d800c1541000100140a444e8007403120100031480c2032020340442c1c590a1013040082d0848200c810405140e0308041701e00d90400407540070b40303680300d4a0031a2190030545443d0010b900c4540300c00c001401117040340f020004115180002c1303059107400d245c18800d0b110351854007605107032408070181c5501d1031300d5086e0284603224148c140c2281d40f08202e09c60030270a40e5424030003d005044c60400c0d00c0062524041400c06403042440a403130000c0f12300044861526595080c008000d800001720740c21001c0d03840340d100f008449040d61900010500b841d07403a985924150606210b034111070b00c00d0285000142ca400716541204003030b04060f40900c5104044010300404e24031a114250f4080b8040c840744002560041a4000c481806820170f001c095031001c03103c8001401d10f02c60320303402071100c0f030040c8a4250311042c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 293386573 1250 293385323 293385331
    0x90a090204062304090912080603060123030717160b07080427050108060a060801050f070f1106010b070b070201021804020904110f030106030b030a03080f220b04020405 74
    0x8501d0941072a0b0300500e811440b14200007444070090302200100619070440e001031a4440c020030284026280030701c1501000c04c4005d00084440300032030468540421064121020050303580f00010400c1c44402d0030000c205000340d0b0500a0400029901480c2d1000000c0d9807500b00180002440804241c20840c49036002909481000d203e00f00003e140f00c0221030940b0381d55401d11002d905042c007403013440000c5410100300710b41880d000043c1e0500c0040c805e40902102c460030b1000d0b94071004801d080b80c4007165021000c01442002c0b80c0c255004905000c500c1c1c4052800b4100e0f40350110201e03107801c40a034402c103103403100000c1020500ca252406a6003154652000b981780c0708401015584080782294428800e503400184224159110b03881051300c040030071f440f69210406c843d10364805410074821400441d00b80707803c40304145400b090904c3c1255050f150415582c4441c0c00085810b9401007803002444401e04540008c41703984049890702c5480b880c000000c40c40c09205003c00c0d158090 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 293387823 1250 293386573 293386589
    0x20607060608060c1318020702040f0b0906060708040e0402030c0d120207150e0f010e0310020319020306010c03031505150310080f0a060b06040905010b0406110312060913060e03090a 80
    0x440f4031078804010940c05c40440d070107986075268104400da0024000d01c2900340096005182408014204280da08002d19102007101c02005031b03a10001404540d01c60000000d1940b801000305020b408502c81010b50014005800c4541c0c0302c060201081050780240001e40e8104003007201c2c02c400c25030401524002e00010b4410a015401c40c1c2c401034001c503021111035205000480018855922a017030020141000504450081d00e00f641e50400a44c02901c20b40300c5000300d16a03c4881030070078000c03240918810380d5000541c82658904800400030b500484101000c441000160741c2d90b00207000c640c84c0c8902076040c0c1d0340d0618130310100058040c1d03030058240e0340140105600e201e00c08615403000e40c0e00880c0200e50b0603081c01c009101486107410503000d039403500c40045200c0a446024209a6620340c4900c224410007a0b0321507528059030204100d592926000101e55080c19001d8641100401c0300c0e0503000d42c0b10390783d51030a036810200c450030103030300109042c1540c1c40c2401d001300041840d1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 293389073 1250 293387823 293387827
    0xb01020a020a061b082d07020913060e1002030a050709030503030a02180a0f0f0803040e041e0f060b270115020a060c09060f111507020307020607060608060c 69
    0x964040342102c0c1a078401e480c10710000c0f00c03d00518001c4031311001241c650040c1074903070341d5816104140d0000340d40c0c0c4140303881d210000301004101c404603040300c42a50700140f1281240da100e8009074160101f8407800c4071021b44881003242004000c01410b0829006c0c003a015859117031a000b101d0441d20024003200401110842c10070214030013004607a000008400091b80c0c811030451180080041498020f030040c44005001421201d02c4a0701800c1c2c807168420290044e0b034489119a881c0218064011980d03000004140040d070314828000a190021804102a0aa90722440118100800d0603950f80380c03102034000c4186802102c090101c402081c2c140402e403501c41c0d800c400d40320140610707940400c40c07800d8681054020010460007a6020b401400401c001d55002080e4400324800da8011030420400282c8036402503c1404a2490103001000d450110010b96a42d054014002c1802e5000800400e4003503100c0400820b1010f0144902240280ca05103c0c64500400200001e240ea142 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 293390323 1250 293389073 293389093
    0x90c0d140114090f061201090209040c050a1509060e040e151609061403040f08030106050c010f05060f010f031d030c0d1e2d030b030c0a1a030406090519060b0102 71
    0x44140136541114040c3c80350b036041c0d40101c140da80100044100030b5403120b0600c040004210f1081c60b400c05885060b14400016503442528040c2202c00c0d0580c10042000660f0500c1920f02c01c03802c641c80850000c6c80407072000c0f942000c1500301000c60386400035000705101004020101021101c1208401c0e28040e2000c0c1d24011004103181e00c100008441f82c0c0c4000040340c00e00240007374116a060708200d5407507895039101409000d03030b0701a40ca00040740d42000c442448046003403103518400d500c05080c0c841d081104200443e80303219043d8045003170594030b0b400400a22285007881446980c8900110790300c18003501c40030b11b484400c2c1c80d04400c1002207001020050004c1556414000380e5061826258404122041c0140e000310342c1e83c0b4041d80b400b44209401c540c16008450480010ba00380c031141307441c0b403062044003c82806101180601016200810254013000f554024041c0c0e000158203011940c0c0c079824010311391484004852110252001d001c520b2203100710340c0381c2c00d0009210400d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 293391573 1250 293390323 293390341
    0x105090102030403061d06010611010501081603120306081906050f1308280314100312120f021305270105131b02010507170114090c0d14011409 63
    0x403c0d804020b119944038482825205444a07482c03c450090b0b4082c3d903850b42e12040c00801a80c040142d204c0c456080200021741440b012a40000c4110b0400b891100c05003503843e05c40030120b100300d0803402c06075503c0c2c0006a0321400c1c8414030540c60340c1d820003000501ca82c24070f9425104090310010070805080c05014003045140b0701071182c150310a40c80c1d51103805544c0c40c902400d820301c840b400e81030f00c41d000c0d10f881c02d81d0580c0400981034182d60200b00e56165002261803a80041c000182036110300ba00c40c2c0031007130081200312219a9070000c08210b01d40081610700c180e030061710b040c10390b26882c58424440c0f0704d40002c02112401450b602c000b04407501d01d191035500c2d041840744a001d00d0560310050500195074004145240302038000992001103040d0007802071030300312051400104510280e9466241d0900814100c46503c0d010300340340100d04040046641000d000480b40f000e0400c801140c0c4061806a80070350112080d142c2c2207581341c81c866841c800c242c500c450b13104810389030420400078 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 293392823 1250 293391573 293391577
    0x3110301051005191e0507032c220e0609030906070303061d0f0a09080403171306110c0a050108040b070504120b0a0b010e100804030212030a0c0e010509010203 70
    0x5041121000800b036403402c0141c03080d100c0e0008003500d90740c511246046254000101c000003c181e62103d030f03c20320012500701c0c0d00b0301030307080000d00081101c00c03803001e50341c10009c03a030b0030781407001c10004625800c50000400c1d031280000c07a82c0b020300d036400e07010000102e07611aa0760302e6000600034101515100c583c0303544900c601d0b4007061040300e020400809141c8654000c00c0038218481285580e1b5000c00040c6682c1380d0700311191110b08a480000900d0791142d40500f05c865584075814606144c10350b504d5021411240102c05079840c0280401d100b90b5403a60010002041181c50302e800320200c2e0760102c0e0600d002400d0b0240940c1c688501040b072640c1c0448429449900202c2100607500e40c800e0480f05482694410209102800c440009000901203110700500c1c0361542040360584080054502d080c2c280d075030302d911240c0002e4507130030780340503c0e00150700602c00d10540c0c030040415020030210350400d540041039140d899017455522500550b02e00e010020900300a8107203251800000c0d624 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 293394073 1250 293392823 293392829
    0xe031f090c1e17030d0501081e0d0504050405150907091a091f031d0313050409050316050313030c0302030c041b052115090a020307020a1e020301050f07020d03110301 73
    0x204a8201600030703c040b090080d520b005450070b0084c04070356556801c86a41c3e04060000b840481c040d000f00380d2009000041c2900c900074662111400d040ca08801c01c0010a001080e00d0407443c5001202035031541d841c000c0b02d21401d020f071200050b50341411412010103882002c21140940204015481c03581c4a00140404084900c10200004020340c011000f804040c901603a40507210b00c101d106c01d15011001e40b0700384550001c6214a180e0f5001040142d07145004060302a400821018504c80c5543c0c0c50321804d180100100d900d0008030004010092856600030344410603642c10910852406024145100c0011a0244450604803512443d04c1c1810f6801d4018440005043d0600c0c4515803000c451110350020318100b207140600340b020341800c01c039020714464221400081c44c000000e200f56406006682c1c020018410196140c5000d14403c258211039551811003030300043c0d4003400380c503225011224000d0420b0410600c043c2c43c0059800104050509180b000d03441151a00141c80c11 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 293395323 1250 293394073 293394089
    0x60904020607110909011d010b0d0308060d0c090c090b030f01060e0102070e010b190c050c010c1a0403020d020d020c0d0209071829040608070e031f090c1e 68
    0x241e000149482c0f500d5030240305101c1e820007000010400044010f40c041c00012000605040c0da0305640a0210700300c031013594400e0340c885e03195a50b50300131030720440030030f0352020380508001d102458648030b40c11b601006038000da0503030b03480b1719407050403c0c2e1008180c0000c0081450701400e60900032a80700c1d40f00b5050007440200071100c488209140e20801580005004051000c900d6503101c1a62800e00e034451213403003070548036945075150310610800c5000091a000b001400028070b688004482d2494002c4058900310171071020402d019248645450050340300307800400704042122000307800d04154001541c1590031001e0640d4980e154200e0541d4040c0c0c0c101c44107102c0c1e41c3e50070b4090b160002c808004103c120300069000c9904404000e00500c0c0e006080075541c141d20114000e8640c92185016070400a80007501064419018081542240000506980c58000c603155004100e41c0000c0c24550303c0c64840c44000244000600203501a05d005a40700560700760300d03103424028860303038814a00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 293396573 1250 293395323 293395327
    0xa03060b16151b08040204060501020f060a0507030605060a020c03010605060906040501050d1104030b09070902071707020a0306110d050c120415090c15021014070e01020c09040f0b09060609040206 86
    0x4a0100c41c3e900c030b6000c8900a401101000203001401480c0c460f04580881c0100e107071042c082001e48c000100c02c904189000010507150340c54031252000303440c014020105050f154100803c003a03896001909600303a83d43c0c001c0141c5000b09080500352a03c80c0e10850145500300007a2040b501e4450480303040d01c0e42070908940d00d40150584400030951040c01c01181d602c04170300030080000060095010740360800494802d10303101c0148804a2161001c01031004400c0c0e501d00e441c0d12484005001c00d00d000400d205400c903500e840340400c0e6403070407404983d0324900180340c2c080e2010728810706802c0130003038420f030b800c002c0019901242010050000f400c15900d100c030b1084c50f024190440b103e510b03401024506165035a060211455104507660320160241c0e40200365400814441c1844000386501c0f00340c1d03140c89144e81038074072074102c03003c2d40c0c114014105004025102d001026000382d228a00d059200d0343d040c00c00506428001d4164100303500014148805580c844402c0d136000b54040b6107a60f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 293397823 1250 293396573 293396603
    0xc0803070f18050f150405062107030e0606220f0c02010f090b0c0f0f0d090b07020d020d080a020708030f0114091303121404110316030503071506050d05030a03060b16 73
    0xc5ca44c2c0c000e503440740323034071000016101082811801c915200c8c4408448018079503111a0b03030540540b80c0c441c1015089500c8840090400d241182240700c0201c050083d0341c0c43c1901d0141d04000340c0390303411108201992034051b0580c0c01c03542403240c0e00003010003010400c0719190b950703038240100201a00049400e400450003441c0e00168404440034560302841c9181e070350504400c4500a001094416600c20346000c002981007400030903c81d0301040f00d98060540b0058401d815180700ba4060503103c10305074248403050010b5494001540201090712080c0030540c90058500c4421420700b65440c011800304050054440d4034260854017140d06041c001d00144101c00b40200602807c100300c2040400e030030030b11048c80085810070403440c1c03054040e11031030000141c9030740d0855410b00c001041c85d0b10802c80030f0085043c08440e00022000c403000890450f0b92034000450001e83c0350400c2e078443c3c00004007512030760340602c41c0a00034240c80300b55a0803c406a81c6c11405070b0798484005e030151040d80f0003a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 293399073 1250 293397823 293397859
    0x140d0203031f170c040507030501050612040519140c0a0b0301060507030e0904121215050d0602091027050607020607141212060607020306160c0803070f18050f 70
    0x206000c0e20b43d0680301460605250007059a80b03120300c0d40d46014500c0c240208625501c60b02440c2d0580c0c1001d492149030071080100084000002001580d041c0617140c0c51080805485a15031103e40c001c40845031a0301598103114240501d8800880c03003140210410050300040704103680c1100c1c101d0401031348445142c141580c810f0004440c09610103424400c210030440a0710b02440304401594940049002400304002203546060301006920740f150360422603403915448400031103100e0381001d41014008170128080c0c03400b943c106800700e580380707030451400161410f030012101e00c480c202151003403a201c0861034034411100003034010b0400041060074840e008250448803d041c204a594011020040c0502604286090780075009804046030322482d000050f41d15081d002000342c6501d8650140c8414030804402c1c40000340190f034407468021904842c040c521584190b01d4541c0361400401c8014218103c0040529440c180b07000248866150440341c0284910192000d990000110b146 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 293400323 1250 293399073 293399131
    0x4020c2a10082203050d180b0c07020a170c0306090303040b0103080703110f03090a050103020301080d050c1603200108090d11030d06031101090b040e06060901050c0d0903140d020303 80
    0x16000d201d01c100f000004065018000700102c03e0204010000a5545000b0700022001180302511900ba50004a11200207000090140a00c000c0105007100d0745d0f0144001046100b001d40390b52500320305142086030400340041d0741d000004001035480c520349581e030b0713020303096040c08040c1a4500c08103000041501400c01c43c144e191415089038848120450000ea1f294090000340340502203010002429500a0080c2c1303040c0c40105000d488481e08a480031601500042075070841c52083c4044008110307000711810300a14090000c0308140170558107119413401012200c2e504221981d010082103240c00308415844032814506001844038040c8890301d9800b13070a84000803285459800000c11072864130724030717a0080a0325031030100c0e41d441c80212514000c1d445a00c2500103158001a5203141000c001c1c21f8035a4141041c6013000000800c8503e0066501d03032410124842e4901070051010070007514546a0403640213040440221000030344a01016000c2501064901009115501c1d80d010b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 293401573 1250 293400323 293400361
    0x60f0301020313020a0503210a051308010204030605060916080702030d060e160813061808040e09010e0c01171008030c060f010806070c030c0201020c04020c2a1008 72
    0x4000d6490b8104560342e800b000d51543c2c400c038800d03415420b0024079800c010910611a40340d0b01104005601c03036a1000701d07150300260a5800304001000003020840c141c4000c0c00250641400061f03c1d0390842ca882c07000c440000d0b180b148940e0541c01006003900880010b10714001c62031401e903a003601d8403003003681f45026030b002c82041d10b8104400403400c0c912042070b05100c2e0104d1704120f000183c0107202580c500a0036075040c900d81d003201401601043c0b0300d4003c15a019601802c180e001d41c010b80321100c5540140c3c1044d2081402ca005122103218240a01880c03a008180a490351019a400107060900c03400014604004a01c000610000c0241001401403082500343c81e41c0d04028089941c44000c00c03204406401d40000002c01c0c031031000229944070700fa41c1e40320380703002861544083c0c42540e0810750880c1144030b00c3d540b80c10b60b521640040d0000740e0200f40100100302082100c040032003035000f44803075080b0105190103401e5a600380c0e582d240b0030490a0140c0c26403140240c2c42c415505100b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 293402823 1250 293401573 293401579
    0x60e01140d02062d07020f092503020a0e03060609061309050a08070210020c0102071a090a0609080f03031314030705010203070f09060c0f030302030c09130204030c0b040f0608060f 79
    0x4104841c0905140c0c03131103072809800d07a02c042140a222038481c0300f45c1c09450781c06500962850181941820100055500300741c8008581d50025085040c1c40c451034251969100041c0e00843c1805240c0d030040f400320b02415040b00a000503140c1600070075091000140618800c1c86005103502e010240c60340701c0c1010a4100301520440b58044c00c2101c190791043d0030490065902c400403ca64920105007042c2500050b80640078141c46c00c3c00607442d03484000c0500804401c20001c00d1042d6468281c41d100604507501c03003699075031800350030701c0c10000c407003c1001040e0410810450000d80c9888085140703a84540d40c0d9960708500000c0c240b0794011020024055071000040c4240300e90000c0a442400c95a0387d1030304c4145071076507400c07074140701c01c090020505804814207000090107500510b62018411040d1420f15845c00001015007081001400c00564001414003c0c00b1240c03500038083d19010703100501e040d103454121040b6000c680b0601d010018124080b4841d030303071400d0380300c141d01c9801 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 293404073 1250 293402823 293402827
    0x14030a091a06150705030f0a050408010c020c191202120a1211010f0b0d060507110a08071401020306100c0c050a080c0108070e010c0f020d0c030b19060e01140d0206 72
    0x101e07a19a0310200192a850722601d185500503a8000164045807610350307004002e98100626a00211500e8004500701800d006040c0400300d42d00030244550214018140d000303081c4500c150042c400c4214029900e01201c198104040c880e040f50904042c160790741c1642c50a00e0742280102990408003c954028090840d21411412035503020040540c04c0d0300d06402000111079000303415040f20f954260140e0400c0c1131148200209030954401540700c1000d08110425101c0d00102600b00f803040c0300200c402400211303a040c18040c80d10701c8a441c1c0d0306039030000c40c614140440050f41002a4407940c808200c05141303070104000c000c0d41080c008050103000b001e0303034030389071a03010341c550340018100340c0010b1010000400d890f1203603803182c0f0300c0e00701a1601090702e05076031241c84181e000b42a040c0d8001c01d44494100000700304840020045009044411460828400103014195195081c104490038100180800702ea4041c009044824080d09240c00056a001084180b0710542c4042d511540c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 293405323 1250 293404073 293404103
    0xc03160801210c3209070c0f2105121303090509070306050607060606030c020a0c050609010509030a0b01080d0801080d0509041d033406021605030304030f08010504090314030a09 78
    0x1307a00d900c1c24600603100241c6004441c01e00038030216810440b1301d140010140300401001c182034400d024241d6000c1da05240c42000c0740d00701c40a18034607424080780000c40c00900303140000320716005260802e0110360843c2d00c02e00281c070010300100107400341c640300314100004200c15034041d9008500400d4090a056220300c04c2e41400e070002c050610039900030034208180c3c0c0200c9480070500136003076039101c200b0041c2c02d81041c0501c815a000002c095040c01810800424103550410503154464480d1094031394640c10001d40d1410200340c240c5207400d0244442c01403202010101d61400c03220050300d00389850300980c2e4000790103842068442c844076008054881d500d2440400244000050702013600d19910941d408140d0310b14203000d105d61001003206454000071502d030018034409a0504060b807080c0c0711a181c003070a40c0d00582e000c80c00310b6000172140e640380750011315550062000b11000c0000d00200d450103003401030441d41c04042e09a0000c00519049441e5010b1b041081d002a44552920741d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 293406573 1250 293405323 293405369
    0x4091802060d0e071205150115141803102a05030708131202010603060501060c050304120204090b09030a2d0305180a1103010506041107080304020604030204050c03160801210c 77
    0x80c0b00da121258847e0320400464046d00c0070840918444541d03650601000c1e806c04801b406404c00ad04026400c500031104403219541002000c084180715000007a6a91111002c036407240c090641c0c0b01030000034010040d580719085000c0d0380d440aa1410031110f0f5944a07462070010702002d820003005200d0707009522103280d5055200c441581e200b10b8040289903203840055440250242004145a000700014410010b1040420f0300491000d4004502aa2965544004076408558a0541c1d40c0081000e8001c40e03841240600c03600c00d50030b0fa10092001c0d6600e04d810324042400c2d4402419211808121041e40d1b084c0140201040107064401c40607246c90241016124402064465820300000c21068605407044d107458103500001d4900d030000664400b045500001c106a034421020b010000150b1680d0060314407038100b18045c0c503a60b180c03461000c0c00348142601414100b042440050016940501040c86100c0c000890b48080102c10700d000400103c0c640c00c82141c1a03049400040958 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 293407823 1250 293406573 293406583
    0x7240608031201140310020d0204270c09050105160f02130c02070f050603070f11120307022e0207080d0f06170d020613060b120304091802060d0e071205 67
    0xd40c2c04600700c5500e0b40d80c2d0980a00b908180c0c1c2002d94950004001010743d46910341c020209605032200160500c0d5503404089482c400081251103160000002c00c1c03440c000510600e0480c1e00701d82042000729081800007016801625412904003c5d2450800140070a110035040c1c0140d004142400003001040700c140a8070000d02004090700c10700002040c5010079440804c15100c0c0544a50300711360310400704031621800810304400b070105115000081038801e000707201c51000e012001ca40e8904248200070700d00700f0820480313000000d850318480403840113150714114a400700c120150716605076042c2100d03580708011030f6800301c92510030592800802e40e00400b0844941c0012802844c00013028171b030712400e040d1409001604082c0c000303900c491000d11800b81d2503006900c00a1f031001020b000c0f070051078a81c0440a190f9001050070004000d082c00b400d01965000007140016585c9a0b0129459014241040320010384854909000c5403040100400030801500f20306042409400c0807600c030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 293409073 1250 293407823 293407837
    0x20f041205100c03020d0b011e03020a1704060c1d010f080604140103050615061c1109040e0616180311010c05330610181a1315050724060803 62
    0x71b0b400c01d04240c00302d6000351301e80b080081420091303c807045002036040340294808844602030011a82428000100101da20361144d0320502c03000030703100326120b806010162209105204543c10508440441c0d0384118290022240c60510380d02c191204c100040203040c4144a44244040b02000001885400100680520b004900300103403440480144913052091200028040400c00e4020700c2c0220607a0001e8070303190014441e2801c040300d140000c0d040e01d1640141c0001540042c0900c81c625040d1400345035003642c6400d03e2182040106034070841e01d4020b100145c01840c0c02c4108203000d9005c2c0081c2108103074000107462100505200382001100012803c2070016039281940c0c040c96104008980601401030419103110024841152032040410006400c2038001d400090300411040b0768034a60160341c8241521990071640041001034907a114044a40c00d08000c24107954201c801c039040b00f074100d8000d40c101e00b001c80d425464290304040c0030b000304d0301e44400020301700804400361000c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 293410323 1250 293409073 293409097
    0x14010810062c101a040e0901091e0501140408090a05030304050d2003070b07060c03180633061205010f0510020106030b0a020403060e070503032502091008060a020f041205100c0302 79
    0x6d1511020521422075080c50700042541e440ca0016100d0b2205205001640a10460000c1364088901e01c0e0261000000c0c2c038202d0701b2a202180044c4245410f02012003d064258011030a0501c0c1c0800690f8503000080080c00c0d041d00030410007050b54960301030704035540004d82111203555275440c0d5200b0b241d00c246401d40d00e4034902003a18a900e40320340038801482c0d5200b07501c070301c561455840c0e40000b0030744210344131025a0003038240d0320755a405100300024a440b01c03501d10308071490b140c1c01500e4180b10584000c01145000c00500c0125841c0e8006030580b00142d607420344050000d0307000e9005120365003000e008015540208035518580741c0040c0281e038455002880313070750003010103a43e540b41203001e6240c0c55041801030340505c45140c45071001d0840e20b655120740c4000c45401240c2000001d60f04000180700a81c1c0501040704200b2185800c60002d0400714a0841340e550001841d005038004c05243c2d003201c4501a050000412091b90104d0145a08101700c0318a403401400a500984040c10 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 293411573 1250 293410323 293410349
    0x109050606060d06051f1101060f060f170406020306120105060d032a060506040b04020a08010303030213030f080a0f0903030813020a0801020c010f060503070602030301140414010810062c101a04 85
    0x7c4814041c022a000c407801440211651400c061066500c03119482d814000c00c20800140441401a0212240268003a81005030f40381400d4040c000c41411340114013036983e050070b05000c000e880382d05030040b0642c0c040c07401c06042c2a2012400c1c04c00405250420100c0340e01c2d0034101c0a10446920a038050f0400329005c2040841d00b4003403005031b019030030160001c5040300004102083c000c0d00207001100100c1e07403c2e200c241d1281c0c1c484400c00103515056903041c0c5d000c9100340c003654114483d07950714280b90034800e0350b4500c0d55900600c615801041c2d000f940703460074a03000440d158040340c04080e080f010003e64441c4400e52055008048900d0980c0e413903070400d2000255801c1c045040c009891069004e1481e41e0b0030701d001c40e0f9086000302ea0031a0042d940340c0c0310744800703403900c40c0e1036020b0320140323014003290421007024405a4030f098104515610103225003002c8d040d00c2103170b088081f00e2056444500756407000d40800c520500e45c1c6c0088032414410b81c480ca104080030f0020015150400f50800e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 293412823 1250 293411573 293411597
    0x1205090114040b070f0c12080901020f0a050706060e01030203030412021f0305070e060a120902130e0714041401050405090f0d0207170f0a23011a0306090109050606060d06051f 77
    0x1c81c10040e108003d0040e14661f1901000144150080e503440552640098071b84001c0112400d01c85d0301c207801040006502069150400145024800040000181d05a043d50460f00004e85034800e03071090041081d201d01c0b0000454440000711002008440108424060031035009005400e04a415100180150326500c0b00c516009040d00c4030888103540b8880c0010304040c2c888020700301102c0580e4040c01007180001d000b1007d000d54906440850041c2242034900598901103d880c190900e104504103d82001ea285019440c60304544003181c01080075258807243c582055040900303900c46014141c0ac4020361034001074083c08881900f81034616282000e6a85d81c2c4500c001414070312190032031800400410300043e900d40050300b04a492414002111060034211000240049900c010201d500321b020314051040c50f9100b002c243c001d102e54919a13a804c0d0311014020010384c410100891a401515015844030000d003801030b0413040c0c07508070000b50710a070000040b003810002d40002802 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 293414073 1250 293412823 293412827
    0x10f05031903081b0c06010305030415021c081e010b0a140412030e01050d020d050711152a0f07020a05030a170a051606061a0405011205090114040b070f 67
    0x40d003919405a80e01c15207521400441e041076180e20740c0c4c4d4010070801340025100e00ca0140003e500851040d8025983d903858078207190b1040500710361040941d0003041036858062411034109007010401c3c904036000e90740d0028180e080c9501010080010003401e0004148074149200600d084412520340030a940035030910769005114600802030303800030301e026074030000f4001c43ca40360300400141070960070320150002c0c1e003049030000e00b104072002d901e0b24103012050340c114060300392641340c0324050038100200c0043c1d51029000500140003908900c03c0c000030510b0f65142803002070b00000b01040e03441c48552246042d580000c40d0582c480d00030b103240000d4502d00003442c00d9420340c1c810b0b4100f503455803203501d11480350050810031090201c10400c402203000c0d0489201840340c0308440020f913460520000c0b10201c1716290782055030480410040c441c0342c0e00603031500302c0801080004a041c0c0c0d6000c241902400300e22103414108004002408104811016400c0c49a20700ea91240c10405200c001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 293415323 1250 293414073 293414113
    0x305060d1e051e0106050f040c0206191803030203040c12030801030305030c0904050c270a0b0c07030b0117100902100c020f03030a0302070b0f0402032a0603010f0503 73
    0x100400c100140360004080c050076100d1a000540103405840b0803620154801e00a05400c0720511103695540d4001c6c84949020103a1040840f0203890402002c0014140a9510580507016001d8480e404020700050080f9800c03c81d0076080b400d004000400280c0750190283d00306443c2100c04242c034802c00b240f49080341001c150f80c0360700740d0b60344022a440c41e00c094910b944040c0460001c039108101740c403620f031500c1c00b8040c00703980c00705005655100300500d120881c9565054182800303501400001440d5110740d640707400c0d5048004555a1180031400071445c0c403445a1000784081c2500c00001156080146001c0494011109540300d005110120340d0807248001c20003544000c1060034034802c540700d28950798446101420040780766003c500080d1550b00191440340000e500020b17180200400f911b0303860b400c07043c000b4065049040c60360000e41c0300c141151250041c1081c03402c0d584541c0600f074290320362100300a0708403660303940c407500c012480d155203021315400ba100300e0408a207907070b40543c1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 293416573 1250 293415323 293415349
    0x803090d0b130209010f050f1e0f0315070309030f030c021e10141006090f03062d0b010801050d0213050a020f0d020c01060f0e01060302092806030506 66
    0x100100e204603a403000303071648014002110a00402641d4030068a800072800c1c060a14040d00c900007a01d090300b0018803030b40b00030540380a040303502584a0b00034640700880d80b81c410201c40303c50032854a00003082c68103040e094681c90071402801845000e5400d075100390101030290ba184140c549900105078161403120b0f0164005071b0100c010340504035105400300706801210416a00c54204035a4440165030030340726a450340e03000d804148041e030a4522041c03c001c00040c14241c18580c0341c0b4040e000d0b4140b651001034078140c2c0b0b682d8001038048251054624051455640c010000a610300e894014110640a640800c4e0014004181d510b0112044411598010b0518290802d545014030140202a01c1b0105582c2c0901a0240303c51040c4003600d05001c24010058441441c1d920507400e42c0d049501042c48201540300c184041060118280e064405c207003005a42c4a0f800004142800c1800e01c020010405a4140381545006240c40d507080380d250f5a0248120303100d200c100804145000c0d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 293417823 1250 293416573 293416579
    0x2100c030909090f02030607031e060803040e0c041d07080f090a120201060b2b0e0604030c1703070201050a060806070509040f111306020105130f0f020f04060801020a020106080309 79
    0x45000c000c10007983c2c105103041d034443d01c038021070f00c1095030201e49008015244400426140e00d04100032803604c944010400000000c18080c0e0751030000d00d2503c03031195010340340346414030340d00040300c002c91340044a000345100b04080c0c0c0700c09400042803040d4982510b86400003105140403036101c40e1109481030003000c4903000382c120860710340d0358021281e001030402020344d502d131a070020301640f100000d466a0311001001051400d80b0b400204564280c400800042e46e04c0c00080001401000800941c043d5141c02e2400a10b11141040c00c031704041000003e0920000204201081c2e80c1900601e0088415034814480f20b030300c0c2c008458440004030781b040700141040c0320001080c9810340040b0a50b802c03180c800520740e009000f10004076030004450404c10f200041c030400002d98244101030340550020484944500300e40c1d01c4c0342500748a24000341064290030080710039941c030700811481c5894020000c000080c1e9602088e0f001c1d402040d00200554609000042d808030f001c0200e81d0390303960003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 293419073 1250 293417823 293417837
    0x7030801060807270501020f031603050f040b0409090501050601020109021f11070909050d14030105040906020c01050a321b0d11090a090b0d0b13061802100c03 70
    0x800c100b140c00c00c0e80240f000081020042070100b900030103c061410300103c0b19092407403a400c1c400060710b007040300780720320140b50b10411402c803094807405c1942d03090550600e8640d0b620355440c0f0803885980074903004400d151000003400210228150301c4208424801e01c000d005070707641c450041e4201c0b9034440c0042c1d00080c007044060140900d1600702e0102d210242440f00f841d034048220a450322100d500200740c0c49039103250203418810200b0846283c01c03040e25140d010410852440c080e140018814203001e1501c03460043d0400c036058054410419141000704030b2850075003400006000301308140e004946034200e100c40014400d020f8809001d03000046444240c540c100791044511400c0140b04421b80700b480200fa041c04140a9203901e084030116a5884952840401401880070340c0000a00c81ca00480f20256480e01d42070300540507002118070400b80c1d100003c4401040d00c3e00300003080781d4078146211500c0d940015000c00c9860007983e070b00f842d000445800f0345404d640e030400600440c440f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 293420323 1250 293419073 293419079
    0x90d03110309100203070306170f060c040602071203031103040b100602120906030a09020604030303050a0b0103051303120605060f04140607051b060d0e01020c121804020f090613060201050a0207030801 88
    0xc513001143c0048852500140c5c040c0c1c0e8000303a0036104151a10302100e03800c54010314902801c108101c0c1c0e006001d1070f500030301d0b00b0f14082000c1c2d52005944500b034403003112030700031505060207580540e94040300343c0002603070791510b85000c00c001041143d1102c90031866080100d061840040c40300f01900005040300d01d0a07000c0d07000c1003400c0e0001016802c0d4961962101c2c0010b032601030151005600c00c2d00e01080c01e0400a2002043d503000c1d0301224105458a003c03c6680c03507002686250494150800d00702200a00903450094805908400e42005000490103000c5001000520880d8138800e007031b0340300101c030000b00070b2284503150010b015503000f68200e10000d4a1004403003c00307817004181d14503105002401d034084d6000102d010000cad0354085a107106c052000d100700051145060000352070035240e001c00e81503a054401d42d02d0b005950114018100441003403c40317040120040c50146c440541102425000840740a1980154242400702e1a041200d0086c0c031032940d4952580e5003107a003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 293421573 1250 293420323 293420353
    0x5060307050603190c0f0e0409080f1806030c071104111c0207051209180103032a0203011a1306050901090b0102010f06170c060c030d1104080303090d03110309 70
    0x405016544281341034110f26a00d45054070480350400c0c1543c80b91070180c80402c44c094481e0f0300540000340202d01f852941000141c01c40101c0b85a03025542c0c8594a0700b0360128030540e10920050000d8000c48008148141406810041c040d410710500da410202000e05080c0011303156041002048400d0500c51131450000140f41c0310344041030b40354014141140f903194245042002410291f441ca00011500b04600b40b030754916140ca11022a000065495964010102d40c02c3e25421480300354481c001d1814410800b0311110b10a400034004d010405d034035400b01000208115032140702e0405483c1c0311000100c0c070b01a20f411500004d1482c1e403103a182201385805020140c40290455603159003c1440a01c1d503c00c901c040e002030b032071000d00d00e102d00002e6882c020400c035010744200b000b0700141c1d0709142c3c000111030200d0400e9402003400c0e002840d81c024280215000701e140c03400048200314034100001040200a10340350340034071150101e42403210706c5100568030784c50a50000a00780001003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 293422823 1250 293421573 293421577
    0x405090112030c0807061512230f071d130807020103090f0204020c0a0b130c17070b0705010e1006030203030a0309031b0804050f1002060f0702031c0e010c03050603070506 75
    0x150290500070b10700540741d40c0b0301004c0c1d8040d031000c440340c1380d45030090100f00c03070300040c182e0141502880c200d4080d5440c2c0c441c04204100c40614000091070240c420072030304d40a020040c210000b140840300300f15141d1403510070f1054910038004101d1282c500288000d1550341910762656048a000ca1401c0b0b820b40044026206004003a143c4405009450340141c8942c8024101480c0c14030203000d900780c45103809010314901805d0032078100c0300080100c01240454040c0011038807101340c0310008d0141d6144060809036960b01504403010082401000c1c000190032101c0140d55200c103442c0181d00700101d1604840c428000690113034018010740f60b92500075408034140c9406030030150004000c020b413070140c1500c401c50407036030100041020020b50402000744000c180c1d007112106586003c1550003942d418009000b00203021007100402d404900a02c1120400c900c40e80280700352602c01801c91010f014038a4012555600c0e005008404134800c0c0706d600e025420080c060321241c0d02d80402c01c000c0d5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 293424073 1250 293422823 293422859
    0x80103060c02011b020c040c090b040e060319050304090507090609060e0409021e01080c0304051c0e0a031a1b0f090402040b12060a120b0103030c031701141504050901 73
    0x1540d80d070345036410b104000c130b18040d1341c20405900402200b20b840d018007056440100303140061101860060081b0800720095405580302404101010340d03400000031304d0030540d0f0440c440148041d00b00355092000110050041d100b02c0034007401340e900c1e8203004079075140c014891200041c4041c101406010300c541640381400500a00220f00d03180c607500098584005482481040c55043c0e900180341d5801500c01e9501040c950112421440c080e03c0b800e032110740a80f640341c01c0d0b080804040b45c05074004d00840202c503c015001044a640741c0c582240b612110a40c14501002c616002951001d50350b2412110480c6030071401d420460000c1d1131810581006205a034095002e00011400d0006440a0406d00100c40d075001c206003006801e001c0e007186035801101e000100a021240410724040d0744070b04480c3d0500c1c0c120440c9550781421644034a100034850001c01d14540001440c0108090110300171000f2520b198019100307500c80300d01403043d03115103030b08030303200d90010044610078020542c12 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 293425323 1250 293424073 293424077
    0x206090607050a020a080106090c1e050306130e0a0b0c180f0d050a061b02070e0105090717040b040308130f020f0402041d0a0b10200c0301020a030906051303080103060c 74
    0x102c08590340000c05c00949074000d691903130342d190700401600c0030a02591078482c5540c1440d200316281d00c801c0c4021492001c000c1800d101d0000080740c0261140d00030b00d00441501d00d020000104610851a161544480c064546102c1c64002c02c0310b01c86054100c40d16000072069031150a40303880c0900000c0400c811041c0d5022425807680404144140204031480e403244400092040103445c4564800c01030300c122500311350280b0014015900031900310381c19514100c07a03103c020341e22103500b100c800341210002038070050076805101c01c1141c1005103500403446502d9401c211760b00c040008822490010014002d500b81d00d910001500b0022000b00d05058040d00140c5480d40391403c03001c91900d01d1040011344a0a1005c209080c0c40901c529603400717404a45104000805400c000e26041e04040941d81842d800403d0900005e4100422052520081e00a540703c099641c00034009113449502529028203010024100c0c1c00d1405641d001298035454400183e421342e00d800000300648000201 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 293426573 1250 293425323 293425333
    0x304150e06431a010b040e010b09130603031d01050f04030807080702090702071a07030f030e100f0b0103060b12040b0a060807320619091517010f03020609060705 71
    0x180c10007410b40c0311000980034024450745200b40c0401280b90b0201640b241c2d400044c00d00040c030140189114070350440c0c030326017050b0342c41e00c5c2c0c90f80000d000c5614281c10740b80d01a207040000410540c00c84400d06941600c0380d000c070030a0700c600005540610541d055810051005c00080c000200c401014040042c007982c1d0303190411580b039000c00d0030720109440d10340159026003420001b005814150b401c00d1112015014100001a80c0c003804400245032107030245612400f003200b0b68401080010141000904244504e4000700c1110b4001c000c403c1c80340b40041d00f0301d800412200200c00840b100480b1003414252030396110384480c8000f80000d01610001521038500042454040000c2405064900307d18900200d06450b00410312071903140aa01740d02a0084034510360383c44500752050b0340d0846404103500300b16079a086803800e03001d03040107402c691801600740d2565030ac010700350b01d00580035076100c0c4681d0705d41c1c0325494440c4403480000e5004208200404d12800e000c8040d0100318440c07404c42c1c1c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 293427823 1250 293426573 293426677
    0x70512070906080717010c021009030c05120408010c030b0a0b070c03050105040309061205060a1e0f080606011403090a0236040318080c0d11030304150e06 68
    0x250a59166034000f42d40365000c05404d201300341ca00d1007604021103220008000c880107490f006503d40f580342e0141003c0035036401c802414035004145001c0c106500c00700b07803115540701074402c9801d0b8200d800380070055031801500c802158080e1148022030324004024864841ca40070541c1c2e03c59021201c11100d090f0948000000110709003e41c501882c0f00303454070280380b41051001003ca4640b09140c2c0c62840c00c0600b44540c948070498442c0c140ca115002d4400307842110103200a248035107501c109400881840300040c5d045003c1a09401540242d0300c0d2202200c0441045840d400161540f0390660031107542d0100516103d40b40d8078402400400071030b400f50140388040045400c1c03501c110b50341241401004109580310100da0342e401600903000161504200e65640e6070f61011442c54000c1d085c03140340c2414012003000c1c0d014140710080803655215200e11031240d80c201d86503c0000443c1c10700003921144e07c0c06005840c2a0300c8001070b2950900181015100381c52071014413050300c05101c00c00b403 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 293429073 1250 293427823 293427839
    0x7051801151404060306150e063108300f07060b090103030804030e030f0a0b040c050306070c03020d0f0f030f0b1512010b1243030507020105040507051207 68
    0x6080100001c0d10001940f9151140ba10340741701c1d02c2c0070380004010081680f0f010590b9203c007900c151031032007455044003281e811600c0d040c000ac4400b940ca0b00380f501c40000a40e860000179040c90700c2c000028202c050213116102480f540030001c100105481d4140890809540e000002e89a0240641000314504001601140301e01d0070a030820780000c2c542e04200414950015605209688260300a00340118031520711521840fa04c203006064120420104050155100d0260040c020040542d01c0c0350134402005001c1c95005c2c0c800314094080e4131640e102e541d00441da0404511346076282d001803600da400c4c0072401801e10b2184003000d00e81c3c0d01c1e00792100b0b032962900301e00206a04052156101c003071441d140080c520590040060740c6082284c1c4d80001103a600381da4100d03500c609128040c0108410741c1200601024455045008501e5080f60440141001a048207802d84041096440f14041282030b20f10856010f4a540c2c00f000302003041d810110b1099218011101c1039a4949841e03010f6 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 293430323 1250 293429073 293429077
    0x8070b04050c0a150f0c0203070513020c0712140102070c170f010606030f0b09010305030d050c0c0d02010b090906040210081906151b0b0c090103090f060c02070518011514 75
    0x2144c3c4106a01c1a008a4010321001920202410107960500c01030780082c1e502d0340e00d4001c150048902900141034400e46406951000c615502518041038668490740c4a1150701e580a40b001d100000c080300d103046062086a603280e401120205241d400c0c800100030a411030300c0a940c0a2107201d8402500304801c0c4184400380c5000d03500803880030030000703592042e030304426421481012220300400000e100041103c8250790851808902661120b01220550251441e010304500614403041141c0394103610482520760211024000790300e8045e00159201000c845c0250006903c3d02ea60309014083e66030543e0203412888501c8819146c41d1501042c2c40c1d40781d000f602909110340b031000c5490341241541d40204c50f800c041c0e82110384c4d00d880c1d06401d8000540812402c000005500c40c160344250080c24034140c2100e402c4412801d00e280c060001c0968a08450060040d100040398904e02281c0710105050000303103c450907400c01844e0741600a004d14408140310f80d0307030100107881101d040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 293431573 1250 293430323 293430329
    0x17041709091f050316090b0604030b0c03100b03040201080417091818010b0307150519050c010c0503090d030506030a050a0f030207120c270617011808070b04050c0a 72
    0x1d03044031aa0490780005034540300076000301d44a9003024030500c1c00b04180d07007060000c903155160041000b007d4500882c02c03a121720740000e0000300e00401006501d1070b0540080d8010316448556140b0349a6601e40d0040078007065a00034002240e410104010541d5000b41c031600d9000441010f141c104031800084038001842c1003041c0c0c00000408001840400f8000b07448203c003000002d00413401c10000080e102ea55502607510710307440001002015510070001e03034002a03c11840016030414134540a07007070740c0080094900760340c200074159400754800d105803401000158010203d00044500c240c02034040113210030b40610801e80d1210101d481042200c900328045d400f80072085005040c02802d0988039002240d03c000b0700241d403000501e40030b81c0e410484040d40711790b1460342050381041084281c0040c00311011400c02801054016402e0b49228107062420000c00034180741c0d41c907501804105200241c50386405201150105070303e010002d41c0284658107854035046071200180214040b07030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 293432823 1250 293431573 293431591
    0xf1e020a0201020c100c02060f0c01021605240703022118150c09121c1206060804020a030b071116090c020a0b16050c010e0c010201050105011704170909 67
    0x100d0540d41c0501582c0182c240503071348018001c8040002030440c44501c2d2000780184400160411040d0840054880000244000751360314040d030700c5414062050030310203175168011003540440040c61700d10556041d642c0c40c0340042d0242e864001c00d070000d4200c0e070000c1440048520545031304020440869104a0b0342645c0080400c0d0482086450003410147d204009401003082c0010100c4403c203076484010222030000a01d0582c541d40307814000c070000c0003000700d001010a48a90340c3c0081d10000c80360b0141104001c0b1958803642203030010b0707041e07030701035005100040c0038004500c00d400100e511a0740d90400012031030008100e140f80c40e03000302114600244803407092000d03c1084c000c1c5104403034148020a0130a419484048014202600c0002170405038142287c40d903009030305403020440014020051994120000d64071107000164142c01941380c06c4c0007188941c05100f01808501d401041110705079166038545190498000c0800741d81d10090111070000e940361f503c0603106904007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 293434073 1250 293432823 293432833
    0x91c0c030b0903130905040201110604051e0d080103020622090915110d0c03110a030515090c16110909010f0e06090a0f150204030309080d021b010f1e02 67
    0x40c01c005184080160144169402c10801250054040020309080e140b45440c0010701c0c1d200c91006a86500081e140c0d90804e000b00002c001c01d0100200300200010f00c100d980f035403c014203804503500c0c3c2030880724500c0807038001d900502c00b5040c8000940108840c2030000c0921050702e40305000440031b0b82d030140080a40f503031140400c0102041c542c00d520320b00d0301410f0200c1c0e0040e184003c01405941445040a5035600005d6490b41c442d0b049581101030000765250340d81841c03000200544012910210702c445865800c06480c01e251034860b100b5841035490380c2c14061311440c3c032564420f00364030584030900c48400e03104a9654080c01640200440d800005484002d04000d8003030300c0b50380504050b15040141044013404010400c1c10300b250f80550304070a03100c82c078600308402310258120b0002080c400f00b004001c058000e0307614000d5030306810031500ba484070343d40708903551110f8907581f0350201c51740186030500b540103000c60803000c40713142407004030317a414568843e440b080704849420050340a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 293435323 1250 293434073 293434079
    0xc0601080c0402030105060f0d0b0a1508011e0501050f09091314060f061302070f08070b0c09061c0b040c03020a03150509040305030402030a14060103030e030102120a02091c0c 77
    0xc01c00160380300301000d660542c11580b6100000300f01c3c1c09150400c5100e10000151552510025401040d001030b0013440c0c418200c1d10351844020340d0001d02e130080041003002d0000701d11504180d684280c1c10000075a01e82d071050810b00112a0742e0004003003201008001e1200312410340e184100d25101d4804420400c10300f10a500b800c030103040c050480d1030301c0c641080003400a5007681e60f4110b40d2103030b0159100c21029001c00c500c00000e22502902900c041605101c920401510f0b500810015000e2800305d0305948806074158054440c0300b00e0954000cac0b00300544052803c146284000c100301c0c1240004070b80c9a10b00100c0d003514008604100003a50014290001c1d03600341c0f282c2103045850070b1414043d241000081141f41d80040d1020f4248a0040005002c650303017048108001580b005102e0040e1442e00d020a94500b028082140419400d81c45002c10b03050500c29504040700305240003086448241c5410b000750b00460440c0e070440d001030802c440300a0a111903c030618480c54034001031500d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 293436573 1250 293435323 293435339
    0x1090207020d0c1d1602060406150306020d0902032a0405040204180302150a0c020309040510330302070308060d11060a0e09100302130f0b04111b0c01020d110a0501020c0601 76
    0x134000c1070f600480c16030760300c282486603001038501d9200d94040c00020b0009503030082001900b00d550f00c000d00450000552007141503c40e0000c500c100d02c2501120040305001541620384920480c42e0070a150700006146520320345a0005600240007074030000b4400b0886920140c9006444420741c0540e006020420f94100c08081103035014031190f0701000b0211561074025105d1141562503441035403501d01040b40d440b002c210443c01440d2050301100007100680711600d0000200c000d06e0080d001c041c90b00380303241d4028000c036401c042c3c0c55039075040903540311403c00c078103061100c000751001d00c54100841d4403030b180d400003414a0f01c025218124003050020030000e202c0f400504012807020041d1040005886810304403400c090b400c10085607040c44000c4100040c00c3c0c449155901504065900d5081840302005003400d541c1644020548425a08840c1e0b0311003140e04102d0040e441a00c40f0740b100c2c0e10a03d03d400d44003c1c45010344454002c0307900c496023603030800105d03003450307400400041081c81 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 293437823 1250 293436573 293436629
    0x151602090109050c09040f1103280b0a09050403090b0f04030b010f0312080a0b040c090603150e0105150d0204030318090e0309040c020f06040c05120a0b01090207020d0c 74
    0xd0000424090f0345072500598400340150f10215024607142c04a002d044402c0b504491405022460810707240d03c0d160010f03400c002445030f4603145202c8603040e5005025100e0203103072a122405081c0c601500e01c1c1c010250000c050007401036040101e200004a100c0d0700000c01801148040c0680b6a166415401c2c50341c0d08481c180e100c0b9400f4000e8a008100081c030040083c1800d0f0f00b1428041101d40d1040c02e060080c100d0308054660181ca421007104005411201c01402c0e00c070680e4003040582410600800d81d1440b60040c1c02c00c81c080301004110500d0030049640101c406918560b003811036401582069801c960002c401061218440400d0240800e00e40002480c880d0300c240f000c1000c010f0f425841384550139106020700d80b0748440fa50b100b4020004004440c036514101d0f02c042c40c007402d20003071095140c0903081c41203840c0618415030100014000c40465003000c21034006910300362600000790310030719080780c1051211480401280f441c581500084c020803c000c1c00440901034080059 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 293439073 1250 293437823 293437829
    0x3050907051f0c0c0f0b1e07170f0409060305010911062d04080d0f1b030912030306080307120e011d1909060b0414060a021b1516020901 60
    0x3610141108110400b09441604024030641004404030819007840f41910308940c024003074590600400141c5d183c2404004c0010114018055a0320080060f178000107204100000e00754004e40c001142d00000c0075001005250550b04949140079a60302d90b450507621250300984d00759540c0c485240c04e012189841001901083300d10307034030f41a001003420304060302805143d648448002c1d0b82d51140b5407141c00f11805007000004491007441c0300240107061044820500300003a4030305442c003101181d070702c6204942c40d9042d02c449221909000200003510400841542050313150310000903d400240000c200160043d03e90802c4c90b0071141020300030710106c11703909040040000603000c9104692504607040345003110311260103400a00144030b0300358240c0002c410b692505400280d00400c0720014070407255005040b041403020391003084000d02481a0340c1c005a0003504080c084040804030300f80030404010410710610030a1807540b103036900040050525056108000802c2d8a4055001401 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 293440323 1250 293439073 293439079
    0x50d1e0c090605040b071a040602090a15021002090d0804080a1109010b03180a02130b09131109040312050109021210061b03020a05060702160902030106020c1509040504030305090705 80
    0x41c03910741680100144a10700c14000b242001180703034810005011914140c095210050400a04103030500383c0c001d602c5014060720030002548009003a20382c0001201e0004902d0b0040c06440008800000c003a6000400e402d6004840031113050000b00580e02030000307026000b00601c12070006291912005008000b92440340c043d05004002221440d0200d030351140e4440f40401c001401000c0c1103181c03100d2040c000354003100003400600c500f0341d140d0010304062400c480f03840d01ca842d070746400c010082c0c0c0030b44050180350600054a80c18107150f00c2c910b42082c440c3c40c003604006c40d050340d00411160280c010741c1c0c0712a00043c0d0300c3c0030042c442c0c60050300001d8421902c02c0d0a072030014050310301651205503511514000340310500385402400000b01044e041f4080e100a442c0c1078200a4441082c01d0004d0011855010701094210181c0b00340d9040e0350154009158000c03c1c1d0301001400740c14015541c5041104000d1805503845a0242e503001e14886d4a001c40c950a00d007429606091041d042240 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 293441573 1250 293440323 293440337
    0xb010b0c06070801080a20180a061703070210180303090603110c0c10030f05040f0b070203030907060813050d111c090b0c01180803040c0f0b03070f050d1e0c 69
    0x42001c00101b841d003441070313021460078a15052400a4404141c01c2c42840340d001001145000c418083c141d1f240d4840e05403e102040010303201c0e04844528406040c40c204103600c01c0c448900141000c2041490b548550300381081c64001e00da101030340e0b0a100746c2003180010f966071020080c0b50307018003610705000441040907041100318050199225000b41c038aa2185540d00c600790081f078041d6010b892041c801c050144014585400c1035200c40c44c940710b046400422060000f800c00748084141c80c01140c40b507003d050920318100080305d0010001d095600c03908100320804000460030400061403021585840522a0840c9032079130424500005000a44200c0c0d00c002141c0c03a4859070110a0322840c00c042905e4001c600d003c240140005d1070a01920505c105510092100c41d2000c0c41c07180d403054200072030711511022548400c04041c801c003210201c0610101d101c0c20b0159072080105041403410074141480503000300151002c800d0360721600c15800c242450107100c0350103503039100c0e242e505040f4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 293442823 1250 293441573 293441579
    0x70201020307061a040e0303012603030712140906060102060708390c150604060e040602070f02091003030908030408060403141c061404050105060d0c09030b010b0c06070801 76
    0x41d48a201d5404000d08081d9541c00d5441c6401d0321802c581008030000c0c1003008101e0840c0d0005580360300a0060100301000c11500310b0381d6240128000d10305001000155040d925400001d440d011180d150804000762181c41070010300d001001858407941b0780500402580c105000068107020000d042c00c01000504810485401c01401000c5030051030303c02030a46810038000544c041d000703000d884000d2200c0001c0c0e201740e80311000586080c0102035401c2c2c1c81050b140c81e410801114140e2160b064401810340004020413080d601a000c00c1b40104055200d4000ba0360019600c4102200c070001011031950b010300c24941c1c040d0250000e00034880c002e500e0141041d01040e0303600d00040004003041030120307070030b00d071100b01c04103845204030b01030440352203030780049820000b4140f02e00407440715801000c0e10030302915160041174100c1c0d00240c0458600041d040c00000a422180041401d0280c540c0000002a1040c581030f4001c10038501810f4550010b00d6042d801c117030001e0643c50802510f00014 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 293444073 1250 293442823 293442827
    0x50406232709150f060d06060203030609070e1c0f020d12020c06130b0f0c01050f0123090406020c120d05100e04050d0c0c0b180406060f210603050a03030b01080c070201 74
    0x6110f0820f012110003c40c04016400100c1c00c0c80340b0043c0020403420048001002c035000400395002e010b0480d2110003643d140c0008481d8400b00c00c081c15401251a01e81c688d00254401d021365249001f90050000b110080d00800c0119120b0201184c205005145143d40d8550501005200e04804c40d441c41c60300b81c0c41c55888059506602500031900f8000940a01a40400d42140c0011640c280244240e00e07111060303194101e02403245008151100880503110aa0801000505c0c04020b040d80e40036181c40d12074800a401200d0f210500e0705c10504a803014581c068003078402c03214000c0340402c091a02340010810121140c2c0598002c003589024000042c0c1d01081101c0c01c1d101c5440d03c0380010700141410944e00c503155002240300c001c0018181101280c45c01924080b4006030380c04d1210075540c0f4412035940001c0503001000660005505584692910f050f01101070492400b003800c940346e031905810051200d10071002b0036034440100b015944c211200540c098021198682415455000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 293445323 1250 293444073 293444101
    0x903030801052403060301022710030204060f0c050c061606180215090d020d11010f050315011206050a0f0305010c0509010c030509040e03030702010207050c10050406232709 76
    0x880f540740c0c0e03400b0000901c0ca440035416120852043d0124914aa03464603500180e1004412003600aa403000c50130003185010b03008841c12120306985d01c04c41d11480c0d00088829500c040401c134bc05010f040c01202d034583d600300107803401c150060700e2500110302c940f41410071210060f0094040807030002c0d940b80540c2e00e124030382c100c500440503415030310640e400000d01d1031180014000d600c02d82c91010807050080310589840003040a8031074000d0030203100420f455601046903c0701c0c1c440c600030441507032944214019909415864004981c0a450718001000d04005410004039045624230400900000340556a0890043e0900503d003a83e4080001c01000d000c990142c24801e002840407181e4072150302400d040e045c40030541e510382c10501c4000740070354440e040c107541c01d106100400341d50f841c040510000100b07107a16034034034143c81d046060f1000e502d441c68882d4407007906101c07100e00616400007400202e400f80b000d4581c807000300c1c240c06c01800002da00103005072001410000440d80b8040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 293446573 1250 293445323 293445379
    0x3062e08060f071107030f0203061e131b0b090a0e01031505130c1401020d020f030a23030c04030b0708040c091a15040303020105060312040e07030605030d090303080105 74
    0x110101169a4030041074800c03d250041311051441806800024414000d4840003624821015581180c59014440d16440c024020403081380c074844001c981c1c070300400d40d20b01400910915000c00d03607900429810300061640d9104600e00e80d400030324240b641c03605045100203400150315001c869411500c0741070210015202c5140515901c1c030100f4414803001014030703071045e40701d01a40b2045444214134403e5011010f40c907800b503c0341580c200c407528004204480c50030481c0005604050b51043c0c100c0f5034004a444200307500c65111500014410a140154410301ba82d040700c5641e0752035460600b02900c030050402d01044900c1e014403001030f800080303400c01ca03401c425000c10041003241007084907200d62000e40c4d81c003400700001071080d00c00c010f0103081128029002003265a442d2400c1c16242d4a6501d01c514985404000030700c40c408510211070f0b00305001c2d180000300585c40382e010034a0500781d00b00d91404100390210070010141c0c00040180501025500c0c03066400c0100b0318032400c405901 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 293447823 1250 293446573 293446591
    0x41226040915090906240e0a050c09030a21110d110705130504020f0a05010206181204170c0f06070206031f030f050d030b010e09070e03062e0806 64
    0x80b10706018000000700310001d44204441002680b6042c6016402010b0b0391403803c040d0030000e42207101da55003406140d82281e880c030660305040c1d580c00e44503000420b00241030100550044c040540d59880401400058074415600c5201e200511500540e040e61660301110400c81650010748841c01d0200d6100c100c0d584905141d022902170907451350810400c1d400c11500007001140130035940c106500f100d80107500a84040700c187c04008141300030002c41780100d5016a006401090903004419100380020340d0030010b5609c0d00940b0701c440703803880d03100fa4007802821840a1014190000501c800085100d040b04c00c0746100001d0000302e42240518a0040d20807840400028400f59107180000d10101c4054009480b00341c907403405007c100100c0f0340c180c074144665000450854024032400f510782a0517140c600e0b01d41c25401c1040394541e002803402c810450800d110803400d441c10000c1c180180302211000107d2440140541411406031800a201000d40c25042141c8040800c820383c11400b01 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 293449073 1250 293447823 293447831
    0x403110112111303061802031e010603020604060e040f0e070902130519061115040b0702010905100b01021b0a3605010617040b06010807140412260409 66
    0x20540308070081407102003000e01003200184000e008081c03182c040066901c035007070801603030b00d01003160a403da0910310300a4055000303821514a56046111581003012941d001140042e107a6000c02c40750b421039800701e00821141c8002405601c1c050180352502c0c3e2061404105a20b86003000540d2020903125100c121540040ea2140c4084410200e60241c61f002d00700221040c4480500103079070f02e00388107680009485c0c1c80d20269049011411554904195404020707e8035262500060840c005c0c200505540d607030400c0b500045c505002440348441c0c00500010184a0000003a04107404131604c2708101089060400303066907100003400507600c441d00d142c0d01d5410072a214014042c00308007034101c4940032141600240c012900882e06039a200da81e2400051032050351503a14010585000700260023000000e100d81d40b02e40265a40305202d0300d000804048044161103059005800000c9040d021070901d800b841100c1c5682021100074001c3e402401d041001101481e0160307010312880c1c141c035 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 293450323 1250 293449073 293449097
    0x1030c021608060601020f030f1c0605042c0109030206040b070e0603010b04031703040312241409070203160f020112060e07112a1302040b031b04031101 67
    0x8200444a121a106910007050503168a90b40da80c80c441107611500500c40d40045e41d0502d8000b00035212068031069030a410200d1000300701091444541c3c981c40c10559411000403036130b07580c0c01a10460500b00342d0181d001c0321600a40c18000315076840c1210301d81e0603e0001d400003640019599030082d00240440380c4d903203510342e04460301000806201e522040c007200105491000c20b0041c000c5a00c514a0780b40e0402e00f4603580da440d80800c80d40a00450020710385100c0c40c4001c1c4d0000ca10b468180080f40a50119503209200d42614640150103480340403c108420340c01c004251580014050001f5401c00c50662015080500c907528010000c3e4040c03001c18085902030b4000d03400c110b40400c801d1040c26110300d440700c2031030411694580010040f4081000c0d00d04081f90351000904440175442000c6d00d03401e104034250001003661900110115151403c101507440070f440601402c2c0c3c0e01560700d0411107001c240e24a1206841e5040c460100810000640c001144c140d281400b82016940d400ea = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 293451573 1250 293450323 293450327
    0x2071202060f04030b150306040f061d010f0f06080303040c05120f06130204050711030307050f0d02130519080a030f20070510141602060403140102131e030201030c 72
    0x2402c4100021040007240100401200d00c424a1003800342d4501036032403040e00340805548c1c2c18103550107000d0400b050b03e0304010481c581c002134909802c1a4220b021020a8407802e800c46501000c0c4804c0ca5540c2e00440c04002d10601400000301617a20046003941001c1d1500070700b03a0007502c1801e01c00c184003d002d040d0104180501303508080ba24054800a1030320008800d80c1d00300047e0128400d0b0f00d444009640315004102d80d60358035610b14000e50139540d40c060155001d51201d008105031007002d01c040504942140000c0c1080c500300081c00c00a90b13f41018030400d441a000fa52050004844e02448000300000c0c01c81c0340190540380040a031180f1039001d640c16894072010a29000300070002140000c030014084040f500d05803001c00300f890f40117008598060303409480d6400c900c010402100c07402000c100c8183c0441c0020407840c941562030f0744040e480000b504090640d650041410b010551102c484000200088071003441c0b000552207010b00072a0341404024181540c48c0414181c0038 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 293452823 1250 293451573 293451577
    0x1608060303043320010e15070207120f03020c09130f030905060316020705060f031f0b03040302060702010f1407030c1206170606060703090308030603030d06090e0106060f0207120206 80
    0x401e0001c4141c00318007803c2d00810584d0b200c141d08850304400000d80114076070504c44c0e4890403268002074103c0000311146c1c14241940a07101400314842c00c4e401040300061022000d04091203141444041140c81c0b50103402c2010014085104100440803c480f11141000e180200c81e4440d40c9003050050500e4283e407104041d410003030308240d0200800401d003045440c0240d1155046c1c084503100b698800c1008403a00c50455000b00301542480441c1c0120642c8030040c4030085400280c5000302d442e1140160300d030300129400e40c01648020103210706a42c085c85400d01841010b40103001702e900d0701d5210840131f174016244600b019510722001d000188240b8403400c041c0c04405080c04030361b42d1052035500d411a090b0f2a00068081e0300c0200368907141580c21501110340c107440e1880100d2450b00d030054035410003498542c0502003041a055071001da07108800c050440d01c03030005089550b08808500b1141140c002c0c10600003044120741e1904e400040c1c0004441800308440c0c0c0040c0d035803021403e14 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 293454073 1250 293452823 293452889
    0x80109020d1407020c150301050a0e06030a1205030708070c0c0303050c010b130e10200708071b031406010b03060d03020a0f0b04140105011202010c141203160806030304 74
    0x491a0b4018000025070110f40136508800071194814240d0900040405521085c4600c42c0c0c0400b5010040000d210b5031012954070107401000d4415480c2d070798079181808807808009000240c0004100030341c00f504030941c42d80000b502c2c0391845801e08145e80308820769049010140600802041110f010102500f0000c2c01401c0a00301410302007400030000060703c0e4490740750030360380150880024038014503c80c03100740d0034400060041200e12815248441d0f07000010582d0030030801c0014602050b0120035443c0d0b0000c000456050061450806829143d806400c001d480d03080300c4010410711079010181d17a00005c045940041101680c074080c2d1410b020b45400a011220b840d5000e400e11010658507407081c2d008100c0418500c00c0c1102e83c90898a0074020758090b01504041d40c409544910b007503441e230034456400c0a526109001340e0629100c240407420400700d50000800c0f1640480f0040d1b1325480ca0203042000381c40c182900065282d001c1c034001c02da00102c825a4105900c070440702070042c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 293455323 1250 293454073 293454101
    0xf030a0c080919030605090c0924130e0a0209090a0b060405060604080714040606091508061813030e01094211210913020408010c03230601080109020d 66
    0x3c80b0b03a40d280801c050f00007203800031030034058030040b00301e54146000800d118042c9040b40309188200b0407460a01111059003854101c035000c15155100d220702d06c2062411071130440103008040243c410404610801000b000a5400600b800c00000320200e009540041c4211804500c540c1d8050100707029000b203911070b45040c030810600164911243d02c6520780064103450921070940ca0b11410b40e01da134910f204001d00e003100c4010304202544220034084d0052801841e030800e849601c1c0320106940c00070341d09114032103216a824410107801c1070744071130410000c1c00e0559215140484524202706005070300e2030b150780560343e0745415280d00c40e00240c04601030400034041d8001c40000030440880c0150f6280c2c103228030341c00161f154030700c0f030310380714804a41c121001c0c03030003c0135414000403071780005088800741e03000d100215800b5030a011780348d810b010541d400610310345101028200d068200c4c0c400b0124520060174401d42d640d000406a06481141c4c40c09a60382030b0f030500c1240284012500081 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 293456573 1250 293455323 293455369
    0x4050c090d0c090507050301030312020a02160801020a03150b09220905070e0705070b27030406170a02030c03010b03070e180601080703151e0f030b0105030f030a0c0809 74
    0x10405802c0c0c1e9034099070f8104504210650314a9000d44c4c5620003804042c000c110750f804520342c0d980a83e00202019041d40c816910000401c0d20206070031131168000c1000c0d42d401040e8096030503450700c20710351581461491201103614011180040e882803030b001c240a2011070302001d400d40601001c8070f0410b141c00c0b00412000314541000ae8440b4040d005031428964400c02165540c0d00c100c0c19104100e13001154068207440310788442188410303070720504014000f103850107800d18038144098802030800d5110015100000c4001842c0003c0060030303e038090744184144110106400c055905585945004507034948503010141c62025141c040b0b15403200c01c182c403860301c2c4010185083d00482003a03e964a243e01e4414082d0241d60168540182070681c02004001d00c0e0006e4840c041e154098071808003229454030310f07403501c110094005490580a540042000b8241040740d01c0c4221502006503050104180b401803c6203d140c1c0094081080030420703036410307510040a14844192111000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 293457823 1250 293456573 293456599
    0x18110f220903080a091e050f10060f0504090b0a050c0d0203070905130b100f03091406040201020d0513030f0c211509170a02010219020705190b03040204050c09 70
    0x9025048081c412000160840c010070f090302603034001c024500341c0c0b0640619560303042c5040d40321304200d002d0094419110b8540100085d07002800903198400c400003002c107216041010050707520a0503401103005506d0881c1001c00b00d0700e1014400d4200c04c8000000c04e0030307246c29003032005a001d003104401c600d40c800418412499003020946003280d80a494550190090b441540101d802204126410518090b01603070060310400f00c00b00d61550340e0800060031081500c40058181c8061400003180c1d21003c1800b056680400ca030500d400064a0075038600b014802c10400030000500c00100390450f2000b220042150010740c4101030604d4030036140381c041d0540da05030b0913050140025520b1601c85a88007454100502801e1541d03904000e003c04040440ea81e900c0e040c1d4802445141103550034028043c0d803403a1010810b04c803c40e294000c0000a04000030000d401184000e0032800c1b0481940c01c0004401710f500783c0f54000e404907030014031503842064559943c4102c2119503488402000344e2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 293459073 1250 293457823 293457889
    0x60c0e060d050601021009120e01030f020430053003090102072616290709060203040f05060c0a0b01090905060604050c0f13051306030618110f 63
    0x15101c2c80b400da01b06d85032031010709409821a8001c03c40500011040c0315440e50761409941001c0c0181d03818074001075404001180182281c02c03503000071140d50700010f01c450f0038003440000452100382900304200800440d9079410b90b280105d640b48048440c41c0c114020103002d000b0091a000403d03e03500c00d94030f18219000718001c0d4028141102d2031412104201180036515040c4d03610700ea075289c00303507162440304902920340c51109001181c2c002c510350342141c4d044800c0c20600380601410801c440c1c042c2403040c0064041e0102d40c0000c0110750083c041000303a008c46000c290100c5809840c1c860356000c50410346418044c0101b40980141c0c00c460000440400c00d034400080c1500800944042e901c0f0390b42040165007040d41c4e103074408007091040030364006086005000031100594698005660b039001300304118025038402818070b40e00c041c01c00034061140201d44210004403217101e6420903581c3c0b480070709200315200e54001d02006010304840c0d180c0002201c8420102104592008584209 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 293460323 1250 293459073 293459081
    0x15030f042f01021b0108190605030a060207021c030815120111040f09052707030614180a051f060b071103070501020601060c0b0c0405060a02070302010306080a0203060103060c0e060d 80
    0x20707960043c850101410b03000400d01e003604030203103c1690343c038189032a0f449050f0040300fa00b8485600c030a55440002540e0341d020000b0180c26803180d1000358070303100b49004120900e4114203001c2e40c410000518000029401400380303902981c0040c5400050301d2000205824910610001d21a0761900000201104150003c0c2c07007140c0c8402d58072520380c0e8440c03c0c41d01c151842611180c03038146203000082820b403000c42600e014a08503000321000d407581c0c0d072140c0c0c05944010100802c000340e582e05014200100c5005910313058100b8004101019541e696156212203414060244001c80541184070310000d801030001866003056454881c245030400018242045003480c0c400c1c40fa40c02e0000d43c0d94000310b41c00c0d04962594640301e045441986404c400d4281c010214207124204110104095482001400540700a0307801060100d04500c005003c60341c454114200355407200590310011303a4000f0381c141c156a440200814195800d03c400d41d0b0400c072103009198402c0e40410281681141d0ba40 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 293461573 1250 293460323 293460413
    0x603020f221419051c0c0e100e06010503070e0316031401051e01030f0203010b0a0e0a0509420112050105060109060509270c1815030f04 60
    0x1940100400322400c2100f86040024060050740d0480c0f002c000500d0408245200599168002c089240160707032600c0700c0812581140020002d00414803a01242d0103415402600d00306803003003100c1c100980081c0203800004c181c00100030041c2d00c07003c0103031018010307110b81210b04807040500c00e84038600b104400b50000031100f610b40ca850002000c0035544541a206c140c0980d8a44440e81d0941d110340c10b8420490005036090f40d20780304940c0c003a444442d50000181842001c114403420322100a1040e502e024218090f550321482d41c0c6010a0340c1080c01400c204030b4040030303022160302105000746400c0e0103a80450740c45815800014550314501070700030010302c030300020010b541d2078000641b2655079502031900010340901c03080099060007080d0030091004000031400c804114560040340920071202185000c401141051020384500d10030780d50300d20116100f82c1c824a404407100c400307020041c1481d10340c00e40e00d400b042c1071000783ca961142035100401d8021180c191100880c09a0100f24 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 293462823 1250 293461573 293461589
    0x150c02091509040803040606030503040e0115090803040902131203020309190e0a02030a0b10030b03070902030c0304020405270717061e06061303150507090f0603020f22 74
    0x100010020403000142540c0070704014100045600e964490030801e8100030421207000760303078000102c0030400800c081e0009004807002a800fa46c1800e0a8001e5990b60300a0507060141c0b00b401440706180100995082e03c821060060f2940401e404001000381030354401c070f1007140c0541c1d10344189503000c00103001e000c3c0151007290a206035924040d00b29491440b5521080750840085110801d951300110342100d119400850110003220000380c00f0340c1078244400101e503480d10a022913080920556005060030f4400f103041d4038021248507402d20004000130300c21507403600003c000c1e8001210398246284400c1d4032a002c0c000681c02e81c0c0d0760f00e8444c064000740901404001c007581100242c0c41e84074403500c0d400d0811490001c110000040d40c060716041d4465000d0200829040c0c440446000550194614400b4409505207880845130040c1c695410400402c4050188014002c10442110840c0c0350050b6200d40ca00d0381c4000c2d5000d000f0101d086041c49521b981103500c030b2030020724141c034420 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 293464073 1250 293462823 293462839
    0x30403030e1e090a02190903150e060c090613030c05041103040f0f1115030f070804050717030706090f0204050901051611030d021902010f15120c150c02 67
    0x140c2040090032032002082e0044200c8541007040703040843d0a2078000c0c94200015082c50340d4078441170882c010740d0b09100001540720004000b0f01500760130540c00001c210004010030141c400700c49441c1d11000304001050440000da0224907195102225401030705540404201512482d0008c000d80c0c152207640c3c4201d04101545040c0040002203e00035035000f80606082d10913603031082c0022030200019600d82c0000e40031040d1586a03a035208010035001040729070f0f6454808503914058030060019403c00c0001c000f00000540300040b40002d4440c01000a50020079810160b0300d5071289440c0102140d0405207041e0401900c1540c40c04d07103034800c030703400c3c0400c0c2c1d41c070034007182210b40171680c136000101c2c4040303880c01c3d6601643e10b160301281c1100a5916003034810364290180e030f2102540c446034022520070341e48403a5080c07113001c0c1d80104980041c03220341c0c044840d280401045028580d400f042220441d020424014080002800d1100b01c10141102644002d002800b070040c0a82c01036000d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 293465323 1250 293464073 293464097
    0x213050d0507030b180f190f0c031211160e0105150f04121416090e030c030309061b0909150d0203070303090f1a030f04030c05071412010507120f0b0405040503040303 73
    0x408100c480c0b4078400742e04460030ba00b03c103846407600b52080e401c045e030349c03030f41c03110710200100ea40c40410260000d46600c4620400843c161840d26050384584442e82c82848a402408114200a007441c11540102c0d51070402c909608424040c9121340800900c1c01c1c50009000194904500c011000160140c01d042c1c0441c07040c1c2020765182d880a186076804264003a4061107116103039409080541850f504a90918001d183c0c0c503451603000751388100c00c40d4070580810451561500302c0b001010004880541000951004181a004047d003a01e00d2000c204183d50015215141d00340381d0342e50010201c1e0801684e038200a000402c4d20300070300b10050440e00b400300d02c4c601100303511680c58126444c0c03580f03983d40d00c074103000c076102d8041e004400704560b0b00d0741c50340400c804000943c0549802e20321075228800f88010450400c88480700028a079041004002c882600b011050034511058840407034400b024048040c000c100c1072a4080e4401e162409200c284440040908280d0784243c840d0066021 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 293466573 1250 293465323 293465353
    0x211509070201020a0f03020c0c03060a0b120d0e0d14060703051005060a0230040308090a0512060604090203031c06051e0a0603020d06180c02100213050d0507030b18 72
    0x201311480400403d00c0c20317101e44040d600c60b9004099040464095031843c1240c180040e0402030282c503003285094075a403030084d180c60007003840c02014110130010450190440c0700030781055285803009120f5030f559005c400a1003030204e5031609412402054513118500100c0181c001c0405071402e4130a40074080d4081010f0a0070002c03180b90030203580003042680d910020070071180043c4034404008003500540c1075061207560b00500040d6104011181c0c544e682c1304180815824203610151242c007801e010401440d10114200350044400d503404119000d15002091640c46140c400c1d640d80000880b041042d240b41c0e90150741a035604840c00304411031005804030600000300394485e4000f11a0f0010800140254001c08403ea41e41c040401d0302551508821444140e510a500429480310781e080d03901c0387d05000c0c00305e212000d01c104504000d0403040c4203034109a06d0080a00890303041d4006024440e007003000324015a80b115074040580390403080000d60341ca2494051425110b0798684202641c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 293467823 1250 293466573 293466577
    0x80a0f02010c02031c0605060c1b030106030c17120f0c0c030307030f0f0e0d110108060a080c2809090b010e040305030609040609140d090e040f030521150907020102 72
    0x2c1c1980210700f03142c078259038104881088680c1d40c49881c0d541800141d69100c2c0009800030501e5603010f0000b44075080c85098007422801040c0340301e649401c000f4400160001c01c11016541410508503802d140051030034608411804803948903800801d4400307264034000001c00701034a0706001e4440b02000d01c802d01d5924010154020b02140d050340059180c50320410003594040614907083c04030340d40c054003086400c100e100060307800c1814400411a1540c00420054000b50150343e9414ada070f151124136901c0300030107800079115100c141e12400400040c0301d69000310200c0c2c00e081c0510700d0354441c1880000c0c07401c030360101e40201890b40005450300c0c014007400e01c0f0b103400d40c94062550b0740d1001008000d00e802041100d6a56482120034085400c1c5540301103a4a01078009095060062201078903c00c040e603c841d81804040c41004001504801c261105c10352508007580c907510304020944164000c0400d00c40048858010000c50215003c20b581c13a04030140c4501c2115180d0310401c900341c4c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 293469073 1250 293467823 293467841
    0xe07060503040b0c0c070f06050d0b1c02010305060f130e01051305060403140d0e250810050a0e060c030406110a0e01080601091502060105030d030606140322080a0f0201 74
    0x543c480400144c00850010700900140c6680400d85600c13540700d100c4100c102c501508410f001800c003040140e043c01c1c452103458000c000481d4a040c7c0d0b120302c44d0011602c03070a4010b00034109525031011548903103035050700c2d000b5810000e052482100b91741c507202c40140082a64519590309040104402d03405840700310f40b40e103802c20050040b95550340c8081e40c07442501c030742c80701c0b208108004c100c610011512030054011003e402512a000030030008501c0e010043ea0306040d24001c02c0c0c4100202d0754001103000003101802030105541d03644c603503050018288481290300300d000c0ca804010440e4552001144030303034422001040a03141941c0390a20305d000b001c0d45c00b0f01240584003009103540c0600c580d554088014500b08a0b0340d603c85803140e01c031542110300f15002da4002d800501c200d14092202c3c0b0100e805a02d0100b00481c500b000041901102207011950ba10780000469041881c2034440c652050103211010b00c08102d5183c8811b8a03485003c900000034180c5855000161041c0150703052 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 293470323 1250 293469073 293469083
    0x306060d020f09040c020d0f09050a06120204030203030403050f07140d03030509160f0e01080109080f0309250e100302030c040e0a050d0924050d0902220e0706050304 73
    0x5000501240c24000d40c0324504810000d8414071040603203a40c0c0d80034010900c5180da01604640c0c2844a018000c09081032200081c020704035421f110ba5210b0180d07200c101c40040c41c000011180000088001380f00d44d40000e505400005404010b02c000042d010701d039880c034901107422141e0b0f9180c1c080c4e241d00b04010f00580c000320f0542641d001c02c0c8240c0107182c10401c004250ba400920013104200383c416070344e0001144c0d06401104121070b2030740304845030040121000a1060b50070b01da6890700648207032149104e0680e03000c00480c041c883e003000140d5644230181141142807213114005044152103201d0416008040c1000900c058200504d6004503607001e0020080c00d1303042e40401000c0c0980003403140c000c1c41542d1001010030410408942c01e40915110040340038202105010182e030444001002c0c0800e16020b403400300e500c10111130b1040c41101d0001610345240c070000d411144082c00f558401d10380124181d0f1070b0005a030014544802c06012030300c428ad950002600d03903010840740540 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 293471573 1250 293470323 293470327
    0x6070302071e05010e010c39080a080d051e070302091f140d0e010216020108090a0506040f02041e270b04140c03060109020d051003150f1b050c0c06030606 68
    0x3c03c1d5000f4487c002c0b000b0b210b11402c010f0760304980c414400c003c030b21000400c0700d1031090401c2c1245020000800002e89008030107005088030a1f01c880a02d413156a4048041c650360f40001003603c0940600d249028007180c4594085062081c0020040d4000802c02032007020341001e81c400321503113840701400f12034054940c03100d1316000081c0544035411500e0715031041502da080502c00c4000c00c7c03000b0b05401e0100d5121007100c54580c0001032131500020b104007100e5201c203182c400810b02c002803050784254062126125038040d840450040c00701802c1441c0140c1d51032000c60190034480d0400c0c00541c4a070404107644d164030451041441002c03940203442d2030180b5001c1004250315100d40390b102c2058004031002d950301e003404245404401d910007800182c1c0801c21020003492809415008908010180052030071504c501100c1241c1d03805c0c0c6c00700c00380c0c0d605d80410a081d242d04950f0602c4a804008280c00d4003c00c00600076a0100f0b00b421040c3c05408803420f81494140103482c01060060f050354 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 293472823 1250 293471573 293471597
    0x3020405010e28021b07080c0405130f020d0f05060403080f011d1509010b040f0503030a1d0d120509090a0e06010501211104140405010b180f06070302071e0501 70
    0x26043c440240d80c400b15400b000b40d08500c0d64080d8003030443c41d10000040c84900d14001000f810704c589048410f01c51801d01c002e1201c0300c074040c0160380c1720750f800506100600c02544001050300c00c4054005012800e088881e50910402140181c4a14000c1c0c82c1c4d900e482d40c5100c4080005a424019280303080401300c0d506c49440d07450304ca0260f20200000c051a002c0c64180d000680c41c4000341e03c80b4021003400681400030355000d244110092100b900110f0606030040742c05041000c0e40c0342076510710180f002d0030b24041e44d034000c0c522074016040a242c0704480c8094500070260340c080c01c03031507006039110b90100303017030700b43d0b40c8207191000709a880036241d9642420011541c6035441e285410b020812018800c40100f80c07445028060f4030002003480da121318068024210b94146580140301c4e80c5400c00400044511034100c0b4188000700032520303449050300300002d5007001800e5119400c07030030205420040580006584d801d0341c2c143c1c4400d0320140892504401380d2041c0b8000c060000740c0d42d40c084 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 293474073 1250 293472823 293472871
    0x302010e130f15081015090e071a0a0906020c0306071409040603210503100b070318080a0215130303050306030f1207020123430c0503160b09010c140703020405010e 72
    0xc1c20b0140014049c0d801080c0d507074801504a051007140342001c50400109641d0841d00161104010001c0340080c0441c01001c400082d00e0718001405035003230005924807190703513076440021104020401401000180e0b12414150912130780b40d4120040f9444034041841c4440c003070000d4a108105414001c040c9500300f54a002c580c2d00b0000c0110240800c042401c00e15410307542212000c1d04070100200058019030040001d54035152890400600003008000b06c2c08064034601000d4030b405043c503554944680c00032a161505000c40c80440d805440711440c081074424004110b00b5000366074000d8400488040d2030307000443e2160603620024100030f120704020326603116024000c0c10100712a092100850210060340703800b0858404010024000000c1064000114000e41400e0303009007010894030311544500c030901e001e41d41c02c9050104044100da80304524022000d540f180035082913180c0e02d00704c0d035075541d0a40400c9200d10b00f80800411201c448520140c0701d844c0e142148502d924084d042 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 293475323 1250 293474073 293474081
    0x50d0b0a0f0f231b0708070503210906160e0120010612060f051312030207170304060606110d030e0a1b080705100e0607050f06010b120c040302010e130f1508101509 72
    0x1023243d0351300050100c1d400d4401c0c44d505083c860759010b2004611803400c000d5080c10b00c84014403004080030f546907000446903018a802d081d240003802d00c00c0c0c1c10700e40d2002482d03840d888858054050344c02c240000c035090303031171968085240f80316030401d00a5080c08442d0900b5500100d41c07010399000d05801841c0482e15030340346c2200107559400e00610305112a11039440704045032000a141150000038042000202e00c2004000c040518100411102d000d1a43d0741320b140781e042c01f80c20940c859a1407101841d0511461400d01c1c0d00c400b8092a080d450000b003c1c0481513031140c0340150041004c0059182031841403408001030541d070b0307400328010440800c0500c1c1c100c40410768a47c420450941c403108030070004039001c4c14000f40410b89820140c1c0703c10380000d40090098039a004103210410050743c000040401800017155003c1d80086040c40c240c00904000222918203800c00000b906035491040d0281b0039509000c05850480c4c01c2d00410a0a41d0907050b08040503068030302c801c000c030803d10b40c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 293476573 1250 293475323 293475337
    0x17011a1f050d0207030305010303180f1401051b0106081e0c010818060702010f1a0d0828181d040209090f010e0106050a050d0b0a0f0f231b0708 63
    0x91071424941964407201c01c0340c0012030103c0109540304014018980c20401c1c04040065503501a03034000e0420800c09010f103600d00c240c4a010284500da0078060380180b05940c00303121006100990000d41c485114041d100038030900000780100b0410318049074281c822600400c00000040c402d82240c5001120581c100070302d81980302c44030254120b064141481110b005100c180d0000c41d549551200703100440320b10b903454a400601c614000000b42c0c071807410a80e00b8581003481a9110104114105070385103180c554510104011480c290340c481c0c006441301041c1c0c1c41451401045c58542254000c28404008042ca01120a82c00500141f13006040140d00440a400782c4643c0302c4001c1d083c3c7d007915622070408110740d44904092045090064104000f0402140d5065007050152605981400060085c401054643c0000c0051000c0c0c0c2c0c01607000c1100c42e800410031108120340541d640c211a1a1680c4480e00d15004503004010342041d12000172a125030702454040140d5443c611548045 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 293477823 1250 293476573 293476577
    0x405010c0819080103200109030b07090e040b04050607030204080a23120702040b0907050f07050a12080f071103090d06230406060806100302091009020417011a1f 71
    0x1228010582001070402c0b040301d095290b9100c1941145800c103884003d44011002c81c0514986c4581560ba04c06180c1e011203400000b1a01940c5030701c10100d44902450b0000085040940e00307000810602c030548600c590301500c2134030710315260607204030b041c0d201741c2c420201030b90301501c80741e00450b0b80050380040358920080f15012042d00c26040c6c03814652003c0c01b207000000c02243c110154105802a4480040120303500e500c80c2c80d000e07001811900906112504098000c500c5804015040007002c1d04950003a403032840820300f03840010110001110104282020703400800d4006014044886200340c0441c003840c02c00c003500c814032510010071101500c5c0760383c40300d10131404040000058808510160200b144500e0281011010b80c0c00390390140290f503000c48100000c020314440e0035030a8940c11101604262180300d00c040010400d03410265000784000740000d11400a4880380c030022030554020b00c2849250880071041c10350021000c1d0300003000880c45050400c2103403222005801e14 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 293479073 1250 293477823 293477827
    0xe01030e0111090f040c05071502120c0d14040201020601120501060e09010209011d0901091a030105070e040b0303131509030501020712090909020f040b0609060d1a0904080405010c08 80
    0x3009455096510801580c440b048000881c4015800c0c40c0c201c911a200c0305803014080c1c03a10681c00103002e0300c42c4420250044044669180320594181c048848400740c95401c401c241c1045a4041403d41c0104180501a89803420003640004034201c00b0344a02d8058028103403903807803e1035000c0c2001e61000112050f56a81c100464201410f60845d402850b0740000181c80c0c22007580090405091100041d180302c000403820607080d510303122564151803032140702003481d06c07001c1d4009400640c0c0c5556035074135501385810030030042d9004101c4400401e04407030901804000d20241600ea104a41040040f800104020b20040c4007584903081101c18070714082450300d0f540e440c0c040c2240c000700301c11528120f0660549081c194001500006403840780010485209554001100d481c03202c4119030180b40c40d00c02d83c1c1807d550b1001950a941b0001d81034076650003046040100038050b034102804034007404903203048941400002c003440340380d222078a14546800c00b40155145004d510007141d0f40c540c1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 293480323 1250 293479073 293479091
    0x2090702030d0e03040f081f0c1115061c03080a02090312040803030f0106260c0d090503190804020a030605060310021207080105010f170c04030b0708180a120e0103 72
    0xd0f12450015141d544080c40c0c0f0b807428003134440c501941035070211080f41c0c484c5c695503007410024080395070880040300d800149490f22041c29240c4100080010005011740c610120110310001780c02c0b0711071310045401c03000100e45001c1818256010081c0940000c0322000000c0c2d820000764018007521344010101c2d2000d00c0042c00c0d2407125400ba40001e9910b80002c8180580200050308071400f40c005e500f0207000140c8110413900c656207a0380300d25000317040c040020500c0e01d81c0d040d080316121546280103000074085410300d2a941d92100e42606044c0314044911141e5910800d030040c040d60703005140001c0e080c170f1a215a0003800000d031410b5070600500c52545c414610903c000c189011440c0103446041ca0418405066020141d0101d03041c48080307519228076a40c41241ca00180d6002c0f0030358a070350785451000030303482d002e01e41005003040303602d00c10301840c00d8010581a11a00020301248030380000845965103c082d07180000701070a0a40301121441c40c082d22804440c1e008c1031500080b0b41030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 293481573 1250 293480323 293480347
    0x18030f0d1103131212030902221d0703140606010e09070e100801050102060618071b020307030f0c09020910030509010902030715020d0201140703020a122c06040f0209070203 76
    0x84a50700c444d095080001c1c54104003c0c2540b04400c0c00301c1c031030a0800c2041d08540218010b0345104112003c2005220000d00c3d0f034040381c1d80720003096000d5510128120ba00a280c0ca039541d4240d000564140900322010300840f1400140d4030300ca8041a543d598851a82105000b8a00030282c03201e424001d1074205e003250307503d9400d00700220401942d46ca00e0f50703501d005d00180c1040d5018000c54018400c60103440d4200e144014203a420034418545015440f03917501035a4640000f00c0c0009601d40140c4030004180003905400d091050b0040b1503103040a9550355405080384100c507441d80d0448801d909101e00716000340c1c407255008103e0b81c0042011002540080e092060760f820248100d141d0b0888010078542c10040400092114002044038044000e03210440c05801400b1508140d00040c6540d00648035140d003000300d90342910309000d02a0321860441e21203606d50a8215580590058441080380015507070340940d810141054100c3c4c056024019881e4000300a01c00b540310800210940701 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 293482823 1250 293481573 293481607
    0x1c020a11010c0504051002210d15093309020d0216120807020c010903020f0a05030304080c01180303080415020c030d090218010305190510020a020318030f0d1103 71
    0x1540e5903c86030380d24142402c105002c0002c0981c001150b20648210b800800c20307280c4829210030000302c490715000e00003000c4001e401c2c130142440c1c61010351100000c1032007454001100e0541e41c0c8a03c041095004079803402c04000030b4454840c0c4001c03e090070081e0300d55aa0040081881800c070152030010f040707c1800d00b42d076010204031400a0b0300113035861820343c00910f0541152081c8054000030f001080028484009130202038414000030740a03914030741d10001404004d01000e02a00c1d1251f54a0150548540b280c406603404254442000440b4400701312981003500d605840d924102c2d21a0344a07800100040c1c004001d0a0342d0802051088c0802007002d026040100200452100c1041c41803140a95031960094074000300710700103100040c0082885031032000700c000402080c05203410075a01d4102c14a085007000342c800a075540c090340c0c4c00310080c810040840951060a00008140756940103481c0303103882150081e0203444103491140030030184c2c0102240841e0b06181c0716556a035012 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 293484073 1250 293482823 293482841
    0x510020a0e030c09190e010f0c0f0305060306070c2a0803040906050405130201080a2c061b0f2a03030f090102040b0901030902041b09090608031c020a1101 68
    0x208078810841001e92a00700010b12807032106599a120300c0c2000040340ca540304400c1c048002e55511070810818418095005090f1a01a0b4805201907150b42402900c00c0180d0100340000a09080001e599403e00103801030040360381c0d9450800022503034603806e058078a0403035402090410310401104010345c51070248040c0800d203000c0d540c1c1d117140056050444a00303600c003a001c1d5040004100c4074004042140c0c0c0000d8080c03d008025039210b00b0300d5030080ca51400700390700d90001c80c945450071b1603903c030102c0280f4112004480d5541c5503c0c0c100406c0fa00074042c2181103080421043d000065039070050b00d4848084c124110f084000301203080c3e0110b81c0c00da1448030950010013081a0302c600003d00c141c000942ea0001c41ca85400c0c8981a2a28800c1d000c426050544030080241107403201c2e400042000c20490301c075074011142403001440d40780341784555007503a424028042003034000803086802c0d035090412043e0300e210000d03200030013035001090400188905104241c602200078040e24401c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 293485323 1250 293484073 293484077
    0x70515070624080106120f02010305091e030a110f0622020909010e07051203090f0d0b0723270a0803041205070e010b12090102090307170c010806010206010b070510020a 74
    0x891414489400d0840740c5c5544900c0c00d0303070f04011940011522180c1b149003265021f02e4081002d84c0c2c2e044402d4a03104402521031345100800e0442c0740b83c11750102c06070410010f203590350018000c000c0b031120b59582240c200001d99400a2002c41e00704d00c02c1c1c008038403078040c40703610702e43d05041c642e00007030300c1da080440d90b090059441e02d00e0002510784c02d108040103860100e0784019101c0b582c006180c0d8074021411018003800001c981e08600b6540e0303424101c0a20303031041501b60f451401c0200144814030648403001800d000c1b00200a202210b141a5040c0c11a5452100034105c800000603042009882c50b4540208511501040c036460520040c0003410321180000c00c80d0255281091a1074a690301442042c8040001803084100c0807045441010410303031320200395141c41c03000038020f1282ea403000e0352600c40e40000060051860340725030103169100e0305496003c0021401035030462012145503005811020040c800040250040c00009010303604681c0d030b960105400780c003264040f40315440 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 293486573 1250 293485323 293485391
    0x20301031104320417071a09030d0612020a060e0625060e06090d030912081009150501031d030702130b0d230c0306060402070f0b0a02070c06020705150706 68
    0x13050006410076a8139010351014890b00e030084035125086000302000c1170fa0700c407500d80310115500c0c02040050350700c1000c0c101d80410443ea5030718844024042c804208900035085d17100001407050051303000c1107400c0400381900d450949156030181e510f100852030943c86400c551929004640548240c94103000031000908040c1440c240c90340c50810b9180c407142c00c00d810010003500203100c111421341c3c01c00541c100501c540e01c40c0034100c48003208a40103000101c1c44c0003090003070a24180545012205c2c05c1e2010845100d20b85445510f841c2d201a86114940c03040143c0320043c01c10000b800c406040034400052022105800210019800607003a60311000c80b035001c444031a0700b25110820710b50307100001c00030000b801010a4582000600b954401c0b40c1c0400c0c00c000b03214041500d41840f50b4000e00030a42454000d208400039000544262503102118002007505800040d07110b0503900300804500d80540000321501503948520011241c2a1b2a0805240039034070108544441e510007503403102c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 293487823 1250 293486573 293486581
    0x4021b0f07090b03100513120306060f020102090a05010f120203040605041a071d060708120108071a040b130918030f020a1703150a03050a020306070302030103110432 73
    0x152a2180d10b8100804203071900c203000d1a503680006044201c08510000850241d6601d00e000040c14046000074080406425034a445194194020400d984050b150900c006e119108228200d00810703000301c0d00300a40201c02d01542d030040c0403030702081800303240080480350b46503144020303a0070030784040311251b07105c00c244000c0040e21800850810f0f15020303510b8151905100042c40303032070300a06200034546800d00b4041543c5425040301c0115412400b25a0303075110030300300c90380301e030209120325881c0713000341e84000c1510700104c003503001004e0441c4059070070035042a0ba0504503511601404c1c800320800a400580c0c03900b98040c1c0d801c500750b01c0450320520011420003408840c0060295021500268100e03400107842c900000c4040d840c17401c0311074980d0340d041c04890304c0c0075801c10415882520060000100000054840c000078800c1d0281ca910b5100c40d44254207070302007800010310030380c50400315540310309080d406849800b01004d1230705420381c00c031007410f281c010a984020307074031502e40380c204 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 293489073 1250 293487823 293487853
    0x62d06060714061b0325020f0d0e0a080102070302030d0209010c0605090105060108160f05070c08150106022515020106180614031b190812040303031401080d0e04021b 73
    0x404c0e400c04400c00075142d80b0700342011204c00013100007a01646010088000609031080000803241c085041c02c440c1980c8641c2c01c05000c42c0c0008040300d21a004000c0b010450201c10b0003520300481d4180c00440c101850181c0d4600a50001106a810020702e40c9020300031403154007946000d02112400002c0700d0419038001046840c009208a41341e11903004048541d59020805424400040ca049610b072811850800745001540e40803115030f2007000011881c844e8501c860314102d03620703902201c055103480d5002d824000c003404880c40385d100800508000c4641c48a00003801c01c009840005500c1342c46441215915000300210b16035543c0d03441d4184030401d4042e20740b010542007140280b40f580349445007003025142e44682d041c00b45083c0c0d181c0c2140d21030356900500240454806640c0c0c481c0302c0a03641a001e802500c002c5c0c0001c2e041810662086000c0c0224038141d401641c09400b06a1740807800351f400080099603190050f90800c107503900c40003e0040050904499406007840d9018401c075 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 293490323 1250 293489073 293489101
    0x6140702010b010807030209040609020a02010516030b09010620010e07050f01090302030d1413030305030f0619050910050613090e03040f14040b030303130302062d0606071406 77
    0x1650066a00d0071141e900160380010401380d100086103000350351016810007290140a0310741c04201c25174004204140d10070b8040d00300c244181c4105070102503180b02c0640c11416100c8030700303041d5005416000103126442c400c0c0b9038072a00404075801504030400c104407182c01c41d4070101142076140c0080c0014009403600c0d4408110800c801d04c0c0c0919040e081d41c0001e621500c042c0b040d1070a100d02031424044c058059400d45600c0c031180139022506a9684c180548180d104554845090880c0320020792070b072906800701901510350740c1c080703960b00382000244421804098984803030040003040000341595000014540701c08400b010040d85854036107008245c400d010a404220740040c0010302412518222110894603003440e00c18001035080702150083c61441640d54050000104206c01e21501443c2034088038400d900300d4500d0340e1040c1d49512034107904e100030b01e2882c0c22000c6020748160b64210304c5401410045c2458902041c607034443c1c0400781440891046608547c0401c5550034010369 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 293491573 1250 293490323 293490331
    0x702030c070b0d0b0901061206240e01020c1504050310021c0906110403140c060a0215150901080a051c0905060715180203010605100801170a0b040614 66
    0x4509189000d480d5036100e0701a401041c0c02c035400468502c3c468a980e4000071036043c07001d400b0b141596105d04c002051090344207034100e0348908107000040d001d01e60750100c4100310000540046100740c0d0010841d00103071594880b034110700c25810703156401d0b980d400501c01d0302503400d84e015688512b0841071506200c0021280700040b441400524a240c80d15400c071086c9804e0f112000540312150320382080282180ca009244d042c1002c5004000c01ca4050032440c02403104e0343c11240d4180f0007100304070551159500440c016045000000880001c0c0e0309410f400840c10b801141c2503010460110318003030001d038410340580c5d000620388014000140800d102c030602c60380e01e0b001107848900000e081c403030741c610506000340000140c040c14000384181b03c0c0c4404191950501c08182440c5003403800700c609030400d0f84070703502e4020002a1b17480e01e0302003601c44609035107800c51aa03291040703501700040c11a018100341d0203070403894000510101c0d0b01c240b007a803044000040006c1810205205c0c810010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 293492823 1250 293491573 293491577
    0x301020a0c15020d06060801050102010e0c0a050456010e01080c120108010606090b03060904020409030908030d0609110c15060307120503030411090c090d0f0206130e07 74
    0x1203440c980640c0200100000e9411201e038103400060007035207500134031a601402200a01d0180b000ca00240e12010983c101c0d43d099000b403000e60051b0b0743c195180c0f841c044101c0d81c810400cdc4020000c80c246500070303a80c110311142c041040a2800c1c5e0364040421980741e14000048802c2c0c441c2500089980ea070000d4910801c000a900086202d001a0042800510f00d5040c8846507000610080d0003000311020029201b505000c25651006d80d0340c0a405140202da0104454401c0800c1c442200d0f000d90388a00030041c8425441e8a403502070000402d649041582009400c2072302003a000030400080c00c1d5412403101c001030091078500000c049a00c140200c01e00700d9030800c8010b032180030008007c039020b40c02003d0b2081c5074548600080c038050143d03210030400c030030802c1d09406004020000c1c40c803681c010140307134012003104030800007580700c2258031004024003072182040e6400d25070040c1520612502c0500d200000703940020710f81e41c01c681750b101440b14031b0400500c010301c1c0590207150000018 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 293494073 1250 293492823 293492827
    0x41b1407170924120414010c0e130b0f2713110652050c030c1008070201090b09030310090507021e070b030c0a0305010803070c05011206050a0803090906030102 70
    0x950faa0990503c65080030074004c01c103034008502408058940e040040c0d404034000c11212101803405003660b42e1491207548a4500003182d80310080543c001c1003200d075001001050b0f10700d002d0041100102840d111007103443d001080c1100c000d094106028020210070041240c00c50440c43c2081c0130400c0e2482e41e41c01080288001c1d0f1030120003041d9000300c612024011903200d1008000c00c942c08102c64842c000038121000048860110344d03031920401c40c01007003580d014152201c14141d46410072241c458008000f100e524042c0c070300c12195143c01c00003d00c00804e00c1405074541a013214026941c5e0381040e0000000e01c840300c000034103448010901807800344200d141c064406511604815034000b00c0960640440c550701c0001c1c0170500c050700e0401407446d242c0c109450852546c1c0c21030000d62000c03078608000030400b1040002500d06140d400300200c0201420103004650508000e0b072204c0c1195210040410f103a40c2d0071504ca0701400c000001507031104004010401064005040d0500907481 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 293495323 1250 293494073 293494129
    0x1e0c0b0f0f03130507060c060506040c09150513030c0914040b0610110a120206010608010f0603020a02010b03010e030c011107150905030715051005041b14071709 71
    0x209094410908408041c01e440e81e580a044000143c01c1c8500142103014114000c584280c20000b0620403600508003000642e655800780021504d003004107601068100c881008025900c0400d94001d581c1491301c103061940b00044046503620903002120b943c541c0d0317001404100345a10a00b6518025100c44c01c1d52400c05468549607010080c0074a030003449d007490004a428000d0100d100b051000340101c0f00c000b502800c0c621596003100841e0401130080000000b01e52f071003041101d040c1c03030381030364036042551411006070b000b507000002482c04d654903141c0c01d01c8180d4081c800d020361803860300b0145a840b214190751a007110480c1c0b8040c140440148052000719680c5640300030030600e03200001441540c0c600341503143d4064400020000358076031000041100040d0046c900403404131081d004055210010801030310984160311a0290f0741c4090790400754854441501e00e81c034000c0c4010300e051000c2d2605c0c0c0c062400319441d80c203020000603c082c468141400d02062035565101c2c20f40207411 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 293496573 1250 293495323 293495347
    0x807080a0b011e090b0301031a01060503010803090d020a150807090603230709050909070306110705190201201b06040503030f13091d010e03091c0503071e0c0b 70
    0x140c1d0f188180e074581401e52012140d0f030198400e0320142072809800e0303881b50780d6450001c00804006648065902502c4000035842d40204d099906880707034800034500341000320003480502d8038000403c0c0d03842b00c0b8150b00000c011100406004101900d41d403124542c1c6820040641180741c103500070400c041c501846070740c9003002d1001c1211080070055200314961a116412218048142c06c190341c084000000d10501c104005034040072280309810a0155000b032020005407401100b82c054030f1500314549401819140031305e8040c01d18414182900c0c002424101c800e03a007a1350440c0d043c415403000480c8550025203400c0c60f40e462a0466165185c14100800321741c6038042c0b225582601d11020485001d0075074801c50b128080d041e55181040b03400a049a520315029418200002d40c0d464200011b02d545004800c035a82c0042c003a1008080f6140796080c203040d08034600c03054880d4001070010000080410303c001007000c80e10020b11001240b51304109009942a0b4450b001400c0c0030003140340c00c10 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 293497823 1250 293496573 293496587
    0x10b07030c2307090b0a0b1204032001020d05100803040b1c020a030209131a0f040908040303030603020102072c0601051b07091a03121b0106060807080a0b01 69
    0x5039141c541007031140120724048909030620110a59100101400c000c0e110000041aa04444040e00140141007a0009000001d449070207100c0f1480d50030480c1744101540c0c610f049800c14801e180040c1000030000d1100d103580054403840903036940008000c060040513001c1d41ea003100c00c4c1003030a01d04500d807410703807036984c455071080901c03241d40407136000303100210306455600003c4840707800d55840b501c1910040003940058500c40c80f4007140280b440965240d44030300f040b4400085220a10588413104005102c1c105032140c0d80e0042c0c0f6010080005a1050b0103800290720070b4070003180f80703402c502c00603080420a4000a462805833134881c0d07119406450a0703001d10000c1241c2c0300c1203440390b00040b40c1600c2400300410082d100701c0c0103c950045c00241040840d400b07190200a01910303420002000d400c246c80c9143c1c1507000b503034002c0079001c0c410004d192803d001090344a2543c02c040000c0c2c01d40d14154049004a0300310010050381f15042038000d035000c4d140c21800c10a08c8820000a0421 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 293499073 1250 293497823 293497837
    0xc0c1006140f031c08040309120510020913020c0c0102071d0f1b03040516060518060a110604080904050a02161203060f0f050f09011508060f0d06020705060906010b 72
    0x6011501041d1040e8600740b100081940c00d003a26100b441e44d1400000c0e091902c19201200000c50042000600300c0540180d408180c1d4072038081c01511124154400280d001105020780c0600520381503540b00500340f004001108016000c0e10f84403410100190425001e40d00dc40d0001c070400104041c1000110b1540d6840b40100003188007507111041041d401843c01d500c414010140041440184000001e030b000e030800d4030074034023490292107100884040c01201075411550303280c1c011304001407130000081c1414006c80d1501e14008035540700010300e0201305980c280d604080c0041c800b0540d0034640602c9038000e003000341c00d51030001802e40358030b8104440d01d00a0008024128586095807207508140028061140b000382004c2d150300903118440440c1c419188294021109010f0354102812118101e070000c038005c114002000006030f559000041482ea402003d41410003032960b969a4560b840f14001d030401a104e11051405614000001d00050f10561160b80108401c041c114101e0f07401c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 293500323 1250 293499073 293499079
    0x105090c031801140c19020c06040b0c210c010507050f040b07211d030d0e06070501090203010603030806040b090f0601031508011815020307020604030c0203030c060c0c100614 77
    0x1440300c82400c0d070050150000035013800c0706903410300c801e6805400103071040311020a150384d0708546010069030b49a02c0e2150303064001d202400100409c154a40c003030642d640884003983c809141400d0b0f00100f40212120010301410003068681015a00b4416144d015055041c510700c0c20070303461210301e4940541d20400324103001c0068040c0070056911200b520301c0c901000e0284a00042400c003900c1808541d03505e00c01e0021041022005180c0000e4070345014070281ca96070112012503050289942c020413095541e9074a411000006880034800d0f01b00a500030b44d195043d07424034604000c20707134101c14405403154082005001d51010081c00071900407400b420300040c2035043e9420840c0d400707074036445034115501e0041d081d100c2d101410140182c0510030480c880f9210078000d1240d040f4041550000010783c00000040c00090040f1281c552541c0010112820080c0c00c10b200351509070304480444801802040d41da400740e104011404204a07107000a000f81800c02c00002c01e883c02e036184c5244 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 293501573 1250 293500323 293500351
    0xd1107050d02060708070c03050d0e03031603081f08030909070309051005101e05030c06040f05060d1407030f0e010c141b0613020108060103060303020a060c020309030709090501050105090c03 84
    0x40000c1c84041b20031180e4000300402d0829500d041c5151160071188100f00482c003103d5800005203004400c40f10103648031040007118480e141c400315040e0000900382d03429020180c640c001c1410360b12804800030040ca0b00203603660040b80c0280642074102402d242c0c149820302d0104d600103035012030108410002da940000b8969203007070724002464068ad03c03046100c01c204010400c550a00d0b151790080c0c2c0c209404680c0c1c480c1004092151500c61407040003034440c0740c0c0e181440b1518000700104140c601e051404200101d1140ea021003201003614800c000c80c0e0750f800c0b1085100c4140c05a2010040303244000c00201442101c080d12a02c0c500d10350800e80d8200290070042d4050b28554030055058030720032a0780c14a80b0340420740f00000800e00680c0440c01800000c0c0c6158401d00890701a25410350280c80040015035507000503004580c2d001c020350200b8003078612543c03800c000c04c00c003c00103082c01150420081c1400d40c21198182c101324040d4144404000d4080040c01c22243c220201400541d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 293502823 1250 293501573 293501587
    0x4050303151804260a080a06120b070c020607020603090c0306090115050103050604020c010c05130503070609030303020306042702130e0303011a0f07150c0c05100905120301080d1107050d0206 84
    0x501003010380c003680341d110b4004240ca0701707956844801c0b5403055003c05001c00c40c0b66220071500c0c8940b03110010081c00071002d1070014450501c180e030300c0307414030784041c00c1e1905061007a800280503420844142e500d5604c00181650903240400c1a070750007002d0a0020442c003800b29005c19480c040b24019103050648400108d040f0380c49550445a04a00d01c500800005019032002051b075031100c00d60645a0b41004c00205403461f021130384000702c60058940c07520551a66405501135040240042d5206075585140302c1d070018861222003002910f00016440c0d40c00318810003145062151447e5100742c58180c00d0350071034800200300d038103442d801d0f1030302a038459112500c4000c0740318607410000c0f1140003040c40e204218046e0707444080c0d4502c50703806009030300314020700316051300030b032031000d009940180103441804040e988a2a80240102c00b603070441c010712280400d8544c000e80c407442c010f902c52404420f19079032000c1d0301d202544c0400c0c0035003110340c60030300000c10011030407002034490400060750f2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 293504073 1250 293502823 293502863
    0x10e0a0512120a0e09070302130306091b03030224060d140f010c1d0d031205130c0b0c0c0d03022109030109030c06050a0915022104050303151804 64
    0x1c1940004951180e07560350405201c020003140c2c80e12001030017404140013040545009009854031080c050050b80c4006103152640d07409450500c50581e07100350a10040003840500b0034a0102943c02034008028924008204080300d034205400e01003106821010320000d03aa40e030810210a0f41c000f2007e801c94204113013014180b4191543d95425036103800800c11100f9040050080104803941034030a00c441c44400b4018040d0700c0312801000030710800650f00e40000c5ca40e1006400004840c00e03c660b00120350f88030550140b09401600501401207600281c0b0f640811200c6034020f400c0d5410f41d00c14a01e560081c0d9240c094011b032290600381c12000240000b0004d05640c405000140284080940d40c00c024002c1e01c00654191216400d1000150503030308180200c00d2403940c4022a043e85201001c4010000d4100160042c510f401d882000403420000d019240c0c01240100080c550740d042140d10601c5000000914074000c5403092010306c0003d00d680c03a5242d010750031a19150400e8060008 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 293505323 1250 293504073 293504083
    0x2060d0209091312080103111003150603060f09022106010302070f030804050f16031e0c030b16020a020f0f0f0a090608011109030304030201230d0b030c010e0a0512 72
    0x3045402c14144410021050000207440b640c190140e02510028880e4510031950b0280c03d01020303080051156030021142005001610380080034540041e101d20000120845086070b5030180002944565050101c224280840f0000301480c890451400c400c0018406018656081120b20050350000007481c0b1307400b9404852045501484514001803186030103044100241c1d000e80d0303540708603620414291000614904450400c04100e17001c1e80c07442d84c03070030712000c5001c0050801141120600300080c04480c7c40300041c0d032044000d4489807800301c80800008000810361011540300c2c2c10400301584542c40d046032620419252002103d5020340880c40d0340004400f081d030444400c4d0300c002031003d190b034420025600078100a0200610075102c9294900424240d030398107402c20001000150301800c61b441c2c1405660203041c00c0c07a86c401c0c6c2000300c0f0b900080c090621607500c400d010b881d903207400e01513101161001d0070401c19658101d00810000300c103170b001c1c1c107000d543c0f01d68045000003c00c101c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 293506573 1250 293505323 293505337
    0x2060d090507090606110703260403050607050a0f0513050904051c0224010302060d0905070b0309030d110a0804060c0c02090a0914031e16020303071a1008070302060d02 74
    0x459042070f0342d0b0380c0040001d003901d200380c400084070540e0342c00c10b1440201d5030070200c03500091000d0071800640010195100d003256201c00305402088000b0000b202070054a118058a0b2031782c0c1d460780040c00d400f91010305072030840000c000e810031003072007092100d002d140160390042d90085129625894010b15000103d85808a07003100d403091030741d20b254009881141c410540340005002c0f030070030054046203402804000c0d48000d040c004221541460341c810710b10b09000d0001c460180c0d54a07400345000b51b20a4880d101d1780d0b0400207400e088030b001c0e0b024202045203844c40c541c1c9492045840205425000b410003040742d51505489458103214040c406a880c4c1c00400c0e0074a0b600f081d10b445401072401540440306198200048508903001100f9110480c515480400c041c40035460400f43d264170101c0311600c0040c19495541c050f072420000740821314402d5004048003048441d04902d20400203001c1c02d000342100806100c0600f0101c0d01c0c1c2d045a42c180c561544590301124a64080d002e450 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 293507823 1250 293506573 293506583
    0x4030e01050c120d09140c010e0f060412050309120609160e0411040605060406170a050403082d010b0a022808250f0303060614030106180510050a0305090c030a02060d09 74
    0x40c4415546c40d000c40c100340043c03070076210300143c8054841400304c0040281c00e92035001e101032000304480b240900c44440868400d405903813900007400c0010b94242d0400304511602e40c04401045001001049410700203000b12004141c1d05103404420b0b0b020365801080100201c0c0f162629121945650304580c0c0079143c02030035a615540c0340c8a00600c0f1801e40802036010740b41c0c140c04501e60441030302c2450300030360b0140d540c140d0b40e80d2364940c0600001141d030300d08803000d001c4801c6622a42c824610041c0a8814500c419980b80750741e00d0020310b0704d24424030840d521400082e00c5100044001140c03a44180e00041e42031f00c81640d0144080003611102c03002d03c0310910002e524081040b410010b0380101e101b924204081c42e2114021115240b00076458440e0300410001404414001c59126200b01825007005410b10344030004180c1c0801c883c249403021400114201d140240c0500841b94002c1c0d0000041004c04a61800a9a41d50300b851010f801508000789442010680750808910300d9002 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 293509073 1250 293507823 293507843
    0xa11011b0c120213110901200601060e03010e06070f110f0609010b090a050408092b03020706030b0108040503030f0702240a14060f221404030e01050c120d09 69
    0x654540a200c90088408134403500b205203039000c4548052140d031803001003c1c101c4a0500b403110005460136040d10301e00b0b425084c1461805400c400040092602030546a613030a011555410145070a40f5500185517449420520400c13009580c407440100950845103441145214480f03506030405c010400266454010b032400c0014030301054100800a80060300c4042031540c1c3c41c1d08042c2250003e4030010300390b032000c0101c6505860b1401c5004080c040004c00f2001d00e05824405160004109004a026030072001c2c2c200f20207505441780b025140c10a080200e00d925040d030f6210f03141c0c0f10045c22154100c00c280041210540f082101e02c54400200f0102407d40100000034001b81c0f4081b070f04400260304184002a645a000031000d0040300b001d00142003c002240801909850742034a18044401544070051014002d000d0100040400185980c03581031030f0130f00404e0050040003070340c10b0050811a04820380301c00107150b141208601e4285454900540c00307440900450f07140034110742c2e17030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 293510323 1250 293509073 293509079
    0x1091512151706060a0b030f060105090402090607060b091b070204090f080a090e06010e010c0f030201020d02160c0803120106030c0c0821010609080d1409220507020a11011b0c 77
    0x183c182c0910350407030306070f240c03aa80d9000074400c1d44421680842880d40d510301042403940680007510481400500160400d075400000c2401600400c10550300c42c0e48030f81c810203c500f001882079800a401c0c00404401158040c020b802c607100ea00300090260390b0707641c0c40c40103010700d45188564007640305072841e544282c1c200e0010412420740c042c900d1080210380200d4003070341c01141041d0b0760a0060f10340ca141018140c4a1900441c41c0100039400e55400300a1001c00d120709100401c2c5c10501000c01a841890341d00b8010042003c03600051500d920802c20385041080743c1c00e079181140c0d640e03c1c0115414880c0d5000300c40c1100e05605c014190203001c150a40d00f0008540c28180d259072980e0032006907a42c400741241c0d52080c038400d915441c0c01800c1e40c0403040384502c260440400301d098916151400c0d95021a000402500d03010782548441200f0241180307083c00b5158002c0d04500c002e292012580d124107000030394000007107041c0100a054482e6010002c103000207500d810565044009507 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 293511573 1250 293510323 293510369
    0x1905030417030a03050601030b09010303080712110a1101060506071403040b032d040818030c060a0e0a060e0609010c020103090f05010c021005010e1b0408030403050102090109151215 80
    0x64543d04000c070381000d0000d04154800c1c071540641041c010010703105d0b83d18585042c0c80d000c0001d80803000300310282507040812a41030042c0710032074002c0035170540d50381c065010042c007040b1b4804c10f949050f410448100440e5580c0d03000e44800c2a00701e80443e803076480502c0301d245503100d0b80e4410100c90703c02104000081081c05111510303043d4030020404082d4400c0d644480c51041202c004100c00d00903c100700103c407406542c101c50f000c01404551504000f04d0000d5640c2d000b0b2032900000481610980e501802e0408088009050310b05080c8403410a44000501c1c40c080c2002070760421541010074800c0d60b11036000000301d940c00070461040c289203403c00501034950120178202601c42e14620281c29403a61203501c0c100e43e0792004104003900d1b41b850030701ca12030301c040540340042001d0001184400c404d0000300005c40c8a0000140c2c3c840152001400c40512a1700c203030214606e08400c42c059940100281c4110240344c4800035000181c03008065040556411903072040e065080c0141c1894 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 293512823 1250 293511573 293511577
    0x80703030306090b06090d080d060b070f03111207060203060a053a02130b0303070507060f090b0901052a0307030203091c03020a03050c07170a030e12190503041703 72
    0x1284040284030b113802d08003d02c80d0521400c0c521940000c281406900440c00c072030302901d1555804040030a1150f03958545400640080e4030540341420200e00b110109030f080140c10410101c0c050180003000702d80a140300440c015054083d1041c0e400000042ca15502ca070000c0c07014010080401e101e0346424005486003041d42c42c40340060110540e0340a01f84140070310303840c0a4983c002c0150292105070345005024186407545039815105c14084000069001e200d103a01404141e1755105450603840c00042103004540c1c01200c200702c00f041400000d036400740480f050442d800490044104404d180030002c4c0f0400075840341d00f40004201b43d82056800300082408160031100c00d0f1501d000c0c0c241c136040c03a901c14940180582d02101d003840c0060f0040e0041c00000714070f0702c1959030303865580182348903807032000480d1441900230001710710030141c21081c0030309030b114240ca03600b8031445840c450030f80e104a107104140007041d450300740341c0c100001081158060079240c41d0f041352540032280304554035 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 293514073 1250 293512823 293512829
    0x40e010c09060503010f0909050708030c030c0606010504061e1103040801092604031502071b030506130b01050409080403050312070815091612092910031b080703030306 74
    0x580c0da400000c1d82c40e10620550741618109818805400d00d04a60000180065042110103010700e032000504c82000f440544516031001c40515650500101180d00309100140f00605010007403206200403a440714200c0001081800c04c0504034181410603190002c41c00c91049103484000341c00f061448064100c9203469100740f0700d50407c510100c01d44920ba0070b82e800440d503031407010700c4104003088465203581012201d4900c01840c0880075110010284000040304c00410310014040080006c10061160300580900b5078a28040307a550b80c00e840701030706105042c40f4913122100715041c00605400c4900555012007243e980303058004018a2080048513614041080c0c903000a01d4808240d20302c284c0d080006010320550f903504000e0020381c0c1c20040e40003040040c05207403150400042e11074288000c1c050040c01c04d198031058030260201421040514a12409000307024040f40d20480440640358012500802098035000e01050416180c2c000c1c2854403404d2000014960154401340907 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 293515323 1250 293514073 293514077
    0x1c05070c020d03030c120e03071b12050723090604110c010608161208040618050405040506010915050a21150b041d0312061207060809010f050408040b0a0509040e010c 73
    0x1201b10307020001c41c11100302d1081d001c26500104103140c0011100c510908400e0310507045001e00b180c640f54503103001c0d40526000c481c07992091006106011601040c4408603007440300c0340c003450901201095a20002901d981d01480e1a14121000c60307001800b50384980450200030400a50744000702680c0b50303410203c160517000c80f500c000c00c102105d1016010119009034040d07182a1038201c0403610340710342403000030202d9000103012500359258000c03d40254040c00c014001c550406200c8011158941d20a020802004000304002d465a038061400c80d903c03040140515903c01001c0f61000712406ca0007009043c00700710007221700560380c1c40303201510340c00d8074104011540304c40380d2545045800d481d0410395106121050000304001c240c1a888100070704000c05110003481110324000c1103411810102d80303e00100301c0c800d0024441ca400080d450102403005007000e0b2500740f0f15100d03d0142c0050b000c0700240742e15115001d081110110000034204100d0161710301095402800c0000da1800 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 293516573 1250 293515323 293515337
    0x2030f2d09030304140303040b07050f0106062307060905010c0801030c0906060504150314150906060403020d030f03020c060f01080f06072a060c170109021c05070c020d03030c 77
    0x3250401401501c01d6900080d00641c80c0a04024190300c0c01040120074682c144010400440d0084401c40a803210600c5907008180c40b02220400a00707454a5070820b00030409000e07003040744245025002c0045c4100503c1e0319030340303420500b884005041a441c02500c01d41c02d00003030f844003d50101040b41282e00840d10310400c5604c4841000aa891520640713000032010311003400408450240859030b680d0706e040010707101519000b2051450710458888100b11411800c0480a00b4814801a4440c500301c511924050035580090207900c01c5000c0038080204211000c41628040d904803012002a030080324054581591803666441090052295074000c14039158490304c8001082d600600058403014100c10481030810102d50440c84985c001c000c04d240b0f03034004156076109050300c0c2059507481c0003000d68403108908000c08185c3c01801114410400a105030001c03140c81440b8040d5050003181075210f0304411a072060501c0b0300658041400c403001e204054055118101d002c10a4807410b03 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 293517823 1250 293516573 293516647
    0x20406080d081f0e06010c02100207050a050a0e010620030f04060e03060610110307060f050a0b100e040902040605040c02160503070b031306020c060a0905060604180b0702030f 77
    0x80c85283c5400c0c240010607942a00a2011058a280750fa500c5001890902400043c94001800aa0f800e071030074009070304810300500282c14941d4800c80580720a1714a150b040d450311000c100310020503c250400c010304030301e00001400500d80500091007022040b661540340c84450324019500a00c103120110b00d0b20721111390b0078240401c61a100380c40080082c40b04020074a420ba0b1120601b43c3d0b501c07210b000070020080000e6982c440e03000c0010400e0300000351840d14180d01070840f00a0b42c0c0c1c851041c100c2d86003c2007003680c00050002000029140401d0305026440410b001d4109900515806810000c106082c10f60002c3d4030726000910100031801c1581e110140b503103491080c01104402c020410001d50002070b5400c4d40c20465201d00c0c401403600c102100200c1c01c00409448042131251128481814003c04000d01500454211420001c800303024a14101082d111840244441d0042e00090b510701c1c006d10640f0b040d801e40201156840d40c6411029942c180410700305070f00320502d80658 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 293519073 1250 293517823 293517841
    0x306120f060601081b0d0b120d0305061203070c14130501080a030305010f050d0602210c281d0f0901060c021320070f05030403290709060c020d020406080d08 69
    0x96145c14440038140b0745000b40e52010384001e00003c0c0300142d00181c2d0b101844141d14170030130034082c045c079190f170780095641481002c00000e01110138044103298001c4c8a0140030540090b01031003150400702e09101c0c0350341c3d98804640740c40000e5103020740462801e800010400c1011070403804c52803003540e041229a88178190818621118044c043d00306e01c000202c40c0018a10b0b500030f110941c22485020040030ba440c4698003400c904542050407200c0101c3c4d028422100801020320b9180180206500188424001805620400741040047e01d86c050804415150001c42100c0e842014201e480e0039038542c040070300503203103046049024484070100581148000c3c4225058254003040d000168203103d052100180c10040c020740c1c0d060503c0511a0028008000410040d8451851a5150390820f820102e115240d0031580386050041400c1040850384a01d01505031185c60070310300146085800030406041d112030000750082e11f0042c02040181000609070410186030350340100075502c1e5641 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 293520323 1250 293519073 293519101
    0x12030f01082401050d0218010303030209033304030c150501210b010e09030c011e0501080a050c130e07030c05040501050319080711030a0c0e09070303050f0306120f06060108 76
    0x81ca0401004200144030314034110009070080c50004100c0e80b407560320241d007500c03107c200ba80114046580002c2803031050900f8080503001c1a0100d082c000740c0115041c490000d0b43e1000003548030a01e500700014101405101381060302030700301c10300300200301c0b5051640d0000c0c8028000d284c10b20101201c8204240d240305a002c0510741d001403552005e0340703841c103404c00c10400a051040e00740414844180c3c80e80c1d00f445543c10344080f065559441c20584d5916004070b0341c045c3c0100d540e5030021084440030500001c3c02c43c031000800c0c3d070300b00c030b4880704042c88500424094a60b0170080c041c01000005109070031540b41c040e290101c904000c00c2e646c2d1420182c1d10302003101c1c54605c0c02c48901085001c5001c000c081d00f14135005101c6103003491841c4001a0400d002c0250894860001c06006d0104810304e080803544000d044009000350307400e41d100500345014090000c0c0b5501d000000158642d1038000800f203004821004542403020a42c40c0c490711200d044544c0e50009040c030700081c1d4151103000c9 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 293521573 1250 293520323 293520373
    0xc01140c030a021f2c0a0f0f030305010506070819030b120f0d02010e280204091a0906070c141608030d0c05030403120e0109020603180f0309030601060c0512030f0108 73
    0x442e07844400d41140c4400b0b075240344151100075401410504008030b180c500901a000340700d04942340407045140307005004c840040e003206008010a1080d0000954003000300c07022280303003103e440e490074141c0304101c004d030211300081904605010401c01d01350900096041500c0103000549031f1b15065001c0484c201e414066030322140780d04c403640200300085040c10100150184100c88510001142c0100e0150b03032542504590520101c1142004003040c540e000350000080d402400d518100100c004010400420000d04202007120101c0884d503010860f5080d40008804050011503076408040d03180e070070070200300a400303050180b9030015912a00460307215075416100c0b41c05061032410190020f2100d00c24504142d944c0c6c01011340580c1d95640a14860107100d02c03814401280400130504080504190000036481801514081d503404610b4606545040c42d1035501d80b01141008c515051001d942c1c030b80240000400c2c80402c0422400080c1601d20050480d80c022001d607101000c8601034403 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 293522823 1250 293521573 293521601
    0x60901090620071202100201050c0a0e06120a0912031b030522143c15040501020301030b0708130602030910110c0d050403050c01140c030a021f 63
    0xd039090062600484006a00400c0707600300402c64040541a14a040500d4100c0403a600d000d45255045103014a8500d90429880c8002d01803400c143c02900b40f5401003940c1c81c800e00c0b9184000c0c0701d007500e440c070650300c404d00b008200d489641030696000e8000d220b1072100350344141c40c00c40415445c2d4000c1c02032081070340415950700901000c01c4811001804040d10340c4a440c07260400009500b18a5103107004040c0c0101425414083e401414910308203190f89010340020b0441c012031902e00400002003000c11300380c002060b1000107420140e04115030000000c000c0042c0206000078400154095410f0f203100e804203600d191141c08007075841640c12030380150250300b40801c54000403800e0300515080070a0104468840040c201c0d040c4c1543d12807040c02066242c00b20303040040100070001e01d201d001c0107080c20f618241c10b540380c403911507800c507070780c3d41c14072214000c8200241c200001726034092220782c040c2c030385036045113100030344680c3c0c10108814a0100b000d0b03052135040b154800c600428001d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 293524073 1250 293522823 293522837
    0x6130e15090c030a1806090c0f1d04021302190504051905030a12020106120308090601060f021011040b0403120f030b060703081801050403020304060801080c0a140f040f02090906060901 81
    0x910540702c05041701010209611000725181000a28140960151140b08070001182e140c00c140c406c0d0311400c225408105150704044600c0401091184895002901900c01a00d030303a1110070b0711400307445a0701091400900e40018010240e60090141c400d0343c00c21200d90180301c2d540245412a00400c1c040d5a501d5003100c40c00750001a141d1000c20b5001d4454000406c0a03980d0700003075a00318119040907404140b207001001802c0b84184038040c05040241000100460099030003503850b104845041781d000d5460500e1032545100300203640c000c00351108a19996900c2e03217824450408000d4501000c2465a1100c19051f4020300070b000c4001400b40529043c00702e030340c03001c942015002d8a203035048140110440300100007805440e2040340642c0040d640c2e640342c0100100340d042c0503844844240c102030014000d617981d01d02810122420303807403c4005050302e4000a401c101004c00c4d2540e11a240920803081c040d07143e0040c010015040b140c420440e524036040c02000c2c802d00d20725500040c44 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 293525179 1106 293524073 293524081
    0x20a0e0102150f16170123010201090819050706050c250302030a03020a110a030f14040803030a020304170301090911120d0e06130e15090c03 62
    0xb0200c1405914602040240001d10000d0312080e43c000141d003007920b480b0310901700c0c8070b440c081441c2c1c90022541e41e5002413a010003012960791f01c10b48110b1001080e98018854010001d8000119074a8141c0c0d1110b501c2c0540c5000b50280c0a00200f800440041001ca128292140d20051502a42c81c243c0d043c1d01c0250030103880d00082000100403034080040d6011042d0341d4010850b040140e22003103410800d95a200c00fa8228a505d031160781c0300c83c814554040c15954104805440d0901030420260203060103200754018203046500400c08244901c0c0c2d40c2e4001c0d035015010300880c2d00c14092110070a03100394020b03802480e5154640400906100c0e030f007502d0006048040722200451210b412070300d0744507014408e1400500c854107811184030703101c040840d101c1400c40100c04900d240c669100700c08000e01a41c02d2001034118050b02907042c1030120340c1d82e0061203079030700316411030750b07 = true := by decide +kernel

theorem cover : BRFrame.Cov 293345323 293525179 := by
  have h0 := BRFrame.cov_init 293345323
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293345323 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 293345323 ≤ n) (h2 : n < 293525179) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
