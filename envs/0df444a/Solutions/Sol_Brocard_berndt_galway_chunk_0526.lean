-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0526
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:16:04.251496+00:00
-- url     : https://prove2.me/submissions/5a1fe599-2701-4dcf-8263-e70d67cf55fd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 94424460 ≤ n < 94604316 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 94425710 1250 94424460 94424467
    0x7050c010e070614040806040204020304050a060905060f0703090b0c18031f05010503031201060807050c0a0c0312020f071202030f12180105040509040b0402150a020109060e06040201090603020c030708 88
    0x10304941d21511031041c140016502480604c0c003a8400d02076505130303020035000d0500750705d4540802002c8e40010f00240e41d14001d80e88424000741d854420800307094400c1015100c3c600e000c24031414841c1009001c0070a05042c0240b450005544030390869106005e035804985603001842080c0310030507480030a0790988144404802d907150f404d0140940c000100d0400d2007160b0300d80302032545a0140b00b8000030b24082d017400500c10389009465040e441543da28080e424208020310350303460818152015100344107045414004c0c446960b000d8044024540020a030600c4403202a96952180340318074400001c940320007508654080c850346209480320b0b0101c610407600c003010922654001078105000c941a80003242c1a54024130666085400c010980b0310255699211240c0711500100308aa201b01001e07680d031054140134020307200c001125400007901c488079140039021100340607498100c5500500801c401070303034403000401c152100b52030b01584401102120758554000c1140043c039000011 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 94426960 1250 94425710 94425731
    0x100f02030d1a100503010e0601110616031104061d040605300f0f100506010e04020309010b03030f0a030e061012030e06030703091a0103020603060d080d0c090503070611100507050c01 80
    0x413010354144c407403500003154186c540c400156410340c050101140305800ca07c00007900742424103420341441d0316500b008100204003000c0c0f15802d9005411580120b550078441c504080710103e03a40e2500c050503542082040c0c24180001c0c03400e40b40f5001024402a507000d084a80051800960240014082203600070380002c21842e880c0e05030a100c0d00003a1003500d401804840e958003031769010b0722040c0c4401c1c604400c654180400b030750000b4420303050b81d03403107010b0060a134800b00300030010944502031158031800720040003401d039081c010291416074000c001340071210320070f80c506a007241c201400f100031701d01303481c81c00361040c00c619010540e00c114041f0401c503d07640c158019803c002d2040075000134807c0c5190350400d4900b001c2c0030194000c0c1c814000209182044c68409502d540a141d0090602e2032121011702640c40c0d8030310310303800102e540c10200800e041c104030010140501e801d00701d90220707003820507658481d030320702d055000305446201083c011405042212003024419000740000401c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 94428210 1250 94426960 94426967
    0x3110d0c050d02010c0e040e031e0a09090e120702190806061206072c04050a06051f05030402010e0114130312020d0c060903210605100f02030d1a10 65
    0x110326060300e41c0c1c06450ba440810034410b22131028503d5480c0c540410040318036081c0300c01003a6281346c1100074481000091010b1203842c081c00380003070140d0161135440080c03e000034a440650781c844441e80c0c1c00c02c048082100c4010884da540348402c0039006403100028000104101200b045080786180340c11b0f004104103d020a400d44203000640c1c2c1d843e000d00c1101c9842e60390301401c035079200c001102e00d9092a0300745220754100343c503c07004260410741000c0a400190448000391108480c4030342d6800b00f008107013820140c4031201411203c901c034001c020303107001a00c075200c01440241004030140981c2e4281c3e000b619505110340d04035140d030740c83e80004c45255091110600083d03440c2c0c00f4100002d84500e2001a00503003180d070f80d654200381c0d0311065540c4000340400b0f0a0880600001b11500f910b204a5002291070500c1c5c641c0300070a03081c0c603003800c1c03019100c201c40b0208200052960b07807072030300c075000000c0796045a0440e00000314046c0c12600c0f1134105031507075440c03640403039550201c0303417542d51 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 94429460 1250 94428210 94428227
    0x1020d02010b0a0902070f080408030301140f01021507050d0c200c011202030c0706050c09090609060f010309050c060c0a0308060414040f0203010b12012003010e1f1e0306051503061303110d 83
    0x8a800707500201031607a008102d00c8500b8030821434010380c032680104054650710002543c01c0321071402c000d414403001072400c80507501c0520f06a0000740c1c3d124583e4442442003810040c1400240c00a48043c00c2c4034800202100d400c156403144543d000030204a0002c5e802c0e046694140d0408000c004a00b0807640c241007503030000e6002c40c0b14040010108800d0b2421440c0c0c980540802402e680000c03400c0d50065026004030541a0b50368000d981ca1690b05072100b1004040040c40000640585006071801034043d92000d00079900451400c001c03052620b8100c00702680058011291140100661000901503e40d0000c410703005980900104040c0d00150401c0803c6580a0344919020704d140703800680500091007040454a03064000c02c0c4160340f8225030440b46400300d400d0381c1e0310f0b90700c948110940a03030481b00d81289003c9200100309100e45841001d820101e24049407103404c0e80000001c1d43ca00000d4600c2c00600c00801002c0201802102e1410b4404048006c0d54084484414050846407 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 94430710 1250 94429460 94429469
    0x70c03030807030524151611011e020601051302070515061c05031614030a1206050d0309140102070e0a020a02010e062509121101020d02010b0a0902070f080408030301 73
    0xc4c24a0045000d00800c1951300e014840400b000c0007990001e041046503003206400215803a030f1003041080c60030b58909000b00c1c5118090528103002501d0440010705886403108152a52008548404411075001c1703010b85c1101c1048030314904920500c90020024030409600a00034820400d544150498440003075215540403120781420011761072592417035421850005110381c104211158285035040340c0c0b1260540150317055081e0b90621042c032071440d8404041c3d1004100c4080c210001107510f400b4a070b018000a541c14014003902d81c0d00a03040303956134040d541c031031600c4008603511a48200310401c01811859000c800341d01b80805a03800a6021150140c015400c002040043c00b1001851074010001e20b40024050040301e0140c0d0303c1d20190303404460411603504400550b4118400e109504503000710705080c00610031034006858003192030f0001055905140540005548540003402156285000581d44200515000c02d00101217080280011000f103008652074200001441c1640c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 94431960 1250 94430710 94430717
    0x20309010609060504060b03242101180206090907030e031b010509010204030f06050402130c030203070f1e03021602030102160512031012020102010f18031808120c03070c03030807 79
    0xa038589003480144c074514000d518010071f041001c250040011441c031150a40c513048107120031840c0c003002841c00c104030b4078503030115000311080c0c0c80c00310428400c08003202c1c00c0c0f03000080764880302d50110f0707200c6c007646084601c60b0a040000480c2e01d402038101700491907c1400f80c9135180c500000983c5003c5055450000035071070280010140d003014400c440690f504082031103080130039a9580c501400000b00f08a030401e0318404d0720741c0d8003505e42c0a030080b0b05e40252005070f00d900d421040201104c0b000b009050800007018501c4603460076003104c0022145081c0b80240c0e40b040d050544072071500005000941541c4001032141030798014030b100e003124510036425141e000c141c0c6c61011255001c2620210184030700300b0002c1000c5440d0700303003d11100d48180008108140d8503d035410481d02400700c801004103803020301c00205948040000988031426030465071a44c2040022542c0c1c002020440500010014220060341401c000341e626640d4005400014182c072440c000341402015107903c000b1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 94433210 1250 94431960 94431971
    0x709020301050a0317070c0605030405161401181e06120504020102030d051905091c020613020d030207030b0907140102010b1f03110c070302010e01020a050c0d0213020309010609 78
    0x500006008030390490b000140000802411074850b04d079010400010038100340d4003084180000b4666225a0b4020480d64035000d40320b2130700b41401420514001d00385050045920740900c0340550318641c41000560a00c0c0642d80c1004071307007448c0c0c026070f000d8111070f4030324000d000902c01c00703210303081c2072010746820350364000081c0803085880c010750700306460007405600241301c0040c8000860380070031380c0304030300c480341c481544404891201100c0e8150741100494109a8000d000201501c0840b000744480303100501c89460000c014040080070702d0b6000388501c0050003400145231082100700040e541191500280e410004141603948496106816010740c98444041c201d60042c4511020b01c03c000d003000b00d420030502191046012120310840904d607803003440a4440d46000080d100c1c00306200d004204240c11400090400708560400e513045500c0074400ca13000840105a6840b86035003070790f60b104140c5441c40000c8803c0790542c2001c859a1000c810001c540005402030302c11502003290401130f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 94434460 1250 94433210 94433219
    0xa0c1701020f0c0321150d0809040c120506010504050109030609020d14030d050c0903030316091203180e0606040b0d020d02160b01060504062307050303161202040509061c020901150207 81
    0x80508116081246d200494040e80c8050412641c030907406482405420314203d05500020100d0300c6030700c03400c00081c00c84800119000003a03c1040d42008007420082e01301841c1000007070100803039010007421940c0321015002191143c1110b0101035600002c0006090080c0d00e459a581d000101524105410308010035515810308088030450040a8040d62547e0f40c0c3c0030304007154110010f840010420b80c8540061503400c040c041c6450684a5034808041d954071501107060f175140c581000c01200d14180501c20350341d440c80210b508441c418100b02e0344130040ea8407168000e0041140b0342881c1400010b05c5621221040f940701c0c0383da0f1291034010b42036601d50324226114052805080c020801c010280c0c010848a010310403c013003810758429241035204d664090454000340c1b4211f02126410844070085600006c0841490001010031814685450b001501c2242c0c042c00c054002c01341d03c880c060f03495494851f007030740e034a8018002c880e495a50742c0b4401c0156682a00340300050181100101d0b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 94435710 1250 94434460 94434517
    0x4050c1207080105180912030112030305060a12031b0206120f0708070807110703020d0c0503071406070201030f0b0405150f06160b1906060206040c05030a0c1701020f0c03 75
    0x34180c80c1c0292005d0308a00c40c0d1901309a078010301900c50380c4e01348203503002410600c0e40040254007802e030031503000d40404520b00d4042c0694001801d1203204c0d0b85142001d01c03c2c000140c440301e407026050326020741440b8820504106580c6c4040004e500004000344a05466041803940c50098800e0032144e94280c2c0c48810446100c14184d0340a400102da001c04a50b045100b01c2a03110300881900944200c1c40d030346e0b0300041e61124801c508803800c4851442c100107074901403124400500e01036502d50781611014000581c14803550070700070306140e681c10180404005941c403285801ea00600108000c1c00d18580d4020b4020340b14440e130b4400d044410307101806003040ba00381e9607100c10300110211390798050340e9a85c3e2465001440900380b584901010b44003482e0300d0083c00010002074000e0246810281851a04481c154006500951012800d41d00203086030b10010220341d550480ca2455800e410003884c064480d0849065103000c01043c042040320010004000042c1d07260710f6804800d2802640d42c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 94436960 1250 94435710 94435727
    0x6070819360506030a060b03090a05011803050d0f0b040c03050109060f05060d110f0304030903020f0402030c120612030d0506180105060f071a0903130e150f0402040504050c1207 78
    0x71003240c09500c010030180c10200b000d19040314002e030020500075218000207000e60001c4031428515803015038940b081c89400c0c440c80442c4110110300c1e0400714240d0328054601d2081322400e00202e540c85c1d42d0506507413201d40c001655004002c00502582d4100c54008014007001e019060f1854036000000805004004000c0100c400242850b4242000c400480d0003c0150f0100c20201400c10040b8150450b00e400003135124601c41e403160300c3d0242c03c50060100022280407000d018501c10011310404041e50307000e48010955082c8260ba181d560b0101203042e9441b400c42c000700074407011882e0f0300001d995030000c40c40f414041c0c40c641c0759114002c020b09004c07107080c49401e8105000300b084209104031240140b03003140c02001c041502211601c01d04032101c2c3c04071386610182d080440c1d1740f480402000c200000911980821000900309070721118454516400742600ca12103142d001003858580d90159001010300a008106501d00344ca075411040c0c0c080c5a4518541d0320020010b00d1141c0202c280 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 94438210 1250 94436960 94437047
    0x5011104050d0807020312040e07020c030a1104090311011109010206090a0c0623040303030e0115030c06050a180f03030f0908030904020f0904050403110c01090b0906070819 76
    0x76441e4848042d150f581c0070350300012050780c260003202d0320b003100301c0c151000400040a98502e034040620701240000e083c0130701c5102842c466001062003c0201d50b40401080502008560015210351140340c251107443c1ca620b10000917500704083d968420940340b018012210003a02503030403030b030b454904045e02d4043c41705000785100c0c9201028080644100712002c1e120106074218146070820382c1c001e581c550040da100b100021307155000121a001e0a001ea0040103114900706050390b41580d60b400c04a04190150104100d00820348420f070038850450b00b1458008900c0740103640381c907214a1010009a40000d4020450000b24010510b10a003003401c229000d950281d42400050002c10010750b210752200040c0d24000d1103140202e641c0e40c032404e4015031103625518038002646a0341030508e0300c03804005052011600003000082190002c0ba059100c0c122503a130741d903591074134210340036004150301b01c400587c004c07000440c4550002003141110176200c0c1080c03003412161611400445c6d04484 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 94439460 1250 94438210 94438219
    0x10e06191a090114120a080717070506010e06040b0d0c050a06090b04091a10030f060909030212030702071505040801050c0405131508100f0b060403050a08030a1e090501110405 77
    0x4200400740440e104c0340e40c00c00141070303400c14140e070000300d032404480c07550650344032200140c80d03410008401c1007144180c032a984914180101074490648a20f014480d4038442d01542c000980f0940d21540700000c0590010404403100006007821120100180211809111054008034109000301c040c601281d000c40c1c1051303d40360070044950081c100700648014500f1011540c80225900c2c0c3e1741c400c0318110035540000e12030003010140c9003520760641c00051202d10300548803010a0b0b01155a01004001c41d0010f1b0780c80d12021801c82c03600324564007044100d0000d11407000603940c400020011a028000244815116050200400c0c852840303400d51002c480d000705010305440b60820481851001018401c00b950707000d985060851001c12001358903500c40c01c14108080b1032052008031101925050309090540c3d40d400d0740ca1710030395030180080301e0100c00180c040265400c070711a000e02d400c01164026940c914003602400030b041080b1078a501b440e903121a114400c000340d4003250001403 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 94440710 1250 94439460 94439479
    0x40306060503060f160c03051e13140609061305030f030a020c1801030b0403090b040801020c07120b0601050d060308070308090606030a0327080105010b070b0a110714010e06191a 78
    0x5c0a031001c3c0c01840c1c2c02c0b014040d05000840400d582c102281410202e8030102a69034410a00050440b4055070001c0342c4040d054103040740d1a44650083e204582010b81c3c231550340311407990314aa0441200d0344003651512407038200820f95507012000d070490020300e03001c070b503811543e0000700b0032415800d00d0f2000740e0a0340e1000420100740d00d80e140036042406420540030994592621410a910a0f0002141c5a400241407030a4030410840034000300009404098980081e58600d0840c280c050a018100328002c20700450b01c6075107a004000030340c2d00841e82c0d65211a240b8019007034580c201c6000195001d241e001501600700030841c4030201c0e0307040e5200c102c407020102c10b140040c042940c2d040207242030244003158140f001d1080902a1644481264541d1a14601704942c1040103144c006450b00301b0f401003401501001c140c8074459440082c24010301404440b881c01090841d61404943c40b440d418004c45403c2960860210b0845400620a401c2502502101c812403c5002c54203c0e4088 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 94441960 1250 94440710 94440751
    0xe031e06070530010515130501030207020a08010e0c090c130303030e030c0a050303010806100b0a141603080907080d080402040509010608061602100506010c0b0604060902040306060503060f 83
    0x110000c00c1c5811081040740c04003c0301c0207420410b48104100f40e142d100403a4014081441d020710200c00e6511040041450001d200265406500041c46014145900032400404540c2d510000402400d0b68500030800c400340b0384803003541d8034600078156000303014060110fa240342c40070045403c1503400c3d0032601881e501c1c0d91313070440042039082e640311340e180018045046c101100380a05065103000303800450302d9504281d811410b0072000f810010400d845a541006041c01d44000d03034000c440305090120085400d042490000d01c501c0a607003a942e04a1101c40041680081c4101d0095100100b20b8a1007501c82c50a00c0c3e8440981c00f0507001b0410b0b503800500189003a0700141c1d400b01048001040060b550070480e494002c0544551482d12282c04040078002c2e41005050b451807416042400b050520000113080400b48402c040d0004030400c00062042d226074014200402d41204210758843d0380341000b10040941d8010603109002c1d81010420342400d0301203a5024590a400400a52451 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 94443210 1250 94441960 94441967
    0x162001090e1b0d06060804050f06010609031101120c02030d0b010302040b090909160803180306070909150b0d1d01090218090109051504020f090c041a0c010204060e031e0607 76
    0x2c80c0c0090803400002c000c420314000e6503002e2000100890340341c080081c01c243c43c4c21400d0500039240210f01d03620038001000595484103011040f65040142000c55121140040381e0301d82c41580c480301c0280c1040394040606a00100a02104010981c2004800c00c8a40118281c0c800d500c54400b00c0c29061200c141d42c7d250242805421417007160440702d04a02c0c0180c2e5043d142810380c0070b14412b80020941380d10443c0c81d98800344413400118060901442c140c080500f60308018050852400d0342d50400c0d444207600e200da0800542928220561150034a00043c0080e00e0702c0c0c1000c0304400700250040ca407aa070140248055a5070003000c000710b03810000b000c10103020004100404079034851658802090b42401081416219100c02c400c242c81c05005108402280c04090341c014411002005440150300c4e050b6000d8940d20744040580402c400e140c0115401048403480295100050004c0d04e2030f0006007444000ca000d6050350304408804403004000e680e0181c0850f010f401060008008510 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 94444460 1250 94443210 94443241
    0x3150601030c0e03060406090b0a0e0d0507030315082409030a0f090306020304150605090912030612100207050d0507051c0302070b1501080a0e03091005162001090e 72
    0x88510b84200d003440b4080000b4a00901506c094a501d60b0b50101d03401400881c03016580d211007000710601c283c1c00c180e840507030355071019202c00003000f00c0070814204040c483d80204140300880780c0009196602c5110054842d60140503100c84034000b1941440421a003514803171080000901440c18118180000d0b680d460b81c3e01203c0701040310101003c03002420034070155004501840e030440407000e4900700c4804a8005411039807141940c8810488650000101f0039403503410030311320356183e440d007401042e10011131000026a0b4043c10b400b82d600110141d000d400e400340901c0071607051a0254005a8543c89451006002d07600126803210b43c41c0c00d107000072030741c400c400e180041ca845c0007030300e0755000c65209842000200011040c000d45642e0311001c019041840e908042000d12001c100c0e071980c91003000b8110b0301921443c00004c040501500075140000c894640701046980d841c42c140054094500c0081604d801001840916502c40d01c0d009058070b00507040c070003060306e440007290301824 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 94445710 1250 94444460 94444481
    0x190513182603010803030a0606090509270a05011505040b131505100507050c010302030712051003060504053a03050901060504021308070b070c0e181603030e0315060103 74
    0x32070301d80000903503010840042d802041352074080c1d40c132401c00ca6500c2c41500c1c0b050f404903040040841d020702c050344d030301015190080f520034220480daa00c0c0b20f00c40d0140e010050b6100c6810b01a0700250f0050140c1034011080c000081d1303580c13102c42601c070802c00044401c0880d40b160407051120182d05003691a034002c1821044582c1a5080d143c5d8074000558440c585450030400110080707162420000100a03d0100c2103007420f0a60a500d04100d0041c506018600301034543c688407008900b003178622501c500007070342c0c0000090000340740a0a12543da101c42803000c1e00b40035000c05000100c400d010030b0880200d103103d50b0040466051400403030107080c01400f031001d0355680c1d200000c4c0e95541c520003017003290240d5002c00c034840c0c13400702400e08000c02a070211051041c20081c05000515403001d15050b610010004050f41d1201c0300781c0c0711150b040040c054039505c9100c00007103000c44d001c12041e048034480d6444402200d2450207060301d8000c0c00030420f94210303400e8040b40f6113602941085c1070b500e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 94446960 1250 94445710 94445753
    0x140609090703050105130308071d0d02060c061f0e040f1101110d0f0201060605040f03020d082203060c030b0a060305070e06030a0501082b030c05040519051318 70
    0x40c2c07a626010308450043d100b40d01c107048044c060000b0150004c3c0407561000c0b06081020311010042c54282101e483c10080310302c01c2495484840440d40d4003400d550040901d00e04441081c504010070002d0360b01c2a00011102ca6805440014100100301c0018860781e4004040b5611030740716920412001030b07414020f41800341d0710a149002ea0410800940d0000d1140e50301b000300c0007030307038000381c2140c006030010003c01004220920907000c0084245040b00e030b0503102e400e0200c0322414500000e0240301240e40304414001e8600c031780c09414821319030607603019480c20490140c1c550415022101a034155642003052101d08021003406540040e0707000c045810203070722258505000811070751046421640c2c0c180d80e0f00040c801c0150400c0002d8504100c01221034143d440c4e807481c0710002c0d0011800108054540b00e59039030041c4030310305480c007d10f030180442d883d42a540d0308400c0747e50780c0c2d1702806004101c5040301e21011b15080c003031104c9003500c42003010302800c8942c44046003c100e90b1682c0154 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 94448210 1250 94446960 94446973
    0x10906062d2124050f030c1201060e040f0c0e040308041b052205010b030c0f2b09060b190e15030304082103070f0302070507030206040803040303030e0114060909 71
    0x14035650107001d4220041d900000b1500105000d9030641010f0394200c54000c641041244e5550f40b0300260000d03020904543d044681004a0070b03050250005411541c0c801c40e084090004101a15035509c03483c51103030302140805902d8082d41d1416840031580500014081c0c00071070f000c00e1398560b03515001078030429102c043c3c684401c0807a4940350903281820a1408440800c1c01d1000329100d1203015120724600c041c82e40c181108000d505000d264480c1c01d130390800203842054219030f5010003008841e80d01752000502c0b4800c1c0c100d0002d121951094404904100307500b05903140521080c0314600c40d0328080c0c84d0060604c45046104400106520780c045001d481008980d81c0c00c1010b00000c040000050000c064001780132620940d407400e481000250600511647c103410442120141500e8900141c4030316003410902d01d0703c071640e48047c0d080f000018001c00c01400c04130081c0141c9009031070a22400181070340b458221108401b0003c04c1d8041c0401041b05850501d401d40d4121030690b003150780 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 94449460 1250 94448210 94448267
    0x503011202180112060501121a07021c0503091501051003020a02010207080304050633040506031c1d0307080601090506180f060411130302130204030803010906062d 72
    0x1626000c4c2c00180d02510303105207140402250b4000e01d805440b1403130080a40c0e520070307501e00320a00c1c0f2881318040803040781000144098130070071441c041c0d0001500101c0c20031450040261055106032204071550042d039100b80100784003e00c049040368409080e0800b99220b280c012402500b1404107401155000c01500300460b00000140d40154081c1001c5c14850403d500c00c41000004805c581340c405480a04012444240e40740c1c503460303010250f50109440d074510f8006030030200c0a00880c10324001e8030b40da4507416517128412202d10758044448880c16015a010160707151150301c20140c060b4400c40c014001202d00f5045a600000090060125000503140d403600b444400c407981d69071903840c3d104000c090715150142240311101c503480309103012060b00310407508445500000e8098141030410581d1890076130704a4000f142c2140c0141d4989d40c554107900042d0105101e0300000070000350380000c4010200c001c00d2409030204914128800c5c1424007540c640d01413401e1030000c440c1003610030b403 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 94450710 1250 94449460 94449499
    0x60f1a010e090a2c07081603111c080705060a05010819140123040c0b0405060703110319021b0316060c02040b040e010b0108150604090207060207020315040303060b03070503011202 79
    0x5002c22400000780000c4e85c1407070049490304a13022103004e1601121f40c03040000c60560300920709041001cac1c0e0000c040d084a400c0314506165034034401891900001a03079400c1c083c001c078005010380102c001c01c0c00180d03039445e00c03240c0d01d49450200342020000100c5460003d81c24403170a80440350b0f41400410a105142c100348601c0070f240021841d00d80d03a607800c020800280e50b00200282c91032081840c180b50074000444c0742801420350080c18000d05d144c0e864a00003041040c1c9840f0740c1e0b62042e045010340319100003900c074440040105a024100c0c05803040601d40480c40507030085880f42403c1c00f43e860020201c50100b580103050760400c0e41c50b0586000743d2101d001783d0b55610f800742c0001c24500311060005003910401421081a60305101241406654080458003122800c1c180561100c440d4100540240b140721b00c000c0d0305200da9400d40100c0d6119a0314544600c1c02510100000c80d07440c81d0090b100e100c121004000210100010b001401410941c8018540058020501e4102c903060340c2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 94451960 1250 94450710 94450781
    0x4090b010810050c130506030604090816020909010c0e010813050a11030d030c0905130204090e010e0d0503040201020a032d030b040f150b16060f1a010e090a 69
    0x2101c0360018185119400c055010f1140c1210012031600e2500644914042c066021401403e110710800804200c09a03560f030030003000c0c207800c203081e50350355040306464640c0256410401c038050114080000c102c580e0602c10410920340307544502c3d07091a28500110f074001d200900041116904500c00c1b07021907000c11803405100d2103140801c00c12841001054505188810000e08040c2085850840360750720060500845000766a80c0c0c40c00f2080391710b942e000e400303940c2129441a02e03040c0ca2100f001c405407c001d510404403419100c030180082c04c100c07024402210080d001d640501c44106c00a4883c04421044810700c8140074041081055030390321600100c0b0032030000035107819074480782d454280308400c50f034140030808100203a03900c0041c0e0400f011030300ca107520006020464420340d10551207135003c09944000300304404118211410001e021700c007185203940883c100306160b5035006011100385139100818964880c0d45041301a0054910b20191007200251a2440710320303054000d405 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 94453210 1250 94451960 94451969
    0x504021c11040e031603030f09080708130b03010f0317090607050a020111030403030e09150a030b07030b090105061b1c050903060a110403080a2c100e0310050604090b01 74
    0x210461074503080802043d2001c90000ca40035400420414110346900040f196a00c1da0600300403031058500d5400c50700800399243e010b0500000005d200c010091407000030038030401c101c255190b100f41c680200070a980002d01034040b21203e1960240081581040349903003404a20420500e00703009040031503140e41100c041202c00d503200600b0402103682094040c03034103440100055040c603107180c40c01005c0e10000301e009030003041c0380d6012623207143c01c407030318103954910207006501e4032070b56443d00c00e010040460350400004e10b04460480e940c58041d000070304032000141900e0038800626134105182c2c0c210524444a44100099a00d1501c0d05200350507209801c0d40b5015220744411080c54107182d4010622400285400c1c9107407040b8907040241d070162a006000c2a407036107032189003929540346450b01d4070f1a00c4110441c10980003c10807110042e00e106035040c0017654400481079034490380b0454520343c9904083c2011003e0760307055005c07a9000400034030100710b0405d640c40302c101201013a000b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 94454460 1250 94453210 94453223
    0x13030207140a1d060f040519050c04050303030106080703060819030333030b06040c09060f090e13050c0108150103091505160807020a0206040302060a110709201c0504021c 75
    0x2040013920700121000ba000e20f06817001e0100c0d1914068060074001c0a004141d102a5104003284a40340b2400c2900c014010260890341d4035616200301038500801180c940c0006030505401050b003410105070b8011600b001100c133411a0480c3e40c09502074405080c0150a05804401015068924403007814032240e4000301190700904600308aa01c03c20300a0070729001d0381c1440c3c400c040d000d0381321103188200c03240b625182d02c44956041045412200d503900911480540340240031415901e0745100c0d0784c061040c022030301051082c90055400d14811910010351491081500341694040e4000f40016441f540c1d05401c0c6800c440c008c03200301c03101a00d010200c80124124001302ea03800c49201c0390400100c2c0000c040b60915540080d40070310560000a000f01c5000c84c40c0911940100600d5901e00c0c0000c068803026034071a0800c40040c0b4034055151540d4102e1002c0c080c04a502c0000c4811559051803000c005502a04240d00903010117003040340c00018031a1124040e0f80540c0c00301c01690722800 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 94455710 1250 94454460 94454519
    0x21080306030c03010f0e10090f08031b030a0605011b1709030703050304080102040303080105190303050703032304060f0204050d020402091c061b0f02250b0a050d0513030207140a 78
    0xb440c6140c13807102c247c902c03150f900e13180c1c20300d001c070301e0380c140c1c0380085940005c00950ba65200070008212448a050760740c503201022040c0001150540c200c1d0f4103449087c1e0380e00b4180300040c0740900d046001e4020107801c90400b0350040129507904401010389050140c1118005966961590b14551095011000d141d501280510070143d10081f03003801020b086480f05c000719801407040f070030407000f40700080a010f800150314003054007a401160181502c550b41c160003180c05020520101011201100d40034a07084100d00c04840910949090b150090201c980507641a82444025800040301c5a8054640304400403c07103c061029800c07544554004100580401d00e0710141050004200c004e0208481c107400d0041d0340020203600603802101c441000d4a541405015402d010b80c100d20081140000c1d07003400240c02400411410b03014120801c01e654840380c641c40d8201c280d0a0080041c1c00c5072908201a09481003040a0018020300084080e540c03130301c1c84a40480300100f028140b0300e40381c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 94456960 1250 94455710 94455731
    0x70309030e060a030219020102040b03070513180f0b012a14010c0914010c0222110a02031201050306060306010501080703021c06030213140a09030201060302040905150121080306030c03010f 83
    0x1410307008206d8440f40000d40c1007a04001d00e00b03856020040c0004104040420160b07800c03d070750b5444070000e009107071807481c020f144040c20002409111800703d40560400301c240c52a54840c41d00c4900700c2c03101c00c80c0c268862000fa460544036403e43d10095640003e440b8508403005000e00c1100804169600e5100285103051040b40c20304000a8060b4107000d28107400c8405604da840c64500230188006000e900301400c00c1e00c07100141072210588100440c0070800c900c0c440d4000000303083c40300401c0c2c207003201aa40e42042660361201146d003107800d504110010801540686a4103402980504001d820100314900f40f03407103250a201c0003a80b940c0c5032401001941090b02c1000c40d02d0401d41820720851881200203800303400090421081e0565500000c81898400e51000025590003802400041041e0a03d56038800c80040f43d0b5020317400c0308000090b1405101c14010a0100820052211058a4803011004c0c2c02c010000303501400307155000341843c0e0b0f081c03252518000544c4000501e0107042d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 94458210 1250 94456960 94456987
    0x70e040e0d0f02150c160f06090302011a060705030f0f1b0d0f02010209030a021005070203060a0204050405010b030f0402061b06090d02010f020703090e040201030603200102060618070309030e060a0302 88
    0x70031001d0010941501d0a000c03000d412282190708020f1000000120304110345850412604441c074050b194a20307100c0034102b0158103400c550160801600050010b01020041010901c0741c5540202aa881000306503441801b00c400780c9441d5065030b002c3c6013441307000b04502040704020f10004d520740d00070a00143d40e1a810588144041070746100031828054050003180c0c0c3c409120750081d1185c00b441440c410080e118000312030001b0ba0140981d1518107007191030300069040341c0034903071040c0d00b0710001085200241c010b4900c2a484422100c00e40e880d0342c0c0034041a0b600200b40030060300050442e000c0301e464100704a40c0206894801081d149000d0714000b801c445055030030b1552503004200d804007207584000c101c4140d41d1550030b01c0c1c28a803102d20059005100540c402401d00c00c2e03841d050a540d4040008a0456020031307004d5034059034840e020822614501d640705414030782c4035000300e4442442030707111841caa4400e082c03400305900300c2c90018140303400080c0b030000000c1d000190001c0c09001b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 94459460 1250 94458210 94458223
    0x1706010614030106020a0b06061309060311010804020a12060b09010305030a0f1b0303020c070801051e011203050d0c0908061311090405061807050d060606080717070e040e0d0f02 78
    0x41d09445076042d941441c40082d1242c034150b501501c1509844045920344d80d0381001c1320f4030a100c0b85002d007400381c1d6400802d405808503120607140c42c81000134412081d4084c04205120302d900a01d100e03405403e0075440c0040003c401d100b5104103686000704030681d2504c4a00b41d0180d8001c6000310b44896103035200800040700d40103c0020005200c007644100658803500d42d84060741810b001d070b11a9401101c0074034080240d03022200c590b080c8000d0008040d51400c240104071070700c51440046030b0300c0f20982031894068490080000c3c074208030100c07003a001c1d80c3c050501c1003114a00a4083d9a40d01c010505d44401550343c6030940022401c20010002400c4800c809402e0582e12514145000d0329201d444903001030503041700c04190842017041708230610180000d0180103040110124840c100500180036901030800030412074004504080c0c090b80009028404940e0403d103680d542030b404940e454010f03245035400bc0c0e120b084c0780320300310002e1155030f04103107050380c0b1060003201d80d0500038981003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 94460710 1250 94459460 94459487
    0x4080604230703050304050409020d060c09050907030203060102120705010b031e0c040e0a061d06010902070b0a0516030b010504050d0f12050c07031e0b04050f0c030d050d0f020417060106 82
    0x1404010b04100007070700841990b044540484000820f8141400440c4190390300d80d80043c030240c607205d82d50100c0c9410ac100c20096880c19943c0a8036031f92645401d500304d00c000d8035941c0c0581d1056198400312210f0500402c9414413a03000400e00050510210b850300c400402c141400b01002e030100700c03019000700300a5001d200d0403141480482204110135859040b210ba001e8003090300c40100c1c0001206526400d00f0500c2110204d4420f980e480d68600002e4001080858850752114003040c6e0038035076406828011201d101545000d0181d44006400402000d00164180807042c0310024040d554901300326490f50040c0c07103241103400c0c0c81c0b41c600b104d04080079460084c0724050003805114038001801006807540a000150780f42c04883c20441480c0c0c1c01c11004200c514400104410040d0115482c01c40303e900b10119440611407604154031040b8400030a80000e4040c03000382e007604a19003140380f50f001503d500505d019107800c0ea640101c0031510782d82c04298094401000510342c010340c81701808 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 94461960 1250 94460710 94460713
    0x4180e011a060306120c0d05030d060501030b1c03090909030903020a0f0b040b070302070b0316090605090310022a0d0e0604050f010309020102010b030d09171b0111030408060423 78
    0x9810001c000b03165404054206402804803940b207032241c2c00f0801c0070307562030a00240080d40f070f4001460101c0d03890f803181380040c203880c2c02c001002500b54004c4c0910542400b0003440607025081841c03407140c22a00107401a400c1052000300080c030041103114420710380d800b039510008561f0441c014040031a40300e40c0100150912950204000c4c80b00ca010b44059501d040b04555032245141422803270300c072498000b41da40180000a0141c5000801080e00202c0c420ba10745e005165070b00e5030140d4917030082d6524076402d60001800c001200c0842d90061225044541c0b40c05c01050051170440710b49440f4002a210a41c04068002e0705180c008005009407501260030501d01b84c28040400d14030742102c0c04260605849800070000c6a00039081882c200c00064100e030141d1569440c0100545039921880b0920001c0c5502c10680d07190108480a00b000d80c4000d04404803800c0004440d0500c941c0b640e504140414072010803050030a100c000e005a02603181c42c3c0b91888990000000d002a00c10445c805 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 94463210 1250 94461960 94462001
    0x1503140f0424110a03152904030516050f01030e030f07030c0f0305030912040302060d020c011416030b03030918060d1407060801120b07030c0903020306010906030605160801030f030504180e01 84
    0x10048010000c1c7c4510b198410b80d01c5440705a450340f4103004e544c000401074001e07a001030f4070000301002e512040760401c8506c0d0310041c00703100c01074044601c00070a14032281c00821400c800f00c25840000c1030014840e161108440c08503403039072695000308180840025200009020303048200300440000304440103149032505183d940001c403e480348060750300080e40c0200703910714041001c5d48454030101c0d054048840a2924014004040b1801402c1802280c6080018003150900006440c5285009418418211403400280313201c40c0000b010fa0b0307171108482404100083e8160500c0d512402c0503c02031070441e06000d005040c210050300303c1102520141d178484040b880030b0050b141c108006040004842000044c11078440313403d9000a901407180c1000004c81c24207075444001268041c400802c8241ca6607010b407400d0791840e071100f200181e6000018800b20b00d40e5490380098510904001d80380c5070b81c4202e0940d1880c404080000c8040e542c0b0111414550213000d142c0c402501c22050014 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 94464460 1250 94463210 94463219
    0x13150203040603090c05030a05010b0111190602030406020913020403022b03030b1f0e0301110c03030f0a151205060603070b0406140d061503140f0424110a0315 70
    0x140ca00481c85482e08041c4c4403844442070001020381180580380140035070b01160030074181345000c2c2000c844064009200c100104244e4100494491500114800e0030304001a00e034907954040d42000c1e101b603d1460382049100165034403428001440101c4100c0544c803640b03180108424503140484a0a0060a5583c80120700111020610003640d040c1800520283ea400114658240e0201c20100c00804e110001c1d583c540c000d050010740e40002c0b00207110340881c070510190315018588481c019580113102107154402002d143d1a44003080b244002000040001002c0b0030010550140c403840c0081d02161742806000d04c903071580144150000d00941745004a15016841944240801c102c40c0303c0b00101c09602c1f5008851b002c19001c4c000340a042d4403002800d00081c2c2014201011901e840074580800c03c120325111701c40d120354198000c8540d1240c80340042034400c60220380e58402000003240030311601d8071072403500c0d0700133060442e00d402281c00c018044401006600e035046108020401 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 94465710 1250 94464460 94464463
    0x1d0613080d180c090e1b0303090907120203010e0a050a0b010503150a05040c0816030903050406030504060b040504051c02030301050306040f0c09020d090218040f060b060c070803131502 81
    0x810300701c040c041c00600620b0501e4505444010b80308024103e180c01c08001070711400c5900581c0c0000c420300b09940c02c440c10180c1e1458480318501c0d2440d050742043c41114981d1030504081036001d911800c121007a810442281c6040b0b0307000341c010390b580e500f500d030502100007854030402da4410800d0b20104005000c44c00040e2040c040100041c101402c0401d01e1501505c035000309500420000d442484920042c0c080507044000807180080e10300903140c8582880c0b40300c0c0c0910400d082e0507444a44c41c280c1046022009000d000744166007540d02c1e0680407005448500c40d00d44654000d2010704128000d0360f00803100c0e101040d40d003504552080c001400310741c0d40071071040c1d0842c0d488005074003802d54915200544841952000500a00c0801c030111170100d540c100350980c9108840043d95a03100714510806060240c0d009021000f0b910210030002c0c4483c0c1c00422048002040c45040000303043ca0b4603d4011241c1144144d43c1001c102440341100450200018114810460300100c2803c00000e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 94466960 1250 94465710 94465717
    0x9140a030b06030f0a050c19060804060b04110c07080106060c0506060906010e0310050f0f070e191503091b03030c110607060507052107020d030b040f1d061308 70
    0x41c01c2108000c02080440d41c04100d5000c0055504040d030309482d4a60800b03e8890583d002400c0c0180301c1d01011810200c0d85143e000c0c00d03183c198440303099580b85c58990718010080703101025006581c451115240d108100b001c0e010388100d0000a100643c101040d56003591015031120f010300000400c138000003134001c54802d074400c00c185c406c641a031b0f0303c1800403151011500b091540501560407040160f2800f500103511420391003040f0b01040d240d55030026100c90080344c551002846206240b8078510313003120130144a403c00d0b064140c030142c803038586242141000120b000800d0782c8440880401c01b20402e0400e0401c10b510308403001500d50f03200079002ea40e0b1840006c15100c5c5000a44d21031396075a400341c0d4a480d4202008001a240c5900e01030283d43c0f1034003c000c0100642d80040070a0380ca0f014031144a5444c90303018122b4840010400c0d0050000c0b0041c2581c050340310300f08441041e03450303c5807581d41d01c5099200300603260030900340c0742041c402414503002458000d040301c01040c2c00000301d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 94468210 1250 94466960 94466963
    0x608030a110703060608060403030501050f010c0b04050705100302120604020f030609100305060112021f090b0f0c0d0201050103140c01050f0306060c0114070e0d1509081e070309140a03 81
    0xc0407058005040c0b1403140c000600d180e16201010507603900000d081c03403150b803007510104126600c42d0100012a03508450072400107000910060000c0d100c500482e0308940700720f0072141700c2500e030740000c2c0e40b1a039600f03280030009030301042e546454a03503098900c0e00a5801c0e64210300c0c2055401ca034407940e02c802054540141ca061010504070b2422680c41801560030600381c84a41d6180e41c1c15010400f1100d0059102d80c21850300d138103640d01c110030054401c5605440b82840c49141c1001c0f00480c0d0004a0f104000042c144a4144940c5052100062505247d400040d4942c11454260000ca0360000b89440c8c0798010340c40c0d008243d80000403146d8070500c060807107440fa550100013400030b00c00c00402c00059420820b034a0b0f0184020035495005072090380711400300c60207000038000340c001c0124020300480c501d402ca1200521459100c0380405001d010f04a28081c4200800d550580100d8030312410703480002024000c0c13641c0061800003030001c0080e00c4030030041000c0061a9000785010 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 94469460 1250 94468210 94468217
    0x10605030612010f020d06140307090e0f0616020f070303080c0d09050a0b0601120c1215030f03090518010501080610020102090a0b0304021203120c0d06030c0306021c0608030a 77
    0x41010759644001402c050355440e00240030000d240841e120194000380700310821036003401d00c0401e02203050a0030300078074080507001b403252524025215014140340405030000b4050725030800344d11002448054401d0800c890b0082001001b03803802464510f411855500c6d540181505100103540000c05a0304200c011076010b886070005007c5000404000c94024181d20424120340108030494486510400c0c023600d0300e403140e555140010055a9483d0501000100080e003511407a1005038400e98041380944241c80d12103840f07680e90403031b801e42140d007580480c2100030100605e20301698005044c034803203040f2254079454100017130182c00010f441140f00c0e041400e5000f0050b0701c01d60581b42d51010080c511215140e4441021250382d0003950180d001f9100b841441103054000000c90340c2a040d450340d00740d160f0352688807088454205600000c5c0898035000c1c008081201c00041002a5004210043c3d0300c0d0841d000e10003200341c9000003c1202c50a001c4104001003000c002c4d40c02c911900e08 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 94470710 1250 94469460 94469467
    0x7031b030203040b0406020d0f050405030c040914150a051e07050313050706090f090204080d180321020114060906060d1506030903090b0906180105120438010605 71
    0xd8207a007180541e4200c1c48070b5a0300400c0028200780d0002c1d25010b020110748984404403412502118107100b680200b94150b07105881c00066400d065101600703485c00740004c1c898180040c0c114600382582400c034400700004031000d0101c200501e100300783e08407180e03140840fa9929800c0d580420742d5001403440b0184030001c000107220052060480f03801035808400e403902c40303850b15806402814039020302050300da03500e00017003040320880c800c03181541c0d441001040c01c081505022a000c0e410300002c030b4100b040c40352001000804101084140e45181d0300c0c92100c08074503090083c00c440304050341c01c0d4080029001d10030240c8030f07003989640116003070f1025a6100d40a0b40c08a01501011000c01c0954003a0b810000d51998903601c503034940c2c0d1107552145091584c1d106014501e0299480250340035000b0000a1001c41c00800c8a080c450307010f050190401002403000300f0a00400c0364192040e40d030080d410150404c2c0941d43c2c820380700c102030043c0e03d8824407942d8140e50040500030744081c802d000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 94471960 1250 94470710 94470713
    0x709061e0e064803030117150c120c0306010e010315051c0204140f0a0c0c020303070f0506060105040b030c03040f080d0c090603021c050a060506070b01080607030207031b 75
    0xa108844510241c0080c20b850001000d411914101c0991801078901c1007041d5210108220200c03d2058048140c00942c10742e402c1810160449170805180b01e1684221080390303c0040702d42103000d10900448850603180d0f500c2c9106001c8008000300401e50380c810410400c03d03181c0c0c105c100500d1641081c40c00007000340400d0858920010590803c40e80300d0120701c0104603032903c071810704803050b209031350038801010303001400c1d80402c030250b803587d02c00703030903400010b0706102c1030f40c08640c00403a030b860140c1c0507912540220381503920540f130940d140c9412000390001c0c010100035490300300e5428a0702e14030700303450804864458080601980d5520000002240c14441c2c4031001400d0b07590000341059844405400e0b100c000c2665490b848041142c8140002d0414000e10030307201c0c00c4881800400a0803000d00d4150f00501000b0001c4c455981e8640340132076645c4800000c0c00c00daa1241a4410455040c001c00518101c8024559400c060040001c00d00281c0d0215201d2510a90b141c194440811039 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 94473210 1250 94471960 94471969
    0x5060103021b340e07170906040c1a090105090d06060b0d050702070b03012603030106020a0c08030304022202071703060103150312050d020d0c0203030709061e0e 71
    0xe44110242101421040040b12080030032681010010b01c00e550301d01c942500c8403101249044100c3d030306151080201001102c444901080e4026002e06e022004c3ca511410840c554000c141c400c00440c2d4421002c00003080101c40c0140c000e004035220520181412a031001d105100c1c0b44060340c10410080352029180d00c5403540c1e09070883e402181846a0b40d21042c4400d1160040790810b0459414500482c0d0510300110b405410340744051a024950ba084c1008038400400c0000003241d20900040c8034150000c00f4400b641c003900310b80d800740c4001c410390304158960541c071b80c00c012041d800800c1407000599400f01d150340c1d801d0482c6000340128504a200200074020500c0141080914201c3e0203618403004004600c1420241c904019200440001c01d020303410f9400000e003203420200c620482140920042c10100c1c1c286100946400c0ca46214074003074980000200000da40081f06014280360420b001101400da986011280c8065449004c1841d41036607421406128000c00700c20907070340310f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 94474460 1250 94473210 94473217
    0xf0403080403030513090b0a0302060c1911040e03090a120203030705060406090b01080318010e030f030f03010e090f0312040c09180210030b01051806070f050c010305100501050a030506010302 84
    0x4120500d6034666640c0d0a024002e0ba20034140d42003860308004001c940079120b44604010110041e00004c0c62605590034450305a0003a4411006072080300d02112094000c00c418521442c46a000058500e000c24184400c2d40c0c42e4180700411508180403880b05902d40713044103000c40700c1045d1281e0b15001c09002090035482154006002d600070001004203002a43d0810588103101d11001e00050703036600d04042d128003401c242d4400a094500010b070180d84034076500074440a0040907640d0070380e410300200c0d1465002983c000d1100030003100401c01421004032282d80244000081c0440034181d1507031503101e01c6414003021b40c017803201e00401e060000103e061405803a003014100b002d05080345002014240c421001c030700c1482d440103d60501481b81c0202e5a10000686405041c45442c0001c034808010486e261a009141842007802280c1d200348642c0320180030340e001d401015030500c00101a614002c0030001c00a40855040200c1e0364044210f8070a100304e07280000d0300d5143c64004901a12 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 94475710 1250 94474460 94474463
    0x20c09040309080f030301230d030806040e070306090b0f010b0706240611070f060e041d03030c07060c090b0d021308030a020d0215060d0f030327050f0105040b010504020f0403 77
    0x1ca91349850010100010085041c2d03081651203a0000440720900842005d43c010f200382c00904000c5003d00090268000c00d40044004002181c02d111840600b890a4020b0b8000e0303803403d44640b1848188800340d00d0268210b4105000900d09605102c0c0300c140f503200e007400c01007916503141c07000d1600b541e5002c140202c8101c40000c2042d40b0b40c5e00e4078000d000303034410503071404070f8044d0f45030020715640b02d500303031004a41031a05c07a11500d14400007000001c10074450349003020320f44d000301104c0251043c40210300ca095101d078400e0301d66038035041030411034400704410024082c441c8420710000c0c0c0a84291440c00c041d408025035908840102c80110903980c0e4040040b41c48082180e80c4a15008551400d000c5030640c02c07200c43c89512840b2450411050360202e03044003000600601046a902450440030b029080c041001d552007400300740205080340009940440d40c2400e0410860107100c5612003c401c2c500074002814903071909603442c0010f00c2000e201c0e590024410070501d00c0c1109541c02036 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 94476960 1250 94475710 94475713
    0x7060b090c0c0d170105060f040801061d0106080c030f06121002040914010b0406030203040c0e01030c0f08061621050108060a0c020d0e040b040b04022a0a03020c0904030908 76
    0x50915590071001a0862000d032034243c06500a89000d5510801058000c020b00d200030702c8050740b0b030006000483c1c1c0001e1106052900403c80890341e440240140d0000b0700d480c01c0c003804200300c14190240c2001040e0000400c1159550a00c580408207200ba25005484900c180c1080d4079510005509214540320000540c0203246c20344131031a00713075805030003100e10901083c00600c00940350800001001d00400f800000244000c4c44001d1283e030244d64864270400740c0719943c2c1d440c0d900d5101444004d074030888021484032010b0208881c1d10320644c00030000c240003091141401c8010611000004054408101e000203000409040348080a042d000c5984803c0143e0b51b10740c106141c0b80c0604032941f628690038007040d500c0712131001800b000980070584d1b03407240c503544140802c03000d404181c5401d54010740b16402e02e4036a580d188000c0020904021001e060703152030f102c000d4207000c0c035030000e40015041180d03c500805d4010035601006c00c41114800c1176661180307415030715159181c1160000c0d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 94478210 1250 94476960 94476979
    0x9020d03080402010905010c020a0e18030304063810090b070303020712080603060403050901181503050a0216141e0d021002040303050d0b0a0503190204110a08060607060b 75
    0x6050704801454055030003030381d4001c9419229401916104100c40f8000d4000d4440e0404003c0035520000c0641c20400c0d5481c5145810b540282c0685190030658003515a9641c03003202c01c9601c00e05101816007140310002c0c1c070440b10000b078940e60a0f482c02a40c0d0340d000714081100305441c644250300001c040c20b2400c20030707030302d40d10740d03007402402504090400c035a000d2005060380280f03401591080d00c140030060041605a035281c1e000c0707605800031074003d03052102d40e800008a405555500e0030180c40f645110f001c0040c24028002c040c0c1e0380103496016140d1040024142820303141502d01005130b040191110340076401c810840c0b0389080d148109a80c540d01e4580c48218a201062410079a40f203a802c8400c1090200b036088124030589c40000c01242c0d080103c201200e15a80106104260003402c41d005d8170765800100307040c11807203d07840d032680004000e85401c61a00344607044040b041501254100840c002010300102c80280850303115000219080f0704004080d040840b24a1014213803200c0c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 94479460 1250 94478210 94478213
    0x90203070f09180816060e03040303050d0b010e06220f081f0c0203030106111011031b0c2d0d09030b0f040b04121103042912150409020d 60
    0x401c08003402074180711414070280c0d04000d0141d2400300101034000f240b240c94400801c450441c00c1000000c120745c0d0588a943c015200348017480034000540c00390300c07526552031400d0100070456031007083d41c03410b00ca401d0719034040c507454920544008000180c844c00c4009101c01d11112100c6240d48990a40c0302c0784e910100700414041101c05008a010001035061404464880180c0e03001d0b542400c0141d00031b000400449100702c14450360301520b003041e62802d000703200350700c0103a4189100011500000209208094040c00840ca8000090002c65410f10031403445441d11842c0f04400c3c0301d02984046045800708040718803140d80ca81001c02281c0360355106d02406020340c102440141d440084400001e0810025484081e126690088440308180e4442e561030300c0f058101c0e4900000c100c031004042000c04010401400a40014103040755405203504515000000003e005804074109124200030000b810003003540010020050040c0c90b0103180c0806c004124401c000396101e15101040b50 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 94480710 1250 94479460 94479479
    0x90c0622080a020102060c0421060906020a020109021009050a03060c0201020c030403031107120b070c05010e010e0c0901150f08070507020a030602030f0f070905090a0603060903200d091809020307 86
    0xb10319500c00c0e000d03103a0955821711040428082c038031406100c121182c031980080c3c0445200e0301d003518030480e0700103600356681e142c80080360401c100400146c1c0d940e040340ea00354645030b180703030a0384280c0745448070819040202240b00701d010b070722000b4078440e1240003524009000b90191000f4004220490351243e94030b0400038161700842030021014003c030700b4041180795100c550225015040200799003907858100d01112180322501040c1c60315580c980d074250300e900080c0201c0c00c005801c00c0003000d0001d00075040021000c0d040e0f06c0301d10a158006102d018441d040306811040200c14101440140d480d00c030b0585a40c070a58400a50001004001204210380ea0b400b0f180661140b003031040441d6181264164141303825905180800c010400c10441d92900001441e4402c07191240461600e603240d40d04001d5500803801100850440d8032038a590340740703805803200e5090b00b04008240c0c640c645030000e41420460f020b0149018030500b00e0455035545038120f80c045940c050304030b4039002d5403441d001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 94481960 1250 94480710 94480723
    0x80309070e0108010501060c0f031808010e071202010c0b13080403080406111216030e120601050907020313060509010203070b0c091903020603010e0907090c0c0b060108090c062208 79
    0x1950750010340001180c0810140f15043c10380307002d40c03a604201c2c8a103480b03160060400318030031420800d01c0000c11140e01c030382d0046d0400a0881c6000403400c4601c0b0040c29041900d1900f040206105a102c1000941c0c4c2c4050744444160304010048146c0c1c54010100031480170201024061050019002013003000580c02041218455603813565400701e070391501511002591003030403803040240003440c20320118400d00800a8402c0c00d000d4180d207071540204030000094030302121280c12980042200e8140041c1281d408052031000d1840d018001092030a03410160060000300000070400440c685d0003042101c2200d0b070010900035042c502201d02482546c03080442a0190040b000000c4104a204204ca400e0780c1d40202010300b10f80c20240030165041009020041c24803410600003800702ca18401d6650001003035035500075101c0603003030401521101030030076810400701d0313810410a000c0228032180840ca088880c40da4851105005805003c001d1501002070340070390300c001a0824000030b16 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 94483210 1250 94481960 94481969
    0x11e1526060f07030c0f090b0904060513020c070501090b0a05070f0515100609030b0a050403170f0a060b070b16090503010606050c0d050a0c060902010c080d1a04061503051308030907 80
    0x1401440b0051300204d80d06911b14500c2c4001c0350070141c0512030b1041d403401920707210300b01400004036180e840d80016030507080b10103100c0c020707a800605c2c000c0340003051144c4005070800f820141d02c0a460b01c1c121051031306c24401f08008004011a141c420006d4003400d4035031042c2c001080701d031004000700e05d2644000040e80c0c0e003000300c8203e10300024250302511a0204aa800c681c80e01d129907100403124002e040300800072803c0050a0401040300180c12055a0042c0000410030040d0700d0b00c2c10b090400c8070250b810101c0d00101c180312400c001841c4100f60b96200719110b51480c60301810350b005446e1620144c0105034103500b03010011031096030060140a50b0310b1071200b200c0c181c002d440300644007032107010400f4002907440300c074060101c0c020b0f070400e40c0451f1040c9082c0b0100f00311500c03610215007003003106610840e00c0340d0384040d502c100d45d03082d030120880c1110200559440c181850b4407036005a004001810749400000d004d1501d18050956166003000e283da0780d03890061031040d161042c81c0036 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 94484460 1250 94483210 94483217
    0x2100c03030908040e15040e0703030309110a0f090b06040b0306010e04140106050a180602151e0f01080c012a080403080703020102210603070501080c1902011e1526060f07 75
    0x12428041c0307024087c42440c0e0000034081c9c8103250460724101c02808807050103903840702001d06400d40584403141460020048040312041290030100da400c191402081814462f00052000f4403e40c0844030840e90095070900303052204a42c1140410050b02c0c0c0e070744800c040c103a1210000110301f9008002410740c492641d80d110000d845051a140004526009400047c0e0002848203e000454061550403c5190020034054131030403403d50400c030001c80c1d00000e642e209a004200d4100100940300c0d500609003000703c0c2100801801d80110b003028510300d401c06084051700d90501502000b100d02450700020959502c448600380070780070b98000d100314640035030100185403404819440c214002c080003030140c5055031400c401100c0e00080a4010480603408024000c02001408040c41c003040b00e035000440d1010540030080700d245d040c9041102550b04040c3d51000040c01304e2050816101c080b9090644004d00000d162801819070040c603500c1d2144006010800e5500d5495a1040c5160355 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 94485710 1250 94484460 94484491
    0x14040f090506060f1e0603072703030f051903051b04030b07110a0305090108040206090d1a0a0209011413120602041a09090a240b040e0604020702100c03030908040e 72
    0x60900c030002c142205d02c5500d5070202d103a011080e10700301c0015038000703025141a403145159110b03e19a88804501c0ca00141c0d40203030010003c064000481d01b00c5422981030075400d00c032a4549215a95070700000c850101036032800014108507004901c402c491103405034160307c5540341d14015510041c151262004074401c103031391800790400001c01680103545940c400d03040070700100c01900d4004014204907440103041c03045d4141d0f901c5000031924940d02032451a01070181c1103242e201c0700314000d44a03080a50041151200c1c0d641c0103003110f41d010652865072659850001341c403111a0406070020611001500010010f200541d000b41c810303a0001d00c0381e8412410101003071074291040010003500b0003e000c00180c015520b0794051500040c1030790310001d10101e101c1850080798450f07001802c0044020509100c41403e80241c1540048107803011842c10300160000340f20102041020300400c0300358420501014440d4100780c0700b00754011400c0f07071966200c85882c0382071003049640b405250380d03d1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 94486960 1250 94485710 94485739
    0x207050f10060b0f070201170a02030718080a0b1306110c070f061403041401021c0b1c1203021215010f080709090207020102150f010806010b07050714040f09050606 72
    0x1449000c0490b881c40303d01e1071500313035510b4801140d504043c0c3d09038107001940303944c4110141000032213403113502d00354801683c9140c11000940910f10011186021941c802e00c2886808400100032103042d41140d4003021b03d80d552801d01001e04d00c0d01e10300902d66400e01100107424041900900102c00400c02a0748040c1c1c1c41e00c0100382c201c80702e8401c82c40066145c0001100c1c400d8418025504a4024841001c203d80c03152501401d90b84950038034164905950f10541c0300103040d00c203102d2980030486091a001c00c6220b4280c003181000c40b0050310f00c1808841980341c56010b0350444001000c0800400704c03901d0101800c0d41104003041c0704d42d020600107010032102611a0159078413035100c40c0c0f100c24416007404490002504507030003c0703065128a140324201e5151590380d40b4483c00c1c01c00c075414080d604005030181020707010b038084004210309001180028002043c0d0340240c421008100c104000703603000003000340414241c004e1035180343c10042000d2100100e101c51103441c06680a40c48810310 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 94488210 1250 94486960 94486993
    0x20a0801050f010603050402010e030106060e040e01090b06010323010b070201031b02121602091003110307030503070308070c12090e070906050d02030402040b06031f051c170408010207050f 83
    0xc0301c1c0080582e10007801400114080e40c08190440c3c018541081c10b0103111001c642119a50b400a030089080d0324050006894280240c0741c406130010300030701c80740241c1d40d6005103120303010300404d0602d500c5911407425180c003040c581c43c20020030014410300c0e503943c411808913039004031401e90009040c00140c0780190080400c010800e241a4002e003500122100e0496043d00320400c56403021408825000141e03491a5460303014010000c09488414a0761400304150003858aa15000350082c3d07508101158020090383c800c03a405061083d01c603034404804966400e0807110003484044080c1451740c8080d4400c0110044d00c0702c0302c1d4810f4054030f070718100b942c12a03024400d01d000a8001c10809641c4052a000345400c9480508042000544840003e40c2a042100e490101f40680a1043c03c40e08410f885000104800d650080900100301d514410220420001034001c541c0c05507200d03406480d01e42110f000340943c200864403194103140427502c664060454000c188903d030000d1840c1c654 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 94489460 1250 94488210 94488221
    0x2030403120504020d020d02220605031b130906020d0c02030903010605030c060714010621150b1e0a0302101d060a020304030b070e060a0c0219030b0a020f09060a0309020a0801 77
    0x8006045e0024620164200500040084401c80c2c0210540b4000c1c14480e003000040401042d00c801c005c0383c2da500b00014545031400918014003240700d04000440d481c2c0300c83d01c03618030100b01004089080f160034101000030348102c00c010100c3c1131512a50301202c0c0d0b80840900810f2004074000d105040d62041016550340340d03c0017196000600300038110001d42d80080018104042000100b680d640c0e40741203008400592101e840e005130010308910801032104400c40d83d14980c1c0904000d4a80c03032101143c50180441441180170407019000d0001c2d94400062800440e8000d1008000f0803c081004000f80101c9488400d11b07920b01915121a1401400380d402c20783d46035000b07500709855500c83d2101300c4000707800d4000b8002400d00b07404051301c407100100302d000e945865804560f00c513441402801e01d030074220f00c130140050b43c0c0d0900000320380d20300c00c03a084510b241026071524a1004206064864000c94583c420000a480824140c01d90803128400f8021200e200000d03945003182426920b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 94490710 1250 94489460 94489463
    0x120503040b06040c1b021201140106080901050f04140109061a100503130227010603051008030306130203090309040212010f050d08091909051504060b07050309151c02030403120504 79
    0x500c40f05117440e002a864401d915407a0000345120740c002110b24015007107410303881e2042660180781c8010b1003a940c000d40030756000114080200014030b4207100418100d00c015000a14035900402c1240300d0030400d42121501d9504035204000701b10b4403110710f40081c441c168145009440c4a00304100150003101030300d01c20a002c0020b103028030000d40c06c10204001190580281d00c8034896401384d003420621800e8003801c5241c03800505400c0512030a4003420840e4401c6031707590301c00c10401074140c540c0340803211812008000583c480e00d61480c2282035000c5d440780143c0103840420901c01c0100c002c0600d034101c070f025400c0406140e48660901c018580d207405c014000c003c0c10803090b00241000e41ca80d004140a403e0154a220717100d0002a00381c842c180c1d410000803104141e80f1100d4681407082030f0040c852120050702d0b280f1f075a59840c1d00d90203148900e51299620218030603260313180004980c455502501c560744004042e03040c44000b50070070f8800761f0010300c0d0020508880c820302d00c1014000c0b07 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 94491960 1250 94490710 94490717
    0xa0e010f0f0c140a0804080a02010806090121030519020304090f02040b04030809030a0609030c05160503100203090102092d2403190606090303020f060705090603090703120503040b06040c 82
    0x20825610759540b15000c00c1d191002070301c1104030759400301c5c02e04800b50000c4c00110005d81002100b0703000040c800d52014054078030030307025000100055199050684071034030440d203146641d00c80e913040580c0c00380a461019008006c8200390385104907400b00051040d00d440c00400c02908492000b0038040740070720b00607000e14a00420013480841c17114005441001c800500700c1c1c1c40c42003190758480c19905801c100b10041200d5592000400200340040c2451115808105d0702143c030b00000283c1d50b5030040404c00b0701c0380d8000049013140e9400c0d01160b40c1c210024081442200348064a8022129140585859018224280042407901550101403520003159080040c04003c4010602d075002820070b00340300d603540e81c01c3d900800041c069080203004544420803070600c0d6007006810f040c031210240800e03821003010019115040810b0351864607084c3d03825501c1741d50b85031085181603643e0704090422100070a07a007490036441030055114038481d02d2030540307540f520400c0c481595030064404011 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 94493210 1250 94491960 94491977
    0x2103110d080c13050310050906070f0e120c0d05060f010b03010510050d1404060c030e010e03071e0f05160801090203060604020307210515091005010804020a0b0a0e010f0f 75
    0x11050303902d001e061003038000c4851050325a513640010b46412030044002d001c0c40c0e240c500700180c0d07400c14000f482c2d00040b5424099144104218004d00307282c44000c0b0705d4401c8100c6100041e1034030742004003502c4100d02030062407524200d401e08070340c1c0b40340031216011114032820000c1900c4504106981c103e44018141e1a00390750000419100d43d0030102002e000c050340c034107d000170f054403120418003c0e401a2000100c401e03207540002e05603481d481001b00180e0600f0750107500f44e1000803c82e01f10030b40043c440c3d051010500d100000350804014098248154404a00f05000380440e500150380c0400c9074400354642c0c1c40601c0350030307a401010013035030541207000010035604054000390340c0030b03c0724942043e1200ca043d4440320302d5501c1034000c3e01c0c5960394100308080403522003204a10114101ca0801d0a8600407801d60502e28280c01420f0400c0000c4e00401c3c21500c9500900001e05000d50b03950380c454503100d41c001c11901a10340c015000842d08003e020507640100c0221300c4001040c1d58a00300e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 94494460 1250 94493210 94493221
    0x109060804020402070303020903010c031a010e090105040b010c0f30020312090c28050402040b030a020702040f060905040c05101b080702150a12060b09040b0103062103110d08 77
    0x31742080031700b90301f0b06408000180442e0340a20900d40d0080301900c00050304549548800301105050781250f0600080d0141d080041ea03a140c00141181e5048030040765412034400100ca100344401802044a548807020a040084900364000080c50540d6103041414180e60007800c050b089900d40f03000340c1c0041110846203842d02e030a080c0d0100510086400641640d0007043c80603081c1079400365019002004481d040050050705002080100d40c00e505250601614411510000e804d840000f980004d8400454076030350884101c66817040c50400103140d491001d40050b100c00c9a089440c11081000811149003146000d81c07445025910329540d01c601c2c0346040f08000c0c0000301514000c0041c80100010390760803444a440c4110a000c440d103a440042c03025200d42415404480740714100041032145506ca401a203642c1d260885d000709040c014080183c3c0244074070341110711140d600026005810007402d48002800d0702c81d5450402000c0001e090903181c400c0440ca03080001c1c04c0402141c03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 94495710 1250 94494460 94494469
    0x504050c12090a0f0f140f1e030306010f1b060501030b06180f070e03030c0106060504080607020a12050307050c01060f05030f03120c0309121c060501110c04050a0f06081b010906080402 81
    0x2180640708140c1e2200711240d1140c05450070721f1820311074000c3e50196100400c072160201d501103d400400740110305508116001030f00040440e25603c01b0403000b0b001903c0f40780c00414606a00701d803c514104080e58481c10b0541c4540300c02c451842c018201c80d4511810b03944900c600134481c80307004036660010b0306d4644007250b000d2415480250704d444203000c0e40d140031800b8841e2400030402d41d1112580c40d441c1071101c504043c1700400302001d40d0000d40140d004210301c402c029440094901e002039582d0f5901105031880e008100501500358030780600400c41580c13100c0008183c9108a0443e02d01103031ba000a03c0e5240705100c01c0309500a620000b00d0b40c844044000b45400059110681e4a0b46128425440103038000c9641240000007658800404d03422500ca02d5015180a01e080e2100402d8403c60542da070003c441814001c558030400241404202d50200c41284038055003404010354841b0f200d9a031b2503840f9800004089451007070501e03903004440d1001199a10f0315910010b07642e640030031 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 94496960 1250 94495710 94495733
    0x61807050f160b061002060703020f19020a051e1b03011103070c030e18191d070e0604060f06030b060403021809070e090a1104060504050c12090a0f 65
    0x500601806000040c184040c20307014098041d034014900c000310910303003820030394000c0160110703004951003052018215404107045500000710f04001d603a421501171211500d01c00d024448031001101d407030074103199a0206014034990f000d04100c4000399104031103404c250403060f0301c0905c1e5030300900b0304101404400c1200902c202c0002c0000a009002c0105a03c0642c021541c620000301034211650816400ca41c101d4203546044d10a0800498551884541703900042d00149032118441c041407a050383c540c00910450340500d50184600c51603180c1f60750340d0307a614007540e0301c6416008000740c0d0701d043c24410f250403102242c0d1440c0582d468480160018003814240d1a0801c00c1000044013503115000351003003010b0581c01c500541d15010f414642072024680001d40e8000054040c007802c600e0006003440c0c403039008100b428a900702040001d004065603804660083d040404200c040032008014118100c4078001c4490986c0d034000d0450703142c0da02a000200342074090034a2201140c0f900510 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 94498210 1250 94496960 94496971
    0x8090102092116151d090109051f090209040518030412060f02031504180203070b0a0c050f0a02100c0b01030803150a0e060103230604230c1806030618 66
    0x19034044540300c0070380741d5110201d6002920030b80240342c0c1e0b081503250310544110481c000c4400c000485d5018500203000414103104881d2455202d1010a2038841000c81e0115030078000201e452455654203090b40183d00490140380c8140d291200269007024800501d410350803d500195240034140003020145412a00c415180c055550710a03070034100c410303c02580201542043c83c14403601140c1004180c1e1000d0485d540105240e01e41c490041e100090b400050701c41020005860b0042d90b80c044820200a00d0054083d101d80b0380c401e03007007035408541010301034020386040c07541240d600001d5513056910103000b0800701303c03100108003040940002d0350b0400c00150030042c4612036030002520000f01c0f50064840b2014000c107000340e40d81c151290122580b032001280a0364180d011244260410042c5a9406a62034081d02e5039080c00d14405000240c0441d44800c1071818156000305c0039030480d901042100c401740a00303035441d107814001c4e2480313200c000303004c21540720f1819241046800c01504 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 94499460 1250 94498210 94498213
    0x190b03090703120c0210110c06090105160c030b09061e04030507060c03050a0b0a0b07080304050703051b090a0e0a11010909090803060f010f120e0703080408010c080901020921 77
    0x3002c800901109540b40da240941ea640ca031100110b4010882c403854040000b009003d4a62401142d09201248034280d00604a503030644403030302c42005a8052146510710800c2100c903a00c18420001c450360540b0a507409120f8070b40c0310341d8401080170f5807500c00b80c030b0b00b51801d0002d0001c81d100201080e42d06502521914000782014000e035207903020f840402a08a0200b81c40c1d8040001c15520f40c8643d41c0c11000440b803400740302d482c1a40300d010610800d032024000441c0080010b082c03010803c1030f1001160b1220489026000803026001c4448646042c0b900c038940c420007092160040d8001c42101c0c0800d034015181811490380d031007201151010155061008803c13001410b1642407044189444c050764445581e494841c003046003c2d94014517446c10300c00d8204080390840da01c141e503110322407a0b400d03000030108001c0034064940b4116a0008180440000d40801c100d1010b4110800925060311030007060b4a503080454241d000d86031102e13810001c8034002e00502e824481c00f041d2104002d20 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 94500710 1250 94499460 94499473
    0x6030709090e03090d350a030f0b180708090703020f1201090c08010207030e03060f0415020c010c0f0201050603010504050d0c060b040204060f020f01050106091a09030a03020705030c190b0309 84
    0x10114030b400f003170541c054a640c07480d80c0d03100d1081d1500c01081c3e0680a204002864405840031441c0810300403821174004241c0d45800e0a20b0403200b0764000c101541c0700500744010244410700b0010080c01c12183c4a0014025402064054400058071019654010100c0101030601800d0240309000603031010103640d20740000300c003c212903d0605028000640025903105010704014100586817120b95020b58085001c00c01e03020007100030380780c000b0f512900203200c4811540d001000f03402003051442c02c951034110140c5000d5000036100c64660410740090040d80d485004050898100f12005003154100d001c201030818400d1f0100e1000780e02c52100010044408000301e0100e80142c0c20400100d0351201040c1e5440750108945841c3c2c1ca9808000e0080350f040207001014000c0c580329294142520060440b180c021140990b1000e41c406802c4544140c000e08009660748050f01c5114042d01501d050f105e424205405032062107211000141d20242c40c042d200051548000c0c004003080c00750301c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 94501960 1250 94500710 94500727
    0x5090d0209040318050d23120c01050105090618010303030506010c0b01030b0f011a0706091401050f0a0c02011a0f0102010905100e070504020403030c022404030606080c06030709090e03 81
    0x80d15090045000b0b680d461501d00007608440c200384d000341c20441c0320b143d00d29111800a20b490080d81c007014034002e03280c13804006404070f841c58252114441000407002064601c1410f00551001e070413140300300c404071110784414041c0010301708164440d07039044e60004014004240603800c05500b064062400c80303000040e41e201c030f00200000380c008031048940e400c24404203803200200c403809015092412001541044a030403104c4c8600c4400802d8680c6617030407107041c404054250b24244125030002c1c401c4d4500400d4109111404840402103071345090810020740b171051249038840c100703030410380c7d0f62400d00340c040140c180023440e8110704540d201e5610100041003800076461a0841c05004100030341049405030818085411850180d0300c107110802c0400d90140300201d04503010703107402c1001c2080303000e0b0056035101460507000d00703e0005400820002640d01c140d084810000c191180c0171200f000f008958030080c0c4403c0005600d01b18107001e4201d15a10588107c0010320489251036202c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 94503210 1250 94501960 94501969
    0xb011811190311040f080a060b060c0d0806010c12030504120e0307090207020307120f05010516090e090f010606020703030206100f0e090106090c08090105060909061b070c170d08040203060705090d02 87
    0x40307070801486d43d0464241107082003040d0042c04d43ca48001ca484509110f00c900310f080c2c1d00c1c4524050344082000781e20110b4402c0e402812582201600864000c44000300301201401401080c1da0803110141014484420103207e03840300b5806000c010040c0c5207092500c2040000381d0000382090f41e1501600100241503d90051800c004920584842030401b00a003841030842c0e8001b4a443c26005149885541e21603200202c00145e40070300b14402030503110410605d213041d100d9034000e0345540c82c0074004507006400084038000c5071700c40e03401c4600c151350740d00d900c45c0c0400d560722800c1c2e540004a08144000d10054410507400884074000042460f51216004c040e110442d40340f001059542080c420310660070b0003045d40c081c5003540d000c402030804d5000942c0e41c01d00200b101401d0104900034600c010b138010111000141c101c0300311034440e9280c0400c0844a120241080480e2055640c0d01c0445801000d15074455078004010301216501c0e040240c034031760700180301554080391010f003e80c016500c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 94504460 1250 94503210 94503239
    0x20c0601030b0106110106030203060f0403180e01090e0309060711010c0501050f0103140d0c0201051303080f19080103080403020f010504050d0507050307060e0325030b01181119031104 81
    0x42d5510740b0895140410107050300c1416082419103074144041800561800606150800c000b0b102403841ea03507d6007011260031441e0880c2c10b10a1901c10000030b060442c0502362030584200a008024044441e155a540c1c0d11601070f056030410014440f80000c00e05e10700c0c40300308138039040c1081d6010115a0b5142421281e04903031a0015100c0940144240900c110603900ca10300d1050092440c10403128020344014840c41c4001c3c1080b40005410550a040d158140000d550103005146c40305141c00301b14440342c04c802c00d10082c0d1001c0041d0000254800d071100c60490390455409880c03c1d0a54082c03205241c1e95042c40d6041c4401003000181ca900c64201e9000094003450203401014145010141000e0055115408019541c0f00355191940d0202c0c2d88454410044100d696003800b10003441034040d8a07600146c0010703102c0c0300006491807503402221400d006000100030005950103048402d024070540e1610b40c440c4c850910390118080c1d44011035200d05482c0c01401c0030741e2110114650716 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 94505710 1250 94504460 94504463
    0x1202160b0a030c0813060b0402040b0f030402130b01080708090102040b0309010b1002010605010e06031005120f07060c0c03030f020c060d29030c011b0501020324040c21020c060103 79
    0x21000201c007075940d82c0c1840b9805000301d0070315040031681440042440c1d5802e00c0c11000d80f006695030640001c0e039a40740d0480c0c009000121080d510b070350200c0d041c20300756002281e060b4080c01400802080140691150144901d8161600f40c03407034803410021a000e5000600130b151641d800c000110f9048410b07400b461107641400d0010030314109500502010040300a262401c1d60b0400c1405c0c00142e810010041a648050b54055240c0d5076428a004134422a503100503080040000c1040c0c0c1102c000c1041c03400c0c050300804407001103a41c0c0700101c80440d51b01e10064680100180c007400024440c05070f81c0380c421018411903261014400c00200d01e50301401c2e4842c1b080e81d580035480c29098014015806c0756001100540030a000203002c03070f4840d41b1400d40d1604000c0011900d02400d800300008511840d0410000c5403203240c2008410360804e070001030000d6801c2c840115140b907141600071902c00c414140c0da81d1800c401083d815280c50405100d010741c07601e0b001e12000700e0050003040303001c3c020b5 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 94506960 1250 94505710 94505729
    0x70c060612110111060108030d1a10030902090f0c030411040912080702070b0310050609130e03040501080603031614240f01120803070806010507050d020703050f0703050604120216 79
    0x1000b500002620b12508200982c0f11074124800401c100c2401000b556555004010b0103d41620782c001c2c00034200e241c1c07030806540881070741e0301c860341c003a41540000c04141c4241d40d060b41503107800001c4c0c82120011602591780401c204001400951051a008214000030f007001c5000300055498503500412110080c0020300c040c0f040000207541003200c00e0041640759081c2c1d00d1420500c1c50705452000a0103100d005000014100c10703a0384171082c41c6148070002050410491540c4086c10340c80350321612846002403100340225229145c0030040781c40e005001a9800c03204141380d030b940000b4010403048001c8501803c0c820441c1030928065108000d640800b105440c3e02c0c0c80c0200714440340d01130b00705402c0281404420000550f00c1740c01c503504007200b42070000642c2e0715400101d4492040c054010011f025100e0607401864000803401c0c20baa11480940d2140ca01c0392240303c0d629900d44c0301c0500180e00040215000c15000d48150f80e212409106071591100742844403a014881580000c800 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 94508210 1250 94506960 94506983
    0x1050403030b010e0310110903060c07060b0103060b0d0e070909030203090a0609030b0403181802091302090f150c06160e0402120f070201060512010c030b030a050303070c060612 78
    0x10141d06204019070700780c1c24203001000c41420307004203645440300c0d1440b0030300c0c03507641400c4030603440e07500300762000d054000307085404074a0070403a4903400da0010141140d9850a041c6004c64542c003a000d9070060b600310b13440480c200212240d2160180c00f0013044400785010f05c5001141c400020302502143c0d900036001166900c1e192014000038503000c1c0d1241040250112043c000150a4200250030907050324007a684030585143c00d15901450340c3c0400080303660300c00168450103840d0081c2100307000888002e2101c055156130035007a8420759182980c0810301c500c9128071440c2040401c111812001a400c0c2000d02c2ca1020307900d0705070142c41c0306a00300b414262a010441e07000600d03500208007601d0644c01d14400c100c22284000011345948003107008000010480da20035440035000300070040c150302d0848881c02e8014001c003c0d8080303000010b0f0070b11003491110300340051140d000a074400001c61035595890011103210300e56003801c0b54520b4695200107000c81c2840e005090140c0940100d091 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 94509460 1250 94508210 94508213
    0x20a0b120c070506061e090f010602010515060904020d020706060306140c1c0b060705010f06050f030f0a0f02060c06010602070e0a1401060809030f030a020a1b08090105130e0702010504 81
    0xc980350010000c00e01c08a04101e03190015902150454200500795410400656104e01d039950001406807003d8001d8a008100809200c8100f290f40c100c440a40007000252155010300340e22228039001d45402840400c801c0c81d0300d0900703a006129034030400c1801801c10006642d0402501d440358016074070701da22001d00708145040b0040d860f802c0344050000e18a40108101500b02240b200b450286503242d503001241c64a8480b00c044521581c1d001c00200312000420308a2001440e16000c0c0a001d01c8010310b5505040c24000380303200c50b070320b082c60092846d140e055490166251307680704101d8101100340282e40714464208041d6010b402c00c0e40180c0507242c100340400407000e5004092451032400d04038a18905650b241c0b5240c15203440c0c1c942011984c1e2a122414a10f108420007405031100c0002046814141e5901500d40c65400756240c0c140304400414003007041c1c0582101805107503003048040c803a5800366004020103185828a00c00046d0341e24982d00140d1805c4030141c015035142d804010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 94510710 1250 94509460 94509487
    0x150e090c09040615121502030606040305030a09080c030d09030615051017070806090609040201140d061503050108030a0c0507050406120201080c0a120e0c0d051005010e06010e0f0d020a0b 82
    0x1806002441c003682e000174001d403100d0350f24000310f4000320f079065030000c00708807262514400c94001c1e60b0000101c80c0d54416002300204034112610809015000700d4082d00294603012685540e0500c1d55500c503c3c10318207644442c030080c9002da41c560340080300b0400002c2c5588518011050340c00351910303800b0055001c520251611800100600c4c2044500d20070840f0640e20040520742114081c0d5692140d80d44510040e00c0301c804000f54020304020100c0e5031146680c4581140059426644045000303803e80d030026025154203026110040c0c00c2800038000251298554007045030141c4101d0300c2c010750ba0800b0900300c8585401040c10355244910800c19960007400c1d0907040846070420f513103090030f403580007048165440d6070300c00d01540710300c034640c040001000175280300c00c401003428440142e80d10b0280e99031103c080ba690109030903c0d0002a4000d2850f00c003d204500603110311050a0594003088180055004a00d501241c42c1299002584650030781ca0080e000420100d0340d106840410301 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 94511960 1250 94510710 94510751
    0xe010e09150408070b101a0d060b07080301030b04030504090c050c0f0a12030c0306050405010f0312020102040305150702030706060902041a030603070302060c10050a05040c09150e090c090406 84
    0x100721200342050100140611040790001508071540c400e10b91616001c4450f9005642d112514a228581c040c0c3c00d4801c1e4680105120b01ca280c004110031030b95503070560b4613402a0500500031180a00040000c10030f60320769954410b10920b03000d8a81034070340c07400c401210401c10401001420104000c0d103440c0d000c100680701341c1126401801600107a6072808032100c1103054013005c02d9140c0d43c0d4401403034000e400a41c06484014402e2000d5a154012102c25030780901c030640b07071441000445000d490043c8215010781781c103d4040c0845024190340ca002040000d4036020452004016400c0850007510800b4041c1044180150ba22854044070021109030000020b203155001c00030b10034265400148031046070750503200a030311410361450040c00d00400c1024841082c0c10700741048008501a80000e10a501c181080c0080688803001d0307008440f005425a00100445442484030040b583c0100f548802400304850001c04108041001201c003a282265403039160070f810940100c170311840 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 94513210 1250 94511960 94511983
    0xa120f0b0109051906111e01020a0305060105030415020711032b02010c050306040b030a1e06150501021e100608160815011809200f01110a0201030f060e010e09 70
    0x20443c9401514003030340c1881500f44115014886d40305600f849800051282c0054844450385100c0780d06a914075450103503000e41c0c01d0000107441c02000075200c1d8080c00580b0300035600704c3c09444c802d016170f100340f00080d4030940b0b0560784030340e00140034551342e40d0422a080c4001d4100004900c80341c84800000d4240380310960100641e4104074242c44030aa2080582e40c0c441d41c112030205210040c00c02007410142c410b40b014100b6001025001c0c3e20181880e18907002074421801004501c100500d001c1005059000b6240160000b00040c0d6160206035801000c07400b05505031046c0009070b640362412605030f54484411504106039010303211004242100c028000340c4054035000b483c030407018a81550501810010304c480c0042562001c0895104641e4198421908044220300c0648050032400007420b00c3d2107010400000c002c1075228445010300300c00c031f40c0c00820310051142d00540240c5100382a05440d02c0c0c2c1c42800150b1000300030002802002c601058611790304045800608180c5e50004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 94514460 1250 94513210 94513219
    0x4080307050c09061315030f0c080607030b0d03050304030909020307030c030e0c100807020a1505190b06090618030604060b1311040e04030e0a090b0a27020a120f0b010905 75
    0x810282c0d417500e10754071a40441104e00045c1c402469048044019481d400141c03ea41494000004102c0c581c107400302941c070103800700c43c40e95039a12802c6050391511140560444104040140024000c40203150001d11030308254401540750300c85a01240c004a07038100010b0b480d44000959a9018403991000341500405002d1011a41c0b0100383d541400303c01190030003280c1000225098070038081c28401c1c5602503200807651201181320000380a00f5180110840c0100ca9901800504d40c07042402d541e0005c2c0c540b50030400d08000f04151508125806880041b00031400715040e9010701c0380911032803241500084080e030708404d21103056018407804081ea0f10f001c400208400b800000d641c1250f0118140d5241c5a4032450b04841c0a441030000300d40105642d4004500c011079500080e54090042c6c1d0400c40d83d0f9903441c91103d88250480c0191201401c05803c00c0c3d2041c940c1e00141074000309400d029803e07140e9120508205c1e40b00c1c041c46440940c3e100ca08200707139170340711500e80c0082004a4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 94515710 1250 94514460 94514479
    0xe03010b12012309070b0c0f03070c1502030316051803060109050f090d0504120204090204051003030f0e1c0606030b010b090f0a060f0c0c17030d14090304060302090102030f04080307050c 82
    0x164980c0d40c5d0f03a820f01441204640126124601c40c504202c00d20103003201e40c1c1030700d403982c3c503903e02180030b07813418001c040c5140c1030040383c20001807000050f00e00c0380c0340503100c80c0341100e09131009803601c1c0d0007203081c500804c2002034410102e4600b081503d000306880e20000440c0e18200e00860180074000c4c00d0840b003904030030f0b10300c1c0c015507100080e0b90659050020308100d4032102d10000d00103100a580c002c0d0418200b074100000c0c49c0c144840071084a000b41c9810f07820f481c24000894450031b894680300d60000010304404640d40601100210701441444005030b203507203a442c0c242c0600c02c02da0040d00301c00c3c400179140d0310302d050402c0f522861690a4650041c01030038140054503503840c0d800c3c2c1e00e04010743c0040c90018807000c05140d0004003800201c0240040150070320b99180d60000403208441410060204161003160294600c0341c44100080c1d800c00b420807004801a5120320a0349045200501405801811180c001e1009054100040d036441d90245001401d10b009010f1091044c0e45a2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 94516960 1250 94515710 94515721
    0x81b070b010b16060c20011803050f040305011506030b060304030e011d091914040305070b0901060e0a0c0216050f130603050f03030601110a050d0e03010b120123 71
    0x80d14624151540e40004645607100c84020108910a015014080b90b00305010b4038101904401c141c0c0171074110341e4070070300340d240d512100354240c030400780603a00288100c00a890109108901500401281e00a00d51405607070762902070039141040104050455005d0042081035018810112035120540b4402c0c25450320341c601400d04d07a0100840b6050115030504040c51110074000c0083c07102000748038500305e0505410a5003c100c40800422a1a10345100342d00d0001032400380074800c0382e041d601c5501e84449607440140182c2c026148000964031040c008c6445d011031100d032445814801030016038540e407540d00078508034901085c0d6000042d02c4a00784070940301d0564180079a03d05403945909070a11a554000030a0b1036800544039025500903010118404801540101c000341e80d0b0100c1c582926106c140c981514000c01055a8424018803c0300c0303011390b01509264400800001e44031040f080851141042520102c5d21a55601681c03c07251070a818650134a40c1541c9014801e40307800c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 94518210 1250 94516960 94516973
    0x1c0623090c010e01181503150305100b0109081f05010e1003020f01120207060b0406050102030a020607030b01090302120106030b01080d1b050307021513050409082215081b07 76
    0x60000e0b041015214070b8110f01d90084801c0342c07500ca031001120320810f907a105403a12a1500031102d00002c2d0414241c2c00b090301f500001d400680346c000000d071100c04c0502000200400b0032880c1a0306029100800103240c800a005030006075184802c8802103a1030a1307110412110305030003202e10030442405000c10003c2036418102030b6603064401a000599000041e20f07190341d041c41c14414280005003200c03c10117180c00c01c5248510aa4041c0302c419110350059860380513800d09e01005a00180006805034400d030440c040c0500d0604004440c00c0d280e4010840191265024444903916041d04204210340c2ca40e005006080b00005000b460052a00041a40c3c20381003001400d0480080d100d0240f003014011100394650017043c0044009440d01d0017003040d040148142c9842c2c0e0984000522410140110b031502540460400c0c80c01508268600d00016411020070a42c80846000b00e90385e103213044010042460b84c4c0303820300c2d81e10340b1848010101d0201118000441c405001c0030001425 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 94519460 1250 94518210 94518223
    0x905030c0a120308060a081e10020705060f0a150801022206050403240207050f010e01230403030608010e0703061112191503082508090409021c062309 66
    0x83c1450718201c544c40d4400000c524142c2500020b02d94000e4010200c1c0241d49140480380003809002500c48803140181e001c8200c3c068140c01404c66002500061124140c0c0c102666000404510018039014140c0c043d1011440a81110000341e60015010040801a0741c04251041e00b445050428900700308004003103000f1480b0003010052890502d01c1041c1d10118241440d11000c1c0f4210744030720460400c185e444c910880010060352801500344a0300c0818000d98030844c07002a2410204180783c0000032009100034000d90030036585400c04600113000f80290800601410014000703a4190b0804004441c0003014034070040c1e03006c0000c81d00280a80715040c2d44206104010000d13400580392000c058a060210f11121808044001c82040310380380107890b40c0c180308983d42200083e40d25046202d86034860000d0a4a0401d2281d282c840c0707416000904110b101605100c0001305016000801c0b00b107a01040390751544440d0042d54038156084170b240d18148542c1415541c1c03c0501485440d081e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 94520710 1250 94519460 94519463
    0x40309090207020a0e04081b15040201202d012307020708030c01150b2106010909050906060111060c40050103050703090b0606090a150905030c0a12 65
    0x39004a480d4095544003c1c03100700034170301814044014075040c038040c65a940b140712408041a05942c1c40c1213484400500000200c885206424094540f5001941c0f402d5840340d000b20400d081d22280c0d0060070341070110b413503660303902d948045038020341c4107000151000002c800030040e0b151885d08000c1030501400c0703e10369080070702d5200d403a0715142e03401c0f410007021b43c00441d5503110004002401c4801540300a64140c81c4020a0403456240c20380302c2168424103900c81740c881488917000c0c081201101065070008414100403000655134000c14081d80d1040741d4200082d00001c042028650300304210700e03074100c82c4030301a01c003602c2c2c0b407032564055000d45204014020088131101360000700e590055400d6050600c6c481c0320302010340340d41d0b61402610b40502c0380044d0a10b0003203082d01d4024080c00f130010b0780c000507161442d51042c00f407000e01e400c0074080d50360055408900107411a003007585800d020301d040c2d5071287c2032400d000c2810300d44004500000d00a0300495002c10031805174903403103100036 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 94521960 1250 94520710 94520729
    0xb0102010e3403110a050f030619020c07060201060f080c01080406090606030f0803041211120310090e030a0f05090604090e160602010902030601050d03080106050f070501020301030c1409040309 85
    0x5181c99060620346000b000501c60600c00d00b441c0c00300600c0808104000040d43c00c0325203a100d980c5a009200c80304007042c08103030b059440070001c1000c62046526813090b45050040042c2828402141e00e0b1174a02c6c65801340c1c015075907030101030069600b5101010b0160031840300400c2200c500b50700007043d0020061000d00b2248c0d40b91040400c11405820072402503422241c0d00d81050901e08218440c0c3d801500c088407900c43ea924480340490051400c0804803121134003800ca00c070108401d8001c1070740300510516894134440e1000c1800781d1984a4482c1c2c201601c4000c40c0c451840d0000a4844100004c055042c4802889040350a544907003c560580f0310312000420a0160030403510710708803406038424000c10442001045140d4154084802d26000320121012640d8032020b000310300301201d1002c0e00040c90b070300060151601840c001d0152800594106140c003051383c0380c103800c90304281c10442d005083c07040100220791940c044044e52280446a00140f0b041c20384d00075000d04524842c00d20b00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 94523210 1250 94521960 94522003
    0x50a0513060b07060218030705010509040207061103040501090c0603020412031d120606010215060f010813210909020a02060604240902030105100513180f021204060b0102010e 77
    0x215003141d0494401400c2802c1c407580c441c06503140c000040e40110040003c100a4150002503500e80015a44120f44040c0c40340380c03802012100384000b0798003500083d1007194072200c2070503030b9030b42d92001540b26500603400018610381900d441c0900041e141c1c0700704201401804140001090380c896405401c0d030501340444a0700420f001c003000312002d03010a651002c050ba000002c0c1300808506c5c02e1181501b41d09648a10401810a03000d86500f501c00a42207490f40d110040307254004d0344020b41005800ca5a00300c82000f560fa48001144010980c52048050104461019030807504540203080f43c1e040a5042030441d88009545d8180200150b110b2910b07241440c1c0d0720250340f00403d003c52240009508036507100c07020403020b58020303c906401038042ca400c04000b180316000340c2c1d404100c1030b900f004110745000c05d0280e4034140f404a0307015443d40d41585010040301c43c402401100d10110300400140b4003030034070004450100c02c10506590605090001d0444042000440c0051102d00b8080 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 94524460 1250 94523210 94523239
    0x3030f1e0a0c08060a0f030213290108011d04060b0114121009111b030f0a030b0f03010203010f06180504140103060525050315041a040510050a05 64
    0x144064448018400341038150180301c0044055000b40d020304a483d218850152100e03400d204500038684120f00201010a0003400180b42035000c0042d64910b00c0c101151401821001d40d000d0881c80a001011040c8010a1889960031551450040a4011131541e054185801412840000800041c0465130307420105880f68006d0000618226280710065203821905081c4071321000d0a90b0f00000060012000007003805032805400700601310f026402e82000d007204085001c005403c03040c4002c0d80000d00240c20561602c001a0a12038460b41d03000c80c200b10f40c2001e000d122603603111000d0080e40104010302185035041821000c9070070321700e440032152000700241c52047d10150415584141004061001c4000751800e4505a901a020802460b00d46660100082c4000390140c110351110001440700c450145001e5580552808800039058098500180c121515140b0000030200c060b60100d505007000d10030203a201c904042180130a5040c00005103031030205200d210700c0388603242d15484 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 94525710 1250 94524460 94524481
    0x81b01050d140702030d1406010219060b061306080a0b010203040618031401021902032701050705121c05041106030402030322140402130306020d090209040f0606120503030f 76
    0xb405002d1080400e00c5030b041c0114029102d0f80b20000c4c610390281404400300d42001e8481c03409005d04016001002c0000700c000c01c81860790340c1d901d001e41d40607554541855154490600910b0400d29064610b040c20781044000740403018041c1c2000015803400c440d84d111039030008110340951305181401e201000741c107400700307a240c2450f030001040b2040d00c60104051075815006018502e138034800d941c4002000b00e501300d07034901698041800040960103600b500300e0254070382514008061420b40d00d0500307991191032070300140103d008029040001d4004442c8158242201d42d00c400000c18402c0e41010348400359235940e030000051190b00f000000c0740031541d080007116898072014002d400e2810a0401c906180c426034490868000d00c2c008040e681d03450a40308a540082280c80c1c5503415608ad61541002500002c0d4000100d9039103040000145e030329800c8040c4203e2040c0602e2405800034503001e000d4645662107a01d20312801c0c1d0038600040c0004c0140d9901071001548d000503980d40ca401c04 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 94526960 1250 94525710 94525721
    0x80309010603020409051c140304030f0c08071b140a140315011211040509030d090201030b03030d050619120f05070504230c1e07080d05100f081b01050d 67
    0x3540240b80000d840100070000c10152407445084a01040c0c00f0700c6000251401881102c8c0426020400c00003e0000780c06100e0b2a1b6101095282444280c4410360b591099030340117040c00d40d1011920b640c2c0d500c4c0241d050107010040c02001500e00401411040443d908440900804c800c1d5521488081c3c0151010010245000c64280600c0f4455030340d08601c07048501d00000a448900702c4403a03480c01c604003401a50f0103880c0c118015072518080d1030300360f4020000d10b44c04904160b02c50038421f00590f8104094440c5008244c000105410f100d01080118650708480c1c20989e05100c000300400314044002640f400c0e00852006108025464040e0a040032504000d81c040e1906c401009120301c4940003041ea40ca2403083d5000c2a2a03040343d00c207540c0286101800c400c405090359030f03a030b154420060075403a8480c8100500b80a4442904001e03203c0031a4010300046014504000f81e8a03400070410007005150050500081031410720034800c0b10f0044458188500014404c05551260713005 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 94528210 1250 94526960 94526963
    0xd0c1e080a150e070806010201151203020c060406050901181d0705041a0406030b03060103120c060906060e1b0703050901110a02120c01020f06090a02010c14010e012306010c080309010603 82
    0x80309546420b0128107052044d1060740014105000003080d5500511804810000b803c00000e031251501c07840000c1c0d9900b8180403004c41c001c008805401e915174002070800b429103510b4103900c84038850001494010402841d00d80d4003240b007001c000b2039401a048242c010115030400d40c190f6540c0500b520350f4401c640c49000301c1003184a01440c0031040350040c0003594500c0c3d605201d010b1001c1c04140e40c3e00d000b070202400800f256100303408801e00030b4070000ba1684c800c00340801c42040c00d80340c0f035089468030303405a801c0010310310802412040e0410080030a95000940604200f01c90b20004c0030340c00f802910b01d06002c0c40c40909134013418108000d00c12550f0051144100d859800301858954200c2c001c118050f119500b0020701c112800f0450f544a4440c4d04d004040d0301c0d2290f0011180e00d48040310550310105060000c0302820020700650002e0046600040303043c6017034281401a01540c4202041800001c3c010701001d41c1e44545107102c480d4100c5400f40d1280c88080045004040070f910 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 94529460 1250 94528210 94528241
    0xf100b0403060902041409063c010503070b040305060a020306121903030501080c0d060207030c0209090607080a0c0f1d041d0d02010501030206030a050702120409020d0c1e080a 77
    0x1000010080c107074120070043c52083e10203006015030041c103030078552811303600c0300381542010340010b0400005080340328005181d203410304488041c0310450107101c40704079a110014072910700144040e050402c10030004112002071103107803500e1900d80035141c000c09450017050a80001c003180f5642d030381c0d00800303d0704611101034451039208548110700d46c1c1d10b100c1003100071074180303400060b0000010401224800c0041e00081985500d03903a104025070203101b0881c28860044c2d880405038961110091203500803400524080c2440b420141460720001c000480150074000203010340c46c0d0143c14461000002e003401c40450001440c0c25600700d03041c00c08650031514040e075440c0c0405044001c01440d000a0083c3d54000100e0a001c0742a00d100b4000a2340141040001c11000390300742d40700392360142c0c152069901450b102010100300d5400380d404540590340204441c480b0311410320131001d040c0c0036400d00c8284402c0ba414126070440c4405802014030401d000000d00c8864290407807144200b0481 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 94530710 1250 94529460 94529467
    0xf12050a020c120406020c01081003060905060403020609030a1d0112020a03060513090c03030804060e0105041a07090509070507151d160b040302120f010c02010c110c090f100b 77
    0x40c2a14002d4100410380344892080107003118044561200702c034103036900e690203420310b90003c00040d501040c000c0d01070070000d00c1041c5c00002041071882161405403203900682881c1c140350034001d20300000907005555503001001212500e9070022405103110b6510f1343c01c1072080c030102c4010b0740c00c100c484801d411140e00001d88030004581c036030b0205003070b1101100c0381803010300c9900b4260110b0340310b40c03030052800036100702c2400170134082c12110b90321620510300400c0300002491110b0954600399000ca40c42d511914120420803a03032502e50360b0001d0380d40b4000c8001460b05c1d0016000c21009841042404400242402031004102a0134a401c1480b40e0500c04604540703240ea40e03804101f580c0110030b0040458458607840840d10040440d00000e0080b8105800c507001c10848231010424151304d48900c0489545140e02130081d421018544c0d00005074400d140c07040584141c0030318441e041950000062b0012655034003010a030001071499140c800c5a40d000000d58640030f441e00096280c10010 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 94531960 1250 94530710 94530721
    0x9092214010b041505030f010e12030603070b04030501090212060906040b09030706090b0115050307020a080904061e0504050c0a0c060504060b0a0807081603150506031218040c1404060f1205 83
    0x7000322900700c42040d0b0407a00741500d802c0c0494221000c50112060517041070021080e82cac20400701039500048018103950034035580b03d610394041d80c0302d03905c21141c42c1d445109480035440c02100c9001649528005800c0c14542811515210040140001c01c900020004540c864200f0001d0742c182c0ca500c003604106440f214100018085424825207042024214100c400a0f21a805a0740200019002081c5c5200c95a45031902e5410070380340c2540150361144001520300304094481503101d90f8801400790541000d0034802500d80c02881000c0300750040140010490f44000189403c540008000500303440c0c07490148050400058816404000c40002140615000c00c80c10b04458110046441d84003910303080020001c4d4520007c2c1c0125000081181c0164a64000c1c9620090040548001d42044504500c06030007048c581d8002191805100599051a20503240000050304005191090151690b0701c40e1241e4000c5d00b042041d400a0b041103103014a069000c00c445101042c000d86c80c9c007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 94533210 1250 94531960 94531991
    0x16030e0301020412060b04020403051c0507200a050402030c0a0c1a040305130905060907050c0705031212100302061c020903011b0f0903050709200a02010209092214010b04 75
    0x902d48240e1701140380c105003481e140380520807036003100e51180182601c50740c0c4489840d0610040b021540900c6010007040001894045c00b510082003840070140c48502074a06011070a03400390041e40c000c0744100280310703040810406581c800642d6150021414056141114065030010760107004000040c007400b007007641160190100d8a1040d19900f02c1a0307540d06641b082e0b1b0000d0320341d40e40000e0760002043c203051180006041c0b0800c0c040843d420250340b40007107490601d414050840090b0301240161130901845d02d0103400045d10070010a125042d500055007a200d40b080040c1e900a1042195850008540690b40b803020010300800100e07000b00754444a00412b0b5000710000341200c0400209140500080e00c15207070094000c5c080716040c410307a80000d01102c0303541856241c00b02501003000b8418001040c0d00c0703025500150301c4a1001040c4484204050403d0044602140c500d240c0401341c4001034203140e42120520240c0703000030a500b1f0040c102510074075006410081c150405440 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 94534460 1250 94533210 94533239
    0xd08040305031b010203010f032307080304150302041a09030a06090812011203120b0102070b04121a07050f130504180c120503090f060c030a0207060909020f16030e03010204 76
    0x15002643c6509242c1207800364200d2100740511035804080040078008100d084070461040007521001500304248403224529200c216880203119a00c00502032010b000d030600f1080c2c030702c41e603801c3c154103080c14011034003c1046001c1c20f100c00c0c2c0c80d0200d01d40324503650401c0b1158001c0e412030010403e200d00e900304082140c0c450342541c05400c0601000040080064410f03600c41d40e01036448108102401e04220064005500c03181d04610031100302050b1070080000a00041c1000021150401e9181ca003800c03034109140580c940183c0d9910400910710742142c00c40d0490340c1090f41ca113650f0944000120901c0b54587c100b0398105182184074415140c801c603903001da482c080c58402a01c56070f036610000e4003101145e0004c0c00c54105000d4122107003412103c440800000402d01420008036080d0036240d03800114801005030f00451007009990381000f0920080c03c2c2e030810940c030b4464082001c0c00144510b206066803614800003001c01d16114031281044810002c00a650317441e0340c1c0d040c001800a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 94535710 1250 94534460 94534477
    0x309030207050904050a0b1b04090e060105030f03120714030115030f0b0f040b060403050105040b0a0b06040b180112060b090f180f15090a090b0a060e0a09020d0804030503 75
    0x20541001141030f10305a80081d01c03c4da4810003d010849660b6188102034102a10303240c0d902051b5509040c03d5507c41c0c01510140091220015080040849007841d04a044e44514001d40005201605008012080b591a44181004c500d49a15582e804035516840081c2034043e080000c000401e10450380582034010005a640c14000001074003126412524582d4416600240c42c09405030103080c190411002e88000502c90380c03c095403901d540e800d6800440d0b04072049008030003000208900361254000580065032001e041c541001805c0e035461154040458200c01d9110754980f05070b00c80c1082100040c2e041000313200b200c3e910881c141c0c1c81d4005420f210302c111040c00fa0403002d0b06001c0114240c00c0310302c11a40c1a50f071918000c0c3c4860203c01781403250b00c0710081d680a80c0b42d40f903000840c0d01806842d100060701c1000390070700407616000904043d4034241071410402540c5d907070307286c3d16400c1505041c1c00281030300c40b071000401c40b140240d0028503256020500005005021004c0d141c1c05 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 94536960 1250 94535710 94535713
    0x1406030d020111090f030f060703090c0602010204051302280207180504050304050418140703060509010203061f0504031b15051c1109130606020f0c0d0b04080708030703090302 77
    0x20003404105034203030742440e40f08490b4681c0c103100c00400340c40c01a0740a80120780c085d040d01d1125100344451801c2c41d00480d03451000c240c44600100c1000a41944140140703a80d1008500345030600340058101c3c12007603915082a50003140c1c8401103010544007800a020f169000e610000c0c40c000040c1d01ca0980b441000462242d1007145291800c0341e0103142d104070f80c400302031484c1c141840100b0004150317040c040300c000780c5a44002400900c0010b240c0015007603c4004041191035841d0070400c0e5040200702181503401481440043c0c2c40d40460703054125014003a540304c3c01c40101044441d400b40c0c0c0d1010b0400c01249880d00d00c0401c500c030344031080e180b0000c900d140e611803603034080d681c5214912480030741c450344040103031a0100b103074082a184405030000c203240858140005032003441100908001c9035a4460400c40b040d01008180a941c10f00c0015020303900c604c000199010118100c0500350900e11000a81081030145c11583c485078400e190903181e0500500043c0203109030101100903 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 94538210 1250 94536960 94536973
    0xc0c031009020a0302060c030f0409060503060c070f0b062706030c0d03081902130e0a06050f030a0b1b031f060c080d0c230d05060d050c0603090709140603 68
    0x31159029861910b41c000d00300b112071602c0c65013031002a40c01105020b955010910103160010b81c440020002850b0448010641c94101400c042c10210081c090303503500401001150b0002da880d6001035025030f0024a6408160b56850100b01c01040b2030803801c24000c0440c500508110132442c03914010300060701214400c3e00040184400d07440010760207404181580c00107001f100f513107900640c0044a51501604001c030140c20819200c4142d04400c0c4640e44030130810410000c2071142000402c000c44114141030602e1380402e03240e0f0380c0000b01030522000400001c40105ca000702c0d0844000c800d6464070f0782da1070201030072600d2481414200c0b488088410740040c0c0180304011020106030019080c601d032a0780c2688800040c5407103d0620240400c090480e603584c146c403085156140581c2442540d035440c1140b413841191002000d03103205402c4000518041000002c088210103c19104d065a94484424251802422303030301a0140c00d08021441e0070f0315400440644c0603403810740440b0503 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 94539460 1250 94538210 94538233
    0xf150102010b090a0603110907020309120c0d060e010b012102090604050d0f1205030601050307111905010501080c041a0402090a090903030c030506060304020f010e01090e010e04050f060405060105040f020f0c0c03 93
    0x1048060b1001e5004be03006100c4440c0b40e02d40380c00303851804566401103800b400c0265000c0b07207494007100d00a4501c01c1c3da0729031000c9903907001c0c054002918024a0500c0100369140024002c2c1404110740303903440c980c08101c1030110b894140446001e04801407400103488191701d400440070021180031140c500005112350f103030a010304203990207400140c46290940d664110100c440403201c40740000d282c4508040715a103801c1d5281d4004030f80d8000d034000300b002d60601d1902ca140000313280c602c81c000d920300001c2920b40e4111070264503086404a40241c5e5030f00038140051491941a0420a245840c00300084101509603000b00b80040e002c0d14203000940d100c13010840d8500084a0203900f11a0030702d400040c0f503208a03920708080605041506c0790303585070007140c104001c2c241c003e2101303443c9000c188424030000308441a405651b0900520b00341c981940c80585554062040d50b0240d9107a41310f40103140300d59015070b546503821030364030780c3c844003001c2c4201d070780d06000010b280c040d008450703121030b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 94540710 1250 94539460 94539469
    0x21b07050118031104060909050f010615091401180602030a0e0a0b07022e02010e07050901032303210708090606010c0305030603030409180314030f150102010b090a060311 75
    0x25807000800e000150b54a00d55240c0c0c0e9421080303142c4890f800f41c0c1d103a102094840052190002d0307240100024000710609400c00b5003100c120b900045038201e000024241100e034091016016142c0d15034006d10540d82d2031005985014100014111542d1060008140580d002000c0d03c0302d1340c0103540f8950f0141c0d00f14180f04c01c42c80c85000b1080014420048200981404001c81260035100903403030132494090b03450f0508100c141e0000c2c20060f5102c2d1041541c40c04d04002100103041c0884404507254999030350084035600d06216850242c0302c0a8070407510440030f00648003040300d0080002000310340a40e600d200340c1e000722101008110001e002c5020000c0008002d48548010b85403140f010025850949042e000240301c00d0b81417004210100d08071426000300548011101252510b02d4013502c1c010f0f2200601c080c3c0041411414800c00000780c1c001011582c01c590170030036003050036040e100101c1c05800480041c0f034010803983d00340030f84961141c0c004c0c812203024007462041c543c8070800b000b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 94541960 1250 94540710 94540727
    0xa0f1e03271802090f04020408010b09060306070e010c03050d060b0a02100e1015080106090b100c050a0305071511180d05030405040509150405061e0631021b070501 72
    0x2000e103001c005605a00900b155000740109400103000c16003036000c44000030140d0380a0380007401e03641d440744221401c40c2420340e426030b0020021070192415190024000b4560340400c41c60504110210254409150144044400e0078042d0842071016a46801181d00301e5444104030310018801d036402480c41121510815402004040185c81c1412036450f400016003040c0c4040f9000c0207000000080c40384003441188001c01001d007001c41c03806601c17410003001c1841c025511040c030440c40d101c1c10000e2408610445685d5050078440d0700e614541c14103840c00f155980040007600c0c078002c880200c840d80c0d000540f410300ea82c4915508005461030920401c0c401c024001001903000b40811311507894a81c1000341c1c004025002c40e41101000410206403480640301992550403941c140f00c0c00211000010004c02943c031601c540030300706040411505441c42c200203403440060795500d041403c1c0c254442d1a08403954000759190003511540311980c08044218800b04d200320b000004140d4000d950303d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 94543210 1250 94541960 94541969
    0x506090702151807050301020d060905060a0f03060c0c080c0705100201020c060c070f0b0a020a080c0406050304030c140a0c051216030f020a15051201060801080a0f1e0327 75
    0x1031080903207a500440022010b000700314071481c01464030101700b41d1001d00c003074081141800340100781e01d450410402c0440708060300070340c0982d03540c0b0001e00c032a101e01010181240c0d400040064520030340b4000f100e01c010b00c910020f082142c001010b20109c2000a840310903500c00f111140820340600d10182d08074803030558040705580101700001d40d840e610030040c1010a000720039401140903143e58250081004840ca94095540410ba000426500c0001a030f44040c403103107158a42400e0401c00380c01800000c0c001010818000490800c0250b075a20941c1c48034980b000311026482c00c2d02d007203034510450b405200d0145560b47c80481c14248009001c035095100b0029510b80103055480b0300340340b186c1c4010142c0e000120700d00e00040c02950107480c0300e1940007540e03840361246c0280b083c5c030f480c50704180d221608004401c00140103464010803904409a400294001082c0003803400300540e4076024042a14056080181c8003415042144507192070011840b941d140000000d400b030b1480c0c00c070f005 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 94544460 1250 94543210 94543243
    0x706020c010f08040812090303160c03050403060213030206040f08060a05040c0e041a011203120b010e04020904090807110112090c06081e070e03070806042a0b030a0506090702 77
    0xc03406090f02442d581c5402500a403d41843c22054201c0c076401400306450350f005503400002042800052404036160115003846c040005601d1520014414040c50101800345540010b00c110341c1c065904644c001994058481c5841d5035581c5d4003c1d20b08002d921400b1003a0040300006416001c280c4141803045910503c0c20380c1684c02d001c1104416040103104403000c000b0107183c1e519000b40110b82c1c034000d0001041403031800d070903840e00810642c4500c0303599509606001c4071015903a0020f9400881107410307070b4011303210090900014040c280080005d441c0c26000984941444510402c5140080c0203072540441c950402d90200100c0720480d4000c4c14441518005100783c038461031100d031700039003081080c3c0c0c40c0d101c980c000d5440d50b02c0191460000700b0f0780340c1003002460406200180003440780310040c1c183e81c5000c1d00c070071600280d008072280800d1103421011009000d5640c50101400c0400800340e12482d120203c04000c11003074a0440c0f0402070000010180c6100003680500d4607600403 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 94545710 1250 94544460 94544477
    0x30305040f05040203090d050703140c0105061f021b04110301030b07030608060f0604050a0605120a03090603022802070f030303021c05060105070201081b07080417030a05072901090c020706020c01 86
    0x1101207032541c10032827045041001c4500c020007240d038050301400200c04003000000d5076060040c00c0140c0e4801001d6010000b2020000180709030390045140341a09280003141c0e40c6401c0f030540010000c0040700f4907034511200110010042c480708040091040c41c541d202041300c5501c034240e035552070f0303000c81e00b01810f000b5813000100700c2d00b459002030b50010040100807448584890002e510010300038510505907004200040500d58000c001c00024000ea04085140c1301003200c0d00c0c40e8450709401c10a0034601503152009000f48200070000041c942500d1610b406516407034010007960040727034091000701d141d1056407141e403003611500b401010141c69640ca041e9090740150781c0c00500a1a213078840d01c6042050014402c84002030110358400c0304101d541e1403c2218143d050103040e00507650a501c1031000c12121604002100c400940104201e03564002e01140c1040d803540c249814011000c0c680d000156050341604211a132854540030b84e5034031611918102e0380d51800070103050002d4480c4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 94546960 1250 94545710 94545733
    0x709050112021513091b031a013509070801060f0b03040b06031e0f01050906100e0a02130f051206061e010915080105090708040804141207030305040f0504020309 71
    0x4100510000f0a9181c8440c40c040c0d482d04407408640c00110b900036210b281548050501f503141c4034850303001c80380d94003201c1c00c0d43c000b1000a2161480001c0b10489250705908101c40d001070044541140069180c0d496440c80d18890a0b074503609948252140c030b60802802140d540c031200306a0054a229040b02810b40d6190f48800c0c041a034080d08581d05400b13008900451251001c03005211155003e0060807818100120a421920001d084e4807031074000c003050260a00c4e0003010b41c421640c80d0403002010703481e112140e0000f4403c43c040b800c8212034010f000982c1010b070312440b070110341e4201e5401d042016018040d64440b038044410aa004201e0a4225207003017884042c400301c0c1d4030600d0215a010f80310700700a02001c48010014010a0040c00104140c0c504a4140c40e8024010b1904203814102a030340e500e61b43c00741d030107502c4011480c1c01e2091103544032021011060440241240e10f001d90360b08003d409544207000d4005101d85000000c02c039404e06000300d038080e603000390041c150038060 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 94548210 1250 94546960 94546999
    0x3060311090c1204121803020a0306020306060409051005091608160201020d06030b010509130b04080a030b0907080f0603070b0706050703060e16030f0c021e030903010e070905011202 80
    0x61089031030780418454403800b4011000043c4c07049110b8041074046800c0140090f240940001e46036168031a60b18080c401a02c40860031021640d01c00f20143c1c680d120100003807020700039a00030241c1289440c041103034842c198164003080760b405807842c080746d481e00407060050945a440190108450f5408521036090840d400c03c0b804215100041c200030901d200c10054074a254011b4a000805900501452600700b1060f900004980c10411302d0f1201d642d40c078001ca000c0104007600c4444007180c5102414002d4200c03002d118001403146030140342200c0050041c0d074090340c1002d02c500348800000c52904000540c02e00f50ba1200d550380d42000141c1d40c540f0090280200080300701070b11000e000481c071a151200398020410f82c03044850407091403000404448004801400c0e0380d0070603082030130917034001c20000d2181d210303075030000742602d150b000c801c0c40d40c400d1034840b035059882c01c3c8032401c5031400852800c042d81c144405c140400e99072100700400102110502035031154a400c044201402d8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 94549460 1250 94548210 94548229
    0x3040b070c15060f0510050a0c0807020303040f0b0c0601050f2101020903010e300f181306030516030c1e03021302040e0a38090a0c08010603060311 65
    0xc03a0118264010015001a0a0301d8070f0364000c000c0c42c0c1041d2001e011602e8000034068846005280603401d003404003030010006944408090300d0806d00203510000c0d03440c02d20840b03020303218150408034659076810a07204e0070783c0b00210315a02d5004130b100114240c80c02102d0030741a07150041c120740711040e69034484490481000004140740d0743c200050b02c0c40c0d0320203018142c0004410f1020702050305100c00840c9251100c680319041160040d42c1c09500c0d0800403080e1039140040e0001d081e100e01c2144444210000303d84c458540c414201881c0381e8003048940c100c10262f0384504196161481c541e810b481450509010050100394442e100b44a904052000b480050760700d03822951350150b076900410200c0e030070b00c071000306030f1a000203042c002c000c0c0400380c04d82c02c040d08500c204600070130444140094007405910700300c080380741c0c0c0d1103580414000c1d0540a0f03020f00241031312254140700d2140d20051880514407000719100100008000380039200c0d900031607801c011245080e5581074100301d440103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 94550710 1250 94549460 94549463
    0x105010501050306100c0215130f21140a0b180714040207020121020d0e0a03021b040f021801111f050402060d0f060501030e01020901020703060f11030405010c0e0603040b070c 77
    0x4200401b000540d5075800b036420140f1801f608035540b044c00031084002447c01d500403c10801c4411030421200c2101c00c41c00003420600c207068410030142e4036056440981500030300303009100369244541805060256140680036030344d09400c00b80a603040303041d201c071003034801c8002d2003912021554903410305400400307000d03205150148000000544060009074100b485004959000c55200019182445550046a040070090120b6001c5590080d5201c81c4401c140300008031a042c0303907505456a4001070710180b200311095403103802000c0c1c40d042d200035070b016440c001000c001880802410100e00010004441e010f5050f03a0a901c3e2465000303001d000d0412078100f10f0803c815102c80d02e080c0310300d07101e082c94038801042c802d240070001000c0c0c1d0100c0440e640182d00c10000b64003660380018880c1c0480e0f5100720042050380102001030001c0508002400880780700000300801c100041d8801c0c001c013140c540750003901c0a08102400210b003c1110700130001c0c040980030441c0345004120200009 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 94551960 1250 94550710 94550717
    0xf06240603090105060108060a03050606120313030303090209010911040b0a0c06020705010902040c0509010c0b06040204120c1d0f0f0604110a020a0308180303010e0c2205040b03010501050105030610 87
    0x100004000c5081603000b11904840761359203d040c440c441d0b90108100b60400b20440d58980e0407401e540700c0c140c0751107018000340e00ca4014046021034400c810b00a99203e14007001c0c90841c56503490a0103806840551000c0344555030341c10010500b80c215100341902c800051106500305800d01d0411541980f020703d088080c0501e1202480014880d07000034840a44107400115080c8606d1040c4800c4d100c5004014081c00800d0020007002d03644480500c401d01d0704010004601d48440020038024031403900309000950104081034144281810b050048510100c02070440c842c4a0041e611043c1090301d80b4012107010341c01007124030018010b9650452801000050050305001c040ca130b80f03520403400040945c001c503017040c091581210070980d0008040d100713550904a2800107980368030050140203038600380d51000c16240803445c0281c40d10308464000743c22125040e05154102d04041d8440c1e644118101261030084d07003010302030141220700c1a12903d0440d2502030030000c56030300044201040 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 94553210 1250 94551960 94552021
    0x903100606020307030c170d0b10140a0c0309050d0602030708010608150402090112090b1509091e12070309180b010903022112040509070f0207061b05100507030e0f06 73
    0x1500007c1c1e0007410260141036001600c0d28410040c0400081c1e007981c1c03070b82807001800c00b4440440381201100d1004200d0328240e0342d400218039003601c00c07910b0b5421441d001000d8080640c100f00c0d00fa0b0003940181007945440031160303038614040340d07a10790403694072040c0404900140303075605241c0c000e0b0407a03c0c41410941c8440e4240c503c402d049031400181580e000b6450428400d811448540c0c00b041181d0580791450b95140c25001c40d03a484558101545000940341ca064800c00f6050080a0185412142e8543d9810003424000d1055131203000c0d8400e0381032200c1590001813000d200b200500c40c5c040e102c2640e0031b4656000c1208040c0360340d244001e8801034a04014181405022000b0000310515016454500f000248020307040e00400e04c0c001c4c058800240b41c242c0303400142060444200d85095410341a00b47c1713410240c1040420000c1462041001c1a0300070340c0c81d81c20a0707100f0901643c0410200c0741c0c28080640d28081210510070642040005c14444400c00300500020050190b91005 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 94554460 1250 94553210 94553243
    0x40b0403020c091b03100e0709321912080c010b0a0302010c061d1005100e0105060318120301060c0510050115030f0e030a0215061815010c0b07050903100606020307030c 74
    0x250247c0441c0c82000055074001c1c1800541c020180c000c45149031400f194460503d28600340ca10003440b191610b1140140903c2e10725204a0b4006140c05019032803401c0b8a00440f07031804041c13a800c0b0400c40b01065081c9610110039007001d50344001100c5c0c050b9105402001c2c941c403401d0040079800f44402c00c3d4800d111980c04a644100105611306c006118000344a10f07203620202c07c200c1c200e40010000745c401e20b004000e99600c44003501d400800343d40c0b04201420450300f03084c0c80c140c07044210a41076030011000266580d0440c5251118601807004e4a024084400e590340c21900e0074040c414180954541700d60540384207601c10049954000000140d0300e04e07401000f499070b0092078100c00141d000da01c0500401600100c240e40110381920207080c01406880742000e0904010f14003001821a00c1d162a410fa114a8000c1900c0f41c12003405625400d103040000c2c81a40b10160030f42c0644901d55060030225902e220b6007003200c0243d405076050000c283d60840d0002c1c01c0d2042629501c07000d105420 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 94555710 1250 94554460 94554479
    0x12180a0302150c01051305030a0809010603020406120b07111e070f08010c020f070608010311040b0904140d090305060105010807051905040512010b0102061906080303040b0403020c091b0310 83
    0x15140b00b110b01000d83c880c03002c121100c1c2510001405012250449038801000600000039900d1691150074035048580e500c05807280100300700d91010354000d007000d200141848864031401e00c8140110400909583caa0b0000c1d201100d40340440403265018030500c0e80200c0c04c0301e0b145644020300342c060721106607803040d0481245c4030030f4021081c0e90b5501d1140f00f91840c2c04001000480d444c510240000c0d0b445e042000e072602c181440007500b04020804020000ea880340d2180c0301c1d0460040051145003005d00303000040d032005480c008202d10034070f4000200280030350b850804596202e4000c1081e0ba0a1400445000202030302da1400e2160900a60a50f07070342c041d15842018000381d0710a43c48600d000c0801c14864126003c08000303916203e000341c4284da0104038158025141c4144454002070030700030400030249a480940540030202c01d01040103212043c90f8007d0307000303600311800109101e080110340081550300003000c141e512201540044110301a5030300000042d01d140d042e0f41d851500b035 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 94556960 1250 94555710 94555729
    0x2150121050a1a07090b120703020f1204120c0807021c0506010306090b0c0315040903020f030c06040209090601051008071b030804020114030c090103150302101205060312180a0302 79
    0x116440c8100f8a82e00021041d03402da040e030b1140301481c0030340340750340340c8500307101c0358030802c0c8240a14280d6200003071290380c020b804603501c0f210130300e4055a484298011114403100c090fa401c851510054954150b40d40c402c544030100d01c3d0f00104054074142881d401c001c0380084a00e15001c118030034842c0000450b80501500d0f00030340c000c81010a04032481e03d012030780707000700034030f00300802e10140300f4401f044a40c1c911a130140e040c103803000280001c43d0b09013a842c008603100038864922000171000807890000c0f580131f014510a440c910080d8881003000303a243d080c00d00405401914151945030124841c007038130780d0007601d0350901080b251000c040c0e000030031002c40c1c0150301091011051004559111010190070110005041e0071800e1440c02d90301140305d4640d1a50425072540020010b500d0600300440003542d0080900c80e11540c01500035005c0380e490700000000c01c0c07418000507210300f004194243c800190410755468501030300510701c0e8000d00000c4481d0810308281d801300042c0c5945030003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 94558210 1250 94556960 94556963
    0xa110c030a0e272505130f030203060720070f03110f1c02011701082a0102070b0d0e070605220302060d0c120510031202150121050a 58
    0x3440da50200444041c00318520200030038010801c0c03100702e041c3c2d0410400d0b4681d091000082104481d25003c03442d14614010501059a8401c500701220083d50803c004201016810070300d50440d81d0348280c404c00c418200e10001c1d405400c01000030351a540300d00200d8951804080d000b0701c50082d50145d0034034040c0301303810501864082c4001802445a1400c03211035070b650480d09c103020780f0740c3e850101e40c200c82080703240d40d00e400f103940d07466085a001b000c9008400441d000c0074211917a50340741031a650f82070b403048050040e1000c03038000f074000b5102c06204840c80040e001401c6c01e52822a052000e54031182a5401403a9034050b03890400006020380801450540d8170103488481030b0000040b00c0010541030104030040d44010401070b00c0b0101620b81c8031069410014201050f901e044d02c49680002940074040d00e0502001342c0c034000f00c6416801d0368050800d0b09040403947c00280d03501c0c215211020300b13100a44004010b0108030040303403240d2008200d58802a4112681d40382e06e0218030000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 94559460 1250 94558210 94558213
    0x607080f030402131b030513050a051e0321060a0306090303060303140903070e0a060806040302060709060e0603040204090c09021b10020702100e031203070503090105010609060e090a110c 82
    0xb4081545002028004003200d405000c0003000381c0c2d400142d500c10354200148013410f480d800050144d240e80f640c2056599003007001e440203000e0626000e030301d502c8107001807080f8000c1d01211451203603001003a205e05408003030b18000d6241c94042c88a6200d1401003030540d2105040c43d000c40058043d01846000d81c0c42510003213941341c04c51138060b00c050f0407100b42080c810414001050b255a0008e404801c866484a0f07908040e1200000480a00740a400c0b64005110b80c0003403008155001820034032688055649250181d00c2da8001c2301c20f14100910240d00c00c0d800d1022801525255209600c07180c4a400310000555850800c003050345c00024400c00c2c1000320324020a40c8034030031310416000c200c1e40c0c4411480d18034903a0004d00000e003618107440c208a201da03411107454504014a2207400c00a01c042c82c0c40c0d03c0c002100a140354812a51072985502f071000000d0f080340901c400d00706407452500c4403008030200c14240100050000c066407022a1540c06003d01402d0110040051081540 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 94560710 1250 94559460 94559467
    0x2010507020708010b0315040f02100f0e0303090d030f030e16050a0506070c030b0414031206120610050111070b16030807021902150904050c0d11040e0705090607080f 73
    0x154040d0402d4142c0c0e03c5420f00380d05120072450507039000304400c0302109000260b136010382c8403818402c14450810300000d40228a01c8409a034440e00140c441480f595640d0742c50f0442d241050500d81c0700e0041c90b00c0f8a4010207a801004000b83c040c03681084c00e8000c40c03400041c16240c3c600d005151480c1002420a20b050000c020300842c1000052107010b04400d50341d4906e801c03103a80c0c0c1d11440941910003c0c0840024001180400450410b10070340f10b04214100d94031407041c40d40040e0051402d40b551442540009648a408100895441e104a00d000c07070900700c45180c100150b40041340080202c0d002c3c001c140c00842c4038102c6c1c001070315015031040394501d4500528500171300401e00c0504908151b500640d96815410040c0c50680c030102c2e41943c0d41404100d1082c0d41304d8890041c40092680039003400d082115802010005d003100d2440364105001000c0000480781551080c2c6c0036a160140f040c6001030740460041c4014403000d40054420f0f403a00c04d0541343c200303058104902c4400c4144001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 94561960 1250 94560710 94560721
    0xd0e0d12020c0a031211070b03010e0603070806010305010507080105120a020f040b151b210a0c02033c06060402072402040e0109060b0a030b0301020d0f05041205030705030f06130c020105 82
    0x4209141b601d4102401044000d06044070074203103000521911a0109200000801c1c0703031000e100b03090042980c2411603045585901d0014040d1038100e8103c8001070491000161510304aa0f01c0514615444058100140b00f42c0900c0b841c0c142003002c16402c40d4071680d80480c1e546171301000300955060040e00c26258549010180d100c412200e84d400301940c440006003424240c00c0a12034170400d082640d00d90b55800034842510180c0400c84d0227541400b918400d200c60001c0b83c2860a0b00304620003c00210034084558503600c410b41d1204c81e0001e51042000515500b400da000701100b0b80603c000c01480d4418415846003c81481801d007811600402d007000182c00c1c10040030b0241100c0d42e020311800d41410740c0a2118001e5266610070980c60790b9a8a40315202036044480b00103800c0004d000500a0b881110003400040d14101e840710401011002280e03c14015603004072141d6950500d9500e90190960300758078003a2480c0d62000c102ca000819083d0184154039104c6440e400108461408 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 94563210 1250 94561960 94561967
    0xc17190801170102070b15041d010219090812070804030c030302100b040c050703181e05280510110a1a070f02060c0a050f0a030209030d0e0d12020c0a0312 68
    0x2d441c10b031003613005004c0c800008940805644e44100c0c00c04900500021030380005005d019030f42c100c122100034203103d070b0108013019002802d60300c00401c0d146960b0343c400c200841d03803060140f040307003810781005488112030494800102034180c000c404d1282816147d45400c01d1449142c2e004401507070201c03594180350030050281c4585c080b03044404010200460030054075901c03c03044020b00b041514281b5106000d410a02e24014206200c01c030ac50802c41e842c0c0c14071040200380600d5228120602032003000e501e4101e41c003030001c8281066280b210f8a1300c000c6c8042410000400014807101c0001d0340781840040042c41e03550781c015014030140c60001d960070401c09401802c0d50040140854640c0c5d01c1e1070300040d101da001814044115940ea808500444031801800300407400001c0004001c603003658150050a01c844040301916894101a10161404141d40f0341e203e4103c090040740e4000b09040324080540309645005035103032407004000141012407075810440c0c2144c03100c1410786000d0352 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 94564460 1250 94563210 94563239
    0xe030a080f0f06040e010e060c1309020f0f0f07051f0e060912090a0f080f0606010c030f030b0f061204030908010c09030b040c0b0c0601050913030c17190801 69
    0x80308000d8101a0804681c2c0e404a00c5004050b00c3c011501c0d000315407141c0400b5030101184407144802c1d03c41c0c5003030681002c21135078070060140c560103011040100d2601c00d10b2080340c0c5048150410300c1c0ca004080681c0c450303a80c0202d01c0131040388509101c0e403c08608103004a2a1442800d400e10039407600e00005072007200c03004014807090382c0c084002c00c00c4141000998140348010b4401c840d0b22005020005410a0240e4002d00c1034607580c01c400080c003501c00150711801d000b2060558000d41d0342d480044609181203040030b00055445100e103860749001c1d81c403102d0749080240929450869000200b460ba40c080e10141802001d003000300301c14180c2c4111040083d08050000340541c50b1404001000202a800080c241700c040b1004102000a8807500703000400900400c0358407500321288850b03c1c0d01c801d200b4035010b040544005040c40c14000c2c900400c1c0c9506840d1101060010780b00c0701c508142c02806180034400c20803031004100304022800724540b40c00d41c0c50315000c2d07042c0140da056030321 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 94565710 1250 94564460 94564471
    0x203011d010501020a0609020316170d020c0102030a081026153c040b01030606080309011403070207081207020a0b030f0f0408070206040906031a0c0f0d0f0e030a08 72
    0x11440d000600060b030780480c10032107650300010045136a04d080d0002074140021003901c4c0301c07618401e0030b0001e007c01d11615840c0f1003280d8071042d102403582c254000d0b41c0314000714000d1401070304100806001e150044d03074940e41207618040b0980481e80c40f4800703011020591b13221010350998040c1d01041d030a00c200070a1440c5080c80c444000c02c2c1c28030b880440f01625941c409188050b02c007141c1d03422000120760210000000d20001018207081c507007014110144c080c0000c0d01c5090800902041c0c841d40001200e000080680d00c100070558445040101a040035044000318000d5807400a01680300300501c0004100c0350036042e50b030b61554810081900d480381c0c0410220401841081509540070002c039034820380e10340643c03006035140e10f440c0c0e045100e4500025030241c0041400700e501d8940b5403200060307920a5240c5220b030106001c1000c8940702c212410080b0700f1042100d46082d0060307901405e90902122000f0668040c19480b403020340b00d9a001d05055540046009040203520016094102 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 94566960 1250 94565710 94565759
    0x503040b0718050112020909070306050a0b030f0a05180d0504060e04061401080c04031b14010336061e11070b0c030705160609030810050d121e03020301 67
    0x2d00190074601d07108091407207968140301302805000044803c64040f070b01005802041070303035035151051024000f0140c1c0c0c0982d078000d400c0132a0110b421201c80741160302070b00464441104568070f80d580100903090080001c0b100d490101000d403800b81c01082019920700b0241c0741c0035211030410b18000e042c0104114081e03c00c90500e8420056484100c56a0b000c4d0344003171900ca42e541c0d0b40c01c002c0c400c8034842e9030300040400c80010403040301d001000300200150395240b140700607003c00c00d100440070b95040a09249852400c00c0c4081e0102d00c103c42408154070003005070114442c2c25895100071681d030705001c000c4209110a005000c00392034890001c00c000814050381c20030505072a41c0c1200c800c001e02d00c0b024084004049004a401401511221000d80041480d0024140752100143c4071034902200441d8100004c500b0240b42c0c4904081138400140c200318441e01540c86820040d80c02c440403505000188403810780042c0380c8040c81c015040d5607100940d495240030004180781c40707182e0303104000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 94568210 1250 94566960 94566977
    0x42904052802070302010b10030c02160b19020c03030d020301050301060f1a0a050403080a0203071104060b300f16020a03050d0b030f0105010620010204060903080a02030d06060503040b07 82
    0x18050064807034031007402a9801a111003a41c90180e004020012043e80d010340341c6a411006a070b0b00d90480c06400280c1d5013500d100b0a4100c8403400c000304623000d80612500d080c41155031042366550a038034888494030488160072042030209045501c068072100c0c1d43d0f5000801440f82e810240180700040581c41070224042d86008200881040c491080380760405000070008030191040041e40c015540018240e070352401d4540c0c01030741d20740c80014111501d05180c2c048455600d0f01e40b056400302c45200d20650302c2e00100f070034400e48040c4900d4600c982c02420f140c1e0b03000345080c01022940b00b80800383c13001d0030500700300c0c0424503039088145510085600c66241c600020394001c0503248541c81d010000304a001f84031000904010604d002c4809540ca0300c000018040d50020100c8908040160380c80f041d00c030764903415401c1c0d00c294001d050220741426020000a08244020141001c0701d1050701d00f0820000301d00c030240d8035640e01501c0010f502000344000d10040c00380d041d4112056090542d030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 94569460 1250 94568210 94568251
    0xc070e04030203093a1506180b0604030804080c030f010e3705010c0f03090206030f070903080c0606010e01030c081906030501060f081204080303041104290405 70
    0x40d43c3c407655a4850213564080500b08600c412484031014540030040b808048041c84200302c0c1d61780124a01c1a10b500103101d400da100b41c0028410b100590307101c5101020170002e00b144140c0030b081c1c04800c40da0020720403c0000003040000300500090700c0f001000d04500034504007010302d00790b103400d00341d215645032401d00c08a0100002d5020b040508680d4041800301040c585044003e282c0e2081000035003a00403498104035040d407009800c444240c50700fa8030185901e41c110112030211500030742191081001c41c40e40f02c017110405500c032800380b800240c4039803642e0302c01d10103800a0400701241c0c2e0260003400215a0040c080312025070007031030104150991104000c1011030080d09111003c101d10403101c3c907440c0c07da0440005160440003d00900c0e5940410080c0180f0340e124030b440c40d000f00da06070300100000c0006c9800b01c400890045085441d00d4440300390f80f1004c2164141d110f0740d54800c01601e000303954000c02c44031014803480da90030320000082c0019a400100030b0040301c1421f80c10f030381 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 94570710 1250 94569460 94569463
    0x20d08070c0210030b09070801081b0108182109040f020f030a0b040209041a030f07081005090304030b0a09020f030f030409020c16030803010807090204060f05210c0c070e040302 78
    0x140341d02e40440e2510504106003809800070104010900d4104c441d582c20009100d8004a0040c1200c130b4140440c0e104002c50017a00c403103452082d40341400194010003080400c0941140900c1154044040d5003030501ca1201e41e00c039076070403110003011031980460000004c0ca014400c1039181c10282401b0351074440c900c89021080e20005010803851540d42d107441c15103840f2581515044580a0810803034107103064001200c03031035190481446803080881c880314000000c01c0c508201c0c3c90600050040e50b04010142024104c010a0729802e0712041c800000404c01961419005400902000500010500501171512128100680641d0010815449681c00001200d040342c030303400da00580303481c50510018140503c141411503005c2e114032020003030003844c0d40114100c0f0041c50448000a66441d000c1060b0b000d28441c66000c191030700c3c075000d4001d000d03034001d1070f2425a616070030820300008015040c80d008203a509198800340032820304501a401c0050b44c01810948144601c185410b40d0001e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 94571960 1250 94570710 94570727
    0x50a050f040e12030a020904200a0c030e2e030e06070f050904020a020606030d09030c0314030d050a0e1509120705070f090c0f180306020c10020d0606020d0807 70
    0x15802655244181402c41c2d409204100e43c0080700604a980d80c14419a100041d4100c0000c2c50710035031400c1c03071840689041c0c0098175211040d003004142403001c4d40d182510303130b8125540c0a4080c004d88908144141e90b0700b041d828181000701c2104001c91910340c0080140030615542c01303041c0b51400b48624003100e0001851940b058140c83c0918455074440800c869500455240700d070401e002140904603035401040f56481100c0640440b80c4a0f034111a003100d00c00c151b444090201c2d4464841403021a00d024502c1003402c0c001e0044030703d854242e40d850030894504645007682240d644241d2140424280900b01e040394103104190002c0c240701c4a0307d070f269421754400342e109005c0001c05008100b014440c0318014211010a4043c04d5525000b100c00342c0041d1781c103000000e01e05000119030030b00400703210000046601081c8411411075031803600a500580d080e00d03d501c20305c1d100700c400d000280010045080e411001252807450920080d1030400350300d28050512000b8403c0209555024411 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 94573210 1250 94571960 94571989
    0x60c020f06010e07030207050703050304030203061e0a0515090708040209060a0f090f060e0103062c0a020904110d110312090603041104020f0a0c11030601060e09100f120507050a05 79
    0x50f40c1890b101d216003030707000b4490242c0080c01030107030a000205000000c806802184e0081d030603121036550755441121008a1000d200014036164008a4000050f9901803540000b466201d46420600000080c003008003c982010018194004000c00c50038840b003596040103040e43d46140c40e90a28440c1c0c04805410b00a82044969408804802c800c0c290002c00040c1841d4030703440e09550b140d04061000e0124545000703507411a5402d0300082402c07100003132040501201c00b500034425103508103c241d201c054010b5542d9102495000c0c01c5070f662004000e001e500c1403880d69048001130041c5403d20a04e6407404003c1c01c400e10003001c940e2600c0d400c9991144e031083d0010107003259140058000d014040c042c200802c404076803120040c0e0403410862420703001e800c0034041088a82c0c1003581c1c48000340110030010340c40c82c0c0782c81514100396151640101280e42c0c08029140ca4000c80d24507030307002c2c0c1d204160819505507903038144034041c8902c030050700c82507400d08419400c01c004949519010900c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 94574460 1250 94573210 94573229
    0x10c09150c0311030f041d13020f040c2d02010b0a030210080403030e1203011706071d221401080105090309060f09030706110d0512010308030408071707060c020f0601 73
    0x1882e0389800203204640a045e00c0c1c5601030744a42e12000c0c003210f00d01203000008800c80550300072501400c1c0c0c00c0703502c00c40c0c243c0c01000d2007411000f401c00d10000d070a03117580c00002c1c8042290351710200d039040d00c125200d0301d004402225a0101041c3c0007801d48040380d5115004006c402c0e024000b588881483c180500003030304150705503484078a4210300415000b0700d00c0445000c0d81011902601c1800300550403240004500f40300d2199031000c058403904140c03001d401150f181c501055244207408659450075100914102004405000c00391000c440c40c2e04041030b40765650201000c146148402a0240020000070001807501e8007000d941c80c423400308503074407030b04001c42d0481d01d07110660704403804901d001d02074500f40d40d80c034080600008208000346c1c11034000d0b4130488100328071540648103024000d8002403c80d0b440d6441e4078000e0707840a001940d10750130400c2941c0105180d16291411400b940342d00550b140058100241101e180f000c414085400c450009011303d500000e02c2d9042d40d40030391 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 94575710 1250 94574460 94574477
    0x60406050901030218041502070b0106080717160e0607060f180c03031409031f0507050c030904090c0b030c041d0c0d05070219061a01020d140a02010902060c010c09150c03 75
    0x4c080c141d661002d136595a81c41c0c0002030301d40c104100ac0000c81e040f50802c0d1140c80040e1a8010306a44286c41520407041c000369850000346080d00070844c1e4407203401e035400d081c940035060201240c0e807640044025210307907450f407101c03038040c07801885640800c001454811078405415070b1885072071783d81444040c00700078810001d0504c0d00600c104803200c8840040032100301e0701304504590072003040e4603c400c1c512803504001401c00350107801118865000300c0d0245192031401da00308001003a512105440060711002c02041c40c030b08520045000c3c0300414040c1361150700e889000c0100000c0c401103145240702a005010342c0c0c10b880d20682c0c11101c01d403000810f082d521594200d1810041d0b040d80503940050320703e400c1c1441360990214453f000300540341403500500303100581c2d491441e00540c07000101c129126103440e41400d4090000c040c0700e44008948280941c0025030290800c0641c02c0c0c0070f956480012036420b0304a030245004007007819010200c8801c814002c0c29042c100d43d0040c05000222 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 94576960 1250 94575710 94575713
    0x905060f130f060c022d15070b07020304150309120c050a08180901090510170c030d030b0103140106050316090b070803040b07020606060315010c06060603020306040605090103021804 80
    0x50729060050540d5105042c2035030b41d107a000038004d8081d44c8080e4003c0811485d00d80030103010b081401107801c01808015010007480c030521418a4404032405200c540c01d11001d00010b1003200032501a0704158000c0d9110303403e148094151002c00003020081c140740000c480300040b24418035101c5072150b42091411140241005800d2520300140100307145c60000d80c102c490b040e40e5814070000c81d016190144a83e80314a5054101c61041c3d95980042200c40001c00c0030304105111410b400d23000c40107030360035018142d000c00c0c41d20b061140041c01007603d9900d04c10b801d5070305100703514014800c1980c04040e9490240f01401d01e110152918404200381c031039154800d03000e0000a401000c800280998401060a02d600c00750820780d404c850b021b0b0703107e02060f0b1191001619600410006200714070f5911000500f4020003803010246041c8000421207101203225880303540f0003081c0782d403005641e0346050420071040700d0305034006501c1101800010300141e181c0d40141c6100740e98844004900391901d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 94578210 1250 94576960 94576987
    0x207140402070f0312060b07050601090c020f0111070204050c13030821010902030a050610140706110a091404090f0609110d060c1b0344160905060f 65
    0x9003840a0f140003c80d240240c20560701800225403005500f10030407515445000d0f003401407040080203071050744104014081d01d507055101c0c2000d41d030940100d9508072040b04505081d9800800801800c12010402c40103508160043c95400030303901800709c1c50300001010f00d0941d00581e00015104110103c5c00c4075901c161148122030000e04404003107041d6030344080410282d0b20450301e042000d410140403601c0c50806802c41243d10a03075845080303040000c900458055003222406070307001034450300424803101c034a030003d24480d0300580d2111016401c00410824200704140880c0c083c91404641401203010310b1400e03404154440004144220f03035060580401b046c503800240e2041c1030b04610030411202c6d52008500001a4441d0080014040c00c10f4054401c60303074000d0301091031803c2090007101d040c40c0503008203842e03494100c8400c0800c6801080300d41300d81004004426444288207006000c2c0c1241d080031061803030b112141c941000c0101e5064050400e8540d8080d2001c10300e00f021704036 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 94579460 1250 94578210 94578217
    0x90c08100c2a0311030c010b0406060804030906050f04090603030f0e030c06090d0804050303130906080d050708070c030b0a06090b03070f031202010b150301050f09010302030601060c030c120c030206010b03070207140402 96
    0x34180205ca07158030500032030a000341481d803090341c8520303d4001e000444a0040403150720a40c0c054940e404001d00d440b2065400c2c1e4845c42103910360303040400010400d19010301c0f07441c1c0554042d968000170a0428200a07084aa40d0fa410520980c0110039040b000c1c3d8800701240c480000903186e00e0180c807981e24003289180550381046a00d400301003901800c0340d10348602c03503048500d818001d001035645c030544251134207250b20000c0005030701045000d0108a4100040c801c283c802c0c0c48034102c450b0790b0384410360400e81c1034501d0700d0102d1f11038800700240c0f202ca0190400c20b00381103024000061400030344a40c0f01c18980300042104d45401400314078903000790b22804040f800600207c0340c0361140d01e5410340592013409802d00c14446038260400030f04010810340e041e01d9014004000c50303401c2481c1a038a040107010110f081100c0e070b419200c0018441070b0258580c0d401915005c99100c401d18001e401d0120503040b0341c1186009004001c61a076000822900326400350070707282c194440c54004940a8403 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 94580710 1250 94579460 94579487
    0x240301150e040612050d0801080a0f080904061806050102030f0306101b080a080a0b0a170106030c0801140708090a020d0c0302090f0f13200103090c08100c2a03 70
    0x3c0c5402030000da0800010110341c0b9652080084d144400c000d600180d81000c0c1c04c1c003440100740c0c00400701100040322100c1c01ea0006004091050600303050310006000d1f1940c94010032500c605501186211094a014801c040e0800340061810454007200d141418000103110b10b11a9010100e8081c0480c003800f17208001040d150080c0111140f0b604007541c440d4020f15500c8000740340e040004252850500c03542402c130310002d00c9004658581111031101807504041d9945955a030400007000501c0015008001e0002e20000304102090007004001031000510420500200008000811001190350032010358112015205d4980d5410180301100391604000d402c4400302c010311400c4a04020030501c50b40c001014010035a42c0d00301464013110082c1d0b4000c08034141488490141f2900341c0303940c0483e42c01032400041010381f90300c51a1220000703500c205419000700c948031885102e580190020078509080600e03264010b40c2e41e4503402600690b030641c1400030710b49800100351180c1c00d406441c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 94581960 1250 94580710 94580719
    0x70f0f020f0604060509010e0f01080412050903030418180f060c030b093d030b061504031401060605030f060103050702010e06161206140904110a14240301150e 70
    0x32901d4031360260182d80079076041408202d00008481c4145865401280c501c281a900d55610761150394940301d040c8201020441440003d0250360340d26241040900014501000140c2d000c440c0707038400300d0444103800b004200b0968007248410220b800c1a6a1540480d44000d000481560107403045005082d01528558400075450501c118903202414400d6400c2404c1c0ca5251140b040d17111000051800307040f01d2891428480e020400700b1a03001d152075112202500c40800204c0e40c1d40c4141040d030040d0001c50f40511000f880070b06040e42403080a028048034141540b0f036007040c402201409034001e21860400d80c0b10800503024034801c0d000782c02c405048004643c1c8a080410300708011b503005c07007800c20000b05022941129080103016200c1151500c401c0da900c1e5900b8441030010142e4010800e5800082c0403c05a429407070340010701d002444d40c0b0910304510040c0000308940d1440204843d0343d92005542500d145110340002c590469507406000c0b40d401001d01010388503002c1e0209116400b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 94583210 1250 94581960 94581967
    0x20d03021c052101060e10030e070e0a0e010b030c100c1506080f0a05190f02040608060a1413060b01111006062c190f0803030103030305060306010807120206040801020d0e0d05070f0f020f06 83
    0x7010009033405032030600c4040c03200c0088110650700300c80740c0043c92981a0300c00500c2e0300c01401c080c14000c0300c0c00c07c1460078440216041d03c5041000200307082c0350490943d0703044100078102041c0450318100d501031000e000340603107d44a4640d500d0642c1a6940361184030304688040203900c070742440e0130981c0500240141581c4400c682d03250b0000b1522228403a0034982c000c180000b0708030400d8400c003558040703240c0130850303910317143c0c0100f02115030740381889140145070f4100c5400704006805d010800002185c01824210003c240c0319600e0b00407008070100b03201411101b04407101d02444c949017500c041072403544804048a48071f2131940b0440c00c85008040100d001300c1d000c40114140d0380a51424400c64651000380750303079810240b0420340c01c2d4100348c030140180f4543c14264240240014500790a29403142030a608903881440b019605690f100b410840e071003400d01c10740d0b03031040c0d16040c401c2c10003210740c88030059050011001004021109680720465584c40d0344805003890107042c2c2600c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 94584460 1250 94583210 94583219
    0x8040e0a0f1503050d03020f070f0503160c05100806093d050f0a03080301030602160606120201200309010302030603010213120c0b070807020d03021c052101060e10030e07 75
    0x180d402c140003d859500a154500d030b1198003900840341c00c2400302c9807035860040903440310350204403e00e10441d6640400c2040a68210f800010071021a000303500e41841140340c4410403034150320708007000080c440504104215991091078a642c0a07245c072092210300021a24802c01284010f030030510694484088608682420a922010f9070001d4075500d0625141d0f401f00190b140312440001d20110003040107000146441d0040c0451140155000c106150703680e40c2c0d5025501c3c90f03044200d5071061160a00159a070061504204401c82c07000310b402d003024500d51540340d10401003814185a0000041100394800b54110740d049021081140b0707011b6228000710720082d6060307400303440c184410f0b1004196035510200f15610194400965403a2581660034013030410401034003601540200000811002d101d07140075a82c544083d074559030784444036800f0f4000700303119660340140240c00b200144078198201e80402d51489007281c8208038058007400840251200c0c50f2000941c1c0503034040081d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 94585710 1250 94584460 94584491
    0x30e0d0b09030c0111070f02130f0603080901030b100807030b0f030604050708060a0b03030702150702210f0102190e0307091103150d020d080c0f0f031308060408040e0a0f 75
    0x101000d00000280028117020010f102c01d4001e046014201c00c0c490b256800051802c07546580000036030890110300680d135006030030201d4400b03034820740e83c001c00050b4810556a040c46807040d105012100b4a03c1c1d424000402003130500f00030035200a260b070311900e5090315642c010740020644402400c0b92094609440c10380e4403000e0b030344a400c43c41e00c11200802c44a50450261072191500074001398100f10301c40e0200b2548802c440c80303402d440c00d42046150f0268403040c0c3c81d0012500c2c00024074401307003122650700d4540700444130902400d91043c0f1000c0c04401d900740c444c10100c1c0361440c3c810b12613011000080d040801617070201c40424034100001c0c1041c1c4418024500ca1000520600209812101803151000e180b07480250301c104205d484c00001008071029210000101e0100c07500c56030f03103401f20307840e0408061480c25564804540504440380c5806414050500171000d0401e0b4282540c0e18203041c0a54002d240c800d10f0f0b000005050510319900190306900c80c12000e1203100351018120 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 94586960 1250 94585710 94585717
    0x5041109090f0a140f030a08040308131406040203071d01030209041e050f0705010903030219080c0d020601090b06040303050313020d0218100807050a090207020a05030607080907080118030e0d0b0903 87
    0x1318030701e02070031480801d40350001c0103440200c00c01d5200c1805590ba0344d03a0031500104010152842051070144032000b041404e80400c0115180e81c00070402c60401e401010f03d00340040c4c1c480000c01c070301829070b04140c000483e41203045a42c19100000c05171243d00d08490812802611340c0c60b08a1018946000c2c007000140c0c03405803140c0c07134080d54621502c450044807504a2400050050b90105840b0f80010544d01e912010450140040508000d00603450f0750801c54021244401a8003880041c00102104e100d101425503048500a14040c91654098400d0100800365503030640141024400c1d520307107420400e891640140ba40184001d0740c000e1550098064505c50210000d903640400d950000181030010b507840245514002403800c80d01e54040d600c800b81c102d8010b41c805800003003c0d241007207410700900c425116a6200c2c60542c0015161040d6940b1400550381000d4290007100c14001d000c0f1002d41e014500041c0b0401c25902144100c00440c00080001081070100040c17601c012028 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 94588210 1250 94586960 94586993
    0xb060f041703090904030c0311070b0901030608070f05150909010b030109050703090308060d05010914030301060f1403060f030114040b15010903050c220903020106030b0a05041109090f0a 82
    0x10210078125074441e50350349025010045030404e4482e0080b40100c0e005000a2141e03c3c8646003144141d88030301c5585051000f82c1d0710003611004042408812036800d40560b6010700314000003440742c03030b103090405005000da91007054050940c504000e00262001ca0440c0c1e900c22010b40044119603540303c8420803980240b04220700c40d841c010101c4c0040348a80520340810341c041e5103046458440004011405146101c200c030300b0741d0f1340c840c07600000d101c50080d1303c2c4815070080a9a140e614142c00603001201d514400c400b00301c2144030305010b5088010940b50010310994281503041c0760790340801e005014003800b40d400e041402d000c01080004020441c1e108001000d03924000c500060015613091901d03010040031038218031110307400c6040140030740c0300c6c407410303074a1079000707507016003a501e0486424500590050351503000c140305000910240d01d800c51501c000070429450703d40c0700d1002c20780a06884c1842420000d0114103451000c0005d203450002c003a0a4940c24521494042c0409028468 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 94589460 1250 94588210 94588229
    0xe070f0e01180504050703060b01030e0a06050702060702061009050a0b13062912060406120b10060f0e04090302030903150103020a080105010302030d080901110705010f2a030e010b060f04 82
    0x34003840202e2180101c80c05554020028001e41f070540d5940000317440003126075030415640b005040350407c810040340c040c8500402c2c001803141482c1c00024203000000b80404195880001444103460036120001c00721451000000381a85805100b2409440c01c051850761019801a007502d03105821f9101a04a03407407a98004003001805401c40c40e102450303150b86602c40c40500040e1030311206c42d000f455011f20000c00000b02c954842c2c000500000b05000e05440f4100c5020802241c00c24000e491006810039060111101e0280070004180301c10205d03100780075507295529401054020425202804070040c203031030700004003841f1000741810900c1f06034403514008800291114040c805d15050f00d4002e070213400f188159090179254600d014003019000d40d40d0b540e20418202444020300a150722800002c1001c0c4d0049280c40c2c01d40310010505015040108014991022543e0b120100c052581c1404900c40484581c4e45005041c5462601e0300404009802d1045410840041050302e1103142c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 94590710 1250 94589460 94589489
    0x60a030218100f0c0c0b070c08010f0605090c09040f050702030705300f07120e040b040501050a1a0c1902090c07082502031209040b090412030e070f0e01 67
    0x208104041c00d441d84402c011481c540c0e40c6425851044c5240034400d8010f0040c2d030142030340c41101441e160300006080d58011034940e024412114280101c00311001032480600009003040001043c2c4407001e0030254144400203400500b5448a4000040300c080b041d00c10007813071800d20340c0a922a4001c5400f01d4041c004c2c400425950300035030500410b0244480c00700321295250000803492036016845100403d0402d001000000e0800581c00c0540401641d952030314028480a000960b403039410300e240708904060041c00103071036455201089603001c17621100c244240304030166551243c0d000740401d07405040740480701ea034246440a0000c5109480005995491140c100e4071130081e524002c0c4507280400541c0e082601c1b0f42a9960181c008000003000340c1610b9000a03d4401440c116281d9201c0201d110380b0189400d109000711a070b025a580720040c9025514049655100100e0300c0500d691019283e10245081045802422441022485040d12000c005204107000d100d00e840484109 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 94591960 1250 94590710 94590757
    0x10510050a1a0a120501060201090209130b06060904020706060b09010801060f0c0f031b06051504020705250e0403080108010f0606020a170d06170c01020a0803150d02060a0302 77
    0x4103900101e490091400942401e41c030780b040d00d5640250184002c208280c003542ca111841441494000e040540001076202e480344103104050300c000303010a2a02480420101c0402c00b01c000300313988480211000c96440f03a102c00090002c1c094000c01515107841d007003000c07130303151003a500406694000340c80c1c2c92031030782e031390722003102da00c03604c071224100007454804840005045e00c2c0300101810301c00d06001c11380c810791881280c10030b001c28600390358098542e410b00161100b000a562803041c01038800b5840d1911a0700c0f259aa215482c442064a43c2000b042009400c0501c3d1250090401c41449450711300380780c00d004000110a010b040041d5103401784401c401e44282c880d80088986640250248030841d841c1c00c41003110314013545d4003681040050781c0072842d07144036183c041c03d042c1804d50700c4c694203244400d14159004203442d041d0341c446000702011074015410713264414142d480d80000c5200240c08a040c503031090200035003200d030115454544a425030041c080413140000700c0001c0301c022 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 94593210 1250 94591960 94591969
    0x614010609061206090e010219020d1b0203071a0307020d09050a0b0309010b041b111612050309031606030516120c110703030320031605030a140103030201051005 71
    0xa00c1100c011892801d82040400d0003501120180c4011450002d40590f03903212880079254001a83d6885960020b1950030f510644c034644441070340f8510003440c02504400d40900142d01070b034840013021900c4e4140404640d02005513002400243c0907140001c0c25079004014103800540d13010f03001d80038900b040d1007520721035131941c000c0b241c004100762183d80c500ba070000c20035400500798980035500d48a600080d6200d030300410340500c84d40c019402c88542141c000801c2821000288076464000c200e00310301c10700c135200c2d2180030f451840b00b268180180e580707882880d42c07181c5200260140035100c07200c4070090713650075464200d40c140d0310140410b5a8a40101803024041014030001c50203a00300d221480040b075110b1524400b50b400e20901716907580c00700914081c07841d0302c12000a61a0301200340e82e2a024000520303c011010001821818216010f8034091810350300c0104200c0e010002500194085c1c200c050807607501190824996180d09009010300740c11a016405200c0001e00001c09080 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 94594460 1250 94593210 94593251
    0xf0406080109050f060105030601051902060105040f020306030c0402090613030b1008010c0c080d060515030a0c09030512030705160506090c060708190203090a0b04060212070201020d14130b030406 86
    0x840c0131280b540c0d00e207001590950005802141001000d10854030001c0c203d000845003c0d2864009084540c500381c204400c0d984242d0030074001c28010300a110382c54500049084201c14122005a1210b01c204045150380c05164595000894032540c0041400813011359a8080e4140c0100d040c034668691094078261000301509a0000b85503400c0360010540e8000078040403001e44101041c880c1e5101c1c002402410905c01144c440c14000041c071164041d00e1250301039a42e018105100058515210703107840d220001c0c0061001c000000005003d10320031421607020301c030051011400f070211400d1459a458048680d5102485181d40542c101c1c40c042050b55000d5501890040c5400b42c0301041e911901c9400c003444042d8803050081c04490391340c08400001400004e403c00d82c8940c50401e0007882c042844800d6603c04004000300f4000d0b0341c0c00324041c92181d01074141042d00880c4400c21066602c00c0008520004c0030340c80c0049001280c10740154091800b880c028400c984129000014000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 94595710 1250 94594460 94594471
    0x10b0f030a030e0a050402040b120f091c1e1805040218040b0a0b0a0f08070c030906050903070503010e0d20030a0c0501090804090b01200c01030e01060801020f040608010905 76
    0x510200384040064841e90b805080200098410344416541c5c502082c140d80054101e4101480042418040d40c007600003141e03032010400c4040a00c5080a41d03100307840b00c56601c50b40e85286005c0c480c140202d4000c0140071416900b81e80e03141004008490700400e0307864410000500341001000c0000c6500d0240207030b4a421002c5101c040410b6100f604000081c034040794400e8001406000c0040d4038200203011b0601c082c0c0c141c95185901018034002071440d10020b1401c82480440d401100200390f0010701441511101d0425603a40e1800800080c603180c1c2541c0002d40c5503092400070502c003400450038180b000010b8039100d081400e500500140b07100042111045644148403e8040310b2240e40c04441c00d9008800005140e203e41c1c8884415a01641050f440ca40e190408070041d5648602e6882540c914002842005510415803980ba04900301d012410183ca4007800755501c0d100390301410040440600842d070711415600113001640061280c140400d15520000a098010f4029140701c2d0303 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 94596960 1250 94595710 94595713
    0xc0e041a0702071a13050d060b1201050403080406230108010c09080102040b0a0c0804090e03040e0c090d0201140d0509070603050601110a03080408040b0304110907050c0c0d02041b11010b0f03 84
    0x103104041c1d40424a0304400e0a201743c0800c9880c0005058540d004901c2c891401460b0120f0710720900d00034030a14200040005035568501010440402d6000c02460340166200102083c2c84000700040d0344245901104010301c0c8014400015080c1c8055001d141401e845071a40c584140e07507100010700700e01a510a4001c4403030100442e1527018071039640c44c3c1c0400d02ca615032a007083e0301c0307000503030880d140e001180c0c1d896840090203001c140e414180440e80070340d00014241c5848100c07008262801f402c0070009042c0806904000c07452000b030300649110340341d00f007070030070542c0f1b080c40c4010b9480c4864030030038020a01e0b250214000794416001164800706c040000e00e462080c65074100c40c00c01c0010402e803500c9900b4400400c11144400046015a00540102025403251420800384110140c554000c3c024100280d0025a0004c01c01c8032092904840c0d040101e9118004580a0a0019680e1640e9400d05801d00c0d0020707001803c1d031603007503020380003084443d51140920a44041e0300c0c400e907030b05 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 94598210 1250 94596960 94596989
    0x1209160308040504020a051603051201090612060b0301060801020d0203040204050f01060206070f020309060a030b18060d0221070608090606010c110f0d050d020703030315030206160c0e041a070207 86
    0x905085e00280b05c640028a4514649892581040100e160724401180000c100080c0c6850408003c143c490241611060401c505440d000c8281040708810400030441901d4800401c2c00b070b50300b03501100041900f00c0096540c2e0251840c840d0096108441c00c81c880c070701e8080414822030100032114180d81454000740281e03200d80605032840d20340e07501c40034218401000250016110407018001d444040e880110300c0c01001c50410204010300841402000340f00c008004040d55162001068550161903400301010110801000161648448490b600c182e4000080e80d90740100e0052184101c1e2064414985500c401142c8203280c496018041c0002c45c4469103e5203400345e004040820001c04040103040181d88007414101c04401c8071000d40c000460400a06030180180c1211a0f4101c02c1e4400c43c40c00c5500007100e500401480c00c071290441e40c0d0b9041040400011200901a6034008052510301441c1028005802d941000008401035011800c65800001e03076806846104c051401c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 94599460 1250 94598210 94598219
    0x1e0d0b0a0e010e011413050a020303040902120604050420040f0203090f25050f18010801020301061805060d0527030307030b0102190b0721020702010f05040f0902030615120916030804 80
    0x158407143c0405a51038060908c00d000143d4041008000822a4407030158071880045e00d955030400c001008140104c1c00c01003000000b43c0a40e8150b0001140c0543c0c02c40c40c1c130301c49404100103116501d01c00b045103200000b0300c051000c00280fa08060b60200c011544100800c1c510341d0f00fa030025451420726103e040b081480b051404c42184011007201409103000c0411000d00441c00e00420703030000070349940c004010710505070700100d1505030604000d52104954504404900c0c18414278148500459072800420342c0c1c4c115107000440520f03c2403030000d1020201c4000c0329100e510980306400468608000344103154000f040809040440e05c1e075603d40e1412503100c0c1c030007a9600400d00410000c03484000d100c0b104012070a4201880e8000d00140c940304944005001110030854039010b00000303001c1000034a42c00100c8005031080c900d80940c0fa0380750800070601c103200c0503468494881000c582c00c107a4542c2a0a020310030b404036001c8441102948080c042c0401d2640005040306c0410030080c007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 94600710 1250 94599460 94599481
    0x1c020706090504051305160510020307081b030403021e0f04050f06010e0103020d0609050f060a2402030f0313030e060306060412050c0a06020a0c0609051e0d0b0a0e010e0114 76
    0x3c5c0e01400548042c119084541d45a40c101040d0b11032408031812160024040b03400c210401a00007071172800210304e005c1d00354944030080d0103200c00c42480305040c50f441504c107446c140151002164060050360a0502c0303000b00901c860f941148a80c00b6062402080030680b4148c080e650080c000203812640e1912128011912340409014040c103058080141c0f070001c01c003900c220350041000500008a905001401c080c5001c000740071b00340f04400c2c41c801030200340340500c801000804803c1241c14070b00c0c248201030b802d40c0a00e20440c66189004000c10000d00d038000e00048101d8466034980b0030480c802c0c001c101c018081500d41c42d40055050100b400051440480415810300610442e14010807140018503001c0c52a040500140c002c0b01c4071b1820004404510b0003d4000c80c2440d184181c03c0c8004514107124001954030701801c4c90520102a032601c03241ea61485130401342c18112032501042c020080d00b1f24084a211035031828014031340320f01061007032203640301114412386a192540310481 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 94601960 1250 94600710 94600721
    0x60f0902070204061a04090e0102070317130804060305091606050301120201030f020d14151f0c05060f0618040f08130902040905040605070e0a0902030a06080604051c020706090504 79
    0x40b030f0015034914012500b1401140007210400d040c00d403450307580d424602c000c0e007a500000307142c0807075a00510400000a400440072034500da550031003101743c0e40d10402c0088513011a00070240010b00300180100c1c640b07600d80c0000d44074402c0001114400301d07807103070341026000e0944a4900001c1040c8014005400e640c100590058014135000c40c1c00c00b48c12140000300ea00c2130360b20a400300c0e0b461481220700d16042d540585d004900c0d004415640203054041000d40d07042c8003494518403041c40860300c4c914001e80300b41c0d1003a6000001c03600540750010314450000e10617600e6500c210300411450034000c0d07100d0710f5544502d52246220754044c2d400c0ea1468169000b0920411800c0200540070030002890310180004000000700411617080c58184041120b10282191040010002d800101522103140680c00c0313a52102006a80f41d54203513810b001805240c0006001d801124240000c1c02000244108880004c9203031070052008504d090340e0b0b41c45c480c85907602007803c04904100c24940b0fa8842c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 94603210 1250 94601960 94601963
    0x5030603070b280c05060106140c0d110c03121204020402090306090d03060510080613290a0f050d031103070609150605030102030705070803090c0307030b0a0f060f090207 75
    0x1c6844203620b40c035204020303400c07a020307001240500f0003900710b411103507840c00d485a601c181080b011860080c0c4a00d9210707035050145c401440381b020b40350005d040d2004200c1e014082420181c4410720745c140c40c000d00ca5260042010b80d140b082000940c02864003044065100c284290018a41260300290803d0448010300603039010b5400d2040c02140c0c4c03010700c0030038404c2c08403401901501c107012034013404450030742d006503000d21142d10842040d2504841695000702040361080c80c45101010704801070b2540480c0c1605000300c1d081010008081c3c1c07040805035800031141844100d484a21703001d0300106511802c0e5011301d501b0081000f103070003240007c0c00c00e401e0400781e030310300151740c0c60312020744140d09000c03030305107503000b00c600f21850183c42680040c060071402507103542400c0da401072060142e0003001d0040e0800201003404031500f0403408811007806010744070003581e01d0910f00340280085400d8102c3c1400d210071880200b4192003403100b5511900d094540c0c540c05c010306c0f00c00941003100d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 94604316 1106 94603210 94603213
    0x2010c0504050f21010c2102160b0a020f041401170c0301090b06070b0c07030207090504020d030c060f05090c100302030c0f0f04030803090a0c0506030603070605030603 74
    0x403c40440c1004035201c18544605420a2040925400c500074056181c80202a03205400440c0c2800e2602e054000960040001301244264801c203018030f0702c0c00070305507008800551003525503500518101030041c100f90b250303136003808036502c550004a0010106203050741c1940c0d1101c00004d4800c1411030180090500c41d83d0002c076808113000e001c2607103444201007050b03038840c4030664040d1074011074403002c0b44c20024035125050b80007a0040d0014020a10701250f55080c0c0d0190303a000316801b4080401d5032265840448008003d001c0459010703403900c0584501ca80640540d900520901015040c03a40702ca0003049a43c500104d404c106043c01403003001003d146010980300a496050702c540c0c0e40702c5107403e07100b24174400c40d00000d00c010004414012900b000042420ba042d10907081d00000503215400c000319404103c5080394103601c243d10622826102e10007071500050040c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 94424460 94604316 := by
  have h0 := BRFrame.cov_init 94424460
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94424460 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 94424460 ≤ n) (h2 : n < 94604316) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
