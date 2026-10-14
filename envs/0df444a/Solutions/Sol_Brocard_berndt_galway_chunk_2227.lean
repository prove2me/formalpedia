-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2227
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:03:45.119988+00:00
-- url     : https://prove2.me/submissions/98fb401a-9a08-4b9f-b24e-00d0a5ce4ad4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 400359712 ≤ n < 400539568 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 400360962 1250 400359712 400359719
    0x31113110a030b1e0d080d060b07030c0308060319020f060409020f030901060e0402210c03030f07151407120b06070b0103020f010914010509010908060f010e10061b03020102070609080901020708010204 88
    0x50b110344c5c280ca1500022042e444007001c81e00000500304907006030040500100b020000c05400180848030745109407681d00d9150780d20420b0669501032155000c0c0200348500c2148058244500c41060a00000e050310b490030b921359400d4001d03a48295284103200800108000f8070080a1046101408804800300c2080c1002c0c0c0002d04400000402c4c01e080c0c9081c11b90a004851041120f1040c0c0c803809070135640c451303840c0a140b040d150000f06060311228050300013012500094403410020510f441c20040c240e841e0f5107403c960400a40c1400e0a48a644d00f4004d00c0ea0364403403014154007441052001e02c1d941c110b1040c0160121250092814070004813424408480201d031241741000003844d1498507022064012a0711440c82ea0080203180906400d02500031031800016042e15100600010180c403001407034103c003034a0b4030400000440342001540345d464010b440300c2e460b40c0684005070511725281c40b07040031a00480c0044600031000503041c0c00c503503010300000f0000c00808000b103040502d07 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 400362212 1250 400360962 400360969
    0xa11090a021c0b1f110106050108090727060305030712030515042301090e06010f120210051902070303120e0a020d020d0b0903070501060f031113110a030b1e 69
    0x102d1811681e280c2c450707078203905a0f21114941006055148220b0800109509000c0d00b181008202040340b075090035400f203640d501485206010304e4903040145500b03442d05090540740c102d0003240714010110300046903040e100b0340c00f03160701950092000c1d50342c50b5800d00c2c065500c0b440144209042c14282400c02c58078400c4190003070400c0b88181c40c00f10f1200d0400d0640d48005d82840d810b02500312600001003102c101d281c0c8150307800002d02c41203500603622000009010149032289030441d9a04484400c01410700412041c5010040c3c00c1140c20840c02142c0b01c20032044080402c001a0b10012003042071590103a90301e160b00e1800b2a00308100294415150f85a02e00b00c074010740a10b0541d1503180443d11042e2480c8080e07078022001384002d0414a42a64895101940641c0d070741d030030039201184e421310100d402021254489005040810564103204140700c12508000a0075540c04003860000c00c00c00c000d00140031603a0740010307140c61010070801401c41400d40c00f0f10900442c018a0380a84 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 400363462 1250 400362212 400362247
    0x306140a0506030a05090c06070b06032103071d100f140f0708030c0702121c03050c041203020a0c141302040f1a1e0c010c02060708060d05030702030a11090a02 70
    0x448044000c03910360380e01b41900b894100c40c00c0000d5008200004e03040c1c00c2c881500704e014061681202925070000d007101d811403a41c0d089640c1d500010f002000841d000c1401380164582d1049c240e44500359038288540000d41c486800d44008011841f0f5002e028001ea51044da0b10ba88654840181804c1c1103125031000824012000010b04001002010402c1c5030020703c1a100495402001c01613540040004661074908020220604640d00e52110195034000e028482c0b00d02c1030031284c103040601d024220300004006075016020f60040049900c0802d9941c0c1e0f004015240e200c2c10115141000028400c07240907081c42040018414003040c0030300c8140c101910100ca08082031450714401d02e13400e4480d80c0c450b00c0054002038203080c082550380090b144c0500600c40c1810700070014070403161000c0ea22001c00700c8034000042c020000050140c070f01200c90810250183e41240d00701440ba40c04240303807070400002501e81c030020303079071450461a007540c065502410919040d0309000703112440c4a000d8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 400364712 1250 400363462 400363471
    0x60405090c040e010207150212070203090f0d030e0406080c12121210150f0e040b012a0b0f060a1a03040b1b1216020109170f0f03070306140a050603 65
    0xc50703e5824541060109405881c140e5811500c519101c100418246000b035010701a480c004046200000e82002c2c00401a01c664280c0500a00c84010100c0204909252148002c80c14014100940c10300c5441e0340c41044041c0c00c1140003052500024020031545060b1126011010740c0700c00030883c03180341410300b95403500724100d002c5205c0e0b40f21b0b94200024800b02c0d401429010244010340210142d100c942c12300d000c1d100d034803120900c01090081c0800d40b030000502c0c1d40403031034a4014980084103500c006070510400000101d00b200e8555074a2010001562240580c60450382401514907060070460008c08102c9100c082203511104000c44502004002410001d0f81c0e000049542c500c90600c1528050400f038029078600c0c807180c46110146050b00d000d0020346942070807260041c01440b401c00401e4020685003400c00141c81d8900e2141c0c42420050740d0a1001c5c4031320700c0e8603000381c00a507000742540d8401103111030a0030070346138103211a400f0325803088103a802c0400c0346450300011030390807 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 400365962 1250 400364712 400364719
    0x2010501080a050709201210090203010e13080c0a14071d07140d05070338060d0207020409050d03051e01140a0b030c07141209190803040e0a05060405090c 68
    0x51b035000e055007035462260700d081102180000604000002c061000583c4980507012007110060b031161552012800240a07400e901c030b881c04007290318800c2c1c00c401401018416100c2901e400700165825040052166081b10b030b403607031201d00302c00c092014044140500300c20f030103200c00301c0c0c020300c0400e00004002d0300c040e0500141450b2400301c0c031074020444054980203c020300c114144103000030001d0115440400c008404800c50b211400074016441031012400e6452040300000c11003000f007558044600500c1c981e508003c00c00c0140c0315030060105280c0118044c05400e8401d035000b03000c1e601c00034424468490803503068691340b14503203203807810342d00318500c0c0e58015514800441d04245007600724401114001c0304100d540b0042c1c20040004900c00d26003248150580d4400c1d07641e4015180e9640350005060100b0040c6040101000b90103001c6410030424190b502d00b0700c5030560384a504a0b642c110760800802100d140d0b1070084170b410041c03d6074100450318019900a4580d035018890380d10 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 400367212 1250 400365962 400365971
    0x110901081e16020c0619030b0d0201120c0314040605040201020d09051e041508070501020c18010902070507030b09010c1106060a031b090203010f0302010906020a03050d020d062402010501080a050709 87
    0x200300d4402c01c2125039010001d88001c1d070301c1240c081c040c030700c461b05500b1041c006802d140d02c801e00e07070078140300403490154181c48030388040007810700513000b50400c4d00d01d4100f0585c2d0340d010b15034081a00714000e40554000c800000c0c590800b0b0000904050380c1d400d040b0700f440840c0404100300e4480c0e0081c070030600c4180e0180039108501d42c000030013a2007640e1054411440c0d00c04041455840811000c086907000d030210742c80c1441e03150a20030005100c038600760703021200d407004105a825640040001030300c80c5003590b04968032541c401801ca0801c0d1031612407a9900c0c0c2d035504000360018210241d02c0286002000d05182480004001003000e00005114000040510900c4142c1490f2000a807070f95980940d201d40e15a80110402c41b039070301c4280e0001e10003082c0040c003140007040d4000540e0300342c0c0c1c1c0c051030045200c60f2040070b90b00002050f00c005503102c0000a02c101c00b0840d4090032810000003d010060403d402420f444068002090341d0f00f10602c0e9500003940003400200b02da658140209 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 400368462 1250 400367212 400367251
    0x12080103050304050616050d031b17190e0d05090103050f0c03060f0a26010f061220040f0e0705120c0d060b030303100f060f0f0302070510110901081e 66
    0x146c90f03d00600000c04610800c0340965010790075404c5094030317000c904d00344070842c2a02c800c101c41c1041116151610403a544000c20394190306a1001c108400c0c0d6521701180101d03a1031403482c5881c001011280003d00003103142011507a06000303030340d00200b4188141d03095041080d4644100d01c0094107a07889a90341d021010720f03580300d03214084000c0441e25442c1c6100c2c0d00810a601c000c451180c50f12441d9480c1c0316003a080303a40503101780401ea854442c01c50340005420780e980b091034000c07803940c290704440c00500c0003603d41d11400b41003074246138807001290098204031410710309895604640d00c50010080000c10800000405d0514800304450291401c45c0ea4100b08004002441e01c20350075001c00020000c2550388a45908200c5120059009100350b6800044500842c500501400140380c10300900d100c61103500074104050140c41541e600e1441661140304035a10140c408041c001c000c20503c03a1581c0000000354044080c080c0d0080a208081c444400d03400003c03c245032401e103120701003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 400369712 1250 400368462 400368487
    0x312110706050d1a191d01030b010e04050f030d1a0405010308030c131208030601080106030908070206031e07021b0d151107060903031b0e0d03230d0603120801030503040506 76
    0x140c510010141c0001c8503c0c17a80c5038001d044041d14011821300346a2808000a0503001102a90481c0c0d04003420180590a20801902d401c00292044d41d99100d14103204010450900040c5243d11107483d0002d408681e1110003901c0b840c01c0031a061003280b03400010004038080b001201d0303000c1ca2107074523a503589404030303001e922003030082c1c00c0300d50b185524914290400c42800d0045015400907203502c42c06a0307031103004030181c4030842d0b40103100f14010f106202c0141032490140d5009140c1d01020120b02d0b03240f81c82801d0414007102c0f8140107a001140c00f081c250028035082100341ca05450a2041c292540c44822404100848841c403107540c500010703903240801d01c1940e90a5500a2081c42304000f03e060081c040c1505040c5c00c550800d02c03807500070780180100080901554060a540c0c60241c20f602d0075030340c001111440000d800b0416180401d200208402030403040c01000b00002e2190a60070a04070609a00c581c120601c1072220040c4007041000050790200e41d81140c1040da02d40c3c00402e503 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 400370962 1250 400369712 400369751
    0x6100c060504050a020a0b04082a0405270309031906140406090b0a0501181505030d02030c0f0102030c1606020f0415080a05060109060c080903070312110706050d 71
    0x40c000354581400d12041000110f07031288514000c4540951560700e070120a0306070b02c141d00c5084055444061320800075544074106c8403903d401c0805284050207910003003016680d08a5201148201012954041c1258203480380c1529052070b0013541000401c4001c41d550b000320304200c0c03c0029000c10000104600c5800c0386840304040c0402130801e00b080d19012003d84251002103551110010000310041420300c0b52038103c0e0b0102400000e9003011a081c04010940c1c109084030346e294280020400b910108295916011198010350361011031003c003c2c20041c04943d043d8039039004006100c1031031901c50903110b965404441c081c0a11286180000080c420103004400d038046c082000a0201c0a22800d01d000c0240c6440c1c1d90103070740e550301800d0101c61040720300c90b001c03907080101404030310b105444240e2410300c1805c24510b421100300009240000640c41201c642d410088800d16003035000071500088001d90300200700517820504040c0c000d009120094180c60340d54a40c0300548900c03000b4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 400372212 1250 400370962 400370987
    0xa0305090301110f190c080306090402040603201c020109031506080703060608100621031b06020901021506090412050715020903070b0c030306040917040f140105070b0610 75
    0x1403244da0748010a040d0b1909401001d400f94032a00500005481d842c000c1455070511503101a034189160f55940821246042c00b41040c7e80081d42c0d04008000134580b4611003100f124881300c0102ca5050381000c00402960b800828980000c22100f4040140d8100616009480c0c2c051045801e0045210f000300007008150b01440b59840740c410000180f20060f0b00c802c0644150310b05031354030506585415802c0e00e01510400c03000302e03d1226a0420500c0040d041c01683d403081ca09208003541e440b0010414800c0c1e0f003402d81e122627000868403202d68040150200e0340c0c00307000380307504140341520000d5105c020090014240061030b400e01240f143c401c10440760740680c8a20302000c4c401944034042d0094000d80502e40c064403900c040860b449000d481034514003007401e00154030b9a96503405000103014081da0407900301b0a6019183c01c0d0302c0a040180014146202400f0282881c0589064004011a011505020f801c000b072002003040282d03002c1c3c3c00041614081b8107000402d1045981408150 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 400373462 1250 400372212 400372241
    0x11505060f070b070503100806061e06040504090803150108090a0809041e0f0b0f150a09050d111005030405030711130f05090111121f051002010f0f0606020a0305090301 74
    0xd0401c003a190304503001d117007e081001842050b081c3c40707a1040342d591500f0345003940c0c00303040320807000003910b240c403503204030400041e1980e824184c2c2e82020400b41c8184090495035004d0100c100502c19082c05a81c2c00080002d1034025058244141242d1705c1d8a81020007030301c00100001c40f10465199900210904030210070b054050443c2c1c031014900511005100d01505814089049181c0c41c2000060310619401031620407003030b030b041c07070203607a9584200c11800038401c04410008032941c40100602030280911a070818182e04201049201451003d200302880028820b000102d04000251035032142e0104403100c0348440d5038002000001040072040c0442d05141800c0e141e10314a07000a4000d15002c0300a01c00d11044a210140342c1c0200c0c41950341c00c0310021b0001d00e80840c5140b001c0310300d02080001c0703010280c651006c03400402401034510090f0f03449003021000c065052240002c40c0b8103030303102007142908020b40252074500450f80642004408140000e40365003c3d442a01c0480846 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 400374712 1250 400373462 400373483
    0xb0d020f030408091224041424072d02100509010c080108070608190204091107120305040c17010f0504030e010807080118020a0c020d05060a060503011505060f07 71
    0x189800c04059114295840c02508001c00490306510001055180c1c6d003503ca0407015100c0c0d0356507803015040402007054410414090019841810034040705071804036005112401601d1684010020080038042c003040150b80d005000c450100300c01d25001c180b04031422100d120211a00407440e00708040345181c10039283c4014080d031044154044007000002da269410a030780c0e80d80011f03485030003030b10903840490400130000384007140b0f40084000d41c0302a04001030030706440c0c4504004545090f0700312a103010000412100744001c10f040c0d00080c0f241e62805108a10389603860842024140c4901040c1211140050124903029044114000030f0100b0030403131482d15050051941030b64034402400b0a075a40041207d8501c00c0c038603d03041c2c400706103209041c0940c20081c00029030004444004010740c3c0142d00380160b40e1070030350703208240c01840203007545e081c00c044c0c0700100c51440d8010b0340720760b15204582070112084440751040324404c031000e40e118500040c451003288262a801490702020 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 400375962 1250 400374712 400374721
    0x503060a0f200417120d151703180d02031209010302070807060516050c0d080606091201050a11040302220e07080d140304052508010204080f0d020c0a0b0d020f03 71
    0xc2c2c01500450b981402ca08071580c09100320161102c8603c1c00714051074204005045c0a480c0b107400111680b102031071000c401d9699444821000c040a00c4560190341000442c1c28010450030385800342c001d412121407482000560000f0b0303071003582034081d02704c200c40401c5004460780030794141c030001c40e0444d40081d9110401c1c07030904001d05040b5100c10000031040340015120f0b10400540d000d9454020091074030045c402c4066404d000010001903020700100449601c039125550303254002e040c000c00100310350810050b104165078131144904000c0301c05110810250b80c8000f200746018146850310070214003218860f9000e03200151817405944101000000c4243c1700040e5081c01e0b80c0c0c5551030f91041480c1030301d20421031209440240042c2d1200c02c120039450a01080c040c20b40c081c420079500c0d501e41c0d0307a80160070390b00207034400022a001445030605d0580c082c0301049485c4800d10180004e0400c4500040750780030076024804400c0c0010444d44020303078080e4100c480004440d009107840e40b62 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 400377212 1250 400375962 400376021
    0x10e1801180c0302040e0613080c011b0305040501060608070c11040e0d020a030f1701050913150606080112030516030504080703060f0e1605010c021f08041703010503060a0f 76
    0x40b90700c0202d0140e0300d46050b0303030780c103007408102c03140541e04a01405c4004040b80c0c0700c00c103181d080a41d121072255a40e9844031540c20100700c680c4006001c3ea00d01140c14a4541081800c441c0a13034004014482032604001409920001003c00e43d41d21042d211601c61054022034014000f45186140030710070f80c20817403134492300021050640c501c607644000031940344c1d80b0200c90360b802501244050082d08001800140741180e4500e41c0000e00e2665884006a90344500034016100241110001c0e9200000d100b125070010106002d00350a44c01300c0c03400c038a1a1b40c01042845020404800c01d1034900460041511036011a001402001c0413a142e0781e469043ca10014280c0482d195134961070903480c0c410520011038013070059a510441030a01d03070300c2d14006417180c000c564812a40401d50804401c0740e8242c80781810050790f2207599003515440c040c0307458440d4036050302d22034882400078001040250380011390f0701c1c0c0c462009000428190341c180c5a04002e00142c00301c0030b140e41c1403000e01511440 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 400378462 1250 400377212 400377233
    0x2a0d090c0621061a0706020918011401050708030f04020a08010f14160e040f110c060f09070807060f050c06090a051002040b0301090207111c05060f010e180118 70
    0x4484040d031012031018015200032101103105134101100407465110407501c07040e000d00840d5014038400b51400321000000b8111068a40045400001c02d000510103240464843c2081110a003011464908261100710550000404030412441810300040854513034000c030400502c0c5110083c040314900b0400040540280200720590703880740d80c0000e10070f1408803030301caa040c070080c2c568204040b0b61900b840054000c03090600326098403107680c22120a082c40080c081c00140c0b401030140c03400c02901701d20f000040034086010a6000800a000d001404110031003128218240204000d4480c4420b6540703008000d1100907900541c0104059844040742d8041071610138400c3d40c40c05100102000100c5c0107600826082210500c018041a03c86034001c14125019213160059403618100207080300c418100c12440b078a400843c001c0400c1300420440c1d8000f482c007a00c101e8158102004141519001040000002107150740c0c02c905110070b50188a81031424aa0000c0d00d032100c5c02d103c003070407 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 400379712 1250 400378462 400378487
    0x30f0106060f170a050603010b060a050304020a0f180b03100615020601090e0c040f060806010602031e07030c0602070c0905090d08011e05060c0c0301020301031a2a0d090c06 76
    0x10b0515850410b0030303204143d2000c080c1c40d81100030f4110b0b16184031280042600030800c40d015036a4400c07840c010340d9100050200e155560303a03080d40c0c0c0e28007481032082095155105042d0560101000c1c0320003400314556844881c502c18000502900307410000780f802a01e000c2d0303005010300c6e0000c041f83c0c0c079800f03a19209001055800b04c0300c4030390740c2c2c4410008444507214112500d4000306201401c3d4642500091860a020a808540180c980d40900d0400c0d8082e0b2002015074400034144007042440080b5858402c800c0c00c40700e060124940b000f8000c410040b80c000c00c125030010b41403041092041017900a0003048800f000545041c5841c03036600c071048440380001c50b1660000280008480f40c840b4030140200c00b100700c61a1411041c00071980010410600f00e004088081390035840902c003039402103000740c000c0d2150f42c40c0020400a0300074043c00c2008100903003040c03040f0824650b426022004001c040080c0c0c1d80c1c0d00d40902a00a14010000419001c0b040c01c000039510361001e1680d006 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 400380962 1250 400379712 400379717
    0x90c03061b0f0f0e150a02060702060c0a1718070e090c060309210f0a080105101e08090a020d050f1603110607061b02101b0c020607020a05030f010606 66
    0x20700c21075640aa5000a440d480480029244020b50354807510846072000e071030074003070540c030310b600e00003001c03102d0a402001d40d60006a00404c100a10389504100288d044903104032400d140007400031008000000314558000900c01c2900402c005950120b0607880107044401035031422134890028080c040c0d016900b100c2d1510505108500038600030040f240a040082c00400460b0303ca03904007a450304901d841c00100e81d009103c43c018401600e40108801e40041d592102c066051104100c0802039100b4000c0810801079041e28049030f00c1d501107242c1c1651420852032603079a00750715920380381d000c8400070340181c0000d22000030804001100100000958203641c051518015800d0703c0c4c4085210103014509001428911420320000400d0220700404e80820b451003040c81582040052500040040c1c1c02004030302030b00552032242c1070340c4032112102c150304400007000003809034880b00406031044070005401e10442d40c41c00e03401c42c0140809006e4414040c0d41c00c56103030007803e151082601 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 400382212 1250 400380962 400381001
    0xa090b0c061b1204060b061902010606121b0c1403070503040504110c0a060f06052206140307211208010f0608390f040623070201050a03090c0306 64
    0x1480b203076030019180c40845104403560300c1e9551391540805880e4071001250002c80c104003004400e01d91111012003020543c001223107040c60000014051100c1d00c00f8504818602146400c000d4801034420301c000380c003442c0c9441017541074180545400d0131440703181035501c00010b2480030001c012000e0412614120b80400c105542040c0c00f80c59403040e85c04180072600306041c1070000400a92112200a0080200003299600c68012507150107071000c0814038050403c250b8401c0503080e00820000e09100902d22850003143c0020964502c03007409200500500500d15034041c1c08800880804c1c00c1d080000b2400400680710082e1200c4400c4c081c0103010400c14001241c032601416409000c0c01172890807509104440c452110003100b81d2044000c03140c141412051804c0e0303400058081c20b2084814030303580e1454460042c0a02c0e4a00740c868041207601c5280d02001601d8031309a43d00d40d81c0a08005960f128210700440040002c03003002040c54402140c08000d0040640c00840c4407981c8802108 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 400383462 1250 400382212 400382251
    0xe03010e03040b160204050130201f03200a0212030a1d1f1b0f020f0a0503090906190b0d0f0e010c0318030906050a090b0c06 55
    0x1426203012400940c0c966004020400014072114004c14803584035600d103946254a503400601038030020b80c4200308820488820310056003144884083c1c20307580c808241d0402d2410b40c0c0701c03038104c91100300700d82c50a04d00000e2800f50b602c034484825180b101c521040e41400c80443c1010b80240500c041900304640d042c1081e40c10003d025003224500889500200390f801042980010729a000801c1d03c0905525a1030072071004a184c071007040d03101001c0d0054242600c45034031020110261109403050217040030301081d9441150a1948403415651400e000307051003581099141c80808075035404030707100302c40d000d01c10303c200880581030031142182c0308a82501c400f41041403c010f034100c800c1e22030b403540c0001c00c5008602e00041084504419000c11060b98071480328080311081c040700e81059464100340e040b0a5450300c1010038407100c10303102d040d404c403e54034001c010444901500302407003c0054071200880c0120541d4000300340610b0b80325565041d5804040e1a01e00580700c0900100c1481050f0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 400384712 1250 400383462 400383469
    0x906040b0702030c030d021e03040c0608060303120a090302070f06080907150203030a0e0f030d06030b010e040f06050a11030405030a0f08010501210213030c0f05030105061804031202040609060e 85
    0x1134a106104400440c1010541c0e50303940b0095000c8d20181c0091840b42c0f400805001064000e10b101c3d41c01041864210362030580098083e17180103101c144a0340082114005016842c6e04481d0412a0300308001509526840e003646040e007990400011306510b00d0002541c0340e80126400e00c14030705c000a40707518a54510001110814070100103015070418030009140032403a50045204c40c800004868207010b05400c0349080d9803103004402c440320303101c5800f401882555070342c09005181d07100c07403c0c03100d10301500c481e40c86060000c0300070a102c1c1c03100080b0b000d81c0b0b100c0d002901840110412581d40e42807031300c2c08607620740c4031402001c08584800381e40600f0742d0080e20024100d5806840d00c034102c404900700b540e040505a10b0385038030b0980c2481903011110120703003444080c5104a010b246058189290765940042d00e43c40b1070310036818201009116161041219980005c88101d48000d80301c0e8641525461446000300311428400300d000151207a04c0386903003045030070031349030303950000b0854060 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 400385962 1250 400384712 400384717
    0x20f04020403240902010c030f181e050303040302030601031b08031b0d0201060e070507031205070c140d050d0f020909100510020307050a080906040902040807090b0402210a090b0906040b070203 85
    0xc6c1c04600079401c110046801103103030010207a150304c0c15a01064202001300c000704500e400c80400c141200c15101403d0610000420280c101107005604140c91540000d9881d101400000d014142003440300c80c441f200c0100c000003074540b0030b0a0300d031144407203641c0948000d00d14900003045d104030403041411a0041c4110000d0f58240402e9241e103a40c1d03484140c03083c0e80014030072000c009042034580100440303803260303602410701036980f031b0408841420080c1e0050145580074140c1d8000c004518111a0800210307403454420702c03404298904c01d40d800700000e01880c00c106401c89421010811000c0e15a000c40094800450f01403002201c1d884080780da0b401500c0300101a81d2004e4403c070003049401014084514008000a00c0c03d900c1e01c40c120300b6600590b1200107250b012a0f0700380485d103028050b50f4107040041ea01141003c0803c9202c0c104680c0034414050404101c0c00450140841d0f5001200c16642007813402802d401c0090060765103800484060700c040032017002160b1041e101104 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 400387212 1250 400385962 400385981
    0x4020103140f070e030f150907080d0c03030b010915121b05090409051914010605040b1807201b040c0c11010c020907081b04060c030c020f0402040324 66
    0x12460780b81d5501002600c4549121040300d0b458403d89200c0d00004604024405500c00024008003217800c1ca01009490191070350002c043c103030000501102c00d40d60040040301115014600400e81480d141c006070b9400f226a000000f0802c0c1984d0080111900901081e08480251400f0481c0100c58080c1c480b9403083c00035620000b8800f0001d511951410b6007040c0c056900490644e00302807002c0b624405203e00405017164480c0310012242600c030000c0c8159001000d00795070a0080d0800540012010100360341210500780c1d200000c01d1295204c1d0304109501112101c1ca2000b40c40050a000d94035155821403060304003c1c101c8c48416800c10b0300420b152080c041d280c2c02601003040d5124100c680d450441a81000a100c20180240c1c2d83d9143c035500411441c0c56060f442e0400700c240c551081c200d40c00c00303202d00b07a0403c801c00140c1e911503044001d0541510307103407441ca81544006050301117407041c2180c0c01070001c100402400b008003146503034191100c00c141d0081e81201603080640f181802d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 400388462 1250 400387212 400387231
    0xe0417070c09150b131a0f07030c03030b0301060b070303020a111f150501140a020f391e060403060c090f0e04021005071104060609140102031c1d0f060402010314 71
    0x110070001c510180c6e4001401c1858640707201c0c1402003002e081d410395007080c18250006100045c0120506030144114005a44254000e11031076003002d02d81490703841703028001801c0560000c0c03242d5141d0b106200007680c1c4044681601c0400003459034a00c05240809540c00d4414980003200c443c101805c0003400450700181c6800c1041103111480c003c1e41d03041000083d003035004946400310150030520044504860441500142240c1000c15454180e12400101405068443c04041c103540f0041403c80030211590343d4455401010f0210768940502d500040c012810003150a84c00b54100101205594201c003202d141283d0f80e2801d814106001d6901a400c4103a00510017182445503008140c610b0144000318804606040818100d90b084d6101c80d00058110740140214030400d50400b0103044240300850078030010752101100c0505185c242207030641c0e28a030340d0350844d500b208204a251036000030b0360845950b5a4420b511042c084a049002030f1408680005110340809a035004500d110b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 400389712 1250 400388462 400388497
    0x303060a0e060f04020a020313090203010e0c03091e0a02030708060a151d06010905180a0c0507030504050d05070302122b050d27060b040e01060e0417070c09150b 71
    0x1c1c824003000f503001d0b080e09007c502041012422010140101900800d00d1080059496141c00002d1400c140c0150900d003500c003040040c00044440002c4aca280c1d1000f80c03003400c41010320400e655141c4806c00344000d4140c020a900050525804512135106a2aa0381c0034000c0c4042e05410600038103050107400c08070110034465452a40c81180150392150044c1810729030a600c42c1e0019400c10b410036801101c161343c800401c074080040740070f080a25002420010f04107030305e658004d40940958020180036048800314081400401c111a00c011600030b00900c400359043c43c2c1494861172a480e80c0c1c0744001341c130020100c9000140c0c4000b1418000b60341d80508201c00690154058680e0204441c8181900040b001242c0000207060406620840d000501c0c10081024003090f01c91020001e18142d25226042026540041d012503100d64003510f0008881a007c0282d00c40380141b06000e000366072029004a028035459005844418030030302a5444180c1c0c40c40710600700d00c00d08040e1011045078 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 400390962 1250 400389712 400389739
    0x1507080f0408090405040503070501060f0f0b09060f0f04080c1012020a0c14030d180b2818020102061b0d02090319120809010504230316050303060a0e06 67
    0x14042000d07002841482c40900e810400d90004045c0c1e407068409660700d4000107602002c002d000d11441c001421104030084440e45440c4030048452114032802185000000e940c00040d03036100c048a03607005030b0002c8980c441d59815041e51003038219020b050700074810f03000d55a000d0b250800349015103c02c2941c3c7d42070400325102c23959001e50011100e803c00e1191064200f80010303145a601840c4148400c0203680700c0c818002c0c04000e84000c807a1102c1d9111505406201040e46203040503407107500c4c1c010b004080094200181d01d00e11441c171544a142e858045440804074001c00300f031030124002d84c00c646482d118044c6a6000c1803049030003800111042120b803c004c80950042c02102c0d000074259070013002030f003a543da9100040c480449110040c44c01103d0f0aa40054001d500483d601000300403502d0259540350f5074944230b000803084030700b100705080842c143c100116504891401c8040c1c52000c40d030316041ea03607608252206440360410400204802c5100c00d0f445110ba00c0003085a07200301d05 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 400392212 1250 400390962 400390981
    0x20c030319030b09070503100603050c043c0302040501231e030102070c0f0f0e0c0f1c05010501030f090308010b09030703330504030c0311010b0d080c150708 69
    0x207504a40c0350a15440f5070380c05070076079512040d1030710070003054403030301c1ea02e183c15203e469062a05800810030b05207010140310340280a03a003500c044c5c440b0f16500382507004058680b00d041c501284800c1250308a03000302c518440c0d0341051000102ea02c280c0d414402c5917200d1504440d16207403d211807803004441e0f401e52005240c004a010642c0a490f198103541c081d101d4086070aa82c0020410354440b100850100518801010342c2d5000704030040c2e0700300c0303900e0621076407004244014122241d500804100c0382d034100c840b4000c640030b02501c2d10200707110603200c031098005000240b184c107000c0381c50701c040c00c109402c00c1d01501039a01e07071603a0f80d045540c0c240044440950882c81c0340c0c039014480c3c01c60200c0082c0301403c200c10328102d1901c00039a11010a400408c0c0100040c104800403070800e014840000d07000f82006140030350604082125094020029004103020008030342d001100380d00c1c803c18080c3d000001d103000c00b0200182d5882504040b01c400e0200340070760344440010090000910400d4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 400393462 1250 400392212 400392247
    0x30623030606010e090f2e051008070804200604030b1603110703081905071107091e0b0d0c090915050108030306090717040b0a0e060c0a03020c0a1703040210020c0303 73
    0x11600c0038075910325030804800c4104006e8070300d110507c5132202d4105101c00d1600702074140c0c10720102e1034104918981814000e08010300600020000315018220300e11941091541c01d10322a0054134080e21150b407402c1c000080541903524800107030f41c00041d85050f034442d0041c20302c1c04281450031480d200f03907035904071800c81000703000d04200c071500c4129020380c1026004907401404240e5941100059102a0900308072060b40030184031407a00c0c000d28103400c41e00801c96036500201400213087d0340e800d004103614035184800203056442200e00400c520255038041e994140c01681d146000712598549801160402e000d070300d860354828400180c1c14039242c4001940220246011407e00728200d514044012003980c048510240d89001c10822215500c11900e285c8c0307100780100441c1c1400212607030203101c0c030544881015000a501d01d4000001c000340b5034965407041c0d203600c0d002d144041040c0d1a070002e0b80e089200d001c2400980345001e100140c41082e050005024500c1c0c5420041c0812011 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 400394712 1250 400393462 400393471
    0x1e0309140a0e010b070b151e131b0207050402250206070602040b03010501110a1a091f02070203010b010212180f100c060b0301060b04050907030623030606010e090f 72
    0x1a010140450540c1c9a4120b450003008020f03880d503240c04052170044210880200600c40300250712042540c81d070341d0400c111102c213090741c00c26412203819801064581e05040e20342c4a0f00d604015070b82200754a001c8904c80000500ea0aa40300a500c482c1004240d00c070345082d00b40101004160703100100c1100c0a81048940300030a03952610780a655441c041e60055440340304102c10100040081d540c2100d00550b840c1c41010151500760b0311070b038401071080c40355036121100049a00020719112010003104503003036400325000510880c0d001c508000380d48038136801c0b40207500b001c071050941d5000003032564440a00803c4c4a0a0000548500503850361b08541d841e40210712042049103529280c48004090b1403982d40d45900b04a9810800161512150b041c1e0081e8942803081081180d48006c0c3c4003600c60464182e101601c0f1000c2c21000741420f60082d052801c4100194640d0b61003503107401030702c80c0003602a03d500b55292001540e40c00c9d03c003522142c111002c40001100f421400203004e620 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 400395962 1250 400394712 400394719
    0x5010815180c161b050103050f04140c030708071401090303080106080912030403050d0e030301120305161e05010e120706020a090e011d090105090c0603220602071e030914 75
    0x6014008a00f000c40003810542600c421424140d02400c10030301c8002c5001900080c00d00f07203c0d03401c240c4076100d21074000402c0980300e000d24840c1614480c0061020700182000201110b0241d511004041e0b02c0700306a01c2215002c0c0b8a60b06d900e846075000310740c0d9100f101d40507241c1c40216841c2402c242d0300c880c001002c00c207807800b90000c000300003d4501d000c0d40c041c6000342d135529200c01c440040142203e03540c0598110650091004000d940ca00d01e8030441d2603581458180d44172101c0030301c840ca4200286000400c920382c0c1034150004502103003408000700c2c0c080c0d0001c2c401000c2e010107290311003035140b298a41071401040340c1000306102c0e4006142041d610b107400100030b035642d40c031400406400c0c5c11060300d90b8002c41041d2442c0e01140c20a98000c031268008000508100600a81d0340c2052183c00d400b8810110001d200111030003684240c60400743c00645510904d4a000ea0080d80502c2d0101d80301840d0b8030b010560740d82ca05402c50301569040c0c440140c01d0341007e6803501072180302c0884960 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 400397212 1250 400395962 400395967
    0x80a02090f070c1709030606010c050309061803070303020f1b0109030308090a05070f18060b07030c1505010308070b070f09051e060c03040f1a03010b0a030e060f0105010815180c 78
    0x92106603000460010088000b45c6500e8400d00301030801801402150402044860f00008140d01204641d1401821290180e8408000d4821440e01071300c0740402d41c0c14010400000241030300403517944501c8074074a00303a4031000a0b21000444054000a02a0001e42002c4062002038000d00743e45401802403801c803401102ca50390b42c1880d001144d0464410200904000c110000201c0440003100240e200c0c18411681080280603c0703020f811390243c104480d15810030144188041236030b1981e1400340d024030841d0b1f100d00341541303150f00c025000c9a40407400d02c006201c85102c3c1c4500490b1b02c0007079540802ca00e1a00c2c0420281c000c01d010303812074040ca20044901507907284001803006020f410040c40d180c615061550618102a41c030102c0000300c07402d20108030240f84401c8906454204500035291040c02d41d0032401406883e2000e00544502c2c000e201b0f01000700d0000c070b4100c1c0c40c00d90b00e220595954004d821190b58417410324a410000f8440400006008010b801d548031158194060 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 400398462 1250 400397212 400397237
    0x6120b041a01020d03060308090f010e060a03060f150206060f0f0d1a0f0609011703070804030303020715020c0d03051509040f0b06061602011211040b040e01080a02090f07 75
    0x10201c070070100400c039006028010601442d40c05104400120769035050801c440e80c95a1240c2081e03114401905101c0c05004120ba41180e000b0411001a801c0260515480300803d00003d0014481c41c01030140d603000700c4400061410303c034000f0341d00704c5005038003510050702c9034418000c02c50314540b24140c8c00300480b103507051030f920303204550210b09005404001ca0000e1130403242e02c60310b0019016604405000e4100010380d15508900c40c11141f0301110405014200c0d280b00d0b0450080440080030704a00003000824103506030090714031503006101494004410b0080481284109408900e031a00a10f0748c03402040d01982c441030b808000010041d684589002c0016138401c800c40d82212410b14036400c00041c1302d1030f0880d49600035010384003646020b4904c0ca8600e0801c040700d2000b410401e12036200030740000d680e08800d4040f1320312030000752182c0e2a05000b00703064120303000f40c030481c0c290100005045480010800f12290300580a03242c40e440c0e8110301e84407004001c104c078040c00818941c68 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 400399712 1250 400398462 400398469
    0x15020c030a1a1b19030b031914010e06011212030606080a0b060405150307120b0616060b03060c040501030b030105040209010509040c210b071716030608030403060506030c01051306120b 81
    0x82524501e445440130a40d42c209401404688420840501036404448440c0c030744404983c0b00d040207500408c108080d00d0704402c1803800343c940383d204075080c1c0c00303064000201c00da01d8945000304031748a844616020301c5000411003c0722076502c1140300094042c0089141003c1640c482020450701611080c90715403a4000700e015104004030b010509000081081200c60384a82c000303182096410742405210301d08000a00d80d8000c2004d00400d0390b10602c80b0340c0800009621589209a010702520030320714107044242c00d035400520515010074188079104c0712900e0180701e858455503000344129441e90a000500c000020000c20031115100340b044085112010318280e4000c25a00405000f003000c210710f0101d500c080050070040a20010501c81411101888a441c0c0d201038110205099500304242c1140641410b520002640c000024003000b032080640001e4810303a41a000c442c1d81c0000c90004450901c40d503075940040160f460030600c801841580f508003018000d1034041043d034480e0002 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 400400962 1250 400399712 400399717
    0x509061305011e08030f0a0e01110a030809060702070609031104090b13170c031801030b12240106350910142e0308030115020c030a1a1b 60
    0x10000a040703d00c05040d2032003542481d00a040c1000c041c6007040000342e8100564080d4002c22428090072081c110704076442242804056070702581160550039031414050b040d000c09481001d102d01403640014202400010349104030388113075507801c541d1032458030780071040a414002c15070310585422011000c9054510b03058018000c01d01c080c0321090640c030745426182ca1802e1a659021414015080001004800e48040b0307904118000d82050418004074000c0680c01c1c1d003107512110121100ca550f000c00950a4525201c00800119a40d611544002c0c6113400b4803490001540d1320091900b40c0c980100c40d82240219690100f680700403003512141d8401d801c40b4900890f90000c076807601c001c000d0b40126000c20b82c07103029007203640c20022498828001004007000c1e440300160601c481c6170a8641e030380710023141c0103881e241e240d503100c0b42c039036400142c2a100003005200b0650301184620380030900d11500d9502c101d80101c0d5000c01121260390043c01095540c1043c1240907048685a01500 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 400402212 1250 400400962 400400969
    0xd09030803091e0601081c0c11120102031801050105030604020319060f0f0b0f010c03140a02120c0303060a081906050604020c1501050307090e0607050903030d1b0e030303040507050906130501 84
    0x40d004540c14124418600450329011030742c0309603c1d450400016030410750035002309400c03402c034201048604000c150044040c40c0d0342c004943c4000b04000c240100c4c0c58a800d05039580300002c4c8030690b038a004143e500c05043e44c02941c1500082500e41c85285d500000c2060944182704c0030030503040301c030014422161a08014850355443e621450201d10742030700000f80701362090900d180005d91f661402400803144e01c503c3e032200742d0000b80c034000d170500806c643c045403144401410303a0f415040303507140d07280e400a548850041800b90342c0492804000710701d440b0340d0190585c44401400c559140c0380041e102c00350801d07801035800c0005080700101405518206500321140c0000c551404003898940760441e444890304600d0802d406001107408078149030030400c6445d11503120507039480003a080d44221400c03810942d00d8009403030fa440c101d000703202c400d204442d100c08001034400c1c0c0a254803440100c0d801413241d004480c0c1070019290800000c0d402c088040e003480100140b0722000c0e403ca0344280c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 400403462 1250 400402212 400402273
    0x613080d090609091e110702041503060506060a0e0d02011403040609030e0402130504020a05120f0108100b060318120c0105011401030902031005070c021c0209090d0903080309 77
    0x1402480180c1c0c00c0b101c410001c04c0b02c13078010030103503560080c840305184101940700001c684680101c64000c03400000e0f141c000741c00810401100940000c404406110f92100315051420040050002d291103015180f041c02c55880d0710780001d02460800140d4010900b01701c0c18400813490619000e1451000707184560300c1120300284407101410007601552910643d03d11030b500404c0280c01d14258030090508444c4152740140c1c0748c00b10204107a81030301580f401001400c40c14810410048202a031072412103a42c041031780e40b000e141850400954840c022402c2d04040200003098001c04406c4200304280607c10694054180320841190142d00844000403507030346420042c09203009401e00d00032441d200f404c04110848190303001c00d4890084815110300070f41d441d00040e0101d4042c01c0d02c0207845900501c003960143d81e40310303d60400d2a52450583c012103407100020b0140100245031102900503407500500607145a8950395150310040c020640350040000e040703080002e0710120f00034101c4d040c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 400404712 1250 400403462 400403477
    0x90a120b060f09090a06020309030d0e1507091d1003080a0507021f170703180f060b0f0303160f12020d02160605090d03180824060a050613080d 63
    0x20100b020110640c40c00900c114004000e100c0003036000600d01c00c07038542c0010050f13143d13a11078504905502449401200310341c288004c0405019000c0ba000c556036141070b0900e461070322040d0b01100c0041c41401801d08940c026024484080b80e82140158018450324512071103507241c0d51000000d4000c8080c070750101c1c201240180440c0f500c00c01400c0800030340081c050300710245160040c0780080340c00141c9414841040400c440c42e21940041d40184000a0b070071020307006070300e0030042007845840281c83d05440d000d011811341ca0121085500080000d000b14104424201010f42c9a866030200702c4800074960058400a66106610010810b064018040c0c91005aa020381070499621071145000003e00e000d1044e02c2d008001e6881540050300c0040d090398061030103807102c00e0f94096809035145900c1e400900110002a01041110510341c4100ca8070b120768040001c00e0030030b03110f8a52028030f00f4410322450504c1030140070421041d0b10004901c035039802202e410318004910100020f40d00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 400405962 1250 400404712 400404721
    0x31d1011010b030105060d0f0512040303020d08010b1c0e0a02150a0e061606090c0902180109060c050606061602060408030915030708040f030210020a11070801110708090a120b 77
    0x784a240d200002c154000d0103140b6002e0000740448400c003600502140d0201708034414808100a0b488007101e507100113907520744d04c030300340030b5aa404540c03500d900181045001040f404810000d40c0c0e08134400c1740c00c5078081402e02c001c400180803809060005446010324100169a581001c2c9501c03029608407180d03207521482004015141480c05180550001c008084509005c107203090001078002600003203a003181d1a1610f804101648030b481010300101d40012070040c82150405901002d0303c072020030a40d603000582e4600c011650140180c1c103c04002500360030700038014089a00c24001c0c8805460f0f69038009030071034005821107222179101240104030740c01d00d542850f40160001e9003450840c5410300d402081c20300010002082010a500070108041c001c01c066603c84161200c199155400440010484140c80750a180c80d440381e03000000b034940041c4510b00100c0008050f4904d0400e01d42c61f144000d40c0318035003050704504c21030800282c01544804651946100303405d0b12071103040 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 400407212 1250 400405962 400405997
    0x80d0c032f06060f01050304110f10050d0c111216020a06020f070b0711060702010c020915090604020a1b0302070302030105010b031f050907030b03070e0c07021002060c0304031d10 79
    0x503d403d0003566116901031803680c000c001c0d650310070389c02074040d0350114064000c41c0000c4062a01d19401003100c0c0c044956144d04040070f132003280715a00040003850040309007116003406001601181d90044c00522400301616001030443d460003100304016100b01c0d9001c070346021400e031310520060304030318224101010709002080060401414582c1440b680340c0315001085005030900e8410600040c00c0021a40911a16400c1c190010141701e510728140030091000d01200b003035240724180c03040000d1031524240c0300b13440c0c281c6015561000344015800e0040a04903050000340c0c01d610482d1400001031f942400340034040d21404c0c01e065200e003401591704149240c03e80130361707440542080c010310040d118068000d501000341e2501048840c40c44000c20700b805034a07080b240100500340d00300042d4100314001020321070701c00e03100030004540c0807000300c0e100c5105407200b1880d928108041000b0030302c07940d2014140303100f00d64a410819214030000d580c083d826911a008a100028400594007 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 400408462 1250 400407212 400407223
    0xf040908040801140c130b070f1704092909091e0c040c030e0d030203071101020705060106080709080601120c0b1c18030e09040f080706020c16080d0c032f 68
    0x1580540d0811a10300007691000c040350151f50301402000c41c2080074056814580c044607600250031440f030383c0c6150840c0c0030710b922502075507440a052007450010307408602801e603043c009070001a0901441d0100700a40807901400d554000e10610300c8101108000d140ca580242c04503000070007142c580b5509010035103e02101c40f80c10b01d0302c0c1050484004202103803180d48010f1910b0010394942d112002a2000c0d20002080840d9601c0070407840100300001501074140d1f84ad68640d101c1329640c8280484512080780110140b50b0080801006244d034902d0b80344d02e049105075030b164280d548a03403101c0880c0d0003002c00300c3c00041311b4500c000000c0c107041c41084260010469044145801031b02d0182811400c00ea103203005014160020381030241d140c9100d089258000230b0176645440c07500340b0030042c1d04003407101d044a001c1d9540700d036600740c0803602a00485190328050031101120043c16584011004d200f0340a001020315442e0b0800b125003038902d9100715450750020040e103954910344c60302 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 400409712 1250 400408462 400408471
    0x209130b040c0e060d0c020313080106030203060124050c01271203051e04050307020402131701051b090109090618050f131205090a09050a05060406030803060f04090804080114 77
    0x2c6094000f0101980380c40301210480c955082c4003003504503203850202d103140302c1c20742d034028811404030000c5014001034102c00200ca000302c08444190b40c031850302490342c650490303041c5000901c003003100d4030081c046c80192007112000030000038150b200c541c000f441c1124200c0d0f100200c0c1140d201c0c517020040746d24201032040c0c00e03500e0100900d1601001000008805441d0b07501200b00401c002420000108100c0c0d28840c1e0103041907481e05c009036400303003409115001c0c82d41c00f0f4120244400c2000d00500c102c910400e183e0025980941901d4614070442c0e00001d000780c10040c2200d00030443c210782e400354600900d0540100d040c07580c200d49079402100e002078804168481400144020f0045440340070341c1c482c1d000203c0401288110ba07027038409214034291075400004a038400140c0881d90340c0070361b118149000742403186a6501040008075000c1d4000200301040c144003181103401c1800a9400b1640f02a200150101c0d50341c507038514541241e03204080320fa440c2c004000170f1080c0d0908140c1c11 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 400410962 1250 400409712 400409717
    0x515090a352503050f010203190b1507022d10050702030d08090a170304020f040506100e0a0b04080615010206010b09010c110907020f06060102070302060301050f01030209130b040c 79
    0x1d660808581d192508900312040c40c1065008640c04104040c90781e841000750fa01c41c0880304a4000308200c14040d4104030751040a201400250042d1902a4002c00083e1800140381c1c8041202050080381c0c143c20907041a80c0000c0310403184018402e00350f10782d1540841410f0344d20708544804042010200c1e5030506601041824800640183c5000900715101e125504000f5629035030301c00340038500022088080d207a03409030300b0741b202c003400d0240c01103000300e0013030f941c29600c9200b280034002604c40942c0c2d62a0030882420780d800071710b4071401a00e080003000a044a884580c0c402d580c01554001c2c1e041030304c241d008003003400071b03061542c0d1078046461800c0c0043c1c44558504a2905540c0c0150040e8506012403042c11400700603001e08503a8250728014003408180c203190100a5690401d1201000c2c03522550700495215800003844a0449900074410340c076580c2060b05000c1203d164900480c14142c082c004520b0719a5082072000703164042503800074075134590303504100030b40b0501138440d400d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 400412212 1250 400410962 400411049
    0x90516091e0507030b19030b0f010e06090603031905042d030605130c0314060702032a030d02070f330507110609010906050a0203010602070515090a 65
    0x8214001800c8034a500c510180300203000d984000341134000d00b604c000699401003400c035003900c411204079025001d80c0c0c0038416481080e6030740c00c0e401032183d4083c02072403010301c0c2100014480f890f120310119403120000c2c081e681400c12504008181010540b10000812400310b414005080c407910741d40c08010582c20f10100780d00140b840b40f04600f0813800003400c0640c40702c0004840c3e080e252000f08040c0c0d80945a6084259030b401c00c410144280503511710070b8080d03100450402c500c00000c1c1d6a94030100c0c0002c460700d01c6c00c11103d1990400c90362601030341d8001800304d03800d01495031005c1c01500703024082d2003442c2201c514088030000010282c101d00c0200c420b9110208009540c40030050b100c41d090000b4081c0c4890074107840c00c003001008018907100e05820010150010b401118143c4e1058a00740215200c6981d458142e0209008140060388040010010b038a4001400c4904003c4140c0151410800300003065820319103403c0b087e4440917107a41030b4507045601c0620145050490608403 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 400413462 1250 400412212 400412231
    0x301021204030c030c0b0a09050c010201090b061c080a031d01020c031b010b2e020613260d1d0c0109150905030105180d02070e0f0a020d09051609 64
    0x100c002500150030040c00c08843d1080601480844035210b401c00e0b05441240791030b100c0036019010340306080b00c203801000d020781001e5005000d80c00c3c4803070384480c0303a00e070030354802050006007072640000092140191020a001c90183c0d8014440c81d5403903940441ca110002c5200c2030041c501c0c0c20320302010b030f1041204042c820300100640350301c40c03c000c001500303000b600716046015010280d8003507807196400f80202045120295416060710f541c1f4105100c100c0502010f980703511045440c1800c0e000c0c4044c5900014004040d8406204030f485845001d0000d10114501e103504120030410300d4070740e684550000001d0308107040703550070504001460342031400c20000700900c0343d0384114540c444140142c0c0c41d120380580d28103000340030041c000304600d181c10b10300781348500c5100300700d0741d814095102030f100c485101150440a0740c1101151420703e480f4080d81c13084100006006141c895420f02000c0c0c040e4119000b0b465a2074003400060031035030050fa2016101000690014440300d10f0506d040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 400414712 1250 400413462 400413487
    0x10e070807021b0d02191a090a12020307030f0f0303060f060c0f03120906061503111210030f1a01061e0815060403080711030303071e20011a030102 65
    0x404814101c00c42c3c443c503841c2c0d07010100b444200c000d60002d43c0b01114611240c1c00741c03030241086085622030091501001c0e1030701811032192044d603039119000310340700340103224101c1641c803200c1c03507148054129120070747d90b40c4906100021202003181c02d5081c1246650074142c0c54022140540085001d14418601d08070303001d4a0107030400d000821006a078400d07002410f00503940c016210070403403030520258a0524284000705558000c01380c203000341e4040240010300c40d01c641880d0341d1111544e41e2a1030b650300c4460302c08030801000d1460140700f0481c08030000f00c40090b07100049210f0489280c4142c044d10414a50801c160841400c1116a4108010f265a140c2c048800c400076030401d405e0903110301d01f50380340341003050714001c2d007040000500008101e0b0450040403000d01603070141c4035110f00b003420992244410b4810100085011441046180d241110143d00c5111420108401400d0079039002c6420b2403044e080b4861b175519588040382030325a480c00c01030660708400852400c20700710140d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 400415962 1250 400414712 400414723
    0x290105090f06030f0d020d02070b0f030103150e031206011b0b071d030a03090303021c080f13140318030c09070e01020709060902190c0b07230301030506010e07080702 73
    0x2001c01c8108002040b596141406991030041480e800c2c3e864034201080c0103076132010f00301d0100e0018132410360001502401041942d0f1011034003401d0351318591a40e01ca90f4048000c041440025035039802540c1501c220800041040f4032070000400e800345071040014100710400b82c217003c06003144401d1a0005100c0c0c4044560141d02414822a03584056000100d8140403c0702680c05104240985040c140c000389600116840303a401c81d1103005060703c942020010000344030000c26125008500d1104024282c00e6204c908a8103202010a02d5210369003280042000420305420004a518413095408401c60084000b030700181880443c0d00007240440c1070090000c0700300140f01d8a0107034140e1090180070024150384000b44145500d42072a18020362085c03200c40821420402400c800f0340c012440040865044004140f043d81c0d0070505894081d4030311010a0703401c5100d2010000c011000e0b0155000c2c5020f48000c201541c100300c1c0003056940301038421418056520100901c142d80081c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 400417212 1250 400415962 400415971
    0x80f06040303020a05070222050c0c1f0912081f1406091801030507080d1b030c2316080a0203061b040f0b090a0501030b010f0507140a29010509 63
    0x140184d49018400084641d40214071b0300030352001400c0c405600110f43d0b41801e0000c40c24074141080a03807101c0c50301c2c400c40d202d680341c0b2180580001d50b00c1950383c0c03042204a48041010000841c2c0510703241c0d50544a1882070ba0010007043c915424400b1148448140a101011684000c411a402d00b000c095800d40c480707a01034410b20000a512000351281100c001102c2522075200455517124030300320307803258582d0041c003035503105045403034800501c40d01242d81e2075202021040158005030f10b0481d0301c020703110019140724541c00380c4001d0311480c01110405994003240902000c0030034a030b0340841466030382d00014a0358020270b2400056074001c0b990b1504220802e04a5880300c003210510612400b5980c4801144240c1d43d500046e01a02d51004100004048403219109500e5500640403101e902c0070090000f03045406445145008000415810f80a032035415002400550010b03c1c285940b0002c8400a2040381103e4200218035100d0400742405141410158109030100b000450003d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 400418462 1250 400417212 400417217
    0xc1e06030405010204050d050a051b18280c110a0206040b0c070504020703030e0c010801030c090c05092e0804080a20060115020705060408030f090a1d04020109080f060403 75
    0x102040070000254101c80007081c6c098a03014542c0d41500300183c6408040a040e146030058201c0340d648010344c0700114a901ea40100745100d08640701c2074800c10620000e084074108031a8160444001e4080d400090010825400100300000d04110040c109120a14015120b91141900900507640e0785c09407425501d20707402207900c0303610a90740f0a00d88280365000c250098400030350107040c541c0c19081003041c0c3d0040000c0f14040786803c4011501d0030400d1002a220b941d036248107005040c01500f10494008551038450309207041c100004100e040c42101c5040302e468020760070340401c8110f1002115003061801c16a42514044e2a22030492291a400d14100b21401a846d1500003100f013034980361445450484400d507031945420050364140c2e030302c0000988078001001a0501d49036007101d041e42c40c2407020f5030401c2c00003a06802c3c00d07000040e5280d030100000101280d40580c51401d807256107040c0c1c01d000c040317040034000940814642e8101c1480c0d60031100201042440014900c0e030000e5051 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 400419712 1250 400418462 400418467
    0x110304150212040f170d140a030e1501030b010503120406210f060e1602030702040c091806060318020d0f150f06051e1005030c04030b0a05090c1e06 65
    0x115822400c040c2442c41c0840825004140400d400103c0d005010542c2c04000c1804d4000c449082c00d43d68942c00d552a490001308001c1884500441c0c0c040a4400100d460401040c00300c03003001c034213087c14200e100c0ca4072210f94040042051021020307485004010580141459800c030705d0210314113101c0c6001e401c00344080d521818154082406507411800321030311040080232507800040c2c002d000c50b486509243c0704803c010802e400c10815850b000c0c1c035400c0e0001c5141c0300b4150700340700242106008400900c0210080010310401130104003100c10191440014680d0500e40e01500f120103810440c00c02201e061035082c0140c44400b048030300039230441d43d112100b65181c5081482c103003a00300d004c2442410440d690005403440d40041c01960812240c030125410b1180180e405100940b0800d54440f81c10392581682c14003580c0107541003945650201d14160310b984030185600d03401d0714001c0c03049598a0400840d02410b1010070781030442100d15092280300030154001c04882c040b030017807055000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 400420962 1250 400419712 400419749
    0x50c0307210f110429100c15060302060c071a03010b030a05090f01020c030c070b03060607080a031410080d0f02030a0302090a0315051b0304020604060f12060b0316110304 75
    0xb00c00c0709900104001e0080c00403150b45c0681d2285450040810b4000315183d494490a0340382420215200a0407581c4000c201100d80e190008014000c1c031042c1c0055035079207001701c00340e2100c0c1c0081065a05100060078041d281030550440210311f0030410121756004c0c030042c40500c0b482000c80f0b40182410002084948481d280c4506100018071507000e04e607c00074112402c0d02d808806001610240c0c81520b0150340d990780f42104512046410940c8181c0801005002400e4007015200070030a518001421220000c1c50b0b9401580035542201c10700e44007c41009000c10400c00c6c0040c0c00354502e0001c0c89005203003000f9560f8040c0392501c006140d0042039103051501d5842e00c580007103420400c046014084409060002d020507100803809000400040803000240b00c00c50f030007154054155890180781c000211030300d8800100e030303504000c104441c01442090074020071024048400307000788d0b03d0038100c400001c50110700154000340b00d0145056a880f000103c152070441e15280c0103c0c0c444c030380 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 400422212 1250 400420962 400420973
    0x21005040e040821040b1e1603180618060b012c0d05030f1b0d02060112110306150405060f0d0813081006060e090402061e090d050c0307210f 62
    0x516041c00e4060010b0320400c000e000390003483d58041c42600e012040301e0b2074a88501c0b04014003c03200b00d2300da40340f03110805000300d120b07030701c080d51291b08a13614603056400c40e6181e0095403642020715909100090070300060099522500605a200b400c0500c503400c03400003502c1341c885507001070b03180041071600c00310503a440d005215610994400241e941d1084040401c100c244c02c20200c080c110b0400c1100c0351440b42001885c000b000c00d140e00180140d070710301035181c100e080710b803141254040940c0064200c151070400c00d075805041d00c0d85032019207000a80070b201c101c83d00100203922035000340c01c100146460300c0230094405a080712035aa6500701a00c2680d002035542e922001b0540304100b10000e608540d40c1c13200303050b200190382d0044520015801c01c0890349c07040d54080d5200800f01700c03520400b107800300d02d03001510211443c1820700881d040080c0503803c42d05010382e61500401450310782480c1c280075090240c24288656500d501c205940703c09820140c1c1d900408071800d0709210818007a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 400423462 1250 400422212 400422247
    0x60409031b1401060b160615092322020609150712020c04050f01090510050a15110106030f030503070c0c0b0c010f110f180913021005040e0408 63
    0x24408401c01c50382104a140c000b03440002048421200d510744038001c20096122800c07998640c0c0d0307030402e43d10b2403202502c0d01c81c01400000c0390680301140c413403000a04500140600380c0390500c0e030028140404155036500020a0004003c0702440200716100a0500d100781b29500c103664056500680b00d46056000c990200d91060a0094040e8081000e20070072100750900b4440058940c207645034141c0010601058840554400b48501c0302a8014000c800e9550f00c41070b440901c078004400c980395a03001151460016400085000050640701c180060b040021500c1244a0a0003045001d00e580c50706200400450002010400004041030380c081c4140401a0f980e5002003180603503a82e61940510310340d10518041a51754200110105070001c036106205e40303414000d41c0545000f1080046600a600c5905604034000f089802e14085844400f01d152050b03501400751550100c89004109808086088035010000c04100522014100145894120744c0c0710352126141c020600c0301c403840c03d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 400424712 1250 400423462 400423487
    0x150f031c0c06020c0d1b03080a0915091203110705060406110c07060f030c050c07030201181e050316080a030804152301060905061237050a0c0806040903 67
    0x281d0001c250013440ea9070104a03080702940d00e1700e992105c0d84091206101c110420030025020420010004086460030740141001a100d945d462105d6000b01c40c0103c01c84111000596050300003001c020080303909403085504400b030b043c40160822906944a940e01c0b41c005100501c8640c442a0815035141c0c9031066541c801100700a0340c518941741c10005001441030301818000034206000b50007407500403001c0311543c94040c0082d264141c00c5070019034507155010354288020751100d20001c0c1d1452410001c0b048c80042d40e00124015140c0000c052505c2c0e41403002c6c12803201079810800c60f000700041c21400300382d49030604400940d144d00f0001d4250302c0d18a204d01100c1d04201701940040c401181c010111a00e424501143d643c03510000c0707640e00443d005080d00703d2420002551341c560143d5a80368030021141e03920840030800165a1803406410420700d000c41ca65510020b0191094012564400da40803000c01403c81e54142c024804a005000580101d582d00414010726204013000c0101 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 400425962 1250 400424712 400424723
    0xf0c030618010623010305060a14010305180d1701050301050906070810030b07180b190302030603010b1f090602120906070c0302041802040f02070b162105150f031c0c 73
    0x4024a13211981401200421900007864103000401c1840c00b0310344541031b0741c410540c264005524000540003044080c10341c181100d80700c13428035901242003040044000d584e640708044810742c013040200302d10f07040c0c111911a0b41040200b201c490400034030b29a00200c0380c6013490b483c0c0ca400741900c03601c107420780000e0306001c3ca4401b04552160064001604020888120a0440e664001e160007500585c08404a0000800720b003070700d11403194000d55002900100001445458100050b04128403203028010460f26040451045c1d03030444a003500800c2140081c1c0340e4003180c155624400c1c441c026209201c1c1c0c0c0c0208602d03007400390840035a400b031a4060010005018002c10702c07204d03882180f5040b4441c1e1b0404072991045d80c007500a94404e0780e0301241981440c0c80e10b1201107541e01604140800b00a03c209510b00c114102c00c40c82c006405080c14001610f061510346c405c403405c44400018004c6a480b24500015240042d09130300307022130480503001100c400c003c01c03116613040b010003901 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 400427212 1250 400425962 400425989
    0x403081005060a090501020f0a05101e0204240e0a0e0406020c060a05012d0302040207080d09060212090a0201080c1c110d0b010c08030a0c1e0e01020f0c0306180106 72
    0x42542140b022000c3c5c800980031520360010b401005551380d9095000106590050441103101ca086c641011110700c0e03108032100f1124100500c83d100f2a0801e510a007242410080140c0c4204d8102d1006071120f50075151000c6a1036007036001c1410a00301e4800d146024040b0b00010702403000c2503069070012100308050b81d8403400c000c030320b2402030507003801800d50360450741044104030200108442604801d003100f03c40c50600d10b400300002500301304400e40d0101e2041020382202c040342d00c1003085892145a00503201c040199103841c2e04400104804001d500c404402d501503a088040564421a40c90500366074107940004c4003100040746440000c40c50400c14956107480d0000050301c80c48411850801c1200b403000e004694555414078090b0a9034400c002241424980381c00c100c80300101c5082401c0c0481c00f0700d06101d120f440524050300040d16a8904212542e414412103c0310312a1800070003c0414000000f515580c001d4040100304482c0881c800e8100030a400c410010400b1a10005 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 400428462 1250 400427212 400427227
    0x31c1808072306040f120c110d210914060c101d011419050705030705070501091e05060105090106170405010902100203041d190b0d020a0b0c010506040212040308100506 74
    0x6800b50300c410b00c00c591805140d1400c800440c401d200440d40c45030031034980d2424079a00b5040c00502814a0002d94000301000528040201a0310306400140907034bd884420261a1403240c404050b00112110301c126010046071003ca500068180e8031820307803240020301e000114240e61980741501c469400b0030350030440455025803156030914464030b504131688030a560090002c0341201d2044840c500420300038400b0805562160002d0008244103500021784245640c807500c075074251810070004000c60300c1e566042082030504c02180100030a5420120075410450042c044400060a0384802d0000c0360025050040940200d034180381c010341030b04020318030703c800252258800d0041045a0020b81c548134100703604140031910507402602c000004246213106040580462610396600010441d02c000150396050b0045000f0841c800020360759862980040d8203449004040610851040c040105042004200f05034410b80c189040340050365584401c00803d031007504840e80040d00441d524 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 400429712 1250 400428462 400428473
    0x12021c0b09100b0414010b070614010b04060f090f09110f1207170603120a02150106090503010f02040b03062e123902010608031c180807230604 63
    0x2000b04800d100344580c0410310140025074880d003002c2c400f00312101c0d0041206070203400142036a184200d002027511240c1000404040c4420b802c820200a03001408200140d04100220481d040c00e040001072645003200c1c6108000d024072428240340d841d00030498420030f0341c00c1290000c82a128a961320341002140340046200d0407200c481c046900031a401c0b42d069a03040d5182d108140c010000c0c8001800b4020384016030b040b0944910030341c8281d03121040ba410082407024040c00f810b60351900c0583c601001c044c25100c446404a126900c100014401d950402c41180e40c49201641d1520400f482c0e10800600c6003400a00519280031289a201c044d03a440702c5859a03880140c101032080c810246039282c00b80300c20a5a41c40e00c2b85400700007016030450441c500361b8448250000040056881c0e40040c02c541c4200d070000200d0020317070040590118507208451480c070032112049411182559154458490030324090a440c48070000035541c40099400440e488404000340c440c40c1c1444c1c03405 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 400430962 1250 400429712 400429723
    0x10507260105040b36010b0309060c070206040e16020d11030d27060608010b0a05031b041d01050a0e030306010f0c02060d0e010209012a030c0f0204091a070912021c0b09 74
    0x1052090910340c00040c464900c8001d60b4050425274019020940702c1b25018081070f4440c0000b2600010180400600d0040d9203420341e12a0310306c0300c0c00910012489800a08004400344100c003032114034040000e18a40c00002d90b4800c0d100c0c07240010361510104142a08410440c0340342010307614210240b800c02016400c2031041390141002400740344510343c1000a05c03503940c0203250301544614040c24040d500c3d03a02000700e441024100050501803010070444a41b9107401c261026034545c001c1c4a8041010b100720f0001003903010285045040110000381003c081008000400986004102c150b66840742100d055004d0010304000c400c00400c3d03018041d4006500700e80c042013100440f01c0442c1c0c4060362100d050140c2280d50080224580d0f400d4445c5a890354060b51110171185140300182c5507407144c078108a020720b80c0a061174601226000c4843d00c0203221004008014004000052031780301c0c080c1d07038581c0c105c031080c12008010200170300010351005c001d0120aa02000c1c810445000700d403 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 400432212 1250 400430962 400431049
    0x30c12032e031707110f060313060605030d0e03071401021507030f020301170c0102060c030a020f1e03010e130336090213090209060304030309030c1202010507260105040b 75
    0xc000c0e0b25141804100900c00d41d12101c9103802050410008004580c00400c0d008814070034ad000007440754403440440d2a004441e00300780085502c3c1d4150300c032a0f00c2e08100010081952050803601710b10f900c80005d4442d800211020041a81e81001c2504a07000341c001d010400280d00c000c64880d85e5625840b442960026044405401140c503d018254400310300213200d04079030b520721407454950b0342c411002580403084040212a0a00c50002c042e100090240da1001d80d480c040ca459504003403d41441201c0038040d55152112202600d00180e0420200301400b800481011020490301500000c04012005015401e851441d40030460303580d241d002d483e07121004c00c266103046465102c1c00c0100d02c10343c0c0b03180e54044030510000340004d200b508004100340c0300e840c08010485550f41c51040c0720300007420280260351104104414181d004c1e0050740101c0310256003010f8108103440950343d440040c0511070055845500c00400307903c911008079a880c111000501da525544041081c030044000b8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 400433462 1250 400432212 400432223
    0x501200a03080a0c18031211060c0d0c020a0312020d24030b0702120414030312010306020c0c01030507050a0809030c0f0c040f110d0923030c12032e031707 68
    0x20662121135110301c04c404018056010100940303411074441c4070755400c40025540801c00800c3c141c5400180c01c0c840c1901546401d0141519180d050f0000d04c11b440c1921407400456101d002c032000800e900070502c0102106250005a03100c1030b1781c4400003d010000000c0a1810801d81e51128034440f11400c0d108490050f207030b40c0b8445ccc86845040742c440d401005070700a6120280310038085543c40800c4050004d20080c2200e1a120051541c1c4c20008026802918141d6010a001440c14070500001c0e0120708246010407461401c588060b015004003124001000704a400044202c0b000300110740c1068030500443e0840e06002c61030341d03500c140045129000d0b0341480c0740e42c000003046010b52003005480301007550801a0000500000380300f418019207804558603200d56459040080f400c9050003100c0c003541d564403e45a00e07604e0b00d00400461078486408004000d032200809588808149160341c4002c81080c9902001d00094103d82011784005604c614000c1e0404017000240304440c403c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 400434712 1250 400433462 400433471
    0x10031e03020d08090a080309191b06030605060d0e01060302030f1e0606090f1005060a030b1c020f04021e040f0503070f0807060c0204140f07170103020a0501200a03080a 74
    0x20102100c14050913203006540d0b901031110351001a01c00c0c00910380c03042e00c1c0c80031544200100710f050800c100b080141641c200c02c10303c4d91000180150b003440d10161450342000e210301c51030700011a21130b1140c20600328100d541c6408002c048142904424010b5030002e0803a035914801c400c107103807220f008101d510a004444003110070b07001400300d042c520640c001001c000c007954800d20080301000004044400f0341d11303400004681a540e08014294020131540c002032110064401c0c0318982085000d900004c0015034103000059849182042d940d140503180941c9540c2130581152a6141e0301a01450700350700403501160100d1107844980071510101c1c00c4a40050b41c40303104242018190044002a40200384140309443c00b0f185248030309480600002084240201808801281a40c4005540d503806007442000e962045035100d11410a0501322555491680060030307a0003e0310406050005140e050320206d0080030740940c5c0d176030350501500c0551b08039140007880014110b03011a40c01d460b1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 400435962 1250 400434712 400434733
    0xf020d080c010c0e0303031f170610050f1518040204090c0207060c0309051522080d0203041d060109080304090c1d03190204060f0806090c06030402011710031e0302 72
    0x664142d6000c500145c01341d891515100107900d491102c00d000a00c504521580c0041d40f4035404010000e0071000c400a861141021040d5449602041e40168071a0711045444c0d00280c0d50070b400c0c08800c1d4203600e90705507240f02e204240c00403003080e1000264003502c00f1a002440021640013040303844201d070b094617410394032250246e8412480c00c101a0026500720010301603030900c9401ca804040b142c010385400d04180a085c820900d180c0341c22038800404281e070420050300200402010b8500c9800a14145814540c2d40705c401c20196040f40342000190003c82ca0030b9000d2840c0602801c1c6190a5a40c1c0b640c80340070f070801a01c4210311920024800001017500c0034141802403004420050140c80044880c0180c140c0d07880c0303c0003040c0c1e445550f503040024080c042d0b000180043c0f05110181c4010300e0441c4d0b40c18144103016442ca4043e0790208200b10060b82e102ea04001c001c4550060440036072601001c2c20002d9032540c000801c000d200342084030303402110071500c01459200390700f02c5604012 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 400437212 1250 400435962 400435967
    0x509010f0303080408030604021b1005010f06021b0a15110c010e10030b031f060315020c070513060305150414121603031514030714030304030204090f020d080c010c 72
    0x2030621020b0005089a004100000e540c2030066400890040025041603d003205003a84980300040c01c88465102103001003076984680200c500500c440d04a0140b464070301a400380d122005014100c100c0e00030165102c13407a954540c10000074105070002041b0310051200c000c2c10005000407403034505d04c9a660040900d41c4107070301d000e0003094050001e00d100400080282d01800c0030f520019414010a144803807940301200d115401890580c030302140705031850600302d9080801a03080080b00b40100044195018005100341c100ca0f01900e040030061380c1d118440c4018041508000c00768002c42d0700040551503c04e4030349000314005c0034114008211111080d6582a00404a8101d0402400b60117034103884256000300c014002c0c1008110010b2040c21000c0040c5950016400050707010060b4407241020010300300903115104e01050b5004520000a40d03d004e2884022710864452141c00200a280d030a41300845a000d4a074004806e594589455581c10040e0380607055031030b121a24038140e1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 400438462 1250 400437212 400437239
    0x72a0c1e0f14060d050621030d0f18020d020a0905010b0a0815010f080a090b0a090b06030d0206010e130803070c0201030f020a0c02060705030c1c0219050c09190c0306050901 76
    0x10010403c5140c070b014100300c3c5000c1c02c8000c00c4594014102001c0c4e900e0b44500c1c0900012041c607400c06180e80d0072032010903400b00c8580c060387c034001a1600022100e02d070002620908000d030101d40000c5080c0d46480041c1c49100c0b40e03006500c8060401d800003034a00d1801002c1d004010823500d4400c542d03070751210214400b81b0303807101150004561341c49044040e0b00820b803060b0040a01c12003ca000c6489488040d84440259004924a9515070301c0e6014445001e10740354000504402400d05142d404030002c1d507460043c01030004141d55031022030341c0ca003000400e0381140c6a202440c2526403a01c6000903050002c11038099001c603042c094040c7c01d41c06148202c030a0204652186442c0b86483e409120321900311010445407403104002003810204100500052b07840d10401c2c6012264900303000904001c0a2280c41703003a40101c4c9142e20003d01c0c041420b4003107650550720070030140e42c1c9035a00d804506031482540082c83c5031102030182c45a0540210301034079000e956000705a40e95148240245 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 400439712 1250 400438462 400438499
    0x7020108150a0f030b0a0c05040e01061116090507080f01060212071a090610050f13090614150102060c09010804030c1416030605072a0c1e0f 62
    0x559030000a54840d40d5500088000355000d040802c1c01921000301040b075208039041610110300c01401c02803091101d0217440b031003415a1910340e040920f000b20201c07980c501030180c507050165405281045038420130405044000050301c6108403550b0751518401400181d50142c00100d42c2000501503c6011505504a17103c0b6070041c02d54114400e0441500d4001200444044440d4146041e04d4100c903111a4020b80000e405001e03103044c42502d0b00080c1000d5030000f4020303080307280202400c0c0e8444c2040b07014140748000120b814040c62074000000c060000c5620364140e101d2003805188046450750759005807080c0c08030303880c03034660744408241b174081c0b440242c0c00101c07032100003070001e03105200ca04403662182426800105030080300d6414546190380d001c01140c2c40c03003820000d0059a000381078000c0010309014051303940441c242c001c00041d09605080c81d00d03034043c2c0c0504006048002a00500703400b501c824203850602310450444009110300000c9044201d004035040401214240c2803 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 400440962 1250 400439712 400439717
    0x72d0f0206152803141b06070201030f09140d110102030112030e0a0911030a0b010c020310050606040905010b07020102012405010f11010e0706091d010b03060a0b1209070b070201 78
    0x810000c101201d501010403c40c0400c5090281000580c0a8840805544100c0080c190389420511440c5400c006149245040034031959640c8941c481c1401c680200b0b8080c46d001c982c1b582c43c09006030141c40581001801e8054010321100c0495000c90100c0d0301c064075503610400b6004400e0100d0a078042030095040c3d1050145c0c00e02e000074001c0328400366075803015116864803669003ca801c221424203440c1000040000b041205003040392213641031200c02400c02c11040603407500440e030f844208405c224125a52400403131280e5451005540003000e0296050110350303101c441104481d0800f8000b2805076003098440032040c4002c403188030111428496802525240500442702140d4101750b100030b0080080e6a880320700e100380642c00c2221074400090040b6454018010019000303580606806503400c0405641040c0000e81e05046515401c080c0303440c4d80780c15001075408803081c1c1c49445011000179605040320700c21842c00d4800d0780c0c5035080d580390700c0c1d440c020b4070210320854038001d00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 400442212 1250 400440962 400440991
    0x10506040612170c010e060a0c0f080411090907080d0e150708030f0a09060606171605040303030218060a0804050712020603040206030714040b0408060a06080307020108072d0f0206 79
    0x3442c0c2c4050303003e02901d048813000441d4070700c440b20702c3c582480003c2e030f0440c041c26113800718020f8054210b45526401c4d480c61030000450f1900d81c884120b00c144040f0224480d60b402008102007003010003450b0081e100b40c00c00d5840075a80001301902e100d288000241c015580c030a0b02c01c0070f800c024402d9075070300d0760401c4c0d20350324507510143c0b101070900004001c85802d0361b03200444408182c9603c00c41e4003900c00c2e03481c0e44045024940303418401703000c000e04c45002c03400760181c040f18032688038041e5812240e060402584410441c0007074080128041c2e015038120101240303940381071b43e10900481c0610300030b0007501c8156455225a42c801032074403502a42002040011800500300300d00110f41c03008442c03800d0038000c2c0f68214020040c3c4d1080e030010042c2c0d01c01003020b2140c150284070240c1c0004689100308055840c200280351a40603070500a414001042c00182486002e044107200c0040c1d059020451003444c0c0035070b000c0505c8055911000a4140400f1035002800012100e0040202c6120010f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 400443462 1250 400442212 400442243
    0x50a050f0d080f040315020301050315071407082814090102030327010e0f0f0115090504080f0304051006060806010e040507030b0d0b01090b100836010506040612 71
    0x880c2da800006118051002004004085000c0c83d01000c501760002802603036035494181050710308051111a10507030308a1105121015030019600c0b00300c1035035150a07a031150064180780703030540140d441c800e851440d4880085c000440414803e41072030300751307202d0072055507440100078080d0080182060140e0701c10070125011742c1e0280007282101e5041c87e81ca07540000c4241c11142540c400311108002d9500170401803000340c3c400d100510010041c80d0080014140010720300c5c00c40ca200d440303044245940d500105080c402a242225240c86c1160070302a070b41d05240c40c6c02c569070640b07c0041c1c038520f860f0510100d001e0b442005e22901405d0705940700440708250404000c02408050704c85c2d021705981d081c083e40380d601c03a008000001409810100c5007589480003410941d141441018865640744401184058001e0026a0400203c1c0f004490481c043c0500f155032184400d40a0110500103001502146054009510403407096509001d46550350210b47c411810000e0001d00d8001c01d5904070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 400444712 1250 400443462 400443473
    0x10f0e160305150409030c020f030c0102060103060b010302070c030b01030b0f0123030c0409031806091208090a0509090a061b0e010809031e03040b070f0503040b1305010606030204050a050f0d 84
    0x20b42c100f01c0c020540000d01080b0300c001401c403850000c00f200407034103600c2d07603030250719044046210a150640103448100c8611300000c0d101d440500008007800d40e41c045030300e4183d20030381c199050544c1c1b103504266402d0f00d03410014400c840901c0221a0305c80e0030360000b03441c0c5604141090480c2c2040115448c1122078194840c1d001c0c010001c4640c061180d19030790006a03030b40d030003607507003c50194aa03070004103503d4510655402c907a8000b181400303413802007080030001560030140c45681001c92151150414000252100743c2030340280e510481e071a041c410b07804030111308032403014402e550030032010510805030400d214000c1d45880c0440c00c500b00604040d400781c400d070340d400f090401c15a49400940090450080140d031443c2c41540700c00b01c100b03c2040765080c0c82540100050900c1c07420f101e03540d40e0050044c800200020840c280000110740364054604d0320000b161343c450300a001e40c9884500c010000c3d0041c1c82241d00c20b94481c1d0700004d160502502002d00024090320b004000e070119100e0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 400445962 1250 400444712 400444721
    0x30b0610080601120e1207060b09040c170a022d0f012c0621010b070803040f02060c060c19090b03150616030f2d0f1412010f0e1603 58
    0x1341d090f030588900c203554650400388141e0b81c0d20540c1a080c180c0f201c10508180c4210f401249086000354040c50501c4085078005003440210740403d042c00d400107a034403e00c942080d180e00002034005a501040107141801e4a642c0d44084846034a5440313814602010082e85900002205002c40d503400c03130f00c41c00408404040341503041010780e0030b014a12558041002c550000e130b02001c03000c040120200035180440c1c100fa004040900c0b5080c00c3c03003820340721a61688000b5000401c00303802102000210f445020a5450000c0d46a090b01e496103081c110007000c40c0d000d0011491010808201d2910b2030f4010345040c3c069506900302c981c12b6945800c1c0101403000c856040e243e01032024410ba00351010f1084c0c0d61421103100f070b80e55000030034441601030052030340b202c00c00d980c80001c030340c9503400c001c0581961945680726160000001c0f40500c021340c0d080d0807000c1c40001c0414002400c20010500e14203490486506c401203980076940c030758004014400c2546c2d000400840e00d1030402c5698402e820 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 400447212 1250 400445962 400445987
    0xf0603210a180308070b090d0906031d060a0506030705040c050f030403030b060a05120c0901020d08150406090905060903070c330e03010b192606090304030b0610080601 74
    0x10800c94103200c1030080703000382c072031a8021520700c0e00008803001000400008a81c010b40b80034001c1c1512815001c028010f41d800740200c2c0205903440b001c843e1907030000c611140b01118012300341c0b0f585050503075024000d4542100d0b03290081c407952800180c1400d091007070000401d0240d45030340c10003410421400d0305500142040e400c25403030395088000756447c03100034461141d464882ea651410211051402d4400040050408003070a00c01403040780d80118074103154040d00d00e400509981e0701409400701c4050b140403150810326014005c103030007449070f02000281d0300917801c0700d41c07a0b6a1807000b283d4a1056400090102242c0e150401c4a15041c1003405029814200c6000907002c0340a01070b0a80060024203000140040401e403001e81006e10442030700e404150340c1c0c4003140310250a240c81c08202841110208500000d1102d00001d05110410702c500c48a02901c2c0d25041603071405a5a41090000380c030041e0780755001c101980f80ca03c1101c1034400c81500c804020b55980710040d503800342c5103107 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 400448462 1250 400447212 400447217
    0x513170109060615030513020a030807170f0d060b040f150309060f0902040b1005040b22120210030204142206061e231606050f0f0603210a 61
    0x20080790001e0218003449028101c25401d4040041c503150300203064032030280c1001d1503c03040001c410050380359008501c2c141e0f50001080740da0758045142222800400803000100040702040036501244500000c001080b507200c02072016030b8481114602c1b9220303600c9040b101c20002c1408120008264103404038610f480e040014070b99202c0d85038002581e0b80d030700a070f2500325a148000750461034079115160800b0300a680034140d0800c4600b010300507100fa800f4140c0c91000210302071050306420180c030340c1105088815041d00f280d4410f40f0208940c04031004900c0780090140c0a01d02074404d2007590211030344440c0c044000c910f10014001c40d0035000741c0c1d408441d0f00d040c111480317222460040000030101035907401c01031226085085070315a52450000104000c01d100c0a5401800d108000e41d82ca06020040c0c1d60750242140c40c8101030710070300c0020915410f2108101c01c54504121440c4521868850000c0303d0381c0300005c15882d40c02c1d021880442c0810722400d00464103080f40601b28404417070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 400449712 1250 400448462 400448471
    0xd0f050c032a0118060c030902010804060e011d100e06091c1214040501060503010b0105121003140f0d1b120905060705070305010b0102010204150503071709010e0d05131701 76
    0x180e82c0b0342c00e49542400b0071350303141c400014442c00c200140c0724039040b03414130345810460481d041d40000c046000240002d0040703501d0b4003031071140120030b500241c08210150190a03c04001c4001103850307540789039100340224031300003903042003002c00b20345644508000d90181540f08548488800700200b9070b50314504100c101d4002180404041c803404240c004103ea100902d482c19180036420350711140c10450281c1d040c04100c0740760745d80200c01c0d0740f20411098a0500540e0b9244800c4410610b25030001d05090740d0b0a6400d0f550580c04984041644410740c152100c12420820a0780d0000341c00502c0c1c4101206040640c001c0b40055103119810541c81c9800303250190740710001100d6070803900c01601c00c0d810004080003006024030030500600000c1c002035041c2454054800102c083e014204410300c0000000280c080d4402c404c035100703019000c043c40001c0e08010301c98600030030120710124490300c1180208026180104150303411081000601c8404c03908103030351040440e441d810440b1040d07486 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 400450962 1250 400449712 400449787
    0x90106050304150617151b040902030615070305030108070e100b0a02100e010e0613020907081f060e030607080c0313020d0204052d09070302060714060106020d0f050c03 74
    0xd010b00e10511a00ca8001080c000c11500c1c80700920250207803d99026541f000c40d40005468000152011154000340058a030381d542808070303858580b250266001c14800040050416030001d0145061341c2070501103d81c00c1c0e46441003103c401c1000e407140d01408283c92010400309400c0401400400390610523a030000b8400042c00060710b00d20341c0298a242d44810841150790303c10004658070041c1c88556448007503164010800b9000003070f00076030800c884c0c200003504a44400c4000403110a102102c00d02e080d0f6608002065642040000c600c079014900105141c00d11486246004082e00907a4a2640d03c400c000400c00c04010482243c2003041c1c810500050303540d501c5035500c00c51803142e1800c000f0700142514038800b182c40342c1d54800341c0d5915007405000100000c1d000c01340d0354180d404994808035410101c101080350181036403944501e000110f80d181e40465030048500c0240c0f15440e1014040074181d40078012400028082ea00030300c8141c0e0810a00306031210551522a45810320102 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 400452212 1250 400450962 400450979
    0x50307022a0306090d12051b0322080403120509011d18010b030114030d09030210030908181e010e06090a0305030d05090c01030204080312040c210b060901060503041506 74
    0xc111201c404e00d810401c5290350054101a4500038030000308403c0180f49040c070441000b1003c80300c403466200d4400700010ba4100710001c45d501000b0203890340b03000040003500d89101c0d82d601601040321503804a400c5d0603801030060090390344490050310b03030000d011001c8640e13a00c44c01d07800002c140c0c40b064100801035151307035054800d40600700004003203036a5814102d500d45100b011124040c06584026006400c6603444030800c000c0c1e80c0d048a1482242910120481c00f078616018050011000000c8140310103941c12031a00c0d03901410388042c1551003114140c40720342d40040ba41c032400300b4a969a03104151410303030018080100300034003000444d612038071242c0c81c40d00064007840340c050744c3d0b40511a06203400c106011001000b4a0194079041c00c00208545a000c1c940a07011310082840c086000c10154818000141a9882d001d03030740498450342c074203015203401070140c8212694a020540d241882080c2c00c1c103031681a1242d900e10344075580e403800e80c3c03d04c8a41480d1101d90380c0c2c0b0003007031b0890f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 400453462 1250 400452212 400452223
    0x3010b092d1306150c06060605040506030f0c0405040618051005180604020d230907230a080607032003090d081509040c06270612020405040c031506050307022a03 71
    0x100a17694018074a5651400714100c41c01600a80b00f0300c08144020080d0366940b208407540681200034420b0140c480342503410060160f90003559210741800c0f00403c4040d04400079050301030b9600c0c001d00c42ca440301001c00c001d0700840d02a494100300303152008120300301c00c003028640082001e400140340101440e14441181c508414905002c2440440d44444800342400607400011050160140d83d103402c41010351581142da00038510320701c503200400a50381d14480000205842c0c002d5408620381400028001c000d42c6409200e10307026040d040b00c60800820541c1d10480c0418010181c40d500ea01003566039000081c0140845125000d47c0d08152704c1d000c51160045203d18207018400303080c45000f61072803400380c00d4040341306c20f48403a4041c1029650403503400c8608600786140845107800305803000c0e2050360400b542090822041242855241c1e010f0483c520b824004600c00d96281e900446103840300f6115400141e00c0010400f01c00540e013000307107603a0440d03160a50380c1c0c05070803400309040c50b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 400454712 1250 400453462 400453499
    0x304061803121107410a17070606030c050301110909060103110c0109080306100201050709050906130e33190902120f060106111e0c0603010b092d1306 66
    0x321a405e02c00c1500101c40c103a48203c082c010446078540714001280d0f42d01c0a01850141c00642c2102d01030b1301521901040f1402c46401103c1488003544078108100006554441c203800f030b40c03901e410180503da4541c182d07040d40700020300b170741c410307449040046000d00458035411080000410040e107001c00b0034881d4121a6102e18503854403441c00c48100b0035010014507200b000c2da41490308103c240d69102c8500b0066a60131a0345594545860010440032403406401c0e03440645016070040c00030900103114071a07120a5102500c10358603c50f50911443e581c0c5012f1540b034030000020400c0d01841f8050040d4404a0660000d281b281540000710912102c144078502074104d4454802c1201042c006103014003658108803d904604681c02945c0f107148024072030514441e48e60208035441c050004850400c00103090039243d50310340ca0000a107500c9244a80d00c109909240c4423800041c9000b44550a0810f0500a18091001081c8100d10418070103204400d035036044003040c8510343c084190480f = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 400455962 1250 400454712 400454753
    0x12030a0b03160503070e09061801110c150112030909020304020103092f041b080415060b1b070f0902090112020d0e010e0105040b06120f10020304061803121107 70
    0x2a03e01c0c00040c103003002e9541d00442d201c41601c5040040c03801c000149aa041013034080544c4401e4442100b8500411080d4500c110721180002e80c4a64041d00007a003540b01d40803c0070f80074041c2d136600340021440c21100c2005000c81d034580004c000600c0e0326400307141e00600606001c00c880c03409540700054002402c0c0d40309004d001040750300c410313080800782039a00403000b5101044191122459540f0300040350002a00b0440044002010048039462844551400070301c140040d07504c50203603484c40d4000c0e0511840c03080e0756001c070340e0a04500184080031a58841240e205190402c0078201c0a50310262085c0d05100c140307030340d00c82c1003030252000f801c00c004010000644407004800035805e44520710170100e42c7e6030401d014000807a45221040c4d8004804072038515a400800c0e000c14180341181c11184920b001e072100c824490300d0541c0040d0b00c9a841002d04008a0b26101d5920a412411000c080c00281c052403026240e41e081e584540341a81d03e444c0ca4904040c842e40d81c2c101070617100d1000018 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 400457212 1250 400455962 400456003
    0x51507090504110307020f0703031d0103020f0708030717010608010b3009070b03090c1212070f020108071b02060a171303030b0904150b0105040302060c1b1212030a0b03 74
    0x1017a9041c481050b40782d1744940079003800c0780703503440007400e01d909180d10412140e01303020b0100c0a60300a60481c2c1112240501d41c42d152815828400800c1d0000c5030448081052880c0a10040700d06d0903000703050f00d0796600c03940450703420120b81440d150080c0b009884d0f0b440c071000700c4100c1e258032800c030160448080f440440d40d030310b0003491481c2040d025501c0b50038600014414000450320202e901d205129064800c800c806a640b00304d0b44c03404110360840302c07001d000000ca42003404070120384180810300131b0301c40303a025844410040344d20003002c0c403040c225800300c111080c00514081004101900035031800351b4240038050303208004888283c54080c000d03601d8011200030907405000300742c1d481c2c404603000e203413503d400c1d140c0000400000c0c00201398660341d0ba2098101d680200d0555010b107030003400442c0ca842131540c3c202d9440b28151556001038001c2c1d0f015811900c0d22059801030141000050460040c920301c14002c1c5070000f03029102c016403030740c1107164651410032004030144400401e582 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 400458462 1250 400457212 400457221
    0xc0309051c0212071707050c1005121303081302040b100207150905090a0b0a0b03180f0706020d120902030a0812010906031110020c060309010c0212070515070905041103 74
    0x345080c07000c0740039403c885820310008000c200381002000303511954401c2950748441c245000740c1010100c085484d400f01580b840d44245581c0b0001038118421010780d41d1400b40c41c0c81d01078021100c1c4820004000496117400101c105242500301d200a071b10180c00400d0303144040c4009201d01a044a860005074840d01003004070b2450703110125821045130414182c201d091501040035810024950903640ea1200c1c0703002c030544c48400d00751006005141c01642c81e4100784107207400e10120000c07090441c1c450454850381058010074510304940e0b00350000d0a03180c5121030b05a85000c1120642c509940c1e503030b030380c25015803424809203550500c42d90615566085001e0000c040c1c28045c0c000c0782d0214541407051000409200c0302865100c81207171501c04a50180000b2860415240405500400c0110030f0200c01c80054220241d20034587d001d5801c880c0c042e00d801040790042082c00342031644051550484142c0c4c01408580110907450142202512003010030f069481d20125008030040010420 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 400459712 1250 400458462 400458467
    0x1e03051b090a201303080f0a02010b03010516030e0106080a060b011704021c150c03020d0b151b0715020307120e01020d05030a020702130501050103051f090c0309051c 73
    0x10b58440e070014002c00140a0300d04402002c00a12140b101c0000030020704101c010a60b5900c682c002c41e407010806075039440c032007101c1400d504100c01c508003542c02d0800c24445441d042c042d440c0314481c043c0c45120042400e84084001d0700d00f440044105558501004c0399400c0c0a22603410051301490010462805c01e0000401c0760410041d6109803906c94001c2c080103949800341c00241d003a620502807442c1c0c1d400d0a00c0c56101040341e0104a840386032280042402d5059006850340741ca20010810004500100b07101892111b00a954203881c02013180407004440d0715960000b805002c4229226240c494020f08035821744c000c24903001d40d2020410008020001c507101c040000c042c0340c204900300c0c0c4080041c2d5202c407980e115a060200200000d450060240d064442d025001000d1612100000709000000e11007800341c7c1d8000fa04240020389808c0480202c502c0c0d40b200c09101e000f5491400e0311140c003d1107245498030406480d0041074001c41e03070800400c11000384014100090b9205040f01 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 400460962 1250 400459712 400459729
    0x60d020706230405030a05030403030e2b0908030915040e0403110d1e1128050f060603250e04060b1e1e031c09090513020a1e03051b 58
    0x40014800b80d030100000200007006440c5008210304002340c40341c40b580f030140d01a20040044220910401c4001c500c1c00c502c0441c01c0502001040140c031480f81c04d00c5045600d08518043d0324410790040009940300d090411580d0f01c00c48a001c05103040a0315490302d0740d0b0308031003070307400b600010384103e030b403582100741070250300c0034a02e050614140d03160700c113421826444141009481171181000503e0100c5a0901c5000500c1c0c52500c02c40784403000e10280c5000e2182100000d807564400c800d80310000d030400290444c0601d0005000b8240c3d9810149135803402c44600e010794238000900c41d80000d2440c000320005003c0c0303115010115905504a050046103003040c00c0b002042104c00e204a1070b0b503110b030b0301c8180100d03068140c000318683c050f1000c603140c00e00172201c00e04900d03484402845000d42c0000c8140a98a5502c400c1c40241c5500d039048840e42411100694400b219050400003a0b1155071645014201106005202d0f40e0301e0303c4a0707007015040c0441d0041d140700c03601d26014501e0090070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 400462212 1250 400460962 400461011
    0x405010b030a0b040303050a0f0c050a0206010503060717041e0f0303140c090d11091608090d05040e2a04050a1e0e0613050907050906090906060906060d020706 70
    0x80180180903250400043c0000d48090b007416500c4020500c122a2a00101e9000200901c2488103151a0320024010b6005044140042c013482d40045040d240101d038050007282161349842c804030482c5000d0401c82d00282041b18bd09120015000c20014400368501c400ca002d1030350034080d6402420090300303942c5c00c40002000014048108071062002500b5501b940d1800d807901410a40d0314502075018401450005501140d001d04020060b240c1c42000161244296220842500c900307900e80c2c0d4139101144240045403013031100348800000c20041c1039000b200c41c0840070a00f00364403601d000c60286c1d0031840815541c0014240040c1c00c0400b800401480c00d010320145003501300403e4503500400d4082c03a80a85400d034046605680d420158074410703510b4207800c00841c1001404640e0b070700c0c194071426005080d9140000c040c0d1400010244c4940100d40c0038002594450003001403a04000340141ea10002c02d01030b5a42e00519880a060094861035000849105e908441003001140381d0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 400463462 1250 400462212 400462219
    0x32805121903050601080703110f070f050c09160c0f2a0b0901091203020102120f090c060703270810021c02090d03050306010e131a0f03071a12010e0405010b 69
    0x3400300c2640c0c00401590712807154500009e080301002003960300c40c403480919118001001c00c007074080c0611242d00c41829445001262240d074660710038806404012078200d0350400078100400039231400740142e0501c0720721580d50395000610b6655510b140c080b244284100c2070500800c6105807641402c0c42c04007800b00f885078541000070b91320000705102460700412b469507103696440b904040c000d4040e03a1016400030885c26851800c00c0d0080da0340403045900f1141031086c10000011424a81d04664070180c040d61028411030040c401140d1a145280c06411152810080010307418001e0051112101450401603074a04450946644550404460824240c8100003178641e5a4600c0c3d254801c0c16450708100307403a6542c02e001030300d15500e003018260f002207000a6010f22007600d648400c903030100c0304000000b8a0054024480b0030350310f9110300e036010380c0019424801861061648450700c9424080145014581811442c1c22142a031001c0c1410303815005200401000b07000741d513456003054 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 400464712 1250 400463462 400463471
    0x6010501030b0f1207080102030412030f02120c1303080307020114060306100e070e04140106180510050711040c180b0a0f03020a0201090606030506070e030c032805121903 75
    0x7000055402404140d00d02c1c4110f04a90384481645003c5c000300c1c0041c18040021503c07032030f2605102249200881803040041d03d080340c000c20003103140c426145c4c01035580c4101d280d1075a645120f4469507010b40d0012051202c01c1c08000001800310004522454840d070001c2115400d10040f200e40d08405040e4a100b0b401540802800000c00d66900003102ca4521504100340c451120541d0340304105401250410304100b040d00c501c550303402802c2d040380c0d540e40c0d85d0b03114003006401c03604003070509005075035110359400d20101a032482500901030840c01030b070802e8101c846c030000080444110a1452380404c5043d05907010210709045100c0c0101101c00310316281c500d502200603d681003031815501816804641441d280b4801d40c4074090980d880740d0204000382e26810029a904011202c1c0030004640c20000209820080740c50640c0110107001451940b0302d8442190703011048800107082c3c9001038080001284040028400d61090840700a989424142103203000d034452806030030606090 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 400465962 1250 400464712 400464731
    0x6021801020c0d03050313080a0c03081f1406131202180c03010302040c0504030b041113020412020904020d021507031206061d0105040b0c1c0c0f0816060501080f0601050103 76
    0x40c0e00c0320240f010f80c14684141d5a644d0f410048491380c0d0b08000103040c50b08003080199106801ca40007100e00340c0280c41d113484076a200c04a080c1c1440c21000242084100e5030030400c51680100d451865000d0000c2c602d5062540140001002c82442d03440603607030a003944000c406508044c612a0000d60180407241564601074003128060300c01844020f02540da16100b07114410301c1241918003641c0d01503685456801c6c241481c3d030041900103000c0e88125884046d0040040c000d108803001c9468403800509400855020040303d60001441a60400700500d100740040c3c0c1e44441d10445010189156a182e002604000b440c01d0390800505803a81d28103a400c1c840150001005000e003420001441020080c100c0101e40500499202074a041c40226101c1c5240c5000300c0c0307501c441944a81d8851030b610908504440403065603030f01038071151003030301e0035404100d00743c005101d030844032411260090400d80d500001ca8900340c1c0012400d0b04101608410100241b00150040c10b09180c284203400e81c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 400467212 1250 400465962 400465969
    0x120605032a0316030807030507021206240109180b04020705060a0612020604050904060902060408070e09070e130602040509010f090b0f09060402070606091a0a08010c12020a021906021801020c 84
    0x20f10b001c00740c0300780340100c1c02c0070415100313034119100380c1d9000c0c044401804440c10310981e0b0b26010782d440f046244400c2602000d00240d11110619468141e490301030f12413a00e814582207484800c084003406446001d142c00c079840750b000408045201b08000c2c181c2d847e121540c00204c0310700e6009511541d0401c007100c4096910401500c003a92001c5030110500e450380e1801030001c0200450084d0001004a40001e0b00b02c0b02081c1142203a201d540043c0345551480c0030a5159405401031903c070703240410124030007007041255000d00d41d100e158018982030322440021a402000d903c8204a03002c001400e00c5820110701131041e0500d801c3c0c81d47c8058045610008507a210300428180c048c903400b092500c04d20274a80c10000003071042c400200021940d40c0d4034815140030341c1d001e040c0a9000340030000398521b4144600251850940d8a1792525011903030003a001e0344c821000801141b280c44180340803840000341d000c1c5418418070b00107940301d158074550200760640744c0c2024107540100b136080f1003d0300d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 400468462 1250 400467212 400467253
    0x91603050a031b0f0803011a0c0a0b13050111040501030c03020c0d050315040f0b031207030c020d030309050d080103020f030102040501080a0203250e130b010f120605032a03 76
    0x5615083c414504100340301200350b6444001405080158180c40c4282030001100081d4165504248503402c001c2d0f01e03c4109805214904402555a0182e80c6080c045508220b00a81121801a0100c20307080c050300e550303003540c044030002510241c00040401c4250703094410302d10150b0b01400c0940c1842070401425454404800700e0b0b40a2003000030000d102e4900410030003151040007007040000329912494800144040c404444c02071042d0540004942c0e038020582e100c40c3d41c56900c0c982ca1885d81e500340800110707418022024591200740da140040d80601c200c1e5612030a0b50344500f01076155004000084c45054203041c040e9104000034402c99911400039a40b002ca001e0000d030740c075103d50b60001d820324500d02e15414002d001c0c04002c1e002e0f6500152907a02c0f15011104003041c120000b5443c0c04943e56600b466012a0118280c24021b50161b405070008203882c4100096190f07031800440e081041c9000f0304461007484c509103c0603141e1401c10814018010780c000c0c6000304c601c186400541 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 400469712 1250 400468462 400468483
    0x5030a030b03010b1203091008010302030a331a040219030b06070203010e070306060e0f0609090c090705040e0f01080606061608040902040306051501050a031508031209160305 77
    0x15100d00e092507060310300350040c41e482e20010300b050820800c1381c100d407600c90308600d0300d1520541400b40300e5060948101d0409040c1d83d0000c001e8441d04400c2d94800642c01d4400000041443e0f03010b040b8010000d101001c08010341d540000400c5407207100d40009040185901c140d4820740c41031243c46200300b424030700020305802c0c2d400c0c0040c0303001151000800e13500894400943c5907003410345d00c0b5100c03c0c000c40c041c0112071040c2010b10807207454800c440f0024404030303660b4814018010000c2c9081c500f441c802500004070b00262041c1c40104004142c03a401c040308c104000c2540080c082000c000404c64055000100102c88101ca5042c807803101e07141d100160a02c1d100b000c01003002d0782d88070000c15140e182d0b0b80d03202c80c01b90395441c0e640380400041d420a00c030540300c0c1d80c0380c0350004d42150300c0c040740e201ca1039605a58051425134000800e400816191801d48580c4800150120340c0702c6081000301b980501010002c803003031406400c010302d804d0b0505e40c800d0f000b035003030641040019400110078621 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 400470962 1250 400469712 400469717
    0x111c050606210709020a090b0a05030a1a0a0f081b0a050f03120c0d0f020109020a21020d0f0c050a0f030f0317040f030f020a0305180f06030a0c0f080405030a 69
    0x80340c01c04011240c40040310b420240540507411000403541e22540c000c04103c1104d072104442c1c55910002d800c0c0c180110b0b0b2645010410810000c0d00000f01640019060100004030050405c0d032a004505040440d0b0812040c100349850240304022042100600398909030341c2500e080f0401d50040b802200b01e520400d8005c80c40c680b9402c40da40c0d007d00c0180030315800a48895211184c06c1c2e6519951007045260b600400d0015402d5040e551041c00b035800d0403500504901041441e002d100d1a41100815900c1c442491100d441342c010b949041d007010300c00f4020b0302c0c0301c500c410301400c041032440115031019102e034082c0320080200d804024031000450340c015041c0e6020803824203003552000702d58111003c0c0e40030304208120401c01a01e02c50443d15000359242e00d1924a0a903007681c0d220111400540800d400f401102e5503120b15042d270302228403010b05103000040003900811025001521107841d0152902402c2c20750540c801000174600c000c52030f01050500382515000c0c0c892240300b0b0081e04 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 400472212 1250 400470962 400470979
    0xa060209060c0a0b0619060f0807020f030a180e0603070b22060f08070e0105070f02030a02040c11010c050301030f0f030c1b090f0603020105041203020a0807111c050606 74
    0x3901c0e51200160358840321203600340d45140820780780c41c082c0c0f034504540e02880b582c0da0b14004c005031101d100c803520658095484082006a56101c1560324200040000045101c0c8140440b00054103002800040c0c61544540585c1d5440b440201120411a0024000034041004010003a0b400040c103d0403a8181c80d001740da940000e18204121406408840e00b41404c000301c0000c03d00d500081007410211660754440140d107408800b1142112000d01440c0050801d000280200760031042c0024054030040450b0f109201ca0350104055034284400107010424009800489840c20700030714030000000d2501500e15811955640c0a010712440040c040d1451503161004041c0907001414020380c224001496180700b045940c0c062807518054040003905180c52512922108d01662055990585406041504111501c0242d1403111400d40440c80b44410500100e00d410000713048403405102000904034849041c05540355074010351858126044d111070001c181c0128500b60001404ca80611 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 400473462 1250 400472212 400472227
    0x307031404080604080912010e1e011d0102091807021207020315010801050601030e0a0b0f0c0d0e0109020a1e0504020307090302041e45081207080112050a0602 70
    0x341405241c10100d81482494103020504c07102c20068904d0200403640c040d0713860082c2040340c3c00d03100325a510003201e500640040c0c0c07480280b40301300c2140200002c00001c50000031000030112042d94854826145d50001d2000078508214448a108030700e42c8029440500741048001d69500150410029610020400d00c0440d070b001e020072510383c00003070170b070910550f11081010b000705020748001c5c0c0464075081071001442c5001c40c040103440c1c0c0150383d101e141d0f56166610460540000e041981c2c01b0401c02114112500c1d9204d00b9900d508280000541181039205004603d02290800e070044154200c0d0581020b0850702d840095038402d440160f140d03210903200b5514084a500025402410301c80c1c030100c146c00812050103104400341d000c0c800c8001c01c2d01c009010200d011903040e0500c120400c0250410b81c498942c0c00345c01400250388480c4000c7ea2a81c1280d0b80001a152100d11a0341f0203200c011984039584601411091030110f000c0400c03582c440340e9816544500074030850700071800c0c0c0c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 400474712 1250 400473462 400473497
    0x2103140d0e01020c0d1808030d0518060f0412031e0f0f0c081504050402091501140a021f050114010c0807060e0709050f0c04090b150d0606110f030703 66
    0x811219607500940d180c000280400361105150300c60740002501082c059010421117500000840c4c120001075031620301a0120240507003030003404602c0c2910701140400c10395408112183c0303d2000c1c5d0101d0502c0d42054a000c21807008841c03201c108050914201051410340300d600100034000c1c1210004121196a020401a0028503440352005240480c2442c2c500c1c0c006002d548180816051301d10403140000070001125010348002c1d4002d815100003030700006655040d1060760105041603141c059030b11041038465032050347d44800582095003100030480035030350304885052404005101c5581490b585000050464400368104030440e2088014000b0041c12108400c0d085102803004c2c0c1c1119038919601c00e198480d0342080c84c0313407000286180b00240c174054028610b518001d4030389407038070b81001c01500c080407440d5070003150040415003503d080c400a10000c00103c4011414900c1c0c482c01600c032100d00080031085810581c1e44070100c94001c01100d070801e6050609605035070032814007 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 400475962 1250 400474712 400474721
    0x403170a270315060311060c1e0f0604030c02010816051e0c03340201080402060a021005102c0723040308030411060c060402130e01020706062103140d 66
    0x1420f10041d00201d03980d00e101a811003010340340070342040c1198000030014410300b441f9000d03000c822a04001908000348060002c0c401e420342c160402c640b1088144000541840020f440440114104e4103d01046507041454150b00126080c02406550740e00540500a03100b4072415003200a80207080003010110503081d035030659814002c99407102015070100072843e22071001841c101d08404003000e601100543c0b4150130030342c10381d207139803540c2c81d503509122a42d0401d02018066026528252402142d103101300b61161800094503140c19140c00305482c4000802c0c0308078007000a44488030030710740c40303071440d5160001418542810891403040100425001c8c9003040c5010b80030001e00002400480c0010758041c6004002040100315100d04003c0e03a4403030100c3c403500c980c12100c00540586015803000d094503040c01c40101d4070304400801e032822a0300020044401e07944d200000d01c001805140000a800d5500300343c0c04012a19480c094541d560219070150150f0002660800b4440c15070003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 400477212 1250 400475962 400475969
    0x4051206091b1908150f090d03110f12011e060215070201060b0309030c01050c09010e010f0509040e061504091a060f0411310501030207020a0314030403170a27 70
    0x52607003405466580c2c641d11514603041038003171082c0d0040403d0301112410750b4540a030003204001e0030000c503210b005030090205a52001c43c030501c01e114440c2681c106100405803840300c2c0c0c51203c6c0c298182041c01c06007181140340f08d8490101030b0014084144c0002d02d84c03000d107000710980120340c1c0e0b540804a0241131183c110a10300c00c0c0200901c01040c0c1c002016001000842001703114669400742540d89900a82450500091010000015650140c03800c0d031246c0f00c0500e44146820102070114060360410020080140d01280821180d1b41c2202c8205800c103c04940034049451641c6403200e03070346084243c11521468690109040d680c40c0c1e20b200b0720148020740240030307000b18a403004201e034111035001d00301e202c50000000000d00441500c43c09514a07854100541400d0000440082d081000103d070040345038000440070801e10050401c4a0b0b0306100115a90750071480e15140b81a89003001c908848811b02c80352840c41d401000804004203c050401480064049a03418401c0d5a90 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 400478462 1250 400477212 400477249
    0xf0501060320041104060f02010f0501080a0311060606031803040302041404021906080c0f041802070309060e0907030504020d02040504030306050f150d2a02010204051206091b 77
    0x200c00400c020710104500000390311a00c00d02d501110010510054070031035080e0180d4180100401c1c000790740604000280310754140300004070005402289011035070280c000100607449101010200745c1e106140302d550b2414140900420704040c400710b081da02000e2303c1a5003043d448481011103850810640d802190014000c0c00410004400c442c1c00c04030542c0c003680120b02030a4503034071003080304884c00200c4000e56980c4401c2c9d035a0920324242d40d085000d1192894104000001d0341c2d568900c41050a0300f00003000698030760f2586130180001000d54403d006210058121041c55a5040965039103d4401d00380810700f03503554400140304001c0800c2c009d500030716000c01d2006155040d80004141c80044d166544100c0310f03102000700a402c4151005603001c02080038248804140c1c0114807070181510800a48200300a9043c5c1c6c032094801795400140e50204042000d480e0181540f0306c150300100241c842030404440031070711503a20450758107440041800250b541e842d04c07002ca0801c5603c01 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 400479712 1250 400478462 400478471
    0x90311070b030f0606030417130b040902040807061b03051e0d050610020c06040909030c020a0e150a0b090d02010516030e03121216030623120708070302040203040f0501 74
    0xe1107081c09903041a50120b4001030b0000001e6070302c2c00c0c49400c8034002c41d00400b61514000c0987c1141d1142c1d403192800902c0b00c80c0006001410f0724180c0c024002500710341101607211820081d16515011556001d0707001c000a6501464070459070b00701420150b07415261090342d51604910980e26003540180e40f9191020000341d00054030150340c00580201000c8441440300705100f181280d0b00c161400403154800742c204010408005207030300540c000c5100c0c0c1025060141c1c150001608141640e1000410704100c40c2042491500e0b0b82c03042460391011104203404505102c0241d00a01440703203800d0050080b40144002e40e030194041da0390115800421031444001e034500240001100d90030540a44200e00440703a060040c03406441240c40e0104281d401582d841e042c076680031148052580c1810f41d00d650109503180b41505000c080c198640411603050030071028401c1250030004401c47c180c00c5003805114140d00454501d0449804a501607242c0e00d482c1010620600c021030300801c0bc1d86003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 400480962 1250 400479712 400479719
    0x110706020c2814121213140601031e0c09020c01110a0c1502040312080c09031c02060f0412050a0203090a0609061e08070f20060603070614090409031107 67
    0x442444001e4880c051008424543d070400c0d55607910148002c5404410601c81c8805d42008003180b81d62101c42000d11459904aa442d03141f00752a500d1151011904544018401e0203060440800c0e0101024800c1443c01000c0d02c8000c0f800a450203031008580d00011444808d5909400080703501d010700e240e1a43d0f030300e408032000d0540d640000040301c00240c0d5080f942054101842907404480d08440141034030451107500311024540103090340001c0c1028401440c0c0e07030b20304024251080c101a54006448030b204180685040001055944000000d800b040005285050080306155181c02c1181d1940e810b58822f070300354003072941d01d2030300000c4040e80000c10982c441c0c19142100c0f000d45480c00c016104400d110480000c1c0a4074201190f480170200345228400c5207000182c04440c54403c00c0000c4a030348001e14007040f180d104c22141e01c00070512480b07140c28000b0707100500c00c40c20a54560700601c044804580140500548a680e980c001d000915000d13040c42c5003403902c9070042e0b40400e42c9 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 400482212 1250 400480962 400481023
    0xe1002030a0e011809020f0d0f0207021201020315091317040e1605120a0b09150f06121303020106031e030f0e1c051f05061003110706020c 61
    0x11101521001800b00310b20503450707502070700c03481c0c02c04611a4a80d0300084d09000d9408041d60280404401c41942004908245505841181c0324071032003200141e03484050b03004102d0108110403107215140d10400922000d416080c104e04c0002c00281d0310100305030340302c0c2e903030701c0b844001010068021076140c0222521002c201c8001c0c419906a041e000c401c9840301140080c48020768842c007008201c0c1040f101c4450000101100d80c40040d400c070101c1d601c101c02c000708880c80000d4800590925062002086900d0300c040401d0726a003007030320200e0070044003840a446001e40600001c8a92115548620606100390015000765030480180450703844c0c40352540f95603007000b41040d4001128030300041c0900340325400750f03450710f4002881e000110f40e52042c0650000d0b112881142d86105422000c18401d079090b005c20b400c81449140060700786060000e0244204544000100b014649660412041c5441d0180c802d19900004016215021008513a01d07003d06000c00300380c6203070002c080c800c4054 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 400483462 1250 400482212 400482217
    0x14120c060f0310061b0b13020a03060b0906150d410105061806130806010b0901080a050709030f060e1207060f0501050120120f040503060106050414010f0e100203 71
    0x403c21445080c02e50341d000850b60006042044d6420070703c04802c81010a8044010680090048850045160070760780040d40c0d5051943c400c59082d500d91550340c3d05c070b1610351282d6601c40f4050360414103440b1140c0885005205503d08546e040381e4a400e5604108041706070898600100003103c02800b8070072072004d0242941c01c4210301c0d6082e0240000c03400f8148402640c0407080d100141d015440351510420416412030945035040d501c01c19000101c0320402c0010a0090101e51042a40c6e400030000051048100034084032445041c501407088172a40305003d402166008100c1c00d02c190380d9460a0400303406000065070092040d40003495030230f0003460050400b184101d008101c0c480e03150303000400b550424483c00f808542c1641a002c0115507070740c841c1c5a940202e2065030345000705800d0721075036900b050701d40003900030010a0900c940d003410440c1c50b02600060070030a080a10308460000341e0201603050904010a1680040300e950150100030201c8a00400b4030001401801c402580c0f40c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 400484712 1250 400483462 400483471
    0x60c150f140702030c030a1110052401030b0a15090308040e010e150108010501052b0e013602130f0e1c0c06090503130f0603050a0614120c060f03 64
    0x1d640c190126101a00020407036510140fa2030156080c4451090190344080d00041c4000c818020038400504441c000c1c4100c0c0c3c0300707084002c14181240024a02100c6400d111203043e810f0600c1e29916032203580d1141c20308000c0b05e2010030540e58080c51f890085500d508164401024bc007400b05000c1100ca98a0403a941680d00546d25521503a541c112144410441907410501083e4510014000c40d40303d40014141d500c1e00c00000501d207441d00d0030035401864820b1800709003e41d110245140c0c42000c1c00341c0784090700722181c3c0401d80c90114598803082140900c4003403240c0e4806800b1002c40d251400d1981842c03082060800c508040300410a000e416801d00d821b0040c050f1081164040c44458480c0b9000360745507880e040310581c6a42c8040003401100d0068900e44403d105111355444c14400000140450725000048280361800180607150302800302140d9504044040c460101110000708855070f00b203658080026640c3c1000f814624400c00c40f0740c100c0e0300040c411420415000056015 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 400485962 1250 400484712 400484741
    0x90f07020129031014070e0415031a01050a032f040203040503220f0603020c030405090711011a1005071406100311030a0803040f1109070314100f060c150f 68
    0x41083c04410f4401c540001000e805c2400c501c83c0441d00e10361045020410b65030010304000f9001000301c41d00c402d10840d80c0d10496940d0510800100e48114199005005110658000c1038041c11981c1c0e20880401c9009200000c2928038403500c01c2d4402508a8030410801038411540d0341418140f407903c075030007541070f084002c580007648444201c003c4420412101c0701810b1203403990501e43c0880c007035405950080f001e848240710120381b60381d80c4142e55004800a46541c1100c4681504440c00c0d1403a064803001504840f004414007902c84c0344049041c4003140c40c20965544051501b20841981040801042c2c4140003c100070210040c0004050328001c914005100340700108045d5100c0144034001c150580900104001600e81d11710541503621610408034103180b0031001c2400c0b100101d60040001e80c50b035100c000401e01d0701c40d20b2500003124209007107003a070812141104150b05485000200f0030403001002c18020720704020118100d041030140581e07040f90072484040c001c4101103610 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 400487212 1250 400485962 400485973
    0x2220c050a110705100c080405120703150203040302071221020102030702150613021e0703020606130e0d0807030608030408031201120b0a02030a0e0607020a05070b0405090f0702012903 81
    0x2c03142e07400100740c0100c0764014440344285030b43c208100c8080052401c21101780d00c09100105295440c82c000003080c0e100f0304010710005107103042c0a40d00803c00c00601c11034610420600000c00da001c2901f6069455080961464501911340402c40059800842340c0a00f40c0d500c02c26400c0341d0640003140100400c1d0b0031501a140f52501c2c1e40038880c010381c1c80c01d91141207100031410142d1586c01810580001458500500700d1032010f101090780191803c0b401604260104145480c0c80c00300302d003210250403170411500300c481650546d10308600340d1080a104010001404842c802d421180107000d102040d244c40310765450764940c1c2e94002c03642200b2088102000446c00e1040301d0340e40030800d500058090030a4484007840002544060a201c001c1901d40e2001003a2060804c0428040e60306030b40249241c0f801030803c0750400e01c207504a0341021004000030005030b80d40b00c841075080300b100c0b44452420344074210146c0c0144006c0d00e0315541540d01c041600e000005401d292940d810040d000c1e83c0c0c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 400488462 1250 400487212 400487237
    0x41190311100801050f0406120501241206110412030c020a140d120323060405010b0c0309010e2701081b010c0b06040f0f0b011704020a0302220c050a 65
    0x11001c0c14903100d4400a0214001040039240260b990f01421a000d40001220354407918050001405050706a5a83e1f4683c11004842c2c030b00c2c804080d01401c8040d020809071400c001054225600400000d0003842c0c5865192030b0b211070940480340141800000440c07450624034010740800350201d82a0322850580000046842800c1c4000c071000a00900401f0b150303009503a04d01709002d20540f004201640c070304110359541c5045590151104802000314510f1900340104025640f0503007110307603000c5060280c20743c00b05001007a41c640301e6090a000c0019100b020101d07104030620800700c80c0d090044859003944102034150303141030b28248025180610800c521800c0601c888510841c00101c40c6980000410b44000c1d5650300710300010000b0645d552461622020741d000424507400242e65600b01d003065680101000e500c00c2d06040c0d5880341c0303140c035030000341e80c010030740c400a8000d14400040054000c035195442c1c01209090900300041100034400500a4002920802c0400c0050f503002 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 400489712 1250 400488462 400488469
    0x70e0a1e05040f020301140d170f0301091503230c06040902071e05032b0e010b040c08061c03090b0304030815030604050d110f03071a0141190311 64
    0x580c140c03000500460380b003165201c00e01800a8008a027504c000011034190200910110010421200c0c035146e81500d95040c081a1801c81d0309440d0b0680000440a0013000092050000c2c0302c1d2000000b58084943c12940750704c2d504007174100c00690362280d8002004240300b025580600350341c600170031008402100d0095503014003004400b0181c001e90040c4010701c0c0d12814020340c4200340c418107200d0581403940c5036002003510040c00940c02965160300c00320341141414418217004614601d81074015040080214241c1002130886811891a03e80c0b0502418014070b0700b40010540d03c180c440d500c4c85d246c20b0080c103540013070341c5203030ba40320180003c10854a80014868003503500701001d8074220f49031400c20761b4654001c03d0703a01d000c0c1c0602a100f040821003030000d02112401040b0404035005141c03103110910030b058000c0b0114000758a801c1e502003508155a00d100030200b00a0324155008440c10351108924076131a03503011754120058100d240b25005200c00706c074130801e020b045100707800d001c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 400490962 1250 400489712 400489717
    0xc050a030f0f031205100509090c0904020f0d0203035e0807120b060121021c050411090a3e0f030916050603070e0a1e05040f02 56
    0x54000300c1c6032111040821210001c00341d00c2842420701910051403182110141c40045800001e17981c1c4882c000c02c940d0805400d403552294440001d0582c100c0c0490000b00d0403080500003900400420344043d105803510710341d090306142c000381281d8039110311100c0d0040319028040074a10601d95411034900c40235541006480e03469050f40010002011245900c040c0c40000d00d040107840b800c0348001a03180403d2064002811001545100860b028204403402000c0600381da4100410040000080042042a54280c1c2d410007805039480d001c802018070041070380e07800c4000d03e03403502040c0300411030b40e6065210340103800e80b591800e40d610b00c008001103e80c021400c40100358070b2030b15249010f14044654200220704a00c203580d81a03410f4590080340c001c65104950340c00000140076104008000c402500380d0f0440c4d007062243e0401c40400c00340e02005d0140010302025441401c0180d40d107500640142071039801807904001840881e00e9142d54600c5814011440c00e032070308030024664003c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 400492212 1250 400490962 400490969
    0x306050a0b160606050a0915050a0b040320100302040501030b0d0b0a0e100e031b070f0e06030a020d030305060a06031802060a02241006020307170a020c09090102070c050a 75
    0x255081100b45031403803000c0d101402c1c08550003a964031012640d65035065041000c2d202c1940e0001e541c02000c3d546010404894010307510407006d0060030080a800d080440c0c00382d0754012804110324207410910410481c01d04040c50388900b0f8091104400b80d40b50f80500100d510903a8148012103201042c0080c072039044001625000314140006c40c280155008066001d05920071100d501486d41c02c4141100e0245440902c0f5030000502903c1c65a00300060107070101e01d48004e400150316200700c12403a0748c494400c810204002400050141d0b0b414000708054a8024200d20000c3c4c25604d03005004200c119083c2d4484d541807980403030500e210f03104034194140c0b4600c03507004041b500d40801005401101080c0118480c411502146001c06a2903140316110301ca8103200c40d0034016444800260503412260456100b8000a40854030007500c40324500d4429030b2480d61103901d034070202d00300715103082001d81103010002808a80703001540100320160045502010f0562288204165100d0310711 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 400493462 1250 400492212 400492229
    0x1c0f1a1501050c16030c050306060604081020190206160e1201061701090506010b070515100b04030819050a0f032a0c0213062303011401080d0306050a 66
    0xa0303800c0003940100c0041c100460200c1c2183d0344d880304070b0761101880040350000c49420681981c100140e041c1080031130b8020030200c0d4260304060a109001e07540300b00510414040540741c001400d012401031518814203c0d40e00b104668490625000034050360301c01e0710000041c0702e20300c00a1031615204803a0411034a090350762210448041040001c265065511084155661880003403c3d8180300c83d034200d4204600d0011441f0039481c2005420020168022032402401b0807890000810200c1d0303610318074410300309000e141d8940c400d00900d00480d42d0407c58400030000307004024403a2400103015000000743c40103083d0420110119442d009400f50480400d880581c0324072014060303000b003403805124902c036907645541100019802c180f03080550000c90542d41280b002d40c2002c80500710002a41e0409000380380c41c2c200031024020020325170488102c2c1d01703c00c44120750380079080400400e1180340034050558650040130f8507209448018008030345054000180d40c10a1351841c1d003105d0491 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 400494712 1250 400493462 400493491
    0x30f010506012c0303030117120301030f061d0f150108030403020105040605031504060605031608190c0e0901240305090304050405061329030a020609040b1c0f1a 71
    0xc601c40c1d03c1c0030f084240007425034080003100102c6910f00b00003960081c4031800f05011200c1e2210b22881c10203562124804030000e0030001800412a80c2080006080e40014000740d18481060804c03440b103000241101c00e4001c1c04146200884009590341442d184451182c525982c2d803010b140e9644913510009000c91401c3c401008198003c03c0a99400f608864083c600760388141c00280c103c0358150000c84c041440402400154120a00000b07003500c0b032400e02c40e405041c20021400141c8401c010140310b15107030103552800c0e5100b401d00240c2540043c0983c1c031036584038a40e03444d44c01e05500e82e19540c542442c81d9004007500c2801464001c1c0078801c0a18600740c01d00051002030a00180040e40090020300740250048051154002c4041c0540c5510f440007400140d050315203010030829403080c4d10100000015035220070803501050700481e0001039215045003c15000c4025048450304c04000c04201c40c24000324040e81c00301c9a02c03c610600d5041e400303040e0050f84100c280c1c0c85e0344003403428 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 400495962 1250 400494712 400494737
    0x30313151a101b14150f0106030b090709090b0406260c09040807020d030c05150f0105010203070213022b06050103110a1e11070906031403160305091306090b030f01050601 75
    0x42c200074130700040182c20343d520302c000400e000c00d00c114183c6880e41820712400041041c0d076403600c03449000344021110401c1030b0610010080400300d081c0607000d030095981000c11143d07030b03460b07100c1d06c01030111408051007240301c034010b2500783e250008068060302407000506103070700e0804030485c40707154481e1045040414030780922544d1100d248040b4240800d030b20014010841c2003100b0f00002496150468040c5000c851702e201c140c0c41a0300c4141035600c1800090016510148009241c0c28a07003030058580407002c000409102c032800b1f401d0920030314840240f148098a0708284181d68080e02d040c42260f0030800c0c604241d208112849000425a40e030f0017000070803260500388020301915000884206c50400c190800f489680421099543c0d54810000c00c600000c070f041a0703a07200d038055070070070303002030465980e150b03a030a0000c040000000d501c01c0c0c0360f510140c440c940300902040410109441c0c400c41c90003440b403082010300c00d1061841040345580d05004c0d6901c41c1e40306031b42e054120003c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 400497212 1250 400495962 400495973
    0x231309060e0a090c0e09071802070c060e03030708030901090c0806090c01081012030c0524100305030a0809100c0c020f10050d0b0a05040c050415020609030313151a101b 74
    0x82d0003031b07016000c0c0368000220f030b01804101c0300001242450042e51a180340c40c0180c03024803a035125005010309105041071300d980101c141d400345030f04415466034998440070958010b0001c003800038128014440089201c030400103840b803080340000201c0710011301c00710065802c0343c81280d800c0c0e202c82c0d28cd4001e10208032051007041c5403e03c64104a000012036130760302d6081614414400e92608009510001103580050201da00464001e0710000c0c46801c50725015241c0c420250345d8002d201904002c1080e81c5402c0104921410655800300700003815554010701c0285112020b078031410300089459001e25210034942d14010300307a1074841c5407030511031107140601000310003d41d10244642000901d501c8501402120603c290b07585170740c0310700f800030b111403a8800414a2045520140801c214200300204aa40240c00c1601880256145103003103009030035503030741c221641d604010070198407840380307904500e0505080b10306803103003044500201c54810440c1340c145880000c0350761204c0070a0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 400498462 1250 400497212 400497239
    0x6040c031106090a091a150405010c08120103080d3920060708090313030f06020403060c0e10050a05030f06031c0c030e0a06231309060e0a090c 63
    0x5002070140b0b0b0034800e8007000101c1c00313406684011032641d25960120700010100180da10b41032802c07280003011040101030300680f40500d000b61414468078051072020300c12070a00b40e8185104011245d44150703101e1904814a0700440401420607003004038803050207c8140c1a0420f0303981c8030a8040c0c0d0401c2040480f8030303494514421b001488044a40041d0200c0c0400c00d1100d01e03542c0100602040c1804440188031040044c18641550824000703030441d00803980d1160210703a002001c1071414040c90804100a2042d6400205810310f041580d641841d00019050549102151400fa091141e58010b0f1402c7c400c0464400000e14100005070040c1041000c090f0030060142c1103070354410580e442c8400881d601100c3c04041640188080d0415511a00300716004030142d40110810307150800c00380c04400038444901161080c102171960138405001685c01c044084440400510f0313550f1052001018540600760380c118011002410309000c038051102c0182d405a5040c0c411403801400a4500 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 400499712 1250 400498462 400498493
    0x80f07090812190903050303040602070501020d020c06070f03060f1a191701050a05010f0e0f1909050903040506040302100302120703060e0736051003090c0806040c03 73
    0x8030030101040c03140040251002084140c030359107645500120b003140c501d406001c00c0d0030801941c0030050000030f00120a40303401540c0700b00d01603100d8020b464114007901803494000c0c140c03071001c00c030b00040810002d8114003c1090361540941d12039500d00c21000d460642c0224a40d18822800800505842c1001e0615001d00011000d0404011080c0d09401102c031212050000e002c181d200c4041c0744482c07004500402048903044d01c19440c3c840081c0156810341110780030710858840754251900c59800000c589400200394580310160703620081003040160140c00c0015151500141031158004100d4050710801000705080502e9942007020400b4014000b104041d02407015121801807004000e0003203050b61408505a030418040b0410741f040100040e0401c030f5895818140e540702091114050558820f02d1000091442c2c10103007017091030303070010b038000c009940c031200d9213581a404880c07124481c071629200c1d1650349201039951802928040c1042c1550001000003800584031080d14 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 400500962 1250 400499712 400499717
    0xe0102061b09040207060204050a08010c020c060306010c050601030305041409101406040b03010609090f140105040509160e1008060115050d0f020a0c0c0906060504030f02041107080901021903080f07 87
    0x2c0444001c00700742680c0000c48103c03289078022406004031311b80000c5003400f41c46808007c100d0381c0c40d111402596200e401132031a005a400101240881c2d1003205038842440d000310071560f8075603503032400071310741d80c06845080d0b55506903201e0100c061400b0080303640100d0701c0c4400c4003100390410461143c501d405001c2d036617100b603040200003248030400006d18003e11280d100c1d40c45151600c0c0c0d0a20503260f5807090700306100e240601c1e03d009442843da5150540703006540001c0d003550b60041d40c0e860f1818488800c3c5046055071000500003984900d05481001c502d420400e103644c0d21030407503035034500a0244a8000003807180c8040180c0c49040a04040341c466100450320002c800011000c0341e004c103200c60001250300512600b4820055101c00c0105480301082040500d4034000a0860195002c01014411080000e10543d560390f04648801c84502d148280e60f6080c9142800304c0f0360210344020b0150090301c07501040c2100481100040c9030701921281410340d9140e05469103204000d01c168107 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 400502212 1250 400500962 400500967
    0x6201c140405060403080a1415041e091124070c0905040f05010c021f0b04110f0d0e0a02061605011d030d060e041109040305041d060405070e0102061b 66
    0x90440301180a40c1c059006800c26040030306000b400904010040007c541c14142c48403c2c42c07085000440e40011847d01c0054111000c6000074003418180303040396031040c045410b1385d00c0121264080000c644c031490380e12000d4a01c12040c0a80403031485000040c0b05407940103a581c1d04088001810103c0c030402031940c0c400d40f202c0d1104220742043e54240c8131440c40c0c45051040050900c51002e00c40003a000038152458115000c5000d0322900842d40d01042d1030340060300759a103950b000701c50707a5500d40108030b46401c0710120049154018104501106060246500142c42d020440200c01038001d04014a80300001d080c01420940c0310008550b251750b10300d02846105003116201c41590914070166130f0310700301510b8400a513002c1d038029041c0304400700c042c000003460f038124909501c50292200b05196603941410b131514081c0d54018003841d8181c40a04204c0481c1d110601c1c880c0300211010052504c0b00c10003120446407076a1400e01581c0550b01050103007074075070740c230313038040040714061a1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 400503462 1250 400502212 400502231
    0x3061504150e120601080705060c100c180b070f060e0a0c03060c0905030c10030c2a1e0b0114061635030106142506201c 53
    0x9900308481c10964000448269000d0610702c0d120241c840721119060041415504001c0305035281c1e911442030a2040c5e10000c0d5140141200344201001c5042000041229440d81c01d8040c000001001403902c0082c02c4c01004a4032580a00a8400e415000702d100b412041d080e913150707801000700c0c41c000c4205115407407c2000040750b0300c01d0000130b14440c500100d005206a44050900707041c50f0000c910a4002144420311031311034001000d5250340da40340200d09412030001c20740d4040102c001031001d0f032804100c41280c2803000c1000c444158441d01d003d4003428134072842c01040c0582d0041c014840180f00340108802e51140008001c01403005064030700d4800d1207500b440702401009c1044441c09940040c00d500300c403020315020401c00340225840d158203940ca000b804c481c4014000d4005000e685050700c110103c0c0c0b24140c52580c071070a14540f104089841111101c600d4a6130221140707800d1000b55940c0700c07441210101990015510305080031b04054041a181d5298214065000c3e1f5611403038 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 400504712 1250 400503462 400503479
    0x60603040804031209050906030c131a0913021003060b1b030c1504120e010503160306261002041802031e04080418091e15020f0a0915020303061504 65
    0x3d16501110f45412140034580001e014409500414983c460380080780c42b408617403580000c004407044441800140210064400d480b114030700d02c2e80b260003c114804208520801440d0b645800d8021614980040900f82c42141a100140a10085d881080c06100000400d4241c0003034106a48000d4a0415103035a5000e8540b6039000a244601401007050106104006d40801d00c910f40600d007500b10303442c0b036100207801c520000d01000c6c000c140580c1500c1c070f0b0302d100790f00c00c0000e003402c004669001c018410341c1415960380300e400c3e06176a00078003002c0070314803140d803007290708848002111240087da1029001e0080d04001c10090414460094544070780e600b804d1918030070b40c031620450780c480d4140302140c2d500300001d424885029142c52503000200d10f12f00e00015090a00c1c0c0603802e111340075890284040000c20403100300a500100d6103903980031200c4064000c00e541c03a030b918400956918000081070781d02902d0f071005030704104003003a6a0709100045001d115488070100d4030309070361b41405 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 400505962 1250 400504712 400504733
    0x304050a15210603030908030306180a0902061801030545030a0c0b07140702090a1d07150e090a2d06030606050d0b0606090d06060906051203030c0306060304080403 72
    0x2440c240350380340fa0500416401407000e030068002140110f0440c5485404613140c6c0030802c00450b40b4a44c1c250000345201c45a801c078a81140c1e0140050f5214814040c00b4900e451100117041d001c00c1c100030000e1182540f031b03e4030070b10744181120a550a61102c0b040c4076400b00c1122aa10080305041c2d40d4600100400c10013880c460010350b8030a01e1068041c1001101c07020080c0c101d0041203425001e4504e040500401d071062690111a4000346031681c0c8901d0000306003400003480d03ca800c510384604860804180e0000310350a00c440384c0c000700d40601c0100d41051010030f5035079102c92000085080e07452680d200d00703500d0b034138081001c40c04045c1d1139035224150303021003007841d00b140c4900c0c1c2801003103401e004040050030161003036000d400044da030f421449030000f000d131400b5110108040000e40d0304e1003113001215411540400500c0d8651a030007000d8001130003a41d0040c44200e42c440e540e00c0001013168401c0d103107042880d0854851008019082c4c0c40076009480d00c280c10710020003c28078007101d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 400507212 1250 400505962 400506017
    0xf2003130618031106090709020a0c0f0308010f0801060305120d0b180a0b04050601020a0213060b0c060a0e0309030a14240f090f0c0f060c011b020c030304050a15 71
    0xd800064180f900070150755080803000142e4100c0310500403800d90009000f0155600b009000d61651f0844104480c1ca85030341d50080c01050010228405260f089141141a2070084d03030000c0c00b183c0c0302c400b0307503080e92910310000f4059404281e012807250440c0018140100701c0c9800401c8038610580000d03c071550100c00d40f0006000a001d01c800e0702d40c1031098000a00083d1418040340c0340480010751103003400e00020703000d0b010040d643d681803103040d444000074000d58a180364403505c02500071540c4500461f000c1c4801407401c0845624000e0010507900c20010040080c110708855549510305080456403155282c49121a542a440d4110629810039290401c0803003a0b0314026941002c2968080c20b8031019030000303258803050b0360b808281145a00410360700740780c550400601052040c41040c1c1180301c5546000c40760703c441c541000c1d050720b61488560031110500483c104040c0c0b20321071445280d510000070401040300b45100050076013500124200010348030006013001c20030104284 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 400508462 1250 400507212 400507241
    0x609030f0724090f090203071707052706030121080a030903020c0a0b0406050a02070b0a0e031006050a030f0602070c060816030501030b1b040f030302010501090f20031306 75
    0x29502c1000c0699141c0007099607201d10306140440c1c5049900300f070740d070114029410150b0300040001c040c1405680884600e209140310180c1510340b01c03d0080242e0800c01210300d11452080d07140e6094159140c10030803000e0010403c07460b691a0204c0010401c0c0810380c886408808414610040b80031100500701c1415251800f081c1a4a1490000c0c1407280600300c061203603003203050902c40c00d00e0603810b035800d894072401c000c2c0e650151800203a2604004d03034030a40d0035607800114035900315803107000c0583d000e00179011146a103984180141c03d40b85603000c0d01d41c02c0340600d83d040011a5030082c0c0d1481c12030154400515041c01c1e0744030082c92010300c4e0030403c0030846180510581d550081e9a492010805144c1001154116514050712540250a10101d9110070031040c3c64640550200c900400003000e1980c2c040381c1d40d01e800783c0030300000d20a42c0c0d500e41c40c006010400721281e000ea000c802590b0744110b4130200c029603143c0100d810103805989414000e00307100f00002e0803480307410724020201 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 400509712 1250 400508462 400508489
    0x30914010c051b0a0b070813020d06090b22030807031103040605040506070507111203040503060f01080d0912200402040e04060e07030f030c0512030106030504051002180609030f07 79
    0x5040d41c810308100034030600c2d480c2e4041007140d00405d603241c0509030000300e40e14004005840740f40b126101d50803408006540201d4500c2e1000c204004c1360702c411070003481100c4040b410340c0c03809401111000b2031803030105504420345650000900c25003034a50301039114180040c4043d13000860501d40e800440341110f2803075480c0309000c00e00c9001c004c00c2e5840f409602d00103280c107007241d54408825441000544c000c1c2c00b41c04828035002130a2003902c01400d00a41118414a0802c6580d18140704c21301c03c0c040c2030700130024030640c5644502d41c5001960107440b010f43c1d004405a40d180003030200441001007245003200d4400995603280028030049c80f8035a100340807800c09003010f608603652511521450340c0454410400103580419800c0c407a505428003a014101c84d08240e81424038407540f0b07001c1100c00000100c7c40340d4241c0c0c0918001c030301590403180176803c0c19620700d080344200131142c000b156040f15030404038500b000081200ea00c01800f60380d00e00117003446142c6030840e650030802c0305603801d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 400510962 1250 400509712 400509727
    0x91a150a0902030705090f040b0913030807050a09150e060a0e0310020403021c0828120c0219060b030f0105220210030e03090306010b03091b060307030914010c05 71
    0x81814001a10701ca00045295080180d4054a20301c036150155025042d211000313032655846600001f0340903001f903c04600e40c0341089007003802e1002030038118041820400401d6982d40b1400542d05007036003075100d411003541030403d040c1e0502c00810b04c0b001000003a50552042d0344541029050017515a10360043c83c4606070f04160800e405001d0207100300b84148420005a030340d9078000320103005070080805c5001440d040100c441d110308003260000074a814180400382c000c02951141403404c40e510302d04121208070305001a119000a184010791201ca03011456600c0d4405000042e441b94a002850540c00c802103400c0c2018101401400d135074540802603040e000b0041132042030030592204800c0c0205600054032040300c102400f003015511020241000e00c2041165031915006084401641c2d5071280d43d45540d000f29000c0c002030091a801c0e9100c1d144030201403204c000002c0425056a8031400124002c2002d03500969414941c405c2d0700d0702040081c82056460f100da03030b0f81d1660b6020b9 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 400512212 1250 400510962 400510969
    0x2010e01180f020904020604030c03080418141f12050708120a05030a02070c0905101a0c06061201060f0f0618150809010e19020306060d08030109091a15 67
    0x4401500c10806080301c0e0201c1d00050000300c00d80c1003180d04403040041d9817035500108882c3e000d40c3d0001400425812070210500038a10f000d00304445100000c9020f82e0034030510340045d105940c40403c60b510801c4080388601140001040c83d1001cac082d80d0032000742d40e50511007610030b22030b5416500b0f0b4100181c1070088010500640e44c8407071050700303894540005070340010142c1c40004d0403640d43c035038089980f000b00040715082e0401092070b90350601080c1481103c2e040340c0240d0b4420610280d10302910903641044031402d5500490200c006440590380c0d41e801e00c80079144082a04100755660540030459110a25500001d0080e6895207080142458000780110840124001048101d903004002034140102284003e80003407408410646a21260702d001d0076041d540003425004172046201d4810500090486d602c0c021400c0351160303264001884000400c0c00800742150a01300011300000c031a035042088601d02c00c0708408040d01d441042e01e288030109a0741031072000013011f05041e480c81c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 400513462 1250 400512212 400512221
    0x9020405061030020a080117160e09030f0a022a030c010c051203241f030c030603080412020f18010b03090a05010606091503050c2208030d1d0c0114250302010e01 71
    0x388414003d01c010200c209c10708003110410f12a20410100b000005080042c05006641d40e0107041c3c0d14241d200c510044002c1d49401c1408610701c2d40803140052290a001c50100000d1000f2001e00500981044400110340500c00c080044d00e8074440d08a0701c0e225050504c000b94841c5007102c549072000b000b005405c91a555200f114a4030400d10001d1100190000c04200d05c01220700d0b080000d05698503140c168080c10040d803001d402d03514080f0b400158940caa010544040341700b25a039180a40851082015400a0000d0130319040780b0755006000501d5180000d6401c203581000315091580195200750a56410741c120702c2c00035800c0138080090083d030040c02c0840c1c04243c107051109107800d00c404c540300c2c0140741e03907107401d803804404483c003003c141007c0700d0160181e54292a96031000c0207000340a0000030f1f40d4004c490b4440b0392400b040d22004a4110050300e030581d10414400341c149a41202a000000240c1c0e804613030000c032064080d052890904034070300c00d40003c1482c0032495100d60868 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 400514712 1250 400513462 400513499
    0xb15210c030f06010e01180605030601090b0403051b010908030309030d1b0e09190e0a050c0d0804180b04020c0a030206100317032809020405061030020a0801 69
    0x1480d0078001d2103840070700010700d00d074004030131300c0c0001e041c824100048400b1031004820f203103100c089000200700305034488021403088c0c1080c3c860003141e9680e841c000792240b00f03500c00541650414240d01050111071084a000214140340020f20a512031415504580c42600c4000a40e4400100c42c1d4140d40280145000a50309140b09c100da0304940d40041c0c004d000115400c0c1c440e06041000543e69252070b00681e0300742a80b03000402c02c40070050901c40c2d1381c02e40d14005941c24420281119040c0c41c010801804155008a0740c5090518204c0c3c00b04e0b54881c070810a4403015211101114140c07920310107080e19000205c0200b04d10016824043d003042c5010b8540028140460010310103d0004030320720040b10940701c1440c1d66607403004000751381e03030030b0003d1035254855030401403c02410070f5801500180d40212010803a684400c020001541c4c000d1441c4404544840344c0703030640c0f56010b003105102045240700a85000d481182e550704a0340941065400b01d00c43d00c00511a10b003108100c032185 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 400515962 1250 400514712 400514731
    0x7030615081005011b060906110a03150e070504060507030201112b0e0304050f0303090d1a1e0105040f060504060f03050c0f01200a0b011502191101030b1521 69
    0x8917544131011708090488440d020b0200d5403902c10507002c11605600c0000e03070414103002d00792204175800009000c1c0086030049180e00380c00d2100032840703480340c04055020305442d486441c507040c40c021041c0c074036410030b0f6070130340940d580e0704c2c001100c4030202001860865090042c0c1000d074075200d030980640d4103060400d15443d0f40307089001071102e04008111001e80f01c084601c0d002c500362a40c0000e2640c0710310b1406503001401040c0340801c00800610030200c0d400c2c801c0428030690382da08180d410450403a00841500d60084004104905003036010000c8070f0381d484070214015840d10042010f07501643e10520762506070410400901c00140001d400c1000101c4d40740314480f15400008100c01c0903c0c04440222184a50a410200c010019050200e40c0004144007540e5203d5a4100f100e040d140108054010b0915001110302500595180b40781d001007000d4005c0000c800440003400d411210350740040454043c2f03213003c000c0002510104079426501e12a5a20300c02d030b960b03c4444c0151540c0e02 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 400517212 1250 400515962 400515977
    0xf070f1e03020901120213110c060a0513021c200102010605010305010b030c0f070501050103060b101110020a02070503101a031908070206190c0606050d0c030b0703061508100501 78
    0x50f55042c0510381100d6150075000214140d03400014886d50000700c000e24034910781003512000316a00d00140c1700110981080e00c000b5941d200110090320011514090b1600950f00074400524050010b172540d1445085084480380031507480d005c601d001452131022001074040c1a480355070782409440040c2c0800e1805001952424500e1101c6005c007030442400e203017000c50040e00c0000d080082e1009182c0060083c00196500e090210091039405e45a0740203210700e000c2c90740d8850080515040150800c0c00804e03c040c45821140300941001140100f140902e1b000041c00e56420010520f00c8880104002502d041c5501c85140201712024114001d4120302c1000c84141e0400d00320759111a0084152540d442051000030124071420088019084801000c2c80280d9400200401041d01c2340104005c001c0d1203004000d003160031a00000c03c480e04ca00c10a00008518040040e000141e50a022644d19205c000d09259030900e0031111002601940400c402940100b100c000149001c0c00c00c2d10 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 400518462 1250 400517212 400517219
    0x2071e06050d020717030a02220b1b030c070305031b06010e18010917070215030112020424030f060c031e09030c060216060f1103070c050f070f1e 64
    0x910078010000c2e24010158085000020700904001100ca400980362500e981c07407510f0361002c0c000f5040f007006d040f05608801f100c048100d0b040c019100644498058140c1884800e0032405004181c1c0c60180080740010300c1095408201046154040c1d446040a5500c40c1c02c03800500c001d00309400b1070f8a030745502400040100003800c5149030b0704074884030b240030400c00c12403030b8860141556000051240d5030300050010074070100409050701038421035011a02c070818000c0080c0d40e01085c014002110701c08602a001031801c0d611858881c01904908a02c80e09031010a50226036107034419514090380d02001420045c1511841d1030200640c10100701e01401c000b03518070305051981e80c100c0503541d505283c2d81414000e80a094540d6840070096540d01821003000a03149a403071401c8840310300f0801c1c80d0300030a2290103141d1021440310445800c550714804111442c10420109881078010740d07020924090040c007008000d00f07949104040c12030f00d041101d44040c0b0300c0152401307170040100c2003031 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 400519712 1250 400518462 400518467
    0x6050907210c0e120312010f060f021b0f040905120318011406061b0a060b040b22022505070608060f01080c13050d060501060207060c0c05060a05070b0702071e06 71
    0x342a030a5003910304070202a003843c07015186100d1072201c5580d046e00000000766407210240f460007518400e5851102d00200c0b028140da80b0400b201c031039400580c1950720030801e4200744100901c0e0010050000c2008281500d9407820300e040440074188241e400800c000c2940e81e03104c0c2c65000403012000802c400f140384003507800c42c1c07000a89400d114020000d8071140003403070004140c2c00700030030320151074040326145000c4c40100b50100980340100d0a044814441e450a40a000b1004008031a2810b205100c04901c40003075002d1150107132000126107034000b403400c1307048030340d140721303106100a0000500f0084003800083c4010089840b80001414942040c2d074000c8840e03030000350000003251102100915119501d425400c80c0f50480d00c00f005604c10312506030040e9040707038529001c0e501210340325001124900a8640081e10710648a1410000c0c0d05059004141240031450302a080410594a40c3d000d100142d50107801644400c03800c0c4400340380c0505030b038a4501502c1c90512850304e0001d02 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 400520962 1250 400519712 400519727
    0x150c1a100512031c06090527010e031602011806080901051803070204050a0e0a2102030c0304150309020a090c142d091801090608120301120606050907210c 68
    0x130764200c11000d40407541c41405a00180054903051106111500d04001c1d0401540051140341005116601441300c66031010700ca0811504021000346d0302c2c0c04420b200242510305507410072410807041e0a001d03003c240c44180079801a00c0d280e0b56000301400d15500481c00d494019150b900d5407074807004801450030700041202c1200d641901c012420342c2d2000b45000082c6030244070315a0703d0141603000307130800940901190b808a07103141e5035180281c4100080740d40340101400c800706588208000d2141c01c1c090661030400e800d043c54042205d0000c0d602150b2480c00b0342e8494402103803201440440507400040c084400b03c00c0c90242403d01e91100c00c1f029807020300c02c50243d0f60140000d564505070055104a64006c0b80c05042e0040e841d41207a40c6141c00755092050940750707403900c040800e000c0d5000c510000780c4064055903504603400c0160010034154100c0e812500c0075a0381c2e400180548ac0c58a14600c2510a6201e60b950800c1c0080c800d1440e5810b203804054441c90304480401164200f1766 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 400522212 1250 400520962 400520977
    0x20310081b061b211b0604020105071506090207200910120c05041a0a060507030c120219062003010503120a110703050c100c0507150c1a10051203 64
    0x3c45403492165021402c0040000090a00035186603010100e804030300e00510b200318841c02e0060b102050071104548810040e10b0080c0000e204000d10301c041030203aa1040d040317030036095000070b8040c0d80d40303820300c200d9004103412210540000070130f40344a00184801c144940c010b0382c1225603480c0ca4031100380f400086000c0c0002c000c0d41c0503030000501a40440100107440301a2040001040107506843d01c040420406403103030305141c002123034880c45082681d41440d410745650007103490aa460b400440500544e03401148501a2240105005114101501c6004010004400240c003650030401c19a182000c40c004400b04010012600d0011303c180030b848104108586401030310000b01e407a40f0f101001c01500784200c03803001c014004042048514110200d43c410380f139803400e002c1981c01070261000548503410a9208001e27800c44c189103020005042c3c9050001d00300c083d52940c000c440c0d82400d040c02000c0e940c0402c0002014100b05901400c82105c25280d201c500349100c9507244036060 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 400523462 1250 400522212 400522237
    0x709060602010b01271e0906060207030f0809040b06030403081b160807020d081c0501090b100309080c030703020102090a1707060e180f0f0c0c0a0f15020310081b06 72
    0x8555042d555090700400f0050004403c0daa64051b441a0b560000301074140681a90a03141500004125000180d590100c1c2d91000c00c8a00c2071009840311006904601047e42e0440d4880981480d41d40d0f500f0001c51040d842510741005500701904c1a45c440c00c032403030743d110040400b04604c0c80101c0a46455004c0c09600c50346d1503545800c5480072403560314160070002c1000e103020904400581e0511001010a07894074010801a80d03103a940d0000d45505005070303a0000c1040591060640c842c0c0c01c04001c050049411a140101190045145501030041900180d501041c0c00070140b410589030401007011f914001052424960f0784c51710360095118480c20701c2191703440c05005464030000702e1440038266542c494a803034151008000b030501180d004031180c180100191929030381700300340c807180070103c0000c01c1c01c6121591344203100e030342030b400c19a8101e01140700e20780302a2240c0000c43c418290b42500c2c00c151494000c81c145051503101940c032901840c00300c940b00c2c640310034040c5c981c4e100204 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 400524712 1250 400523462 400523507
    0x10605040519050301060f0317031509060103060b030a0902041d061f03020301060b030708070c150b0102030d0906150b1809060f092802030105150304020616050709060602010b01 78
    0x9104000d8040b11039400260107509103500021000041d408040881e405582c0d56801c050752200d050311548802c403004203a110100420212a0906200f4150b1101d0b042c10005490b42d11264203546642084554042c039648601444046003080c1c0503c0000c1007041c08882d03c4805402d8045460b40002004009d164800302080c480003800030380204021030300a4020450b00791140f1181c0280c0e8011604600401d5410f408104854400c021002c14140c124260000001d949a044005800743c9401c1c1030440c4003d2042424680340d600c80c0e14040392103050002003890358030194455a9420b5406000400e409018540300724888480b09903200004540c24611940e80740006028690107080094109290340708009001d1030741a00007010001d0448000803111185207000141d1000740078880d00116012190340c0944003440c0510b400c140b0061105041180c885000540d0204583e4203940a5101480c10041c03601030707109040103000d10f03200070b200c03a140d00000a451616805405001d84810 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 400525962 1250 400524712 400524739
    0x101d1f02090d0c12030f1b14010204030c1d01120b0f330901330e10050901031404050a020111011d0303061009030201080415020d1b03060504050106050405 68
    0x142800300e0781c2e842d4401c080071603064490708919220400311030220045a12051741602d858010b010203440d04c0030301c02565a0845d0182d841d40001c80364451021095902880080300007110f5403421000350001240a02811010315242e058003101030f80402401502e0706034000c08201d1211280c1c4c3e10851401d042a4185c1703031003100445404142041684250600303043e14000c4030581100301c03501204960b560007998031005981d4003081c544a051202a800d40e54184110050410710011303020700f402e0844683d607841000c2100103565202c014005100041e03600c14641e018800c030320441231900c2e00c0041c2da1034142d442e9550342030060030107814000300d040025007a035800d40058861041e45805c0e00000250200300c0c980c1d80c0c1095078560312880e048070340c1040652140346e4100c01c40380c0595445c604e545a90310381c102c80000458070404c110b03408000c406446a21402913080a409904103240c004840b214000e003101c82c03581003e03101c1ea050500400c401c82d484419902500c0d002c4441c0b1305001d44 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 400527212 1250 400525962 400525969
    0x902160803040308070201061a040311031002040611010510030f060e0c1e01110f120a11010c09030b0f0601080a27050a031202040b0a050901020f101d1f0209 69
    0x109294020004800001008105075010380914042c42c000e0700248800390300c030340980892200c5a81c5107441400244010004506d0707821015240d00400340650729880c03c1c100c090026a402a000f1002042c0520b11080741490709220b12540540d900d090a40320a08580e103482c00d24002d88009046562a40360f500c0a0030b00a0180780e1080f1401480c25a9011400c1d00b40e480c03500c500000c9a0209850012a030002e0102240e250010401d100180c88413a0b050035068007150441c045a400f000016001c08948590910a07902160b60369103c0ea40d250707107180313005c412003980108502100e00649052050f40d036000b1340c400c0c2e0803084008002c0b8006034000b210160110100300080c604081c2c120700c150901c9408995540098081d0b603a100880030f50081d0f45003030f80b085200340020800104002c00c10144148082d080030303081441592100b01c0c01000f000c1c07074004813140c2600c92959a000f402030b02170707018400021100c145030151a2b13610740f008071480380c1403500c01100c59140d00051081d04a56 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 400528462 1250 400527212 400527247
    0x60b010e040f0506181006031d060708011406070f030e01030b1804060c180506071401020d0f0c0f0206040b060a23190803030402040c090b0406030e15100902 69
    0x10050030070400281d0700c600c207030043d001c140d607014043c001c095a145060000008000c3c0b04162a003500300c1c440707141c21012401400e248042d01070f07001c03190b00c1e4504081014016580159442d0359255099414500c3c0c09020710214a0740318402c0381c1c1001075000040303414401a0056425080c50310021107010010381c060a10740550780d0b40819000001c00c40c0d46202d410103802103001c0c850420010809038800e8841c00040524200b0001d5842d83c20006894101e000b0316240303206940ca40203026100c500e003405e80e08280350050350285c40d145c03c0c070416a600d00c40c1301d4010500e40740c07002c10300801c050040d454840c050400383c070111640b4009405621045407250080022400448140c00480d2241840d034094100b200d20865464038000f8030340c50315034425810b580c4404040c5146880d04c0c0e0810008201c00c44001044c0070303003c8000203004280c40041c0c001000c26840100303d50310f01542c002e041c180c42c1c140604500a92105002480e6008611003003a121140c5005075114501d024811440 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 400529712 1250 400528462 400528487
    0x2060a051012080c16030f060929040b09030415110304030c0b04030b0603062e0e010807050a0911030402010c03020a150b03060a060e060105090d0f0812090703050a060b01 75
    0x2201c0e60801d0710b0400c00120028201110141c0c01c2c1c4606585c22084132154503002d20019005060104890011400d10b0f03000300601841030480885002030340c80f03110400b44140d5400d0448905510400081c0800c5000c039946c00300101c8082c500d45424151000b881c0146a00e0080c2007050741c6049100110b801c00880e400340d90005d4003d59519070b228038500b40f036070143c002151040290380206008d401c001075400c0c0101c840f107194020b03890b400c61101750030500b00000d0282c50120000d0000f02d117803c56225502814a040180100e0b505003001c4c402c154490398019100d0341d281c40e20a0040340c4619050340e400c942c0c2460603610400507820708a00d000b820220161100e411a9011a00003d841d4080500c0090603000d0b502140d5442620782c0071070700d4511030321070b181400100158040d803090004080b070810003898086d60081756158400714401200d01120507200009196440072603c00b000383c0e0001400e0010300d02581540c0c1c03450340700c1e15500001442c40341c46002012240e80102440a0b03903 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 400530962 1250 400529712 400529729
    0x1a09130c03021f140a080106030b040b0d060b1c120503060d0602030f040606080316060b03010204080709150503070621020c0a060906060801020a050412080906190f0f02060a0510 78
    0x586405001801094686900c070201103201202c1280c0568a00415505c02c440035031100086a86170100960141c44034401c200c0c2c1c480c0c7c0d80c03070200100b96503401c444000580521000220404030f88140032940c42c02000020030402071400c0c0800249103445045401e000c985091034492300d8080224240380c1355a480108010f00110410820b150403001d01032145014050601800303a881402c1d58903442a01c02260f172036446c3c1c4440b40d02040c4150801420408003500042c40c242e510652542081d01c55000984003a0709c90040741405401032032442c014240460241021514049020705440c00313a401d48800300ea51410200c0c04862641d0540324a89400800e0381c209180b60b2800740028100c41908590f040d1820801045415051007900c20b00507a0351a0249082e040c014008507240c00c010040701d03075100400404456413106000f070500c410303201c3d4000c19080803010001e003825101442d0f4404200080d0f110420311640000c45d2030300908008400221501e42101d088040c04d142c0d0000841c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 400532212 1250 400530962 400530979
    0x1603110d030e0d0f1704081c05060406050609010219050118050f06150f0d020a09020f1209010209010c0807060912120b0307050f0111010209041e1a09130c0302 70
    0x3a580d05504505007854100d4240c40040c0982c0d282078400100d1092850001034042da2400c0202d8400040c081e08640203900c09400d1013500d41c5009442c1c40c08440c050b24080c5c581081c0503a9041034020740c0c01810080389c1c82e9080c8410400000e58459421402e22041030743d003da0442031103000e5100040c0741c0c040303001040b15032859041007030741e0b8015490201c8041c421070000500ba4100190920407204000b05100d14006c664801c00c8007141c10801d06036480200c80c1e40000d2044d20620042c21664201c5030400d4442d401120781c00c0300070710000c1c07400b04964010426804541c0e400701c00f466040c0d610500c0640c551415082000013802c03c60b00041610003d50103847c0b541d038004064a101d414656424440640700e4400d0649400c47ca12803503401c4100403040a1140d8061102407441c0b600d5800018205500b140000d0b095a0045540c0f03040e4400d0012000001d04031030041d03500b103190301d07a40b42c0ca500c00c081e0007040c802400140800f40b10800c16030010104034903a01d042c0011760f001000d013131 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 400533462 1250 400532212 400532233
    0x80c0f0907140f0301050f09091c1107060e120102040f0902030c1b1e0a02181f0303170f10140109180e070e070f080601090305010c030b03160308160311 67
    0x186500c00c0c01121f00c42d0401140404d2646010101140300b8200d41d0b001c1d124899801d07a00c904032030303404a001418404850b505503501c078002c00c05407008104a0380c0360002c00d0400c0c0c0c03c3c1300f02d4403185940310003640d00411052006038807100d0b980003104c3c0701d0440142d40741c0d00c8a104c2403050042440340d5503007609a07651000381e4400042c0049020f410005045601c28040b01d401396a407121140094004490b882150b07030888000328842d0b4040f484460003040191800c0c1d140383e1a49040d00201e01049a00d18a100c0c03099444984950018200050000f2030902c40c162032181c08041c0310303d07415003924a182d040300e130f403089050b0f40050014071a1003034050480310101025204042440c40540315402c000035041c1d0751480010302070700c900c3d2071f080400030055608458a11000380301a05002c0319501c00000184244600c54080d8480c1c2d0700052608008c0040505140300e140a000307140f02481818008107454408651900f0449550020030050071f01d8103a03076803080419804202d000c2c250254 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 400534712 1250 400533462 400533487
    0x90a120c2a0e01050f030c0f01090302031207061b0c060c14040311090c21070c0210081801020301060e041e290303070c0608190c0216080c0f090714 65
    0x20709494920408281503a00c90003440542c001704041c4d1981948008011481e0b801c0c400f110382e503417030b0b010726003072525545a402207490400c80d04900a0f41c1c0034001256002d024852261a083d00112005160b40d03602c1c1c000000e015a0781d5074800b506050350b4901112540c2e0042402201090584003040d8481d81d40381400b40000c400008071a0242b80c484000503422204401160a40b610f0140110040001504600704844c0e00802078018040c0080000f4056560b03501e00400d48000c3c0d9072080c01d24a4070a500000d01c06000c2e10780049070b80184014861140c000c9041c40c841c000940c1d00140d04600d40c01d0400101e11000c2003a045d4528000d00c4880c4400b80c03050154403040c1880d180c01e0055501c40c06d01d40c0d00d02c40c042002c2e265088048091040c240319000741600311a10021210541e90440b020900700c0b01100291409179015486800c41185c052040100405140014181e030040c601c011803000c01610184034850411200050800c50056000600d85844100d04684135900c070650b4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 400535962 1250 400534712 400534793
    0xe0c090127050301060806010609031e020612040204200f072a06230306040914011a151c020a09180203040614040203071422090b090a120c 61
    0x42e2402942002c901058009000501350b04070340c0c465a801c3e1400345191603e140300c40800310302c07207000700d20000d90a015030b46540240000d405507800c0c0b81500d0509204000c1101d034000007004140d040e14041031480300c0740344c00f651110494030700d00c66527903002854010b0201034005c1041041929404440103c41490048034050780e41075101c0075841b05411914071400240130303550006480d0308000082c881d0030f05820810003284105030024640e40a80c0722a800d641104002d900c100c2c620103481045072510b450384840a5610131082e602c1c20240e140382000400c1012244105c072900004c080703015510070101040102465440709032203110108090011303500c103440a464079420040c0c6401240d0b2060050b0b40034960090061904629100a0100140c00140c4442d4402400f030011b4025198001003140100141500001c00307805500e00140d84c090085d040549507400b40003a40006512596402d4200e4028200801d00a03100e10304880c41d40002d02c4a0135042030110b41c40c95005848961 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 400537212 1250 400535962 400535969
    0x1020a1244010b0a0513030203011d07090e0312130219080c0411070f060b0a09020301030510020f04060e03070f0305060603060a0b130218040213031a010e0c090127 72
    0x18240711442a01c03a100d5080d450038007482200c00410414001038500070002080c0001074890080b204540d80d170006400c4031013016101614800d407a111001e4400148019400351001d6142044103068181225999000740361012510001c40c05c0421000b9403c070810206440d801000651a85410015030400d07a040d44114916072041e006480341d646064040c2da01e02603c1c01c601c5500b0308100e134803804140209580d05850301c0d0f645060368111515540c1111000d00b151603409607682d4590726256251400150410007514818020000c48444003422101102d503103203848018100b104001a0038071190364480e10100d034080324004108800411481d20550045085d10826580e035158072042d80c0c45000495130180e9407098001150303100d40d002e80212086200c0c440003130300100e00402c04a074400b080301010950904070420400480c40004c0115038240d15000209500d40400541e40c0603014002da0503408012030840d1459218520b1042d240d20b0007500301e0701202c0c0c0000c8000a43e00d0901 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 400538462 1250 400537212 400537307
    0x3031e020c0f0d020c060d0f0e1204140a0f0e0403110604031d1f050f130e04020a060e03070603020c0a050a1212020f1e0d090b0f06030a0201020a12 65
    0x50150950f50000c91050000000600100d141030420f203400e8000340800100514415982c9072400d469040400152148600c4070300942d0340d4506180b03050086c00035039114244500021034040c46403072a42c403012022255180d1004015450314039080e18500c01c1d404d40c0c104a07102e1402044107166200049107003008500c4030501c5202c2000d401d00090b54051884031000b01d41d200500c8013502d00c6a4024070103403242200c1345050055501d00d03000480785a031b01c01174482c6101410b00c01540b41a280710780c000d10060500700080c001c0500442d440345000d00c501400d05074040784000045006001c607540181d4802c0589030004000e241542011201d06030202c000f40b200949078002041034422100807103820035181d400d05a9071803000c42c21011000100031103440501008485280070f00035217902d00d10800c9610510724151009000344140200071034441e074004c031402000b50740c01040648040d50801040c0d00306c2c014080040e91300072160038540740c107a400358102900c418600c0326a02c0303039141d902 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 400539568 1106 400538462 400538473
    0x60908030105090f09060c03070908060405030d061e14130905010c0809031c05070e0603010303030606020c0a0501050d0c1803081e0909160210050109020a1709030703031e020c0f 78
    0xde4800f281c00360310100c0c0401c034106050059030094200500c4406079900c258081c07031100c64031740c460380e0a0203c00303158800302a00c42c0005d072240d072904068240845952803600714000d000c00d01e41c26002554031710104400c000301004840f046211101c84008164502041100402025081c0320a100b807003107980c2e1441d1a040040c6000714040d8500090081c9000c401a050940f411030480c4a101407080502039aa000000d0f602012a1000c0c0000c0e40711281c8025981000080c60030789a80080540c000100300c03075400100148283c0c1da04401027940340400301c83c000e014802c0c1e03969101c26030100045100f1484e04203000d4043e002d20407a51440140540301c0100c1e00281c00c8072003000d0300024103844198214186240200000c003001403180b8011203555103a01a11200500301601e1380301c1d4070744074603600e03120b4584507080d0002155100708802c02250754800110003400f1a0264 = true := by decide +kernel

theorem cover : BRFrame.Cov 400359712 400539568 := by
  have h0 := BRFrame.cov_init 400359712
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400359712 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 400359712 ≤ n) (h2 : n < 400539568) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
