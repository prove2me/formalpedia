-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1618
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:53:36.356977+00:00
-- url     : https://prove2.me/submissions/fe8f8b94-755a-44d2-962a-2ce6d7ba3172

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 290827338 ≤ n < 291007194 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 290828588 1250 290827338 290827349
    0x3030e120a020c0a09020c06070f2d0314220f080a1806050c0a02091b040612051018050408040f030602090a0b160f020f06070305030405010509030405060d0e010204120b01 75
    0x104d985001030644031034002c0c2c0e800a1a008007610064691280a852440c4001c480406001d50400101c030407082111a001100007600c80054070a0070401c001021203030790b4113542011070701c4c00003880100b4100a18980207121740307000324580e01c0040e00740364111541c540b10092100b080001c400c4070302a0f0100c81d10640c1c2c1c905038409070016450310b806443c58002c2e00d10b402501d9012281034409817904506042d000b020040d000701c40c190003600781e00002c0e031054101a020840020f4101c40d291054482c803035024000c009461822420300044041d1179001452011055071120086428880c45070100c1d00201414556050003590b00d280c824003940200d00300c1c51045041e458001840740344842120170721414071269030300c10101c035a5030380c031644059030040c2e8014820301d0340d0b00700a07140d403002000c2d01ca009499007503c80c6020b280003130940f01c005000da8804e400c140001c0169440da030094070000001d045e0085142e100322000c0360300a001d60b03405100502d4481c141d550074000d44405141c1130b1030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 290829838 1250 290828588 290828599
    0x306010c0206180111070614091302030718080c01120c0314090c0111120a0c06020706110405030606030a02101b0c09020a11010504020109060e010c150507090815010303030e120a020c 80
    0x20503172000e66032602424460f00c0b010a511841840c1c0440c181c2008007000c0100034102c0402c0003402c42004c0407a00111040800300b02c0303464014031704c2006114290002d04103240207180c032440600c0001c2c207443d807072050903000903122802007440501980000503d41d04000718800d1519200081d20b9588071a818110b0200e00303c1c1c4c2c403d4002d0140440c045034014007240680746403120009080f20303030401442c0c00b641c0a5a080c004600007404070f000e80700154144440c6681c4642c20001091704280d40a0003043c4a540b000c1002801615900e002c40701c00100c50070554408088074141c00084404c10000900020901e800810b20f0744541d0b02405110701c0c42e5075214103078000da00f5124201c071425a406030218080f64004c00c011840741c0401c030741c07210041c0b410044112582d40c2c0c6401c030300c9550041c2c1c0c030400c0d1210100400c40780c0c00035040700109100401801c2c020038100d0f01c80f61481040c00040e0400d9101c04110a40020800c0740110120a0408490380c44c403050b00020340704c0e0340350144140300740c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 290831088 1250 290829838 290829857
    0xf0915030607030c0e180408030702070801060b040302041d0604081c0e0109110a030503030f0406060b0a020c01020c0307180b041b02030408151612060f030b0f10030f03050306010c02061801 83
    0x900345244800e41041c0030450315100b644071234440d200c59401c014076510440c8105040803d5140c028000c200040c40c840041d66121411881000203075104031186c0c454a0081c66148000c80c000000c140390000c0d000b035903030b0707036140c604081d210600d00c44440101c1005043c00c9035400403c405600a20b04903010380c20440b0420581d008000c880032851102800ba0790040c03000c00d45401c10186160740180c403030710000407c0c0795034005030309c040c0e0040455803015801c12400d59425580501c80e071021000102d0140c5201c0d401e2a8040001d00c24540c010108190789a004030550340711a4420031210b0099041c0110070309800740004d41e81e5000340580003182c01003401e401c0c1d00c1100308000c0750290707001806401d4511300d2900c0440700c0700551800700c0d80b071070348402c00000d01038078243c2194043d50050100384502d29000c0e0015003004c0c406030540092800c0e03c0d5082000c0b800005003200042c0d0f040c58103603a01c3d1200c1004031440601d1a001a501c01c80c0002c0c4461044d0000c0a04115a202a00d802084c1d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 290832338 1250 290831088 290831117
    0xd020a09090e0c1f0c0b07050a030606020606100c05030403050717070510050304030804060b10170c0304031403090c130203040510110a0f020709060603051f050f0915030607030c 78
    0x45403501001ea9400c03110313140c500c090948100348003035080240342c5850881004143c50b5910404401d81d010004a040002d1003a90f0541c180039010282c4030074001820135007480c001065401e4a1f00d0003100c104180c010303004040040a004640c0296003003011101c4854135a400000403809a044d101c0b814810b5042c000b0341c80c02d00c81c0f40410308020301c1e140d1a0854ad100c0d18203030380752134005000b120b0440d50b940d40c4204594402c104a0100b41c5c181e0b55121910141c501040c0c2c003410064000924034506104200000b984580844d40324410120742030f4503a141c55060502d82017505030101d5001014152440086009602a601c95401801251370310385018003001d00301d034515290b104552400f08007080c003080c044c40b84110200d0b0b0500c1120702c107543e9540d86030200d4075960030004c006a2910107115400c41200d0441101c1041c4040c6946518030309400038151070341c8109500d01071140701001492850303451985211005026080d940c540c81c04a0008000b000347c2d11246000c00c2007400d20441 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 290833588 1250 290832338 290832343
    0x50307060e28150c05031206060c0706050a09080106080d110f01051302040b040b0a0b0f1c0509010608060c0d0507201c03060302210f030409061a0304050c01030c050d020a09090e 78
    0x84e143c10074003070740c50700861761205c03440f540005100e190800700800205511032000c1200e14000e201075544c0740d480e202a1000148200308070f9010502c580c3c10034a040c01419800b244da00d0000e5200d0503c0c1040d41c00c3c01606908104e880342d0101025481e050400c00c40124540221110910840c0e0030010f04121b4020441103c001c0f440303058020006140601107840007900a00c507000c00d50151908221709920800c44200206070f81084807602c2d0014031100d03c100b4050341e80034006c508050b15003450101017040d010f01600300d02071412501d0340040b950290207071010080e600d8044d508070f188800a440030542e2241008150075903108040c804030100c510a12445003541d60091040d5240b407412900303422907060181c010340703e40c01419610312440030100010002441e40340d4022581600d45581004103c01700c40d43d00c0313101a010401c000024102146010a0b05c01c2402c0004011482100443e5580550009080640d1002551340e00700c9030001003500c11600d05042c140b106030b4000c143d058 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 290834838 1250 290833588 290833607
    0x90f0d0912060902030c06070f06060f0308070305130b120403180f09050907050a1d0703092a0302150c0601090b300106090203010519050307060e2815 66
    0xe94580d1110744100044440d044401d001d8001400c40e0020010280015200c0e408480102c071701101035084803080218a000b1400104040031560901c075107161a0780c643c4e4400c800e002130800200241c400c0c0d01e88480e02c0e0010281811000d12529003921528142c407100701a0703815008289451030100c1607036600701031102030f0707550035900341d5400340b0307141d6803074042c01c0d024204290714041c8031400300701511041641c45c001c10060485e03d400c800f03034121035180b00f1400b80142c3d08040c1041d18600105140e603400c0d10398805900a0100760400c1810700003964103030b54000030740c481c550b04100304030380f01079002030080c1c49d2640e4181e5000b80d0f40c0701d00caa000c9520449126030415891030181c000c0c4007090000040420b4540c18102c04400341e120703c41d08640643c0c1002ca480303907002c00184030780c0c20301d1020400d40c1c8581c020b00506450078180005c1e902c0703107140708407400c01c002c0070300741480d82d1140b42e450310a800306e161590303003205242c5100c1034512205005900e0881c803a10456907102e4030440082 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 290836088 1250 290834838 290834849
    0xa11030109020706140c0d090501020408030307052706180105070f0302010e070f1a1312030203070b0606090307150e0d0b18060c04061b05240105030309010207050f010e09090f0d09 79
    0x180c41e0140105241000d800d0950341a510ae541c2400700141d580804c0c0000d600c241006d96810f680c0b01e0202680d040c00c0000710510b02c2000c076038250b603070a480d03d400040b103818a012042440a02c1c0129004031250320507410000c0081c03410b018130b40101501508140b402c89100e00c03d907241261920008030306c40c1e4444c451038800740f0700f542079020360140400040900b500300000d00b4a5280e19407150710541d40c0001401ca006900c0014910107100740c00c6546a0444000c5988a280040c0000025a1140240a0f8001d000850610f0005141c011504000c3c807107400303840c45203c4100f5040c0001401e008030b40a0611040d1004510126807010540d64403c807802d80540341054180202100c184060070010000c0e070700112120000300b1010401c04800b03e42941070280311552084400c82d0728201a40154000e81c0b0502229032541c2e0003044100a9072400d60701c041484081c0360049440210301074041e80c1004400c01880b4240102048031031140b00c00301c1c211511246141c0080324156041d1041 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 290837338 1250 290836088 290836111
    0x10e07020c0d0609050a0f05030304150903171504090b0a06140603012c01230301020a1704020d0c0f0303030b030a0b070c030c06020a020a0212070b09090a1103010902070614 76
    0x5140020b16544d001c40a024021070072550544110b40d6110110003007880c050307655500210401c001c1217040130f01501c103901a8142803081008603940a400c24001c05102d06140000308000f03410001000d0303e0b03041c0328000400071300202d00c0b141802c9520314401d81c1e810440c141070000101e04001c03882040084c10001811540c81c1d61702c0c01141c91550b050100d84640c41007071210012241e04079003680b03d40a03181e509419041e0042d08079240c440c0c0c0710700d45001802a401800103584680e000703107a9072000700f103085200c01559101d20001d5081d02103028002c1414800c0e12000c1406034140300c80c2c000b070341e120b81c60070844100e00000701540d0341c40c0e161000f02100780010009000907c01c072152241c03148031b0f00744030060036025919281a42c101159500060b8042410b84040d854030700b008420004120002e0300c10141000882456481100d40440c010f0044801259100b100350307003c03d003a0701600e500c0544030b585560600b4080e5120420640b0b09a0403c5d41e42c2c018542c685c0700c014050041c0402 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 290838588 1250 290837338 290837359
    0x120203060f09040611071a0601020a020112021b07090c021207110d02040221060307090207150504051501060804060b0906010e151b031b030c0c0415031a010e07020c 72
    0x1c000b00e0400040003103503e0390f120b94800090320fa6841c05450f2061041030b413100b98544460b42ea1066107002041c090456204403202c0000d41d030407522b442005044500c000d0780e00e001c610200c0e140d4091101c0c0d00c3d00303a889500c100090b500e2043e80f1406100c00d00750300f0b80301c0c0c4590a068002481c003c45101500401002c03c1c901c0141c9841d00030a04c52a01c060070260402e280059440340121610702c41c410307510128401c002070703450b09011107005800c020703808505102403511a083d103040191089002543d032000800c0601c6030030005503440d030201000d40f420941c2c44a000500800b01950f0841d2881e0816003240706c11303e051800541300e0310042c3d450080e01e66070b0004000c0140f066050948101d0800c100185085072010340b00c410300c5400e14001d41d42c0b5103107072080703107c6441d9640503c100c581082c06025085407000c41c4841001400316400f185840e00426008240321150f40010003040500414025201581c0205030480e18540c5d12940300d03544450099807200300c10b1030000e621212844 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 290839838 1250 290838588 290838619
    0x706110c06091c3008220c06030204090f0c021c1407050604020f0d0f0803040201030f060909110121050903040503151501020c010807053712020306 65
    0x1d0722001a00804501d01410400100001c0a1480e84203640d504c41c11201030200e0340710650802450200320a0581c0143e2811000401c1254058034189a890900c242194039030145100360401607040382104442035034a81001e402580300c2d100c0d400840c2d0400e1039400003c0d01c9032042c0b0769104501c1e00603050100c40016441e03a02205e40c51000709024031014210000b04002c40603104c460b224800610396402c4c0781c0108003540703070700203521440703004000b11a200103080301c11803442ca91f5104224131b450340c4503840140c014103a8100c858012034030300380d000591000682c02c000d1507540550144600c2800c16401110040d00c0e80b1000c4070303101310300e140240301134a8035440a5440b081d0706080da400c00c0d4440c400603040c455400c02d102c260500000910001f409800c0600d88541c4d000d000a151190f400400a8407401c8020401d005105012400310b203c0b414002d02004415441c41884403a0318200b403103420140f00b03811602c000a035201c403022071703040d9003031081b2030203183c1c0200034945446400c2d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 290841088 1250 290839838 290839849
    0x40506031f33030e0111071506050f01050d11030403090e060909061f090207080405090a1401210c0b2a0a020d03090317090f030102180111120c06090706110c 69
    0xa51142d410513581c0d142c2c1c045500c41c04e1041c0020f11010702c040f60343d100c0c0a424440803d07030099640b10003442c07400c4401c01103a600c15000440c03c44c0d0a0070442c1d154103400c10514020140100c4d00340788801e00104200070143c0c4040300009070b0f0051000d0040320788651044c41048402240c08480990003840803402940c00c185441e1f25202d10f804100038041e0320380da644000e980010070125100c000c0131030705100c0c52502c0411107a0118107a1002c11a00d01030b0840251071080c1032281611484140b5119031500304042e03040c0680a42104150340b03c0d940d25803044805a204030100d0002003100e0169005c0d121415920010800d040801403c0d0302999408100840c842210220144080d2400000002e50400b03e00018240c0c00c44104d6211000441400820b812442480e4800e901c10802688904004007031211228420b1030421001138281158500c0c1c00c0c9c82843c5152514404105160b2200300092198428800441903901c50b80c1e0700c6806071b50400030324110254980040301280c02c0f50a04 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 290842338 1250 290841088 290841179
    0x30a060b030a020307090203010504051f1202010509091503120a0207030803060d0b090102071b050918031c09020f331b011d06131502040506031f 64
    0x14103841040d82c541c0c0c0040c3c80d02070a640500301c1660044010001071070640325040d401036010030072a00680328100041c088440d980204101200d0030340100c4196446602941c600c44406099098642084114000b8540070116100d100e84140310810800081280640700000c40a03001001e48070306641d607024442d000140f541d138101980d0311104000c03500310714040340600034807400180d03222000e0030203540b40e05501001c1e211401340d64408100c0d5498628034654040c6c0e2404480240300078030b2500600b544a000014251031750b80254003a883c1042e44c2c0b1000c0107c0c401c8500036000f5542a06010039140c10140076844000000107242d030b000025005031141d00c8003441121318052404004012070a4071140c103004136956200c4401c50704103a80244190b020001008004074504409243c1a14030f18040003021200840300c4408450800c0c1c042c0c401401000308029100d162840f0803828010510301181000c20450030001903801b01700208401d48402c1e15405458181c03040c2c0c42008400c5e0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 290843588 1250 290842338 290842361
    0x17120304050a0b01030b1504060308090108100305010e0d08060405060108041e06050f0f2401030b01020c04050a0902180912030601020a120f0e0109080d0e011701151d030a06 76
    0x1500d260b00700090070001e070850296206118840d12418580b120340703110b420701100c5900a030b141080c1400441c0c5540d003074079a07619091800d0391856490084480a80c50142d000078170365800d290010312034200c04038203040d81d0b200a40d502d41d4255120400c0109440085c0c0720700740401c07403800110b008941c40341c3c010b5032469004911811681500e50340c102c203d81c01101c084000d01e004000388144a264410040e8100341c520741c9401c2016040c56030302240c00302180c4201d0503d90b9814142007280d00910020750341c40001002001140380801c03c1102502c600c100c224401d400c50000c910300000c1626105003d03680020040c00702c0391042000002550001d00030906610540301030350009011151380c02c1c002120340d078540d5400c8150403030240c240156806014140417003104c003401004000240b40442e0f41d024503101460018203001039511048100d100c101c1c041603c4004070b09241c085c071483d80240d40983e1a0100c41c1a03680b1340310b6071109a0010180d054000301c00460100e2002e42196041c6031 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 290844838 1250 290843588 290843593
    0x1808070c030b090303011802090114030a09080d020703090617010303032a0e130b1302071a0103030207061205010b07020904060e0d081602070614030c0403060c020609071712030405 79
    0x903180c2d1aa42c020400454601800b54070000040c0401424000c2c000c2c5244005141507042040c0200080c2a010460094513091a0040001400c080030f0b03030000c2550b2030b00095a40e0707485155400c080080e5100550503030119050400008403a0703c24509102c0346114100f021110ba42140d03411400740c0b290600703400d89036044030041d10888400f90f0302c10303412040c0b94841070121080c090502075a440d0b070000c0354144610b05103030503400303403221580010341c0c603404000180c0d1940d96203001035400d207140e02114100c02105001200701900040c50380c0560f0107544600700b60f1507980790504180c40c1c0034011501180390070300054006007412080c458009104500101d0701c541114499807400b0080c2d94003200080f00c3c841400360300b0052034400755080b101840034250300d9040c000c01030601600f0070200c0c0d044c507000200256a06025005550107194400800c5c029200c5105000790b030b5a40c06e130303604140781c095503038001640000da14031510034074000f40240040c0700e21240401e6070b68000503c251220b0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 290846088 1250 290844838 290844863
    0x1503030f18130b06120606040305150a0e0303010605041205010e0115030b01080f0a0209071803030908010524100c060609050106020d030c0813050f070305010f0e01180807 75
    0x2280325805400300d10512820020070034000420002d24902541d491980286031601c200b0311903c0d5403080710f561584000c40c000d02c03512044040350f9580f0a552001d4528060101c4603200081086407042c080c2d0043c08041c0040000303082c0c12500d82c4000c0c840c240100b4402c1108100a040941d600c800b11406140001221408908000d007501c0e502c031400c0b103e64060190a1003080708c00f11285014108941c000c041c9540c800b011266a20305041d8082e10620820f000121058403541107101c10f5416041c1c940c071101d81c0c0385005442c00312075000d02381455003444002008512030704520064500d07003640e104031661028003400319030020301e1716480410000b0f040c0d0b01c0206a40d801180021306090000052070740c9480c80090500071400070040405081c4856031034010345c031140060304482c2005204a40e0683c514005141c640c50071300000c0e4038020950004203004041d07001c140c480d004910180000c00910108500b07c5420b40b00503092448490000c0d004074400c100500907480c851407c41841 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 290847338 1250 290846088 290846107
    0x1260c030a291018050903030c130b0703051b0d0c081b0303040f02120615061621020c0a054e01142401020c061809010815150303 57
    0x22501c00319209004029100004c000e6070052400d444041030707032504204614200700c40340503202c1c480039001904440c1d02103442d5220821940a51006140c2d000c2441c1d5101014035001d813141d002031101c10604100741e80803000303220001c515941a06003564840510382d486644100c1c8541001c0a05504000c1700482502c03040c030100015400b45000d5402e5440b4400c51b4130402a4411404040b48005e400460a0180a424a485403010000110740c02d9840d4542900a070b034503441074100103014010149060302400c2c3c40c0406d2583d0300d00b519070940d02c003c1030a81c1400303400700380e44c492682c208450b4802100b02249082d1002d980c6c5883c0d00840c0703031428000c02c1c600303484600040e10241e090f524008603600e0002c244541c2070100d1042a5014551a0100a07003e04015100103d00c00c200724011003a450f80c401d000042080d08003c00c00368a4501e44001d000c110341c0021487c030f0080240303030300104080600180030030304448040004145030b603c05200f42d0703101c0e403803d92444d0035100901ca40c030390 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 290848588 1250 290847338 290847413
    0x20901150c0b1519080f030a050412020d02100c06060f060c0204020d110f03100e06060405060c0c060313020307050d122105010914070f050901050a1701260c030a 71
    0x42204d407081c0a281207074204082e450400c0c208452100359544204015064560403c0c107480c1190801282180c4c40200d50003c224041c85070710000754007042c0d0380d00d1035050700c0c2c0061549401c0380c0558010440a51110f200c01030410a074003420000c208204e108100619007030f0010000060041c801041d0310000140115031038000b0301140717500980c04010030022000400700117000301084003400040e0300f00351010a0403071065024160103030b10001a4020020790801c030341c0c0c545410103000b540c0d0b649011001c000000400700340881c802e000c1c1ba800041c0501d030200c01d4144450304000904444000ba4a007641d211441c0105180100f00070b040d4420217510340e100f103600a0150100c00304841c0d4610000c2da0341a0b078014690004e00400103858507039113612605803541c6032401c1c20929625a9040300540e41100c4105c22441040410030010900c03030400580a411089070340001803010051196140d02c0b052401045501070340308a01180118001e0b5030f40c3c5e071000e0903102c2161803080325242e0945 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 290849838 1250 290848588 290848609
    0x20a0818060c0303090102090306100e070c03030e0604030207090b01030504110904030c080f03010302100f140f04050316030611040e061e100804050c04020a09090f020c07080109020901150c0b15 85
    0x10440c7d502141c1d6410314242848034590103500345402e411a42d00340300d00000304580c05400101041283c0d00c40400305030290307200000c003d10081c110303401d910342440c009545202c1405100c18050611010307019030750180c05018011648189001184c10400b4203101900300018415001c1201c102c8200340071504000c001c0c044140e81c0440e49030340350706600501601c4035201a15030f08010402182d0480c0c550320040c2c460020031980e50a81d070b13845450600145900941c0c01181d8180182c03075003940381d03508100f002421a40b00390028000304da0912aa0356076400f441c400d03103c0603003900000408520300401f050603e0880ca21410813000044008903410b48a009041e10108854106000c14007108101041c00d1540840e001d510306080810004d1110042c0e114100c146601d40c0e2420003096943c1d010382e00258050301c101e0300f41c2e5642e5140d0354042d104a01c004c1c0e004a0303040c0c3c0045030484103421b0f00048003a981c0c95091714908642c0c1d0305a45c0b103100030034084014460309035041295540c0c90121 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 290851088 1250 290849838 290849851
    0x150806060f010c1e0c0b090d02040506040b150d0c020705030d050304030201090b040b04060f1a0121050c130b0403110f0112110408060f04020d02130905010c051801020a0818060c0303 80
    0x10380160940c0750480c2e205c0078035041140d00c0c0c04107200b001041d6490910141d0034560656001c2003c1c0c5406d00443c000d0070a0350500e0380d0160910386c001c4802c90a03040648042014808140000750039000c0a1b41c540c0710a02545130150415007898202c18042c000544d0418441d100003d00d14815480d51000c42c1010303501291440b0050083c0300900001c3e000d4800c02a0708203d0402a54241002101400917a9841603041c44400e00740c0c1480d819844d1030411500400000a10851400d0f021100307059003c00341828491031890b1000c43c00310300420948007034941c00300307101d1100c4600d0800c0002145928840b5810004d003080313a150810300e507001c0c0d1450555104012a1500e046c145164185540101051000c1c8102e030308000250707554042ca07524494050310b02441041000c09480c000d04a0000c01901541c00c0043c00200030313600c03100902846e50117840070007941c14284012a2500c0d01c03190301034050007041c001e170b0b400503036401d54900c80d0174001840301c0d00d070450394402c40d4296001195031 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 290852338 1250 290851088 290851133
    0xf1e070203090409081c33170609061e010e060d060c08010602010c0c02090a0b06120702150106031b05031005030708010f050c0705070303080a0207140c0103150806060f010c 76
    0x10710914501070706c100049100750011b02c09003021040341d15111180e81d0301d04c0b0042009004017480024030812110180465000307000c43d20540000c100c2e0307220025510021103220700e40c00600f1000361040d00403445112600c100c5681d0f480c00e0700c100c0f5221805170140c0c0d070041c11110030000150031849441c125a203030342c66854403503140c428064215030003080076800b4409482031010050b80e8240032184d211074070000c000744000d480404102e140c0980c1034680058080386007804142500050090200c0301e4100034943e460380c0f101c400301c09903158138a000e111403000d02d0204005034041c801469004051710f0710083c083c1d03a11030000380750101070791100d0f2a9955808960425038105c0c0a143d0340300f058424450f00e0180320760b13541641c1d000d15101c060200b2001c000484d0300c188003501101c4c4001c0c0c100c02c15010b06452044c041c0d1b00c40e0b085000090200b481c24243c142020110f805120460341c003507015045640d1110248240d01d00140c80e000c1c10051b00c4c0c104800042d4201e00000c0b41081801d90 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 290853588 1250 290852338 290852347
    0x306030605011a070611070f060f1a0306070305062709070909030207060e060d0f0e0c09070e0d02060f030c04060e010c0c03061a0603130204050f1e07020309040908 72
    0xc000c011220107802010140c0019881445031203440c0c42118400c99101d9000140c501c24008110003501816400804044452046074107200d07e68000300e1783d03085050b0302040240c814240000f25024014103a54168202400003000d240c080c3d844036078064009401c0780c01b210880d80003550500e0382d607881c7d100082608000d01a0f07500c0300b008144060500d4840c200420900780d00e02a544041a118440400007200c5c0a41ea580d2078180a071000c8a0b80104c0034880c420590185001500741914a2485e51103003141c038402ca0710f00181082c1c010691920741e103a26090b42e40c18860000c0603c5004d070780045040150916003140303600154030940c03452100720b0721242000001064503030311505c2541040098044070011440d04400d81c0d040300d80c012000614400418404590484c0d00160f2a502103408020000d810b4815010702644038821075081000327568042c011141c7d00400e0700c1c00040c641142c0341f01c0f03181d07010100103030741c01c120f03140116400c0c100c50038001803c0d148265001c9501000200d0f = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 290854838 1250 290853588 290853593
    0x51518101112030c04031202010f020d020702180f01090b011803030801080d020f06060d15060f09110c120307050d050c120a020a080411010e031905120a05090d14030a030603 76
    0x1082c0b2411185161942c102448500c1a0f40103600010305021480c1d6082c20800b4001d40c0400c454044401040d92220f41903400703540250440c110a90203800d0b070800301c042a690040c1414425210b003c042d01d02a400e004040d0010412011f5007814001003401040204480401440045200f0303074568032950704224110f0300301400c0381114401d5500c83e0009403160b690106d10181d1004040c1c68507211517255080c480e16112003210510b10307551a05401042440c0440300800030340d14014421300c80c01203525170300c01080c030441d40030740c0c03580d00514203820030385035010001c64210440340b0702542023960300070445003142d000fa103001000740c200044281d0800004402e42d948006507400450401c10820006844000024002405010078200084140c0c0c0507000e6003080c0342c0d0280888a9101b2406420f1100c0004410f0545080c490300400c00f120034080d404560006034165602414440b9203014403002c1d01802008a506c01c004c0f40c1002c40400d010405001032180c1c0c1d6034046072461450 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 290856088 1250 290854838 290854843
    0x314040501051e040803010302150409020c07080d020a031b0804050a090606020d050313150615180b1314040204121118130807150908070b100515181011 67
    0x111100c2d40c030f0f04000740401011542150549046a4040d9051444401e280399605441c6c492a000154040d1001c6134104040301c0c0000c4040981e202a07040320000b000a8805036034859408100070b0024900e0710001030400c0201c400c0702105803181000606281e15480064000d0f50303150051549156900020800107a04000b00380c0c510400d41091842e505107170349840c040c05100b14002d0080e007841198041d0918541c0c2c4050002c1030004200200b40050100040014100902011110314068804280340340340c141141c1c041945510841442407408001100c048260070400f0341c031941c01c4c07000203401010000346e103100320300c9803001444000d401401c010014008400708014550088100040c58090360400804107821114254072407a6600d000d80405c6403d0b0321120704942030904e10000c0000c81400342c0007581c40b444030305c50665035180a0fa0701c1c1049501c0f4141c0d01c11000800c0310500300f0b60f00010701400020320340c10460700480e407010503142c0482a0f45c950001c0d254000c00d02c50302d0740a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 290857338 1250 290856088 290856121
    0x60c01020a0c12090506190e060309070f080f0606120307150903030e12040b13150206040308090d020601050f041b12140610030c021c090303031404020a09020a031404050105 76
    0x35060110f0000d0030680802d069000305441001164403026114047d140034030090804444c008009a50341d1400000d12501d40c0705e2842444403180d0300b8507001c07851000106021181c07407001401801940d440c41c2c1000404c3c03192134106401030204114500204580001d035032210401c850010800b18074500d4001c0c05c6a940400e4040c2c80d03001030800483e0030405004450442d07410b000002d07207034540303100040e1101c05940d02207100c0b8100d1103070515040740c011562600c254007a40744c8229903036031045000d4441e10900103010050304000c0040c40740b85800603a4a01841000e44001070204107940703075041880080000c40d0100700b01c0d40100303010b4045801860704200c0c90050061143c20308a0124210b0381ea0300341c0e0348080c5a21004804c0d01c0c50320820032a01034803809600844810305440c009007050149000c01c1d00020706100010a00315054425140640d60140290441619010950300250041e004480806455001c040b00c580c0003044407901590045000050700d0a1a41014030072003007 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 290858588 1250 290857338 290857373
    0x5070509070c03020d0305060a0902071401180c03080d09050327012109080c0601090c030b010e011b05032a0606090106080a09060f0504060f050603030c1b060c01020a0c 74
    0x2090b010620009038003080307003103180c030741402c002c40e06071680f0002605201c901c2d04001e40451000c036155042c0100384185212413003123030000700402c0c021a050801004c160500182030050001800c20010703080d20002c0c0700e00c01d2560300c00950081542c1d1020300f150f000e240c4e0080030501d1b05c10038001c000d254141d0588c1c40300c82403d14140480303040742807a040281c1c0c0c03209090a160b035141d0050900c02181d080b00c00300c6248000b40d80350341d81c499103250000c1c040c07009680b0000b4075114070302c00194002d03160600f804e00140c44040ca000e00001071091022080c40c1d08480500043c480c0e0f03460788821904904842525013030030100b2032042c036580c9280940090841c1e00c9140104010401141c0102c1180d410000070000840c049041c1d0504402415144c040d40b54420f1400c420001070214503071220b40d19601800b01805140c035101d080690343d0160041c2c807001500003020400500343c18854101c10b1000182046042c6503038885007500f2030f007000050801180b8240559002c204d90002c84000c02d52 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 290859838 1250 290858588 290858597
    0x313061d01110c04020d020d020301080a0b0105030703080421170c011514060a11061003060e010506060a030f090b01080a1b0605040308030703090b040503091e030d031d01090507050907 81
    0x81070b94506a9807500e400f1454040c542c009850406024180c04540416402080035556540d560004558a144d00181920501c000070000f042d00e2502280316022290010341c0d407410141016409074442c0e0070205820041c4c50003101201c0081c140402c02d050f6800d103d0b82e16626092401d211070700396440c00e9440115174058103401c0c00101c8110303c0b40314034010305996aa031684d0001a09555000c04141e91086512034101044070b0008404420026030f44a141d00303010b10303061102d2080c262081540d149a10200900203012054800c1e072240b0b000000c2c031000483d0342c00303458172900800750007030704000c005400a0b801d070010b201c20051070306132007003140308080b01c0d20380b030000001c0041c0070b58003000340340141c00000701d0280d074800d8210342244d6800016444150509181c126038039440040304030300404c2600c616842c0152249800a005030300603000e400d2141c1e0300c00007200102404140301c9000c09558402c003102650234130951742868498001086280e00f802c0420224040040100c1c0030417 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 290861088 1250 290859838 290859857
    0x7030c03060540050a0605101728091a01030c0501080c2b0e03160f020409120c0c0b0c10050901020903121c020301051e030313061d01 59
    0x241c80b0b000e480c0c46041c0c50303040d40324480c1c01010400003c20318a501d08281030101e001c0040401e0000d030384100c1c00f0343c44c01541003107520b980d00c043c403005041c9280d012001c0390100364011520b9403001c082c103600040104180350b040c90030421007100f9180f82c464802400b0380c0c2c0c40a403c01c110f00d401d40e034200f484003041d070041036624507902e00b606020704c0c3c015a030402c1310341c2003c0740c02410000140c07011308a090400c010301a100c401016098030000080d11400360420003030045040e804000c032551076060003c1c807119100380f5241c0d01d8540b204580c080b81c000750350341e21600c0801c6505611160402103580c03208081041420010b131546c41070707089580001307020480190003c40000b190920340403206408034003561112015030090141941164150250410715004008180018100041c211103040300b5680c4105141089000074040c0b1070300551140b404042e01418000b055045a00c01411249404400302c0414a4003072583c2c420b00c04500702c01c0424403001501408801400340030b20b0001e030301 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 290862338 1250 290861088 290861099
    0x304051801030b0a0207060603020d1410020306030d031107020613090e010b0d0b060a03050715090b070519060b0411040302010f020a031b0c0305030301081509010603082b1407030c0306 81
    0x1d0400039002c502105d40c0012400704201a03900004003d41d002007602400d98814104154180309500c9007041c58011004035520080d020310a4070700130b0401400800c00d142944000b0307401000c844d90709440c60a02030051034010380c1c51100400e242811225013120162900d078580d4292024507060840c00d9040001d20300d20358451900c11032080ba0000540d044948900000c01c5005e08990805000d6004d03140f800709900007030311460521080700355a503240c43c0e580c82c1000d2681e4003607410014651b41140100f1180e410840201c202e61902a000000e0410b003107a00207001c44641c01c06800340c02d0801324080007035681203803030580342c2ca030301c2d0000d0030b848901594001c040c0b1801c4087e00404401c2c044011043c8a08840164083d543c0314040301d40d25611442c0450b0346400030302c009148030f41404000f0f15001418001c4400b101d501a240c0d5061141c02e421030030122250110210b0060111040151503400600078528084880c114003803050900c184002d00f82ca002c160210103040c1498410000c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 290863588 1250 290862338 290862353
    0x150203030103080a2109110a05030601241b0302070617070c14030c120723100218100e150c030f07050c060d060602190b0f0601021905030405180103 65
    0x2141c50303490107042c0180c1800c181401041d0900f264890785c2d15040302c40c800c1100440d59100d060404803014243c00f40d440d000c05540300c0b000d020390140d80c0e006000d0003041201d034800c003034a400c01074100640d08800e41c0e22600720388404004141d005034090082001425000b00c0454401d6044c140c04414030700e81104080c05c080c00c5048010440c0c4410004200901c000b8010345114802d00001ea8020000d2000a03038096013189501317131032803041c81000c440082440580c4906612004021300b00d8003081c260600001d401ca034103100d01c02040c901415146585400030034200e18640e0701c941c81002008001d100d401541c054040080c40820003d00c8065440001940c00c1014004003440c4d03514190f10304507086c42940e40c091130300507201081101212034690007030000d0f074429034201e90490845240401d0140c1d070001028001c80c0703071540428050a000080c140c0c0c03048042c01102d5145c0d02c90001d40b911102c40003800e4a440e0801300d410710503490030403015805400c10000103812941161109003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 290864838 1250 290863588 290863597
    0x100201090218190b21010605030703060203010f0b1e0705011409030c0f030412060b0303091c12020312040308090c090a060501180e0c0a03060b1201050108090f19020301021c0615020303010308 84
    0x105c07560402d046400303036210035003040c8058500039081d60700c42981c0f49032410180d0801c0c0100711001154410100d07500e185203080c0d401303001c2000d481c0866038034456600c1405a10140082d40d1b1135486030b12185001550041407800780701500000c641d24940101940c1c00e25002d4004401107800c100401c1045425441282c000f00f60401000202c0e2166100020720714415201610381050b10198880e001e040c0c541d0110121038020540d00100306424101281c0b0792207240241c05103030038414041800b0034455500f89174024013810440c1c4420100360b000440901c0211008041a502d402081c090b550307101e2075802c407600f009110004000c0c01c00081c1c02030302c500203103611018040412103400aa1003508498010007003079401541d151401184c40da490f20b0300b4080c0030f01003501c07040451032002c000941a6608100c0704080e1411150142d265404c000740c01c3c0c02607074599001d11504580366212440100b10310103040d000203441d031900c3c1001c1c41c4028401c520505541003030004001041941c000c44 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 290866088 1250 290864838 290864869
    0xc27120a05250905010603020a09082109010507050f030d0b0f030601060e061606050f0106050c06012304051303090803041a03040804180902130218100201090218190b 73
    0x41071012950028007500c0c40ea07a0f01c009800303402c0800006100ea0580e00130300c0301e5003143d034400550544580700c2c140e90760b56400c02031000c0c503034000c1844510032503080a8003074010149801c6184c25160b0b200e5500e07084050280a94076007000620745060100ca124100c1c0e0240b09641c0c108145031480300098580d5814030882091205d0a111a001d582c0c58008580c00c1c00c128144a8000c3d03240c1381840d100828088500030050017020002040e6240030304103540701c484a48000300040e07800c099203200413000c040a442008091030724012001e50b21405024416880d030400c101809655040003000d0700066480701903140c000300400e021119003402007903111039444c1c1d03949a803500c440c945041c1c54441d6600070005105200f01212541080d604070300b554a00813100c1c68069a0008107410880c404c0300040708604402e0515081241480030b400c0007480c00ea4000012402d9140d00403034520320074950304a4005905200708407900c0c00c0308401d202c000442a0003000070340404004520341c0740502c2c100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 290867338 1250 290866088 290866123
    0x121b0a1217180303070b07030b060415120b12030c070519060327031d031b0922080325080f04020d0507060e0f060a08040206030c27120a05 61
    0x80300550104104844515800602180d07540c0c40c40b17080a2400c03c40c1650140006428081e003442c080c078001d02031700c058071500c2d10900c0b078880902c0402d8440d0380c40360511104454944c2c00081013075945c03853f03d00400c98003401550355286004003070760806450b6040284541c84800401065031148181c030300075104a8200000e01c0003c038400c848003901c0d4200d8202044000c00d03d00800c1560040b00d808214807003c070080c2c00c2010590030591501011419003101d111900c02d202e003145800401c2e150090f010900da481d42402802c00741d20f032044086400e9424000000c00d0049a01114025110000160103035a4a1548281d8000d00c442d00c0036194103800440c000116066641e4650090f84c0c156001e0200c4082d2a5a20009030110f0700d0240294131507980b25080d08003a04024007256415440c6503a01d0302940e490340e003000700f141c10250000248002c140000e003801169045ca4403000080d030fa0401660240c04020410b82e808a256425007580080885034002500000c41c0d02e4200c82d00c880 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 290868588 1250 290867338 290867347
    0x70e0d080c0303100302040c320c070308041a030402030c010f27080d0c121b050607030501030606080109050a12050d150e011a04060e121b0a1217 64
    0x140039005004825181500d40400014842007a20300320091048920030340d41032041c1c02160005489040e022400c4038444880d00149000b140f0601403038802c040d80d103402d00f500784050303c5a064544801500100e50382600081c1c240504021130000d94528001d4403502c0d860b520f00790f8080303034072004c002c41c1d69030611100480c1541c145000d0b201000e90700020200301c0c130a04402000208400340644540742036805031404000c011b5118101c00d1000503040401e01c0c000e1480c05404460f080a035042000c2c0320400303408007600040d001d0003000e004901658001c1055411410030714110f0300350381e001981c10ba15001c26000054004100750703180c075400a0501c244603182170025105031164500e000b0400f0b2500ca208220b1291440c4c80c801a03c0c280d55400e01c2e1030782c98042200c0708906030283d030004400103100800040c0d200300c000d603008880c00381905000707000070741c00e5070f250001000180107030350380030f50310b01c070031810242c02200041c960b0004900c0d008a16481340c400800c0301182e40756010a0015 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 290869838 1250 290868588 290868593
    0x50a0c110405090618030a1e020f06010b03160e0102060f070315060302040914040201020a080c070e0a0c020d05090105090603090a020306090607020d03050c03010510030e07090c02070905070e0d 85
    0x2100c240e220005042800b0302e14007003084640380c4600325500015509400c1c5200d402c241d0000558091200603141c0100c0100705040f000a140c901c401030a0442c842d10703920b00300c289014480507000744a000d00c110303282e040918910f070b40c900c81c107a988003c0052000d55018660380c0016060782001c900113600006403620784044000d80841000802040108040081d905925030300030021901e19000c01c00c09842c000034011303182d40090340c0190045c0d114100c40c00210b50410024011090050200c0d070540303a0311961024240340840d4619082a0340b0141d031818541c051020b01103124080c6031203803800301c070000041c2080c05080d000c0b0f40110f4001c1b00292042074100004400150010110340304d5141440c2d000b582c07144120755840c01401068681907a05000380202405018403400c2242980e0070712040c0081101c0e50300410381055111980344c24000b0702884000d02508282c10040b031000204203002e40342102c25070203a240c1c42d00c1c0ca4104241aa402100940400d608407169501c02d1585e0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 290871088 1250 290869838 290869853
    0x601020c09071b0c08070602060105090c0405100c0203070306050403020d02010608100902040b0d0521040303080a020906190e04060b1c0b01050c120d060b070b060909071e08060f07050a0c 82
    0x80c4004040410014002c507083c5c8001032840125981a4200d803841d0382c81d1000e01030039900c251440d070540721080c4010b0100b0310704200c6850805c81186010a506c8606070002032400403d03a105a030003540e20300510003855810300c0700703001190345800240002c1e413804203034986d0f42c4072a41d100c80581e59500d1500c0c08568071500442060b0000600d01c103421540f6087c003a844501010f074018101590640c42514485070034155000c4a4140e22080b0a9a403015103900180d444004600d40c03001c4108104404225103001200c400c1e610743da124040c1d260042c09100844200d5001107490300c2c002d0064640c1040c0f0700344141c0501d11900d9000c00e0905880c801a1214010f42816080e03a010b080a6909003409050180082001003602403000782d5440c0311070051842035200252100e607605000441034108014942d4012402404031b4105554030b040b9540740c400c1c105405050b1038074034001000404002c0020075049110240b001c00d05003011507014185204440c0404240700000181d1030038000036 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 290872338 1250 290871088 290871137
    0x503152803080415170708070905030607020a0618020d0f020a08060109051f08060a0902060d020a080901050610050307141e0d0e01060f0905100302030307030f02060601020c0907 78
    0x350014200829220302e04101660007a01401d0100300702c0740003080050707101d8041c00c00b4155000050304001c0c1c980c1c440c12510000d0081844c0309120501400251030348041120034441c96159001c3c04001445191070f40c03d40b0204030400040782a680f15620241c5c1d06c0c02001001c80d503000032070b890307828054408611880c40d95070000f0003d0258000014540085070040ca02c5103c03e0000d541885a0300d40405150070610300554126031300000018070701002c241c0c8003981280c00200b186081c2901012801c040e64820018040020740010038410305010034050039400640171114079a62201d0408c0042c06030100801140c00c02441601d00c031001200c5034201d96040c0c1e10b503491132503800c07810080da404550001c848541c0e450702d0800105d80c0c0780c0c0d0603c207030f0058850b0000080380e0203180c00642c0700a854090007100f9030000203000040140c1d03040001300b200c148245c4404030848500d050103810100001c040b241503402c0a0000d910568030600c4450b4096242d00702040d003113171903525881d0311010 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 290873588 1250 290872338 290872399
    0x19050d1e0b0108060708040b070305040c17010209040608010b060a051303061103010501080714030c0a0207081506031203010303050307030c0c0b010b03010f0b211317070c06050315 79
    0xc0304080034044000300d6a03068850710821610300b901e4403041101e081c0402c5030060080c0c000d80c40803500d4240b0036000190000d010710020042603072a032040345480720301c074664400399039400110203145041c00d025910040841034020092035903482c010419522030b20500341d00304080068104046248010320101468108500300032140b0915220308140d4020f001d8540071808c03690004840610038141841d001011140d41030440d1241084958250481c070306990942c0104403002c00c542034204604481507200c1c40c24000b00303007001400d160605010b01e07101d41000e4400c00052003c1707604130f403c1302c0d00030b181303031400044407020031000302d80d204405440100030010090001035108141009181a0b503004032103103c441781e82d090850040d10886014504400e6822000c1401aa20251840d40004a00c1002d00d80281940c5c80302d032004da0740f4407022410000895940709014480c900540581814205a403450415001d400d461100310b2174824072502d103481c1044540d40c04583c440d99000d0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 290874838 1250 290873588 290873633
    0x3080f07080a0c0212030a0906050c071e0302100c03020d0e04091a040c06030e0a02060c0f0a05070e060607020d0b041103010c03060504270b0c09060408031819050d 72
    0xd90754009141d42603c0401340d204003440040201e080b000441143d56070b0601e6200d403001d89181c5101616a82c202110416490280304000101d18950a090309039074840701e9008034000b4114410400803c6030007180c40c3c204524545050000785c0c000a250101c1c0680303040c842d9440602c000010302500301918010705415910a07c00503c80c80004000d00403481500c1073301040d500e4003021800c030b0b1500c4243d04038940c44400301c070000d410454000e203840d02a00302078070746031641d900e40d540c134000303002d10215406c3d0b009050800c446903490071020b4116408591861510307031260001480c2886030040a0164800341c400300c1c0400c0303449941900601030240003440714030840d0070050000e10389446100d01990038000c5c0400c80242e41100448007247c1504802d1054441c0d85403054441801007101d08007440401507403515070b07180009400149400002155501141e401d4801f032070400f6003d0714026a038000c020700d2984c1c4080c07050310a031340f81511403507000121410000b8010f808031200800c841d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 290876088 1250 290874838 290874847
    0x140705011e090606170a060207020402070209181b0625020910031406070c0b0907050604090f0c030603030f12140f1e04030f030b0f040c08090d0e060403080f0708 71
    0x9001c03a410200707041e4000e0008100440d582c00c042c21a040404006500e01d41042545100040440d8098070a141c005000141480e00c3d580c04a04046816500d01c1001482c2c00300c1c41c10107c2c410001152040f075076135441785150a03070f1000300c1e08600410046403981c000310a07803030051903c080907041405400078402c1d221800c01618080a501550100340c408102c000e000f03035054580003400030700070b20f0309643d5074582103c0c80d03e1300c0000c840060000b02c0a4024120001180c0c1d562380b0217000a04035030000001c4260600241c28111244900f0f54402e140c20b28004002107500004024910140c90502a480f031175000040c0c001405003e041c04d040300c80000510030459890381c500703481a10030207810724262040746000d1500ea1011100180012115205050a00d200350000582100084c180070107052001000ae800da60281d1645000601036500b0002c9a6004015045000103107003090085502c4031008102684610f00028100d20000520405441e01200880d04581e4001581c580c95 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 290877338 1250 290876088 290876141
    0x2090c0705070e06040c08040f0f020a0f03111e2d0406091b090f05100c120c0b063c030a20010512040f020310060306050f01060203040614070501 64
    0xc80f4000e5402ca4011450700e102000c3c10703401082040d0160350801c07041108025640d440c4805292044412038101c0860407000030590762902004010790310039640342841c1c2d5403503424010b078402029440200507d0007500c0082c01d4a03082080c0165100c42102c40461210741c0c400103174402c3d00640c40d10f401c50314212001030365980580c080401346841881d003c40706007696500310707120703041c901800d8140c00001408000310701d80b04400046c114500d04265214030000c0d03c0b11414a014420400e01050407268103004010707114214a40c4010b04955550340ca020701c4854100d8404200001005552242040f102440144154091080d402011103114110030300d0148403030b0828900c842007526007540403100c03560041040d10700724480d01ca4030031307003030759540e140c02c070004c0720407801641c1501813407025955645083c01a0000f8500460300465281819849030001e110160300a008541050106001890344100ba0071100315009003000d8036072801e030401790b0050110840804104800e100000c40307 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 290878588 1250 290877338 290877359
    0xb10020c03100b030316060f0218090603060702031b0109020a030c0e0603030711040507030b19030512070c170c0a3c1a090d0b011a09090402090c070507 67
    0x8030004254161201041c00c0e040c00700c181e030b405480703c41c1d164006120040064a041031040400c500944002c54104144034100040f039000e61414036595001c103982103141d05041c41016081101a001041c4500c1e00680094980c00748102d100804011480304018045003504141034080e001010342c00015507038035081080d5440c600c510f280b03e00c1c42400080301c6107408000c0d00d8000d9040100e02d650220301c03504104c024131000304a2414159038100c3c10000707071100f8000e0152040e111002d07503001820b504184d071411a1988104200460030001400090303051403044088900036014210501d4800d0400c40c10042e01e581030541144c2840c40c001a10041d40b5051a0150941041d4031800c1342404600c840402e05070002c40c65041e810001001040c00c1004203c1000c0d200802035800c3c091040002050340348001ca041e07681c004c0110061141010804c1764500c1c0c51f02c400c000618041e4182c01054900700000c0001c0c0c40388030300200050309000410201c64660b5841300076600000c0d01c3d468940c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 290879838 1250 290878588 290878603
    0x6081b0a080a030c0209041a0a020d0f02040f0b070201050c030703020c040c020f0718090206160302150415052205011401080a0c170a021503011d160e01030b1002 71
    0x1441840e0103140040c1c030000200c1c1401d59640c05a481303001c0c000320340e02032000035003020b0012514800300c510b4002e01944001440707402948000320240e5a12881900201510000765910310518410001044010700300c80000d02103c10601e071240c0c9496840c0010f0362035002d90701c0c584800340800035000041540c0491101000c10302120f040084aa10020480e03a0300031100100426600c100e40901c0701c42c004640100c40b03018411804100002598041002034001d0285600000780f9107224004040c4c040c005404a001400b8481d402c2d80741c80c0d213880707807201b00c201c503e00700d0940e80e840892800010400890140350080e621014a0035542c54124000c008941011001400800010079002404540c0a044c0c580105e010307007103103041104c00303c6546064800c0c4a550300c5040d11040c010b0303e400d03101700091025800c025841e9858203050790001d100704020f58046610060070008152050340301d14204807810320b89042e44003270090044e4000d220088007203900c01c920041c4116038550005554 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 290881088 1250 290879838 290879893
    0x603041b09090b07120615030509010606050327070302121506040e070621091a070f170a0e0f03070201120513170f0a030209040c0801050f010c02040608 67
    0x4091039566149070408440c0024001000036503840045001c991140300000d0a1000944000402136920102100309681c0e40b07a6002c04203481d5000c00c5141e4101b0311482e8028881410514598500010310006040d03242c0741121003d4052817242801d00001c2001c04091a400b6002001c0d8100d00c81409580c4e042c90a2401c44441440001a0903420680104a55069518010510305041880a0304d01c0c400c001c40402d1408807103941d44407000c035640520000c10740254050141a219031001150f0101c00030007803400c2c4007030701202194583c0c0c0208251112801090303d102140c94a42d1800098021081114414851545450300001005c0000d00e25103100b43c0740d0791131400a0740b8101d000d40304210303580c91588411540c1000803400058040e4010352510b9841c51520f0140e038140c50181d00b045502200190b03001c0b9891b80641000e109000c044012410320071140d601d000e00284106500d8500b1a0400c50f1805101d0110340300c80d0480b0001d02404000d599082c403901980f0a440383e40340058 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 290882338 1250 290881088 290881133
    0xc0c0b0601031e0b030f1623090c0f1303080408010b09090307030305061203030a060f082a0301020c06161709030a0e130c0f0801081515010e060304 65
    0x104030305600910803041200da50304600c5001c24441058140281030403c0e800b40c041c040d448a0010090060100c40c001c2241100d030059040d080540c0c1c3c160b4021452451040074881040048043d0780c1e1980e01540186603070304c500e0303580c0324004074106c50703000b0340420b140c0c84400300202100b00030201001d002070303a270b4040080099502004c20005420016102ca40040d0410442400482c0c03194201a50004015100c03e45408031500c2c034503d10741c01160009000360348c0d540c05100740c15000c0081e8000709103080c01000d07101c00750404640c1c4640000000c8503d01840d0900c070305181c5003034064495410074102543e05500d4a04110710381e48101d40c5040b40029500001185804107400d4080e000d4030b107600041d400d26460460a031350148124880c6e1745d12601207060402c1d000780ea8021888045100e91f140b20b01103078000d8001c0c10940b4180c002269541003852060403a4942da80744a500920200e586401c5011400069940749a44050290007071340010400050241c041039500307545500cac404 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 290883588 1250 290882338 290882341
    0x140d060b33040b1801050f0d0b03120705030a0806010207090e01140601090b03010b0708040b040605071a0108120f250302070b040b070204230a1406040504030f0513090c0c0b 76
    0x2407a41140716500503c114200c050040540c203d41021004001403010304100380341804149110740d450300310107075941030340344c95a0b03080351076050500012030408501c0075038600385415940c4c1c0c5034690203010f0704001000107840006615a10800000c4000e1010035020400113401c04001d074042c0444c00b4602c4042103070400440c0095108094440468805019a0b81164242202c1400507880f1700815148408188000309403243c003000200000d00403607c07a1662490a4070b019039581041a103503c40400c07612004200f4030501054440ca05c50404802070341e5000d0ba803a2540c181e0041413038034038407611001713580191a00c0040c0d10403040d5019808554405565152100c417600c43ca004034014080b041c415800107084c20703004859081000c0c0504100740000045d1201c01394030456000b040309868035070714540100c001d4a2103410540a030b038140900e2406131806090503104442580c10094006118150309140c013030b211000c0c000703c01c1d081c4250742400c07500404a0710500c43c140e604140450 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 290884838 1250 290883588 290883679
    0x10f0c0203090a1217030702010b060a080f150906040f020c03042c010305030d05192c0c03070614041a0703030f02090d08090301020c0601090203011e140d060b 70
    0x1004030031940005030741d4a83e6400c180381070403904080c00e05808d40d9262116260f031541c401005d04081030b1a076407285a14503280d0f000d114980d0000d09002c1900380e890000020b99280c4140040c0c0c4040700317441c04900700c100205000c00a10032807100a02e0b50001007404120b00041c0039a16806400010916410150015004100b05c0b401e2000400c85c0c0d00070001e15012644680005900484001d0782400d00018000700b50140c8095441001081111300c04809000030914a001015020100201984504074010903502c00b42c0f40a4134040c060b0103034116000509031011140904040d8007110070b0b19101070701ca00c449801590046020900303200386010728034010b1017600c2d500c10005080c1c40d880500758071410300a0303118809240c2c155408103d0898984810440cdc03500074404904c0c01030b50f84d80b4001b48444500a0640810000c0014550410024440650542903d041141c0114403041c82d031419800524044100d00e400203800000024040d000d42d200d0710720501d1850403005454841c6 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 290886088 1250 290884838 290884859
    0x11031003020d0201090305030a27030b0114061e070213050906040f0501060b04060c060605040203060a03110415062115030b09120415090f051c020102010f0c0203090a 73
    0x121004614444440010800741ca054403802d03084500604040480540300d8465600b1035000408190100c0c0340303e5452161050300641c0d40029401082840340803d0466941700114141841107003128480d02d0707401080c40d9260400c445001141502203034103031240014065298102d2001a4441d6007120840220201c0f28000ca9104100c003d000e07010941d00c59440d294502d07004002602c0665803a2000304090398500000d001425298035202403882e0185488802e0340c2c0d403504001e01460050091100580351414218240ca600c0038000250101000c0030030014410525035440100340d0140024900b601f254a04983c8454541140c08414580c0041d400350317820044c01c0700c812106c4030f20400210721001444e54004014030180ca00720300103018007403295006500700485000000c01410f42a64004040d4001000d11108420440d8940000500c8a002c0098440083d006059071034045a00c00c0d4000350204044803c10403580c0803000000307649410401d01c050103900502030224110014 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 290887338 1250 290886088 290886091
    0x7030b061e011209080d0911100801050d0302030903070306020301260d1b060914150709031118040303060f0b03010b03181207050d080c090d12050d09050606041103 72
    0x507070a09411035204040110f506081144640700c40030f035104254400908820f0003031a180740d1964003c1020545418030044a07040000d9143c07040d06105440c1d28800e812150050464800315014407208070076041c182c1c1135100e2070200d0380e4103004100c4048200200c55005d14181c60700d402c0d642011505040f51011141c1c076052580728036900400d440503003a485200703c6020034074018016003049440e5551141512041c14003114648a0041d10b460101c004210210b0354180d03235980c41d01c150400c020003420207125404003800030008802154016240c9040300740c4d560014250030003661515040c01002480280900c103648012450009510f1920105980c1628002c100c198510b80350305e2840700480f9000d8a920030a80510100340c04001c000e0b82c0a0880740340154090008105203800c014550761004225610554044c04111500e0300c890300c481001542c4504642d80c82000150256210302036403c0c1011340713a08005200c420040d011a000340102c005031400d101841044030583d04a010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 290888588 1250 290887338 290887369
    0xa0c0e0d020f091f09060321082a03070c02190e0604050a060302030a0302030a080612030702090408040510050403050610061b0c1703070201080c1e130f0807030b06 72
    0x3124041406141507001d858226030701c8200e0350456a261116401e40c0d43c0303994080c02c11030346d480004000380300f0082a05408041c20510344101441840c1016020075405014003206c2240d9281d40e8100320764114070312001c10b0b8038000e226141e252441c801401440070380b10403030040159220003001002c1021a0f1401d40b58103190010441e41d0341d02c10310004110041080300459200c00000003d030301c042c0326203040c5030300a0303000c2e5075500345005003c1d21a01014140a00683c0301a085180790007020050307500090b412074640a058559007402a0a8090741d0005544500d000310440c00e12038004000b80100d911807000d81c1c855a4403110b0340c043e011203d04c41e400104041c80390020b0a0221072039819582485031420071021034864481412041e0b02c8410300c02d49910000b4848159a0402034a03540040014070700ca01c1c24014000e00b618500040c1e03100c1070100c0010407501350070b180d118240300103002d82c5411110f51a0360795a603c0c0c0d03590030381e1005541150090707011404500705010001d45064 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 290889838 1250 290888588 290888599
    0x1e090203090d03090206040306181e0b040f05010e16090509030a0c1b090c110609060114010c03090b030901020a0f0905100509010201091a060a060302071a04030c0503030a0c0e0d02 79
    0x8902c050250050842c19504a0380842c0401c40030000a907107200c2c160444450700c118140341816442c0070740004688003403462242450040140c0042c00d2001901c3c1d01680c000c07002200741c1d21030300d00240540078410007a54980200210502c50f9040400c240040350368000003803146856803940c1d40e031284104200c1c40c00055810000f0004600c0f080d6250802c2c2548000c2c81d0314955403004110102c81e000c25a4200141c07007030502210250003088080d8001c07544801030111549801029a00309a000c0040d90600281075540350a160180800343d00901e81a03001603030324a0b000781d0b028000d50090303030a0408542c0b5080c4840c0c0683c4209080e20076640054412091804d0710703182690b0517040074003d141190340304c03400400000c1711034075604140a456288280603043c20070070440100780d145c0004007003510501c600c0004c25140c1c44540ca800415100e03101d441d0711103040c211859416010701801c0c6100000c280808400140e0111031200450303076450600d02d42e00c4082005074000000040d40c40f8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 290891088 1250 290889838 290889853
    0xd020a03020f0307090c020601140907021e0a020901080c1f170a0e011a0301110909010e090106121109061804060b0103151e0f03050d03020304080904061e09020309 72
    0x40c10300d02e4602060040003000c0350300c0c0d6542d0b004420309843e02d10f001c001c01a00000300401400f08801082e8000300c004030390300d110603c0d0201000b5550556207401260a03400c07074000100200040c0000d020b001d4020300081c1c0c056841e43c030861ba8070094261180d014000c00084104a10074444182403400d0329581e84110059003d8444014030700042c0000c0f01503903136a5820306400324244650f0540c0d03084080c18929134419441050708680111400301700c1c0071000c1002040c00d81e1624451410b6400081d44042591158920b590042c0074903005222010b11420007401031042001608400744402c0325002031980c1c0d4141400700c50401e0031690701045102d48040390000d1029000021202418580041c40d24800600c20303c048803141e1014440e00304100c0c00c0c030740c565814401035014020105120300140c0c6507540f03080d0b440d4406503040e000c241d40800484c00300541c081c1190707035107140100180151603d80f49041c030704a06100103041d510b0b1800c4000600a1003078000d0728882c20050b00502590f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 290892338 1250 290891088 290891093
    0x8010506031b0418030e0a08010b01050d1d0d090305061015030203090c03061801051003031e0e0a0b0418090c1e030c030602041703070f03031a09010e070e0d020a03 72
    0xd9810305140b80f0360007a1140e038200004044a40450101d40c043d0f9120074441a181040c0495508135812030042641005903541299812000f19881c041001c2800188550140300107951004600e14002a900441318a5803c0c250701c0341004056034042c1042d5242170700c0311400c040d0441414400c61549103000102010181d000b41d0103958841c40c030301c040e02e50b204043d200003410704200710f601c010044000d81e0361803c014400d1065560000c44005128843d13800c6450141400c40c5e0310030361480501545000c0711302c5600c44e4000080c1d004001d40810701440c0c580e4504030300b507002344c0500c401d008100580c1140702c0d40e450040100d80f50b001141440100d0500144101c204540924202c0087d11030400000003900c00400000a40c080c4c940146c44500349001c2c2100982042c1c01d00131161f00070b114540100d840303c0c084220403541810001a881d841c401400024520070b00070700e5206950500018078040003803400352203514260740e5400c034003030b01d44100604c092030524040c0d0003440d80301c6c3c10b000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 290893588 1250 290892338 290892373
    0xa090b09010806060706140103050d0f021506150f130302040f18200603090f06060d05070e06010306080d0c03140708030c09010302090603010f0303020d08013f0c0509010801050603 79
    0x225001b8a00850002c00740c0c1074148281c07a081c1c0c02101d00b079101c4142c07801d4850f4040911690110071748041c0030a050b19000649500d1030280009104102143c1140c103003488240840e0002024802c203d6210b00700c06401e452141c3c114030050303005600707144001140c0d800300d00c1079813142c00202141c1c00362a52240c550100c0403c82030000c0300c01402c443c00b5043c2ca85c2e24a005540700ba05100c00038909081c0600134a0304011001e01218040c0c0050150f03040050340c04902d81301900c03801c0e240c0710034990f1070600481c083e2500d9404038099010307401040c40b511398441300c2400064040c1d01d030903440b80b2008002e5495440b6546010f0000c550501c00314100580c0c5030014200558140b50160400d013400c00020f0080d40700780d00040f08141c007140100f08164060048245504040c01e16003541d6242052112203c9022001d2031030b1051112804c200140c0030215500107010080100d20304072410385425045510316001d11480b03035942c9070000030040e0050145920170342000e00500000e404000100d41d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 290894838 1250 290893588 290893597
    0x507110a06150f0f0503011a060d02280810050a06090b0d0917031e070804060905071503060618030f1203110f030a0e0606011d01090b0f0a090b0901080606 68
    0xc0b00850303a60b00008006030000315a1000e407180782074444803149840c04042c21510071601d98500c0304010a41302c049541c9000c142e0300229032030b240260345c0e0380041e03080008030362007241c0101c1c802103c0f603551902e0540c0224110300c20201d42d10440c06036622042000783c884a1807240c1000583c00d02410f000030b100d18406410000e40c11000815000700701c1ea0303138148007460a40d212030b0251003c000c024840d0a00038412039440300c85940d00c0348170f00b082070b0300400c04400100007a01c2e103070300c0d080c064041103070410034503000b4001000b0400e036002c40000c00030040c01e402e00c580030009140011203080b540317010070000304032507101c00e00c61004515981c03854804580341c0488c00c2403640e02c180140a40c40340c1d034014000050840c0703c2c3c039501d1a10781c0c040e034101d49100b106a140c80c0d103c1010421240d0708417a04030400110b040c0c1e500741460030003004942c25040c40d00702c1e0007801004924844900c0741c0304003030100103155880e884065a10303008804170600580780c605000412001c003007002401c00bc0000c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 290896088 1250 290894838 290894861
    0x20c0304080703110913020901090b030a0615151b0308070513030f02180906010302060d0209060d06032a0b0f04080a0b0a0f060b03010306050c160b04060507110a06 72
    0x990909984000c05400e21000340d0041e034142c0e1050100c500700c0d00d814240185d100c3c1c074524041c1c1c003588458020408d0000140222403079990f8030220165566020019890034030351003002031042c0d010f00756076a5240811482000c01d4614117550300340484e8050940ea1107070400c1e00e01d1600390b80301e80e51803c440e0b640c4041c24444c14001c2c20490102e2a0342e0407808600550300074800410512600c0c030502c541585109207003c80d0410a100344081c0e51404115541140d40495401d40c80c2e04003803030060300920413a074010354030000000c0c5440802030310f5048507003102c1c0540201141d2501e205c05040d4517407800380110244980c5d901040c0000c0341c0600140040b81403541080d41440d445080703d500d015808003040e60300380c84c614104504400c05000389440c404403808203003c90380c0b50450301600390106002c0240a1505c400001716a064000141d50401a02070344040c008400380c10100700001065405403580b5090000007400c850080d10f1405c0c0a171071300e0b00100034100454456800078003d0b0500f0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 290897338 1250 290896088 290896093
    0x30a090210030e1506131113031505070c0b07030504030e0909011b030b011b02060f0a0c050d03230a090b07020102090117060a0608150312070b10080709020c 69
    0x4010260311550020318420340301d91400280c0c2042c2000c03840c989140c86507400d504030714000030002c079500c6001d90f15814491441022030040c034426904800c90040d140b0050a00481400000070b122820042c000c5d88150540c00304450b0b00c0301d1800303da0f261010740d005098140c0c0f078800315880c0d030b01c240d0150f079000d03000340f50509a10908800140032100c4c1036031003000c035a4491f05040c41116480d018020742d900c0b2401d08010144203800080c0290003c803240e02c0c0b40040707811010080d5200c8030102e80c42d60b5a110411503075180380190142c80000d40340740c140c5c0e03544100c5400010803402131080440711141790020300001c01c025041141d0840000740b00c111000c0e01d450300c1500140605c0c0c04a4041c882640000d45c841c000c400c00140300408641011280821078400c0c08090f46500000100f40c0d40245050486030741c448005041015064403c503815209201d2942c18403c0d03600081d1420794415015000b6986581000c1d41035003620b4003403840c258011200c1008048040e500900c0400966411b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 290898588 1250 290897338 290897351
    0x2040b03220605040f020132091504060203030f0106110606040c050c01061724060f0607051618020702031c09050901080706091d0105060715181101170c030a 69
    0xb00c0405490054070203c81464641000d6001c540e0011444910425917485d60940c0d001c1755200d207000345500044e580c0e0303401e01c0054410f0680d118000301242c1e00c00c1c940754440d45c4942c0c0d40781c0203503643d1041391030208400320000085085481380b2031150354684e8420042600351101001c01006041c01c1481c00240201000803002060083c0550001800c04502e29440b1108200807142400c0020040c1c0403540400540300d40300030040c91600d0303001101601d28214003514180421003074818800f018056114100c211070701c104400064a0540382c165400c0800a045603100c40182d019100009502d5004801d058031f11102e810410f8071072400c00c1c900000041e41d034001181351107500784c0241e4140c3c0c001c030900b0321800e81c011404274020650070703101140d00d5440595a181050040c02102e21950001034041e0074406101c101c00f02a94034120108514510010a1071121903456800c179000a071103150101c00758040c0e070a88440802502c09020599102c035000c0c80c460344020070881c56a0360340e00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 290899838 1250 290898588 290898593
    0x3100e010f0e0a0212090d030501090c051e04030f11030d14090d061b030902031c090b090a0b0301060c03020c01020304060c030c17030103050a0b0f0121140d02070f080102040b0322 79
    0x7074009003d0300b00d60b400342c21f2401e9042d0f00242503480c160041040b150402c494000300c0c3c0d0740b000031100401f0314138120591785088220b00c18280d104590024104aa0700742843c0b050117108400712540782402ca0842d003041044a006a8150000400c140030b90304062018820178101a140701c040b1610542d030000c0d0705687d5250000880b220342820000091307561945d42e003103040800222507640e0721640e424130f5120203058000d010f031034240a2407941d45030100702001355844010f80403000e8200c3e00941526036844550041c81d00078001002d600622585602803800d50001c8200c2d0292509581c0780c000107456518199051001013804440c0c29140701a0600c240c1091405140a94451030150000c1c40990810710f500c48000761011208800003001041640c81d0b00c140401010059801c1000301455401c01d21408040c3d19030821480c005e5145091441c2d6000c1000d9045d40c05a6040b111202e81f00c2c82e43d02d00300c1c043c900030404400c1d8100003003000c031407000a00d0721180d6000050950300a003e603 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 290901088 1250 290899838 290899867
    0xa081009021803010b0a0f12030509030703030f0e0904150905120304030504050112020a020613020d06060f061d030304090e0f1501090513031e2303100e010f0e0a02 72
    0x3502c02030b002e4080b25008645401c1c040e03403e010000311241c41d42e55007000c62603503203454184640010004d1a1030600700301030080e0b060f03070040040141683d0070ba0703640e400c0c0501190103008000000598100d0000745501d041003035540215085000d50340d046200036200c0005006801c0700b51500e2117640034446807000104000e5204a200e82e441a0b1958640b0001414401d0035400340400c00780140b2078080710030781c0004c250b035114103454500d103214841030001c03c410018405015001a04100d8042840c1c080160b519080701d500b5070f5040e81d5010b258405119441d0f0050185a05410400c0f04101c04840ba4118801d1400100141c983c3c01201241051420b14000400d020556612004008a07856442180d60100702c0201d81a402c4e40941d4000b08010f1240401a4040176034440900d12248910007125030107a0b44019600b0400780d5103070b8080203800403280c0b210300004444020070f040910f1444541204c0b0300031046040300b401c1203006003044400400c44203440790b003404015859000c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 290902338 1250 290901088 290901097
    0xc0201271502160b0f0304030c0614060f0402040e010b0f041d010f0501030908030a110d0e0c0319032309040204031104050f0c04030206030a09020603070f110d050a08100902 76
    0x4840381840700303a2245000c0d080807800005603100303d29503038081041c1c0160400301d507520200007001075901e82e114a410380750080340400c083c1c00d11f0300e031070080344070f49910392401400f45030b007100e12600030100002004240e22841c0640122034020350300402c0300c2d09450001d4200d103034110603180e04064480800c0203511881c01030341094480c444004200782c0310002c2610001d040e081c41c080c0a40a4241c48101142c40083c011110302aa03525800140700c1905040c0e0b000101c0c500c04c02c0c000c42d00300040d030640e20384004121520074000c06c2c02d42c0c3d0203981c041214000346a4140c6604001100205620b07000c0d10241c01c0383d0710419004c10481c83c1c107958500c000c2016620501d01041c020340440d06200803110000c00c20b582c0c8a51901c18008142072a40949044030341c12181e941d92542c0c0c02c18000007500c0c410320002d401107030200c1803040c074940188006076040b84070350351105d0b42c40c000d030062940d900d6042441400310b03808000040050384140300c000e6000c0303504190006184d550b000410101da00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 290903588 1250 290902338 290902349
    0xc0f070507060f080412180305030f041a03011d180601060c062f0a0201060803040608010e0c030106050a03020a021905010e0c0604140d0f06050a0b0a05100c020127 72
    0x201c07014440e01d50401c040d480010600e1410344000d29081da11301613140384030380c1d00740280102c07440c90700219030000028001540d400f20036070303445d20700c030790700f05007541e082400f0311a01103d4490315a40356103044c0060340d0486210b4026410604e000440002d84c059010348800c179990000c1c540042c140c40c0800c450360080c091943c070005e60b1002c606004084414030309401c0040c1c940190460459048005281160840790703204542e01d1280c84030590040074039074401481804040703800500b0079003046225048800d080840e00c0995900e004008261200f400780b0004601c003071010089051281d405032032040d056004940c101c1c4298036600800480480044a8603912009a03040e006000c0c00145440001501c6540c1410f0030024035012000c001914035004e2000c0d40c401c00284404405a40c0405030031030410492801c00e081d0700d101920207900e00e00c6c0079040c032132000a06401c0c00038480001c0c1e0b9441d80c42012800c0c16500440c0c0d0a2910740120403ea2102e0070703403d0400224200b000300405 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 290904838 1250 290903588 290903593
    0x15150d02150a35090a0c050105090406030506010801020307020d0f0c0b0604020903030304050c13090206040905090102220f0b25061d0703021e060304060f02041d0a0f0b13050c0f0705 80
    0x40d840d01c40f054144002402158240c224400440000344600d05490654809081c990b0300e60502e8804030b4001d020590000e0001e01c00d40000081249040d4011401542141d007030340d40340e10310b107802984c00c40071070121080080c150803540c0c00030521f880f0303400c1e81100c3c00500c054900200000068a140c000740c5050318103803c001459a8103141c8041080c260380304a01d0240031007c41500014a540554401d600e0304540310800a00c40e81c90a5044501881c403d00411000e905504801c41c1011130328010315040280c081004180c034100d000a503031511071900201800c401c140c002c00003900361645021141a61540f42954501000402d202e0802c00500000c107451859401000340f042d191003c0b183c03046000c84402c05050300d40c1c10849621075048540441d149140c030f19480001c0c03081e580100b0b0780d01000c0102c036100390050300b03910707001d160a5581400b2100801e082d100440380550113441e401001500341544544254001d2540080305590150905200b8801c101c07256020300700c103e5964 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 290906088 1250 290904838 290904917
    0x20d050303181903030506120703080d05090102032e0f060e04050c0705030906300405010e0c010906030b0105160b0610020a02030601140f0315150d02150a 68
    0x200310301803031141140010b800820b0100e0114801084426910300050201a100c50004940307071905030211080da1030900c1283c0c030b07845c3d80b414040c1c095040f000382200040e06213408035014182c14000d5038020700884075200c4d015914283c1c14100003080641e1007241110941000406011526502c0010006a11801c05103000d075020042150802130400180c00024801e00000c100008140c44441c203081d02c195581d400311251168140d4440240468406000c2c608405501c3c54280342ca805140700320001d01414401403001601e80d00350281c59030000d4120310301081310912907003165940a1040c141646801ca201c010305400040a140980d1307202007141c14403040b81404107443c2c85105c02d51019010041c2241d0000343c0300c540601c1030143d03010700c84140421a81e546c2500d034541c41070060480d1044060340c0c0265015100c1241c9040c0400f140051140c464100b12007040c0e42d156004200281440302c503034880e50a60000f107817903404c00c220400e800c2c0d0360041c0070044000d48115401481d000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 290907338 1250 290906088 290906101
    0x6060a110f060114041e180618021e030a031d0406121406011a0708041508040c05010e1f21090b010504061503050402040f06121a040c0b0a0c020d050303 67
    0x20808113258a5010740c0ca0200a40290741482100406130307441000c0202d0099011804018040d40c009405404645881c0380e4103080074000e80300b000414030a03508010b0900300d00e0380041114a05d44052034143e000041000c00081c8030700c66600c0051084040300c03010020040200b000c50b070040c0c12046144102003d40710074002c40307009240c02c00e46560300611880d0306280100361100040803603020304640108071441040327940815140903001254a0805451220700001c00340d0344251410f0703500000d440801b00700ca52207045400d501c560b000d0030007075040c2006d004140c40d0300320a9040c03008110800f034819800200281d2020701000704840007244410032030500c0c24a130841a4000c1d031080d45030180400c400190f14030101c1506100b03040000c0c3c82d0303031640046009003450705840c42c041490100c02046500320440ea00d078800c1d004a03c4a000e11100c2c9050344400e08043e00d0180c05d032811480304010580c1131a005240200552a04010000041d8003151400303600600c11261030700040b080044 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 290908588 1250 290907338 290907359
    0x2031e0301050d06020f04030b0a02090a080c0d031b02060715060915090903140c10061a040e100815090c04090206180105070b0f01030308070206090606060a110f0601 73
    0x2004126146898a035516041c0011641d9214480040803140c0205000782080c544000382d800554006501086e41e24188007018000c1d4044280c06208008400740400d000100148611703e120016004500e14101524203848082074090600c0c0210a00000c480040e103400300030b090320901c03543c1c6485903124203040d5141940c1d016040078402a28100c0c0b42071244104601080032140702c9500050b041c0300c6820200c075250110400712003807040c005110180c0540005600c101e551308040104001030702c1c0c0142514a40e02141c882969210030300c4107014180d05112143e8200030f0715202d80051942d90107810b410510340300c400a00003c180010042c10000500c20000d82184c1100c08000b806443c0d4009030143c06103039000c9075200058100e04519900450450b81426004141c0504602d0002c54401440c0003d02085001039101000305204c64000240c4c0d0f4001c4235604080c12040e56080140000e42e0814000b6204014002ca120384e5801070a100e10b41e4000000302c0079000719810080c0602 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 290909838 1250 290908588 290908627
    0xc030714030f060402030a080a1e050406110a0b0109151a09010f08070f0e0105071410140c040504050417030a0605010206090a031d010c0506280b010e0f12010c0203 72
    0x10b040c1e402c07038400c02005070380c0400c1d00320130309a210035401d450307004028044900c1944808881168134441010040154101021304103d40381c0c1d58a243c0d1803041c0c011107036100d910b080d00041a0655400c0180b0683e419900b01c2c4601c001d441e240a07070032540d188031290b0319945501c1a420a0b20b4002255401540d201000c0c42d001c06803824960607500b00454010312150303959101500304843d0001c0c240c2c031a03228104070740c0d80d66080150800d1001205181680322036020b40d50164261600911060038080004040e1240549c90483c508240c034203003c0c44050600100304403590318001d0f00681d58605000065800344803600030000c0d4450078003002a10b881d4002c0e0580c000c60740005031000000380c0c0001450140104047e409004494040050300c1c00601244014068001d003c20051002e1441d50300d40807a044200008031354401c01d410340030441d024211910300103281c04030000d0b0141031513040701c014000007403e01031042800013001c0e42103c1d08034019000503000001c16405880c0490101d0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 290911088 1250 290909838 290909863
    0x30204110705250b0a080f06120703060e0102040e0a05040309050402180409210f120b09070c0f050f07050102060f070c0f0602071505010503010e070303020c01030209030c03071403 79
    0x441c41c0034195100c0560b203c46842d550903552202504010f1100700b2161500d004001c46101962165131150018000030700c11900340c4d0000aa1000180083c541800da8281c2c001b00d4070040c04400c0c2c10f5455400103000c078214518201c0d03400700400035003010030744c001501c5294982d000061504003460010140340c8550f20151041d40103200c40b41690880c00c1c01212000d01c2107c0003c5c040d1014030305003800c00340907000641d00c0074601050300e031203540013000c121441116558080f440c04521061408a1704d900c0c5826402030314401c0080c4a440c020004d20b07203a14003400303010000030b00342c9d030341c003407801080040248454008842c100b00c5541c04110303d039046100320716010041d01d00a0001050b5101c101c90250009105001c1e080503c00d0790313411100640d8100980541e0b9400d05c44088000e09004c1c03003240d000750f00e0640f400941c0c50003c81d0500541c1d80c1603001d4610010300e04011000303500841e003220342c54044c0c1b40e10340300d082c1d504100c4034004046456101d400c42c1c082034100342c00c008185c48003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 290912338 1250 290911088 290911121
    0xc16030b07031104050f2209120c0305031b1e34022403011409010e041a0c0904050103050604030e03030a14071104090f02040509010e0c0609030c0603040c030204 71
    0x41803950043d410130769054440c2600c007410803680e41070002c0c0011a0179010304240f140409103504225006800074807900303006500088420800040494001d181400c011300001c074140081640e1001e01075002e0707004801e20083c1801d1000c200381c08980407850f40e02d029207551b40080c0c0c400b001d408440e10100b03141b8030b0740000d10144030460560361030402600c20081c403038070070041c5103450178030002e5031580c0000d400300f07503075850350b0310307041410408412100c2c00c501c15602c420000480d060082c1e4030b40c1c8030b1688060f031030300e5240b85110921000003002d410200503031130500103041e0369216407040e240214043c60040003107080c1400c002e0800b49075084498081c7d00104148170b01c0303e800500101e0f2041e869801c1950751090307414094001f81707806110581c803a050200c8842400181c91030042d125000315070130041500ea2130b07440c034201c500c0c112044005401c21281d415151414074040c10203458090159032141d40410002110340d80110b40407079a0340d650708014015070400c0e12450f1020010000da = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 290913588 1250 290912338 290912351
    0xb0a06030c05040c170c030f0f071b020f03010f140c040e0115030b04090602070209060303180f0607051218090601091202190603140a060b030f0c0c16030b0703 70
    0xc4041e4194500e0040030f0282c2d45943d40400b00b5849041684541c10035400912610b0404400310b0030103038000ea5810054a000310003044000c84102030003406500c254480b000000c44042c01310707801010320f41d4141d074081030514501040d604e0a000300d0303400005020f0006660400c9541c03500032014040c03c81ca4000070f0070304c02400b5100e03c0d060b000e41901d0440c545209844100d000880103803200802c001d40060515041000b00040343e006010064421114070109d5605c200505580303019600d4006039560a1000c001d5050a2017503841000c0c8401914040c030b4030307866441e0756180450500168200c2c00c070004680304c100303c162800c42c26000c0101c0c1d49220500f00000002c2080300036014640542c5e90003880001155030f0800e0900302d4104045040b180f0301d94441000d002002400c80c840e2550382d5003800502250720f180326500a03941d07101d0002c3e04507110050840c0c00a10b00400c20074110340200200301580100b044400540485410911102c0e4214030b07080f4024000a4005c1050504014 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 290914838 1250 290913588 290913593
    0x612010b060a2a0201200304051f030b01390b070906020610030b0711030d050f0106090e041a040212300903060a11092106010b0304031407020d1b030b0a0603 69
    0x5110003003121b1300c20410f201c2010381c4000c55045104a90115070b02200c81d0900c0403250064a48941603410261002c200d03807030510005441403400d00000201544240444a80b1901c00818218841c0c50580d2049000c0702c55a41d20041020142e1710440803c81d608000c03c40583d0400049a000083d07034001d010062a540d200301a044e400b8100c1401d01125500201680c1030170015102c105120543c01e10150500d400481e07200c42c4203000e15000216207180100e50500e5100c40716008681c0458007130602e103180400200351141c0508205d030f0110414550704006042040301f141f6050490f01450048911a401401c1004800010301c1030400280f102c50180d9801080256005807d1140415021141d0702c40c0f020701d100c1e15803100c2d4001140300640103e04039140301801d0318400740301152106d90329000d401002d40411071b0001e0000d1128a1404151503482c4003404140d4406002e00d184003900750b4a02c0c0c2c0140042850303c0c091921001e0030028000c00d0412540c2007424001c0c1080103034110b4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 290916088 1250 290914838 290914847
    0xf15020303041211060f0601020c0307030b0a0506060f040b1c1803080619060503010503010c0c080703050c01090c09090501050f07021510080106080f120307080612010b060a2a0201 79
    0x400c090550564000b28280303c60089555201d10980b030070903640c0b18600090f00071a003510a458183c0140700c0c0142100e01801c5c0000c58206036500443c030314800e0b80e161310921024000c001d0415810400511000310724a00c024060000380c11044c640644803000d4114074101466001041c2c0b19072420f280305201c4105288000911a5800d071803c500183e654401242804024589200c0c2c091002940003d00300c5c0c2c0800a10b05a500482c0240900d00706d0307882c102c89400741e680300540380301c3c030030000400000d000310010202c5d03840c2c560012076043d200d40c443e0450f09c0007542c400b0700c650340c85080d0041005820b21409034049484030300c2040e42c0c00c155000035940c402010204600c015890040740300b03c0d000151620007024818001d001854507160a586c40b0050500d58502c10301c901600c0100070102481907074030074055650340d51965a5070b1002c000300c42917003190085640d5608d0004208645604004000c01542500c0c0c08007243c040700200c040c1c00b41c2c4002c42030881c0400320b0f03803040140ea11 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 290917338 1250 290916088 290916091
    0x120b070503132913051911060a180f060e120c061c09050d0921170702041d0d080c120915010609170105060a030311011d01060f15020303 60
    0x4400011078058280c03448960081c0c3e201803050488514008203c030440e20352801200b1240b0882c00c3d0b9045118001050310b244031140c00081c82c840030070303810342000d042c242c0181041e840c692404030f0400c0c483c145107820b80070040c2c110b412241d0b907041e02845100d810500310310300d811003a00d00001c905040c1c8601d43e00d880b1180001d62289100281003010305555850000706038102e81d0080054041a10b860748d030b21000350b4180c0307001c101c1c0400300048800c0310248082d114100318400d400718011035526460010914071060300c1d0410b09014003409601c45229003d45013003c1e2025103502c140c00d02ca1207183c0fa00e604100c074100600041000036040202c01601c0214002481c09601e6441c0c0182070f40c248144c0c2e40721802494070040000610a92241441d000c0307541c030459049002945c01c4900b42a1101182d90903044032140c5c50410010b84500702c490180c100f4480000380209844a028800c01c403000400c0c1041c0c1c5d1144000c1c0800f9030f00c064a18014642d64540c2c1c030755046c200e42d019480e40030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 290918588 1250 290917338 290917343
    0x5040506100b120105010f110f0c030105070504061407140312040c08011107150204180f060f060c020909010b13060e100302181e1602011b0507110415120b07050313 72
    0x500c0020007480e134080c40099502c1c00d23201084c0c854a10314030140d19521a01c80302080d200350f003031401080c482030090048a06039805079441c80c24000d483d15001141c4e03802540d003100c40125403140407407444c0341030001c0d21640300b43d1440c2188500741402c0c80807241030030303401c400c0360350b450b21042d4450744030400211021982c1c04264200c500c1c2d02003c5902c020b0280e07501890400c0c94108401c4207942550b4007200054901841c1000103d849042c1403d036860b40d40682004119080010f101502d01603420561004c01d01c00003048828000f03022801c03500181051301d041c00e4440d0018489403072120452030340f2028445400041c2c501d190000fa075912a5a44046490038640f008205101c851120b4041030041503070403045c030342c208203030441c01c0e0386450903860b40194688020241d80041c808220090309460b0707511a401c19009031184130350844807071250782e4406d685203048244c03a814983d0007401420f03000d55041d8000054200a0502003001300201e0400008104202c1d0701c202d00c0d01004803598 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 290919838 1250 290918588 290918597
    0x5090d09080c01110109080f03010e0112020d1515060e0a1a0403020d06060b070809190501020c01050c01060509090706080f01241b080c0c0102030c070504050403090905040506100b12010501 83
    0x201d4012032070b80108000c60000c7c1c44103c000400d410711052050042d030480d8a14564024a6a07840000c02c03031041400900030b60100c40d203400e00c1d005c180c081e209002500a581c400250070fa8031002506444540e50303001002040c11441c14032201c0ca4810010801840d003e145e403d00d008250706800c5151241d400024800c000e000041401d11415900500142000203141e9a441c0b042d8246601c1b2500110000c9104250b01082d42d040c90348a91070071411114181c006011840b5034000660f02c582107038400904035075950600140540d14901c130f190107400c0000140c00d2560900e5401444030000404040e03103620403100400940351980e01c6280115100c01310110929081c480032600305024414441e00c01c0d100c00000403c1c0411600100790030b420300012141540c41610059031a4003d044d0b039490250041141000581403680110f0792240c030078904010341a480c1e040308401c483c020780301501e5651241c400c00060030643c0700898087d0078840103090420143c1c894440111005008550400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 290921088 1250 290919838 290919857
    0x12010906061202091c3e010c2d0b010b030405010605152209050a0606021b01200309060c0102090a1d160210020705210415050a0c02100305090d09080c01 67
    0x4003012174500c0c146860014881480d03141100800320103007103240c1940c0d402d030803c1b4490541d13018152200006a000814640409001700c1501504061003192103000210409040000e094503e5003406000c0c1c00540d551a82001c0c20200e00311800703a04003c0c0039050240c00001210981d10035108152680b140f400030f25555440c444045001d00c1d4050341c1c05030708000c28480485420b8110f030094a0055085450055403243d042c40803050007605540410381040b08408003020740136040040300004003c0b20315040141d00440d40b00c0e8000002080d080c0d41c00b2413120f245140c102c0c40b010060088402104801d010360840504491002d05100e80603500c001c2c44422090003071241408408201000315200d8070f4034203090351504a400f44000711a0001540c00d80f45610307260075901a0f50702c4100c04c200c458074241043d601c0e80d0208040c681484504088c1c80700590300e840703511060420a82d00414039003071180070035260592074003030401800790100c401d1000352000580c41088503424602403410 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 290922338 1250 290921088 290921093
    0xc0504060b12060d14030304031710120c0f0e010905010602030406080601030e0703020a151407082205090a02180904021c080906030a0615030e070b0f12010906061202091c 75
    0x240d0940d400c4c000d00c4000007906010240b000400950703c00c1e4000d07150318a00501e51a1440344096003280c51b4000c50f44081d40c00d2243c1202e29001d80c01c00d522600e50703090513640710b5170318041a804942c1701010b04841040103000c802214080c050052030702e40019030034582030030740103000301000403c660704050340d61070a401c4280003000350100441d00a4070b07441c415900d500d03190000c4a8150212804601942c1000c00115a408226041d40380c20600690810340d00300341c80444180d800001e0741070200e001b103012034203540b1000454000c0c0202100140d5447c02d40149030440420003003002c0c4503103108800c12015849000c00c0c0e0800c1d65803900b042140400620f00701005001c1d44c0369a980200c03021081091600e200d80c041c8041c0c80500c49000c0130101805c1c0c045082d0b4501d10034000c403503089920208103040405000d048180c801521301420300c40012010000f00a00341e001300501c1c1c1e160031041000940000300c10b0401002d02005610b00713000c907008104900c9006c20f9158003102150307900000d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 290923588 1250 290922338 290922349
    0x12050604020d021903080a030e0a050705060c030f0408070513090f120903080d0911030a0305040608100503030c100506010e09180109050d03060503070603020a0e0f01030e0a08070c0504060b1206 85
    0x4d10203a000744003182c1545900f840000c50b0410505200440c1ca000b018040100300000e03081217656100c030081c0281c1d1b09040a1041a0304a0040e90340e0074401441040035000c882c00203407003c1c2143d0002400e502d0702d8402041001c0c461545034a104070310f80b8070b2850106020482d1400e020790440a07071002d4a010050407194040c00e980043e16141011500d1861204250846882d160140d41c040710a003c42030201501c03003c1d2010000c0201d801000300b0003000c0d004400300d5074844420b510046d00e0f1559070011a0070356101c409150746a401c84008203a4056041c490550081e50a1a00003284651306010400421010b000e00d05607142031070389003105030f009400850f00703540c4c400c050b100260b02c440009070140015000b428400d0040d9500400d909101c0d20a03640034003295900c09070600c9503001031002c40000c03010500e04054032051846043c0740104201384049104d0602e10340d0314a0f040c14484803d41c040d40100c4e04c41c40c00c09034100700c0f2000e61801d8484407000c03c1d2a0744483c0e10741200042 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 290924838 1250 290923588 290923609
    0x30402040f02040b161b0b130902190c0303110d0504030f0509100509040b0a030f060b0102010b060403120e12030904052d1e070801170114150a09020c0705030712050604020d02 77
    0x2818025055000c103144d0034820150501d0281d88401d0300d001c582712000b05013a40100030b1000c0c505d004e01c1703040c1200c0d00e21482c0c0c1c0c0884940a410009284146001c9002e07a6910804581c22041d8036041404100b540c80030041030072061030310f0014241101000010351000c5480180000c0040105810381d041e41d5561002c8039101c4c008180ca1503883d03076860b103010740c84076018081c1caa0900d480c0051800c1d500601502042c000000c00051600d4155501c010751a803088001c4420000c0c1050700c5607594850105d46504e078003081c7e0007152110300903001c004c180c5000a01001404148960002ca00a5003020955903050b0b1400d41c9581d956803040900ca88006401d000780581000c002404100ea4100302418160740358138081402500c1c10108580c00e847c076115400b40340c9a8442d00140741d180c0210208040030400034014904555105040001d9812424038110503800404040215140400180005041c8121441103540c50354480b40d1702c45400420103409050384568503411036a440f420728 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 290926088 1250 290924838 290924873
    0xc2e0b31020a11060705070b06060f090d1506060e090c16050d21050411061c0608161e060302070f020907020a031202040806012c0c030402040f02040b16 67
    0x21901c442c001d0000400304644500c1a1410b4090000441c3d04203104000721102240c010080d03142036190401400740c668094058100d010800b4000b40455030781e20070340c1c070300840e02850031555041412541202116201c0e0301c44414001c01c0605a5000e07100c80ba505684843c68441d1a07845104c0303261034074001c1030b6800000f0103038020322800d140c4450300003410a014514001900481c40b00324411401240d8007501e014001c14a041c141001906e001c034000c0c103403507020710302494607049040c00d40400e441c165049284950004410044908000307c20407005044c05182c03c007141403907000c040200348150140400705074001446100780220710382d50503680e0b81e016201010b10310b0700720b074025150600da50313045000074030054140c40d140b1041d0007914192940c4401520702c40c0d00c0d260012840d043c050841d4a00c24080e107007829244902c80789400c0c41043d0800303035a9580d14040c41003008a5150304138101d98280705000c00e0001ca50074074151042e182c804e000030201d040190400440c0f40441f4441c8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 290927338 1250 290926088 290926091
    0x409020a061d0a0303021509100609060305010c030b0a03110303070c0303081b1801030b1306060903030e032107050114090f010f05040201050a050f0c2e0b31 69
    0x4516a104031584488aa0b1020044032941d000c420010f00300c0061001400617802941c5443c20340d40150090368011928008407400e00c1e01e0440e101054408580c020078806940b540108207020f42030047c26101384082c034041004c106104000307040410180405001403070b41e40300488094034108211650503401c07501d20015140c0d80e240041184030f04403440880344c6403c0003142003c0c400702d402e4400e1040890389060b900100240110000c01105034541e40c82004074401184642d85445110050042581e960031840d08505002d0310701d00303488034498081e6110341071a00d000b5030355100390251a200c0142c4aa60342c081410b09a015080800d0030700111415541030090398440083c0030f002d941c04c1d07540284100e241c0ca221200440303008860280c0441c0c400c2000c3e00d0781c1445000104180b94090448078100440802c0f602e182c45041c1109001d0f944100c05400460340d007003c02c100c0c251071040400d002e0220203201042045000c000a45c0d10074948034450507400c8a030700e500c10b54240d00e1510 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 290928588 1250 290927338 290927359
    0x3140c0910080f0703020a060e0f04060b0a0215090d110312150a08010203040b0105010c170a03020703030b030f0a060f0f0e030a0f09060f050906071203060806010f120b0402040902 79
    0xd0101c01080c41c1e2007450400e03c2045101e02a000c804120750040325001099540203520b800ca0a6a000145c59075141d84403480490900311552503204d81c80103000701784486a155600100041e1800d5190700d1600541d058801c204101c4001c0040d4904c0001d04601e00680c0030030501d0303501031071402807502c008007405c0004100540c3c0c00c80ca6901090301c801c125407020703440c0e640740313a030500f00d100a6401400c0408194011320980d4083d02e40c851034a880f07100c02481030350700c0360001d0034190401c0c1944400640c00140f0041419414060303000220002c402406c0381d250400f020a6548000210043c00c55441d1404503004c45044c7d8015840c0041500d018409030b0704600c0020345a80c890558840030a08803e403444080c1e201c1e00000040d901c260312100121580d070041510a03401c1104141e900c09010080440052001c0c0c1c581902c0100c1610046142d86c1458490b50410505800c0302c0b9007150742d040d040090b54010518201000d421064000c40c907141c3d400444d000e040d0174040a50007940c5001d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 290929838 1250 290928588 290928601
    0x241c0602191b0203071205190803060109050402090d060902010e0604061e030b010906050708041502030d060b0a0f080c0408060108030304110a030b060103020c0718020a110309090103140c09 83
    0x703005900e025501d8115690b0b12014500d0b914035000006074044d809540f040c0140b00a400041445a0141003200d00d00401c2000c000b10910b11503070100d85c6079001006100442d60030405030005040d080300c3c298100041000422642d860308100601f41d6611203d601043d0790107010075400c111400f0304110340d142d86a42015026030b402e00765008a01c0c8074002c010350002e129214246034402c0c16918100883d151a43c212681c1d04150000d84003254100000201421032048050787c0c3c01250300515220703401142e00c0b10480d01c4640c00701881c2c0303001708100300f0195130140d00308408000500b480107494641c1075190100303000b142c00501282c41070000100301640b00001451089110f20302c0c40902801c1c46007800001c60321448003d0244c00b568002c07030f00940c0250040c1c60055650b0381240c04d4996104800840500c40858500d415036000900080301503000e030280b130380b444904000318602480003001c1142e0410520001e42151002400c00c40090018402880207440013400c41000d401d084 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 290931088 1250 290929838 290929867
    0x6102106090e10060f0e1803070c0326030a020c03040518061e1804151b0327260406170703090201020615150409050a05241c0602 57
    0x300d040c0d101d58031440351000d481d91240d0140c0000d803494084154185072070300c1d0701c2900c020342c040d00a1054011f403101d15514050108040e0590134000c0b0400c50880d4070f5420000104146120703109500c8504c0891400c60701c0100080702c0e0030054007280169180d049420f03560850141d604280e5000f4192007040584988030003180780162001c80e568086941c0491049100507043d9a6044d0000c581d04081000d00446500d1507504c6030164907045140d20a40130498101d0307251441c0300903d00318000b40c0d90112545841104078202000b279521030310103e1017602c08010001d1450040240a10841031182d11414003440e03142581c00c13262068450781c4401d0042d0414034210602c08030103a441000854082c4640641042d068045c0c024140f0740d00d40405111050355070305042608101041d49440c0000403c03c0180010000d24500040504201c45000155907003d400580c07030300c2d40300d6680495044802d114020604044510054550881d0315407940e01103282000f0705414408182111407900e107 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 290932338 1250 290931088 290931101
    0x305060c0a0e06120105010e0d0503030a1407020f06060607060624030f020316081b0d0f060806070212130e040f050f12180f03060c070b09060610210609 67
    0x381d126401a401c124003404818020344c0c115884c60000140100080e5000c0c1e015040d2040f80909001000c61468030f0301d61841d4016100b1030314160391000c1c10f80480e20f00c00d084942000c014070107440c000201019650f90354402519581c0303d004c0001c2c040e001c00440d90700c14001040e030700c0109401480c110b0040e01c0b0b240da05c0490351012a040003001550050280700b100d10800b0f1034003034401e003107003288000ca40306003000340005a0080080c1c0b03070798090384080c8040c00c1c00744012500801d940d240007490b1300c00d44240e50711407840c80e03000d1802d00903051340204107a0b08480e0901d0209840d240c0801030328180205030b034003402c000c002c0f600600043c00303c0c481464407001c2c025400c8400e80411b81071020f9030b94164030a030311500c000600c807021500d981100c0711103050800800d1114404280c00000c3e052850607a8403181045001821404012401c5032080d405480103024102c1403414001081340700c00c0f00c901200c00c01684007480140d040c02ca1500200344028207104001071074581c0d50784c0c0001c106 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 290933588 1250 290932338 290932357
    0x7030c0807050603010b0301090c02101b09090c0e0108070315060e0909060106080a0f0603050106090203090f011103070c061b02060901150b0f07030207090e0123042006040305060c 79
    0x19504007040724204402202d0403106c20030b0015140d60710380350f080b00042c840e0081308400c47c001c1c8101e2140e034103c9030048100c0610003542c0b414020448040151000c00300ea4003010110342132610303110420340c000c0e603100307a01d04007030030440c1041d618010118028090b0104624160951000100c2c80c1d5902c0114005e0070001950702c0c0d501d03926106050382d0342d09024400d00c4000b91507507000800110180c1c00031420b1403900740d40824010b480c1d03a219800d4030305c29080001d4103940442042001c11040003000c001c0e01010000700105051101e110010f440000c20420500230492084810080b496015805010100c2146405080e101500a440b01030035140304406600300042401c1c03240100e00103c00b00c0d13150580540c0780c00241105038646810030709099055025081000820010601400d41b0b11642200002211b00c3c90b890132a0405902d011a054051040b008002c005030020111000f0b5680242c802c41100414000155862241d0780000300a8006c600a12807106d55442c094800c40c00c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 290934838 1250 290933588 290933593
    0x4090c020c030604110301090b09160f0b0304030332040b1602100c020f0d02030403020907050313020d050c10021b0111061f09020a0e101b170c07030c08 67
    0x20424804a035185241403106a15411400110300080c44119482c940c0c1c240c068000309160b0301d241c40e0b00741c5281045804806581200c1c00311102440028888006001001900c0505a04000c0d40c41e0350390100500040c181a910101c41c1300d115034241c0070700c10f0403400c10007030601c0c803040c0d40041054640584084900c16050001300c1c05144001c8141d615501c040c1c2c1c01040c801c0501e082c41d02c00b5140d0040442c00358001ca032050001e01e441882081c13401e201c190021a55145148144074000d50f00400c000c0801c081401405040740512040c074120580498088440b40782c5824010305240711600c40d2503100588040801000b03401142d08010103590342c1c1c10b4102404680300546044a6005c490400b981068000810010202280d2150000c803080c200c2e0010351a1003002c4200e84c0001807000c04a07110100d0362080b4035003503582081c10580e038545503a9034030080641c07140342c50305800000c1800b12840c00400f404490b1000795100703003080d80b017160115680d034140310614140602480e0b1850 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 290936088 1250 290934838 290934851
    0x3080a090509090c13320a0b0906010c0c05091f0807050306070f09030b041a0709061d010201020708040f170a020604050f0f100305061c12080613050a020409 69
    0x1d02d0b01ca80c0807441641c40b440645000280f903000c100301090000c14004035a5665601100504680328082042074118501d0b00741d94901d003210503403400001080003c10754140100d40700340313444110107150050400c0c00d10342856022854079544002040d0029904101d40320200b003503d208019581c0000004440303500c0b10742e61a040d6031601d5042d1030203840e030558007800c0460748142c4a8100b00465168a103400c8004984070303910614104e5003038400761843d0031001d401300001100b0064071900141e4504050074110706c2d04c0b1018108841e04000d034191303500c0014490fa03141c3d000390106d40003144c2c00803215035944d441c1e1f44d6004504440f409000b4440e41022100141c0d0a000506c2010640d0000c0c0030314101442c0c482000768040f8600c00568000c1004512070100b034460400c980e200b42581c1e2004640b81c5040014007120031180c583c40c0c1c0a00410100010218121401500b0001c0d95841d000d24566100000320740c8090b01c0303030605a101460001004200050b544c003400c140d624140051000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 290937338 1250 290936088 290936099
    0x708070e0102061302060f040801020711090a0b0306010911040b13090509030a1b0f050d0e01320d020714010519060302030d1211070c1502071805040f02060403080a09 73
    0x643c0d0048460720002140d040c840409850114040d254005204034803070b1402d911011020309980001c9002c940c0581c0b902c210301b0061501e20320b982e40c40840f03020100800d07694034000942c0d42d801072140c1c008140e44c43c042c1c04502007a94085802529070300307070010360703070311403a440c61002d1680b8bc4078605241e490180442c500340c2010040b0b0310400c0c04d9070340342030700d00ca84030041c04a0510765640840300000c00c1c0c64820001081480183c98440c003684a05550074945c00016002d03148859031820585440080d0300000b01d10007248050005100d0784e050784070700240348103030000e10840201a11a01c00300310301c0388009005405c4680308082c86076140d503040701465030003415101907000081d8503800c101d1428405501c10b410300b40e040141001d000c50481c040c144964415800303501c05640d152404001440540450795080380f820030b15100500d019494190380051f0700c505000302004040d140e801150034454003910002040360002c1c80b4030350303450f031b80e20f8988007541c003001010020130180c1000140 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 290938588 1250 290937338 290937343
    0xf031209030f0c0d060b13050c0d0c1b080903150f070e040203040c0b03090a081c0605030a1e0c030b01150f030c050412020d080f0a02060a0603260c01050708070e0102 73
    0x10f5086001d40002e085080d40d13038442010342800c01d80f01e6040124070f41c1100c400d8006000765409628800904c2d55a1550300100b0000c0c0d5600039401828003080d003400103e220404102e00e640550814035079070701d80c881c0b180001c2c200b00680e41080c0800c02d10105001142c02c1951110780220714039103455943c10381080c20b0000341c2c0411100940304110f1600c08020300c071041e100a5910039280c0082c2d882421042e40c0d44040c5401c24810445410100843d099051405200e80000750800301d00810006c0e501d41c0c1d814402d9640a02507040d101020130f843d400300450002c0210203107501040c042d03c50342c0c40f0804801d40121b654280c0d40054612040820703098081d125510326006107954841c900b5003040c0c2c92882250f0f00c0d02003242c00101540c180c40c0496006805049940300c1e074101d03965900d60782e0300001e14101000d440c4d50592440c00c0d4007040080c0000701e146040f0480c080b944000000041441d07611030061070701650055003070400300000f20f03138003152080c410040fa440750307080c114885004aa = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 290939838 1250 290938588 290938603
    0xc010801141309080915090a05010c2a090e0303040b250e010e0d05211c0f0209040e010902010809070608190207080c060a200a0e0f031209030f 63
    0x1e03000b9003000301101c0c9101d0550081080240a4021185480d0350708010400300c3e2041e00900301b4028000c01e80100d40c1c5456500580140340901e82250012490f172994542c0b02816000c0d4100321003e1425505500701662410b0b0040141031010403a0102101c3e5560b00ca5004440440d420408180010030140c0c266034030700c1d031142461100000c6100515001c0d907102605644541c14009454080c2207039541d4408603034045442507000e040d0400d000003408010784500c40b9803944d44a0700340700808040000e00c100c0d0302200740d899408100140000a018000e215121802d40c020b800c112103426941415044103030914402c1ea1034031030a50340c0d42e150580300d030703114020840040d07050740202d56415484c80e501142c000070031200629140301a0b480d486558005807450b03070030b0b403c903008000c0106d440c1e108030b032150813691402e80c0300c10548200a8020303214401034007052220005d141603068076070001943c42410060126040d4007401003141c0101e400c4a41d40502c03a22442290f10b000324008140c02 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 290941088 1250 290939838 290939879
    0x6040c0c0503070212121b0601050109030510180c0308030f01150c11030c09010e070f0c0c03030c061b030b030f01090506060d14031201090b010314010501050d0603080c0c010801 78
    0x10b60500d01c882e403c029100c8803a001c6030080384035500c0007241c0d240d03103a0b0091140e951910001c0450210860b206820141d0591005060003800801007012910108000340d10341b803404400113004040204417039150b001c00001805c00700c03120501008101c114002180261004208203c4c40c1c0e98549400c0c500151030900c990004400407859400900a00540004124000c003a074200d036900001081d44d0040907800360444400700028000d09580101e1030518044140c41d2910b00030399503842d4041200c01c41c3c40010101b00c000131a840a100180e8070090118400320140e84440e0b6103514028042d0520060031480b03801100c1001800842c144a00390049902a0103002940d640300200058440c0d29407065410210386800c60700503540c02d0000346405800e84605804550401c2450300c1100da81040e400c0c1494584540070507492446040107045510901c0c1c040e50341c100500c0030b074001d4000b07903200918105011400e040000d90110301007020003001c1e4ae80c1c90030b582e0f841c034455003e8008075912 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 290942338 1250 290941088 290941093
    0x70e040f09031d03071d01150903020a0b0306040b040906020a020c011107060f050c1c080c1c05060303160803040303150b03040201030911090906040302010e0c03060a0f0618020306040c0c05 83
    0x1400000c600c0d11450600c00440182030b612020380d1200d5001400da0010508111600a08010700c00e8407805035402248c0354051900c800791074195804111000c2d40e40c041d0001100f404400940960380c3e90304803040b14040608148040f4690740f406a000c0d400000354800980240c0c00c08803c554410140303500c4000b00d070801045170f01d00d044419281c0036152207400c010802c080207918444030003040004078041c08050b0480411003a914020180b50b405000305c40c07080c2042121000010000a002c00c5805034074030001060389992000070710b14411100210707035402910790102d081c0255074025602c030381d002c5d171024003107240e8095141c08000e03d42e010300e0304000024004140554840d1784031051043c8130385942004214050006006030300120750780d031140e0303000c08100000c040c1e0a002d02c851072074800004001400303500001036101e881c010501240c55649260820801b6900d821800040c0580e4600d8503004450b07542c600c000c1d5104071001d0b4001c5050415403006984664000041c19400034007 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 290943588 1250 290942338 290942357
    0xf06150f06280c02030c06130e090d0f1b0b07111f0506010203040b220f081e160302010c1a09030a140304020a05090907030204060b0703030f06060212031b03070e040f0903 75
    0x4000c11f60f00001d4102108408290b400704030061099200c601500c01d210082c0700c2140395240080c014100d44c0c02030b10401504400c0d8040c04400e9016400c0240d03801003c1c0c441568890b902101c4001e0a4070050116114150354220204040c041143c4c080c45080c906000d19035444c1b005a0f0303a4421840f81c004600d0040107041d40b01c082c503d04140c01c402400307509102035940c8401e083c50170b0b03234581c004043d81d03040728100d0202c110f0b004c8000d1600c0f825402c0900081311103101003440103c2c50b4440603042c002e4148144040255507484460059802e2162242606008646c15503a8020800c540c000c103040603022644c41c030484040d00e1059a008015880c20b81c1004103101c04000c0c01341441c100e51140000102c0143d80e40c0c050302000d003c5405184e900c0d001941001000d4480340801c061039103144c074400303100307282e07002c40d50f6609040c40c0c444440d6252600149985203181d82d0b0803440019002105100400e07900c50301043e8009070403101400046d1500341001e0407181403003001404a0700410 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 290944838 1250 290943588 290943613
    0x3030a0809010603170d0b150a0e040e0d0306051309051018020a081006050603040b1303180e01050915030c0111010e070306020d0e0f06150f06280c0203 67
    0x40c41554444684800490b40942d41d0341c032141644901255040300080c0456070401070300d031070b2181c8201902c080b218407803005128a072900b054070480c280303007081200d281002800d135260b0b600503690000c41141224012540540001c00600e490300900e8401c0042e801d403100202d100f80580c0d021613801a021b0012030358207400d8503004000e884d04002500d41036105c01805a5038607080d010050041d8406030001c00000d641c46c100315842500070610642d0240203102c04074189080307541e80240000d046a40e078481508040d60003403411407110350403200402d00421a0900f034001e150407620103071078054450b2900e1030341d5a22000741c40412500750b440608103410a40c4210660300d50b101c0b4200001075040c00240d030ba5410a40300780c0003541c41c690001042e0150b4801ca02c54084184032100240c2020380042c89155181d1b02c0180a0740c450900e40c1c654042e07540c1c0c44100c514540000101025541c072003109406190b03002c01c586220104070307059100741c1c03402e000ba4a0745406942c01805010000e0180 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 290946088 1250 290944838 290944847
    0x2060c031905060d0f060b0a06110712030912060608010b01030501150c021201020a020303061507050615060d06090c03060e1e37050702160b2d0909090a0203030a 71
    0x1e101c04d900c2480da40414010414103665510002c0c024072020a04040709414800f4050323055010008000c5e072181e04000010002c80c2040948500b80040091031106007003c40c3c89075000d400401801c00c8030300c1c3ca003003080003952004044420000081c825154071078010f50450308244a10f0728034442c281c800c0c91746188540c4408039403910003808281c450070b5070400399007240c2000030313001c01591001052081d1031900400d003404618519441915001c2d4a50f1001d40b00c042c050715003a180503510140a005548040a035a262861094208803041d80e50ba0140c0181000000150220746440740c0403030f403000b6100c009403248840783c1040c2003590074030120b19000c2c8802410781500700b00301134441c526058072002ea010040c02d4074481c600701d0340510f000d50381110000780001096500042d00e9654500b0b480c0007080440d2240480340707417580914844078203401500102d00b5500051006000c6c02c0440300d00c09060202410303150400c4940d10000c50582c2c41854200117507055200b80150389050340b1a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 290947338 1250 290946088 290946091
    0x10f030b07110102030108011d0d140c030409051003021309020108150402130e070f0f0804060b01020c18090d1d0f0a0e04030306061209020a030201050309070b071202060c031905 78
    0x40d00d00b100300c100d0032059440c00c90b0801e80200c0c1d5182d4440600201042c4010501c1600e20750400150076122402c010190000704410010b0342c0e8500301048042d9030704818025a001024140303010700c0245011003015411280ca404120b01c5071440e0464002c0f8404a4460517440c2030381078481039401c0e103400359000b0441da81e0114469106d07401b04020310403010030031040c00c002d00507503022800500704204050032051482d08a0410030001d10000d1035010b030310000c00e503001038128000240100424004038200185240c03665000506441a1a456081d50a06900c282c840701c2c03d507803500c0300c0404200e8080c0402c4e03c0c0c00c02c0d140c01100760b081d12450100c4400e48420402000c1c55005503441c0e80e01c140b4202c0884050303002c240e41c0d4074200b095070f410800b0b4403103118086404000d402903590009503104003d000c00b0f4100040403001404040007006140e007e00b46c03174000780f80ca8100e94034211442210540c0b4100060080a010660400c22401521302443c40440f1302840e0769110030741c81004100 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 290948588 1250 290947338 290947351
    0x90c08130f0803180a060501050f100806010810091803030e01020903031e16080702090112020102031c02040f03080403020411070b130203030403061b03060e06061b0705040e06150108010f030b 84
    0x24041e60300303c1c01510402c031000c01c5c90b101c1d14020925615180410212106002d152030086004002c041c0400350710409217035004c0d00900340129039495450380f04028480f10b4010000b407916000000c0b00c2c0e6400406242c542c01e00c240d400740001c0f604000386500741d01592082c16090340c070500174407041e420142010407110bc5000c12035810a144600d146c4000c460440301510010400030b0501c0c01d6041400f540d84c003501950103444035180665000039034034481ca409200c0c4011894440d554001c0b5070360104c900414030030000818031910781c01c1447c26603210f44412403140780341c40c409582c2c400c4507500b40c4c0c501603000030400b01c850fa56042500011480440100d900d0b0104200100028030144145510f40714409288a5980802c82c0083c1c02c4664640041c410103c0b00c10400c0103981da02c60888986035075001e08045901e041c81882c5103004420303001103620600308a00840010300004686109103403881804030300410502c010740d4000c00c203000d4245120240d0f5014000b0864822240b90002d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 290949838 1250 290948588 290948611
    0x21801050702120a03171006050301090b010905032409061611030d052409060310020703030608062a031e040305450a0509041506090c08130f0803 64
    0x81c072881c3d02401e01203080030880101e01c010216261021051941e16480b0982088804c003080c1040401303811804140302d079030561030701c0c0c6480c01d00a03481140107400800010b001c6404088804041a03140032300c01042600c82034105000800615000668a010b8100b40c0100d40d030380d2113846000c48040440b116100c00d284010031192504038994811240b0810346404003511090340d112080c801c5507500440d143c420901041401030300d0341c0c0443d40129501590000503681d03035061034194040c0a15600c1690306004500070000c41c825108003c0041c1e1828001c0003a05c441c140300e80c0b080a02060301d054100c40c000c4055040042070f6100000d0300140642002414001c080449d40c2c0f08441e04c4005685d84891241d8a0007411100301c0140c81c0c055240003074003210b8882c2c0b0007143c035500e03941c400e00780301d5010800810188035551818648800081c4000e21040b6260300000d805000d060031803a0005844100040140503a1010201c901d035100c1e24103001d92003035484038612500050300b00640c0a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 290951088 1250 290949838 290949859
    0x1e1a0a0c0803011235030a140f090c011d0d06291003020a321201050a060507020607030e04020d020a090e070302070503030a050403030209040c02061009021801050702 73
    0x1e01c01c000994020b02054030400345801d01407500c0b9080800c1044485c0059001c0c5914141d000706801c100e4290100c0840303415200d6440b91a0704e40503107030084549803039020704000d101131103150705019407240300c0000813102020619001100c3c03204201d001038006800101540c012803600c2107404000340c1c0600c10100703607142240450404101a0504220040380c000c00a03800c504000c0500701c80414142011418107406217800703801c4046a1705a01003030444401d40300161304803503400c7d6414103ca4400d036611129101281c0300400000c0c00ba080c400e01c0041000242c0b240300d00c0481c0e50440e0b000d001d032814004c6580e810b07921003805840781070303200d6004d00040102001520180669030800c1d039a24851502e05020071080900c00b81854017014010400d4001041c07002084a8010012003c00105666542000c070003c0c01003520095215081a000c840c82c1d9900180142c0a001039044403c256070381d48452800320f209440190392800e04007207248240b0341c0290050008140040c2c0040488c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 290952338 1250 290951088 290951093
    0xf08150a0906050f030c09070e0d120c0209010806070507030c050f060c1806190503042109030b01050d080a050a020709050c07050609060906060409030c12020133050f0d0c060201061e1a0a0c 83
    0x3c8060300300032f00c400142c010440c5001d51a2010900f4010202c4501600356402e00250051203445040301c05800d02c42c14080d043c0400800308100c0d040c0b01c042a06480c000d04240c0608145988402c46c034442c00c100c0c45400c0c01c0949000d80444506c660420a02e00205110300c005030b805410050003070b00d950040c110001c01800380300a04141c50724141d65030284280c1145440c03d81da40e03040c0c1002c2c3c01560b525100c200020000340480c1c190906500f0050740300d041ca0b400807854036a45401190401c2c2c20141030200c2041c0190142000c2c1c0d20800680e0700c83e075641c00100d50707910b50403a0840095400f0703802003803031030a25510104440d802843d100b5000c00c4103490303100c6491011680000189c2d513546e00700b1441d1102031100c0e44040c1c00840c3c0700c014100c000c40103004140050080702c0c421087ca603044030140e55000a501e0000d5030003c40030042c581e0700c000c003078028999441400300c0746040c0e04241c07900400041c0c50a050300c500d8580d4a101e290039440768030300c5410441d0301c10309005412450901 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 290953588 1250 290952338 290952353
    0x703030b031c020303100e0408030c0c0708030f13050609011707030e150103030206010b030705040e10050d0c050306010b131a1b01091a070f08150a0906050f030c09070e0d 75
    0x66028460b001982c1e86d0608904421004219030703c07409030011460140400070b052081101c1e04112141c490b40e45994001d41c89505021440c0c1c015400341c800000c040c44450640806842103c401740382c1b02c3c007070540c0c90041c00b41a100b4824020700040443c3c0e840c115002543e00e04942107001c070f207000159051000b440500d4041c1c61039a8000107220366004204141d810082c040c003505082c90918194207058001030f080740124020b4100704c2d546030300090411098112181d00070880141903494400c2e844c01c22000818580c060340c0d0090040710004a62070b600141110b00340c50340d5000078100146440512820030110700c2003101c0202042200c070600044030f2440302d6981030403200000c2c4010380c03031030098400c1d56000f111200104408040203441c54000d146c8100f241cad0300f41030007401d55481d0505600405001590030383d003c469400701085403811a0711100a80c1c005442e031150306582c04082680d104425642d40d41d02899103000030b008503104000051081101408000010b1540d80d01d519 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 290954838 1250 290953588 290953633
    0x90510060306020d1a030a081e07121103040b04030206070f021518010315090e0a050607050d060503030705060622060902090108072a02010212040e01030c0f06050703030b03 76
    0xb501107401058102c50748800e8460701344c0750041c0702c0c101600e401000003c25100e400d1104083c0c0144d82c0401c0c2c000b0760003480e9a40460650742070034500e81e584020314080440c0030f0307107180300320003c0c0e103210a044000e18000304407001d071062090351605080c6190b00300705040d8010315045620100800761440180c0b1021700d400c15205a04156075220b0b00780e00c0500388901d8040c00500e0405003003008904441004400700741c203607038141c040800d802491083c100d203031030041d400013841407069508001100344c4c820040c025005000f03d040c004142d172038007055940d008020001c2c1281e00000f0200d1040d19240d0314240302e040003902c8420300149070a2141c021614a980820700b55074000075803130b14641c0d01020a039402606800c152545100f010700b0144c0c003c0c80d04107558401d5000e0000c90381560b00810286280c400d1644090b50b66070307240c40706e070b01460300280300484600d51804404260011640e440c01d0655503580c1d1142d04000998800f10058601c0b034903001e800d0b005902c85858901007550804 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 290956088 1250 290954838 290954843
    0x3050f180117010b070b07020a050a140c120d030c0c0611040e061c02061e04170705030d080c031b1215030c011409120a0309031505011401030905100603 67
    0x3014400c1080c00242400003205907415400316900011310803000d1040540e007032180c0010311503103140d891b580c040e8a4010350b100090728a128040c111001c0040c91811950307d805c01005803a100c8403a4001d01c0422550710000c507240b5040000c00e007110314802c2c0c0c024a10200c0600d41b1641c201090784034070f011a0a05603881d24803100005061100c0c42000b540300d500084182d8070000980c00b40f4600c004043c1490000074403442c0c000809041440240510680c4164000c01140d607450752112001d0040d075000c100f05015001e9aa1b00092a241c0031a540307440702500d85500250303a940140740c4695a10080c100d10b2403000d0144110041218000039001450311940c407502c440c102540c0c9495024011039400e40320342e0140b1a51840c41e603000c42001401e6808540c0951508111000200c1030010781c1024001c0388a000031150a2640c001501011039004c1c1801c0400310001c8a140d800741c030024011400b0b000546501c0c204554800c0c0d010881c1c4502810585200050400e4910305a64044e8001d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 290957338 1250 290956088 290956117
    0x80a150b0a06020f0105060904020f040b01030609020f070507170d030b03030d06230402090310050a0209090403020a060c020120090102070b0307030b12010b03070302060711060a031b020a0b1303050f 87
    0x60744070380c84d00340b1038603400400449541c50b03031740390030f50008210010314140d89010315241c042078012031740aa00404c01400c5120019500c3d60540501c0803031a801080e030a0303440f0302c54001c0c000342d0812040e80c00a58546000301401c20040c0c403640030341c09410400074440c0c16100c2001354201e6440c941c401d001c0505440302041c216a00344482c550740b44041c82241c24402c5204001d0702c0b20a940000f000d0b40c0003103040c10003142030785d111100d2400070301522002ca5041607018080004040c1d010075807480841c450601040000c0461208a0032100c9902d0502c54820a06520740d0001e0a20405080a1001481110508c03901c0d00c8040c11150001d580c6030020079146c000c801001c1c0b4007150540340d2030030b03400d000704201e0410a002a40c0ca8500d448080e00030500015408240a290380d6200340f40311010344201da9500c8403440040c01070800e2880c2c5c0810b089040444c9038081d10204070203020a41107000d00d03903a6202c0040030030300f0b0321090310f08500384282001103030401c512030400f515181d03104041 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 290958588 1250 290957338 290957353
    0xc0c06071115010620010e0f010b100809070311040e2b11060c070c03050307110a290c0102040503060c0d0e1c0e130906090219080a150b0a0602 63
    0x10070752811005588000440c2c00036001406216071069603200031440f681c40340d00c140b05032103503214010f00840340840400e0144032001403d00310150080829000c1c15550044080c1109400710340c0090241d9000710142c00200c01040840c00a0359800c480c104000c0000600e4204210760f80d00d0040001c4c0c2c4a80401c0900420b2140341c004460030710400b8425090166021506048154551900402d80e168040003c2040c20038028002070b42009181d1041c1103d55941d41030811690000410304414031075803070f110020070020340c41104c89a04414000307461003240516600ac00182c1c100c0c0002c03142c10340d402c2c0400170340703a0f400b000014012500c10300d1080d56481030010f07080945200a02c070080e03941c0004a02103040c9065210200500650b18100100d03140a0780064061240d40c0038007005c50342020320300014003540703074010034001c1d100b20f07480785d001e55100d50707141c2c03600e245407040000341e800c213240110110702c8a80d103007820345006802c002032208d11100043c021585540240006a10580 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 290959838 1250 290958588 290958617
    0x30c190903030f033210062a1106030a0501090614060702010f1b0b04150504050a03080c04090e031c05100608060a05040507020a030e0102011401060315090f090302070e070509090c0c0607 82
    0x241ca0f0000d0a1207223400413065403040a40002e1300001840c0200000e0501c80c258103000c0c65940c002c42070000106915900e0400155540c0274000a0143c003040610b49000002c0308110b4101b01004900050125800c14503280c00541d241e81c221101c06d018440080b02c00441c8a101d9403001130502c0c8035410141030b42c281070600011100200e0f444000740c40c549424000440c20015034174204135454078014019584031840c1c1c5000f405207520405200c0d0070090310070860103000c0302510640d050180d801c1058001b0224500c06d655083d2031024505c443e002040c82150f100d00211980030001400c00c072007242d520030102d012140125000c6005130031400c100010980c1c4805000324005092000707004043c518040c00c1000d4106100c0d80007410790303802e004425100c400c071842005000b82801084410390b680d91220190544d102c0072801405850b1004c940d034140701030118021807040d5100c0d42040036030003c1c4041520050189481344000b4040c444003440d003000083c0c0b0030402075413a01103004001 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 290961088 1250 290959838 290959861
    0x30810030533061c0812180606010306060806010c02060903120306090907030c0504021602031b0a08010213140a030c030c0509010b07030f1b0503030c190903030f0332 73
    0xd0307140d51403030000a01445040d42c0d4103262010780e84c0c1600860969003526240c0202184075110381044407042c18800c01507821002c00040b91103207070007026503045645802c0118111000341c094400071541c0100814541e52042030900103151003d84100d04e04818080024540155841202100c11b07000040204509181003802d40120b9080014240141581e440117050407040c094140556030224903119030081d511184e1160a402805840c2407804081219010814883e000b82c0100d0035102c0002d00c0003c144200c0d50324420300310030810140c2c00c0013610031030841d00c09800e540c0101c0b0300c5000700200c2d14175400c181c003c0d48a0005440f9151800c0284015840c05921030401c400d0103000f03550100b50404002c4840000900e002600744507180c40941c0281c06d40c40000c2e1461001004101181c00e0183c0244403c801460705101100383c0000c086a0903c0b107808002c0c0054440100728030203a02a030455500e5850340091409040c0b61042c9054180c158503050304184180182404010b03242c1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 290962338 1250 290961088 290961163
    0xb030411190b090108070504030b040b01140a060806120102040807090b010212041d18030708030402030715120903120f1a06031b0c1e0601030606140d0308100305 71
    0x1081c1c0c0321080c403841d100d416207a50040102d400d06200402c03001400c0c4034032841c01c9501a5034029030442d802e0820342010404004240a418040d10121288580078070308410b0580c21503800e560f0341041c680e60325051020741002420103800541d001d12001c038101109202c40c1c406480c4070301000810b000480d000a190020240d003c00401c2310801040c44605000400001d07071099001e274206082d111070842d0101000c038940b510940307000200700303d01005445401140503500803811034480c15240d1044c0340c002e515942c031900101d510070380c12640104464001c082000d000e42030071080715685401000641d4001c00504009554034030040c903455103084018a102c2c50184ca440f0b09500d41148101541003004c0856000c900740420f44800504041044410707080c1710f00701c140102c0111a4030542e80d40028042211014107002021400b03900d1411070700f02003003008050120310f0b1159101034803031880c081c100038208410340102001082d000c00241130311030605403030482c44800c85140c0b40100e101 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 290963588 1250 290962338 290962369
    0x40b060417161d061807050702040e0609060f0a0e0a0c09050a0b1e060904021206090702010e0307030c03021903020d1b02060702010509061b0c0f0102010b280b030411 73
    0x4030200c007441104550700e0310f02e0382c2d02e4403020000015150b90f00007902e5400700c11213001300c107040c1000b000049607008025150003031003960b0a01012014544541c3c641c00c0c01ca9800c85180d00200002e01c0400309504000e801281014001903503228104485c1c1c00e0603050081aa50700349842e60402c00202c0d0b078070885070300964404d41040030741407000c00100403000c84281130710a000f041c101c03080550360340d00031074403a200c004104550301c034800c0f042918020411244c091080c0c144100042070300340180203c00301d00c1d0701c04019600e00421590140d5100c519028145d08602c41c20310b01d200c0750200500030a404070702a0b0000c040e107031000400140b0f095189036000710f09921005521006807605c5068882da2a42400c046481c0c0040002144003401400340b40b0902c2c94150301f55510940c40804c0c0f501c0c8118054480701d01d4071210b48016400c0c0c516102c1002e411004200c0c848441ca4126041451400ca0b103901240600ba40d03100c0c112900c0d001a01c080e03d102c4072403203216220b032078814500038021a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 290964838 1250 290963588 290963623
    0x402090a0b0f01140d1e0b0d0804050d080403080a110d030e07170f060a0615050301051309080c0f03180a0b0f03071e081b0306060702010e040b060417 66
    0xc4407004154940c2c034509000703042c001402d841c625510341103800d40d401e0780050502040b0000c0641c0b0448a205e40000085841340c0c9811881d04290910040d0280d2060f00b00d004645070501d41418050750100400f030941c8c1c000f000380408000100300c0d800512001c6015520821020f1291810700c2c100550302480000f41842e112a4220a20340400c1c4e00c001c4940244149036821807920205081950a051355440d030b00684c0e041200d2029640d01c038a042c2c4407445941c00e0190300b014415600361001303029450303108811850350b9000380f14980112288520640b5140d04181c4075007400e610304440303850701428907040441d0154192401082541505000715004404d145c50030005000d2403290f0760916550f05000400104040c0c021340d0008103542005000900c6e0401c40400106101d0090740c0c0f0f24090100b00f00001e103401c8060041d00d0040d0710007400740b40b4207242c035801510080214401c9507041501d428101000d55102005003009014030080742000d10504103800741081082c2000114130f5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 290966088 1250 290964838 290964851
    0xe0a050a06120b13110c100c1b060902060f0c120301150f0c050a0804090f050105150c0709020309010522030504030623090d1b170f160b0402090a 64
    0x107a204a14035485101c2000000705a82e101c400f00e003550790410b480c0c0454a0901044070700c0b440c6200c005000818401007521f0040000d5181d00e0709880c0307031400402c0050207510340c1c5c0d0240c0c200d03207400d010700300c1c4203080c00908808035601186c20707900300114491100402195100c1c0c128000d00c000d60282141c410320714039560402c59100303000e1940d44003140400c5041c80e50304940390f0044a03642c1202341c02208441d0340080c01c5c80c100b41e11340d005001d82d9140c90f081c18120005003400c1c1c00f419061742e400500c44003204600c0424440c298104240b400c14901c07c103440040d1003a100e20007180030b021883c00100742da00d446600458598480d15640b84071400d06503211001c254004140c50917a0780c003900201e40600340009814004031040310b0f0540c0079001c40c041c00354000001504600c00310135902c83c1d2103244400141c207949001030340c001414030b0480b00d802e81104030505000780703510a104200542002c0c0d00030214a20b50140c40700c125200c00c015170600c41980703000c000190b8412503003441070201 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 290967338 1250 290966088 290966099
    0x3050703142413020f031e0615130e090f0c091b030601052503110307021509060403050a030207050310110a0f020c03010e0604020f0607030f0e0307090501060e0a050a 73
    0x402900c1070040039600c2d80d240000b1680c1d00c003544101c840d90f0901081d51224018040a101c5900aa900c406240ca50240c44540702c424000d003207106200c010569081e1001000820708590700102c406054612400301c0891081801c1600a0003404004000c0c09585c580f08aaa403610505422052140543d0b4082012680c200c036a040000c543c1c400a154580d114080140c8041c010440c4c5502d001d4200d07a000c2261506040c03c0c051054004c0d60b0340c2d0514020242d107203480703100301c25020350020140a070700b07a03556000390f0090a02040152034946810f50300e4079401c0c20481581303021401a08440f0b0200b0952904000c05c45100f20714440400c104221000c5031519445401c00740720901c004500f05910f00303402400702d42c1c0040000f030020302c000303d80040602e407071b10003c407400c030f10440303a01e004454142000d60688042c00d40c581c82d4031003886026002900c1e070801030b09000b5414890b150010031104440c0c040c403402010280c6403c960080b20ba07013006403112480e00b0060055016102c03c00c10b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 290968588 1250 290967338 290967361
    0x1c30060b03011a16021512010e1e040c03141b0609010c030c03031509090c09020703020601121e0602030109050702011a04110405030105011205060f0127090b070305070314 75
    0x3503800c94000d95544c0c0d6107020b2485116602e12010280d4001c11545406080c00e01800080a40c503480140e000b00c2aa210740071959020401c1e52240311200031300c0c40c49900c2181728040c2a800a0144101910440c3d595448040545151100b080c1d1a0800c00303809503d80124680444201400c0b41c1540c2400c0120740002d202041d000409401c020f9070071340b07a109141c0a64400d0b401c0e0700c092820bc401c4551207140c0e040107000c00d041e0480b070040c5410381c00035640b05248242d50106525070302810702646080556904024800e07000d880258004801ea4104108035294140c024404c507405030b101e40c035182c00790080b0345000f080d501c19641441c0103101c4162840403001d50180301100d0000d170321910f00007000c42c3d500640d000303581c156190400100d00704918000740040c46d07202d60101d61490b614445544880c00b001e02c2066094001d841d042c001420b48180d0344000c43c0c040c642c001501e41e100f510340c01510700701078407500d02003a0781f071040c0544503905014000031040003144100f44c0b82010b1a8412 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 290969838 1250 290968588 290968619
    0x10b010c02090c12010b04080d030b1f021c08060f030d0909021803101505060c030d0f09020315090f0102040602030412020a050904200a0303021c30060b0301 69
    0x20702c19599100050720701da00d40025a881101c1002900220f9a100c0118800755842030080704624440d58a14000e0148039000d000c140d0036010740681d44100f501c54000404020850381c21084d400f0302d9a45200c80d00d442140741e103151441c0d03903070b07a440c60401e00c007070021400145002c02e009410a6014049648d0001da6090494031440c1005903203200462800500c07201e423000440e814042c03c00007555102c0503410240e00340707007021800b80f0703820b0b600c03c10420103100d45980d841240d04140450301d004a000d81c825042403561078000301e9002c00650001e400c00c10300c10880c07004241160b06101540d0b0040107042c4042540030000c620305414800003a40d240650710034000c040c90b01031001c000310b490b1050f403040107110252841c0e07200c5c03c0c50f06e4243d00c101e41e00503080e000011500c883c51700500c0d2182038202100c0e0160007070465505a01420090350410300c6802c01800000d44030340900700e0390b902c1070030348400b08656030480039200024020305840c4150b01281c8090b100f43f0050091a0b10f03424400d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 290971088 1250 290969838 290969843
    0x50d05130b0a2c03031c0f05070f03090809041b030b030609030909040c0f0620190204090215160218010509011203141201050301150807170f0106170f010b010c 70
    0x242e8402401c8040c07600f46a08044001d501800081442e020b54144408124020343c082c2c0814889010825840800c0701c1c802c44559000070890402c8440d024002e0740f22071022405030344846d25003117100c400305040d68102030940c440464541142020aa414416403040c550118041c041d00d051401c040340e96030094104a80c401c85221002c582000b80300115100185207852050300741546d1500003504120000003064031004a0b2801c01d1405003002c03d1101e000007004404070b081c856603801b400000c15145100300e8001141e940c40d0103000006d00c3c06000c100150b0402c9880400342032040c040581e0004210502c3e48040780e00605c4603035500c0e80b03204d0640300d00c505801d80f00b05d21820116040386280e5407549121500103121b40c002003203085036074181d40c7c4c01d070002d201400c11281885d1401001d0301c01c4403243e4010443c14410080c00e030514072610507031041211810f17001c0d01460760841d81241d110403c80800040d00800c01704090141c1e41480203c2c038006c02c40100303050300180c400a03050400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 290972338 1250 290971088 290971127
    0xe100801090f0204090507030603030f0c0312050a090f050d09120b0412140309060714030405060105040e010f1404230606040902060412030e0306011e050f030703050d05130b0a 77
    0x6042c1880d905642c001c103201c000c240940e04201001400611a43c001900042c60018039031075018014030b40d02011540c160355503400207210110180081c000a04260311050b01c50384078501050078400c48042d03170340c041c201400030100c00305000303002030049903c81d20f04403100b0010744000c07174a14404c1690258004000c030501e11885441102c5580e00303404a41d002c56400300502082620002d00c0c503100d0f50780350b16012181841d0980080050208590041c410790020b40180020b00b495001140040d00010010031200320071225041503801500c01c0c2c500010b00c2004000500480e200c00006400b08409142c615008a900319912440020255402107440360b440d001107483d240c04980041c1f541007200f00c103c2d145450024050142c00200354801d1080340c00101c1c82d0007004021f042002032441c03d080a0900d420700344080c2190701045550b2602070240000041072090062508500c0c840ea80c441d039030034105001251070302440d00510030085080c0120020300341c100e13240380403400207041d4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 290973588 1250 290972338 290972351
    0xc030f06030f060b061b0102040302010201050a022a120a020c030c010e0a030b10120602030708070810061103040f1e090c050306040504060617010209010305010e0f01150e150a0e10080109 82
    0xc00c451388201c4800f03403403486c030a6440a040080c107501500c15240700368002d00050300e41c1040b17039099010700043d4103d54846460101909840400d4840d00c008111059807003c403039115401101f07811050460000d41c0051903d00b030186000d100038280389100342090360714101c0c0d03a8045102c100050000502107882900400c2c1d0304200c4095580c01401c0b80e0302c8484804030303039207440c0c00a50819503100000c00d12a001244480f8020060035215000607581000710f1480c0c2901120f6145012005030400d0004200c0464105d5440081030701901d02902109103410300302405913500f841540c82006a6850186d412010541c4102140d8010100300c3e804074084e1504c0c2041d50082c00d10780d0100c08000f44e42010381ea11000190041c000303214090301c0400060380c0c0ca029501002d103044840c3c8401460314401440381521280131800001c0042c5014846410b8100108040700d00e0f00c001c3d002808070105050340d40710350141c1c2e05800d049054035000480710b407280c0050700c0c2400c12701079505040d0b103c02c0e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 290974838 1250 290973588 290973611
    0x40c031b08010207030c030818031c140103030801060f021501060f11150718031203051f0b09090114090103080c0c1509030105161d0d150c030f06030f06 67
    0x800c00751494400840d0764010624000d408030315003050803400b040e007140005602c00304444078070980402c010055454101c519010078003451811032a101665a1003c44d16086440f41c2000d03406144240c45001455050110150150301161803503011580f280e15030305100a8084a00d504444031401d01e001010b00c3c420041c0d5404044604c2c0204603c2112214106101e07070000450040c41152200c08a018410848503820103160001500410790305905080c002d109901241e40b0075070f521012001d01d94503046150207420990300152504070b020a00c0d100034640820b0709401400c040e807483c0c1400881c1800300c1c030398420503c070180a40101056070580c250080c4211816400c00a106483c2d0716070b07052940070305400981c40907000e0741ca080001002e19400d07291f0200c4090058481020102185e1912001403000c915140d411003441104d00b80000d0402c50460070305403d074240400e0f00281d092004048a40b180e050703180d2a4140f0707108001040004107a1099aa04058082407141c00c10 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 290976088 1250 290974838 290974883
    0x304210203010e060609010911030112060b060304050109050c090402030c10050d0c051b01060b07171c0b0906150703050711190f060507030e040b03070302091617040c03 74
    0x200041c0d0154209014200b0801001c07990910a00d812681d01c0d410ba600c540c007600849418030b141880c943c40801c0107001711210030a070b05074018410300020888a4080d0041000c0e42c2041d039040f1032682d1120021810000103200344a0080016204e10030585400c5d00000e07038500340d00d80340900440c000d07007010151610450440c0c4d140030403044280703d15005100000c0465011035042602c07110500c41c1d0110750b14040c0120800c407900c2c540c4250520782d141e25140240c42c0d0304009503104810401c0000750311035503400455400c459806002814104400901c0f00442006203040d109180c0c22000c000ca4002000c1510b02e00c42e054a02a500c51001c0e150003d41c02c03686c80b420340d0f402410300e2504c0c1e01c02080b04100c41c0994100c0c408000c00140e544105403500d00900c000180407454088000741d8a084c6540403001010f0300504907400709070340c0d40100f82040c1043e00c001c5144240e042032050f100e80c125008901041d14144910301e03e2401c0e031241140021240802007502c100050b0a040d100c050 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 290977338 1250 290976088 290976149
    0x30316200604032a0f030201020f0312060108130609061d0a020604090f06050a080d1101060e070e0105191d010801030f02010c0203160b070c050603090705130603060203010f0e0c07050304 82
    0x800051195181d05d10f036070040d621031004030b006100345103102241c030402100382d60b0f4190141040501c9034039035000544503400c6c01044d011511180301c2c154004611103010300c030082401840700142d2101003401c40c03000904030304451a0b840d40030880050060301d91004840131a9a40c210000380c0d12505882040a400d00d036020b164401c40604012a60315408109030b41a146161203020510003410000d50076035146100306040c0646d00c8000403c2c0502a0315100b05070311051506510b02003240c103d001e4094000100080010010144c208613406401c0452044031401d080c41079040d07246581386c0c41c0720105040000d04118800c40b0b0141191802c00000e400382c2450b880c082203842d00c0e0154800583c00c0385800392040b035100840041d4508103c0700310f80c001e104107009007601c18180401d000d80d180311114107260380c642e581000408100c403172001e50f018210408000b4000343c540800c41c0130000c00034082109000081040c00001400001100d04a58001611528020550070303031540b10b404 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 290978588 1250 290977338 290977403
    0xa0801051c080f0d2304020d03120f09170c100914030313060c170f150303040612060b0a09031415070809010510062a0203031620060403 60
    0x2c0440c0308a50100d100d8003a10103c64031450401c158080000400b22800341903070030b40700d400c000e07101050240c18018507040c6440d0103400c090b011102c070540224111203824a8100c40c6a42c0c9490340801c100221080072403405c4002990382c100400350b0034081e1500107211006180a03503500d16101005140500301c08615500d9090701e0b01c0c0e24241110b41701b2007403924400c503051450155200720702d85c0034604140350718400d041c0e401e000350b031480302e01040782c000600164911811100710224030f940c1000280042d144541c0c0300d0030310080c90420311040d41c100750443c50100c0400e01c8981c1000c0e5001d001c600441c0d402203150030038466000d44650600f070842c1d00d00464201828200070046030020203d13405402d0700340080101d80d032806500442d00200c2d01481c030001e020301050042c01101c9a0320401a02c2e00003c0414901d060f80c0c2c00649503501c01c80c00d59410b00700c10a818400e0140c00740c03007503191107900708402e07403240060000100e061045000040c070514021241181c551595100001085c5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 290979838 1250 290978588 290978603
    0x30912070305041a1303020603040f1709011206060507170403020405040f050d0306140d03140a2007060c03030e0307021201062c04030e13020a0f080c0a0801051c 71
    0xc0d0900030550b500500688500c0303d00795040b240040d615108448500032a6802040d5145c10350382002000e60003e082510b00d1039000741c50102251496442c10a014860b0b803100d651043d01070f0024240d0f00495084043c01ca240c0311041100d182c02c1011114000d0b07211042202079082552464a140525003002e5042840c0c40b082204000041061a0059020740b04541907039040b04401c4080d06d49602a92050181582c109980d606001e4600720b829442810600c1b080b0300100c0c026105070b040a40080005200c0724112000d146501c5080501544440d0140c9003540c24000c01500401c0320804c002c04040e41c810309007481a81c18010364502c607038024901190a4120081d2501030300e9207004a40350300c100c0881c01c0035000e00035164503030700030051280700760f0a03969910702f92481c0c01c94842c100c0d017015910040402c4807441c0d100409210340c1940b100020841101c40040c008900106482a810801c214194495800502e0241125400c4594651100b010b600c0100612000b00c0d0003003445 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 290981088 1250 290979838 290979847
    0xe060c010e0106031a1515090303160b2d040804120f11010203040e06190e1e060f030a140f1b09220323030a050f070f05040b030912 58
    0x1a4041d0032100860f0301901100d03001d5210010030041012084d1207014414111141a501c541080051006070b0000d41131f400e030a04607031201080c01c42d40700c0c10750040340c02c3d5000628010840c40b442080c0d00040c50710b4803590304240944c1c038801560340c01c4006e990035001500001d4108645407089a020b0540d043e481841002180380c189030300003218908540140c0384090b007040c1940f00000340c40444800b054400d01d20b8403020207003c0e084400305003903509242c0c0000701060341c10000f00f582e8019082c0034440851352480300b10ba40440c000240149114070190700010300240d034002980310141d43c102141008113110780000301d1030161148000751031030203684450200840340100c00c61b01c1080a8a041319556a0070705400001c1d0074148105c8400c070045c07000800440c1c85040755000c41d9807400c0d08031001da150400201120341088400700000c0c0c1e210401c20181d4195a1082034125135241412414a9007442c405051402a40140e801c60300001c00014130404042091812180b01c001015a64 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 290982338 1250 290981088 290981111
    0x318010b12150106030c020705010c080c030f0309010b01090b0d0203070e03070b0a080c0a0f0f0302070c09060302030c090906070f090308072d030c060914010c020c1507050d0e060c01 80
    0xb50145088010040180b41d400003404a019010707840b101d12499010f440818104001515a036112602c142e0700500c06001d08646070408000402e80045265049a01c071b1504984944c203407148045002d0400120190800c42d141010058403054184040003584a540700c510446040c44c0c0e140646502d84220440020510b842200a1030101180d17503a0b003800b0f0361404106c03400303881070341d030f400001a10a1255407240c0b840b890202e40c3d41619882c000d8640b04881d22101110001a00030031507a540d40d41c810000c501d0300700710117a1607034800c0d07444406d5450500f40b4262950b80c001d000006001403a05003003201391007400010051603000e00140e496a0181c01c144800a65810b507941003980c1c81420f00c0c200c821002142c003400b9503d5079071400304048569a9070007a000d0140c1c204d450102007114900c03210780c20b000e4200c40700803540c010894240754404103c0c810005105102c7c985c1400c00c1104083380c0d02280c040131408840c00d04d0242c08003544080740c1d151103000c40007180d81d440c11008000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 290983588 1250 290982338 290982343
    0x2040b24091306030503120c12040503091002190b090a051002030405010501061b0602090f03010e0a03140c030d1a03030a080906010608150d02030115080a0204060e09030318010b12 79
    0x141c81000741da00010040340080168103d440c0e50102800c9035005002ca4440446148806a4000415681c00b030800740034401c8903079240741c25902101c29400200b6120a02c0c104102000e080030140e100070326000044415040b114648800d024140c1101000062901001044808102030b8007104990f80d0b40ea0165080c0025041a54100c52035403c00c000000c8c8940b01c1c034100540300d1758940901510462550340c002c001c0d8081d1200d070380c0055084441c10203542c0c0070b01c180580c03103030101d028200d098160324006011011030005140440000c2c03100c02e00c1a5000003da41d030700c082d5040c0000340d184c9a170380f400c2e072040701082d01564507100005051841650045090703026a0103c0119070b40e0b640c071070800f940d10384000c0f100903000c500c4680c0080c14500c0e060403400310280c0041c0000076044003039002d80003000042d800400702e6502210f0050110300b0580708141c018a9200d90600b15400c0c02c007141c9440b40700251140b850000348600360a0844000c2d131040b104560002c15036038825200c159600e4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 290984838 1250 290983588 290983597
    0x12090629090c07022d090103050f0c040203100303030209190b180603160c020d020901080f0c041a1528110a03080106050a0306080303090f071208030402040b24 70
    0x1402521881d001c60000c0d404101a2204103a006040c42864007030580004042c5156002d040054003210082ca2500e8880180b56806035009501811840d4860001a85032a174100041c9020360310400401c00c00c050492640001d90342d140c40d01685c2c071000900020b18a43c01d03100d8850801c001a9000126540711100416141403400c1000d0b02c02250842080b105020403640c1d449015140d08618004030303c10944603c0c1c1c14801004a182806aa000304081c81d41c240c0005135164800b00c9800f440b444200860714503204204c8041c4000710500f016451007000080e0501e0181401c110506103019250007035079065019420702040407642d24800b40c52240e0505409004070f841ca4042550720b40e4041036038442da54045d11203548507440c0120031941ca502812031388040540d140c002040310318060005500800c1590000e01080551303071602070a000b000c0e44112140b0600700d00308400a6500019203a100341c040781c2c00566401410041180c0070200309e40804003042484a802c1560300d844080c1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 290986088 1250 290984838 290984921
    0x8030315011806050702060705100f050109181a090a0609030305011508090a03050307020a0506090703210f03020a1407030306170c09040605070903051501150f120906 73
    0x1c201104042c04045002c03001c2d4010040050000c200503c05403c148008000305032040302103032003018944502c1c1003124801c9041e40404c517101c17001000861010300a0800d030380a1f22040c1400603c0a50b20319604103200d01d200f00c0394028a00c00659842014060800c00030b400590503c000701c0c42d440e00030001c01c0240901caa80100c4114681046803055410754843c1180000410b41912940c4040ea51500004c3c505003c6200303821036507000600c01c0c0840c84c0a41c00880c010280e0f10b0451529403504d040110b28803400c080f0600b90300103500c0e030080c0010000049410010b0340e41c04280003c5420001c00344c1c500c02d80b110001802810160306070b002104940c000a10000490b016281da2a111500300c81c0b0b040d07001b0840c101003030100760103501103904010303d0309200300903950ba6030328a0b041414030b22680110070980001000784010041800c0400c01c2c0d2840e008080002d1598050550031024142c08501d56444100104000080e84407208880e111440040940c4504171603100c94041d04000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 290987338 1250 290986088 290986097
    0x150307030b0c2101030f020108101e0815040203030a1d0409030807120c0203040b03060d020a0e04060b010206040b0c030a0f0213141008010b030a0b090408190c03080c0c070803031501 80
    0x3112030b6220702d420400e042c5c5c0d03800088410038481a400442c0c001c540502001002c000c40c01c800291220000000751020540480c5492203500d800109030500c0d0700050384001d920300c610100001a500401214103483c89810050340010040040703035914006200c1c00b40e0418a0124404140758000702c02c148241d02e9541c41c180006820f240c11015030b030f4881003030800340e88188018401000b018019542c0b2400260902d00104a03540006032404030781e51101030761154803000c0c00300740089030040f2a1030004c203000404041c1401e03614a408031500506929074100044041160400c0c80d41000f0203d00101d00255121500b480c240c5d444800079118054001d51030100d031031214100000d49460402c99601c51141503840c113640c0d500c5542c001043c081245a48020720307034642d6100740c0203d00450054404507210328540f085201d814411040d0b42d81400343d4840c0d082c000982c0125200d501c0980107030416100e18034061f5041c6402e015401030082c0b0300010082140c0d8001064191400360b070244e85 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 290988588 1250 290987338 290987377
    0xf1103060f0102071a0f090a0306020c2419291206040803070e0d080f0405010e0d120f0908070308190513030f020a0b0a121a0306150307030b0c 63
    0x59a0710380017442600182860900c1c0d413102145050301a004004100da400c9181403070307610016402540b1900704036049640441c1400c0344840801680070072803907101c410084460300c01d10320b02140000414001007030415050700d4210003a5038004850030032070200301c0105003107803044400c0d00003401d5116501501000281980b00300b00001c5640c0500e4016901c140b460312055021100e4417605101c3da078001611411200c0010681d00007455160189010725444030309120006043e00060b0140c98801c2580070b0340704010480341c02e0400c20840741801e1485c00d0601060054034540c040e84e10850041c014824000180004a40105000b44690381c070448000394081060701c584c05030003031507140d04c81d65010600005000000c80c00d00c850004100520140d55140380d05101d80c4450b50700c00001d074603600d07200504482e0380110031040c1c0c0c114446108603510b10011a80d0fa810050004400744a8150341c01c6480c0c5040c41507101841d0810f114031b82e203103821381e000e5646070700014004541400088 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 290989838 1250 290988588 290988619
    0x2010e0109020f0906150409020a0306060327030e0319150204150e0310020d0912031802150405150a09150f1d030f0a02040513020901180f110306 64
    0x420a0212980100446403e80c406003c0c004075a1000b0070311a04400100200703880c0001c1a005080180302c44076025a07035800c0e00340000c09584031079204009150500e0f940039a250010040144a000320134005420b4105500b000c80e80c0301d124221042d003500a0b401055411400c000e10880741a000f203211200203204825640100d110303034811251ba00114030900801c0900c0b40c4101c00340d04030000c0c111050060359403094000c9078040100780d040340d592803041008100600101d1401c049a034142080300c550f0040001d12010000326009200b00241441e00c0c000801c000b0550b0007070140904400c035401e000301030a418903449400c0f800c01041180741c1c00100303c004d000014100944607070341e401400c00101000d82e4003040210515621811040f2564803e883c00c2022000c6d2010b0080106880310303440c0107110407605c2c058842003490b0302c540d1140e005600da5903845811180408000071001020085041c010303c07484400322485406c10b2a000149900e01010354091142103070007514440508 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 290991088 1250 290989838 290989841
    0x90301270605100f0608090102120a05010e07080114010f091505131a040303030c12110a030c0e03280605072f0604060c1107030f050c010804050c040f020d02071202010e01 75
    0x113104030614441daa03d410720031603214021054005c84040005814100c5032140e010070b4400c05c40350003103402c1ea102e004002c40b20000c91055004003007401c0400c2c203541040030607003680700400c0107103052000900d01c0007511445049084010240c518040c0b04c603400c11200140681c2c0580048208a0502480840e1141d1954180f41c42d0b07c07015000580341c1491076805801401058144078240000041d080c0e41079002d0b4000c015202483c4d03c14155108040b0002504a41c2c1080c1244100070300b0343c04550a13601d00046511400700c400e558161541d0380110509031007402c142e401041c0500341014416aa9040703901401c183c0035100c54000340d050041d030b40b00105801c0101d1020345900140100f03010600e1a48038015016161134045030103c40d86501c3d600d42282940111841d20b0001e003d41c090080a0111450310b00017480e1107500d81c140303505c0d01503884d020341840d00e02c21036440060b261084560b5040b0b842100c861502551580c500742081c00c0311001403c40b040140d42440711121481d8010f = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 290992338 1250 290991088 290991121
    0x6030708240402040209040203070f020d020706020a230d080615090108040b091207110306061c1b150c05150106121107060905061e0403090308090301270605 69
    0x55035034109916601028251400c0030141050f40c015500301b1807020b0589460000794810341d61601c2c0c500030342c0c0940000a20302000b140300d031000c540204106100301c0c0d0780851508240d541110683c2803190b0380d58001d100c41c0480700620b142c2407141615807080b035a0400c10241c030505007250200c101600f522409000c1c1e1142500071400940e6802c005000240010383c0e864019003c0c10496046582070900080036601040c030565608562071480043d9240811843d0391001094901d402e400340b0b0185040550140da1000a00c40945184100b000c01d000d100003000420724041103550012040c80060700548288009980a0080103c0070860800242d0118100c400965520f00840d400118180007080c0c2c24841c86040c1004000101c041101e500070f90904038020006410385082051104000700001c00e42590351941c85d208000100307030007690743d00403641c021011a80d901a2140001c0c01080500400e0302c50361181c40e964403c10010b0a0b00d114941d11600341081241c03541800007000246 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 290993588 1250 290992338 290992363
    0x403090b0304030e03060108150903090306070c060227010f0305060105091504090c080f01140306041101021906270213020c21090406050405070c0b060f031506030708 73
    0x468181001208218001107a00500900e00301e600c03250443d0011741041070030303030245070380d070780246414405014081201604140312a008520301900b0300c0210f03403682c0b00142400c00b8411840c48a82c28000c0c03540440d000c0800744040074040266000074800c2c0e00003c00c0751140090201c0706650a041d00038440c0b00e001c2d0310140c49580c1800c03c0501004110340c881c0c000c403800c0700c40034040052685d44034081c035200d8072007603100c1a0341454100851003414505900c04450442541c80b910045d40340454016081174000c1c0041c402d894481c00143d01d0481d070502c050000f084410740900a10019034040700000e00d14200310700400c0c0c0d109040c91164040410003039404200000c81d480680381c694000e1401140441c2501d80e1300c3c1c1c9040d01042d90a43c1304082034143c0f000015211801d280c1882040c002d088200e81c104000d04040c02d00900340d801c0b046005200c45c03007460100d01c1580c0c0704160f8480359a40201110021400f040e800078802d20281c550300e01a20035100302084074500842d0180d828003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 290994838 1250 290993588 290993597
    0x51b011407020313050616060f0515100504061206150c020307050307140607030e09150a060f1227111008040b0c1315050a0e0f1e04020906070b090705090403 69
    0x341071804010156008200c0000c040c6551301c7d03282c000030500e014000954030b204a00060b00c1c5007150782c000c000345140c0750715482154066966005643c220099030151402c0e8545800114880d020a20080c14160001e40c50012054882e8410382d070700c0400010094070a40580c1d201564400c1403550f07a4400340504400290031148502d0207003403c3d800381c41c2071802890098504104a80420440001a1961882166051142c4009060951404004080a280100e0210198000107080341c480c0c40c8078140e0306454540540d000c6284400400c0030700c913400d48101141b4101d00d0015140b654441c20b95020b00c503031409642105000d01c074074510840e0814000340346ea07668504d03801040c0d4414545529450301c000d40209008482c4001501d0700b0903151141a0348400b41e84001d030032405003282d03580c071482684400c82d01640300d103428071a50705135040140060750710b42c100041c041e000d0440d81a0700514003140680078000c8500d0350502603504041a035046503129000d00c840710b041110068041b4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 290996088 1250 290994838 290994877
    0x60901050d05060414040b0403081e060103021b070b040306050903040b0910020708070938010c0501090f050606090903130e0402030f1005150402070c0312051b0114070203 75
    0xc1e01908010781c04500100001026504039000882d00c0005440c1030399048510810801095048107000741c210709480d149200039510a0b01c0070107441c1c4001c10381c3c0e0405401107503000b406805c0200d400b001c440c8110650791203548542612220390070606c82514682d040a02041640c14003100315400e403507800c2c40103481c00e86904140000041062010000c62080440c001503803501804084060000f541010904184048040c0e04c20b0210003088045000c0b4500f03070070039001114801685a400038201862aa459420458010080d420010700a0b58520300500c041113400f1541500c0380c2c0b001c0f6203000041d25269031040d50380c09011001c4d507406000400600c42c0c91050070303100b94014402412a01138880d542c0c1c40500f0f10009510448841d034680742800104803031800004202503007500d0441c10598207842e864904e07003441c8130180141507407020a411540c414002c40d00d403480ba0000c4036481c469010609030003000d00d8210050011900d10100322030b20f20110072035640013040c1c0f4081c143d4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 290997338 1250 290996088 290996107
    0x30403110a08030301090504030306060806240c01050c19140909040f06090506041403070510020a110d0c05010507030b0d060f0b030d081005060415080a1107150b06090105 75
    0x100c4031420915944001000d1000504440400c011400303020b50b1940480c2a042c24039010b02030300c5580e04080c00340300c00c0000308801d42d00d0b1060031464105510050303603400c10f0429120354080c820b04015040c95401c00c000c001030300400310010840304a500c60540c0c00d541c0e1400d81111a51401903244e030b01c50b44c5c20480758985291003c2140d810038010181c0c0458403502d1b0740c95104548800e0821100c03500240200000c0c00081c006d110804111080510710f8400130703969150310342a003d49410241c03a40031402078203e40c0704041504c00001d011049680700e8072605005049030b003c2c10b0040b00d82d5800c050015101c1403007400741134007581c03002c0c101e11208980c0d640c50001034040840109100c543d100c0729402c2d503640400a01203c0e81c0140c44194690401548064040500d41c00050042100700020800318603242e800c1c4030101c2040c0f40c440380c25150580e2803406001c1005242881400119100c0244600c0382034400f1041903918040143c0c2201206100207030042d14007141c013013042071110014 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 290998588 1250 290997338 290997353
    0xf0f06090d0909020a090e0a0905010b0303040602030703050c121321030c0201030203090a080310030b1e160c05010c03140709050306010b0a0e04020307030b0102060c03040507170f060a050603011a03030403 90
    0x48130490404091b11074446103225036505085070000501d90b00c43c45042c06001d400c0c0b04400400005802a40c60b160600d07001030364900c51010300404025000460030388c544802e001c1500303c1a8645801a581c03040c0c0c21041001c1840c40c080e5000710b4481c800582080d0191442c3c1510301c030742c103403a80c03a040c080c01c2c1c00640082d00010251aa1405061500000a0a800001d51096454001030111237055045c21608110300a0007061002d0521100c405405039038000f25600c403440c06500c0c00420388084085861009001c0010300945c2030000d071170038803078050b0081051100c4078074401000395540d81c41102c91403c00c0c41003a800d90000c0d8018041504d4560042503229000d0130316076034401c02c1c1d20101d002c03680103c641c42c00181c0d54000101041d81c1c18001d60383c00c200e240c1072003802d606041d10f031561101881c1c4074200b50610185041e024603601840720f00003844d0407000b40d9a2515000c20214080d110072903416100c0d520309001003140c40100c0d410600c071300402400441c101403c50361101d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 290999838 1250 290998588 290998597
    0x6030a030827010213050301150b03040f050d0e040c0e0108040602030c1606020901022b0804020f0405070801030506070f1e020a20011202030105061c020c0f0f06090d090902 76
    0x2004000311a85071120b09991400741e0b090301d0010000143d40340300f003440d1816030305c0c25030300000d00c641d040542000e01e40f064000c015080d00e002c01003555032500c0e54913098100c000264001045030190ba10780140701d6410290149205e90700352020312400d0140b40003161600014215903020601d80030102c0d0100306030754041c6600c0303410301e81e10610b050000584504840c0c200402160002d40014903c012941d0512155810411840c840e10000c400600b80076820614040c0c0502045800f80005055503564800c5055480010f0300420450a00100040ca02d4100340401d45582c4100350100700d40c288910846404825283c1e0b0701a4200c010400455089601501c5a821032007054280070104020204031071007084105008941d5001545c009000c814401c80c20108661050004120135101c0c44111960089020400e41c40be540403899240240100c0c01c3c01c1c105442050a040c0c00b0000024000c0c451010f400102c0c1d80e203507120445540d403860200031160000305a59802c0010100ca40c0190 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 291001088 1250 290999838 290999851
    0x2505030105070c05032d0f0304060c0306030215030a060902040308030a060501141e04150809060603010c17041a01080106061103090f1309080a051b2e02070210030b130506030a0308 79
    0x16584046d036020a6003660300100c0c10f5203a0f00000000b88005c00c0130303901c1071805909260409215107481d680000f0013000780f800000c4004400040041e0406113154040006000300005c00c54035144c0b03a082c0307409249c008542e031880103440c015001c0f5496000702c00104410000e080210b10340b04442d98607503445540b20b15030041d41c40c401c0c040441c2403400b0001860480c20603582d000150701e1302101052a0031009002140a83d00d00303050074800583c060030210070314004082d181c041c0d8440b454142ca694903d2851000c60014880001c038280b0810742002c01120381c10783d02e2500644103101503540740c3c424040d4240e8006014141d01c0380b42d040484401c103941d5030703010000400d40060340743c100d07850344040250f00000e000080d120041e2100e8908440107403400400600500380e203018816840b05286444c0d4907074154000f0fa1101d004000c3d01101c00380c0741d0240096800700b103100c0001d8094400000b0bc288620010903451044480c11711034213102e8440140100302c9a0400d031010b5a41700d50240c0304 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 291002338 1250 291001088 291001147
    0x41d100b091824090706050f120c1603080105010e040b030a140a0c0608070f021b090c040b070605060108090a0803160504120506091c020604142505030105070c0503 72
    0x10005403414801d0300320204003e525003020524242e04ca5508002c4250003510034020180000090b4080602c1913400d007040b404c00c18480c0d074445800b1420103004400c418110250142a00e000701544880c40d18100c0d4002e0b00c034403401b4558402000180da45c04209590960301c115a0800412000c0c418408080d0006069803500c10780b40d11042021140303504880d02042c200414040d00b5075000c0b148501c81015840605003840c1c01d50f08002200c40e01d00281845070600a01080b54022030320100c40041c0b40300300400ba41c0e0309540c500540644400c03114540400e4000780080c291410200c0c0c001c800c2503003d1b00d082d02c0d643d00c00c0401c1100d1903900d0300110801c10148408924084106100844580240010410340c6000d030401031401d040d00410130080681840000382060700010410340042c3d1188010f0000c08141c094180b501140d403620858078000d21ba44c1d00c440a1820084000740c803819802442503a0b602002981c0d620240c002c02400c1764000c10004081c005805882400380707a1030300c0d1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 291003588 1250 291002338 291002353
    0x2030c100c1403131104110a0825090e071407080d090804081b04020a0918020d0203250206060a12050c0a060314090a110105030a0209041d100b0918 65
    0x40c2d82c8110741080b60120404d100c0c40742c52405001c2001551030440200311000e0040361340080f0043d015000d14818501440405c1d4042504c1c10340b210f000f0f00102800c0701020b10005c8092000919820340e500c62000403034049804500041c1c807030017138000c420300059040b03481c00c6c4255840d1402648850002c04405940c2d0b0065030028446000410040c40c1c504000c1c00c000b941e41074007080952035450205d10907841003018012950b04030143e2802ca035112880c030845200c2a21070071000e8440e100c01309808910000422030709503900302e03141c0c0c010210b02d400921039101c1070000b40d03035400068488642c081601c900c20800c00394003200c8050828030800030b442c201e105600214040324040d401040110391201c6c540707440b041341b90800302d0303014289138020301d0500702c1621101a54502c0302c144034100800040007034002402c0b03030100c68411202500400c03413660340660750101c1da80e215000b902c40d030250300c0d540c190542c03480c002c004540c240200144900c0c0c943c080701c000e0a00c4d03130780c4404806000713419 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 291004838 1250 291003588 291003617
    0x922031107120c08061005090c160230010207080306060906071403031503071d0405070f0303120507030c080636011a030106020c010f03060510090e060102030c100c 72
    0x14030110b440c51007100003040c180d0070810014206003009180d20520003400f20b0030003150fa20000103a405c0410b42940c40e5581c420954000f5928403440c038040d400160101000107030903511b0044409149405007191030241c921900d80e4203034170904002502c5940d040c0b02140092a1020040800050040c1000e28250460b99282c00328011001c2c2240b01e90070100030040461120401c90210141c107d000d0201d19003028407041d02080c1c600010b1034914888400070341005000c005650141000541e40c007070700b41d502d10b00245812078041c0b042585508007408240d899009002c0e00c00030a41c03d0b1100320f4035645580622481010308540d0a00109030031414401e140a0100300080703500e0044611000c6606000040544101035002c01042c8502000100b004650201c0e104d0f5800b0405d10300700b480c04400110850190072150402c80c2d1020056604582d4244c1090b046800c644040003c4a0290b0b1180d00590710790284444002d035070f030014107090700004010ba01114144c0c10500301080c90900d00d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 291006088 1250 291004838 291004859
    0x6070e120d08070201050109090b01030b040c0807090f0f1b18152a02060a0c0809040e0c01110c03120d061205070f080c1c0201140c0106050922031107 66
    0x31000d0320200b0701000c14020040c2c0d0a00441e0b01500302c1d250103000c0340c84656105d40d1000740500c005400c045295001c241008043c200000c0182030840c00c5404103034a44403003100400e490000d2a1000e464180c40649468140c00741046900b0310a01055010b0070030901600c00c140741e58034100340c0b1824110082100305c60034890700c0c004d00040da00c090240030000390554200c0c508184003d0170044212110005a462400b1140000114581503180c003071546401c2d07100c0d0280010055000e4203100000f840418000303822034034814241e035070403440305c03d40c40c0e950388820041c1140c0d501034000000081e0801045c4005002c8001d048800051680e9030f0090ba41d040328005204541d82c0c0c002075000c00211024940c0c020141c2007407409000143e01681c0000c000301e03091000410741203007421041f0290382c050603481400700302c0001d001e80d4464030300e100c0030300070005c50041c41d01c5a5000d6010410309a103e403103150040d4081c0202c00d0541d000c1d51001e03284854488100407031845000c201141c0d16540d07 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 291007194 1106 291006088 291006103
    0x111b060c0f032a0d0902040b0925090305160305060702060105060a0c060e100e070e090c04052802030a0605010f0f080a0b12030c19030206070e12 64
    0x8410b12075495982e6150781c15040300c0f0100d01201c8800d507135044010ba907442103804105012100041140400007030340d14403886007401c07102824a0842214292050800b4281800690b903640c4d1050329000600600a045088000040042000c10444590003c8160003e40144e60402002c03d0340350095003100000c0081e100380c000c0601840ba80800300c00c202d00000e4954001160049401406d00d071404c21303a4900c0341540008131070b0080700c1e02a004407190400360421100c1c440401c80603080c0074081a0000c5a00e00c0c44c210000103800300703410090b000c1030000d622454010070030703011903038030303a06c001c0c184072050007000c8080341d10100799a03211440f03092214040d21140d08030b800402031228855004280d01008103080b520000180540407a0079088403201c0f031005082c000403c40503040180540d010301301003404030b0300440c0e020f440b41401070186096126a50040ba26041c035 = true := by decide +kernel

theorem cover : BRFrame.Cov 290827338 291007194 := by
  have h0 := BRFrame.cov_init 290827338
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290827338 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 290827338 ≤ n) (h2 : n < 291007194) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
