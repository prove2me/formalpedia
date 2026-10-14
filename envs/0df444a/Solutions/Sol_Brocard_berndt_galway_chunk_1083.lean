-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1083
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:09:57.663892+00:00
-- url     : https://prove2.me/submissions/0b8552af-28cb-4c8c-8c17-25926ae29766

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 194604316 ≤ n < 194784172 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 194605566 1250 194604316 194604323
    0x10b01051303020103200a0f11162c010803030402011403011518170c0328021e090705040801150b0307080406110d14090a03020a0602090a030602270103050c16020a12 73
    0x38908c54540c00024900d41140c1c0c40c000041e84901c03140400f5800090403042540d94104070b005100860b100b144d00390b1498800305450b08242d10000051900011002d140503601c04d0345c40d02c5c01c199560109e071849000c28061480700b92004a40b00901c54010f00c0303c21118664403030321002c895603968200542e0303c0c1da0313030f145001c940181480018514080c0b000220850001c8455041c03102401000d203200f051800009004a405d64880c200712014019003010140b8020b20340d00305850485402020340e00a446040340640c28401c090038035080300c41c0c2c0101a1015501942d0071036403042811200b440b800381c01075500700d43e40d0000a80384a43d071700080050148810020544c4ca01d080a03d07640108001c0140300c0b04c0d0410340d03004000030303400300d00d0305c2100c3d030407540c090380b1100b1080010310b8541c4183c0c4010149071002812120140c203000c11009001c0041001544500c0282c00641c15604100c0300300300040002c02401a1740b140303e6031107209142c009000340760082d8541500c804030028000068 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 194606816 1250 194605566 194605577
    0x60b03040b0411031612020d0b100602010c02030304030e0919051608060d02030309010809100c030911040c05160305121302030714010c14010b040f0608010b01051303020103200a 78
    0x402808440800341c056010198020710052552000c000103141c1c59000d041e4500c005086c4050135941c540410b20011500308400c2641c600b0035032a1803005802501c90b800140d400c01c004651403500210a0768400e9815455085410300d000d800c1000040d03005105a44406990000550810480c800e0910440441076901038020403440090010b00c0300520310751158a840b0880c1006031400300030b8981e903038002c0c2031021840c1c882055070790411002e044001d08a524207402480c106034140c000347c81c01402070b00c0d100b05801900f8240070954501030502c001240781001070345044030428038000072031802403600324204240302c08030070a8600169508082c3c191041100c0c0150f14050202c00010480b40541448400c8c1c0c607070001e4400c030010140941400b001e1071006c1c81906c0290043c814100004204115000304454a00010b00b4180102d04440d8a030208408035940607104a403110281000b20161003480c641c01100508035400f8102c03150590707540380c500740125050140288907032a0302c0c0d6 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 194608066 1250 194606816 194606821
    0x30a050a050d11041706090d0806120d050409060905090705010f020f1e0607090303080420130e0c060c0c0607290601030f0b0603161806080a0b0301110f0904060b03040b 74
    0x2c0b05c00e030380c005502500194020310b041c85500e410000d6915075440c50b90824801542e100742c0000c0c08918048a0f0032440c0c01313505811146603600100410958000410030003100d42c0340c04201c411610116020b101940c017500342030180e907028240c8918201418411204003a08001d03800e803c00390f003020080400b00345c0c042000810b080911582c0c1c0d10030428070345000490700e140c400030188140504003a10000c1c001d001c801c480744840010001da10009005001c000c045065074a00600314010001c40902490041070304614101c1e0889058110b100010590f0300e010b181089403680c044401101c85800360300c403c10103a6001c00e508200368585400000481c901500050262000784040c03841003850f2504480c1c481c1d50340005d5a0b00800b0100c210071518580c0c28064410032912512514905040300c000114150311125561052051020622803010884241426112502c0305032003d003000340b18810394107910001074001d4100c000d0011134299030301c420b00c410642c0140d500b5210300d14401c04 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 194609316 1250 194608066 194608079
    0x1b0e0a0c020102070f0605150405070503090d0e0d02060c010b0a0312020105010b03041a09010605130902030f060408040308161a150a03120302090d0204020a03200a02030a050a050d1104 81
    0x60040e0412240000e5180c800240d030381080b038405120006001e0740d52800032821559040d84d60325400480504100200d00702a03401610940084038074440701d2040e400324200da00d10803010380d0b41c078a5000d800407082c232080d17508201045e001006540700c150b40e140b03c3c5154640c3c40f9032444c00114001caa10400d92840032a00074291881604402c1c0840d104106200000d0408101d90b50045501e51000003192983c2054502521103517209070303400440d111880c8190000c03948020480b51003142201c8201c03265503803254032018200d9000c1c10100d0180001c0004c603108800a0508040a105c00d503822a2076517207845000d003002c0c00a050144001081019141d050200441c110304101c84d124007591130b55840302e40301502600108200741c1c0201da4451152070300b421500c00242d00034019501d079a2100720040083c030230490000c50740303040038100081e40e9140e8002c6030140885940614544450001d00380e80c0b82d400001400100714082240d100f207490140b040300030108111007007030307625454000c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 194610566 1250 194609316 194609321
    0x403090503120a022815050a061d07181a0304120c020d02040b04090b0c0c0d050c0304061412070201061707231909090b0c03060d0f1b0e0a 61
    0x3003203010305000401401100f19000110f95020550301000481c05040d0342000030605e24100d00000d0940c20418082501c2032540c0d002907114110b00201040001d03507840e0358040702d80200300c40d8070800c81c94402203031806100302011500c1c03d074611808a44140d0300c0030080580983d000354000780c1c1c6004001c4c0020001e004101e40700a680901e414000f400c4540c00003800b000301d00703000034401c030703610468000c0c5a01c0ba40c1080c800b16402c5084007043e85442d25148149900ca44210781450203401e804030b405c54069416524800d01ca10300071810641881420b40c2c0080f540018030448940a00a2200c40d80741c9641d0144a0709243d03001140080c9000c040b00300d42c20705540d149006801a06d0140100c901e0040102100c10414034402421034900300481c0310305a8481050218055684001c240c100ca6600a83d0986104800c20354090391164102850ba00040d20a56800104010810b0110740c40403109241240100c101110132078000303442542c0824541d104050140044040007984101803 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 194611816 1250 194610566 194610583
    0x15070515040f210e09090f0d0518090c07060b0109090207030509030c0f030d031e1b1205010b04140f040f0c090e0405061f120303090213090809060f0903060403090503 73
    0x14040419140f5801c03802030120302c1041c0d4400d004240c20300000307110340d02c1000a00340040b0003105551a1110703c03040100142c0c04191b050500b100c0040303107c1458100f90010390703c1800000300e05420100147e0358480500f03014400700341000120710020540c0442c3d48002c2c00200e1103629110360729050482858280f0100c003030341c5840b51503200380640e0291001308a52100603c00d00d00001d19401403010300107a40f840c4505481000d2811f0601003000040c106004400d0910b82c440c105182d05609901040d10b001340251141d0403010b0108010012011039001810b81c40240022602c0840d00c0101d0102e401410024440c552201e01c401d0200d5008842000503024000d07100e0198038040d150a955028082c1c144070345104030101121028104c89100e4001d880d6281d40c00a015005040050250800c424240d101300d42d5124400d040c43c100d4400c2c07550480c4c2c4402090305060b0304004000541c1c00400501c10701c0b0b0000c01c5442a41da03000e2040a1060784681c0324130003500d0070700003070500c0c00e40f41 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 194613066 1250 194611816 194611853
    0x15010206040201080a0b01170a05040c08010903050405010e211b1c030806010c151e0b0a090f0222091103040b010312050705150405011a15070515040f 66
    0xc4400d000150368000e0540f58440018100070503076030b0441004031540c10783c4c0c0004e000041001403c1c001e000304103400c80c034081c502407050080515142c6d00103c0c2243c104400007004610100310801a2354000c184420700180000c0c020492501030310707a40c00784803211600742c00311904134003060700b2100701c110b0644030840010780300100106020303400e9030b401282061000d01805401c20009010b40e01c82c1103444840c940c0461100350f07402d840458000030f8440b660030501b1901c0c1580c44541d50700d400b4810300401d0000103000745000d0703140c45003460050226400d0150150340030440600038072507020b001110341c17040e016800c020380c3c40c0003c0c84049800c0c4102611098030301f0010f01c070114070380c43d00345415241c12040c6498070003000c9100f51a5840790b490020240d020ba202d20300c111031000d00180b032142c2e01800007400708400c9031140018030700907080301303030f0388400d41c9010380d207030f2159071809001d03554412000c8402480490f030a080021204640440b00320310f40ba0003110412141c0751514549940 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 194614316 1250 194613066 194613073
    0x4030201080a051314030c07060c030f110102130b040f0e090604031d0a150f03060620010e0a0c0603110f090103090f2103060b0301051c030203070b0f150102 69
    0x1154002030004070081d00070081d00b500c503408510114a42144d04100c168403400742e5014503940f602080d141d8008964102090107010700000b0b01d14055443e68020f55495a100e0441c21503a010a03540080c0c0300355401d0702d0303642c244240c100c83c040d04803900018103500d0301106c3d190352806902480000d40c80e042003a001041e8810320001039000103040303401c41d03418240501d420364030000e4000c6010154038129405041080300160020820b0140160020300e55030f03110394003420302d0081c1c0544030036103e8140003038140f0050500c0c1d01100c45242c8102050b90002048450000402d07e02d070007070f8050241c805500c00c4e44104850384c0c0610600440c40d0600f4001c60418569030407144041c02242d00013410300d82c07110700c88010010b42c48108400f0f941d010b01c0303d203040500132240c1c1791121105903038039003c00c1c0f61550121341460104141d90484600810308940e102100307041c454034042101e8101d05502c014049040011011603001c0c0c802e10b40031070926198584103e1540c410402540c3c950305640 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 194615566 1250 194614316 194614319
    0xf0d050c1c0e060d02070606090506090601020c0901063b01080702010c0507060b010c05070b031e040c0501050f130608190c0f08060a08010f020910020708030d150b0309071a04 77
    0x2600700c5003100c50030000f2288280c45440c800092000392107050402007100f803078111302144d01d1b40c00764070440c050f01c07040c0c3d58441d03260348a10040ea0b961452803c030300e61050003400100401c030f1148183c0e20080021248001000141c0018081303d100340081151a81003c80c0400003c0e5900014456001034144000d00030114074480203462803080c000d01604d01c035142ca040d4890350340a551140362841d8441c00f02c84100d66140d02040d103940090300c01c40b03560302c00b13034000d0b11100d050340948601407a000941a00c0480c0703444c00548940e413220340c0c0c1509220042c0308184452500201440040030300b621200d0481c540780460015000004540c08101890411501c1500358801a030520307100860070a40002c2d280d807000038a90051650040f00390307608001201c01800e03946e4010740710040d0250380000360039402401c00d980b282a07901a0801c1a0301c284230701c1c0c02c02c5115400807840020042000c2005645400700307919650301c121342038210f03a8010002003000c690403482030b8403100e244d0340b051030816 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 194616816 1250 194615566 194615623
    0x10b06030910050c1e09120307050a0501050c090f06030a0b0901030c03020f01050c0c010c020406050d0503040f0f0e0c0a1b0503220b0a030f060b0a1110051e07020f0d050c 75
    0xc5c01e0160668501c2c0c82c0202d03054400742c5500601c07801c196411005c5980324042480d0950341c4001404007104c0a508110109e1003030300a640541c0c403078130320091884103a50428000d000713032a04000e0039140440d4888101503510384a81000c035001c1e41c01001c021014904500500030010035910b1402d0400c00c040100800b50500030441d00503030102407801c140e40199a00025001e0402070300020b5220001110380420082c0000090040f99060004019619500c0e504074000b06022b1041140300b1044400158044400d1001084204000d081421040c01034241600504090090890340b0354000100d60200424001410b11035141c500703804000b090078048404c09334010b41c00d514082c56156824000007950301c0d0428005052110803440d26600959030040040903040d120070f110380036028241060070640d008440c49540e00504600e03441d5060241c03000c0400d8000c04070801c50284801d070890441c800c1c001008804040d507107032622064010401814200c413401c219050414012020301030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 194618066 1250 194616816 194616847
    0xd151211060a090302040903110607020d1206080d08100b0a050702011e021b041e09031215060507080c0d030c021501080d0c031e02100b010201180206030603010b06030910050c 77
    0x19658140c80225141d07000785815180d034440109ca40c10b00e405603d0410004c160f002802200342d10f5180e48410860a0000c11802201e80e580250f1441d47c000c04000032400780124082074216440403542103e00d551540310306a00e4002000000c00640001003810a40d079201c00407441440c55181d9103c04c500054001070366509000c0d40d4043c0404400b100c45041d40c1e107036030205124070b1285c160100c0200066600c0d2000780503015048002c2560410701d0420540c0e0b80c81107015440c0380d5401c21041c50700b008002d13070b482e800c03200c0e0868030001c042111320f070182c00912049224004c561808039000c7d00f00c0300003905003500c44503880c1420100c031004001401001030809916006400c140010200d54181118400d6002270344c440074013281600054061390000d564100e02040d090f00f08a03403140480124281d6101011280b04d0654041000c00540b4281c0c00071904145d000b0000222035070164046801500212003c115a40140045d0300180300c1c540500b55001c1400d0b43d8586c6400c4101c00040807 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 194619316 1250 194618066 194618069
    0x71a070e061306080c1314030d11070909170a20010b09010b0a02032203051c052713050907060e03100f06050607050d02070602010606140d151211060a09 67
    0x8018130b840209020420820455008041258903483e03503c7d1540202c5d2108104909a64024810304054030140c40c4140003203180d10201d207000e8030110703140c40a54400340c10b00f02c0f42503403003c2600403c20300106552004040524442d299004400c0fa500c400619501102c00840116410034451544643e9002c00083c19070b510f482da569150300810408a02d50702840380c0c00202018150140200384c0c10480501c01268030803802ca444070b40700c0030440c40717003602c441802c1c00c003280062100c08260398000c800740c050a1052494150031548110001d80070904550256008590310024003460140621013200a8029810180f0700071403098042540d8100712029170500d15600c1c0603004482150383c201c0001000000d01442e1610001e0400c40e45501d18150102c0151141398400a038490041c081d020469030740d6110205000f000c0c00c0b4001959020a8100c1302d010b0b1b0f24a50760714200000c01d003804c0600050500b103814413000c1d1501a004803aa420717824414901031290703140d03e59100a000c1c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 194620566 1250 194619316 194619329
    0x30405030c0616021009030b1e0c09040e0d0c06200406050c070503030406030203090c09090706030c1b290f0a0e0f0d0e03010b06040b120c071a070e0613 67
    0x40d50b030b070304100160f04006000035009510400c0d040c000c0b031220342d02035000d006590281c0300700380b034640341d054803454011281c1682c507070341c94420400101c19030680700140c01d50f90307406000407510328400d1600c1424440180745200214000080c40d0040c0b0030903104810030b00c40b148000003c07110804c018410300780514030511003008000215103038103010a100c1d6000030030019084989903519a24054007a4000b01c40401181c4078a120100e00c1e46030112140d4040c00c00340b0041c1610a082003030440141c51602000003d1002c0129009400f9482803001e22042e4082c0343c542569464224103a00c00c24242c40c4c00c401c403060040e05005044841d2001e198000c03424105c006161b0f107510708400e00b441300b041840060740c051880115000d64201e800d072003000f00c00314006c04c4010000000c004503030140c6d00910060010510a0303841c0c0030103407007035903802c62000c520721803c0c60302c1c903540c0c50b105413421002030340da41d0205002e00c0a0340b900000103400540d021681c0c5030505d08400c160452051a901c100e0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 194621816 1250 194620566 194620579
    0xd0201090b06210102030106170c07150c11070b03040311030a0e01030c0e09130c050a1208030709050a1212030603150f06090e010608060c0a081b210f010503030405030c 74
    0x10022110f20200110f9001440d800035900c13580d580c0400742030141d05c1c5918064411201c1d0000d03074501c5604088607401c6500c5011209400486888107004200011a07030090014404070000301100230408000181890740e010355a03858503241c004c0614141645442c1c4940c4188600380149406c0150f10703884180030b29000840c000445400c60f0075403201158142c1100102e42802221021001210000c50150003100040c60b07544007880100750a034403c408181c00c1460511001030040c01c0219085030b00e500d005410340d0b403941f00150202d4403030b030b00c01080840c0d42d007038141c20090245485013040307285050800c1420b1442d11154602e080c00240f8000c00e6644a44e1107030b00c15000d40c0181d000d040c0c020010080d901e0244012402030410380030b000340300d10447c40001d01c014018411038003a0400c65035031550716254641c480e001c07440006c045590002e0203116810185425105400501481180340146424409600101e004060300005e0083d0800c002c180120744001a0413403aa05059501 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 194623066 1250 194621816 194621839
    0x30b01030b04020d0c080c010306150e0607050304080f03030a1a09010504200a0507020a08010911060f040803070b01050f010207081c03061d04120c1104020a12090b090d0201090b06 79
    0x2e400701340020380c0201081d0400102040c071100020f0503c40f400c0e42030300c0c104a0180c4500703285110b101d10201c1900040c103610400d90240c10700c0c0000c0c10076640316104413030520351240891420a0100d10301000710307510100400015031481e00030115100e510300b5200340401088004102c41150502a0764082c544822206001001150200f0030452802c2c0f41d007521000a10001885540908410f07845403005900c0800d40207410b21590704420b40c000e2686d442860030000b44040f5421424020505420604c000900307a68140014070805100d10304040712036041c00e080183c19048404e48504560003a4001d102c008400154074140810340c1010640e20000d241048003d040c494205a042981d50840e019030751041f40e4034075016a100b9103202c00200501d01c021510404000f1014003492410fa1241050b81450b5000f00200c0b40503162040d40528030800388025907001200403580c440f4080c04100511909002507000d00c80c0d2031000f8481043c89031a0291034800250505103d100c2280b00c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 194624316 1250 194623066 194623069
    0x4050a03110c040e030a0207080f030301170f03040621020a021b0f031006081203150d15150801051f1707050310020901030b0d021f050906070b0a0f06030b01030b0402 73
    0x1421500442c001e105001211003c2c02c000c3c0c0340d0304400c136910098404d100011a403060040341c0200360004d03c3d0010f500b56803070041d00f18003000103480c220981e8014030075240c04010781440200090704464451243ea001c00c00441500301031101d00d038481c400c1c410f00070041300603404a0002441c2c22040d003c0c1604242c1e000000e00300e0000032100740c2e450700c0341c030b008000740c107409400413021221034100b503400f528011400c0b04200d1000315144401364107000100201d524100c5010110306000f1900e44a01d1000f0a50340702c11540d80d001c003c644c0c05020038007046140001d015680d0311010b1040e035000002e00414850340c104a0034040d100d5060200140300718180340400c169002014020100d9100290581040c0000e50001c0c0d9a14002400c0c030f0003000b02e605201d80e019000643c041c084d80c0d0448040c6504054050341c0481780000c01c0350401410b02e0aa0380c1c14090092240900044c004a00b07002d40400210b80140b0340c000c442c03600b800c8040000c255885031440c1101c0d04a00c2c00b0708030765902d10 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 194625566 1250 194624316 194624323
    0x204140f040f060e0f0109050405060c18060304032c0a0308180402030f0a140402060d0f111b010b0a0317070305070204020706050610030608120a1115041a04050a0311 73
    0x110280b2503407400c2c50004100341580420350013800c10b203080702190798a60121006a40c1c0484001e492030740141c0202d2041040c41d4000c040c001c3da02104419444031100000700c4e1036100b5a000d50000d028845240340491034425461200303e500b5032400802540040800c46a03140c030310000e452002c0120300b805602014209007444800001d20440d682c1c501070107002c004490035905000054503080194459608203400305020340c0c3c000740003500f00040e1520303407005440307007400c1064001d44840540c4904001e9a01400000e00728165460784500180100c0e0301f180c0d44108001e1080e0f1120f2402c00114003940e90000750305600e16125507490707002e0300301941c640c810324034000d404c9880041c850041c010b640d880079000c1c4d0f1003190700300c86c02140c041c03044095800718000d84100d5000070b00403084943c0000010000d401142c14820002e03e407a1440c7c5003081d1071462101d00d5070741407034200010003180c2c25508100c0c11400c0003440080c1459194159284c00d0141d00405100c00003200c5042a034042 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 194626816 1250 194625566 194625581
    0x1406150703050c01020406110f150f151206011e0f060c050a1e0b0a0207050d0305060a0e0a020d0501050105041409060d05010c0c03021e0a08090406031718040204140f04 74
    0x200217640d916941c14004106440207181c0c08440c5c010414260350300c2e50301281a004041a848031014540c4441c100d103500c180340908404a0840d00e0b0043d043c207500c0d104001e2110040190251650f989450200f011075041c150704200f01800c0385e13205010040c2101c0031102916001d25080003030038028034115140820312040540030942c0604481c06407407a0021800c1800c1c0300714904a2151507140b040400d82c012110000c00540003038074882d03200c41c460b501007940a0001409118030aa0b602058120150f080e00c281411507000034103c1c0390341c15940284e6004000a103452841e2920703005240903d5040c05580c940706141c09004900d441c0e945e11420300d003444d0800000c000041e20101c001d005c4004250044015000720300503000310000d800380542107610403001508035010036603540d2400768407000e0042d0b071240d6290b20120200b411342c1307650172032014080d00c115580c00e030740002e04081c8500c540e42d00b842280100000e10000990b8072400700905400d642d090340b0348142c80002009009030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 194628066 1250 194626816 194626837
    0x2060426030a020703030627050a2306030105130206030403030f021b0c040c0302040b040311030f0f211c0c03240915080d0f0e0306040b040501140615070305 69
    0x20080c0107000d800c43c0e0042241c1c034800c2d1402c10549540f6120195001304200310000f0b008869003000540d0b08aa4105945c0110300200c0024544a060300310744501c10307400c942020008100041110340d080c244070f0150020480d501a00e00039209070b00094062000420040c201a104c0b41e004902078040d405503601d44181c5030540c00543c00b00c442c1c4a81c4c0c0d01d0508a12807241c1c0c142400320100710300031b10888013994102492545014103585444142400c0000401d0701440b590007950304546003406201c2e50004668068140c94a460074807651190000c0c440b000a088108129000c010965501082c0f006040c00045240100003005800034000000d03034408200001c105d03031540140101c000b20642d15070b88410032241c01c08242a4548172000d02900c0c403c0d41c404d52024450303900500e0300301c0d81d0712640d00e481e240110303180740845e0400700141c908584c401100c031705000c01c010080c002d40580703134501c05d14142c1e0b40c5001000940349011031040280b40500000b18101070522540444600101 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 194629316 1250 194628066 194628143
    0xc0b01060c0b060405010b0409090201021e060105120f030a08040f0605040308100b070b1315060f030618050705100201090b191d060c09060c1c031506020604 69
    0x2510a0041d00026064908441d11905500018242d00d820700c2518141c4c0c900003007641c10036040c05100d000a12074100c0030f0b03066204207001000c51040000d024000560580d02421095141905100103000c1107054107585410819280c0341d60907000041e40c859501074a4121981e0712582003162011040820140040b800c4c002084140342e049000c4d14000c5070035485440081d540d82e00080c089010711007000b05200c007010302103018025103aa100c0c100a0040c5d11000d9100d9440103031404513929a40304501090102508005212403072250003140402d84060381070304c011668035940c07214140e010b071030b1142091240c0d1220303062007580031070102684201c01c4049428040440362242014908103102107007072250008141d01d100000c03100b051007484c010b00f8203441301104a2955001106031a40080d0244241584000c04200715060405503c3e002c845403001ca0b14020143d13980c20b42083e8034001441010018190300040407a0f10076001030464040c0100200d408460182d00c8000d42032100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 194630566 1250 194629316 194629319
    0x516021311071a07020c010804080901050912010b0906180f0a0209030d020109020f010309080d23010306020a080f070c0212010204090509153411010c0314180c060a0c0b01 75
    0x20441ca046200d851019201e6003e0b43c1c4070002280d4600d03103010401e0000d82c041021600050012028008040050500d40d09040103000410301607125000d4a500ca42c1d11440b241c0032034185101010b802c82d00c1961040c01d6030301c0300c204422040d0406002049080c401d800003c0c242d01c100e5046d60902c29009003900c18030b4010705030090180181c100c0583c462010591604000e60191040d803041c00e501040d0720f81000c003004100b0000b016070440542c004030070581030722000642101c28a020703601c10100161a0341042c4402040da400041801d5015409002403282c0103402003803080751540e0459505050082280c441400390045910092140c3c3c141010720490207008230706888150244101c41400751b80700c904004002c02445850640904000c91039095001c1c11143e003940600c0c281031411310003041c100e45a003156400704c10032000907601c507501860207070036066007a0819044942c0603a445228101e2030303240c5411071130f441e200748000074410101038001d91524814a4000a04500700e6 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 194631816 1250 194630566 194630573
    0x405010b131505061201060c03050c1c23030112030309022e0503010e0402100309120f030e0105010506030a05180303070806120a0c05011103041e0510051602131107 72
    0x14102440300c03100308424141c0120300c50800c4001c0d42d04a61040c401111710364a042015100708190507000c3c0e081107401c001c8401201c00801c09c44080402c00c051385100300c480610024049080c5055080317081800f142035800002a03441501d0655010707103090365440c0201d1a01b54010004141d001307400004015000381c401100320005840031240800e810318a9030b640504450b60300c403d019080e0fa240b0803002040c0542000700044d24a070f452410300003004001030f02c5800d401c00e804c09601c000102d0030429466501c1c5d15011700302558410304020701c090350601002a4170360000900d110420f0b0355a00015000c0c20940090080405048055980c3e03410318440c01043c0b002d0444010b402009c3c8010810340c240c03000601100403d07001070001e0415403c1600450303800201036a8020540303c1880040b6001e00244180a05540c42e45101007069183c1010710484c0292030303c1200c10b001e000d1112030403801d551982212a2a8100d0b0360801c14400460b40744000c05d00a40d044d00e082c440451a5003c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 194633066 1250 194631816 194631821
    0x20c0f0601050f0a030b0f07210e071a03010b0309011e020d050c070203031c23040605070311030a0f090c091a09010501020c01050711090c0403060b041b080405010b13 73
    0x59460543d07540f850741075140140f002003005480b00a00341d03a08203002462460010801c41e40020310b40c0361516842c080b8680c103246030030030204400c0c03640d0ba0b1a03c40c900b6180c820084030f0028550450340202d1501c0345521310026000520642c0700c05c081c00400501181c03020352082310088050710300122820031040e0014001e41150482c7d81c8483c0c9094045640d007603c41c000d440c940d907801402545040440000300c0d550880c0c00d1140341c440c81c0c81ea03102411381795003000219a903900d40a076844003482c10742890001c1e2403001d00f101003414908419034038075900394421a54012050b0b00c1c04032305007403100000b400030215484003400b4007002c84008100e11006400c8076040c441c44d074404440c011040010040100c00a1081d680035074480c4035800001e500910203070000a018000320800c00211101041120303a00b101d400610480006084c81000040c0c0b08051943c1000d44042040f03001000c0740c060443c0150700d6074001e200342c0200180030000250007280f00307494003914606014101d046151302 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 194634316 1250 194633066 194633069
    0x15040b0106030507091404090311010c120b09011a030910050c03070e0306060f1c21120911010809031e0405120c090c1e0309060a0c020a050a060b010201020c0f0601 72
    0x3d040c28041402c661040c01e040c000e5841e000500c480c0b8600c0441003100400340541c0407014070600c0c0c0d10080d0203032001c2c81040300052058842e84c011014660014048a080710811803045442c000180440701e044404c0320803140522180603a203488820266242401c4001c500003040c1c00c2108001a01d600c0034051030244036513454008428513040c04041d100c03c002c07a00b20350801d00d9141c0c450060702c1c180703100344401d10f0303100050300340204152201d0056806540b03650110b14072015841e41d40c2070f80155009011501e0b03080400020700c507651003807080c5850455030381c108a100700101d80c00c40400d2040700c04521607040440741710b52809501101d00d41042c8500c0b13201d29400ea280d400d616202094801d100c0000605501140c0d850300104401901f181d5000c10414610403000409072035120015805081c4400042c80c0c140340c4940c265058861b5400d40f1030440d0004070303201c80060000517060707071126401070020070204441c40040380280544039540d41244070b001040551000003090903030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 194635566 1250 194634316 194634329
    0xb0307050c0313050907020105190b0a03060e070e010509040f02041d0d170c0a0c061d030d0203220b0a0b040e0703030c0b010603020c0a080a0c020d050c0103060905090c01030b0315040b01 82
    0x542c06e56a010042c1c4c02c80d13030308441001c40380c03134000d480307142070901c6030321106a042000304082041501d0f070316060222440d4200141301030303101c0c0c1c1007841036035402d0204500410080390105a1890b1580e520050b0311580d0800074001c075140c0100c11000d80b00010000510110401203600403205400c004141100d05404040c41c0131000c1c0214500e4513110044a0200700f0503140d8005043c10f0786c0d80c08005040a18000e800360269041a60b480c0074140020045c15030605005030b220304090030342d01e41070144040314002456500220303e0000b501441040d1307100c1003000c00010902d09000218001e8501420100c0d01c60141440110070180c120b5002c01205019400c510304907a00c48609030124800c3c43c1c3d6a540a52002078080d00051041008215000452504c01d02e410a582e000c203251420401c1c041300c4070f8200c1641c44945590503c102c00040c880039406000a003080150651901c0d0201c128504058440f89021007a450400c520310050070700c020040003518280c104010850000c0c085d0301c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 194636816 1250 194635566 194635579
    0x702090a1b14040806010602060907050102070303090623030109090506100e040f03050d050a060801140411060903070b0313051209060d0c0c12020303191103010b0307050c031305 78
    0x150882658403500c51018103500703144840c550500e07401d8640c40702d00d0000c1030b0000c40400c0040342e404410b02c01c4500070500ca40051000b4207003d0b0044d4280303107283c1c1102d411948801c4003000801d611080d44402c603103442c1005c001d442c0b10036189650f1080c0460380001003003030000000900c110658003045409008009542c016103036040c6001240840c2e01c1010700159003840410007203130320b024505810510a041036894a181c43d1251419104100c40d00c0c50500d9a0b2081080040428042c81c99114100a1070300b1040c0741175600c030604840c501d401e9900a1001280481e0f4544040051078041c00840a0319510380ca0007034549841303014500300c1180c0034040c0b0500b8004190080b803c1c0c0304007400c010406070803c3d406034071171030082c0707105141030703040111080c400d40200e41030022100c0c0c046820f6001d0742e40c2c0d140203001040d002001ea524042000d140100c0da10321702071070000b52410355126680d40e40d62034544040c00ca5441c0248203460381b035404001044081d82c80b40820b51412240252050f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 194638066 1250 194636816 194636821
    0x30c090403021b0d02090a0209031011030103170a120b120106030c1d071d18071805030a020a0b030705091305060a050d08030610120e0f190201050a120f0c05070209 72
    0x130302c0514240c0400003508004031501080a40c0265000b901480030047e08541035882040c4208054400030440321010100c00801403050148104440104441148006280021420004241c0300360348401c0e040c100e644a1010201c0d5568180c1400074804150080c0480c43e22414024409203071407140f9800c20083d01d1001c0207035444401205e01c900c440392190081c500c000c0709011b0324a80c0e83d09030b441c2e01150744410445148049403030345024002d255a07850b4030034183c1040010b40d08494200501ca64031108841005a9a483c103503001d0302c3c84102c0302d0b80c580c0c0700c0752003e940c14081c00c0d4550707607c0f91040008103a0701040e580101d00c500c2e411200e090302c40340e0303406c02d10001c00381065010300241810000200746007403020f100c80740c404151070034401020003022401c0841d415200c000b0140d4100354800400c3d183c042000a8a40001c00717440b6503920b41c5607001821502c590030400e002c1c081c03806c0c00943d08082a6114000d02c0312440000d2200704143c2c00020215030000104900c55802c4001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 194639316 1250 194638066 194638069
    0xe0102040f120203070902130902030c0d0b0f060f070809030a0503070c05060405010504030609051c020102120f060d120e04022b06081f020903010f1401080102190e030c090403021b 79
    0x102d1400440c0c015024185507820138160801a510500300030100c21165103000400d42d500c1d04c0110f100d64128100c1c030b42c45910500c007940c00d85903408200d51180d03804081d404040d070f540748102c40341000400c4d0459a00c403210314080d607460254180715a03050144080719401d001d00403008041d401c1c840d00240740307003e03110b0041140318092030040780d001a0050000340001910750b801042540d0248088641d804a28040c1d60341312440311564500603500400d400158041c8081c00b185c0001d601071701148240303468000314008080b0404041d2040400e5004013407020301503002040200400f0b4402d42d0307602140d201683c52404402041c00d030347c940c201000241e01195125440548690b107020b0185104620018003000c0090f46034607040603807c1000e903031244c0e402d01c951000441020b002249540000403a40d041d90016072040c5c1c00e69004114204620684101a00035030002d4148003485885000200b0314184c5812550764202511100380410302d034000617140d5030000c0b0003040f0f204c0e6080080 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 194640566 1250 194639316 194639339
    0x307080708121801030b0303070f11130212272508060402031c0302090d0b0103050d050c0c1903020d0b010519030302060609070c0f031116030201080f18010e0102040f 73
    0xf43c514540d18400b9442c0d800c00e600c0380e04088035510008003103c1c02c03d03409032103042017030340407030403c070781d103901c101c54a096038100a1902d8000f000d140d00b0850078512500c00c0842c404000800048607034042c3c242200b001c2c0005240e81d080d107140d00048803020340499254040141401e00b140d40e500f42d08910011b041c0000180307451113070340d0241c050003890742a01c107140300070512010303240c0c2071617000c2c8001d0700c07039031101c1b401e03903e8a5000e00c0b540d001a516504005041861003040d100c1004800c009a00c218100000d403005040c0c1d094840703909174801c04010100446098100a40c4102c0d00c0551009020140c03650305c0c141e52301204c02d92200c03030300e1090704074500c40c6034030000b000342c3c03c6203000548602c4d18458042c0d02c09014200008214215500c103c07010031003003012000704c0d01e00070200700b000300e0030000b003208102c6070200e114005041d0b40020341401c40040c11049104540000107000007241035841161406880c000d100910700d465805003c7d40040c096400d100c2044035001802d1007114 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 194641816 1250 194640566 194640577
    0x30901081510140f0a030f05060415031203020f030c07061a030706051e0a020601060912020a03020d020409080a09031104110a1112040f060e04050420010e030708070812 74
    0x10201e20350580b08410603a4074080c1c2620081d02c0b04000d000900c1180b074400c00030721903842280d0b0001a1741c0300801e000411520094440c134059490850748540d030381807000d144000d0f00d82080403040f030700c405200220b000e0322440101c034100f00c202200b40444540450003134400640304141c280000319000c404804003814050500e41d02d0707480200208000d41c002c100030080082c20341c1101c0781043c020b40c00d20006912030b42d80361006078010001000407507030011034038001c0d06058001420b00c8000c3d0300000d105a0050002038803400b0700d1010382045549941c4031085e941c1e03102c1c41050711128075400203826151b05100039204007044110542151420f48100005121045100380c1040c00c0e2100407074650080b12500070b140e200d80002803100d02c948201920007454540300c0d810005050000c0204160030a0f00b02c14025410f00e000d00000035007004803a8205a0004006200321604030012501202c801c0c00580d0103008004000c01c041c07202003007010036103018804550704000202a0f015051069 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 194643066 1250 194641816 194641819
    0x1107151d03120f21010e0108071205070611031201030b01080f0604050a030806060c071509091803051e190e0d0c060c030504030506130c08010605180c0705060103050309010815 77
    0x2c108540114a4881c05003110b0704c02c8500120103000c2007483c03100c8580c1d003a000380d903001100d44010415040c08000203c050200d940010450a11554034103907510348a0045509100034403401c0001980104140c0303004010f149410350799035940b42444509101300303008041d8980940541048025000a80c150007164420010948441a0f8a044070403010262440d0f84c40300003009400d0b1010010050754004d080600c054103007400910700702429501c401c0d8070041c1ca5030304012518500030002d90b0801c00142e010b08000c2c1c1d84248000316003072810100d03400c03100d480a010a481ca80c4046809540291009a40303816106100b4136080000001103c50001e00c2c0050341c142c1485003512602c4200341c4140300f420100e04140d203982c2c80d241000002c480380365503843e40020501c00d01c01d08404820041607000003c111160402c2d0106607031645040c8004100b1200300c000c111040074130002c8890360b941080940301256140e1900035102d501c41294640001d6000012030090006e044410024990 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 194644316 1250 194643066 194643103
    0x220501021c08150105070b0414010b0a05060d050c0405040608030d06050f0604060e13091b1712030402130c05030a230402040c202b020703031107151d03 67
    0x2036030326807403c001151030311082c100a0148810b0000940c0409002e000c0c501c1502c5107118055403203103085c2150341e00c0602620803014840c0402050300c0f0300084030ba18180701c030700109050b0386400c2403d0a900c6a540810780191034244002540701000c07014000c0320070036000074001256030384104000c2c00d80c3c1034036080e44490208800c22000d800380c400346a642c0070250500c2d0090010b00c2d4041c0031038508260940c1c031400881c642103810b80c4a403040d000605004070707849030440c2c01d01c40303821b5480c0c0d2012038043c0700c410000045010341d42c1c3c110600e01e666413400d0081c0420070303040b0030041860300207903204615503040501e01c40c5214000c1501a4a0342120341d00105140e403141c082102400e13110308820248030740d42802454140d00c86480304030310a007410003003003188000d035060026100c0840c40c10604120100e410b182403a808285103003240d80624107200c01c071011041c49418a0342541c40b01d05080707010800b1040d0702d0f03040ba44c0c400302c401c80300143c2182401140b041c142c03200c054840403403d504 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 194645566 1250 194644316 194644321
    0x2a06100f050d021f020a06060f0e09011407030e160303020c010f0c0503030604051302130b12190807150606020604060e060f0105120309090901050406200901080c220501021c08 77
    0x7070a013000070074000c0c400e1044603005091516494100d5155030031050f04c1c4603042d1002c2c031045041e00c6039950003209100003003111502298000b0a001d0001d00a5401c142c0c4071004107441c88020001414200c0000500aa203250381c1d145c06541c07030000704101804100d51016035503071240500d81c1041c401c0c2c1c2000166195503213200800008110051085041210030411540540c862480344901c1c1d928130140051140540c1042040f01c3d51085094212640001c030681c00e0880f81452a03800b043c1d00043d141d440b01d020b454207901d2155008980141c0c54549440040c2c2e0310750020b9018011401511b00b000b001c0d44a0111a80b280e0080b04c8100003001d940004202d80e04216810030801103114041d40e0070210380c1000154504c805482c2003005a44504c240403e00c1070b0351003280814900031000c0ba01081002004141c1784c001c440d03455050190b1840040ca10004040c1200c10b00c00126207400d070344024000c02c1c15503810280c050300340144a4111520511694280382071490301c51078482c0c80c0390380d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 194646816 1250 194645566 194645599
    0x18060e0c03040c033e010e060c0703080307051228050f1303020304090e1006050604060f03020c0a02040615030509010b0105090402211018112a06100f050d02 69
    0x51240400701410380401d0740183d001054a005c039400855003040b001d0318541d40c0001031801c0340c003c0340307180b045c01d0170000400541c0c1c0004d1a4400c40350302840b090307200e5840c094140c800e40522020003102940030002c0040b09440d08050a000407565920ba070768410004000c9021100304448101d10700c640c080108481e0b42030082040c520902c01e104580c40d19445040c90320545207800314441003075120052103409c4070442d0103404040d100a541d0781341441d00e13191000b0055100c2c07001050034541d0000d080107a4400c14401340c640d682d00a401840f5190744c5081e001d1104400480c008002440c01d00400c1c40700406014940071504140d42d024140201c1c0e00800000b5070122641460007522a10103200502001c260940b20b940143c2800c0462071600d001340c950307000c0142000e00162725000441411224107025101440490746802d681d824180c05140c1034141c501c90220154032685040001c900303107548240c01912510700d024103000c0c4c0c1e140c0502400014946001303505c09407010300400003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 194648066 1250 194646816 194646833
    0x6010b070809090421050c0f030f0702060a09081603020103050a0603031416061104180e03030103060513050703050c0a050108160309080d02040b3c0306010918060e0c03040c03 77
    0xd00404200d010f0340716030b150710f0500464201c4024041000402d408847d01c0301031281903068825400038520b042114042445c15101340d1a00a00c0303043c0111701030f503100c0c1c0300d00560005841e04008680410040011030414101c151008038006410f000020380540d50300d0003900102da9041e25031200800c1080910360980e008041d6804101c9210044e4002090241c082d2075a285003141c6d846980302d044c1000c00301c2041d00c0354030440105003400a5516a5000082281d044a030081e03000281a250200ca507030110307100e55030141a03481001e0020041c08800b08120000703020803140241680c0c2c0d50001274986001c00c076146da02e03101101b0764a614103402a00308517061807013441242d05c4c02c0c908240c01e00407600030f900f09224414021039603804400385110303d001c03540304010f00c0c9048a03440d1582c1c0701e40fa02041c2008025884003001203845a4000d0031004007903c582e01d240e1042408804294000300000d1058134940400c180c082010301c1c00c514101d9018a030003044c0ca051007410750311b50882 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 194649316 1250 194648066 194648071
    0x1d10021c140f0c0c100603030801060504030b010509040809131a0f0d0f050102070b1302040507141606020f07110301050a020c100c141603031109030a02010804021801031406010b07080909 82
    0x3c900010464258058024000044400c2c0c44980002e080c5003142801000301e03005812100500c20100401d00124a181000700d0440e502100e000d105559030380341c0a0900c2c0510f4a1407038102c0102001d007080d181d9150410500f01136501006101d2501401c00c121064611920541d00014001c0004001c6614000340740d000302d0250300090f1601d801030341d904602d00e0b03007110010010040b44081408600d0075000302d60b0010491700d001c50704055418910705003441400600054401c005604601b0003003540c044c0c0e42303641c070300719400307500c0d08002c1c1004070700d10301c0305004d1610035483c150002d40c554405100303950038034050800502243d0b0360044244000c200007d090411300a0300380b4841105a9507000620f861000c03441c900c010045140780c041c0030f44aa00c00820601700301805002c2c001e8800203207110b2455024038141304a9102c82c00400d00140003c0f14a0f100500340030001310600c50740d2071140082c1c020000c119031448e030703a41c04400018003d0040060036000700304101c0c5110300d0200c952a4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 194650566 1250 194649316 194649331
    0x6061f081308041701110a091503140109200703210603050604030c050c0a05090a09080408030c031b03120c030405030c0a1104060f15031d10021c140f 66
    0x500c411050b8540102d160001d500009030148407460b4130b0310800c804e000350400401226103050605404881c080c0c4100c42c030380100c901e01e900340b032400f1200f10300c01d0f0001f481d0b00e8100c0d031151074256102d444a60142c00c0f03002c101c02d4a5500c0107030031050510002d04445099405566a001003140d2016110082d15054007074188a500d450010001c200140040ba004900c00d4451000303804140c5081c03800e00c140010342d03030b118071a0807000300150384844003016403000040740b00240e09000f51070001d406008980007039a40d4480482d50410b010000002005500745200d03001280004104807940e40b403103101315186442d0821004100a00754601c00b079030f0014844c00959040c07880c810317a56440c0c10720303500041c2e8120680d4412254030381854800c050140280002d40100c46040403680500c14006280200815540700c0304601301c05000003428552002030010b40f036108201180030b0000e0340001c201c0729801140007801c07000d012902e103c0c034450f200c0341c0c5481c52680d5035003500403441520024803d4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 194651816 1250 194650566 194650591
    0x140904020111010e06040209060915060a11070b0909100819020f0d11090903070b04080310050a0b03010806181005100b0403050a1406060102030711011e0302090306061f08 75
    0x42c001c00900b8003aa41d00b00940e20002c0a8602d403500401001c40e8000d4469030003850010203010f08204945400c03c50541c058841541ea002c20040c100c4010b11840c0c00c03000030340a030590125030780c2a81e500074102c0740c00032500c00314681c40f40e8a1506104400344070b02001503109452010b0358040041d024155540010030b0b10319200e41030300205145004c080c0382112006480d040492440c40d09402d07407a000b9540c4001141803901c182e980800702c02029102030800c03007010000400006040c03400901500020b0b1480050729540c401e0100c00d600280911082d9008e644002a1054651001c0c046c42c4030141300181130b00007418904100a01000e000c9040d19014800040b85010041e401000114415001007080701c06905240d404d0151036501c04501c0e400040511501c4da03030000a4401264002e44034001030810240140c03003209040b2504441003024001182ca00780d01540a4030f0f6607403065054440d5680d8290030070001b09104410f100c203e0507001c46d000009441080f40729801019a000c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 194653066 1250 194651816 194651837
    0x190e07020601150f0302071a090106090b030a0312090602190201060617010b030414030309030c0c0402033c0403030501090e0a0c0b0c03070203011817070503070303020a0216141503011409040201 85
    0x3c1c0560194164041c850504248c003e00003608400d01c9920b004245c413100070488401d0280020343c0311142c00300e0107410031070488012901c0300d0b410307880f60302c5845c0d10910865407100c009080c607085104070502d50002d5440c268002680b54041d100840403c260808440b9941c1e0806d40c030061942c00c06001500c1601000f06a003102c03550400007107000320100002507071aa00050280381c9099020f142d91b0380103900500520002e030324680e4000c42d036003103e509845041c02c0010306400c00750808025440181e52480b091106154140c0d02090580307081d1601800710040f104c501d203648908102c0001c03e181c0d4007500400413000760b200a0410950b501041d20300e40405a00002d00750b6000182070b11404d034414607580b00b0401a81d031103200c0c0181c0c44460a0800c022615500d8490041c1d001c06018143c00044410104d8400d211905c000c2109000454800d070b1185400c005402c807045070310f8091031507030048551903403ea80a882c101d414000440131b1003410f0400340030707280d080034100f2418002c10401 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 194654316 1250 194653066 194653073
    0x5061b060c0c120f0405040c051314100503060f060309160e3c0a0b0d061b020a020f040c05070c080606010306061427190e07020601150f030207 63
    0x314600444910080340e44824581282c07600384440825920002101001020044411142070340d00300c078001c88000980c481c1c604000e4500d80314201d42c0400110407180c01145445c10440d43e01224081514086002844280700f030b01d02e0300c000d68206600085075100e1010a1410800456218000d803080c0c458211200322241041e051a420010300f4600d403c00b0001c02d014100035048110f50039100720044040c1440e0a0303031404500103140254040880d002944007181504040c2d0f0402004d4900d074000c030b02c01e040110040070080401c1e441c0d40119200d8070b481a200050070000b2907001002620070400090401c001042c4042d881014411b0520050002c118071841c10070003440b240c0090405458100f0004003150f2580d0404402d114005096054059007102179814084204011f162803101d2240c040000700a0507260a41c0864030003035916141d0303421416201200e000d910100f109031500d02d01079803104802d00944d607c000c40e2990b030002035441000301e40c801c4822820014503100c0d0390348 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 194655566 1250 194654316 194654323
    0xc060b0a170a060e2122031101030614010e0d020d2f0d0b010e070e0301060f06020c04020c030724020d0b0112090804060f03020f04081e0105040203030405061b 70
    0x600542a40c10001c50700083c800640586110410403d000d403d6081a01640002010f4554140014440082002110341d1800c40d020780400350001c480000d080e03500c2c503000c603841120034060342c0000d00700b000014860449030340307091003084140c5503180740411101c03d0140e42a603204c2d041c0e9104222a054001148590310384d50480c01c45059820034a800d15440321160030489240c00d07005028159036030740802c0e40000c131103064039010f4803206050b4403211002c85d00309200c8440c00c2c3d45546041400a00c081a07903445004a03038068081c0d8200c260140708001c01c902071004001f495030400c00c840b4000031007107050200085d444c1c08410701004802d101d500200c3c1c0144200d42042a038620100880e581c0000101d02d01e46081042400705d00d1055851451a014600c12030003413089480c58103440e076000e50103840401460011180d207d079541c02178103503100520f2602400680e54503410503520340d01030140c98419500940150b00d41807808c8103002242c1d020400805c0526000d0010000b40282030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 194656816 1250 194655566 194655599
    0x504030f0b0f010b0f27030708061503030301030f02040c140310140603060d030e0a12060219090608040803040c0509040302060402131401030b06011403070801080106050f010c060b0a 80
    0x40d80e00340c2152820700d076010001801070f0480c410708181404084075222041c42262035540300b406c441704042d0103c64000601c00410810740764140140030b8042000c90002403254401c0080221381c02e88140c1107010b1640700e21080c00090040107000d160b80340942842d401008400c041c6141221114001401d4010b80d6081510103c1e20160190010804a580b003100d141c070981d422103c0030b186050140024008001e600350040600c041c200c442d511943d106185140103150001d00304d0460420307032401100079400700c02442d09110f01c941d12040000d00c00d528503000d90b00b9503140d462064465072264820354000910441d1501d500030400729a585804480e90b0159200f900200b0305818039104200303032400d04d0034196211a02e4010b4402541c82c842d418241140e030411180034031501c0d080d00484088d18100345c4914031180000512800350b500624140c125801c030002080080c1d00c0300c0422200010b100102030020f14180140c05c0800c00c254440d101445c2d008000140b1203585589264005815 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 194658066 1250 194656816 194656823
    0x1518070909020112050601170c040b0f04030c0605070b0a0506130608150f060f09061302160c05030d12150302030f0705010905040b100804060906110304061d030d0207030504030f 78
    0x1241d1001c0219600440180c001e41034a00041c496442c00c0c100003807006800e135a125810a1a01003c0703a00d50844108503406426440c07400c694440305038071242d03681ea00511040314095410306002070041c0c0310301d05030b440c05ca078400444a41900d880000502400d0045d28031544249403060522864203035205000c02441d11201604003418812500403480d02c005099504403036203407081004a944900411501c0107007101d03100019214040490001e01e240b41070a0110f42c400251161254241030180290600c1980202c1c030450b101d0052640316042c24440f540450b5503520b1164074882240c10540c050052003181c074280c15502e8002910b401208545112650080d401c24056075a2103043c0c00054074066405002d81e008910100c0c0f1a80c5c60346c6040410000d046021508100183e046001c40642003202800175019040100803168401c0e502100e00314644900000001c6a0144a91072411464042c6080101103582d50001e584400821010481c0402012001400c01604a90950301 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 194659316 1250 194658066 194658071
    0xc07141e0c03010606020d180509040825230309131a0301020405090604110c0109080a0318030c08030705040e0108061e010e0c0d020409050412020c010c020315180709 73
    0x110303440c00390401d04203500c03650107a41011414084140c001510040c4140585818590a034040071448000038282d000240e100e203403407051101b40003200c8082c000c0702040340c000780e1071031082074088400d00c20740c528000d1560510b102c071117000000c11214001451061400c1d6850030300c22a001504004400900040c001d035600c000c21505140b19401c80304402082d8001c6141c1401c1800140001d03400034051807086484116091125a60f5401d5404986a4000a02c081c2a0903e00440c1640110708102e0000c0e00d0017010303141c3c02d41c06180300c00d94181c042d103030081c805001c0c0e00c030301341c1c982d0006005505108040100003070750820141d049008040840c0a01080c0c2445800d0351075202c2d403141014150304581c80103001c0c4c0f00440d170072144c1080340a103400d07a44403415040e90019000d0b9900c40442c117071400302040140107681602003440c0c8110b600340c0b0204482e58005640c01008171401a4041c0d002e10180000071080600203a0002c200b20140480c40380100d60310351800703810b0781104000700d8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 194660566 1250 194659316 194659363
    0xe0d2610081f0507091212020c13090201030b04020f2d04090608060f271207081c0213170a0f0c030b0f0105060a0c14070f05090109050402090c0714 65
    0x2010f44107041e0007102d245000b0404a00c1e00c11618600440500c001d0310710601c8510f540c00840c020882c00e4040000a40031070003040c003e003081b8000700444a42030b40800d0401d01d40440c130b4030b043e1003280c0102c2c0003024a241401c01060300346030b400a0144d0100f0507100c40304020022460f5110240004010b500b1022401c4c904220203641400800b03440341e00c0d5a020041408a21481c43c040010107034000800d42d1120781031040868a4a0400c011041160382d001403070005011401d00100076120200300d407407602e03124401d500c40c100d12030407032902c4c2c485014000600200b91507641c103524208208040707400c60f03446074841001c052500c0c9002c448440c580c4408000b00560318513555481025203007596a1503151001043d950310591040d00c00300554115914108100740c090300740708002e124112203699444100101e00041e00340101d91182c0d02c0701000080301443c40c0142840b8590281c042c10250b155000510841d070031003c03003100c4036140b2200300d0320701c0b0b00100040006c200001161041c004c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 194661816 1250 194660566 194660623
    0x215030a09020a0f14040b06071b12060615020d050405040f020903010204080715080105030c100519081008010e0c09040510050702030a09080109050a0b1009020d0e0d261008 76
    0x2c0560002c414040c5003040d0306604031ba681d41c01071b10701403500a80810111240e0a0402c5400c801981021210710bd085e03a0704000d000c0e542d413200c01942c400c1000b0103981d8601c10b0f400d0742e44c0d0720b09952013400183c00704018411401c09400c10380860100d44405410011900300182c01c4ea0007541040d400c65115080c200028204003800b8110f4101a04140d800c41d4101008662038150180410f4011400e40120300c09280c41902261108040d5451000c0d21521502d0024128041940d2075112040c1030b03440461041d034180b042c17202545603200188000382d403200c1170120802d80144140d555000340b860b8001004018001e480c480d000960145076120354101028219180a80240c192a858090b510000480005510307000c1500310303841d080d007581d82010311007105010b604001c04545c004108400c46070b900340c01074699004154191002e85050070f5003294030680c200c50410005c80b410300c00380c200180c0300d0b007410740048052132105600c545460b0145e1600c400d100f199084038004114a40d41d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 194663066 1250 194661816 194661839
    0x1603060b010801050d050d0c0f06051f08010608100c020102040506040e100e040f03030504110a0602030c21040b090604121a010f06020c01030b180412080906040215030a09020a0f 78
    0x3d401d0032185c402a0342102e45400d6694400e10218400b1f05c00700030404030a22114280f50101182e0020013884a481c01880d8901e000300d031210101401d00ca04603000c1664103040c0079100641e51264014442c440d00700201c080503005d81c01000007175560800004c034103921000000d0020b0a020030300c48009007080394503c1507103503159000d031600045500c244400170303140320301c404d2400e501482c000c52540c6444c24516031000310b0326112580b10000d140008bd0154002c00035209040f030000681d420300da0f40006801c040140000d0006803844100814840811003d015100002c1d02800f403a04250300c03041030800c04d2507406400c1e150b07402e01144a039000040031410034098060b0040c101041441e210313020b5a201071030456241850744036100407056844100c550500e400b000716000325a418a8101941c1c0d44001c0c2c032180c0e000901a00c001000c4600001e162401981d010b032082ca003c000f08081403c9580001c0c0162907240d86078000740001d81d0384d840340d0f0000781104c00040b500d001d00c0c14207000c91 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 194664316 1250 194663066 194663069
    0x90903080711030a0f030c11011514090108060601110709110711010f0f1d06030a050405070e0601091a0c0616090801060e04020f0a03060f1a091015021603060b010801 73
    0x28540c2c02080368841c4e955200d88090041091400c000c50002c038405010381d00e03501080c0d070b01e8050b580303815827500110f00320440d59000c60321a0110104104c1121060181481c005d0050050b0380c5c1c0310201003a80303075100d0031074901048031420a446000341c84100110a441e02c03107005801080001c110081400307a12654403130b4541d030900780036103450314080000d0583c0480c040584240400c1500d51051403140080f000d0048000404040d80c070301c0e00148500050905680c180e17198454641d0100e513910b0b502c0d2003140540c0c0c058682c01065482e05000780d407121207031100241c90315000e0220750b088541c1007083c103011741500480c40c2d48500211800600100c81703076019a02c07036070606000708070140d55140c94640294064406005002990001c0780d032560055100414480c58442000840000343d400300324400700340d04000c49410402000c200d13003000d098640303003508003206408200288030b65007480c200403042d0056941501c1244101068516a644107031005501ca0101280a680c026107076030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 194665566 1250 194664316 194664347
    0x1090b07020a0b0105040506030a020909160f082104120b010302010f0215150105070203100609050a05071e0306050d08030910050c04060503090106030c120606050f0102030d05100909030807 83
    0x140c04542c54854940794501881468000d9603038401140581d2024030880c03181907009840002c1a0070501d510076034810b0380e0101603156211140001c00d80c403020480920864403924020600602c0b401403003810304010012080c0000700400c4001090688240e801007800e000782203001e540d614500000d00901c40401c1a80d0464000800405030003048121881c1c00240900203458807a0485005892503c10144041c1d410302c0354208080380001d05030400303020b89480b59001d001036180c82c2c843e84203a41055443c0300c0806c3d00407c1c6445020410b4100034080580d900d00410090f50b00c0010844011b20b0f2070043e41d004100004002a041e010403110942c8264840d04000303526000f1494045030050303001d10010403000101186071a2001d4010101a541145400200799038503500e1949020104004442c06070402c5000034062900038a070551954041e00998075000070042d40d2001410010540480b4000015000c0303641200c5100b600840b61190700c9068030b5040c041009400769002e0f11090307 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 194666816 1250 194665566 194665573
    0x108060301062312030c06010918020105070303090c0306020a111e0703020d03051e090405150a210b090f060903070f0b07121103010609050409110f030a0b0103030201090b0702 77
    0x401c050861030018501901c0810070940c0c1c00010f8030005160100441c03100b8001c0d100102e1700884540d008900141256010017080158201e400384816000d400309001901141c2c01780414004607000350803d80000e40303d0380c00c841c1521744075503800c0d003240c11075104000001c9040c440301000c02c008001c00340241d0912050691911221061141d80c1ea00d24000280643c3d81c18104a00b018054015140011588807510686480300c2003200300c550405080907201d00d0401c000703c2c101d1110b0614038440ca280107404c00c4009410901c80040c4d070503c0203108038008003c1841600841e400d54056030040409401a02c07200c1e80c498520b40c03400102911040640c4c004109040014050b2280c1e005501e900c900048016910004c05075100d00d42d40c450281c200c0d08008100d60380c414039100450681c1c0260711820801c5444006000841e0311581b802400d1005030b2842c442646400c804040680d5001802c5642404d10790341c420400200130b0703000310090303916070f080d00c802c201e681c000c03480e8840042d2004 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 194668066 1250 194666816 194666819
    0x503070c0b010b1b121905071a060a090c1e0e04090b100501050a0c030c020d0b131b0605220302060c01270506040210021015090f11071205040e15010806030106 70
    0xb03140003403044c841da184401440942c940655030240098a02c0c00c9e4020707100c0d051101d5070700750308041300e08115a00d0344148403400740400c0c1c80036144291400545607503100725441040c1c001c4008040c10000402c411312100040c40c0030150340e0f1b03020b0742e04560b01c80e480001c00e504100200d00d00781400741d04914140f0009008400c2c81d0b66105021040c02e640500d400140e80302c19002180d0564100301001d04841c00f0303101007005a00050082d258000e01c241d0040c2c3c0043d0716204103100c2d1503040d00411001480c2040303103041d101115054200e00c54450b05150042c1d903540e0b40040d1203540007207904074281e510382c1a02442c1c2c1400810f803080311410609500030441c0641d451649840004100074490f1011080b00340c4124400c1000d4800080340d0b2004100107881c2141e40c1c0b83c5070300d4a101741d030303056405c111f4805410341241c016510000b1039080040c1c02e00b071095991611004864050204008043c800000e240c1c40d00c070681c80c05110045c40a0030b4965030800010980c0c01c4c018903190003603040290 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 194669316 1250 194668066 194668093
    0xa1211120f0703020a060c0506040305130f0902071209120201030908040915030c09090f12140315031603050304060f050702061c0c0c0c0501050d0b040905070503101b0503070c0b010b1b 81
    0xc2740d81d4002d506103031441c0e5402991000700448112900101501002440046845d40681c4d0081410303034064140c042845581040c2101d80b005c0c5c0380290b48214001094000c01540282c02220840707105100c00c1d4201900d801d82601160a0501c1084c07400f1107400013002440b4503850704001500b0000002c1c00002030b02c0d114400c01050340c81e03000b000c081c190104500c45502c140400e01480581c0c40e01e056032814507401028003440754a0580707210707008040350003082c440c8820418044a5020024505061030000152840b8042640500622a041119900603907600009180c0305107004280940c1c0d1655400b010103d404552a9005200700c85103100d010408040100c2c044503030900c0c0c003d81c1c032440075440b107002c2e004070481c141c0c0003030a0613150030030050007080d00800e0721000e504031041c0c00c3c24981000142e829103c2600f44400f6010001f500c01440303200103551041c12410440030800441d070707804103851400d0703029802002020940d800030b8000b01a0a084200c07002000300403480c180310 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 194670566 1250 194669316 194669323
    0x80106080f04080901030219030b10080f04031b08040e0109050a020a09090c03020d090b041115180604120501051b070308060d110607031106060a1211120f0703020a060c05 75
    0x1800070f0148800850070400326880b03901100d10300030b0007036078501c801d0b03030501c1019001d0004d00c00168443c020045c050003a039072091211a20809201e0040c0d103894640f41c07010313503a120075140075281c2d41c010f058941000c1542d4400520061030002c140756040d61404110200f2500c01810b12480603004000761044140c0c021040d0003955603070040011100790b49142a0024410b843d4240707182414913070240c1c00e0200300d00b42c01c0d00c01ea001d1100040824454001c114040071186c40000da0418144042c080f040409042c84c6034441026000600e400c0c1ca805e080421404100c02c1110b00d40c2d12203040010b5070140c2c0015209540b01c2d0407002d41881c0d175660b4080c00803000208250b01903a960b600c0b030302c240502041c00025411026000742d680c0d650798240240040381d01c0304804d11600c160400325420741004c05804044800c074040000114000e80d86030501e00350184a4654410130403440c0d1030283c0400e0104920441d0341c2030040580520310300c1400020141c07503000703000340540300e24514082100030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 194671816 1250 194670566 194670571
    0xf15010509190b03121206090402010c110a030f05030309010605010203030106020322170f06010b070f0809040e030d06031707050d050f040308120f1003030509010e130908030106080106080f 83
    0x494140031441998804030000d00c405030941380c0c580f1803440702ca600c064500000700240400c010030b00286a60303010034060540c006840003800600c01d04110b4002c20080c1400300c1130802d0007404e00daa44c0d5540c2c3c03a07801c8907080d004070543d0107030800030500122000034440c04c00240030a0000d5429585040e20203910f034001c00da2120aa100f225500c541d01c40180745c83e21000d0021109404154840e501140355120758034000d01c2070b2441074500218003000c1e0032003500c1c3d106a100f806d5160021081d6aa2091500003915203904035890740c05c401e05101092000d8046424118400100c0c40e00d1803d007002240460350015400c85010850980810000f26403403039811598100540d540040011000c1076104607413000d0040040820030000d00d44407807410764000c41d000560706241c1e4482404000880110f444001c0200e1010001031560394015604144500002454040701501907803601043e50680c0d00100c4941c0c40000052013841e0b00b10182ca40500001d00d08040c0900e000c004040b03000344e01 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 194673066 1250 194671816 194671831
    0xa02100309061e020c07081c030207031808010b040b011b02091329061002210409230702071d0a06031407031119050603040609020904050f15010509 65
    0x101d020300800d000035070300700800c18590003400c003074151001d22140000b50402c0071040e007280100c01001500d920009a0076048d401031a00e841e1018442c120290003c1d03014080880a112030040e01e07059810800c0301c0c085c02000002c002103140d00142080100b00c41c20802100e041c030146a00c04100c011a000c1120360300c0c0e80c15034107244562940e5640c0ca0800039643c4000305880c06407200e4064a2911044404000318000e864480325101d80040214040b000041d1000503407000d900216510b41040309014400000000e4501e0326448071610070a8418584120307c2007400c1c2412200840381d03640c9025030003641da20242039a181410610303030601440d100c2d00d051064051010510452469111a0040d5808038069402c110083c0300b136511841188401d071a0f038072450905549508002c000209034210020080d5840303070a100400c6400c0c0c001410907a40b01d80e995182c000141c9880d0350b1540502e00840c01002a1401d01c0078252078040c0a04040001100c08070040140c0d8444840700c2ea00300c02e0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 194674316 1250 194673066 194673071
    0x6080604050a2408011805100c0e210c04020306100302031b0304030e01141c020313060204180605060702060a08040501270311070f061d10090806090a021003 69
    0x110b9500c1c06000d400300c80d105000c50b4034034031984203d1002e0804080112990760000f80716141006100e03c01148034010080c115402c4034928540e080e905501113030305a050b506103001100600c00c0400ea00b40c0740090528400740d82040d2461a40d1130030004a401c8820484082d0b16501d80140410005090405040c2c145a00032020800c010318224507000050a0095220f89a140c141802800e00802000c02030214007991401000100380344e08a40c0c1c41c90021028403c850a4841c144d030083d03100030300b0b00c80101e441c01c2030740c000035070907000502c01445060b1811043c0c2800e4000e40b002c48410b03501c400d110f004204454001a06c0300000c0d10700c40300131400c2002042d80c5505203e400b42800c070101c4403c1d03580f01c0107030303c440000040ca2051480c0c029951880701805000d501a9990010301a01c203c60b5444801000001d1003009440d00c000420f14540891054042c00720f82241d0700180c0b581e01160b007010080c0580d041c00c019442d448080c0b54000c0246c4030300c54010031800401121900201034 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 194675566 1250 194674316 194674321
    0x100501080a0f06020403081c0f09210e040603050102030f010b07030801050d0f020406060504140607051207080c010203070e12060f06041d0f1501150203030601030213050907090306050c040608060405 87
    0x3c0e10b0341070b10300a40d04580910b0343c1e00c0d5132000180d90b82d034a400c0f9000200c1c0c40d0001000c01443c10303105403171210754002581504c00c40080001818041d82c03441d400c0c104509040f0920720307074071a401600000c500c03e1002580300d050520411460f810144c02007035413520f013032042c3c101095001c04c03140d045881c29140d00080310f041e0b04104d50100e560b240c01a400a0900340c00150b829400001001100d010704281c44140c1031110400c00c09100301c5a003d40341c1c5d0302c5400c080c0e454080001c002d0146500c2a04400d2401c0300742e46030942aa081180c013000444c1d1214515880b0381810803e9611400102001d42480c0c94040718000d101c81c005001940038a40d10304c010452aa03402c00019100c030b103098110f803046802540305c0381d0b03106010b014010510850301c1c0001000700c0d41211081c03000c4030a801840c00c5644540044000350406c2d4908000801c2c1c0e0480010b164030390218444c00b500595440b0a009030031410000152480034003113408484003044100002544108551b81001044070f0103f102e4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 194676816 1250 194675566 194675573
    0x51002060c0307030b1018050402040e040803330a0e013204141e04020105040303081f0303020307052107060b060d02030f040c080c090403080603011b030e100501080a0f 74
    0xc080c1104441d82003001203c188481d03980041f101015040c1c6010b00d0018580c40f0f205000681c0143c2c0310700c03c2c005450401050014082102035503000c018580c44640c1218102882c62059049141240303080781d00c05429040303801c00d2490440078210200c0f8000c400d514241c1c400c41d00741402c03c0c2c0355142c521001512000e600c440070740765140703010052080c040c00840038500202644143c070902d190102c203640c1021817541405042c0d00c6680c0503182d0909040c41c64409944c0350a004103140b00d091030b0ad9035400780a11940140f031001c1c1d4080e40c001c58982c48140f42151500a040040358822026244000403000040c02190801944050081501c1e81c015000c11042d004044003000502d00100c100541c190884240f18071440c00f400180d2100707590f8041d1103031200e00c0381c902260000d00304400a00480d00405031140c000c0e85c0038000091900e201d200030ba50b414403501c904030006e07458aa01d0201040d081114403401e501101c0104203a51421007603d42e01d6910b501c0c02042d44000481c00d0051 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 194678066 1250 194676816 194676821
    0xb060d020f220c050d15030201050a080705070203030a08041103060f0c1b0d0f09060302040602030301090902030a150b040b031906090c0b030103080d050106030911090a020409020f0a09051002060c030703 89
    0x20503000600788a103c0108a0203882901300104070744060345040041041c0041c100140c0d012241c0684a240ca0b010f40032030101d500484c002c202e40241301c4c04111010040e01c04000401002c0d15959445125003801e18064820f000d8a40703e030351080c0e20840a019060317030b02c0c0401a4100a401402c02c0c1e848000d070f401600b0170a41040c500301c5c6400707240b0180d1051130f013058680c42140729a03900d0325842900c801d07058040f8016809100c00613401031005100c2500554000d03501c06000404031005090307256241d011920300d610807800b81135104d0300420b110b1305045c0155580342c02c04030041c01c0030503d01202d1841c0c05a2441000c0e10454440c0702c80024800c1d850303100c2029042c00480c096981d078403418081c201d0781c00850b00d082c40c24a40b800000c1e009200348a20802030750f001100c03200c1d4218003000c0000b16030016059015841e4200300001e080714403480245201c0319003104482c0c40f0710250310003034007003d0b0750351040340a00c0800d0b010598607540031440992241d0b02c03441490300ca8541c04001c800 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 194679316 1250 194678066 194678119
    0x9090c170a05030d0b030d08010609050603060604051e01030e01090506040f021c0807051b09042a0905010f09050403050f130b03010815090715080405160b04030b060d020f 75
    0x864040004e900c2070301191600a2484805c0c180c00b20b4052444a64017191200c9092041400058001c4418071080c60020021500200018582d604064441c000038025009140c0c0684132407415034444803a13560940603000101500000800c4007070181d4590b03a440b440e0081009094064079109141150340c1d0071210120800d85510300c0645a01c14540080c1c0c50340608402d4440b441006404481010201e19480304410050910b4140f52105c0d61400e21200610100201c3c0c8401d6080a407481030240c45401700901341c0a20105565141460a4454040a81048082c60b00b40b03000c00011a40120803580c0d203201600d5490742c1c503a003541c8030a4410105400201503078100000000700408005940e11400020405002c2140c0722002100d54507403180c4503101d444481e0740401200d95004a001540c014014015148440b0030400e410b11520304940020114880c0410103100780300c14612001d41c441c40c180c0d010804640381d42c000452074401e5421146c4103c04c1005d110120072460403c425 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 194680566 1250 194679316 194679323
    0xa020c0109050f0c030327010c0503030a09061a01050301120f0507031a13030f03090c050d03020d0f03140c070204090f2006040f06050a1e0801060909090c170a 70
    0x80756007060302c0c080303849400560844406102c0d039008903d261034003208554540340c1d0314441c9200c040900f80403174090545c45868038140484c00901401064081c0015489035400303440c0000e85002d00d140c001c003114804101500c40400d0070402d0101c50360000700701d0341500c1c00c03100703c08641922443e00003269288404021305d0f0f801003031400000c00000800100342120002240041e6503100b47c10102460700b080c0e000f60000701c01c1613442ca0b07418020b51040e02568000c81c22034071244c1d21100032400203540c4600440060f4410319a5440036a07000e419600e200500b480c040c000342c042c01084024000c40585802505040000c06800b156a160b02091080360700c00c09074040400d040c03c040c01480c24a000718107400f0108410410780c0c1c503240040310b09480242030055029820040f08483e1038000c0d080d1384081c080560b5502d191000d03848804810089650340305c890300d42c100b400c0113010303182c564080032949051107039640020303008a045174180c50300c00c082d02d81d032001482105803500c0418180036 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 194681816 1250 194680566 194680571
    0x2070b18031b0102180301020702030a020114070219030b0c0f030402010e01030f0f0501030605180a060e0f0304080106031101030203090a060507140c10050106020604030f0f0e060307050c10020c03120a020c01 91
    0xc1d510602c190060900d0265249108a1030404501410700381d110b2007034020746c99000110040019800b403144880740f41c112120752404d10b4800c2d404581350000208100a9902c5201810820007580900082e40201c0d601543e506021248014884030700001e04020305001c0d03140983c20135039109034040703046600c03400024408491b007480300c90700a00003030000350ba01909160018040c5144141d0044800c00c0b104028010004241c80d1f090085c45c06401e1513070319024020034078485800400140010b4120f0000000d0039501c2c5150000d411520400118181070060040001c1086d000c1460729401e50484000b2030240d031003c02c110380741c00d181000d90300c001001060078100c103540092548c60405210034100004d90b00c0d00d005982d540c01c2100c0c02000a29891034021009201d41003104561089007040b0307000050303480000e0f009820403903d15000560100307508030f020000300280c41c1110700c40181103240c03010300c01c043d51700c92045485c5102c0c03080641001c81c01078941d81c0d04484c44c030413a0340000c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 194683066 1250 194681816 194681857
    0x20307061b0e04051e0606070209010b0c0610050609040c0e060a020f10020f0919090912021902130c0e03010906020c073515010e1902070b1803 63
    0x45520020450082400007a14072190981c40e052900c81c4d1070090352410220041d014910141d07441800d0b0041802c0d80000041c004480103890b01c094041c082c08885250940310a1410f602e2454508000d11069003011a00c10402103500d4284c00c4810002003038401140f1130385400000e6960540800203aa0070190008480d0a0382d07501241c070110440008013980c0f180d03d000441c110980c058061001c0c4a00001c005800c0b40e49009480d01e41131190301c690780d035080b560b6020050f00700c616142040c0c5507a2066601c21400320ba051104187c40720510b911000fa448483d00070806951880c1c48050019640e00c440c08030190040f1803881200c070000380240100d500925014001e900551b110003410710079000007142929650134003c140305070b2032400d030f5160303a0b103840b801f0403c002150007a02c0300e00030000303940340141d0f910b81203601070184418404c2c0d0328209031541418055030400c89911880c1b0501880c2c001440c410740e115040314047c0384804141c0c250b000c6490651081215220b80b01030b0490a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 194684316 1250 194683066 194683091
    0x306030a0f030e0414090337050301090501120515060d08030426040b160c181401060c0c05090903120f240303070204090c17031902070f06080702030706 67
    0x1103d404601590b0601c030301080f0071500f1941c01d405a8006860790414003a0a4101c0c0032484003145040100401d10003d180c0154030f0108402030303580314000503900000500c441a65030182a00420700c80e0500350340e078a80b584407580c49a407800d43c60000c3c16045004904171f40d9807900451081034001580d66524102460006510703059640103454516509000d07248020028060750208c41250075441d203440f0005009026222902808407406400d507280892001070070155001c0c00c1d52240c1d0001020340e0750039503180344618141d000e0801c000112803814001588900f0304070407500180c541a031075403585000380f4218054510880d04078420f02d01081904be4507400c0c03a031300654500e80f149581d401ea40a0640c00703281c01c0c07095190158001c02281e0010700b000d0b0700c14081180606450360a040d240c0050607024980c1200045151f800411040c1540b02003060300d400c180c0715800104074462800d00000000303801842071b0020300c101d03170b800145031030b009008440303009501c0007003002035036810740 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 194685566 1250 194684316 194684327
    0x4050a0b0d0b0301180f031202070503070b06040605130e1c020d0306060207151101060503010c050a0306090e0a020607030c060c1706100212070501021306032a0e060306030a0f03 78
    0x5101c64485414801c075030400e410b040c0300c0d004000705050110302d5040000d80701d0841d0309000d107100b00d0070480e40c40340764440e001845c4040d1031105d201d8809182e03148900d0600b103c424602070421071240b4908181088180d0312800d401d51001c1c001640419504040300303007241070060104196060106840302c5886042c0e01040e40410a05caa45040160b16140c6208070303070707a84032405000290b072028803071860464010102224a200e100e0300108005440b6004a820b4581c0c0720710100100d680405c8142c0101e800d401114054000036108111407440d44180a5681e00f5011020b40100c40005445042c1442082d10340c6560380c220701f05015400e007420300100b5815118500c910212030003800f0604518120f401800703c0c65196000342030305040c00c104103410b0792050307404842640d400c0042a0105002480103030051030291400103100f10a203280c91a0094540d40180010311490f0050307400ca500b04503c06a1607006480d12901c0e40c0c1d40c04046490200230303940141c41c900300308008004142e44032 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 194686816 1250 194685566 194685577
    0x3180204090614100e04082b05010f0e19020708070c03050c04060b0c0615030705030a051c020a08030c0a090503100b030f03041a0304060207200f01080c090909010204050a0b 76
    0xc0c500380383d2696030f5404608844803540948010040d0800204010840c21b0300500304402040c01c81c2c200303d5a5400c041d2038482c207200d407280b000c90b848500401049000c48030020050034007400152161402c035103101885841540391840243d030125040302071100034019a601e5951049141d07030002e40300d04001d5521400704650f0b6100c4e508188c030105118030681705a900f50f0a000c002007029848840d00d280404000e07a039026098400c441d0b00040e160380401243c3c0b07080b40205e019080804090003004006128200c3e22015540002d50040015020300101c1e54028420b015041e2510103100089600e608158000c036414032404840404800c400d5211801c5000102c048504072035040c40d07699160700651003110b80c0b81000144a0b0f12485070345000310381c02072040c9001440d001d00c50795024100c165500582a03581d2102c01c5014103410084e40b140715902003402d050500d0310380f004601017070b403146201c258081e0b41441c010408180007501a41d001c0e010050a082171075445241140e5140c121 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 194688066 1250 194686816 194686841
    0x108070807150804020d03030b101d0f010f080604110c060a0507081306090f0b070f020705031501170708010204060513051912031701120605070201050f07031802040906 74
    0x4521001401d860000000100941c0c1d03910f0b040c003c4e40d1603400b04401c01030360000c10b03002d05031141140440d641d2000000d0b00c10070400cac1c0300c54440703042d032800c1c4402c1c9944020721070b405210110b030180c00c00c1c0e070040341800d46804245803041c135903a1150f020038040c00c9686a442460301001c030f800842103201041d001d12909100e01c0422159544c0e50701110071480030342e6034624410100104402040a541140707003014000c0c5004255502e40b552070b1151410110f440c1e00004031251141026194180100c030001c2600301d00901c06074071031000c040b1881d0011700c42d61080181c113180050005d40c0920a01005008601c000c649540d900c0e90064003d07406403402800c8441c1412004c607048c605500848400c0d6a142070f0040b6590070948029046030081a043c2e0521001c0910120104e048074001406080340041d64004a40701d4540702d01542c07800752601e029641490100907000c04100c1603654406411319022070000108030320708121004c0e05001a4000d41400c01e45000e100c0c0036008408421034 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 194689316 1250 194688066 194688073
    0xd0f020d0f120f1b030e1503010303020d03050c03150d0203100606031d0c22020408030703080a090b0f0a0204180e210a0e0a0e04050d020d020c0603010e0c0f0301080708 74
    0xb20800703c540d1041c5400c84008600d02d4181510041c0107102c5844215100e410004003d00345000055401881e8400c900f45015001005208259050001c0c000902450809001d90b040c49500050302e404001d0000603036414114501c009952007000003400c0580241c00e0300c03600d038644c00015001d01400e004040200c0c0c01c00500e0920210110380a6502d03d4070355001e88800c443c01c90400c002c800500700052070301070b4130040d0781510740c0052000b480105040401195550040d2401421200300100703060029890001709101260103101c144e5449030001c0744c0c1103c9075841000e0b142c000e00907500320480072210511400c0016011f540305404540701101210320800000001001200c4c202d001203040c2c40090051107440b60042c1e030035110500d00201020f2516488031140000c05004a8096807a50b2102020210054041c0321080070001603101400100b90300601003400d40c40103200308000004500d0000315810200415500505802004141e40e56034940d03d0030b50301d0b9014069203851f0301 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 194690566 1250 194689316 194689343
    0xf0609150d15150803030106030c0e0d121101020d090506010f0305030a0c020109030b0903130f0510110a060501080d0216050f010c0501060e0a0906290d0f020d0f 71
    0xc014401103941000028000041040c1e541d440c00e0704221480c112991041c2c80b6070404448540d100000005001d28400454403580742038001002da0f0b002200d403005012240c10b55803480e41700c1016010720240c0140b400300704202c0d69103040394100c104003040d40140d48040307000410440c450308407280546c0280c1c00c8628a90f210310f8004038056042c803000700160b008200000d0554026040d401c4494014104000b403280e0340e445552445000716000e500d10341002a8000ba151800300055020f84500c01005a40d282400041031414030741d01c0005042c41215040c00020007810481d0400c4d071988980c081c8229650b44500d036075520103050740360703015015401d5120f451000101d056402c0320030081203070b90002c1c0c204005407000f005041050340c15540304e00c00452408040f1002d80c0c0248486080019440540c2c14480100c07a80700700c05150b41e0740d18a100c190501d0104200c00b6120104503012030102501786818071000c903c0c008001c3d00b250940150505119003081100840d40c000c107180724001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 194691816 1250 194690566 194690581
    0xc030606140102010e0d0206012108030f0601030c030b0303040501050f160311060906060a0315020d0615021218010e03030d060603050402130b01080c0c070902070f0515040c03021909050f0609 84
    0xd00e04900c503403006901c102c004005001a80d04035010f502c032808030102086245840b6816142d208988400e0700c0dd031684148116941d162040c4d0240311058501005030201180000c5e03200e11a42c0f19042c1000360129454140311aa0001c8800d003a01821044810020b10b20b005001b0b40003545e000d0310180240000154226400b19006200d1000286060042030960b503070720100342310101710f81070750340d81c00d000745100202d85110342005000c460a200c1081c82c0c0510300240381c44032170b0b001c003510f0480c244072403a0041241d08000e000c0c2502402c00f0a100c840b45008680303580240b05213000c0702801d0200004e0a1605030f406140164003c0d0b50740002d14100c1c40100098500030201180000c1e00c200000d0707003004060010781107500e034000584c1c46143d52103504100b640c0003801d0030788290302c0c114400800c100c0d00f080306011140c0340c00c9551010745060b48424020004a1001038000c5512010202c05801010208400340148013070404c402e090510b1100503554040351101d000b01030600116140 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 194693066 1250 194691816 194691823
    0x1216060507080304060903050d05131b0b091e0a060905090c040e070c0816050618010b03100c02010207150e0f0705131a030607110d091409040c030606140102010e 71
    0x51500844003500e90b444d15a1504020106d13944181e040100910010143c41e007039000342405038801d035504802c3c0a4032400d10150390b0301d0407084103140300b0b0850030820400085400303507a136488088a1003030416600030300b5141c3c140700c00801c46070b0081c0c2080300400c4541e002101034003590b0f0b054401d006546d48aa02954440c0300e10f025400c1660801000550310038400c40201d00e40501c0b540601d0b003070900780410822a0b0060318804c0b140e6412070300030440d020001c92402030030240c1c171000922840030500b0109407100840098507100c2a1544901ca45580c000d404680701160700400008204400780700a600420f52800703110228012440140c64003080020303502c091318001032602c8801c0c0014442c0000500c01a84411403104040503070b403459690900903280700d200d554499051544903901e40f282060401c0042c0d00c14025003140902a07001c90303440d081d00c0001d00ba5504641600e40341851044017031345901c01400c0d54108400400d0400c0e201c8428803220400b0380081c06044508010380341c4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 194694316 1250 194693066 194693077
    0x70801080a0c030f0f05011a090907030c06180e07050306040b1504170f0a0501020703020f01060b0d0e010f0501180b06180f010c14060609011d01170c12160605 70
    0x7a411182c40d0520102c1c1e441842028101d00c0b500b03500300001c2c515590300c1c4c2542c1c2c40b100000d8005038038100068003418203115175940002d804002e04459410356950000445142c01101c04104000c001c1c1040300380745451071400341c520352801802604d80300c8030041482d40120b419500590a2081c101000c0c20260030405120303500311000e9081c58100020703440d2440c10003044914078030403541b0418203c071091201c19a1540503100250307485540c2e050103490400c0c407400c1e66005038900082000310030246015120718141da040701103410b803860340301c26024240c00c19800441030b2a08000103020550f1a02c88052140110003d0104a6003501004000d004100d00000d00d01034500031079846240c610002c00c2c0000341418040400480c40c0c07201d8110010461510410380d12140034404035241100055006094041da111680401042b45034101d00040c401e2002c00d040000c003000c490b1000340300301c4c1000600588808240c40d02040210303a81d5103514a2400e01115400e00070440c2e910030303802c451 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 194695566 1250 194694316 194694323
    0x5010e010513060320070c0303140c0709020304020a080d080601080a0e0709110408060c130e090a0b090f030a1d1f120209060d02090103050606090f0f06090315070801080a 75
    0x1100341d03103403003402d13030140a40007809424114000071070000da04131107000c4c2141070700a04690360302e1030851502a10b030341c0312600c1c8103d0300b41c824031143d0300014000681005880da020b8001d80c80761503a2021480641850704540805d000c0c413120701880c103601c510018450300d0242e84038121903c0302036401c0308483c0b4200340311641d41c10252080c02200e500c1e4000002c0800941c10b0b5920380b0391748151481c189076060b03401d06020500001c070f000031291030f0040310020b000c02c0044c00c00d03103003800d51030b542e510084290020200c20041c400644805404c1c80b1840d203d810003001c2e640c0d920703601da80c02806030651074800000d80c0c9541100d00d05600f0300c500018410b0740303d1052040e801c4442c02090b2403001105050705421070b002c00c8284140d444c0d11014018043c2071500c0540c56520110001d010703035038020401c0e03000b80c1d018043c9101a41d05c40020440e401d130240c500078607803410300380461402d10800508136010701c10403403140003d04400c801244179040070382d100c0300141d80340c80c1003d444003008040907 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 194696816 1250 194695566 194695597
    0x209040c030c1d031204180f05010e01051905130207051c1403090102040906060c030e03060606090d0201030b0603041b150206070e030a0c0b19050903150424050105010e0105 76
    0x100e5019840b19062038500700004d046a20510741c03040a812103601c0360b001080825280341d03901400000c58005d21102211510041c03000e5814507031803111071181440303401e01c10030b5000e5007021114030304050400503101c09011242111080070012000e9480307020202da00f4400c09842580210102161030a02c80740e0303507500b980301420450485802e0b00b005c1c01807c03d80d5400c00000030000307210311070307a801024240c4a241503a8a2401c000d040806d0083d191406500300204000f865a1200c00315007d146080f10000a4240c40d800101c1c0140b000c0920b45420640000620050142d1b030311b440c2e16810440803040392540d440b030003100c0d00581c008640340301581c007030b102107003015000f41455407010102504442c0e540d01544c8070000d0020003540300c085401000039141ca0030030b0744421443d91400032400d00070300c1d0410240c04281d491420404800007510704c2e50106041082e00298041e000540342e04882100720310901c140e0040200707118003808505042c104460f07a501960940e091881200603070f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 194698066 1250 194696816 194696837
    0x60c360103111306020a030f05031303050c0c0d0c0317040312050706180f1e080403111c0b0613090203030306040507140d02040801050c0705122107030209040c030c 72
    0x40d000b80040030032455071103000f40443c80540e082039004100401040c0e006120a00107070802410314200315039000b0800c04c08000b00714200c00c6400e61070400c02d605241090b43c888016000e075003000c44400c1030a81c4080011b0580003030080c1c0d1700d000b900b500c1c068100b41120000c07201d8070a030b4030f2050303200042c441c888690004000a0090b409401c8c6c0502580b000f04118080d043d1440a0000c840c2c802c0700c08414000000080c013802c0310009180c0310b550000c0551045041e116102e80340124400200300740700c41c0744601896151540c0714003160000410346072504200c0c0c9003015505908854890052110b400340d18102c0301203000b0640c0c050b8000d4003844ca940c440c030060001070180244200c00740042c0f02801c000140101c1d00401c0b0425000d600183c6607403c202070781c0d00390755001e8925844c03110280400c0001c1003010460017174600d244030180395917544e1500700822000c00a1008800a100350b42000385130307a010303001403d0242c0c040f07030108885800c4050940c102e44022601f00000f40c2c07103054 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 194699316 1250 194698066 194698069
    0x2070302190c0504020d0c0f1b15020903030f0d0c08010f090c0905120c040506030f0d050a0e0d0c050301050612101a06030109061a0712050d0e060c36 66
    0xd01c850707009164500c2c1036500d50021030241d13440420080d00d090380c2d071000001c070954068429140000c2c1880c02083d200400345030341d500e46000420180030140e03408442248148a581114181c00c005800d490300c46211541d16401130b00600c0c00000719a0502540b54245441022054140c43c8100e00e440149824050070700020445c0200b500140030064a0206641c0d80c2c81d40311200541c120001096450076020610003036400142031203000394050b00d4400ca90178400308200e581c0815034070b403160300c546414800f221345402c1c4008440d04902003d04440601c080704808d00161107090380280680e448210038000c0800200a000186401c030005070004400381c0e40021000e503000032004210700ca0b081000601d20b61083e400340c520b003941e0311020448011407018003030036065036171519230900c0320949502540807010050103081180025030f00e110301715241c0c08802a14446012200c142c548044520099800f60300001c003404610702c00d0202c00c0440c004c00c003507081010442c10101150702c40 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 194700566 1250 194699316 194699353
    0x210108060402240a0f1205040b010815151002120415031406150d02091203030403020705031203010521030a0207060909020a020a06020a110609030414010e0d021002100e0a050c030102070302 83
    0x300392104002500841d074450007080d02034107001d2270181c0100348555142001441c684800011010411418101000107101040c130f400c0c0e013a8203081c0d4400c0110300821400b2800c04229020350210300b100881c003c0381e9600c0f520740d1715103d862561000c010101415250141c00801141c44a0f4020b0301800600c681c2d518000242c028080c40790030140c1000080000102d800d0440e403d40701150740080200302c14187c3c1000400c0c018003061303002c1c003241012900543c96a2005000d0a07004d407600b5807440501c07030004200c2182482e04c07503080d6521900341450007515444a40f00d00740001300411008906440c8500c21601e4034003894000300909020fa41d1035001a4000b1200101480811503d04450400a01280e845002d5200180d941c41c0c1c00c0881e20781c0b0b07175018a0303c0300341005080b050701985074030703181401002a07404032443c010080441ca400ca01d000e0710329018070111070900702c000301d044c0000120204064030030300c1a0b5600007404000c0c18201c0c02107500c040c0c0180d006205100a422628 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 194701816 1250 194700566 194700587
    0x2011b11130b040c05090a05060f0f0705030d0e030a090b0a1d06210a140c03060409061b020a03021218090c0708040605030103020f0a0515210108060402240a 69
    0x4000070850030102c20000b0b0031280c40c120f40102148000542e200b02d407502911000182c081150214100402c030914580320f03000342e0314136151303c0e00001400e00900104005036810aa440442800444048507140b500c0b9000000366501007441c400006c100d80d452141564810312459940802000c620317903d0a0402144500bda07822010400c400c41491903040d080540d80c0b40b0000c64480a814044032800031944040e040c3c0f48014030f0142445051034800302220b03013000c01114082001d0300c460900c14010300c140c1d103054400c0092900c80c10042900815101243c0d4060380a65030510044483c10b4628032581e91007148110450350b0074801480c1282030150080e640c01f00c1e0754189540c81d5540c801c00d40c8290001d8020078000302c0100214a405511002c640c8010b64218075503e18100104c0c0170310030350404074802114046925043c12414054441600d25002c40e9000d155a5801201761100720540e410b90050005448c10320f450359028200c41d0b0310100c107a0220740740000703440d0119140d0000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 194703066 1250 194701816 194701849
    0x1e1918090c0b19020f0303060315061309060506180f04060e03040f06030605040b0609010f2604060615080f04081b1f06050406050307180209030a06020702011b11 71
    0x1c049010840c000000d015005401952109007a101000d4002918150307103124410160f61040003040110380340810480540106031000510b15120b240c001040e4503084400581c515107001210014000103800140c041e20003524941c9129000150041049004a03200c41031180c0040224001807016405109890388110136641416229609038070394440030b900102c00240c641c5c0052249141c07038400d1091082003145d200340351480540029008503c4206080c2c144501d0080c00c401081409000c0f55074400c1181d0031010b2490545425030041802e800b80f1140c80b402c4100143c1114083c01c905400317072102d00030542c06641d440c0e0300e44010354016000e08050052005800200920070010b02c003841c01c00e0900c00301c07100c01150f4900c048420b10307809a4030907070404004200c80d45010841000359034100380c0d01840001e0703d28607080a0700c10f40808a801d0322a064a041c10710072650302038a101071003661504403080400c2d14031720300c880e84020080c0501094000162140c07500c11100c1c0308210300e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 194704316 1250 194703066 194703083
    0x15031202010905030d0509010b0108090604030311090409290c030c070201020c040f0e15100e040c030b0f15040b1f20030706111213050a021e191809 65
    0x102035030750f036080d50004031010a183d030310354051040c020000c1c000c2d24580082841c04c10007070b00c0c00300015036032400b000d803004d400d00d0340c0c88110f01041d1120394100e65803a400039101703126400d4a85050010708c0070a1381d5040c40382c0403c1c1d500300381c100d0700401c5860107840043c86150071034031140c11001d00743d80604000c03410751094100f4107407a43c445000740c05030101140760000d05c61000301e004a09100d02c0840348484848a02c08020211300ca1600c1c0f0300035241804d8007003034259510b2500c0c7c180714102e030704040e02102c408400c1003200b400341a81548184083c4154201c1029514184402e0f21030303035091264484541900f018070404450203840001003145042095030701150307043c200b003c802d81940c00307058000103046818080d903130013002d01c480b03a00c2068510345490034015400c0b4a5024091107401c81c00700d0408014050204440341e030941d00100348280e40301e42403850000151331011550b00404c8000103102c02c1c0c940340303080c02003224540e00c0300130f40b01d6012002c0c000c01400248800c036910030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 194705566 1250 194704316 194704331
    0x60f061318140609040309120f0803090303060a0b0403030801030303050403051306030e010c050301150819054003030b13090807050c10140d1803090e0105041503120201 74
    0x144408198007011000c1c900084068803160381d00100100203000c00c0c0204070510501c00000e60203602c036022104401a00c4103209058948113020140411000d0311641c00031082c011181d60100007140201d8040364405442c584c0e508581005020741c3c84080c01091040d00100701080c0070340c101d19403240c8a440c0040c03a01801c110680e6000c0c0c2c00340c01c8a40007903070302d62040745960780911982207221681d04019096624022914484a80d2804414104104400442d50070500d03140c22085044507190240114605103102c401c0340850080b164500e0111241510080d5014141c3d14241d4412225114a16183c030344050300a8035285500ca038109460101d0030304001d4041c40b0b00c1040034071980c0741603954002410024070380845d545190f449603242e61181c0034842d82000002d60500b1160f42404c0d104c06210580000508848890b8549140c8900007042010b42c48412041620000154207c6607604d60701804100ca800741c80400003072003000ca05002150402549030031150b0503200215041 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 194706816 1250 194705566 194705579
    0xf110a0f150f121a01031508100902040b12160b190e010905131e0509030d090510060b12090313120203010603020a1818080a0804030c12050c060609060f0613 69
    0x199000c6112544d02d880701c0b14120102d40e414001c812017141d080340c460182d5401c0801050300c1e0002042c111115a540d130001c10215215504080b455210080840700850101e050b0a038507000e140300901b501e594500d101040040110090390190074402101014441c00d0300000d1303544c242012940c074140422290002001c2e5602a0502200c4038040d401003070703041c50100d04044100351030400120072401c00c1c0800c201110300105a0312803c41002010649048a040c41805c00004210448866041c0749002c141941080000d200b0608411340c45c807078aa0701c2d424019100d000e807480300840d2488014013000607850600700c215640d03000400002d01250740380e001510b5401203600c401010b8016071014001100b061140001d98a43c10490400c1c1c034000e0b607251500d46c031980c12118140003548010809061040303580c000d145034402c0c00e0780700c4e0b00592140580395801c80060640580f01d600300180043c28001c5030319002c0c80d40070345120b01c500c90210801481e9080100031405012600c000001d89 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 194708066 1250 194706816 194706821
    0x905040b15030c040e1302010e190e04060504023d17090c010207060507020a06051c06030b090106050a0b09060318010c0917060f1605070f110a0f150f12 67
    0x241ca0303d5a48143d407149804840d14144038010701200d026007400a4060140c4d1b08014022034200086469020320b140f0041440c408800e260001b0317044015200400c410002203501c2240514000c81e003403d040022844859402060401c1c128080c0000c596402912815070181c50340c541003e081c4020700007541e100351003036600111840b040541c031803034080c4083e503010302a01010f4116854400e190190a801241260286104010400900207035600e60f003080000c4450f45090244000d201389030b541e09110300c144100341c80c0044035519000c0000b074035160a110500c121031601c075001c0d0400b1200d2080020380c0d04010400807000240420210f0030300700a02c02e050a41c825134542c9020a0301308038550b03601141c0443d22076010360089041c0007031800c049a84035804840061110300c0312aa078801120603004d80d6000628003002c1035119804c000810010103032104042c0d0b00001c5085e5115002c80100c100b510070b07002c4218041c0300e80d98126116000450f03000c00d45c0c0c10708044800d11184c00204 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 194709316 1250 194708066 194708071
    0xc010e040207022805030f0304050d0c05130501090506030c0a0306020d091e03170c160201030b130204150504030816020109030210030504050609160506090411120114010f0905040b1503 81
    0x415004c20040200c40c01c04010200002e0071064000b81881280c040030583da80c41035004940c46101c51180b1041004081c180d00300c09400060300381e410440055210502400c001c1c090000b4050900b0001000e42c00c0001d035094070f0304070081120011900e5600e07020020340c029420101d14a4840c034001001c90342e4101020030302460410900100d82d603900700240014015800718410b0101c1c8c10500c203810250314180c409110054035112030301b086030310040c0c004000d085400c0f50080380302551110718580c20b03030182c0200c405140706035200c0c680080c001c40382c03407080d40001002e42c0c0c5c050003652007030300c1004804a50107106040981c0f280741c4980011f0701107807540c165400001e4640c010041004014400c1311341051000c8000d106c80c06401c8440c079481c4209000e264010600401c4c03148056a490300b1441440c140d031440780e59500b040c0c00c04a403424809004030080001038400f00b807030951007115a5821208140d42e5501540c0c205020000030380400041d031170b42300c00d13211000703120b13228000000c50 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 194710566 1250 194709316 194709349
    0xd0b03060702030d050a0203070e09132001110a0308040311150a09030e0d08031303020c0d060209030d0206060d0803041a07030b03070f0b030a05060a17012c0c010e04020702 76
    0x10341340c00301039805109803000202242440c4d401407081c04419030300041402c14440f0708444151083c0c4d5461410700e07440340d4a5070040c100c5020000000c00b00c07411005d4050820b0400c1c0e0b294203c1c0401404040c2e035566140000030300158003440068042480392000d41100440030059400321603480061402048007a42c0c0000c00c950f88503815010550030050bc0c051040c02a03e02d68a4110507450f10000b0740001800c201300c1c8509503604904051080c8071000060074010a03030001d80c44c4509144000390402409a0f000744030727840c1d0480c40c03d4000100e061141030300a04a00140ca65907a4034443d81d0030251045400038002c43c1200d04c00d40a011160b03101d4400d50f80e000540c600d05008141c58580c1e107900c01c603052141034a060014036148030031a03500407403c1101140d01d49440300031500701d9426500085513a80c441c04a10600001900b200c001e1002c1502c8070403004149030f802d04049442660841d00703a920000b140c42440d4001c008c10303031018074018801400c1940c0340e008502801290800746 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 194711816 1250 194710566 194710573
    0xc19050d090503150a021303050a111801080d2d080402030106051e041a030709020d060b0414130f1e06060809190c050604060305070207150210020d0b03060702 70
    0x480c0200e6001d54058028441100103006414a4001079000070f10080c04118000d5000a880c513059406604100002c6601000f103401c40a403a0406110311540341d680303140f10700051581e09e80e42c00800000203042e2624003001e00100da007400026500203141900641340c80703610044101016680e164024804d440f29111982145001d104160840b0301c2500003600c503e404040c203d8100d49410300c1c0342011030f42581e0004004080003900c103081d41e030540c0c203a6403500c03c0c8400440c0119140d005000202c1c1144402d10aa82c2c039030b0103015070390007540601a81560320001581007454980d92520315403156450002d01c071009040d2000c191030b0785150103001c03030030484401d040380340f0584034000c010812480e244c242c504107901c07440d44519020315545071000464649000303000c0010b2211000f420010203043c1d48540c1c848015019140407070b4020050300801e0300000324061200448158020654050703c0c1d0820031f060203170000e401c26541da5203110703560316000c9110744003040102c1c040c4025030000e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 194713066 1250 194711816 194711833
    0x901050603210f030a090611070b09061504051009020a17010807030b010302090405100f0f050f040c061d03070303020c150c0d030504151401080c090103080a050c1905 73
    0x241072900b20140c2c0c0c0700300212400004607040300c2d203410640c2d0710340580c091503a66a803114085140904441d880c0606020701d0404801034200c2c5000042c40881c7c0303d03028658072903940b0303800340380c40d400304940010000d544201e1595042c942540003c0d40803601c0040003660a0b2912690f03030481e0450300503640440c0e07078551139580070078486001900400c0c0040c000d1a8290441d070310340203c2001840024000c91441c400718007003120602801d51003800700c040030800741140d0340480d0050440c0c030702205d0032240b514000ca4198104288003501c00d5400406000342503240c0481165a480d4001d039101040e0203080c0720700348941d800d02044000310b019900521004404008120240f85001c2e00c400c00d109003005032000110000c101142c400907507003800a0f45603a40d0a01c030080b0007031201103181851801039100d03017260f000580c0605854292045466a41060082c080454400c1c08007400e81c000500178000e407180310300004d0084e0301c013030320584100c0081100448159580031604443c030b500600d11 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 194714316 1250 194713066 194713069
    0x1508030306042a14070813140102010b03061909021302030412050315060a052101140102010207020109050d170304030e04050606040518040311030403050318010203090a0b2109010506 80
    0x1c1000d0760005007070710200307010f2041d107000e03003a03000300d1104092040c190700c1c00795220006400c1c0d8a11503000380c070b0541d0b079900c806210b030488546030040e94000b081c00450003259500c14494600703181c001034010440c6071102a0fa1180b682c09119854910544440f400300058440c100600f030000c801c80f40158407070515250404070003106111100800000344100000c0201201c42d034004003100766040c5546009000701152300307100301d82d40c0340303400e0842100b1510340074140b002d482c0c102d0301c0c05680c030541c54200000480c01e1348101c03440030740092a040d20074412031034503907030541c01284110f0340c000107103000800528039a00101c805401181d00d90780700321000e00705409000c3c0e0016048800c2c40c540343c00c1c4000540184468004100d50041c820002030815000b00c0311000400c001004480c0c4465481c68125500c7e8450182402040d0f294200c1503020350000082c1c868803070000307240b000414105070040001c2d803c00d070301002000320780042848041c1d00c01124280206046000803940303140050 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 194715566 1250 194714316 194714321
    0xf0a080d0b040903120e01020d0504051c02010b010c11031c0512010510080408090a031502040513050606031602030d060608090f0a1121030309030a0818070b0d150803030604 76
    0x8001c14000c90038110740c24000303076200c0042d1300c41c01c4034403000003490000b0454681c0280110101c0d140707081c1c9030006102c107000d000540d0381210094698a40c404596170038080b800d87c2d2002c02d519000c40d0000c160100000c2641443c12000c01303000d811691108540030030141a000341401d034402003100080c0141030051400c59460140500f51000141c600c2c200d40010b080060040c8050103078040880d01602035178440d41014020754026420341c50355a2203c074000000c1d8031074842e50784101c1e1804000782c01d22405000c0c00c0e2041000600203821560b4142060102041340b000480450104100010b5100018410310000c0e020302c1c2d690f030480d4507141040038540807020500e02e582d0b6004d6001d82c1c00160244940c3c00300d083c81900e80d40c0030304441c062849138040c201c02601105010110401070046000070240400064036a603201583d01c0b07045252041c9140c40884030b41c1ca412400b000d00007591024001c00e00b04440440004100c9a00605908074a04a8108007010740000003805158036050 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 194716816 1250 194715566 194715581
    0x140a0b030f011808090f0a0e0108010b0d0c030305090a030b0a02040f0801022a0c0901080c01020c120a0f02011407030c110f0d0b09010e0f0304090c030c0f0e030f0a080d 74
    0x9000b00504106464000d58001901c3c8005040304000168841c15450341000c03002ca03100c02600300d140d0316031901005545a44240900c4000c4d61070040060b0701444c0c8000504400c5030009001300c0642c0c29600c3c2142c055100401d41da4111f4071889000002420600c102c42c421400248010b84940c00c101000c08542c4150303004031a103a005000c00c010004088071400102c4007070b484010301c03122100c3c1d200c60400a070342e4403460f0301490070000018041804140d0b200c6ca840245d09540034184620100160f0310030140e001c400311b50092181c5400200000071a0b0391403801410030300f0f0303400800101690598001c02c021800240c081d04020100041d400c1098420b02c021035031400700401140104510920550003e0071950f1800081804a2001c0d801241d802c02c4c2d240503110444c00001700240d40307074414880c0d0000c1383c0c500703050102c1107071181c4110300010381e0a40d501a601c01c1c180c902190b00e84540a1102d0307041c080c407411a600140700300b045443e030602c03c4480c291100c000d0405c102c1140e000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 194718066 1250 194716816 194716843
    0x6080327010507030813020a05121b031c030e01020906040314070512030913021b07140910060e0f060406090e01050307030503070b07020a020306041103060a0e0601090b04140a0b03 79
    0x60000ca400290446015a0b21600407070071625070340c00d50700010704107442c8c0d0f611280c0c1003901d03020707070342850b440114092002500c2111a40307070300da0445d0103040d925000302903c050024800841e600000341300c2c0e086400c5e0344900300005410080c040001411300e80c0f0990003281c0c01002140640501c0c80180300d160020a02200e0f6502201c01840c0c49603285e200d50580c0a01c03841c500086038400703490b55070682e4010360149200b4004410b456520035540c040038000c0d5480500345507400512440d10b00003691040107000101c98038249441c4040c4c0f4120710000d1034652040842a28580740d071540405000207283c3d581c0c5e12509545403154800035440181c00090090700500c8003800440c03400030468115507406510f100c00c6036a000750032810809002c0000b54103024410a101c10300040742050114110308a099580300e4881c04441400c0792103048144149800071401003004119076441402c2440000e400800c00090140303c2400d4210101c412250aa0340c42c5000780d1981410042608454030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 194719316 1250 194718066 194718077
    0x8160603182001090906030506010501080c030624070f03030b0415080703031b080c0102030f06040c1409041509020301080d050309120d11071202010515090c0d0608032701 75
    0x8150b12110303909522905001442d00842c180200642d1013070482c0c4000704842d0f0780c01c00800e600c038074141e503c90f1000e10810340014880e83c0450240015034007200d0003980d0041c102c10303244d842e21840c400c40c8150611040040704044c400c0b0008a6039425150b0410341c481d940000d44c00b56207204001c1103400f02d0219400440c00344c1070920168200056100c103a81e090700340420490002c03032441c95283c0d07103504020412100412040c074045070540143d030080c04121400b0b1003584e1807a0a02c011100b0039468000015030714080303140c4500300000284410100a031003c56840e48000207030b243d080c8542d1101102c10350020040001c80824004000c0803001450f006145060021074199507500000844021000000701044107001540c8031180c1e16080246043d15a481410404801c010300212500035500700800141a40c1e540340710030385546002007218000d03840305244240d10740c00045040450325520702d4081582d1008202801030b9100300005032a403210202d0031404014003c0700114180b18 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 194720566 1250 194719316 194719361
    0xb03060106180b0903190302010207170306130e030c0304030c030b0601020102071a0606090405042906130b0414090d09060801050d110301240e0f250908160603 70
    0x401c0600c2c40d10440d03064050190b03c880c40d450000c2e0800540d8481c1071103406261002a04150301034001d40f0020380070340b1007803134000d60b07003101850544002c803280c03540600381a0390120089060340c0624070100103001143d0405180c0c082843c519071182d00203440888400c44104100411002c02d10ba22080038030003981032150b161385450142c45098034440c6640d840e10006500c0d074032410309a8998040048c800e100302d050078101080e018120300042c03140704400a000600012440c1c0105001e81005400b8043c14801c90a8440c001d207881070b04240e2042d1a212140b50084599072414003800c003903800b03490b40044101c0080c02001a580c458418011804010400d5035510110300c0c48144d00000303120b400a181100090050000c104940440025642c801c2011080d0070396440603907500546400058036140d6000900c0c0c0001c80d00081070341c05e002888802000c4441a99001c1ea0050802408803922100c446051103541484111400c07040c942c100040b03540740c064070303c07020406140302039805d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 194721816 1250 194720566 194720597
    0x1308030a05071e0204060b030f1612091104050411010f0206011401140c0d0f090906030f02040e0703050a110406140306010323070801092d020405060a05040c02010b03060106 76
    0x30b005041c000381000444070010041c40700c0d80100602c00740c3d4010410842261904903146813070300300f030321402d81c03003440c010003e003044002e6580309070030600c180c80d03520100012079403600181080200c1210550320b031989600d410784a40c0181405580309010400c80d5400e050001018140782c0da58420442d4004070040252081c0d0456140c09035000303190400700c05000e642011414890701d050000700b803003482d1201c1c403003940c004040c04031901c9565803042c04a69462224050754428040540510007602e490001458241d0080f403414060b54117944841da030340d840d8103040240c840410303941c1c60620a01d9040605d418424039002d01014198498550140c1005c20b03520304050000604074080f03900b06041e0b20100c01d928a10014a030812600380075100c0910501034244070902300c4107620b01a01c464415440803441440d00a0007840000240c0d5058081101412024021640003000c1c000c3c041044e0b01d81c0d000d501005032854001103580b0340071000b41840d02d04164480010000081c1e16000d54 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 194723066 1250 194721816 194721827
    0xe1002030601023702010c2108090a0c090509190302060604050a05010602250512070302040c17040602160b040609120306050f190e040b010816030804091a040608031308030a 76
    0xc410745482509201c505920042c0c540008806d406850035042100000030b24100052800d12504150380b181e0082c1c544116065070360780900c0009020314339809040c042d00300168011a4000c1102c005c0364819081d08180d4041d060700d0103001d40042e085407040144070700303080c000c0c0b40d0402249001084150301d4040000c1d211b0b02074002c0d1582d8461a01c41c000f0380c1c0f110055001d809040e0080c003243c800c02a210031555a0005440200d00444c00c0c074808901c003d001d462010b601c18a0b05500c1c0105a49960325040254818000d805030036180001e03404c00b10700b0b2400d07aa032180b4400d003000920742030641009900884071403019403c0500b0b1020500680c0c0382d400003134140460a84224000c0803514070f139031010303c1041c0c2250303030380c446a80200030512264403080c034101d800d80815030344018817141d03501da00444035010181480350300304410030004800764081e43c003440c3c100b00d5525000c98034200080c2234905580c80244260701c00b0456040160001c040701c4010111040110314040340303060090701c2c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 194724316 1250 194723066 194723143
    0x20303092b0815040e010606020606030105040b010513091509031706060d020c0c0303030f18060903030106200d0e1c0f06020306120105090a03030c020309090a0c02010e100203060102 80
    0x400c040c2c0004203084142038040600342c00c800034420b00c64150341c0c0ca1414000c000a02c40c040062180c0004222070341018410f80c0d0080390840d840c00043da080400b8090304003000341409800f03035038681c050400f182e03688241a104d240448004144030f0002c1c00d000346400140e0440d00c441e03e1245e400c4c080c080da82c41085540c0920f07803c402688600000b03130400e04098011401c00e80501002081041a0910794070b024480c1001d0b0160342039000c41c0210700c0340d03102000c583c0c1d407019a02c00c00041c82203602442603c04204480f8856400c41e9030081c20241c14031075510780a001013407280103807100500d0a0000e01c01440190360b21624400410744515503407850b00040a0080796000010801d15140ca2806032214940c0780e00a00160031314009840e59482003000c103400091030710720689a03881c408411551030343c0e80208290f1154480220340c10042268620000a540d610f801003a1005824404d001c464041300900607120300d0800006420440c00020b450074842144074280d418980402034902c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 194725566 1250 194724316 194724403
    0x150703021f050f06130b0406180e160e0a230711030a05030a1a210d08010510080a3902060403051c23041203050919110a0602030309 58
    0x204005c4110250314014020844a59009410b10401081103c4104c01c03241101c0e000b818200f0a0b44a807004058942c403003c4940407441c2804071081240601d400c40c3c46030428599000081c800252403c500b00008a41da050011034071800108110140c20000d0600300e04a51006103242000280307008009220042211203995139440100f500e04440c9040c180b0101e9010f00301e0228441890500100240c21025071036881c41040381d0110f02520400c4100c0c1220350180800c2782d40305c1c0c8111b055404c0d140c01441e04100d240c0c0c0380501481c218012008605043c0188481c1002c0c241070003a148100c0403010410b429980040240700000b42d0110485045901184540015850294159003d08a0030524403e01c03e801120242c00400300b43d450b9008601c9400305002c0500886000e400f908c2049a0400540e003000300034606051280f180307030303205038403071002d400c806044880000d504c100c01d5041000143d201004000000108004500b414521403161961060000540700303207803e060070001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 194726816 1250 194725566 194725579
    0x170406090b070807050f0f070f0f090b040b03030f07062003060910080a030905090f01180e01021c020301050307171e01021902030a1803021509150703021f050f06 71
    0x9403d00c12000251410030350300c88161070400e100303111b4880d5100c06e642c24500d043d00441d54001154061518040c045440113560440b4032490004958010900d1240d841c0d00280c440740804d620340c0d810300c01010095030070f8190941b140c0741400d04e5000c0760250743c8003020304401c070351070800360005080c296940304c074040341e4140703150380d41d00545c00c0d428000b503004404610400c5101d500305500080c40e94281c03441610040b036a5516140d8440d15410300303100307540380311038a800903d040c4001c40d040340719280038100c005450301c90440c10042505180c404503400859000c070060001c0e00e010b00c050001880009031249031a070403851081c1e2101c1c145034400d0a07000c1c2498000010030781c290140c80704440c40c0502142e1040030303001e001e500c0368040c0d00700e0800034903000440b2000007000300c115021349030068680c684400d02980c6040c104d51060a1040d8026a41d21280c40c007041d800c0d00502442d40700768050440c07020346000c03141018984044051500b800d00c010030002c3d03c06940d0023a400300089800 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 194728066 1250 194726816 194726827
    0x901030c05150c01050c190206070f1101020c1911032e0b03060403031505060a09030803130f12020705060a170402131a0306150312070204020d020d09170406090b 71
    0xc090305440b80f04a01d032030079400e00b800c000d81d60080c40e016158500c0d030166150030600c0b13038210898913001c0c01c81c0e80102064004c0180842180b042c0004c04282c28000001440c003103030b00514605e031500f50079032000d00c00741c02240d50302082031105400700c0c02d00064008002c9441401400d100020300600d4510036100c607c039061070351038a2174010440c1d001000e008c1d2442403d007410018042c00e824081400c0035012020001542c2c248602101c1070020181d0318100c4d4241541ea41894680c80078089840050203201e080020550121600d00840e100c0c0b0340500d2140b44083c130281c02d05142c1d07400f40c0d108410a014400c0c820740c11200305280007095040181590b41c4900c00100403800101c10481c12a190503201d000034101d04c0d001401a0200324211802e9550b101940061469806105c54040d0460300e9a00c000089440181c982948000c0001d4101680451120200c2c0c1010450604d0291148801c40030b011148481c601c0c0c8a0055400350700c2d10303003801c01c090048100352041103904c8500098 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 194729316 1250 194728066 194728099
    0x506010c0b04111c0209010e10030f080c031903060b0f030f04030201060e0a150806071713080d1a04061511010209040903020a12110c0f0315091b0901030c05 69
    0x101290043d1004010881140b4480c0c0088044106000e0403401440040c1c0089040c2e1400400c040c4500b26201c4c030203034401d04560b1003016140c4089400c5610354800e00c6218800d60080c8007030084a8403000c02d1190704119034070000d0648086900041801408205a00c902d911802c2101ea0058180340e40030700351b44403480d08900415441d48400c4004404400b8885580802e400c000444507035501080d5130940c50b14007484e00c695080d5206008141c840891007a210242c17102590b125882d6558400302c04240c1c2c841c41c0d280d0303101c156000e45041e60341e00200b4a52101008203180580c0c2540d04000e51810000071403220502c0c01402d4050140d980d88100c8030120940454483d40809030090007280c140d8500a552008003000442c1c85002413030002104504c150700410381b054a060041240c6503001c1e0501201c0b400700050640c143c018000ba100c0c4020315102c0c420b0140314400001c000c100b105a80031111040c1418a06100d0b08000300100080317041148030009070b0f1811140c1d0b624280d001e44 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 194730566 1250 194729316 194729333
    0x4050f0112060e0a0b030303090c040507110706030204090e0604020d0213090212030a0807021c0c021c050f0d051e0904020702090a060305160e040b0603030c032b0506010c0b04 77
    0x100301e038400604140010480b25190501d65001d5000e01c1c10600403042c0c45804c16450307010440e034204003a445a0300448182c07825410003074020b08281040440e0112034290181400c40d43d0f000305d00841d03000201005280010320400503000a4940680060708250740041e61031006600082d1180a114180c0c010003d8558403240589a0081c40016848c1481070215260340200c080e26021503080d10024440d9800850010b1500c03076200c0300040c0c820759503c02a2040c4c03115900c142c0e0840c6202c004c102c00c00c070761070f0700000340030740603900074a808a0200c03040b134541802034652004000c4184804082e01c0e40071038080c07483e520040b50241c0c552081c180403900074002d144010754030030724020030f00528403156480501500d009405480c80250002280b40e0041c000c0d1040110290311240010081006100035503000f10000381035a03e1712800c064290b265030880301d0008040124140744c8909104492985000f800d8034140500240c500a00060a142070540380a0140a92400011704010210 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 194731816 1250 194730566 194730587
    0x20090a0e0c0406180b15042106140f1503070611030c160905010b030112062a091d07081b0c030a0c0b090a080d0c110118021e0604050f01 60
    0x140080002e00d60f5813018944500c1010079a122081c54a00c0380c4c0e0403810006c01c03010668242c038403001d1401e4a4031a00342c00c03000c402c0e00064010a610025280029100d000d48455040b5556110f141810021807251401d040a0060307034114a00c054aa01c0545010030a2412100310381024001400c0c041101410340c41941d1550a090007180001d154107407828a41109803064028108000d070703203903c51034070544400c2c0164000200080c0702800000d00c59002040d203100b0940504960042c620300002030318110406410114400042c18840c0060205250880100b0b20150290340c1c1010403010f8080c1c40080c1007103401e41c40c041c20b03051050020f40100eaa00f004120120382c2c0c0c03140c0001c0000c2100c0205902250111000404110035000002d03600d50600d81051859280c8170a54504400402c0e0084041050020b40d030383c41c0f80320305400c0c4181c001002c0c1000207054102401d00c100845502d03080c140e8100f100aa0f2071140d060384990099038282c500c04d9a034100000b15210040c2e55102c2c50 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 194733066 1250 194731816 194731819
    0xb0c070b15031c0c0f0317070c0203100b010c02040e1c0806100c021903060b0907020a0c060e0a030209090606030607050324040906020a020109060e0d21180b0420090a0e0c 75
    0x10443e101d0b04066110f045801c603c418101f003003e4036122001d00b25002000309101030340c10b5112500c16590000310f03034001181094141080300300c00f8440d501042c240d40745c04020710700c3c540000070042c2b40380484680c00c042d0070100b0b2034550b440381b030408000b944084050440d0380801068048040442d20b404603100019017002c4400c0480c1c594030301c0c00340c000c0c010300740d2003d029101e2480072900b124000201c0d05000342d88544501d0000e81803030001c4504002000c4c405a0003408900c002025865200700380f0b001d8541e0b140074004078074010082c94070340800688000c040040070010001c41207540c5501032000031040010b20a0a00d42cfc0700002c000d09180000a0812403000840c001c0480c0c0540c08280d081380700305402d10502e01100062500c840010040c4004540104107030801c00c0a00100204042c01c8290001800553780d09040c611000b003010458a41040100740020b01c400b0141c54882401c0d5103680c1c1c0d200140040205a2102020380720741c0c0441d4503a0034011111100f0312505a10250 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 194734316 1250 194733066 194733083
    0x9121a040b090106060804230102040f030f02040b0f100503090c131505030715030506040e1603030e0904080414180c0901030e0606030c0d06090b0c070b15031c0c 71
    0xd29060035920400151034040c2550300c2c0200003c1c2c11070003441e5081c45580c110070340e910202290b201d120007101c441400400d4a543c01c11000c928800c5030107180020b54010405407603694514410b0108480d11004e90b0341c0716500f61055400f06a544504151040c12280361207926030700e41c01c0e07000c0c0c640b038066040540d01440b07103054000707209010740c880b842d5014031a000d4030784255503206258407a0450300a41d00694501810680401d010742c10860304420050400104c182a0340b110500708144c109441d01c050803001010000c3c19031141100c8d2110704111003c2800e424150380d803003c184100e02c29561000d0110415102c296602142c85180d0a03181c0c40424440c58103035004081a4010010540800d1501000325003601001031014401d880c040e0040c403490010710204042c4200c00c0c00212690b94440203407400041d5209411070040c5103200920b61034412510341000e185600a02c214520842c104100000d9a00015840e04084501aa180c14270f0610b0a003103407100d000c107001038200b00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 194735566 1250 194734316 194734321
    0xc04050414190203060a110c01051609060306060503060d032003030a0e010203041a060a09110406090b03040c06050309070e0405030702181003120e090a060801050601020d09121a 78
    0x450404803240203202025264422018955a4650b0401540207501540000005201c0c0c0a881d405100075240c010181070034942c1d000310311400d64400b2541058080d064005400c0515007000040c40644454202844800d0401e0300c003c0c428000203008520880c612030000c414580111304900956203441c200c600b1400c0311105041da07a500c01d4a907410014500264010682018401d40c4e00450b4840c81c041110304411031b42002d80000034040d5075000c4050800020b07041e030580704200225940441050302e0341e18100014160403442e03881589180302c20010400001c000070940003e55071503003032031a00ea03242d4070716091501c0c2c0141c21200c9080104803c0c4003d00100001510420344201c40316018258a0702d00f0240fa208140d8202102d0b5a4188003440001c880300c52440c0d04481d40e1411040d01b4000c240000c05410050343e80b00b099a542e0941880390300340030b002e15a840784003800144070a1070048401000d0302003510806c0c844042e00ca080100f000f151142c8803c54114504990010b0f0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 194736816 1250 194735566 194735573
    0x60d0f09020102070609030f060b0333010e070e210106060503190603030906030b130c11010c0905060703180b0a0815010f080408220f090b1203040b0c0c040504 70
    0xc048a9000741c0c0036100701c40000030900d218111310300980f036028010b07100f1513100da91000003030562000c48680c1805a00302c0303904070381807450490f408004803035002643c546480070315803000501a0420142070468604000085800070104800fa00301a02d140c0190007404100908685c5186560320b03d079400d1802c0000e030b45038413401450046809071001c005003190800da4a080b0307202803000901044014404001030350080d4003080d00040044e24400444e01d890582c2e00454a25045840c0401e410340302c100f10100c02441a107845010f83e08241c40d000303003084001042e901541100608115180003140011012441090300a068801d0040c1d180c42030b07400041c1101c00111a104106010340c04507205641c85000c10b072480c0301464860b402031362215151941c4076442002c0d00c005404004140301c4602c030134410250002c1c800202003001003420001c400090341c020384030030342c0305003403000081c001d0305004000c4408441140c03600642d80c03814848164144540100d003e03501c6480d220421060 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 194738066 1250 194736816 194736821
    0x509160201050105042003040f0606030b190b011407020103020f0a020607022e0209040b1002030a030f0605090f04051c020307020112140105100207050d050a12210b060d0f 75
    0x2050a030024012a0b03216018042216040c4030355040c1510000c0250183c2d442c03480055400c680114041080341e0243d403900c6094541c0d81d84211900d844842c1000b140300d4604008000a0040b060203000e40c100c020002800700035881074042c1b84210000d4030300c086a000b44c5c100c84c00d081c10a00f0450b1158000c40000e03407030315000c0700c0003c050300071003088142c0030916481c011910310a40c0000c1c03110340d040741e141d40300035040351901c140c01c56921204c1c3c2c051356a5403043c400c5a10310aa0045588500003a801000e9070384160440269508012060000b65152491a9030200008041060036520360501600c0c020359000c10040810312840203290060303010001304400c80c002e0700e0b500d088a02c207481080071140c050160302c01050035400180710301d16240d01320803403a0710755104440b0302544840c00110726081754403084a042c2e11008001d010061600900043c541160910840c00070450180c060402c1c5000038840003e40d40b000082059a200d00568520b40c3c6925401c002c6007020cc4071030b000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 194739316 1250 194738066 194738101
    0x70807030317010b0409090f02032e02180f0301060e010e0a1a0619050405190e09010606050304030c020a0e070206070905150a1b06020c0304030b070503061e03070509 73
    0x540102a8000d02c040540e0814103c8050035403080c605454518403d008020121046540d084501400d1015031307010000d6624000742d041e41c54481c0c03020180d040f203140d44140100bc07603560040c869480d50b0404490301e07003c0700d40d00b82c030a64504148040020300404440d00100400505900045052500703070051038400c4252042c10001600051480c079200c080451181d075004000300442d042050150380024030b072400c141452800c00d1785550000f0b5002d0070814902078051000a4200302d80240041e0041e00291084000c000c031a050103002084e91000501c090240031844800000b1900c0d440c80300310041002c0601c9036594100064000d4481c0420380b624000214502c138081143c3c980600b88100282d18813055074031b00021060155a000940d040c0c00a00c40801c2d80d160b80403c9040c0014000c6002003805503590b80e04615050103c1940900075100f04141482046156200c020300c03141e4103042c410b1039561680000300000d20780503060b00941d41254207401840300300b00d9162202d08 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 194740566 1250 194739316 194739323
    0xb070201050f0417130b04080307050c04060302030705190f0303030e15090d0c060b04230c04140909011d0601050a0803310308070b04030e09101505070507080703 71
    0x6589402e04080e9425000381c0300900755041010005001122040017421081c414940b1140c00035a01c02225510760803c1e8843d0b031180d00009068001c1204c2031040c04c1d100042202d04210039410368000c00c0c0d8450071030142d00c1c0113006405120f00a001c24071711403030003402550114810181c9038a0010081c05414154400d00d20500303910741c802510700d80159219040042c018180261800d00807140046036040c03d41d4403503654010340045071154041c1c0210b50350300c2009040340030a014030b081e100a80c0241610f4280304140f1040c01141d002c903c0c2510a46000c07102c1440644888942d5801084050182500311190300d914044d92080030070000d04a038411103170045201d41d214080f9489201c3ca840101e6907441d02e90010306603030b0907054043d035880745846d40d4682d191b49039170702c1054070703172010301d0075154140224208010181d001ca01d0301049034090b203002e00207040c0300302009510085401411203907400941800d8a2078815000c0e038000d035811104641d000c039500c0e0741c42900d807200c501054 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 194741816 1250 194740566 194740571
    0x607060e03091e011d120f0c0306010806070c03120212240301020406020a0609060b09090a0c0f2405220503060a020310060c080921010c0f0c020603060d020405040b070201 75
    0xc1c80051a51000f00700515060311448504a043c60342a0f00417010040c1070307548103003189081020440304000905840303e020006011003042c4404040c42e00e50164060400c6038011410005491f50018050b00c0803541828000e400c2d1b110034441102a028100c0f0002a00b10400e042000d000074003c40701086244003400714038400a081d09041c00d0340b003a030081c0c40241c0d00941d407040c00180c0a9029900d43d50080c00000741c280c6880c00000c0b80c00c3c0d0280d410512642c0216018005c0c0491840401c000741b10b01200c2c06d940a2030032082e199950402e4a125559154001050a200c1d004904440e107401c48002d030221626082880070507030304224040c0c540a44101d04c00100d40e22140c0c070840340102a00c142c850820f03071800f5021208010310304802c59400f101800040c00d5501c2c0e100e070358001c01110810070b030f01c4160503030901800c5520004401d420090b10071003120368146c2012054034595016902617a99690300d4020501900c002c0324001d402a14143c100030070b00125641560013a041d40e40203 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 194743066 1250 194741816 194741839
    0x61c150c0f090504051509130605011814010e07030c020705060c160504020f031605160f02091b0406230c030309160b0a03180f060b03070602012304020607060e0309 72
    0x144011900304070799410049224410158241c5000211107600840523031158888010aa9408050310400c0c0d001002c4d0f00b1844103509521344080c00380c0383c81d000c00800000c1441d0300d4404440031682c00030707104900381a40c402c0c440121501c01e20007031000c2c0001070411952042040000c1340d49140c0c61300c020f5000c002e200345c04903151a03e070084808a100c1040c2c09411030325a00303031035084812100420000d1250800c0504407070003603800003070512805990b4000c07004e102030051000e0b18074004d0200c13054005007240700b805103160b4000d64040d56994989480007102e00116400b0028290212500e02c0a000c211090070080c0000150f202e40c1e00361b070548800304481005411280050b000722a1821006d009004506119900031580003100074480040e20069403110b40100305080380580c1c00c20f8950740d1aa2003810308210120051035688001c101c242c849584d624401e206400500c0d01031240741c1d0104d001d565500041d140c00b150041d00030401c2c0b80700030941c1a81c0390f11201e5000e0156011114 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 194744316 1250 194743066 194743069
    0x71b080f030c0703080a110a0308010513020705100209030a1704080d18030209070504030f050106030c080c01050405040b0d02060d1a180601080406020c0106030c0e0f061c150c0f0905 80
    0x641e640031442c0c100500c01c003411035a030450079030480181801000f484118510042e1410801e4441e268000e4440c0d0b4072350350600303040c04003e400e1042c4074038086004201110000d94001031550040740c3c3c0b200c0050b16040040e0020703041100040010780000da03103003207155042260000402c21540e030752045034580103541d078040c2e0707000c4c00c1c01414038554010380c3e41c1080542016069a41e00ca400e6252461510303859544a4900d0000d0440c1a00c2c07981d91140300b40108811094100050086400244402031000340001d0071b901c01c90013a03500841e11054030801e03d4550401a20140f079009014a41740d480c00c14000307000340341d800900d0114010000c1c284401303040c9040c0e030340c07090207100c01c008410b83d0301c0e200199045140034004641d207550030130141001800030f200d482d01562284004400d807500e01010215182030240c07800c1605101032007440426510b00480c8500708200c80885403484400e800c00028a405c04103090481c0ca050107a00004e1170790200d4581c24802d4152074207640940c0300e10 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 194745566 1250 194744316 194744323
    0x20f1e0f0a0302220f0e0a0318180e0a021815010e10030e0a0203030d0605011d0a060c060e070e0f180607051e0c030901110d050405090c071b080f 64
    0x8800f0350440f244040c00359450034400d01d040b20030312040e1400b00f1641130400f00001100e001c2545240d080d040702640000301a44034546145000340b000b0a00802400d10305506080541807000201071031352403400313446501c0140615100b8540003003c990100070204585000c1980450302d078000d2508110300074036698050604258074800152686c0d0f0004580d0034154020000d8803461109481ba4402c40001a0340403c002d00161a0388080461664645800075115524000001d030000503c503002c4003040d110900c15004407885480d050007003104504000000380050f660071040c1e8007400300041105410408814061000720800b41c18542e035a05030f55208041c08800207400360411004503408503c1038002d00030381181141e00404005000d0030103440350b445034844200e00e800101d981d501560b0800c02890004910101800113180404c1000b4003900c03450003414030524039580841d0002c45c3c440c080c0c031740960b44000c5258800c845000380d0350945146126481240c41f03003080803a141e90010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 194746816 1250 194745566 194745569
    0x1050a1719030e0306090d030f0216330203100b0702090115090906031109010f0b0306010503100308071104050c0403020a051002030705070603051504020304150504020f1e0f0a 77
    0x950240242481d25104405000760404055007003042c0c000f03049842c1e1341e0070303c21103020702c00c450b0091070383c240040c0001d8140c038040800714007410b03c14407440e4110030303034016000d501662041806140b8580700140c40c8041440745482181099214907520b44400554000c50041a80002040116984610060052048481c0250000d441200400042e2101074807410745151070f0501d452141c0d02e40ca20402140d03c41c1d0f00a54004411480c008032a0405011450142005d204584106800c08103240c44501c0302610407410070000000040c1006080044580515800340d600c6544010a0030000c41c031400082007107110b90301e028042680e21003000308030b8003140d6000d00700c0050607150008005686069150500650100304104070000d031050207000d02900980e24006801d041c89081303104402e8110120071b02a51041003440b0100f102c40000c44071103010100c021070342d80c1e604d1012031110020401000d8115440d8220b1249510b88480e000d400650103481c20050000c0e074504100143e0b019 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 194748066 1250 194746816 194746859
    0x1103011706130312051b0a0302041d01120b090c040609020a02010b040b0a0308070501091209030c0b04270615020d110d050313050a021008010801051608190e031201050a 74
    0x42c441300310880c1c051504080d91158691194a902004140700035560b50703c01c0300c0c10f41c00254000f0f014403650a44c10030314604000da543c0c41c0329a540c142529401003460700d50015000080310000683c10480812802114800143c0700b0300825982d02d030418060340022070040d025500b089181942410180f1400d9010040140800c05d03043c91038480c0c0d401544910420345495403902c0c1c81c0001714450b04640b2001058680c3d0b03000c0f080e840c600744208010f5594202c461030f4001007000704401244007641e8108000340072010704003652001105802000c603540a500320040c841607842c140303500420030f0740b44254145c59902c490000f90140c0b41d26444011600d03070110340144042450212503101407600d191256040342d01c08500c2d43c0008503c460046121400540302d0380c01444001002e008058025007074035045c642a2501020150070414001c0c000007d1062040c0c04400c0c0a0840e04807540b0305d0f64500c11340740c1d507200b41d00000301c00420034001d45000342c4c40c05100003551880007a100c030312242c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 194749316 1250 194748066 194748077
    0x6120f090203100c200d090911070605070219150c02070e0c0703090b0423030c01080619091811030d0219170c01051006110a02040c0311030117061303 66
    0xf46451400044c454015041c041150a00d100c0aa510044c2414815080068024810510104002403450309103400400d03402d802d211070051070003554003c4d1543d0990048010446640f00d807070803890b01441c0044041040c1c4032508039010302001a46c014403e007140174050010341c1c0303159410b9a4964a504c200880580c22100180b00700750060041e1400610034901203006642d10f03081550755400c130307400090308a6400f045407656020340b01c00c0103a5180007540a800c900445c280041d220440c000c0041d40207a0480b03040350b003000006402d140244c102c0000c01c100003880086240e802c14440300d8100c4504180000d09001d6190002e249540c005080c0e0090004403045082040303100f1091104a405c101e83c4003002200f106a40003910300d11210100000f49480d081000c00600e8800781d01c01c1082c00088811807068078000300e42c103485a074040da000305902710703070910480050142034181c41c0c40083c044008101172845001c00b141e04031641c0101c035401e481e0714100404c02105010001c01288 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 194750566 1250 194749316 194749333
    0x3080402040b22110c0d0201020909070314131103010606080402100302070b19060b041e09062108090301050403050703090b0a0e010e01122301090203040b07110c0a06120f090203 78
    0x22404c0d0404e50000c2c412100480c1440c0105040d42d181c62084100b500160750081130000403070403c002c0325640180a031034140100c0c050303d020740d072042d50094070340e410120107402d20707100380018201c181021882c043c000f0030015a48440041c03898106480880c0b04000e00002145114824000d5800302504510820b460392252a41c1c560400500048440a240c803118002180141ca0300039100407e4aa0f040141100c203000018002426640140340302c40d00e0b0840501c502854070012005031940b0b00090040c0e8034090800d1003450241c0900076615608003010030040544c0400a080038511a80300c0d035400c1d6803212400075031409207040b1400061013460035484503612550707020241c2d00040c10f0051540c1e0440b00004203460505040d9603941e02160b1404000120001e125030040010b20011400c5040999440900200103081c150410802c85080107040c403050080e491410802002d5405440e607903040a01154400702c2c48640c1e06240164204001600e800f40d8011107600802808621 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 194751816 1250 194750566 194750629
    0xd060e0109060609080a1109190c080106121509020703030905010c23030708040f1b060504170105041511280906020109050d031d06011e050a0b0f030c0906030403080402040b 76
    0xc6070020710381025021811075080900700b02b4070540d003005203a81c0d01e1034002c2d810b1a40140c03048241103912611245080d584014620b4482401c9040c1c0ea010707000980c1c0d031015400c084024044030400030302194030780342200002c107803c80b4800c0032000c40340110044400105856034124001184c070f52000c510480b00050000c1ca2281202c006036128201490750011b50008080302c25079140c04c298007107000060700b400602d00c07001c0362442c0d22143c1d400901161500390b40e03107000d598000607443c44070b54590317507644001d02c3c0544c282c0e0000d907411407101c1c828140c52242944492490001900400c10140300070428501c1802000c0003140c2000062060521301203045000344200c0305482003202d5600c0d8100120305090001a0003441b100c041c0078418407151420012a0354a903000c01d102c0d41d01494104484845402524030306450108003c0d266500c0741e00100e050700c240340c404e40e4004c5001040108058001e008a401503000b602e0810540c0113890902000035064688011040302011061100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 194753066 1250 194751816 194751829
    0x1b110d050a03020f0d0905070b040b0904050924010e01090b0306040b0c040512030d050718030f06060f030f060605010809100513080301030b0906090703080a050d060e0109060609080a11 81
    0x41e4100780b400500d05095440e4140d860780208070519020394507040d00c141485010440c200150810780082451701d440e080d8a038100e441031034000350095440341e00081c40e602062100c6183e0b06603410179100b20849107551103490220074004d10254404501c0080784682482c8252060390002800411281c0caa80c0c9894414290090080606000030040417549072200c8800c44110010000196110030300c1701030120a0300e800170a650104401c400c070724901c440c490f4840100312600620401d02c4100181000310285ca010740200440441c41c8a0000811120710101c0d440980255010400c20780c4401c011039003a0b4065030301e000c07598004066104507800c294040d94000c040400f0059600c00c0c680da8145940e00243d106031030b0741d0764460400c405078000b03001c01644518014080e181e000d0440d81d07007035800c3c0209400b4000304a40070404880c3d002003613010b02d0150200000d96202907a49201440291225000326400509480c60016014500092900e00c0550101600016181450030b1007030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 194754316 1250 194753066 194753077
    0x8010807140117060a091104180207030905011b170c0d110d0e030f0105090102090a0603090c23040e01021e040f05090c16030c03090530010e01020d1b110d05 69
    0x80c09182e41d50700290700509072140381c0c280e4200c0c804c11f41d192840c01170001401100c21240c0801c2500400001000992022040e000c1c4c4109007010700c842e25007182030407081c1703010f02c0008090b0300480020001e1184581b001d02a1440740d8030803221220340c4c2510440b0390309042e40441419a0001c0f118000c01405018003803103811000d011115205001d4000a00b036500c142d903001c41d6650700103064002c1d410403c0d6682d0152600e41401d2148440d80e607981e11505001d481940d0300c83d1149030b807146003010145c00181808100030f0041c49103400213030005000398008403031501041002c110744407400341c040301982c04403050712004904452078041404000c60008004208007882001010fa0180c0e9840c851714195010b550784245010141c82c0281c00f0007090b0b000a44070304141508c690241504400304610b60900301e8203110680c00020046024001d07100030010194004640650854601d41c40034825103000c81c00d03d81c254600e9002030302d01061440500364a0342115225080c1d41d07015000a11 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 194755566 1250 194754316 194754319
    0xc150f01380d2004061e090303033902060a0b010e060c0106030c030605010824041419150c03060f140604032a0503030a0e01180e01060801080714011706 67
    0x90384240c810351000d140d036699480d40120f10b101140511807164850b035025024072a02013002c141294041d00600040340c41c2c40010704040c1c44480c054040050407600a03000880d01d02d03030b00420300c8108070300e981011a2100805c01889000c0000d25003104600500194120607103d91520080716801d100b040c2d4007a480c0340780e075507480c2d05001001420300003004000354011000000c103541403c0060f414a581071402e03500074071a2a0f0004c5884074480382c920b402076404100d49a1802680c50b0250070100b590301c8150441411020090602c40207440e4500e5100301c0b035104000c4c4190011045d82281d001d40112400520240410f07c80d0620090000e124010000d00d001e0410740c1d2a42e441d07501c4180e240700c0c10303010001044200c0101042040c550042c0004174061802d05070002001010703040c410003020b04020310700001c085210601644200900042210081f50f5a1901e0f000b508012080c8210000c0e0712a00ca0005802c2c07a064060300030070001690b529030580404521400401005031409 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 194756816 1250 194755566 194755571
    0xf011b082205012a0f21030b040905060402130b0607030c021206240d050604030207080d0e130203060316061805090903040603020c150f01380d 63
    0x1802250015028205014603004190320751a0721818620422800390b2145040c014a000c0f400a0000b0ba034500081310082e008181810207500e08100e105804008000b81c504500486406200f181c180e9015990380040e44081c8041d41c03001061000700c1d040f540b80035080d500014041001803600003070305008851203103804142c43c6007050016031654007002c1d003100800c2e4a43d481c581141490b0002ca1841c000c0d4901502d83c6107454140c0f403030030420a030010f02d5001d400800c3c440c50740c0e0701c2c0070499100d2a04501103c001e480c0c203150181d5a01c0482c01845854415118a0714071a4424070a03004810310181021101c6180c01e400c0d00c000c1e4101800701503240c05000f0340000032010a000d118000c005030381c0e07520f85980d08202d001da40d00c0441d0f00400d0180380508204100c407040001140d0449006260050ba40c07426403c0480c141400c7c1913104c0300302c0d81e002091003140c4d0302a241c4a816142200042c0910321003904011100561030081000845000c1e03402c0024148180082e040c1000c2c0003001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 194758066 1250 194756816 194756867
    0x22050616110f0a03120b090a0c05070f0f1110211b030c0f0201060b0912010902150702030c01031e050c090607030810060207030302060c031e0405030d05090304050f01 73
    0x1420704140407003040b214107612204074402416488865a01081c412603020812404000042050071200405104541d0f4841ca184da0071944507801316004103800a62106a01c802c51a240b84409000a4196060010042c090420303241883c5043c05100c49921510030062842d65100e00480c1005a0080015561a92061001401e884585110b07036607980c001444003114501400418100d0080011a031400c1d03414442050084212019010111081c00c00340b5841072242d80504505e03c002504441c0d5080f550500c0183c0350003600145108406489c0403481c06801141142c0008820000c00b211088150300d0008450380103a0304601c10034401440d001219021498650002a080f0000745001c0d040291104800f288500548894400381c84060f1440c0c4000359a0340001c2e10304101c0705030000101c0d584102c06e000404140143c40810461032400e82049034517a0007041044410300d041078002030f6a070303201008480a89100400f109041c2c14071600451b602da01c04030303406a01d4162910b2 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 194759316 1250 194758066 194758097
    0x30309050a06050106050306030d140f25031101060509060d060509010e011d0c0a12080a05090a03060609140f0106050f09120106050117090304090f09020a030302030322050616 77
    0xd6113010302130300e480d0a07540c0c1c1852414035241041500303118040004000d2121003c5034180101c41f446060250031985510000c0c0c2031890741241205402e4200461450090826422220004007450303520020401c0c2d039030318001c2c004030240441b19280d208807500e0071440010800da101c0c64101151000004a800130b03840c10500311400c0401403810490514455403140da0100300c0b0700064201600c50680941c81d0000d01610200300d407000030600c00010403043c0e226480340003620003120f0700800e6550300980c1c9090480c002c0885001e200b04003410064112103080800e85602e00440d2401c02c1340d4026803a040040b14a41c200404074803040b0030802840702e1580c0c2d012000064004d070b51000040c0140b0b4400054502d85a07200c482c20428175103005c01000550102c00d6034129412110049241424060801e004004404000703600884140c0d0210606070700001540c4035403208580700b0100000043e4410541c03487c1c102c01069944040005002404404020400d02c079290921040b000490034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 194760566 1250 194759316 194759321
    0x901030e0c0411040807120807020609152b0504151a21011b08040f03050c0303090f190503040308220311130209010f0c03111b030c060313030309050a06 67
    0x10f04a034410400b090520400c0014002c1600401400c100000d90301e00719603840c4028000c0500291203090040340544035901d0340c04c103030032026071810301e1300f82d4a400c411800c0c0408840041d407980900f5540d4100b0062012601ca11030086d40c0102004841c141c0100c502c50282c11000e5625200396114122010240c549686001c4003200706e16440300c507102c101600500310b40e100082c0c0c02421800d603482c0745403140c03c842d9481e0000d40080041b5440038090030261031902ca0f00300c441ca104e02c4004100001c4010100700d0304400d9041a081e100c2210649005074a106600384024005030010441040080ca0700300042025135602c2d2080564180b1212490300c108400d64402e8403040e6445291820350710b001401e032201c00081e0b400450500c180d10340000c03c0c16118080d0704080c0a0919486d0b411305008035901303501c038400b20007161410070000000411103545074000e41d00910880250425a151040a4911600c4c411601039602c4145132070480150040b07410035151070240c007081c0c40c0030651030b0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 194761816 1250 194760566 194760581
    0x15011203030c03110d0e16030503070b06030c010c1104180303021b0607121e020703051207080c030403030504030c0204050a1508010204080c01050d0b0a090515090c04090c030e010e0607090e0c0901030e0c04 90
    0x27000511749580880c14034002d0b000c801010244030f600f1600740700d00c02d6a0000d10031a205500402030b13007113005a4a010038000d10218603d900c010344984030010030154540c008242c80c403031000e0b40034211864459420303650301c010740b142d00114640d800c41103004070300d40d0300a00302140e444403510000070880c04104100da000d18001d0740003403070000c0c5040d6696045541d0a401c40c83c0c1d0302c2d140100b89808159148a800003400041c1003584603800b007010f26109800503192150014010085410040612401810b143c9601110704102002c001507411042c07080d101194620b5029040c0517816a0045885a21110104020945d21400e50025480319035480c00900040000003810b0b04000035040e00d511244c110243c0f00e90380400400c40c21000031800d41d4111440200c1c0400c01c001508426005080c0444070b02a680d072078010502101c000c0090014050652903ca41c541191103103042e2030260404c4521000403101003201600d1544a0b51100030a07108280540303400501d0480064196081d0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 194763066 1250 194761816 194761823
    0x7020102011b021501060503090a020405040623010510051c050405070801090302030301050405180715050c01090b0f0c03070e010c02010903061b031803080c0c15011203030c03110d0e1603 82
    0x9940b045030040b44d01881d180542500c0c14641e08600d48140d0440da504e899120083c00b950704c1d100410301700702c00c03a001141c3e50100782d0800f928070300403850809080d0009200782c0c0d104c0d06601c02d0781c5940c14085c0007180e4109010b4107603280c890340c400708408058000a0b0080b81c40303201d030705000a14440f00713100700414248139601031941d95246c10304010603510041c002d165202030300c20241c1c0d40c11400141e038008035282009805807400e50880255018028048140090750a00c000007040080d204804c42c860403030382500c0c030f0407925010300b4240c16010485404001c0b07200c103420400f803076000e231441100080c414504000c003181ca03a40c1d100260ba200307092840c0c1c86400982020901c0303401d805a2080590007081c00420b031b000e0307030301d000301008000f408108240c000014801e41021007404603028194a51001464a5039505c181d20031603140518140e0010b803505200c01038040c40ba00505900c2c0e054810b0090400a0102141d8020a102c90103107400e446000704071f0f080e0060002c4140c000750301 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 194764316 1250 194763066 194763073
    0x12010b070f0503070f30030c18080f010c08010e0f040f0204230105060c07090b06070c0803070c0803090a06030e070302040509070303021e031c02070516050f042007020102011b02 78
    0x1a440c050840c2407505146d801d645404100b03086040c003a040a41c5407207555440c0100e000b4803a0300095485142c120300d0002c007032403204d401003201040000d8030b6400600d0706001300008080044202c9201e00c0a01890382c103040c814020484440c10f030b800c0e6942050040205c40168001640020202c60b01c0100840b01c0c801a0070740030f442c5214240c41180101007d8412528298482440355158101d5014140c0c10680d60b440c2c0705a030f51100c4003598840f5601600100341261140c001d244d40740c03c001c1c402c07a803a188042001c9420300010003591075112014001c251010704050707055010704805d40300d103a6a44681c060000240c4c0d030b00d0056a005015881c041c00001d806c50500030305002002c003902484800c007520038030b04080000125200028841d000400c52030705112400064820032202414030b200d9010071403040d074580023510081b50407c50f920107440340343c50107000c2580c04c1000840300108968900f45841400b2600400080c1d105200004001d440e8411083c4010f04d00c1014174010391 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 194765566 1250 194764316 194764343
    0xe0105090a0e07063002040806070203190e010c05060f060f030109050a0201111501061e030515090c0702060d050703050f150d060f020d090507050612010b070f050307 73
    0x1040d840580e003060515a0038401004040c6619035100103038401e0408010a6072903500c001c01180322400b08020082c1a2042ca11200c0400507000c1e4000e0700030304403030380900004a45281d00000481c2d40907481613001a800100c107100a80d00301e600300490074140a03044803010001a030512071184034020010b03180701281004001d012640e486952254002c1c1c0c5040488c0010460024145900650911300403481504154207541000925aa0001c5080c8030000200e0140e0704940801c2d9a8912480a2800322180142c200e0560714191412940350140e0000e0342e03000d082440c07070a64058880b6101c0c901c2c042c607580c04900d89500c407822000d1590b540e6000d2200455050044581003078a0075101426400c28000621100701c404014610945029001c001004910303044070388543ca030000115111000381940401811252100722401d01403881d0101d21450701109590400d805080c42c081103030b00301106440a50f000c1c0105036807200f940041c020000e10200000d0120390b11039600c200c1c111 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 194766816 1250 194765566 194765569
    0x70f03081e0426041401080c0708190e03030a0804170a1d040f061d0c0307021902060f04030804082a010e040603050709150506040b04030803040812010e0105 69
    0xe90001e00000c100c08450000e10728400d0300d00301d10981294100d01c40c00029182920340100191080724200030030700380820000751510010703a1100c2e40c1e11082c0c841103100d50b03e0701d408254034454500010b04208003489042d43c0400001100718040220f4201000f0201200f4002403664114003502d80004031404100030401002d44c2c5040342c1c058009101a0900c0403441000c0d0128030a00301e490307a00d119903106840c3c0c5135100d0304201c050707001d4681d041001c3d03500c0300303072943d072810700c640c0f1129182d000d0b8804600f03000801e004032031007000386901520b210b4800c0d840c895481c402c0e485003a42e1103c814055605041e444000420095118a00c11a039031031030905541e040840c8600c0c00720075807103282a03e100d5010a10a818a110f20900c0c0c400141a410f0001400401031034101800c3ca1280440100d401c080950005000c0030300301c0380c1d2004069031501001110302c5540105c3c44d86184c1448100006000c24000c2c6400500c21051030303003011000340000440d040264031401c0300c40040f00040009 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 194768066 1250 194766816 194766827
    0x10c02210f0703050303160315030305030a0c02070e0c0a03090b010e09070e0105030a020f0d0f0b07090f0b0f0a110f070e0903090a030212010b040f050105010305090604050a0308150402070f03 84
    0x1c4802800142080d146962103260316404010715010f4a001c0b14429020141e120398415010504014103400042752203040040440e00226440c1025074602180c92402a00010701901120b240310740803810f80c0d90f00c4040c07050f00d40001d2100802d0613164030900001411500001d40a441d4400a0080a10304031070b24924148032607000c40d04080308140103000790388020074240ca20540640d1040158485400480da0300c4040c8000a032010070768031078800030402c0c10341c80c0500400040d070341c1103001750321228a0740e11503000b44540e0074030b0b40040009646c1c00900e07002404104055050100c0106803401c175050414021034044503040d0400d25003406944610000103070070410142c019400c003150f00003c40c002441ea0f0101034412000358900c040f144209412003d05000080c205102d8070f140581120098902800b50901081c180f1000401046000032000d105070b4103c8014108091261416102c0c454043e0070010104100702c1e84440382c0c3c440b80020a2024403038072042040c0c0070203007002800c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 194769316 1250 194768066 194768083
    0x60d09020315010806130f0210030501030201120b130e0c100206060a2312030d0609050f0105100c151409061603020307091a07020a0815070c030c0b06010c0221 70
    0x40c41d002840050001807800191785600685808002811180a041010080701e9041000390300280341c3d50802035469042e00914100c0340300380c0f55004a04e104680301d002303441c1c0a84500d5041800e18044500b07003000d0760007451000b40c8030410b0b00c0c170707903402c0c4804a40c05001603040600580c3c00f860a00145041c2104510000e008901d901d00342c0e1015039150007002030380c041040d4400c0c5244501080d101c10144102ca401c00d001050411030565501c45e1726028000c100c50303041e8042c803100c000040c0d6041c108aa120b00d401e280d034402e145540c55540d0801c030b00b40d5100382292819030382c044480380343d180d040580740514512001004a80380c00207100c807107403a118524104040c014018480344030340020104050f540001c0c0003440d089403080100c2d542d8012550b0280d84441a9180025000c0001c1440c00440c01c240142c2000ca6403820816039140c110004000c1c0012101149880880d404000e5950410814075011b03280b0201a00001c0e54986981d540c002d581074090180040d842e0100401c07030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 194770566 1250 194769316 194769343
    0x70806090705150c010e010501080a05010b040b010503071206050607031718191502040f03020a0603090c090207150f0209121501140d140a110f0a0303030b040902060d090203 76
    0x11005040c0b1001c20380c00214400003003124a0041044000c0000c20f4020704410a0721800030001c541e910380e001c554a0910303a0042e12154a04101152281040e000c2d0700f5083c141a11001c2c919103079407000f190203100032144944410f603160008a100e940e408024240c8a00035941c0c2c8041451901c401482c540018154a00300001c0c901d80d014203800c0801e0034140c6080140300c0202a18440c04c00582c0248040d00c0c0c001c241780700244c0031400f0900c2c40c000c0c0c02628026560341c3d50b115100c8205904540c2e8800f0007034280582d1f44020014070095030000c040791803141500740e00b100c00298101d01a580469860000c0326004030f20f085140c1031200e44800040d40d403100500b000004102c0300d8480d040d0601540e4005007419841041e10344072030f144502500e504c07070032510000b03205034025501d0b0100840100c0d40b0f0320481e00c0004151034482c0310040c5104009107943c00d001d02c1c5582c02d0f002070035648500e039006901c07a1500f00c0541d072080090020b402c0384141c0414520ba0074410141017201005440 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 194771816 1250 194770566 194770573
    0x212010b031612090c080f0111040e0c21250302040e060907031107052401030203031b010b19210c1a09100f030f060510030908120907080609 62
    0x201c00c1c461640b503400c00b060080d0030b1503180c000c100d00b0031a0107050b04400182c1a26040f640000718a003000410202c03840d0340b8002007001e0308e6900b0100401e40705e00e2148001e072079884400b080052201c20000c100c0e20744140c2400051125030502461060401c996843c03002d1a0000d0180039400a080544401070540c90b00b14945814020659140b80d0041d25540c05000584e0004040701d00a034000b1342041c009407102c0b61103140314903080e565000461003007400c41c80c4140c2e96140750301c4240007840c160b0b60300038069410120034080d4400143e56200c4060440c1d900c03403200020680711514114684440385c40c40c10011070034001090519049414151910800488110085505030190409652604015041d80710140240c241a8094000d4031a0f000843c00000020700d80c00849510004800c0c0c5c5042c0403e072481c0524400b100e029102d1540c0000341c8120429419100e540801c01c0c00f40b241c0302d0107023400210943d00083c0242203402c3c203400c1d4040304051000d11347c20014103a00840c50b000a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 194773066 1250 194771816 194771821
    0x109020103060519030f08040f0e09070501031a040e100f020a1d090c0d020f1c0b03160b0a02070915030b0a0615050901030905060411100311030615040f03060212010b03 74
    0x82084800c014417026040d40b41c140c200720100481070301224024200301c2c800c083d025482c0c02c1c2d03440e2288020f48902599203c2ca007000181c0794002d00503004031003800405c22a5030340303d0f001808042c0c00b2142d014101801150a1080385d4042d6200b03100c507101180304016114040c0364005841d43c40101c040c96445183c111400d4400da4489503d00d610081230500d00d80c9840281040e90040e01070380b10a5280e035107022902860988801280e080102680c030002d1145600b400181074071241e800c00b00d01d040d8403880d031043c80b4422500b0024070070203403540f049400700340c1d0781d025178411540d50079801d08800c10440c6040013402012186c5681061031400108603182c079290300078440c4c2d44410480f42c00d0050110301180240e000e03600900581c2d1300203080c4d0b445441e147c580312090881e4030442034414842868000c40491083c400d0003001000c2503460f9286407500020043c0c001030030580300c3c882c00001c010100d58460300f400d6500082d072240101580b1040702000300045824140c202720003d6009004 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 194774316 1250 194773066 194773099
    0xe06030a06110c0d05120c030f04020f030703020a03060204062d030902040902180412050901080103140a02060f03010612020a0f080406060f030f02040c020a0c0e0910050901090201030605 82
    0x121500c0c0e155010304005150740c0007000d084514040c1c40f030500d2860041c0c200c0850307000d4102e0003d0004c2040140048400c1d610001e40200c40e000c141e0702500c4a03124807001400504102c0701c01c841a000007000c4441c070340e90380e6000400b072440c00c0e00708507072060f00880e007040310580000928404104060210f410700c000b22221528004e9051101410141c4400f0080c00395112075200751130a54019000c0b84d84102510f0700703c4010702c0d050340c044a042040b01c500e18031051240065407413161050303498200c2039185886144508030308596500341402544030301c400581c1c0d003d00038003801d00000c05181e00d941c90054042d2010840c0342d54404800c1c010480c1c490421750080d020048100b0905040e40c054485050a9008042d1500503500c034a1501030080f0901100c04549180a48225030900c0401e80d500d030101c0e180c110142e001006280c07015414040240c0c42c40c0d5055101d110f003400c84002d1000011840140c074020f590094240c0d550350003460039035030f0500551000d480256a000d804002800c1c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 194775566 1250 194774316 194774323
    0x90c0c1109060112050415050c090a0f1d0402040e030c06070e0a0b0319061509050a1d0601110f030301030f0302060906070210020a0203040302030106090524010806010e040e01050117070e0603 84
    0x1460a0410303a1741c0c200003010000c100c0c580c800d03142000c1701e08002600c2c1040c10301c50301c3c0c3d0003076280702d02c203281a200001e0600003c510340d0007030720007040c0301280c01200c403c80032034100f40103413080741d1064540781c80119a110400140207200c13203c000804c1503050040001d00303003c40d4803a03214024000240240103070303214041200c3d00029800c800c003081c801070074101801000c40f6009448201501c0001021940d0320280d960103840c0300b16258030b41c040d5145070200000c9881c41e240600e071840800010070a40c021441c503200f154030101540d0080300c075080a181194000d0b0411141001c0b88010b04091507410001d0320b50040310300d4020030850400c018041d51714a02e00c60102c06036a00024000d0941d4400d005032401180c0c00b070001c0c04441d4440d0346d010054441292103540304400c40c040a0f507072440b130700030043e40c1400c10385504071582c4a01c0e004588120b56441c6035070b003183c1c5030381100080c41402d11815000f014801510820400101039480c00c0442c2e5a21009102841805106079590b010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 194776816 1250 194775566 194775587
    0x190f0e01030b0c031f060203040611010b10050a020a140a0c150207032003010906020405120307260405180405010e01020405090c03070c050d0c21051c06090c0c11090601 74
    0x4407243d5100da0741c045442d500c000906a20040d400300710f250014030103400002410585140707482d4911103103e00c06134182258128485643e1010085c50034072102406140204070400451040c0c8960014a4039000c2070b0302284440e260199211007411400d0012100500c0040c242424030090000c10300381e030096079800b541c00701408801820b07600099450607540704030f40c2303a00094000e202c4180c1c107080110003504a0b100e10b0303004101503c2d00e045079a001104603030415901c40200d10180c1464192102c00340603a08800190810400002c995591811850650164900512200f518240c034109081d01c1c0031161040c2c0e80d0380140002d101e10768591000030741c031002020359035403aa0b84080b412140790459504c0603245000d21040c070280306910901c516010350044101d241d0a002450010151b015801280c8000510601c008205d25034498006c45040208ec400803524985524401c4c0454280d00444804218103568031000c1100240d43e03045040f02c122405d03119880c21800203001d00005 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 194778066 1250 194776816 194776831
    0x80402120106051519020708060a05190e0c0f060412110f060a020f0d0f080118060305030d1a0d02030d0809030d05040b190e030405010c050c190f0e01030b 68
    0x180c0515100044258414001840000c0640300c81e044049062046503200d84580c1c1035881d02079002c000300c940009000343c00c50b01d03264001c02c403656682c6401401460b01400350390340c100b001010380d041005140107030445040304038007030a42c101052003000f0b8441c2c8042482409840280000c210718500c07075424011075900007007441e0000e1648400030380c8107030040485541c040c1c80801c01c4a40583c1c00108600c1c4614500122249030301001001d440c0c81404140078800244104010311200d000c103810b02b0301e9425203040c082096600e0f9605d081c00d58010030201c800403903075500e0010719078441843c08000018159205a83e105682d000302c0d8640301740050a4060162510210710340000420484d12084540b07041044503051038603288400030b805880ca640307110f08544a040a1403014071551201f0142840214603082c0f5020040d5040060417805076098080c900869400362a45c0403d1030041094403c03095020303042c50140411280c07650091210368a1010062000428281c02c441c1c00007032 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 194779316 1250 194778066 194778079
    0xa0c02100905010612050f1002070b040f0203030d060602010203190608060c0307140a170610080114060d02040f08070e01080c0103090606170a02010905030c1f0e06030114040606090303080402 84
    0x71410494050401c9900c840a286407655690045c440041520744500750000141c0b8040e103002408401607014020015080068400105001802070210f042c1d031148050162810f01944299400c21141d4030750011015035000400c0210100142c1308c85150781140c08001c000040c1425052603940c28024802c403800301000011881c510300920300c102c404900b400413076540d407183e403400034111411092708442400541d0040396242c608201c1040801c00d084c1d60320b02d21070f80380408125424004e4602c46400c00820050040c030451030b8001400580881050850294500b00700c240c503045050340311629141200700180202a4007040e0491545c04c24a00401c034200207090110060805a00c08142ca044101040005a002082c40d4a45034003d03201c582e40c00c2e82d01c00906440302ca0155680c0d034020780595581240c0c00c8401d4002d10509014a4203080705c0000c039000c140300c0e602c20f0f00302d007005000d04000200e0b24640340c0103150280a4a16100082510f10740c1c026100240241c0000d1087c0d1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 194780566 1250 194779316 194779331
    0xf06190305120306011b0f1a01030f0b0601031104080f070905070519021905061e090a02010302130812031f0b041206141f09111207020712060e060a0c0210 68
    0x84c420741c4d00001b0a40b2500343c0500c03400092500e251004c0d188a000c503005000c00441404800055408a040781d820403040b40202c001681e89480d081070080c04103061641e16484d40d44584100b6003c0d00283c60110002c20021440d601590702d00f11045e842300b02d80d079040c141080301751030303002045c0e030429450300f00d242002c402409800d0341443c07854070209440c1a500020030341404000541540500c400880c2e5a010700c140240440301c00380c4c1114207000641c41103a4540065100b94003c01001040b01002d0f0480c80d11201218107246405820600c0a00e0100c18841e42e10300e10405184810183e42c800d1604515000c085c485a000b04c2c440d252070340f10300506010501c00d03142c101801c0c43c1d407410511001482c000c004007660b2619143d0209020103480004102c0401620600001c1c55409a025040c40406d40100c1068a070003001032003140181240020b1200010006c08041c5114100215107140064241464603000900031200103060400c440c05554010440380da4641d5480320104908 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 194781816 1250 194780566 194780569
    0x909090709050a0c0f020a080406050a0905090c0304050f01090209010512031e0a0f090e0112021c050c01030b01020c091b040e0108010606030606080f06040914060f06190305120306 79
    0x1451a600152625007028100319144038107500049a1004c40e8884c1802460344407001c03070359a469000000c100c840204003e007c0c0500940203806c0c190440e1421440a40d21031002c0380301d019055903000e14907a0080207020030448280850b0f1000200c400003003015400c940c000505156061103418001c003644d5040c082c400c0030520489020004404981208100140616409601241c12030000a00864858412a1280c903528088440c40250020207900340f003420418103603095000c0b40d00000c41980000c080450300381e40b0782d0300d0340500058140940f98100160a42d10b40350440340c115008039610507070942d5124501500002108101c600c64801c0410030061445140c11610000754420000101910150803500a5a240b6a03003400280d50341d20040e210010309850390340078131441c040041d0302030420307901440e040c40c020210540701003c0350003154203061042d03c84100400542c0104042410407000200d01c50011400d4030350030605d541c980c5621003c1c0721441161126000000c078809 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 194783066 1250 194781816 194781823
    0x6060c15190c0206060a0801140105100203070b01060309020a0f080d030c18170f03090d0311010f05040b0906060f012c0316060906091a07051006180e0d05090909 71
    0x65191100e0812040c099400b010395182c0e0101e81c00c0d4070a041c17400c00494481010700844000404030b40e28050300d6400e0004009147d0880500817045100600c0781d980070401043e266802807109031400203036900940140114108541c004440c0c0d05819181040b00a10018054086000310300c0d00061016200708102c070312150480d201c41000c0c181e0103000c20110b48045e541800707065090110b81c02c8129800b03420f0384078040d09180c6a840300c480c074208404217004d0300c0c04020f00440d040c000551250400a4030b012030b1001d40d01644c1d01c0c40008108814003400300a266003028048030b00704449511440001e000000700f0031a0a245603086440c54074610f070022204445000041c10340f02c0c040040b40e1126000240b034464540011012000014020b0003000c84500b51420120905441d0100180c5584560b00041e0111128450101d801c194000035114040141008071081569400c407142c00106403000017030074150b540c02031001d808146401c0030032641100b50a94401e501c0d0742d0f43c801d51a04 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 194784172 1106 194783066 194783101
    0xc120e0405130f170c010c0804051911041806180b0f0105060703030e1c0e01030b010314040b1003050a05010207031407020a0e09120705060103050606060c15 69
    0x851a43d41c0c0a580d25110b02c2c0400f45011207070f081690844071f903440c02000090140085c40b08010341440508441010f01103404130100494407920115161103280501c51995440d040d895001101c00c46004a500702c030040250400d9006039014044034590704840016145002a20030660700100034184c8101802c401d06241c01a41c0540081040d40c545003031a00c6880c80b8822031182c0c544ea441e4801d040d43c1c0c0d070060042c0f104030000d4169001703140d1041c141810145d00350b052800c10300c04c032984940c00010942045e112411040360b2103506410143c55805020303014000d00c0015001042c01d42e109503240300a410800d800b003807250003407140c000d50103c4840810410324910445443c0c1040129098500100440058032115404124100c1d15a04244010020b0060030b2190075802030095903000d16007515603480e283c443d4a0410f00b44240000c80000c542c0c1e001441d000081c = true := by decide +kernel

theorem cover : BRFrame.Cov 194604316 194784172 := by
  have h0 := BRFrame.cov_init 194604316
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194604316 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 194604316 ≤ n) (h2 : n < 194784172) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
