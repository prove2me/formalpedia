-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5469
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:57:59.848982+00:00
-- url     : https://prove2.me/submissions/0a0509b5-682d-4a2e-8a6b-e48949208a1f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 983453237 ≤ n < 983633093 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 983454487 1250 983453237 983453323
    0x50a020418061b0905010e010e010e030c09042d1e0f080c010504290612070b0a0909060501080702212515090213050907090617 56
    0x5030214180500700311a003404000140070b00e140c0907805071400403490114600165070ba0366075104070b8640004443c80c9030680b4941c1d012588401c51003595600500241d105460054115003d0030344005c000b805403682a18191100a00c0d0740b40c00c40d20755028511406101240701c6000e1041c2e161345c1d0b0b0304400720860560000d07440711406a01041000983d50f0b0800d6540010826807107949070017506000b80740c1036030211003440e0b41c1007034040c45144002441a181a21540e034a64903a9904107000c01a44103240d28074960050a01c041074915842c005408403c016550320100d440c00c14214a080318100d4100d03505010081042100f160360002c4c07041c0688a107945c40046138009000307111002c0c01070620501c60b440d070480304085000c00403c010344910707014080b00c00c500e10703201d842001202c030380110280d0820507484a060040d00c0a420894219041404480301c080ea111291011070745c2640200400c1d42d50410f420180700800c10054094103030841300030070381d11500c081413078295140c2a046 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 983455737 1250 983454487 983454491
    0x60206010b03070e0a06051206090c0706051f26010203150d050a050304090903180f030f050f0118060c140a0f0c06051e01140d1e0515100501020109050a0204 69
    0x525403c1c030404113060401c0018019204242c0c40341c1001d81107411041e1000c07036032099200000d0f440e10b003030482980035200e80440c0e149800703519101c0741c1c0a400d00a00d80b8400c04e8030003002c0b05024a412410100820904503910351a1070f00015019040354800c2d003181e102d80c018018010944414101140788460032161403000085030714041d42018031069024140b40408074000a400b0010b400402c01c0c40e01c00d03610790200b01441080c150504620b4040e00398440c0c20024140005071052180d680b840e406401101c0780c1c02c200c45609030a43d041d620703004906c04a1360580d10204a176070b008000c109002800e10549608034500200168041c000c3c0020420440e85001030700300d4051140808a80d406c50030038005840c04c3d41144445c0c50b0070344030180600300c04200005130150110044295680c00a2403441551031944031038050814076440d02c0c8065402c2000e10b0300290080010f402c0381c0e001c513181c5500900d0001e20300040701d001075100b5810f590600380d074680000c902007207003000242d0440740 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 983456987 1250 983455737 983455741
    0x9010507122d0204080c120703030e18043804170d050a270305032a0721230307020f060705130f0b03190b060f0d0c0207060206010b03 59
    0xa2014203a8102010207403011090014522410302e41c0052041d41c440f141124001e034501400d010f9024110a150801038010703c03400d02c0041c1c030400109200060003840003441e03070102110100c1518058a00302c403031000415000c1303044002469100c0d860040c3c60f8042601040d801c0c054030034014001d0004019900c03c5422486850403602503d420403184dd00800481c03074041c008100501c15400707610700c0c42040901003807a0f900c3c881540c1c6039050341650f5060958485540400742034035078103c02000d11440d00c168880e080116406000001d00070840700ba010005040e50140c04900d8803070b6142000700d0884080d2840b050003100f682c10302e00c1c4c100601d6a030b0b6a1920100d0400c0f030311540107a103a00440081c040c44503481406410707100220780d12148040d5644a41e601182ca0034030030307440c4028090000840e25012010500040d1407000400706030807000f240010b0003580081ea20310340310340340824003000c42c840c03e22030b420001c5000e000900c101c0c0d0034241f0280d5100c03414847d4103165000000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 983458237 1250 983456987 983457011
    0x2100e1c0201230103300815060a0e0a080106060c111201110a090b120103110d020910081203040f08030a06031509300f090f09140901050712 62
    0xc0240554a080b407072000c40c500c1a20010100314000303101c01e8071806030703040761b03650200450300082c0700007145110b461940300e040380d005944024004200c4141c3c5e40d0081d842d4445a21248000c002d20200b603a949501c101c0140100069a079040d00301c0542685001c0d02440b20603000700310140788640180d210800c08128000081e40821030b182500176950820070084c10203030000018007500e00d000d4a903401c080381c0354080c5000c0b41c000c000d1faa510036039481004001103541480f106801500103001451103003865000f02e60305440a48100c80804100c0c501048003071010302620328500c0d01c0c2100079145041c40d0b01c0e1481e801c1080c3c01d001e009410000013080c042001540300c400103551004400e4000c091008070503008224250b03003074540000900c244580112400c650981c4141d004040c1042d9403041c0d08100c0f104030704810b041e0248404031501003075030750303121400740c009240f08213000c58a1100700c00d0611300c6400241040c65540c1c1000240040030750008502c0c141c0c58030040700002c1d1a1500c04d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 983459487 1250 983458237 983458241
    0x50303010b1c290f30011b080c0d060f06020705011b06050903041a09010f031b11011d2803050301030209070504210203060903040e04060e0c10030204050102100e1c0201 74
    0x28004c075030b1003415000b4050042100485c00382080c050710507007025011090098034241c5101d440f0052442038840d400044090084245640000591180ca42800141d0f800c1008441c105c0d000f44140481d41c84080240503410044800500300a02e01154002c03440700312402c00707074410b407401010b103a22400090700815003041070360b0051410701c011180740b4100c41d00d15a00c1e640030700320706400142c90341841c5218900034001c1120300001001304800c200c1414404450503409604000501e5480715400030039017050502d4040700340d0b0140e000e0498582e518003c940d041c028200c2d1746001c040c5001e41c20b00842c0d04501501e0440e601600c0042080e660441d0441c0c0c030744255000103240819503a1710100d008192509800114030981c101e4041d601c0d8102056580d000d41d101c2d03500140d003004001400181039030040440000560211078200010100203508002d41665400010354045401c00031580c0c10064440c1d29180d00600300114004220482d40b0b0b01c6640c1c5c120048032942200c1003c20510035 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 983460737 1250 983459487 983459509
    0xd091401111e031c0c031a090a0b0f041a0a140a150306120b0f06091b280c0b070801060e012609211204140a050303010b1c29 55
    0x4c1c03015100d0071245240b81c1c0d00802d00d81d0510030000c3d14280209240410b1401155000000100300d000555113003002d550181003005401030300b00c211507034003245a880302e000d0a001c220181d4843c5914807100c0d003c0c020f000c0050381c4a030340c010159807508045902c4801e2903500f030741d549124400e5403080300030059019046030380c4691034482d0b03102030100c24403224542090080e1a09204105c898032400700b0072100720300680341c5c56801c40c50155184004500e4200810140c0d00404100c080f40c2c024103d180c0840144808000105181000300010880ea8140c1d040e48108581400c0c1c0c45541080b400034a0207c0f1071030011306000002e612041c0003040c544400a8445003500c601110303181c5002c16540f14240b0321021075440401c103441d59803074106201512001001c1c035400c102180c0d1181c84000e0b00c4800d8402c0448140100c2c402003001c201305000039030103040a1910280d5400a07034668001c080c483c4507407010b0311450b29015509080c004800f00c0c0304000c1c0c81c21401403000400000800d14070070 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 983461987 1250 983460737 983460757
    0x1a03040804082a120d0309110a080604120c03020d21091103070f0b07021009080a05010524030d050a210f0b3a050d091401111e03 57
    0x540f039001c03060184180f40548042655070344030024416404140329450500550b01c0104d42c011200010340c40f4801e60001500f14050304004440c050350343e000c11110065901300d030495802c080c00b000140f081c1d94164200422251801044c21038446e20029281c81d04e204001c001c12010351500c0ca813103020034606032100000b55000304041c0e60f940c80c0480981c80754008403802401b4034500051900801c02640c401c03118000c0c0207a26000a0740c2c200265150f04620b00310520076201e9012404201c2000084a00792060000060314206001c0c8402c2c500c20201102c803280c54240c1d09031800b61404200200b8410540c100180c6945090106903000420403040c81e884d032810141c0e02800c6c070480c0c0c00502100403103800400440384080d05101c0007000b42505041c1600c1c80c00b0325246160800750603201410400c041525000c40b1a9a505080c081c0ea401c000c0d0024070341003018411a50000c1504041d0358090030228500381034061200d880c1c1e880c001c50340c40c90b048455180111210f0500446024040c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 983463237 1250 983461987 983461993
    0x12105060f0717090d1107060c080906120c04081006140409060b0d030819020304030519030f0905060f0708060a030f0507030c0b0c1b0901092d0207030201151a0304080408 75
    0x4d0492038241e65200c038001184001074220700e9007644440c01141d040181c840325a99103424110039146c8400a070b01003c0103d40207003040109149000105c0c9406009098203811176a42d00c0c94101e06c0c0d031924006001205410340341c10b00401c09800c070300e1048549054142d4001c10003a1081c10041c0041c51f4819206070019158040c090403d503209240070b00c02e1429462045030a9001e02440049010032140100411340800051140d070420b00c00c4690b0440041c5801720340c1400c40c1c08800107031490510300321003d0b405542845001d41c44002c8569204034146083d600918081001820500091002900f080040c40710b0b0014007009000d4003000c4c58104000510850b40d4851000341035101441c40b030494065203503003185c7c60300303c003000031a4000024401c0b61540d081054250061082c4400500e15202103800140000c0c089000340c610f07007001504c0162194810706020742582d000303c2c0c0b58828407219a1080c407145404140c540e0030030403800e22103510f90742d442c50710440034400d6420041140c4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 983464487 1250 983463237 983463241
    0xe030f012c010c0207030b18070306020a0305070c020609060d0b091f08151b2701020d1404120203120301090b0a0b03070f0807020102070204090b012105060f0717 71
    0x111140c5108414940703032440070403505244042042c200d8001c115401c0050300a04020000319450683d032503009a07800071402d141505048103240b400340c507540122034107074000c98007450a0360140b01b451fa21489509109826070a1540001d169111700d4004500c902000b05554807182c1c0d19070720070b4401ca10080c0800e0024180043c48009451092140010704248110701007001e00340811041b440d0720b900c200ba1800d989695035540b0358411100001c0c88202c009021001c01584d2444585011104e0352f0341368450300110f88002410410324580603c01c0c0031140780008290b420083c116002c0b038501c0c0b0142c200c1091244002820020b11406012042d1800300001c10800c83e01c2c4c0c00b2010285044070100025903480360500d13054042180c5c05004a0b00794602c21201034010081c2a0f44000d462000514048596000501700e48441ca42685e046c2e95100040c003c0c0208102d02c2d45e000740380900600354200703540d52525503d64000300b010040d20200c0b00403400d814020a0003000052080c409200c8034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 983465737 1250 983464487 983464511
    0x10060f05041a070605010b1606051308030406060602010606050a230f070b010806011202090601140910080f0907030206041802091e18060319170c0717060106050403030e030f01 77
    0x141c0020f0410b0319050b00d8200001214050102150240c1c10411442d2540780c07410f803110401054002c00054100104007820300c0000c102d00000e5205d9440b0754000181d10303040000c02400c503951074010b08140202001a104c03030039001780d204400d4002041441e000801e469051031001d000700d01d004501c09501156070410000744940321030680304440b0807074000340c0c1da80c020362a05490b61880690850b0040000c40c03001d52051036040303100301c03100b10900d14040080c0080380d101c5081c00010400540369006210414064001c031580010a21005105071411900010450300c15441075031082189407980000078280b540607a611424003d0603648412440100694a15a0b078244244503500141d0701101054a1451845c0a51000350007403004c12000d0140c0e50940031008000c1e540341c1c03c0480120058003079003009081c8115400050031007035141c07040011452400710807200194100130b0051015070703401400d5408481d098a4005807102d10000031074241100e1618404041d402d0101c58440 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 983466987 1250 983465737 983465789
    0x50405070f0f020111040e0a0b060a0c060b060405010918060918021c080301180209030a1b0801140606090d0203100203011d06030604110102330a020310060f0504 71
    0x4800054480c00b010070200c040407400c8a0405829641c1004188420301091010442144d8040d521040008100440100007065a00000d11400004544821f07030020403455020300000281e0547e0190304003810712001805052003406800b011030780311403005045501c59000f010050800304810460030b003209851860b039011241051f40101e022034011302c00d4480301001c0d0202c481c2c020080341c1c00e42c0d003400685c01609080e01d041266081c0c0a1040d9815039500340885a80c0d1445270100c200c0a051b0040f41c40100000703076001c04403c0e40341c122400402101c00c00d9032940800b0846500f50341d17a4003c800680c10401000f80603405205074001911076440660040d8180c42e40341c121018030101031206000138140072130f40380350540c00079000b04d8006201d08206104511050040c3d50351000d0710701030340210841049043c013504902c402000903c4505190440d0000d500003002c1d4070310f00c0c0054010403c0e82c080e01c04d40081116207101e040d802846042030790081d03d092110100105205030400403 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 983468237 1250 983466987 983467007
    0x922030c080d15080a0f060b010e040f0906200a0f050d0c08010602060a1a190b0706020d0f0b011d0102010204080d02010509100509060f060307030803010306050a0b0a060c080c0705040507 82
    0x803e4652079040455120f00c00600012807a900071810705840401d0ba850001411440d10058140a00c02451204a64582c05215080d00c140000080c0030400c40c20280140c0760440243c80a406200814102c48208070003250018039082c2020f00c1c1b04800340900703e40fa403244070541000c0500d484c1c4000e03105584140118100d130090390845103251104807082d07007140c071010100000400008482c04c05402d0200703429000042c0701d020245400c1d540c100e00d41c8960320007181241d200394005001c003040c06062040304001407100c1000c10000c0d078264006401c1c80c0d050b41454400881448450700035a10035012100900a60070075607141203d4180081d000e040191850001801a400c0b84298840b0b180305080c400c0421100500c02074580509a4140280142503190540200c44012000c030b032040700111b0007148200f900090310718041202c0c504845090a21074481c4950711400c005859010a240704016003201c04036684402400e8400d1078040036510540c0c006003010100101640c10030b0820f2 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 983469487 1250 983468237 983468261
    0x9210c0c0b0f07062f0408060a02040b0f03090f073c1809020904290906070311040801051003021f021b0102030d050a0b0a050922030c080d 61
    0x101258492000301020b005502541c0d098100c00e0115030041001074106915400303920b001403a60310525000600d4210405d907120300003c50024040160101c20854640c0c4010000001c5061605003106070046100741d040031b030300740b0b80c0100110f00540d0b400d204111017072800c03400b240d01705030b1f5071a1000d00340031040d0400d0340c24a40081c0c0040d00c41081d407002c0002c20f402d54090450301410309821502001602550180860340d500604006845a00c05a405a030003a02c820503c109107450764800458200c842e40401800751301486500400010601d42101720b038203004c500041d5007911120b9500503548041c0b550b42c208404d0200c95190203001c007050303e0080c5c0d280088080340f0401e072449000000348a40040e13000ea607028070084009080010741050520680c1d10789480740c00d101055407030a036105200079a540c074000c440341c90302c09111401003d0a8070898a50304d080070000360740381540c8030312141a903840c5142c0010148100041e201c0c01d903001200d651100d07030640981c0d009103101e5400d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 983470737 1250 983469487 983469503
    0xb1c09060f06091109040c11070311040509030733020d0c030b01020303040519020d080d0e10140a05090a17210f040609170c0c040f05040c0909210c 65
    0x41030f01c803940d010f060100c20140d80000c0c5018500c0091000030001500c0c070104000610307141200181c428080c08009600419031403d880c110174042004650000c0c28030395076680104402c4000400e845010030780c00084038031400269040c0c0d0b2003040c07442d100320201c00109100180401c01d1380003a80c040410068985c0e000c000c6d5400d59001640d40f0722090700c02800e03a610000904030304100380000280520b1015000802d00f0039559075440031740c2c1190783c0c1c0408540c2c82c0c030030381540420300300210325010701c0c0360030b00380420002900e442c5400c8102809100480c1d40301c800041e400801008250821a40400103106002a00c942d20303249400040304170111443c141d000c88900300381000c401380558030400124140303071196500e1a00800701d4100c1102d40309040d910072402071480201a02c03d03009100080d1900c0b08841040000f182c4100b00f107a503c0c0b0340340009100100c4e4200001105950201c5000210450207040c68510005904000f009521507070303800d13030b540310390108079114668855024 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 983471987 1250 983470737 983470739
    0x509040612230a080c030d06080604111f120b0303041e12030e0906030a20031c05070f17071a070e0105030a150e0f04200303040b1c09060f06 62
    0xd002e904080302c2802e032009a001c820700c4408180c458000b0700203c034894040324900300eaa1040d2a06684803540080c6160700148104010300100d9861407140340c004580c0920300c0c00e05116981c601c00080e0058504100c0083c1300c1d0854012a50300c0380303141c1b000040860b47c031503580d807004420f1801820441c10311041504000980069101944041e566041d1540741000003031034140020610000c0140d64503101e16104100410756896031003070396a07005c1c4851101c00040c40706145c036102c03428400e91000c01c5011900c202d0a640001958030740c035800b41200c010080b290400c03010721700c45422450402071000803403004000da004209260b0302d1101c014801c60b41c2d44c035042074420f481441842c2d8045076041000401403049648641b100740054019045060b80380e55131080b00680485003c2c0e6140c0c202300c180000d001000c0090070101d880440c1ca203a011000801103030b200d015a11079041c1921000c985086904d8161240400100d0340c0101046055118180765001d040c4064001c0400c0f454004 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 983473237 1250 983471987 983472023
    0xf081b031822050c0a180e01060c022701260c01030b210d090f060207060804060e03030a1a0301021303020d06140739120509040612 58
    0x1e6a1640100c4a00c0e51410303000e03041071000d6014010409901c18800b10b51080d0350300e116104050003080405201c54560001001c01303041c0850340360700030b000c140e58001c00300031610441205a0669010345007801e0380c58154800706086682e024a83e0050300d00303035021510030303194907200d4504031955583c11104120002d028003d80c14844102a815a00001c078460030b6940a03401174208050090200c81c44500c81030409512180780c1280c11441d0303000300401c50f40090340310340fa60001c0e14035169556015890480041d58507282032162405000741440014244000e0350300008443d5600410f8030b07580e00e072401b91400208580c0208001d41c5680030300c07400d200e050510966410750180c0b50740300d00c0c507030031502040b0140460039411200c20ba1107202050b21901000c455070701404a580350048410210035a030341c2401d1a842101031180c40280072031108880b2501c100140c00d4101c80700d060200c241040450b001d12801d13000ea0b4205040110000d00200048502e9a02a000d01140385104103028 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 983474487 1250 983473237 983473243
    0xa2d0302150a1a0d0c090e160f0e01030611070b010b0a0f0905012f0316060b030606090a0c0e150406020c0603090304150c0b0c030103050f0105060105190c0f081b 71
    0x48524032460f00d804666501c2c00c200100d01d041c40d000d0f0101e00c101907130b10541c400a8510f5151941c0003070308030588258901c2200e8110344003905129024800d0a810104484a215014400134240c41d444410681442090701c08480200740c0200c1d040b003066031100c10303e4285512050f01d103030000c2c445041001d0502e12511030482502c0c0140c1d41c02c03004c240c54240d80543d0400301c1081c452009200c0f01c45262261040000304032400030981a2162448641001c00484000788000c030b0081d04904204061607a0301c014160784070401c0c1d20000340361a4441e10490707412000e41e020300d81101e1410f500302030008088025008440d0184d08513143c500000040c003115020658200c0d41c1903105000502c08404c40b003c40585200062030304003d801056144c507841004140c848180360390f800001441030100900c0707080c00c00b07140032000f0b10044c100703080001d00c107205602c021a070607a03035002c81310062485071700444000b58100d040100e90000b05d0904245580c010b20b1407100e01c1e0a007100300f07003e501e008 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 983475737 1250 983474487 983474501
    0x614090103111201020d18301d03071701320403121b09050108100b03090c04090605060103152d05101107090603050a2d0302150a 57
    0x142145500601810300c90f0340340d42c03154114107554003440f141102d07004510644207150981d200003d5500481e040c459242c241445001009940741158103104a941100d4250750342424680b09c1a040107050010101000305140d80f90315004440002600e051150609c032190340002e0000c214201288204d024505142c543d0800f07070b2007144802019801100c000c181d8083c0c001d0400286400b080b0301e02800700c1d0f04821044640f000d81c010b01d09581e66100e00345602404080c02c0008150411030f813120b40d008071902c00ca5001e450300000003103440d90f00303103c0e140b10707040043c00c00d00107a8000d141c000083c2008441c0c10380040e140010a001d2810f00d910340e48100c4240601c8510b04412a5042800140780e424102c420306810740300006031901e60007010302e401c064035690520209803030640e0345d0800c0019400a041ca5041800c14408144007060741e9100c10707030100a0000320301c011219000e41c2c0c050384080080480308070f1514800c1c19004140491030001c0000d000c615540d0798192182200c0361 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 983476987 1250 983475737 983475743
    0x5041505090307020d0f02011b21030c0203030a0b191701050901090b07030504030309020607081206030319050c010b09041a1e160905030607030606030e01090f030f0507060f0614090103 81
    0x40c0350b051001c21b42c00c0c501142541e0040c03401000007d4103041c4010350800000c01291072072040d4024081c803030184079540d501d9464600d004d04c6803a484000081d030b28040680b00100065541441c1c80c0d41c0d41c1c0d49020801103141408841d45003607907070340005254416150448481d5400c000004621100c10322915902543c003e04e44203042e183c560048000f400000c00880515031744996280150b5901c03009001014403401d9011f50354030851500041011015022500ce9842400740740003005c86e02155162540d46450910384600380400da49006d03000e084256a00700301840240300600400004e041813884600002001980314120072070300e1080118100c82d080102c60380030941001030f0a40080b4040c503145031402c25151600300180c18a18191851b0003c00c0d9500340400c8000c1e01402800710740804e01000304180c0700152907203030110049010050400c403010302040038180c0100190345106402070400c215900c003110465000304420300800462169070804130006180420700241a42c3e4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 983478237 1250 983476987 983476999
    0x1a09030d050d02120408071101030b061e0d1112010f0f0312030b130c090e0903030f071b050c21150a020f0c06180313050607150504150509030702 64
    0x30110840d074542150240c4402c00c0d408015810f480315207003024030300441c05820743d41d50342c03482c510300385041001078440300e414941007180b200030980c2d80c0d0f015035030aa0480c15046901920803211841c1078415240c00004035481e082c1e070000781d00c8203400070780090403481881c03c0959803256840c4084c0c00d110b201b00143c440504800740005181240c500c100800c143c2000f107000011400003036000c643d00b04e403140e6480c0c1d8501d01012a42d0384044440f0080501e60300f1480d079418900340c0903880348801045e0020191040c0042042c0c1071040490803078040c0540425404102e03a4517004e07864488c18640c0724071031080542c541c1100d98844a602c8002c40c1004010915402544408028403000030052168241d0901a001c0c0096103800180711001e2504040c1090789415050326900c1c0b00584000034241c0e00034011101140c4211100e00d06442040380c029840780030a03c2d11f450340f040401d141e0b021039800c090502081115941c12000305450346003043c08141e40d0f091141e596409000c034042d6005e6 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 983479487 1250 983478237 983478253
    0xc0102041d16110c040f0612060506041d0c061b160f060e010c122703060f0c080f090a060e010f060501050f040515160f20090103081615061a0903 64
    0x119240e80311b10041c4006030800301308aa5900e04640090007204815183d072522601005011703c1c1c280720b0581411019030000d0502403804070f000daa510340c440d80b420300414002030546e40c421024003160707290401034012200f03182e402044481c00440584039100100c0d00f408000f159007030213090030704007544040c2e5845000c0d040c55110845000c655520500621103001000c003202604070b100382c098100215262803819103185001c108075440340ad0111111450310724288003c80d4401800e5802802000f0283c020780c569002030b42c03c2840300c8030014400c9180c09540781e43c42c00190400904500044400c010389079441d001076400340305d2904100b00c0031204006c01c2c0207501d0102080110346030084030321401c0c0002e0004445a0600c1404241c0700319000106078420042e208008142c030a10b038200303241454001202054413000103000050100c600072940804015000d40821241074000e10982c0b030355015803110500034501c60103801c051b80c0c00c200607030a01110084c1192101f81c40074005003108 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 983480737 1250 983479487 983479489
    0x303050906070c050402030106050405010e18041401020c0a0b150306070206010603020c0705060409090b0114090a05041a1f050a18090512040b0a03051e0c0c0102041d16110c 76
    0x156021200483d0919103904010440d9121803000d1406040c40303480d01a6160704000002d07140020182101d80f186ca00c144001d404007a00c0c40b0115040b0780c0c01401702071a00c8044d51440c3c064060800c49804a02c2651851400d018150810710f01a03105020b40f169000702c48414143c54402c22104c0001581c0158010448180310b80c2c0100800503400701518003003511030001a90980c032a03848040b07995160420f04040c0020b65520342c0c010004180c0602101c41d804020071344c00032004080f402055940c00c0002c00b402030b5550180303090540703001c100d1420310305200c41610800142c03c0c58281d28400042c00b2909003010300b0798500fa0b4000d015540388032a44c0c42040c4020b403003803213800c4904d801a4000100304102c00d0001e04040c0590107241921060324000040482c2e100030b05000105824120351541607822202d0749030070100b010181c954401031180054003900c21039009150342280b05451501c80d03444c0109440c00341c000712420f9424480c0c0780e0400c484501c400801074500d0781003003407400c4407 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 983481987 1250 983480737 983480749
    0x203030417090312030a020406090f1202061c090609110418060b060909150301050c070305070303050411061b1b1c020409150b040b0a140f0d0618050f01050103030509 73
    0x40b100000c1c01c40e40c0420004028120542007940c03540002d03600481d05005003608020484040c240403000b01074031a20f00702e52005640d10780030020780102e900060244088401d141ca003484c0512010090102c60000d01e410b100516848101380c6a101c410300c0349142629140c0030f8403a000c444442039082c8000543c030740c2c10040409401d000c1d4400010828036155448041d2981c2c4500c0c103000c00140ca0000007810b142c02e42d10010000c0358011020014040040c2e00041592a100d030145000a159552031506041880004003580d50080c0041054403106a070b100001c42100007200503680120f2404881402c0c0030b80e80d00c8038030351214501e50104d0041402120450486000600100790004c1c640c4800540d0076411200159894946060340340d141081d02441c0450f000503103910007024504000844145070701070204d4464184044405031903559884141c1c00300350400c804000c072103400030088200d014500703003c9032103029205082c16400700c18030656049980540303c462030410036004000d4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 983483237 1250 983481987 983481997
    0x51b18062106011a09060417010f020d0e07050405061c0314070f02010216060914030a05010c0203091c080f03040f06090510062301200610150203030417 67
    0x504024100304805480706080c212801c041d0204018000300d50400700b160000000b000906001c0510802140030f494540b8030456007205c0e0080810651504200c6507103000d840c0240160031a41c1c00812140c9005440d5031140100300004022035109a60340d2044c00181d510031611180c1c000d82189504842c0810003229100184c468130b0001001390308441c1206a9800101c002c2d155010008070701c10031540c0400120f20800b912400b010510361408600410495840c024144020904608800d80e82c0302007040051942c2c0c804000d000b9840c441000a40d26040811100d01c1a20030800b410385010000e1000c0b4040703034004080c24a4a40b030f16052050035807000d04212200141c410321000071492500c200354103280b00c2d1016041c50746a403c614000d0301c8060308400d005810321400fa0050202c0c61115451000080c00c10a00b001d140c1c3d0020b43c200000454240814020382041103c2c240301c4101c40b4042d0380760030240c0700e006101c2650880e684c2c0001c8a009108640c81c80f00881c4241542010300 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 983484487 1250 983483237 983483239
    0x30f020706020f100c2618010510290711040b0a03050607030c110102130905070e01081803070804060f031107050618030c030c0f07090b0a061103040909030c051b1806 73
    0x1200d52008111040b0f1b00021465405518900d41000d00001c820041c01e1000e117143d5200080c446810b0101a1a41120070761089142800150698210746030100d407101c0021001d0032450f0703444401c14200107050040c094117031442079142c4445152a490182c0c40c200c10340b0b4001d401001a9500d0071400ea004010618401c001d002040c917458503d080c1c01d000038816182c681103001405171902000718140c0308003070002424014007940178801359138803054065005400f0741c400ca80e1461030500c0f460940c441c21101031b042c500001000705d5015002441c01c1141d0826941c2088500740c01445880107018075500200306410140115001d0705c5d40024007504c03240c945090300d150030701d42c8805602e1340e404114a002d140d00550b1040585400c2406020014248584140004821100041c11006d650301039139080c800c0c011040c0188040030800d850141044920400c80141142000360401d44c43c4582180d1500c40c0d01000d40407804c0701e43c4148501d0502800030f0710712448040d42010750860043c80a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 983485737 1250 983484487 983484497
    0x32d11060d110705060c0306060901081e0907030b070c11040203060a0b03130c080a0203060601050708070203120d0f110a050702040f05070315060905030303060f0409050a030f020706020f100c 84
    0x74400810902c01d185007010804490b0b903880c641840d102d414150b0007029031840980520400055458000c1102e5a0b0f82d001d00c0c0441c40d40da103580d070706104041c00401d80c1a64034481000c00250703200005200056900a401c040075950b15030303004a070f01c01d20011004205030498188a02d050034160081c41e00008000c1c0380d005e070551140854421600121030a4003040c002c00d0702e50b81400900255140584140d0f0040d00c4104a143c011a503182d101070005810044002611002c4c4800401038441d01a80203050300c0200f40e80d0036100f10150030043d440c0036100e1800a4180740000a442803a81e48080f2108031820304070004001d07542c030b41164030305a80041e22010b9070403504150307100d028030825040c0c03070003d1034613856030088070824800c1d002403052044225091103103a8001041ea98840000c5036020307480000c200c04280900300c018401081c40c850300d807088042580081d841c100d0403030075500302c6e68201c0d940c00040380c1d60941c4c080c500f5481e401840c404420080c098001181561aa081c4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 983486987 1250 983485737 983485747
    0x5030d0c0507060e0715020c090f040c0b0d09110d050a0b1e0f1509010602121305130c030c02150115031407120f0605012705031204032d1106 62
    0xc400030f456482d140c07140c880d004510f0070710842504451099203908148008c1100d400c0d00710114140c0c403005442500711040b90720020b0200032281c040c0c18080e2001000c0c40d5124101205130346c001e8034231500d08545202c407002c12a4810b051400d01d0100e169000002807000304800c1c1c44a40c001d10001d03189a200c2d200b5500000c0039006290341c407900503000f10351550000c0c230b8021a00c003a96400b42070064403812202c4010410140e00050041a00001145107540c2e80c4206030768220f003da040d8803880c0c000b0005c0032982c0c400c0003140d00c00d6a40d0011514148403140c00d059080740c54084110380552f003446681e0044c05061710b4907500a0f5110030b10b00780010b5507142942100c5018208407a00000111a1070f02c0c980c040081d0300a851854a21320410f1080d1410007002814104401200010039031100d4541004210030448820003414041c095810103513003860b40041d558050700060f502c40405a48100f80222600007440000d00081d48020080b0380c0355699805602a01c02d445a01c82c0040c00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 983488237 1250 983486987 983486993
    0xb0402100e120f060603030408060f070302070b0a0c110c03030d0e03040f080703030210021204030c170d0207061503030507140705130f0e0f0c010f0507060e0109031b05030d0c0507 79
    0x40b01d82d41196540020010210720f0000d091400c1c10003884140607400c14001044030400000d07059400452031204c04c00c89965040044009009680000d882165014280645001564400c1e042c400310f03039441030400740c00c903840190b0312000c1c2450160140d00070400010070510590001d44a80c0d05c503400d4903d0250f50312079600580400c1e0704070040540101c441081016010810042c1e81c10b510041507040442c411003078081d1400040c000b409000302c8625040400032503a0701c0a051850803440c090320707808000300d00c20003908180c20849401e4600340580719420070301c0501c1400c4a40c10f50f40d551031715600b5600c040d5001c240840102452103181c01c04503095494040039000507030b201400182d1480d4824400b030640c2c40c80701a000a0750030032001c01c00d000348080b0b40a0f40500e000e0a00c8000c0066042044030207104860020341154a811110b441041064200041c1e10f4007035910100000d4001100b010f400d0300038000100306920030080e01d1500d01883e049214007810f20305101d824408291 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 983489487 1250 983488237 983488249
    0x1062c010e041e1b080901090b130807051c14090310111918140a03020103020a1808031b15061306090504050f06101d0a02130e06040c08040b0402100e 66
    0x78244e140c41e003050200c01188298081e2601d40d002c10310000078030035511903445505002c4405441d1885e416114400f4200340010b240440c3c0c00320340d1140c00c9030304001e40e00011048000c40d94407201e000950400f10000c4200344003003074609c9408014064036440b002c00340003a008241c02c11310102c0015091100103070601d071440c14080e0000f0551074111921042010038500c0c0d080f950014101c4040004040c51030b612540c07106420707240c1c2801c006a48207003002095408403051300825041070481d20001ca08000d011014080c494041c00d000f11070003089240070350f22111140c00030480401c2c40350019100740307080d4401c040c0a502a420006042da164400790781924000c45007034030540d002460140c3c155804000340c96206240c06504c3c1021800e1641100c00d81110202c503261540e489000310351010001d030b0403180310049140c0c0da1080e895a640c000350349903c0448106224918140309440f681c2c0c041c241103840ba82c0d010f160400d40b0b80d030301c0d800c014a40340302c09039060420802400f11299500e40e1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 983490737 1250 983489487 983489501
    0x409020d050106050906121b120d0c020a09060e0c09040b0612100509150d050114040c08010507021f020a181205011d061303020f030301062c010e041e 66
    0x10700004500340781041e05004003140040c05a600445412912036031800020803070300e042444074500001c420a4034000101c1d80c40e802107108034a030068060070104a5080345007956458400c0c1e03401e18101d680c5454110844640b8850480c00c800150001059011204000d02125a0040c80080c0b510002d1000c43c0003900502c10b9005030422a00c1070004990200c090341d002864209c0d903585191a00040b06594111854107660140082460207001c1020a41101c48001700c0340c0160307076984c6018209021082c4c2da5104e904101e528200200702280d1020800f11042e0024607420311480c075078921000f000354002c40b040c0701089404215005c00310f810304004e20051121444080302800182800350850320711104405240c08410f034031081c2141c000c9842d507031218407404155500811814242d00f40031201404e844640030000003c6003141d040228100b4910140000020465609c80d0400b030075031050b400a80480c2c0394500b081d945107090303042801310329918038441914440c10052071080c0c52003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 983491987 1250 983490737 983490743
    0x30c030f040918080f1c02070609031214060d1103011e0e0303041a0c0f0307080a14190f0e1603110108040c06030902060918010602120408031204020409020d 69
    0x8001010807580070140100d045400b0022020341d1143c030640c0d15040188a2034605421410f4081908080540c114581b1454000100401c1d035450000c0d24000c030042c80c3c0c82c1ea08801280c666291068113545500c10410440d04100d0200c4e101e84a103800c0021b600703a0710000f11030340007034424070003900d84013030107030901007040c1c207000e45400400785605a0135202d640d40c4254a0758401d104000214001d03141c0500c0c0000b8044c601105034894130b445554501c9500c1508002c82c2c000002d01411952010049100d5a13400303100700300000c510015200302810555080e008201020219800024583d00c0b101c543c50300c040b40010b00ba45032002503030134500c0742140284412280311040090101c0e100c81a0703082c006c24a42000186003da0b28182a403409020f44010150381d5040d40d0215200d0761b0880e0b070070110060411030060540d01280e050b40c5024011800140030b0802c03150590315014007034400303030380d10403024500b425440610b4180c1101c0040c02030303900c1740e1922022405a20f5040d101080700d40 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 983493237 1250 983491987 983492017
    0xf1801170309010912030c1e020307091a0f0a12050123060a09111b030d0e01020a0504050906031603122304120f0203070902040504050f04020f060a02030c03 69
    0x214180c0080008041400805480d40040050b81426070303104030fa8006407038540400901c100790074282118090719140c03000740712045902c09001c45c01a20049101c41c20300c01c800320303004291030303010740c00a0b0f03505049500701d48030045e1890b64607442d001c006400f000ca40038201c001e20550340c0c40c80f581105500344082c0d410740d40d42c18041c08002c841c1000da042415101e100030b0700509110010990b210302c10f1050745045a921302c44e00d5080300a240403120010400c0103000d030603150307030302c541c64417540411902007003245800e0a07002e0221041c003c1c3c03200601151030707241c1030504d4001440300c0d0390b00c0206126410b0140d80900001c0801990130a0302540c0500501080c03004400c101406608001c0b0056140d401c1080a000d03901c542c2c4400c641c150b941141001501c04040e1800341005070000c0d02c000d41c10300841801044404943c1d0241c400c40d4003c40703003800981c03124544a00b4100041d24042e4009880510280d0a400e201c402004441a5441142d1801c10402e1105045030840040036030624 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 983494487 1250 983493237 983493239
    0x4020702041104062006072003090310140906190207030c060903030c02060c030c0703050a020a23010f0b030709020702120706030c0e03030307020d230f09040e0303100905060f1801 79
    0x3404071000780b2180c5c0403040062415050212016010700c032001401c1c10401c0415003210603036002407003580d0140701c000d400c03100000204070a15024200c240522000c044c1403100281a0b1007001840034002c07002918120311011100706c1c0b840203503100c04030076420b02c4400d0141400246580c890b85445d54001e0360006025074401d5030013414200090801d40c68030405005000c1d004000707204403102c0c0740e450308103d680c910702054160308000d107a04000d010503400f005809203681c2004803118401d0f00d080020000080034184034022a00140c0a258042d40441424270990382c980d8010944140000c100e400c54151000322640b5000d5180c1203c800252101441c0548a42000361040c0009048010b10700b1441d01c10030083d91002030118002c2000b2a9075101d51108490140e58654000c03200c0450b651180c5000798101d0aa01c54120140a00c0c50580e000501c91008415a4010241480240e10031450090040003800e0044d21b10340d030200b614000400d1a5032044200301c1ea1418400800c150b40d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 983495737 1250 983494487 983494517
    0x3040c031208040b0f06010e06070b0f100617070e060412020306160215060f0406230d120518040204150e100c080319180c0b180402070204110406 64
    0x1010207440680c0c1401454030074040000c040302d840583c41104036103600d01e40d640740001200c0b041d554200c4507402260010700242440541c5580a11401d900c10041109458101c0041042c10302c500c5a0300011307503101c0303e0502c60b41130300241640140440c90240c0c02c0a81810001d00c5c2a80315501c07101e1032a002d003028100318202404207640c8410784003c03803652210707000000317900c40f0411007047c00b03100d42c07000001340b59a07a2081c142c3c6025102405c00c0110035110354114061040032504c01c902c000d0b69400045051418503d95000603512070b002a603010a8035600341c499420410742c032000501c0300744004c4041e4031507101a000a081211004406e580d03401c81c050076050251900a01401107411003e071401e400c5000c1e84242540410415a00c1d90382000741601024080351801c001810555402d0ba0807424860350520f45004102600100c2e03681e0892070302c0d80c810403440001c1b9900702150125640f4255001e030080c41d0010f00049440c1d041d20240740203e40c0190000c001142140340d5103401 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 983496987 1250 983495737 983495753
    0x50405090f0d090f0b0c010e0609010603021f05040b3a29120a0f0b0402150408120309010212041212090b01051c1b0302090a18080f0f03040c03 63
    0x415601420610a014209841c03032a8210060080800d02c04000a0346c0240f480c095008130080c0001e103080d100e5a00f40200c015020384454402640310703000d08100c80300c0949a1400c400000f0700940c44441c0360a01e443c0f40a166600111588000b59120411070711070b903829001d5400c10080c170003a0300010a500c000030b48040340c010340200c00300c14030075000c0100009050141150199000c444120014403003540702460b05401c610700611260300c0d01d00d843e0401540d0043c8a0007248204c808231000901c1c4950034810740136611035568164031040c8648121241e0030002e64022041d140098501080c542c81d200d21094280d0b011544011484001040107902200d4095a17294440091111980580751a680081c042c0a071078451030310103090f034100300c4064419500195022004821380201386440d50300149035403100786e00030749103000020710340c010900c00c143c01c0301ca0602d21341003101c00c1604d4a100c203130014040c15007022800c0202c0c0111031017000c040d600c1148200b419030060380c1140741c01d80c4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 983498237 1250 983496987 983497003
    0x20708240108161e091803021212040f0c0b0a1d060903061902250204110a020a030c060e070e0103020a080d020703031b0b1509010609060f030213050405090f 69
    0x1196400a0b03002a840880310f080410442c0e40940c0c4d04c44042c0d09090710000c0113060303540042005890410740c0140003080c1c80040d002075001e40c003902e0074110300d075494040e00d208001c000640420300701d00090004066401640c005801000c0d4060300584824070b1416582c42507820b80045140c2c00703170340311700c6c0f08000c1c440081c000d00a03240c080c01c0810700380110b0307a14040039002856006614406450b43c0c68240e06440e056a800c841c030084a07442800d5003102483c003071505034021414a000c544074007a0f89401ca4888800700d6000b0a0f24906e543c07004ca5070b04140dc541100c840782c90b0745880d10000410403100001e440c10440084407945944100403c082113a03200040d280c101140c14040d0036004101102280c0c0c06041140b00d15003a07018a62540500f014028a07004113001440040e8013883c01810708010180d40021b116600c40c4400e403081c461a108080000307207400030620089202c2d0300504040d200440c84600e2554036a0300140a07102d00300c40300d2405600c850107500b4440802c00c40c01c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 983499487 1250 983498237 983498249
    0x60a080d0207060806030f0d21020301050904030f0c0209161e0e0904050705090703050411220f0612050c100e0a060c260310050a050d0b04030207082401 67
    0xc24489840006500e0b0042d80c0b256005206030400001c410741c5041c003840402483c01c03000d4881e002040e040c043d02c6900c04c14108001528100c0484050000d00d208880c1031340c50041014481c0d94650b542140d00344041d0300d002c03082101c003001a4005031110343c241c50140c1c4002c401c0b207102c08001c403002440c04604e501d04294194030f5400201045410202085d04000140c0303d000030360781c13141840c6142c4562540440d030401c607035004109800c2c1d031691000340034500c500403400305118810b0030800d1604000000a11040c44012403814080c1a5400100070802004002c202c0c90780c0c2d06030507480b04920380380540703007a000781c5080f248a00c1c01d00c5078000500b540303003800300c43c68241380041580420780b80148018401c01c100c0100c14404900010070350100781000301d04503000882e0003505035030020b41d101100c40075013074030105552401000207016900058043c0a0340790f21520740403440c100240050302035018148012604030070a2080341c1c1311300c013800321402503004a00040301d09a24168000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 983500737 1250 983499487 983499493
    0x1719141605030606070f0c0f03030518060a1205061504080a0204141b0304031e020a02010207170c04090809030d030e0c040606020c13150f090e070b120a02070b040b060a08 75
    0x404035941c0d510517208240d4121316502021203443c1b0342541c198050340c02c005150155200300004140d0701100510700e55800751200c42443c20b1000501c035840c040c0d001601c0208140c5640d6807514010355000c0381e88100010600c1600500314290580340350300c1608a0006504030034018401e5003481c1c0180401c0403001080350342c807881c1258841d40c2d001e0310756003820f01404000001c6030a240c4507030410701c603c076440405000340d010b00c40381c0030f55141e01c1181d00f02e0150040500c0098100400010180180340c0304001d00786000090003000000d0a62a008036810102444200b0711910204801c0c40114002e80b000182c0c1d001c030210b0549001ca46000745485981007072000e010007540441d0070100d964054a60090400e421122400900000c40a000e40540716400001d5240381484428045402e1540c0c20002008602c210340d403910300350700074406842020414482044100c680e0790303501080c071080050412410b81d03075175241c0c3c00040d541628060042c0041c001ca500c0e05e041c07418000e061000007 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 983501987 1250 983500737 983500741
    0x10510030b0a0207030e090108010b0909160501120e070806100b0f07150e120409200a0c110423450f06040506010b0901171914160503 59
    0x940729600340c010401c050180d004680b0008240c050100c500705180c0040c540c08043d83c484803068020701e01d4260745403051555001241358660045103480440140705040c0400505200041d00c0014819042d4048107075100d0311140400390070320a8001604000c0b0207440c0303034204580d4014080500d6040071640d401c0403c4244c0b50491a401101e01450f0b01c240c09140d50400e07408214020800d090803008640900e60702c03211007101c40c00041081d16131548040103004031551003181108001c0c11303529040041005000c0201d400360742002c054038410328604d4404d13404c5001050540305007019101800111034035184600040c0b107083c6078040c40d810484443c0007241d0140c0f01001c101e000349289004c011044200d0204908100707800900c0e0b0000885810414588600f40c1d41c0c00c084405468078041c250022800a945030100c9140b18416510800d20024a40728044424400f501224032410641101c0d180004d2500071910341c80c0244200850914203000365048600d801102c7c0020040100b013 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 983503237 1250 983501987 983501993
    0x1050f1807051507120801082407080910020406030605040c030e0d0e2e1b0f0803071106130203011a1302161703010609050f01023a05090301051003 65
    0x540404442d41114084140740701c0391a210702038400d002d006080a00302c80008101e6030341000e20f1504855001c1d0880314603422100c1c0301025a4a81201c40075424030b81c00100e4096440745019640100210060742c0c541c0a0924540f4100d030f0007a070120000c03031b4a48500700301610b4a403141345d45403d00f1382000d0250340b00c0c0c420b041e5203c6c209030303d6550038003102010100c20b603115803a002031400c0741c040303101c4640711018004020030140d0315904000230f03245066080c45040b040001c0d551659100e0640102480e40381d403400da030b0340c00050601003000102034040380490010000341b4041c60f841d20204154030f0007401414295611070410844544405282503050b80b1450858055905a200c0044e2a102182ca010103d0300d550031000d024140003100c00c149900c0314400550490b50383c1d890340244a50740c0d2051016440f0781045c03243c056040302c503401e1354021210b031040210038a0b141c510b45105000140d000c080c1b0402d141c451001480105020f6501d003401d2007815000a01141e101c1900c500d590303 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 983504487 1250 983503237 983503243
    0x9040b04110604242f010e0d031a040c05070b0705120403050307020d020f070306090f060c09090b040506010f030203040221150c03010803040515122d090c1504030f030201050f18 78
    0x1c2c000b17441307200321862620141c4800c0d4003084d008291881955031181d10740b040180a00b203080c1010b000429801c42c0200c551405202d030080c10405034031402d0900c00c075505c1d4078484800041c5001c0038880104084200000c2e601c12451195100c0c0e00d030300307031a42004003009240c10361104d903c10555128000903c07598900160382401c0b40d51100303010602c01042d244c0390440c400024801000c0c282042c800c1405150000d05100c10349666480c208011110b1008000a0703450030794005003c078070b129480d00c1071517100b81c00441d44140090121032901042004c0784084803001c124035000703074100c1001070030407202101500b90044414201d841c2036504100c1c0c3e80e0f0320b03480fa91044078480c4003105e1f40f040c084d001f01c400382d5281c0f0070070007031090040c0b40080d55036050302000210980d0130100c40c0c501207002180c003041540101511001002140070004c2442201d484103000c40c50603410a1000000081000100801d414465800440e039404c00300c50a0f8803100300500b5000190140d1545002c03018000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 983505737 1250 983504487 983504537
    0xc04060305070b0d11030708071b0213020f1605101823250609061701051003181104060605070b04030f0e030a050a05071409040b0411060424 62
    0x4003261540e500c030b4600400005e1035002c4074219549030120800482c55080002d00740305107415251035114042990b13420701e5280105200a6000307102ca0003050040130b065025010a140d404c968500d03000462540400708405d10404844c0c641c00200d00f0301c81d4501c28003070f4810900800c00c05524401c55503030740c05020f0550344038110030010f0503180c0c07420180c02008103180b10321a800c10071400500d0030302c0b0703240748009901491000c1100c8120000d0000e00c40d00340c80c90883c01c80103840459900305400c205000341181c00090425032204140f01e8544400d1a4040d0000e106143c810000c0d00c0c40b10500040d03c400da404401400014001a400300713084452859202d541854400712800c420742c42a90300844400e586609445003880440c1005070000e5140da04038080d204440f041e80da603003010403482c0540564503801010b0040800c000404608800750010304c2561031405040203040400c0c0d00b9080b079030101c55141e00c045101e40b4a80035071a800c0320100321516003040f2074404040c0c40038600cdd0f02 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 983506987 1250 983505737 983505749
    0x818161a0702060d0207020a050a060504030302070f0b0912010e03130f15140706090c180b0603091b040216050312151804030c0606090209030f3403020409030305090c0406030507 78
    0x40c6d101c0441d900c004c07009000c1c2200401d18020544c03144d00c000e041ea081030108134058810124081201080140c4e071000b240c80d084030651401006000b80b2401441d02d080c055000e648a4081c203500c10310074005405000e05c4a500d90140a24001d030243c45503e41e603101070b100e5080586070001c2c070380e031004181c4407010204036641d540c2e1501d0b1501c08020a449a400780c0020760302c10b004104101000010380544400f54803d022281103002002010701c000d503054415607010001d0300002043c0480c0c40c0c1011b1300004e04c01030400540801940110f045603400311541d400c0094504810204014a1a0408480410000200e0b520380104030111034208007007136200300080004040510a40c01007001c694084010700c480d0342d6400040029400c0104198882d000d0301031b100c0440c0e0400075450038800911102001d18081c070b80d0b800403450403400401c443c0c00c03000300790110244c0c96a004030034078903109540020761845e01030f00d0705060405004280313124074240311080000c500700041e07560a580b2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 983508237 1250 983506987 983506991
    0x20109290f0903070c170f0c0306070c05011104061e090b0d090213110306010e010c1221110d05150d03031e060905090d110d0818161a0702060d 63
    0x80c0c2c0c80700503245010300400144081501800824018140c0f4407000c9001c152108031001818002030480d1501d0044041581560050303000460051040d200450303014000d0000207034003104084846850781c003540205020840304800851345000c480050444590b103883c02078191401c000c41c4003003521076101313024003094880000c103096594040445000580d8240b040100c100c3c0d020500c01c41e504200c9196012500881015000d0350240b038842c0134441d402046042c0e060103488090329140e01c00707240d00b400303898031032040c441a503a43c2c03140c1199030484000c4903846803c00c0500505a072002003500d1039240d009054000681c0300c00f810060380507414200401d140c8800b61044000200d94100d01040341d051090008400c40c080c1d03c402e0180100d0415104038000c660380644841480320001d884170340c000507007007140f03521407400160426842d5041d448508c0e80240c007103142148900c5226501c180e150340c100b0003a501e5200c4503003012270003464242040d4658002808500030f5001c220159a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 983509487 1250 983508237 983508241
    0x504090201050c0a060f0c0c02010212390c040903020d0f031e0203040b010504140a0b19090e100c020705010309080405060a0c030e060403210c050d020109290f 70
    0x1e80214240c6200071190702c01c9400c252841d00705000500204100076650910f88907250b4030300c0780702c1c284448846e50180c00800e8031146203140d41c4e0b030a0744124500c0d038089041155100482c240e101c090149183e0141c102c02ca4100f41020242c00d10544501e039a110300d1404105400194000c158400d4014850400028a819612041d005401c2c0882d07a541083e0340c3d40d406400544080d4040c5016500508440219a072280c09001c00c44400c3c041e0b90803200500030001c1c420b02610303000707400421406004601154000f209010707643c030040e0011292540c80b2a07a02000c1d4108200215207069900300274001036210003006900e90075280036003030405448000030001c0c80b000c2e10440d07000300303005400d160307485411030703002005010600707011800601c401714011914981601503c098075000000110021480030000080c0e501101100c41804a1042c0c4030021070000d02c959881d2101a80011541001e1440c0c1620501003c11040c094944407243c200c0c2c0000d0000f0103980d1180c040e00b00c1103201d13 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 983510737 1250 983509487 983509489
    0x50309070608010f0302302a06031308040b0a050a11070b19110715080f060a0e06030f060f2a0d0b01021614040e0c01020c010f0e0301091101020706170105040902 71
    0x648642c101c0039800c2614105080b12641c0000e004230440f804102042c048000080b0000c28103000c030710060303404074040c00403072601000140a4064648142040d0340f820f95500302501083e04201c1c0345001080000c9040c1d4841a088907017445c12034101c03005050420701b0f01500c85503a00640c4000000ca105020100442c035010f180c1200c074551136242100c0005540381c4451001032407184d80e01c000203400b1000b28005600204407503014200040204030130604140c040e180900b8001e02440d854403940541c0402d481e0144520390003580c5d442c3c45491031303142c005100c044078290b400c090402c2200388091070b6121100242511a0002c020201117054500034004070316000c030785040045c0c1101000c0002403e070b08800e50b4071a1300b450a03141030015441b070703041182c2c5885242c0000f0b805a04000080e2481d03611030428400ca5401500306000404c003100040703801c4800c43c0e0b03011281600c5410080e04603680400c040070092030685889803043c0140801e00d040044c042c407901c0d024648500d191021 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 983511987 1250 983510737 983510779
    0x5060705031f090e0f070b070f0602040b031503190503031305070317030108100204050609090a0608011d010e0c180a0f0f05100b090f0d080415050309070608010f0302 73
    0x1c51580b1405049440c2ca510b1050020a69a5407070099031040704103440c40c00340085094001c6030b0000d00700500703009941d05c80103540e020110040380c1081d42080003198804052000e54010101c409400080080e15800d05242448e1101d10000b04001c0c400305800055000046030f038801540c00a07200c800103185090703898280d268000a10018241405180b001803141c0518100d030340300c0048400e0399600d109044128882d5015098015008029140c802d040528199822840b050000106140da41004a003107a1000a0010b42e102c141d00e08058441424003c40588075112009003a643d00c0e000c1c0011800c5808104600001c4c003944009012030301140c0c00042e02c1001d600040c0802515442d2410003801e044410408000a02e100071522501c2d413415a5403517600517000101d041d492004200400149800031901c0580800010800e25151840000e20008a0304c030552203040c0001701301e007044c07842d810503070030050020010400c0084482030001140e406440185a207072a40b64035141c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 983513237 1250 983511987 983512021
    0x1051b0d060512030304030f0e130b0109170d271208120709030218040519020a0504061415072301091704091d07061b120e0a0b070506070503 62
    0xb030b200600f460000d030f504201100a40c800c900c80d5580f0004402554401e0314100011000141c000b40303681e1000070f82100380d0f0b0200351034500c1410403080d815030743c0c0c1d443e8801505508541e9020780101e4031181714540c016004030058044c16213030500280c01c4807aa039000002ca48189041001010b0405040c051040c040314446001c1c2c0a1000151604d05400f60456000d803104034007402599003041a9003800300c41c0e1720300942d8890045c0c0a04a1950702000a60300c80d548103030f9000400050005041d0340e14800c040c000c0010340c1e21380c1d284400400402180c560a1103030003010301010055100000c0d40e1002450b00040c10003c030315078060030502d005004190544000f085403a10038003000403820724002030812281c000341d0a0144515038820440c44201088001c01603071b2250100303105030b0307025a042052010b00b21038020541c243c65102c40e01300004104905010407130300382c1c910410307082455071000a4010550001e18194151350341a0780c40c500180050100100440440d00c01110003072030308 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 983514487 1250 983513237 983513239
    0x90902040b0a270f030b06030a152d0b0907050a0e0904060b061602090c0a1d0d0b010b040f05044208010b10031b050315061b0d0201051b0d0605 63
    0x50b003801c2d2904a40c1c140c04e166400261000d402c0f41c000101c0034580003c07540002648403242c2269600301140c0c26010301610301c0b9075003048610803c198011003c0030400214040c42c0c0101080501c2020b051217140200a41301c8410414200f00300043c0f150003842e0408001d1040d580b04a107503856080640050810180f025030203040000c50303501c0c3d1840c000c05040294022100702c0e9007a1034001c0c402c1550300c1041400e00c04a216240c1540441808440515210801411880c400b0100356140800071100740c00041425002082c244407103014604c40300c0c05400c040e1010400703181164090198090084103100340c2e0107400c0001880050600b51595051060700329000042c0e40704c032030050181200b44182409082260401d203000c40c400c1c0a0030140c0e080c40c1c515400340368120305003120319900003004540c0d880c25010700c0500507110b8a00600602105d6011040e068100040c103e091401d10064082160704000034000d1015441c034030020300000c52078605513940244107069015003229441a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 983515737 1250 983514487 983514557
    0xa06020c0607020129060309010b09040c0f08061b1b03300f0f04050a02030604080301091a1e0f19151e050309010902120d090902040b0a 60
    0x181206440c00140307603020b018035400030f0000380c1c1d14041210440c80c100381400c41600503050030760540e0070403d000f59007004501d0700104075108200086080da090a440803110b064039014100a000201f8450001804035030b00a0714850030700d469518640d01d40d0083c51903116000180e00300f00e52458007415911522002d003542c2e1544410b03102428030b40c40b940466405200170403404003079540c01d41c80d8180f00c1d5241c0038000c8042c0e2181445c01c8260350008204075098807891000e940903030b508214403803280348031b89140c6650358100045042611324445442115480c00002c00340d2035614009100e031014881e499800354100040300051185015903000d41c2c01c40d50503554480d905034668201001d58060b0401061890607994003100c00f04403500503582e03580d20202485049601c01c200940e00842040000f00d0a038445800140e00b0901e01d03694403800f41d00103015030f0015600180f0300c10061145210031424145400b1030030346c0c0c1e0312031010840304010985010714180354880e0b0708648024407080d04 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 983516987 1250 983515737 983515747
    0x61103070510020a090b0f0a0f1101020c0303180109031d060f13030624091e020a0c0b1503030306090403050408190201030b0f0d06090c050301021201090506010806061206030a0602 79
    0x30400250701000e0318000040c16042c02013241600701044501e4047c003e01e607280f510804000898185a034840302e4001c011070a59150300c1a502400580b0012007154007070f6940f03040c12091848280303e02c41603218070f40d04040070b24021035007141d421102c03070b008140b0075803007410220000394040c030442d40320702941840800c0009510720203c4440f07003500d00c1840c0800543c4250b0600c84880c250710b03680c1820500240c03105019401c01c907009043c4444ac1c164450301f900405201501c00d9030841111a400642410344180c2400080005182c0000104044802d03a0aa02010a40328071000b0110381c024040d0f00045010144180201c030014504074007690505459850a111044110b100c1640000c0c1008203c41051030034600c004c40e803190081404282c450b13180e503008041c00c5101d0b0156403d00068030009181d440c2070009040300d00240c0d081c0051907041c50501e1b82211405000c1d00e040001c01c0041010313580b948002c650408100034170a0070203964038000a40b070843d01d200300034002400424 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 983518237 1250 983516987 983517013
    0x18130221011e051b0a0c0c0303030903090e010b04060c0203030c0601030c06020609120406210c050408011a0105070b1b041d15010f0509040f020315280611030705 71
    0x7102c01040400c9615104184140d404100c05445090740c03001c0481001c0c013441c201070031141c4010039000ea0641030505070749034541c89010410090f0f138002c0e404a520750301c080007010751015403240600107000d0056525410a0700010460107580144001c2c41043c100940565404005403245414407108617190b40da141d240604082000d4440c17000544600408201031903804281500c00100b4100c401d8101032920f0404c44002070101e41e420240c4002507440403140110b40209000e6011646883d5600c9103044d05090840304905a503240510596441241c141e030b02204448403d0342151210109450385a2800100141c0c034500f052a04000a00000c00640740400c1a40440e03c85d24021011340d5038403400c00210036000f803441c1c0000e0f018039000c0d41050250340540301100e4042c100048640c07000040108991040e41c2d4580400c01101b04107245282c0503490f440031800c9081200e00c1100d64040100c0f0030030b030328000c107002c1c818000500d404400d0100284d41c041c80e00b183c1140d42e100c181c01 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 983519487 1250 983518237 983518241
    0x50a090b0a0201061503051e2d1806010302090402040b0a0b0309012307080a0507031503060608012004090c0c1b050411090d11010201180503090f1813022101 69
    0x100c9580da803203108617105c064140c0244038252060601c1541c2c01d21100c022141400301c0d07074005105228804080b0922121020450003c1c500b1000310a0700000c0c0d4100f003903100401d96600f00c2c2e00f0256501c800014070041e156010103940096045d10017140c0c00018000041da840a10740000016800c04010082d00200c15000380e0700040388411104443e204080c00c0b600b07142e20803688800890459000b0800a24051f1301050f8040740d030303140c00038075000c1070361689450125503482500c141e61141e40610480a083c0f099070403c04040a000c80a0030b108403456160340507621440e19000d60b5541e6501540e406036009249159025003080e038401504000d81c002c2036401c0c01113900891501c40b4104240e1100c0c0c086400c0300c0c0f130050810440caa466500d2109130041c0340e450a0440d52510400c4522174580d02140342070f54803540240d07071a4007400303044c0301e1680c02c000035561203110201c140482540e01c0b245da003508181c50b0424489241c0b8180045a511050048880640c0d0a80040b00400b07000c19 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 983520737 1250 983519487 983519489
    0xc0a0305040e010f080303040209150d0305130b16030e04201201171f06050d0305070314030412030c02070515040512060c0306010c170f0405100306060807050a090b0a020106 76
    0x322200342c0072640c90f0350400c070644586008100d107603801040490b0140c6400310300c2583c080240701110302c40500b000045421036120300000c4010030300c0450400060140e1000d45c8000e0801c00d04040e0401c80c5d07010b000c10a4407009500542888540507290780c80b507c0d40d40080c5071140746801c152100c500d06513606142d40e4460110340350b50205060011413107046909100f418202c00e01c0c01400c3c00c0f81c0c03130300c4079010f070032a03100301070007520741e01c0c1c00002d642c0e1210468000d0540c0240c0b191610f40301c0c0c81c20080e00c0207480000b59903601200300b0400000a504c828422102007540c540000c0546031203070b0030b034500030980c1c02c800c1c1d0008400507114500c200780c0c001401516810b80703640071403400c10324450f9503070030040c0c0e01488140b800f07000041c1d180d4070440e6902d030600e00803001c0c00168503d24801840552000001b6401c06e0030001d024405801c2020400d00c2c4140d0301d25080048500d441d100409019001c0d04a03010080000b61250340d040c46510b0540c040e06032081c1c500d030b8440c40750788040e00928075 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 983521987 1250 983520737 983520749
    0x50c030c16050f0a05101b0b0c03060102061f0b0a180f140103090803150a17030405011e0807031e0e07030308070c051c030f0c03090c08210a050c0a030504 68
    0x16190450303916003080d0f0b03002c034219003028100920003500c0100948030380040b0700f21422100d587d0600710000c101907440b080c1c0104552065113907242881c000082c1800d00051880c0541980701c0f034141c405040c607034007900480320007642040d1590030b84c0c541119516001c59410100045945000c2500b0000c10214012104114080030300c4d1568100150309940713404c480504040b5040c00000c40d985000b02144050074030003096040181d44550300d40028002004202c80c46510105080c00256003150030403080d84c40c41e850f1b9070684104168010714078400204a18205500c0340e02405076070079020b9803180c03100c26826017800410039110b0a0790f9607401500c0700707030002900100400d20503402000e6601800703030010060246c0315000600380c100500c80c50b0406003003603650511410f5002c402d00c171381c09600e0aa50f43c0403a4659040c1801c01b200801900076482d20b070404028041010068040b032448850085a6280c0b41c00440c2000d0b62640950310035440c0314003581d4001010141c3c00740051050b00c030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 983523237 1250 983521987 983521999
    0xb0720060a1a0303030a151503090b070507020603041202070515190509060f07230a02210a0b0606040312121808370e01020609010b01090501050c030c1605 68
    0xa40a818407030b100c450362100340c15800400c08101c2c0b1017095084030800c051401c0c6107001165503990102c14002c8062503420010759502000380c20440350742000381c0c00c4081c519001e030074400c45400280d158400548010400350302540c481c40018000c0c88400c00034500108500c12016601c0c0788050b095000c487c540ea0343c980c108032801080e500400c1038070000302c0060912400c08424030228406580803000944860403c41030100208052304050001d60201e04050300e8204054810711180e00b4802d01411105d100614002c6d0307103e000020041000c60300695032440544030314000c640719100b43e800c0548082d9940d07451400035a0080811000c1d455040410482e4a003c04000d07581159550001025001c2c200302c0081000c03049101d1b1850301c201c604850b0401402c00d241403124109203500c54002ca10603002005481d03070103012065001c041e2000a0090399060b80000384401c4150041d903051050200740400300da00100155020b00300076074111820a281031004000d00794140c825144100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 983524487 1250 983523237 983523251
    0x806040e012d0501140d06020c01060b091c02011b060227010206100302031c030e0d030b040b090906040618060203070c0c0611060601141312020f0604060c0b0720060a 73
    0x304510a1504803014030341742e004002e00003010495441d00c44603040e501c0355000e00034200840d100b0721a0a0003007c1a10180d6911a030f1074060042c001d1840c440300c0d00c00a504020640540d13000b90748501118180c1e003a442405606240400080c014542c8100c0410210004503074100e402c0d41144010901c00d808039401c13503860001c030101c1081c1c80d006c000e4260b0040b00260101c28850181c864800c055410b0116222000b440c01520b40302c034014400c40000e8441c0000e1a40341028852910900004c0e45c407070615180510401d46e0b542005040207021690703c40e042240f04008a007050509039100754155507030b06000100a040015800d02a1009030070120002781c558019040c2410003503c12014100a6690780c00644a0800c80c2040e03c0a988040142d00c10410484d245080a0a00c608028075983d840b4018080340c050031490603070187d032041009015158000381d0100f1903a03404014102d0b42d07604c400c0c0c2201c0c1405103909145084401440c0d0140e1148082842c0d0300c00c04417110104815 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 983525737 1250 983524487 983524571
    0x303040b010e010b040b090105070303110a08040b060d0f020609010e13020903010f05042001120f020409150f0b03041a0403210501061b0609140307120e09070806040e01 74
    0x184100c0c4946038406c3e504000b100382c41d5019030082c0c15018001d00340010b680c07240014051903076000807503903c002081384041208100c2c0c14144260024000c2d104101442d042e0303680c4072040c0840c0d05010384900404a4070202c1c13a8421902a403a000d03015001602801c42d0694250181d00000e03c540d1003542070031110028500d5520405103d02e4002c40d03942c04415000b064001d10100310030866040256000110a0942da80e00804001d010364a000603603d514104c01c84089511150840081352900f0800300040043d120315842a03c0103443c1141c3e80c3d4540786171800141c41100066040510003004210a154000101510b11604510601560280040c110040f10024000c00703011030b501c1401014001c200c140420162803007140300040010441d1120100182c07200300321a11340d800060804104001204202200301403130400b00f007402040030008000e484000d1005082006010004500759516080809080c2c4a40020400039103090a010941c001041d01c140c0e514001c0d803081446 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 983526987 1250 983525737 983525759
    0x9041a0325210807020a0504110406090b0a02030f0c1f140a060e01141512162606010e040905030405040b0a150e0a151e02031c021b0303040b010e01 65
    0x40041584403805404554458016030050a0140d030084015100441c4035100e13840f40038000305c0d0a80303007103070ac59240c110018503524141c0c0003080d84a8003484041442c079000070580343d01031021101543c540001a485030311700010094190207602160300102241d02786a48440404041d1805128413030b44d62300d00f8035050740e100388180d034036901403c00100b2500e00d800d1001440408018000c0980000c0018815455000380041502c041484001c2c02034201e83c3e4108041d14110740d0800c0d202c3c0a0503600c120368482003001403000c1e46144d010000301140e03c40c549900320800d0003442045849180e081c0141d4030782041c006d41d80601d14002d038150071440d008581ca4121209090303c0c1c46202c4070180e0488104415407092038011000f04c40125940340e16603040c03490314056664010381d1025040001081e00f2440c1d102500755042001041039846003103000c0c0034041c035001e90151b0354000a07101b04105461002c1c401d1480c1c0004000d000820040c907440c5812105a6800300c80141d072071700304040c2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 983528237 1250 983526987 983527019
    0x30411030d1e180305030405031905151503030c0c090a1a1c24290906130f0b10090501050427060303030f0f0b030309041a0325 56
    0x1001c9807042c9108040c1c000110805002c0c0c1081c0d01d020300a54421041c4921441515041100c20350001718003804039050030032101d068240c5803002c01c44102d00710b4846039260b4103c00c00c400710000a100c0001c0b10314140c405252401d1780d020703003101e907a61143d11116403900d0401440c24851189140403e07681e9640740182481004001c050003090040102041110341103244e54828000c20100d1300008100e00392096072a80d10f50350040d0072400c0d414043c00d401c0700e51a2640340c682c50407a0404114030240740c4c060409020303083d1003044c640c5d201c490001d450141e0020302040c0503401c6c05011070b005406c982100181081c241c035101004001c1e8a002c8e600903542d40102e0780000c9041c042040299460f822100e0f604c454050309440b04440c4004603420b44070705400540129486040d0300040054a10640c0307075114100b0701c10003207900b0030000070b901c9229a04086204507116031100008000305d02c1401d41022000742105c1e050300c1a281100781ca00c90004003202d040801c480c00086080340e0180e9a6 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 983529487 1250 983528237 983528263
    0xf27091b37050c030f031005060a210911041a061306090f1a0703110d0507020f0d030f0f030b0a06080105030f030c060406180213020915120a0b1503070503041103 71
    0x9804d0800c1741c00d4800c031580008040702c1203a415004005001d86408005241c0d104156540f0107580000c0c083c2142031022041c1e907802c415107049030320004100726449101d42d00b4400c071004964200c80d00c40469030520f4099040394441d400044c469100303540051802c08840090300d0702c0800d2130b901c0b200010781480c0c511a5030505a00200c80f0700c00c00c013000c3c008003200c1b0300c61b040044022490024640c0b03056203407010100841c1c030000f180300542c5001031480c161500110740410888003903503001041e038a10141d100c4140b02c24070005420482c02500034206521001d84140080c55481e4001001920b00f03110783da001c1c0c0550484d80781801000f0080b222101c80d02002130031151181c0d5140002041001640030f451440450181c0c0180d076820b455060301c0c8082200942c588801b0820420101403c41560f0443c0c07204028095264440010700c5601031070581001664080e5840800d416510310383c2c900c08030840c00800c01c030b0783e030f034011020b9401140a03085004090800009155882407407940334 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 983530737 1250 983529487 983529493
    0x20304020f300c06030f04051c0e0a0b0901230d0e1b0a080c060702010903140601060e03030403020a0e0a09050d0f031a03030d0c140f27091b37050c 65
    0x340a00b6001c0e9a1b203800c10320a030b04640901c40c4940782039002c540b10f405410000381003080c1c41c108a00e800c41004001e04401d05445141c5000c0b0800608402c0400360074035140c0c403031801e4510407010701c0d006440040c00c500106200032802c3c100c50748e403a0440c240481220407486520840380d030602e407101c1015038411500822029a030001005400d030440a400c030b040002d090008000101010090909120710704000d00195051180160100100c45d40481c007941c0b00340b20400c096510842c0300012500c40340503c2c02d032500e5040f102c40c09040396400151141c130900032100b04590344404040e0140c030795980d0420a80c015400d020200c5001400426415807050150381104031041e40b01800c3d428080c1480950301d4a09407a254258005132126201c2e141c000c19005c1d07a09a00c2e04605503c559810000b160354009980022948140078000b19052a202a0902c140316640421541220035140c03001009005030420b40082102403550032090510307126100300864040e00640350b13480308031005 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 983531987 1250 983530737 983530741
    0x1081605130207020409061802121b06251a1b12060102010b0a0611160b0f1b0106030b0a15080d050c01060315051006050c10020304020f300c0603 64
    0x100070180d000504241d0348540c0d507880b0308001826034440d01d00c0c0c840e040c102850004440e401001002078140000c8161900700c04002e680910791807140840e1074404480150b154821801e6802070b0700700f00703072100c14581804110035042c03040d44203d040b01204207000c030900c0b5503614100c0000280b4040c05829071008180f010b10050300c5901800d95000b101807000007207444a1100190107011503500c034001085001d1b5514401000c1417160111140702201291104c07450905800007500c9070381208004120082000611500002001d10034520000020300505071a03040c049100d01058800349002803503c2d480d80844004880c40c00121040c0b04003820344c8500d40710080d100c9034003203089100765540e10750b00800001d68140500c80c0707200340e048000645162a01c4128030010844c0c101905018060028140e448000034a00280011001016859441e41c0c80441d0101000d0b00d00198458100800c80007a11540895884441540343c0510761030002c1c049041d4940c2c0f800d4500c036400c603c1c2080 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 983533237 1250 983531987 983532019
    0x31e01150906050912150a0f270c27062702031b04030b090723130e0a120306050a0605070b06061903230108030706051f090501081605 59
    0x142259100203041c001803011400c0555081600d2010703441c2c141c1d10100c1c14040c1e000f0311231080740401c001883e0200021644440051020340200740030310f48110400440000b0072030b2031800400107003010798a00703241c1c43c0302c066000b03051810b84008010448c40c1040c0001c000ea403089440d1a100017501103c0c5d210208004080041e40c40204110451140c2c4c00c10102c00b2503006c1c00410046000d612240101c1c108090564200445c40e440749010034480541040c4031000b41000c40d04540c0308031024448140e0310803030704001d000100e00d102d07214003a040c440400d0080c0110700c0c5120b4025a60100484d548510400502002d00d000c0c52001900c148195400204d2000e001508030900403c1203040114248501c404140340e0100040083d855086111010114665040c61180c2840b030300d0035990706001027540d0700c0c003c1200180200e0b44641c0843c0d1520a048a10300d40b0060345072003007a00702d480b240000003400080c1709410052240c681c0311681981140c0622041c1c507401003d5100c1450061 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 983534487 1250 983533237 983533247
    0xf04020f0105180415080d020606040e010507080c07110a151404080d03020918040c03140a17070c0e0703020a110706020a1502121306050a0908030a0c09050402031e01150906 76
    0x5017030b00503102d148080b5003d80c00300848080075800b580200b81c4ca01e805420b01065a003602c101c4252a030414040c8419650401e24040d8441c54031180706880d000c0608002101803841c0101030b42101d44070b42c01284040e55002d490700c04540c181c448003030307210200c4003110603407203a4425a07416412050942e810729202c3c1d001481e60b00030041424029825002c0d50319598003081d18215200d208006081041180c85d032049405500040082d101030b00b0b0a1700d03041c041c880a03034104000794000082030010450305a4400d4060002c045c0340000b60320744000e015000394004031250000c80c468810103505410000361050949050740d001c0c00141849a0710440d005d80300445510915400b84100e220340000490510b108003103005000c1260002410711804a80e40a00008461401e10f00d614000c1426041101c1d04104000d1001610748100002110780c2c600030b8104031780c031600000a03c100619003c48852407030689581c100c0301a41c2c7ca1a00c401005c017100001d4011540c04101006114024 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 983535737 1250 983534487 983534501
    0x40f02040330111e0c012a02012a0501050612010902030703060203100909050c090708060f090714390d050904060308071202010609180f03170f04020f01051804 70
    0x550031036000441600a01d80301094135180c446056124048292640d80c1c03052140400c5400c0b00100183e05903840c0807040115003591010781407081104d103881c1940c1001d201d103080a44205243c00194410b450540d01800d01610107501c24000d03441d1045014006108446c60103500400130090340f4070f1030b9a0600650401400040d203c84802e20008170103100d802550b4080d480341014080801c0c00c102044804c00018140c0c40412096804002c070b152240400e072058140215403011141d510340e88119452070203c020b101c502040032512100c2a00c0201d0015551a440b07122840e41012650840481d01404214040c0540c041c20741040020301900041845040140c404280d0686a496070700c2c095000031002c40c0c5a0340a1104074104aa080c8607440c081d01d1414014840400c4040c000480c80f001d0300c00242c00c28101d00300030020940103170b6640801e082461048045840c0074485c5405051382203405034058143d9999003113280d0311941c11603041641c2052007428484291040c440103000c4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 983536987 1250 983535737 983535767
    0x10140402210a090507060c060c052b0b03070609050a09090f060e072106060f0b04050f061b030a03110304030f030507021203150a0b090901030f06020702040f02040330 73
    0x3450100c1d0b0f003c218103208210180c8090340321906490300d1850b119040f203c1d00841c081c10002c0900031600081c500d800483c2886019500f03070b082d028803400c1c41d280140340d80c94a02d50f06100b01c030b01c000380ca60341240c050422980c084078012244c50f83c885125080e6400000028880200d440502002441540c08002c4100081c801c40d08210313140c954041242c4000c51038207188c0c250900450003041850f0040d0300c041c0070b00450540e000c03803030101030800c0740c015030141c54402d10700104105669191901641d00171014549684d01920620201c55101d40c00041d40c0000603007804c0541441444540c1240c2c00b566150f03680511181140d24204c0090101400c845c0441c09201c000c645d419403001c0295000e0003480072009a401040d008100e2040303941d0b80085407114060100e100d09540d56400f42d81101c0d041204000903400901e0040024480c0301e1000394000c3c0751400766000c0112640c090001d4038403900c080301c01919202803860281d80c0680a2114144050344211005482040200301c8064 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 983538237 1250 983536987 983536991
    0x40f0207050604230a060209030c03160b0f090d1b0801060e010b18030a03080105010315030503031807080a050604020405011d2205010e0d0f170a09030c060510140402210a 75
    0x1100c1c00b102030614803102030560f06c3d90340100e9820380a00c0c050101c5800103404400030440781030095260700b8840214490040b092801050069545502404841c01e00c80001d000e03814920381880c00c0d241031509110441e1181414000104a0020500c9144191038040c4c015100582ca80aa03d14056004240c08401c0c19982015040161410448021258441d80385d040040d070405000504481c41741d850019002e615400400110b04e01004403600590480e0502c02040f40d2826180c0c031704003050f44040d0b45072241d0080d01d028041c0208485000b14801c40301800306036614910000f0700380f0301c03a040c6220031141d240480d0406086290346a4036010241074100710803039948030b06007158078115000d011508601690303890a64000d105043ca43d86a061140e40401c1840415000010044c000301105039610480c50505008002070002983d120718140b01c0b178508845400111821481502900003404540105a1900e40207a40062139451901101d04041e1540130301940c00181401d00c03416 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 983539487 1250 983538237 983538293
    0x302071a090f1215090f21090f030d02010f0b010e011b06062d051f1116030303020a0e030c13021c0507050c0c010504051507030909020a0e040f0207050604 68
    0xc00f090200c0002000da40420000c030b4900485440e04101c056007002c281508001d1101d0301d66080100058081c50414000c142c8910321034001c034181d0440c3d00c100503498403880120300c031801d605403c04e1885100c00802271000180311801501e00200080c0100d020a5260782402102c04030100360100c028042e010114810b03a41c3c624454840c202192440c0a102c4d0700c0c02c2070115201d42c03408120051005841040024450080c0d400624200700d01100822400b45d400d41d00c080010082c21342100703414540401600c0d0740b4900a002076203c01103282c04220300c15403c011518010444c019039a5000d0540c4ca450010200c1c000002d6004501c40c021035070805c410402002c0c1d1a200e0107100e10010f4030344070344e00d49540c480c1c64506400d01e07100700d04001c0100310600864507031441000b0b03000f940080c41070305d0f000c0c0c0e444e0a540006c40c9411684c05244081916040c0b0350340f04c000f8485559003650100440704224024406034460100c0191241e44420007280c00a080040101410104091009030070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 983540737 1250 983539487 983539519
    0x1110c0402030a090c0b0301030b0117120d0911100f0f18030308011a03090d050a050c1c170405151f0b030703052d0604140907030302071a090f 63
    0x90300b080d158a400c90b070759080d8007410054044c4241e0b001c1d0041400441c19076140d9a00d030001100140961318454500c0c0c00303042c80040c420806078410b41040e503481303a04d924000c9a000300070048040d007500d0b1180325407140071981c00d06104400e21031006176120083c01020b00b10564450303040c00c2c1c0b800100110a4441c0c1e401240480b11903010310f100383c0d11010103502d800c7c02007449090b0907d521001c1c0400300140b040e0301c3c074002004e2800340b241c1e00b005074803201a414156860f004580380c04005005641c45119901d14240e0700e9907404001e62134640c5016015000d0781c0d86034504440051690303016201c07216038216078148040d0305c80c2240300400203168401038400021409a13010140c180c0021051043c000e42500031a54403605800c2203154240c000c0101125038841c600310301781d0741d1101c003000c1641900d0b2a081480c003c0c0c2100414062814000c120302d940c0d1205100a40c0140101000823441c0309549811038160240b4810060074040140e00f0171400d000720340d00603a4008003180c901c2002e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 983541987 1250 983540737 983540741
    0x1e0b010f12020a0e1306150809031204110d060b0a090c0e1e0d060c09050d02060d050408090307030c2301020d050f043201030608030a0530090706020604080901110c04 73
    0x404a10000100c0c1b07961800f54400d550b03c02158404080c030a24108010313070007400009662000001f000d01c51110f40711410007200707100c003a031011604941c00c00010b9003404082d420403c20002c0c142d4a0303040c0070350b454074580d00300d07000f0325071680000390401c9030084645060242007a0030b500c1c0c15032030802d0942d00300000381a00703c80c0e0000c44003d42c0718280d20020b00c0d080790b2028028401611004a0303000640c0c0040c1140c41105d00450415948030082020f21141405503940d011004d0200c910540e140d007440080d03900c180c85a903800f58207419007221105040541075002ea241a0001c00b1015103040080c0c64681241600c91450b05080c8400503c019041c818110790200101e030000b02017070786c803c09000a121840001e41414100031040210180c000116030a0b18603600d80079803660061896420344c2c80c100030a111129082550309040a00c507081c0035405201010304598409035521000c0c0d072a8001207502410078602406510907550003480d00400030405507090f14450040c00340041c00b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 983543237 1250 983541987 983542009
    0x2070c05060a2f1e0c03060f01060f11030c01022d040b0703171005310b040f0e0c1c030503010311010c050a0506101703030a0c02101e0b010f12020a0e 66
    0x20700322800084c3c45160750a00010600c55025409060301d403402e10480462820188603c9080046105a44154510601079800000b15a0042c1c0307a0310120000c07500d0203500329004424608040d1400402d42e584890050500714030f00c0320300642002e01d4000042410b0708044020707000d0003160303805924050641000749114a90401da031409403818041413241070207000050258040155032443e40202083c10801000c400c4e00702c000c2407095003030011601400420034043c030601e00708021608100bc022030440d112020981d1005511205980030100c0c0820500014020400802c018030106041140d445c1506d1418140100041456541c003850058010810b6905400020500500c12400003506002300b01c4103201428443c3d044100702d403680700141c040c0328415603543c08102104d00921104da40240d200034100001c20000c034010f46103215084028050514080700c03d0015805000603008540150791140c4035612150031940003980701e1030311802801125100450aa0b0755a24804 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 983544487 1250 983543237 983543263
    0x10302070c0b0d1b081e1b03040602181504030b130203030d06090c090e0c0c0106180f0f050705090d081303060f05070224041a070302070c05060a2f 65
    0x1d0b980d000f030190030904d050010708030007001200001c0c02041c03003000211072500c03401051142400d03200c892038440702039080c5010581d0030202104001c18400241d01420030010540701d1081c40410aa00300544084001d0030342c0d04607402403105102243c240700d000b5a0041030181e011042e5043ca40000345190010040000c410b501c0741014008000c07240540303407425825041c160120390500c8450f5400b22001050070b01950b80110762860410000d401010042403146c0b5a801c50407504140c041c081c2031118004c02c003080c1052003c1c150f003045442030070301ca1540c42d681c03241020702c0d0008020080e0701006064a00d448180002800700075034140180c001e522400e030004061601001040a4410062250065400c0642c00868041c0c20001142c0d00d2010041413078021341c1e03540f4081d00400040140c02280c082c801d81008603181d05907009180250180485c050303a0f40e980c10030031030588601e4803c0d400040c3c00715008261031050107201e091488218000460b44020364038440c1c0b620403081d41c82 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 983545737 1250 983544487 983544491
    0x90b04050106090b060a03330e1b03070c11061606110307020601030206031f140321042303150414030405060912150c19020102040311010302070c0b0d 66
    0x2000400909104550060680480034424800480d000401500130000c00c0303420b064403007403910a2035078290301a100e007a80da05c0c0c0d4945008581203515071103010500410310121001404030b034071440a01100001c54070740c1c0702410326558905204a621140307131036088890284081c100612565007074040d225030240a010070000080508007001a074400702c02c208000c0104200b4081682e40c00318030381c6d054a40540310341e907481e21080380b012a03415210520200748082c40720085400075035005c451182c0c0004908807000740b801b804001c1030006110003000c20404042204005d1456821000344080c224900c0240b41120f201000c0381c00d060781a02803440c00c0a0160400007040101b0020071441100e43c0c0041d41018201401315407903220b0420018400d411144c01d41e12084030800c814803c4104100c000c0460707050001c10092141c005202000e200030404441400d02d52051007610700b160b400820302d1141751078040054000b0340c06040c064401941429001c9800f108110081c803423803448501c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 983546987 1250 983545737 983545741
    0xd1103181207020d11120d270e0a0203040807050a03050301091a2128020301060e0f010504110c011a040b1c0803040503040f060e040c0c0b0402040506120a0303150501180e1504090b 79
    0xc08190b1112340d610740400903018a905001031001300728041e074084484040180d80340c07120309048819028854009101c0c0c030030405d40c8001c04d40c1c840055030413200d07110424030000d1000308286000c0811046000d0300551102d24100072000300140c80700c0e000440d10b003079038180708603800592000c074120070245505440228200c070840c20300b445108014019581602c43c2810480303034040b41407106108a0340f1568035848a49484985141101c0d00760b4030b103000270002d0a01d9170b444201d881090f5000e05205524040d030300801e40c00c020740040d1000790901481088103010380d0329815142c002078015a164402888040391910081060340040c0a09856100f00300141c24100802c1e02c0d281e0b10344030104552035104500161400c0c1c1180c3c1c016038102c5002c55569209030100d10b0760420402c00124510815010005041d0945c0c440750380541c450b40d1045103162a00015582149107640c25180f00074452030410000d10203460702c50700240d92103003482c420700c540741c001000d03103000080a40e0200c07001c0f41 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 983548237 1250 983546987 983547017
    0x1050a050105070804090c0512090a0312020c0a060504141e0f010612140a02040216020a0902040b0f0a141308060a150b0d1103181207020d11120d 64
    0x2000600030102464030501d05003c2e542c603100c860065200d2070f40100d88a20103121200d0003502035810042142c020080340d45004a0f40c00e688050344207098001c0b070001c8001f1000303010107000b140d82a40d1503100511400e002c0303070b0b00d08000f000b000b401030b9009400e1404544504070240314807408a02c00003039096122030801c11440c142121075104020903894043c01304040170300b900260314000d0b0411543d0040101c0b48250a040c5141d4500080d0700510010f402a6600400f22445021034000e0380d866690700d4803213110004034802c6014240c030b42c1c030702031206041c3e8183d044003e08407007910707140464400d2448805d0420710780180030b00c0321200001f202c007072121040030440e0b240e1010159105001203950000d081107611550300a6039080040051030900100094124003d003203014440d055480c5081800b03010211031b00400310f00e00e40288405130b200c0c1c200207400d868009400030b1011030200c425036544007014410000242e040b024540c2600d1580209000c0ca0f2003075407954540d0140104a46 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 983549487 1250 983548237 983548249
    0x105011d070c050d0c021314010f06031509240b12092d19060212090a0b01050f0a030b0703050114031524030a0f02010201050609060913080f120105 65
    0x30903210800005500c2040403400c005206480d20903281400c5080a00e90300100d04a00140c00c0d490442c54204030030307c20444234000626040f101c0c1414081d884589035401202542c11340003840211958405084c0b02c0c2c018140d018042404071602020102614028040c4049003545e0251004110100361100301410a04a0650201c0030002a110301e166003801d221500014490904103800450108001200b041216a0460702222031080d2600d20500c0d111001c2d500520010200c240720314045000d10000188403400e02c6d501400e05003643c1e01707180a10051b604803800742540990140400801b04190028180c0502d4940e0b03400701d01c0358144400300e03c0c1c00700070401c11b5000350710401d04501030b03039541404150006083c032144004c0d8012080c0134480050512400c84d418020010340301d0412811403641000d0b80d01c01e8000340984d969072410802e01ca10100c80103a0401b80f040000b03000d51340e0808920822a00c01c00f8680e003407042c50a81c5503d207801449402c40d040b0703041c40041c01035291503 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 983550737 1250 983549487 983549491
    0x20a0909020a0e011508071b08041e06091809060c440423030d0510060e0402070c0905010f03200303070f080409021201050405100303022d0105011d 65
    0x101c3d881d0b005551521349801c4e440310068581008003c03404011070302c051f10548410078a500e07841c6800e02e20500a040511159015109600e004603002082040309036208034918103c0d40c20740c43e0007407030303902d0922010200c0035500c941e007000581d80c240d420300265046c0328244003007080380d45d071080340c19005000c40c00d050481400c050303103c42900c401c09810040482044100c0901d1000e8046036140c61600d8100884200c00d40340b82c410048117810f115070303400005001c110306040c6091200c4e849440f640401604180100e50006a082084c1c0c0403031708040d00240581449031841b0086d482d6101c2045c02100c0084c1c210144880c1688001c0043c0441480003c0d450101d04a0140440b4141000a9074902c40e1000c0204410781629400c1d05010300c403130655005141031b0409541c0c030150b52000200c401000d0141c6481245070034040380407a4000003601065a0b80b6400402484090340c120822080717040d1010403006050941041d200c440c2030040d9802001504041c12400102d800101c03414a00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 983551987 1250 983550737 983550749
    0x307081504141801020c07120213090506160e090a0608070915031101111009121803030315050301020c0f0606060c06010308030a0b09090607091505030a020d0207020a0909020a 77
    0x24412400341d041450072106030403140c0f941100303032039900c0c50955a000e4080e00000100714000e0400000d1031802e004e080350302c014801c4600701d83c010140c080400880d0f8001ca0058100d510a80014032106640e40450140800d00d05004184110706400640060011151305140c4c2d900d4807020071070644204111409001100c50600404008001d43e010201c040d00c40a0720780850040c0644050f4010544031080d169508190348081c0b85840407040171f040581e02c1110f0170803180a46120103449225400c0130f0b040c00e010741e140941e145480072405054050410101c5a0051a0004566509200034050040310f18060840070802140f81418000300a00c928043c0208108800c084140420b040d41034a501014554a0b80c035000480d000420441e84d0040d042011541031215010000407410301c9070040d0b5640d0003800ba26030303071400c0d840c0e004007484401103a01440401d802c80d1103a0040d080b50f00c1c2c42800103090080321340010b0b040c0d080301d030301a41d60075039a041100150704100039440b020f443c0c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 983553237 1250 983551987 983551991
    0xb090d030516050d0b06070b040f29070c052e0501050604061b080f030103140d021b09091203010303051804090305070b06010c02090907060e0a05010219170307081504 73
    0x542d10b0042c00d544551100c00d030420741d035000c80300d005a4402c01038030b200c190015007105007840e092034880c4421040c0300003a00c0401d10300302c410401100480c84400140f582c107440e8501a20340110949220a0103002218680240e05007119103401030403028085c018984a51180e403c00800110115807040c0c004070300a9130208001c0c003846400540061074605041d50503c2d10b00d105040400060250b03140c1103201c050004000024400c548a0140064a0300c07001c2d1b8501d40300840d01640e03541c0c02c8000340060515070140041552403c1400654000c1040054490000c5040002021540241c0049011440c01301c0e44025001c5000603038540d1940568040003580943e480c0039080303004d004070040c4242229000900c20703074401d40c1d00e00549030b8054244c01341c6040403101c054445165004402c00180039054424451a00c0c1501f03d040b500185c02130440c0c000e24800c80c128501d2200000e4a0350100d00101d115410200310041d403143c0629920002c0c5428100c090101c44208114542d10641c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 983554487 1250 983553237 983553271
    0x16030305010e070f0507080c0618060f100b070c1806060212041d060301020d0c03050a0b0402211308190e030a05100c0e190608090f060a0b0d0b090d0305 67
    0x1d40004002d4540ca41a051041e15208140b0702071f4980d100e90318010840340114003d1002120f80283c0100c41925240241c0c0e2040d640d1120340c14502c203040b80c016244014144040080030050320003440c689009503a40d1240a8030344280c41c004844503000701050a583d02c404104c8075606014580650209804051815203001c0645090300c11403415000355503802404507103035560035412283c03174015400c070501058803882d6000d4028002103403001200c50400712103101c189000d20881c1c0c989a10548091030202d070012404028980007000e4030110280c0c240644040b6000302c0c0601095554280841c0ca42d030b42c9104d004002031880d40c12503019500981f420340015001003852550324601420004070070190f258104d0b24001034020040c0c00c05850400203110400c10145202510385036210b4500c5500c6411015995498040151926070020800b080011107540c00c41b01e000300c0e0040c15117000c0c1c0459150000a60815550341d8800da2009039604126a050f0103655440141600464601 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 983555737 1250 983554487 983554501
    0x408010612150510120312061703070f020103140f062b11030c0a17010e0d02060403032c030c060601020705030c09060a0f061206050603070c1b030816030305010e 71
    0x49107001e00240c425150800074826899000b032181c01030410f14202a502021400c01902074240007c01e6034800e41004804206035912680e05200006568015450b140c10341c0c03210b000d42d4155004c101d0416840f190400100001e41218900032166540c0d41001d0f81451000c02c40c4001c02c007840042401540b008811400042112068100d9000402100d811101c800000d003800d071403524283d8000c0b4111004549103913000d1050b40e400c01e109008118120103506a9035035640b56030384540040c1d0007080064002031080c0c01100d002503002d0403030541600c500340844200c92620000c039401c0d62000c0340e500d14503041040100c3d000380c0d003800900445410320001c2501c8084841183d405400d111000c518030f5100d82080d0300050616006a4030032030740302e500c0180507549108803040180e00f030050114107071508000312805001342c2d4541c10b031020040d40e1101c1d010b00e1044008483c03500d081c0307030000200305208000d040540201420110800c06481e0240440d401038014510210300c407801c011003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 983556987 1250 983555737 983555753
    0xd080c0c12270105180a242d12090606030f0b0a09020901050f120d0c05160b030601030b010c051f0e01150e180f061b090310021804110408010612 64
    0x50a012800b0721041c42d4003645c045540f9460b2903204618007500e52100ca440c5202ea42070a0908044c50755803c109940714035540707009a4007581a030178200c000d2210148400303004001c0c150350a090320001003805a99515081c0880e045176005170b96a20000505104120190302166070009205908028902843c2c01041600c0014014640170b0106540518016501c0c034200170000d80242c4103c07000e403840c05200401e4441c1c040e50031140c0344501c9840b0f03e103411a910780c1c6c0c030541d14240c010609580d60389004402400c80d10b40358506204c401c02001d000300304280641d000c00810003054400002c403108040c8112200d00380001241d0b403602045801a00001100b181103e0358201504180e88852804c00104c00100c043c0302c40710312900c07006000001d808191188101082144400804640c0c07894a004e84110b03581c11f540340e004440e00c09644004d03035004c0c100140c01c0b441866448100000800d040300c2001c2002405c000011504021514090054401030011400c4d5812201110307518119 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 983558237 1250 983556987 983556997
    0xc05070b07080d0b300a150c14030405060627150901120302190821040501110a0c0f081c060503010e0a0c0e0c13030f0b0115020d080c0c12270105 64
    0x91404082c40c05c04210a80400009400075001600e2141c660308805495006102d4010f450011420030104440a080c0030b0301036034811a005400780000d41d032031804100803a0403a90324040da580e464443c0c4c80d4031001c2800d460b4443c0f2030000240030790940c648200000d00a059111410000c0c0040085001a601003034485045501c0702c980c0101041d41d14080303813a80140304141c5484106400030383c0c00320707000300d281318042c070300640080241e4841645050928800c01034181c000c200307000c60050009074680701c6060514002d10324a410030420b401c2901d14503180f1000c46140d15183c400520680c075081c4211440d69852600a00028480359144941c10300700744501400c0990480008041401d103408071240b6604000b041c0348280e4076454402c81c0c25503412400da440e505020004160b00c20840d84d90a101c018a0b0010000503203042c20481c0d1013540213041501503c010310000b00e00c92005c1150311000820754041d10b44600c4401c040a5640e0045400300041c00501e00030f80255036000f40440e8 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 983559487 1250 983558237 983558299
    0x71707030b060a171f1b050d0902060c071724040c03020301020d1a03060709050d0c0e0711160b0a0c02010201090f03030e0c0406150c05070b07080d0b 66
    0x201155601070000d5212a0590f009441502e0709000d0002e00e07135404208018180304039584d4442c8a4480ea040104036005001e00d6042900118541180f00f4017880c09000002503003a00070580900903804202a41c102d03125046803940326010a000c036420f084098141740c04094014441060071091810105c48070164080103048280049802e1019210308c8101035030b000b0300250b660f120f0303110114008207142420f0b48101c0002c0f0000000ba444d020601071f0180401ea940c070000b15040104101103006400303812101c600d0b5031305001607082d1440301482d11894040d140c0c1070300310082c400e02c00d0410f00014400408901124800e1040228840959624604524280c001d0f40110f10040c6c0c0100086000a0071402d1544c0040040582c590410741b451107140d0207840340307074600ca0305101c2036840500a00341c44180c0e036464501440d00c5507a4852106000d40121202c036952242c020219900c049416554140c0c0041c403501102c0e442d000b08070519034140c1d245038982c010030700e118401c942c62000303030f17 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 983560737 1250 983559487 983559503
    0x213060c03050c0109050601051c020a0b030a1d010e060c0c4303110d0b0103060f06030816050106050906091602070512011e05010509180a0b0408070507170703 70
    0x101040c544640c059400d608520f200800c103524041c1040c03540c400e024070a80c0e2280c070309070591402c020300702c0800b201c1c0e16501611a840e010304000316100581c00c01020520386039030300c00f8100c5400e40280f013a0b405500480000040080c5800b04250901800518501c454002004018841c03100001d0300a80c1c0c0c00101d02c0c84c550044000050184005680c41801806040040101100f9640302a00c81128841c2d0b0581d985c108800c403c0c001c002c400e50b000580004040001003010401035000124002052100044c0458032581c0b07148058001c4101c000e0b00414500f04081040000d100b01760240104844880c0350345050000180c0745030009006c018a084141050a4076070f000b00a84406843c004001c0380d074098030304045d00d008143c4061007415420341c5500c2c0249021003849803c0c1a6a000360072958150b07100b511640c840c01e02104d10355110320038080907034081910080c04030f018621030088280e680d501410716a2800507613422003500d200445050030303e0210002090000c0ba548a651 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 983561987 1250 983560737 983560757
    0x507030602090301020d06031109100617060f0913030e0d08030a0915230f10031211060a020d0507020601050906120c03120705120f04090209030a170d0f021306 70
    0x80b0740079001b440009040c2c142082c4010042104150401403015803c1c1d45004003540c50030066030740004244107550101b2841054a092480e10700c1c4841c0e4050005010800b08428000210ba02c44004803015480b00c5100081c1c6410107034819800c9442000407188400c00e820300751540c1c1128072000d03224030318455a0701c2c035600c1000f0044146020701583c146040003200740002c00008a040c0110044003018091000511070343c1d020300e4070038001c180b01c002003007119003980e88000d010058148174000b400403805000981e140c0c2044000c2c450400d80b10056110304803000d505064407005090b90003903401000051100341c17996801c2d0380d401041128201568010040c107a0306040300c0b03840081c1c05004900c501c980440040d0018a02a44144125a0314203070044510b0840e0089200500420340200000c1020040b15005402440001410f55a1072465503494004d0100080801c044ca90008100c1203a00c4110b4420610788901001c02541741c40e06400c600035032900e99025030800d01c518565 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 983563237 1250 983561987 983561989
    0x11b21031b0e2e030c0302041409190501060203040311030a02031221040b15030d020606010c060608161505071509080717040e010f0b03150f0d030513090603050703060209 75
    0x43c0d80a8200f0560072110840b2405100b40c100d03590a00c0001012070b040082c50000d45109100b1201103485d0403800204900f2400708104503030308040e044d40640c030121064030314100704a00c549402444e0b15001140d4951642c9011400c80f814804d420b4441c1e004101d610300941c03000301e01500d072080ca40e104182d07542e00b0101d207865041510740e0101a04150301c010402002060400f9a0180e000380f070104000390000c90070140d030b860304080400c005030403103801300d80a035022b00c000000c00343c8113400108030343d030700c400c40c1501d400500782c4240d0801000c50f00c1005000f9801050505150180c035207540342c101e145d01e82c40e020820035000003202d1580d880e1100e0900c40d0410641c1c07940303640b00c6071042000090341007041142c1c026004152002400310000500301c0080090401205c14540250341141d844d0b8040e4030031709059422075900441094666542960340d40a11070b81588203841c0c1c6a2985810501403001c02c01640091040601d0b0400900120b400007030b01c0ba085075804040035035100d201e10 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 983564487 1250 983563237 983563249
    0x3030f080a0f0207031205130335041a090102090303070305210f04060b040603120305091e1b0d05120d0915140a050403091202011b21031b0e 62
    0x801030140e44041001d80c00c25600c034211a820313006261b0300340059125002460072a10340d055000b0045a404980d50a00c05043c090881c00540e61054400308a10320304982080c0d400b08980840300050405d1850901c9201005150703000000e03500218180300810380804d40d244613540010b014440049620000500e50342402c01c030030500d0300780710140e03410030000c0086a00b100380c408451850420210f059142030511401c01125000103041c1c40c680b8900c1801d400416010704461130034010480001c54800802e4040041084580300804840c901521070040464140021500c603c04150103203000c9940003d030640b03030740089809181c0c0d038560b031401c0e03100801c12594018194103039039103882016041a803000041007a02d0044101e03583d07070301240344101c510403034005020514804050003020701c40c08010600d00c0c418108180b450101c03000b0a4460f07506510110383c922144220b18400c000b002c0b00c27000c061460307800d00340982480403072005400d030f0100b40b4000c20001c601d41207102a0383c0d20 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 983565737 1250 983564487 983564501
    0x1b0507060c0c0305010c261005042301180b0f0d080a110601080706090b160818090a0203070e01230a03230601020c06040509010e070302130f180603030f080a 69
    0x6c0040302c86003c03015120391350702070080c00002c0e241120714041c041a00c40440c4204041c2000559190074107041100400701c0c0d03c403940428540241c8400840710440e64103020b840300c003040094039081044004141e401d00408140201100c0f03403082c1981c0c5030140910101540a05541d8807080002000c0b2021240d50884030801d04c6101c0001030414400b01e006000d8500c0c030344c3e44c1eaa4240e01c407090301c083c912480032459140d580200b12400031581e610040d05c0d01040c078072030040030f070410a400100b400400361900c0060650003c2400380e910380020448031100401e0802c120801d5080c04c0f401c01c040c0c0300c40d5034444d00000008001e010305129600c00424090003903a4600d1840c1c1c0e45c03131580d081d10411907074103001d0300c1540d01c105424a0604180c2c2e0442d00020b0070724446a082103041280c0d0003019100f20141038081c40340101203020504030b00c024080140171403409a150140b0358641c41d41459801107035620b4000b00b8000700c0d47c0031424280d552420708104006031540d46c0b41900405c15 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 983566987 1250 983565737 983565743
    0x1090f0207170409050c190c03031e0213080105090a080d0b0d06022703070611031b030a120b011b110604080c04050a0e0c011b06020a0804031b0507060c0c03 69
    0x1080d03a005150070911000b40094501c1510200000d640b0001004011f10815141c40182c00c0ca4030701c184451403185060b0341d1100d1080c5400300e417040384100ea045040810300340c0e44440d00c2c1c001c92100b11690184030315100801400c0000d200360b05011031466107440c10031001810300b110008107414408569000000c0700c07500a030000800c0c02d62401c261009400c62000148004450b1f001c041180c0340e54140c1ca03c0605d40100540065803404200781e170b0850b010340581a9500043c003401c88284c41c0303041084401c041074409150fa030103005400a017a82103554016808618114038134105990002d039803092800041340c405409a01d07401e0071800c140f2100303280350b80b0050001d4003103003030314012031000300300030098a0501c000e4440b11034030700540e480c0c9503400c041944044090300c610761140204004500c00d40d4144144021246c1781d20099a0181c03ca44000c107080784244010140e106c0710800303032080d5403046801040e185540c2c050f210103041c850b240400020102110620075002100c030002c40d4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 983568237 1250 983566987 983567003
    0x1a1303081f0303080a0e01090b0105043812190803180607030f0e07053a1a06040e0c090a0e030301090501080c03070f061d03010905010911100801090f0207 68
    0x81e4903c0c0c01444080c0c21907419901e10300700741030303965010414000c03001c0c0d043d800260021300382c2c20001480005e01d120306a40080a50760a0b000c411020f107440b10a41202c60400050304001c0c0c44011b100000201307002452907035101c1000b01200503807040c50030103010303808026196079480f00680400c291191004901490066a05000c4480c2d00340d0f0000c0d0302d9001090080c0094801404800d07250025441b541d600b1850b00412038139140707682c0b0341d003d0000c0040400a40001d01e5080c00c1d00305040100d004507400c1c44100303c1e00340002013821006a115504036002d001903400211030503168954110240d0144020b0004240041169000b03610b0000c03200080725102d41c1e44e0031000010307100a01c1010b51500580d92940803d040125042050324500c01c0c10b40401d40ca083c000315800030302c0b0b0340800032a0b010110250031540e400c0c05a0403400f07002d47c0c00400c07541d517182442c2ea00107202c1601c041c8500c06002c4148100c82d0403000340c0341142e01c100130004040c1001035222000e84105040241014 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 983569487 1250 983568237 983568239
    0x6040902130237020319031b0203070308100311040c02010b060d0f0e0102190e031606020d020609010209010e010332040506090105040c050f1305090a1a1303081f 71
    0x40c18580f14500c82c006072400121081100181c1410300449201d43c45005070020080041071248076070303400c0e07000e0081d481d00040085420084041d46000e40705403600617000020700c04181a030010500c0d0f041840c1a056407221481d41d40d40400d003e40c0a074a4500464989001e81c51484c000e5000a032140000b4201c15507c1180c0311001004150a284280010340381100c58004100144282c071803810781031100307100141680a0030749801042d20b080c2e0b0b42c180708090100d03010140380801c410081c03280d0b0b0020900050b030710b0380c060f0414600510244541c3e1040c031051007a0781e030100c0d1202c4030042c28200081c0c001c10120125000352242e00041050083c1180902603811b5000c0006102e81d0141081d40c0417902c0310480c1a080e100107031005807800c2c0d2400c0c0d06211916050303001c40c405030710003000701c000080745a640d2000d460045840d00010740044004c8018049040d0401ca0714a1100742109224500718021110a024043c0d02504100c1c107070b8000f03503100c0115003540702086000301c4558002 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 983570737 1250 983569487 983569507
    0x50126070e0415060e1e0402070b0906074503030525050a02090c0c0f061006031413050304090923010902130e0c180601080903040608060409021302 65
    0x81140030440c80d00035407402c00c0c0b000c2881e1002400d00c040e04e641c0d42d117103000000c0b50000c004010340803404900b17588141c4420404d403551a0f00c000d02c41c0502c030f011320030201d15081c0440390801000030103200920140c0741070344101c1c05000071420762420000c00030076a0f1b00111201040e2076005008400106014550088141900000540101c480344690801d500c0e407180d04200d448401001c004005900040c4404010315000003410390250039090200d003040000a072945c03034003c801148070980d42080c801d11103003c032035000d580302425031414203200740c5449104030840c0710b10080a202c04280812417000c10030009204640c010128000d05121000c0c81d41400280000d10074a05400c004400c1c103c0c0052407018050b40144a800070408214021300d460803002600d204101800140104104034a2a42c2d44407000c80e210500e42c045810309240545c00548200000762101205500c01e009c1000311541c0419080e600c05c400781c4011131230541c00d04c041032400c03128804240c446400465070303940c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 983571987 1250 983570737 983570747
    0x907120c090e07150f12020d06180b011b050a020d0308270d08040312061202030c090115110a0c120210030c050d0b0310020a02030315010f0905012607 66
    0x3981d514040402108201c401c219642d24010f1168061030510985001c10f12401258201c00e240801c0c10040611100c0d10280b004a0f4080926110745503034550b000e0000307060f2001d0490180d2444641080301c1c5c4c10040000e844e4284150302995061038608a032020000c0500040c1c517080d41c040c0c42d20b003402c240d900c0c0280404104448461320044060008a4840c21030b110550500401d00040e0190460902c0f08843c0204010025814003160226118120103144541401400000f056a02c0c0c1b011600c105410040034549240c89a0a840014025413411084000e2040024100004030703001e006080340c14200c8051000c0c0c114002000b000610b0580000700c0066240700300d5561010307824070842a0212444041d00c0e1001400a101c10000450198001290644028200c03800008840403c80c140d1303000c41207103001a040481030005407000181b00c0c0c605030109003800c2240c0003c20400910720003a81c411281044504846102c900c1c20000e10500d40c1611044076a1141c5801c58002e42 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 983573237 1250 983571987 983571989
    0x5010e0a031d0604090b0103090507170c0604140108070c060c26010b030a09020105120106030b0a0906060c060209061b070f06020c0904030c03050d0207060f0501090912080907120c 79
    0x10480d41d0128510700842140481e044001c010001c90138107042c8513114000b810f20000c1141131603543c541d1300004c00c50404c0707128024101c000d00a140f2210100180d410000c0001e03030140116814030050000701880821290f0040c820720f00350704244d035840d174200c2e610401010060301c1245400e030801c20881d407100c0031003031400101c50090803842c0051040c40040707000340f2a00000e01c1080c404150003000d981c00030b9180c20300515050b0300340116013941d20000751b4282d202001081d950a0898414105030f04201d0042c100da90301080090300d40362010b044020700c0305004101c1680010100c02c16600c00701a111081022540b540c1201580392100340da9518a003e441003170705c00c5000003e07109200054800901c000644250225240e44d503060b00c43c0101c1d88070450522105003d06401a080c03072001d80708143c010b410201300e911000710f00c00101c4506030040e1520504140b1048040740510b800740c1e0303100e1000c4c41c0c010ba9640d240240c103802e003601a0843c1c14400351550003c0c1c140020264024 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 983574487 1250 983573237 983573243
    0x140705010903080f040f030f12060b0408070f0621020403200108130c172b0e2b080c030a270602060a0207030e1c032309041805010e0a 59
    0x84402c1d00c0304141244c0c08441107800a280309400e0003840c0c00a40700d01101918000e243c10714400300d0b4044a000c006494058000400c0314034081410000c8102c1008500000d1502c016280c1c01c840c1002e00003004050040d150804000c001c1d100083c130000e0301e904a4005541240c8040600001c0105504480514541c0c15000450780400710300400c10044031200841d500584042c0c3ea5850f124407040c100c0038a0321a80c905001d21101e541b0011800c02041d07611035104040a00d16118694003c1e0115a17000b01c5240558600c1e814041104070f46480d440c0380c0780c5207201107541c000b10761814406512840700c00c424a8040460030f9240b143d00a03010740500c07e103c01e0680030580b0207134403d0030a00454400c40c0010f0b448180402c4203c401e550051200c2402403500caa8058035000128008081e0706206400c80c84408421034103040c0d0140c03a840703091442c541c120809103001405460980074075010548650340d00c800c141c624110a2a07208101a40900288156074882c00020f440d010008419 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 983575737 1250 983574487 983574497
    0xf070c05011d0f03120703020706021c0f0c0212031309050f062116120204050a05011412070503010c09150507080307030b030a02132013060f140705010903 68
    0x45030560041c28030022118032654890030300c0b124a01040f0540c01814121905400764890210710880b0410080c04064041d4006020152414600a20746181c031080226640190240f0030a440d900c0ba02038080300b03918ac6840c001001d211300020f148134911040303091591200141040140c8481c030311100c11500d4041c1c0030040c0d50ba6001000041c66021260190700107880104011111003541c004c00704080c0b000c0403541d040b404007400740b2000c3d4142d0015540c52041d00418802c5140601a40c0c0d4000318018062010f54584402c03c1180040410103d109a010203000d8082c00710802c9580001e000043c000e000000c0b00d1040a0300d0324040d03000d51000300c80f0a441c20402940100120f8807426030007402d5901e596140307902240206070401d1401d51500403842227070301581d9103541c18026120304c034500154400c90741c03420f100768143c00c60708052a04803d10146d4482004101100100c2c0e207a403c000401d943c00e007100320340c2c028011600c0c40500e41e0120703184042c48015031015804920940321 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 983576987 1250 983575737 983575739
    0x708010608030f0f0f0d0905010504060507031515050705070f03300309020a0b0304031809110921060405150109060b0d0f020438070b04031d060f070c 66
    0x200790312440344600341d151101c4100484c07021801c41c54000c24180c88000104c40c201034040c13945c4019209207081c15109607450384140018004280300745038000c40f003420300300300d058810740e000c03007030f10009120700c600c0c440501081d5985c0600a00031035641039841016038860648800031421b803601d0364042502c4001c02e465500092900907100141780ba030f1403050400b4520b4007403030124040c01329040d08076080340c0e8a0000080c0c1285040c081e5009038883c0e29003600c0e006184400c014101c80c998070800e07906042500c0601605e003518221030941d0019108013411204242d4441c85900c8071001100052154034208002d000000c41d526070303031754092414654503990300c0e1686000c2c0d6a5074003a0307944e40c1c04100080001102168480758240d588442d02500309a61040d105840c0c4100b1800001c0140220340c04523405c0c076854052043d5000346400090600135542c0314103102c00e030002c1009040c40242d07252281682e486180680d00c1c144010306040e41c911306050449a50703088843c049070200b1500030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 983578237 1250 983576987 983576999
    0x30f050f0703081206191d090105060a0e04050a0506010e041b0e150316140901150c0206070c0f060c03020c0906030316031b0602040f06020a08030126070807080106 72
    0xc1941c21660001c030a5030600f007003101d0428001c003000d8411a44106200c100c0c4441c48400c1070f03007900074180000d0901021440625500c401040113100c080f85914283c10444559a103c0d080b03400d480c080103240c0280e03621450501e01e4111940350280841c4100c178000110301d00003076221445640720383c540c4070000e90103d280f8008118580a4800c080c00184002000d0200c05041180202b00c014103c643c1c0c81c2402406041104107034003d15014041c49603d00010306100404ca801460440d5070908020005c00009103000c04802000b84642000a011400e00c491075a405014080110410100d00d47d1050050300c003110668088000d03019001198189241002d102442040064051450004000d01c803c0060f41609000c609006081c8200c2400820b04041f028007641303e4440144c0c0c6508160007018a0205540460115407090002070b001480716402c1d00c0c11907011155985460964407081d41d80d030850703000c0f0041907110b58940040d503020002a028103c3c0c0350b29008100f8030340c40b40 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 983579487 1250 983578237 983578243
    0xd030e1b0d02130506010f0804030f0e0420040812030103050304090b06120f1503061620100905010b060a0504092a0201051602070605040e070c051b011209020d111504030f050f 77
    0x210060040b0fa0070342c1036070b840bd80c065520402c0d0b01030300800000c0c00a58401c2c07440303059200070b405045500008070701400000020001401c1d101c1c0d43c810307281c1c110342c5940d603456500d128501800120903250a0705ca01e543d1940001d42e00e5015005080301c00c00d144c40034403003009101c1103400e00c45102c0c2c0c43c50042e115042c080740b0b0b107008144841c20a00f03501d0864400b40c0381c210b54a505100c1081e510a0400003081043c8410b803515024400003050200c1d490900d5425a80c1000c4010f1082e603013009000025600801110102d400c8428041000c3d0001111214024980e454807908045940c900d81d0070554190320491003100050a511000c82c090241260381d00040d01603031000c00d10400c014003804181a00950b40082c10740b50803103140780760b0b41d00c450800403000000664083e00d084010301c0c40d80c22041400310001c0200c410041400c45030009108070001000140c06100280e0030b4540c542c68248441c0d407914120000ca0f03546a680e46400f514040804000340c41e07500501044120b040004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 983580737 1250 983579487 983579491
    0x3021b0411090d11030109050a0b070201020412110303040b181002030a0e0f040b1216080118031b08030c18031b100c0203070b0c0d030e1b0d02130506010f08 69
    0x10081c10340c10007441070203000480403a580c3c10b554880700c24040031010b43c0c09000d00d8441c10f10170005005000400e01d42240c4003c0090594400c4d64010b001c2480301840303458902505a810442c28038400500344c001c02e02303511460f003181c00e03074190000d10752202600031000c101030b650007682d0001e240e00e010301003242c03a801031002c86c0000074950704008906180c50b510031a80030600803c0090030f0900c4030000b546002c242c2c05044015000021020302c044074824661006014000c000c1c002614881440f050140c40140010140194901e2070034074016040301d881021640602c2c155901c1c02c0c001c0e00c440341c1e5001f29485901d80c0050312244081ea08010030300d200c180c0200207240041581d66810011b61410344100c2108011503a0b100c080940d5007048600014020811415500c0380d5100760b050900c0310b01480c1e60103250414401102e030301c10010304408907185051455800414000c00104440c44548010750b02201014285a000a582e030046000d041c00362940320784030760f034075900340c4080c042 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 983581987 1250 983580737 983580761
    0xc040b01120915050106180603061a0309030d052e0b03010909140a060f0506061905030c04080703060f050106091a03060d060207050a03020d050f04230d03021b04 71
    0x94a4034030960340305034101008107031140001000c55260140034030101e130002d0340403800003031f1a2008148850450881340c0040c20040c40d040c06803606221004100100b0403ca21944950000018034421024015542281d50805040c44103003007404907641e221031440d4140c41041910000d65181421059102045400000d1010b04583c6443c1c50040242402d000c141c403080002007400d19240c5090100000f003900c5110300084014072900484100d60700101103501a5204009a2002c040044e0001418400528081d0741d81c3c0d492041a40c2e05002d50f0384500c08620641710003200f080000c0d0408010302400c00f400700704903030366800111541c0000c3e101d0456156104820382c15600342c44002950300c808044c0c00400d800c541587c82c60203e07404540e09a980b50480c440c1d140070181d052002010704985031415904088000803003507060300c00c40c0b00e4075141d034003401041d4003440180041c0202c9850002c042c1180c5402d1818040e440701c5604d40c651080288540b0300c4551864184251030055030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 983583237 1250 983581987 983581997
    0x307090c1d030708060109060311010503152b03030e010c0c0201090b0708091503041109150103270b3304020d0e1605031e152e05030c040b01 62
    0x101100e240408000c14522050b014010101c000c281040d00f000161b0080c80040d8002401502d5400d009001c00186240c59041160030000c0c0010a0754901c0c1603950040c00711665030001510781d0100c10007000c980d141006080e603010400080c10341650003c108031b01c4c03000003441280d100b074804584116a640009011911002060100c1070600b809000701603c5110042d1030002d1000010780717441012030038a000c407240041044100540070000d000c41e01415101c140c1c1354104003203900b082c00307035030040c1e10304240c0c0d900d034408921400103240c03000d1f0400d02e0003408503601603414580e1062504680d0001a427034800c518852a1694030585210030309110015409012620108400b0790301403c100320900743c646900c507224060501c45c0768204084044e100a046103400141402c201e003000442c1d0503c8030822444811040104005d2113034400c00440d5503036940d0301e0744080d503000b4a160341c40140f00004030350703880f01d527103454200300642e0000c40032034100903010420013003543c42c1c0c0c4416900040c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 983584487 1250 983583237 983583257
    0x8010c050c2107080f0c1c031505091603090b0c040e0f01123306091a09060103020a1101020d050708060d380907090b1e06030c091e0307090c 62
    0x68200c4001d800c5d46a0f003440c0c50f0b483c00401c901d0f400e20f8036145e1004407a140707452400e006500360f01489508039102c0c1603522075a80c90320703000008210190082842184050080061b44e2043c40b941c0300c501c04550004146500e81080340d006181c035041405a44440369150001c62661000d8043e072074102e2b2a9020041a0858540e03a0403030208144020840317401030061416611540350281c64a00c9408403100144403403410300c1c0b44c4161043c0704400543c4d40000f04c04c4a03442e03140c0e080465400402801d0147e500c0c51510030071a62541c0000070708909501c0462074400c90b6580303410090040900f50340d0350506407240c40c00c0200c5c03035154140c001c0c94003040d80124610500240d280342440020345540386101000340300007044084080b80d0452482d00002c20030f0004504a101d5003000c0042984c00b01064650400300d412651284030020f4450540800003901190b50306c400c8860f02c00e809000c002e10040d0191403914880c25501d10360303100f400f4080c1e0109507410341d4410030780c4035181992070344c0e404 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 983585737 1250 983584487 983584493
    0x30203190b150a03050d0f08160207050f030c0a0b071709011e0504090e072409030605060f2125060509060705010c02030c1005040f150608010c050c2107 67
    0x82c14004181c9500700c122030200101144041c0050005410281c403502c00d5907200000042c030520006007200010001c00c40a10411607000803040c09542054a80c2c003600c40c01c2c4000240f4100e401030660b0f0703110422800c0403031100001000b801e03040740303c0e100104ca420b900c9c1d941b0009038014150305500045006010002d0342114007521501e180c61400c0c09e924040e183c9040c8415a806030507d0704523030380324007010442c0e05c51013103550710756088111004450700c0503180001c111840701e10001c0c1103652600007040265603852030110104600822504683e031050031010368507101000c140c0c03003a0003103c0e040c0800f40a500d00c420078048030150b18550450a00390305840036000040c030941c04c41414052140090424491240564299001142c4039815042c3c0c091401c280c050b500386680c0d043c0002d01c000128180206c84680d94000c42842c00e42203009000c43c0200103030752141d000c41d800c020801203010b80003c01040c82c2c09085064070745600500c0c2c565089204203100000b0034000811920b008 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 983586987 1250 983585737 983585761
    0x70f03121112040c170f1203070c03081b13030302011a06090121050f04170a0f0c0305130303051b070806010905250f03230402040f1e06030203190b 65
    0x101621800c4138403600c40e10355411304881c03190b41c015202c1c44d600c8800b40340d520f41010060000200d2460100700d28514082a000300041c809100007410b0106407004181d00541003c14440a00d41808115446640440d040491104603220544c059482e2407500e06441c0400c500d24043c050016180c1c6141250103030045a2800c1305541d0008129861011940a01114050213000315080d10345201281068201907001040700c0e40d8001c40500200400d10001c1d03000241d40241c04114180380000c100c01d42000c3e1480d01c54070a148807100003401c0301104040c0c10201030030402c030311040340b42c46012040c0e810304d9407449030b40102c51155018600400940e031843c2c0103c0d80c0194203a10b40b21180700d0007413850803851260300b00c10020600003540c244202c2d42c0740c882c0c5110400511207a04081c1c0d40c594100c0219103015102a02403a220789032040301018682182050410102c0601c84010600748094001c0c8410b0104034400d000e288105440704d03404541d00c00328207401440905844d180d44090b204 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 983588237 1250 983586987 983586991
    0xd0207321315030b0403030e0a0b06150c060708180f070506070303140f010815060f24040f15020a030207060e03070306020406170a0c0c03081803070f03121112 70
    0x560303840c0c1e0414810602d0410b02c1038001c6204030f90b000c0075400c01e45800350554000003051849540483e40030000301d8103000d0b586400c450151440780e1451101105042140300300f2a8442c030394458403051020701c5500c9801e25207c0d6591f104900381c40c1c100201031756141d9511500400e5103a010240c14801c500d0708000400c4c0e4184681400203110700c800c4040b00f90b080080365000c50340310400004200d052418844840419035800d0b5200f950f107003039400035a0920583c048907008000c54800b0201030303600000c1e000405408100c4035034a55949061900840c042e6014400c07402c42000a80c0100c08d0000505002c055455009045c1301c070f0400a04841c10780854a03016030500c90004000081140344c07004001900f01980c46003101c2d44540d1200002000142284503641c0c94800e901c0d0305a42e01c0030001c44031903454a0a081c00e03480ea045100d00340888205410703111b00001440c4c1d0100410010041034081c402c0d00c07254050001000c200381100c100300c0c0601c00700002044002c001c50000ca030710b00d03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 983589487 1250 983588237 983588269
    0x3130503072306091f03140f0a020702121618020a020c0d050a0807080904050603120904020d1401060f230307260f060f04050103120e030f0d020732 65
    0x6062030802d000081e5400007170341500d4400c1c580c894424000941c54065100008001d807600000c60400090946030176500610314440598080342c42000c543c0c80c0c800107071410641004590010f4001c5943c5402e0707101603c03c5094181d894070214003416428000c0c1c0e0785190340b9030060254000c0391414040b45200c0010115000d0054040b9180001d1264011b46407582c06100b24644400340302080c0411030b9006011a4400da000a07034040b4a0a0007000311040d4400555015071a900c04d10424400b408600035407044059000002260a0364001180e050310702841d41c0303202c40d01171501000c5904023510181805520410800070b17907a54018400303001c84c80700a544110b03070440041d002c8082000705072402d061060030481800980d103046003401c000280210790402940d403556480e210011750500500060002280c80b0031000c0e80c060040030308115481d010348050603c207050013510f0740000c4c01a4480424804035002201a5402100b1558401c4501d4058092103d2041100b8160041c2d0300c1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 983590737 1250 983589487 983589499
    0x6050c041703090f040b090c1303050318010f0504060c03140f12042018040c050a060e030105072105090705030a03170c070b0121060e031305030723 65
    0xa015203841031118807116110040d6850ba00000d082200c440311034210644650f00340044001c40790f4508605c280c00400301c11007a46e44c3e10442505d04034290540d44080c200b808040f07401c0310161404541d01407103480980c1d51403414030409205031050702aa0159100054106940e940064000c0456100700140f203e42c0500b4081c0c0b2400d040302d6039020300f45170340d140788180702803104104070b41c02c039039440004d441e40f01e00c100c04028010072140804920541c1000360200d0124080c00241d4070440040c14014201c00360143d1207440c0540300d10315602c0000c0c0250b00c3d0000083c40c80e48101600d00b00652207004183c0304200c12070028002c0e00010384050114014040001101da0b020850940002c0c480e0b1280100d890140000c0303003030800000c6c07421a5440c0c3c01c00041d8000386007011882c5c1560170880311700c0307201c0c4c8807001321005003905044000c002034a006e04440d00b001c4000064008940700b00341d40000261a03206242c1c48890900c1a240c14500c240d112a07010a001c003100c0c4004e0388040c0203 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 983591987 1250 983590737 983590739
    0x60804030c080309010e07080609030a05090406030204020a0206040c050906010e0603041a0114010915140d0f140108010e0f0c011b05072603090a090e10050f0108010b120a06050c04 79
    0x40c080036030b402984c0c904440da5680540e04810003041c45004010820040940003604d41600b000e0384901c00c40d428541086800036005610750f4840d4440c8003d15000f40045440c1c44403c40080d41d01c8109031001c0d10701800703032400010035281001c0098411070040c1d43e034000d440401400e2010a1700003a204440140028445070100385542d07220360300802070303a410442042c40a0001500c1e120041e040408154080598510b4568100461075a03045c43d001840d030342d41d0319202c0c0b0700c030041c030701d403101132051908018240d401880b41c52111070503034030403000800840d90381441541e91022101901011604404c5030324035190b00540350803066503003000c0d0790615a54550b80c0e013800c1c118280c1089481510148987c0891004030300544008106100114900b103e48000110060700e1480340803a401e0302d600c0c0d42c0400100c14803241001c1c404520040c4140d080003820510205400d0003002d00661805940000c145080b051860844220402912840001340c581a01400c03008001c40240481084 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 983593237 1250 983591987 983591993
    0xc0a1403061f120e010612020d02031e0309010905100e0103050c070b040605072303040f11040c09030b0c16060509010e0a030c0b1501080a050603011b02061f030c060804030c 76
    0x241e00105003002d0350714a000f882d961803101d000c480325161440c1990b03141100a0109060820a0104007a01182d40451102d520710003e440c0a6110149507901d455101d00841c000000001074600420240c0380c01401c262110140100d0748605003c00c40091414a848e12080d400399124581080050724441d01d0b100c03140d1640ca09144003540c00716181e0b55104108000c00744d00c000c401084100301c041031540e00001c0421141d803400080d001401e03034844182c0020400542c442031101d4080094814810f101d4400c101502842881c402903c08a02243c006000c030a400001c445101d2416400b03807020035603a80f2407500510004015525641d640c12503581403203420072103049050b10a60300c81195920a01e401c00c887c405c013419040c0d030f407081800420710340c2c2c1c1c000b48000c0c1c2c819030410002440d03a6603080000d0140019086440e422007040384855205940850b5180c41441000c01c40348190300030914001d001d030610301c0041d01d0b8038142441402940d02c00c2216580050003807034118407184082d1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 983594487 1250 983593237 983593279
    0x801020f030f0f0420130c020f0d02010b0d080702030102091917011b031802060316030b060901050a0503040c1d091009030f3002030f0c0a140306 64
    0x10216880d50012040102424142506a9001c1c02c0d8451041150a05645003182c1c1c01650140520203440c410340c1d48030300c1d1201e815400c4040c2d001c0406102d400301208020351120101c001060355405800c4604051900500944525480141c102c1811107903070f0315403400c5a04010b0341207905540800940120366035181000000103040251040070070310346944c0303048098054461029603414001c9046154482500300000c1000504001c5803055030000256507448555800950010002c0180a075810364501156000c5e02d041d2020051401ea0701c041194a004414400d400a94208021481c4034465405150000c2c070607401202843c0e200c0072254210884181046800d0460030700304608080d040188002035281c52b0420801c0c000c0361346001300b10b401500c0009082c40107a0102e510000740800702011034504a44031001e9259088010f20060751095528a50080352a00490455401c00f41240d04c03c900944484000c0281e00380100f44613000281a00c0c1d000445640f0a04142c840c1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 983595737 1250 983594487 983594497
    0x1b030106080102120915070c020919060603020c01140f0103022803150606031e0b06090909060105040c050a05190e18040303150302180a2715141906080102 68
    0x1158030401450b2039a407840c03a00b900488a5078183d01c02c082404021070b084984423900580513103246505941d51030319447c4207030702694405030030352130000d0000c1e00a0740f60f0301504240c42ca41c0024413140d551024400343e030285c190f8000700101420001000103140410200310180c0c40340b614100040f4100f0014800c0010720b80c8180d030590341da0840341001201d680300d03d402806003404e0030003c1140e445d0b244141442e28101200f241c5903114200f0b00c255541c001520314014004000b01d18074039120950546500083c82035030300641c1004400300c1c1050041003690480c00d80703503030f58a0822051002c036448041d05607280400340001006000e502c2d0700c40b85030030360040b194045c0445a5041c10701d0b0080440b950401d01d000102400101800107030f580040d03c1d00c1291148000c1c61030b80c0c54000c0f540700200a0315884032840e00c00031030360140f5000103c003176082c45400f920404003900c0078007820905945401c010206107269038000213480800010054050b02d10417100002e9554071024030b182240e200d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 983596987 1250 983595737 983595757
    0x5040c0518012c070e06091011070b0405011202090f120d180b0708090609123004050d11061c0509010b030a0210050c03030c0901021e1b030106080102 66
    0x3005100803400000d4141d00061110398025841450f80c00280c0044009044041003014400c020004c6070358140c02d59807801303401400c4400b01c00401c031015103610200d01d01030704c442c090703510300154400f200000e880841700c06842d00c8034160114200200250701002c129540110380103441d070800e803075600b18031419a1440008140c5016070f43c0000c0c024404c602d10700000400300ba0b400740030202d000303020b440101e64070440140c0c8540041c40010442c0c000e41030301a4200300b007409410008800080c0845401c09580011607082e140701c541400c000c0c040405020207100208810091400c000b580038006500501285503440c40490009a140d0b12407000c10100140b5001038070900603061140e650030800f980e008000200c00c01c40425195012640c020780300f809260900300b4840c0c0901c00703e410b00112101602d550703260552200800b9040415003500611a002071517a0810a1270107084400c0c0b9502c0007441d00c4000025071080e440d40140070982c15548640c400036407400240050149111 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 983598237 1250 983596987 983597029
    0x21080310030b3301050f07030e03010e070e070f0e1e031608070b04031505061207030312050f0f0a020a0e03060405011d0a030503070309020d0f0323130905040c05 71
    0x7407800510b48a00c008402c04401502080c40f80c034003da03040f8080300c1e058540c0011094540c0c0302400c058890b0300b43c403106181c1550a01e4982250390030041002e4096686c1d50a40765103503103850382c04440c008034108101c404039403200c1c1c10401500c0c0c0105100340c3d40882000c40c807601320620012a0a000c41310440d66811110400e040c49505414000078002e0f0441910244c185443c40e2140b8410280c001e40701c0503c65074903000302d4410341702d07590b10110021081088610660303036417400800c080307040074098907a14a004007240040104c110407600422700300d0180d11075a02d031450004000e60180c10b1403000d0004540700e03c10304da1401c1c00443c3c443d0f03018800000340001d078428a030100010002c0584602d400060404d80001d41041c1a0307070304800185400920308101d88040b902204103c280940054441d1080da0308040d03119030b44008504480300b10001d40130315400e41c881300c0e0007000302441c0c105240700014803072901241d1010707070b01c00d002e200854155030f500c2010844142c1d8032a114000e82c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 983599487 1250 983598237 983598271
    0x91531031805010c20010c0203060f010e010501091d0a180b01081203040b040b13062a0203090135040b34050c0109050d05040f21080310030b 62
    0x12000700c0300030005000a00b4039030280c0d14107a0300c8913007130b6041142002c18800160303039110060b445184d41441c1640d01030101d0b00c1c641040b20000d41c050000b4801c40c2003903c108000440c55520503a00305089518549280c9a540310600c1c40d4045c2500007005911900d0b0340d8601101c2000d14994802d41041c01042621303290750515031300b00e05200c008800e41321024410024000087c0e030481220307074055042115022507031560040b49041e01d145001c0640042c0c2030043c0c041e5082c01c0000d01d44003402035410352003600d01440fa4280d849014084044d03003c1101000346046000c110511b030780c00d504018002413900c082c1200b0110b507152055030151504550b0070100003200f03040b20010108884031a06900c0000c054410640c17000c3c00b4503c0400400c0f002056004030000c00350810400c940c0c2c45801d03a00080074030070740100950440d01c5403450086100700000707500150120700c40d403a00e80c003841c03c0603028a25180c521240c0d001511000c048440d142000000c145569105805280e003101100d1401c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 983600737 1250 983599487 983599517
    0x5030a15120b01050a03020114030a02040902070b010e0708042607080705010606170c0403030f0c020a0324020301080d030c02070e01060203040e0f16080c2a0609153103 74
    0x28142c142c0040740100d516420501c0540e8218003030994020f09140c94561300c0e40d0342e80701d01020b4000c80c0d121300d240070f0006c41d101c42000440030b0071905a803c0f400901c3c145c0d64901030112020081541c024103d0451400b0b50301605540d0307216000743c400b81301e00f90f61916040d035441c030321540c1c0605815070701655594403c0c882e0b103610800305100301c00300c100400386501f45000c110101c1d2040d880002d00788007600c503481c00000d0180c040d40b41c1c102d4004000b00c00c100d0752405c001c4820413401900414068515030198140d030319901c2524165413030780000b044440d0032001c0581c02400700182e04c501b58420030400040d45e44600d840c04c1c1c068007040c1e003c2c545903440c0906c81142043c0244c2805034409100007000072400c181400301c00388107050314203004152140940c4080a1003071302100c400305200d14010f00c00000c07a204103407880312540d0085a01e6640d5880380e0b0303a190340c8050607503c04400041d000c10000e6505201462000701c07c901c8014105a044148020354584c0410403800301d00d00311814014 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 983601987 1250 983600737 983600753
    0x50411241c060b0c15100302040219090801091e020a0f330509041e0207081e1215060f041502010f05072307020a031506060f0f05030a1512 61
    0x3407451040300d600f4100c182c80a140c6a18079140c1a001e1145c4c0c94002545850030348003990300660b0041c000b15a901c0c0740d61a00d034059492035603100c2c0800e82421000400640c148141402d59030000305007daa42c411110740b075882a2242030581e070000e0780d1702e000b04000d640f10035003a008100d04001d9205040b1403103450f6800440c0d80340c0c6008180c0181030001c401d1904130049940396602240d00080c100600015030303000a00300c1c8019a4402d1002c90700400300328403000209096940d5001941080c121020f13080014407a0142008200c143e800101c1c024128800305540c1407440101a503040401c40c280200342074216620609842480c50303104040c0b00c0c0c080c0306019800742d200201b0700c031078070308006e010b00340d603d2849030000507410070300007224880d440a007903481d0981d0081041c140c0e2596800d00b542103c0341c21900310051441c10340c0005550f0300400c201200d51003203483d101d01031504050f054443d904010301d10f006054403001da000342149403200761405040c030381c00040b8404c1038500b0a240 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 983603237 1250 983601987 983601989
    0x60c110d1406340f030609020415021009260c0a0c150f050a0c0201050f0c0d090f080703081c09150f0e031603140313060e01050411241c06 61
    0x60000c03085403c21000ca00d00402c01c03100301e00c2c0c0c20018441101008114001c003403942c04401d00e0341c8042004640c040c01c81020100094044d4201c2d10705554101981e003c9404614004200d80b40c40c14044104030728446020701c0680d03600c110f1600300150b0151560601c0000740d030860385034109030424010084500d1624030703089510314010045040621020749144692001c400900c41d582c90036104681c401c0040301c0b11100780207103494403006d111060701d64030710100b249480462240b40d80840c0c12034011101204803106030004008445c60341c0c95030a425444450f0280b41503000c4510081d40100e0f40c058a02890711580c180c82c040304401050004440c1c041001c1503140f820020400074910000003070342e601c0f21268281600412240c40d09030b8400c07205511035118048003004121010041c00c018050b03d60090400b4040585920115800c868040320010440400c1c20300c298078600780b16101c0a030000b40711407040c00c89036101010a4403904415441460503100c0300810a616040d802450 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 983604487 1250 983603237 983603281
    0x120b0703050708270a0c090e030c0a060507030212040b041106120408210903040609050603040b07082a2a1c12090501020a0315060c110d1406 62
    0xc0310b410081d40c0140310740000b0340100320680c02c038030351400035410703200c440841070101c00200c40da601440d1811074400b00152040025203807900440014040c8080b00712204d1036480d8014010940c0d07982d80708401010054540f0302003550034050441d030b416036034001034065801258200d80c00c0c549441c0410f907409a050f81d03940650b509015143c130200f020403180341c02c55800100c86449000301c03c41060310780317502c4100050061405041c812125404001081641c03810707561084080e0b2140d00740940c4d480300342d900030700e2441c903500080c440610071a00f150304400458910954003c0000174a007140300c081c80c0301c4409040018407081d9009101c1c4040361b21024100c9200080c10303a40d02400c3e2200341da484010310703440d0055401d801c4d0a22031900c1f0454550b86a400300017048480c00c21a00035044221104040b900d000b02d441d20300c040700000f4000301c4401e0340c0e400001362040c0d41c1d19a20842c654020642000d0209000000249012518481c0c3c2c2d12a100905081c0391808440d468050000108 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 983605737 1250 983604487 983604491
    0x30f0906020c010c180b160204061e0503060403050a03090c090f1406030a0201020601060c0606050a12150b060a120207060f0905100207080a0806010e0a081b03190b060a0f120b0703 79
    0x32008106841200385c12900d40c280215207611401e40c20507141c12215000950041c41d148001c0b54411910103400a000e880c0000007551580702c0c4141543c0b580c09a50103030100c0d00600c9207032141482500400078441c890444003400070341da4643d44040e1103103814181415a19083d05c00381403a00406050b52100c1c04070000c102400c82900080d49814060007108100b0142040d50402c1c041c46400841c01044042c20008803a03680310300314164003c510b0811116001101c0f1a5a0302c5607460085c4181c01400518891a00485003801d90b51001d6901080d80300c00e40a000400101d2254442d03140c0d503003050500402c00d50000e192039400d00f920080c034600319501c10b000202c040b0302e55000781ea801c02058205607801c0e494010050350b020f0030340c203501507000703030b8901021480010120740f400101d01c10010b01448141c0d00d804254540c100e02c14005028440300170118085002e10b01010f412540280c040e195440e1526160f0340001e0864001816944410b514841002800c41c0b160350700403003900e01 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 983606987 1250 983605737 983605757
    0xb090f0a031e0c02060a05030c0415090e0c0a020c0603090a05010614010f11070608041a090a0c0617040204021b03040b0a091d150a15120b01050909010b0a030f0906020c010c 76
    0x740c0140905042e1324100074002c0b002600c001140c80c12034020307068601a800060be00d41d40000c0103501c150041480030785c4580045403911130800140d4400501c150082d100d62050901401620707040105900402c0c400d811214000c60820b10130b0704040c2c5503600018100c003400200241041d601808050100005014085070522000c0b440200781d810074a4110340c16215410f0544490030511410f800400c406028440e240384000381002c0554410280b42c1c02d1641d80d06415130b294140240d100c404800705c1000100149815801843d02e09540140d89240000d40c00d480781c610f800681046240031800521b08003805e4104560780c004000b01190341140817500c5a0701142c204016080100c090280e11840c1580d43d0345011400c050620001c0381c01e00b00315403075002803469400c2e007041c5100d145489046009544100211101e46c98040c1c80d10f920b507481e1007810509179001c1d91024040540c0c40c10445001c41c8207010702845039010366405611581510010b40c00c540800e5581d0b4180a99040 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 983608237 1250 983606987 983606989
    0x10360302100f08070c0611030106030f0b1c1e0b040b040605090606060f1b03030a0212090d02120d090b010603020315091b0a12090605011809030c0b090f0a031e0c02 72
    0x549140d0000131842d00d00005803051400c4000b604000001ca201410301000200307400350715602800328000300d14018000e1000f00e030700307010703040c1c100c1896500301240503088100400d4207a117020b52640b20078101000c041481f5220110f25001c291000c6600c3c10043c41840305009050186581151451010b0001400c02c0000151244a0315000303480000b00421a111000100034010040318880d0341525030701d01c1e0400b540d04c000d500c0381144503d80d485410100d80c00c050300090903100c1d1401e40e002010510034502c0b0018040c0c00c10304103100c466486803001c000090524250a0080402d03441c0540c0b01d0a144d00c22030403d1550307000f818040c0b2244030800840080c84500c0c8862a0000c003c807030358a040e0940e0441c0c94500303140c08404000e0514225408100b85030344058101c0341094084040000d1030701154081d0356101002900040b48001c8078004160040c48241e00902d1403012a58040c0c610099907041c801680c03010740109140fa20003c008a240c04816170710490149000400d600d040d40c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 983609487 1250 983608237 983608247
    0x12090d020c0f040e1506011d061213050a0809120a030206040303200c1b011805060a090306050a050f06030705061920010b03071410360302100f 63
    0xc05030711560500d040c1c02c1d083d84980e44541a004101c0055480d000c5100300c0e607020350314003540d039070340040e040f030b0000190103d10b50b254985891005103901e16000890507403041c0183c02601c0300c2d68004000704c4081c00188104194003220b0b00c03460001c4e0300e6a0724a010010414104112481590010740c13141c40007990106d00c1552195140c10002406044007146503400e030b6407900d080e450f9000c00a004040b4150004a540e290210345412104210300e4000443e02d03105000845500305a0142d001c0c4001d250800c050103a500710343ca0640000d66607a1140d80a81e1400c1e1410192645d8030350078000501c0b000100780c6c1d40901c042e001002042d16280206000d0720804100c2c0c0280b00c4079801c0b90042c24461a021561810f40c2041d14001100b50440d2a000380310541c0d58500c64031175100001001c980561000b40024401421066a0100c600301940c4103031240b114001c5500c0f8050003103581c03401d208462101c0d00d500700c180e00006811841407001c8036038005903003410b10242720144228a0740c00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 983610737 1250 983609487 983609503
    0x30305150a1d070e040e03030108010e01020a120e0109080d02090405010b040501020a140a0812010f08060712020307030f060b0418150512031903020a020d0908030a0c020f0d050312090d02 82
    0x458003203565034101041350091a154601c1d0703881403c00e0b610868032080040914180c80f2104000c20a804085441a080740702d0442504086408110307500d1101465510000c81040040004580354000b541c410020f6802a4000e0507203907404500440fa030300f424030030a0f014040d00c6452b00d2505081200217075859402000003400d0b0400c0da80051149001404050341e07a0b94800041c2d52116000031615000090034040c2280d80c6040c5c0c2c600182e040d02c00101c0a01900c0251110a20820000907140207036000400060034984c480300c22501c000c07424810203005050702c00619490700e04200c0f07611101010340e5030000a5500b0b1000c80c00f0800300360b00d030280455404407088420f00b206040845d04601846030070b0501c800e012404040000d4041d0003c2001000950a840c60410001c40507940981140039100350399005110b0090203a00415401034040d00003061281c1c1e50a6101c0041c50310480316504403100d800c086881420f4014022400350041c10f0840a000c032026a03040007503032140a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 983611987 1250 983610737 983610779
    0xb06130f1e1401260f0d03020a020f120304060c021e010c0306090504110f03100f02040501200703170405040614191206050c07050307060506011b03080c0a1b030305150a 74
    0xc0c0090404e4800410003030030130180038605c1612039916906a018000390084a0000054045e800c0500310010002c00c0c10004041a00d864904544950300d80300010021400140b0030362240c603211100407244c51004650b10300070b9100115000e103600320f004040c0d521a6108400c0f150500080c4000199080040300c00100c0c1500d070780d0b0400c2c1c00300000919002c9624407c0603910318010141000707800c4c0d50010019640282ca03010300650005412050006075181e0503211908980710500001c0ca40c6d04014650204a180450915407101d0005044405d66405008100c103100800100781c20702c010060304555a008030041c01900e428100f8928002002000305a99501d20014200600c004150340100350000100c2c2d489400c10701c1c012000f441c0940c5c005001c1280c0b03070111007160400c4a171503008580d25646540c1d154441c031496100302e40016204009210b00340f01c194600e099240d58201d030550207940c01280500f400108015000d1010101c14015019040203108000f2803407218680e100d6 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 983613237 1250 983611987 983612039
    0x91f1518090b01030605101413050a0b060408010510060302040501200a0f0f0204111932030118020702010806010516020415060305060d0b06130f1e1401 67
    0x264840440050001d25401000200790070004130901ca202c0c3d100c2c5208500944035848100d455228480305050142102a03204800d0701c4a00907440351b0b42c0000b900100d40b400041030303601c0c010f4001501a00160404102a0364a0b0100300c00f00010707500c5038000744031505045103400d08080000b031088541c061011400c1d1200fa052440a0508021600050b034104101941003029458a00f6400000e60b0047c0d2081341072040f140d0b01850040d040303400c01158490704a11a840c0c140c81030b22a100803806003c10f16400313421046262060483c2901c01e03030860a010f42e07880d070510860281d41c2c4041031383c40c005030307205010880c0144d1b0400341044e0401070900b483d0792240307010580c40c5840f510b031400c000d4000b03060080000c1c003508082e00d2482680c0090b10b05201035695030051020b03003d404c440240c030401200000c100c990810090070301010901800108034100342000b0f0340184c1d0031810300a82d06008104002001c0440ca110b00d501e1004000400c0509515142185030f0208085a49104000d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 983614487 1250 983613237 983613269
    0x403020607151503021315151e020c010206090a030210020c0102090a030302010203191a04021b160f060c21051b010207061407090b0d0b030105091f15 66
    0x8410000901c4480240742ca09003e08002c400100c0940071651104034081c1c2d9994100140040043c084d414039806c0360245a12103504d0601c800c10801681c0b1450701c00c0c44291340c0c0c0032401071001d44503614082203030f03001042403ca000000a140c0100181000455000b20102a0001e54042003110300b090300000096154080740c0310450081c0310740d030400b5510a01604c030001c1010740640285100e01280303c0028180d0210b58041c07007e4407014900940c5c0c000008643d080246080e5000d03090410000e0384440040b03840c0350100d803924080141c45100810704020800013982c00c40309100140070310f031401008011007507a03800d030241807601740864440350b6114a00e000078414000d6814407450b00c1c405501c00e0f841100070600035402101c2c00d880d003034109011800120b0014800d20701505031355403440c20b91403030303c560b80c2042c0d0407100301d00c08030710f40300c580b407000c980d509004070f50080200d14080c100c40c4041200c00e8025842c003485c484140ca06054074040039920f030941c03403812a0000030302c0610706 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 983615737 1250 983614487 983614493
    0x7210201120b10020a03350a022506050c0c060f090c0310050108060105010c050d08060406030818040b0a0807030f2109060f17060d020d1401020903010b150403020607 73
    0xe81034440b80140c11950041c220600280c0c00074890300c03924003c0e04e81c0b0f03001b031540b104c8a414401c105040c801c140450f42902d0075048400361922640a00258001820090203a0440321202e880100c40d007800c1006a220105101c094860309400c920701c060300c6031400035a64101038958a00030a0100d03c0036802d00041c04000c03003840314603010f520040c01e80d42c00780c41c0715040c60000d00084c05104021320420001007200d50040101b03019141c1c1000080c1030851408078101c038120b40c010725080d00181c880c400000054000340c0a4560f24010142003002c214080b42440b04940600407103074454a4005010801c100010580e03006498000c41101c00c00700322810500081c9407104044c04d0001401126803100d40d5204611105540680e56500c0714098070210880e0302d002c0e19015a182412014049029031405022030280c8500c05404500e003005e00751155a400e07601c98049082a940024042c4034a00c3d0130b100d400301805040301c85211003060000c20301d0a5000f6404028060400001c00d2014 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 983616987 1250 983615737 983615741
    0x12030905040509070905011502060f07230901170c0405060919030b090d05040605030117010e0f0313050607260c010501270507080a0f090816050721020112 68
    0x140c84054018000c1c1d050480080da610215441000e600303614210020030745400d2a5100c54214007140d0051005803280e2205803220300000c0e0100c0c01b030014410710f40400408030110b14074a00000340d08039865031002000907041d0340d00036a5070b22400341520b003006100406882a103081d03031425903203291104400d102041070180b107443c08550200144600008016640110b14810000030301580c402103016001030355503014501480c0c022500910051001c81d155031100110010b80400114031145c11a0306242000c444110410312500000b8241c60703000b0907100748038000c00056072031601e42a110f4803049010122000b900c1d00b81c0e41400e01c421600080790b005d0783c41c03440c3c0c60b0b0000c100d15651000d030210b071800c081001c0602e01c0e0020a55603400340a0381708451103041540c4840c0096aa00b4042000030404850b8143e030a40d131b24000d203808141c8001c0940700c0500912404010002581411890908180c0c44401e51014030480d09540c03c038405c000307003035642e8207080480d60501e0f94482680 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 983618237 1250 983616987 983616989
    0x120b03010f0603050606042412020f06120108071e09020901090e070503061008060d0f150608010213050f0607060e0118030507030905151e160f05011a010801120309 72
    0x154160501d00b011082c4000426002d000d500121400c111212081c055552001c1c0480c50703820761407104441c10031110fa041c0090b0000e10b40700820340000003030500d00103825a0400c100034081c08040500510084030100400d502508488144100d4009081d045e616007000300d0241e507103029004a007820541c3d0040c21118054890065008120328140c28003e100307810440e002d074450b4030303954507503008140035184042c0150300142c9035941c81459500e0b485200b03209034004031022000780ea00d50210500520584018002c60b000251362810401030207a2000c4482d0415442030b6281001c210b455581e80040f00c601561042e40440c0c001100740c5814014802000c6140801076100d5110f42019400700041480d28400d440c0d00c6c0c21982c075941880074500240040542140040040800d81e034075411500d01c00400d1080c1c02440c3c43ca080e078980e1b810035042c500c22200100ba2000303040801c04203024a00400c204d95144880d101c1c0d01c5030000b0030360607061040440d2014000c0c812003e0500c5a041c0b40 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 983619487 1250 983618237 983618261
    0x606080f030f0903031b03071208271e010e0c12150a0e030406030c1701050102071406090d0c030c0617150d050a1112060c07060b120604030305100510120b0301 70
    0x802581190041e4888e80140350860f01b070030510102108060041e04203502900b40a0302542c0801d00001b4002600f13103010118041d588500200e012a50381c5040c60780a60204000c00401c0410344020f000349400d0982000c41d2090129000d081a2000700141c00d040c82c2d039681c21000c2407501d03103030004c0c80280350103031140c131450200150210b191600354002c0d8001100c0c640d510b10b200603140e040101071034000c0c0601c900580000070200898205000c04100c09880201a01d00d002c54000004548006005089400700c181010400a00200040d000d0041c1002c3c10015a000c902c09140841c80d14000c0140301402c0f017840c01910707951144001505e900364804102c1707024403401d0801100c1100300307604151145640c1d2680c90a107102c082030190244400d59001c60624101d0340e6840c0151602c0b84c400303500300c40074030034840c3c01202c02c000e840c4c000c0740240c5001660782401281c01501039076036000f00e8003561705401ca00e4400d651046002d10007407200c11002604000400c002409442008260 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 983620737 1250 983619487 983619517
    0x1030902092d0106031b1805060f13090b103e010c120f020c07140f0604030b061905090610090f030c08010608060f130c090f02070606080f030f090303 66
    0x3107100740c2c02d60701030000724211b2070201c0c015020000d0104c410001100c6a8403c00d00800c4040240d802c2003030151805000c03c00e007441c03c2c01e40d40410400d02d00407a07031004a6140e19a8178040d410300384482d000400c10090b142060100e4803400c04841031030700e848a91070100700c00f002c5840ca08000c114080e010803801e03500a011a1142c200001c101c0c10142d80e4078070038949800001d0385c08031203034804c45000d4801c11026009031440c1c590300761003168100d04000d40040c510901000c1c145d440200138006140b10314a41880d606012080c07108481040748020b0703207038503080d00c280400e648408503c1e0b80308074110340103030b9112500d100855000a2031350110040a0031031801000f0031110390300201c2564800030080001c503039143d02c4169611025183c00d04031400c078102040c0035581d04a1a481924028001c4070003040c0d0f00c0d1005011034043c4800340d0f0384154003007603082c10000035000350340c0204901d00080c00b041c0404105e03280c9900c501600c071b01d8610400a40c0304107640301030050300c45049034a121 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 983621987 1250 983620737 983620739
    0x1180b09030118050c01020d1e080402030a021807121103040b043201050a11270904084f0b070620040308180102100501140f01030902092d01 62
    0x2940e0b81c00c1d624000790148c00b03036801820320729100d10342c030f07078514007501406039075480850200740c640e420050020380e01401081224030258441e00c40007480060707074003662003c81c5003c0b40000c181d45840c4110702c11060800b078111082c5a401015690001d40104801c0e8250b26a0f19060000308600d0b59201940510300003c9401c00688142e0300d20a2280c40000f400381c2d03550709044104842c03d0301c200881c600c0701401030000044926107a41001e01d440b900b100d00c9007042c0c4000907074002040340c1c1101c00b0f0360005058190001c0032100c022458400d488840d042c01e210410302d2814415660698280d4092100d00100908061007804020100800758aa0b12061410310901401314607513500e202400c210614041c005607402124110780e006102c1604141e04407510300d01c581c0c0380051907811071280c8075a40d8440401803040038000d11090340410844075020091004030000a1081418107207002e000784007584595644652184086880150200380c0403050f0381d20761203040008020741103500c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 983623237 1250 983621987 983621993
    0x60901030f0501090605120303040c060e03100509060123010801140301020f0c061512030706020d1407030b010f050a0c060203041a070c06110a1707020f0d0e0a0501180b09030118 78
    0x5c480003e43d00d040e25032041c411102400d55030789100665004100b2000d2140401107a40701d4111101c00309002000d0366091405000e20350155a01030741c010050760040340041100c00c103240d12030400100c0920800440310800000a40204d9051140c0200464020000202542c0079811034090000d00c51185844062a03104959524002c851070b10790818a021100640c0c40c00050f8400300072001da004520b0318906d0f03900e2034042d40192a150746610380325210f41040e41c2629440900c196119540014141c9542d800140808403002500c801d10408004c1e0500c960780c0030040100d01d60704130341e015075607480c3d5103440390444407d40c00444440001205008d49960710440380d00c00c0720702a00092051282318400411107118198180000c9400d200703503645000012040f42e9844080c500607a580005640c1003e0b082c1001804103a0014018019012503440c00002c4400600002c0c82d20b038144009803001b4084020360b41c00740403804000071032600d03450758003501b284e00700f407480e0354140c501e03e045c0346 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 983624487 1250 983623237 983623241
    0x7030c0e1003062c0f04150902241306030605132013150e100f0201090b0109150801090206160c03020402040b07141f111905030106020f0a11060901030f050109 70
    0x6404c03a410400030900c0c00004e040314030301441d004503103031418820340361502009069150302282c00040d5201c1200403012001e161700350414281001540da0140e84880f080304c42640d0708450103251521801740290f0b04d804c841d10803540b4500c9000103c0c0d00901c10f50940072005914040554080000c40c0030604220340c140c03104030303800c030f58003405003500c0000245c1d0306a250075130542d0013031814003042a4403449048010048201e078000010810f40c59219001e1003e800d030412491143c64500409908403400b100d40d004100142c0200040b603091360000b280c070301c0b58608449440010079070300d50601c250550010700031980101308640e202d40e60302da0311680b500500010351350190b191b038031006600d80120342d0301640130f100781540360084141e01c0070750020302c2c4200c07094840301d50503c00741070001d0b04c41d4130401404455440f0350341c4a40c50210001d152401d610600350701a04541000400558441072466000303004803400c42c0c0310258000101e00500d41c071200300d9071603401c282c0005a00c06140d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 983625737 1250 983624487 983624549
    0xa03060218010f0509030a0807140d0e011710090c11030a120e1902090705071a01030209010803040e01061b0618051009053d050f07030c0e100306 64
    0x3a00d4005043d1510907080d60b444c05905501c640607003080e40140006281c3d00014844184520030b456907502d480c1ca03086240144141140703011400c0c10000c02000c0d038100c1e00c44414a014004200c00c246061107002d500c48180b0311543d60002e4a91004000e40e60148045242507009081207035283d80c07034000000d100c01ea0140ca01c2c00c9035458145283c0140c01d0202c0d9a041c00c9113402c001d0f0140f50303030380d909104614000821a00c10401e05100d100000b0b40443d200b0452240303d984402225411401042502e0006170320418072239108004c02c103d01c01c8000081411100303142060b026015851120554452920f00d0003042c20f03107042d0101448120285d06010001d014500300d030984001c501c0c0c01070031541c03503a00c0640f180e403210240803140c0205030440e29420701c00c1c010103031400110300c49800b0824440b0310342241c4251a0010010f00b203110780c03826544507800789000d001c034007440d03800500440850703444180150070154911402d50300a420041c020070b46079608440b10709000e00703411050030351 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 983626987 1250 983625737 983625739
    0x509040f0213020405091503240a14040210030e0106031202100b10020705090604060306360b1815160305010f0b12150d0b010509130c140a03060218 65
    0xe0901ea0200700c082c920a50301a514050030f601e81944603011605105a441c3e1601079041c400c040110380e542e41e142c41c45403001d00100002a1880c1030500f40101902c49041b80846846400310400000d0307540c004c03080d50500e0300c908002510405502200b03000d45925007002e041000607070100c81c141540060085080c82d1040c00c2000105207007000c00c9198000c214440303005034017403a004d21040c8ce1202a042d000b1380010400a8815601d076140c40503140c030070050801682e40a05c640641c002480f080b44130104100b200401e0041090b51000d0008101810403030aa49000ba809585460204012100301d80720300d806120501e054000750084050401c0711500007030501c2c2c00060000e240c2400501030b00d00803084242803e61188800c1e0301080002d10710301015207901210195070320340b408280c03562030040b26860031542c1010244400c480d0040e00c1601107200c4440d44d103001c140010444403d0b00d050a9411240d0101c40d00007802d1103050b60406800580b0004031701388108840641c0c0942c07090 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 983628237 1250 983626987 983626999
    0x13030c060f031b0806151902012f030f040f053313110105040b040e0a050f3702180a050d11060901050d090c0f090c21060509040f02 58
    0x10014010240301c59010f514501250035000401e5443c500721038400c80300c40c1001895800e0a8100e09001090a0f40306a040050f075900c0d01501c5ea100140070304900300304070102c2c1c8140001842c00d002d0a5500c001041e004680c11010702081c00c014801444c0b4a259400c0130440f10181d1147c064200380e5a002888040300d00c84441d903070100c415184a201303106034040c1c850700e142c0c480342d0344440644d901c02c07000150402008000c04141c13603c00101030f00203000303040b1205402d490210031900440d81d010b07000070010f142400800c0310003204001209100211074030303c00640710040c034414102041020264018600114802e0034101c60204001c1d1103034811681940c2080c0e4407024050703540c2510340041c10700000954038950509002c1c00a041c0b00714103241c01403038000f0108030709040b0b6540b040100e42c500e188940800c41e6010440d4140c0c05002154400c110700e116002d801340095400d80000902c01888040c0c4880d0300b10668020f000401010300003c07028603161410410119200303004030b03c511 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 983629487 1250 983628237 983628251
    0x9032a0d090e0a0c080408070201030605060f0a02060a0207020d02010f0509040f200a0f0c0519060b0102070506091806040b04060305060f250c021311090312190513030c060f03 77
    0x8001c5018452a018850305c0e038840a88440d1110082c550085c54140c1c1810b8840c44e00203501c1d151a8028000024001c084036116410410001d00b41400074010082d018018014070016076030f45001582e5042d424205942c000e42c250340c0c1a40e0501800d0002903005240690b26501e007400c603041140781002013109400c4850899020f10700902500c0310880c0081d1014020681d00c43c0544d00d01440302c5c1c01482107480300601103003040d08040c2200001c840054448486c0451540c041204c040689400c41d8003e08181e100404650000c130380c0600400c8103200280464072a403580d500500240d41d020b0414085203440f4182a50344040c01d0f60203290149403280010514103402401d144050003250720414042c01400d001c5076031211500b0241c4e400b4282c250302c0c214079405441000d181c0450f03450895101c243c640101802c1180d560f584180c5110708000807481800c41c071f6201a2000303503504142d40c03144c0c04480005010300d050382000340f0100c0f250a011907940d8000c1c440310322080c45a90305210f02d0b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 983630737 1250 983629487 983629501
    0x903041a070305030c1312080d0b10080a0c0c02040207080301031514072706081005041103010504050c040306020d02030114040b09070531061709032a0d090e 69
    0x1031051003809000204107202040459035008001c2c1b6041c5e41043c540f4030706035203400c0810f1480a1400c01150000000500401241d1460240d050382d240d08443d1009440c0300580050f105c5940200a52581640c5100b00c0010f18003c92002c039165401420442d19007800349840703041340e80280020f41d844040300343e2109c0b000540340035183c1450240e110034030b103589406006a5065000c04c3d00c507518054040401054000016007050040545584003502400e103514400b800706040d4014900550030040f000f0800c6403420304a81c1183c0707082c0d60000d06d82e503405541500c43d001ea900001c01042c000280d1603955803180c0c0140d03042c0d68803c1c800d00d409244184c1044112030012900039005258400040d00c6540288080c3c030340c00c2106205c0000a59682160b140c000709490303824280040c406c0024010a54451001244480c0c41c2e01140e00900f48120100e42d24051600c0184d000d03450002000c50004130301c900000d401e00410100c40c841d141c1d54401405055a03801441140c4800d40000394074 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 983631987 1250 983630737 983630789
    0x21070b10060e06030c12040501050412020f25030b010e0123031506010905040f020705010f050405060f060a0b03010e0a0c05160312090803070206160306050108010e04030e0603090304 80
    0x315038075900c80303030007081403141401901c0c0c000900c580301804084c41071100c40080802414403c1d8410800064985410b240a40c1c54402810f10042150300059861a0320440020052910070207424101d1409503203d410401110b45600b00411920141c0c00001e914902072b207146060743d002c2400d41c80882e900c1c010000480c407402c030540c0c5c0d055000310910320f0fa0019039101d10307030010b406151400c11a61201c003c502500c0d0703c5078240711800da0005040d42030102c03c0c03060511020440030148200d05154960ba03941e0ba002038500d040c10340c500c0010a0151351031420103801403040c5a1034a44075a0740790074281d05200c0480d600c406281c24030070b000184a20031802c071000305041191180c1c50304015182107403d48000109064a82d54545006010400d010003440c4038034029801040725183c05044c80a01300a103421800a240c2001c42c2400681e0f0080c0030385040d50b06002c004034450f42c13107083c1214403d0128044540142c0001b050280c0720710048000d02c02d44017840381d20204010b401004d510 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 983633093 1106 983631987 983631989
    0xa03090501050a2727111602060d020919060e03010e25090609020a17071209050313062304230a0f061706030a030f030e21070b10 57
    0x1701e81c5119000d0b06055041d04c081d12410725180300341e241c0c0e50361180e9030000c2c030a44021a941048400b00c0e815980222401042d038010701c121511100310b510424003648000034400d1890030540c2c14140a17844101030100b00400d1540760300080840c1d8420f000c082114509111040092486901c2c068040a000b54500c016901c00d00c400025190b000381e030200d18207003020300f4100045190800000c04030002190301c01301e10b6a451b40b4100c0c1c103500c11011158109003040c0004901554080241c5504c90056280a0600c20283ca4142001e024a104c0e040c001c44190425125a20010207001400000504040d00c2e080d20345c1c0000c2c7c400042504000700055480e0301c154011000e0480c515000b100a41c06041c030070119840041c50800901e42c800245601da9690304d01c00c0b0000c10440121004504000185462842c4017001590044070240d80e03007003115020031941550500c582c4 = true := by decide +kernel

theorem cover : BRFrame.Cov 983453237 983633093 := by
  have h0 := BRFrame.cov_init 983453237
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983453237 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 983453237 ≤ n) (h2 : n < 983633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
