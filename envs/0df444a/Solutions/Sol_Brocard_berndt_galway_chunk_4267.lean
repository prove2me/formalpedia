-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4267
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:03:46.256977+00:00
-- url     : https://prove2.me/submissions/ed6cd02f-0560-410d-a6af-9682c9bb3bad

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 767266187 ≤ n < 767446043 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 767267437 1250 767266187 767266207
    0x1030b15030a1d03070212060c0417030904140a0b24030a0b0a090b0a0906030b010b1602060a030c0e0a080303011413090c05150322060e2d070b040b 65
    0x1104400039507808550360652902c05103041d41320380c40ba503016803146100100b032651049003c10541c5c000c4a02c00801c9250504e00145407000d1000403405c0c0391240414004032a03079459a0251440035400988114018509140d204080300c0b0300e6013910340a10714960203013a0389508000e81c666a4280c0548131900da80d2112510380180225694046d001502104009540d10b855040038803110000c0f600d82c50003503140e081d90002c4400d5071001601c040c0c034100040048450620003004481780340c06d0035078450312591300414440d80c0700c1d100e25800640d4422004d030241e944844a40036192040f50031320419071400074007554900045c01000322828801501c040f69170348038180607904850007141171000c501d0504141c00342c50704034455140104540c501c54880d041a00044910038440d1800d1a2410760b094810702803202081502261107a54420710154840010080c020581e188104100514081607500803441c4040400040d0142e00520301444081a42c0d002d89042e1001c100940f0f48400142c9 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 767268687 1250 767267437 767267441
    0x18020304020f030d11010b010305040c0905041e05060106031d07050f060c01060e0114030a05070b0a050403061d0c0a05090f0702120a12060b0307021e01111204060b01030b15030a 78
    0x12126030501c03552415200c500e070410f08002119401c00001c02c4401e40d0300c401902996412540100072001c00c42c001c1c040e0f035029030310954209000755a0ba007009494340c424a49540c0b420302e420381da244c2c004d100400c40503600d0300440c9026181e021010150030915101141c3d981418028a4030483c08101c142b01c0c0364440710709a80a00e2038640007804007035520b55000805d9002030080c2040f50300d01c840400e81900b03000500c5100b84d903014004104843c504400d081140e0001001c2c070301000130402000002c21642e004500c43e0400345002100070703c40e6510303120719040c2c1e0b035035500c2e0180701c06a00401582c2d83e005005540114902c8040ca22691120000c030708000c003902c070070500e030040400e1501e5a40d5214244240003d0600c2081080b151038201c011900d000440e000001a8480030800e4044280308000344650f4110383c0c0040360103c400d0030400d0058010f003c100840d100c50100700b20900440c2d0140300801c0c0001e00302045101e0040c800b2900c00004403d010803036610000100300c944241d5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 767269937 1250 767268687 767268709
    0x120605043f020f0d030b031c020105060109062c030330060904080405040c03060801060602010b09180c060319060b073014130605041d011802030402 65
    0x101c140c010760018911041440d0444490040712004100c45140c001035000052021007aa500802403011044014045016081c481405501805880f0104e40940082c010703000700f428090300003140034a0000d000500c40038040d800881048241c400c0681000742030110480786441e40d1600c903110540c005c003c03070b1440c0300f08401100b9440300e243d003002a01107a031784e100300d45a851815102d110f44030700041200c10340b001c0c0c4002d00f000408006c00c105034a00b0340d100c1c52441209041c0480c0d203a42e80c0001c1400c440c1e00c2da04c2840943d441d42070503142da150100e8420390040340a0788031074440f0304040c2216a101c800f41c0f002400760500101140d07445001d0b00481d43c1401c3c212500713001107034482c8540341e415007091604590542c00e00103103100b031100d441e0314081c078604010b003801c0e90f05606440440d247c032083c0c0e4103541e409508221403000000b9200350800907000c941c5409607282d1501110803c0900c0b80780c9201c00b00c030308050051050310310142d035822481d400710310702585903122400022001500 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 767271187 1250 767269937 767269973
    0x211d0f06090f130203040201021c12051909030e10031b050f0c0304030317131a060a0905010b19020312060f120f010c0f0918051b160203061012060504 66
    0x3190800303d82c2040c50f800440c401c0e4400c2c0c5c282c0e0761129017001c1c01e0044004004c10f01d80800c401126034403010055620199100c141d600070303904034040440007807003115110082030300040c00140c010740c610b080c6070040708450304142c0b13000c002c0200a0300003184128241001c80c0304201c1c000503d14803014414054401c1c40d44854252541e41ea80d074a03001d045400c1d803000c1910304041c42000240c03a16018501a00416000440d010180014048214200600030051a444034116001080e102c1d0701c2e00c42c0601074101d04181c1a5187d64036218060b1082070740d060703102158402c0020924001000b620190040d4064505a120362400d200181c4400c1070046941501e200b5808511800c00d01504000f88206a903124034498a241d400111041a0320b0b0003440c01000c0110b90390407200707c03140d02450340065011542e00301760303900b8803901e80d00780c2c0896080c500d04040c2400300025494244034054001002c68203404080e03180c81c40d5800c03003081981000d05030755681d030002420301610300711426000c20 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 767272437 1250 767271187 767271199
    0x90109080d110705060c150619091a2709121c051008030a05091813210f0513080d120b060a021203070309211d0f06090f 53
    0xd411000b0044000c1c054400114071034080b0000e91070034041c044480c0071004c10301030070030f000c050341c0e0b201c010782070207407240d40c100200e0061514000d200ca101c1102500c840c00c00802c008840702c0e550f0000000da035001c144a2032a602e4581e1914030b40849051040800c0c0c246914241d0740d41d010300d8107040283c500580724040008148000386018140c400503034071f03500300401240d00c680580320041840f034011858140e00c100542c60106000e000a046554070080c01d2150030b1810001d030f00403160040d0b0f0401d510495106002d400c0001400511154544410303801740a1250104020105c562100c1d0300c00901200003421504402c480b120800507001000455021954500c030081c1004007404a854085203000c0c4240784910340342040322000c60055005040c1c006408103443d05590010f49150181982c0c0c003a01e50020300303904603e04062454100c0050b14081c4940040c0a02081c00000c00003203414001c414020743e140a50107001c2d032000d980c030300e40312141c01c1f0200b100e0100340e803d0303540d0041c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 767273687 1250 767272437 767272453
    0x20309060a08061c0804180b040905070812090a030b071e02071d06030604030806030f070b0a080117070b0a03020409060906150221070f080304030305220b0103060209010908 76
    0x15420680d5a409108255580c0042c0c81c02c1300c0c2070384001504180000c0c000e202c1044108000e103c0e1603c941114014614001a040c0308500018126040044200c0f441e4100740420080000140840c0055042d10484d052409400134000741c41d000c070380d010042c880c05004c8085200544114940e058004a00c0c035a4441c06502ca40c004c2c2da1410306104000d103607041c5680070002e26020104031401400050700402c2c2c2a100d640d415548010001d0401e0303054856102d1480c00342c1c904003e044010b00b24a0005130b40c03815000da0003003956070305030080484461180071030700008100040b114100d891000388241c40305100f84045001c0d00c115070055a04509100d0042041001640900222100d10400340900042c481d416a01e40d0301002c010f0306001c603601240240803003400014248588914551100e03498980d0b00d01446400079902900000d5948007006244030b1341501180c826030b4004420b0501c0203559031089940b1005000081540360042a1140c49900400c0458043c100c1001a60b40c18 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 767274937 1250 767273687 767273707
    0x60c0304060e01051f1208040b030901090b0a02130b1804050613111309110d09150501060c140304080d031a090412030501050913020111070b030a0608100b0105120702030906 76
    0x91184084103100c40c5500d04000101c4c0c1c4900c1e14606d112561040300181800d15110320040d00c0d0300f0081081c3d106540f1210281c0c005a403442d02d1174400c0601440068941e01c1c039004c010180c0c480b0360860400c20108216180c07007040d40c60f140c910100022100420240da40301b000c58032420400458003005070502d071075400014541c1001d404a0b042c0c0d5429038041503500e14018003510140c2c6608030082104125200050b20187c01003113040780a0b480003c59001003001e03420494109030300980004d04075411460800a100f00c600c050804560019418103080c0840b05403140b000c100031300709242d9141161441c1c81194040d1010a41b0f0081c5080e04501d07241c1040110045100c0c10328002a1401c030022607035160460f85180a14030803580300768075400c80c0c0e00540700304c258884042d449100380c81000030968a21002184135040d80c201c0072620f9494403004520f84540000211851811f0000d0341c006a42e02c40c0c00c1e1004014841c007201d95580301c0344000e0f819840742100803034018000050703d28038 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 767276187 1250 767274937 767274961
    0x40f05010f061a030402090105060a0309150603150c05041413090302250f0303030e01020d290411070b0601091701060302011b0b0c030703150305071412060c0304060e0105 75
    0x201e848103e00c41801c104500c82082c0305200817030300250f0004c002c00c0140b03c24100341014100c03480755400c000900c0c04054491205800c9007904460807a82c4462090040054110b031110034009070310428401d846e80c104000c1c0c414000c034040c18404644211001f00c0ca0b5a402203041c054048220041200c0b11721400d009454006103615401d4235a1040541038a09102d18110011119071003a0301800c00c0c1107035401c8001e01a4020a5480c56400348a0100c42a0b0684210240c0304030140d05101c1c05503200840303101f0510a90343d0184a18900114990850709500031110501c0c3e0000981035a6030750180181c8010031982c2000229841083d02110b00410551048040e05e000362540c40501c0032640440c0307003040a601009100070450fa0101d85501c0f50311019642000c454140814483c240c0500188090590760082e501944150350811030100b418030300c0541e007941600c6e1419000d500d201c2595403500040c0801180090002c000b805000d1160310501401d0003040082c040341c00c00d0060000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 767277437 1250 767276187 767276189
    0x715031e02030a18120e0d200306090c030a0807020103090506011806170318040605030a031808010b18070c1a0601030b1c0201141b0f07121109040f05010f06 69
    0x101c50b4a0b1100380130000e031080305000e85240d48089031101d2401c0c0460101c030b0502c0c1c908a55900542a140f0784030010340c0142005c140b01a2603101f02080d070039070300308051800c0800f0f00013502d41c1c0c2040042e09030a46011a40070340043c0c014034a5980c601d05d070b20040700180601ea0010340140a900000324500020b03440c11410001502c000b84940354a4001e480c102d50407100b90032906030710800c107d07c1400c0c181c2c801402c6c2d054000b08009a8141d80300c02103810120060402c40000d101c01d1003a009d100c00800448025000000081000300c0050009c24071845909109486030108900020101c038131440b000d1b042e440d4007881021420840c603a600c81d00c290182ca07503a01003400e02280f408103007080082141550203981071980c48403419001511005205d0f10f0b111206c0400f003021032001e055941c00c83d84000580c1c0b00070510203030031520007414094640c0103c1d0020001c0c00c0d6000c0880e00d4001d440101144c2220082c1e00f5480d81e1905011141c06d1035401000c550034002e03034082600056100070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 767278687 1250 767277437 767277451
    0xe0f0a0308030c21060f040b150c0d02010e010b030601261c080f07090909080c0a030c0c0e011a0c0c030f0c0a05040603020310022209150503030307020715031e0203 72
    0x11081031034035804c40840300701c1d6810f41059074000c0c5e0341e00e1032406821601803450080c0111408403203170f0045034101c0c1d200c0014030b403e40d44102d0002e080c159091146c500709030f45010081001100070303030010381c407401c0c1031107142d5440c804180800154522040703002c0800440310308540c0d10160003241002e210071031140000c04600a00300040b41440180da9180c4107280307035602c2210290400c0f15a0004003820b05040c0e8408805000e510700c2484208100c0c00301600a4584210000480c90310f0407555078550400058540341400400400e64501c3d207040d09074182142054460185128003480c211602d5221503052148503a99040803401044060103560180c0b0400c43c07560700d45041c00300f0f503105488001e425520040c580d402c1010345902a2000036440756503c20b0380d0b9116407a050184c2c60b030303820400c0b00380c2e620003040b00d444d0140038074980140015005503045103004040603403140200e105112089504281c2c40705c1c000d100f507001c01d444461010f10740f01207111802d801d00c02904211040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 767279937 1250 767278687 767278717
    0x5030402120613020a170703140f07030b0108210f0703260a060b1c090309050a090501060f030506060a1107230a06020c03060c0a0519030905060709060e0f0a0308030c 73
    0xc138011071b6407442840d00c160054000c0030040d01d956146a00300c00401100c0e0258061039855510b10312082c4090402903000398110303c80f55061100e42800c0c2805070889889181100f0032200c1d60203542419940700e24006034440d078884410341800c0d241104902d00c14240c0164040000111466030280d96000e0b40d01c004081180c1b03a125030b00400640710340d010300c07490031101c00e40b003800d164034a41040320200d2003072401c18181a83e9201182d403460b8540c1001d0280303a2910018001940d10006240c0400540d140601c01414801c001c560a40310b01c0e0314141c20820034614038030000f68100141401070140c80741180b10400b1216902c23810030790481000e4403800c803038000002d8441c4000746074241150b00401404113070301d400654551641c001e40040081c03200500c130407041031100c100b03c40080ba41300d84012948409130300d865424060300502c020103100b0080c03c00e000d02c0c0d500107e400c12141007501e26400c83c8810300005104035801342d00041c2803140000c2040f00c05a008005005101005024 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 767281187 1250 767279937 767279939
    0x402150c01020421061401140d060f1d0607090b37090602070e090d051b0109120e090c19031404030903051903050f070201110106060f090b160305030402120613020a 72
    0x1b040c5440100f071007105501e41c89081d1901a52606002c82800e00d03200c6c1400040114040d01c501041c0e442e4201000c1540e2407a039807241800c1030600500d58403c001c0e00d0b041d01200e0600020381e540d070040c20400080b111804005070cd80c1c5040010000744814800c40d41205014040b000524850700c6001d0100140109038000803141c0101c40c00d10300070201407000e480d00310001117049034290010104050810149030701240300e018280704407548070b8010144480c059100c507034041c1403000c10301036850040c0500d40c100001264141d0550f00041702440b00e600c0c0742d2885200440c060034842c0041d00c400d03403000c070a110415070001401d00c2200d1248003524020800e5400090180d6849200640411820010035071140340c10402400c0c2ca5105040958045c10341514840c2142d0060b048000032800d1071780368170303080c170741004e0088002e1030845031191400d034404001d2010800988002028810040081421075940384441d4420095400071941145090261801d81c0e072044031082c0d004080c4424 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 767282437 1250 767281187 767281211
    0xc090d03120e1614121b031e010204030b070c11132c060106082e170c0f0a03050a0602130b0706092306191b020c0f0102060402150c0102042106 63
    0x51703412120000034001c440303030032103289001c540383e501c5843c1e250040145440c1103082e100c0c029100c90b000034000584a03030175458500680c041c080c2c410000c2c0001c0c3c114000c0050805080e48004c41d5040d01d40ca007512a1250b08030001d0014040104036040300304d803078141ca2103600c50f02e0442d1a07400c80c0845042e40da9074141038459000c07e0341e03010b031101844120313001d030001404d180d0003c020f00340340b203504c1740c0360745140000307440c03048001a00041d0407045c0000c00c280740c90400820200011104aa11285076a880c940d40c1c07044082c00810303240d0081034040b00e100c82005040010f15000c40d0250360b4041c01e181500c01000004000c40d110030034401824400d52468100c14030f0801d080008102a88a00d03d40100c80034200c844000b5003501c0d1004090404a890028400240280c0050080c460f01e82e040081095000801c81c2c11540403904100160707889295542d01d901d0b0030956580e80f003a290714590302a00c06d50700840c030683c810002000c0c100720922001340c11540a41001c01011400e94 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 767283687 1250 767282437 767282449
    0xe030c2a0d150b010e0907030c0f210f090204140403030f180308040615080c031e07060c0305040e011d1e06012604050a0302060c090d03120e1614 64
    0x402a103981d02c0400380015801542d8440312100380c050400c1e1083c1d10032400010001c41c001c0345c040703001a450b43c484041c0c10b81c20a2140a40c5451410001c1070025410392184900c02100b05412001c0e440d08042103a185555010000e035640140007030100031030f0f603004500381170340c10b480c11000246450803041d140c036002d1181c00d900d10b13424204260700b403e86440840314150080c1c800c1c0c0e004c5a07a046000d1400e1041d500c40030041000401030004036440d5400c0506140c203524140c2d20716100704c1c201c402e41da40089114402e480701410011211000f500f41101c484c0a107800c042181c020000001c2449280c0c020352a030b0b581d43e4010601c95941d22541c500704405000040e0510080803400170481660003206039007030503681d4480001c400fa035058401010010b043d1401ea8040d00b102040e0001d05070f060000691001d01c6641e80c6140140c0880814016407004070013504000441041020203c1c040d00b040e172190203004200c500f0300c254480c510341d004599108089101c1400070300106241054 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 767284937 1250 767283687 767283709
    0x20304030503120c13140f060315040e070306050a15170a0201080a0f1a0118030f020d0311010c0f02010608070513022212020405060d02130e030c2a 65
    0x11801460034a0490407145480030782c00ba21310b20000d40103121420074407051080303041c001e2214207a00d4403080b0004040c0081464074041c9980078007070410400c4490b02a16101e58031011040e40c0010354022400039541c10074100c0c1d00010500f40c10103040c000f181c42941c102d840100c103600c06011079255035480e410083c000c0c482540785250440c41c050740156010700da407070b6808400020003080705502e000748401101d689010042041d02e5841d803500b101c0d40e018442405846500280c0440a425911000800401d101009101e240d43d00070b8003082600c42c141203840100000028031002c0c1c802100680340c2c07074518007104c006610380180000d8607500051060122039001c0c044003250468000303401d000e54000c0d032401c04803004011546102c4240c03e9410700c01440208010444020288100400d4030009400140310720310540700c0401581e900c0900303c0c2020b180440c0010300159106001d821401190350384c0c0f9544c0903005e02152032011150b10129000d8062021143d0071002000f084048007031 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 767286187 1250 767284937 767284943
    0x60702100815060723030c0f0105100501080f040b0c0d020c0109120305070e0d021c03020706090905041e1b06020f01110c1c0905033f0306060a0c02030a0f03020d02030403 75
    0x24132031700c0905110401041100c41c0310740310540f0700c0d09168a90241c03400c5110700420100703039940c4040040d080396078034811014140901e07001d42c141c180300944503031841c406880642102015404231b100c0351a11030858241100801040d5180e05101c41554000e0607002d2040d10004090030341407031007a02ca413148910510701c40d100c0450f640d1741d10041c80405140403130102d801079005507035203051702131a000e422000313481307079004080f06d80c24144001c040c0b003000d602440c505410003041c04006261703518140568444c0074078000342c140882c103180243c03009440c5010310707409110704003007002e81e4045840002040070740024440f640c0c2d480324482c071905c40e001c40a000b80d0000000c41e404000440b030206022001d5260a0710f00585690020b4108008859011003144030540030022208040405062825101008440000403c180f01a25110003000a40719078070001da0740391068081c40a120111380c001d421a1615810303807403c00901c080300403050340584104440e00b02c3e03c1e8400421101940e034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 767287437 1250 767286187 767286203
    0x5180304060c081c0e1c050a0c020103021308030315060c0d080c120901151e0b0d060305100207021c030c080f09090405010b01030e0106050607110607021008150607 72
    0x4a0080102c581405002048410610400000511885030182d001020100c0307403000407985c10300300c40ca80c900764001c188480b1500600011a845503000300a9910b00303020b40c00d01e071100703144510040b0300921407400782c066241d00003000894140300010145118a000c181c1244200441d20308000d03007030050416200d9194840d10501c41190311880081e60001000105d00b8100840e45481480311b103411a0720302926075442c452400b50866210817031000700400401000c284001c514001006c81e42d41c01108901580040c00a50300c0d14141e000100940d005825a400e50303030301c40d2a19019500c41306003a840f808104100708801280c400c00e0040c0c1c1030307240d1104e500c055216079800040c0d401c80200f041c40c000c8144070105054035103000b070511817032140b400060420700300310000d01107501080780c2c0440360b80341010600c000e46619088484490704032494aa0780b018003400205d0b44d10400700b0094100c0c0000f18403610550700001c04c0f601500c0c01101d043c03501480c00702400351900407123001904000c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 767288687 1250 767287437 767287439
    0x2070507080c012f151602070e0705120916030b18011104170106240f08060a06110705061309180f1e05030c0f01060b131e0f030c06020105180304 64
    0x85801c11140080030520b00f17403502c09442040c0000f10701d600316281448031954280d080c29640c0d05001d0103000e0015051f0000b190301380110b00070014014000384c640a203507090081428801304114000e600e05080002c0c02c40716869241c002008002a25140c00d10781c2001c02c0c2a1704040c1c18003484141800700c00e03141303040915081e01743c509040c09180100d15550307109030201d10200c9030f404e0410802c4089110201d00c0f8800040286500e002000745402c1040881c244116680e075100500110b03000c929040e1132803034086803054185621603000c0c960103500090540e904440c654030b014200c0b0001401000b00c50b64403c07403100501d00c0d00340024541400b070041e284c0003810518810f64803003100300c882880d05502d662070030b01c1c640c80039a10300c44a81c040104181c15400034007404000d02640c1404034140401c803112205a4081801400400440b240c030810b01c0d41880c0e03803a44001c101690100e800b46990f0308210b00164000d000c3c120055090600103018600706051080d400e000c050b0056240c0303 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 767289937 1250 767288687 767288747
    0x3131110031d280611031003050606030c0121020d020a0918050705031803121f090905100c141804050703051312031107050f07060206040f12090902070507080c01 71
    0xf03a0070b0b00d03800711259541c50081c41341040042000d5480340b01400c55a1007401d0450034554a00080200307071a1090b408020042c81076648424802d03c454507100d04152140c04907803804cc0039000e030003000185184040395101c0303901c3c1e00c00e0144c03003190441000c01c0112900000f0f00c0066400817155800807034010000311e044161488814449503804006032402c3c060420b0b6061441101580c2c0203840c60704100100c2d03211031000b03032920000c1c1100c8200704041c200c0c03a0342d0729480f00d41c2c95100c01d008541c1c1d11140f0020078002e44240c20901d0103440301c0c44d0390310b04000000000c17040e404496405645050000341c62a8000c6c0b003100e00840542440100d4421182d44040d1280c2905480e002090341b00d060210804600c2c10180c01c44e0b61003100541122803021280501d400000d51040301113610040510020405402c42e42c8440388d0031240080480d8000700041c1e60f5022140d105502e11440010704500f800700c0402d00c4c0050396598010b031000792b8000d100444078221901c10a80780d2600c500c00350100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 767291187 1250 767289937 767290003
    0x2040207060b0a08120a0f030207150f0501120c14030a02090103030f0801090614040902040e01020d09110f09070c05010b060309031c05060a091a041113050d0803131110031d 76
    0x5035403ca0b140242c50400ad90b03560190074004491200e4a00e0b4485c52800701c06c02e0680200381c0509213500f41c44c0816146a11840c0103d040f80c071440082c00280d02203481c090b01c080c0454070200c0d401504120b500d5a49150040409203030800c2c09001900304000070a07c0d0a83c0c0c02050102c40e0aa811542084401400c1000404001d10120382c0103644054a038204c440a0024000320740d4441d20000e40000982840e03a104c440c0c03249000d2240d07941c5d188034a004c0d540c04c03103425007004103403a0074411503038985030880c010840c0d501500d500c014080b040107040c18000008001d1500e840c0c0310f004d4003401882e003040542d01d0036290305521459010080c041203e803540050142c00300340d2052403960710030354040741c1261004043c0249626001402441070140c180201c0c0090400740d82440c0766043d242c035000c0c0a4040507242c203110701c2d13054851340c041c4990a41c001440d404018000074416446580140040c0380442d41c4c00070070a561000c41c6e00007034000c6003c100c1d40d44403401a4000094448200f56 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 767292437 1250 767291187 767291207
    0x524100e0a0603060e16080a08160f050307141527101a090106091a0a020a170408010e031c0c0504180906050f04020d03030c03020702040207060b0a08120a 68
    0xd207855036410700001081d654010003d5083c05040941007480d034165680001e610584c001c1e461950141d44c1d900d0024140c0e2040f1080d41c002900010814000ca1610341611551300701c2c00380840c4004282001031003844a404225030752044111032034920110740440483e041150300800034068606d140d001c10301d605002c1d21107424000140c820760040560700804403094486802c180e42203c20000480c1c0c14961550f078098801c038107203a070f030051401880c2c00c0001041f400601c0b040c0e40201e501a20f06000b00324400541e503110801c01c12040035045070310216041841105003541c28960079100c0c24002100312104040117800311940d9230188808540034060300442c00d810000100000900c40951071590303010848440f0b00483e245000c0c0c203180081da10054544010500c1c0b1600340401a80c0700998400345613454100460b010001c0c19094001b801407190180d0040d000054080403c00b00703500c00d85190302c0454448441d0b0f81c440300110b58500b070135560b20454800c03c11600900c4c03402800920 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 767293687 1250 767292437 767292451
    0x140906070c0b060d060e0303041b080a110d0f060b090a1122031a190c050702010f05090604170106060807020709090f020d080a20030a08041e0524100e 66
    0x19603180485e0385200498a10b40d03c06407240c0c0003c42403208000e600035016a089080d80c00048403d810445081c1c0c03200406c0400501c2c00c11a45905107440d2501011440360641005d440c40200207641003840240c140404c031a40300344640d100003102403102e03101e2040c020002c23100b09810003108501d50385a15140301c1006440008241c0c000000a00c80c40c0c03030311005c60368020500712500742000c2c54442e1502054981c10070340d04002406400a51043c103550f101c0303809113026005c1d1511201e060b140380c860039a10a402080c005400301c0c411580843c01641d2082380e500030000d40c1d80d02c0c18111104c5009440260040e00f007a4420440c80c0c045030005101c450003449041d100140c03907400241d5165060300c0c100c640b03400c040341c400c1c51036400c0107070240c1441130496007180301c0c02610506a103e00c100c440309800e000a20b00400c0a10031040307040d994016040881120058050620ba640c50344003c2001c203849070111540d105202608004074065584d10f5101c1d10391504080907031590704c0c0024804 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 767294937 1250 767293687 767293699
    0xc18050105160c08030a0305010f050105030a0203150a060201060302180403080402150904020a03090b16090611010f020c010207020a0f03020f210a20030303010e150102120409140906070c0b06 84
    0x580d02040140700315000130900c1200440c0c0e02c03d0303200d1014081d80d10503071080b0346d9210240130400c01641c1000460754080002200160382c1d59400c0c0b071907044000010940e58001c851208045556501540a1402c0d24000c84241c403c94150741d07040d5140000c100c07002000500f0070702c00700c2c0050505581201c2c45100404529060411401c0410226040109d49000003a15405003d052000651400707400c03840080d00c803803480c0a000405000166903100c2d000c00c0000c01001008045401e61150601c000c403100107541e115500c01c1e46a0103500007890aa1098060590004511038091007410450b6405400c01c82c0c0a411031080101c00581840c0d800355540500130806281c030018003c4401143c0b081c0b401c142c150404001c0207401203038208565001c0da10402c010f00848011001880d8400040a80a040848071000407400d026050720840310040d00441c0c003280050446d0880d000c0242c01107540c260681d90080d8a95449070103585203c04521880015408900100c1200398807580281c00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 767296187 1250 767294937 767294977
    0x607020d0f050307030e0a14090402271617071e1218050c0418020d080f0c010f0c030b010807030f0b03030c060103061b0206011404090b0c030a0c18050105 68
    0x40500f5035218403411030004503e03803034901651521078600e2003e03050325030000d40c10341e000c140842e620b800003a001034401c000c1f54050901403062140c0004d5040f1a082541c881814081080700d072038481c4022000225075860481c80c03200307030701600b424807603030b25036450290703035008200c0d20300c02c5c0700500700f40404010041415440244c140d02800000b1400c4a40c0c031031101405050003410701e488a840c050cc070b60b00304aa2081c01c01980800464000d404842d0300d2801162890800c0c55407191311440c2404041c007160382c1991060640c000c030410400200c00380650602d2240440032110f1410a05012034107110125004502c6a80904c0521815540014400c56900002032558010a01c40308071a0301001c014400c0207154001e10100441c000f4000d20400312020700039444040500031015981403048d881540c503504d64204200c101d40003d456145414480700c028801d900484089a00030b042013400c11b003d920603002e000e9203000c10809034103e0340c1014011160780d440b00100d072509050002e0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 767297437 1250 767296187 767296193
    0xc0402070302100b03030a05040e060d021009080115030c03062019021207082b06030c0303020f150604020703090503030a0c15020a020d0503041b1e080106050607020d0f 74
    0x1004000300390107030300106403001080720044292520203101c1c1d03010360010b00280f1503868004042d074054552983c0d0304251941d40b100400c3c8208500840658132420601160580300c0d000b40300c100c29520305400078402040701c045d07415481d0300e0902c80203000b80b000078070810114284d9407110b28600141410000c0c00c003a00c00b414003582e0071890b059215099440101410103404102800304070b10001c865a05140c0c158440d603c00340510000c00c0d01c601000150883e0702002e44490452039190144104030b5280c0380d080a0841080070300044026101c0c442c0c0380d803981d03074000580700b002d07040303501c2d05035442d50b502c4c400d20010350010799044040c84a903075000f00d420340d0140003801d0040d00b196618000c0324854108480100c4040710380800c0540f04100a00c1c2059000c1161a034144450504070f55980303c0b4604442001040f0384070f80903a2031314034004603010368140e46207859510301c21006a42c40f034132220b83c1c0e401c848c09031003000da201100700085401820700080102046014a1a5105d010f1243e1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 767298687 1250 767297437 767297441
    0xe030604060606020705041506080903130308090f120d0f05071401051b071a07091206140a0b0a0519150302190c050a03210e010b1216060f020c04 64
    0x30310226200c98440905200b910b5040005000400040340d080c440b01a525100c0c840840080c02078400b0001c0b007000280c180c000c200111000300007101e0f21006c07440d58074200b40f049a0092880c03244100d054511000803407409030387c07071003070a4002d001910541c0445901660503200c0020078406002c801e006010209000d829425040d100c040d001040510384804500c0c00308036a40f284a0300800306100d4a00490489620110b0060201d031100e2810789640c4425501000242d21002c0098030b111846020000c1a400268140c0811480d504e40c0340c441424040649550f01d020320b4216030403800030445842c00d103d406c010986034198031920540c0380c90072921956421a14400400d8000982071580600d9010103030080ca40c5141110b42d01c0e090790b880c0c613129103076624041e0420650f210385202a45050a045040c044800c0c0104041303501e37552404e0203401400301d411f1280c61078150304400b4440109402e010008241c014041203424400242e600d401201408402c5116205030074066842e14 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 767299937 1250 767298687 767298691
    0x106080d0302040504180c031e2a050604050d080904020912060108070506031e07030e011a1f050f0a0302130b220b0306101205010e040b1e070e010e0306 67
    0x81d40d0142c2d8541c101014041514280c030040b0f0000ca100c2c50881004c2003120450200b502e504c052030b014840c040d078030968a039074840c0720003400b00c0000300071101024001000112107a038207001290101b039078179010800c03940194450143c200348072150450014210000a000f0584010001400c2a1035800458804c1c09021003540c400c0d03100c03134018810084100460700080008881c8035180d45001140c008440305890f045074179194044001c108043e0080e000714074081100c400801a03c0424920b00e00014601c1308054002c1c016a40340341807044110920b41d02050407a1250351500140e40c0b4002f1140d44181000410160309002c100b0402e060901040010158500b0854403900d00042c0e0282903003401e0582c009055030044200300c940e8004c1c1c26a603020004680c400d000503005c002c140d40345040c01d41c3d042d51952900c0f0010070840c0b40803d40ea8043c42c001c2c10007241035507803034107603506581ca240d80e020172407912000080d042d07900c1078880100c54003041c500030f5511000140800e14041301 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 767301187 1250 767299937 767299963
    0xf0f02120714060901050c18031009120f050403051c09090c030204090e060601320c0a0c050118090f06170c01020d1b060203090129040b091e0603010608 67
    0x40702d6620244a00410071aa002840319000300094200108401540e00c0707950211120b2240e140369001159400348040000400d000c00d09010580480c6401141e4840ba01074078000725078841214020030b403140050780c0c01d40c2ea1200c010580c02c103000101886e200668100f240411a0300c0801280b442068002c1d09200c010f00d403009a1aa03040200181c02e032119040011515400041001582e0f87d02251400407010f00f56616046140a02c1d0180c0840c1d0101c1c0660f81d4411001905030103203130740040c0c44c4c00042c1c0039a50300d9109503128001161405035001440c00d807140104400d0000d1001a4007240d0f01800c010030005015507511640300a0720f42d030400780d8002d50081c0d50680415601884105105c4800f0b00d07064030302c01d2803408555450390001001404555020000480100c000d500080b0f0303249200c0c100060300d60461000d009440345450049000c0c07820805c4000580c204100b955015001d08841d0156a4409501c0341920f00310081c600707a4159200d50380005c5030314007409840b4405071 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 767302437 1250 767301187 767301203
    0xf0c01021b03040312260603281b080d050f070212010b04060f08150a230103050d23070f170408160323120f180a03030f0f021207 57
    0x850750800f0071728252000440c2c0280660700402550118001482d0400881c45918034519501e44e000400c0c900301d90b000c178907191640317661141e0101d10f00070504011030b18450b4020400000c805100302282504511598510b0b60080754050f854600401c0500315030258180341c0c1d400c00c40160001402c00c11003c070861036995645800c4042810640581000341c00c4008861500c030b85494215996400c5050341141c007042d0354004902c0740442600f04989410400b0061020b07000b02c000051f00c0290300307202c1220144038406d00100390310700510450340d01074008003108120f500c01341500d03840741d40700c000c3c1200c0b402612803001001810b0400c0024200c458813506c503465a040000f4a807416a9840101015500c0d003001040040c86002d03d0411020b001d11080c50010386000d202c919208041c5c9810180810204041c0c0c40c400107000600520981e061046803907078422b40511103040c5240c000a000074405d00210300d205400b585105100a6551049804090984805118030f801c80320040318200c07 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 767303687 1250 767302437 767302439
    0xd0e071e030f380a060e070302180d060c1b110906130c121d0a0204180501090b070e040c0e090907090e0a0203010e0645010504021509060f0c01021b0304 67
    0x1c051001001e901c881114805c00400b410150707450840340008125404254001403c0c8050410625425088640c0605101122803440c5050b1020744018800000001d29400c07109018400e0030707074145d80c503e400070700d5000311140b0784003882000c4000428050f007003003181d1138525403882d881c4560350303003400b10f0340d0342c401d4121080d2441404c2d03540300250600343c801f01c84800105041d004c55905801d80e0304480009030345c8240d0102801c040c2d04054090030079403900c0010014049404402881002943c0d184a00d0601401c00c11080300c1c038048100c0d0000b00111580380c0340d0b05004400c6a00101403100300c0c2d100558031078150701582c0960003403114980051a01108504090091805a105103005454a40b03040d54041c1c0c1c1e500d00b8a540c0b01142c0e0042e020b191520100360000d000510306590924001110310040280a448141c4c3c0c100d000c3c0036081e0b10300503c04803000a0310120400107168510b4403085455014480e0003980c50520195400c00c620501440561030744844802142c0141d0380340c0e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 767304937 1250 767303687 767303783
    0x206190f1103040f0e07030b090c041a190c0501200d0c2a0804151e0e060909091e060907061b0201050a030f020d0e071e030f 55
    0x1180d0803010284907030b07006000a100c2130140650b031038151540035900e2243c5a4071440200c0c040c0c20902c0302039400034000c0050201084080d402002038440f20700714040e00300000081050a441090716a100410b0300c4505010441d00c98030500c041503000310004904400d6051821040814030541c0401070300c00025281da07056481d0003440501189400d00300c090412803e5000e94901c0c0e01c18003400505070394507003142004032890aa5015181728100f2503c206400f140192030395003202c8041e40040030880358210401e100b001810620000138148a042c28070031403e0005089000c4d0405507103026601c00ba044a00c05050040502e04212001b460305040c401e0b030340c2d82032160b260016001c1010b00c02d101d60030211200c0d40d241380b0f994281f034440e9648103030f07450440081881c92140c40f0124000240e048465010307400c0124010a0320040c0c03400560f4604e03066151a82100307481404030764604e01040032452243d0190f042500440010101d01c610001c400c500d20285030124503034038500d000d80190 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 767306187 1250 767304937 767304947
    0x91505030a0c120f0b1c020906100203070515011404050c16050a02040f02220503120705150a0608010c180308070c0e1e070810090b01030b0d0f2d020108040206190f 72
    0x43c41141c1d501080c054000c6e1713004184001f10082001e80228440c162041c0540e201f00111058140c1090980c1d511091001c5501856903003882429020401c403401f017042d0745441e00c146401b580035520324526181880600c29241c1418500964a03401207042e03500240c0c032103000b40c1040301816240144c1e182e00a03200f0100c502c08030a010f108200d0800000d00158a0002d091210f0007486c3d00c40945600b124900185480c555950710301014281c0000e20007266540c2c1c01c103c2c1550030007402407110b40030070b8500f100c2414804c050a259030105110800118410000810102d40651040c03400640c6802480d582413800745e403040458449014010a52694504429040305062034201010f041c07a00d0002c003844458010040b960f030359502d495803940e00a031b01c020a00a009080d200140380c49080c4801c813212011025541c072190010007800802480514101030700b141c482d80f030740e2903013150011510300704018022600319208101c1c40055540d50f4040c00340d2509140d40b2101c102a41c42d0005003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 767307437 1250 767306187 767306209
    0x30f0d0e04150806042907031119020703051e030711011701170105160e19080d05120603060123040f0516140f121302090103080a091505030a0c120f0b 66
    0x48101d01b550995100b04c00341201e03402c1616481c010600c0e86906400d00428482c40900754000101c10303510283c440e8000c60900120703070240c1d05968036540101c4203032644608541e64519190410811480058160300107905008410f1400c800da049090304032400c0070000381c0000c103c03e10040c101191044e000d005007036211103501c200844520099030007a0101000501052003001065545004002210b4803607000384515412a4440707104800d014106521281e2a03d03281540b520000e91607040c0000c425040320b2490340001c24034801808103400e4130030280c005030b521984500c8150131642c2c840c003415024648009202c003200304034010182801039180701c0c00d00001c0050104270180000c00040c0e5168803102110400c00380c1d0340c08090b18040c822598003e6005540900100602c8400c60103044d40031600d460303442016031105060340640c1c01c94200306002640400c00550003c101d900a854a0b000a0901e0900d010180c800c41050701c40e80380001a5140e41c910113403ca524001002070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 767308687 1250 767307437 767307473
    0x60e1320010e040b040b04020307030e0c120601030f1b0303120e0a17070602040512031e0403052a030a031e030509030307030b150703030c0e030f0d0e0415080604 71
    0x9201411035400107005140d8440459100d96660810340b500740d141d50b0040e00f0501d0f0028000c640d2850310078006401006c07038186018051150001849072030621404601900d03002c603000700003581c40c0d6525240300c00500c03070044031320700d0b441e103c0024110b0403466000040d40c401d45501102410001c1c00380111602c801240b4050341c404551300300400e14001a4603004107034203400c41d03545c401d14200750300684225400940c101d000e0703214011403050040040c20b224082944211401034003614184e0080c002e81c08058444c5d00080c0c1182d4001c0002e440c101d039a4500040d04d000074086030b1001a0500301155000d4010900007403a14041480c22151615207001c1c60608102604000803500c1c0d030fa00000341002c7c18542e444c3d4a50000d40c6e1420300c100500c0c45081203070303655803c061400401030b100c8004e4060100b2400e9042103882d183c003003102400c3c0d121140c020890f03a41e0391501100c0010242800d190410713501c00300305000ca1101540100903010704e000400081c03d10b0324020101c420030381411 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 767309937 1250 767308687 767308733
    0x30306011713021908060a09060b10050306010509010c0b0711010b100c0f020a050616200d02010e010e0402070c1404060605040b07020613080a05280f06060e13 70
    0x2c0032280d020032a1260a54040e00e15200d80030b07403440700008203515a00010002d00c5810200705146140c0d402c10303040c0078030645051000c8611203007400b40d02442c800e0180c010130b1060002850350351056001d40218201450300443c02c540b40c1d1501c9400100c151181000036440c980680f6825409005200d1081c0064400d60310a440440c001000803500e000002d02520101402130f055603a04610000038003401444542d841c0540c1c401039081e00e091106c116400550003031114403031811405002c4e05144042c1c0030600303480b0326134011162801601149414856800c1c00450980c40328070140c181640f0601c1030027030580c01d0518403580802c524880c0c074481c5082c9402804803d03407000c1500c080301c10a00704603450f00e240c0d2000451034000e0b540511801c40c949480040d0f6550009548804907001e0010344070076002c0d80c1820802c24851808411000ea1000003000000300054500d00c0b0050103801e00140c010348911480000280c169545200b03080e81503120000d010f246270320f0141150f64031b000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 767311187 1250 767309937 767309941
    0x1f0c08162a1a090411120c070b071701050d210e040b09100605032802220f121401020d091b06121d150a0b2b031b050303060117 56
    0x1542d00e600c80e041c1541d00407611541880341402d07225083ea503882d11848070780c09440c070700000c8008090700000e5040d2110304040002c2413020740030781101e10382c400380901f42503e1a0b0815042c8034a074a109003088071001c141c0b4261034521200200203a41203607aa0350b442d60310001000410054411030150284a8003050051082000c4003605440407580b1a00b4010f48031303a40c0401441018042c40000840a41580d42c445110303d5190300500080781414006602c858501002e042c10000070f028440e03c01c400d07808240565820380c10007205061145e54116007000c40c0c40311032426600402090848540c2b40d044c03038020003078072021100d139a1001d40381ba00c13503035881c111005004225801c542204990b0368603029890b41c80300307501d008490b054070f812100882c0510b0480121144219044c14441c0d14103032030001d030381c0b4101100c5190000c2080300000b031080701c1c28130712504020f64082141071000701202c44412030200c0140c03000c418040da02458581c58070400250040e000c21015141200d40036003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 767312437 1250 767311187 767311229
    0x9050c09150406171905240f0c0a02070b033c0708070f0309171201050405060f0a0b03060604050a080c1516030e031f020403021f0c08162a 61
    0x181c00018000840c00994800305c0ca401d0035030400702061a5144c00b5901c140712107098842a2040b02c6c00f450248802403003d5503031445214160040380c0304100180c100301000c003c0c40c3d0904004d9600300100040c0038804002c204c159040311000c039016403a980c0d0f030b01450007840b11506030002d41d10200e80e0400424a1134144402400b401c03c840600083c907a1300e841100500402e542c54120111140c0c00c0140d544481c1007000c81c01401c244641c1b841030f070410000801604006100602d4031002410403407040c1c0c1010909412600010041d40e0840c2050000280729a40c0c0e1001800400e035000252644401040078000c5528922920074141f210400100303506145444928072025094600000401a000c0010703080015291681c07201030303200520b884c0070b071045900900c00c8920031200e401070300c01c00d464001a85e1000708084030100e80344c0020040821607040c02000000d8615008002c0c0781d20a03a80c2480c001700f10804001c0314240b401200e208485101100009420f400015040d9803240070 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 767313687 1250 767312437 767312443
    0x623030c0a05150f0906030c090405010506040605070b0a020903070b030f28021605030c010c0206060405070e01080c0c12070618020310090305040302090c07211209050c0915040617 79
    0x1c03069452000180e4660213401001901c80440d4002d29255480c2000c1200c203055400408402c0c0c402c6240c04000101441e1490071102200c0c19910b8590030800b030781d00c0e4003080c501e005141c548800c1e001c1000880c0c1c0c1d0740030300021014140400640d40c982c245007203100000c200c01003000500c0c4604214505c0c01655a510703c0309000c81401c409a503500a401d8428030200303070403000810521000c02d00100e40324040d080400c1154441d42150031598400080100741c4900f9180c100119402203044c900710f51140780c0442d803003282164040e00e81140000e500345011004402240d903044013198103400c0180c18090a400a42c9004440c400d00502c0d400081d00d401d040d08100c1101da81e9115054105406681618002c58004059018924102c415100c242d48581d00444517403034111004400070041701d00d00c02024645555910703e41d64a808207a0052a03c0300041c0d81520940782070700720070781d41d16a89a20070015001c0304111481c46406010554203a9041a0020140d402041d00c100c2400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 767314937 1250 767313687 767313709
    0x304050a0b030c130306020a0f02031c051f06050909011d0f0a060302061c0b01170402150f0c300f0310030b13020108070c02061c0623030c0a05 63
    0x9881e00380d54070380300d0301d5510b0658440c2000d1014094103640000013801065406844190160744504071a030240801c120f07107901c596030b640c003010745d01804081d84058103607101591020b034466103160030400051031100074180c96413017840007600c002580c42e4181889118980109402c24550a9550380241d00d001c00b40c00090499a0455010001803200ca92940180c8021074020b0911580c42d0f803150000500c0b000700c50941080d090924107400700717a511032055284125035081c1c0f929941e4a43e03038200210380440b0500921016402e1206a0021070410001d040007030556004103d00030201c00c402101710b00e80b02030078002c2c03104a6115001845100200e80d6540091448141e680d81c49000344002c00216400c0500140b4004040258100300c07266528040c2e8000d0700d50300483d607640d007000c803845c0c1c0507a80e00035003103181448150408460300b103c944090f806407030f01060b0a61291042c01c141d607401ca400c1030b240d041ca03a0306070f00117080510a07a0b002400c10354025070018100b50124542d1051 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 767316187 1250 767314937 767314949
    0x9060b07142e1a1f090b0408100b2209110604060c02010f090b0d0914070e040b0c07330c0e2d010f0c05100504050609070810020a0c0f050a030206090304050a 69
    0x4240c0b5030411130b8802c0c40d111020b0600aa11551120780b50441c01e0b42d10f04880b00e04d00300705868a580c408017490150b440e84400d40e900000348620241024022020f002c00c41002c8489020480d50550640da94501800c068a41540c582c88a40e407140001010303903001d04807540030302c0041c200a02101502e142120341c84c00c001d04012411101602c0c11171104405111040a28000d24501184251420b054640180e00840d0003424540340c02c0300e28046445042c10041c0801c0c81d0789854401c001c0008003000b800804003507008003d007a8100148280c4910801503000544c410404031801c0c80d00d104124203211040c0c150040a1600800d001c0c020301940c0482030602c60f01850904030107208140706c080e516408010344010782e40c2440b009000d4101582c080b42c1900580c8009200541d0019440d411600c0f15401400c03100c6403038007904029444182d1000410041d100e64801068615055072000e40c4078000600f03c0981a0070001e0812901134141840ba80007004200070b15540c0b0b62883c0c054480e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 767317437 1250 767316187 767316229
    0x17010f14150d0507060519090623070501060f081203010e040201050708210403170405070306110405060301150f02120304061a1f0909060b07142e1a 65
    0x2110800145030114050004209214000b000700d0f0b61079201c1b016056a02c0c5800b10391000080d0040140e0f130490007401340e080080c180200040700f62440d8482010224021210146004c106407501405d403800c68008411100394240c08005400041243e02c0c0700c80030703002e81d240c02c41d4105044413105002c0944042e04102022a6440a1010600c21980c8088216000b540c41e03e00551114828a1007194190003040074014044000c1d18100100c52140d50b01c10003511030903045643d84030003841d21000c00070082c40c040c0400719980e03c5080045000e450000d00850401722010801082c2661882181c0c00b15002888400c60f42c4800000303594100b40d0060001c6882842c0e0b444040091007002d800b1a846410320f1410581081100354001481d078079640c98201036a182d9071080251a4507108092584500300440c6000c1401c3e916003102060250066034081030340b1110401007603401140d0800301d00c0640481c015890281e21031741c400440c551000403a112846400034040410803005000000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 767318687 1250 767317437 767317471
    0xb130204120209180f0601050306160203030604110d020c0a0c08030c0a030e0103151202010807030c020a02060c0114070801140a05060f0a11030c010e1005041e030e040617010f14 78
    0x35a05051400103194800112242c1d0717074512000c159104028401c2c0f171300902842001c9001003048580c090f001d00c005030021440c3d5203490b000c1c000107010782140c04207041c00500051242c5441400207040c10b070601c03c0106190000c904000c900172905074001e2041c0c0d441000b036039a000c1008102c10302065054101862034501d083e0040c0d014001506440c21044078845020a001e2041160240b42d030303000ba0f80d4003086541d48001502280c0001c078411000d0713407010716000010f00c0c0030801003995003280342c0080303400005a503418103255011340e900d40120300100c005101d4000814601c502d1450101c135280915490000481e5030f80c8180340d100c4a0303a040001c1c1c1c10260b9030003091800a21031f03c850449913601012034249000700301400880070300780140c1242311183c01c590b0041074021500074840d10764005e0041e10742040c00200da0000c43c2400b42c0c1e100c602007566030760f20420005260081a0180603d404070403e821108200440d02c00140703800c0000c1440f6803581038942c2d1214a0070746a80e090 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 767319937 1250 767318687 767318701
    0x1020705181902070606090608010e0724111c0219020a0b180306040602030709090b0f040c12090302070302090906040b0414010905010e0a060e150a0f0b0409060b130204120209 77
    0x29108130384000d00301d10b091a0001a0400f200c2e402003040700d281c08001c00408001400b000d896031024820a039141e058280c41108021b900040600bd4030020f0400f90300d0f088c9a40c50f0345050260740c034805403e00a8070000c014086805100e005a03250f240320400140d110198001181007410f4000c07207142d903c01103044264040c080b550031075104030041c12034541d4602442d02001a40c003c43c2c503180010f006103000940c0b80454082c400c00080020150002c0c0c030400c1e800d12000340754111821040200046100c01e0115003445180c4e00140283d000c1c0041074154010300440410251030305c0300c0da0303001200701300100308100340c0c09030401d40c031000908a070381801298034050720800c5400b902c1d951a0103180880021300089889600d4402d07034050084c800e01003041d503141e5182c000c1011100008038001101c0c1d0003cbe0b4002064542a000001641c072401800319048406d2440300301e6240743d0703a40d20002c252800d0308815546020440b0158a4142000e000c80b000f410320300390007401100624041960 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 767321187 1250 767319937 767319941
    0x18240106050a0921060207051b060f030f040309050909060702120901020d142b060602010b03030703050c191505010504050c0d0b03012304060e06040c05240c0309010207051819 77
    0x213600d4000006640b01c02c01d5041154950102002c41c001010030b44111641c642080816600500500072205096a035500c40203281c410000780100c08200c280c440120b80740d5207185200f80a583c9c8a0020b003000c2c0b43c01d4801a240940c4084001c0415000b84050006682e001070f41360710300041807822003900c22a01600c00524000c42003288a1403080090f1904520030f50344d554580c80340000410300400342e41d0350341030b400c031a0700c0c01c0c2d11074051b01300b040514080b0780200000e04081422204992401103050b00140711406100b0049584401e9400741c521411030350700510f4003600c012101004079041468041c0e2151189015000c0300c55258140d03140599001e500c2071281121210b901220503020046074091030500b190103c60b850302e8000303a1070103280e00240640c421a17101c032417802d2890a0008005040c1c03040341c80105840368a084c001590058500900071501c007100096840d210301a001a0400e0243d410550081c0e2075500001304041100c86441d401104207400010b050300c6404001c40 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 767322437 1250 767321187 767321249
    0x3041106030402220e0d020f010b1207270c031a040605030309040e010b0901030503130b0f0405040203190f0b03071a07080f07060905060621060f18240106050a09 71
    0x200c1c60081b0070204000d282c010410441c8000c1c940020802d00e04a00c00700024200d10000804403039018240c10322000260b08540e40305c46540d600c1c50010190040c0c03038141910781c80c000ca000000e4031303015240c800714100e0a002119000440d420b01090703003420003090381c1e4003408105500c640d443d2400400560f8080d0b211000c040805040194a580c403800c1460b03907640031004000c2c0c1c040c08600005030240e140c0b002d0300c070050030851490349400d281c582040040c3d0000b13000190381100400404010a840d1b00c1400d0301803140386404551100b60408041c10400c2340d40c08020008100e8865001045903801142d030402c0c1d10080381c80c3c40b0400414415803501450f00300600d003030316140d48101440703800111184115000c5500e10400c41203e0304441c1c000c2c00c0340150001d1907108101050803080282e11b11503001c1036405105503c910070700c684500e007404c000c40401c1c018912071003010b140b242421700c4a0240c503407810a1850100d441d0001041d01c82039104d0301801903a103510303012418900c100c0b100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 767323687 1250 767322437 767322461
    0x70c08240709080f0c010206011a0901032d0e060603030f1204060905072403020a1b0620070b0903070320070f090c110c010c0b150d080304110603040222 67
    0x1407046600d42c81301555060181c903400d001d4421000001004035080750240035a4615200e0107081c41c10510054001d4101150a010300c081d600e604007045841003124000072001002000c00c041380f14907041810400090000ca001782c00030890b07400b1000f14482255080c1782400200f2409913070780d040440082c000c3d00001840c5000707084c8009004050b0100c10402e401c28503192402e50501501c05800324410701c00c0400c00300701490000b40c069a0003024010400c1c4c010540851103c03503c0700000c0f0545041c940d000d0b2140d001050703020501008440c0c9030380c480107a9000390300c3d05c040ca4130080c02040d049501907010b00501c61116000200a00c50b41009100307814104804503103400d2004090010300c0030850000780c1d81204149080e400240700b01e200e11040c0c40740d0039000300d01d4541d1b06040780010f000754146003504407500203903100d40700308440300d900480c4001c4e102e0a15142c080f01170118040c500d4400c0350305000f4880540d59210002c0101e4050340c595482070004000c108000d01022030a00e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 767324937 1250 767323687 767323693
    0x10080106080609070e060d290a1e020315060307090b0d020c0c0d260f040608010305060703020f0913090212010c090b04030b150117010b070c0824070908 67
    0x341c10800040c0b81c83c0a500b40100359143c260319054050312154046416660018060440c0004200904107249600700e9082211040d0001b02c0074440a5190560701150025030b140f90105070081142c40d00d1074141300d030301d40c15807450500c001c1034134840c011401c03060310500000001c2400c040c0614003c60040411030703203c80d220300c600c80e0480d001350018061089203001d5144c0c8115a407802042400503107912030034001201d0038480d9a042c0300c9654030024258040d08010406015040740301074002003461382d0356502d99604600d011414814060040414580140020b10328418407174290345e141c040c2601e590840801c10700416003d4135001034080d41100c051149040a0b042c11b400c42014044079880d8100b80300c0d910a803403a21441244000340c9007803800008115110707582d0f56070860885051418440d420f0100c5014090440c081c2d22804191400240142c20480c141207400000c0c600d11016090000c0b402c8803925407540c00e1940c01d142c455020000603007086c003d1400d900070300704083c21 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 767326187 1250 767324937 767324939
    0x30302070501022a1c2a05040c0f030c0306180501170714040c0504030605311e0c0b030901050a0501170309010e1302040e06030610050d030806012c0f09010f05010810080106 76
    0x2054280c1c0040391801001980780c58000314060230503008800c11940550b96036041c688000000b2002407130b20003140400c041e00e800001840e00000000640c2c040080c4000003000c2d45040511030441d05148e2040301c0c2038100550800c03910592182126003107000b90f90210740130200c090100c8083c0b0031034000a214520b00010300445541407815846001c0e141030b40076403110314841804440e50800c1e10001c02c5640c01c81c014030503080c00701072504e000d03621410442d88031a031940315600c034640045403240801ea5690341007000f1080c3c5400340c60b005040f124440740b180004d20300000d4076131003800740040c1800001110003440303850b8103080031003003a0281070031500c07151140c40d65010032001740c030800c0c428030078200480c0608007070400c18030454a000b414440100201d0f94155007110009010905010311001400b2640e19040210801048030301c1c84004260f19240800c40d80d928907580660064500c64014001c2010150703032002560001d00384100155142c101d9004284129003140c0324039402c2441c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 767327437 1250 767326187 767326223
    0xa140702190510020d020c0d02010213031106040b191706130c020a0615180e0d2a030e180705040603151d0106080901090c0905040219030302070501022a1c 68
    0x101500600e442c1c0070545403239801e40d001c03c07070a03800b41d02c00e0f109540000b4036040001844100d02011240c034060400c50030544d4403640c5078640c0d0001d084d20f05205030301501003183c03103500030302c0c00100300e94207600304405084c201c01152010100c442054842641c5a400340005402045039a000310b602450a001091400700310900d94200c2d4401c3c1805613804044004581c00c8500a01d0155504035006080084c021a011180e10140c18003d4010304107454140c6e003e0288502c14418a50207902e460000a0783da00c00d03c01140c56480c1014041c200d4801070004140e4414100d80444e000e0380f034085801360340c80e10070441540c0540d000e200946155500c0c02826540380850038101c4004e5141c54182e5a00d1042e040c0c01d86880302c0d0f0080040f05401d4052120709942d0384880d400a0000e000302e95006440d02e070a02e4044034a0300181c0c0560710100b01002590b80c100300350f46442d0214905820102406030402060003c5ea05480f80700d8036008074051088046040000c0b0310755004900c00e200e100c6c06034 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 767328687 1250 767327437 767327441
    0x3020f010b060301051023120601080106030b0307060f1701030b0601090512190609020d051c020703020102060613200306010e0406030b0406110c150a140702190510020d 74
    0x481512055007010151203003440c000301901e0496401425039462078000000440c0e0280b0317150741c0c2c1441815035017010b44090840030046d014110085d810081c0c00e0a0600c005812050164400802c250030302c02d0440f00780d04e0108409088868a0034585903c6074110400e890303020588038040ca00e849120000414010301c0035010740120000c0e2241210310707455200340034540e0204c1410a095600c0700002c990a46041e00300a14468003900c5c00048501c415800100c007039502c00c40c140d450350b0000c944500d20a031080444030340030800340000c00302940741d40d001035100d810044c5850710450001c40c0344590180d85802c0181c004041203140000021401580000c0342c1007071f61440c0c001042d009011100341824490441900d0700525100c0c019500c40d515a00541440014904412018420380d03040100030440f12030051004806041d07a440d10421540842d1201070b45000d800150000f80940c00d40c003c40c1a107402511080362280c0516981480d621b4018091007051041d84001102d0030023880503 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 767329937 1250 767328687 767328703
    0x4050d0312050f0112030f0c0c0803030403171905130c0f03050c0301020304031b0f020301156c051b030d0e0a030b0a05090708060f0604090f020d0302 66
    0x120004000980328080c00d58490f950901400e0721040b000360010010034060300716001502c0b02481c019403c0c00280e5680b07030f0803110551100030b03203a101209000030550040980d120403070034010050206d14003180c5070f070321218401426605c0300c1d40c0d6401041c0c81c000105041c5e00c14941005910030002e0b0741d001c1203680c0741183e100c169124000c0e2035000304103203010700880340110b4041ea115403030001d0340343c000400c118075420101c40702c003824115003005803000e0141140d242161031124101a24007258a210041440d92000e48240001c1d5903007840118405000120725420501c03024034102c00700310800f41000e0b90620311407000c03080c4201010094614031111690b1295082d00c15401c0c60000301d6800203420311040d541a001000310742d1440e4425801d1450411000700035101c0b0f0359990700d03042c000d80002c2e11030a180c01d4070380080040e10b80d400c0000000904a4a008101618003401e11411001001d040a48569142e00014082c8005042d407400d4070354004220580b42c0c0228a80607503109c2071 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 767331187 1250 767329937 767329967
    0x26090307150219320406021b090a050613050a0c0f031a01080603031e0a0f0930120e01110a0b0a0e01140a020901140304020f0d0804050d03 61
    0x4080c20981d01d1803014000e0301d00040c0c1049041c452450701d844299204412008000d2401c0c0414402e01c818803c804035168640101101d503560b600c6c2448802030600c004405aa4000d9050010801140c2c03502c0c4000c1740d000d0344002001805071a248002088146095510342c8224100001d11440702a02c1c0e005002482042d01d814408424060303064065030b0b01449011403000184012000075401f64a00e1036018000605032840d201a120222080c41000b14005004007000b00c1e030301041980110441450321424284918400d1400c46000030a545203043c501c1c24141d4202102e44030003091542d070118941c0b01d9400d948564454400402d502035440141c2d00191442c00d1108030a4008560043c070f42e60070008100e50740d900d02c41c075000a01040ca945481325942c0700085501c40c28a051a01c0c0036110b14200907a4500e041d0000500c00250300c070b90890f41d26002c005000059071070001400e1680c2060702d00020045160034031406c10b000d19030000350001c235080f45484c1003540c880044441c0c101 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 767332437 1250 767331187 767331203
    0x19090c09300f0506371e0603030c0b0703090b0a0f0f0606031e0b030c1e0319060c051213110402040f0906171f23040b09010e03090126090307 62
    0xd0b6001150310612401c035088243c0003500e61481e00da06070280c00480700c0018806e103d081c1800b4040e031020403150717682c0c0b080e4002907030000100e007000000c0303042d15000003191034140903240c182e032114068620007500e01c64036a0380c1c032400141001e409030414007207890180301c10003031a03980301d502a0241c585d465080e0075814a00744054144483d51042147c281d201400803c19252506c040c4062818580950749003100c000700f512607a030703408000d0b841d03a425901480d480b0540310f510700070054505e9402c84005021090011103418070034441c83c607600c501d0f89101c0284400013420300508600203852009e800500004011410803454807020040310446501042a5a9501c54191171301c0f400080310259a0020a9106d91890070210440004403a981d03000803031031402d41c501407001452110800c2180d03511802c200921680d0a6425402003c04d1300a00964402c1c403400354692183d0541c080c1800b41801c0400349541c0e102c007503440c00a81003202180710341441e40305c01d0f036280c00650044480e49 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 767333687 1250 767332437 767332471
    0x503060a0f0b22020901120603030f0f02030a0206060f0d05070b0c0f0c0a05010503100807031a0f10150203040801050103050106140a030f02150919090c09300f0506 72
    0x704180c500c01c00030b54801e6243c0b02e12091612120000396000030283e9040084850403039504a5842c031a50000318480d48981c203100e03207100e4010f01201c00c2d4649030400d54205101d8001444e8010602a5104000715649150310660100180380003044c0a0301a01a208010010070000b1101d0300901d140c00c04901201c0520340803e66165850b541c840c4910f810030507000003040b5a500910242d42c0059009440d907c046448440300e40c60300441d64016281490250509804184c22641d0980c00a84510008001c0d20300703041001040709507071242c03030b911034060720314440d00c103100b4000d1301c0292241d44002d10981d40d603400c280c0d0180c80070f801041100700340480000c50900e0030943d10703403c60342c1c0440c074401582019000c010b0210380c1d400070032180745010001103e40355918200d0105035400c0c26407202c0fa850400a0b8075048403840d801c51800d00c198444280035034000d007030044410075960140204110780d1805900007001107031000501c40010a41c2c1c0c681007080200f0790a11170500c0c440101e85d40 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 767334937 1250 767333687 767333689
    0x30c050f030f101a0d180209090c0f0d02091504061508010f0e06010f0c0819180807080a020d051501080a03030c0801151112041421250503060a0f0b 65
    0x3020300c40c1c0f113075110f00004024030007180c1a03e40042c40a1504450100510489a000301d61902c004480d060555004905500281e1414030007030a0a04405e0340c41c8480006244d0119801001c060304d4074030b81405000a56207641d407107800c0400545000258201942d46089020303042c2c4600f8014484010002000891182d0340d2408951003100165201c0354580c03c1d440701943c0003400807000340c400300d0b8200800c6040e400100c2802d42d80042a41d2841060300440511054022440d0412012a0045082000010800a00f460032030360101c880826100461802c03a03d401080c000c8110000c1c00e0000000e40c500001c6000828203011b61024040000b12060845050000b4001d4000030000d09880c010203610a01c2113620705510f0354111080310720780400320744464000d41c0c0100409803101c10540d0741401d0043d60080300c1846443e00700e0100352a5039495031964038a9401c4210440c80303140850703a44007480814070044c072000d4144c1d00c0a04284030944003030041d19082954103400c28075103101e1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 767336187 1250 767334937 767334959
    0xc060b040f110409271b030503131401031505010e1f08040507090902010c030f20070602010f05060f0613090e0102070605010608100312210b01180b030106030c050f030f10 75
    0x45d4501c842d41d0301901404556880d0320300c2c815541c049004030301045c2c01000140f02000106202c851945842c0111440c2c0482003524140100c143ca04240c140341c00c1180e50000c0c036580c0d20544d1001d08244654001101c04541408011f40705d040c00800c0490917a54991f40010703120f80998020020383d5015901c0390b4a0800343c64030458000d000400038440c06011030304c2081d564021095501d000504c148401000001010840000c40400d400c030450030041603030244030703880c00c0d0604c451051060b40303000d000007030f0007034200000e0a0040d00b002a80403540040003502e0b5005e0900c150b020000055900c83c0207000b900000003c45813145464004206140600900f920503038405a1100c081810f5a607901101e1740f0414502c002c4c03001c0c403c4c40640183e8402114000c0c10800400050b070216018001803464181804621034000d6064003400050300d00012a03055407078606011800f02c10041c801c880318072036580001c0700707658044180500403800082ea0382c01007000715030740000140c9510101c21 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 767337437 1250 767336187 767336231
    0x12060f0d1703070c0f14010e01110414040204050d06061401080402130c03110708030a150b044101030c02010e03090d020a03061112070e010c060b040f110409 69
    0x34001000100845040301c0046510039030074135120301c50385090703030fa2442070034101801150314105030300145160010074070500c07005c0d0782c104009100c4d030b01b0b00f40300461242c0300d98050346816400081080240b03440f90b1301100c00038000940418a06e2006080580c010300036030007012208811104046119807050307400e1030141d50010030b511902c900354220503000340359800c800c800781516410b183d10140b607a140030385125030080e021181d403454011034880450b500303420760041d09070341000d0134880f0052041c156015501100c500452007810102c4126910400c000c00b04055001d9040500c5100c403504203020320310308281c0301884407541a00040e400d03103d1101750b0341c0c1c450348248840e00041c906100c00400b164000f400d11101e480d1a500c540303041d660601c4094400c1100001d5811150b01c00346540b0b80e101210740b40c910f482050005c002840704103840c80181c500e80e1a000d40755202d03039495201c5150021503030001c000d030740da192803900c0c0d55400c9031180e2180c03079140401d2894140c0c0712000c004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 767338687 1250 767337437 767337443
    0x120a0e04060e06040509010b030f0c182a0f0f190806091302120d0f080c070f0605150d0507090b01140f0c031c090c17060a0b01020c0612060f0d 63
    0x10b6a50707075901d043c040104002049000150b48410601d0b81c0743d20180082070081d00307190040c00440040c1d90602280c00c030392004001d000c20307101e0708012403140e080e8694100803032140404400f034000490790009a014145003480059800280d280307258040390000d00041043c0081d0110703000301c02c0010b451440007100c0c0f00350480c1c1d0000001e02d214428101c0840c5851000340034000d9a00d100030300b9850182d0620300b26000c2240364007000106500001c01c142d100c20030b400d1052422a00303a0300c49050f400401c0005283c1d036143d6004ca218080003c054148128016045c844401c2590400640d00d14043c401c3d0400f007450089841c000354445c0111807100c88034507403000e250880c50f0043c00f205138000c852403ca240810b00176041c101e4900a00080700c40d912410100b05e00007035040071030303034115964010030700021000e003208240300c3d003c10120f030b110b01c04841c005a4201c07100f005074144140b402c2d11315400140014095500032029402038003035002500c442c901c0b5000b00050140c0380d403840c8009 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 767339937 1250 767338687 767338709
    0xa050d20011509020c1203010306060e0c070812061f0801240903020d081e090f060a020a030c110d060e0d050408031206130504060203061201231008120a0e0406 70
    0x20f2155500b55002800507480a01c11910860b02203869800070340c0080e001140e032070345c41d100c4c00c101ea0020042001c1e00400102c0b4014a410070b80c1e03484608510036496414010a000c4000854940c0c1c0d0381300e01e144a1b1311500803014000502c0c0c0c40204415000d018040b0440c244d1070301240d0748001510040f01c40315a68450300d8030b040c155002c10804a003960021201090308205c000d00d05404041c0950148081051294403026810108009010001c603114001d00003401078a241b2903002a6a4800e5a050708219074400c0c55810710f20b1014a503a140f468020404c03804040070051140c0c03164041840030420340b140e25507840070441c1c05205612448034513a00900c10440e0300b0038108899604802d0050403a80c10103e000d0721541981c0d0210703029940300ba0b001c8200901410402c071030154142c0e123600200400c0800840090a203802c00c0001001104080c00140261a903c6003000c090860102101d031400240c1c5800d1000c2e030b101c445040d0024058100030103c6003000d029240c00e9450030a40 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 767341187 1250 767339937 767339939
    0x6050105071403161a0705070b06040c1106100609051215180709090203011505031b0f0d050a020315151c0f08211302120a050d200115 59
    0x5aa03400d1440c0d42d07200c1c085020402c0408400494401c8011406120340001c2c4040780300c80701c0040c140c84c07009000e4000d1002c02c11180000a00500c540342c1c0c048011280000d110811315000c54940c02d003008006085d100d004248103180307620414203c103c070794681d90f820009840300280b15031020b2003020b180c010362080206200068402c81647c1c0e000c1440c103c21030070030500e85501490140fa44d484059201e940b41085000d5050a006850724680d00038018011145018046955000b0007400004540140c80c45003031190f692808403520528004e0000d450300ea034600381180c0b1000100130803482807041d82c1d01a0102c0000b2244240300f0007108070001100c035001c40500c8220300c400202c5854085010a007040090bd03140300404442d80507240d100c0e1140e8515089503440707100e8203824200c40c000c0030104008085d50f080c01a41c49541034030441000700303501044074948060b075031f4003c2a134050400c3d090180c550013807017581c0c44084002ca09918600c0f041c0a0f5088030704480c40d1600d040d101c924 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 767342437 1250 767341187 767341193
    0x2303040308070803131b060e090402030c120c04050103051c1706150403020909060106030b0301060807181e090b0f0402010215270714060f180d060c03020702040f0605010507 76
    0x245034849182d1034100359941c1d00d80d480526a050b861005101c010751400c090120944c4020348d181c10700c00c103813003080560803da0002541d41c1d5200cac9a8a204a01015411072602024011282000d07000342060086503185d00e402504c64a244c207240d90040c42d104201542d991207228418102c8217a104500141d1300c42d8428840282108204072440890800000005803640f60203076118007482000340c0b8265040080c002c068582030303041c03c0d100b41e040250a00100f80c020826100b1034102c1900c0050f902d2030b00c94842d007d8200d05540720010b02030314440d07000d9400a5000015113a1150030465099603480c03950041842c82920068016071182c00355040c4240044a03107600f0007c03502c0c080002c0305d84050b404a005a0401420032141c110318010020b4082c0808140d856010403585242000d09654428441d40a00800300c0b95540e540c80d21350030540c881707000c0b840c41079801a00078450f07140c036600040e0203548109004c07809246080824280411076100300020741c0c10503942d1b240b411b07140e52 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 767343687 1250 767342437 767342453
    0x1205070b0f060d170d0e0705060a0e270106030c14071203150f030507080601030b0f100e0f0f34030204090516020f030f0a0f0e0409230304030807 64
    0x3003546420003416140310700803c1d003c901c4000c013580d04c0c000c8950b4503114641c8020030f0305d0409551240755800100300344041da41d0a003e42e507444400e45800804402d941e400214044d0007089030111511001600381d050a0b520b2800300c0c181ca01903182071010701032042084543c00140041c1100402d001d01002000a0304070015065000440c40c0100b85180030342e40c4100010007591001107040e010315000c104020090040c1c900619107600580550f41c0345441d510302e402c000038021141e8581010002e06c0f4410110041c2d80034040e07161145059143c0303003544d070000f41030643c0c4110300c580c0d1920014601d51141c01c1c1420310328510584582000c1c080d4100800f0304c1c5020108601495020b000c08103030f082c2130b440b445100b01003496190b5014041c481000e03082c0030120b01004a6a001000031004020700042140c0c100203662521002c0d181d02d2510071603640030035410040d801828196038000744910f44600d0030408190480402e50282c01c0c4c20a650340b8440e501c0018000b041c203000c5030000c00da0203 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 767344937 1250 767343687 767343691
    0x3030f09010302221401080f0406090c0b04030302010501061d0102150a09020d060902150c0c01050703050f161b0602190501020c15070201060504270804050d0f1205070b0f 75
    0x60402508184d11041003090b45400384a002003000b80d441c408000f0f0b01005241c90010138400e09226220b800c041d41e0f0404031450080c405045541c94480c00c2c000c20540003422001402d11a80315500e43c1d40380d1a000b400303044207106003000203840c9200311f054040741000510012038140c00400400420300c0e031a55030000c0041c013001e07615640340e00d41005030300c0d681c1100c00c020348104000540115a841000524100c03000600d0310035505010319100e0340000500451072850909000e61201d606140880c0c0c0740c401c0c180007007294000490411b0b2400c200007041407a00c1c0c42601d01c0c415500d1664010050114544114401640401c2c1801110340076501d81c9102240640d0001d0b01d00b540103030f141890042e42c42004628034000d80208000b50b40d080c81100064201111700b4805817440203100100c2c001d15000710509401c0b1040d0100070000c0100132078004010203819120780d00720506044e07400b5004003506030381503d034038010407a00038480c80448106980c0440a20541d03100c2523140c107810140 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 767346187 1250 767344937 767344939
    0x30c120a0507111908061611101802060a030c020c010201020c030d110702030106120c08011107060f150b0406120606140c030906040e01090b01020a21090b07030801030317010503030f09 81
    0x34611305019070110061842018182110040001d4141400e505003800240500242001040786082e0f54040c0042046011841c1c0e0007004110b00240c0449010003200300c07000203501c203e00040c80a81c01c0d42603080b2800fa940315800751002c840341d20340107909034403400f244808150010000642503040070751014032220f10941c511401c007001035012a00710780300313a003221b0301005074044144c1c1041950036100c00a081420002d0001400d843c1c4c10340c0c00c601070080c0081046440b118800e0050101d80d10400c1222441c06042500b55606c1c00700b20b80c59845070141c4800900060b10a5280150078003845040b5402503482c01c00a021101000030160401c1c52820100c0c0003c10410000c0d6640e00081d1015054046010781c641d4541030841d0111348000e200a07040d9000780b06886c01003030300c000c070780c00750040a0824580c14130700410040b220070610350481c07110390300d000c240768060690080561713040e28843e8840410801840c4c039240c01e0564240301d076962662080041c40308a000340030181481c110 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 767347437 1250 767346187 767346199
    0x20118020627060f0408060c07030c0f020d1719050405150f120a0203060a15120e0109150e07050108042117091605010905090c0c0a14030c120a050711 66
    0x5503000100f05078484407504403059804034062010810500035207821848144180d480c00040d9600681907240f880409095680211491419901c03420300400b10703150311024076203c4000340079080c880f581046041f40309081050304c8000c1030b10300680880d01607500091403032217a407564040040413940042c40724a4104010700c175800c0d4602c0161b55160141000380b0002d030312407400c4000d0205241a561045285050b2582c05140d020b4010040010340130076001c0c0860f8000c0120381c840e014140c0c4070740080543c41d580003000d626402c6036100880703900d03610094a1000b60b56000450354a903050b28013400d803540000e480c00d004a85905406591621410600c10a0381142c013542e0101008a88003001030300106401000405007400c8030003c1c1a09081c120001802c000100348107000051030480d22000000e0740d000c1c03050301007100d41c040907407044031601d4803401c4440440d240d4000a24100403449600004202048524140d83d005400d40e0740399400c0001c2900c903041e9201354800d0355030300b101d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 767348687 1250 767347437 767347507
    0x70605040212031b0c090f06010e031e030403020a0b04050303040902280818120f0d0b04020f04080f0105071d0117011e0803030112120e1f0201180206 66
    0x200500181413900841183c0b0003a107507094480e2402d1a401820961040840c0c0042000441d4442055904550203103031000610450340d020900e00158404d100304a02c80300100143d00c0c9100200030001d4900c00d4444440d00c565070394507248280a00d0144640c1a0414442405000036650103080108880d21140f0100280c0c50042c540d20860303007040000044803a0204a0f85000e845107a03048009204014103550201d010341d504940154038541e60715031000501881c1e031108039048220303c6030000744115502c40310700c20814090f500510a80806002e6201c0522a109041c440c4520480039902d07000030760306050544403111100c144e803090500034561100a0004804400706000e030501c801c0c0c40c6080c0400d0495021140055440002c0c9a40100700611008540c44000d4068035401004803141501c40b01003a00c0d500c08a0f202240c00c40e00c240080000384c0350074091901e0a00823a00200100c141c4080c007007807052005c08020f90005810015107092901020a00300c0c02001302a00d01541b0b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 767349937 1250 767348687 767348719
    0x903031c0204180608010e0604120e01020f0f011e060501050d0b0d0605042910120309080607020c090105030a030c0b060312031003120203280909020c0a0605070c080706050402 77
    0x150f040c1d50303624038003aa45440c24050001c00340318401c1d0000c4c041d0001d01c4185416526040020104a25001000140030504910b64020003a01c030740b03400c0e05000d44238107005602e045802804010445013284400050718000f4824621521003500c42c107035034003454449078040d0400030b0149012040d4201d03996040c0d0710003041e42c80c460940503c0c4039a15248143d0142406c00ca08a600008403130619524501402004d8010708801002ca6019814032407050526050035651901c8692004025018010400841e02d6022510446407401100d00c040070741d8071041032640d119004100140400d102c041b140020411140290754441c40060848450900003005400d82c0d42056440481003610368000388100a61100c00c0b10b103d10040c40214100300b55568400c8000705400650661007400303584809545107d5403000d80035100c800c1c001c3d555042c00d00348840d998001d804090310301c1450718000c10b8010b441036044000c5160000412403d14846840300d6000748030240040b41d0010740c2640c01b4080b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 767351187 1250 767349937 767349959
    0x907060509180f060415050105030402090c0417060a0501091406121603030e1003142d04050f060109020a020a0318091107050d0810090504030c061e0f020903031c0204 73
    0xc41c01c3d601c81e200c0b0280c02c101c4180030650f89042c0184034140c803c1a402d0003d66070003019240d1141c0c0440c0c0d41c07280341e240d1040140f03643c4980c1c1c20080305803d003091096552840003883d41c1c00350a401c10100071030385e41c07801d025007200c006814003d046403800010814034541289036805e0385c642001079a042e1802c4140382c5110742c207650b008801281801a031440d880c500b44900c0561414542003d0040d240003a24145032054010100030140b0780e00000b003a4400c003204811540483c26000d95109800c1509040e562041c2016021080c3c2c8030b8403002042c440650300070354800ca002500189a070041d20b603410f440e51103241c4a401362120b06140d0015090002d801000c00172010a50302c00e60b071300c80901f44035003015403010100d014081020140007a926055030858200c41141030000fa15480b01e25084403541c40030b032006440d00c1c0c00c102011380c00222034020000040518181004180c03480301148050307000308a445540340d0814002c0049000102da409803064180c540c0040ca80303030b02d0b8100132030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 767352437 1250 767351187 767351191
    0x1d0f01120e010c0c061a030a0b0c0d0c050304020301150f05060a0e04060b09010816080c070201111605180f2205030406090e01050603060a1502010b030307200603090706050918 77
    0x80010400b490a000b0b015592140348891042408103003c81361a506c0429562448403600801c10040031002135040d52100080e9030701c0e030840303640038442e01c182c0000c01405500207440c164429440c0181a5803132844003143d91040b40c00d0f00801143c3e082c40d140400c4a245c11405012003031040110300d03141c007a660b511810024061540c0a5504c03400c904000520b0904020310444880300d9074080d003800c85401804482c1d1045241c050681e031008a440101e0748413a08a00c010100d1050f003540d001ca45200e5000e01041d240c09a5084d21220000b081e00e1400722820781d440c00700c101f560b034080b901c000e8400f1000d02007107080740c0c403000c40031145988092555000d03a01800024040c03201c00d200e140219816180100f10031100182141030100004045020034454800e001154602041140d4000e40140c0012a001003e5980704d120904050381081008400c01c4103010010038640441c0c07070083c060701c0c013a2207900010201c160801c07600751016400007034620b500501c81006680e4075107000e01104c0c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 767353687 1250 767352437 767352461
    0x2811030103120f0c120314041a10030f140a140f060f07021c140d06050f041527061701150501020307020613030803010b04061d0f01120e01 61
    0x554941c5142031261260403840350b40010001000000c0340e000d9801180e40c1c6900d9000603041105040c0202d0a90003481204029a2000740500400c000c4c00041e00780c1c070080d8510001f03003440070340e1082c6c0d4001903200c003800028007002020b51020b0224100305009545459490304480c0f21080b00d80758500e800310150301010107584400400c020400e42808400c4e0040182840640c06040c1800041c0d1034114548048641e12a16541d90685600c0341c0d8a58404e07241c03910845646000c220800130144c84a4016180101d0f2200c01d444a1400d00d031017919079410f801641e0b10303a454106480080b405003645040c502039030b11042d01090040f164424240108103450702c000c180d418110f106400d4031004580400c02c0c40044030300300820b0b6004400c07200280d0f811104d40750350744c8003600c0020f00743caa1600040e1600e00040008900481c0c410018415200300e0307101c070712126444803240304100105020658202c8400b003400321140d40a12030fa604100c03607a00b408901e40003803000c02401c44003081c0d05c034 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 767354937 1250 767353687 767353721
    0x10609090f050c010f0801180b100e03010b0d0f140c1c140f031828030b0c03010f0302040f020d0c020c0a0603090c0521070602010209210628 62
    0x401e0400208105a0380c0c02e140030b0034005002284428060191107052080e1420445040b004804000c0da03a8440b407901140281419144420210001c00c4e0040300d0a80d64000d41c41e0211031541440d00303a000342d80783c83d0f00000d811136011003a99080340910b40000c1c5403001e8070030305a03500ca46540b044020b0300c0c041b01d04009900c4140316030400c000c2a00840c102141c01c2e1700b000300035011004000c0121103080d22510110b9045100c41e8010407404500300112600151286420300d418100d400c14080c226402100c031902503482d4a00304442c144428450100c0d07604414908000500f811707042041400000100141003240720031071501951000819000140c100d000e008106240c120010300c05881213140420614001d507a500401d20340c00d02407035120b01829684000800040b4003028400d0040c3e03000c6d19400f0769100c3e4040d0207034000680c500d2240003e9950a840c4491382a00d4080c001c040c5002445184c41c2c1004d0f100b81d080c0c2c9100301200d508900c0c0110b165003d0a4003400001d0301401040b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 767356187 1250 767354937 767354963
    0x601030b04021804020108060402090118080618030406090312032c0105090c130911060d0e010f0c121a060703020a0b07030b0109060f12050a0203040501060803030705070803060301060909 82
    0x1000842083d024400e00c01107410400c0c440541d9103c480c82d82c0c0300205031401641d90320a00010b943ca0002c50085203036030b0004200224556070b0103c1c85c2800781004c001c441d1441201e2440d0b0039164010f42c0101d01c00950030341420000716071840c003d030007228041d05000036118030b0904008681e50501a15042820a065601900031403d210340d55010150074050400c4420345000640303c45208450b02c00900d0711140014240120010002d040c1f0200505040d55240e80b030210b00050501e4500140141d441d260301c9001c246040d004030141c0010a03503c441c41c81088800c610000e0848515490383d4152070305001003692200070040482c64002c1e0020b00045446192010a0701002402142050b080c45030030801d41c0d8020107084241e03285410a141805200d1008541403c06901c5d42412103013071406100388007161ba80110700840c094002404040d03295100540d41c0e12040c0d502c50001b510800c40c0c4404035036544061500102c0040000c00d103e5580c885c007100740c0c5c0d8142001d6580f2020140 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 767357437 1250 767356187 767356189
    0xd020711030606040626010b03030c060f0f13030f020f0f07052409010c1104062309010305060a02070206040504020304080a1d09010506160203060c040504060e0f0c0a020f0601030b0402 81
    0x414250f0041003250244441424000c10703040c03400007003050070550351070441541c0c2d0f864403e421000d0581409030403651204c900c1d07441c2581c1c03054140c170045454141400030400742d0401c2d12001c1e2182c4101c1c0012030001c1050360b030450b4510b012001500031030045400c030074070000c02400030000b900c000100804000b401e000400200a0070710200b504001c0c0c0b4803164204660803041542c403040c50900f00f4400172040b07402d01c90a50400f0b0b103072a5a1142c602940400c0d140d03145043c0340650a5100504101e2200d032800b032060a840070300010307105034440c40000300800302640040029a101801d81820030b523451b030219003039030001d980c1140c03072401c003041c022611740c2d001468092189214504003441d0007201c0c00f041e482d06040c000c05001304000500d0406c50981029504032443c0e0113801c4a1f21403a101c0340b40c42d41034002e130151a00c12130510000242030011001e41d00d0051108aa07a52070075100c00310340701074980c4a0b8203050b041d40075050703640c100340d6014400b00d8000c600032040c0510302c0c9040d03c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 767358687 1250 767357437 767357443
    0x308031603020403021023030c2511040b03101b1e0e0405070e0d050a03080a140c0a090305120c1203040b19062601050709060807050f0d02071103 64
    0x2035800340405205020800c0540e50701440c1d08103c0c0a54184884d504041c2d1784000710442614448081310040003040c41104d0f102c841c000c103000714000c10700c940002503031002481003d0b840c4801810514464036501d00741c1c5040c0d44103455042008040311840380030030700725105540400e0718091151076007901c15841c503500b0000228860f40c404e05500d4a00c3c1d12088003a01d00d403c81c6511b10b004aa41d40002560240074414062401c43c0c018252501129640351155550003040f2085000820080201782642c440d40291000c0100d00c0841c00403940d10f10040041366003149104c6000c000c103404000020510612981400c1020240c0c0c00796a40d8034002640e1900201440404080c4020002c00010a61030880d20350060480481180d150500300703c0c1c4005020300382c004040781c8a160210781150610703120f8000101842400070301087c1d5a901058404840c90300c1a000072415120028100c640309a005021710284552440e04103895002c8040c02ca07000500111442046030401c0b40c2146010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 767359937 1250 767358687 767358721
    0xa1b0e0f0108040f0b0702030412110a0e060a0603021c0204151412130302010e100614040213032d110103150602100c020132090307050d0507030e0a030803 68
    0x2e0034129042d003410355560121000b80000544259150008506418070901c2150000c040450060000f0045800d100c8500d000c0601068450030144400040c403d0b00c515109100364070003409882d800d441d065003a0080d500c482c44503d04000410982144c1514910250010b040e0b80c400b05003800c02003d80160407041140c101c050014020700562180315803444e60f0a900403d1251568100111032906038051701b01c182e4501c1c42c9002e5036078030311004501039120340215000d4400c40d880710420442800100c1c441e018400f0000e5a03000400d101042d984440c5082140701c8080641d2010104511480030344000300044906080c030200340261396a1500581d041010b01500d0710345182e00d0100040c1d03071fa00640d89030720a00703911420304020140c000e41c0707e08600031562113906140300501d8048814048451803043c4070f5022040411407140c0000251030075954404003c1440300401c90b01a0391640180384c0c101c00300103881006281c69110600c5c440c3c0114851560540c503810114007a40c0f080f202 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 767361187 1250 767359937 767359939
    0x80a0b090a02031b01050d0504031e090503070e06130c030204140906100e030f010515030d02030a0806060d060b070b0411120307021908061317210a1b0e0f 68
    0x1c85884038001d650049184035110510038482d44240000c0e00060b0b40b280942150b0401c000d140104001c14035802944520320100aa072100c0008521070302d003920300038014060f0640542c050601070041c5090090340c243c0003407008010720891250840c3c140180c44c1036408003400030b84c001c40d0801602041e0380190400d18800c0714030300124909000403071218090500c00070300b00070740c03100c074030180d40c90500c00c002c04080d10750003c0c492031030500324461401002d820114064800e004288031118808000d82b401d54420f555000300355283c0000b00004ca401c06002011140e6803501c0020b1840e00006c0148030540c800d0080300c81501c1d0a040101c0c0c0303820290040c3c0e0140d0103545903188404400b0080700d56444d0704036007180e00c1d1844d08422000c2019130b504442e0061040c2001d21259140f80c24403600183e200d134059400d40d8030284c902ca001400342440441034400200041e0540c24201405a0fa00c890b8a0100080c0a001d0f1550882d551554804180100d03c2010030350f42c180c02c0c8003004048501c4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 767362437 1250 767361187 767361193
    0xc0307050402090306070e0609270a09150f0f020c0a060605030c010c03140c12360f0102010b15040914070503040308130b0a060e07020622020a0906080a0b09 69
    0x4030b0307100440d485d42c1c0000d01d004200003001c0742016543e624101a02d102c603a000c0c041d0940c100094003d2b61300c11841445140843c810383c40020b42d001c190f4040c610341d1a91144501802c9006140751401070308080e520140c4275521040c0c0c002d03e620680c0301422034105a100140a000c00c6424560111a10b603001240650822209524141d0b0028a24183c01741c1c03500d405080201000c82d200c141d40600340454035140100c0c3d500e94140810000600380441d009646d0a881d0b006556426030500d0500402c040859a10180c105181c64417141e100c200031011f0002140340c0340d00a00107120500700c446003a42001c0c0100d4180449110761240c1c007030300140342202507030b1420001d901910700c1c04010f000070304108403040041c070080c0600100041d0b450340314808085c50b05003151000003030306041c015084240001000103121510019070745000342184050110400e005070594402141801c2013603821405406000640c41c285200d010f0041c00c1c0c0710044d10703034042c10345850f1124420140c000b82180c1c1c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 767363687 1250 767362437 767362447
    0x51c030c03201b0303010b0301081603050a02210708061522091b08010507031404020906151210030b010614090409110d12020d02030a0c080a0306030c06020c0307050402 74
    0xd05030700b41c511800001ca0032519002d0800f5074038075054007186810280c1c000440005020368244010750705a42941041d5070340307100c607400c12a419000c54403014080c0d500c003204060250500b1000444281a001052101048040f15061500c0c0e210360044103203512040401c2a01e46a500d209050b41e0000c503217500c0900d10b4180303101c00592103d0340840002c1d58484e0010100403100b000340c05581c001555100b02240e4850070b481c0241021203030400031030704005a01502c4000301038864803480d4010141452034075044180100418075500d44140303070f842000083d541e8146d00340e4040c03081824060740c0f46c00c40c0c1186409000c2c600103034060000e012440d6030007841134030088152030741104180c9002074110042e0400c10702c01c060410b4065009071145a0701004d128020461030340320381103a0204c5124149200b001c90383e92081d403d920000803010003030840041c040200412061507607203004600507483e52a904141c15090348400003590040d20802001d050a010240003807604440071420300c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 767364937 1250 767363687 767363711
    0x1e011b05060606090301020910020a06110702100305090102221502010c1b0507090c03021210080a0204150308130e0106030504020612070c081c0e011505100507051c030c03 75
    0x40341c0103840039219000c04079070300d0f0550302c095055460302c810080212444048010020307488046550050ba03c0a0620a10300c1c41944000201e03084194080e250b00300d14880d40004a0051102170034958840d50200304600703c2034022a0390308042d1001103400c00d4001e1901000c3d8030340429440b650401d69040c22250410150070041400c29002c5c0c544020400070900c1c581941030030060303080011054606044114400c0e030503070242c00d04480125455000352629a030703100c80f000301c2e48a1614594050070a91b001418260400e014070680c1d8060106060b07103a55038a411608449065015030106034000c200040c000b91040d801028142410021802d141d000305030613100381140121004101801300e0a06403142d01082c1e20b0035017101800340c03541c1281043c0d0301c0040003401007080d11400c09410320010003040c41034480c0c01d44d40c540490035181c80d0030184244c0307201030781ca02c81c240441406540b000c60300a000d83c0c1c0d00c4180700b440588131480c2c20301000e0110f4080c80910002c0610b400720034110 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 767366187 1250 767364937 767364943
    0xf07020703031b0503031003030e01080f010603020f120a020306100315152c01090e1e0705070609050102030f090d0c03050306060c030d0b030c12030403060c0e1e011b05 74
    0xd890305840d2014810100c00590303400d0b9418100002c04c10f210010170001440401514001039a10079551080c1c1c0c11800340044070356120641d0864100780005004100c801d0007030b4000c0c880c010f156800141000101c0040943c031000031508100d540342c00200704003151400310081d030014545801c0030840244501d286074402c11041c0190005000450a80c007841405035501d07040c80551028444c0c0340b4180c10204005141e03440340000e010500500e008101002540401c600c204403500c0c03050540380e08454194150440904a4000e20100b002900301049071070080c890000d000d54005a1b032402d2004403d070403081c0050100119402441c01002002e0740564039003980b0790545080c80d2651a40300000d43c0901c01d401000880740b0001580b200d4810581e000900360501c1203040c1c038a0891042d041c45012001d0b41c081c00c0c075540082101340001607081c0e10441401026140024000303540340045110340707101040d40d5580d4401c00030803032043d61f801945002090218602c40600020b940d40c1d281d5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 767367437 1250 767366187 767366189
    0xe0103031d2805011d010210020a03020c0a0305090310050106120507020106050d0515060a0b0409020c01060306180501110f0427050711070909080d0906140c0405090f070207 76
    0x21911191460390700307065aaa044568100c414a68001003901d0742110030450002c0714800d06010030480386103280b522220303101100c060380d01a0080c2c40c00b440c0b00e0724160020360014a40406160b030030701251031400b0341008034404003880b07521401d40d120200c0701014a021440b00001000300d0038000107002c034547c0425884440b1050b1000400c550f251071310268050405500300703503004009601080b00340100003804605068481c190410281c4605050001602d558000e14440400800c0304200c0030455900616500b4502400010499100c1d40e8400940304881c4c1d040382c04060050040d0309104c028452982c040400c04419840d21020740b249001a0040d0710170903000d82025038024142d06c11204a0b1190b48030006001c002620300018098100e035892100a10707075205030003000c1002440c85c4500d01d80250400700044c01c0207060340c1d84102401166500b00c80c2c140e1a20241d24902c2c06000c070984c00303201c0c100c0183c3e0301c8030b00701405d100a204c3c000741b44c0c03d92418400180700440d900414284 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 767368687 1250 767367437 767367467
    0x1080c060a09030f2103021c060528091d010b0f010917101b17040302030304060b01020c19081b090403030207020d050a1208090609070e130b0103050303040c0e010303 73
    0x98013001c0345040181400402c107000b000c4500b410188403810303c1c2d16a0081000c180c07604201034041c5a80300c0392504480300382c0192078101a40b0b80304944100e1b50031041c44541d4102101580b00d05448031281410744081034441e0034640284281c840c1c030908203010320080b603003090720709584050781c0c3c04c00204020710900c20b5444c040d003030b4802c0e0702c1420300074019840407a484000c00c3c055200382e01106111440e002864400140300301481400d081c0d0b580d0005c070301030394040d40110f00715161511414010a443c40859041d84514038040540391034603d4031105007902e40852002880c5414407080c100f0006d403901510022592048182960b82c01000d150801d0f00f600e00140c480d04588007040c0300c40104107001d0718911a0241c40b80030044241d84100103260b85554030080c54440d10b103038541d520419181c015060700000d0342030100741e0101c0c0407513034044951091030480c650140c40c0c0d645140c0b0f003a0029580c1da00300000f003000340400d004c1524024a20884500150362660320001c04600042d1845 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 767369937 1250 767368687 767368703
    0xb0f01082d070b0f04090b09010b0a030c0e130c02010e1f05041109040c090c141819060504170309030703031b150b040e011b0509031c02030301080c060a0903 69
    0x90302020070400051001d8240c9121160742d0351445110700f190383c0c02c40c0c460002210b05044c0e0583d46030a0032011103048418041d00d590521880482c1034000d8055082c1003010803003102d100d900a42d1715203190040301d2100490004032100c802c4002400c1d50f50014502e50185c2c0302c035a00303d201880d4180700d0320b860810740310001410346440c0707000404055a0021baa900601c003205101c2400f00c808502e504440801d1020010700b03400f800b0541d00702654810792242030006101802000d40312200701000e050008041c1d80f50140074101031080c102040d0890710019401043c1130001490412400701801d050100450800c0f41c0300c0b0019946000d1800b00904001c010456212003548181d4060740055000e65140c44440030120f181006140c90014a031240382400d824120060301031044c80055904140071800b84400d00000344c0d46a1320002c04560140b0840044c490142e0107404000a42116035020b142e40f07515018955103008008182548246010000036000c240c011854104803a0f04c0510 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 767371187 1250 767369937 767370013
    0x2091f0e060711090712050702010908040308070224070201030b030f1f0603060c080f060414070309030203210f18030a0c020609150a03180f0b220b0f0108 68
    0x321800d03440d40300b107076004031004c814445038540108000441c441c0e03101040103903589081049080c2c1d40c3c00d01c00500303e20f004120500208403488028021705001501d0140440b040280300e41c0550201c1141c000680008503400c01150b9150290060201c811402001d802c040e001c80d064990f00a0580358076494543d118070001030805800c55001513401c00070800200c03550000240111200300c038500c01244001740010348500d498811906004400e482d000041e54400c10154010a00c1290940541c802440421400b000d0818020141c1c4441900c826040c10204601150505c0103401410101c0301c0c404d120f20040400420b490400c201da02d4600c0c0300490b07a00215003d03104010b10700d034100d140e601e06030650345180d50080c9501109541c0c100000d88404181408400b5052801054494206401e0001c2144600f0040d000b24440081171105045d490000c0c0000761a480b0480700e032b203080c2007008800c1603080355113070041014001070041040c4507003401580c1080d0014010854100c07a032 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 767372437 1250 767371187 767371193
    0x2040f0807140108100b0a02010203040c090e072c0c07030f0f0203030a0513060c17180c1003020c0d080f250f11030d06050418081c11030a02091f0e0607 67
    0x4009070080075031b010020380e903141d0074030300030b010350f004840942c4c02007559a800076444402e8424034028140700030140000c00d081036250304400140e0114013280f06550187c844d00000201c000c3c6009100c0015141c0d40d9400529002d045442010321072010f00a42d059806949034010048070f40c00304250100240300e0341c4443c05018202c4011784090030701072810b6002105144c010141c038510742580e050985e02c59441c07241c0900041c00910b9060402d400c000703c2c064072410b1807142d030401c003082d504025040c03034070945140380751108220399800056214014021080170940030a6085480d0340a04401810701707030039004100300040405030802c00034001c0c000d0614071403182e000c030340004541075a42c0c5a1894601e0809000d00e0b0050510440c988004402e02e25402c03205c4d8401681e00004d00760500362610781c00003240c3c009aa054007066100c150100c3e889098000651103103058003001a100d0000e00d00303001c82034610740541d980d040182070a00c00e201d0b400c180c000d00c00039402ca60059a402c030b286 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 767373687 1250 767372437 767372461
    0xb030c2d030a0203041407120303050a0b0d08040306050c040b03040809040b130b150c0c1203041d042013021803240c091c08070506040602040f0807140108 68
    0x40504101100070003031240b90b9030660001c50042d40200d080e0003141c1c544c401540c1e120012031003005c1c420401c08030a42c00003070080d004564407201d01c074000184101201e01154410129000403510200001014800c0042078400c0340d81003d00100040e04081c28600034010610015001522030400410503400a0340c442d000020500000b421401c01d40c0d00008100000c1d00f201c3c8034591040c060306112030580303801e64050750780c2040490002d186040088091100d4403100c4c100c84007140c0001c00c0003040c3c0c2c0c8292400c1900c5040055050581881c00b03042800c458240c0342c8010844082d0080f0880701951154010781c950b40150b00c00513507440c1c83c01100c2400303200b420003098050294007052001d40c56566004c40024200b0300190b0015074a203651a443c031721582c1c00311523100d140d22004a00403180c44641d1880780e44a0030015103459002e8984520b010380c00c4404403101600001c09000082d0004002e6004211000c01041c1050500c040c40455655005c400c0341040311140024400c40d60715 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 767374937 1250 767373687 767373757
    0xb070807020d0b09071a030121050a03080a0b0f220609110306013518011b020c0307080c09150a14011e0509190f06180b030c 55
    0x51444446840619000c80750f03940450ba003c0082c09015000900760303080942c1c42006416544155145a09240c40f4115180219400c88403041c229084200011020400d04100394000e444511183c036028090b078040d200225120742c040e0b14003203017410258a420050164251017920110b4038034410166000040502e0341c07042c03080781d0400c041100906441070003940100d00030307a07c50310003084503c5071480315400c198050b800714880c1c036440c10143c41075411180d0040c2c5140c06101c84207102c0c4103a1401c0d0344814003100d40a0041ea02c054200300c2d0108100c016280054003e0b00300b80d40b03400946078840a5070508240150001400502e582d484a0b0030b1608a41c00101000c200300e4913044103017480c2c407900c0e03003040c00315982c2d00c0e01440450100ca80492094a0ba6540d940750000b820248041d103100d0900a1540580c1079401040e00c801000b10b1001402e4565200058000e80c000d41c1c0100d08115032202e03121040130030920a80615a0044580c200f200a020310348000150342d00d40c84940403 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 767376187 1250 767374937 767374939
    0x6061106180f190b06040b0919090602040311190612150816060806030c1518101116060e3304170d080a090212060108060906010b0a090b07080702 64
    0x10003c801d0740c100f00340707540200100e0007403810816035541c180a200803515031512490f80240c50500050700180741503241407400030039400c0801e10410700d580d241c0a036081500700700c40110b04d008a44085041010140c905000325005981c4514500310380a0412040d03292080040c545801202183c0390080c1c1743d1030000e01d603e40446680d030550411714100e04075140200c3c40000da6103000310b44a4540002c1603440d09400400072060440346000e42d120302d174041c094055030160b82000c075441658424494a44006007921548520100e040303101d4203259242910100c0d07410f108034240605940210115002c00b401d5a5224030b407181c514080b8403003c82c03503042180c40901220820740030000351020b84200d640003203401c65a14241040242c03a070148030407440020380e10301c0014000308403c0c1c10000c001800902600640341040c4d01c0141421026040700c5425804030080c441003030003c02101c3e0040c981120241d00f1311aa4410007015101c0b00d2050145020000c25520240401d074012155404d038 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 767377437 1250 767376187 767376193
    0x1d161d010519110d0207080c0d23010501090c0531030803011514031603050c0c0f0109050607081302150c010c111c12230a0204080106061106180f 64
    0x100701c02d002060340b00d4518050344540070f980c1130901c1c0a40009a004141c40c86800a040094001410722058203200d807030564070500070b00b40c02201c20601903c8004181c0001002060940c1044e00420684403c560b0304000c2000c01c002c3c988030302d02c21000c4911400003480341c80400311111122004540d40740d400150484600000003d00302d00c1d202c2e002c0342c0c4100399840700503104021b00c044482034003044400b4401240308a10342c14441d48242c0c0007540c4004040348042c1400d0944002074a010b40c018052000d41c0e41d07412720001401001c0060944c04006d928090455152030503403170700c9004c45010020b0265141c019080c98654081c402d0f00c0141d08510700030400c0500446004005174280a00c441c0301d405280f144c00040c1d200e40128180058941e200e5180b803e001e08a054010a140d20741c000c1100c00580c02d4140f214444880070340204007504c0c0158a45c2c0c03e043d40a0f01719101039002c4403c0c07004101c01880680004603656902c100302400b955840880c40740f0003414595a0100708a640c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 767378687 1250 767377437 767377477
    0x140d0c06020a050c06030115030b130f051b0301050303040b0306040f051519060504180b0d080d0e0106030b0a02031503060c070b0a06031e030302131d161d0105 70
    0x190300180c196540c501a030100d5000b04c001c40d00380102d920082c01803010918104c80c2e4000c146010ba040107a980700007030948418503c3c1030344840101ea0700740803001000c646440600c0395000c0c03110202c1d030340c0480c0c17465a18515490400001d60780e1145116040c1c86150106c0016a00ea4a6501c040340a0207520000d202c249440d400002220901600091054442c2d500e02802101041ca0001c15940c0545405203440e0070903940120005030740303044030700850304c0318144440d580b03542000382a5181f01c0d030038a640f01c3c2c1d1071b04030000a448081281807400d0b85800002c0020030300d611900c1d500617800e8440141d0f82d403601206120402000c0c0c5206425116200034000034903161402400e1881c06455020a144c40d00344480086c6d501511016040710034a60301003103481c81100c800c0c0100782c8030b07080061034058000c3d1304035110b00d5a540b00c100c01d13a8a5180b140b07100717031441001c2588405603041c14500300148600c00390050050f60030f09030301c8899070707010f01c002c9034020011103100d05a00e6180d80190 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 767379937 1250 767378687 767378699
    0x2040506070c06021e071224051e040305031819051027020103110c0a0302030d0f090b0f0606071a0601030e1212060409060e15011202030304140d0c 65
    0x125154403900340107200b50400d0172903a07040c900c500490034511070050012180303001064458100c0c10700e410f5402d820010724410106140351031a105081d400d40010500740b03003d03103281004030760500c00095015403407020000001d030702c0310441e948180680445c0754902074030f0698600d05100d01c0c000c00b0040200309250b0003404000100781e180b101d032000f400d119440384000c14440d40802c4030031850060004200c0c080c0158041c0d04030090350310142d108142031800e40e40c036080c60410080e1040e000741c1c100254002030b0340e069009541181c40e42c5601030200031b40365941d520391504002c242801c0c1500703080100e031042e59170364100d400c0c4a400032040a0b52040900617042d80141c01d03142c090200340b030001c07070415815002c12005020b14024000360305010102400c0c505010006100ca40e0207030b0b8840c0c214001540502c1045590101c440042091401d0940d11402e80001a000380c1d055004607032202d801070782e0000c103c80994041c4504002c450001d01c020034040c01c68030038000c0200c041e0b180c004c150 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 767381187 1250 767379937 767379953
    0x210702060c0c040b0a0305030f0a0c020315010e0705030c22090c0909062403020702010201060b04120c050402040510110a0206030906070e04050c0922110d0605031912030204050607 79
    0x2a0b60000c503020840c00c4248020040140c982d44030061080d00306021254010f0310620150810851605000b8565407481c8c0c0004c2c103100320036079007002c4807000c0b000505c0710b00150580d01703078080d01c541402841c48c18900c10301036088c00351141020040c0800a130781c05460f00c40c140f142004104405003401140540f9401402c1d01804d40a1180300c00c1c42d01c4000a4008800c0d04500e656100d0780c42c80c05d08001c401c0038201c02941c01198103074155900c1e0306000842a0816000b003000381811510102c410320545040d00070040c407684041e200f070380184008d001d55034904864503960001030520141600c0309014041c00d1000c3c0c513101a501c0000841041001440810082c3c0705a000c4d544c3c3c1c3e985110000100000c407081960a10010641480000d031542800103540d00305189030300b0341c0c000c0d1005400005c1300b9188010040602c1840224561004880d6405268040c0c0f4044010308655440060605410144007002400100c1500f40041c03201c0c0c001c0c3e04950140602504155483c0414102605 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 767382437 1250 767381187 767381203
    0x6050c0901020f0604030504050d1e061b0305040302100c1b030f18060504030209070c02031e0d020705033406020a03170f060103020307180f031a0108210702060c 71
    0x2015000e40040300444a03004074104e0b1040c0d0341901c0b418102401c2000703100780d900700003c003112003001a1443c0c0401d903ca01c00c552905a10544011807980d2684104000203d041c020031010316040200b07001c0003075000b18491070400c80c0402c0c0090108904a0100c815400e911101408a8005003402050650000700601482d006444280d107449100d982a11803004920aa5000800c18882840185011a0203c0c2c000006142c2108103881c0c0740c0000b4108500880c1400c1820713440b100410b5801c206104000240c803550014002e03003480c2101003a2129011680c0c000f800c6a180e9410a042da07140012814180b01c004601491b6510342101a599000d042c400b0340c041046c0e900d46012511030351000303500c6840300c04030625841d210000150065003002e0004014004940070b46d00c20202c4261410004012419100320618594142001e800851f880b440e040010b541d8014081f42500046550b01c1c0b0780071404c2070700618800c01c0800c41d1400b80c000002e5001d00c1c0002c1d80e08650a002840003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 767383687 1250 767382437 767382439
    0x1e1205041101090e07090312050d05130203070b1206040b120709050a060509150906040b0409060b090c1204141005010803031503010c09060804020d0c0b222d0306050c09 74
    0x8443e42e448003074910481000300d92410000c2e1098106100155643d8007178090703513609050460829002014040644804440c50003803861104c0750308096103402c1181500620421080f54941541c49a05030082c031801460140200d80f1039180b04502d40707c415412507681885003d41c0c040c20786412809001d00b5003510494000c5080101c04101460200d420368016401c0b2580c4020f004c80c55800d222401d00010301d0b180c0d00a13170300c20a6000b80d496900038001032a201d045d00141c21005401040076000c40604602c020302030600803455100a07a4180507040f60f0070544200f992a05851440d01d0110b610494001c02405c0c940009260780000001c1c5005140c10b0164412481c54581071600702d8094802003400540b0121017041b00c0d5006070142a0014006400c1020b4488962180d561106140e07014004032000020030782c02000c40c80c2010640c00c403d580d405440d951421103600d414450403c124080b182140848414808070f040d40c0d4030003076034410300c00d114030715200c0c4e1800c016400c04e4030f402d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 767384937 1250 767383687 767383697
    0x80303191a01050d09170f1b030f1e0f0d0c17060901210501020c030406090e01030215030c07050703050c03160e011a1303060f0b09071e1205041101 65
    0x1410030a078040c0380c521044241a0360701c500780f00f60003d255005c0c00c01d5103415503400c0148110302c0031102c080c00007085100c01c034564a55031070021110350380c3c154001c40d5903200d01e504207100c0808084100070450b01c0c00304480b469224501d04941414a403031203070080035810050300050760741c83c41141e6046039000300c81c182c443d95580c80e181c99607120302c0c00088907a5540540c0540042c4030500b00d651403199502110700c81102c90846a0f0340309800c991248582e001603034000b041c1000707120b5000074a540940760300320004030b0951541e0b0109140380002c0c03289404800004c030028408180070016552010380210071202c9840e9641092602c800501c0d000900030f0203840b42d1910381d100c01000c10700848055074603490140c0e2030581024101110004e078403440c40410801a040b40c0740352400000514000d400014a01404500c038100b25002501d800c0d0181c10b980f4200035590782c104520400c00d074007403180e060340308807843c10403600100c0d8041c071a9a424038020600c403d106168854204440003a222 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 767386187 1250 767384937 767384951
    0x1115060420040f0e0601050a0c3203180102070b0d050c0906180f0103020906120714040806090d0c0f0209060112060303080402130203100b090a09110903010606030204050a1e08030319 80
    0x461f0070340f181d0900f480100b8401c0d018038000456600b0080b00c2c2003c072203a9410403110315142d100104180090f0000194004036084440288420380d0703c205400074002040304502c1c0104000aa006101c0180412170f920400113001560b071030115810440c00802ca1591480a48903240c04090902500d174003654030300700d0040443d4081c3c4200ca1401000030000e506080144200c068900c2c4010104030800c030603160140603c8120380c010340045c10300d0f24094007c07032520700003a918000d0030041d0341080150030f8100c10f003c00c0e044e40780c11040341d80583d01d4807100d0761039000681d1200120301140015502e0500d0020900d41d100c4211805a803080320701c0800d0602840049040e800151004401a105d0100800c40101d0450050105030750140c01381c0d461030303aa009048102c2e01c00d000300150510000440e40405e10382803203048041c20150808500702420080459600c546600070400b5020150001000005400d1440700c018042c60302100d9032480c021a00502d02c04e00140c0802c1ca4034200702f1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 767387437 1250 767386187 767386189
    0xf0301030f1406270f0a03050a0e0f060d02030601200309150325020c0303041d13030f0c051c180b070b07051b0106151115060420040f0e06 61
    0x741042c01544e9400300140d41c24004031642800c1034080002d002c80d0320416054840c4c0c200c00748024030525001751105034980f000207038054030303080601514500c2605640900d8400381d41e007100341d079400d01d4100350040e26680c3d89001690080b0000c0003c540b13039450b07800b1003410481e0010050070360040541c1c500c44030b101d500c0680c2c045404251409a501c6c403a04c81d250807284500d2519000340e00e0148100c8050b602200046404d5602503004580c00503094568003100040020610341c00560302c04083c2c3c038180054070010701c1d03c00c40300a082d0401501c40351130303000d00c40700704413003040092000c141c04103c1d440148090700c0000c0408241500e00d0a00900203401700b00d003000d48000c1904404207450641d60014220365070f512107400d01c088040d0410040c0d60007042442200040c0164900e10300300d43c14000c0014002d56402d03c6100f07038136803100c44510008103c1c105c0003030704080300b502c020840c9401e0450174618076052000600c800c034000706c0c00080469540c6841d0f01141c443d00d82106c9103440e404 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 767388687 1250 767387437 767387443
    0x30b0d1419020a0b07031202041211011106061212030f15010c03020318060408030a020607082212020f0f01051e060315090f1015060906020a060e030f0301030f14 71
    0x84800ba601c00142602004244140c01c001d003000c91103031a20904511518006004030b800641014103d4407903c40c4181c1040200359110007005000d00b881051075010b000d065995401c0140031902a100035940c10021013420400c5c09250544102c08944a2400c0705a4007500a001c407403441e14100001000d40d0254000e00100c0350990301075029518002c0400300702d802c00002d4951082d04444204000a03a2800070f00c05401c1d030040990141c589814070420050110402070310030485401914001070120100001c0e00300001e520402074a8140741c0118140c2c01e00303c0180c50a0000e0140b4014084c051380c065001c544541c0c12001c00403120034041004416041003152501e80541c40160038592118580100e5035000d0102c40441d5801405281d44a06255504000d275580e40c0e15244143d00c070580744d010220141038103140c40340600345004e10003541d40b50f0548e00500100d80e43e9124501d403d50a0013112544c5450704416940c0307581d2403901950307481d02c1c0c11082c5c8004118405041903040c0c04 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 767389937 1250 767388687 767388733
    0xd0e03030a2d0e030403020a03030806090a0b030727050906090708010603030516050106050a141f080708040620210105151b01092603190c030b0d14 65
    0x202c00d0065190722900b00c503070040c0740044500c00d8920003480004016503e58821070040c502c20760b90f0403410b080c0701c0d0501ca201900030380340050300fa0030007080d11511346000a84070f040b54030115940c40101281a1083d030310903842e00a079403401c0e060000f0007920203000140e10b07010780c80c03140417035001a07a241c0200342242c0180c000240002c0d410040455882d120494905000d0b005000004011f40d0f10380002e001c02d0107070f40c01229501e1010031241e401e85041c240640304085040004003009460900c01042c41d00001e000205006030900840e00344181c551001c100010074401c1100d07082686105001a070b0441c40c580420000d000000c0c4080490600840d8101c54003d8558a1400034091941d0903d800c90764240038031400422210072141d10174011803100c20702030140800300881240700259807045e100b102d80c092003420018003034080003880019209040f0080c0005155900c050110040e1000100c0300d0b51011018050500388900080c03040c0b180001d28040360700f0010002c060314018999 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 767391187 1250 767389937 767389991
    0x20f0414210607030b0f030d031b140d050705070803040b01030b070f021c050d050109050a060819030e04020c030703020c0102212a0d090501020105010603060b031b0d0e03030a 77
    0xc0b800316070058080e400103814160b00901c0c100d83c081581c00442e00d05103044100740000b81e00c0b01e44c212a044024410000e282c070740d0703140030b954218800340d5411151081e600c0031442140d940c4000303440d40f4450310a4880c46035020801660b45c1c02e29040852014200717000075166901e82c1030104241a000340303146c040201468011f07101aa106000b014180301002218030148081006900100c201502c034084c0a400144d40c005020b0401c0b101e840c04480154000107c940e0001359540000c0019000701032460707500d403a051403006c040c040030802038098041c041101d0711000c00d4030f804050700446c1e60803240c0c03801c1c0d007248c881d48202a1000020301d003501211b95501c10400c00b030f110400f80410b11062407500c0005800a22030305184441c580042c0c403440f080081d5040c44140181c1d03908cc040c09004284a00c0c05100d041d04150800b030309844043d0042040780705080200601208a209642c0341000591042180b10300c050b607580c3d1a0340c41210101605847d008011560b10100725040c107090382 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 767392437 1250 767391187 767391193
    0xb0c070905240f041805070603140f0a020d1407080903031306050921190e09160309050303191d0a1b0b03040f03080f0402060904020904020f041421 65
    0x152180704089404814007035940003e00d0100c140050340b41c1d4000c10403502d40035248460036500c3c1e41089030910810340c01800c109814018003021030320252000507040012401c08900355103510340000020b124140504010b03c1c10b0544280303e5403c0d80e50900c3c4102c00c142c440800642e00d0000c9a5100d200464828500c044042c0549010032110b9000350350103001e0f281200d040403640c0110700183c4500090300c502c10314001410212108400301384650140781401c00c1c40105c2821800a48000b030010700501d060840000f10b400007500ca40c00c8a601e49800c40103580d541d0605202103100c0c0030b160700d9259645d50030f150140745d160480c1151000d041001401411001901d584d40301000c0744090030356102602d090344049036031002500154065403292051020303d40e600d00e40640b442034020f00398004154880d04020140c0c8600d000c8459643c82206c00580d01e080c3e0b840000e000780258040c0c20701980001ca4007240c001c0034030f1043d90341458100e414034801d0704a4005c80201324604510a2143d070 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 767393687 1250 767392437 767392471
    0xe0601061404030209160f0309030807050d090b090105180f071403070e0702010209090114010e22051005030c24070f051c0807050403032a0206040b0c070905 69
    0x103118240703014104000030569464150707290002480d00c002507550b05800800c070088088015000074020f01c034045141801d001c1c0850648001d00b14140c014051070510800161403440030f540790380f1200340780343e0288410000b42040360015000341411541400c150007440c91041210000281801280503880020010b0501748008a80000351a4001903014840d826011075824211100c082c4181c1c1507500040c0c03104100803c20407070400690003070001c0028040c5040f4543d030300507620800024141c07540a01c030303074082d0405003a905641070390004052401091001c012100003024044403c124200d6802190304401c0080394801c90101655070444c643ca4515001444406411400e004008903002c0c82c045071181424980c4035282d156000700f070b1b64000c1400c550880c0c0100c3d00038000b8035103942450f0460350003078078005480200740c0300110030702413841c10118002c41000b505640607000740d80b241d41d41c80000280e44c004255000a074041c0100101d920302c0c0b98482c0a110303000890346c0e0300c018 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 767394937 1250 767393687 767393699
    0x2030f0d14120a0c021e03090f22050705090d0b041430040f03031e02060c220b07030c050f0615010c051204120327060810080706050301060e03010e0601 67
    0x81c0302940b04e41084d401407107060b1001c080e0510141d144090540b01842e92550301070100b00c105032034003645901c40c0c811500020f00f549184100005201002e0b2030000b8a40c880c070b030080c0c4050068071002c42d401036046644030108854800c070640a01d01c10070308200308400d200780140c1c456009085103546461440c002c00694140228900d0b2006462000d0a241c683c4802c44002c071000103030005d4008c904c5072030003090403016000c2d407070621648600c003800c0e1908010421010500c1135603c82d1120f6a602041042d010f0a40e0429400401400100c00d0303030b50030380e490041c0008100810a803000d014880c60022000d0003c01d0151040500701480a10214014015603035280380350f000307540c41d00c0b884800c1d0204400310401440507020f5803240c40600c03d0f081c500102050401c0d2214605040d501140701e0b400c20602070725405464050a0008003035603449129403514000340e100300a2403090701c500180341908200110305036a2503641c0d40300309403480d100b85401c1e40c4036003076809007a5210710010014 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 767396187 1250 767394937 767394941
    0x301050f07020c0d0c0305010204061d04060513021b0a03180609180f0f051810021c090212100902090c070c03080d15090510270c030902030f0d14120a 66
    0x44c60300c522002410035459446641c22604103030001c40200b03002924072600460304a5680350002004c860a201c846d0410000c00e10f026a0f00e441ca1600c650013041070b650b0708219400c041d00000364242203031070303a110a0900400361040c4003c1d070740400ca18400085580d40c0318440c0c0000791183d2a420b0f064000f001000074001307042c086400102c0c10b07600e800c40c442840c041c1c002c0900441c3d004450202d0b6002443d0752a080080f80214010a28410000680318408440c4621a000386865000503807229a0012403000da481c000200aa03015620340c1440342c0000342d100b441c1484c0241c881d101d09076903112201d0340601c9980d4005e418052402c40400024180c0e100030900039900c8000400da402450802c0203507103c960f04040d42d0b00b501c81c81003101180c01c2c10101c2c40242103c03000440c90200804c6510041e80b0001c6c0c5081044d615541003140c000e000c1d4000b05001d6901034202d40c040d000111100b91126a01071440c0c0c0001d09002c1d640c1c90300201e80c0f0030f030b84c0c2ca0540c070405420076488201441b00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 767397437 1250 767396187 767396209
    0x7031b06050f0928050108010f0e01260a0b0f15012c060c250b040303050906040b040e07080f31080310090b0a0b030103020402090a150207050301050f07020c 69
    0x140c059981444c00040c911214080031440740c4103080110950304200000d01461016007180da480350709104100704c01000e0700912811149500358a503884050916040e01c803090310310f08040a40701d000b02c03ca00300702d0051f6480e40329400c890250300a84c0c81e0082c030fa140712000c03010640d0000304801c0705090400d402d00480c0700b280003090706e024640d10714030b40401c495404c80010400da40d00f000240720700c00c0480100165181c030b6500015440d081c1020071045e002c1c0124003001e400c01c0408100003049450740001c81c0c01929119080c04d48a59450385c0c12070011408440000004107a0f0700070803054488001c15600a4080c9900c100b211138080c00000610540905440c041e0f880c40e1a1100c0032806d0080154082c80c081c40c0c5002c2040d050000070070545101c82103042c0900e141e0481041b00710010400e03241500e50440300940d681c0c0031640040d20a008540241c00c03840804580680b07035030f0700058011b040300d00c1a4003d01171a0764000d07400200300007c07201103000da000f50352144071f685025201d500d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 767398687 1250 767397437 767397439
    0x60f0301050f040b120f0601120b1611010f0b1002150c0906090909070314030304050a03030f0902040f05060f0108040206070201050c030f04090903200c0103050a021b07031b06050f09 80
    0x3844440390400030f00c00441c500007003082c40c2c01503a0743d90f0001b41c050110740d005d05035045060740e03881d05a5451214020004043e47c6074811082c1d2002941031081b08051007144107400248210180401e2980061811134106807280b1407190000c07004600204011102041d241c050b0745084d6070740c0d480740000e41d00610b00940c0c080b10070001c84805907102c3d05040e000e04020801002e8444c25480e244501d1350a040408000d0751044c410080081c60000300801940e62510300480c03a109502c510300003510a680c002544281820203455607181c4951025228810880388500030000766801506c000e42c05980103504000708011a202550050008020507a006405c403850a20641c0801a441d00a6048004000e4a402c500d4051590040703a000c0074841440c0c840c0d13800030901549640c1c0d0000300c501681490380b00c10000e20040b410b941602c1d000e80c40c90030216100c0580c003940c19201e40b924041220000c544200441e140040358410000355403182d11003501e00420b070b1404050f2904400842 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 767399937 1250 767398687 767398691
    0x3010603020301060914010e0f040201050711060d0906052a03061c1b09020a0f0c050f010e03030603070b0a0507031d04020408030319020a020717070305030c07080c060f0301050f04 79
    0x50b1824400c1c1e2004108180c000215000140000c0320f8003901a48502520f003903040a01c809a201c4000440d049542400e03c40d0352450945442000d0300740b400203896010710046100d080300341294200c1c0c11020310403c010002a56900906c00030750082c000c00d5500009040a500d211601c550000c5811110041040d5140700100d10b00210940c1d08104c200c52200d5007001a01164120480b16400703060034a10960404082030f60081040216201d038104100d0141044001d0003800d0101c0252103050310b00030700188090581c0282d0300c1e1700a56016009202c1c2441c00141b2121103001e50f00c00ac040c030307034400e4a40103240d14112010780c40c000d0070f4205080c000d4400342155642d0300c020001054144c0103540c5900d08032108062000920300000d560324010044c0c101196404101001650310100f140741661400e15036040c5480b21a80006000d031000080c0241d12810005070380c4100d40100c1d089400c6042e480d003d000c5940640309001180102c00d1005205510300704010140c504005000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 767401187 1250 767399937 767399939
    0x1605030c16080408010605090103030c060203060a03322118040603030801080d14090402071a01091508070612020a030905060c0a0e0f0a030206030402130c17070e1e030106 75
    0x3640340303181c1c10070022030b000c0c0d00c000b4040015490a008590041c40301710b40005407903145032000351408981e61b400a0004d40e00200140255031480c1401d0003440c2c1000c102800380c04142e404400580a140122040014501c04103c2c1c900c40010100c020381924854002010420100100560000c80c84417030001e070000d41d403a100e91503d2017100000c5000b559001a694900343d031190600901840718420001d00d045060280050141210001d520a803001039540103d401c01700070502c281c070300307100200f00682c000150041d0613409c07400b00641e08001041c01e40b03561344049035a4464501c42d82011070b000e00880f02d41d130f000d1035000d03088120503414041040d65641c0d4403e41006001c0b0b40701e540310310011510300c0c420b0342d02c69105110060309a440e1400e9004000010360b0718101488001d115681c008000790864807019600c804034a07400c2c0303041c000e595503208044d02030340000e0000c0031511001000517103aa84a0401e41e000c1e554050325440540115a0840075802c1188410075051340d2503140c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 767402437 1250 767401187 767401207
    0x30c11060c130902071a060d0204020f0c0c0612071b1223040e43030b041a1014160203010c020703030f0e130507080f0601081605030c 59
    0x40144211221081c1d03981d00e0380c07a654103545910b03a60b040a1a12841400010000303030b40d28a40342e00600c02c100d5020788a644010000d5212030700400000d411500114044102000340e801801888209805494402420605201c6d46001d444191030030201440c3c08110654015a45e0b05503c1690340c1c0c116003010a00c0d2207404d40c0d00c40450080c1c00140c04070ba10700d8071502d910f00d81c010201488000c0341d49010b14101d0070000c00d10020301214801c880064207500300d107689a42e210f0440b810801c01d004010f030710281ca8110f01c1841c101200c0840d041c443c0c0c01c01c203403900e03200b24030032028800c0b120740c0f100c008401031003852507200703408005204c1c3c072440031801c001000c0d000e840c08100d03004030951540c0e403c0c8103040c29a641d2169150030744d1301002c4140000f980010700d0035030400203403a10f0007900f10014000741c10210160030700d8900c103140000780000c6561282a8a2003078a0012002d1810344074040110340b200720483e1640002c1c8180501d200c0c00c81e1103200250b400c0307907841d0001d5082a0441c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 767403687 1250 767402437 767402443
    0x130819060b040f0c081015020d0e0a120302071a041a0703120e0f1c02071503061d1e0c03010b0d0617060105031b030613020303070605280912030c11 65
    0x2001d440072895030b05c00c00c406500c1a8015501030b103411000c00b80c80d03612a1801a50301c22000d03054406101050b0580314080d200d840e0100001c00141e41d01901c05c1d902414065220384040c01108004142074404920910842040710201c1e118501045074030484a84031501c01d4010382c84c02c07030802c00d0b080700b0f0500d42095802400606041c00015284d2a0507590340140f40403200d040c0b003100c0048801c404020030b50003145100c2202c84040c003000b00c03420410f0040717000381100e0b04180455074008800b80c44e8000c001001030302c81c01e031302d01080ca07030f803141e05030384049007030048900d011041030030401030054190705000703800403241c50100440d80b151103454818220f1820b19008005e9804a8010401843d04019142e142030300500b180803500249000b003174607210300402c1d42d0801a404400141152003c00465070f0340c58100c2000c000c4d0341071a100c6100d420603007980c4028844c06d8015200fa0040e520b12a4640480c0e00c26000c1c0a14001c0e843c00303801034660340c1044000e002c89500302d41c0a060040c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 767404937 1250 767403687 767403701
    0x90507170f01050f12070504090f080f0a0e030a0b04030f0309170c1203011212110d030606030c090503060105040b0303070807030f020d092621130819060b040f 70
    0x1030707040303000c00e604050502c0a40b4a604e140e203403050754040c0d03d46083d614080345c00029030300306640200b4501c0302c80c01d00d441c0020803850024041c0c01c00040f00412211071001510000e0907a55a042da07041c00401090f5a41c802441c7c06403482502d0301c04075001030300984040e0545510341c10049180309454440d11000403000c10b0031882440c0015620660100a000544501da02c0000b02c500750350400700c0f245060044900011304245030101d802e04414010342c0880306201c40d090896040361150741c0001c01802d210322412001c83c4c101a00003001d10b001d4200d40c01a1040900141201c2e03180204200240c081c0e030203040c0e0140000c103d100003040782e01c001481103074000c2c1c4074003608945140c40245000001e1aa0801304000c3c15028869424840c40440c8541b03110901049030804094989007442c40c001042290755401d081c038407000001100c050400080043d9007213544a41e281412038507a00003420100000b181c3c420b1142c00641c071a881482e9015025000066400329403141204880324 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 767406187 1250 767404937 767404951
    0x7171b150d02040e0609040c061412010602011b11150a02071703072c0105090a0503011802010809070522110324121b041410230a09050717 61
    0xf4184400100c4001c290340004094032142c01c0b0b80b400e6291001201c006004031000c02011241c2c042c2141d00d8041500d84154001d000030240d940e64000c0a8000d0805508a109511029440140c2c403801241c05401070617248002d8060020324001504d00305e5402414011115070178811200802d5200c00640a04c88620142075900d041544014085220700c070243c0b49400130382800001940c0104140b6081441c080c01c04540301e41e82000080c2c4c1d80b221f00d41045805600c0c01d054021004e4200103403140c864000e03210410780343c032845416601c03034062303000d0036400402c9003c0c00c0a01e166180c001d00880c0b01840b4000401034100c550b001e0340e5500540c0d40340000300b58510f0340203494030508a01080b81c1c00848200c060070600001c85030300e40c1c0030b4920389080e8001d1810000241c3c0c032244c02260304407020030640341a0786404c03d02c81c4030b406513078002c2c0361910412a5018021b0079a00720103005c0d032000102202d80340340c07400500c01e01401000f8a083c081042d41071078141e40713405144146006500c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 767407437 1250 767406187 767406191
    0x110c0603370b01090f0803040504110c0109030203091003020c0a1e050708010519020901020c1c060203130311070b04090510091a131e02031003051c0207171b150d 71
    0x1c1d145000418100d150f410150403540040006c102d884000000c0741c0480324103440229103907003402850308003801070760010b00b482d50070840c8070340405501000401442d0070403501d954031510140b10031400c81c0a917685a849580c1301c00c0c116000300c2c087e1035084142d104800c00d01c00941c08103540e402d04100144d4070600c00c60391914240171003550810312100311441d61100850400d544600001d5845040d011501e000381400000304010b81e1281c4061381c403091f0050710a41d0740341480c41c00e040c4004c04140060340000d05030424048100c4003c1062003c80e44155581c0b0f09090500c1c00c60401803a01800030240d255a5060018250200307014010410400010381600b000c4044284010b1050700c4501303910061611680e070000403100e0140c04001d205c201c03801601e995030307040000e0038440396400181403807282c90284460f03c10b80628111b210b441507401da0b40311943d14804450040041140d10405410204101c2125040e143c030204c54188010f01c1c0e1059850180407405166000c100807508441d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 767408687 1250 767407437 767407451
    0xd0b0d05160e07050705030a030506040b0301060b090a0e0702151504180611130b0904150e0a0e010903080610210e0c03030304020a03030c0f02040f0606110c060337 72
    0x4111042190f003c031450504514005003079442a4881c030483c403111080c1960b440200e09a911254410440100c1c094020015543c8036581740d07005030003030111148102c488050100d03000303004120960180806400819010324001040f207509080188020749400f030710407403500c00759130b58007840c011000e40103e4414114807500701201a0f44944001d00d03688402005143e0b1859123100d0402d0445251484554136030b5004400540541415400b43c1c102900040f0049052804000d02501a04d04c90800300320300700310350b25254240e0304010000760101e40300b000099418104185003c03072681c003a00e0404c4c04c160400d51000c8000c01c11513a07400e0f0007682d40b0700c40d4400a42c02c00038420f604108034000c5d41945055400124401c890340070003010065101411000c000c0b45007020500381c1d50040052110302d0540300d95070000c01c194422480011003007481ea00803514046103003089220b01403c454615503941020184090755040100382d5032408000031004c19800800001c2003e8103410040b65074 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 767409937 1250 767408687 767408699
    0x70e0406030c03030f091505132312010605030303060d0501020d1d0d0912030f0212190801050618060f0702092401050c0307060f020702060a08010e070e060d0b0d0516 73
    0x44007174003110a003401341011003030203010340000c1c8616100c0d040e032910381c2d5500d010040c4200030030b07501e074040c080848401c2e030102d1038034200d0408940021001d0380d00402c80d00d036040c41d1ba8265012072090300d4060b002040401c00c40d06001650141e40c0e4040c0c80054070740710001d98403100b15100030f91400700c25080401508c00c0e00a0034004000318100720301d4111507a82c2848041c148141034080005c040c002c5100004820500a02650003081000d0710f00329154522208034852035410780703003010006a036001c00440e06250500964505681d0848500c00c014400000d00c641a8881d0302e4010841106001d00401a900c80f600b03148078840d030241000001712000c614501280b021014241801018000c141010700004107640308203411100c0481c5910b04e01d600f4074020710851102941001000805006840c0c01201e168121002c2508040a80d9a44602290701210100c82d141e07002c082000107158584031a0000700c00700310000c10442051545031b840a2a00b881000f1501c0c40206070380e810042 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 767411187 1250 767409937 767409947
    0x1a191505060a2c0a15031b020a03120e100f1104090207110a0302010824090106031b02010203060105070b1b0c0d0e030606010c0605181614100512070e0406030c0303 72
    0x80a0316207000c08903c204103000241e1108240d02680740e540789a11003500045100c1c1e00500032080e19104942e2481c1c00316034000351240d11426050707010491262014043c9480b6105069280344004042d05030b41001c00040d001074659102c1c20f002c0306450300301445d50007042c10002c2008000e003582c0140d44404900c3e01c14891381e03203111b40c01c1c404c000e0b00c60100f008d070341c100d00e0403a400f58001002601100500001001800c0100d0859810101450000c5036441c0c055111318141011205074000500d01400201e0030b034032044410704d0002c0c805005c00030010b80143c1c00d1030781117544141d03681c0e8010081d00003807400760000305034205030342d00c60011486400c0e00a0511300030021300340d000d0056481c1150029000010722107000f414a684c81d00000c602c00c0481941c074050525507816141154001d030015a0020b100b406000d0440381c443e003010760b02e0700e448001090340d0300f680d0f100d9030f081004242c0d1010403064000c1110f8240180300b4550552542c8a11a04024521039081e42c1c114a0030340c01c0c0108 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 767412437 1250 767411187 767411237
    0x7171e0a06031a0c0f0d0609110c210412031211070c1e05060702040b0310060906140a090e0a060f0203070e090417160f0c031a191505060a 61
    0x15401c0740f000140001c80948000716040e02d20302c585115034801c06d01c411100146030903030003154520310f8955402109004140141400c0b003902040f038003000c0383d4402c0c041441014880c400c01c10302003000208480704a03188a0000240641402000b03243c0076003403001600d102c0c500e210405200012a40d0811100740021809411001c00d41443c041d082080f444280352107001d9244a81b1010074031804558694001104409014040e24032101120381c041021300003900400d1011b80c14800d005c120807249422400d00c5a600508011483d8646102403008001044000041e8003c030000b0704c01251190041e45a042900000140d8038a070121008010a00300c05080d407082ea128818400859003442c900b06000001c00d07196640c80500c0d881c0040d40303629481c4010001c80700305500f0020301052003402021240641c03105c500e078030444004040440c1c1c04890f07100d1a005552040d00c050621588041c1c404000d444464900c3c43d06c03200051500e4110f490b100c070004918044840c0320014640c0804 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 767413687 1250 767412437 767412473
    0x110403020d0c060923010c172208010b0d02040906060b0309070315020a0e10030605150c07080d091502150f091605060412020d060516080603030307171e0a0603 70
    0x305e00e0010803d04004084050140c150400550540607010710950310000401e10368030900c02c907520304809070043c52181040d0401041c03032041e60700002e620401030042d10181c400062078011518500c1c3d003040001c1054070001c1d59515601c860100c0c0c040700140045001d14141801051503520b5813800f168280d07147c4465240c80340c0144548096aa000340e2b0303000c2e409800300c0d4280c0e9212600c56044006094a40c0411b07404034070b41500800300c01ca2500140ba03e4401d40042e205201e4440e070785199181041c50455000806010007004903840e400c03081c140c0c4003802e1054820a04050001740018070701502c1d0401c0550b128800d000310310030100501d0110045000040e8240703450030b00000d0300c9005034481c040900c2d20340e52140c411035071907115a07000b290b408001041503090102c1000f0b10001c3c5605c1f044d000c2000c0c41c01190b038034071303001081c1c034840c408076a40c81400720300210b52012240d801070582e061065149000600c07503201178a0071841444158800208203246051415000b513490801c5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 767414937 1250 767413687 767413709
    0x150e071e1707080a2705010b04021305060d0603051b01080601020705090106140403060606090503060a0203011a07050102090301051501090b07230f0a0303021809060a0306110403020d0c0609 83
    0x1034014030000745015984a80750381407100f5144c0d02c0d805140054000d0010b000f082150110880703001c0741c004034180f170215004070020021b51442d6000e000c1248918040c01d580d00880c2c0d8000c105901e4040d0041a00b407081c0c0d81c0102d805640da40d03c092a0035285201c000101079402400d8413039591100e44071358001803d20041803454685800300707003034041c11b01501c402c1000000c0b000ca06c003201481290001c40d4404030400019540d80001440001e2502955220f030060902044d030f8032255009483c10795040507910591007013903030a020001d0f405402c0840e00c43d5028401070290350380070700c6018820f2441c0c1c0740c00301103070480c100010a041a140c000464045083c0300c60404980313048200040c42107850300b20340f05c42048070410f41c07400030783c2840043c1520510207540101036064000d400039804240c852048220b0701e03c100051201c08490080d004542210108045022900048030103491000c401d450207032240c0114940106280080d580411156820803555a1240c2c0c0f80e00201884015 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 767416187 1250 767414937 767414957
    0x41a0c030f0414010e0319030608120f090f0d0b0601020105010510020a0204050405160605040f06090806070804110607050a0b06030703020907050a090f09050a0c050309030d150e071e 80
    0x50701c040604050406011950b52020101c008802540107900240704e02d01280d803903408164000e0340c4002d1501d41200006c1c104000060150310020f40e09821024810300c0d107041c001c1441d690706254010f012006d40c841c40c1e140c00c42d49640c039810356200c01c00d8092408130385540b03001400a401c2d0360341a0f11250045620750a0303051220b80c00b04401c500558100c1d0041403d03241c0303040c468070f0326054054800f07550b04056000507810303801000410464400314002004a03070348041c02d8031284030500c00c2d04c080340c0000c0d0004031020305c904501036009120b00d1a0426558801001c0b03030707480d0803140080380d06030700012200d070901c68020303820b90b88140203d00420b00d1030704540c0402c042c1540a0801414064040b5107250031500600301b0b0b00181c81d05400c2c25030303195583c0402c500a0300c001d46045042070316000b801e44150f0322070382c00c40348101c131080011441c3c100320140c04001400b10018540b81c2000c1443d001c80c101e40e41d40d0080d4003d11407a528207118100c43c8240041814604454200340040144 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 767417437 1250 767416187 767416201
    0x20901170c12030c06150607240203070903120f0807050a030f020a020a051506061c180f1505071e020304050306070305250c140a05010c0906020d03110d0903110105041a0c03 76
    0x10844010395400b000c200540306002d0027690503440c4007021450360500100410bd2450352203800401120b002d120404c90340200d6072425980b840c4c0c0210071800003607184001482d0725006200610f0001140d190014404038442460400c80e041055040700680100013803409220040082e00c01280459100d51807605102d030026072a40702d0030300502c8070100c0b004074408162070294005032414950b00c0c55030400e00320a2524000003150848200c41d6050f048510391101d045034840c40d4420b9020b034964070707100c50240103080149814409800300f14030081101240c10340b0203012050241e1255100450581082c000926222070701044a846440060500740084c0d030b885a103540045030444820500d0305084419582803802c207180143c40d039801c0100b1904011383c410820340c215031907075080c1d0395002900f5804900382c803006005d50038440703000c0c00b0030840044180e103e00c0710300d1300ca030418980c10040a4961801e6420494003980d206034100c002c030b20a101122810390f8040403164000d45075240600c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 767418687 1250 767417437 767417449
    0x80a24030b100929060412080d050702010b0d030e030309040609020a0e01110c010e151315020c0a051201090b09100615020307031202041214010f09020901170c12030c0615 75
    0x1552489964001c1044c001502c071201160054000c510f03050200746464280408281c2c8104080d040f010314001c00608110f01c18414641c50a000410350544400b041c0c0301140c038100405078250f4180810032010304955141e01c6001c0040c8409140542c03105054000940b000001440490510002441e411200c4001140407811f080c0700b403c06e1079000c8036120100e0200070310340c8102205038600140030802090f80340001070489500c00c50490320040c110001f26240c000320381003a908003101d070078148418504100c1940c41190340b04000540c801d40d81d01d594a86190583e20002a50400e00b41029000c00ca8040e04010309014544d03415035407012000255a441800c101404000ea1a415480346e0340e0341e60101d400804202c0c3c504610b45c0340703900708034601c200080c0c2c1c0f0315020761030320402e4100c0000e1030080c01740c401e4006200952580c84d010040c801d44015114440107070181d00c043d144966101d0003050b0008000400075a00c500229940c2441c144d8050180c2c101410115052a1181d0b561 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 767419937 1250 767418687 767418731
    0xf0306060a09050c0f0a0216050a0f12050102090604030311210f070c030b01150305100b304f02011b0303230403080a24030b1009 57
    0x4003002560b944c03400300300d0304103000712101c280c005a40050f140c18000d0340080c0007404d600c11848000d00b0a0fa88104000e1808000d200b552076110b0400010040c0c0d4010000003144140100d0003d480d040354000090256070003504210b0209131080b4013885080800c020914080a141405242d00c0102e02e42107035144c0034200d2030046082001940350108248202c41000859102c121000903584883d040724100e1a801c031840f00091901c0002039100b802d80030040d049810900d041403030290000300e184414800c030390088230304c4004548003841000081d2182441401c1e07015590300c0c14118880c0203c020424038900c212000003103c2c0c80d03020440d00d100000e84520340700443c102040440d20050740c14403c1e1b00014041c201031090001c0c1895010f401c441800c44c0040079000042c0b00c4080b140b00d40e02c00a507000703800078205400258007400c40d588180001c980c2540169582404860b001040c10f03210381080350040034030000d000c00038404441e0a400781140020a1050140900ca100e043c0c1d001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 767421187 1250 767419937 767419949
    0x3050f01051011070b03150114040b16141c023d05190606020304060e0d020d020303071b1502030708070c15031a15090d060609090b060f0306060a 64
    0x2c0d480c2c80c010060f000d241000a18026070058500040c0d031030f104e0300c4c00341c1c0040f00c0140e11045070b942c5402466104004030083d501e01015002d0800313041c181c6080301038101220303140d042130000f0540000b1494182248010201803c014043e00c1080c0500c402e403983d18482e00130079588980013604000000603005039814100c41c1c8008058a54108410b881000d0300180500151800060007080d900b08584010701c0c0c4200704040c0691603076010f08036901c0c42248034940c001000a4141e4841e0314103080c1c1d00ba0890700003048211521941e400007403e540c4211000c030343c41e43c1c0b1090301d80c08400340f4100010003440000050306201c1c1c07901001940f28444d8203c004d000401c0001d0741000c201c00407001e200038095000500c8a04215441e015000b0410940d42c1d05160402e00d004646a2501000e801c20b032b0201d0f0081d841c02c02c1000341c01d0100c44900c90100300d8841c0c1d203550020488074524442e62089500400703604119080090070302c40c6002d4110041030080e04807804108041d21890071900031513103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 767422437 1250 767421187 767421199
    0xc090504020436061b020a1209030c0b030402032e2007020d020301140907090e010b0a05121c1d0f03060720030406080a1406030d110a06151503050f0105 67
    0x154540700001704245011025850060020751320707420b50000313034440c2e030300c3c4150001102039400071010341b20707900d06100c010050040e40364148040c0340b00b400a560018070150032a01182d010b40c890020a8094011461102c10207500066002950740200c0c0c00d0040e2400c0d2511483d110076030468000e00c00e0303070700c06406000721100324411074800754401c144100c90a48448040c0c00c0c400c800c00c0e20340b802e03407182445c002c0c01c140d00042c1c4040184601044c820707005114000c07461402c000d02800da9241107544145002d090901c0c1542d0951403d680b51501c103e650354550684c2c05605800e5403022184510b004840311182030210303072000aa480c0e0003c04908003040c20840d0340303088000201080307040c00420f00002c100000c00075044000306002e407080000602c40e00760210440b00b40c0c00c0d0708680c41c0790305038029045807542a00500e00030700d00701c46030001d503204501951250003e440c0340c0260412020b00a040c1006202d0460300c1510b03030301c0800d2909001d10b0502d42c2a29948040c1030041900c141 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 767423687 1250 767422437 767422541
    0x3021e01050706020315120c09040f0f120207050a08070e070302070813081507030504051f0b031f050702031e131e1401050a020619090c0905040204 65
    0x303802081514412503220700300390340d13038900200503040c092500c050741c50142c510f0582102c002940840d820080039000b5000075100d90b51510f51800c1d010403103405031081e040380484200424440d1001c9000540c8039002480d0310b81c60001071111620f50782d800b800c0340b900b01e20828860105a9051a60401220b19016840e4041d900700020030703105200c42c404200301c1441c80000d03191300c04100f074032215800740034090b061395440e00180c040d81e0045034000d04030340281400c54007018606500e038402000f50400016203c003101c0200340341a000500000c22503400e41c000e0042110300b4050030750312940314409903043c40710800b03400c001d5039a00510f0402c440004a02d4070500c01641c943c150051640c00442c13004421801049400c01c6150b004500200e00350007c1c8103150f5002c0e004071141d03c186540100005da032400c50403e40103042910032482507894a4610010943c0301004101900c8080700009250420b881080100c7e022410001c00d03507000390300051801c41844041c03c0c0e00c0000420424410 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 767424937 1250 767423687 767423689
    0x30607030c120e0712121b0503122a0d050106020723011404030609050c03071a13030503030c040906050409030f0e0d0b2409060303090d08070501023103021e 69
    0x420040d401c0721400b111216401c05c240008101c0341d03c80d64050380c40d00d2504110f02100030491075400c50700070300b03079520410800d5060403612001e19840314a6030702ca00304044101c8000740062580d00d200300c54043c008160003406601034411240100b1840c00103016070b0b440c219038003401003400d00d8106401080080f9221031640a0303800e101d4215050421a584c42d0740701e191a8008081275501036840348603121000802e800c001583c03505441400281c1072003101401c0041d03806501115001d000d00c03500000000c0001c0c01000954041d032000e50207180c403a800c0c42560340c1141c41550250b40b00e14204031056020907040440003c3d90423681c60039895042908000c140b10a5801c1701c0201088000400c20140071030b5000c40403042c1c541690200545032010082040d8420180c884c0780e81178100f0841044203240207000d100c4e82c1c0e8401d04215044c1445900e52500726081560703140c0480d448450007001c0341546244c649044480350b035078840050700316004100008000010401d1595002d1800e09035 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 767426187 1250 767424937 767424943
    0x626101a071220011103060f150403061b0309080306060a022e0c0302031b070c0b0d1401051002060712060b0d09120903080711010512090606030607030c120e 69
    0x140d402290302c0d0506600808014121400010407664081c06416108100041030086080d604440300c01107096840d08000c008584100403403442c4d010700b2080034000d4000c041ca028000550007010001002c40648036426142c00011610a04142c9401c1400e000100e40b42c0540360032079001d44140303441b52032264040e03240841c14030710040c10308640402d200c030030603c0c01d07100c062020740300106110080f1613a4083e030903400142c2d40c021820344030303244501d6090b42200c081d16078036000d070200c5c01d881955490301e02c0c616808030200c90005034503500e010801071810129280103000580302640c01c051203000080d2608005042d80080001001c08002e584c0f145402100280820554103981c48941420000003410514812540300041c503500d414914001c10520048039007022445281131107681d2002040308100d8446818003030240103102213807507000d9041d4410511030000704501c0c1002000c0510780a00200503a04241c180204034078490303400455040750303507880ca41c04144100c105003d00c0c2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 767427437 1250 767426187 767426197
    0x3040315090228080f070e040f020a0e0c030906070509061812071e090c0203160206041206090c09020a02250e0f0a0e0111040e070e06040626101a 64
    0x700904032100d400d000ca0400000690131180d4100c1215070a04c1c20b41d4040f604c0f0006440381c911401284800140070949400f8820061440105001c17106521800030b400d0501c002c1c3c0d40c110441d94040100f201c035000070000580c00c058203090003400e100009001441e0341c03048060703054040c5018001002c05442d600311a19201020368142c500954884044a941e502c040380d1901141d05c60581c00034503444a8824480c40f94607580c065440d28110140301419481e000b041283c000c002044001100c113080b20300543e0032171007800081341804242c01d00713600406e05134001000d16403040144502080d00024019030585004080b10b800700d03802080360782d081407903a212902000d06641006220315a1708001c1c0e1240f46440000c0020032550f000f07240c00c031741001041d034444400c1048280300050b800d003900ca90010342c52900005840b07191010518075000781e889440031480c1540300040c9010290b401030b02e90598104d1607006850198031750120a08240701301000c40000f085082140c01c210002c9407 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 767428687 1250 767427437 767427469
    0x51504020d0b0a060513140307030b09100903030b1008070806100219140d0813061e1401080d050f030105042705060f061f030c0c02090408030f09030403150902 70
    0x200f55550b2154003038260342c0150280081e11407041c102080103805035520100c0008041c000b0b001c510f0030742d990003000003809031000b103491140e0300c0320700b0401c0c1c0c03503000c2e20b0500c44c0300f82d034042001c90a4400303000c45456600d01726820722000303008014105910003080d541c0b2890880d51000003800d20001030b800e01d1080300200401001f040c01a00602092841c04403a071050b070300c200d40c80c0003142c000c02c4401400c107030b40401307254a03214222800b04d85c0d0b90300000742c10381010781450781800704070b55a80c003250000840c1c044000c200400400c031a540a0000d00d01c0d10405080817464403012000301407051005001d69417155030303038120006000c81c80252a03084280311a00038401c40c1700c1c50a043d40e0700c2008039401c864103002880000c0283c1802c51000084650a50040c507070b00d4186c51040e400b603c0100a0442004a1481c0c5440580c6c0c49160040c0154001c0070320640d40c1c1031086070345c50009401001c4404683c02084100002101585040d40c0d0840d5240005403480c6544005200c4c240100443c2c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 767429937 1250 767428687 767428699
    0x102102409140c04030b06010503071704050607030e031615110409020304020f04090b040633180e122b0e011a030726030313050c0301051504020d0b 65
    0x1c1000c0c01507600961500320648050304555807032980911141c0304902005001d42d03025800706100b5400b64016640254103800c1c5030214440c002e800145110048130107903030f41e901080c10f1000302c0f03400d407081000746100c440181d071809616101e00303c0042d89215008040c8035151a0800762016154018280741c08080d54950351540d48240002c007942050307400341d1041c03400041c4c9081518003841400720140d0300907440e540d03030365681d160100104070751176200400b10f42c6c0c522210f4000c18040410f01c02c201e40742c203c0c090031900302000d244540c0008502c0796201d5250401030307220404001852051254040b19240c2d5402040502091203c241c03a0340c07888012142e48000e40c0c0709a9900f00e0100301100c503000300003204450848802030b031860340e80705406802100090001640c8607400750f100741c10b50000c2907058083e85c0a49841c6a004895940c01c0001c040085010400203022200c108542180207021a0030032420b0503941c0d90303486154901c265400224140042ca8940104145003001025 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 767431187 1250 767429937 767429939
    0xb0a0c0219080f13030c060c0b150111060a02070507080a0506041211011401050405060f060433021e07060504120f0203060103050c1804080901080c1201030f02010807030b01021024 79
    0xe214131013941e0301085a030760300103d00104210748644030040760300780c000405042c0d54841c0207c5594180000c140c2904210034140000084c0d80200501c5010311041c440060755131509060450901446400450540c3c1000a110002c1180050784c4c3e40c00c5038100e80c40200c40c48045000362020040294081959402c040100c0851243c0400282c100c82c41a901440641d4403801001030b410841f0030200d50000c3c081c0018040e40100000030034980403050491500c2c413840040f0322501007460402c0d60016800900c800c8084c3c0038041103804c0580b4444010505103013031110190080c0504d0044900781c9440100c444140300701624a541407640180aa590300c2d40c4070b06002d61203c550080480c050011859112085543d4031a100d10039508080d6060400d032801c4011143c00c28050300765060703070030f00344032140d869200b003490315000318411300724001c502030584005041c400000f4012000c0c58913002801c089030340c01140100c17101c1ca100c1c0c0000f403182e07041060b4484001000c00882d02c05100703000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 767432437 1250 767431187 767431207
    0x11703070503033c070e0111120d0603060203090102030907060516020126090606030f070303090b13030210031e0501030222020d06061d0d1a090705100c0b0a0c0219080f 74
    0x4d045000c0d0715140d8038480e4000e040b90040d84d000e00100c074003040710780c410200c4080e002c1071600640324014002e04c010560942d40d44440c2c050360070a8604012696000041c05a410300404c6028020403450500e01e040044541244c20719015542002c0e05000a09554150580344855003d110454840b0082c00c4c60400e00b8001e950b5100880d2024060302c686024480c450a00041503400c803940769035041d050a0134134018000f40e42101081005592210a012005035551552141c3c40300d0182d03000906080400c28112111169100102c0030600d050018005a124903684010080500300c1500d03841203d01032010080c4600b43d030781c1215074a404d4000c11410343c4003d010a081c1000c050402840d0880300802c55840300b4880000c01c10b04840e549508142440d401131341c0e000038543d0588180aa80d140411144207960482d2800074900e4460300d020050700d4113080380c2200010f00f0400150164010280d681d0410800300400002014501c00421039104100c5100c004000300711170301c501501c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 767433687 1250 767432437 767432551
    0x1030f03170a0c020d210e0c060c0f0c0a15030b01140301080d0e060a17071206060522060e19081c1403090705040207020f1801170307050303 62
    0x5500c040c018045d204144c3d4582d403092020295809200c183c1c20410040a92514020013a0032175105e054090311844281075600c4c2c0e405400d807080034401600b04541d0150103541410141a20240309d9400180d0501c500f981c406910381c80f0084909000485c0d5103a03200584041940c217598500c001400030010030742c413101251030007030f216654940c082e2011850040106d6400742821800001e04000001035074003002d2030745141c01030030500306440c40d4401e0b100030400b500c00075006440810000104462020a81040070000004a00010040d503062241c01441c030400400100d1042c003527480301a00801c0501300210041c0910002c885d0000350002030001c8020b0074040c0800494a10300144400405420843e482100c640014080150401c81004001e401c4054181d80126520640c440161030b80da01c81c04110fa907001c0721030101d40c505175001030144078407085100d440d0414030040c0c00050703002040e6504882c3c01000302d26030715050032003c840c0f58500c45c101a050f1640750301c00c038407165040e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 767434937 1250 767433687 767433701
    0xf06080d020708010506090f101e17012d0f05010e090c010c0b0f040c1e030203070902070816140d030e070e0708070f0216090f051e01030f03170a 64
    0xd400351202d4994805a5900325401101d000f5000740180300003400344a10f580c4d015920500b01d2542c1c1e81e001d500c03044e04c141c200381c85444105400412503410b1200d60040d0012985954400c8024404800c01e900360031488101c000905018145444010300c205c8055048111031740b50024007080b90b984d40300002002c00f60190f0784d0042e580074920701c400342c65124000300c50171f1a8010b6001c0703903540c550a0a26030388035402441541c194483d84808103001954003000c42c0481400483c0004d01800d500400d420001a50b001c0d100c410720401c4458002031008054994603090450b5a41181c602c0341010f0209000409000c42c10f07004030100030f054250507612138040003810740122402719441d50f83da0403002000352a488082107009001400745880740e900415184654815981c00285510380b8095a2010b9040b41d82e60603101e020043d401d0b00b042c4105984401440340e800304a09120101c00091a0103000c040e04140025169105240c00740c151000b91150684002d0302d507290000f0060010049 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 767436187 1250 767434937 767434963
    0xa0305150d030327020303040612021908060906031f0e01020405040c091d0708160903021509040515010c03110a0206070b04020f040b0306191104030b01080d0f210f0608 74
    0x4841030322076410419001c044c1d00b89074064019890107062000542d441c1402180c4841c2140d0200041400d51044500c40d2603000b8281d107601c02c01c1d06080007003094030790b0000d2030140a98000c02c0751000f01d48440c0e0404030941d2031007100144142c04550150b029100301e4024030382007400e003854080758983c0f00c90000704a030080d501e858680f00341d008048a504109440c0b8200142000c00410805c07503804050515284260030a450003e990750b001c240000e82c100c88610715088041600280346c00c190150f580d000c10f240c88204041c18002c0b0020780507143c0d07034502900700444c040300c60000c01000c10007941c425800a01c0c0d10b440704204d1524900c011411541240101c250540c03440d023031306040c00f03080340045008014162950364000b030601c1c100d2000c18000405030312182c000c040d44224000401c06075008000f081c2c01c41d070424070300d42d140ca03046400340c908003c109642071131941d43c0414545111100041032041041d0301d002000054080c2040031541d540ca0702100080a02c400100324400200b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 767437437 1250 767436187 767436221
    0x408031b061614031915080c01020703050a0b06060c0601090510120c050f043b070f0513020405030319030e2b021905030406230a0305150d0303 63
    0x1440300500034a0200d0b0b0350034400841c03031078441c40d65009000d1003c0c42d8803980b00b071480d010700a0b5005180c01a50048440105070302d6800106102c562401d10401036035010030b0005102461450b510181d59121104000d829201210042400c903540e4800301c0710030700b60381003c40c1c0b003a5840780d004c50010001550804070301030758146d00141c21340384075240281c0982c005d44801a13880c9402c3c14003220a003c511283ea1059503195a004503040405500900c1d10350f2000d000e6035a05500c161200741c21804482c83c48c2179125510800181c0d84102c403c41c02e0b14000c1e01c1140c0f4800c14094594045c2c0103c0e08a0795040c040402c0841089000040000d0fd101c0d013994140940082080c804d504c50072201d10602460200c208040c620194010f0003030b0b0b05000520444031120740d0600002591013a0110442c0d41d0b400014081050b194854524102d80420a50b090100200061b40880500c185940382d03040c152a400040c0d010238000718501064400070305003c0c103400040c54020010400c4802c2c1c040403030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 767438687 1250 767437437 767437441
    0x3160912030206130c0807060e1801030b071d0405130c1403030f0702030705030105100306060b0a1b050a02150d0f0b060a0c05070f0b180102160603090302030408031b06 74
    0x3114a490942034041d0040e00c0d098846800d6219521010b240603101c01c40d0020780003038145810400070008040c00d81d10140300011007c20010650030040f040d91115100f41e0040c00480d0016444940210340c0e801d08000e40d007244d20302405081020b45601d03602034501002c211917601c4051100c21450b2013a01010001c580b600450400c6001400b1481d070507038030a011200c20450403000410006000408445c00c580e51040000d09640089540d005c4460188000b002008214017900000e02400310320f1a05103041e00d0801031807000c0c4c2c01195511610303071000440a04c0b00078000c0c94000340d005401c0c444603942842010f211381d4001d0303800c0d0564618240001051103820300c075000c56010000c100f58a000c00303004040b940114012819110350249840004503c6a21182070b0300a00c00708070a55102c074000c80450168030290340707e0318103541103449a032032401c82d43c04c0e03240140c07002410b0000e84260036041c102d01e10700880d00040c40520000be0020782c840c140a4a824007001a10300300c890315 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 767439937 1250 767438687 767438699
    0x1401060b03060f09070206060d021f020c212e050a1505120a0b1b03070e0406150c080c150c090306180703030525030c0c0603091e0204020c03031609 65
    0x44130121100700050f0801000304902e807900316081c0b2103a45c0001d000e80030206081c803060700c105e038041a218015a210200380b103418241001300c0388030f00d80c01d1141141c050302c04181e480e454600494100003e5801e00a0046148150840800013000da004040086141980107000104080050350500c0f001154002510f40350600c2480100741c0d44d07002605280d0245c0d9103800d020705001e07007440340400000440343c02d0b514006e00a14800d1100d82d5468046005100500046070f9040d000300b00070310040d115100c0200e402c2152411000c1d40800415660b10210140900704043e01c0b00b24240c4211180910089000c824058101c000081342500e1868540c0301c484400414918240d09c05034210f0801000441d000340d014000158601c48010100804441c154190701448042180812424440c0d541804100038500028201c01d00302000b07115031f00e0b1220742d00401401801c145084910100030110b4580382c050b01d40341c0028504580d100e0070b0500384540e501c1d00e03003903001000075154900013400d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 767441187 1250 767439937 767439949
    0x90a060b060c0a0b06010c0519020406241119150507080601021906200304030207060807140d14101701050f2a0a0201140a06031106071401060b03060f 66
    0xb00020721401800742940d40d81d140c084a503001400036051062000182000c142e0038004c001d141810b4010184401c00c0a10412003211100c0e0030032054074082440290290448000c4c5a1240c2d1241c00d04c0e00c07031041c4102520f454882c152a9421001040c4c5100204109a1280050380e400f20000240025560000d007110010710403900180160701c2056010100b201c402c0e00e201d02da5005020102e01108440300e24000b21452500104102d5400010002410390500c80040549254507106e01182803034440200344107517148210104410003d101c0002c0d1080c3c0c0e2103e101c0341680c0c40ba1021704c1c604200004040c0c4960720131600503583c1d06c1c03450702484106100350f5104d2040715109000c9130b11a640c12030710300d0074221010142600398407940400d4100600240070302950f03507400481c1e2410b84400348018a103001c0c081c0c03070000c1d040c0703102070000030b20b0700030724100c0b203a41504c0f241c0c0c54800c80c0c200341c1031080101040d520107502c3d107880821691042c070011441004259030108484094034240700d4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 767442437 1250 767441187 767441197
    0xe0f0d1b0305030c0726180102010501050a23031204030b070207030206120601020c030a0b06010f021c1b080d02070c14090103170c0f06040201170f06090c070803090a060b06 76
    0x500820003c1c64250341040a028401e0089118843c00e10503c40d902c01403280e2100545942180071030001c83c003003819140d40c2c407c2d000170320080c031142d4508004034480407500d0051015004280390300706a8020b0310714080300c8240c0014101c07908580c540a45641542c054041940c030080b001001803500c600000c0e01d00304803075000d04402d113001c50f1072588110341c100240405046024100107800c0b560b404000880800b4010070001c2e03041d041010014102400700e8036045d013550025090160f040206a00050380140c480c102070b42072102298a50140189844000f00406400300d00381000e0030701d82c0c0c060400584214810302c20280c840184c1b00d07405860203184c55000180e40300500001e0390344000e400310380c254000b000b410410308004040c00c12244074050841075201504210566074030104821b0818030300040e49000d414401c2210309180d100074880d078080d042c1c0c2808200301030045400c4500c00c54114007280e80340e04200c4617403500c4040c04001980c065043c4840c1202610300503040b15 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 767443687 1250 767442437 767442443
    0x11d090703020f0d0f030e12070303050d02090f13020a080c09030a02040b01090f120c060e01052b020c0c19050f090c04031a011a19050d0e0f0d1b 64
    0x12001600d56400c10507465040c43c01c054001003130a1807040083c5800110301c40c030fa807003500d44402610000c0c0900042400355803540c19640d01104040010a07004170842d983d0b00300d10300c005656180360300d000c00c031642e0340751140702d41040380641e4500311015194050800c4060640e61440c1d9034607003441d40c52031401a0920f043e4950049541100180740c140d01403026280181010f42c9810fa80e401c0840d1030651650040580d64104a210b104100b001c1c03243e40058003213410460407102044000030164000c2d03103d641c0d115441c14800f407612540c8140c804a800c01e074001c0542d501c0c0d100603ea10380b00c2c5070b8809114024000c00e4041600d01490101d030b44199480034080b62509a080703c1000b845210181000300c85d808104004400f042c00301c2c650508400828900742c1312941f51003c000d040440041280c030701c1e00c0040c0b00e54a07000d9a07540316424021580e01d400368031404540f51517001804041103100d041e01c070320580000f00100101e0100c40004980c2c54442039240000010300c1c441200c20b01c02 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 767444937 1250 767443687 767443693
    0x204060509042a0312031a130e15010f0b030703020705060414010b01020f030d150909060b03100e12030712050a06080c0105040f0b0c0a0602031509060303070f0b131a011d09 76
    0x11003141e8487d900408400c24800946d034841c1c035800000c58441301540d401e904846071140c00048541c881080744015580310b001c40202c0341d61408490150f03040403405600e0b1209000004180658480d070150b625050308441910218103084c0b5010400c06c1c25400322150a50078090f1440c482d600100d410f0205402400c040d41c0383c007003031409640003000940c40c40c450000e100c80000c560b903003142c407400c000c05107d4107000844000c00b90800d0702d170042561810341c505080003802d8440d0100840c4420180c00c0c0030410342c0d00e0f500c8058007525110441070070021f4103460241000500d0350340760060b03c08c96240d01c0030358240c08619801142e00d4411401828513900728000304005c040030080003005101240700c203031780d0702402a595240a0b640155062801c05151201c00c0030f40f440d103001600c0c0c20050450040d4a400c0c01941d444202000400f0702400c00c07aa04000a104821804035443c1210745c000200000c010480d080003135116402c0c0248034400c0510741166485803e0382e50424020940c0c9801 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 767446043 1106 767444937 767444963
    0x50f010c031104081b2d010914010206060d0503090d110307051e010e041d060a0c03090302061303030921030e070f03020d0204060509042a03 62
    0x21a1018003010403040102140000b100c0c2c0c80c00d003d100365130170010002d40000c0c0c91050030807400070004c00d25138550198060983c0401d091207500b41c03038451242d501c41d030644c112a00c1c0700601c2d03030150744070300046080e41c500440c241203441d118004407407a0031074120202c0c0c0c040a011078226250014803410710814039003030003850003901094500d00c804241c40c0315410390120511000324140218070050f01880c0e1035030341208890700090003800121240e03400080c0e990343c80440e0074140d090b160915410400d4480c0c01690803240d010b90043c212070300c5040b00400340900350101181810758681138840058000420100720102041e501f1741c0b0f54500c0c8030060192404110800c1e46038000b1007050140c00c003001c44ca00c09907901039600504559651020130020000c507000942e01c842403408100401c8004c4111045c1084030f0b80b180941841c0301e078204c0040313401c14080240302c91b2890310 = true := by decide +kernel

theorem cover : BRFrame.Cov 767266187 767446043 := by
  have h0 := BRFrame.cov_init 767266187
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767266187 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 767266187 ≤ n) (h2 : n < 767446043) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
