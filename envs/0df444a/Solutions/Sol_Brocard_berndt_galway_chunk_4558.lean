-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4558
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:00:33.590823+00:00
-- url     : https://prove2.me/submissions/70667904-0bca-463b-b35d-a6d2ba692d2a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 819604316 ≤ n < 819784172 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 819605566 1250 819604316 819604327
    0xc03030c030f0c0c0909010507020105010b07030c150f02070f0c09050601120902031219080105030106080d08100e0112110d12080907030b10030c090b010503041704080703060209010e0f0105 83
    0x50b4854054030210740100101c0b14802d40c490001021500221400b4030380d42e5596041054869090003003500401402c01b0302c0346010080c0d02c009118117203240c806132900c0d50300d02089100c24104e43c024007204000120441d1682103c1c60300005480c141034040c3c4143d03000c040c012926100d64030900b030050704140c440fa0036050b410740001010340882c07901a030703060184061840c20804450001e20080420034140c00c40c40202d080090705004060704585d009a24081041c8580d000000d0500107840480c01c100182e680c40c00d900700031484044e0400750500b80b040f800010f000190f206040a0740e8890304903040d50300c032014103001c078030000941c01918402880c000f11000c680950b044640202458050703c1c05140c890b110f94a007160306485100007860052410410302c8030084540d405000b81000c2030000381c2410000030014003002d0800b40c142043e804507140d00b2903011080b500100b00013000d13246035503a2810100000d4020401c007901145d5a5103a0b600310f07203807046468100700710503190341d030421 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 819606816 1250 819605566 819605587
    0xf0c0c19093c0f02210708010e0a110702060a03020705070605030405070311030c09090708070b070c1a25140d1707030e0f070305071a0405010e04090b0a0b030c03030c03 74
    0x89080900590760ba940e42070352680514043c0018243c0c240e81c0e00170f100c00b403404000380c8844080c0042c00e0500700b05140c00180b000c03060b4141c00c1c80d04061a081d0100d00c00b031320801c00042511071318200a5000c1000039003034407119050f401505200e800768042c5c661155540c1c4080c1d40c1480219801090368219140a100040b403040c44441000000303400c8400c4142c840001c99002c200a4465028a42c4144010008014108100b1001e0400c0c3c1c0244c50801c0c4240e5502c400b10301481c0252a004000c904100141050250541d03182084000000c1c506521201594586c038168000035928007031250512040000c000a020b40d40e081965a81321350940000e400b13400d604c0c0054144820940c03a00084449004200300c815014511480682219865031420619103201c0794008410380504119403452105160151400c940d0f0a0034040d1140b640c03e40010010100c40f40b00508109103c2e080c0061080c1c1a44039141042007030f81260a00018101056920b0044100c0203403554820040140c80 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 819608066 1250 819606816 819606911
    0x230f1507030225020f1503060f0d05100b1903030509130e01020a05120a06050901120f0b0114030115141e0339060f0c0c1909 55
    0x28818035006003002c0550505441c01c01c0180c4040361000040c1e02880c0940c501941c5d14003019030226503109010790400f024403030a000041aa40c401c64031210702d040c840e03c1d0242c0c2d1000141e8810241c03040e00d006003164100402c440d40c041c5014241401d22040706841602c2c0e4001903a805440c0d8a0a040081c0c0800c40ca50f48100750009129444940d4606944400d002070142d004141d11400d031030303c0b482450f415034803c0080049211509100f02040f241e101d05181c281036929011440d1503590380c9080c40703040803400072001416034400000009810510089052400004500070b100c2c0d92401d800752071024825000700a1030b100d0381548012079203800300260384411001c500002440701a07000080c184400d5080c040701e0f04141c018845c1a4a008405809403a0301c4418000404190100800c1c3c0c070b40150410345008a100090420032510108040c00c3c0d40c40e0020000a42001c0c10340105902048074890482000c0c201010300c240e0f40d560101d00005000303c40041c0307090000d00da040100 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 819609316 1250 819608066 819608071
    0x110d0206072a18050f04080403170f07120f0f0f0c0f02030304030602030601080f04031b05030706110913020c0d0e0a09112502132007230f15 62
    0x344200c18040841c1e4801031110b07040700414007083d401e00d281e0144903040050b0340700100f03007031500d0a41d2810000000d1501d8144c4040e290460105072140440301c2e600550b83c450815804021031002c40c5100030848516081200c0c0e15141d0380e0703140c40a1003a801a03401501f0403042e480400c8581403c01035181c401c5060000c060f0090f4070800c408200c503004641960b00941080d104e1036000020011103580007070f10142c102b402065050042d25064800078000f001814136201e10203642c0a440050200801c1640e0b01707603800103020455101c4000d506400c0d9845040e41c14000c0d40c0002100744540300910944502c604000054201844004412220b4407074040259520489044000c22390301e8607803140600b07182138509030701d0b540c0c0301000c0101c4101c80c8006000c20251a1f00300c1103401a01c440c079030240340318048000424943c0070306a1941c0d940010f00c05415445401043c08401c5c0644800d0780d50f031801a00c41c0802c100ca210052445d150141e10b80b11222580c0101d403000d41103041020090f9 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 819610566 1250 819609316 819609353
    0x1050f07031808120a06080d08060d02010309060f0b0906060a0e060c070b1306030b0604080a1401060b070501090c08280309050a060203071b230406050d03020604110d020607 76
    0x501000325643c1e40001d074010994101500d00c0900410024000a04c01c4070081e00d41744c001004c242d04440d000030008000140601e000302c01d589510011a406038002c65042c56211a0501c4490900740c69600203180c4a00c4040c0f0a402101c04103001d230410038212203240d0041d5842d600d1740c9103040c003801506c1d8040444640c4611803800c00140c848110000b4105155049080d848400d250640050680e40c54416a5126000800042240c20400034042100650212140d4400c0e1499000280101180d9101d09010383c0c0006601c0200300703040d44080000c40c802c03100c115045440749013140d07881004009042c078661440910441c1c0c180341c4600354500c0351091501000d8562280046800188103034054400350340041400030801a103a209845c51410300058404000d240081d00003105802002c000300c032a41c050480e240136240e0380c00550251001800c1407020881034600250f5031032080320252200c6401c8845140715203052008108816001006607080c81112f498102015903004060f0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 819611816 1250 819610566 819610601
    0x90b0d0513060603140601090227010207080d02011d0d08040b040c03021908011a01050a1b0501020406090f0824070e0d140118051009080d0203010e04020a05010201050f0703 76
    0x1000081d440e0f0080a001d548901810f00040d52200c10301850850b040e005002a107005001009080d40380440107034985079512110400000c0303007401131f400d1041d917410502c0907010300c90300b010006805400c08401204401d0012420a107030002c0507817103400c800c00c9940007480c00000b003400714034103a00590700140940c5610268548d03960016820a40902284001c1e06494208104003c002e108840141288034040907900c194180001c040e0320840824605108041d144071400c00f100014a505041c2d20030300855546458080103407001005126501ea074550400000c500528041081035540d03030310a403c4401c062a0480100e01c211004050320b0810030700310105003081d82d95041104035680682c04184d414001c03120316500b9035403002034120307108141b0600c0200050300050a80c40c0409068000102c654141c9441500c83c8590309641281e680080004154003070b11041300390285100f110341062082c0c1e10030040e400e8460445e1121034001c0910300107504680241c0214216400e0741580 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 819613066 1250 819611816 819611851
    0xb13030809012006070806030105060a180f060e0a0b060c1b18040609050613053319061406090f011209080903010501170a120504050d0f020f01090b0d05 67
    0x780c3d10459550092440c5035100300d090091154100c840e0355046107054009104600c1e010002c82c050480030b00c01c2d150007012222041c84016074550007175501c1180d0700810b002980e41c81091010120043d5486050301380340242c9040545080d00c100c52202c610b42c0b0180580c503261480a46aa50800c117030160401d1200303d00c80c8444280c40d01e503d21030303031003103000082c0000182031492a044000302003a41120300c040019012800c000340040c0702005900200708103047c00c0781544904070100221103c44084402400840009030b43d18030007071404104104030303060703903542a4100c44501580542d08004208600110b608110072040d140d41c1c4103051907403424115030385800485100d01c0b0141c61424011a80155600e020f002d0b2500421001244c510054a034018032038498951590041c64a5481040010303528010410344008000081030061100307418104000c0c100402d000491144103404890440c43d80940700d4101600c1c2e1403804a41400c010f0700c0300c0301c000c04014014141419a4501c0d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 819614316 1250 819613066 819613097
    0x10f140d060609051803090609130b030d091502010b09071b08130e01080303070e0d0606082a01031e090201020709050a1e09050303040b1e150a0b1303080901 69
    0xb003100a09052400284505e0070b0002511001c250020800590300204030002060340c0d000e050340c0d0b804a003120094410169540594010454403000d2a0140604c540c0d0300240d40c0c11048220484020b00d2400715108070701c241c1242250501c40806901224250209030121300c40c0207000b01e404582c4c4652031084115844071042c47d04180f03440240301405050a1101040307030420b103401010400c00450460415407000341c09001d03403061403405100381814440c20300109400520003403100702c041d1000242000303510780200342186881d000005030200c225200d03510038485c0074044000e401101405111503031005028205084041c4d04503c10f002002c150844140700d95030040030300140004110000307000c0910607c120100440006240003041c001082001c811030791720691000c215240b0303603980050448100c021300c120a5000c282c02040112001c2c00c0284d1100b4501c2c11111100030564964000d142803007040020b660580da4244104002404e0b00701038052804141401030070385e10700340b0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 819615566 1250 819614316 819614321
    0x90a020703140f130f080c0301090f0303020f0712020a020108011e0e181605090708010e1b0714060928060c0201020403170909220323071109060603010f140d06 70
    0x400c8090200844c40003002820000c00a20036201c0c0b00b54001e01c2b1807a0107460750f08401d46506009818150000b0364500040d00100071a03008980c0441c829010b8207107254000d59071101168200e000c80d11800010034035002c03d02d8212018030752064000c40308c50904542c5d06415202916130100690500183e55802c1d109009000010064039050784001e0310304010881c92810103070a410134054107070b0052003001c00304001d0a520496201d210b1001c0c104100c0149090300c107000016040485c10f4125035091000400d4250042e44ea000480d00100c8150000c00100410750303074400310070f01c01e144040d000902d180d00b2580000100b80001824035503241c031002c90500510030b0f034145c00d04002500702a03a00e001c0000541200c80c6101c4581e0399545070506000115000101030280030035030319840390b4000805800e803030381f96000340c1194030b560f07140c6000100030001012851140720b03010001034980c2810000d4038102c4020145440d89180b030030902000c1803121003c490f40029050380d04501180d00d60 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 819616816 1250 819615566 819615569
    0x2070f020409150c0e4902090a050a0608010b030a030c0c240305150105070204090c180f0e0a0c0e18120c1c050405010509130c0e090a020703140f13 65
    0x15101c5101c0d5840940411483c10184c090b504042190030882100d203501642016042d88411084c0440101c2c6c071010a610704028841d000350701500c0c900411104c1c800d1034000c1d41c000c014540051000c10f40b250302103426540407042c43c82e0140d0003120f01d103012038401c0450381c00326401413680348400e5884a00c2407016031004030681c911860190034600300181c1c5803003441ea000500d84410b03c508400100000d110340306000b0081d1180d40c462100006002464801e02c000300741501c4251501c010480304c542c0940340140c1000509490205130740d0b91000c0204450030000d9200341400842d500b850076100d0040341c09451401515141e2040d114900002c1000f03013480c1603c1500c40340c44113440c1d0309076840d0035100001c00c0f4800c2d50491001c20310f5600b0405440c16501c1c2403c141c1e88600212010900807041c0f840498240740c18140001a0395030054000c03400c40c5025152a410340e505c040410b000da1141400003800901d845c0b686801841c90000070341003210618080c1850321260411411030000a03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 819618066 1250 819616816 819616841
    0xb280e3a080f070309020112020304031e030f0e06011a0a0c08070b061f021c020c0616020a050a0e1504090602120708010602010e0c1e060a0906030f02070f02040915 72
    0x101c1c0148040306203401007290703020380c82d40380c2402404450b600007011010f00c4805a03414a8020022904043c052000d541e48030b00300180c446a4550b64940080c05010345201482c207103460000c10711020100803800d50f042e1f85864040d6030343c9030695043c140b19903110503800030811011401d981d0000d0b002e03000402800d406a0800803250610380c00304a40c412800c00042d074401c41c05d031103284410342c001c00d1000c0003208041c0a01c0d02080d000905074141103c1104290744620002a0424071036070810003070314040c4c001d5501901c525254414400131034031900802e43c00f0810000041c001202c03008503d07901142c06440461403a10590301c40042ea0000520101008024401c2144865000312014010800c030303c004e010b20030114040d071351905802d043d002e00074041209010f04418403066910040d11015080076550024810014085449802740c040001e051150845800d0340074001e0350307151a0404014407000c0350076070801c4000c004500701102d03900006a120071641081d40300d90070345c2c90325 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 819619316 1250 819618066 819618077
    0x150405130e06010501050a120903021c0302071401060f0e1506040801091119090b030708031b0d0c0809131e060810020a09050603130b280e3a 62
    0x40a420341402c00005800041c10042c1c00d1000340d60040d4041d0207196031440c1c0c104000748000d1075003412410f16041602d03e8980ba142c00b009400155410382c01081c1c0c9a0041002c1c1c00342d15401c0798441c0c04d89015201d40c0400240c2020f050080d03000e0324076055040445400b01014800fc8000840c8180e041580301c506a0396444951900b4410036100841252100304c0300c0700c450f4659586020301c000c0a03401510310880c1d94100b40d6000d51000c101a4015003070384401c8030744602d180c070040c0501940a0f10a040c16000f0403030300061a038000c0160303200c000d6204500d035081c050344e4000e0148072540a00c200c034520391201d455030007104441841035012941781c0390114045007020f00040c608400c0c0350360081c600d481000b400b16007540c02145001955002c4621554903141c4002000e1240e5140d100a0711418001c014440f0b11804915406245050881040005503802196204a4141e071a40a805412102810f965203588400311401002c1203500411000280d07148040707116105050000400c9 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 819620566 1250 819619316 819619331
    0x62309030604030c0b0604151806123002100203130f060506180c0706110708121b13060305090f0a0501090b09160b1b0a05070e0a0b01080615040513 65
    0x11145c00305a50102003901c0500c0210f500180002030f00b455441540810b5480e205a1132038140030390005002040c0c45000c240321350400b0305001410040300e42d408112900d01c0c3c030141901058090710581c801c9400d03005400144016041d54001c0c0d40001c200c840f6134100700445c94000703030504405e0081c450156500017030701d20700311082c801d108035490480040300c1007107001c00884401341c000b00d030500c130750000c8041030b0f00c0801003811485000300507004000c014041100c0080040c040131072403180c0300440c602c2c02c400c0c001280400091103400c880740c01109080c0b0052000b103001e0b81015410412040494081842c401001420541794500880d110394494902000b80311801e1903454115070408060200140650b4035141002c04034414005900070200d075940d041405903c03401c404480c80015590b4401841c0780c55034541540d40603c0e07500005c0e02c00881c00c0c0360340c5440345200c00c00041c1c6803041e26880321000c1002c42460000c4095004000704404122a1121015108640300b5000f011a840 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 819621816 1250 819620566 819620573
    0xb0d050a05090c0f0d0c0e0c030907060f05070b04030e030f03030a060614031b0f070302030a080903091806060d061509061e0e0d1e0c0f062309030604030c 68
    0xc50002d010300003076910040e80302c035080d6100302030402e01d00000c81380302ea22060903141c1901000c100d0fa100030440c0a2500c20002c00d200050001e520030f031482003d6a030115150082a515004031000340360000c1c400740f0145001840384000560814028201590402020b0300040e150044414484000307800102c113015040c501409000701800036810020101c40034031403440b0145c000240658403143c0e888842c00768100540b01200c00c0d016071a030182da5203031803c0c2000b966070351051100c1d000140b6880c0000c0c44a60700841a2414000018900f0541400741340740d8440051001e0f01855018908000d1920a48428031945004001606048168107407641c8090005c1107164494414450090300801c45004a40140203081c045414040445280200810305081c80c100c401040a01d08001e90300000328070b1605510a40d10942120075040c1e1035a2000c89034500505c991340200d8818000341c186442450599813a080c1a001c4c500e083c0b546910010f85452419102079002c82c110030508410f0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 819623066 1250 819621816 819621821
    0x90603120a0c0b0c04121b0815160c2f04050a0c020f1b0409060f060e060a0504020f040b031801090c0e010918080a051303062307020a0b0703060b0d050a 67
    0x8540704040e46070070f05180090101d2001c495000003803004079540d20340b00c001f258801c2940060030486088894240c14070101d03000145c0262041d4070803601480070640003a10414550b00c0302548240303507284000c0421281891072070780301040e12008190207200751003503d6602c1024440c42c1040000b10381e4100031170000c1d00b0a4928017414541b500040f0110f06d522184200341ca80c1160242c80c0000e0004450618500911041050704034507410090005030300503000354414014001100e20308040d42d41c62040000b240728800b02402c0016050100700840741580000e16441451503400d00980010440c0d00ba0031108410011508145008000d0211440c1c082c3c280f40542540c060130441e084009014600205400000511100c030000300a121203101e481174800c404103c40d017a010a5480b45018009443d02481c2c21030307010007600300100f43e4460160a1030040c0c6680d009003420a00c0350b101e100c4c000d24014421410305480380c800040e580b0485000b4005150105800565810810042070a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 819624316 1250 819623066 819623071
    0x3091501050d03090608041416060906090503070504050a020f04080703030e0a050916030e07140f01051e091503070509011d030c04091515080609071202090603120a0c0b 74
    0x1a010b00e200c50b40000350004201420346219007400350310b690381c51401c51400c0c143c2d003a2860081c01742d1040141c04419020307182d001e031841600c4400284d9183c03c811125040c10340310f001d50661107494200500d0405500450300060f0810000d80340c20283c07007000a296000c1d81c04485158002c035420802d02d87c0c0304121191100e021580c0c12221850000001c0c200c08010300340c043c0c00054400542446c5000341e01204c144034403e000e40da030136644c8410400103400304022050140d80b1001e40300c0c585610030f9045a1000042114240b4820b07400400920700d0341200c1c040750b8110917074600d00e0508100c6403000d14850078075907407990b96941405000420751410981c2c0000080d030b41f003185070303403a9a01182c80d03d42014203a034002914042401c00018508122900c601030620301032000c42d032803d9911808003070390a408200c0b442a1205018940d0358503a40c4036a800f0320001100b02001840c1000400350443d4004017200c6d8401464822808030741d0200045030040f5929590300b01c20008805001c66 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 819625566 1250 819624316 819624319
    0x4060b0717130504020903150a060819050303070c030c060615031802090604270305130e010e01150c05330f15120f010609050112020a18020f0309150105 67
    0x142001e4002c41101045000d50040030f10854004c1281b90154504005680d00c4480f080c51801642c181102000c000b0302c0940650100d0303004480240d44055044c0050341d41007035003c401036107035035202c82c001c44041d102510118200301e0748406000105089000d0035020f0403c421342c02c45040000500036040341d5607019035456140769201c410015a51303080300c1940c0300e41d0030f5a0100c0d80c8100203c0a642c06400800241d07011542580c1c0e40c420b040e8010042d0100d909407001f00444640c44e02e403c03590100b001d1180b0300300c0301c00b10001400410354982200b2400301003818800026201e80d07484a003454100200981030402c0843c46100da1800c090f0503d0401c44020741c1d2100da0b041a400341e03034150070028804480070103546030410064031528800751087e0102c009075014250b640741c0785406401035108098102d800c160002c00c05802c0035200c81d071100d03030090410f4030300745c03a0003030b85c01ca842c2088000ba40720950912036103010a03904d038010b51103851814040c00c1c2040079140009032070001030b046103 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 819626816 1250 819625566 819625613
    0x105060108070c0224520816140d0e10090506030907080a1416080a0b09030f07060b040f02210a1d16150f03020f0904060b07 55
    0x283c0142e01c0f048444d42c485d101c40c1210491540000b64000c009201e6250014642101e00310302005054040920b4896004130480100070441c2c1d41d0302d820301107030801c1003412601108240b4440000d89000007082d5a803080042310b5101c03001529101b5515145110503030702508001030545460750b100380c01c051640300460301905800c880c013200610030552400784501810303001010404014041040388001c1104600301d4544d14254030340080d06540c8914400c1e554401e0040600032800a4250941910380500080210b40d80940f42d1002055020304424064001000808100340f080c000600328140100804900001240d0038801111080c1c04900d401a105101c0103000082121040c411004281c0c0c1010790f50f140d01001e200148200c401302201c2003410040c0c5003080c0030105240b0f00441c0064032003106c16030748070880c80910703034411305240000d00d492a410384424000e07409070078004d400809203030400454101140c00c03100e183d00112403030390b40400c00f40d04000c00300b0b920030715035440c2d071246 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 819628066 1250 819626816 819626837
    0xf0b1603020a020d0e0622171b0f04140c0901080901050606070212011b09030b0a0b01120e0115030c0e0901021804090503210115050f1603050417010506010807 70
    0x81d21381c41100c0b0b00d01d040224801e6800307003035990700c02503a01070580c100d4800007201c405280d5948102191092050b0004c1e18241c204a03140d02059413080d05c107aa500c5c1070f4540682d20304021059003903c607015442550741c0307a0880c40e40490340c0090300c9940d48402c0140d48000920000d032190b0402460f000e41c0780c0c10081040025103072039050b1380da119030503a00c0b0010f921410035020301402071100c00e03880c00349402e80c007440c59960045070300341181e0103014403a20581ba0b09070b4406c00c0c0d0350068a4607001c40c064001060258031558000d2021100d140000a200c0000801c021000c0000f41c1c0705560144103c9014004048802c60050304118000021460300c151401c500c6200002c000710b5030b00c00e40d503900c1c0110503c1000d0086413450881d070b1184040b00140403180c00d40003482800f901d2200d811080a07103211354042c200b1101500f007082141c905200ca048402c011405034180101d080000500c00002d00e402407040c4030221070100b00c004512031418900042420800070b103c802000240700341c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 819629316 1250 819628066 819628087
    0x91c03210b0f12070902130510110a150908040b090102011503120c0606080a030315090c1d0d020904050309040b0d0b070f0e0a06050909060103090b13030c0f0b160302 73
    0xb24500007550549100c585122a001e00e2418030b122544034000480c00007903001500c4110b000401d094074404c4402c10480b5201d0315080382c5520300d0710b403560030641c012082d0b400421101a00985201c15100c17004c94859074544e0380f43c0c0729400a500003007160300081080e0640d0740c1c0a000b41481040850403055030300f071840c0c82f40b11009888818600c288503201490200b800b40f180c002c18083d180400464807036444500e0700400414010b00002107046442e41c010030401c103540204228011240d0b100c10b50607404070101c003000034500300704c0c50b440100c40c41c5d010b005841e00c8071344502c2140160051501e40d9052400d100940e01d441d00c1c1144212200000c1c04006042c41040c035401094030300c1c2000c4a02c2c02e5210a6500650200100d40d005006800000340f81d03902c800103020f03503003040e41c00075001c0e00d42100660a480c00820010a950f00410004904180400c012031005010746407003040300d1480d80310349140c0c840d0b0240031b0380c07802100ba0810088070340402d504004a56a807400b10700e002000340 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 819630566 1250 819629316 819629329
    0xf0114060f030f100504020f0411190906140c030c0a03050301080622081e04080d02010b030609211303061b0c02030c1e12031b01020a090506091c03210b 67
    0x4109031004c65807400403506545804041c4445040003070800c2100340c1d00c160700301030b86400c00a40024028401006121054440d4400ea0b00300c2e21251a0782c0b40c4c0240d80c001355003c0e600035800c400041e11083c0270754400307100104024020140651140c69480d410040803604041006000031406000100b4407a08410b1074003845500b03907004440592540040c00c0c440c0742c8520781c4c0f000729991240104010505803404030303008002816603002000401298402e00d41c0b90002101c0c41011500034090460140100b08042d00c074400b02c0c6c1d481280b03095112a44488038260b81d40003510095600d030400c189641c0403089070340c131502060a100701222015030002e0303a1410441181801340a100c0b003800d400150004040898070f00003018401c01d00c1d02c00c80400e07540c5d0072196600401d0020707503983c0750501c0d070188200d500a2199648548106041c5018005241c0c406044035402c441e8004640d0742604030034004250b030500c290303108a0080390801c803900076800120580a0081d2074941c45020546c1c035207 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 819631816 1250 819630566 819630583
    0x1a04031814120f01050a0f150e06120709060b0a111915020705030c0a06140408030106030b1302270a0b03010323030d0e0d0c110f030f0114060f030f 65
    0x8544100702c001901100c0b034103040042180161a40c03c2c0701c18860707400410342140301c01104107682004410000880086a103000307108001c140700241020811504055038404d0790703900c0341400c48041903031381c61403002101c1496201e92050000414804402580003140c5001c210f12030f0028146500711030014090440004e00050440410703541500b1482c44940540f401c0c2e94200040c0c9441c0d6082c60070031901d07440b8508040f15201e00c0c04c140c50080019441b80c403406a0307041101300c0d05582c2050010b07401040351000059115202402c10754240540d40010020300000e60300200442e900b50100d070003002c2114240301d2040c10000014044103000f4025681182d8000070441c4a003210344c440046034050302c00179851a8000003c2062800700ba07608400080308030502200c0c07096080080484212402500003025040061543c0c03890345840d0302458901d0100906649603c120041034900316009090810b802c94a40002c202051a00c0c01d01100c0c4541c06030054a001208400815180c8404 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 819633066 1250 819631816 819631819
    0x60905090c0c032a010c18050306090a030305070212030124030b1e0a030b0103080c060a0b0d0320030406030b01080105060a350406090203010c030902100c050a1a04031814 75
    0x440d424404055605800c113601890340301c0003001000c507501001400e6900c08004050f8000e81500700040034200040d82c01d119a42440150840991581c7c0880c0603050142c502800c6205007a95004c0c50540d0b04019402400102c07401e0044c840b0f00402c0c025104650322514050519113200301d0b0654444040c1c03401c985c04100f1f082054243c3c000001240c440d02a04081c00c080008400801040442001891816214012501d55070340c0d450070300d01911480c1200030f80141c0285d90000c0040d010381282c1c9107190740001c451043c100704000d07003481c6401a500501c0042c1e220302c2d800c5101e580090245000d40001e0340c2c483e10300004124040c098082007444014040d800720409000c6004c003e1404244090610292280e8100760600d000546541e00d404c0e4825482e15810841d298082c1c8606410303254060221114079200300001d4556014440c000d44041c050302c3d001e4000100507402e07034040f01d10340d41000c181c5804d0600700101201500e04650a241c02118014840040783c4032950062010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 819634316 1250 819633066 819633097
    0xf03070806421c2103021201140a09020412140c040e01051b03100e09100603030f03230a020a030e071e0b0307021005042102060105040b0d02011b08070c060905090c0c03 74
    0x13225a8114000e105006011002402e48000882d40c2520041c031040b03503100403185038186d240c89417000400c03841a0700c200000c00801884081c000390500c84405800590b03541034032609103c0034080fa06640d60b03100c0c21076103650744030304229500c038280c200e51102000c0100740c142107181605801a01c550310303000300510030703496000292441008200580c0b800e50030101c18044190ba078a80500950100b10012002c00d0914444002010120064942c2c4004d00300000d116034580c40041402540035258410030192241104511224100085001449901d60f009449d2170789040c2108002c2a9800880100404101f4032010650010300b03c032400302e044800160580b0380d842c1c1500142d5100205d4400403000b141d03a80c1003175030003190075412280141e17424440400170204001040454820007400700d6a6041c0030864070103c0d43c0030900d207a115440291800300349031107110f60610554417040016100807824002410f06102098010034401d50b05400c001c2515480da4883c041e006417000c0104 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 819635566 1250 819634316 819634373
    0x30f010231030206040f0608070c0f0b0a0204050a0807030204050601050c101e0f021b120d05042603150a0f0b030907031403090f03070806421c 63
    0x401c600c949002180d000780513a5480ea50303180f0048480c800340c82000c02003141200000c0311f407070040190115a40d44600803100400d1242d0f241d5480e402d015258801c00340d0700384404111030b100c0d50b4104000d0840c1500034500640385204101c1600e80003007480b41007104c1482003192410b40025448040c0c10400404103400c650b40d0b00340fa481c00400310f82d010f03041c0d0900034001100011540108208491003007010304030072880f10210794800303048100d092884020014540c1c480034680c84160018440c0701c0d8017000b54101038140e2802107101482805c9000d0020a1064120203075280c0b003a87c1d50265050041c16140c0142030601c40c00c0c0c1d2140c103c5440e00040098407540341400400091648406003d00d0083d11040f01303030782e980000b101e0754060320404c08010418600001c000c01180c58000041105580342c645940080120310003400c65603d10500c1751010700030340256905041095a01910082240c40c100a201d415645810980410551510380414403101e903c100da03d464120b4045040c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 819636816 1250 819635566 819635647
    0x30408190b0c072105030405012004060302160503070503091327050102090a0306060f0905040c051011010e030a03050f040f030516020d080306030105100f0909020109051e030f0102 79
    0x19522548104c500509580080801903002400346002c0d600403070013082000c00005c0c021000c0c90507203071149070b84403040c0410420184030b030700104641c00d0754010071f9404414990701d1506d950410b20045900e9000403880c442a030604810003039110900d46010701c522805940011549000c20009000d10181c098110041c0042501110012030b00640361000080c0d9030704200004001a0103102ca0b19600074500041c800800d010301d9028a4005410b4081c0314501810814200c85c0c01c227015041c0800c0c1d0b150460064006c0c03041520340c04880016560b540032014004040b51002485080c80080c2502840b020507248014a40b5403603060504660351192a14000f440c2d10607505c00075400240309031540100035551003d1809604158024801d6480f603030400707800b000d401e001d107001e03918400c881081400c1349034001a1503140181441c8903500d4a0303002145442c0d0000c03800081521159400b0b1000742400c0042e0b81d001e00030b0030002c41c00c2c01c025100e003511400c80000b1101c030b1407480615482c0203 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 819638066 1250 819636816 819636833
    0xe150106050d05151e09061e0904020a050d32031806090402040b0408010b0603012709120c020a0b1305060304051912080106170c0a09080708030408190b0c07 69
    0x5940008180c0c0c50f2420800c10302001141c00d0a0001d07001b0203501012820608003500f060480180341d00071081c100d032403241801341480c0e00070002d036402101440001450384968602e42211405000c0042c42643d940e00105910501c403130740e034200800710b04509d441c000c40110039200c3d1000e80148a94094007042c0000303940307010f1000d06640c031a1000400040c10b2400000420484014100900c030408050040261501092050741c1c0181a05c1c00e00000c8131414161011001c00d04180001d004840e684403440c0001501e0b0049010540340301485c805e46c60711000460040044010b040e1030610880c080c00901100342c42031078080c81020000c1000c0100c2404101307003c440045c620004419603040c0654001072031081c010101d60143e0002c20b0301c0f407240f017100101da00755614400c1a1b0701c40c2d051824480d4001104682001441000414868028000316000f000094011a1150704040c0100e08011140c2600314490400042c0380000407411751203950320800703c1800303a4032900c0e10b0400040 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 819639316 1250 819638066 819638101
    0x70906080f280e030a14180120070e041407060e0103090303060503121213050706050705030c0106080d0201140906062704030305010306060b0309060402121f0e150106050d05 76
    0x1141010844854428000050500070800d591408210454416119103c5c1719181c00e10747d203800d003a003103200310394055448a61040c44112039a5011900350f003445061022640221454100300800d2005200e58049240e00c04491580601070103403501d10007070400c94044e01c0c0d440c145601ca500450034540203611034002010003905a40c548000c1e41600e05040d402220100b8000504001207034501072521050081e0690000040506030300b80072003559550030000c800ca0300ea1000f0810f00003656820300802d0010460301e0b0090840042d811006401d50307130354038240601407842104201d00400d0004410390010800d0760500c0810840c10f100c4403424206008403403140c8010740c144020540d0660055040b24001c400800505407a2004900e1510060303072184418ec1c080c0c00031070003501e0300003d442e1500451004595603034010340b1425455510100391035040c15034a10100a040c802404018a20488008601b01c03640c1002805003035030184818070b101c0075603210000b03100f00800307800c5c07541d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 819640566 1250 819639316 819639391
    0x1090c12051905010905010503011b0806040b060d0903080612160b0a0c080c07150804150f0209030a1a150102070902030c09120d110601051e0406051008070906080f 72
    0x102c03d45c3c6030180303140540001c1c81481d000390303c3c001ca0200203a40d40301608110310401d1703591440c1a150382c401c20010f09894030210364000d00c10020b2007401441d48c4103004100303200307455203161803914008220220702c20075001400e07500008421a4005821180d00d011364100c0c40a1a0300d8840803a01110f004050702070090200780d001410074000e03580026120308a4800182c65894001c0200c0112800c1c60103480045c01051403610941001c02a41c00030300381c0c05000c005c01401c04060b14000f900d4010381c18820f44050a01001d400d208005074122030b075002c03d140080380d4943c0340540000f0754900203442440c070034a50200108041c0e41c070300780854140d05001010f60702e1441d0444695515501020040d03c04641d03120310002a110380802c06234101d4100500b030540c1018a140250340082409102d1342d41309507691004142036888001442801c022075485211a260500010701280e0300d54204030140051802001203141d103054201d9400700c10f032547c0e02c14818407048010703010034105070f002 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 819641816 1250 819640566 819640571
    0x30b130f03021e1f02030a09050607360303080a061508071205010b0a0c0501060b030c1308061302060d182427030c0606030803060901090c120519 64
    0x41415030009400300315007243e99008094040480d102c2d503585a1901080c1c4c0075821107480d80101410903030103558410b246240200c1e00d240c00356605414403404407170301004512072180041844170402001340b115010001e400c5030140254012204059161200a00b0409210300140001c50240c20510040111111036503c4100c00b030009808040d048803a5400a40d000b01c12200141e500c0c013400e0704075814861814603011394508111595110008107490039034a0b14000039000f2510b000451007070240b170070010b484d01440002c0480390a06a4002840795004805100c0080c40d02d03001d0102440e4100c039015500c01040d41c0000c05850324030810380c01c1c0f00400b40540c0c24400d161408003824180c0b6400301403c150300e0003100c411180e1014030003141012a03031484015080341030315541042d001e0b0601c0009600d450341c0f40829108160400c03150b03200044240203450412254003405030464060a01802540c1703a80142440c1d12020302e042c030142c41c5d101090842c0c0b07001c0c0e8a401d8541c40c10406 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 819643066 1250 819641816 819641843
    0x61317070f1103150c13030b09240405030306060717031509010504060b0702100203090d050c010f0801121b090c0503010314191103121c0c031104030b13 67
    0x7450184099400c15140c00000c040c0c0100c1c14500072032440305641c021135100c0d20a40754001017500c01d8210b80c1d052500c0c49442c2c080070002c1a07881e00c2480c0314480550092644c0b101c11100c00041014926040d070011b180d260521000a0300070058a41c040016614a6142c50660600008440b07003180d0301c00038000d002041c000c048160804441c0114002c1e50000c0030b50340c0c0d901c2400704840c16441801e5011009219107401898600703990701c118184c510440781040031031070018600d01407656007160207600c0b80e800c68942d560441013440c148912800d200200c4c0d80340140b800120380494100504d003a03602281d0b03450b0b01c40d110541da405032141103810059241c0803540508503038000c1c0000d48030540044c408070b0b088240024118081390144d55104c0c07034620b0955643ca04ca014a00f01e01f54180144210804036500a1010300315204022884850710305e40036a2120440c0c90b60400341d010142801080b5041d18825012035003200e5010002c2e04446d61a04441140c4100c1403e00401c0085030000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 819644316 1250 819643066 819643073
    0x90a092703052b09060c030605100e010e0f0301140712052701270212030405011e090e070302031e01060f0f0302071a0105101e110c030a06151706131707 67
    0x148114448030303141023005c1501d90081040d814840b104610000c2c0701c0d04944006948505060000704070084e24022140b0310303401c0080d00356407030f003224030a01c1ea06038010068416881100c4840120740420100514281805241d40303525a84901c0c200d070a072010f0408241e590258804440103800004450b00701c0014910500d125052440c146e1042c40b103200c41c00d84468000c0102c40450b80c050711001d000140500740f2542c114042c18441041c05034100002400301e40d07009840d072003210544d0b001070351b03880c0140c0388003914800145205440f20145005001c0150030242c560380f1a0a40c0c01d01e00707010506410114003a10404600600608801e035078500c000c800f115840d4140e500465650b19001c01b40f44d4221590b110150000c40a40c0c401e50241021071f0007100c6074151035200d0340070340e001041420040b03481c02c0c2c41600c0c02c451490f5980c491a01000340715084002409500c041c43c1403102c040703100c460b0346607406040f40340700da42040c8038602000400c1d070200c03004000d0f42c580d031510f8107494107 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 819645566 1250 819644316 819644321
    0x702030604290a060513060f060c02030703080703020a060f0b10030e01060b0c07030303050f040b060f06040510080702010501060c020a0308031005031504060c050405090a050705090a092703052b0906 87
    0x205d040d029401144140c0100e18460240100391031820050010540c6000c0086034602c0558409076054041e511b80030000c181181c00401b00140650000c00c0c404c1180e14060302120303895045101d2080ca0701c04540d03a55511385403400c0c181101803501041c00c06411003168014844c40d400120074400004810900d00400304421b401c41c1e002c2d440800c207560b00ca0601c058902811a0300900d01d0b091000040d006150220903040d0808024116a0816488101055414882d00d004802040381c020030402d003075509002d058054002c43c82e10000d44041c03030340030a0a01741303203000003040b1010100008030110030041c2d40d5070003001c2c024210342c1018060700040054a030151402c1da65241008012078040d40100210b40171147d01501c03818082e030f217041000d401098042d085504000e4108040340755a5165030140c03016010741000051914075800719200c165100e0803400f20b00000c0c0049160103e50001c00355840907400510401d01d0316528164074540218078500c1220355850090414203000c1c01c0d5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 819646816 1250 819645566 819645569
    0xa090216031d0a0305210f0403081602100302090a050406141c0b0123010305072705040e07170625020f061509090f0c0d081c200702030604290a06 64
    0x140b0100500481d403504071b20540c484da056902854104002c1000056a00340c010062041004d60040c00b603246640020100d002080304000001d030040351448040c580b2440410050900b11000c0002c82e107403660000038042e621921510802c030403203c651401c1c0580000900044c1d00c69941d041a68464a03000c0400c00c080b042141419108040c04000e035020b8802c0e54011003d41e1900060350000b100861841c100c000620b05802101310030004e0240c4039402911a42d6804078054152a03090030780805072010981032280b0140d10403400e00c01c85855401000b240070880c3d00102000701b00c40c9105a150164100e041c803030501c06c2d0001c00c044030743c18058100001c041268545c840781c8910000c41e6a9182c0c88107170300000c3d005205400c5051804441d440d9030148555101418400380d510042074008500000c03500c0a61500f0b444080800b20051140c0d4a40901c0d0089040c130700f0580100b40e941400030b00007490940350303881009500140880800d41301c1c140d05201d203050f16100c4011000382145 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 819648066 1250 819646816 819646843
    0x3100c0206130c0b0d0209120304080c0604183c050f040b01060503060d020604080a0201020c01050c0604060f1b020a02090702010911150c12090a090216031d0a0305 72
    0x450020036048440e078500e02d0a21074002c814030f00a03600b01000031400350301401c1380b8088140d003004691a151100800326540c40d0099010315121858111800e00b014500c204c414070413a420401400507196400c11809290580c840c0043c2c0e141007007041c0c04641c803044c0010b17400071501d144070441148600c3c2d0403034150381050100f071040b5180c0420749442144155002010700d0080b01c01400014030503000b8507403001000300079203040e0720990046065540300e60000b40454019280301019941c0400040740160820310b44a0f1030001c3c0d103400c2c00e481d440080d0006026588800302c1c0489040320350426402c014405079504070200c0c420001a58881c60070000b28020640800047c107210b00601c203003440a0782083c159003841123404108030701c4400500540c010b4000911071800300e004100710f202b90100c2e807549190b6030340c0540740c10000c45995030f50080400c40c0c01045012100c3c450040c4002c0d210764541480c0d152102280c0c10110b1050818540e250055502c00000003400700004c2c800008808 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 819649316 1250 819648066 819648073
    0x1603140f0403050d09030210181a0301030b070207210303110d0b03010605030105071706062808131502031e0c0703030510050f060d15062016140d0203100c02 69
    0x4036813040d10f840c183c0e848042d50185e80d02c5da0303109140703010318040051400200c20789640651644811848500b110125036150603002c03005004000000c3c41280e0030840ca070009207651890a040030340314034008c00380341d509401014040c1d002c0600940000c032030248511a042d03210402d640b204401000b280302518807a600b00007000500c2c0c1010710440b4010180d130307a2100c801d61740b2031400303414090300a021940c2004c400c0140030140c1200d04c01f40201d01032aa00000d0380c1d81e02d2800e0041c12601c0203000e881c1d4489484901000150351114148400140c0210260b103a95a520480035006400384000050708840c60401c100300001a0040240900c039407000c03c9141c446080d94402c166040c00703403a400298051a000c2d07146021740103090090607040011482c00d41c480c50058609000e0f0307000c040401c400071401d00c0c1012801c0091740344000d500c002841c01070358500b00c18440c0407140c4680155003190b0320322070425894889061240703c0d0050100d40003010b030b0740304134070023407942c2d4004000500 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 819650566 1250 819649316 819649333
    0xc0c09040206030a18060c050a090b0a0f1d040e240411041e0f05011701050f0610050c0105010f03060b090c09100e04090f060e0f031603140f040305 65
    0x24062048500454014060a085594000c43c1c1d030000e1060600c5007a1030b19611028800150075805003080c402c24a43d58a501e44003913030809031079440550800c200f094400c6c03111000b2294088501c99910045203040241d0341190b21004c0c0410140c440c0c09900103003418419800064001244031084000904491045601501800c0008820360340280701c40000c000c0c401503441e0a0300300d0404901e84c40c80d81c1c030708555450368540c203d44580100c1c840c1c8079203810040018103508055505142c828200a12080c40c00301910100620000c082600c00d180c1e4030701c5502014411303420f891507106050001c000b6541c541402c0740704400d003444200d071002d0914150326120b0614400141c002d40b0325011003801d2030040701c104555640c12000c95003c0001c440d280300c609903103a000300648280114010340700f8841074101842941e13003d202d6040a40d0015103412404480001203900d1034170900b9400250103640d10341101c10030002c00d0600d08403000420000c40d40280c444c024030440340726008440b600c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 819651816 1250 819650566 819650569
    0x80f0a0b06060a140306030c0901090c0801090506101409060703170106020a0c270c121401060c020d1b080706120603020108040605091203070f110109020307031410050c0c0c 76
    0xa02c5030b0040c0c00000b500d004801c0700071301e1520025580007203004094a106a0750800400c10060090780300c0c007185500c4e01201e448403600011010301501500005100743d14282021510795161480c01c5010007205803013016080e1013641c16102100b01c01401e159403881c450600405003000c2010f0512000907000001848500001d13155510a81c04039598205603d44000054003180049006100e00c00c5405041600b404910a1700714500954403010344441c0d113202094122010808200c081041c01070050084541140303081002640c101ca030904034180d2881c0c6820259603030f030216101d10341030003804200c0319070110305102910116510b0707880d00300242d003810003a20940d10010380807460324070101e00414055005a6403019030402114a801802500354491742e208540840c000750074500c0c0c01e450194008d400c140b8046041c1c0c000d0048120540021352034642c14800148098480780d40959440814800901d020045840411592400030700c0c0865a0744954407840c20350150140c25402c5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 819653066 1250 819651816 819651829
    0x110603040201121b030e2e0b10120518060a2a1707020102042103051605010b0112020405060a0324030b01090c030e0c0f0402040305070b04030528080a09080f0a0b06 72
    0x503c414051f01900403000340200b42c1c15035a900017100c1e152210100840e039120002011030a2503250342d1039241064110605003240c3c0081c12038010601030b40e02c2541300c110700042564000510010008048050960405030000000741268a907000c040c2c200a54075004100b281c0340e91215959011140c0d0342c014101c1c00c0b441107001d1850029042605882584044910200d003030b4420b04115240401e0a55902c0c0c110003483c00864041c0c0d100c40e462100ca5134098840c0f0400074250209500701070408001035150300940d2900030030940d0300c1e6260025021100e8800c0003104504030060308154aa0802d1030759440c090044101d01820110380d480402e2180c46030b000f2040340c1c580074141c040e510000f0422118400c400c125403240d0244004000b040c801e10a4030300500041142690b19441e52502904040149154181304085810350101100707211890b401001d5010b0502c2d9500c1041e0201518801c099400446151082d00341c914040040000c140f105d150184407080c400d99143c1e01040030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 819654316 1250 819653066 819653083
    0x2040e01080a05060f040312020309100f060302010e090703021908060301140106020d0c020312040e04110303070c0308030a02120106030203240307051908060903070c0b0304110603040201121b030e 86
    0x40c1c0d80c025000100700c005004175540d0800d101e440c20031019040022190140d802c1075515090540210100c50402c00c07040c411000180d100640074403516185030000b0f8910b8101c018601c1c0a503060400003180f181c4650304a4124840b0720003403420144000030002c044031011520540a90702e0584125200300d402c41c895412194168000c044640302e146089a203001010f80c2241c0512407803402c0044400c1c004058005441c1c1a2030038045858030b81081c111114440c41e0890183c3c20400016012902c4c900c1c4401c1540d1f005100d550740e0380c0b90030411400034860f4500d07441061000000209070154141c0003103001e0081c0034071148540e44010b030310a03031708148aa03025901d40e20648c801c00c80303410007060f201041c071141200110000d079517501080c01e1200440b43d103250360300002481410882c694250700091308041181904600c0c103a9624400e010f07030404118403454001c000a4116840f407171550400b002429014040011407925060540d0000300c110004a424040c0c0002c0343c1c0c20001e504030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 819655566 1250 819654316 819654323
    0xf150308180901180f1413020906240309030d02030403120e16170307020307060c120801080316110a170f030c06040201030b0a0f080d030c020c03150c0d06080102040e01080a 76
    0xc0841c080b580501004040d845d00b1105000d40369102203207903003c428103152082040b008141881441032040041001004044920030886007402da0315048035490141c06100c00d80541a969841c1c6c01e02c040c0c0b56000d440f4804c0c8030ba500000c00c01c0105640314038040c8240a1821003404980a9203e60075250000071000102c414078a0030204240041d10741070502d14641c103000e803854410245c000c00e00348a126000a400300f000540d00108102800c00c03c0b020920581c41c10749141c0d414000c2d09612440b4080b84204113020b44030f403800511407003c10060340c520000b440001001c0da40d20500808101100c61b44980d0701414110915040012046a400c0c00810010b850145e035540e0040d0014140207500b2904285800c8000c1068114144454003411899005100c4e04441e40c90042c140e0349403030500746c1150000d4110b141591400105d49402010f80c2080d41ea0355601c0040d84e48540c0155030b80c1c0400c0a0401c00000340d90741041d0b0080040d180016407048803681c0300c1310304668408d0fa110009 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 819656816 1250 819655566 819655589
    0x90606030b0f0603060105040503032a0a170a050408010c02060109060902090102060a0e01060e040b0910110a14161b140d0b0603070b07140c030d120f150308180901 72
    0x41c1d500e03107008802117903c407405040903400c0c42d0700c42010901d55000f50368001041001e41642d0408401c2c1840818020850030000f01040c49141d03550055a1101000f0101131080c003207000192540030300c042c1d5020380008002002121000840259522005c0c8030b076019061512001040380c1e28280200c0700c000e441a0010103041d110b5030a110300804030800310383e006540c0c1e41e070041040d5111031a801d0003107010f0b01c3d4903919400c09210700390603c2c20000b00f50140c10719180040001096020a542e80140fa40c10415040031850b80486943d01c104200c0c85900d0765120f41c0ca50400c4180400d130f02c2084801c810f081d100b103403941100403140714104501c540c81911010040005208611016407040700a0156a802035592056240540140204864510340b074888429030100400503400380c110100d0060080410102010301203161031301443c0c0d072240e12285c6551003856107411254500e480404080b030810340c2d03801d0030241d641220181502c80ca0244d104480f20745410f440f00d031f0581e50307038001c034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 819658066 1250 819656816 819656839
    0x2c03040b090303070c120b1311041505150706060f0503060c0c0c090c0316082202010207030b0403030509120903100c12061502010b0111300f04090606030b 68
    0x98905500840702150341407204011000c00507542d12030308401001840320803030100200703190501103034400901003d02e1f0220615100c0c0400c13003500d103014400d0002c3e2800142e50160003041a04040c3d140c100680040f035203d20710070040160001002014001c2d02e041040c02d845e410b1020135800729100e02ea034180c2c001404180401c40d00d00081c24185184c0044510342142c44021800403001120a00000710b008001c01000a50185201d035155a980c50400300903d0109407000c40400f032310444103010030b40e07004001c0859000308900b01c00b0b15046001c1d0300c40b62801e403500801a000460340f1890900820000c0d00e584e1040c0310907504c1448000300075200080da241c43d0b02004000c0382c0c40080030801409180200554240300d288054840f8100c044036500020f000a03013550180390140e810003891410b040b045041c0411121000b0040000342640d12002d05802c02c0e456002c021212107480c030006040380c032190010010011500007100030301801d5503880050b01202c1c0045062a001b070701000b81d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 819659316 1250 819658066 819658079
    0x10e0108090604030e311a0a0e060f0d080a1b050a02101710080c031f020a0903120305010f0f0e0708091f0f0b0607080417030f0703032c0304 62
    0x3245e81e03080201429a0321001340060b1200483d14582400e18010b41c0340588601030014a40210018440202c0d98504050000c1011601c00f101e184590021464001c0c0030070620b0351500740d541020040144501012051400d010b0019408070391070340041110700880d4007114100c0d43c1a4172801d81c0110207460369030391756004d0042102c0205c036944100101105201c1030341c1541010030707000d611a00750071440d050900c96854904100003103200d2299011f441c550040e2003007058208039010b0000d82c003603207545000e0802e980a1056420091150180c0d03100d11f41001d80c503911203812551848000182965070700d40803c1e010460b40502080c2900c400c00080d1214020400150840c01403002c84041102d03102d6070500100c086200741e03081c00d07211200700b44510410701410311ba8003022196186841455503036034009104a05c250807054488802c4880f84000910541d031a0300405184196038035950b10b00100289178090340403440c51607448054048103c4d9000c0d00062940030001189800c7c200503 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 819660566 1250 819659316 819659327
    0x2060c070305190206060a08010e0a152d0b010e010c030507031106090d02010e1903080a06090213090c020a0c12021c21030b0904030c110d11010e010809060403 70
    0x4007601071190030452840d145000012214442001c1c0c0d0291009050190402034445126800040140e0502e140704042c1070011500c009001d034010401550a500584d0075000340006070b0008000c170f004825a02d41c440001096001100078244041290809110056030204441444c4900181300c00008074000783c0524014044940241060204080c420144500e0b10b8011200303c030711904441d10340341d29280c090041100c40081600500031204290301e809618501140028003000104070100744400c0301503101001810b6801015582c070200c8070300c034200042c1c0700e1091b2000d013498101c0144074103101295110519600841a460851030b05070301004800700a6001d0344c0c03001801c08000302c2d514a400d010034505102c1c8000d4010b801c15643c0d030b0748010b003c0c1300150061508005c00303c491580d40d10074195001e941400c20034040c0c0100d042100f01c00b058218020707044004001c440c400d200d186242402e0412003680da8690800c003d40044406000544445200d5804000440d00081c002c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 819661816 1250 819660566 819660577
    0x28020a05030f1512010c02010e3c0307121706010816020106050306240616060c03060314070905130206030c0901020f0307031d010807021b06041a03011805040302060c 73
    0xc41039010741c243c0e480080c083d02085484007115a554014001c07030f2030780a0141001d01070002000e44000700024804800e1801c1403445d80c11843c480c203005204d00000054004032010304d000c2103e807160124503182107801701d03824800e00441cac8040c0203062065804a80c81d0b120ba03a06954440c51510303101b80c1e0b00916000c0080401c1555200c1e8004951038500300000c0b40b144415080418000901c5280c0d00e0814103868030f00c500586081040d04900000344510304e114035846040090440c071064411801061207400c01800340c170f0b44280c0300f5081c160000746581507034004141000340351980c1786603280844e910340d4001e401800500000d4601d15004d03000d40302c50343c418015a002c070141880c0f184c0c203540c80003804030085881100c00f01981c00c9080c00100f000b0b042820b160031281820580030303540e4088840d2103404e00003842d030000d8031502c1d140b0a0381e00600c1c080041001816524a070b40c51940c00900400e9a4841d0803040e10b90708450794020340e03004907010b070045c0100d611540d404e1304c0c0380e5010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 819663066 1250 819661816 819661831
    0x150d030c021c0b160309050a030f09030803070309060b010201020c1015090608030d06050f090a18080406020c0102060c0406050708070303183917100528020a05030f 72
    0xc424415816204200c001c02550f0700c6120b9080003031034111106903042c0651119035080600c0c12042200184000483d80f000c5074160410141250341e014044803201d007281c0006080000c0401403164654154011140f4188110401c0c07120301e4a90300120308034010640a160305510000b0f114035000295400349034101860410501d110741c03149144400d0f5041c036848289181c3c1300041d0f80841d038190713100751805440100ca0484c100152040015010301000d011010081d0756284201c18400740e8002850306954000c980c1900c2d15625440651943c1e0303500c0300c09025004500004403020b8800c2c08072025144a901c0700d906102081d11108895001414210107040e0744041118041020f29a41d00b4014443d09a800c3d00d05594556650000900c0d001c030b070003845801c1d029801c0d2904168140c015500c40c081c0c0201101d4503031004500d800d55100320f072540075240c807044c44500020342c04100c03491040300c0d010700d006000100360b48081344958151000050001d0010a0402c0c01440711150403405 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 819664316 1250 819663066 819663079
    0xa0509040203040807030906020625030207020904080a03061a0304320a0303060501030b130c2001090309050306040323120f0711070f09150f06090e150d030c02 70
    0x69202040c126401038400703803035500300482c00d001003591210000000e400140b02420075820440095800008000c0718040007526500000507158030030350503201510f400420b03401181c00d10f4103040c2d105902c500109400070342411004907080b0307510416201090103a00c11540b40d6942d40e1a02c0c4046000c618000c1803000c01c0d841121292001581ca104200400f0005032081c10028580603040740e035144e100c03906150401c010810103503503514098004512022001c0382c6444501811a03680300c820301c266000e0840c0c0e5800400c1d5080540c0100703401380c4a6182d000556484004042c0d4405040360001c0008440d0b0149031448051845001010014000094100040c1c3d9550070081001107075251410101da20400524540c4041307580b40300300769200035112090a11194045014840c082c2c940c8858466182d41400032494207508010030541c14020784998840c0002840840300f8460800d95140000100e1803250420744c042180420042980c80d2000541c1d505882100241c00103982c08507 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 819665566 1250 819664316 819664327
    0x204050709120506011d011401120b180406110c0604060e0312071e0e15070c050301021b060c130e0406060801060603060f2405070c030c030326100b0a05 67
    0xd4400d007100b036442003014141960400101c4a00120419010400121410300400c6403ca00c0700000b100d8000038a0014040b02c030302900d08019200d4000c2054015484202c0c9041a440603c1c46901070361282d002407007554091140c0360060700500b0349030041074000354082000105076601c04080c07100080f00340c904210b01804c43c1008400300700c07900c8010030307940024100c00c0d1012540d1010011060308088048115400208400506584800103550800500c0500b1311400311440001014010000e550703900d00b40c10141c030801d001d4174100c407a1740325681c00b1940c010700c080f0550f1070049040c58030342e1810f840e04580c80d06450b00a0030a032401c503924980851600300c28000d00020704100e443c0070944619000544c0c1e451a1a64004580891141d000d1034884c14a60110050081c080c03800949808142c103002080b1100d9500013462001e40d60000020560020844446060600346d0f0007002039010341d41c1c0c0100c0708102d070640e441c903401d0703072080c01b078420900003500074010645851030500c1c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 819666816 1250 819665566 819665579
    0x1e0302030d090302040e060c0f0901030209034c050705070606141504030c0506071401021201050f0f030d11010b0d0b0603160f12060906020d05011e030f0204050709 72
    0x3001e1058000c001000c0e20420320035420305014548580c120729006210b545072858049600c0c0c018101ca0000940b00040c400803180c0c4250161118004d0007000d64001001c0c0300d88070400551400103040544400311054070a0381d00f80d42400040080c0e13290703841c078240e04080d00c020042500a0400f0f0902000b841a400891858402d07007010f41840c0d100d502443d041241001035181e81c0352001e9a8080c4104401d0000076624101ca5007280c5c029200b20f074032030710340b45041c0a4404e000240c0d034440798404a000304003801010340540c100e9401742e4400400d41d1381174050011010041e601c2c40e400d940400c41e50403109200c2c41c42802114000b40c00000c0300311000f0002044013034a8502a07558900c240706110a515090142e0041442c0301c03008845142d2504038401d41c550198070680721012240f070595001d01410b07812480601d03500c0242103660385c194a29000040c1800c0c0500c04a02d640c030640720441081e0182d4600589822004520b00a5159030030031010f0324008000e0303c2040601600000c45 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 819668066 1250 819666816 819666823
    0xe040c05010819050406140a090201271a090a050103060602060f1f0b0d111e03070c0b010b0715061a091206180f012703110f0c0108010e0f011e030203 66
    0x8a01c184008a007840741c0c044102401a000703801c22310301c5882d100301000140e070414101c51613400020020301208031001c0e65135080200d82c0d40440594241300d14a280d038010303000001e040b01c1104503021600706486100440440b4024010304015074490400b0030b20700c444e05203245038003440a80d001003159010000045141281d80e014941d42940460300609a403c03d02403540c032911840f4000781804201d02a09104142425455048003c008003203800d26108840003001030390031052056a6594a51481545e42e0010f041911000c80c079030f00f01e814843c10f83c0225801c40700c503071042200d18802c0000108a0f80d00120011760f22003112000440b1480c814000144a41005504180a80b0182d402c2904041b000500d561b156490300c1c05000d04031048108030001e41e40b40c40c403c008821750600d81543c0030294114200344900c03c0705182c20a03000300040550080200f80c0c1c50a195903a05e040c6100319003c290368440704122018014020000d106202c034000800040c034059186682e900800d04 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 819669316 1250 819668066 819668071
    0x6020c03040602071a090918012c0109050705060d020720190e0a0e0a06061502070f120609022803300f02010e250e040c0501081905 58
    0x8240c0c0020a0410555406002ca40c3c01040841c1207250380741c1c600c2c01414503e2203040171051244003c1e00100b100402164565901d05695100800c01031078076180700421b4496400d00030303e00b860240d80500c0c1127207060144100460b404001404910b09040800c001504003451000c4859400d000c26008225884407080040d40101c3c40b21520b10a4502445166402c02b81e140410020408007000621721081809034004c1c00410001740955185075058108001c0034400f8081c40d00300403012400c68030300703000401c01403850303000c40700d0482da51440c1c00031608440c0305d0b880b480114412282e0108013580c2103411424070040400da03000031084c03050383d24007a0022404040c100c84a10520410810350380007405a8102003603404c03078880e0440038880080000120a080003410580601658000d4101d460402e110800b52035a14400010b0104100341d44a10101210391940c00000c1c00041c00032014081d80c2c01c804400085400c001c0107445442d4080c00b60700710500c2e005103d0f0100406441410f0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 819670566 1250 819669316 819669337
    0x14030a0b150108091f0c17041a0a06060804110d120305041203020c031b1f05061021150b1b010e0610090902060c250e010e1801090602 59
    0x2501c0805103000140a090000c00410340c0f5409402804c0088032010300c0c0c0c802e0717003245a0022481e4845006c00b1520b580d083c800811a10343d03040e051108110021a4203407182d8800814000303640c0e2203c03030f1035058070020301c00c5001042510011a02044d030000c00c00c81c26800c00351410b81800290b95641e10144900510040000e581d00144000c103d0092501c01d040100703403030113506040c10840b01541324440c5c85200c0703110b41089100c3c518a00c1080c0010300c10603101403180c0640650944040020701030032607030740c3c2c840c4500440c403a980e00c0c051b000815882151192181840d005401c040008001c10038290001088405000a2840070071000745201480100c1c40a940c40900381f042e400d6604440140c80244c001800b0010341056041a07902101da03541000f1414181c1400440d542e403140041030030460080c0c120a00c02c80412100e85500c10075080810005140c5c1d402e0181080c2c402070040e0b8000450280c0441e180401e10f90681c085d00c031144000040000d01c981c3c400c0101d078071101d1203d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 819671816 1250 819670566 819670591
    0x150616080316080108211b100209010305060402031e071218140d08241905030d0309020303090d1b0306060f0b04050d171e0301030606170714030a0b 65
    0xd40c0b81d40150021300415110f4001c1c01110038103a04003001019014020b4075001c00840c80300f103491065130500c0702100da004183c40b40284082030305400781d4040a4a10b020a0070400405d040f420b1a00c05c40c0c0c4680e845603404041c420103000784010310b01c40075041e04100300d61100008031014080c0300b00c109420152208582c1c0001501e80758543d64030b00b48082040742c200d03c200b40c41c89a0080c07815940400e008040300c06034000306011000902c4090398058001c0ca01c5010460700c03050b0680b03103100340c80085085841240c031600c41241600c0082000030b4042e04240013203c00740c1002040c507680c0034400c1c80d5094400314401078090010a043d842601d260b42c4500c0100f00400150b03042401030801d08022034a00760611003c031700c83e40c00c0104020303d0507003100c4421300010a00d2044d11000514540c105035030400f8001c83c0c502e950400e0000f50f0380a490a000003c188080441c00b1000c0b00005010f0141c0c0c528190542c1202011b0f4140766030140207130410400010340c1200254070031126900c91 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 819673066 1250 819671816 819671851
    0xa0203040e06030109030c1104020c0f10110c12340201030b0a03020105040b030c040512070e01050f0d060b010203040b280e130f150314010c03051506160803 69
    0x188100070140c100c074040d034581040d4a0100c1e920822903a221500981004007042c040d03400315001b4451486180e105006d0b41d0001c0103013002c0411280c030039240c4c402c800d1112624a034201441c91227480748100c465440002e0b050010394080c4003034005030048075165408028407012402600307000b01e40c04031040c0c040b1240c0301c00b1981c062289281e021015642c0351601401d40d40082d080d84168020f0410201011000600c8142c400c01110b014045c040d0120701d880411102c860340d55049409403400706940c2d00c001045900348003681011052000702680e04c1c12416403240c0c00185600c0d44600c0c1103000805c008078030003103100300820f20b02c1c003a41410001c0040030000e05030040306451000c810401000b014071455074400b4a42c0000318218440010403490000803507000308407100350348011489000d000024021812140500c01c0c0100f0001e001c40074001c039048003100c00495034114001c60110084145040900240510703143c0092101950314031516131500641080340c840020b001048603 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 819674316 1250 819673066 819673079
    0x402030906040615270b2101050a021602010f0c0813080f0d0c030503250903140a05030d09030c020402040e180316140c0414010f1e14150a020304 64
    0x403454444e456007210150035040529125100d4022038880260b241e610741d01050820040c0c0c880411650b004014214007150000044065140307084803003659441c110000308046000d0084840c0d2640c00314502c2c100c0d030030340c1e07005540c4443c00b854010100120210a0400103485800070110260001454001d2526001545160038009000c2d241540c00c000001c000b0160403069219005903d42051522079a40c07a5012903401d149030142c0001c0f01c64142c2101c03002d90085181010380c0e0240320b900d583c400013001d61541d60108840001c105605c1085905103501c00c41e030100303083c1442031500c00000384d810b0300002c080c0d800c00d4200c0350104170860f0a014501c250b030022968122001130241d801c18042c150110070808512001a0110180d13400b5038240610034041d4202d0307050000c1007004032031600c000440941000340203d0804036542c1c0404190742c06042443c9d1511168050510521400c00e0500c2403240d52800c0784ea600501e000c07514030b00d90391400c0b020700b088a030b681c3e0046031603a10b0882d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 819675566 1250 819674316 819674321
    0x120a0203090c0a050a210b0408132108030a11040305030a03060e040308042022060803120a020c030c0f0604020405060402070f2003010e011a0922030e04020309060406 73
    0x41c0000c1c45906001c030201302c0f60b111100c214003128821510b0440004880c208038007401d004550080000c01410b00300000c1040c844040c08070072801040f0f42242c980c0f07c0648000032070842041d42078440c0001803460016440304015540300e150707a900840d021b0139104004020360055002141c09410200340c5000c0c441d81845a48014508452804030a0800e6100940700900241c00505915040018140c9140508a40080c0f0080144c14021a40d14405c41c01208505a09425030f816040c810006101c5d0030020545c0c060070200c05546101e901d038004103000a51019450021500041c85050281501800700042c0904081e0107032481d0301d010710401040340e500400d8103204520500a47c404595584030040d030f041d034031910038441240010108007407a8003c10044e545036081208499008038190824146903200ba4072140703903040004200615400304443c281442e4078054024228454070729038240b0b0840c000c2c100480400751540101e8140e030f20842d00c00d00180e104c44140010050b00f072 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 819676816 1250 819675566 819675583
    0x41203050d05090c130b060906030109020702130b100e03070305030705060a0b1516050c0909010605090901110a260f090f0a0b061302040806130209070e090c0f120a020309 75
    0x158040c0c1340003d110310010b25100159100c40e00d446980341c403521540d880d40d00c200c80305a107008140070b03107039a95401e0000180d4001d610490140301d02c0240c00e1544043c0e0b002d5043c1044c0700410f1450208543e100803a41c04604c1081c0661501c45c1c01400008201d040c00141016170050f005131a8520b0121514000d880d0700303060681c0182500c2640aa2041806050703804d030162680204801c034a850900a28107943c1d030418613401821a806c2c030107401c4055001c0710481c4c005450740c080070782d15541d22508a81d002200b03440c0c030300780800550400d18441c124440c0704a924500541c94140015030100300000d0482e10740080d0800403007841481d4804102c8624140c48000040418042903500e1215404028008034060a41e6050450010b00e091301920003070414070048034440e00d0010082c0c8900c1c0c0c1c0c04901070340114610004220030714496048002428809000b030100da072900c1c10000840e5205408480c81ca45007402200f4448584003900741c050002e50801503100d013008909a42400c2c40c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 819678066 1250 819676816 819676831
    0x2104052409070b0f09040c030f27020d0302030c01050403050d050c0c0709051b07150c090b0304030c1a07030b0f0d1e020d05062a0307020a0b060105041203050d05 71
    0x81100300004400300081e5081540d02e00d2030a1a00e84101c001c808180d8014002920746c468141100805044c0d4182d00241201c5c2c0c280b4814448810303070810800d03548140c0e4003207105040d02041c1800160800661030081da500c21700c112407428850300c242500f116005e40c2e044000940020340218094414000d07160000d01c246029880d000d00001c2403560b0b00f1061061111303003a2a4400980d03000b50369000b0000305070089585e49d90300d105500e01511195a1040b0001c0b4207440d002546004c03622031150802500d450f6403405144d0703250354400351840c002c120f000300e134007a40c1007801800103445072650074003542c4a030302c3c042044980f420800c4011003851103c0c40c0208500100c0c2404154921104841d014001c00400c0c5000300c14004240d0281c6c00d48400b902504c1524203009a4010350344013420b0804955101c1c00c1c04500c0a12055043e20060b544000113a10100c0e4001c040743e11407030743c9138111005040052911f51344a40300145544020303002c0e0085407000c00d194814203468002c0540c008030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 819679316 1250 819678066 819678133
    0x31509011a0702240708071505010308070b0c090a0e1b030c2508040305060f061518010c0605070518040501030b2802031008011b050f210405 62
    0x410030000741c514040e0480c0644101c60b08000e00c40218601480c244030b40507032440c200c1ea02e040504140c461544480811114440c8030034240c1c0b004c180c217214081c180c1c0d074081100c5140034110f8481c894240809815404060030030030a0034404e95411980ca8020715104058883c64a043c00f0302c10901c0ca8034000300220000c007002000341c4c1300482d10440b030803010148100540b83c2000f9400c041050070021008005c840000f03804070a2040000f0054450100c843c0c458496035603240c00e202058205808142050505000761036480380440c401188141c0103241170754510280340c0310303081602c0090b20b055011450000b40624941c80301e0088140c07000040cbe60511540d4074640d00c0a0541c400182021540c210380800090b0051401c0300201d444040800203640b0781c00c00c14040c03081403603c3d06ca000c0e0950b180445c004a1380100203404582100c5513140d075410100c9141140103154003d0742042c0000c0d00c5c5c4152546190742e20142c00d405540600000c3c00c0040207060180440e5000d034110038803801 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 819680566 1250 819679316 819679349
    0x5010f03270312020d020c0717060c1c0903181202060a0807120e0705120f100e2136040209040207020d15050115080105060f0c0303150901 61
    0x22441e1224251209541c40c03103a11211581403c40d4000140b00000c140d03940001825010072032950050003040182038241c411055544680c1e5825462801841410f40c102c400059113a0341d825024082c00428854440c0003800e80c484a102111502c1408070b01056000c2280180e08450000c04400b80041d01e41100a00c8401c1c0c0001303141d40143c54900b81040101c0000501591054484083c80f4025817800d04c442403c99166a031540d0043c040d290040d810780070100d031030440000340a0480c01406018280a00c1100d610002a003080140c00300c040c0301d107144030f411503001c4a61002c0b400680c0800321380c40345000c0c04a05039400c1c05610807003018180140051000c00c10b40744164045004607001a81d03100444040382c00382c0113400c000303580040084404c105011100c0d66005c51440d22050410490380c80e440700400b00b5251500740400101c00a00500c01030070454010080398200c13071603060404030500e170002c0c0b0790381c0101e030700b4005080f44480201060030301d4100d950240a03007014290040 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 819681816 1250 819680566 819680591
    0x2809140609060f0a1403040501020a030c05090d1b0510020609120406050a0305042d05010f2309010204080106060c030207050a0b0f070c0302060408010b010905030a03080112030201020d02031005010f03 88
    0x5003c0c25540000c0e030400043c580c1111030040030122a01e48201070b181303489140c5428064001d420140c1c003c4013007401d0041c07098030f5610400895003402d000820381100f5048030f4030b90f0031883c480c008000d0844400703403a0202c0d1603036420428440654566004000901e40740c12010308042c500300e1b600d1000c403400d200900c01c49400406440382c160051400042d00d64a40c107020080100d2440101c400c0c4071b055091010f03075840c60b240c2111080c0903100030f0040d581540b044004a4071402c009502000d4001c3c4402500700ca0f0b146402d03000762101d0000b504140d01d44040034215141e83d40030002090841800303000f050f4061044074010813084850030306e102d01e00300d8240b00354030980441a0444c140082c0b000c00300b0606c03040c4007001d541c0140465460f56201c00e40301d4000d0000340c411502246401d88005000e10300001e24034005945641d034802c040e440c00861800c8000e041e80c048003955000e02409201b2041c5101540c8503030f2104462a400c10701c1c18001400e40310048000d0002c041c180650f54954 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 819683066 1250 819681816 819681829
    0x30207030b0a0908040605030106180510030c1404080f1e030d050703140a05012912041a0708040228050609040605040501030c05030f060411062809140609 68
    0xc698000101c40900d50700c42100000900d80d40c0c0e801082440d004c02d0100e00240e1000185058441540b02c1590958410440c10030f00c0382e5a220740e9a000d0302e070402400c8c406100c5e0700245440507590074031118041001044031030340e0b000358109024650000a00740c9109401304858840a0207101442031a154003a80068030303407281d00c569078000d54541011031810341c4240c1c0f0000001d503044020301650304210341405c000e48028442e104000e81c1600c03100c0508000516450518100c0000d1140b40107080d00b404c104c0c0420080045c0c81c0c40004c0b607010600785600300b52683c0301b06055520244240745c01e01c10424003c14103405200020f0b1407003a058080c4001054280075204c085800703c1d16850600001000b8001540207942c00c1420140000b041003220501401621401c400f60b030406a16007404a644100444020307200910b01d466002c09820040c0080042d40c00c6908000c03238600b512002c41c0301d03c0b0881c5d04a00c0004e81c4401342081207440400d01d01014500448045192045250010300c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 819684316 1250 819683066 819683069
    0x109020103110f160c120c09050619120c050a1203080717181006090203090c06071e061d0a0c15051b03040f03051f090c0b0306030c091918030207 64
    0x10450a2450542c0900000c5c03078807030000f02009501002104201d14100001900b10302c6049070703140c100008980340e4034240002001000e80c441e0381061142c42c002c408440d00c2c28410082e1228421500041100c1d101d0f0b038802c0f00544940481907680000500e802404118020884400c100e85442041e440080260a090700b1100c00f40000c2000c0a0456501e42015182c00c0c00440c002c1c50403000140c82a030f10303006148100042d800340c1c3d51710020101401468400c10400401c01d01000300c801d08a402d00000104a02c0c1c003c50000541260929410645203180301d140b5a032507002008a004010744459000d010f8503d2403c6109500500030b800b9100b4001e191480d80f4a54a183c11000846070030400c0d600200020018107441c0c0d50340341445030320380b00710b0507030b21240d20620241c01c1e520b801e480c026040c0c001e0784012444011071078813807030105135000038000942c035004007013040100303035204000b480c000c000c7c0340116003d221400400504031a9030b0307100d110700d001d0a01048000710360007141110 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 819685566 1250 819684316 819684337
    0x20610060504031e0302010f05090a170301140904150f020403060b0d03020c0103020a11060c0a090602010510090c0507050a1b12120305070908030a17010803130b21090109020103110f 80
    0x10220107085c68240c0c00340442c1e18605400e1841d2030b0410002a000040ca2007180b40078441401d2820565040060030f071000f4003030a2621028501c0d8800c80d8104014450b42c083e0045190741e40450986040ca000d8a940c005461640d0340c01040038402c1c854684218280c1402c101c81d10309002c0e18940d000303515400811646810703d64041084d0b508540554810148603100c038040c0e8540f450608907104494111940504c0051071071940400c81e14014442d5030701030040c4180c0340300c5840c079114620700038040c503132075100070440c00f44901c00000300c01b08450000240704025100301200002e01015129100e0307489086070551803064003000c55a9490b04540c000e12502e804581580c580350305641e0002c03d90320140661000003001007400e030b40020700c241d05024030221500140d0780c1c0d00c8003550341c1c0582d036061070400305d07010802c0000c88079240003400400c21104e10195188070304510703524000300440707260641c0c2c4d4543307845204540e41403050400d501c012401c524280401d40100c003001d0700a4203500d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 819686816 1250 819685566 819685613
    0x20a060311070b010b0c0c01180b09120114160e180a0612050a020f04061409041401060807050a080703030519090506030403020f0d0e1e060405030102070302061006050403 75
    0x88141c45030440e4410780e0400e500301c1c0c255945801e1910603078031004403c0c040307011f24200021150312803a9100c400480c4040050042420038940c0308455011851199220f8607d03c070749041c0c80020b004840900380700085001040c13a1900c20700040046000d029010408094180000c0740d682402d0f0502001442030050002d42d52a801303d001008681c00203200380c2040c2d0a41c1c8100705000400d10001403007601d00c00d400c00200c00901013691742034010007d102040d00303001d901c2824015007483e80300b8021000a40c050074110301c03150841e50a07410081d0107800c10341c0184617500b003200844006021060041040310302d1610020032a0281004075180050b0070340070130750701c42d02c07503902c2c1d00240c81c0c024480c9079241403614003e5a2102c8400c40b824490040c3d040c2c1c0340711355004012811210002070310445110f11900e03402c0e151550704160b8958800360601000c681074800340b0150042e540309070000d101d10f0410756522030165120354414001c001c020041400001c1807600c2c1c11054164254a0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 819688066 1250 819686816 819686831
    0x21f0209091006120b0105030a0902011718011b0e150c0601121a150d06150305030403260a030b030a1401062c0412050d09080901030b010309020a0603 66
    0x5020380306800d00d865104800d0001d004401c061555054202c5481da1541d00d001d250124442d01900c001d800014003185041c4001140803000d82c004e1215a072052402081c291071079031055005000641f68604600b5a241503465071784c2003407045030250340b00c0d40f0300082202c250000007080c228600300f406001d50080744002c90501c0c02d0740c0980301500b88640c10389c1e03020740c1c44803005e4031090641101550802a041191100016071003a0103000385121301d02d071560400b0174030511402c8038440000b00d40950766441d81c0c2c2400300307901c2110005103224901940d540e91841c200b03170410b07030080340c080070111100c00c9805000300c140300100e81c0614114140030038181c1040c80003d05080e100c010103460305014107201c040c00e04042d031002c820f65810642c0c10500c41c169105001200640100361400b882c0c4400206020a894110347d010070100d503d4542c0c81c204400003002d0641d07808050403640210081240030080da050300600c0c03400e080070318080201d4101600001c1d840c442610403d0103055903602d4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 819689316 1250 819688066 819688123
    0x1b0207050904020f151204020a05091b03091207050f1c0203030a0911031c031a010c060f1e0203040b0612060711120c15010905010509072a030201090507080d02 70
    0x1416050300c05ea10031103a00c0701c1006440b0130038070b60102c9049103d140d000c0c0c40842d135231400c803980307502844140d03a140a00f48110500e1480f2640054004101845000500907030340c01c04c00e0042012138400c03c0501480101007010500c0d003158003003040b0747c02c1ca5030f103011194246d00100f03596001101030b6021134104420b0a01001c2c6101d584601138250061640380d00c034094050342d00c003422079000d41d0b08200c800400002c2904a680114209002034007000119003c5840da8000d991520404140015111601a025603d240c00c01d01e1060380c1c0c135000f1041109200540c00c4956110701d00742d41c3da4202c0648030015680301c0034010580c00511906650b8481d10a4040244180c85d6414800e11a50780e03e4131103000d40c0c1d03900c2c07510300030840c05140c400104440505018481c100c81020b0000017580e250340d40103460b01c031081c841c410640343c0300740c044054410101703005010700e03400b0750000600040d05090090070a07500741c2050000c0d50002c003803c9030350307940024074540314014a4039074403007101d5010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 819690566 1250 819689316 819689329
    0x303010e0c030c1b03030403120b030d0e030c06030f0f0106050a0f080703061a070c1a19020a020d0b040203010b01030c02060714070203030d0e0d090302010206070806040e0d031b0207050904020f 85
    0xc0d400745002c0b841e1000244c401000401580507070b000c4e440d480d40020104099205603040c4110103034040c7c100d001e610000324052421030403070300001000d0f10044681e00e004a20990421035800140400c030340305100525000340c8155000d04003501c2c00d00c1c58a40c0060000c0e00c41c0c1d5504c00c034481007009182c00030701d41c540700341c0c00100502030101200c2c1c460903a8101e00429900481c00545c1c0000d410380e800141194054858150200798860160405100c00396040000c01c0c0d8001c01c40560103242882c000503aa54211740256a1003100812010304141c01458215061454031605241c03504c1c1d08025110740010342c83c0e9002c071035860401d80102103050310a03814090444020b4040c80081100303880c04a494000307003d401001000c0300c101c1e2068180440e051043e91101a015030820700c0410151032055086a50011002d0000b082e008043e01c1101d1034031502030903074800a555820b840402d0305c520003450103858010720003010146d003440001401d110003c1d200900ca1103099215940e1511042d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 819691816 1250 819690566 819690577
    0xf0302010509041806020c010e15070c0302072706060509090103020907120908040e0c030103410a0605010605040e010e041a240411030703090c0f0311040e0303010e0c030c 75
    0x13080060101c08079140c0400603410400707040d41c455090024141901000145c4c0681e20b401c45201c15106464030b581c256021100740100740e085010b0b2250204131440076201c4118141008901030a1059140d01301d541150110b4022100b000780811801600d40d072108a01d5054039011517101041e9211501cac242c8401c1c107009500d4080c10b00744031a21045c03100702c601501c11511007100801480c0e491206003402031209010041c1082c4d90910007102c510b1040340d440940600340c1c43d440210503a07646e10501e16490340e20b1500900e1380450480801c0110b6802251300620340e60401307a00300b50400d03007526008403050007500c0c19200c1500000c2c007400740c0c03900031007280d0440e66454a800e0415a02d100004450406c1920258801000c00750003801c0901c1007190920803001024115142d580d812000b810a0020596501d900c510300030400c039451103100c6c0f00071031040c01000519001310080c0400d464500400c001560828001004000341090440e9030255100c961f46e039480c0d541c1b0f00c0c4010b060044 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 819693066 1250 819691816 819691841
    0x40f0b012120030906060a0303021005040204091403370c0501090204050112050d21230a021c14010333090b090a21140a02070312020303010f030201050904 68
    0x10001140c01000c442c0002d40c01041481d06945136a6076100074490b01c80414400100103a2008032001d1101d8051740c4500e400c644028000301d05905c450b211444408840440260190030010300ba440030005502d8108100c5150844000d482d106645c1614884100c1500c020500030b9407540e80040040039480540982d60040c800c01032542c691541000c0e81125400442c0c640c440c851100c90945c0c006c2c1c00a8103140803041c0c201c0950210014004c001e0524120728080d80742c00c201c24411600d0300740380d0311803180714407400050702d49001021008000c440a40541003041c58841c803076a074218409001415a50009101940c0001003524030300a0349800e00034200545110703001e03080102c4207403c10841c840c0a040e040210362034011400703440d005400300007088206100003440c2e0700100280c15140c0985103040c1208030308030403460380070f01e68031070518040140c110680c20700410000915405682c16071348025403c642c1042441017212409000c0641400404107000041d031f81c490700042c0d801d181 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 819694316 1250 819693066 819693101
    0x11a04022203031e0207030b34050306030c151b07031406150609090402040c02030f160c06180b0904090602070b100b09130f140411040f0b0121 63
    0x1601c0c20014848000134005a1450040300c81e15199180300141000a40ba00030348031030031a48480b4002c1040320440d201c50240d40c0707029003c000c0021080742d802020405580c0b501e90f0390b032600c1002c06061038126801107200d05040302d141c180c0c0c42c85600603540701102e03070440ca542000014032013a20f0f0a410741d00060001140c00014010150007203115402078050508860203c0100c40800c459401121065600901100d0006001d032800d50000e542c404e03402d00542c1d207030184000785982c3c5584081a81c8018007900e50b1043d041040b1004807400034851071411042000b44000b0b6884c80755001d10030303468200070114070781c2d0380d5030380c4c41d440300258507408001190780d000c1b42d207030108040e00200c640d071181810b44600060f0a501c06e608807050100010144c070b0307040d0f2030200a240200b001c01d00501e4510b40e5061681d16200680e0386003409540502c014595503034014081100750781ca4200300807049401c1502907040c41c3d800c454500400c940f2482014800104c0400d40b00050058040900c41920b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 819695566 1250 819694316 819694319
    0xc051506030f06160f1b060b01050f0f12010902030601021b03070b03011409011e0504050c13030f2a030209180303070f02070503060103020f010c050109151d011a040222 74
    0x109004c10001c49109450709802c1c0044904241c407144107003100f40403007590003408100024020b13071021700c0518050401d03500f081c4a800050b1100d811000000c04012000948041c044031007207009030061200742410352039460b020700002c2d10b0718002c21510541c1d014040c0441c0d92a13500340072800c043c141120840c3c0c0c072580d540f44250402024400c0781400388811000104807240100c07280000d20480c0300606031010f2914052100404008002c1a054032042c001081100b800d101520000d50043c900d0f0380b40440d140c100040c4001d1030300800b50000d0070841241c1f6400019200103011070b6011582c5652030369401341e00a100c03440881c603805540c00000100107003a80c010007079009040e0a1f5003210352807502c8506055642c8003c1c003000e5480030101002c42801e40c42180c429084c2c41c0b040c000400c4485040d41e1f000403422003003206601454581c071700480c136442d0f900c2000d400031400b0002807115a142781291086c11004280041c06660001404c008401050021300441e50300c03070702440b5510f03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 819696816 1250 819695566 819695581
    0x80309031e190c02030d050c0f0a060519020310140f03060f092505060c150f07080c0909040b0c12100509281508100504060c0c051506030f06 62
    0x1036000c0d108400c24640003200000b280d03886003076507001d050340c003800801d41d1802c41e00c019101c036006440d050959200f80000c0410300001170004401e041e202e540089803a00303040703488a8018640842403030362184103008000010000002080c22100102c42c00c020948107400411582101010004d1b014032615040c001100c001507603191003036100500f5541c031017541102e200210000c0c080380c41c41103000400c0904c403502c0e150005042c0150700b05c0440e100514800e000142102c41214440000d142060030010280d4200300da080e031201014089500d414800d9000070485940644050100b07002c0c1e6002481c2e102d40e100032201e404542c60b100101501e0101070007083c28005000301d038000d4480802041e520341c20b10311280c80c0c03104d120042e001050310403d0350030000d06007090f40818912000364001034002003800800c421155960000c1031074030301403c00000341c84120030355100f0001d1804c2d110021503004510418820303814613200e102c503120100024a805039411010b800d5000711024469030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 819698066 1250 819696816 819696877
    0xc03030b1909060503030a050702090702030405031506100306060206150a05030f0307050c03030a1416060e03090102010b01020c150c0a06110c1006180203100b0a02070e060a050d08030903 82
    0x110340c01007006110141e11082070544901542807c00003007002400200c1c014070340018050740c400020300c1141d04003951080068680940b452140c000c40c4000002c1c4407a03424109201c60b10f105140c24213200c09890808025034401c80107000551800400c07603a00c84550b00c1c101c00600903c001011100f02c2c03c49100500d44030b92000e40111064411004880c1d402c1c2004010344508068a84a840c6d6800a038580c44049500103500a4101c80440c6104000291144607901030407035450011034540d8018000603084481c169112810356007c40c0c8e40c010107594003088094018001d110f0692145451442e0910380484024010081403c0c09203c40c00743d1810702c054002d199030701c03007140c0242c80d1101da007108a415a02030031035000d2340d070106080600344540046800c0144106c4c01c1001c1a551848002550403110310140181c0003982e0801038104104140c0350409000c0310000001e514200000ea1300ca600042c004200a00100020340c80c0c1c2c500744152441c20015528045092140380901c150 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 819699316 1250 819698066 819698069
    0x41a1f08030301230d0219080c0a0503031204050109060207060c020c010305010e2806030302010c08011a03040f11090f0a0e01050f040609031124280f180c030308071d010c03030b19 79
    0x941c449d0300314503292413030500c509504541c07001d0051407400c04858031005811200500981c0d040d900e03000380790006580f91000300b02d403a000d840c0c002900c85580304d00a06041e18000b4807410542000014840d594800d2691070700301e905001a61030003400c00000d403019101880052040b02d10b0030b4400014103406400542500000e5030394039800b030380c81c3c1d4100001440b0055401c03001580c14400140041c4c026400c28a0840c0a074081c0d158034003840e00042d03510702c0c0403288a041c403140002030103e031407854002c101400016100074030051401143d2007040d03080041015261580305d9103c0d80a150045004030903807031503841071f60168842059280c40c3c61004189001604482e0f00000c2c0344410404109031009542a5411241d51aa0482d0101500d0781600e10b00f002591110304a80c002d49086000920038491405201c14915504025000b039400410300d00c18089815a00c0c0803d0780e094541503044c03542400c00005140c12400d08600400744101c5c000d0700000d0402900c1900701000c1603010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 819700566 1250 819699316 819699329
    0x60114030c27010510050a0c020a0305101d03040302011e090b0301060e03190503030a0f060504022a0a020901060c0302033007050406050f03041a1f08030301230d0219 73
    0x10b55990f00d200340003180f542400c6440004000b4410040d007584151501d4230480e00080000c11a1a02c0340c4486042480d1903044001c0560307981c0341641c1034055030340705511030703d64903003e9824949550000380014841d54442981800801410000140a0000070713000c0c0819080154981da151503010f414504480c000d24440e1240c002d0400be524004520100f03030a6219001e1402c40d202c000400c0040c1213000b8407070148503110381c4e003c50325071510701c0a05140102c15007000c41c600c400c40710482c0d0b041c844c4e45d501400ba070030011010003d606c4106409045130517901d08880d42e0105400c0803401c5010b8080d10000d5114040310030b0055800380c3e00c55003112010302c0b0b9403000640b217003002542d80e486588034480c0494402c0c440d4103141050700c406507501c01d000d400d85403e006905214410700340c404481e84010061102d031813450f2403000a80300000382038000300540c03031035041141da08440d1100030304451026185c030090040c5501d807041d01145070f0b50b02901100d0801c0804101c900c904640f4018030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 819701816 1250 819700566 819700639
    0x7080a050609071d1b032406030601090b070c09060f0602100c0806061605100509120c191a040b090d09030f020603072102030f06030a05060114030c 65
    0x41840c0c4010500c0c1c0c0468808244c40709160b5110b4400c1c1e0510744004040c0d548240040e00c028240811440c01503202e501a402d80140c0b05418100c212440c0344411107041c0a10700600c01c000352640c002ea0480e05079030000507050b40301c410034035000c5890a8030760071601e8103e00300b00c00041c00c05010a00c41003a11190740030f9507100020795203000102c40b031541c46400001d5151010500b182003000080014244413540446a00c805441319403030b2081c0d100301001c403280e441742000751111050021402c2146071180f91803070140011240c9030f98815441041e1050050020036070204402004210300070100c10140281c9858281042c190383c070812180d1703071014011602200215031080f544481030386d43c092400300f0b101046809010b102d030001080c90301400801054016030300100d4648194032031100a0150b66880c01744010000d511000d02080d0280d03001701c800c0c0c4005003000c00c80c0e03415206100d051500d190b1415001038906000300d41c2041e00000e115a1501d5141c1e640d03414990743d803a411054 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 819703066 1250 819701816 819701821
    0x20d0510020a1b0c060e0120060718030f031209050d0c0516180c090509251704110f1903020f010c0f0311010b130b0f010e030a080c010e07080a0506 65
    0x2040080644401d0051081000c13403004d1010b40d000d540305240000041c5802034010b5040000240b400144880800c03203603101c2d90421549070f500100040030868141d1055800c145182e80b041c2205280d054000e09101d204040710442207038690080c80850303006001c03243c018803042409080d0344422101030300c4034014580b00707280c011807002c2c0e01012035403250381040e080d500d03100b5141c0007804039580e11810801d0030000010079503911030080f40141d0041018050914024041d206011200946481404101c0040c104a50203240555910541008010011403207131300c0006c1403140142407151f800f412000d400c1607070b071403201d0f041c40c00c3e44c2c420f0b6000070100c2d500c20015640c00d8900034005280d01e200280341c40003c1c1c071604160404e44031600001c900600c0790800207400c0c4542040340c0340d80d165581d600c102149040d0b034083e15101800c0c01c086000d5000d1502094a88070045800340ca0328000142c1c41409078002d5000140440da2039054643d050f0303c901c3c91540b10780e0b100d00c0546413845181c01 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 819704316 1250 819703066 819703097
    0xc12180c08010c1d030708060702030309062a07030e0604060306171506061605070b0309160b16080d0f1508010228171515090d020409020d0510020a 65
    0x4000d81000c2c1500e9100e0b091036281d200203019011080c0640d09802507000000b47d5000401800e030040015402075a08c84c9800c00241d840c0440083c2515080b001030040005ca003501d4816451400d44541240d560301c5e04241003e907003034070ba0b2a00c031540002d000a0001411035161f40003a00f031703900c4041d50300c0a40c10603450256451480c2d509400c42c43d0640c102103801ca280250042181c0f5003e845d21106c200d103281c44403410302070710b039000d5801d4050000800100038402d1041340c0405240d6640d0b8140ca42c18115a100b0500906824881307107414107040c14203000560041d00e403404007101080c2700b450600791a91002d4118441d11a002d00d51120000c030f010070301070090340c1444850340b0a1307000b4a00111141d100410281c079824040c04050822003109aa18542c0144100580820004659181d0080c444103280344803406015000c10302000405940f12038818001c190120780116804050340006640c2104d0200010950f1080102203c0510444d40140404156a44500341468040310 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 819705566 1250 819704316 819704321
    0x1020604020f190b040e310b180f01020a0810061b030309140c120a03080109050c0c0f0105060102060a02070209070809250512010e100c12180c0801 65
    0x40380254440c01d03503025426241440d01c0384020a0464001c20380b00300340d49142500095015402100b003c06d845800c00c498041194200c0a5000240704144001c98801e084141c4081800a00511088040c8040b981040c1380d029401d8141a801060300c1410441880303a50003988000f20440200e0456070000f9045516a04074901300c5015455201402a1416034005c2d24944010b088080c155541c6e400000700c0e20454100d0301c0e0b000380c00020894024407104100c1c440c03501080740c403400c0c3d008561107070010760b002018a04542481102280c21344800f019003c06000f0145240542c1c45a102e5501d4801415008940500000c0e000d449807526a80540790580c451080060f42010b030190104440328400c12150f5802110f01080d107140080e403542a03051860f070501039003010840301c0701c24040d030700d01010781d0010310352107030001c02400c0c0740d402074580c0f01e010000007080010756948c2000303031403809224092003103d840181040340d9820f1003540e815402c90b48009a421610312a40418103c85c141b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 819706816 1250 819705566 819705571
    0x90f0506031f060b032802180d06141905010f032001230403051005090c01140906040f0905060f0a090c0306030b100e0f071b080c10020d0b010206 64
    0x180240014078119481500092080c01228400550f00d000000381d4803060009540500c000480401040b4208413842020310a00080301840718410012000441e000d00a00341c1c41e05010b513020f5003111800c0c20710314001d01e079a502510926410004000c4130441440c4503c400e510700c1842001142d881e4903c4403034031601130000400707032011a0104072210b2501041c0002104051400440000c1650003c40d450245881400c80e1000c1c003045c1402040418030040c0007681041c2d50400140c5030445910b6a030700c95400605042c07141060200303044403c501c007290300c00c40c0c0180403103984580e100c00c1c1149001d003d03c00c03a94030074601004508545000200c1b013180102c002e081458640c1000303640030041031900c042c03005050f541e200000c002613840706c006110785002e40250341c181e441d001101040355002099141802801c0081003601d940250f18182c281101002c1c0d114410f0312817400010500c101c680048681c4035007050781c40b1681154005086d00410f0720b1003841a0075185005a07a1030340103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 819708066 1250 819706816 819706819
    0x6370c02072301081f03060219020a020607060b120105090a1205131a16140114040c03080703110a060c02100e03091512010303030209180103020102030a111c0207090f0506 75
    0x207410b00c805456100703101083d0080c024038401401548101e83c6280980d03c0b80d4403c0f20110b07004161070640da0228110700540001c0c900150402c004180d002510510903410003c2c403041d23490100566a40306ea1f65580242020307040200400e003003940d0140e981d4410404111038643c0f0782a402c0710703568811415030380d510032a084401e00603401c2080c69989403500c00c03014030810f8014000b400c0d0302541224054000340c000c0c1c1800030024003201d002400c0d141c5c140034001d0014108400d02c000542d071404003e04403074001d210203807034190324541156030384c5030440d0b0020725104050160007880300b0b43c0d22042d4030003002d40031144041c40c0c00c6138100a41d03510380c003d09156001400500d21500b060389420b40c00102180382c0d41e2030300400702c0b0b404051410a03001030f0002540483e800c01141031207143c42c0c04010f18581440d10b158590360000f560707449198500390401c0b074510a4100d84c6a01000200909840241c00c403d450140503c0259070700340034800c44025500341340f0254000405072081c1c038000c160 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 819709316 1250 819708066 819708119
    0x601061d060f0a082a03040c0f0f06081f0806090d020c0a12050307080c0303090c180103060c0315181119111c030b012006370c0207 58
    0x300000f0964401c40018501c0703a410503d4403090350401d00d4070203407011200303e88840c00c2e164141414845504442600b000410440c42d040511148400508400454255240c441c0c00b6984d009800c180c111039000074110100c11202001c0380620b4089070951150081000f02c130020030300250126078500e030b180d41d1540c00404500d8280015855602d000717100714004c0e41203070724000381595403804942c40340c0380c3c03042d060b0000f0060000c15002845035020b5108200c400312000010400042a09003061000401069445c070225225a000740c100c0082c03c2c8401e0310350381281d81d41d162100c0e0600500075503a0029490014140300c1d8032141402e50304c010061407500d60802101100070303039001c003d010a1800e81d10a07005980800c0e240e180740c00c0710a4009650102e11017210000160146210300c0001c501b80c5c94848100b030400500003006503010b401c090000820843c2c1054183c8040b00190004039000c0c08842074040c060040e8009011072215503080351f19850b42e811031070f80c0e1411440031155070500b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 819710566 1250 819709316 819709327
    0x10030e0d080402220207140a051c1403090a02040e0303160801140111031902011a01031b0807090503060a1a06130303140c060916081501030f0f050601061d060f 70
    0x50101400e8150404d1503800610300780403600c420482c61680803081000e6071000300440200302c0d0621107200b141d02c52001110041200d000c001d0030036101c400f405a1608c0d0040001010440c04005c0e041c90240c0207031041001c0219006660789070390081300e0384504d402060b820303c4003103807140c40c2aa0407074284101c0d0b21520340c600401110840840b00440e005440b06100c0b0b030500c2062042004000c4405800014505014220303254440c82030910700b03410f1615000761240402d041d80240b00103100d4904d0080850355038071f00140d480f52801d03005513800d88a03036800c110103d010380c0e0103502418118200802c01411207802c004151050740010310181e00400c0003000002d0142c203420011902001440d410404445800c03850311000f02c500d00002d910a02601c03214405143c0007101a02688001c1c081c6030072044443c052100040c84000d10a001b0151040d00b07200c8225504c0000e02d60200945205503034a040c0140346179074420600d02080c030100340c0640c0900c2c0600880340504104180c803410705 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 819711816 1250 819710566 819710599
    0x1a04030503090f06040e0a14180c1002100c0e0f03010b01050f0703030603060905010b1003270f080309071a0403030921080d02120f070806090403090510030e0d080402 73
    0x1480143d4941c001c9020b00022918240c044241c07441445d0b00b01c3d00140508680301d400581210103010f164004086072503c840c1c8580109074298035075000e0f925210700102800c405c0346040c0d0215815200a0300c0c0c81441c1b441c0c5503005214550903030084501c0300d40b0b0020074042600701e8490f0010307940440c03410440f2545c048000340182180c40e010341800a40700342c0c1c0303840c1d103030645412050490f266507503101404211b1916205c01c5084980a00e000c100060441c0c0c2c5003074008a4014241507143c00102c6181c1c200140f01c00e8040c011540210340a444c0c7c2030100351150b959840740505156050680c1c440303100618804195401c40b50140d980003100c40c64a8411040042514041002c402d600403210005c5032101000709032400c910040141e450300b030391005149508000d00080d88c5129034200303103c0f01c2907001c0c5030207401900c01c90310400c1a440754a81070311020829808250024490191450741a4041e0300c20b440c8000c8190039184e002e07400000c00c4030039000c21140298842d8200300c8480c803c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 819713066 1250 819711816 819711829
    0x5160206060f0a1703070c06090302210601140d05030d051009020a0e060304080c0106030b010f1424071704031703102304062306070f060b1c0b011a0403050309 70
    0x420342d00010349117414120b80700c07c804950745400c2040803172040081041141414801510f140c441c11011050313560748164070350785400d818802d0390071035040710000780381d2580e90074006401c450348913003204e41d5602d1181002c40588800c0b500b4220401030701c400010403422500854400f90344560300d840d01c00c0d104404208081d0030140c020f42d5580e4040c426055140f00902c02c07036000c1c60107801d004050750700d04440c1f01c1e800c01864110005030700e0b80c8603118036243c80e451500c1140002008100c0c500c00c0b0002c1d083d074018060144007824821811440c004100b160b04020320a50f401490820f20303d0a81c0c07a9040030a100542e0a107c09401e8203900700284070200817587d002c00c00d006022441010b140c1e00081c290b40c82908603615003070040741940f034004c442c2481070300708440030307143d00f41028090b817104002071002d010041c007003907101c0c0c02d208560340e42c151109202d00082c000711165a02942081c8541100034000d881040c1d02036070720b1018071210700341650112907006000390b00c0c209892091001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 819714316 1250 819713066 819713099
    0xa12021212190f1506050705060613020702030d050910050412030807111006150306080303180a080a030e060709050604171516020c04021206040b030f0105160206060f0a 74
    0x20340580b048120040580d160081d0708042d20a0400420094011000c60145241d01d501032030910104020101c0011004149a5070201e821104801400c45404581e00a4864414000d515008200e190010140c100d4050242c0500565491201176070a010540d0203204500076204030305060180c600009214180071940706070702c0d20344989504403082d4402c2c41c0400c108410000711b0348880d014040700450002c89c41c00020035180c00d011b52880d00205030313120f200141003602c00240300c0c403000c140c0b1041004482002036205944550754008070704000c0080c021a030070201ea5018442c080740443c0d119500e440c050b554010034040c0791030716104501d084009504440e900300e011300300000b41108403044100c0e00c141d03031407094103c1c4213044c88002800d081d40c99001c01e224601c1400300503a0b504e0401030684d030082087d00c00248020034840041d14020008100090130340c06c28081048111040d075031194040c0d0b003030702200da080e02c0340006c01c5600441c4206183d04101d00a40411003541c2d480310108 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 819715566 1250 819714316 819714331
    0xc06051e0309100606020c18040b060d080712091403010c080118290a080f1c030902040510050a1415031f0e100909050a020906040b040e0a12021212 65
    0x34811010010351405440c4d140d4420703805a000003031103145074280300300503145035903e10b8414040b91509030f45220748040c01400b8580107800d15a024000c0190715011a03200300c0c1c000c5a00410312802c0c140c000c0400046000b9442040594143e41d109800d050013002918203081d1199481d5032b00701f1196143d22070410071609040d07900c0b50604401c0030840704400880c07010304011500c3c01d600510a00126281561101e103156002200c218449140811045c504818000c1e9901c1c0c1246850000c8001d098030780b030060f44c461f103032000b88a48902c1d49082c0c0411550280c1d0103036803a650720780d02c01c4600e0782c1400032a500060030245000f05d4007410001150b00940b00010f41141c00704288031200d6a8015070400000103680400340a42450000150030081681e280e0038015485c1e00c3d6120b68880c0c4182c98003d005403005c4000c10100c1c0d070745820035999003c2c0036001300104554819455920002400159080b880c401e0019a0052009c203054066a802c4101c0618281e9082902d01c10400e000301800c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 819716816 1250 819715566 819715573
    0x106270905060103022a15010617040201050c19120212030112050a0c0618300302011b0302041403061b0d09060f020702010212040612021617070c06051e0309 69
    0xc844455521440112080040741b0794203020b103111210b1807410f02203040c0e450303041c0c520500400269900c0114940405003070240c41d01941c0b2184010b0702c040c014061444150302905c04c007005c1c0c0f594403a0142c2c820a01035010910035400020301662240901580301080079820001800b24a000e0803010841d10b10030380884000d807945849250310f900c4a900640009a07940010015a00040e00040098140b003410728000c01e802c800052100011011940c00010892011000340b50003980403510509407080190f501d0b12a00c1d100070300070f40c03182c0107001d20400d12151403441414006140fa106841c800800011079602c8026a00d140d0809840c0245d020703141c00310f0800040c3d581c000c1c0c81400202c00005078440c02070340b0001e400d00c103002801284110302840b0400000b540301c5e40c420b090000084d40165560110a11f03114078040d00180540602034030103400690180001c010402a1700070b949510950b42c03610802c44240c0f0840711041502c40700d000103c45140c0010004542003241d81c0b084 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 819718066 1250 819716816 819716827
    0x60807050f0a15020604060b06161e050706200303010f180f06030308010801050f220303111909060201050c0711010c0b180c04090c1a070506040b010627090506010302 73
    0x41c8420030104500000145c00c50800c2c0310400c00c580c064845070500c00c0ba0382900707145e03030041510040b20940700d0207814245109000c0c030100b41c601c19040400b40d003003002c0e2081c041d19040e0181086004811414422a181098440208001c4141d9040e14590f000ca920368a1900c241c5400094001402d4110355907101c3c501e8807030340914450710000b103101c1c5c0c0303884060f50b2510b1140d6086030380c010308900203044058100f00e088040c41c401074081c1e00c0b034000c040601c503400e8102140205012700380b03030305039000c001040325241e40260352469400c0310503034880114648500080b0b00740e0304140d032440000038041c0302c18000682245051a02c4030307018940911400c903151200c220f410b50039079800d94401280342c100e018042d018404010408402d44062111900716510110410000e2103a00c0c58025460048004000603074201c84107142c00c0703c1180d40c85d00781400c01000720300080c859007002c144115518011054507080340782c908100484600340c01d901e00b1082d84080d080040410703040660030402d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 819719316 1250 819718066 819718079
    0x1f140c0a11030406031a040504050d1b0203011109120a0506061e090703061401031505090a09050d03060510110312090c131514060304110d020904050619060807050f0a 73
    0x143c00140555600800c00003c1c401016000c180e200503514000c0b4204010480032850010724147c8425562510354107440140b40b0500c0480511b5400941c5542030092401441c500c4901030b228440c0100d404d048908010b10702c0c0342d0b035400e014074000e20b00d800160004850740740440c03588140c50b032100c403070a802418120004070442421114900440d07a9904203008020301c50310403034040301080c02c081008a11113601c00e030841003d031084034030842e24074000807003010300d5402c098240ca9121044401d0280c14030005400307800c13907005a500441041c0d01c001038652084650511f074200c0000038518000c03c410b4a001c000304001d01d018042c0c8142c4c01d505507540c03601000e18480d51040d02c0c0015500384010410701c8880940d5005016038070214008000955862007102e40103070744410307442560300da5980813072013204007404081d5010300001c0c200020f021001c5035451144500540c021400880c4007046070032260103000352142507006031418410707800d044441d15540c0340018040241c0b1a59920b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 819720566 1250 819719316 819719323
    0x90302041d07080102040503071a122d160e0f310c090b13121202060f0403020319020304121a090f0c04091e03021f140c0a11 55
    0x206007600c11004894034401520107016800c040c0c40400021340c41e0a1070180000c0d52a1158000c8451049450100da660b0780000001c0302e0031001d20402000f0039241142641079240448030102c80c00c4950381140381c002e07500c6c0300d48140c0301c0e041d00f41403079103a01d5490000303c40380c2c1c40c4030f5031598001e0568000030f1515515055401000e60b001071003c0e0001aa2640e0b80d00441200914000c4060503c041c65410b15040281c41094801c02072500341c0320b5203d0030300794040200d55400ba900079503240d01c45800380195495510301804164003110300c20b4459400e481c00e001c400303c070041e005800512411050024410701c2d01d030b5180302032040724282925a800045143e00d40881100c01c58182e030310020300b0160b50f81401e0f0b80b068940c270107440c0b14000000410b844000c2c02c141103115176034900d2000c0410423032600d034111010481142c5481480c0c10b00c0c0223962200701e0034042c8941410200300d070102124a0080c000d001c10301480c0e120154548040706256504810140800e2100c90040c9003038059080 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 819721816 1250 819720566 819720581
    0x70c0305010c111506060a120c03090c0b07021f05040503150106030b060f0d0c1101020703170109060b090f06120906040c0501090605090d050705040e011a030102030906070f09030204 80
    0x304000110b0100400d40984201d101c050f03080080e8100311000c181106001c0c90b01c3e503000105640640e0341b00325043d41218070b903041c0250351031194a4070505242c40d50341944040e4007140b117000c07a0708030a911880482e06500810f50001d40c40740c04008054070250043c60340d146444041c0c240b4900741900c4a000904102404001d880510350f004010440c031603150060340042c0d01c0949025140024840c1c2d4000203100310480c0007000e907101d40814101c1e620580c410302d034486483d0005c54860340d01d0b1070014080162104d000400d44611400070400400314840c040480755401405423403c01294244203031410390b41c0110f523001c5428480f40350a261903545940c80340240001400441c50700303152104a09146400107410000b02100030b100e11178200d8100c99445900f00d0b900e02900c01545043d40c80d24103107412458005003880340d0605402415000120303058040c080c460404c2c0b83d040c06040c202e020403183d001540d8080b00100312a039008480b0042c0071201340c90305620709a101c0c0c01007425903004 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 819723066 1250 819721816 819721823
    0x21515210a081201091415011b0303091101090612051f0b0307020d02030f0a08100b0f0a031b0c1b0e070c11010201140712020403050609030304021005040f03060b06070c03 75
    0x50f1116039510880401800340140200800c40d045442440c080c082800410020140d00f69616071151a801341800310f98803c051050120303000e08510b0010041c024081003159051540319503c1560340c000c0c01000e00795030759a87c5000c40007c00b42c0140028041c05444074407000c69044c1d4401e2386c3d601920b0148003604081001641d01d040080d4000e2130300b20082818021034000780007011800c24070740112445217116250541c069101c2003a005041003040d40217004080f00050f4811005001d840640b00d80b041e152002c003c200284c5440d500c45440001000c0c001540c003030b40140c001240b441010048620680400180c6500d40440e1a81200159a800c010a001c00150400c0084141103001255420b200902c204940a00b503140303080750103481c4000f4040c40c02d00c0c0c0c4a80d0103030307036043e01c0c02103800004580c118201603030b00e107850358026102a03018104604000c42024000c2049a0488845c0c0142e89a00e41c035503140c072001000c3d01031031140e011804004920100c1c5280c904100074501 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 819724316 1250 819723066 819723083
    0x906060201140a0b300607090603060e09061b04030c09020d06061b0602090f1e09071d1005090306040b0708130c031220030406021515210a 61
    0x9800b150011841001052908840c4c1005a194182e4032240d43e03500c0a2580343d01121901122010704840710700300c240507841180700b404200300210740c1c00303900381c4100d551546003002000d458150b50144802d044038490029804000031a12440340e940261501d10768012000303041036180da440d107036546240c0e40007540c0d041d00412012070314203e5101e030034000c0166042100b6012030840c4a601d60181c01400541510380c040380031030a50b00c9503480b0a0b01524010312604240d0a0910490114103003601c042d40130b00c0d074171400594000c1c00b500ca078444403140041f15102a00e101c80030805040d10000c607007403c12206000c401c40341d85080201602840c0b00308518074251a00c145d0061103c40014203a400006030301102d0000b24800081c1c031001d60340c1008040c0d1303060f801d180e401d03a0200d140c84035000b168107243d244050700203804000340050f181c40d82e00340c903108070100f0500e481c1054196040344021840385040300c15481c250030000341e459403100210004c1d81b12410400d041a25843c0c0c151150135 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 819725566 1250 819724316 819724331
    0x8091f0804060506010e180702100617011a03071203140d050601020c0a0f03022119120c17031317130b03010303020c011d270a0c140703090906060201 66
    0x2d42c002c82e80c0c045401c1c03800040c504109070019039030310f140c043d000c03a8120020011030b601138400e03c0b40244c02041e41005100e0700d80e68a40e080034100f0002c030420429460302c5204080031a82240b0740d486814024003c000503401e1502a1504e103001840072010f211411008901a10f20040a03052241d404403000440c1c0c5400800603081c480c1da10001c9225082c071110501004240584400c01d40760160b510703110030104014000c0c40c029400c1028801303403060703189001d00380301208058240d1603c10782440032400e01c01441034071817142c4804010100c0d20340d20301110044141c000035560010311070b1000c030380809541d11401c6841003881f411050094001440140710680e0f801540010906500c200349990f140d83c60003900e40e200c281074141005a100032410101001c4d40e0520b80c00d640007040011565000050a8072403100c9a040042030f0032010001100ca00d40d0303110b00c07000e06c0c3c000e031500c02a040c0800b0582c1050b5100c83c000310b05001c6140c60100d0101403a11591010300702e01c0d000042d014 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 819726816 1250 819725566 819725573
    0xc040f090311060f180307080c0303040510060f15050912012f090f0109210605090f120f04030f0803040501050903040b040603150b0d050105190b030408091f0804 71
    0x1c1c0300320340c0c40c42c0752684240144000210b06428007540706565201c2090b030024003080003401d51003409000b902d88480810218103111010008501851041c8212008400080148403d5600034030643c1003030040c40204000e003c0c0310901d80c407106401b5203400f80c68110184001f5042c6c9040b11494400c6a40d2201985070391104c00c05541e01e0042402040303100e442020500d001075200754030303046001e040d0304e80018880d64010b42c800000b80c148001005a20400d42450f248a2070310f010b81500c00500344008120b481c240464060085a51003020703010010541d6444041a40405401c920301c07035080000002007003110301300109107842540225540d0404e070506a080d00c2019114040f240c02c100f000300b0840c030391002200c003141c00c507040106c1c055108000d151500c0788039511600e2a101c0000f10705148113074a51106059410844120703905400f0345000d030048141d5400b546101c0c0d4010000304001c9900540901030416000782210240704031020000314081c00500301a0100303c80b5010300080 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 819728066 1250 819726816 819726827
    0xf0d05070f020a1509020f06030124030b0303070b040804051201020403060b040e061b120702010221011a160c03030f0206091605010309060e0d050403020406081615020c040f0903 78
    0x1c0440b071005000d41c82198031142414242082184855691003450104640301c000400d804a0700040c00c098480d82d4520f000182c02c0c0c4c04d10241140340d0000f40c404450a4081e10131032550b06030250003141000059a07402c880718101070000e1f0707203843e400e000001d80f0351788440c011014460b816001584562031071400100b42c0e0010101c841c4a10304240700100b00c4040000e016602422903103290f2403031409441c51085a100c1e010341000e0b45201c0c130702045144d9805400800400600c107070f14900000b42c54000c0450204280105221109460070118142c0b0104002d041003a400848540d01c0c10301b1035684000090f060740c81140071402c034201010340b03160140074a990040f0000082d200420300c070f18070403022496078003505047c182d56655001c18881140e001060050154040312403020840801a08641013488101d101c0c41c1410700100e07112002082c0004032956041143e001103041c0402d807640310702e40c02c21a1085102d0010a1041d030b6446010352041491080c034006158007040c10002c00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 819729316 1250 819728066 819728087
    0x80a06090f0c0e1c12030b19081006060801062006090c13090c15020c031f0608011401030822030b060a292203151b0f140f0d0507 57
    0x41450311115280c5481c140f130204514290b80510900c22101c0d803642e00340c0c010501201c2c0c868005c1104000b54810b410310840d21415a14420126180e5680c0f0350b134550103445041c080e5400182c0d803a001004101e0040103294040c00e4508154080d01900b00e101e41c0c6070460840302040300b40d00424035020030742458080f0038909030a908050003000f00c81c7e141c4503032600041c41245a91400c01001c1e4211030f100f0f00c501240d031031005003920b40010340760240d0b03051503140d00340c04003040d850088006080315052098071054010307150001084c0c0c0c07858a070144140c000d0540b9031b05592800d005d118520300d02004c0200658802c605028940c14050103006c48801150011807085040040030f50005200c2511015030b4000054026514030b28042c0c0c5085809508655900c1c48a402e0408420080c98220101c40a4511141082000e50f007040c1690310302600d090180c08180d40e04075403091144214090b1030032a815018a03440d111803452814003d40c440400360f0529a03441d000d1241c0564480140d21 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 819730566 1250 819729316 819729319
    0x807020f0307203304090f0c020105070e030a0206090402120f070201180b0f040203030c0a060e010b01020a030909020f040e01080f010507030203070516170a0804030216030f03080a06090f0c0e 84
    0x220040200040c1300c001102ca11504507080c80d03440130309208410000b003102d0190a11520901001c20704485013406030203240c04400140d401c205c0002c0320148a40b200c1d8110b4038004004084003103683e024414540c2c002ca00244e0855000c02400c1101000c0451660040c45a40e810100768034005000070300312214040b10000c074a450303003900c2010442001e245508410b001c0c150b5411a103803880083d184d88503410009009000700c121a4042c05525800982080c030024003e02c1040014401241c640c60304080042c08200e18030b0b02401311203e66030181c903040c1560f5855915250300c6881d00b400d0100c090317008071196401307444c454440324000c0c0500c50700103132135060540c1181811240601580125074500d5021506c0c000e680c1c040c400d9024411401c10b1448a00d076554200810340108020b80844080d0090320446c3c0c01c1d0310102034a500801e080300d80260814122410301d60f0b041b0782d990800f8000003007480d1943c01c00b1600c030340c0a2140000d0000101c400264480c045140988008031098095 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 819731816 1250 819730566 819730579
    0x30b04051011090f12011505040b0415150905150307031a130b0d0f060204050901080c0603040201050c0f0607030c090e061806060f0c010c0318120807020f030720 71
    0x145030382c00e60801903808540c42103a06404404455000c158002046244285a13600340350301030001c402c150701c84000342d620581e418805490750809100030386001141c03242d01c5007100c0b88104001074588107c21141d000c02d150031440580d4690004041044080200d20b074424000180718241350103103c0d04505803c800004030300d607519000042c6560704402320100000b03890708035200c813070703a80e1440f400d1003268403600c1d0005012440c24210001e401c24001d01c0d0040b90004000302c2c0a0400040001000400500e5246195100c3d801143c544e00031200400b09842040340711500303005d040c000c051040c4115a40041d002542c00c600600d403c0d4154840c0c03440d01d1003d8240509501e0b1264400c0807010b1b2400c0104e10364880a02240c500d20550190380c02d0280302103000101c000040d0859036a10606507070a11864890381d183d940301a40405000b0000003c0300021482580100c1800c2e50142c91401994091901442282d0450f80281c60807a030981038410716000c214032941788098451000c3e20b80 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 819733066 1250 819731816 819731831
    0xc1912080d0c030920060d140103141902130f0e0c091f090e0f0d0504060305010e0c0304320f19030909020d020d0e100b12101107050106030b040510 65
    0x80a603510030301d17010917031030459052a14106882e0201221452250064100300d200b020010032600e2398000c0c003044031050420300030b810040c880010764510800c1340d010040390042c040d5003080f035103089030b40c0d25104042d10381c0010314408945105030920809408054000c04442604101e90b000c3d0081803021070b100303545d15045442100012900907603030b40440000e809102d10704490314151000d05150140d105018494040c594484040c01c1280c0190314140702c90b90b290009800b02c240200e5071000050002c0c0009070124600030030030b48210640700c0c0d1102003000d403480038843c000405100604135034020701e0105030744101002125121690390001d07075410705056030001c00e005654461210300603001b09001d10300c90142e9048035014800c8203c10400422203c0c100d42d00e910031000560705407440c0c9045c005032381c2400c8000c0d0101483e03442c081c0040780485100d190050081c552404074200042c0400c90014030709102e81c101644c01343d8071008103441d03c0c0c9455490500704000090545041803003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 819734316 1250 819733066 819733073
    0x2101206090e19020d060501060c0611030714091f0e03070f0305150717160e030d14130306020c06012405190e030a031e09080c1912080d0c0309 63
    0x80c903081d00c01c6009a0f4030012041d9000040c96034496207809881c242c40c0000009800d50458024120548603850030310081c04040c81600c0d41c0c0c00112000c20200f03001558a4480c0801c510082801400c0100509035010402081c0b29081c3c81b2901c10f2301c00316404a001c4490f030b01d03042203884010a03e00c441807040b00c1c11540c1c0c050b01d5001008001c940400d200000c00d6045000b251480c0c00b1140318400030449140801d41009050b060043c0300022441c0140b182d80c03942404200404100643e455058400118000414160384001c5510344403504825010001490900041564818a100525480d4140400382000000d0341d044240240700801c2442c40160300314007903584400c000200c20345880e0032003000b518109c2849051aa0501407011a403003016040000d68000c02e01001c140000c512550790152100c1da42802000290742c4600740c096014940614014401d141c40c80f081884035645501c10b01d5032820041048515a80204030074691446620800460940b980340c140450b0000340c4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 819735566 1250 819734316 819734323
    0xa0e01020702031e0307120206071704020f06030703060b0f07030f0219170c0f070f0b0901120509120c060411011d04091707110a0803040b030a05100302101206090e 72
    0x340d004901303106160420081c04800d106503452a90401103c00350145425002511840212507010114000c2905903056071140344c50603100d140e02a19200d80c040301003041000540004114200301521080c000c543c548860018142e814140c0700019100d01103450080d20f00000c9003440001c41d881050b4480c4001140715200400d00c3d08001100080c507138100b050302107071007000c60440b8644035005a104001400040610465107954803241040d600d800c1c1004580c440e11403543c0c0020200c490700700704840150b10440c3c0041d02041100c1000032255040c01864005c1001000c1ca90414000c21081c007440e000c501c1c0140710246054140a40c14001e081c17840c4100c0100c441c02103581c0c090722410803509040318118068880d8040343c0b610014500842d000100c1032010b405210880000100600004180c8083d21281ca00f44c904503540c01181e00e0090200030054034480c110000004090389034050301107010400c0382d80b0721138910f040a4111081c0d8000703600c1114141d1801410445220340030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 819736816 1250 819735566 819735583
    0x150408121911030d0f06030f0809030601290c070330030603020a03080304050c04020315030c040c050306010c0c0e0406020a02010518030301140a0f060804031b0b15270a0e0102070203 80
    0x801c0e0014108070146181c4000b451147c1006208450044041051006000142c401c088046045521030b81c2c0f1403107002580001c0302e02915150180e10700700d5043e0310b103040140c800b400100e070495010b01d541e511240c3d0658000f251840c41c00c5500c08030314804140c007028000c4040e0f51420284603513031031540810b400340800d01c4041e100940100102e070030442c0c180728220344080010025502d034240b250101e01741035100100c1c14070030310a01a89281034103290281101d00d030035640320182150745040c0151001041c420b012a4100d102c22000b25001090044040c081c0c1d004090050f01d882619401900f1900c000d402d01401010090102c0d403180d100004580c15141c032070150501600d841008514000115088130b10108801840840c0040c0d102c4a110701c80e50096840d100c40040c0880300c58070411500c00702400707100103800001e08000181280e070804a0014008151240d0705110703a1220b60102e1a82d494103807070000a01c48040e040f8001c090000401100031450700040da40000d40d1403551 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 819738066 1250 819736816 819736837
    0xa0c08070503150a06032327030d050a05010905091c03020f130909050105101404110c010207050105010816060e0d0606120303020a20060615040812191103 68
    0x40028075610f2904892042c44401416043c03046403030f0781018001e08040901c144100310054042c183d0320398020082d074010310051800c000e94018202c07040c004810303031488411140c80100b001c00c464072220301c50300d840b036440220000750b59410804110141c83c00075019031405e60020f00e440c05030010403031003041c001d0641c1c01c0060741c842d150365503404280a000d40c501101c510720700340004e2070722440d002440140d05c586c00800c001d03130761041040e203d1255401001031814040c6650041410698001c0aa160340301d03610310300700341c0c01031866820780e800490203c40c036075114801000801070410440c0c00178484810007102950600000a0514400c0076441d44544440c1810100f130103038a074000350203031000c07000184c40303000141400781c060f44c03145000000140f0a80d0000b10700381e074040c0c404c002c401e07104000781503252500c50421621421100102a82010800c400070702507108106000710711050511458484104130609100101d2180442e000e12000700b0480101072401700465080400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 819739316 1250 819738066 819738077
    0xc07050a051e120a03020307111504060309050c1c1205480319020111040513150f1701230903070501020a0c110a03080a030207050c0405041a0a0c0807 66
    0xd00c0300003010b80c3d014034400d004900601c0068024142e01000420702c4600803a040c841045c850700034000f040000b01e4110162407020300041c0400da00c6034100340c0e00740f4059001c440001050304c000490002c1910b03024800c148a4042600400071741c00008031031142517090007402e042c0e00c0a108001100480401c61001c1d00b07451411080c0308401c142046c8056040140640c1d010f076121105540e5072002404a05c2102035111401d410341c030502038804e101c06107200080c10145010184032100000052840e0a5a12a000002c0b03800f80e201e4103000800b520300115103010302c0d0120b044020b121610345105142d0408a9001660302245094a02e1000c1c101c0030703103910750301c4890356411800744240c0184154000a26080c026a12881034403045016032000c4420785409000c2010040080c400104502c00c24081c056400e030082e40605402030080082e078110038406000a0211607040b80c04071403203800c503685460b00100c0250460343c010726030142040540c0181c640030b4503d4400500e00701c00c101 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 819740566 1250 819739316 819739369
    0x1303080a0b01021c05090306160c060b030c040e0601050f041103071425030f080702060105060306040b0d0503042c0402060f21060310150b0c010e0703080c07050a05 72
    0xd10070821804030180400e80d051142140e4034008245c0d500c0b420700c44d8461720506e80482e804e40f4124440400100641c1c9809840e4420782e42d0b040c02412110b956558503014680e42c0c081d454a45000d101e151151503c01381007590706007820040140c00001c0b885001d2841c0210034141409040c0481c0d4002119050001100042c2400e801407449002c0403014012441d1007150036011486241c1d00f0040d10a44400001940d100e00c101c0b81c5103070880d034440c01070780f101004100c0e5050240085400c040050000709012500230045041c418800f0b00442d9181c1c000a010056031a40c0300e090b44090000704250598030f1154404034003004000380003c0e124483c0000c4125001c00c11004446c4200c0003445940d1603180f481c0d268402c2e010040b14018004d0058048400303c0138401d104504a16410707942180c141d134244042d0110329001349000320b40e1503603940078050b40007408000030300042d480f80c0d1465940300d40480c0418181b1368a40c0c00713280241d01403138080c0819680d25030249004040c0340d0f030703c40814 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 819741816 1250 819740566 819740569
    0x516080d02130f08060703380a1e050d02012703060f020702010f08070c030c02040f0219030c05163c0317010b16050f07060f02061303080a0b 62
    0x348580541d1080c2d8440181c00041c1606400c4040c1044411400640b0000d6440300010340594485914060b10b80c4070542840340c3d140301044030301c2406d10603a4055541048950301003100c0c1c1401e60003030800c90b26048203007440e070242444007102801080c4c60185002040d41e00280800c51700c03070300741460607184050180c0d400c02510785440086030040d41c01e002c0e0a00c1d03420704c40000d500010050340001e400d81d2102c0e507854040e07007009000700c92641c2c40b541c10006c40d0f10301300c5240340001c0040ba071007500e42c9480007003220140041d0040d0070508a00c0002c40e10a5500502103803080f1f00540705004c1c007809103608a0070f091019548143d002201e000d90300720101c2601e5041c000f0310b9102400c5005200180f000d41750064604819140700c0e03158010f440c0744007440e10320040d00034440ca2625031700030000c008040c418203200f8010f0b2403040c0d04481c01a00e040030010b04003140c0344c010300c000410388955000382c07582c10860550070150000c5185a9401700e034130000c214882c020040030704140c8600d400d0405 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 819743066 1250 819741816 819741821
    0x10801171006030609020f04140121080307021e060910091407030305031008010e060612160e070f081603020f040306060e040c050102032b0b030a030305160516080d 72
    0x101d1440310100030198880c500031009000354003059000c2c00e03411103000780ca403c25100b852401d001c405003482c0c0580c80c01001b1141c1c3d55844120b41d216449203809440020010380c0594013544e995005000c0d0f018071b00000a8580c80300741c01400007a4410b0062200c0003902041015002c0c10610010502070100d06204042c0c00352000c180b0590304c0741c4e14000041c550300001450050031032141082c01300f6958080b190a84030620360700343c1260003039000b151803460002070703020501e00c200007941c0003406074a080c20f402c14581d601c208800e040d20f0042107482503100106000300000c0303061495080c00c041c8100c14480e00c0100c8a1001d0541c0015018200031203003051350300039644a00107001e220b850f0128854819819542211265511600031803558000300580b080520300e080601c1c18490035480340400d8421403044100308a82c2c60300200c0160700c0034800b1800880c004d490104003401c12444041003050b8181076001042420301441d500c94441500500d54141c000741c006482e0344680d601c2000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 819744316 1250 819743066 819743083
    0x151308070203030d140a142403100609050601030507081302040f1a030d031107060f090b0108060f150a05010305040501180f1e080d0f09080d1d030901080117 69
    0x1410f2202081007140c460454000c40c0400c61100c469080700e840c0c107003995040d038005402602050b8081d00019154450051584c0c0d00c0c44040001c1d00641004c402c08241014404605041c03074a40341d06091104100718003919400030800c0c0f808100351310b0002c800600d44000500b4446141352801040001d5583c2c9410a803001c3d0034080c0e003040744072016424810301c030f19607241c0e450090194400c0d0041e80d0b030180c23144c8428005004502c03071525040d65600c074000c21030700f0a610044c230f40e42c03801030020501e62641240130b040010010012030810030f5a41003a248002d002c10030105101707007a02c14580301c0389000f404691b42800d002c40d65465074581a8050841418490580d0003010000010b00521000208115008a1803001501410001c4102403450780c4000b900703420301003002d848907010a602032441c200c0b1a034400681c9651a54070305683c5c1c4d2258500d0b017600d40d102c0d10700705055400014029410042c3c10009c40c44d00c0803110028100b04030501c58000b005801040e00740701030030107010700034 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 819745566 1250 819744316 819744319
    0x115030b031c0801080a112209030905120607050a0c03090e0702070e01090c1e02010f05040c090e0703020d080309120708180d02010207090f020f030406090302010e1513080702 77
    0x45890b09180003080840b0300700300d05a40010307064000040c101401082d20701116400080c9004c0440e4103400b44080304446880c03c05844c20611541c00045060b1720600e40802d00c6603589107a00c5140c06c0c10001d0009071540401d05641105040c048000d420104079460800300d801c0001c0780004a04054aa1401e16404001560940002c00007034541c0032030305900f40c070314128a44c1141c0e62540f00d81801c440b0032645000100b82d4600895415103015003050329408a148000b103581501d0b9260ba0f400d4078400e540c00c0b0380119201070140b04076400d80c040d41440d01d1080d0000d111007440e54000504a40540c0c2c00130b05032050020205860701d0040c80701e1001c00c1032110b00903030707542c14500d0864102d03440b6040d10200010006248807103880c0c48c0e505038911a4059000305401c6051100c2c480c01042100907030303200f0507802c011503244840418040e40c80340b4003c038000a8007012a0070040d003580c8001d400d40030b80e41c001e0101c82c10404c00722a0070302e41080000700e045009801600c0d10080750b108190000e03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 819746816 1250 819745566 819745573
    0x510120204291206060714100e01060605070507030b0606130b07030e090c0d110d0e0f0d0305400506040c05090105060f0f040306230f040b0115030b03 66
    0x100e003800800140726030740790b5009142001d07001042d07a02d41040c003c1c400755052524007100816002d01d01980900b0f0742500407803c0004080429480d035141c0781f100c04014056035100c640840c1c40c90001e2146800404071810001e1401d0115603a464443e40d03940401852600b01030040741d9035850b10703019035090323003100343d103100070300e42c641c410b05401d9040103e0450003e105240042030303e00742a0701250040b9113180240381402c05140c28031000e80f03000c04061030000d10500c4058002c219501610b084c508954001c0c1c0708203061090b007181041000080340b01494248001d105c01c0c5c0480001745c0006002166207010b4040407481d1f42e101e042c4942c00710300503840d001c2c0e402c0300a001001c107480d4000c43c4520455161180d46c1c10030b00c000100248207080c1d125000340241d50840d42d001000780282e60004a90624040d00e0760f4500048503031142400f910040c1c81c42c4090100d401041c13038540c0021030414000001d152503521303041d0500c8140141c20240808050888206000385c109801400c0700400780c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 819748066 1250 819746816 819746819
    0xa0b090718021c240b0a08040809011119140105010e01050111030706090b150414070302091c05010e12130b0a050d050a02091804080406110a080403050114060105090306010510120204 80
    0xc1080140f400f07000121150140c0b900090003a42140c111810b204182d01ca0a1f55542e49427940103058210054a80c184542c440944503820010300007024034441d44143c01c08a00040e09200a07084152114180242e15000060003499812046241190002d1038080c1d91400b81c1003100b8214042d0183c004c00c201d080101c81401c10520351401c42c4500c0c0d4101c0420402c01d0030508100644542e0344131007001c0b40000000c218503600c00c1c0c000b000c0381d0002408540b0803144040c000c10000c03118000c140c1c0c481e5510715200704064000e0040e0010005100e54150820070031800311452040c00f0320440c007440340001080c0d4041c03800b54007a500c00e0400d890b010021890300c41c0084010390300c038108051050720f4800700300802e0310340441d019014513080f1345010b0a01d42000000e41d01803d52031460141841050803542c0005e142a0045c8043d41c4950f001062105d80790860520142e80984501c0c10300c4000d022001468070005a1a03044038000c039800642ea88600005603402024100d42020840c0009070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 819749316 1250 819748066 819748091
    0x10908060c03070e03010c120b0a03050f061006080c030a050a0f090f0201020c01140412030c3824040f061716050d12021e0a0b090718021c 61
    0x7541c410f211603103444006200746400c241c22034114032641c1d0041084091007030801d0509900c481546800030741080c04c110b80f2601d40354030b02550403083d80c095901160810a03c0d041250221004101900b0050702c035043c041034a0042b4000241940c00c4e2541e12000141c8034803090b0010030180088000800c0b00c00d2081c140b6400c60040603c0503409840380075040151940b041d80c03031441c0301a021030b00609180c201000c03134140e044c0200050b0704000c0e00c401880041035441c07082c00c11441850300990481c24581ea10f800f281422122140100b00c4008100501400c040440e07403088001e140956a4039100030b0005001482010300f0746410b145042e401003822519203d1040d9040100801c0700c100c2000301e1865104074440340109a00030303e0300c618000002e01280389003010250140140e484004c0703500324030482050020b45250300c44d40203a1913542030001441c07895801c004d80c1c2d80503107803071410400010f113010301030b00d5154001e41d070000b001c00d0100c09007080100300d812060f400b400700b4003040c1c0d07 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 819750566 1250 819749316 819749341
    0x70b0112020301060b090d03051e04171506010507020f01090f0902120108030403081207090b0d06051f091707080303090618011e090303021e04141207031101090806 72
    0x8100724081e40c40c0103404240d0b4005101030b1032040200818034100034416903404c23a981d4202042241e002d591000380b0450314401c00018101604105981c103c000514030100ca01e0f1201c85000150340480040902485d6640b10301180c2100d81c064802c020a1300f0030a0040310540c4031948000c0d80e40800b07070b4002c40e002d0a507400901060880600300f000d00c1e40c8444480d6101d1069220041c5400020400b0010781508604001e03400b071824107000034900d5442d8084140369110342c4624a042d40e50320024002480d0002c0006180340203c08540c80b4659400130280504020f0b00036056294118200e140b00544100204400307440702000343c030b480b814910200c81d640d00c8280e800104110135601240c0c8104014462900c0346c0701070a03501e40394030455804060003880007400c15801c040c0c0800056841d18030080750801480806810640d4940c900035031010f10501400390f09106881c111a2038060640001300e84096a40081072140d9240d02c44005845224556000484a01581c0c04201ca620b4090 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 819751816 1250 819750566 819750599
    0x130803041b1404060e1029030408090406080a020922020d0f1703040305040b0307260619050a0513091b03260316021006030506060f0405010e04030311070b01 69
    0x20380b02400060344038004d10306050412904101c1c4016158130820202040c01d03031000c2d500e0841d07d440c0e209914040c80d0b03205154811102510000f6000a00200d0b82c113151180c0070080170000d010704201c9981d03500180340150b025044102d04500c4a10301c40c80004021749000c0501e50044c01c141145130645040101c02e6041070040e40e4124035403040302d07140d1a411046a01c690b9250391401c0c98030341003603c0c0320143d03040600220208000c00c1c0e4070071314407800062030b038801d25805c2d03054968500c3c03e04c007000348d44401c2090079501d0761840700c2c0810050320b40020340360569404a904403004030103c00040010000b601c0081c04007100d00b040d01b04010b4081a50348140c80c0600c03854810715265480d089140030306841c0c0e00401034000c000048140c102882c3d0481c0d2101c1501c181c9106101219031641662000d070015a016041903091101a19007806000c016040a48050011398500611000c51120040c005001e042c1c65050f052801c0b0a907008079a941c9030310800b1000c103541c4548a503220314008 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 819753066 1250 819751816 819751819
    0xc0302040c050703120c260a05010f120b150402070804090506010305270705100302090307080111030403050f09060d06090f050421122a08130803041b14 67
    0xc1600522040b8840d0007151102501501e03070850b01c80c3c0c102920002019184c1c3c10b0303003c01142c03901d088140c0055000a008002c80f90743c0d4081c1c00d040c00e11190040f01c5040c1d100589c0000458000c01c18852481488542c07250410407070304259030346c60701440e06032600511150b84179100160f41000c01c40c0c102e001d48265000440e0400c41c95990000540444401350340308144031300d0644128bc1590041c02880451030756400684a00c595944007040c14450066111004a0340104d06071400d42004c2003044000d2460350028040d040e400c0b00c500141d40310103003001d4100600041d000040c41c42000403a600f00c14050f0100b551041060052001049107000e140c4501d401e00704810407290460180d140a140c01c41c0c112051500b510614aa0740404041017034284008582c070a82d0003034261180c090b11103a00400800418041e08080e100e5286500802c02481625401c1c85501c00300403040c03405456101c40459a01c1e125030070120005484040305d43c244c0581d0741004103a1030a2640b800c83e40540 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 819754316 1250 819753066 819753071
    0x1115070525080d0c030f11030a150317090604030510023601232709010303090e04060f05130309140f06030a140403080403021006050306310c030204 65
    0x400710303800d140054a003400a011a007042c0300e041e00c210390592000054030810700300003504580038070000054821070300d0710840345117001c01002a0341f29140a4010749140141e911040ca5045075500c80f078246218041c81d20f100d60100700002a501c5150843d40610f40100841d442e0303580c001c2518010f50b00c003081c1081015003d82c07859044140709109012101302c10118940c51501c0380004441e84100b0700002d140c01d110280e02038000300b000c1c600901200d0b0042100303600720341c84150541a03e003800300040340201105001000400d070b01c40b0080f026100840360a03581901c03207090410103030043c90300f6800c003c0e1070a0f040c0019484a0101c0001c828800d48641d500e282e42c0300c0b100f9450480000700103406c0985000341ca48207140820045601031580e4200041c0030746070722140108810b007210b04401083d034040601080c5601000711032030314070b1541c0e82800160304200100b83c07034440151041030000e00c420020512100345089204401e46050501c143e00655070801c08861388544c03205070301407031 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 819755566 1250 819754316 819754357
    0x90903031802060a030c09120803060a06050702010c030309020d06050a02120108070f0515040f03140124050111100c0e04111213050a020603070c06180b0711150705 72
    0x1801507030355a40d0a500100018101507034260140c010b0050f0a01180810100007804501140c448800014160240840755123070b180000c00e200a048103a0484c8003171200c20700603503006030790100017a840c1503414600840e041e0321030f00c0407520010180c0d030000c1400e0f041004000c944515613011701102c400142078000c3d80d9030fa400c80e290301c0701098016802c0441241000b806241441420007032801880002140740a69452841b007009809030006c444e414400b08c21125842c2e0240209010f1501c0e508045001c07507000552601d111445100da41d040c45030b0303455001c00300041801040f021a4a0020900072641d180c0001000810244141845140f8040000c0380d00020380c0c059406041d0104601501601c441040301500342c070b010801c6031244203498184006032602c00c081c5d03000e0324142d1074212100c0c45d5882c009098503500d4030a41c46c5d020104980f640880c07004180030f40c1111231414880011001030344140d007448600071030200320304948402c0c40768695000c0000c00281150000000301070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 819756816 1250 819755566 819755591
    0x21020a08162009162003091509130903210e0f01050405060a0b03121602010314090a150f1a030d021203220203191202120f09150409090303 61
    0x60b840141182c0100c0c2110020b800074410180d8881803c1490030401e01c15003c041c8001503600100c0c0c6029001d42000c03a0004c89401c0068959020300f03500c0d10440d051004100101c0d100507400300c0e00a088585070300b030440605015114031f0389003810800c072801a09104181010280200140d92800b0f0b01c01c80803c2002d403501071081c02c0c004d66100d0050011519494000400f1304194503040d545030052007031103060b1070388000007000380030400e0300105640d42107400050f040310383d0003801041e1030f203d450821803410004190700441b180c1c0800340031410a022455280100790fa22030b90b25241c0e01c1c1040404401031b260106a01d0680120101d0300c2c1c0c000250002c81c2c8821000c1006a04400240f01003500c4d03240b0301400d05080d41c0c103201d03540402c12441d00040e00c0e007800110781c0654800451f640740705025400341044440d07040c9000505256800d540414a140300d2120208040c2c2000302d0203409a0340e5400320070401040481915443d1f6840315643c00003081e00810403000300c0c1c40e210015068 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 819758066 1250 819756816 819756863
    0x140102010e0303010302190e07022d0d0807050c0a032c010c0b19020a0807090807141201060504060e071106010b27120106050a0b03010321020a0816 65
    0x200d51075101540c00d692070340d800d00c15048041c1d02242c1b00c1c910506408203065120a02c440e2003003c1990003081c20240c1ca80490080402100034121034003488030074040380ba0700024820035115064a4001e140b035131082000c0392140500801c10715140a8805040c003410351000e04640d203013902d03a80c40d410180d2080c03000d01000c00007a10050202c3d40c2d040880c404192030f4000d95a00400342180005a206901c14010490f80910202070200302d03960305000b076056200c03a07154040c0244000610065040491803203607691501f441c2c9100f01c041c00b038400e003410800e410850080070060414405207454200980d060181200c2040000d1080350003090200d000092290484074100801d52802c0700801500c072510041c001c030b14031032940b541c442d04140d4a9481020144001000000903186d0428041003660061a4003110030390070184010300110301e048482010500601fa114040004c410310b00303034100442c0c1c05000e0712581c0d01143e9501c0301071001700581011486500d0100c2480f8000030318640 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 819759316 1250 819758066 819758081
    0x15050402120103080d020f0a0906080a11040b0d0b0a06030606082d0c190207050a1e090c21020405040f020313030e0d1b080606030601060f080a020405040e060114010201 74
    0xd91054950041011604c0c14005001c6030070f2002000d45802c1681e04543d8440d41b02511400c006238102c07808000059102c00c0310350b000300382203030280300d48902c06c20b80305040e0140d40035003c88a034000544940340e9220341c3c002c0d10005809440140642d81e103950160081407584100000b08421100054112000001c0340a000c10b1626503081060016800c40c001c8a40c0104502c1020104100c01652004c0300c00c0002040c3c3c695030300815025003017200380009e40c0100d501c08904031000908080b9940403041b8070380c041c3c2e0300c0000700041c2e028060000700d40e19002d040d15903e1061084840f18030703100742500100251a01034a0501108400300c0d1910b040b40b10454403408040d01c0039282100107032080501445000e402810502006c08076202c0d1146e546030f803440c6001c40d210560307040180010030f020840d48920110068425903140c00e20181518001d0b06e40c01c0100800d4cc00003800072440c40d41910040d000180c820481c031000d4401703940d82c40c0828000e80c2c030000f14031000035070035620500940f00d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 819760566 1250 819759316 819759337
    0x30100c05071e1e0c0320011e051201080102180d02030c0d0213180b060405060d0f170d02070c0902090a09090c12081e0918091c020115050402 62
    0x80c80180b6914000448100c0742214002c0306901c480480c40b030001040409903000e44c41e00c1440034914944541c1e04412401070020346003501080348030030ba8001c00c1001c0500340d440f450303001483c1e42a404a07010304c941105251014010b000200e40c0031015030280401c0241d003018900488400740801c4041c04140500a41c950b02c6441d13411054209503880515592000e485079410b2100b070021b038026a22240c40c000b0709503c1d0700c211807040c00724580000750040b105540400103802c1c05800314420500078031300600036480d103501e20320412084049201545600a00c5151550f10240044010354481d120541d440c40000c14040303001062132084034801c03440100760000a0f0300d8101014040c0128200a50b900d6040c0500000d200c40c08804d020441c1c0d2298a540d6500d40d81400d0340c1000e0340d0380007034410071807409220308140c988070401403389c0e0384841c154a010b1699400312540c542101c03e054004440b20040b0325400c025015004040303285602c00c5042d035101c2d2204c0501049001d10344102 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 819761816 1250 819760566 819760583
    0x90f031305011101140115030f1104060516050601121b0503030a0c0203010e0106121703010e18011b0906030c2c0d2f03010e060630100c0507 62
    0x30441c5602031551040c40300f10020000c20b503080011102c8075400401da20606410300c14100d01400d0b503505121b4885240b86c1000200f04000522142c61064081c5008090034420700243c14801480b08040b0203c02d5580242160301c0c1d5132f114203058126a4424800719525618030700380c00c01c1003a1002090040d80c102400960525004410894095a1111050760076560342c810454041c4030a00400018005040c028120012146001c1013404c2e0001d8101d40e08400610041c0b15000010100a03004040b0132142c1000c950030045613401806101d060300f2244030310320201540b260304423040e2030032245c0c140c8040051100008081d920350206003007a001c0030b8003500b0090094400b071401c1c4405150041c000640502d550740c1c4005440094580d82105040c2c030204094280000c801102d8406405900a0028042e2440425038038072000c0c2100d031150460381e4107000c51499440c03840070b0000482400351800a42da00b071084e203442c0b007040ca00c0000c1d828402d02c003c426005c1c5c0100e071310f2280d100441 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 819763066 1250 819761816 819761819
    0x12081b060f04170f03090a140a05060a0b0414040b15030c010912050106080a0302030702100c0f0f080c03181f120203090a062d0501080d260708090f0313 67
    0x2c2103c41c00010f10303420b140003001d00c68000310b00c420300e0245209078101e100804090820b410301480b03107400d507401c00c101680480d04060000e031010400070b80003680400086010012400098058184130380b00d50915944041000140069030740c107a0300400080c1d44103641000c01d03c05041e00d90b82e048207142c0c04500980800c01102c29003a0500c405240035900024410391203003201030415004610650060307001040c400194604803c2080b1240740d02d040c035081c0301c2c0b0300340c3c0c800710410200903000d0100403040c40f080c1c050180307640855503858a6841a03a540700002c40e4203902d207c440f0308446016021152900c403195140100341000340b01a0b03241c44603120510201000039500c01000200d480c050207440000040050180141240f04000d01c60394540080d00c00100c0507211240c0c94406905010042010207030100e040c0d900340705a403a02c003c044103aa5404040d40784058020740d0340e00c2d0f0b41d50801c42116441440180070348007000030740f02002d01054425a990140c414a01501c4400c01c50 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 819764316 1250 819763066 819763073
    0x504120806091b1612020a0501060803030609160e031608010501120317041a0c1903091e0c03021804141612210305090c0109140d020a12081b060f04 65
    0x6010101c50300d40e4110000f14035580c601d90045c580b0035a410169010a0285041003402e00406015100c004004c6065190a800182941201600c0c1e5181e00041e14504c048161094100c00103070800030b1b0848004040007403251200030101d110f101c1d100c0d4602000416421010518910b4050f01075448844031040c0e000000c0e0024000b91088888001001000400d030b0180206039104410000d102d580302c2d100d20302c185012210071006c481c10549400c0c0c0c20000a0b001914031003069801d040d00000b166140d1409800410003908041e500208680100440d840e0642c1e90038032462040003500d005605c1081c115a86d0182d115504071400042d10040c80030004114900805c030303014083c400b00080c03560790310f5070080e1400c80c5c1e03007000261074000b0000600d00810840700761000070718041c00c4030741c540407131440d0788120030201030300c074241c0004100190341e60100020040e26403a60504100ca0b641c0c5480001c0ba03010744c1b00030320b401c200f018452403c150701082c46c0344100c10b084201042580c907580c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 819765566 1250 819764316 819764371
    0x3050309091f06030504120215180304090609020712021605040c12020c07080c0d0302030318120a020c0a050402040b0909040201050d020a09050a09020403030915030f050412080609 79
    0x51002e110980c0c0c071280421540c040003121001494251400289428141040c40c50780742d148818000b90f510522421705c0b6004104000c4d68441180d80c1c040180f0b28010310f2041c114821540400c0207141403150208110b001c0c0e078000d1844612030300884d002c0e407400341030681c1ca403051841d1050440303140990812442c10720303801c100c1e1001c199103041c2480940100d82d2100302d03040121140101d900c00002407140c03031400c0111800c41c0382c0c00c0714003c0000e0400e644c021756070702c0014250307249100c2c0107100c0f20300380c94208048840710a6a9a00c507440f403d40b150000d5455004070742d028031440031800005083d092034800c88d0207480517103140a00d0b180e01001270041000000d44128104401048111107408081c80900251240d6566052844c0c5c9010204006d401c00340d0891007240b441040100000380c0c00c1303456501203440024101d510040301c07100542c010044441462107060800301040b08205220010428208007502c1300e42154031000140611900221440c1c2d034a10034502013a0049003041 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 819766816 1250 819765566 819765571
    0x212c2101090206030712050c040b0a030e070f0303020607080a0b1f020705060f0703080a0e0d0f090509040b0f183d02030f0903130501140c01150911040305030909 71
    0x94004644040c1a6011501030b41c400c0780d5050010300c5005603011481b610f03014444e00b08070f841080343c1c1000e007031580c000c200344211803199003410355401d03403803890a8041c440034000340b4111030840b078140c3e5213090281d02c44c4412030303004000420f07000000340505264030840c1720310725000c2c0c4204000c00d00041d03c1440c6180d0350268900b0361042c9240000c2c070b0b0b0f42e44d2000301100c200258249441d040c0c1442c000e00b0344680a800b0032384140c200b440d000180500015000421a007926284616200066003602c00403841e400464200c0c4c4c000341040241310052110600450440c40e2448480d40c0703500d14000c2d047c6048140c02c1083e00b01924101d40c0060310b810880760138080050541c07515030032145c01c0c110b004802d4800d0034201e03004400c00c02c6115030a10240d82c40944e80703014618160b00c0c0b410b0020021380074017581c0d0600603511049021009420143c0f0500444c450003003004d8a9140c171145075800381d5104082c030301400c00300d82ca1a050842ca041d5011264050300640c00e04061000300440d080d0300 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 819768066 1250 819766816 819766879
    0x12020f010624023a03020304170913020c07060906020a02010f030c05042c0714091e120c0f0301090809100c020307091505121009212c 59
    0x162100340482208203000b680d1404c0304010040540c15051200c8404511090803000505106004120100700d00003a003174140d0050342c002590795058000000e9038104805000e556071880843c040c410144009900400d8403100d880b4548070035a66842242c0e00c030103401c002030001305c0034065603180900030b80200b0301c914110708000e4100b41d2920382c00d0004010400c5e101c0604040910411403181c108240c0d05d4002c00307a03140141254880d0099410584181c415442c01800c1c0c203001c1c44140011a681e0300300141000300800e08110303201d095640e9585d0040307040ba225a548030081885840c0500c144d07091035a006640b46d0a0406c2101001f842a03061a400c0c002c2c4a600c0706210011f90b81482036501904084c8030005240c49080b62501c201e40b195004103003c1c00c0c00d503203001c40100c80002d014201242c10700f00443c40e010b0516041607008110700698080c040c13904c02091607103070030040c00c64a24404070091156030421150200c503128a0703d1700190850b4251340c0c604401d641410160723210105 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 819769316 1250 819768066 819768073
    0x2c04020f131b02061e090a0b07020a15090302121602040e1606020607030c170a0527070e0609100302010f2609010b01090f09021c0912020f01062402 65
    0x22041d60700740c0000c18007900703000140c21107810007003822401546180110241502c12551b45001a4810794643c400540904610840c00000714038070f100300b201040055010100da4211034010310428050101594102c000d40140c0c1d4807800e8010202094881c00402c040034007c9004554003800010300c00000200312038056804050410008401550000d11299000740301514000c1c078010116281d4104c00403c00c0040c0c009000d4007880c0c21000341d0054040d400c0010340351244184954000c880440300030b194401c01d01720030300100e00860079000300c1d4400003c482c91a943c100412168072000c880150700c06115100901c09035104440d200b1101c00715003030150788407248200030403041c00140c51258a03070f8001020009240c0080c010b03160401401e0904950f00b44c2400c000f500d0b505a54000c0640d00c40d4046100c01300f42c00c24195501e800d00700401c0401106080d41171024a949805540c000503200b00c601e603010405051141c001224140c00d4050040014003885000c100010b0300c60710114031 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 819770566 1250 819769316 819769331
    0x61805060405101a0c06160206010b0702060403080306030f07060906030b1f0e22090c0e1b030702030708040b1209030301030f03210c0824011209080f042c04020f13 72
    0x1181000b141e03001d02080c05011f11288103100c2e00a19102058124005a030b005005500043e00c444099400f0b80c1da102da00142c5994414011134900b0380d05402592013486110b030f00068154100d90940f00b694955502803043e400001d007406000c1904110302c49a50007000035915406100c0c599500c40304000a202c14803904245104420345c5114540d82c113861070707859201408200030310703941c24001c0c0001059070706a8500410000f039501860500b003801214000001810248203204555900b0307400100c45803147c1e201d03c441034690700400a180c0940d40741001190556034000305482c1203075484511019001601e40e4101e0b02c00d4030502d010400c16111407402c40194501c0e0103103c110b1811950356901524101001540ca412900240300a4401001d0186026607004203007071900414420003040500d518980940c0510503881c0d1245900000700b4003003099072411650641804c0b250120148041d0b17032511070000c0100558009600181d01030208006003800314400c0c103145a428000070328075 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 819771816 1250 819770566 819770587
    0xc0e06010512040c0602010f09030e0d150e030306040b010201021c0207020a0306060308030411010806010e36070f0f08070c06060512100e01050702030a21061805060405101a 76
    0xb4101520100c80100a0b07440500041d542441100040301005c4420300c0038240585004c0c01d00c14844c21654000d016100800f014055400c2c8038040070b2070900301c10004903107c681c4203901c0350802d031000c0d84a2030901d131100089600c14002d4401c4e00c40c400400250300c04520140034029408544c040740c10010042001000c5201849800c00840c02120701c1583c920309443c05124281441164a06102d4a00107003c002d03644425052512901a90f8070074503003811008604100680901d2211000744007940b0640221401c05a14040d9901d030304c40b1800c8409040082e11461020194140000c021000003105240303e04072900d0828010400096110307220b60102d1800c1d4807040300130302168001140034424000d68407030940c0c04d120000007041030307040c01503000f5268454402c0c15010080150010b229001002060161a9290b0070702004040c0d5039000f0210303640b9945007039080462038000010380c5030401d030081e54810700c09805840a8131b824510380040d681c48d290329200d0408414030444019 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 819773066 1250 819771816 819771847
    0xc050f0306013602040305060f0f0106030b3d080c091011100203071805090103020f0a090516030516081812030a0605090112120e1507030903050709090c0e060105 71
    0x43c1d050385400565182c6c01c50801c5842d266000d013030903801031000010840300744001c09000d03064031142e180109040007d2400a01503480d01d487c625180c100c1c2c50040703091281c54845419501c0c10426401d41050440c0350280c40307094045512a2200008100710150381c541408d4844908040c0d05140d0804150140c0c11407507c0d11004c00911b0996000040c400a90741044581401055255100000d01e0038540822010b07241840002d01501d14034040307848580d5070450000143c07140a1041100b0300c1e1010321413082c480c0d469202d00100c0c0c070301004070344c16840020f0804c003640d8060302d641d03001d511142850031050b600d490b010300183c040c6490b41c01118080e4030055004c0c0410703520200d0310f6420142042a105e01c10791010241c1403000e0b00803c00a6840015603104078807504091002026540125921585070780c900b1f10b04610005100041581121550060702d0041040f6221140c0311030481d01260a501405043c01c0740c030007010040c540c0c05442d0164071a20624246003064040881e1001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 819774316 1250 819773066 819773159
    0x1203130c080114010609090605011211040e090c0103050a0513020f01050d020d0e010f0b0d0b1b03010602012f07061505040203072601060e041d16030c050f030601 71
    0x5480e4030f001c004021059104000002411110900700305e1140b0301000070b840d004403511803484240c2c0364400c00d11305403412002e4030018610219600031307510b044003809031604001c2d240c2c14086458040414090940e1b8030906118605500c14048445600d8007004003130740b1824002030410804000580e048081400034144540c41c800300400ca511003814800d013980d1006950f910600c1c584003030314400da51804e8150f09590741248019545440305004041e0a12900078a0000c001c2e0000c00041ca10707605600410300c0301d480d40750070034450100c0b005411424070b100050035a0340001b80240008a103865104071011642131041c480b440b960780c80803c00780c0e042142c030310000c600315038501d00c00e40b400b0b141b0903d070030312070508140019814090044d00216403445003901590381c5004100101d40700350307882c106c0f12401408541481c0c007170a0b0b60b0056070205001c100d440401030301c0002002e00b072000c402c40c00768a0040141170703e46c0c240700c0d61654815071a0b07400c0c800e200200c0709410000c00c0d011150305 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 819775566 1250 819774316 819774341
    0xe040f020301020c1b040207170f04050d080d0e070e190e070806040507080f0304180e010f022a031209150c040609050105072105130e181203130c0801 66
    0x1141c50b82194a141454022017509002d80c0c0100808800225555608001c03000c0c1e88806944070200310000c8115802550003850304210741d00380074414000c50a02400b074822000c0d40c10700c480703050309890540b0b0703901170b03c41da501e03c001348000f06904841d9007074032040c0101912000550030003180c0c42c00d8901130300350b80090301a4000314140400d020040c460103000d04050401072217030440706104035a07240300d23a228a45170f0b400c001100001e04811340e00060404040203000340180104030109200a6109041c008001d80203a03c41c0c1340703402d40c00c0001d000d9552070500075606015440d032011860a0000705803ca460090360000c0c44003440c89144903010310041d4450b01d4a6909040f03002e001d505e6030340c0005061120034044600000c00032003c4d100425520552150300405c00d2609071041c0c0100c6203540310300d5140072004510350b0150501e00307101e094905100098414411070315074492904141d081c3c02d0306000c0001a50030515042001501e41c851404c4030304440e0703a0001282107070f07040719a00303 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 819776816 1250 819775566 819775573
    0x15070c0e0a02132c040c03120309051e10090c0b070203011e050f07090e131103070311090c0406080406020c03041a0a0327060b24071a0f010e040f020301020c 69
    0x409030008040160542c031381c2001c41c41c284c80e0519859003601c05005100080c900091941c0203040346110707402c600d00c0c1c01d80c488121801000075050044811080c881d06141340d00c50001100700c070036018050549a16041548000450700780064121350342d208520581e015921750541400921041e07454020840e1203034000140340c00c0c9130003545401300025000e20108416484240040c60022408541000000c00407a0301d070a5a89041e40580140c41811a41070241032000814045c8045000c000c1c150201c4000806030f407061303449812030080703000d5000040d10403070005000030030a500178000c2e60600d03012242455503c0382d80b410210703280e135217040e007201000c10240189500f43c000e03400c043d6044403032106145640003c0f03890381c0d8030440340984840d0322080d8421a44d10340220800040300542c200c0303101036120310b502c2074141c0d02080c022684014143d400310840c0c0c0c496121540958509080c0e105c0b0b03646820401c015490007e4020346078001504180801640c00744028224013040001070b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 819778066 1250 819776816 819776849
    0xd2003040e0408031b0a0905060d200403050111030903270616050f06010302090a0b04091205070b1006020d0c0203012408070b091807090b0703080615070c0e0a0213 72
    0x2404041031401c04507841d170480030321655400641040c00032040d01d00c103489907a01c0340000c00384100a41840c4040c00700301d520255501c0c40b800300301e0307000303000b80d0340680001c0c0f02201d026418855140b008a4031044070b90010722040c12011500000d1005101000506490111801d000903240e1b0b0f01292a140c8000400300b00d00007007100c1801003075806c4090305d0142074690f1543d00454240705004000c06c0c242543c481c1828207582e47c0313610007a0060313005880c0401f54041c7e440040d1241e4000716007520000609000551030540d032030704400c103a803199805030900c10041003043e5007443c1c00000403039042d502c2d000fa0800c441c4100503100240700fa50900541040d1411407014140000c9400c05003500c001004044041d80315034008220144a104850b41c1d160342d440c80c03c0b00d80c0b1041d038025042040300020124289a0f0205001e80500012200c52882003c5070f24400050301c00d4180042006e1008102004100c80302c1c110b0745e60224201c18054a00726842007500100c20f855000047d401025050 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 819779316 1250 819778066 819778081
    0x2031c02071d060a0914280203180613150f02190e010807050703091205010e2a0109031a0a1508070f0b04080303420f030d2003040e040803 61
    0x8690740201400714041000d9045105034850042006200001c00042420400c2d83e012241c001070f051210701f07100441d124248002080c291040300c4c40c08001074442d10300414111a480b11071101c00d036510dc2c0c0700800c9503014034580c0001e008800d04043c0a241e09001c01d03d0f030300309510f01884030484559281c0824101950000d0024000a000c02d01008002d208500000c2d4004080006841e9584030b002841c42c1140350640c00341202414440c0207005588181402403c000034000d00c822201c5814136100714104c00440c1c1a0341d882c4070280c00d4003044a0540c86134400214000c0e000a074112011510008910b8a1a024081d80e44281c0066120702c2c0f040083d8129030f00d90102405a50800c10b10341850b04500e07907a039000292558a00e80b12203041041480b4020303564090310603140b61801014012090000060107540c0881401a402c0c900540580c0c5070100320ba078180b03501c80d1a61002c8441d62100120a9003000c0785880091200b0000031400b200c004004501c118071170b551217131782c038a00182c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 819780566 1250 819779316 819779329
    0x201180608180c0d0809150a1101050601020c011b0f020303030705071506034209030807020607051e0405130c11070305030406050f120103080c1902031c02071d06 71
    0xb40c0e0b03491142c0002003040340da642c40c25200349145400003c096100d82c5248001040c108091113484294940090500034841c0c1155003001400248c80080226540d00e000581e29030801220040c0000e40d0a06006081080801e49800c040d0003a061940412401da0100c1c0ca960700650741c6c040400e90105043d41000780d0076000f00046483c5250900a040c07a5680340310f8245408003a05251201c0c68282d0103200001004903c2d504c49212445422003000400741001806160016070003e4145400600c2c1c0c207000050310350142441e9500c0614007603c5140030a181405d403d04404556010800000c1c2c59a40c1008048001c4070075800103083c10105101030101510009030702e8075a0460714081010820200a440494402d8203041d9650303401d05104141500c217016242070055a8900013000f40300d0060040c2480070a01002c5078040c02400840d040d12034100d0400950551088000a107840d0030b11401400c0d061450044031021360300c075101180107050f40a4650302c11481141002954600381 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 819781816 1250 819780566 819780601
    0x901210c0819200a0216260606090411030a02041103090d1403010324090b0a06090209030a020d05010b12010b13060e2a0a181a160201180608 62
    0x190080041000401d00c510302e030140d00b1034064030360a002c035003c0741d44c81c002e001d02c28a11b6103000e4042c1c0b070f00e601c4035403050350703030344041c00e0780e9612101140301a00e500000248107005a0b801414101a41d58941c3c45101043d651011544c050051021200042e2514020300c403c80d80540081500c07450101e000070315004243d200001000905500410b000c6415402c80741909c2e0003101d04100c4c8414004031107078803c0b092007020002c515240c1c00e0003d010f03100030018003814054905100d02076030350700010168064554100d0341500100821801860038080c00d18a80303200c0c40021a00041420000e804021108c035580d08907515184035950f10325024070020b403145d00c0e1f10000c108041c00c00c0040b21800030018903901426940704404004030306110802d03240710720038000c07407a9103a0030064024040640364a01541400c0b050307102203020042c0d01855560759041311541d504104028100450000d25203a040e07060003440c43c030305076032500740f01f066202030135882d00e40b0006400c026041c10b40b8800d0a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 819783066 1250 819781816 819781861
    0x1e031603080703111c020a0b07020606010207060323010f0905070302071203051018060e0c1602012d0507030e0901050306160917010506130e030901210c08 68
    0x6018091000540301c009960b0542d0b054a401d00701c0780d00401a5918020b0841e802403803040c0c80100210000d40c0c001250141d0a110b189030b075403583c940603001da9907403c0580c0c5050140e00f00000512416202e030740043d0701a4251000041e160b01500d10501c46642c0a800c082039a030482e410920804285000e40381d00140b09103011072402c50300da110220300d0300c14107100204050300c5201244203c00603071100c2d030213044001202e11111400c41030a03c000c0480e8407914201c01e003d04002440008407005940d5a042c260415411140701a80112658210342c00b2032800048030b030f0600ba42124201d07414054200d85600c7c1d0940d100d07514280a481c2c8881000c0c1a4822480840140a00e44010820a0300710380050015411007030300c4001a10101c40c00d411110301c20394031395408218500c05400042c002e41c800e4400ea03600c01c00719031045081c0c5180b4410030701180c0c020041039503d544251603107a849913a4030450001c0003503080784e0ba0165181c03000e01e4400191010144190303500401078002041c0072 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 819784172 1106 819783066 819783103
    0xf08070615061103040f06270e04171e09010e092e06050f030c0403080d0914010e060f18120a03050f0f15040204051e03 53
    0x859100c1e41000034803038000c0859146022046405030307204040d200440c1b03820154107071000300c41d06804006940000324945c4258404c00c00c7d82c5c020348440b42108030903003030038148030000340801002043c00c603078200020402c1c50f802150704851181e0f4884816112103100d0016100d007140003041a41000301c04082000c900715008000d4100741030120707440f01c017201000941f00c04080030701445020401c00c014160706004054042c2d50722654881c4e06510b0035440765500c1e18550802d001035000961076030100d00030031500c112040300400d40c2c040204820400c10750030301d698000c05401102d0004040c1c000c5802c064803100060b44111440040703400000c1607000308032940d1f101a4040001030b141a020544002c0400c1c280b5021300c44d503101000440c0c071410b40c0008038141c9501c0055001c4c0d42000b0000d05902ca6514411713021210300c41c1191400c2c4014140341c10180d0012182c1c08204 = true := by decide +kernel

theorem cover : BRFrame.Cov 819604316 819784172 := by
  have h0 := BRFrame.cov_init 819604316
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819604316 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 819604316 ≤ n) (h2 : n < 819784172) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
