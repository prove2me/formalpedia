-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3033
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:27:50.157407+00:00
-- url     : https://prove2.me/submissions/3f23171d-6675-4f5a-8333-c039cc0e82d7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 545323741 ≤ n < 545503597 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 545324991 1250 545323741 545323747
    0x6021b01030615080915160206070e01050403030e1908031804060302060906071511040815040b04080d0e0304121e0507091509020d0203063d110d0905010e03010908 72
    0x2020607640604c0040840f4210700c1004080d03c0c51280c024950750040d0a0340d07031901403402c0b4080c802814008000c08010a00106008032003443e42e0220444044079010f00c1d1808e1111417490024203d5011440d150303558003240000814070708408001015240e040182c1a0003d0040000344000e0316018030000e944150280006405401e141c0000d243d00351003a244510f0441900750510103d51040b0103881003800042424442000308100fa0240301c00c13030070000065880d141da2190b041e5840104010542040820642c02c6490641c00c91a6062200426240c54035101e000a241e4070480c40010b84500100c511520310240500c1404071545400002030030f032450078040502d01520ba020b0106000c8200d81100140000f610300c0580b130070030388007c0090303500c2c203019040006d80c10b51505044096108011010008044410490302003c542d000d4002c1d08040d9074025170320b41080d0707510b00f04640202048242100e92060f0114252542600c1e40000c1d149164181401c8a80101c4000d00b042c10030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 545326241 1250 545324991 545325029
    0x90601030303050702010e120408071202060906072d030906050a09170c061804061a1e09120708060702070f05060c1603060e01050f150f1906021b010306 67
    0x280d000b041c2d00044d14000807800b07140081c040c40c0362220280310340c806c141001c1024414010103110040041890030248455001507400062282c411040220720619000506000b048034000c0070b5007001207119000d8030034882c04482c8445206004a0850000301680c0012804034021010343e1110919a6500080b050801d15800403609804655084601c03d1198106050351103100510b03000802c90b18020902d90402c050000341e540e40d80087c50300141c2c0120b601c1c42440744505461074480c0500d001d080c2d86a41c0c000d0300da4140706a500040d000724004902c0140e2040008008045402072400c441d402d0340d6442e01240c1321489070203070600801105504014501d8848040c0512000b0300d804d940038002c00c240200403c0b001584111411521124012a0380c0c60070700c612070744042075503141072541c501f101d400c40c0510320361922030b445003025414104943e05d850003080244a000c6007101d06458481c00065519011843d910342d201c1c41403c040c0c60345511a0190304200c903007006108071410341c8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 545327491 1250 545326241 545326247
    0xc09051e0f061203090316050906042f040e0906070e0405280e15040507140105090118030602030717100305060711120a0c033207030504030210090f06080906010303 72
    0x5603e092049911050064003e140e074144911104520140c0c5049021171402082c801c030007000a0149100e6490034050b0441c219458031000c6a540d803140916016a80d0b44568600d1805036130403c04040c0404001c0200b0404001500b5006916075226030a0040002d4200429104c3c101d0b4580420f90a604040c1e910000c0c0c00c40541c491410014041080f200e01007031940b5196900742802c0d40940c402080c04240306050140102800b40070394090030b810490400a01a80300e001103250412404106110680365810500c602540d0721260640d40c03401c007000001d201c4401c4402010000e55610085160b111120700c59400722544940035082d1995550016101034201c0c040140780340c0103207880d1b12044400320b0300a01d8001c03c079840c1d20b03240494906000305203032516129100840005500c0702e086a001c1504106280d40c031024890752140a440d08803007a0041c7c0c0e02c001d40202c01321560342030041d0814084400d60341640382c0780111568825040320401b000350f603401d4680e000100140b0101c1d01c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 545328741 1250 545327491 545327509
    0x90f11040b092b0b01080706020601170102190917010b090109020f04090501120b0a051023040510050910030807020d140d0c14010209031005060406030c09051e0f06 72
    0x200078444003c91641410b041620741d003c01012560481c00c1c958502004603a140950251050300d000704881030924001035515070042c0207042420440ca2039806000c0340940448100c5000b544004c40340c00c1d02d4040c00307014400b06005201c44e5002c803510302260a9030520070440540001003080c1c00c1a444c0515500003903000340401c41480f041040081403041103401401d0007030020505001c141601030130880c046107400f800d44c00310142001306000460306005041c0042e14121080564040000101c50490311a60304004d0f400034100300800c40302d42c41d4130030104101c03003068030304130740c0c80c1e80d801c0380d030300d03003540607000080c21800184000c0001d41400c802c1242400d201d41140c280b0b5560070040700f0300c0d100c801181340c4001006003c1d04010440c4007400006c002c07103c50300039401e004485001070340303405407031100020095407000010701964441c0c011400035a08031000c000c0458448040a000e03207801c689100341140b407800e00a00d1144818603503885071541400e816069101d07101041880c00d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 545329991 1250 545328741 545328757
    0x1031a0d0b1308120702010c0c03020604020907030e0d0306050f060c07030311030409090b040219081519240509010302090402060a0c02040c02030a020c0315010e070c051204090f11040b 81
    0xd40340c41c2c20400081c10000003040d00e8480d0049662075850810b10090031f50740110b82140c100580d400100300004d400086041e00990304070b400034426a1941c81c124005c02c0c81241e8503403544551050010b05540580c030400175144180c810758040d00d5100d0500280b4400d114440b10103901072a410400300b4416006618032103601d00c1074030310341070765100f1075025207081010030b270750440a01d07040c00b0452419030450b886100e880030911454038608403880f500c0309890080c4030846e980080c00605080e0b42c052441c102d145640d50f0400400c60000c0382c60060300b0920b0383c000d640100c01e200c0441c484c680b4540c030034126640100359007066552942070010741c0d00000100700600103520304510040c7c0d182d004054903001d140d0700940e100d10501000905d40f02d00c80c00024001d400c1002150b80c002c80000c0c071a41504d0040d1040079980d1507004046540034944000a0064068401100d00181002000f00215808020240b0078540550342034800c1f145c0e91492041c04a0742040104401c08094014141c0c2d8 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 545331241 1250 545329991 545330011
    0x2160c170624181e10060c03120c0903020915062502031b040c080603280b0c120c031005090705040e0a0c14072d080a0e01031a0d0b 58
    0x750703242d0201e00c5a248150b00c10320503032003071403c000c890f41001d003810940189681500e2014102204c0a17189090039002e0030341081141c103000c80501d400395a5040203403200707850400180b101604010110601400100d2141c503216010030400140401e401c0b0707040300010f003401d03d00b2a82d800d0003031051490505d8503134440d01d180d400b0400360340e00f4003010b2180c0d032154140e003402680000410044802c1c16130780100b440b0505080c4131068800242c051182d030000403506001c1c10b9600d5108945100f07150300181410b10311001c0005414010300540b401c0100070510000540320718a21001e20300003100d1031495401265001c00c214945912047e400450900744203142c0341d12005c000400800480b011260380b505d0315070944001d54010392854095120403030300b60070080546e40c0c0e82082e0301e010041880d141540e00070b0450380c030b20003601091001e50100000390b861403180005400c42c02d94500310b5003c01e140c00e141d0040460b0020b0540704a003401000c12214000c1c5030303100307111844003402503418 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 545332491 1250 545331241 545331301
    0x30e091008010e060601030c03021611031515030d14121b160c0f030201140f0d0203041a07110a0b1506120a0c03090b040209130602160c1706 62
    0x711020a100780140c141110b00a0844c03440d0000015040e43d120610b154105481080112848881202c440341c04950051050003000807410019203040191030080ba844400c100610420040c80c100307464205505509032040b003002d01e8000c1d40d016400b0001821600001c10032030b072419182c0c800082c2c0c0031803c0c10a601140100f4034104049400040d180c4030300c920304207a04001e1100d503040a00040406840c40041b090559000802c80410007008500000011811248d1610b8480c1a41d103529030840045440345000d00f0820301e41e84c404041c81c6184582c8070042120340d03105d0044015505a400018070100820381e4402d041e11500401c0b101d00f50f441d10350802e1890b91088000d007421600c058221101b0304140c0c403200308550810b00703400d06251030480768000280b50b90450650040c0c0481d0125400c0e500c00c000c1ca003a14101180c001c0110380f00203402002180e1902e107424206000c1d0400040b15520b440c10301502c1403902d14003108940c03080700000c00c80129042240d040d0702c1c80d00e5001407 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 545333741 1250 545332491 545332499
    0x3040b07031101061a04030218061f020c27060f0f012304030308100b0c0712020303090405010806010801060b0324010c05010c0305011a09010c15061d040209060607030e0910 76
    0x45184c2880305178542c240c400180c200107524111031904e0070141c140812140d1410704400041e80a9a00030703103125084008501ca80d481402440b006c1c2d544200500f03900000713440014a01c0c8000c0800020b0702c0164242804a69542080c4152855071000940407412400540d40151001032000c1c0390100b105507542e203024400104030000d000118402d455072000b50a00d840c070840c400710103030080c2c000803c043c025070b41814400281c0604480360080c50501424860020034150310410059036002420302c000040d0890300059424100c481e0007000300003850f142c0304241404d02c0180c2d0001001d8508000a17241010815520700621505051654820700959981429248120500300200755502c2c01003083d43c17202c16050000c11013462841340741800683c000782040b22490070181454a80c00700c254503005027503110b41c01800c01808019031413030a05010000f4480c0c202c03401c81c0155006000318405043c11020340702030640c541ca411748004405000d000706564000d1140203001c03180b900c005 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 545334991 1250 545333741 545333759
    0x90f091305190b01060212030402040515030613060e03040e18011d0601030b060f181b0c030d0b0103020405060f07060b04050916051e04050406020717040e010803040b0703110106 78
    0x2d1041c0122030701440400d40d54200b95448042c141c0c805000e54001c88500c41c0e5010408049941c4146c1c11200024251101c040c00c44d01608550090364142c80307404107011695080c4115030030110b1140e20305106540584003c40d4903806503200b1110b4146010300800d140100e18480c44d0b8804010a000088210070000003500c4c0c4090354000070740035000240103000348005000ea06034005015107200194120348004100700b81705c40e001c52486000040017280002e1200b01c0c949103001a201180e5031504407801e08540c481c0d10942188a0303841c580840c0a8540d4000d000b680d0450320300400d1a420070800d100a841554000715049802c0d90343c4034540040b95461b071103018041c0341404000d000d030413605c00040804000d03541160b8400c4502c110071400e880180b590500e015001510046219100c52600801a008a820040c0600f0015a036a640c13440100040e00441d050720b220307058241d80c2c912a068480c03140d4058054004010003907100402c1c00b400d05e4849030321301400002501aa154030f00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 545336241 1250 545334991 545335003
    0x9040905030f04090b01030c0f0509010c0510021809070509011103160614070e310903080f0109060803120411030604080414011d01110a060519060902090f091305 71
    0x1640605401040134850603d19200d00b0407030f06001c1c04c040041d603100550250406050072000c0b400c00a00268400159200344500f95803581d203e02100d01c070a100c1c0c10954003a4000520b5030740184102c8a5040407460400082d5002c0c1010340c8070303c3e103800c850700011201c15041e5652a1854030080204145e07007021441c501440600a000008040b464012615410381c40030b055101041107120110a07555070740306040020348841e239000c85c480c1104c104400040400324449201803171030868000305141d0060820340c8941c1c01503844290907030b211000700080300c21900078443e2541c418440301010700350004040750480e014100c0d007c419402400001d2510404803404c540242d0085400c0155401c4c00000107040301003402d00b00e00001812541c240d03800c900480f103504111306038203031001d0001b045c0201441a070b00310b10188058502509a010050b15207010340000d68948240003ea00c62944250348061100034001c280481010040046903600685843d0440154aa201000071700030060 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 545337491 1250 545336241 545336257
    0xf030b28060515030f010b03180a060207060c051c0b061b0c0406050f09060d1a07030b0a32030106080106081617060c0f090a180f061503020904090503 66
    0xc0420000d06100900c92245a07403450951000010700c2803240f0705481c503a132141900e241440468481d5214150a00b0300e00c401040d100307480c0200350030340d41845000d070010b0108078040c050504c445040484105c03036601c185804404030710707032040c1d6242c030912030382e00b00f01300e001e100900e120304001c140307000041d00350310382c000c030b100c841d441004001000d0030580110b8000300380880e003102c0350003000e002091054600074925481851505c565000304569000428002d041801d4203241d140f52104000d0010b084408289104101c010000101d03841c101206004c5018803118103004041101061520042200c0200794155241c400200303030b00b0740900c1000d0050030303a40c0003414128442c80e0140ca207425642c1002d4a0303804019011065902c00003102d5400421521500f65641c3e941d901d00a09401201080c1c1e0b0701414040380024580750150b1646880c00030624108030500a502031001210602d1080c510340070025401c5015403402640527081c0b100002d4008188070046603551406c5503c000d8cc = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 545338741 1250 545337491 545337571
    0x60403110c062b0203011d041e1212021305040914060a0629040e1f1202030d030c020613051002121e010602060c0912010c03020d150f030b 61
    0x19024402221640d0381c0b03070207400c43c46001c41c55541050308451400302c1c010000c840302c2034480c0100f420001c001c0d8412201c0154420f105100c0c00251810388000201410100700080500c90a94200c030421b100f10f68002d08030060010f9402d00d0101800007910030343c1e100384d0b000c101300410142c1404092200a2060042c0100004c0d950b08012410190347d840c423004102c0b00101002c50000c0d1850241200c0075281c03540074814075036580c00603021440320322400c4d41c502b0172034003030b800100314507088003210b5514401c4041d00c504801903401182180d44802507200103034029030101d44000d14440c0c089a2480c00341050714085800e003000328050b0fa22011044440c13408103c20400150a641c01d10b070715040d0250104c80c1c040d450f05d4402036542034043c0c240c00c0a58000038404440d41d442984039950740703114034002e01c25004031460283c0250003e0021252440c100080c1ea48800c1d0490510416203580021250b916070541e04e48240f410340c000c140380380c40001031a01c100e04004180c90a441100442 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 545339991 1250 545338741 545338777
    0xa12030606090b070b0103030509030f1b01030506120706051c0905060702060f0c0f0d0204121b150206010e0603030403051b01121a010c030201060506070b0f1305060403110c06 77
    0x1c0081000300d240d803000044030414084040012201400641126010f02c0c00ba80c60300403010000341425503084011201e44217a520701d0a013031140c010642d01c0d450098030100000c1d61040c05000340e00c3c0c01c400f05c2c140d5a801c841000e010b501d0003000030740700210fa44d08085000070461011345084455088066440360300a40801c501180c0c10014154420700810409400c1d05098034003c1d483d0203810700e604282030001c6107901503040c5a82c182c074001c0081c407081e50285e045508007840040c810031504a04141084030105100450380c81c0704121a03403d40c020b04007680780c80c18030f00b00482d000e001283e05010400c000004100100810904400c01c0782020344103299000014090003007001c2108495414520340c5a020410181c61038200c032028204005105a28a02280141603942046d60b01110205200090240c121403e0384074000302e0102c0e003a16201c6000d0078104c2507800b40000d08903032042c400240028420101d0b00f80f248518811102c001c80c040c1c0004226400c04881d95038010900 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 545341241 1250 545339991 545339999
    0x3030f060b0711011803030c020d330b15031005041b0806040606080c0306190f05030c1801170a0507090b10080115050c030903120408061e01090b030a120306 69
    0x2c0a00f05180590900340000c0014400080c0e05240302c0da888041c3c1032000e000d02d00e000355107880705e048440540c40700e01c0412101440e400c80b40c251000c0c0d00e8110003040c01c1384881c04280d11a02c24030240350300060104011440a40e207186113580000c0c012540300c943c0c6000003d0036240c0d8040c00c1c3d6810180480c0600c0481c62290003088050b008041d03520440c00c0c10401c0217800d4102c5d8026420810f20ba14465507030b6503034808035403140c02e0307001c4107070b0b00c1081300b4000240306100c41891010703208128140d07040b8464440800104c7c0214030781c4c0d60100251000100290380ca611502d828110503c81544d1103a1000e0f01c40d24108121a405403003482e0311806c0c00150f40c40c04800c00540f40489041101d1154144401003500b40040c000c81e0091080001d94910300a2040040c0c1d840010000c0c111104000003400f0790f0b203150482c2c40345211900c10320000c101c1681e1001c2c529140e041410141e80b14581c130b0080000007401b040c00c0c480740c060103040421404a0001d19807192010242d440104460303141c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 545342491 1250 545341241 545341253
    0x2120f0c040b03041716052d0303070c0309030501020a080411100c0b0604020d0e0a12050f0a05071502030f0f010803070f1b050d240c0507060903030f060b07 69
    0x200a000259210080206004400c40300c42600d070455045800b1446582c0d1440995420388103548807101000351010030b506c00c200d0000f550b0340d010030003060010b50210020214100d401450109100d650b08180f000500084c4a1680000136501078604035000e2a070b2900c2d802e007203a0041d50100d0004405008120901102103040410f07081e003550501c80f10114040010010340105000410382c59100d400701c0c186039165019910b44e40d00c8010704101496011001544da04611f080c11558485841d004420582c0101e06a80803100d4110711a40341504018013101d42e58404c540c200c520951115100451b000301d4405944140906a090b06c4141000314200300702c1c040591000d00310341c0c800c122041c001089060b1442c00ea0b07034048882001c2c49000d00b10540660015004150040000005003041c0011030340c03642841208080000c4140b0314010f44c034815101603e0080b07000c00c0003000441c000404030390000c8601802454000b810b0718980039601d09503034440d03102c040140c10126a100178095 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 545343741 1250 545342491 545342521
    0x307181b0c020904060b01031e061707050114030402130f021e041a0c0a0204050f04060c14030429010b04030b150a26161d04081c0b03010212 62
    0x1800303040c101c1024030310303a000a403c100020001001140c541d031341e42c081d690182d00b040003d620203002c100307100f02017136050070018040d45c4140400b000f0700b01002421003001007a21010b482040e9030700417400c0c050101d511141c1c0e0015204030380198100e85965180e103581c0c401c084402c0c540700c102503a504418400040c009040e0050f01d103403907501b00300820103118000902c040704440800701d40c0e1a211414006400c1500c0c403c03000c0e41090506081004038030380c404003544694401d0300100442502c3c2e04e0f0448082a058400089903c400c10204022514041b0840c64414812100e40616610250f0811984800f0380c8102543d03a008101441049901c0050070340c0201c1c0c1c60200b0711101c14404c0007803031199003803050a200007104100c0c03918a24041d118040c001150310112405001015555054102c05102d240103106410b4040d88080011910a501807504611b44a05104001000340c00c441482c403e001c051964036a040340c038a0b00c0c00e002500f403a04420b40804103510380a900c030b00c1044 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 545344991 1250 545343741 545343791
    0x308040318090515010216060e0a0503010e030307180302010c0b090a06090302060601020706080f060418120512090c0d060e0a020a17011805030a0e0f0d11030705030109030e0d02030718 81
    0x17401541984130008491701040f8111040d6144c403180c027065a001042d101c540301e4000c1130b0994208103a005140e08000020741c01400680c0c0c84002c1ca4081603c0e01510455902000b40081e01001d180b1000c229091107854101c4502c800381c5d14249125a0f62100f100e825441c00c40141e0000010860290780502001c4002c1401c0c0c2018159403600c0c042881032440c0c0145050711855170341030034201401c449110440d000364001881300d040300b000c400161580d048805041030010341000042c1b08880e01080a101603000603000801e01e94056030303130001030840c0c4030444e42da9205410010002d682e0f4107918034000c0030300c1300c010b450040000c1001c509441e140600000140546c200900c0080c13030000480700c2c04040d5243c499112200c02c800107030440c0c500c0e1310460f40100912034000a000004441f50110311702101101c140e40d40e203000f0305003070362800040a00420a85941c411480c241443e9034454544000c050b07a4400740ca9000c5030610300360740d264600c0c543d030780c0c0d10b11610f0301000322140d0b42e5a0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 545346241 1250 545344991 545344993
    0x70f0209100e040308070e010905090c0f04030507081c0e060714030d09060203090105090d021e0712241a0609060d0903021b0102030306100f020a020616060605120a03080403180905150102 82
    0x1450520002c2f600600020700700960b4140b000424080c500b02c14020381d03010315880825100c2c0c4035902c1070502c0c0c0c2c518032822082c28166090400c41202da004040c1203104480144c040d505004094403424451030010304e14103500d000c05c004803d5910b21520448400c5842000b00503228200103194508413000104410b031141c0c01202c0c140545500003403482c0034181085907a250a84000606506180e140d80c08407110000c8202c2030010448070b170550812764039078244a403101514569404060f10089051103840e0308441103482a2170400c88014100b02101030040d41c60041c3d807003001e0701215880b01055005800c00041d648818003100828011a1400d2000714258102440014540465040031000b44140c1c1d003040e180c840e00a201190110342c00400c0d543d103441804c881d1000c418034500085918500d480408201e9141101e51088101c1c0c081008101903155a58207460520018000b54140310421149980d00810011544040c000c6001b000c5154140641d0303004624500300455415 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 545347491 1250 545346241 545346257
    0xf0601030207060b060a09030c0e06150a030605030a08090102011a010e21060a02031e0114011d1807020705010311072d060207020f010305070206220606150806010203070f0209100e040308070e01 85
    0x5540d488006084000cc0113103421035444041000940080145501c03254060080c5169481800040006030084400a030001e00002601840c2000d981020702d1205000c03520384042c0008a040a03e1810310007400c200d40285944820f4907803601d490030881d003401540d9000420400c070508540104094181800740c100351550400b841c20b41c040c00c01c084102d041110b0058500e000c007220107103041102c000a0480000c4809a8039407440d00d0300e0443d07810001d80308100c0e000615500c0f901ca20807401001848a5041407003958070380c0d2440004410142c0c1c451540f4000380c038000d03500c1b4928180b40c1d104040043c2e070b0348044d20602240820318205541898078040400c25000e40220b4240d9210180c14510000c50020a8101601c00b640300000b0380b100d071409501280f450214440400400116111410140d9800004913640d02c00d01c0801030807402110641801418215001c5400c40d000c201642d00684c0c079950705005105003241c09400158103503042c0202c00790400094140d0240030b1900e000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 545348741 1250 545347491 545347501
    0x5010606050c03180406092414090112031e031505060933070807050c0604050612190c020c3c030322031403030f0601030207060b060a09030c0e 63
    0x1482c2c0c0139490890302109007100080303140d692580d00140160089038020019a4422142e00d608040882c4065800c005410000b0a032940854030303045940400400380f1801e6800e04920310845d0b404404201c080c0304d000b00c03030b600c10541341c031600c00e81c001102ea400144e01415450080e024028680c0450b00500c020000310f4666164400d019a40440c510305907100c806005003501b5034034800c2d40481c0006600070404404000160300242807850040048030311f60003602042089038030840c0f240c04c2d03000a00300400400301c000f16100039030240e1817400b8000c0464264519006035040c2004285c01a088500c0040c10f45c0350449031700b4110781c2c02c490b25500b0005511078100034501420050760411825210640340c2e503900b00704a070f040003218461101621061000151a50340d540004c80d181224400e4111100000005a030b2103040c2952191095031a044019030003944505400e403011501d03913580e408941c503154004c0c80b0b4962160b0300c0e110351515600300303070001d8a80794011030701c2d100691003806 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 545349991 1250 545348741 545348743
    0x40b100c0c270c1809090506060307060516060b030a030801033e060d14090622140a0c060f030e0f0304030228060207090b0301051b03070c17030405010606050c 70
    0x150700e40307180300c00c0043c03c1d4541e6842614410180038150041e03010304640400c2c0414a030704200e00c4c091141c0b088410030740b100010180c03a503146000340b000084060001019110300c80041402188c000e05000030104180380100c0c0c109801e114080e8081043c400040041100059821003450f410312913003080e400d2900d03225805140c451140901c444403c1c01e420a583e5a80012200402e024000401039240d13075180418500c5012111911b00d40120000900b10005c0c0d981482c000102e0b14ac16407410310b00580d03400c1450000f04101900600c120144200026000c00c0210702030155510f8840c041050b01e00c004042d1803a01c0b1408000f03403c0780c2c000c5650354000105980070340b68122401520403031900e040782140b540c03001c0d030850698030b1b00384002642d80e00070841e40c064680304903060100005c0842414242c40381510000f64140e000200c40741010b440d2005035800c500715281009003000152110481940840030b8050550310000034441040030034854000101600c1c2882828003030340d00069 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 545351241 1250 545349991 545350049
    0x1b1602090124050a0201020409092d030507060c0509060307080f01080c031b0d0c0f031a0c09010804170711100c08030c160b09030d05092109040b100c0c 67
    0xe030140400031402e10030b1341d8001e405031805041d031710104105000c3c0a0514034403600404007a0952090741c031804002054440080341801600b641303405e468000640c1c2c1c1e07036000b0400c0000f40b40c10803109010015495403030700b0045004011742e5032400c0c001d0602455811440c00d043e0310201c0580d05c8241c000c0020b4401240007050315940c989040012850358001c80e24084204100500101d1044001b040e2074001e0035422040e24005c40017400d42c040c03c410910207004040c0e921002c8001c0900c0b04020740d40c821880e45902c5845040102d034099100d0680328400c0c0c000405c2114025428840c40d4000d041204d240c000c03040051810041510568880043e2071101401e0407445600015002c801c45074020700720085254001d070102d4141c070340f01c2c4080d6100e4101950300110242418081684280001010058a5900050745880980b101501c18099002042c40c03600662180042c00702503860b024850710f4842c0340d460f16220320040d49824000060150006a100c0043c0f28030110a03520307208007 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 545352491 1250 545351241 545351309
    0x40204030c030f1709181008070e0702010e0604030c080702030c0901090b010318231212070810080c01320301060f05190507080d0507020c27040602031b16020901 71
    0x424480e80e00c41f11900101048140c01c84c402d140f05403c1300181c102147c8803100d11508182e4020450740c00e002d218903444070015036018001802410000002c201e003080100304043c130090445243e20804804120801c800341d10045180e544c0d4040509156007501411314914441500201d140e5a81da41d10f1981a0140c1851019404520890362242c1e034108018481909028807150310781d09e4508035202c02a10813a113400003e000790300494540c1f840046100191034100300a40b54500c010401180c023689aa0207202d10000758060382d0001c1072000d0362030390105101d180415540c1d07040420140000c0001d1a42000700a01088801e09a840303850142c211452140782c45542c40040d414100994000d41c49100001448d010038850208e0300016001c42c000e405454640d0103030300c1c4c41c103000303070081d031030040a0010780c6101d00240004c0c959500441d8800411004420200c0c0ca010b003600d01070300003452240c00000d100a8440035440c0407200d141c01040032108080c3d02d4108040405104150042 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 545353741 1250 545352491 545352529
    0x803040f0507030b09010506041b0c080310230f0d1101080402120d0c110d0302060a0506060f12010620150601020f12131a0f0702040204030c030f1709 66
    0x39241081000a0004500660300300750398125070309044504d603009003000d07244a8401c41ca0090783d0302d0717000841104440e00005075280c884000c00c06031189071241d07100610441084c602103c0108100c240c0c10700214080c0b0064094025400081040c041c4a07a085040144924a6101c00c1000140c600300015007000c3c0c00c0ca0220700036203c500c0841c0100300c0d800c507000131600410440c0802036902c00b80300c00086010710540c004404419080c88032001f1403500c043c0060300084001003285180342c00c80e5402c10b80c090405480c00098581c246040e030050000e070040c40e03207010010046507510a4030310b0490705400595144110303001c0c1080341e44080d0f5a20a00c02056204000340b210383c020b008050300811513209440d00e14103002d00d440d0080c1c2c044000492800400312022400c80700e190085880e202c1c03110440c41ca00130041c1c901c4000381c1c10a070f100703d90054081002000003120300200c81c00031481444008403490852508909201c02400c4000344207806006021569864641100790f00000030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 545354991 1250 545353741 545353763
    0xa1d030d0605011407060b010504180e07050609031b0d050a030f08060a060f1d06040924050306060603040609150501090f050c0d0b0d2108010801060e071d040609020910020703080304 80
    0x287c0140c40e00d01441c0d000066200300c403511801c880c0c0c0e40d80c01440280c3c08880a484c01941c6980402800740250705616406922840d400417500481c3c0381035920300741d00145400c2004045603101e603e4588600b0301140042c8200d80c1c902c5500e5013201c0e010790011400c0380c80c02c400c9810b1000040c19405190007660400c840302c10045d40c18251111000301c0f0140241c04c25640c0da444036401c2d0050302400010000d100024200d00c41841c00f071a14040640703070018050030301d42e140d04040044503040500705444e140e5035541e103200050304924480c10080038684000c241d81d071520746c101040321151b54103c04020304240c10450106090001ca403c00044104001014924200440e01c1c110b0480720003007070050b070201240302645514881140524884c1c2c0c0c0d90400e0381e00c4124290a0300d40c81d05c510b26003005001c011440d0300b03008140860b4054840a502c0f0707100451031000800b683c5244d41314411603070380001e40c00c030541044c150841c0c0c15000d074001041c1192445d0340e011500d100003080034005a0810f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 545356241 1250 545354991 545355011
    0x2030a02211306050306010215091e030c0d09180c081f0f03151d07060c02040e0105070903060509031204060b0604181506030b030c04050a1d030d060501140706 70
    0x540281c648050745181442d103095111a0b001c1c100d58419920240507104400c0401080e8080b04000ca1003014180301510380d05551400e10075003030180704060b9505020901c4418084041000480b504180326a0354042aa180020100741000c00400404403a4104180040042d40080c5195080480810300c030303a80b140020045000c1c020740b5003080d10b003004600d400001740108024503551041c0340d41000c01100380d02c4100c4883d0800c1e14220300100c0d81010300b0400226001e180031204440c0007410120701020200788035821140700319440400b194800c2c605105014040c800c0740c1d8066214402145016501c5114130b0510800800040100742c81d4001a401030312488259001405985c1c000d0300d40d50280149e0001a05044040c0c0070000312821000078940e10a0164150188015018080703840b081000c0c480680802084014402d0321039a05154005450180c8000e542c0c0c0c01c0041c6890304c1c070010515007a54400d6101c0d604010803001c69800600c0020101c440c030503404031002803a00300c5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 545357491 1250 545356241 545356303
    0x804030c0311160305150703060609090b04110304050d0206150a18020f03010b03070f0215070305180d0203091801030804290a09060816051c0f020705030a020d02030a02 74
    0x80450159070303c4041c1c0000000c00c40005102e1503040741c1400680d40300e54400400710100d4407140718032000611290000c03c41c118071a0301c1904d1052001c0c10104420103e00c80c01542c1d6032058400311090f83c4404d85800c06640e041c003515400400050600c591181084002003c070710440c00745040c01c3c900c00b0382c940e0410104d030b411240e00282a6160507207940e598040c40d580c0ea0801c80d42a400300d002d080381803440610220385000407000580e624034594584413400c400510000b45640d4036844900034550115808014103100b51101e076006542e00c400e158240203050300c820708900b0419509400600c009000ca10a84043e42c80c40c007411400d40e8441c4108800740c4104006018040c000091601440c40e03118942006a03030305510307003011070f44900120b43c00c110509640c0d2000100c3c20710810301d040354a010b002c1c07004542085c0101e5801d0460001c0c03030032a4400941210694400100f10700322035014000c9141c0c04400380040c500304000001d020b5240d2442500a0101108041c101c1d081c03149 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 545358741 1250 545357491 545357503
    0x7092907060905070303080906010b0406080705072418050d0c0c0e0c09011403060d0321060902070203010510030b0a022b0603141204050d02010318080d0c0804030c0311 74
    0x90003a0703060001c0c6940e42800d44d2244c4c03460100368000b030030100010b1003003c400220382d4125000da14032189400c0c940102101d0658001d0180010010100b29450101e49207546410240c024134004c801c0d40e040025a410845100f1820248445445464840071640100d041c40c0001c1d00c904101201c54450301c0c00c040d03108501d4004508503034040090013103034038001014202c1d06032300380c94800d40142902c0041600e80012500143d01420964081002034410200000301c4120034811410040d01c2e04a84000d81d112900200c074144c1e4040b40c14001e51509000f400e40144142c68079130951410f645405082c403400520b0040302c01d40002c4c1740c2140d030000030032241d8010348144120b420f8801c80d4420740040d14161005407a1211287c5c01c2d0b5418100100e0300f940c0a0700c0c0303101990301d824178003001d00041d900c00a034140d06042e0b4400503030124030761021040c51020301c12000303180e07a0000b180c3d02c40100d55404010f802004100010040041c1d0001c41c0c4095054041c03c225030782411000b802c501d80390b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 545359991 1250 545358741 545358743
    0x50a0c0201140c03330301050c0412020d0615171c0906050310170618010c0509120304080610150309021c15180309080309060403120903052407092907 66
    0x4251100b5038402175a018081251018048000b40210385440411406500079030150070f4652252520300c0006290444142046601c030303100c007003030340002c1c043d040012510341d5021055074400c20100c0c0204030020b00100d1010344001c41a0031341850302c44001451a0858000d04080c002c0000100307080400d00c054010080801c50381000304a802d07055802d80b51a0143e80009602d02c2c84502641306c0780042c000c02c0b000c6d03410356617000d042c2000c0d141000015a42c000c200805400200408100e40760140701c201e02c25a1098485442d16152495682a188022900008042c649080040181ea401c2c0e144801700d01c202203452070b1a0038909042070204030003010343d00103502e40520300052190902402d80428003d480b44c04440ea038a0010580f00d20500b0711003503010804200a100090950000701c040000a1034000d450300d49a5a8207490816a1042c0ca10640c1c50410340c401d032400d626083d00e80c0301055103807120b00d142c44d00071140c1c072018085903400340c2e4896070fa46c00c4a004071607200313981d07a40f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 545361241 1250 545359991 545360041
    0x302010b1f0e0d03020d050f04030b070c051203070c0821071805040228110303011d0601020d120b042d0b0117070f0e0301020d050a0c0201140c03 64
    0x400d20a03000c501020101003120380814140580001545007a1540310f1401e40c254015246442d800c0d00100d40c0c582c030002200094450501021021502c0211018401d058a8446414046490038510b14142c070000840c01e82c0c0c901041040455030740682e07209000d59100048070b4803040d08a928082d00d14001c0d07110100d04c400c0d50104884aa4841e03841891000d01d21030b00510283c0700d0050000340d00c00d0341102101030094110307034001000700f422000d1091a0306d10b03080c02460f201c00969815a80207904c1412400c141846c070080036070b00e941d14550000424002405d01261116010f04000b4045240c400b10550350b81c1c2050480e1205c0c0c11070440e1a491404041c02020320b40d0920f45494119986580a02e140807c60030455008034900e44100c048000e4a1000d99148d010480b0042c0b40404004200a1002c1c000561510300740050000740104a00100c1c0510300440c10030100c46c18190b0000441e810a03043c0ea400c6002c80e00c5040d002039001c0501541c0343e86100c440c0b558034105441070444 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 545362491 1250 545361241 545361259
    0x8120906040311030403240612050319030b0310050703020c070603270209160c0b0c03090606030d230c0f0708070b07120e040b04060f051212040e040302010b 69
    0x161100815598400c911a459208252080d5080d40340c3d2400383e40001090051010302c03151140c01c9100090509101011010071010348030098004101132040080f90641d0011800204220510442080701d450746c0c80d0810110082d580000e946041c0b01004c0e014403692540402d411341d00c0b0307030111a5500260700c1150b0485a0ba41d030000e00601e000500c204100001000c031074030417100f00c80480c82c13440e00181002017a89840c208440d812800c0d01481061040b80003503140040e07045508a40f10301c9009400a03100c0c90203804903824104001c01c46071103078002025060815030000c0204030aa00321301c544480c014035121040307069100e60a0020503900c50000881108200010020103442c988400d403504681e981009000358041d03207030300603c02c501424140b01038503ca2400e51844d44030052011610700c1410020800321412500b02d14182d040b190701c00d200e1410000c0c810981500100010101c0f8125148500c00d0380c0a1405032184520254011405040c400d42201107030301001482508 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 545363741 1250 545362491 545362501
    0x90d021009152c030a08160209250906050d021b03030901050910060305070512031209030c01141e071205010e0106090b0a0804020f12060109090506101508040812 71
    0x42110b005000342c00c0d210007800c9400c010780d04406140c80c83c1a502400a1100014555034001d03242c01c032004c4041184c11860510002da9a040f6043d4019025225211a015a00f42a00c0f0700705228610140a125040404010195022084403a40c24503800016101e1001140d4007880103400030f00e0490a20010082c40a90701065000303038001c04c4403030220351483d1000403a00d01a500a844040c0c59a00040c000b00068201a00840d103c00007410640c2c0c0742440c15600c101e110344050751000c0b043c5d0300104d031050008100340704112059801c0403100f509423604a990342941507000540c040344032503040c04180b06d50301075480e461068201400c10300ca55a115522040826001d10803980003800d0558001034180000d412124601d2070b980da401160b64446d02402280c1800e640c2564000710034805000040e0014486030b0302a14144401068940700e41c100140760041c081c08400c942110034008009021814200004000c4141030840e500d6885d03040034560b90203403519101780d03110500304000c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 545364991 1250 545363741 545363747
    0x6110309160608011503270303180c0b09030a12120c0801120b1513021c0e070905130b011e0603060812030c0f0c1501050402090d02100915 61
    0x151140800c8012941020300507580c22661640502c10752000c22219001803000404c030a041c082040001c2c01c0202e46601c3c40380c55101203100300910078410103c00384a00040541c0760040d1706100c1d4000480712901143d50325504a040002e204620708800c1c0000c9e07001d06034909001381a40180c002031084040045903001a055a54084502c08180d242203106200e40e40500d4140d8140c0300340c40d007450703041c802c17603540c04036040000740051420303811414420069980741c1041420041c5003440240c0c0b01d5450f403500a268607034260010b10b0303103410301d88099a01c01000441e00c048803607041c00403900c4d886882104506410303810006d8000c240907000401e00540c0c09032a100340c5001c00d0007500240c0c4e50354008a0458510f400340544940141161180b032845103000b95030043c922080345071509039159120880d503400440d4100b070300d80010680c24050003150301d1050043c44180c50075450501c1e1f03079000440541d0500340003881104084a84002c56101e0030907100078100e46840c800308002d04184c00303 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 545366241 1250 545364991 545364997
    0x613080606010201090f02010f090b03190501051e09071b06020901080702010c051e040803210a0e070e0a09050703030e0f01020a050c060307020f0106062006101406070611 75
    0x51011440303040007065072944148122100c0540150482d01c40044d1980115140c8203c60b00031303800c110f42c282000c9072014844004500400d40741102180000030310310703041c05440b416032146105940010400d04142d9071300043d0114ad40003101c0e1840c040e5038040056a00c8044c03d0040d07010310001510300300c10000740354020b00746203909072100030031542c41040c12403d070780002154400041c400d104000301d02518507403a1140c400454025400d02d520f42d5105c514540155155620340c40a000300c0c1000100000c0401c0d8000c035000405106102c40d43d055107599031107038132801d44141d1a81d000580c403580349a0201c0d100c96808003d660896550f420000d2030040042841840b4280b80200341c2c4d07580d0700009003440351540c44400340c5a01c0703c05008103c0e950f08004c100e18254050f0003000c600703202080c03085002401c56600c84506031900c2c8891255201d00782d9034140310a5000b1000e005021171800e01c04800c80d00c40340b00707080c1d0510202c404140180141da900800640c140a4143d100312580380c06 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 545367491 1250 545366241 545366249
    0x30c0f0f090901120c1403010b03010509031b0d02030301060f0e0315060301060506160204050406020702030a0b1504050c12090304080d0e0405090303060d06050c1b0a0317072a020613 80
    0x45002c982c1d0b01c80c0a40b01a62020700c400501003125071004000303c8103c5100700782080001400061010070180c003081c00e45008980303c042030340000500d05000202c02180d405070324402d400401c1d10b280d4200c0c2c0031b5601c0c407060240e40223000c2c1c2d400000401d680b29243d01000d0000250986010075030a9181c40f81180c0151070040c82035003440c001003030501f08503054480943c4024428241c00d207960302070000034440648151840d9408018100150704c0410541640741d100e0740402c44249440320801d41c030901d200d200c29229904040620000581840a9801c08010495504c071030340c40f1064020f141d8855030f803001e29540101a0300700d045580004884401c00f41c140c906002c139680c6e000200d900e0b40700071204150f1000544800d2000304074180c1c4040d0b805102509076614045100e01031044c3c115450480045c940d21407440c3c1d00800d50310089044980030500c69010040c2032010010f407070890f03103088081546d250401d40401029691001a01083d00507001540d070743d080c0c0340b1050468805000e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 545368741 1250 545367491 545367499
    0x220b061605062206090501020d020c060a0e0c09280617010509010c020d1d1504051f021e1507020106030507140f13020d061e080a0c0b030c0f0f09 64
    0xc0020310307003c81c24400d4a40c120311000c040401220f16900c0c1002080c0031071050383c8642d401c2c05412941c142901c010b080020004c4000c0c0a2803904800100a886150b155010302c0d410185c2d26003120703256002504d8000d400c0301044180101c014003601040c04488040d0001c0c18200000003070400d1014040c000b581404000900299503000000c40c00e07102007000b490f00680c060310491070424820022403d00118500091400320544800107002d130340c07481020070700c02500060402031880c10141030b561404a88003400e03005413003510f000e9115048030180003500942248441001a0280714030105400c0d44640040c25080420009000f0011800211818840d01c0808a2482186c4c4810384100000501c804504c00c404e4040c4090f201c0700d21000141a9001d12002c0c9400c02e1900a44014181c10303032030961006a4613104022410560f0f10900ea103412503014000030880c40c02c035800540e002101031990700e0721900c00400c081c0c0b0a4040780d038803016000c5483c040ca030341120000d0541900c229 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 545369991 1250 545368741 545368753
    0x3100f05061c05060a020a02070f0b0a080106110c132301080729090612240a060504031106070b070807140306011b0804150302030105120c220b061605 66
    0x1c0108588402e4540016003503030310810000300586825001850381d008903105840712180d03a4890402180c1c41070700240b18026001c5544070090b9801031035580108641d280c20804518100340b070640303424290407098024801d48603000302d48503181d000a186080040c003241d401c82d00f07100b803007155068203000e4107915010b48080041d01c1d0801c20003461034070040121080d04282c0c0c603032800225510058800c0e07002181407017280c045001c4882c917544030b44100c03440b03442e403218081d80b90b403003040c1e03101c01062213144124010700c611a88031050301c1c10380764410254200517015800041460044903001080c00390150b0400c507800342d100c86900d00501c401e4a41d00c40f1020002401c48040c00100c030140d0000742c0c0c1020800e083c2040c04029040903025101c428502525402c4190f032034212a0424030100e5000001000720b418001c0c1c03d10000c8203100f01801527015544001161855135035898480d0520900690045440700e43c420740c400000242550703642c07605c0e00076441120344a20750584070f6000714 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 545371241 1250 545369991 545370019
    0x31224170606030f06011715040303050609060103060f050108060d06110a020f0a02010c081e160201170622140a0c0e030105010b0a050705010e03070309050a0f0b160203100f0506 78
    0x2160ba070b03604d00c0240900050fa0038144100300081d0340c940c1c0c8412a21030455000c02c425098240140901c1c0695000709162500c2028400c0c90744001d0f004078105072074241c3c10808006101403420a48100340380030040354440800080c2091328480003e000a440c16440040e460380a100030070300844550252407a419994085036101c210500f4046c1c00310382d01120640c0013696403001400341d6000003144101d40910000540282e81001c54600d0960381d02c900c18030103540c4c0246004880781140d803000c0347d040c0707845400710780301002d11304100354012040c26400702e4213a02a00041001c0f08111094041850500c01a4000e810480100d40100390303242c114042074181800f403981684c13104213015281000000c801c860b10ba010703400507074045d56240034145145400388020801c06001c0e07a0769118003400c1204025400000d50b00c000385041d08002c0800c4811203032810781f20310300700018543c865000e080c008a404c00c0c2007103e00001c1140b400e400809031032900c0c0e00a5004180940b030341507000b50b03d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 545372491 1250 545371241 545371243
    0x80a05030405100b0f0f1207030c210c0b07020112110307030501090207021815030a15060e090712020a081504050d020d1704020d0b010e160c03122417060603 69
    0x85078a42e40e1708240c2c1c11a8402c0e45040104c00f6841d00c032405400f07040c007407092001c040d09240150b08101d5038024061010004801d181100311400e511040481c0c00c90f200d9941e4034003590000b8420000c0c007030740100303101066a006213590000350035800010700115400c2c040c107042e10340c4122410008680f6010002c680c452092090745c07810340e405400f42e5030840810050344c22f03000b4014420f68030340b20004801c3c00661424071031990124862440904d00c11140c283c0b400076100960490304888952a081100c41c40001030749000f140c0000800c0616540c0d5400030440d00140c2c0e400c05501407084650710391505c004207042500c10b50150381503030355110720700d24100d03211300310180507a0018218010300201c41a0500b407694002d84010904031140b0220341e030304079010600360300200f040c030010300c1005030946060700c0040641500e072802c0c040301880c13a5000703411213010202c40050103945d2074125006400f8004200440340140811040103683c40c442e004075070041e03003001c8103103000c2d19000c1416810 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 545373741 1250 545372491 545372501
    0xc0b030f010f140108040606092a0804121b080a230a170604140f0f0105030606060406050a0e04150501030e070b0729041101080708090d03020c010603080a0503040510 73
    0x2102c0070f81090025074003004440084000e80b043d00c0580d550100091190801c1c807880f42a071518201c07400c4800021841014074004000d2a60700344a502e004000005032000c2e0400d1240b00182407402c0445a4030304515124112408000c10070034000418440b4aa00701c07050558042e00302100d1000300142c0700d0106600d000310312184000c80d41030307054914101042c0200c5948550064000501407154600450320018241d0b9110a612101d03010311030095041c114090162105400030f00280c1480f201140c400d200310310070b407010440c0c04940b801e600740c82048143c4407014010014007070f080d40741d02c0d0310304418000d10442d400b0924052144802c0c0e10f010404004603806141c2142c00c002d06030311450b030515036002d00001c0c2643c440820300c5865449106050056002e00c0710790040400f044009001e1600140c000f0050051203400c2011600c0001074006010f07200b4500540c0f0350740244142400345c4482c0c1c100405443d0080707650a50b01d5400006507116500410407108542c212540303010842e0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 545374991 1250 545373741 545373749
    0x50103031d030109120e120703080913050705030c0306120703050c0a0609140d020111010609150602030304050d051e040305060a05180309191e050111120d05130c0b030f010f 76
    0x44200c0010500c4c10301880045844003401f528601a208280403103a00b4140b0701d41085410110204881115042400c448907890300808010404c3d820040000303003080c04024600140c0d002c00100040898032074051030410b0341c104600f01d9007a02d45900d483c0f501c403a4800c003101d001e0030901000041c1e10f4401c10782d59041303644034198489072a0814080c8550544080c40136810300100c0360500d074445000b44a00802814030500008048c4a05240b80002c00305541c8404111340c401c0c401c1c0008144040b9420716114540d050076580e40c401030350b04203508440d00b40307145011031000c24008103100c008910f0622584040c07004005968031900c92102e6030b00d20103400d01c1b49900c180030031160303801e0000345060440d101042454403a81e0382c0c0341e105048180c01c40c1c14201d0004e0840704000c00d58021800b07881c0e40003900301420111000000352540360040710100d50f025602d40020a2a0000500c40c0070902604800365a00d12911070721a4403843e0301c1a0751071091000000300000b0802c02c8000b5013020f07a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 545376241 1250 545374991 545375003
    0x1e05011401051305060a02120f0a020706030504082704111b06010e0a0207110603010b07060f1112040c12030203071707030f030515031603060513170c03070204050103031d030109 78
    0x620709002c107005d07444d040402a43c0a51158030544551000400003402103180d030101020b64854030440c000382000701325845030703003807508000a00c40007419400030b0340c401e0041039205451203e170100050400712610300d09142c202d40340c050003400c0c50410400802c480310385884110000c040c0c5440c41d0356520b8092040000d103010b140041412003920790024070105000e00401810010560300141441d402a07001d421200c00019441d800c1041038054540b031448201c408001c0401c98144103546845034000904c080041c400001c1c0400406817012070240110f400d01e500c000c8914907010b540c981c0540001d0320482620751008290386c4042c801c540e225a41070f0384501060303094620590140402801c220b00b107100742d048854443d01d0401c001d00380000390141200f04070b45142008800c50f080034141e0300e401002c4800d0030740400c03040920f00020011460203d5540d00103074028500318041e01400a5100782450300010030305034080300048540d800141480c04164040082500700c071200b4100900c1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 545377491 1250 545376241 545376277
    0xb04020f0d15260a02270f07021f14100f08030c1c021c081501020105060618031f05010e0a0510031205070b01031a010b0c0307080d1e0501140105 64
    0x2150f11200c0900e641c03103409a0444008684130340c0050310003400e009010421013255080d682c81c0030440e40625801c0103050342840c809040c0880d00a40302d4806603038001503130450407079410120380b80350312a02c054140da2001c1200d41c00c1903140303501041f10900c02c0c041102200b8101044022001c0100c5a0f42151440107014400b0840c11100e10488114909002d46c01044054184050a1890288d8075003035a85c845500f0302d072240006212920142000c0c0c110781c0341404209032074991324126503400e25035491030050382e10201d00007841c0c0018544e18403981c0781e5020004002d0401e0341c1000781a51b01c0c010580c15145e650108500446000b180c00c0c0501d07507003244003000402c01c1c0002c034009480d843d1810a241c448542c0791944903070828ae0084543d40c41d42e007070b0b01d44204444c0c8102405003018a2000b072401c1c90035048942e69004202018114400016407108410700030352040e400c00510700d40d86e01103405040040001841d0910810712000c4480701c04c44002d61040c3c080711020005100d8000d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 545378741 1250 545377491 545377529
    0xe060414090406020d0203090d031d100f1e1b260403051603090503010b06030c040605030c1e09090a1811030a06020c0d020d020a0c15030b04020f0d15 66
    0x290520707001d401035032000d41c200448403400d110750008520400c800c00c024006000c90890081c00c0b20740c0110030002441807500803030381484000c951100a2645050080340b000c200b02e441d48010700050802d080030440342c09000c804030803160040060807200e55a041d0940700f030b001c41650101c1296000c07810386004091403040d075070603812280703800900a02e009810b0003070803065221180380340c000507070104020360010050303403400340240390016205079105401d5051a01b03811419008078000d80d42400408400030722041d03800015200c01120360000f000c4221504907002c03409500c144055030045400d800000c10034038040c0603e41070b0000040020120610b90749880d0755191801069903414002e4991010206000d8005403008240410147c0500b280d4010080d1606c1000400c00c029034004039100c80c0800c4021010008580850000f101070400404044000788200741400758028030124101d041086c05101420003c3c02c1480d080259800e0780068804040142c86001780d0881400c130890 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 545379991 1250 545378741 545378749
    0x1e0602160b0304061a03160e0603031e0d15090606020f0a021c0303021303060b120a0c14010c02030a150b060715020703051b0d03051608010b130f080d0e060414 70
    0x1c8644181d8a603190505810001f07060495540490914030042c80c0e091001d00c581610440d0858400c800440c68001080f0b00c0400c01c5581590302c2c203820401103050b5200012540005508040d1000c4485005403240154002881c07030740509401845210301856010703d00285629040307400412760384101040703188403124110b2810003102050703000d100c07216403800c0d55028074021310301ca0513020582c900005d081c007600101c41c002c1d0303a1a40c1d103c04814000f252141c80e400066454020321114040003560058038000403002000703415114224000c0c05104a143e100c1c5101d1079000380034440400c0c0c170b4003046080c2c02039000c0540303000c42004403551400381907401051890b1003030034104e04040305e04072200c0790900c0c0891020490303002847c1c5450b079142d05108540d8805c0350600a2118840c00010007010b02d80c05008010540b02c0000d2414104100300d52480010480340f0520200262606807050b16040c207841414003040f0003407090b04161414806503400d40f45103049803907503250311000700 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 545381241 1250 545379991 545380001
    0xa050414061e181204090b0a0f0905070302120403020c030c060405012c0d05030319050103050a060b12190c06140d0b0d0f080a1103090f040b0a1e0602160b030406 71
    0x1500d0000044290f0a44100d01072107003018001209505940321441d040303040068503032040b0300e184160903d14080c082d1140100c0204141d074080503002449a0f03a0000680007031041e0410080120083d00030003080503800a15803c0b04407080d02034841c188003540901446020700d00030726012440b8641c00503032501507010103d0014000c442034008026108000c10355518080b4010f40302c03074200004200e012013100501600c0302c100560204031035071541d00e4075500c6103c0c92000400150b11403500d003400360b585040e102e04010a95068480e0005480d10810110720160800c403885854503c0c0010920f01881e4040f1000d101010100e241c0310540400d20024650310740740c540d1150021140e070001c81c8480085207041c42c440d00b2403a545004949003d0700d031071092180d04009901c2000540c0c1076444005410606403001d480c0490b40500003000101c0801c0960000b180c0144180303410840301c0c9500141e20102d80194090301d41100044c0446800030282d801410ba02740c4080000c50000b071540e5101d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 545382491 1250 545381241 545381251
    0x80d0c080c182407170703140c0114010803090406090b030a03110718050105090907030519030905040e150a0212280509070810181b0e0a050414061e 65
    0x590f01c03102c01010240c4440c8201c80740c400054103004244076040103512808940c0c03601601e20030b1382c24115140d40040030003968200d1143c6400d40403544403c120400d40020030742a40c0c00c2482c0c06250303140c1e80c0444d62900a030310494400c40c03d190f80001e8041c03461161548025018028003400c103496101620424404021030f40948241140002c60001e070818882c2c0c1c81500c032002040c19450401000b5050b0006044c00640d600618401c10000e64001240b032507407401042e4904c0d100e0a2400c041e01c868100e82d20440c0c100c0c0c14201d500d014484041801101740358041e60b208860b4881c074541d8400c0340200000c80d0740f0900d040300400c0d409600e543e40c0007144d800380c901c1000c03240030f8081880d00703550f07040d33852424607403151105001d2413030188141014080d03244020010b1100c070600300c03940d80404101c050410300c00b40c06000310b00ca481103541c001800410211202900f81841c50300c1c002d08049030b007507034060f01d0f00420910715a408290305014810081c1d12a010343d5140c01c0d1825144000b801c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 545383741 1250 545382491 545382499
    0x318041118061903090c05010f0206040b18160501030606230d020d1b08090115090b0a0518071704030c03270308040f140105070807050c0d080d0c080c18 67
    0x40080700b411040200034004880b50340102d101703103403032521144046154001d0b41c10b0001200400c130340c072075000842030b50003034004585211940741c0400c1805c140d01000c441e43d9260040742400e109400040d041003007200c1c42a40d0820000b9640e0340200c80800710101c00d4454210352042820500c4510405440c03984018800140740c4070015104d041100d40c504c9925134030601039120742c030b8051781009403d03a10003000340003032040d0003148050000d07110650042c01c12480c0e844c25400200d03142d10685002600000e00f5680482c00145154421500100c50003c0001e80d030342498101d00c1d450707888240c000e40e415181c114160b20303a40d5040e55800908110160382d801c07000400300303203444028582c00c0154060b81d2415581d5041614031018100150000d28003400c100031012800d0f617100302101d03440da821108542c1c440d001880c000b401c02c851095140d5104185801e02c2c0240041d80c1c1c000e090f8904902020000c8400d114401c0d50aa04210340071116004103103e00c1d1600a1001c043c000c4404000f0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 545384991 1250 545383741 545383747
    0x90d0e0102010b04290603130b040c0909080409110a09060c141e0f0705010c3807030b01020601051c081306031d01060b0a0c050f0d02031804111806 65
    0x110220b01140e040d12031402a81c0241c5040c044004003021560144100c10b481b03292540c42d100c0048030000c1e0b180031004041c41440000103050101c1d04501002500100009000130810313410561401e411500841c25002d2400307a06100c0c541000080310014201a11200b83e15803601102780c6208090400030749107210b1000140c251707464140034010108a034400400c1003c80326420540c40c080b40c0e0009400ca55204420500c050383e001640c00c9081070784811050072408030380e110014136549031034041c0e0340303c0708802c0b01040700f1b02801c0c1050310864107650b042140000071001240d40b04400e00c100d58012202450380c0c0003629449151380856030044100714a84170b40c03510204071253b4154001000030b80e40d503c10000300011b004014117500c010100030710002d0308052690b82d95100d980001002e001c0300d01c2000e410480d0a100002201e8403100c01c0c0c48070240c51a4000c0e4884e0f01040f083c80303007520311446003405458248540000d290046045a052420503031001c1440c4100d00d0400c0e5120000b8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 545386241 1250 545384991 545385011
    0xa09030327090203010801200d05070215010909150903170924070905030d0806100c1e02090108010c020703080a0c0c06090504050609090606010e0f0a030303061d090d0e010201 77
    0x10070108001c0c6035841e00180d6940c5000001400c440000e60343c0510307141e180c3e91142000700140141d880040292200049540b680750041c2c0c42d01488012020082045100001c3e60a1095001094442c0030b401e180d0091203944030080211280f0500050101d0510480341e008004a207180c5984500200d00301d968903010b040e00c90020684000940c20210f2071607041042d0294848120402810180c004003006100070f40b02500c1104000c0045008102d10040701c0d03c842d118240d17486116070040e5071304c0307442c100b0140c0041560940c44016030040309103400009400700c05200d00442c182d0350354040c0c91900e085070354a51207944041c45980030041c007140110081402052209c0061000ba21040200c0349810240300c00d844000308a54441c0c1d45000410440c00004941160b100c4004d180604044001800240814a545110641107801c1c00e5021042580561001c0240c8042042c2001030081e108020919101e04440805043e0083c1c4449100e0600910030034855990500001ca08403800c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 545387491 1250 545386241 545386307
    0x303040b1812090a06020703080a08040809060d09171908180f0f12161b08071413180201050315060313030806090103210e0d0b01030311030a090303 65
    0x54040208240c0c0041d00f014145440580359000784211b0014226491840d11200154058440341c80140700809001a080001c10011100030040040295490b280382454040060004000490f583c0392803111540c4181e1071481560102c140815251029032250701040303413403c001034900c010401c0d45101c00c0c090700c0d03024402065908411401800d4a6802c000650314224404c1911505444d003002200307080c5000e100241340c0d5940100354000481da44401c0340c1070b548a19884541c542c020b8140101d245202120400d03030500007103820510089150480c901241c2214040941d0704500000701d10040d40644003450b80f15610005281c0890301510119049600c01c551200390000074900080804d034001c0720690b0070034401c0d140440c00358110303681e01400b00b200c41c0c40741000c4003035881494030309440b40403590741d01e88016000704d05405140c0341c1822500b400323000490104140900e600c2581200005442c3c190069684180302c0c0ca2450b201030341e082c8001032078000511000300e80c20001000e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 545388741 1250 545387491 545387503
    0x1c08030a0516030203010b0301050f03100603150e07050609040b010c05010c0906030c020309010807110a0218060414041a180a05070e0c0405031b0a0512030705010b0405090303040b18 80
    0x2a082001154610b800100c0c2c02408a500940b40c0c01d162041c0010b11440310300c0c0c02684d040d50801c0e601c841d2000000c80000e4603040c000030a00d140d2034100300001c4104102d4608000042c103501c4014811449100c7c055500d40000c1d00903d60014030a109032040c6182507040240003110604118415090944499007034501b0094208042240d0303000802401d5418420364000540714805141412410000241200b00140880c3c08200700c2c3c1c6030054002000f813022607c065402001e40341c107581c0b544c1111038058011a0518442c901d84031a0601101c14030301040e114070380c0a502100c00641140500031051000f41403a800c100c003c290f8001c61100030054036031000d00480041c0482450300e06404600310005140c5210150244800c019a0310001405041c441c001500d017842d041c142d00109a0b00c101c4d541c01541d01c0395408164030010b0070007000800d08540031300000e102000b6208144800e45600307440c500c04581c020400100400c0035240015002001103051031510800011040c1c42c04e8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 545389991 1250 545388741 545388751
    0x711130e030307020d180e040b0709150e030c09070c0b1005040c0512100501020307141c0f0e03010b150d0e060c22030206190302040801090f1101080906061c0803 71
    0xa8090701021000680010406d940d1845c076824519103581040c030500780c1c2e0040900010031101e100d0000c9001d003030050180d000680303022805d2406803a4640310040000031490340850190244040300201410181d0391580b10f0361b6183c4411314031014540e0303555800ca074018414039040c9040c5101007001c0e612806040c005180c96a1016152445088140711481d00a4a60060f51004050030411644c010080c2d0700d4403034000010326809082c0c000c03100c0c101110b01412141c01c207505009062160b802219081d00020300d6500c455907448048281802c0700d55000c2215070000c0c0802a014407050801d00400c1161540603010a18000f4203100d223207484402d55005903e00401300d9039900442c58440c0e00300c04150250205481b4034919008203a0602c9812411071052a822139034a642d2030207074048600078403080c002000039100341c7c240400e1106540c5000c03104001001c2c0006080c0d0b101d080d145009030400c41c06000b0b141c48140401c4503c4081d0a0034001d50300030b80602d90040303030074036001d94810307 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 545391241 1250 545389991 545389993
    0x4050109020307110c01021f020706090503031006080c03060d020d052b140f0c070f0609030b010605090f010f0210090c090605090c0a031a100f11030711130e03030702 73
    0x341060140644008844e01c1d800580e94042400c04869a0740002c1001520380440f42d126286c08036a4500c402030310400c4005072503a4141210b10080050010085104110596942240c03a403210070454050b40280e802d52450381080c000302e181d80c0707081c4181c1c4107984e10040c40009104c1c1d8039601e113820a842074214185405c0000c0f100301100c0415041c4070307000b14852809131089607040c54448000e010381016110244000328a0f078035003c00402505000c1c04e036600f80c015809540b480b0003410203405000460394001c0b020700020b042c034001c106946100c90020a40c0e6581d8110314011109222405d0075241144601404103140c510b0521451401030702039014411058140181c550a42c2d0b0603a0000e07014601e00410845103802032130036650a0202c520300400c007005152020012000c039010021f521400410650400542040c1281c00308605a04d42c00c42403004003074401e4480c02a4000078200c560b6540c2c100300c413458400c090300c243e800d02c0382d0000307440001c0c04001455038208980782409 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 545392491 1250 545391241 545391247
    0x15100302211605040602060408031b04171c0206060d0302010605040c0e09010b04062a120809070f080d051e0418050f04080a0c02010c02040516080c0c0d1206050405010902 75
    0x3840c2100a61540b80781420308001c2e15103840c0c030800030356454000384041c06961020020803400052030130501c0082d43c13a00d501940b103c1e20350102078040700042000e050345201c4c403a250180382c06d84203182d0b900d594258014021035500e6805210403c2030055080f0308655859070041090364503441200380c2a03036a903a43c10300303c00301a0f05000c1d20303c80c1a040b1303600d2880240800c02140e81c1c420440e4103410104500050340b0200d00c0c0d510a500782c0a500000d000801001c01d1fa4030b0190f20120403449010408111080d171580d50403155003003000341c080c0c0c60150300309050380c80300b4034010320041101e4070013900380c0c3c20030007048a0484650b03003042d0006820202c41801303140b0061560f01900b80c0090504903201c84a05140c1d03940c1e11284500c00c888130601004201c0441568056958107408070f4014105000750303d094801c9401c40c5180c3c2c1c0116000c80c0d10a00421007280f42c21068641d5180038a0050440b40e4881106841c1c010400c5880c4541c9512444041100d0b140c6014140c02404402d50240e1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 545393741 1250 545392491 545392501
    0x403030b122103090d050a031107030302070203011b120209030a0203070f1e080d0807020316060c020d050304020a03060b030a08070b0610030209011e03320f1510030221 74
    0x140141d0051404408014024032901d04d00114844144804a04050780c0d16420300500754060800a1022026140003103864030a041e01600180030b42c5100f10005c2105983c41008020903282c2d040810001841c40c4094a40d402100e500074140060b0003021218080d0312170740080d00e0002590000f00c0080180b1104000100c00b26040724858100d04507804e0300a0709256a080c3d4551206446070100b00581c00401c5059000b4000c441c02c0f079220000304e5400114a044c80e01c098840030300a1001481107055510050784180c059034081d59000300800c07020341c5141c41d0b0030058022035248c00e5141c02900c1d038031000516088010455540300d2034a50380305203030640402845550007401001850300402c100b1505031ba000040d0144412003184000300c8400003002140103041c1c0b407a0751141c400702185200d00c3c074000c0340b1020002000c003508a100700e07a02d0442080003c241a11159103820320024003003d0340c64540104810b14195140041c02c7c885150311904441d004041010070345158541440 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 545394991 1250 545393741 545393773
    0x1401030b0a12020118080319080718031b051003060305240f0c1c060e010611030a030903050f0304240e1005100504321603050403030b12 60
    0x1054941100c109406601d0b10100409a03902c241009040003c240000d00c2c9018003040c0b01341c0544001000c89850300032020400141c04d08110004021580704400220407a2060340c40c84000052030318804101880c40c1e40c3c46051000c8a4603e5181522090340031850b40ca40512500e0351505a81e4041007146c034501341107003480d00c10302e441e8a54000d1018501c020040075004039806c01c0040c809108141e1301c540707140015001e06555000340c21403160308145030140f5608600c060b02d00700c205408081c0d0380c459080e10007050020021000b03400c144032031030b03480307020750b001248060003418203500d804a40035201d116603008903800c80d400301d00c0c4002560412000000c2440c0a01e4801082164903080c944203075903444415880c107111621600060b480707005011a200041c400a4000e000482c00725484000c103c5280b90500400c2e5418008a00c03007001c000540f034018a0000314001148020110450103401c0082c0142c0503d0f45a820b44101901d45d18a1104404a554081c00150f4482e4101c2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 545396241 1250 545394991 545395001
    0x20c01111803010522060b15220815090703021305070305091204050d020310020a0e031207020a0b0d021c0c11011505090907030602030f0a0b06071205030606070c140103 74
    0x4580203030300d404100301c51030a403100e030490041c40200b42e00c0c2003013407149480e030040c121030222a03400481c20090b148c3c0c8110301c8406050303c1c040c2c6040500c000008a0340f0b40c8a9100310b803040c408503501542c645030706907104003070306a00302c09601c0c1503c00542c0c90345c020030f014608010110047c280d884080240550307140c885c80c0e400c00c00f00c1c0c0141200104500300c00300745004a000389440707010403a520342c00710b5400b000b00c02c191204001080d912140450030241c200814000c107d070190180340310300100110004201d44205a005200703030011030034001500c505401118489030792a07403c211068a179480b010606400e44079a450120380d81481e054000c0080b202c07000d05999a078100000501c2c05121101c000d020b951055980401076035803030079800d01e40801c0d58005080c1d02d200000b406440d45003061818850b40c071540e420300408018906000781445410405010440382c3c004102c07405104600440c1c10030030013091281040308640310a854492564044810703103d05030040741d44d03560507001d0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 545397491 1250 545396241 545396287
    0x60b030105060f0405070521010509130b0c0901030b04330b030103022b0b0702070f08430914060904030c0602070c080a0b1b040513020c0111 62
    0x1c1c401400d005010031149444000304910494031000000c4a00784541c064409000b03400e58000030080260381c51030441242801858001c10700080002d4001c0d02100d00715003100e501802142d410340d11414040c03a20780002d1505810507072603890582c89a0b403540184c10803610600e44000760300203000a00303401c10124140360341c44410200700030440801d0f0076050340c3c11650151205c00078a103040310030706140501c102da0003003400c090311146010301c0080701d4194401e840a40840300800e88507050302c0f50f408224890071001f83e10951601141901350140a10b0340a400751450b001d08440d00704240700d8610605000d801030810103030410440d01640259600115003003100081350400e480031819500d0021303c06024011162071500401555030b046410f2540c1100e62282200d440350141519548520029110b200e43e06003c110708050203039810314240e501c40d800354038181c941414800e1424206808402c459401d01000c1c20302d42c2c080c040c42c2d0a004e50070403440e40e06c0f003050111419094150399 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 545398741 1250 545397491 545397493
    0x1080a09030e2707211503140d111c2001020406021006050d020a051509090a05162a05100203070309050f07060f0309060902120d023703110712060b03 66
    0x141d118645d0465018502a40c0c00205081c00b06010304a04006540d00c01007000150306401c0c4100040861000d104a41c282c1c2e501c4900140e5601c501e80c0c1d2030180340c041660000c4000c11400386401103030440e0010500d810059103100342c1c04005da08a0b000b80d807145000da001226043c3e00e903210740c85a0001f5040856403001d0707120040d00072540c1160310340512406042c5480803c03030a0101c00c000d503075154400070169056850f0800c0329070701911013518245100505041c2401003d030007241b1021110000a0540c1c1040c9802d91164420307001d6100151802d009500301100030400da0b0008520030f0186071030105000b0520301e8124606986400002d505420807001446010346c41450581c05800e41c2c0b0b030100f400c003c542440b070020900b490000358030003800c0d82a50704401d004100c036448140755800b0345080905404e89480040c1c0440300301c0d5064581e0302c00e0000c0e5030700340d511810390945c001d14001d80005164110305141079000c1d0068140e0030b0720b502e0104c04001d034900074074403c880260 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 545399991 1250 545398741 545398757
    0x6410904230109050907150507030813050d03021c020c06040b1e06010507020f0415091512150b09010e0f010f050603060d08130306020903070803070201080a09030e2707 74
    0x20784600441101809500030164954002c03640c542c200b000f541000e450103050814010707240c1e0703070040d01c150f014140c00c601151500c000070f004400343e00c140c40030054000300034000019800d6800c6000354000801540421084203600304c1241480c4080c0501d0103100313009107600c1c20141004070103000020034462003201040c0c00e010111000086083d040701082c01d006444140510004080301c5036035801c0ca402c00c0c602942e105024030030303820f02011034404800070450805100302201822440c0d01805001c04007009201e030028210fa030448400e004041000181c06a001c0c000929201013030f40f00ca0880380b400c0080c418604907242149004250501043d1080d80c075180120300540002001c140c89504580b50240910624804450501d0a080e016800c0c05440f4500503000350440760303d03107009100390400400c12500020440d06e6281d016101e45205648841e8608081d1000c0e507400c404000d10036400003804d4440903a058149880071082c251020840403403801050350050a40040107406 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 545401241 1250 545399991 545400041
    0x20304080706090c05090c1201080c0f091b0301030305071403160b04170f0c010f0203040308011806030606030f020f15090607051c0908150106410904 66
    0x9001c0300c0e1115800800400c2d81202401c100f918035480340c3c40355420981300410450300008020040404540b851030110701642c943e0511aaa820030f03035003440d0403080144414009241640041e54402c02001442e000c8032645100d10346650404e0740210080f03500440c0c004200400f850318448407030310304030066041c1400b40c02d0b07040a0090158010f0145003411011400b80905070140c03260301c80d880c08690380c4c2c0c3c0c191540c0e40d161a603c49144031000d540b03401c0c0e8113514a805030003208e0007070380c0540d40d02c00c107030b420100f2000d494482808042003140c1d45003c000300250650243c8002075015000e10012080c40340140500310085201c0d087c810b14220b032081c010300885205950340713888146d0b031403a11090a0b10304a850826070310309590107540e0b601c1540e80801c0d4003542c41425901c0c620107407203041d00341c91001800e100e000c0c01201d01054000e15202c1103d90707940d401a81c81d0a0381420007100c100d05a088500655664080e2200e400c0002058402401c1901400807a4040b00004210910300703 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 545402491 1250 545401241 545401253
    0x309010210020c0c04090302010b0a0f050a05010309080d020f2106040609290a05042c0601060806010e061606150501090803030f0403140a03060e0c03090a060506012106051201020304 80
    0x450015a110746c1e40d650b180402e00d80b00b54020401300310f025200700c1034640c50b01c00c0340444a01c9403141501c5962030101c0803549500c2802400c00456021000724102003814030b05102941203405030502e185003d01915290586a01d04040d10081d85003414109051003030a00041c0d40036900002041410300703ca800c1d16a4007030840c4403141e81c11105285020510b0000100501c202d6440740b40e106040a0111140c034801002c4084000714942494988903899499591201801d21550b00810b007c500003ca030b650180c401c00d58240d0005008034a00709281c04e035802c01d2090b802c030688203155558054a02e0b81c2020768100f020f41000d00b01850240d14100034941d0782e06c4014500982060400c0114003094042c10358140303403814a149042e151010168010006e007000e118042c00055543d01088500c51508202c03406480744070040e149002c0c13203450341c0e4082c10024003024104091030203580203000307124520704041721031498080b403030a103010b080103c400b0362901c80c2500c6034030401c188000140 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 545403741 1250 545402491 545402503
    0xd0302030d1a040f050117010b0a0303140f0415090f05030703140c04020408031312080d02070302100507051b06010b12070903050102030a0c08090a0206040b130312020309010210020c 80
    0x44508000b0950700702c100e04000d406030744000301c60342090601951841041c81c1e40c0125042ea200040d01614042c02e40155909036150145442d41003042c203c5c0501c00309214446880c0c032442090b045d11f14002001e80c1c01c4045074031943c0140032207009200600307012a404425180140710034070501d4181d90600c4000b0b40c40b1501c41c40010700d0946610042190700310203201e00701d8042e04c000e108540b0750350b0b2600c00b142c0340c0e4001c0366030a0099403486404210000703030241400302903070002409420a0000301d210002944100401d50a610804003100c9000d280c45c0030300c0b0300c156001d030b9030707151141c0209424460943c1c0130010b04585400c01c000500c03118014100f510780701001400b03d2045912a500166081078072900702a0030740d40000100311448480e60025421a8225074540700302d5510380e0f02c3c0b242c41e0300d06600700030340c0820204410011070003040301500d0741403842d807115110300703580ba40c944001100408648016810102e40c603180c039070f01449800106804400b00303524002e6200780071504d440c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 545404991 1250 545403741 545403757
    0xe0c1c09140f030a1101180f230309060a031b0f020106060908030904270c0e06030303060f040e160306060905091b04020a0c060f051518040609030c050715030b0d030203 74
    0xc1000c5c2840007a42000b500f00b032180c29103130500300740d80740300314101010004000c0500380d510711901745d001c0a05802444121010702000e00166007800c5610007041001c2c1d0100c154642010b40701e18000496401c446880000b6000075154000c1c520b18400c000b07802d54065900c0b000602c00c0c07140082000740c80100884142c0c0400320740000703148000301c10b0701071214440d9440e414bc0404800221041200610502d0150792040080305d00c10759588007010f9403031000711145604580034490070040c5040ca5002850f0200111050b01c4580004e0000c1801000c0e0580c001c1e611075445100400483c5150300c40c040d0050081d00150882910708006243c55101901402d0b02445d070000e003600070386101d480015001070748100305200101c1e0140f06817000d86800d0b1001444501064404441450034011014500303058007111300342c80c2c0c1c2d0380d1140070091408500a50078414603400400c005002841040041c206200a0651000c0e013000e005044900019031036014041d41814000480d40010a441c844 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 545406241 1250 545404991 545404997
    0x30b0a030b010b0d112d0327211b012f0d0509030a030b1c17070204150e070923031c0e010215040b010e0c1c09140f030a 53
    0x40d44045500700000c000b8481c80204185002c1030b42a13000800c07241c001b000041e50340504020150180003170129110a84a0120202c814500c80507003207840c0c081e000c880e2a4030700c15991010b05044148074024190b80190103c03800020b020075030900300388008413040c5801c9008100d20403000100307000d41200200403544074031019140411201c07084045408112000000380007500b08104010b40d690094051000880e05041c6604a07030300b04164640c4810282c3c200d24201e28038a9214070703490361244201d840050004005003005602d56006200c201040c01c0c241c981150300d003040c00c0000000203403444040100a1508001000400b928510b0101500c4042896441444000791a015490603002610080740321509100c5030049200d0852001c00c0c3c098601f6606040d06d4122041400ca800408030a840c00041c400d02d4245110320b03030703c25550074503540342824000c0d0700c100c941074108052075100c1d00e805285040200c0086440d006444440042030320241d030f8550075480b8010b0040c08410 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 545407491 1250 545406241 545406247
    0x100c0809060f0c0708070c0f090507030c0f03180204020f09190b0a0305071b050d0906020a2d06050108010204030c090b0901140310020309030c1e060412031e0b01030b0a030b010b 78
    0x9002d030150850386e01e140d120541c02c080603511107070301c01013501c1c9200302e016452a101c00201d00c5070090080ba105400c0c41d503210070b051011000b080d0014203240300c440c0f5685000d00070100040c1c69900c0289100d12400e60856200c00103201040380c603100600d40c40c0ba03148001c40c0c0410804078920162160010641000700301562403400c01c40c0c5080000d008540103094403c052010f004000c6680c2c01c101146686542c40252102c00682c0d8490003444d00510a15101300c4207009144881070341c0c80c480c0d4102c1c07443c3c1c0302081c1035120380050741c20a81200e01142d40c002820400c2100c45030716035004001c40c43c418004480c02d040052960001442100900016504d401c4c18940c1c0501c10b80f100c071000c50b1070840d00da0800c0410b0940d01c1d0000039a10a40303101e4240d04040c03c089951740c4201c403810b204e00030a01640d82d07560380b052004100314a407091603140c039001110703d150702035002d4060083c10b20004810441c06c000409982c4958086402000c10850602c080b540300148a41035484088003550703 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 545408741 1250 545407491 545407493
    0x5040f050618040f09030e011809020a18170705040c05090d05011b1d0619111c050315120d0503040809030d110645100c0809060f0c07 59
    0x841c80665420141e03003e440c0c0500210355580d2603001c040060f0183d600da819109a0000541c0c188014405400150200702c0701040030303403607580084c0000110b41c505080c0e0030040d0012500080314680010703000b684031843c080c0428404114180042504550501c01d075840d100b009003580c0314551080f4011022141c510080c000250000c03158841030002001c1c0c0400183c20050440d11704c00070051510072030060b055900c2c41c00201f91001800181c5041a885148071000d41d1080e60103014039030079011b115074107203162940301e61007901217040d41c840540d40c1c81e000c040c0c4491881c8940c0b6603845506010103032840ea4500180c41c0e00031100300d081c110396a4989007000440c84c050410110f41c14840c282e01181030a51000d600969401c0c0c1c202140d100b9214280c00c00a02500342c600e00805205644500325000c640341042048a0011080404600c00c080d10305401e185503064546c0d80262035161090030917500c40d0125074014030200c064801800e01280c03030742d6240d0b0040c110402d00500030481c64 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 545409991 1250 545408741 545408767
    0x702070e06211e0f0a030212160c0303050a020d0306060e1003020d0e211c051e0108010501060e030705030303151f09170a030206180109050f1c05040f0506 68
    0x7800c0d401442044404003c1290052a0184074510148502c1c1c002d21a02c414079410010780380c0d01d5294150050100841e58150102841c0c000840d1a000500306520000100300c245880c000034601990701c0720f40d92036600c900a403a08500260040c10103103482c104110340b90340134104400100017150040d05918450000b2130180c06890411200e540c80d185c5601c48550000a50840300c0100c02c10001000143c10b00e08400c6002e545e411140c42c41c44240e0b056044070855110a6005540d4505450100101e1540d070314180c1c0c098101109980d9660014400c0c150441034640801d80304400520500e030500d000300341c4900008e010f03c0603920f00389082d44034070b03602c0e01c0001c00c1c0c6500013007054008016128004000c184140324000c2001c102c0405001032620100f1000c08054064008009944030480716444484200001c1103407550b82e00f04800c0042c0c410301100c058881240011314081d00c5024400508800b03c050b036101b071100030402040340102800d00e100480e0b200f01d61894442d0080307107081c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 545411241 1250 545409991 545410039
    0x1030e010f0f0608060907030812071e030f0b0d0822050d06021c0e1b030115032a060801140f0603010803120604050c04030f0f0b010602060106080702070e06 69
    0x2840e6054100141d40900030b110f81c1c03002040396880400c840ea2516610406d030b8540703006010280c82c011080010219001c0c0c092036041e08450344d40340c2042418841d1310b81c0c407501d0f083c945040340002c2e00e8850440c2491600c0c0150101c0c114103c600200780d0100740c2e1424050303c03840981200207019010300106030807010030404000c1c10003402c0c0c07101c0d0b69090324003d8000e511410f0101c41d5001000300ca20f2144010307204904444201700300500003d40c0b80c10b400400d0402c0c170319449034550b483c1c0894405c480b42c0c4825540007148900b030500009519510303001c0445030030070032242580703040c2d0504000403580001c4003030444003800a21501c8800f13a4022980c5078112030481da4001000000002e07030804000001e04070188448084a540d4543c030f020001a1501030703c40e141c0190040c04180082a0120003100c01c041c811084120088415a100c1c401c0720004d03403015000d600007100410034207030800203042e1b12104520180070418100807000e142400f01420241c016080c100f10070203070394228265 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 545412491 1250 545411241 545411261
    0xa02031c0905150901050a05010f030602032703040509220311030c030318190b07050a050705060f06030f0c0d0311010f1104050325060320040b03180a02010e01030e01 73
    0xc1e43c2e002140c07503803500c0398418203a0310b001c0990701c0e09000600c00c80c0140b0415050310f9031040b070200e240380b85845d150083d400280103000c0c03c1100008a802c4e0014688150116070558009940c850703160000700016407000508a4840d50170103502c3c2c4010441d0303089050b0250f941810300c40c080c00f00d10902d01d4a94050000c407891144000007e003d4000c0f0980101130807030448004444025000002c01e21410110502c010140603411021407056401100034044401032032030702e0303404c214603070300d41d580b03003000030b840b1100c0c454081c5060050900b014044042001350307600040a005040201003960303840342c1c802c06010405030421045235401c2c290020300015005041c140034159a840220030f06034020703c91684244100d025800c401d100745086462802141451080103c0c5807000680103030600d1220b00101013800c81c81e40c0300c9c81e85400050409041c0c0005883c0c1c036890700c4c0002c9607503000742d0b483c1c0d5486a80041c8589005070392113030020059030402e207004284030300c40319030303090140c111101c1c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 545413741 1250 545412491 545412493
    0x70e042a0e0705030f092a03010b0310090204050612030f0f0d090321090503120a020c0a030801060914090a09020301150825080d11100c0c060506060a02031c0905 71
    0x3061001d615400f0025500451030203400308070a440c2c00d10080e640f4210340c00c01d03560b140460b290220000d08050880707251041c02400100d880b5100d840083c1c1000305100d481c80304680d450345a00c055081a01c1560b40c000f4080c0c4000030410000c01215659009000c5000410800011409039800d0309809a40b000c0135580c40501980c2140e14015000c62443c6018003414a0313411b4541054803800d006000301c41c2d80041c040c40c0f4240036905250550300c4010102000300b83c0801445110340c0c0c04000c00c0540300c0c0650785642d865410326000500e9205190710145025190a011200e1682c60080190704160509000215900d2034400700c1c0c0544040f44003800368407803a4000003003003040482d290030122407103809006503000380d641c040702818185c042d11a031a40000007109030303039006031a4605045560700441e0307171000000240d41c081d10280c2c00100002035000d1581e404011141c015160801c4040b00e41906003540172200954a00030088454140310105403003135080c210a50100b201250458 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 545414991 1250 545413741 545413769
    0x160c0b090112051f180b150412050309060703081009090b0f1f0f03020f030a110d06020712210e030913020c030706090c0617281508070e042a 62
    0x50094503a089002c0f2085c01281040c1c441c04003440c224003540b00d06841d8000701402d0505150b510b06409110748403c07600e6200c208010401a5649000b4040d1148240d950b10090300c0c111101d10510384507507008903101d81c209001c0c003001034510202e050344a0b8403407581200c01d58440e210031a104c1891441d0300312000500c1c1e00410301841b030b14440400ea9009590b00388401a03914103141c0d80302c942801c06800103030000452402460142c66503594940211409800d0221380c0d02c64080d20f01c4040c021001080c040120b520240f0030391400400315450401c070401c0300c10710540f180381d202d1048403130700e910503040614803134032440881d4103861001880300212030b2078295903e058001052080c1081e24800007801d400124144503501041c20000720704800000d030303280d400c4400c1458450092190b10440d1003909611104818030035a840c480140e0b01c8032060502d0155480d080803001e800440c3c6101c8800b040001040c0f03030201480909000d44c9141c08001c06a8500b006a02c00039041410302c40c0107a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 545416241 1250 545414991 545414999
    0x30b0a0e07020d051606090f05061302010f050c06011509030c18050c1e0a200a0b0c131401030b0325060504030210030b03070803160c0b090112051f 65
    0x10003015104408980854441e03545103001030704c0c1e030702030780701250300b0074550000c0400024601d0300300e025440d12420150942040c651740300d50030902c007203038040b040400342c5642d2025503034000910102500d0b103081c45403820007018089900c1d602c05018200102808043c0010f0380b520410443e030080d60000e800007956606e8105950236241480500c030002800c01d404120350307038000821210300c99003040310120000f4210030a20303169082040e0b05c81c1130001c0310110441007454412301c094110014000f80c40318845c01e24000303000850280c507082c854803081c8828100c85401c00c9000060f503040415050601a06900481c0981400010386406000301d61040312411500303201c5641c0c000c1040910480c0e203407104e2003211035009038400a94000c1c1749007007c0718002d02903405061040409170030344100d11b0300e42da6001c3ca50b42c85071201a010325092052042480302850050303000d41488201c0b1445c0480b542e000034203018a09240c0d50304245e0b6403000c1526010000300074040140c0c541000d43c2e03030650b1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 545417491 1250 545416241 545416259
    0x60903161505040f15090f0305010b040f051b09040e0708030a020f0313120212030a020c030c03060601050a050c0c0429101b0f080c03030115020a0804090c030b0a 71
    0x1e200305401c40c0d20740301640720094001d400b40d81c00c0d40c0e10180e43c1008240360000340c0c0081c040c100320b21002d20104140126410b040c0078000005140218008100060220141300031100303e80120701c40989400300b408610141c4c0d0702d58240075154581c41035111004200010300424407000c0401c200d10072410001064103000c0060054034400b5000d942a240660364007540341d2141c00008148005a0b640a0180e00d200c00544581180081c0c4000e40c1009014080d519551040220001590113443c0861061804000d0f8030300e080c0c030540150219040081c00642a4003e1940c1103043c0071002c200340707580901c10040072000c980000c0050111400e804c0305c0d04500168000e04001c07456460780503846a0524500302c40c0804000d58410700c00c030070602058045115508812034401e1403040124005c9482080600500700000c0080c5540754509030185000d40d9000d507551040d50007206400d40882e4102041c0c0e01114650b100c04248a000d503082103000700610f59a096020380310410100d15040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 545418741 1250 545417491 545417533
    0xd0e1e130603060c09120302121b0604082511040504080c0a0c0302010f05030906011505090d140610080619060b0c06150301060b09040b0604170f1e1b060903 69
    0x5103440e50120a030300c544c5510195401b610000e409a070043c641c800917441c060008020f401e880e5408181807094181d03100382084000c1c1c605450010010844005803e04088042c1040809102180c050301c000c0c1d69601d4583c1420318294440c554a20018060080741c20840b4418144407041e02c40f50006803410910250305800f00340d00080f420030342c960f4914022000c9a000d50404002070203940c0c64802c1e080340a2081c52200c000b040014418071046895203484025038512031007a0781179502070f04480380e103805030040c902d051581482d4001c20510f000451110303048007101600303190350140003103c003028040e9a07001000b500400110312901c1600801d409010f0700c07040403103680200c0e403801018280c0d1101c1c0103200360000208044101e5245c980d014082c580700103450f0b5030501d0f544030050940c180d445140c04010760800210495018002d02509150f00d0360a155540e20240c1d099110b661800200c17100400c85038404003188090780c458040c0e9028180040841e11902422140180e20513 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 545419991 1250 545418741 545418761
    0xd020d0b0103062115020d020d0e01020306130b0a05090406050402040507021b1314040c0611061e060a050306100509060d1a130f03030b030d0e1e13060306 68
    0x9403820422016961090280c1d00c01c0342d2100b58443d03800d00c0600c22044410405100c01c58003401c0203500c1214071000da001800034040c0074400140c45000035001c4509561550501d52840d91042081000e641e0712507802c040503800c9400005025001807010450354440b640007e644801c0140c1000b0400c401030700300b02d124510a54007844a92a000b400341d80e10b1a0b001035402c40c4141007040409682080c0326101e0071410400c1021a101c00303010100b55906e182910142c848010710302c4144501a0094031039540c0c0c4510000520707003032803c0c0f81e940b03c0300440c0e107000700010340000000c9103c075500c261658010380380080c255092030a00746d0118140d003495214960203050214009295847c20041189607580c10125101e14900118210b01c00700100401d446030f020720030201100440c244d0100c41e001103200741c03000a00d00b100c50041505c0e040402c00c54100304226503411500e1929804504c2d2810981d03403171100194110030000840c0440702c0c200c4444021300d000000418041e17607400418201e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 545421241 1250 545419991 545420017
    0x1101020f03100623160c030605040b040516121202010b090106051c050c09090709030b0c0304030e040903090513060b03040b0604061a1e04030203151005010509032505060d02 76
    0x18104136034034004030401201d10300048a8040c4200000c81c16030300aa4202c0398860444403070420340f030b44d9404080380c009440030303070f1041d00309001c000401c801080b1350b84406c609c048450030380d649007003110130181441d040000c24994000050031f4401e4000d40080c15180030007040e1405568607208000c01c04d811403c82c1200058020a1200441c0400e2240328014440000c001e854200c4c080240030b42c02d803024042004000c80082c000021419036003200c0d01428440e1551036603810719040082c030144440313402070300c69072038921040006a0081c5c104412a03005031400c0f0003000424200e00b0007010340358030030260450000700b080304110314245004e02c0b80d903003117908000a90b164a0003203032050304500903020540c1c04004800c503041007800d00c40107000b8840d03089864280c40b0b50100341004a81104c000e000f446260600c42c00d15045480744019007028a0310074240044800002e5885250801d480080340002810800c112a81e03440003000c2c040182045030b8801e03202e1400c0009512401a580203 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 545422491 1250 545421241 545421257
    0x150e011a040b120a021519020a02010e0a081c051909030b0a110d02070609150b040605010f050d110403020d080301140d0b24040627020a0f1101020f031006 68
    0x2a03d0908201d4a0f886000001400d00d8800d55090007160741000110300740c045000c4c418600403140c540721061417030180c0d07406007000382c10500c009440c50b040d8054483c0f04e0561403074140203000000500d40009010503c2d001e5000300903841c1038600d4416688000c54401600c620796007115004011442100d1007881800d0803070784c0c0c2050060445207501c240946020080100e030b540032240360094a407050245c1000101d0845c01c1c0d503807031102d15280307140d011fa40d511240501c40c1803405206020040001b070902d54011414400c005005104490300d4281d196503451034040c1ca00b40001c252006141d014003840001c5e074480c1440e02036500244651003c090301180240d405090202008a09541c0000b0071001600c810182d241036040d400840c1202d140547c2001d40b081d81c9a0044a009018411410064079040445062080006442744102600401c0482c10b036542c01404140328488914024071204580d5034110f0291040c00d81a820802d400306c14410320050099410040720803544032210 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 545423741 1250 545422491 545422511
    0xf1e0b0f0601020319030f2306010f05090d03090b04080a150e0a1203020d0f1b0302250c09061526040803150307080105060f010206040b04150e011a04 66
    0x12442400300c0301c050041c0c0061214aa15044103c401805c402550401003100c2c00b140c0140c004891030300a8030400e00300e0155211940f1240322250036000a420301c0c02c104a0448041c02402603c1100d403c14010b480000d813807028984505803000140544412030780c2d8413551103215580d6a590501c1c1541e6881da121101c1c43d200343c0f0351081c00c440034509000740030201c0c0c054507000c01940d504800802419020000032480d10200d12a80e6004119031000240d9900c040d46983c211001c06021402498070400080e000d00e0450014850840300c886000c410401040c500381807048050743c0402c1200d42800d0010600f42445203000c5000425a0399080c0c0180441c01c1070b200c84440b540c0c1d85211049040081800300d550403008681c0103140d44c840c990510584030200e454241d1039409804540d640d2010702c020b80c070f0111121004108244001c000f903040a4465102464024000515048041003184850941c0d5000481d100038050001c02000c00002800c0601c1004001d000303124034035101142c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 545424991 1250 545423741 545423761
    0x70303051f09020f0c0604051606020118020f12031201050906010c12030b040612050c1003060f0e0411040c02010c08010605032419060f1e0f03090f1e0b 67
    0x466001d482076094400340b8600303202d80000394031001a0b1244d2000030442c4180140e4208441c502481c4a4001091040f002c1414044008a5034205104590601d203820302110703542088031400303c0d011202c510301d03103914000080d85c90724982c8204030f060002007400076600b64400f028904a40003a2080503e0b40d5483d00111001c0c401070314001c0217940c0140b20071100610951061000520141c0009001c80c1c0b0740c0c1c1607160384003400d48200c4e60703544000c00243e242d00f0100000400c45850b41014461603062001142c005403c3d8003c0e401411000c1001a0a0000c2009001c00300300001d00b0400c066442240000e01900b254100c42d00420075a00000615902c0cc1c03088074400e1480c0764841ca02a12b261404c41d80c032400189050b03501003c1d604904074004100300e19003004040c107842d404c01e00703402c0302d4000d41480300c01c0200c104501c40c2c0050303210009030000703a00d0071608841d143c00568441030f0b00d0b0905403a510000c001d041e14860035988040c1403200226041c665000380c191061030380c1d41d9a030304 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 545426241 1250 545424991 545425021
    0x308190203070807050a1413031a100e1f0b0702041406010e01030e0a02100905030613030e090a09050106061214161404081507030e01140402010521040807030305 71
    0x500009910000083c00d0605c14070162030800700c02c1c50080040d40c0032180f185669000803460b03160303802e00c03e4000c10403c409110003e14903100800303481c80e54030700786084056507a52403280c080c4024009001603140c0c0020700100000030740b82c200c2620642c0d100c0315049156004804220301851070304800760b02a0fa1008005446080c0581d210354050000c00c00450161039010250344680c80f580007a400140c0c0c41c2c5100c0d02d043c5445607101c2103414546802c0614005024005814944c500507401c808203600c4960840455416034034a00c49031602c11000d00181102040640300f54a01034000c20301d250f000045215001030003c1c00d05c000200300e03103c0d001c00c070820350741100989402000112054000e18000100000c55520ba80c1819510110345080c0300e09042d0b2080200e1590b0100304000350141304a001002c1c010000300316040485040e10000c0c8030291000e0f0602ca40031035010080d000f00c01d00007210141760340000070542820315201406420480040700440d04000000d04050760314004 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 545427491 1250 545426241 545426251
    0xc181f0e0103050d0e1840061b022a040905010911010504080303160c120305090d0518040f0b060c0a021e0307030f02030115030302160b13090b06090d0308190203 71
    0x15180c0c1c0c58440c0080007245110000040109204601c80711f4080304566852000040204074040340d501041d00e40103045401e10385042c00080c2c110303065084102e030300281000d078180550340c0c07000c40154030701250040c1c10901d8900a90050600b038819040141c103400c8441541e2140320600b83e01000c420040d10280100d000e07400c401e41c000d00000348200c0c1c0c6072151019121700c43c1032040c0c01c8201034440841d40c00251208001081c0c41e0414414540340c200200c00c10041d940c681356003082c656480500c03104000c0d50615201d0354940401c0c0d0b40d00002580041b0442c8001860f2540c0c815410801944a112045081c0d12900303c074841c240c01c03942090b060a00195000340605031180c155651121024000501640c0541d0b0f5841c2e0750785a00e100a280c2c20295003e03800405280d91410b14880300c8840c5500714400c0c1500a05c403080103107100b0721a18041c0c510b800004a542034400d40412503c5c003d12440a81c00100c0c24441020302d604001058044c01040940440011544500c41d003030340b1059135 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 545428741 1250 545427491 545427529
    0xa110c030a0f0c05040203130b010b0a050a2106080c031605010813030c0203012306040e06270105070e030d0305040302031204020d060f0e0c181f0e0103050d0e 70
    0x920303000461110b8004001c1d4483c50a04205903100c502203030807a0021178800c4040e4a100001c50244604042240c2c010309114440a00c6e29100c908018110f01546140000340220001c810307070004107a5902c0a0183c40c40c140400040da91460010341ea00300490030540240100c0c044260341c0c0844484e04425224180c6602c9040d0300c0c0c171602c42928080061013034041154200400e00141d07000e0040d8540e103140d13a5441c2c40000c400c103a85001e07214001d486503102d00d01d407040180d1000720200f11580c0c0310b010520039102044602101064000031040401015403a200c00c2040c400d4014041180505c41601110044100080c0a4003262400e450107005a4810f110000f03040300d4045501f6480303032000e003120741501c200340e17200415102c1a42c445c00c0c402d51540451300d442e0100300003841c40c0d0b20084881030603100c405030076040103e00291a13041344210f003c00082403040c60981d02801410340c01341214a943c0c2d6410145d0b22100c0c2d0140d03040020780020810300d8903181c10701d0084020a0152 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 545429991 1250 545428741 545428753
    0x16090f050303030c09060c160303031a03060f0a110310030506062d1804151a0d02060a02030903060702101109130b12100203010f0807060c08070c050904080a110c03 72
    0x13540102c400d4204e0b00c0c1c1c9940c850400c001c0c203038a1072002c0c801a0242074a074030301080328501318076010f81a9861440f01d0078001c864034404850a070380c0001d401c0d42003c2c0d040200003c07510740242e40c0c0003811803154465001c840c000140484d00c80304035016030441e400307807085d00d8040c9c5660b010465024070b25518010004464845454004a055404d12607400700030200c03d51401024030030f1030254000c4800b43c2d03142088440203060202d450052062640003511000c940302e1017203000070a01340c0001c602a00800c00460042140d9000f00202d41080d0740081c215500d0340752006000795640f8801d0418640242001c4200d0341407009001915031052000708200401c41c4540b0728840100350124055503c01051a80c0320752100c0c1c2400030400da880300510146e0340350704081070350002510b0303588042e03001d900c0a081088a00e501c0348100120307a5120340c1d8a5030341c0b4814200040248413070303081140d01848860a0008010880c00180400b2003c5c1e201c081011261107021a1903034006441710390190401 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 545431241 1250 545429991 545430001
    0xc2d2901140a12080307110c03030f031008010e0a030f030902091609091811030f06040f08070b070f230912010e1009150902150a021516090f05030303 66
    0x5024494050400070303016103900c65840c9003c100c00d8902d00c405840041c400014404c0c040d60003115a07441c1c07120b50005280c4500001c0200744d0300d11860203d0708200d000030001c1903405030a00450402800600700a0103020f00c1e542c011522500030140440100e6000c03650010094080e0007200500e54009181600079175030607001c1d28618100340c02d184100403054070b0202d96510a841090340342c80c03000100d61564060703460001000c22416500c00d1087d070107075406808200e00020007076401580040343c03480e42c40305481c1c41139581c0a00440140301e5a104810021007581c48024119000043c0d990803800b00528101c1001e0041001969080300c081003121103032605080611244c501001c500004940e86c640d044503041410700307000906680d0f101d10240f0107002200c0800b0038000800e010030030500e501980000e030207805520f0380740403021011a060a030107009000404070800c1640b00c0e40b10920306455000300041c0d08100c413901113080300c5004603828005610300015070f10701800451441d295 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 545432491 1250 545431241 545431259
    0x4030b09030705060709060e011106060d0237050d02091803130b030f0708010f03030f090504020a0e190b220b040308130603050405030a0c2d2901 64
    0x30103910407848100100000120704204140c40368440340d4800b030201e402c0001c02003000e81c14013074060402c0120303600c46d02d450380b0110740990804011640f800141e01d041c80420255401d42da901b4140d854040c1c0c440708032008102144102900d0584035210054541c2c0800c000c0884288000e5080100c28000541d07072102903840c3c0401c20004011281004806400004940c15980000608410120601011842580007943c0084550904400640c10101042201d20503848090704009084a111801c0ba001c0d00c0d440c8094000904150351710b40a540020f06450500340545024048000c0601404004071082d071003902c0000c1006881d1400d030085000e04100c081c024841d0300d01c4071150000d51014460010001184120720311038030b62442034040210880503500500505050008010000300c0c044221800300d4103904040340c41c20350310b043c01e4450700c5c03201e0031050403104020743c3d00c1210705021000c1b0400a102e5500301d41038423101044482c84100c1d01c440c56540031030440040c00b00c0340c1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 545433741 1250 545432491 545432513
    0x70c02010e0a0306060503011103010e15180703050603070504021c0f0e0a030804050d02070b040608070e04020417060c04050a05060a020111131715340e1c080403 71
    0x40145071010003001c034400064049101648119100c0b556030702d0800890601b0b025000d0071903600f14003a0b04540c50700c0523021070104014050561140304030340039411541c030701d0380d220040100d00401c01039038540240080c000340810750300303544203200e503020014451603d4021500000b905002070565003510b000488081c02d010752840400310348500c86c6a002c250200003116003e80203a40f200c4030342c145400d12034102503001c0e40403800c42d00814001e0151070450f00407501143c81c546804001d90ba100003040700c0c50721220103a2944507000080c0011013210000ca0401251240c806480761500d5400815280b84102d00c0794075084100c00034104582e03d41398028207040c400500000c124002460b800c07030041d501c14030b022950019900d00c24414010f07034012000d05000e041000340200c00d0b40c500b900703030b40c928005c115980c030303c45002d801012041c01380c5508000302c603039008012030055071342c40c0600311b681c880d9100360040000d0f0000b41c9010bc903035100729091a8100c28558503203400c1d503e075824148 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 545434991 1250 545433741 545433743
    0x3031b0f020907020c0a0e041707080c060c03060307061706041509020301060c290f090109170a0f05041401050d1d0a050c03010b0901050d020d050609070f0518070c 72
    0x310a0104a009611142900c610880c0c40354007900440100400b000015000780d0045285140c400f41000002909101c0304070300c3c9290102901c0e00c5103828035104415125248196180b03004050501c0b0944540b00d0155000311412003e40c3c3e40349886120442c1c0c3d070100c0c4100a1a40d442c0107000c00c1160030325a105c4c020142e11907081d03401e280d03144d4240300182e03402a4007520000e1042c404000a0003045068900383c0204149092178880c0f401520003a0940e01501d00c4541c05202d802042171750b5000d41c410038040b03a00c064a01b040083c0001e0b8400715404c584281e81c08a0580c40079201c2c2c031840b40c0b040b10f042d1118048000f500360300010044075650040c4508202c0315640b00c800d440b81c0c090b9003001404100c011002411454814a000b0b802c0843d0182e0a9001e6810840490301c2c0d0f40d62103103042c0c103441041d508200d154529000241d5144580c10028003680698001c0c4880203001007044010740b604215282005a642c4080c000f9190612011103202260398010500072072280c0d040050107 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 545436241 1250 545434991 545435003
    0x70308043203030702150103030c11030705041a0907030603080a0810050607140c030c150904060e180d1815030f060605040906091116050115030c0e1003031b 69
    0x169901501d040c040d01080c0c041801e5440803081082c166410042185143e0010401541c01d51440d54007801740c0b202e154000b488012444c0e26101962001c01c4024010f04005006000341c85207a020300780f41038823220f1b000c1d01441e00c0b0000544410301078007131202100e038050b0f009480c02814403403ca681780e0707000c0c00401104800d00800039041c2d6459001e04521800341c19940c0d0192080c1034801c0c5030081c80d003180c82c02500049489401603841c42c0c203002c10312500c200c00315903441c0102c0001c2d00510f0143c220440c024142030910035003e8101d102402100d507008100d031034035030302004192415800c551811103803440c3c40304240302100c40d0740f841094660440c24017042192a959642090782c0454101d000040c3d8007050800000c0c0403802060000c0149640401001d001403c065040b07114511840e0a0894809001e074100002540305800c07400c65074100c240000d0322490154140c0c60700e80308540784410820040385241652440d040d08482c1d150704d8a80808150440c030441d5000c1d05041078800e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 545437491 1250 545436241 545436293
    0xd1101020c0a03052101050a05190504060611060a05010537060f020106121e022d1305070207062102220b0c10021605031201030302060a0207030804 65
    0x344100402c00c00d0b490301d00c6504d5003034503015038551154154500701d510002d9024140010012a240d4010f460180e4a090395803a00e04207000381c0c00c4600100d5503105a410629145002a2079544032000300d0a011441003a900ca0b1345030201c04d50305682003030260f1540705500c030500003072040000080d440707441d01c806405e26614210003c240b80315442544030102058034451500c60955080c803604003e080444044a00c24100e51a071001c0604070341c240211420b00340034000195a604003a1541d01100e44140482c1400f00e10801d1949080d519000740c0581e0b45145c2c10800c0c0c2034603000f418440c0980c1d6004003001841c119044403120480c03a62201c0080e222414400c9089040c0010408044504a80da8000304440110f90051065030700c00c07160310509000c0429022001f0580c0b4280740d00d00d020141e10f8a4a6003005104c6410702d210007826444000f45451880103941b0585040f0f80c066020750312540d8070b49402c101a071060010080000d41c9440010f800510489810300c0e000f02c20046001d2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 545438741 1250 545437491 545437507
    0x8010b09040e0607181e0314070f120303051005132a05130e0103021807181401120204080307030804060b121c090311060901020a021009090501080703050d110102 71
    0x10508906840e040b002407016100f1704100c0ca0501d007224020315041200040da154039000c1a80040030074000106920310428000340c3d015400c12802001c3c2c0a00e100c60350816640d0031003d106a00209000c44c01320b4103290000d02e170743c9440079004088401c054030141042d503005d55020010242c012407409034095103041c000041c509241911019802034031116992031003006098061403181c0c1c80000084550700c010b00c0143c032000c44030011207a0b40300114a0039150280181e40d2030b02500e100b07440600311043c1c00620b01004400c2420303460400c1c0c85407100340300c52076000e0059124030f000c0c0c41a20ba000308060320001344511103442e881402034a0000302c0c0c038030a100280e84141c0540350341c0c174a54071190358006ca060070355068909504450424482e01392a43d5174020307014103a068505c0c401e40c0c1c081628074040c4d000784141c1d2040d039401810711a5134648040c01610548050081c0d2410302d151400100b420707400020b90005894104c4020104090f8244007100c0e69a0b42e14a010784030354081c80b00003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 545439991 1250 545438741 545438743
    0x1141623031003020f0409023312190501060504120317090616020c0d0f300f0c0f020f0d0b01321809010207140102031e040308010b09040e 61
    0x600442540c2c0580680b00d01e5401040071140340011960f00c128a00142d11006035640c0d21a80310701c5d10200741c5141e070540700100c1103034822100f000302441c000b000104600c0c030f01150071500380715000c103000b00c0c1d140c840801420000c50710240124008100100300030302510b021000040112071007450681d4144c2800b0814611a00055800385450303800304091200c40c400700c001e2100350103510710091412010650010b4800c03860041c0281000000301d0117031080c0400c032507240750741c440d506101120740d140410140c802d5002480750500083c508800c1440c0d054440c0614002241d0030188602c00b100e03168080010160042e43d0081d07200e680740c10420002088501c05a008048241c15000c0c0c81203100740c40140001c42402d200080b20380541c03022842d0b070720141d00b201e005400ea080039100740d88110381d0a00a210b1410090000700d4010101d100404054004502c078080012400c40501d07458425103035154000d0b1001004070f02140e005200e840c2529000d0009250300600108181c0455000d071 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 545441241 1250 545439991 545439997
    0x1803150605120a03080714040e04020f030303040507030b1812090604080f01061404022712031209100905100902011e0e0901050907090302060c010b03010e030c01141623 74
    0x2550340b5400110302c2e2070500d0342022100307a2080c03150804030722135000c1181764400780c0308500645074401c6050020809646031860195254000941183c2d40ea0500742000e0b41d1b508550701c01140c2c403000440c00588113030f06902c810444400e5080c020420aa100444401180c110344031080d001801031200241d1094100305203030f03104030701390000560103041100c0d070f40b114810500c04c14015030040201c1001e018006510202c0403000a0504d000500704c64002180e1649414805440c0c8c480032840a00d03084041179413034002c0c00000c003114040ca5200e20024152082903071b01a1050300118000102c4418075081098110300c14500a203648046c09545905444415510000240254055140d86c184044d95601400d800c403404400e034030303007048001c181c1409404028060350010400c25040c80d000d42004000b018002c0080c88a1444550700941da81c01c0714552401035801c0504c1410982190301d91039004206080305540d108000e03030300503034020140c00d503046d000d4901d444200044003620f03405 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 545442491 1250 545441241 545441269
    0xe0c03030406090906060e0604031401090b0a06051e062a0601090e010c0315150507020405010b030712090b0f040317010806060307080102040b1b100614040501061803150605 76
    0x984143c2c18100340e0a4000c41e03015030003501c10f100808a50752010364a1380f0599080f6640141080440e944c00d6004d0344c09041083c60041c5851000411f02c400c841581d04035605035038095402c0c2101e540b00071054103603040d1721642c1035040f1904001015078055603590300003181141c2c1c2d46502110a07008021807a050090744100011555030303603070400808080c00b44c2a032581d2a0320b01030280c45800e920610504819204481080c102c0790380c080e0845002c2c030143d445554004204119640e56032002c19400da0049882100282d020a803001e0f60b46424810a046c040d0041e4210025541d05030040b992810060410340a114000601103401c03100e218040340681070010150044d0b0038a4403e15280501035003013100d841e4010700083c0408090b24050721003601c52000200d5000052401060410407945001f803100390030070002094038180402d011407945000c3d82c041041380c2e40c44408641203c180240a003060044450400204a001e01c403156030740c1500350006041179540e800101e0f62050114 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 545443741 1250 545442491 545442497
    0x1404150912154a0321130b010b03061c0f02090a09030203030c030606130914131e1b0e0f010602070620030f181f0c060e0c03030406 58
    0x104041d4914418010507031801a012075030700c070503d200061612148510348101d004200750026580000e8000c00c0400c208a03010070507240d40b1050076240c415030b01110442c401032030fa540d42c0441d480b401808600f411064000401a60304d0b42810b0b005c24140c1d102400313580c0d0007900d01032a2103441c04103075503140710325118017801c000380703072251052107500e041c000c0c40c13200800c1c41d00b040440400c0c0c02104407035001c02e09074841d40c0c3c3ca035544400141c0034060300320700b080320b8494641c020950ba84c65038400d04200c070543d51340076540c1d0b90f0860541400324600000070b2100d41d2402400c0790550401700806d140c948551030150411490040100181d5400d40c88420b144c008031050042416401d901c0fa4050324144c409485414140741c4041e1100d40960800c044509912030b040700350300014400e4890030402d861740b2a0752805a00c3c030403d803c44d10249418400d0850301080000c00c1ca2405070010240810746642990103502d03102c0d800101041c100c60345c064002c02611000b41d990030300003023001d031415072 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 545444991 1250 545443741 545443763
    0x3081b071a030f15010c0609080c060903131a12040f05030f04030618050706140403050303010f0303030b0a0e180102070c03140d0e0a090c020f0601170c011404150912 73
    0x3030482c43c800d40060b0071441c81d15200c100381e03142660301648401d400d50b00000085040c0110346480700145c800c10301c1040f1180225818042076100203c000d1034400140c018181c2d52545039410850310703007111002c0103142041040f4180040109400040d8000d005882030300c032144044c1c45280c215401510b009010f6034000030300b4410804644120500c00c55130501100d0554050399501d55104118000d200c28441c04c614403040c001c0d01130044030b02175a408400d503901d0303580d00d442d041d9020355070b400100c01103805c080e20700300745040c40c50b00001141c4030141107840f5603c0d4000361954481c030780180c54009540030450702c1c1c00f080614026000a52044006100c500c031209075803400c02020303503019000c000c00c050000f2050350300c0c20000c40c252045444001041c1010700f8041e0714219040d44400907a004c0c41c0c000203050600d9040c558202e0f81200c00b556040354554004650410740c0c9008061094010300c003d10004016500e46880102c039410031903c0304c0e44030030f48101c1c0c122420008803000300c848 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 545446241 1250 545444991 545445001
    0x51306090b01051921080c0f06010e012c09030c1204050108090601030b0f060f0409140d030c020a17120f10060c11010f02120a08090c010903081b071a03 67
    0x1680d241d03200d060100014601c007a0401d003d40e1715400740341c001d5144401000e0486414803400b9030031564443c11620869452820100741c494448100344200300702210030707000015034804800c11032030402d64260404055011400042061031101514007440c42c8001e000000400c0d1381086808101c40010f4103164a580c5090001069100000d20b41d01107504010010000102000741850f00100d2411854116581d1007010441c01d0b42d9a450f4254002e040411304000c4c090194400b00c600e51204007a611207a11140c41501511085040c0c000142d1244410310080360300d040c01115a02070300e503036561034030150b2001280c0340c0d0307016101515091101c0040c8091684a003203104020000c83c20103030907102c0c50f80c0760f1100141940240c90b050140200146581a00c00d10151010045050340384c1d072900101a40103080100c1203a03002b0341c81c405d03440f0b030780c4d0550301070561001141d1f0301005051415080003010544a0329484102c0e00c0d5105024020070700181c6440369030310180355224400d85910309 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 545447491 1250 545446241 545446249
    0x1202070506180301110708070303022203060203091204050a05061e0f0c0c1806010309050a060f0209121914030d110a0e090c03011a070602030a020408070611030d051306090b0105 78
    0x725a2a81781c5404204481d4000412207810381d051281c141c1801621107072041c1c0036400c0c003594241800e118440d0310788044204051750340a1402500b121040302c3c850580c1c0b080c6040b15100f240102d81d80700d405040104550720b80310005051010101010200385030729a042c030309041d00f0881c07800c050080c0104144418010800600c41342d110102d580030070305011101407103051140640382904242d191314484080c01020001e03d0542c41d40600c081144801001040000b50003180e0164071071074621044010988001030b03025500040010011201c0c50707990346801c3c07610816000c030241c0b8001840707015190840ca100d1011601000f19400d5610b2803150f000500c0301070701c0c1910078842e28040091084009907001581e05444045428100607090100090a2401000c40083c40d003400001000381868403900a0412140b41d44112003040c0e0302d41c20103445c5404512200403042d84148205200e40c8134980000742c000320035040245201c00c1c95250306c0c0c240d80d007100040c1c03005800c8400404c80c07810 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 545448741 1250 545447491 545447501
    0x905100305010b0d0203043e0604150e01020f160e09032a01060317040e0906091c090b190806030106060c2d0c09050a0b030a1202070506180301 63
    0x1618035080255606005494200c1d001d401c500c0284543e001c8006810400301d40c6000320340181806074007120b0300844098120941c03d40c0000100311159902503c45814910141c07003ea07012404001d40441c2e81ca0811210308059003c403604603c03c0410a4503d241c06008080107945030040c4462150300f0300e00021103000c4080c0c18404a075204020030600c085000c54025640a11640e0b040680b80100d01a01e026180c1a0000f420009000140d82035030800100100111080c0d04040c0da1150b442e8450152030342c40884205400c0c0d00490000c10811203400f201490080071428a00e078015140c2e441c901880d044403c8032402c041d140d010100301c0c01d401c0040c55500c10b40c01c9000340040703030501d00010700c400c500d108002c0c030b070000407e4058004044c4880307000911a0300070211428081038280402011624890304c0015440c00011030342050141c090f5280d80c8401900801c1001095640c040c81c40c09102900400c601035541c001c200740c1d031142c008240d50314002c4400306900f81c080c820075003116 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 545449991 1250 545448741 545448769
    0xf071502070203120c150601050c070609030c050a050306180a120810170d080a06360902061206210f1504030c081e0d0603050c011106011a0f07030905 66
    0x841c20300c185041c959001520790700b40c00c404c142000306c544445005031514040c100581000e4099240080b51a41c0d0100301b0b20103c0703029007076006401c2c1e900c805001c2c0b0759259008181e0140c001c00c1c0010f0515500b44416100e48441000300c1c1d5541c0f5543d12801191404440354400189180e81488040c9061606031009016030144590540000c610340325030307480caa00100014450018006030030711034558844c200814480c06185070050f1140004a400c414801c1240344100441c14620112035840c0b00368102203074003401191402044040650044200511003030b030080c0700341c001c182e4500d032658070301c074074903003124018941c1e140003000e95402c00b03601104400000103080200310200340e01545400d0780c079410080d85560f03041040000c5c60140184c02424142c0500020000a01141a402041146e020740700781d6091500c00401107607800380d10300701e010081d0300c07a00050040d800348142d200c52050a500c94603250a0a1203401d045036003100c44e058010900102c020010b41c1070000d04d40c0c12403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 545451241 1250 545449991 545450023
    0x4090c080f090606120106091103040506090106050a0603020f270a08031204020603070c0c06020304031e0c09110904090c0302150703050316210c120b0303030c0f071502070203 77
    0x545420b5190301e565100c010200d074401e01240501c40c14548007907000c00e01030000480244400b498407000710b00f142d80144c03070803075082c89543c0029800780ea040c4107800c15940000c24810002e1b1030050118007039000381c00c00c441c81540070050071b040c0988034004a8580b0201c410f0943c0d600d01e501040000205c0a940090342940040066500d280303200c1010982c00307941154043d441e502c0e824003c680c0000018030041012404404c040303007054002000c2c2040340d1290600310808030404d441c019000c1c006910081c500719114206000200e1190030454004081040b0503041ca1141302c0020306031410a0001c0d5416403800005006600b400886600328145110109207003460307da070300520340d21000300369400d60500d940002d02e10921951441c00001200c000e903220b031198000e40300c4018544200c101001c10901e4001200700c4415004094103804010051411035a070141070707030308503804609a011a440c2c1000003000046207a0810030030741221450060f22100c592040c1407170000003040c01c02e04 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 545452491 1250 545451241 545451271
    0x70501050403020123071703060307063e0703080d15180209060403060f050f070207051305060d02040e1b0402091c0219080c0f06030f010e070504030804090c08 70
    0x50f036005003101050742564503071011190420702c0000821b00500d503000348119882d805440c90f58109902460082004400743c0c2c5810390b4516040d2a91040c02c814601103550901d461801c5600380144800c40741e030072041c0d824141000e40c0c041810004140c10031100c0550104050061102d540318250b07201002070500c05509050600c1c403c0750345601051038100d6500003810545d262521401c0d20011540650180982814a0f0010000d46000c552805660302ea610014141d03a2000482d001110400740100140428800103080031704001400c1c1504000c0d4001d104e00113071110710680744803020480c0913148050301d11005142c850700307100002e413280c0e0050000c0b01c41c507031b6140f01100d2000c2d82002884020b034150310214415038500710043c20700b048447c40010350400f01160f0000000310403104541381c0c0c082d130020051513001c143c4c1c504081c0f18040c001440460242c40150350014060f00705242090b65039510862170380e0041e003100066640b51080d40d042e068100f8100707a0403151030514012 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 545453741 1250 545452491 545452493
    0x30318060c08130b0f031501030c05181c0f1e03120b0103090b0108010506270609060112020703021005180a110103150b2a0c090612061305070501050403 67
    0x103426401c1601034a00c1030000388141d244004800000c00914210b060031345c440568988441140d0801c9800e011181c800700340d85052580b19110300c0c07000c40219100c4504084c0032502c0385c5d0b200c00f0b1701d0303036426000400c0111100003900b10b8031315580f207030b845684e101d140044a171803c1501d64000c3e0400740142108080d0710340000350808949212003410800000e42d6176100e5004078060301c03107044060504840c20001040e10748040d00164804c0c20243c030124840088910000381400000704d8080000143c4070106c0c102d031030400d0003540c2005052400320050004850300508030b911045040300903902140340d4985500c11800361b00d81c0b24540503078500d5091941c1240079140c12000d00300a003060310034146003400e6030007580701c01500300c0e00c1e10365517003480d840c0d020710007807075100001401e602684140000038001c00005072000b4042240d010b4035000383c0783e00902100d070001508460303104d02d01203105510088200210352203a01101c00441740303c200790921504201c050703044281003000421040c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 545454991 1250 545453741 545453747
    0x1020c1c0f081509041109060609090f0417030a02071205070f1506080106090905070b031303030e030909070806010e060307090501080a0e07060c17030114010818011503031806 77
    0x201e460807410820b51960b1481d07074a00c215900840c04035405070009040c48140106c1c1c1c25a64140c503000d40c0c10304980d49a0b070042103c10300803801900c2d400220900010000e280308010f0030b800510031544045c8101d0504e00c0e000c22908219501d0500c1d580c00301e0480284090005070307801081031401c005141023829150b6050340e00c1101c10103030010382c0c890444001081280d10103002012200020002c1e16140d58400c0c000e800c5020b42035034203100f032500c042160100c142c200d90061010400440e254281a50b060b4054880300c00b521034540014441c420355a102c100c3c420f0701c107907681d0751408440e02c2c1440024020140f1580740070701842090080002d100d07004141c0c01d0659000742010440c940d01d104122000e00108154540c1a0013011400620950401010000039119000d01c20a58208000c80038850101b40318100d0403480c00001c0130140d500907400c0035004800308107100f40c12881fa4500c2c50030340380e800d99565580d007030040c410414190701a002c0c80e001c04c81e184e0407802c241d10b004c8000b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 545456241 1250 545454991 545455007
    0x5030105011b0320010e010b0f0109060810030206040f06080f091902030a050a0501140c12010603240b0307021009020a15050d0c0504030611070b04031209080c01020c1c 74
    0x80703550307180b88142031418540034440100c0c8009042d0b83c003207110011141494080d19101d0300110030366007005005016880c1c4020001106941a56100c017103034074200742107880301c1e4007910030440800044004009038607040000d0020b481c00340e60300c040c1c2c01d2601400401c001e038000d050003c190303101d00a00814620104034400448a035003402c2c0c0601a10703000290410280e00c00090180c42550f4242d801c12206420990380c50a0300c90021509a440e285140418444c410002c46a00c03510301c0180f2000e03020390321191411036000d400d1805410682c016141c41405600520f42e01c81010082003982d0380c0c100046c000522150205001e0030b600d41d40400c0480d50180105410b0b111118044d40200f48510141d03808990280d01c20f0180103021000a04a50700c0350006403405400c3c00d80d0303000111007480440d103585911504c82407940e030701e0303440c2242d44039a035103c0b04144030307204c9a031034010849030405080303003e9500c0d0005981c2d40c00740303820900e0329003510003081403101000301c5d1180c815040300358 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 545457491 1250 545456241 545456267
    0x906030c0e12070e0f090c01091a0313060f0905060a09020312090d05030d0504030e010906051206010201110c0709060f051509030a1211010501061b08070f06090b0907060503010501 79
    0x80400e88050070b1000ca06104913600242c400d07542c04400c200c0704840c40d680c4075010314483d20681d804009800d0044034a004c85000b02d41203010b40000281e4541e001c14000c560200c96108e490710390400075a58002034031b0400d000c10624a4840e0001020300c001848070580168940904008048840c0c1c04252141c4442149240d00b02c00801c03000e00e030392247c0540002855000b01502d684080102c50350b0010704081d0740a174001141a03038240131550048a03200155200740d00c4160400e00126a0300d524000300400d514110754a400300e00260980c2c07880600715009840000e8a4450701300081001150710661200750f8414080d8420401ca4039681c400c41e082d26000700e00e540d031311881d05000c00c1c50910300e0341c001411000c2905210a41c55400007050001c904490003d01c81e07a6030301d034022149508281c824010b440c0242501000045485000b01441072140850314101600303915400d0840343c00c41c1c402d450301a140c000b0410070040074403c7e113000c0c0c6182d05029003103504080000382801e640c009 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 545458741 1250 545457491 545457499
    0x50901020910030b130603140d020d0512100302091e0603030a0e150c03030a0606031802031c02070f060305090d0c050c042f180d0210050703090902190906030c0e 71
    0x2140359450f8454140000310031482d080b041c0031080c0c2e41d00d010300c400c98003d803041185022705d41c442034080d0f01c00308048401703418542c0ca060600303005101c100301c041070107060602d2100035604c0000040c9c642c941064800d4081700600074402c04031a00300001c0b4100109054807a030002c20078514059049800041c01260a5688a402c88806151508103105079141211248008020800400344540203003041d02c0265500703102c1444400e007000401140311000a61541101e1149003031010a0344040030520f00da032040f40c0a10f42d981c0d9000c060078085800c03030700c0000d446a04100c0c40207800c00901004800500c2d1148540a00b922019109c10103425030501c60f0b83c441006004044c2c000b40e01c01444a141c007008425070905a0700281c0c00c0c2d00c0038060b095001c0c0d00a01d240c00a1a10a01c0c006480c0d402508a81250b50400403c0352607901c4181d00310184508030901103103000c11407001d820400d8400605e4207981b00c45400240039a406a4019800c250074803c424400546c854030502e140700307082d1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 545459991 1250 545458741 545458751
    0x518030918090a1502071a0613110913090507230d03090b1c0509010e03031f0806090601030308100506190918090b060103060617040201021507050d05090102091003 72
    0x42c01c0a420100c64070000b8000400b4481d110a00207484c1d4002c02c040341c030915001c05030550301c054000241000300c0f420796000840c0303d0000004505d98100318110210752010702d24040003200040c4103c40c0329080c00b00e1040ea100800c008100c800c020440c050200c04001e8015071001e05880b043c2400001e08180c0101c10110a1000301400345c00e1f404040c01c3c209428540f43e2241c058004220514540c149440030308240c0865401401841a0070014070000040c0d4516503920b5010700142d600e50a50041c0c81d40403d00020311120140312642c000c641c0c1d480074210551550030020b0142801809000c4406204d090070031060ba215000c82c1c0b550140c01443c482d080d0184070041d1a02d1400c0d60010a144044207420b01040956502502e80c80d4071418129515480f0b09004408866082c082c074000f06910022586160f20b040c1c0c8159442032051045611044500720342c840f0040058851001080001c900505200c9650060076803001010008606110441d800500c495204580700700c00e0513520 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 545461241 1250 545459991 545460001
    0x301030c0b2d1306031b0f0225030f080a14180f04110a120e0d05030106050c010e0a1a1806070c0c080106060504030c06050a0806210d030518030918 65
    0x1600c140c0300d041401001d0391a8984c2e9035500039020300300d070103d40c500c0d00904103070013040a80600c0c0082402807503070f070041c4a078900380d8214000c2c0100080210b5a015030030007001001800303600709030070080d11408134180c40c1c0262180150048120782c680c004a107609100881e41281e00a180d000e00c1c000c01c0310340d000d800c0840c0c00440c0042581754040305055134005048103078142c100300381c1454145007600401220ba201902d40c1e880c1d01915240da40042c00420041080c98810000303040142d220400000e035441885801134680500148100d980500368040c407a21034050303040b416449040c80c1100c1803405818944075444210040100050201449620b03081c440e881d580d8001400091000b0811030fa01e8090140040e006071100b140d502c8403412010411510403000d0325460001d83d1078005c0592144401c109444c101110b00000000d0350450095400408102c004000c02880d1800282428401403c449200a902e1401c02c40e500401c41c2102c0ca8031100c0019203018502048402180c0310 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 545462491 1250 545461241 545461327
    0x1b03020d020f0414070e0112050c0d0b0102030d0608010c030e160b03090304030f0f022103030109090201030e160f0503190b0a0b1002030a0915020d2f030301030c0b 72
    0xb484d201940003012070040041040d000113104004110980b2420502c14a8908800c10307224100c540200040c0148480c0501b000150002c040b03408050065904001941000c442121119404008283c2d180c6c0307602c0000980501c2810034815488024251220f0b5500004105550510074199000000400112100707002c2c420764014651101c503400030700c1c00070308040c90036000c031180036031040510108994428611a21582c15503c1201c00741d42568a4011850010018110140d041c5030b103801c405e100d425010b010b00d490012182d196a001c080c1403a0450441c06210340106010b9400f0030440102440e50b0b511100915034016190b0110350f40e0140914007402c888641e50750414403008011910325004400340907c0540e40d551030820b00d584102c0d00d401c4051600048026801901c031010000344204d4002680380c0303a014868400c0131031400d00c8214103c1c04103007035810340c03c04001441000f14401c0a50014961036075100c0c1404da840f0049480050382d0540c032074810100f8280c24082c120 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 545463741 1250 545462491 545462501
    0x10c03080403110d02010f0f06080a260a05030a060e220c081203071b08030f040c0b1803060c07020609100309020904080a030c14030a020a02030715091b03020d020f04 73
    0x20140d016128021039071030020f400782c0441e211400b200b23810301c0003443c540c070a90300c1007604568000004000c2403101da2074150b5807145102440d8902c0c02c4030800a10b41c11100c0c0000d0140c1c12495403184e40d00c0c03802400110071103406801614500b030541040c060719000c01e010030f69048800c06071095030144186070050032050760b584028140d006413844440200c0080001d58800c04030303030305c464600440f2100101c40103140c4c0030005203044414000716101e140040082c03944140b04800507032203540c4400c8a04030320f81004201148010340317000c0180743c0742018000c241c1c2201c4a1918142498090780c0010540c0c011080c0e030340e0046120300014280f50340312703401c110501e5402030118480313803e150900001d55070002110001207411b0150314412248200750544810a031802e40904544403140c0c40c6000e0b41c00f01400e03108600c030901c101000300c0c10444100106071020f040c001a0410316203014991508c0b6603111040102c1c80807810070158403601e441a00840d411103c1a0b915100d900c0007d004103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 545464991 1250 545463741 545463767
    0x1080616051207050301061103130e040204020706090c0501030609060807060e010c0f03050304020411160b1e0c0406020616090e10030807060b010801090903170606091306050a0b0405010c03080403 86
    0x9248410f11000a13080401141610526900e4441140c0d0b04010b0310703603130310030030364001c00090000c0d004110401c0031105040d000f5100034800743c07a2400e0b0b41c64003c103690340f145040d1000031041d582000951f80510441c4014a1103035401c0c00780500e0292016120005441744006020720501030b0703100c581c440ca01400d221079020b1004441c8080c0341c03c0080842d08121012800b451038112040b044541c0001030700c445101030121075102e01c840303540b180c1c45250094a840008a503000e07080329580060301c603061244140c00d204503182ca1405000900d04200a40818803022241c005d55038290390068080b0142d81e080d035060007042d120311060f40b02c442d00b43e50000c0e114060220382c100400450b9004030600d51000d036200d10355a40c88941c11000c44075074410040100d0030f004600000b030200f0010150380b02100905140c100404400455142120110a00422941d6440c244034514201c2d009038003030114124000d09141c04c01c00041c00c25640510041c0921290000280406220301e001090f40 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 545466241 1250 545464991 545465017
    0x141f1a1c020a0e060412030309060e03070f0204180c090203040305090405150307050306240d14071d0c0403080d090c0b120c030c070b0a0209030318030f060108061605 73
    0x2000c080540038000d42105802000180000120403a07a14103201030741c003901d46d441203104441656030b506400802403610111001620b45c041c80551300000d201502d26a402041402104183c41c4100b00131645c0700500c2074125458003462038046402c40342c849041d1005850300603034907152410103952501520010756030250505d410059195110183d091603400141c04442c0034036100d40070151106e604a541074581c81d100c1d03a40d1048103003410600c0b07040c04005403030b842e101c4140d034903406511411134103274200541c4400c038200400f43d0740c4d9440d0040121080303400d12071400c01c405c4c2001070b03100b9444054440c0c540824201d1540c40c083e0300c001d44055000c03024030012941c5042e2200700e0b4200d042619060640000090032400c00c85040301e01c81da142446c298504641944c0d0341421140191000ea0559428840e148180e2010802484602c0e50001c6c810300c4403442000305454250003240064040d040040100081840024050340046402c2c41e01503400c44940c00c201c42a004140c01c076926 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 545467491 1250 545466241 545466277
    0x504051e16120203100506011b0809030d0503090d0504081e0c030a150f06030503040e1906030501051009150608090a0803250903050303070c0212030d141f1a 69
    0x8a0602060200b4414800e5044c0c50b0082d001020000448a0840d5440d011440822015203052039045aaa1065210304000f90410279850040ba2400c0340140090000c1a000428005e02840401c005003900040d460000d2600703081007130141d101c50003c021a12440c6410000014020713003800b441a4001000d01250030154071400c0c0242c01c1448950740309030040c5460a06401c0c140c0500818007580d801000451410b890300020428661004180300a007141241340c040116440d0f0090b54000c60140b03001003268141145003a10303c8010350b00502c46280f8000080a2501010503080112182820200c00d40c1e61001d015a041869222006151007000001c1013180c01c0c3e460368a9010644640d104ca000c114070340303401c0d500d07083d290001070003d620900008040b90710038100c800050f44090070410560707282d44074451a580140c090281499101c803a0039280030040d030441c517444003401d004008203542180c3e52950113985030040c0c0c0ca1140801006081540c8000121002004800703001c0179 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 545468741 1250 545467491 545467499
    0x30b0417070b04211e111b040b1c0b06030709020f040305010b03060403020a110102070f0605090103050a150314191a13080d180b0c1803010504051e16 66
    0x1441c0303100f110f048480c151415401d400e8001400140c103204d030004d4031036118a500800f00035851406204040040043d00144401a00d07410f100c00046545917150040400d40c0030030402060b24440ca15050040c0c060800c910440e1145810402105400140020103610380350b010034100b0000f40c00c040c00d4640006500900c03140343c00700420890380508020012450541d04054903160140c4000c1c1c0164017101120021070782407940d400702088140101c60041e6503403d00303ea02c0f40d4440c0d02c00404990085070314501c55815014a641c070910300f140420241c800c10480c03081c54071351341c00040d21252100044002d20b900402023460240915840717068401d11170b02e040b8442c04007100d4403280031541600454941d0707902d40c142c0c0305002d5100e003d44bc20400c20b503024400a11031074010184a1486400000104200c410b03824000c3ca000480c40e40d4a20052035560010141004114082e81c941001c00c80400c0000c00c003a40c0c2ca60340650010003140781d482c0030f90315100521043c0d04c403980010342c0c006 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 545469991 1250 545468741 545468753
    0x106051905040612210306050916080601030605210307020d0b09070b03091e0319110706110d0f050708041202040b0d0f02090901061d09150403020304030b041707 71
    0x100c11103008940c2480340316125404140d0041a03120014010038403424a11407108580310402d11041071031070001642c2d907480c0c0005104c01c03004c2d1034201c400c0c603003928a40c4c55907600407945540000e003802c1c107100c540d1516000c107401022aa16080303c440c0d19800c1c44009801c144200c0d61000c0d002807041482c0c2ca10350400c01407032070055981c03101714405c01000080300c0b40b0f80f50949100c1c00c0501d000d1300d07104c0c0050800340b406025842520300b050008018000c1e8290040356007066580349070703485845141540074010702d0154aa0000350a010b8207142111072a5000039480145c2c8070546440c00038500c40140665840c012000d0082840d0b10105020030003005038201000381d1402141e05004841ea04000d0046e11548803101518800c407083c0b200c40541455890150001812030001401d980c3e030384c900f841041e9000e010b411805046c61b0510a004208020390345198078264500103aa00b40b90760069560300c228030000b000c41354004001018005141032204100c1e28084843d69140010701e020 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 545471241 1250 545469991 545470039
    0x14090a15020a2001150e010f05040213210203010c050c060c16020310020c1b210f010603050f060703020307050301090506041103071808070f06031e06060801060807030209090402060c010605 83
    0x1170030031030a003810300144031020408140d0490f8060820303144000d050000b03200195105034008448a44444000101e8001034082401c15280001c00030324284114410907007510540401142009014001c4421103800494815001400c00d071750303159165210f039107101c1d8001c40c0310406581400f43e05032984260146800030814200d0420946000c06640c00324640280ad100201d0758210050321600e4018243c03007800b10400c00010001c45098002c40031060782580c51a030400c46194114001b041c0708050200503280e00203625090960a518201c10020000e0005206019a075034a0700007103800c0f030f10f460348914010340c0000301030f40c0da070f141c150000380115144c0b42250a43d249000c00000754900c01180c14001c1e6a0302001c0381c41d90318a0080110080e02c0d40710004024a400ca00c580700c1415181d1043c07200911080e00c40c99040d40c50488084d15225000f8004400e140c0100704020703966544d080542d0b40158111242501d400280c030781c090040440740c00242c0c12001c3c02c0041c944035101c1c00c40d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 545472491 1250 545471241 545471261
    0x60a1b080f071703070c0201030504030306230307080d0804020d2402030108100c0909020a0315030b0601270303140c010c0201020301181107020d1a01030614090a15020a2001 76
    0x407011500b0680c4061043c10300c4101c071745000040c0b0b40120580158031a4101c950418000c0c034000c2149525100d0120b48290900160a2514074110a0700210300341030110000800544014000c03002c0040c801500f9401d0040c00207101d074a480ea005000c001401510359415108a4983d44c0d0034a501c2030711000950082c001c4504510400d0000c4c40329500d01d00030344607900445c2e45d4400840b0715001050f00650815581d40c0c00341911290010722001ca452120001180104214001400e00c0030025117841c900f1101c0c40500c816803c01c0c05641a0385110704402c880c0d040c07805101c0e25845005810b00b0b805546d21400095081c217900b10104c0e5815005941a520021502c180050b4a0340c0410122110181c41c20007800c0144009009894210100c0c60306034041c1d0902c41410000072100c0348d4000090700212a400d5540b15507107400c03201400c00641c01000b00f030080503010090b0700c07035040c221218210b00941540000710b90484074130610ba81001c0368841e00030030b00c40035400398003240607202c0515 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 545473741 1250 545472491 545472503
    0xc01020a080a05060f011202090112020d020315060324060c06130b100f05100504030813031502090904020405180a05030c010c080f1f03120804060b0f060a1b080f07 72
    0x1010130300510b440c1844a02e000c2d03058581c15111071014901c00d01035040644840d06210b411525480e641c1458002040d103c01c0d081c40041c2c0d640341a1221b40046040e0f15030040c0916400d00c10000e030009816000000c000f8024050f00d441030104001a03428402c580841240c1d0054105000f0807090325450001210310074085290980d48036400802115418070400f504111068010845410156804c094408851610740d00d040d8998403242125030180440010f0907901590810510280318103640c0407604448040d8602070b58900050000074029102038031a079030390004110341c40c4800e95014402c0c280e0100380c9041681d1801c22940300d401c5195003a0b51542011907100722140306209803131243c1070301d0504aa203a1201d4071b030060859030700c1584004a4682c42070100c04200307266044c030550085170395100c1d050310309483d00005440030a0292030040d401e10850300681d03600e20f015150103480a00d002460b10085400302c00303841d074018074083c04003800082c040324030018010040c542c0c1d0340070385 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 545474991 1250 545473741 545473751
    0x22205030c1008060d210906092417090c0312160f080403061505120109022b08040e240109180b030601060302041a03010b1b030c01020a080a 62
    0x1806040d01d40d00007215155010001240014446004018258200030f01510309205901c10b42e817151030801800c4034503d00040c0b0b49000f40e04541c2e01407048400340c507051038488042e0346449a00c1f170000500480d07a070a002801c400e5000c44900c02c0b0319000224a5407030200f25141061100b89865100c000300040c028010440f010781c5810460003120803000207402c071203000070080d40b100031103010344440464910400708000401b05420340641e40f0703400d80c0c10001c03d407414501401c10040021040c1c0f8485581d0505501c1c8026948803244102c08455490658850101e0710b240d032240c0f8080307420003c01800d408103010402ca824420b00c0c40c807446001c0d41502464148490328180424040440c40c001107421800313006011007569125043c01904001141d0440e080340001c1c1004002d800941c0001e6012408001c220807241541ca0700c0800c255070245507505090007000d00f417181c110751045050307041e20741d034a10110030003c035009910080002c5440340020003004100c0340041d00c0ca5402c2c18202 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 545476241 1250 545474991 545474999
    0x170a1208011805040b061c05160518070905041a180106090f0e160507060518060a1a281701050f0c03040f0c050d06140a02091008090307060222 63
    0x10307101e43c6001d150018404540c568901040190400424000c3c549201c2c03d406071b800025403c120a2205140c83c1058001c954145070074404040c80c001c031003240c2180c200c4107210385a9040b0290a0030b079541503802049145450000604108010100c55009005491914400311005008074165451a52113600040d600d064501000c00ca0340140c4a90014820104030b0044040011612808071414494140042c6880e550100c5078100c2d02c48c0300041c402d2298407a02c001c00d2107015800a40c143d02046100003031304150741040045280213000b400e564007000485424900412a0404010070a080c0c4544480d0030314080813820440303c038203600307040208910b5180d80d8030141c410341c038000c15503045a41c2d41d00d60302c40341c0300c01d00000c0d01c7c011000c0f074011400f5158480c072072440c1070044101041011250b954a044800000d102091883c41405080f10769500c100d4a076107000ca603440c01086944410010038154854084014101c0388001611542c541c100c00005498844861107005a2a40c0e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 545477491 1250 545476241 545476289
    0x1b060207081212070f090b03040311010c030501080c060c031b070603150e0c071103030a050a0810080c0d03030612060b030f1204150909020d02090306011d01170a120801 74
    0x90314680018440036540000c0d13505109026003c03082800f40340c60120250340342100707042a40142c40c04d0b0f000138041c003c0d100d5000000d0203542c0c1821814a8100415850044515140c808100010b032181d03c00003902c0c0c018941c200290f803194130140d030310f251201c2516000207139200c026105000c0400c0c20704840962105003106550f0880d00007211301c61160b5950700c000021a0701c01c260403107440143c1d582c1e003a20354400300094a04a981134807095601c01d0038440240c100017000b042d034609107840c4001840445408222342c07002c010191a07091103400545000c1c0c015022540203a040740207e003010405100c00f82d041000d45040542c1a610b4008800c1740380da0700c90158008280d92644200300822030030b4051114003860454501d01b0b445241c1d00d4401d07600682e44604c9240c010385070007140c107007414541031120b5030041c10042403401c156081082c1c24205501305120707442c002421a10700200044007804000c10099100c1840c0d515420251005072442100303001d0524143c01c01d003802d01d050b440d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 545478741 1250 545477491 545477497
    0xd110a0305030601140d050a20090307051c0f210f08011701020f03010905010e010b0a1b060633110705100c0212100f0c1205041b0602070812 62
    0x6019500c079855560703210f0040d5401c804984184024003400c0080d916050304a10a0a0080030348a1001c1440c600c1c100d01301e00010745880d01005811810046188960b400080040403039406498000e80b845021004e50b0081c2d8401c0740c00342c441042c88032060300f0010200d090200300d01d50091001c1d1011101ca4007203d032034240046410105201000601881760040d038444c18061440c0009484c0540c9005206115042a070064004580795070040c03003811070300c2000e28003401c1264002811b0401d00e50004005905c3c00340b98924202e02d100c101405d0144c640c2026004c1c0030041740140c280c9814112000c0e100b520300507400e03440e490b01715100380d186110703851041106401c00c004026032410081003055a9558001c03034400e00030b440c4001c800588a000b00151400c0000d0050400a0350000d055029a600b150040044500d0510800350403604400d524a0082489000041541d9580b800402400b443d116040d0030000300700000440d40e500080407419640b410701514804082000200d03a940 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 545479991 1250 545478741 545478743
    0x60e01181203110f15040c050d051203040813270c090501050d0e0105010305100b03161814090c0315010308040b1c0207061407110601060e1801080d110a 67
    0x1d0024200e00c0803920802484900300030b260103881c809004a00f4513842c110007034016040c10403007401000103010800010000500c001d0715008440d5440c1d6458030307243c09099120014034403021011030700340010701c5d0035540109040d8052582560b00c031840700d161525420030580311240300c04a14030350b40d865800f406102c0007690b183c04c08050700f4080152256000b492042d90f08603a6020000c0d981c08007400341900850013180030300500e2070311617426010ba81141054500030381c02070480a8031113071424041011600404000310501c10704288160240c50701081181c4076030381e04014002255004a45002007485c110100c0d200c1000710306001001040900c4050182c00e8203200410030401c1110041a141903134110303000030b1600800c00320040303030042102a14200d0341c0f003038000c04120f102004d40782c010540381015031030701444480c43d40c5d494805000c0d400c01c102c1060040449034940e1203245041c00000d000b6140b01e0768644a0465580182000e0940000d240e100281642280425025102 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 545481241 1250 545479991 545480009
    0x81e07210903140d09020301052502010e071211030610091d060a0203070912060911010509030c120709050a0c03050f04031e0c0503070b01050306010f0803030109050a06050604060e0118 81
    0x10000da15040f02464000f03620078030b21180c5500407032006985c02e20039184605208102138501d1400b400040543c03a80c02020b003000e6a01d00400701f8200070300083d040c0e003298a08400c00609504a00d84520f04601d645103168051203500700b0b00c410100c1d00e20500b0143c401103502001552070030f0001c2001d0310607901c80c0d4601d58105030f02240070a1600e40086600c80220704107109456511071017151440701c0e107841650101ea40f0700f2000d0400180d40c01e42203100a0901e021404d005080000a4a800e80c2d441940e2080426041c60310000406211150080005640400c00c41c5044601400a4000211401e0001e440c02001031002c00100c0280b0340155050fa594500451390540c1c50500c0c84c4e041714180c0140030224000d0b0f00080c0040004007880c612030401109554506028189890010b0f0040d68031100a41014000300e400001600d0440e0a070980c08290340d154540050f00a02e41d9070000341d0070010006001c600d1640001000082507000c0e65141450f12021a003030701034071424020340307600d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 545482491 1250 545481241 545481257
    0x7120c11180a05060d14030c0c01030608150a0f0c02010b040c03060308190203040e0a0b0a0e0c0a080604060906080604050601061e032d0c11070803030106081e07210903 74
    0xb10000ea4449540701c00050440901d1044030380340c130702c5440340311102e4803407644c030006000510b40414064210f90075401c0c2014001182000c0402d5101e20b50100c101c020072103844001609a6503903003010003a00ca42240070030036880443c2d402400f8000e40901c06004904280c1c144580a101e0700c6250102c0388c004211509000c90486100003006d0316640b000114403052002184420b401e07040c65006000c100c0c3e00180101c2e202d414045007554a900015000704518200404001001c0494020b104603160094480d41c07440b0001d001880b945c1c00c24a00c840c81c4c080003080c03404000413114045c900075400c490311a0380c0da80341100c8603a000503044100d05180925070f0030b042e000e03030000301808662640b5002800403407204441d41e00102100c65200b02d40311111159074070303048105c1016100c00d010150042504111f8001e640c0c0c4410320841c0100900c1742c1c0003030a155400350680100303155003010407656042c0440000c021515502c010440100346161000c0805214454001456810344404603 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 545483741 1250 545482491 545482501
    0x5090103050c2a0a021e09151f1403010305071706070906050901210605041a060a0c032304090c0e220902132301031e020607120c1118 59
    0x441c2c1c1e00e000e02c0f40c0701184107030400c040040c1c1d030398410151464000c40071004c4c40c1e075209081004040f0003824524205201c04100c102c96150000d200c1c00c11061180326444403110060100d50741e8045031036018048001000200410001160010840e001c40903400340c4030f400405507546608064804c2004908418010848a802000a400f203200c050611a90400c940606a25201c201400020480b550340a0900035460542b0414624100c940c28800890b207013040814654410f4401100c01d100f00300006404162003405103030b010001021800e1148025100c06140c51b800a0090002840c18651170001141c45803032176529003c801402241d42030316900c05072400350081c600c44810300351500c2e03802000d40c49640e854440d0102c0a4030024217644801c0c60b000c00c081240411852a050100040000c1a0002200c5410103005240801104224400900c1900c54004000d0800b40c010700314032591078104041d03c180c03030700600c640d41100e04060300704030300361002890130f8041944e0380300891 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 545484991 1250 545483741 545483797
    0x20714060f1e2809050f0307020d060506040e0d020105040c06050903032209021602191a03090123070908011104090b0a0801060803030a0e0d17060d1205090103050c 72
    0x1581050b401c0c200d115080c031075220a064100f03000c00c800c5201a841e0400e6008000c0104980000c121044d00a0740c1040d03244d500045da50340c1a941d01610b03c07a250800300d00c0700d5a4a40c800e50440101d4412030300080c0b0501c1d0041d0180c4000c0f10140e46842c040c0f50002540c9005904a410303980c001400703036141045400d2014400c600300034040282c2c450000c008100e1070003d10042c80c10682c03d0700002c0a24905104210145000b181c80b14680e4501010810290884503403440c00c1444c886241c945070f550b6820038500400c0c1030030380340c6000c05410050001c942d0801c0c044034000c00c281d5540078080c1e525052034609070340021103200d041078004c110810120350154003e802c1d10500515400c0080c0d61040c1042c01e4650a8000c20210340000040c0f213801c4c04a0f05c90901030301c20780d8028040714624024040d0201c026510b0b003044041035180055055030f1850700c9030b06440d03400b000b0b01d43c28550b241d90080c1240c1003d0a07043c082494400480d034200410410383e42c280307441c030315112412800420b00b0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 545486241 1250 545484991 545485051
    0x33008070c030c05030a020102040e06040e070e041b0b0a1b020901051905060409020a021b031b040207150605120105010f060e18150406060f0f0305130501020714060f 73
    0xb40c040010202c00384000444c00c0c00204414080d0384d0000d0303141da040c0800e401a141000c1c0007076100b14030708406502d04000100c0d000045521216080007950f417075082c44402d80d0440010701690804210b8040f0311818400003402d90f5840c11350310589004600e580304540c1c2086441c010b544808404010421071604040d038401f0449141d01d51014941d8410204409402035005000d4260300420050406681042014020486071a500700d40200303042c086034462100c000c81c081c440390348158403042615560120740c421a40316403541030400100a40c20018007180c081e0b17910500b080d10f000c10084105004003810784058800111120f4580b4205640000d00c1202c5607821886203da8000922402000d0610030203039211080d408802140c1000121821500700c1030a20418000c40d5080c1d65010840d180c4075001403c00140325114044100f5090100c3e0800421039800003c0c5d24041021812940100d40703110001c0b90840d4880805180c4220b40c219210745080101c5441c581d0b5624101c518 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 545487491 1250 545486241 545486243
    0xc060b090f1914130302300d0209120a020108150a0b1803190510020711041508011802041104120807020a170a03020609030316140904020301033008070c 67
    0xf4030040c103243d40c404891003101c19562201141903010145501481181c854090070311b1643c800a01140b141e00c0000c040f124a080d6243d00400c03020501d0315036504554501b10000c100114200070f03686031070717580c05100c8001c074000303481b14010901e42e000403981120403010040c40300380f44905184252285800550012940080c00c0e845540d054034144010440d607001c683c41c03884a00c815092043c0360800e600c1007190450700c100a00404902e0100011500320000c403804074002c140507001d0210384905802c407080035460400340c0c501b860041c81c0801001882039905110700956061580d8540c09a8400c030704c2d14004a4440c80002503528005140e114402800044c2507902d406400503403a03095011381c0507540c400c1c2401c800f4181c04102060380601d5030b800861552910800c04000f4600e41d134801414014040d6080300312405000964501075030151046450f50f80d20b0401d41c003d100480c0222804403403840780d10440f2086001c042c0c185240c076031a05440c0741c44184007120000c0b0a044 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 545488741 1250 545487491 545487541
    0x604080a0312060e0405032d0301210b070f12020405011407140d27351605180105031e01090b0f070f0908210d0203070c060b090f 57
    0x640132540420b40c180060103240207000641d140c1d01d90001000c2a0040581c002e48912542c10280140d4852030040ba0b05442da480c801413440700f08982c40c40c8881071203441c0102450300304820808196403003500c1a034000c150b1303511344941161004c904c0040b0710035402128000348264603041c241c070989000910800d403040c420f09960182c08000d640c1451041443ca000241908004100701121060803420300c40141e142544407a00d00780c41e0741402601100c0c580148030000e101c2d02e142038900100b40c0d10610080c410b403a0f10703107280b140300c0080e5943c034080d03e440b48401605c60030041d03801c645601c0c140e4070068020808a4160450301400000c550081c440a41d01c0b60380ea0000a00d404410b0340c000c040c00403907074030681000340024010303d01040d1007108000101c542009044000181e40c1094070104103007a410741ca031000c846105208001d4203000040c000002e02c008181d021007010302050150400700f1054201c6030800048100039034034031000c50071b001c1c040341d1107031601e0b0212286101054 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 545489991 1250 545488741 545488751
    0x1e090e030c1005060a091a04050a0f0e0109020102070602070605090105031047040b07050309090906240d02010f051309091a0402060d020d06030212030705010b0604080a0312 76
    0x115500d49401c0041c2c040c000d0b81916141401650b0030301007100005805120707010302c02909102d03888100c4041c1d41510522454540e40803400b00f00217a030000380c07800c852060500042e0342c841c28940c00392500303c00c200c1c0180324602000404a2001c00d020041d40c07074a507141460030035038500440c0d0603000a855005520783c85840090504070740403183e0000c600301c20006105032b0012030f035628000900d04400c0201c103100002c1004c0650b035503089800741d4013075049081d201c004d40e040a500d503000d040d864039000b201e0003041c41060000061101d1041f0710301d0511000d40c080820101807100340300282240c102c0154031054005602407200354100310315904d0700c1400c040b6030b0040300303c0c03001c0980e220400c007654560f01601880488a02c982c0e4165040007584403504040c1c2c081070301d622032040d12202055000c540c15005116940101c0003d50300140000c281d02d52a91805440c2c0d4409141140e441d80781106824490400c0010346040320450005021000d12588090b0b4003070500140300c0001d035983c0c0d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 545491241 1250 545489991 545490007
    0x80d140118050402062b05090d0306170c2101110403121e0c02041401060f09051f18080d030b03100504020918030f1b060a09020f0d0303290a1e090e03 66
    0x10301c940348c800c0950f40010504200045d101800300c1d002504100f0706800d1400c1c00c488044000a2141315042c0d00ba6802c402032610180c1d20054041e1604145415508000041302d03182c03c50310203807080d2400783c01002180c500308102591046080509284640d079070001100c80d4601561009480314005400812400461075900c80d412900340c0005010076240132100f0003640c1d100c00550050b03c01030754040c468180d182d500070315284105032a201080403441103d0100c100047e601c1c030082c404042101d130260045075010300a0640d6014150183c4901600360b2101e04450141c0340c0200c3d009020600d154558103444400101454004401c03407000b0480500c00700b041c400101403201e901e07110b1844642c0300000da242000c001404105c0c540e03090007d00707009a6180d54602c40d081e0390446480440580624080e4041d081101e01ea14002c2d6114558100c0c00751102c2004805103000c9030301400c2240c880c813000c0c1c001915000c0001248003418400d009080b4145e00003d40484881c04481c2424a0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 545492491 1250 545491241 545491327
    0x70302010f05070207152a030207120b07030e0109030c08250506160504240c051e0c01020f030d0e19030c0c0905010302010e0d080d14011805040206 65
    0x206a81910041e48082c0d020860a80900c6c01c4032003241c11803800c82422030664030002c4040303c482455110117490410800f041600030040d45d03008008030044040b26500500f08503490106c1207441c1c0d00846d08064440800c21018464600c034a94161070720071070168292241200c03500041c8800d40721940005a41e03c200803240500810184114024103003031030103075104094001c00c3c2c43d41900780314041c803080c0b0018001d00f480c00306104100c00c00d46480d00d00402c003102d610341120005845030007021820340131740c1c03002c02001024018807400c440c43c003002e00004a95500f420100f403401c5030400d02c031410b13207000990000040000317003804403401840402e0030b25082d001c0309002140461682d4108000b084005401c6800070001000100203030361540e00064003180c04403440c1c5200d040030000c417070200209541964003d848250301000a00c0d4500442c04d40c0101c20302800618100140c002c40c201120741c09101e110382da015008500b007403643c2c12440d40000e040e00349001e8000c0300e001d00070906c03d8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 545493741 1250 545492491 545492501
    0xf060801060302120a0f260d090501240311060403080f1804060f091d0d0e0306160c0f150203070309060b181503030c070303051c050108070506070302010f 68
    0x4450002820320b145204011802610101c04291074020440403804203500201002810390442d124903005200c004c4004240f004071260898400e9010540e01a000c0440d442680001c1c81180204812911400f00100b900714420450000c0b00c100002440003d0b00983c4070f1004050103003480d4141741d141e070798010054002821841c005200030991001d00d040b100c03004020742ca800d403010001a0b0800700703854030905403070007408240f6032a0b1a00c490381d0310801116041440c20601603c5075840000340081c81c00030400d80c003030300c04d224104c041000244814101081c08000c0c0c0c0303034500b03003580e2a9a28101c4405024003076584080c1507400c0c14440d00da900066102e082540e90004e1902228a00b1790100c90302d030755060b8000c100c2d034221030100740e0785d9a2081d138010183c0a001480700043c40c1c0040c2c514820310407603241d6030144031400800c01d40c000d009442e0003595800d05400c69485582c0c001c04a40091007804526444460100b007142070010050031040d010b44004a0200300c80202c81060710 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 545494991 1250 545493741 545493749
    0xc010509030319060e131b06180905131b0315050121050d030b0307050607051605061603080a0b0904050c28030219051008010806180316060f06 63
    0x40c01c0003040100c0003407148840001044809010040c045c14406241ca5100f03005104000c0b0480300d0110105000f09502c1d80d00d604008540083c002c141c0741e0f04001c05581d00da036a148603100040101064001c0705010322407041890f150a01440c2c07840c0c0e00c2d848180c00c80300801120080c0448000300105100e00c60030303261049201c1d00401e0951500300b51440c41450640c24031400030041420800040d8003003069007074003c440c40d000c5858003050b00060300f48a000d83c0310390703448000001d29004005011428803018820303000c3c03019020b84da0303105000403841000600003190010541038000280a0004980c000900c881c000401c803243d0b00100301c1e100c10a40b01641e0f0b07a0720080c4000c4007494005116015045100e442c0d00c032a11414012007082c15841c04000d105140241070950b8a180861080c001084000c2030400d203003403081f0020b03107000428020300e19140141800505201903a05d500000001890f0041d490212403454241000c2c0c00c8200440e020b50315400c9980a980c0c141c01100094 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 545496241 1250 545494991 545494993
    0xb06060c0601150f0c050c040b060405040e060603010507090e130303140a1401140d0803061206190605030d0503041506050a08010609060504051513020c01022b05010e0a02070302030c010509 83
    0x1c0310f04464068050408440d00e04100101c81c20031900286012501d100c45100940300031034104042d4001541074011900a190007501d01080c0b004a0302c030000c0c070030b80202c1c1c0071341c02001152650729040b20200e645018600c0c01c0400c00300403d5001803e500c04004903402803030300252281c0c81e441140d1448409850034500750b5180c90304c54103006c010411031401410b4030806403c1102d030050115a0084d10800041e240944c00300c0014081d031501e446100d10002e4603410358032949010100e001e03440201c440d980c4078461074040c022865040000b03030b1a00c0d4101c00c1c0c83d07950955850f0b0703480d8008981501d800704500707a2941400101512408840d1000e44070310b03400801c0403820308001d002280c890f6446980f0981c205800d1116844071038a40c4211034009840c0840244e001c1c0740d901020f845007001c05000d13588001415000b5160381100540b080300c96400495082d0609005a01901c40c00e004060000b10303c900441c140100d142c3c01010210f04c83c1c01aa8200b0083c00c0d0303017600f151001c84000041d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 545497491 1250 545496241 545496269
    0xc1c0c0b03070f092601060e04140609030702031506030c0d141219050a021f061d160807020f01050405011a03030f040b0928060216120b06060c0601 65
    0x3450350400c9070480f85410900e88640c11602e00704078011070880c00180103403020249080300411100a40250000d0107960a003414a402c062500b541089070100000c105401307040d01046440384040104c4140c00e130020004c01c3c100000031980c0950307120103080164944280e80d1110815241c140e0000009030083c01b4101420484038400b42c103112050440f104401d80401400d03110042d00000150a00481c1c500192500824081070346000c01400380c410414401490207441c084507504004262100c1c00001c0424815001c05403030b006105a071001c7c0b02040c51036240000701e00c2010107a6100c182c501c11200b40f010920807442c2103400558043d00c041e510b40b0840a00d50312040f6024005900540042d80380070140c0b150f004142c0104e00030f45004010008a908155a80200c6404107c1001d00d085110b420b28449120034800e10340b02d144d015000744514a41080b103039190304000c0b1a081e03445524142da440e6100071580b04001c0031107500075000c5c41009607540080101e280030b013681c1d840b2401 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 545498741 1250 545497491 545497501
    0xd110d18030f0c0312090302030f040f031109070e0409080f0a02150603060c04140f041109010f05040506161a0103140c032a010905030303070210050115020c1c0c0b03 73
    0x1004100002d407680603c098880c1c1d00c00020f62082c1c4107000002a56000141184c0c540307030403800c502c111100f0780e00e2207202080103c0c0aa820700a2035080701e120390300c140860140ca82c1809400081155441c01003460301502c161141480e400c00700c0c685204250540c5004800d03d401e0086810120154006a00807402da044034607448000d81d4120750201c000302218a005e030341d800900e104a0040704400da800303030002d22464450030403d02c0700031401401030000320020000300c0c40a8024171030090005240320750007100c071406803013102c0a80c0c1c000f402c000d242100d080b01c1d0b01882104030030300f00c860720b2003046080148145072110b2806544103a2190400a45d03000f9002d1031300360b100105910940000c002030341000e2a080c2610004480800c3d01e201c401c030050016125003605901c83c0b50540000007c100e450f40d400302d5404d0000740f5000c010022a600c9400303104880c1000c80558016900802e0001ca4078501202403140c03903080c03000b20801c510080d5480d005034440540c0080001c0b040841409 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 545499991 1250 545498741 545498747
    0x21902060702132c0106120212070b0f1903050103030f050705070504050a02130915092703030501060f03020f040308070f0f0b0711010504020a14061e0403020103061a0d110d1803 78
    0x12004c50306007000f8400a82012801d210f1540c2e034540081c80341750703418a0005201c105002070300c01406d2984083d500c8060b01c5084030056440b4080e0700c0356502c00f13071f016158810300a01c281030589400d9600d41d00490000c0310151116401194199202d00c1910800201c0359282d0180500c01c0c0106000540c075256080482c50080c0130541144890030f04041c0400c801040130800002100d0070b5400100b0b10824516840121040c01c10302100d110f00944601c3d000c3c960990091412900305603154205000ca182c0d0842c01c81c00380b184000190101000104023003072820014202d094060b003403601800910741d6944681a05213201207540244880400a2050b044106d0407020804000207020750320700350340090390301d04450260303903840c0403014a03860342511070070705807040a00101060740b1400303030480034a0741a8000384422400241058000300e004014020041c000c030b540d08069605144180b22201e01a201c2804580b05294082c002510b904015005188010452042004003407145007001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 545501241 1250 545499991 545500061
    0x30c091908060f19181e031e0507152d060b091c060e01060807050310060b0a110109081206040609020408070501030e16081c02190206070213 62
    0x2032040d200700400c019120141c030703100705003441e0030f401300040404000f0b404c1100f1058012000e44a03512000c00480c821a25500350202280251a45000100001500304209a500041302c0c005801031010b20005004800c1c1c9804141d4420400305400d14800301c1c1410500c09003801c3c0705070114100700c0743e0303003190544201070160074102d40b1645403088070008a120f00044016000c80101d0501e034200c14803c80d944843c00d683c41b00300082c8200d0f40c0c1c910142d541c40585028452090040d1582d00919403110b02c035410032100c41290b00d17800d00704092402d0303070151115851400d66548801c03600f00020b0410000f00007080c0c01e1413981c0780c603090140a00c001c0715401e40011702400e1041000703000c80000066414200c4100346008142c0032000e091803400c2c580b06220b280044030403401d000c64041404100041d00011582251409050f4080c08903519540c4a52003012016014000e00c09420320000070306c0c0450001c1d0004e1016076140380514100c62481304140340401071121701840072144140e41d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 545502491 1250 545501241 545501251
    0x803040c09050621010b06030c04030c08010911010f021906022203020f040c030608060108240f01050906030a050627010501031e0c0e0901021308010507080c030c09190806 75
    0x1c2003120303181800202d45900600507440802e0500e03501c051003c08030035003103084c2000c80503004035203a00308804100c801d038205010490710a483c544011400e180148607888000e90132075081900d0400200055488203100c00482c030440c01140306c1854104242c040250100707108081c01a03940041042d4059252084480130900242101040000d40e03244280711040c0c1808650010301c0c02d0820070281c00808155000020900075280002002c020104550114071380c00440f12a4138001a0290758800394100d500c5610401444010302c03030313070a00041082d840980a021034501e072150752101c41c070b090422103030129000740141c020790754489000e5030541d1050040d0300a1005504540d03804001c05e9103020100c80c60304043c03040d8428000c0000c0e010b402013034041901101428113240d090b001c0e51020912000c40d184003e00012080c00c1485400c3c895105696a0002e03070b1900030040f002e40c6e00161800c01c0f104401e2003a2000ca0740c1d411603843c8070740c09c00000303105120f1405244074203004005103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 545503597 1106 545502491 545502509
    0x61b06150618080a03050d020c01140106020d030e0c04020d0605060301030602031e07050d0b030f160f060525150c0e120102040b0f09040e0303040803040c 68
    0x1000c405442059466080140300c1808540445440e40309040240d806001034070007003482100602402d030b02441001d032811880c0580c2e20300b9241c2001c0000c00442244004021180c0c04000300b0005000701e050502c5001041010b9070785841a030001d081c040d580006d18081043c0f0294401e80c09000f0040c8100c1e182d58403420080c001b50030484442d0500300214132403901d1000313803100144c03291070b42c4d545491800040c1070803180503191aa1081c1e030503204100c1c0030304005c01c041c00300044818254045038031251401811046c1004c4560081091100c00c01804d440740c00c102000f50a0300b01c0c100060f2643d83c0780c6151061504d00c030a00a106c100d441c14584d1045168880400c0c810713020201c40b003804500402400c01c2c202c4c07041c0d104a8041400c01c01c400c0301d150b86050b0140c0700448008000044000c1d00d40f40c3c140c1141e1007210100c45441000042008100300e02420b4030103080030342 = true := by decide +kernel

theorem cover : BRFrame.Cov 545323741 545503597 := by
  have h0 := BRFrame.cov_init 545323741
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545323741 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 545323741 ≤ n) (h2 : n < 545503597) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
