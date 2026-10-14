-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1537
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:27:37.051662+00:00
-- url     : https://prove2.me/submissions/3c971b10-19cf-48b5-8154-6fc992b0e9cb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 276258992 ≤ n < 276438848 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 276260242 1250 276258992 276259019
    0x60e071418040c090321170702010608160503010b040b101101090209040f02151c0908130b180913030804051e030409110909040201030b0a12080d11030c160c1509 71
    0x310224400c012080d60b01c41d00580c00147c81e1141d0280d0030541d50320000c0490040c4503d501900c16481107113820344015107540c03071003815070b24180d00910402100c070090206842e4120081a0071144040c80480722601c6020000000802d0b040049801c000c1c580001e112040251000d482d905a85141e00701146040103075840c03400303004500c007801c00030400c00d1112121000303207540700c0361501d948418040004207000c4902c0b42c14400b41c46041c103910313151481001e401901d030341421078650900205d0b0700c0c5000081030b803040301e6500189804140c2a6804c5482c131402a00c102d440740704007000da208070130196030407800080c0510011501e9901e0407000c402541c00540d0481046075041280c0c1c8100d071a076400c0164801e0f02820082031081d240c0c008618003440b258007000000d03101d00c403980100009a070041052506001c0284541008441c0520301880300b0307034060240c200104407004000028101000c0304078060044000310035600c0c080513403903100a0080701c0000780c2c03910b01400421103030401c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 276261492 1250 276260242 276260273
    0x20031302150c21070b060a090911010207050a0506070206090a0e04030f0e01080f06010807020f1204140405161112030a140108071406070507090c0c06060e071418040c0903 75
    0x3c0c00d52080d543c025865102d01c2413200c050102d9241d003000036826254a059074001b00030b0194100100c00682c00c012140d02d034070402590050080074400102031401c14110000d503000188064035180082e4200308a13903000c040b401d6000080203900151811442500b10b1080e802030712844c1c020714440320010401c24200034428144961074060101c605605080c0710751000c020700300084203850303580b0140e140c01010a81c6030290310a05010700c0f103014040c0e0241c411200e04404001c0308233030103c02c000a81d041101d20008403d291051881d20030b1146128066032203415003500d000c003240a402e40b2860340308840c20000641c07108400a082140107210034018007030040a089030605080c2c0b840080b00f2903012040c4138140104080b0140b240c01c0c485800140711602c01048803c0b003100d806000e07400c0856094401c140382c100006161690588074a00c2142196540045108548083e402e84d412000b00342014580c220504001d41d2501c1c45844014a0030762590f03054540380d07240c803a885c26802c01 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 276262742 1250 276261492 276261523
    0xc050c010605180a051b1801080901020703080c03130804090b0f0f030c0d0809030f0a020114121603020d05040c09110f030c0306030f070905071220031302150c 70
    0x81402483c0d25820750094011010540114003500da6203c803640360401002e520b02c42da800010300745845107640b407066200450030b80310316030180d43e1404201d00304c1c0107014001d4007007a000c4001410090110700190350041c01e61034502c040c0d0319192628080e94109421070800c041c1c0d01d40da0308049107414140188903500403203903c903a1b0315142020030386402808003401e01944040070003c0c2081203440a44441280c00707000c49110242c803c42c044d40e110000304003a804a80768039011400001d0b460200ca908511003080c107015511a07041580307008584801a500701f42d82402120f45960711070180b1070140303014041a0080038144040d0b40e007203c10399081c0c070305000c8007005500c4e110181001503d074003186c060104d42d2243c4d10b1a001c2401c0c03e501e88107002450155007004907030120140e1046000c0c544540d19411f4981a20700d25078100d4481303c8c0e0910071860080d40d0f400414058000039907000d1425190a4845081c03079002c00c200036021038200c81d1030480480d16031031f409020040700c4111203188 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 276263992 1250 276262742 276262759
    0x131203050f0c070c1401050c030d0506011103120601140c03030906090d0203160f0c050a090228081801061e0305150c0301030b100b07080901030b0306011d09100c050c010605 76
    0x1380d0350b0088450342403040824089a05882c141d19a003e042074415541c2201c0c2500c3d69031000030004001408200c40050108008501c00c00101c080001034030004003600441780020f86030400191624000d2882143e44c0e00702c20400040e0aa00030700c042c5005041c4040108010b0801400700c0d420b041e5103820900c215442403080020304210111088416170b007200c24006d03135480d5802d040c3e0030012650400e40e00701d0101100020041590f600038986013a042900c031842800880f02e0042241000c0d900d40f000803600e90108008500a1413860040c02140d0000a03409560310108402d6440c180000c04e02c1e615919010001d0100c01c1c0143d5400e041d40e01d1b1824043e05d04200100040d01060102a014040c4034002400c0b200c03802c90540c0251428500e03050302c400c290324008280744d0100c0315031800203081072940910d9040000e020341c1a1810386062003d1004004e2068141400041814101c0e10480e441820b0141313080c801c1070314a0000d50749440e9160280020a0f0944030700394046030140d00341 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 276265242 1250 276263992 276264007
    0x313060902101121160c05040c0c20010509010e130c0e01080a0e0d050a111204050f0a080c040b0118081510030201120b040902091f0614070209131203050f0c 69
    0x184d000c075042030180c000c0e03400420000c2c0c203010500a1150b000711ba046441c00c140300c00300f80d401c8500d0022040c820410040080d224010f0f8072035040003450064041842440050829030140840d210f9100018003081c400500807444001900c0c1103014403c040348040d69100184d580c025031855010b00c11140c24019802c6401c01651303945241000142049004515407030400d00c84e0802120744010441203a0100305c1da42107810956020b0712030640f08445a01019946040c280111002c850502003e01000c58070741c010b100242040c0031120b0304000003617501000c54841046028040c1c00d41800074042400c2c10341030085c038100054044070002000190410050381e010880c201d44044003d00030810f071000001103009099150002581f00c03104c00200001c1c1c0c00c46440c007803c1c50321000c00f042c00342d60381c0c2d01c000e940c04881c4588031010307218200216005400e041074900e80051100300d032007441c42e40544840090380303104038a4a0001c1d40b41c4050164130100c4aa0207a0000c4d03108805503d8200c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 276266492 1250 276265242 276265303
    0x10b0306091903050f0a031e050708010b0c01410906041b151110020708160212030705010203010e1806070806040e070915091103130609021011 63
    0x2d52042050720126079071042010144100c0654904400c00005140c03510f007a1440034001d030441208070b041d1003030b1016098080042038040c550084950740c1f01c441c016400d10070020025801007007070941d25900c8451030714010b0303030009074040580200000c000b0035605001d1040e8103c08400c0700051150030a0080c04507601e004102c0707a411651054901c04590f83c685a051062651648000d48050035004003805064202c8500b1110130782100a44081e0280c00c600c820807800b4284001e0072204041c8140c0103405114000d000f03140f17000416600f00c107070010499030310716400100100c8240e500803004112080701c41704030503004081c425103900c00d59004c540a990b1400002c00300c1040140030303000304410b9211980074072400741c1703036406a500c2151030b0b846d084042d05a440c10581441e90066001800406510074048202d0207c1000ea155485004a0800001c2400015181e050f07a0304008401a40c440070056000d20312074440e5410118040d42d281e040c00c11202c011844025600f1424481e440c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 276267742 1250 276266492 276266503
    0x1e0905090c281214010c0203040f140a05030601060c1104050c12040303110c150624070510140103060509010e030d0e07050a0b190309020f0904020105091f02010b030609 74
    0x8040c40721108900d914100d103881c2c203541e40c4003040f201c024100c0a801d0000300244481d0b02002000240140e1807444022070b039038070070752164103405044180c05106400e403003801c4158070407004103820044c0703455070f0000341081020381c00034020031301804101c0e0804c040708850100101d4111810021490442c0d440345651140d020b5825019940400041c00c241c0294041d00700c41c010102503989648504100341ea80304d00141c1000701c2e060a0200252461411241c80c00055001071004002144c00b0311400c8483c2d0401841100c0c0703801350f085542e0814803548203803040b060340842040d03600c0d45107040800484d400640010201d03410451803001342c9800208403070001c41c2507440002c4c01d40c10640c500341003a06a40085610000c1c00c2c5000481c010b400003d07225003c040f801c507560460000c1410b40840d448082c0083d0409030400c45a421417030100c071b00b5a442401810710b98a884417030000501c1e20740c501c1d007454a000b40d659608030030079582403040c810341003010360040126003409580e0030344d40ca = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 276268992 1250 276267742 276267769
    0x5060c010e01151e06170c0c1203061207080a0204020c1c0201020910031521140a0b01080708120a030f0e0105010303270b030406090203070f03020f150a030c03061e0905090c 76
    0xb41501000c1003d0401c07c1c403c880c440d004120a49801090240284a0b02c2e40b06481661103641e90342d62401a0780008600d42048a5001d0010910b00d2003650a001c0650003040f644803150203005040c6062604110034036600409a6000683c1c07107040400700506011007406030f6041500d480501c0b2070003c40302d11800d00b581d19588401c00400c03d07404102c0c26100c0c820b0802048081844c100c4d401901c400516120460b04c81c2d0400c41542c2c1e20307800700c0750391009180704140031584145204191011a64002d1041000728500800d00140104905040c2c0f0791041a00c8010381d56000100241544400f81004910725511104070383c003041019952a1111401104244c00000002c9800c220340b5030710034101c441d800313400e440a841c0d9412081d10826501c0c03205902a800100805019207450390350741e5000a0200e0312142030000c203505c12001808110400340c2403698a02000c00c0c0d043c0502e00081c03a80000b9062049580e0511080704261100a400500d9540c481c4008900c40c0d07450f6580300440 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 276270242 1250 276268992 276269027
    0x190b100e0a050303071103010509030c03033108071a06060703110a0c120308130218060102070503011a040e01061217040506040b04050118060905060c010e01151e06 72
    0x41012a0000070341c0300d9241c1c1e01c0607916100026446040100348448030301200d004600170805030b503e0b50703000b40d140d103d8411009059001000040c01241007251807844900401d8139031300c079600c0c55031000ea030a12228082510981d2012440e00e0030400710300c0014500c00c1c4480100310040c1059008506103004000008047c00a040441400e0300002c01803d0308190b080041074865a60b140d058101c061004042035002540580002d91940500c050140714980d016010b42c0c440c0040701e807081500d42d00a08482e04602401900040c4c6503402d00422035068404045082c0d4202c00700100030407030700c01c21600791040c2d0402a0800085d28200291540e041d003000440550300a074041d552182e105982025a01580104020885a40d020b016106961007a00c0b0762403420b00090000c0d0304810313a0310542c80017500708001880030703080550107080310300000000440c2c2c00a201d000c072429901c004036160840718601500708030a14040210041c0385004400c07000d240350504100408854013641d120b030a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 276271492 1250 276270242 276270257
    0xe0102070504020f09060a050405151201050609011b08090109050d150b0d0c121e021302250b070e0a060228060f0f050a0b0607060c051e03190b10 64
    0x1307a215130700e4104d40203500c0c000e050a07900c0a210502800ca0340190040b103002d4500060710011012b01ca000711200d10b90304401c00c21603a0b00e1305003003000741d9000c1c0324031904000f60000542e500d40f01100510302d1440c454540161a080c12600041841c1c1c2241d22007449a0910417411000c26902a42101005140d403c04207036940d2050200b400014185c10062250305810400298041716019028007240705410618411014040c101002503407220040e6214000017800d0f4440300d461350080003d6150800040e41404500840c1c0071405404542503d4000300c400410080701d0340308000e0000c4007004c82d001003109081400007551500440c003c146000115400c0840f4480000441e4048035880030050000b003002c0300b02c01c005400f65405283c81a8181800300c4c441205a00403424a007901401d542d050100e2a1a00005000294666000d108040041400d04295103402480d00c402d1030501c540c1e00c0c1803d95003482c0082001111400041c64890800d005a0700c29242a01e8880e00741b03088030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 276272742 1250 276271492 276271507
    0x9040611030a06030302060606031501030504020f060f0301260a0f0206120a020a0f0302160230070e06040612031206170703023f070308030a020d05070e010207050402 73
    0x5000388440d0820410300c580200421000000c03541100c001c0d40c1c800c1e0b083d1406a01d80006000f85404159508215240c00590241c01544668031950b4490b00040a02a4400e00c07600403400030351041d0380c1460340c510008014440c1d4192039044600c1004e81110080782019003814094403010660002801141030018031010341d990032098500c4600442024240e6080c45034941c40254854602200491002072034120003901a00c251194180e0055442d6074254099007005401408004680d100141d0317040240d0301c01c52000a420780102002004207011814200e0b18003218000900e45440382d0f04000c401d004c840c0081080340f21440e490b00301042c0012001e80c55070050309803504031310006500f0341036030304c400100000d40d041102d0080d501200304050060940440004076118448601d0341c40e03c200740300d0205250b01c151040380d12000d86010588a0342e0385072255105a500019503a00454441d0320002d0700d20071181c0044260602c401c490011000207920f4540d04d01c0b54074402d550208444 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 276273992 1250 276272742 276272753
    0x9050f060712050c01051006030c08060303190903080708041e03020609010815030609010b0a05010206012103090b04060e0a1212110106032429040c030219080406050907140904 77
    0x2508051813110081c06280b402d500d0380f01903481c16116600c0000c1c1440c1030f218401d8040d8107501e0280001601440c40c0000c0ca40da00788100c1158418641049a50140000810a128068080c030340c40340b00d00075911032410401c60382d11f20200140660042caa040704100580c0d44070b0480e50150028205084155a111440c400d04207038a48803a8041c0030707032403c0064045047d4010180c20b03c0848880701015202c80049039203010074001c1184007140311801c0c40b40d000c1100c5500104510030700d840242c0580703444003003e003a00b103035100d2401b0410312a00c4020a240c80c0c08841b01418100c20700c1e1200c066691501000c22a40070b41003001e00080200400542c03100303400590145800501d41c0d00e00c0c400409905c01c0c5003030f58043c4803860030700e450048500345c9841039415411048288202e6155103c11040000620312100311405056080000c840c0c000355803202c0441d0034506031500600e903e81070904000303071000101030030420380200c541800602001205840b40c00c0054903180d0310382d07486140c038 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 276275242 1250 276273992 276273997
    0x83106230304050a051207080702040b060c0304030b010f0b07051507030f0608100b0306011d0a15090e070602060106020706180f03051e0a0b0a0c090b03010b07020109050f06071205 79
    0xc10204040c004100000c0c0000000c00140b501d1082c0100d03041c62244065a03000c0e40038562004019000800501001d491303d038100400044c8000c02c1507140c1030100312003918551081d0b20484042c0c604000401c0b240100c0c03203141000380040140903107040c12607542c5e25212001b03014000002103c0c0c00100e10503900c81c5d4840400d84d09008030800003d510f40f4540fa90321003062611404081c1490310f5244281004035641e81240ca124001150180284807401a00c0c100200076625242c3d640400790000001c0c052180004e041302c0400081400f04030b0420760401c4919040201907600c5400100652540020300c0c3c811100b04d03141500d244401d1580780d00c502c016643c0840caa807a94400044107000010650502c010284074202d07840190751160b0607211800b40310050614a842c40001d14a840d458112403203103401407404a80c0c558942c0d601c0c1e0342035003082e0410085400040b07800021543c025400700d028041c02c031240c03c0203205040c00115280b007004402400b040c00c00142c40b0445004800303 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 276276492 1250 276275242 276275297
    0x3030135030c1015050d02061c090f020310110912030f070b1e04030507060507050c010603110103150503030d0e1216230c0f0a12083106 60
    0xa40b9640d020401d0000d40d10309500c1c0004040510304001c110909540310714020440790b025104c004074a920f0b408000301d980060546404c424440386d10300c110b80c1c59500c03445034603a2081040b4070a21885e401418607241144200fa01154034080000054240038400da80d041c0c0400c441aa151018294991b4210b0148011000c0c202c440450003100304407840c400c07a44100790b02c41c100c1501208024402c0c00d6203606513009004554200005d601003120741c0c00041c0c2c461281c1c10454a4100300190072030845d400c940c010350303400340c400c03481614030340c4e05000f010540008010040c03225400c007030009440b84a000071038003d0603947e64003c0110b020601ca541480c0e0301c2d520310f554413109180b041ca13068044140c0100c40d84078001c100e54a2142400080341102d00144006041555900c000e00107200c01d045402940407040001c0000c2d8201100e0000c104184074218054844207407240310141c2d000c96850b81620310f0440d2003010340c01000200c4c00c2c021220903150400d41d80142400b601e520402096 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 276277742 1250 276276492 276276599
    0x4080604120305161d04020714010515060a0e1306031a0103051002030c031302040e01060b0c01050a060501120c030b06040303170f10090f020c240108030301 69
    0x8100810310480e00049070742403029890902c0b959489682a020301c00c40c000110f0085003540d6201ca04542000582e9100100050001850f00c002c0d501c1e020849118500c01040781ea44400400220060344013001d204840144e0f0201c2c00c0c108400f002411140c4640c1c000c900440c0c0102c0101615403054028800464110381d6400e022840d40b0801c5160304000d0001f61050302c51035400707001228203842201d04ca4107034600c0460031501e40c80d40d54625400841010b9074480d480d0f02d0094000340c820711400c80280900928540e640609000b890309546006203050003044c6001c1c000c00c4180d8001054040700f0f044800009024894160140c005000100d01c03290080c0c400704022041581010080c40d000f840c15141d0078080d070b42c100342c20814240440d220403000001400400101c2c10a80150b5000c140500016081810100409290401c1c02e000910410703049009a811000400c02150141c80340c0f07009185190b0409056548400c04000442201171055913011008903468102d03100107508034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 276278992 1250 276277742 276277753
    0x91504031710210201020703060e070e010b0a08040201080c0409060b0339090d06090615090b030303040828030221160503040807060203090703120e010e0f060408 71
    0x3420014400ca07811000d6220040c0c010001c40c1c4106510b0207001c085543c0741c840c04507a6103145030300d00a0070300300840482c19445100c40201c0020014091040015808802015002c5c80c0c03501c0c0c00035420040c0d1240c1e144d130740301300b00001c80c455100c4002075000c2d030282011982d40e240d008400b05540310b140d200c44c0300d60740f0b0310601041c2c0305010344c011800344c00e16078055401c006090380000c180301001c0c540c0d1f10018801424008000c00e00c007000d031844c135100414041c0003403030036221903042d00c0040c2d400b2100c00d59249004a8600d60340100c620107025800410003070300d92030f0804603949100191002d8809030b0080343c0c41c000d42504003900c801e800d072211524240070400d00710140c060342007407510454070300c46088a0040115890300051103040294800c2101902d083d00581d0366601c05041a40c2240c020400c04001c0360641c0011030103446800d0080101c9440c504040310ad55881030341d420204042a0b00040da10382c1d000810440d805011101d40003480a23540000f640d500c5554405581ea0085 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 276280242 1250 276278992 276279001
    0xc180b0901030b0603071e05210907060c050703080313081215041406060304170c0a03030b2d0109050d06020903011d1002031003080c0a02011805030a030302030915 72
    0x54203640da03003a20b0501424165600704085400103c546800055558140b9151602d8004c000c42104000d41481480c00c0444407001302c60058810344e03105488000800d10030035070020010000200300500d41802c0307030005030b070f500c0f91100b01900c0040c0c644000840401c04900310300e0510240b842d4030400302d0f640c031000a01c09262103002164114076510310300080032201d0400b0301680c02590b0fa9078607c6415a9144010881150406031080e034034400504980981d21038400b0041c28400b120100600c03883d00b06203001800d9902c04c00d00c2034000c580c100e103140001c80d60000403103050542001031312664800313000100d407611101c0d031105901c44c01600d40f40b0b09100050b03004011184084e0b00134002e000c1c950038070903010181c8804c0850399510a040800160760140d0117190408662184228000d80d01e440e5644660460420744c80e0680000d2003120456811410260000050000c940540392519000030b446409c1351701c002d8241500040007500e080014090300c082691341c004601c146090 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 276281492 1250 276280242 276280259
    0xd05042112060902090f010c06060305060c1b070e06010c14030d020d05130b06130b15030a1401030206040501030207051203090a1203110711030a0212280f03030c18 72
    0x200740c0541d0380e032803500401059000150003241c9160a015100540864a100045504c03604503d801d90b503265aa4a002c800940c040c892035000e180c00001031501d81040c00c01d41541c0300050885452554020b1000300710f07603048046460380c03207102420f01d90460807441c2000c5001000266409049000c005180c0c5800340c400da001d002081043c00c0e0400c510343e120101101580356034440906080c142400046052a060f00e4107520035000580105002c0e0444000c5602500f0b9840a034065110100c00c00c440074805119030704203030b54440c808821039407464001c61103621482c01814100f540000300f090034404100401c0b4015258070600340e43d01d16240345215200d2414440484004d200550340c0c014036846401003420b0010002d00c060720b00311071a901e00c0d4107080000243d03a018050b102d04003000da900c1210304620032942d000a0581d00031400d04e010f00d08002c1707883c108441c102090020000c03c2420001c003c0690745801c00140204165800750f8810074040310320b205220004401090501 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 276282742 1250 276281492 276281507
    0x90c1b0105090d03060305060609060307030804120201080603010b10030507051b0c18072705190501081303140307090305120c010c110c0904060e032a030f0d050421 72
    0x2d0701001616824080c0880881c190342032480f014046600002c0429000e2503c001000e4200c107005084641459482d0737100700064100f903202160030046000c21009550300940d10341e500080071802009440d0f51040040d8401070549591410141d44000180006015108560348000c0400007080809604498666036100801c2d40c3c0e0700800410301c0100264200300c8110340101c2c01502c0b400100b1860400d03200143c04199040e44c00c00c901010000f60b251260000224001d00310300803d4062802c14001500c0c2d4074000c5d0801a440d01081c9000012035400351103161180c45851a082e62919045c408407002c2c1c0d41e98002500078005c2c0c84450140b004440d0041001d0803161009000d13404224a0644100700898070519060b00001c0a0118500c2c010700c80d10750040c0302d80740001c2c1000c045010546542c10000046000980c0401064010543c5078280344111081900861601d05041440003060142c56100c45110b500c1c2d030082802c200703070b007001e0465991280744030003042c01d540759009150300b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 276283992 1250 276282742 276282751
    0x402161103030c0708160623090d080a1706061611030c03030c07030501060506091011101107030207151e1b0b06010305100303300501030506070f03050411090c1b0105 73
    0x18000840e00040a90090000384516402c01003007040251003a005e68400e94401c9882540c031045a80716100041c50b902d02a0070551410303541c200c900034801010f2102c2e038001403b8a0310450f018002c004903008087d5440103295400011440a83c00040c00719180c41e090020141d4036000c082043c42c0c1351440022000d00700c03409132009003d990791361014454188945503540f6080345080e40c08101c0c40d0b020300d10114000480c41c0840e690b03810b45940c83c4080341c2c4030003180c202c544e1001403048141681005440081c00310102280200c0c0c1c910380c00a070100d40380420b000d410a0030301020100350340c012009000c42c4001007002010500c80c1d403030203400f101d8085a50f80d020914290200b00c0110b05a8070310015641d1580780c103640c00700d450424a0106240144031461400c0046943d4201285030190314020741c41071000b0f140e9401d0601025100a000202003000c051901c801c00010420100e98207003401d50680d0081c0103a1910040c6403001c1c03084288807803024050100066007a01c055202d148503 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 276285242 1250 276283992 276284023
    0xf06090e061006031a010309051c05090a0801060e040215120c04030c0b03040c17210a02010506011b230d021501091109061303020a08010c0e0402161103030c0708 71
    0xb10b5840c1d850075422030f408044900740321082e9070703500c00855000e540f0445680e8000c0080b107090084480070700388100c00c2da085090019070301088050540c100b50722008094103100b402800300c03c0c01c3c415480d0750030368000e0010307105000f5142d8400d54001c4402c00c5a5401c000031078448620b203090312000c1c816601c24401203032440c1208100081c4d918076503050713a00a0354401c0044100d41c2c42c0ca42d0103080403402c01910441070107000302903c42d005414416070b4086803119040350f100d0302c0142005c0c0c219a0700504440c184004048944012003405482808140d4000b421b0108060710701d84100410025065480c5144652600e01071071503000a015142c0c000d4400c09040240e885101c01015a000440030700740c0701d031090041d0384c40344c60601c01610b200e04000035810400ca03a01e800142081106070f119031000e035950b110901c03041d5407044500c40c1c841001c0c0c42c2945004040996841d5800d646003025140b1181424520081d40c4c0900886500b036280104660603981c82e41005c3e9252004403100031807 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 276286492 1250 276285242 276285271
    0xc180d020109050d060e0d0e0108070e1c03230a1e0513030602090a090c05090d1502070b0129030105090a1508011e1b0507030207090f0506010f02120d0f06090e06 71
    0x56092080510f061a000180d561540b075031660103054410703300b000141c59002c06035040020116824075250fa0600e03001743c0e228041e031541c4d0040350301c0c2a0100d180150240c04108041d06207150051000ca2052005611030307440039920403412142c90041005160352800c011300e000080c010305070081d10440c03d048505039800c40c1e848840e03104a41a85030501c000c07410901c81c0d109549001e407401c00b00c46001c1c0f851201000b01d91040901281d010060803600700b00c281c401404820b9019004906141014030081c000c00c3c00040070203a240014800c0703504c11200e8100040c00002940c00c01140101c8224907012000e07104c1000501900c080000000200c440e45a6405c0010b01ca000308600c1c01302003a805e040c0f0822a003000c42d46030340a11015000e42c881c40d03a0010345a803440c821200755009032800050641400c1e00018848010954800110b50140c1c030003c14441d95a011103084401c1102d00007041d81c4038014030301c003509440c1c0c03007803c80b245098000307420404c0100d00c240c4124200424002d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 276287742 1250 276286492 276286513
    0x40e07080d0807170a1a0306010e0a020a0201020906070b01060807020607120e19080903010c0503011a070311100902090f0403120518151503070b0409020d0b040c02150c180d020109050d060e 83
    0x43d0f507592300740300706010007500d00d000ca40d081c00e50b9802440329500c0c92002500c0c107410030b40032403420b0f404410111000652400100800780c0d02012141e040446403000d00000c4c1060341c2e0080c1501c0c580310100d01c4540ea01d45011604140c04c1200d010060036107144182c400e0072906241140ba08544c00c4c4600950902021901c40c92003138040704d0603110040f403090744600d02c90082d5515900001021410301550464000d1011410442c001982801240c04520b5030414814084103039800f400a160400740700b0700340b00001340c0002c1c1024903408000303000542c941c2d90181079100091907000b550102d01466401107a04441c0010b034500c01d00200e10400c100e12a50000d00d83d842d0f030981720300e0407402001d1009000382c035041d400400004442c0c840c04904001b0050004044400b24910440940e20a035500c40380c03483c2d0155611b0348103c42c2c0240c2410000c0e0440c018001d81621240d040c420145004002c003168003416025010b801c000d42075980c030100340e02d01072006221a184c0d94034988121100c91 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 276288992 1250 276287742 276287749
    0xa05100210050a020c1b0d080403080d180b16200f011a03030a0311040b030108060f06011d010e0a0306020301080a0c080106032003010f0f0b040e07080d0807170a1a 72
    0x5c400d000d034414003c208900d424035410080c4982201840d5014500f03920540216410b08043c002644c010b041565594503050382c084100c6600210040b12001612842c10100b0840d085242d0701508200445c41107220f040c41c220f840c00e142c1d09501c01e051604003d0f01d05007580000346042d000107400020441040c1140e00d0101070070081300d28580c10350040150000c090b21a07013110102c54007030344001b810f1a88800025400750000d8004007200da10a900300700001d04043c03036168000c0e5080c24120f040c40402c4280409868880b031540d811711400300c8002c5840d80320401104010b642005046442e540c5400046840d180d005005450300e8101c608007003440001841500300300c0f036004050004120180e80d05060051101c0d942c15459562004140c40f0300c50719000300100c850580c0c01c000354204041d8200700c102c0d6080d80040d00d141c3d202d04024000d24100090b8055003040d0303800c14040c203a0380d101040b9074454074520640808c0c185a0207101c4d6894180d0031841902d034901c071810b503a008014090 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 276290242 1250 276288992 276288997
    0x19020609070305031b0c0301060611010c0e030c012304030308072c0906030a0f060b2d0603060d050106080c15090a050f011403011707120515060a05100210050a02 71
    0x190080d002000801110720682410171203400c1c1203c1a900c0c003d0355840003e084411543c0098040b130400d50441100000070320131003040313080c18200280a0120200441e40d188110136101d414004202d110f042130030410820343c10f500100451490303480303840e498001d01c20708043c0c4030710700850390f280c1080350307000070040c020465610038080117416414000d04100d10b00c00c0c0604800d406014100318040072480090500c8902401000041540710b550740c01d0013000451340000c00c00103d1003950302030429400344080140003d08488258503500c1d1240010080c003000c140041c1a5880c000d40007400c07004c0465207203070044088640c20442c211a100c0d0b20710520a1030708040d8440c1c0f4040062001e490041a4824840320625000c00d02114003113400505a0080e0040a0f02c5511010703a80107950342005142e0180000600f41c10700e820f81075440e9a660031020451900c00d400c501c0c0020810346039240800010a802800003040c0700c030564001e900c0b850090120803406040400065042000e03008 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 276291492 1250 276290242 276290249
    0x12020f0303041b03050303070908070f050108152106060102010b0f0102190c0f0b04050a06020a0206070b06060f0f030604061707030b0c130f1404060f0b0306151902060907 75
    0xa9480c40d41c907a51403450302143d000c8404840c48a0410100c04500c1c00c1014612803045e54940f400300500740524540b8140c02a48081c1c40e00345503c000b0300003a6401007030b249e0082c0c550403224520740040400143d0383c0195110300039880040106ca51724511000039080c0c0105002c1e002080600002e01c1842403010880f6101f17800341e40914400d0b4031250181c1c0149071641c0c00b95098441441d12494155440b095561180d0000c50000c90140641e2034080f0151009001a00003490a240b0342d50210b8030b140260391010300003907203c0000070241c1d100d40e000c6490103002e514240da990710400400120b03641041d41c10350f0145281a002103544201d0745103600b10554607034010301c24503203940d03a10303007000400400c0074070320074014403000003070b80c1500f5a6240609021150540400e007002005015a815040094032403401e200041051203c00e030310303403000d84100e00c2c074103a42c2c0e0f9103040118150b00715402004045040001e03501414588081c0c0c2e05004191a80c252000c98585007440344d034070300d190b00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 276292742 1250 276291492 276291523
    0x1802030f0c2a210309060105240a05071506081c1e02060106260c0703022e060501022b0c051507030b0102010524061c02071202 56
    0xc0740100445601600740700c4185581c05111040080c14041011220302c1c0840799070380300703c100f08221850001200040d01d00c0c020400c0c1546802038620344d50300010711540d40141002d11121046120003281c03000045046602c49075510f50401000303055501244c025071301d1400c03018884500050034080c00e01282c46080040c0074003000040181c0c4825070b581c841006100041305200e041544c440d80f081d02c2205540c010b8083c1c0d40c90004081c1201d9285104219461141c03041c800351001c1200741541c02202c0340f40c26503129003007490300360b2400312000003606c6004000c030030441720003070b02c0c0c4801201480c0c2d0f000240410b036a00c0300160380d9001c2c80031610f02583c115030918900c60262041290031034a4500c3c001020781e5454076224101181000722103561031500007001031154050007906100750b803c2c80200401e00d05040c5000580400d000d01c003418400002c2c00318103555943c0255001101811000c0c01019045aa17480003036014100407120340b001c00440c64800c50020132500c00031201ca1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 276293992 1250 276292742 276292771
    0xd0801090506040f0906051f030f0f03052104020114130902070f020a080c1e0603040311120a1e03050c03011a07120c02092d090a0602070c180203 64
    0x80328a029000c02841243c0060341ca1641115102c000d002c0c4030030a034014100000d403818003800b0b10a2401d03030b58651285110301c41d08c0403c0007884030000650000d82244480b820801c15140840b030701e105440100e8810030201d03010300f001140c001c4100d03010300d100342c0320388003151010742c2050341d980030b08402c12000340558601000302111a0b00180007140c41201c0d0441c44000b1540002c540004a40190210360b20510038030303942d030500480031001c140a50110712039005024000400522006000030100070000c8030f49021440c04200158800c074410f0300164035451200c0c0028160b60340e600040080c09200541642d0890080c40340a00a600b0701009524582c280481508401e451100205014804008810100340103c091006008c12a40d0300804101c203030040040d510f1001e00307407104003088141006012454a000c0c4002010200503c00d5207130398803a005030400c7e0094001038085400040d024080028043d006001d4031082030300030b590303400d2042c01c404c201d0000300c4552240c164038 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 276295242 1250 276293992 276293999
    0x1d040c0906030905010b0415090605061305042316090b1620030a06050a0c0e01020c190806010b1c0b030304121b091a0306150d1b030b010e090d0801 65
    0x10f0707007003d002c05020710f0010032064a410040790403a03900c6001805041d0b189241403001c0c0c00c440c02100000c210498509007490703069000520018001d2151511803552204589101d40c41c08551810030a61a09140060f140c07001d11308240d16021486040000c044001c00300742102d40e54161040f04d80f1980058860319826074034010743d1209040a0b9000c0500e04001c00381c680ea040000b048024070640e000300d00e43c244030031b0304815554051102d0013449920040030384a0b90f4001080c3c0322900c4100c0b680388100c40c110080d07001c8040d69412a0038030b40034100c00460040024401401a141181c0d201014032841c01d55120031207181684041d4960010481044508202060704007414024a030411a521200b030200300c0b0365050350f200d502d801d611015002c0c22000031807620490100258042c1c0b08500c1c2065030400401c40311f0500c20b201c1c5000d0340c035080a00001d4540504c0107085c02c81905001034580c180200071050911a115403410f81100240040c41c01081c1c0c182a048607883d0040207908 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 276296492 1250 276295242 276295247
    0x108011211150d020a030c1b240e1606090303090b07080913150602010603240e03070308040506070f0206150310140121050d110c101d040c0906 63
    0x11485829840b0140c0549014803510502c02040300291481c801640d40c0b0001101400344c0c2c081c40381c5c1005101d00072482800030500c55250340030444d4052007111a03110078203030308818502d00401200020b0305d80030001030803220014090000c02d55a0403120040c99840904845d0340031640001400541a28020025036049001808040b84a1000c4c18204462070000c51888011201034040d801e80f0b600c2000028501c600401000e0040751000380006411621414074042020642107040e02103024296a0303000c0d80d070320030300b09035019400b600d0352003415003001407100c0800ea8080e984c0780121802319440c81e0050031507100980454001d454555a000c4004200c80303601501c1b10382501854200030030100052041014048101140c10100e50504000c03100c101e000c00c400b100310300e07240303116030003c900005908043c0039401c0c604158107480c1045281c0c2400d095a003001d4000c10606040d0610398dc000b15171032440c00f12002c3c5968500301c0002008180c485050700383c000300d41c0e02e00302404506d1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 276297742 1250 276296492 276296513
    0x1203060d0f1b140604050613030203010908180919020c070305060106020d08060f0d080f0d090807060f0b0a210503070c06090801090209010e07170f01080c01080112 72
    0x4000346a5400000151a080d02100c001c5108a5006402840c42c41007451412960006401402c00d001c090140301400f04845204031302405201d201c0115200f1004075040c0156005075038040c0c000e1040718441c0c60301900e9500410210030519102d80f841c9140c50800180ca184500c0211600c907030849031040140c4000e5103c0c0c007100c2c80034080c541002c40850000c01540d402808039034001c041006030040c0c01040840c014000d0781c071139554912900016a29018103041c1ca90f00410741d43c0da50031250301007407101c0c4115000f405609050aa100c0140880d8101a164141c040c0700c040c8a0100052580c80403141d02612407584103848650900603181c03020f41c0c81d654417100d01040240d40007140ca601d45150040762007160050042c0e40d05101d03403a8841e02820080402400030b12000010f68000f81c0005414091803400d810107038009170b040c51050b1120742c0c0700e02c842482c8901c1c070f0500351402e9010000901400c4058031811b40518600e511400d4258100c410742d500e0356207240c0c565600d226490 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 276298992 1250 276297742 276297751
    0x2030c07031b170c0c0306060d061509091a0112020a091d030f0903010605180115260906061914062101060906030515010e060409140105091302031203 66
    0x30502d9840c1c00000764003000184034030f50426a0280e1078400d01c1c1800c03850b18404400d42c03030080d04220300744606900d4034010040d0080d8400310110307024580d13100110b01a5110350000c0c214600f40100f007410702c2074081e10003200c028080000b059981c3c03150964042c58807800b9000790010350000c0b04000140144d1320200411501203c80c00e8800034085100746950029100c0094410001960b0750140c80d0902c00e0034000c110544043d540510480d10008280c0c0051181d036929280036141d1411403441030f02d01d25200b185085101e428451185400004075004131012055481480046052898041e8440074401010381d2600600341c10004007040b44006990b445801a44c00c2c411241d0007a0b010012500113075000381e59625541c90500002d100b00e20b9540302005140c40e14090000000294011001002003820b00907008441800418540d00c04e55103c806554544a560580c100b0300e245403a040790402c555010217a260100c400044d508100e0000f50f01d03078018400c5a01c1d9481100103113910 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 276300242 1250 276298992 276299027
    0x2904020409020d0203222301150b0c100501230d062f0a050d0c0c0203060108030d0608070503070e04110d0f060c091a0c010f020c06010f0902030c0703 66
    0x1000d80e030300710210507a008500140078003a004010000d10800312002d21902d4076802020f0940e8000e20f40303400b00c00004015200c0c4e00070070140c2d220860040300350040148a0280e0300078202c1c0782d64030035800075a80c0100c9402000e9001e4070719850f52034441070160605030b90603410090400080c90101200102c591080740341c014030400ca1503004200c00384030f900c040e855900c00d1004c104c4200ca42c07400c407413034031000b016500810074044110744a0344401030703c0360440042000148904041e01c2940c5100c28103100a5051003540d00220f481b100200241801040700c020900515484050700c0e51654558080c9580507840362008101c00143e00c000d0302d80180c0108020513011219401103400a19801c0069071914034103503050301085601d20a41c4003058807803500c2000720341000040601441380d54200c2c08141c2e40401c1350905030000307500c03402080e410010300315171320841a1b41c0d068407802c00b44111821111005000a0a00c2240c001c50344510240100351f480c3c820540e900703072071010008002410 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 276301492 1250 276300242 276300247
    0x31b010518030706020a0201110601030f02040e1005070906090f0e0a0213090204080703030807110c01080613090609110a03080d050c070b0a090606050d02091503010e0601120213290402 81
    0x169102408008058166907006e4480550300740000b43c01d1108181c0040703a140d101c400100049801e143d0442c0c00113904580c0402d058043d0070440c1e1804240d2002c0d6213510307142c0818000e920303402c01d00c2e0804840076600c41e8140c02c0c2c4d80c0c0515824a1100344102d148190700400040da41880c00c0e402414001940c04d2a2046140c9909140040f42c2160b0044890359002071010f009058020302050762041d96490040c5c0c050031002d05c0117850704100c6600f20b050040d0400825080d940b806115041050402001c05ca91007507400c10300054034003000140c40b07071450341500c40010300b8003035014230031b491f0880d082038680f0b00c1001000000700401454400100c009000003800180d0501d0b81034020703075406601080b00386040c00c00d0002c4440c00e81c1b02a208440e951750b4180180c64954036194008244c0036418201070340000407034050141141d01401034050b58002142151490164200c018001d0711141d1420b000d030081c1104940c51244902d00b500c803544140000304440c4030b80350601c1c41d4090005070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 276302742 1250 276301492 276301537
    0x902040303051902250603110414130b131b0c020303040608040c05060307030c030617120f09030304060203041a12040f02220605030f03071a0c04050307170c031b0105 73
    0x10b92011840100300e00c0d802c80080308100c2c817076141c0111101764031780c82a80d500c2d0500e8003148444000002d0080ca0280d0250381c83d000c0030041e6a440a50b21020107010b0dd4420900c60541100600000924603081034040d980110300a100b100e1440c4035070f0f40a802180340c1030901d6402d0301c3c802c030010003c035030003e4124001b2880c2d40301c15010754040c4034a5140032a85c030560402c050f0607a856500001810745c4180e1100d01500c0d00010b107204000303100c3e0340a594400c1010038110f801d00c580f10440d900340c480003400064103903000000b00200d8144040700f13030214043c00c030403100500c030781c481c5070b1100049000410301090101c590280024802042c603030101d00001040c01d045800f03446a441041c0e40d81500300080d04007031004400c3c40b43c850015610300040c80d55280c21204100c2e0030444034501305030000c0c01464038402101d0103402c0c0201101e0030306a8507240b441e4046861081e1038101c0c050140f40c110107040000b801400c410080045030b6241c0800801103c2d0ba4000402e00c0b046040e40a540d032 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 276303992 1250 276302742 276302773
    0x13020408031b0c0f0a1a041d0405160806010306021606062c040b0c030402011b0b0a0b120604021306030f080d1b050a0f2c04060902040303051902 64
    0x10002c0342070301d03215014400e5180c10700034100800c8018071401000f01c480107801c1541da141e445030075078090508910480720004200f0b48540102e4103c080f03a102c603511092450741c0c1d240340e5180b00d41d00c02c004956140640449502c0d10344298803404800358171007001400020271903005010a800680d2480c981c844480d01c400c0291452070b0b0102c2c3d2000300780d82188420203d41601c1200c50030b40000780740fa85040a58801044410080001d0519000030010404680c4180e0a042240c1440c0100d000c00040c203003001000c0003410b07190442e04a2924040d0f003c507003070410601c049000c000000c1c15036a90f4039003d0201300300c1e030504448620b0f603650b480800042c8200c9280142d2754003c2c0540e81d01c070081c1101c550200d4502103816003061040314950f2100e41e9000c0c1c219242044103180a0700c1d18502d507601030b9407001124680641e007128108054404041c0c1640d1011028400c03241448600e9881424404900c107502000d40010010080246050501580ca1810303846c00d1044503139003008107a05 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 276305242 1250 276303992 276303997
    0x50904020703031e0504020102070618090902120604060c0305060d02130b01110a030305220f03141b010c03110f16020d0209160305070e01050306130b090c04092301051302040803 78
    0x4144c41c5a42e180c050006650f41000b80c1d0000d0134440c2400c01c0d8201071044020081c0701144103180040e602c0e04035883c00c544a9010100600d2070810031250036042c10b140c6403018014000750080060301e0a00010054505043c00e0a81e0380d4015210080c41c10300544584041d0845201c424103000300c243c000081c0701820489541414003d80d40081ca81c2080c4e441d54070103110407511202100000d1a081002c503071001402c0c960150306041072901c00c4d43d00c1d40381d02007d0040002c1885040580d090709000c81d20190455500903180d6a410088448c01d0300320100b50b4000c5040d1500c5000090201450050030105c000f40000d000800541a400c0d07588d000891440e030449000c4c412a50b41d19440e01d0b92070309402101e400007040e08042845059600000b0a80e000041020380304012080203d4030617000c42d8408151103038090040003081c0780a20705401c440c1d05c81d2184100781450603881105903c4200c01030070482c80e0500d1241d150340d20700801c0007000345031001c05c01c0c00745908100001c0c81d400d04000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 276306492 1250 276305242 276305291
    0x7030f0e0706180b0906030705031b030a1d0105040b060120010c05070b01151e110f03030601090b1603050702130501090b09010b19030c09080f0f01180305090402070303 74
    0x11203034143c02510601507012006907120020b4410140040d00b030301d81e9203800b0b590b40500d141c0390580d200c2d56000a05010129140c04182180350000240440e070359041d04129100740e035031303950459240092800c440c200d65080720082c0050402c4030104a803584201a40100328040400b10045030460b89001421280100c0c50a030103c1d000003003040400181080340750061901064540c480d405000003d845580d003680c0007803011400602860485e40191650302d00ca1b4414001c40720081c2802010701c1d641d602c01e4801768040740c403d400004020316164102d801c0701c01d402030841212005682e090307805411076001240d0012400102110510b83e030300c900c030f00070283c030000814405a0501841680601a0000320410004009040031900003601d42644c0e60094607000030207500b84041120442c500c0c2d042500240100003490b5800940059000da5102d40c41008021182c920095108458240000200070600610900d10940341c83d5016051440c081e05003c1a04128280d603030032071448020 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 276307742 1250 276306492 276306497
    0x1724060a050f03160e0f0903070f1209090216140a0c050f0303071218052d04110703110d0827071a0a0e01030b010c0b06060c1e0d090e07030f0e0706 65
    0x8004541b80160069500106600042d601d0940f0ba0340341d040c151360401d800a0305007410880c1120281e4803c80c00c0b40f005144826085458130039202046504400242040e9000081c250000541d000e0205000030401d41c0407080042c881d2a1800f0300040384d940403002030b8180014030050011848480f0150350441059640d92a8407030303802c2c4506010003098106e1800b400000454021301400300c482401c400c0b00b41800745280300e2940f400038003e84211252901da01c40e0114640042580010700f41d8040342c0140240d81e466003180c2070403940c20078100c0f0074402203091004070818103030b1042c0300c5442c0d001c005002c1c3e40555464100440110b000b540305500341c45000598000003a038010120000e001d02441e0030300c4042c0003900000d00b001e60340030002e000c8003400360204405030b84003400c45005a03d404155050103c00401c501d400d00ca1041080d0f0203801850300c07e60090f40704201e141c09542601580b03001c2501d40c408200c0081c813190030724491640d680c003040c43c41ea0008001d0280140f540340d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 276308992 1250 276307742 276307769
    0xe0c0303160b07140d200a0923100f180f150207081c02030c06010902090307080a03080f07020c0d0501020a090807030c0509060a1724060a050f0316 65
    0x524182d189100001c0158041040790000340440740c10500c101c410f81500c0081c00701e91900480d244840703401656131081092074001881c80c40301500300c90710b10103c0390444101b490003028807500120140c07000002642c0321021507203082030503000704441c2042d00d52a103480408100b0700c0710f50345d8450010380c200d100e1482100a0800c44516843c03561950074000d0301c043c00d1030a02d07240070350303030f48401d90040c00c41c42c038654114031810f0610800c25141000301c1602103030003551307491035400c000758819007142e400b80c0203c0c000405c980c44001440900395905645a54241c0e0301c628009100810180c103041c11801100305420f07099035210360f544c0040303014a00040c0c4d0b43d034901402925056542c0e1080b00d450300003810803c0441d2030f5047c803408440d015100c1c0501c45d500c0000240301c003030a80c1c000f00107011280b4003a106d0040c0010382c0010038980d040140302100150031507031440d240219008d9a00c5a0f0300e01060000b0b0800e1980c0c4000c071303440034088840a41c00c80040c0400144a90004207041106 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 276310242 1250 276308992 276309037
    0xa0c120507050405042318010f061e05030307030507080d02070204051e15030601150e1512060f061614010e030304050c15070b09030409020f0a141c0e0c0303 69
    0x20300c00d0301090b00c004000039500441e800d11419144800500c0421147e0382011410b0541c2000c0d04448058801502c040280780e480c1d254168003159641262412950046d00201d01810000211007042e43c042e1249420910b90b541e9084482d0300c025050001c40303409102c000016201d601440b4080c03102c51080440050100305809900c00c40107080381e02e85221101071403450f890100300c150542d010340f0b050388641007404200b45c60b1174000d40c00c40ba420042034440d04e0b80300040280079041204045003004500e803038603010040b80042050100c0d60201d000c10807102031000d038003030a486041c4200f401d030418840544140342150306107004e01074aa0000010082003001c1804803940010302100c09030420001210a0b1000f4080d03660f005000306481f0000c12699103080050303c00800c041c2070f0a540d20496100180010342200e4044404184068000035807107104205454010b041d40258251051242c08040054502a01146068000e49020380c1c00ca441c14001403004923000150080f11800 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 276311492 1250 276310242 276310249
    0x1f150201020d0b0306011a0928030c0605090f0f1f090e010f0614070501060e0117010f0c1409040f09060b01110c010f0c020f090a0c030b180a0c120507050405 69
    0x3c142d001501c207421060041c480214888820003860754281e0150b5110303411100410440800c500680e80e00248401d400c150031440b0744c1c98881524402c40066011a0361554140c50601845100d2544208400c6c1c0c45951806c010222207803981006000d9420750140d442980b90025801ca010000650507078018082d40c0040c40c8403500400b081f1055403451460060b002b018134001c40004510704c840051041c0078403c003500503030050000e440924245503503a0110910025410b5945611542000c03142050110f0300e109182d510845511805d54044001d02c4814060380484100c030307840f0364bc0715495602180b041c410124041c0c49040000341500c0301000142c032929441951201a0307200c23102ca44240d0740d01845001e03020381c880c2066031040c807403440020b81403995130010f560080c031080c08000000d96950000100c42035191010012540c0c54010310240c0189201d802581084250105a683ca0185d0203480c080400d8500005a05404407404040d640c09403a80000164003140030300c22844c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 276312742 1250 276311492 276311501
    0x3121e06050a050d170c06160807031404060507021510030302070e0705092403041a010807080615041b090302090606071203051506040617090a05061f150201020d 71
    0x220440300c00e1800391030200068911140441c004101c3c85e00f4060f40003101a9440960721109031840c00d5030054941030764030364000d048549002c0300241041c400b20360114084c0c03007000c0701304040b00041c1406541e41c1c2c482d01c01500f40500207400314811030442c2540210a8903986020740a54a880c140c1d41d40f03503080013480d046598009010091040050124880c0c10100302c6100310419500221712070171800c005910421100c0a41d840004000204400c000c0d0031240d400300141006907249050740c960403015a580020b02410f2a60381c007800c045490074581c00012a0090401800030600d41c415650700081e4580801194010502e805814421030bd01511010780c01201590354609205031504e40d8007074a07030302c0c2066a09050fa0f650110f220070009041c00040c011025180319902ca60f2280001c00310700b1500025805161210302203594500e000c40c6544d2980c1d0080020203143c0c40303c01150150090041c45042616000c000010306482c4035825040809800e800041c0c41d0f200d6280c0f45003c3d80d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 276313992 1250 276312742 276312749
    0x106020105070801090f021204030503090d02060c09010309050a05070b03011a0901120216020a0b070b06100915020f0105010924050102030406031109031009021002010504050d0c03121e06 82
    0x5905280402c41c80c07581c0055000d0448100080100720411464070010003407041000d48001c1a40c81c00c20070051540140040d8007850001c4111030f040582d50508076214403098610300d0705210108813005d010b40c42a080601c4003030240054402040e1595200e40c50f112041d4000004410048010000d004000b2908403d072441d443da428500950070000812030b805d010165145254003060300014103214111120020303502400007008103469050844564001c0041212a00e503c1c00026450307040800668440f8041c2e80ca44d600d1450420b402e000210752141c01540442c0f0800c40300c1c030003402c02400740d54001d1105410001e03840c0400f11101c0d4104481c0d0852568060b055581000566400021078084421918000500006a003c0e840d071078490846610350502c070300035a030400000d8070b40c000594280f00f11a603502070000340505074240c5e80b04032400343c0540c110032101c0070814051980003000038482e1a08500b0a000c0c0c0c0d4504040310b81509890001051f4034080c8052001c2d01d01c00c60018 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 276315242 1250 276313992 276313997
    0x910050708040201031e0f0605040f06050d0807020310051e0705090102100e030706020c010203090d08011202310e1006180b01180308130f0b07031805120a0203060106 73
    0x1a460011009481040041d00080c1003640e98540c0341c15107000e4000c1d0445e0807003041c3c41400141203001e0114040c1c01e03c1c0c01400e1240d4640525094441c1040c4900003c5800141204a0740b0100751aa00c0b1690081c2e1001e0b6054000c03079202000081d858270445226240740300c130340ea03500c1030b0b03d5981e4984660700030321000a0100c00c000c0d001043c0e07000a001c19082c0c82d1807201040c400641c004041c190701a00320024840c0c1c0c008184520b031000c0640155105d070740054220f0700305001c81c04007110300300c00038416511281c074074441910160421b2540c2c3c08800030100e0315513000c1141211600040070024900440d80f6640da180c41000c5101441000000403940300140102d50030b0000d100c00030722000c000040e0140c0d41c0c18064407281d0090f41a400c0c461a8140314009840e81c904001c000fa5024031038080d00c3c031010040c0428482d0a081101040e58040310001c1d052620340e68050f42c0c1c00d240900d0301c600d041d0207030b20002a81d580c1e801d81c40715407030703200c2028043e401442e1040c18903018060300100b05 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 276316492 1250 276315242 276315251
    0x801140f040b0601030b060f1b070506191715010207050405090705090415021209010c09121203060b041203110c030606060d110a0503220c0611030c0d03050910 70
    0x15040e800040640c000d034000c280005503480d600010b9004005c0e00486907046200498001c103a003141c200034180c0c50040700c1c509245503a502106d16154001030003119848007081c8401d01141c0404032101105589034101081c01c01114020a0b41c0940c040307032010304504840010720070a590500101008200c166800e00c85402c152810300e464010b140030b414010941800081e0a110074010030249051240004569a15942c03540849600c81241c980c81c41c0d42c03d040c620035000d0712079124001101ca5034400a6105d1019584d180c951100b08000101091384581d004241e00301c0c1d1000070300c02400101e8004580d204a0718002e82005024013044c21103400035016a4a44e450220300d81d50700a03004c842c001d50342c1c294020800020082c003401415041c5011407041c1c01990440f00440c01400f003002a020304403da40a251124040910000c0c04159500300c1001028088e00e11005108400d00603241032051016069240c14520469140080e8803201440340d102001e016401448040348410301 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 276317742 1250 276316492 276316501
    0xb040c020721060b0603181917090d020a060f030f0203040b010b0f0705010204031209050904120509040b040e010f05060d080913020705060907180b0901090c03021909080114 76
    0x440005400d0300a407000001040d807241006883e80c00701c644c0d100e0041c00541c590031309502c0c01105800e8440100f140344944c4c0c1d04813602c24440100c0044a5620200c0004d10f1b0b0481d5407103240710b4000d62102c94010080410140050b5117030701c551805810309554100c3c800ca40c03031030b008050ba920700d001c00300725a2040050002080c0e01000c040e05580720008044d1f0740d0f500c00c081c0000944a06180a001944041008000c00180e0000c2044041403a40c5080b18903850f50101300010000f0780c2d00510040800011400550242e000380c800104020000506103596001290a640200b5034207000c1e6555030640b102040300c24800e00c1e41141098079035602018595031100319070700c0340d0710029215188100c6040003082541d0112014680c0c130205480c01800c02c80e900550743e0a45000c0d8074207203070440d64041211020751007141d440f810020031a08569117801c075054002c0120503910010540c08201100e1502d0101c01003180007041c0c0d80c0e4015059260000d46400c4852150841c3ca02800e04002e02 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 276318992 1250 276317742 276317759
    0x60309100b0406050d02040506060417060a0c08091009110a06021c17010b070f150c08090d201005091605180703020c1c05070b01050d0503030106050d0608030304060b040c0207 77
    0xb0031706140d042d6000141d03622100300185c201c1c0070700c1d1300c03900c6030749105030500c0c90700680420f00c5e600941c0d04140c14880c000440c04192021081210001842e03800300d82d02004081480d040f07081744600a524a80342c407034011010400004a0f03030840405640b01819502443c960845622019011031514031203160803d00c0082c210303001031040f48082c510104919050107903503000100343c01d41c40380c0e00c0060100c26440e20405480f540390800046841440040c0c0c1352040441c81301800d0b1150360300c94550031004a55480c1c01c40c12604808003600c55126510640b0130700344180d500a8080303500a0650351030148002c645407015400890003a0414020141d0450340441e10f43e805c034545040240e140c28400849a15280a070840e100354038103211104410203400900800a00d4024000760303266a88038800d018400344401230080660380200010032281e881600900041010040003143e441d40d00c0c0042443d540042c4e5055844542e201c482020f245094402c45115018500141480e141342c034022 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 276320242 1250 276318992 276319009
    0xf1d0a0c08190b0901060b070c05091b0a0f050c07030501060f0b0a090b0c031603081509060319030203040312050424020a03031104050904060204090605060313061a060309100b040605 80
    0x900482e016404124013800c290800806866280c80f0f0b40d071683c055050601c04416207120300c5000e4186603000c10151380c10801801c04450030030600e20324010f5403000882d903517140f0700d031703214104401403151003080303070302442404011400f0701c001250150400c00c0c07144124000303921903010b503441000540c0f1030030323004400300c0c003100c030321140c03242d119840725068600303501c110794142031110300c0000c100e400c05405c8510b0b81d02618602840142041040e000d210743e1001c00d46049030b042d400001554040d051120109001510a01c1aa401c0075a070755604285c0a903180e5048020500100e41070144181c1c0307007800b0302102038040a060071400c1d0b17007502944860103040085c0406884480343c05078951850100e0b80105000f91000d001442c1a05200000b90400e00880c000d44e42855400501da2405900b543c2c007501035080c01c0501d102c090382e0340000809214000340414114103951400558419014522520741c4801804110340c41c898070000b07c440c0700030070a01c2203280c0003051242e502c80104 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 276321492 1250 276320242 276320293
    0x703080a093003050703020406090509070e0d0f0b0c040302010c02090604060b0408030c070602070510081909080316110d050711030619050603010902060306040f1d0a0c08 75
    0x400007a0840c00e8140041000c032111808a548407034107103140750207080b02040080005655500300525124480e00314260300c200d20856000400020b001d00141c40c0c12025550041c4490030199400f07042d40b404a503504d80010025510250700c410401e0034019061601c96000701c50340360007072034642164000780c003039000309130081e004071480c07000074180e615160b000700b02404041c03032159200d035a035502d101d90700d910502c094a140e0045400002e01c2c2c5000062281c140d550081c0420740b0710b81c5c110b00c11140c040c0c1c0285001d040410031048841c080c00b07140710b180082c90252102c01e607245400f50722000c000f00c840d600241004110740c1c20b080b1a001c0414824420310007450b0196840e001410851460090340c0101c6515011380d10500c000350148200d4492940030086090069035180810075088625105002e0f40012040000a0280c64181d11040f00c0000d4181d000480981050114400e40040280a22140d002d22105c2e021302001038000401842e400c801840c0700003000d48240079001d819039 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 276322742 1250 276321492 276321511
    0xb100e040f060e0a061d0c06070309150302091309030314040309090b01270303021b010806121005280207172b05040b0a0903020c0f04020f070501020c0c06070308 71
    0x4022041441805850359081c1c01000070f001c8a10050002007113031805100c140141d00c101484061513040c41001d032480550550bd4400507640b030141e4074201030180381661300805900700002e25aa40ea054180f010401211200081c0d80449148c081c00f200c0e640107a840d1002c0600c420000042d600110b07400030ba0b102d09401086c000025801a9a2068a50300950695240600c1034040741112406403044038083e600303c500c4604041c2c45110342c841c0c01e50b5098001400000040c403a0300340880321440d00a4018215104100c00440d11030480d00140c6e400a80641201c4c00204004900c00120541c046008800c40c0742075050741c0c0f40208000c2c0808100002c0c1d4010600c80e00e500421813002921090400e030f111003150b40e4203103550081804480c1180c02118120202d480510a40b081629240d85500100a0440c0100810500d007101446850f131054003081014904281c01d0040c180c490712520016031070340d003c4c850040c00c0a0700c84a020780104004d10400001c2035101e20000e40040014 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 276323992 1250 276322742 276322751
    0x60503010e060606091203030109091101080702070e07050705011505040e01020c030706050903040302060f07120e0105030a11131202040c02030a05030408030405101404050105160f120213030b100e040f06 89
    0x1201060b40f503a0348161800d0b00e03000108c000241020103400281c1558412003400d0300d11035400c0015142e032042681c00000503031003484103200900c0c00c900159000b0144e820203a040204603510035003515401c809502e07a0b140201030030406400c09000741070b010f000140003035080c0f80070500484da0700e00901c01c000c1c04150300d5030b0201c2c02c8a04180100e601440e0003601c0c2c0c0d66030380312050484080e94003c1c0022030f83c0500c14082c801c0c015224815481c2c2d81c0304169551490f6840b5104442d001e4a4103030200000900c00b00403038043d4284c4041148002c0c00103801690030140b030360041004032403140c0500015074004001c0007184607840011603510907030161580c0d4072516035040640ca01000741803e03c2c071041c5071008080f4520151101944181d214500a0110340e032408400081da0800c0d2880c0d40206849140c500e103418080c000c5066a0441c5080060800c200209094052b16840c0c1c01a22100e201c1000e010f1070f40070100f4a0005003081d41c02003400707030800d40da4403504102c2c07949024140550f035 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 276325242 1250 276323992 276324007
    0x5010f1d0a09050708010e06040501060c1401060f060909050f0702031914210615030604093f0503090c220e060a060e0c0a0f140d0203060103060503010e060606 70
    0x5001c8590040d10300b562003046070340f42280d40500300c62000c0c000c07840403222250018006140230b00440b8180c900315500d040503000d0542d50001d507105280d000d065555211140810203400b481040341c01010340c0e60b6000c028600d000c10000c21118007400d0054000b00e100200b0140a40010483d10581e0180a2a5130041015901203402458801451900f80c20000d14110341c0192120181030180500002c000d142d2240020008103031400304691038010014400100d80d0f161543c00040b010340500c03c041050701403080884500c0c01d40f072550240700125003002c103e401c0184502c0400b0068681801461030610901301d5650300710b000390a901c80c9058020b0f50036403581044402d04112500c100901050750801070a589030401140c403104500d251440026000010f000702900a2841805440c80d0000c1e03014100c800703800340c4000e00300b80480d0b14001032a1455207002003640a0740d100380141c0f03d042440004050f00c2255105500c01c0e81003070702040ca007a0001c40c2c031070340181d02103e0039540d4084 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 276326492 1250 276325242 276325249
    0xe0402010513061e050304030804080f070206030a0f0506090106120f06081c0305070513090908041502060610050436150905010914011a070c030501090c05010f1d 71
    0x1500ca005815070300745074400200d454100e020106260303400d00201202c0d541c400350417181d84c00700b258081c1c002010800490302040d507180081c0341c01d2001c4403003107181101a80100d00268001d0b84e200130036542d240794502403d5401d110b401e40210049881d0760565240c16002003501c6030044e100e4100341e6807101901d8079000346500c0040182071030b1099408020032a40401d103100e000419010110341091b0002c0d0500388144112031003230741e04102451101d400c10810a00610000d070049070480030401c00070602c28200c801c41c00550a580e8020070503440c080062110303021030f04a0500500c11f007030009001c40c11001e00507038881c0b0744d03100a641e000002115400415210705100e034101c01d1420040e1100329203202c3d03102040c2c441e102420b000da660b9907400c25040340c81807800c00000215141c01031003100240305040c00e0944002c07200d54201031007611210441021648103ea00340e549100c003070100064002e90500401003428200035180d0007000140a040c01910854016201490154910758 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 276327742 1250 276326492 276326497
    0x311040f062916150507020712030c050307080f0c0705010e0112050601021203070903030914032808030a020c0120030114010504081608060a090203070504020f1c05160c05070e04020105 81
    0x10700b10160359050f180c803070400c00320302d01c0308807404440d060a100008404038000501001180e40300210854482d00b035840446441c03121600840d01400104000f8010440c400040d0a400c51001541507851351782042c43d40c98014039522141c1440384e040c0a54480d0b0307030081c0b00600200003500e0045402d5a90500403800c011501030f040402072004014040c100394030208100c01c2c1c078441d86600f20741c5500d1304065954401e01500c441c0c1d0581c80400c0c40d541c000441c0a8228800b640c035240a100c819950f56070241980003152400d60295020804d482140340901642d00b00011001131182e1400440175422120311050060041d03070b1540c4803c42c2032513403142d01100c2c000c10819040d5000c0300a20f98001040c1c00003445220316074071504000c150342c2015440349039113035680107001f0f1a4091900003404003942080b0000c1003010b006110a0b0504008442d000c062a51b03e182d00103147d140c4890003906c020007030340030101001000c40c940c80005d00002040c4080e101202e2000c2c05983e034a10040742c02d403 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 276328992 1250 276327742 276327757
    0x80a051c0606031d151611060403030209090c0315041d0a06050a060602030c060106080a09120c030813050c1c080406030c0f052802030409060311040f0629 68
    0xc40c60038400140392039055200c02100c140030355503181400003514800da6945207901404a18204010110354101c40c0201c2405800d441410403881002c100707980a07052290442e003c1d40800e400080c0603081d85082c00903c0d52107019450514154145003a2090b52030103045091030140c0d0307903208071540c4038000c00c107c0941c19103614221110105c052600f90090203042d20301c130501d03608282c0085241030020058072080740048004181e103a103420411208103101800d02100f040e9900b050707001254034a040c0141c402080d84500c41400c4d520315006012081c0200f114003101041d0411000090740031822405014080761074290001c9088140c10489600ca0001010220001000a01d580c3c00d90042c4904e6071198540c2c1200c000e2142c1d095440d80f1503180301c0001444c121003c203c0c400c10121440c000d00700144100ca040a444907128000c8811682084d54000c000f28203941c541c5c902806940d682d03001c0c000040c00303050314020b821030711100b4904c10844071440c501e2020301c0b1101181d0603900e00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 276330242 1250 276328992 276329047
    0x80c160c0b1c06090603020d061505121c02030901020d080c120103050708060919060519020c030903010506060c0706050304030509090711011415190915050a06020703080a05 76
    0x1c640020b01001081058508440d5005080c2003000a00030958803882c0c0480350050025841a8026a90781c8001c00036030704004002a07014101003a1915250011000b194221000b040001945070700d01c00c0d8016811110300465104004c03007411070741d0100c0c1291a0308100c2c2001c0c10691910001105540221603c210400d01c0810000052140010340c0384101c80d00c0d101900e1258494445481d00c03144480c0111a44d007601036240000107030594441540f04042680e40c000b99403041d94640d0a0342d1204a010000b603001240c85802c2c3d16013846100e401c110200c43c1c0900d0801d2480c0c9003604e65507075109003418000d0100000b024580030f0011205403500c001d01ea500d0764505150060165440070404024035031a1000e44d21b4034044980042d40911000d034140c49a001410301000b600344024400c0c5500e0304407203280000c20000390f0140044901e80c0e2811210304908082c14040031400e030764004000c41d803080c04100702040c0344404452020001d032601d140d990782c0e8aa400b448200b22100340c2e010 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 276331492 1250 276330242 276330247
    0x1905060a030212070c03170f0c0c031209010606090f12060c200723030a060c020a080c0706020d090e0f15060c070501080901021e070c0807030b0105030d080c160c0b 72
    0x81c03090784445d413408483e11981765102a50304402c280e031800c107801c4403941d070001c8000c808186000741c1c10001c1c200300c2d0703034800031a442e001141c40032548101d0250f4022815a465600a210b0540c0113150400a4120f84405603d410301c0d041c461041c1100200340507080c41e5603140030200703480c49490003112485904801c0c030901d0a400c429950b4601c0e0502c1140400300301c1803040d040444030000c0e99030b840240100113108003040e0740c035824000e09907141e41c5000c0d849601d151000051084d030240c02805440b0011740103031868668043c0c10020705420740004c011020710f007442070a0300350f40044c0d0400c90f1005080d00698a5004c0505401c1482083d190301c00c8001c505032020303400000c0c4c4a01501d8013a6034800340ea4440718801400e0b801085504508003400e25058100d4443c01c40240c10894022007a51400560b40c004507810030216400999054804000600080c00d003081441403d51003860450441d19005038085c502d40181c0340342c0e0f81a0000300080300b0600a02c28510343c05016072209181d03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 276332742 1250 276331492 276331501
    0x70f020f0d023d0210050705310909020307030b0402030c041a0406051e010c171c18030903021306080105090a0611071728110c1905060a030212 63
    0x1100da00000d407011500c00c40140780e00d020071042220f0203ca000c940080c104009910700c060040c0c40300404a5007080410b01c6114035560042c80404480382c150240000e030540864100840c568103a0000c09001d81030484040040c1c5000521300700301c80c1c0014a0300001d0b1210320000707040a02c000300143d403050511000210b20f50b19058079404500c1c04039800c2012554520511a0045000820407034860080440c0d80e201d5002d11003448401d840381c00300706801c20741c280c822419a000801d00d0801d04c8040c1698450904880c85080d84006100d1f08000e941070503a50300a0101989000c003d00a0400e010242c040d802c2d50340040011741000d80080c0310318501901a07d0391008005010389640742001e110040c001d041004445855401699024a000c03801c00c5282c40c0380e0001540901c800800c0980070700f140000041030034111095903501e1707403c0e6030300c203a0701c0c0c03030232016036006403085c121820300d02940c1c441d032108a01210004d03501f0b1611b5440c0b40e2401c0c0e0003070103a0803010f142d00baa03580401 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 276333992 1250 276332742 276332779
    0x20c0a0605060405060111060106050d02160609020a0f05220209040f0c140c0c0405041505040305130806060901031202010216080306010212030c03070c150f0912020102070f020f0d02 80
    0x1039208034000c0d9004c2042c2c0e900c44004480c0407441c07092441103034001c48010b1041078031401c0141a0203140d010054a030500ca07824401141c42d080b1030640307450b980c03810828210b15018403107000418498400740026414407000aa841c014021140b040420000d0080250300c0c09805860500200501c2007250306603200d5044040d010080c00440051312172802c09111000c0c01099512003c1e11038000c0c008015002e00f80801031801801c00d445440da00740b02008071703c0503402254801c904c41c0c2e0b1070680300c40c0c850440140e04076041e0800002508000c0820440351142090141120340020f15410345c03002c41c030b5003a07009100f50307100d6424000004943e8402d0146040c0158012102031b400c5540c8038510702c10990541c0019165440a12401c0000c110f900c0e225a61105829007c0e215840d00c81c094012107008807907003010b0000344951102c0700201400400c1310908624000ca0000707625115655543e071440001a00000f403040e101050440000e0300ca090241c01040e0780941880c85000c001c0848 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 276335242 1250 276333992 276334001
    0x10090e04060b030d14030f040c08030f0d0b040c02150402061308150f071d0a180e0c01050405030c010c05010f02070b1f051f0e06130f050a050a1206020c0a06 69
    0xc2d94024419142102080d6100c0c80300189036810000c111403c6440d00310380081014806441035034050501d40303010410020503c000d1400c1200d0380380d0b003540d038842c5d4044c1c2020b4a102c0703c4640d01c6149021500940130390042214013101060120b10070080d038440c400144207009410380c1d049070340a103070400f040da4030002841c5103c4c000460100380c0540c0d0341c40456940c1840884002c0700060320854000240c2e0311260740528000d00050441d015540c650400099000c0f404041e09241c030b8454180c414094414000246405c400386003203861b1900b0b01e404079960b81d5006540a0401c800f40c501c080070b000c02035000324500fa0130020309640c0c80300182096030182406484a80481000c0301807002e500b02151070600407610040c000b01c20394004d060b4810305881e064646113040c040701c0c501e984aa550b58034003c01c0440c072a0741824140c1070820003840d40c0e0007880d41199000c0d0444000c14006030b0764001d100700454266032000250346c100c5103007030780207800348a00395102c17440f80c03802c04401c000ba290032 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 276336492 1250 276335242 276335261
    0x1020702010305060906060906070629090601021c0e0307090203040305040e09070e04020f010c020405070210060b030903040512070906060e0429011d0603010305010c0f0207030305040510090e0406 86
    0xb020302c1562210030400c401d0319001d0f1503140e40081d04101101c4503050480181c81c00038011400001c41c1d86240042e00c8050008440008112015105034183ca1401c0403039190010402e10041004001c0108940140050015902e0034403158850810107a601009080060b0034004825910781c10545009002034106024a4008404410014004600000715001201d89041c0007180e140c855809201040361384441203410414035640c41f80158840e0300800e401407060b0741c000e00022000708445c5045035010b8102e001114010418000d40c0f01c000001d4405903030045400c40d4505101d82c400c50300d00071050b803203070a107a03003810b40001c0c4198100294022800c0152000c0c0004500c54044a107100b06a01440303c1103408210200129445103108003444d40040ca555401e001100f0001030f10381d0000d0744120f82a039194040c00c040303645c0c401400410020f0074001406424296600605130b40940e0058a0059003407440f2a1ba09510800034440100204210010f55092030704091340500396079030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 276337742 1250 276336492 276336497
    0xb04140321070807020a08030c060a0507030b030601143015190504061e09110d05060a09051006060e031501120b2d1806010f260f0102070201 62
    0xd110115400d00c0d16459420810840c1c9510342091030341c0d00401d58122400a80c2c1018a41101040713036030003000208045841040100306503d0300780700710016944010000e01c101410502601c20b603443c00074000341990050100c111680035441d0200b030320440c0348444c1160752800010948858038940408e581d0001898003601e5100d010701110b00d041840c10380d20a42c260a183c40c55449044044c1d010700d800a00c265002b2540440250100501d030540400782e44100350343c1c00c440c200704041b03c912039501c82020f4503040c5c429204d40d1103158451100070440c0b4600d036220010f05040050500281558103e00c0d034081110365141d407001000347c00e40c610b51600920911485800402508074203604969000d0410025401d0940e540d0034540d40c0a0720002c080540d801307000b2003d01d070642e144e035009030907a00010010b01d05030307200400d80031801c00069195040000188649251030844409440d0300c640d254005401d01c1124240724a10180310304510702450394030354540c3d60190001c0c01100d000341e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 276338992 1250 276337742 276337753
    0x7150e010513031b03090b03060a0902040609050f03010b0105090607030e0a0e0f071d060c1002030411150307050a0f0c0b0109020301080c030102090604060c03050d020c151e0103060b06040b041403 86
    0x101c4c00f880403141c00720240100d04210000c202d9283c0060082d42d11060180903c1d2407559101c083d181617801035080800481c801020a100a0601110610403d10214001e00100c0050b800181c440c0c420041902d00a450004035941814040c01c08040c00010240c5402483c5944100112100300e0135034051038901c0c40d43d40402e070054410200e481080302c0c204400f10b0300d50302c00b80403c0b4291744100c0e400f075440d000d5180d020340e0303043c01440558411800783e41403020601803a41004083d14501c64042c10a41041c0180410107074450280c542c4a4661300b130040e03001c1d0086a044c1c51400704204002c013008041d500224402c2402e0300910f040764000c1b0101d03020680d4400401d8240d015072411580c004d04140000c021041c0306200b5003080a0083c101686007480e6483c0107000c1ea8080410a14982c1c8003078942070b1013542d2580690750049106504400070420104601070701c041c180b2002e0030550b00e48071074a603035039154011200144440350704107a0b200e0307945024404090541c050903200f401071 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 276340242 1250 276338992 276339017
    0x801020909060301091a070207030b0a0603050f030c030313020402040b031305010614221107062301120b150415090606090513180602040303030b030d1407150e01051303 74
    0x50140c2c2d04e540746d120150381c0d0400603404024200060040c150021403041c0e030310010108142d4840f06006000100700803c0140c00c60815914090500c002c440310759104012401c00001c010080d00c0e0002c3d014410012091150f0002074003a0090b50040d0100c07040020a00c0a00703100b1055030f0072850b2285000748841907490050030000c00842e55036076000a0b400410b0001d480d8883e0842101c5030f0607100000d140c503446200d0104980054404484d210366a91030076588103200441c0f215050703000703510440a0f40c10900c9004046103884401031032914030030f01080b03030f80081d42980e03200d00c0d030050f004109101001c0001c0320411010f03c51000024640038010800d94030419014040d40c43c060f140c01541c654042401c8020001c244c0c034440c40341508128000040d500d8002031004601a0364045056601c0e03104060401050394145814049000c07040001d642000080c0c035031007a08124681602034003042250040c00403d841888194a08410802002c418207070f8622024081c0d958031008092 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 276341492 1250 276340242 276340249
    0x111010204081002070609050604030c05100c050a0c210e130203040302031c0605060a1106090705010905040903021e0307210801031416061d030c0a0509040c0f080102090906 76
    0x207240654601074000e40c2a40d050000c9039001030040791b00c44e485c001101c11194840300d00700201070f00c0440001d000c0e0f4048505100c4204540b13003002244e0384013002202070350080500144111007100041c04810348a00341807040441810300c0481c428100000450f904940040880c0071402440f48074000300c128081000f00d4503c00c1e24840c0364181c00642c0740c05d081e001222016a05000644030b00ba48440c0c2c0880d203511110040d003e1310707501c0d85505e900c0880c405026414000d0051101200b6030002c0c00c10401c03682e0204071381c02100d0003035400081e284917a00b01241801159111208101d29000c1480201140040104021800386070032003403981c1d1510308a040301e40f03000e81e1400010500c0e40140b01244030f150441030364800e1441102c401800802e10120500c02c1c3da40800e011a01c56142a402e12040d0760385015520b1049004d0703c1400c071074030001085c1c080507000c1c40e80039900c400005410031403020201d0010b0150242c03a080e4513542c0b0300301940030394840d80b1140c7c0901111800300d042401c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 276342742 1250 276341492 276341497
    0x6121d03040521070b07140102070b0604050708090703150f09080a1107061715090405061b0a0c080c1e010203100b070f060c030f020d062603041206140c0901110102 72
    0xb8041e4004d000b60f01e19184025445400454040d11161003014801000200902c01001c00300d220344045041890024200000c071000204401c0511001d0400c100300e40704e0120303542003925403203405551544176001c8000e0040100c7e8005000f914a84000c2c030060240b0003000d040701881d15558002c0203e0840c00850b2186001d1007071501254041401c50406a21a989240d0050080c483c813250341b400d982c0040e01072a42690169401e801100c2441809401071005051042407450490324000038810000d0011180b140003600e0300e2400f00c0c001100c414103114000b90f4000281c0c0003203207596452440b900031343c800d90790882d040788440320002e00001c0340c1e4259183e050f0410040c0c084241c0d161508000740191400b5101055514048030000c8001417010b0154000c04250009569080400c0c0b0b1003e40c040708240d4055440c111940800201d001040b1810341e038042c1c44800612500340b408001409411070058180161030007000281d105c0c0c14040c00707540c0c13000d90b6200c10481906000380d00300d1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 276343992 1250 276342742 276342799
    0x50906030a14240a1b0f0c0204020f0f0d14091b0a08071502160f060e0d0804090e210306120f030304140c0f030712030c06050a0e10021306121d030405 66
    0x1810420146c1c4403140035030300314214580007500143c60031038105150402a800305001040f514808501e610b8540c005100781100b03440c2d8034240c0c1156040c03400e4031175560503800d202034034210310f6880051074039100d1803821001482c03039400310b9800daa1250300d158a80e0100081c1c40d00107225042000d401080403620b603004035080584031920701400d281045486400c401190381e0016600c103096800030390818002e1004029101c400076034020400442402c0c00c030141144000b41c01c0e0030a2200f0081c0061f81220b400600444051074484141c0c0340076424420201310f07040c0c6501012040005100982c120502c51a88507010b0f105649002801c0042460740c07141d10581540c4817090030700441d078540080c1240c05005e4200700001d5112030f5500015510200c0300c1155261700d034850702402c00810001c4030304000301071006500341031030013034203c01c6034004d48620001c0050100d07403004445d8103a0300014086112581c4d0107462140241c040b80c2c1c3c5e0340148546070007034280b00758800b81a0310200c0c140011 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 276345242 1250 276343992 276343997
    0x30f0806010527030d0e01110a11041508160302040c020f0d120e0a060f05010611060a02160519030801090204080304050d05011b0810050906030a14240a1b 68
    0x2e00c42400300c0e40d21104101c5010700081030b503041140991303940801c880090305120382e44400b071204035280014070309400440c90030705541c4040c080c3c100085100220724075440c425100050401305040554480741203562004140e070241400700e0015418007122102940c0c0252824000200742000403a91540d01c03640c0400c194000301c000380e818900c2100100c0451003215400300d8a01d01030f034541403c065540004039042550b0b034003151141300305401840d004040b1414101d400300d1401140544645009190301c0c1ca440c1c0c00116498080440c400030509150413200700c0d0002800c0c00c005240d601659041513010405800001030122128002c80303007591610700255041915060902c00d40c0c00300031408440f01d5403200710710254080c251f85120880011607071080d04a0901d0681110a049240c0089000e4070381c2c17008104540e00c0000d03c41006da40c0c03125010000c40807409409041542400c02c00c002a64210014004030f044c00c030159000303494800b020030010618403049050b210718000340c40007 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 276346492 1250 276345242 276345247
    0xe09071e0f02240a0f020405060f1c020409020306030105010e070507020415050904050327060a0f120606050d1812081003170414010f02031c06080706020a030f08060105 74
    0x306620610766807402074503500403201003000440c080e40114140c80c41c2d80a909022104101407030415026200000490b0341046107080d0030032010400d14451a450032401c1840014001c0c0e9010bc200b160b01441c000000c4210344580e02d41d074414000c0d52003502d00a10a41c2890000b00306042c42084481c01030103503448651402405900784405012800f10070082180100d0340029141c880ca00348d94030035440b41d00510794400a140d8500003001601000029136038072260341c1030301502c800b02200c0207080b03c0d041a84002035284021512200c0d95840d90100a0424130006100c0b60410702624082d02504070503c1a0f0079035400c0740d0a1454109009050a415900d0140c0801d004001c150381105a8501004140b41c41e41c80307190b0407003c01c0301201c400742c2002408205210201442d10201c04091030403504820140b04000d54902400c00c0d28040c8000000038142d10101a91101008004480075a20242e90f2000f0280d100e040c450001c0d40403c030026601702c1801e10451045100c0c0b00143c40d45030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 276347742 1250 276346492 276346547
    0x80303010f031a240f030f01090b1006050307050d020c25052707120e0a030e0315010b2505031e070c0608060103060e0916080115170c060a0e0907 64
    0x18000c40044842c5d0800524a1420302c2c90303e0a0012503200e008510010940e2145071420500006005003c03601482c040101030050550000442e038001c00c09291058680080c2b06030740c2c1c000d02c101e01140d000c80c891a02002400f0810345040420f8000004400481581d04c1d800c0c000300c501c8484481c011f904441b0a10f926541d95050b08681000c12413810800001d079014010040328204410b400499000d0b421002c00c1543c000340708048510160042c00341248050f441d0070708000c3c107000b28030b0000004145500d842c00000c1410581c500502040c02c190099030a0140e2213502c0f02c00c40c84280c10310817900410441102c4111030740d259104050703000c494a03080084440502c041d00c80c6041580360800040d19220402c54036014003071800c003501c8118805e02c100511038040341d0016909034180400d001e6080d101110f25011200541007684803064540580c0c1d06201c8800611540844086583d40045601940410790a4010b880b03189042d110709606899100c1000200d4055000414050 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 276348992 1250 276347742 276347791
    0x42d0305070f1a09030c01060603020f0901080903091009051009030f030507060207020a03030e040b010207080d05090406081c0221030402040b040603060501090b04060905090a02100207080303010f031a 88
    0xb50800d80144201c420f030751001000811440803d07104c92080d680b010400368180311080c1320b88030050002d07040451401386130341940040c0e40100000c15040c00380f080c2c0043c40c0000b0500450300c00c034100402007090f20417581800b500270321450281a00440c001e40391038001c01e009489200c00d60f41c0000c0e1028414015a40480721940280c1e0700312002c5400380101801078584c06514000b5504c281c031031041034019030040c482204d08091107641198003500c1b0400425001051005002c407031032416507a102055400b04018100a90155002e8842c010040804681080e03403510440030719820b0303850b411030b045900d4001c4105104614248807080011500600d05540480c1840e540074001065080c1d40c0d80b548000c54409074003e940d0319440d107801c840075140a203ea0b070b000e4071044200f0000e9080c00c0d40e481d580d800908000900840e421454490310364020404000103144200440303680b5030316008902d4480b02144021155024903140c1e0643c042e0744c010b1864455040c007540b41c40d0704004024107 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 276350242 1250 276348992 276349013
    0x506070906081f032604030b040209061e04020702370911090108130c0b0a230d0213090509070611031216030e15100609120b07030e06042d030507 64
    0x10341e1a0b0013020f15018218090b03002401c001d50050384500d23860f20b468010700000d03010007001ca6200710308204550783c5a002da829180d650502c01c0e10b005840e83c0007407022031500e001c1e151442c0c4920521480425461010b000b02a50405d1011600c903200c954030001381c070903160b9031520251580f4040c44030840c254032800c801940036807007126003000859a07454855840820340c100d030000d110001946000607400484041800d08401900750840203000d401102074062104034a07540341d000100001d03035660181e5240f0242c203000030208883d05045090b1550364200303110b0480495070116100101e80404002e40b00a081d000c40354070303031343d986900521000c807902c54400400d0590f580035940e6541010080b81a002e004c90040003200c1c05c042c91131840804d070580c0403c08005481d901444a030b81081e451503500d0380c0c030091a60140c1c81e03094054001d0300016040f042d441c13040c04100420301080e81003185401c45d1000b1001e0f500c140012400181c2c460941d005004240100041d40c00920448070 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 276351492 1250 276350242 276350273
    0xc0305191119090f1b0f120207030507080c030d140105010f080403031d010504110910030b2502030918010803161104020406090603060b1201090f090506070906081f03 73
    0x203941c1c0b00b064403103901000319104620358146880d620407940e00580020521881c00b0002d500744820b0000e9610001040c845c030382011280040c0d004030360380c01014090801c0e14072441c0d100070340949a00b01000da041d90f03904080421782c00c444c107004e01050303201e0407001c604d4141c07074060750b445d581c10b003108070180e5a0b44000f802c11000c01d40d64004806000809881c0c49869614a80001c900c608240c107042004812240754203108809030b81c18481d2207140c4410039001c495200c56094502e944a608001051094500960548580d0080284050360120040c141c00c0c3d41102c120003104540c5034240e01c400e000340940d042503402040701e540580354805c014422144a020305d001081e40030400300c0c1c140d8000b80d20040224510306da042c4140798045c045c65024152414020342406444034009500020603c200c042c0140d49020b07070352180500f6089042002d4014040f9201ea0070a80401030100c0b05034468100081e0342240801c10b444a0b0800844400641c000079103480c50854a400680550601 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 276352742 1250 276351492 276351529
    0x120204050411030102160c0503030a020304171f0203070318050c151b03070203100506030607050706021324090e04030509011b060603060b0418080903030909040c03051911 75
    0x41c1d5080c4140d070240028106001448140c0c042c5810525046140347c51b1908458402d4201f4000ca000884c4d000040d28200c0c0c41c2c5198070060310382c0c12201c00d8106070002e041d201d840746025803909144107054005600407001e079541082201081401c94100c107810031002003030354101001c0c00c0d440c2d00d4010000c2c404001072088540c6480301242441071041142c0400c25010b40001c143d141c15403406104101050890b19410711203850807900180d1180f800034040010310030089a44402c0c0100380d410341e884503460900c4050072945506643d000c500c1130445601030508444841030b0018415400c0f8000c51f0702c0d00c032114000740c80781e80e020350300c0d80c100886c0c1b20704004030040203e1030b404410b00340b03041071800365400107100d6065003061030543d145100400d00030344c100300a2000c00054101c402d0006604512696143c01000d00081d0852052224056018503a6010310052148142403441240d11810454a207c4810341c4610382c01650580c01800002e006815140182002d0000d41034180121 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 276353992 1250 276352742 276352763
    0x60901170108060f1602070b070320010b1009060801090b06120406021c090201020d080a060807061706040b01080408030a0612030206090c01050903070b181c03120203011202040504 79
    0x10424490140400d82c410205a4440b100380091100e00200700ca03040340c035955a8440700c0c9100a07000c1c0d07540916100d181c00703009000850f0300505101da49100b61919140700c2c1416105040c481842c041e180300c0884600c1502c0e600c0700004010700446441d0121020382e01d9074401c0fa0b192603030450040501004171504000200700111080a421001610a0344140340042e10340203883d01903540c4055009204000510341580a005030307800044550b4000414901002c540d078401012201403c6c00e540700b110340c0d128404c004541c1a400034405102e5881c4030040d045070395122030400c82569800d206090200794000c0100780407031040300045602c200b0004002c102030b50b58203000803844011400c1070300144c10a8083c4400d0100034030100304503100034a0054280b1041d800001e484840b02c0c4941300252100003441080d0032003608800d804071400409851248000842060800090a400b24005a0b8148803090442598826a81602c0c2e2600640f501640d80d80e09020041c10041d006542c4400070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 276355242 1250 276353992 276354017
    0xb13060e04061d0117030a0507080703030b041a033a05120c040806090c090a0c0306030c0f0f060903050c010f020c1306081203090d08060a031704050f03031305060901 73
    0x10081d0340e825001e04440c0c3c581540d0300d80042442d402d108054008401c0c0c03c100094512070340d0080540f001a034111a8040d601c2d07607a841d040e8010003c641c14503070801c3c00c02190040351903e54140145544069060f9403440c00d81c40000000c1200c1c402d1107401d514421100e40c40420107039040d100710001a414414507000c01922501a02c1a0443d00c0e0141000009810b20803040c00b80f100d0b6401110513002401e0a83e040000564200d000034604110030303542d40d210342d0502c1e2180d0800c0b40119004272076850800c1c0ca903001c40410010310701407512214201c2900083d000c0c481c0c00044200c07604140504014102400111a03c1802d03180c00002c40c030810b138500f51383e07580d04044402c03d85070440e00014801d03d4410968141861401e440c01004820300c108034041078040350501a0089a2500d407207596075060028a0008081c1c001410344200c40e45003401c100303010401041954001c48554440c9042c010806649110300940f0011440f9020020401420054044d003000700050601459007490b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 276356492 1250 276355242 276355259
    0x24120503120f04021827070e01090b0108100e241011100207082208060a0f05060d02060711040608010f0b040c03111c090f0b070206010b13060e0406 65
    0x36030b6602d0361503401c40148011450540d85242d103400d1543d8180c0440e1810b04100303d01040c0c941000308000031110007011000800b0310078000076140e1400c0040180d6110030803980148200194039001c264854003149900c7c80d000440000c5074641c8100722410307a10b81c050040c0384550a50086500c3d818034000316415030b1001e280030185501740c1e4512410034074864095190040f109510344410344108007440126000d0802ca900c81c042c41c4180b100701119400900c04c2141c2244d0000c85240945824400d80d00716a4000d9091006222810300079520346c80c0c10040303c840c4240000b540450200441d0000071005071403c10095401080081d40f150745041440c291035050100c8079109640f182c91200c1403a044c46441c440300c480740380400912002c0504c900c00c5205a4950004503c55076201a5005c1d102e0b03000781130010350081d0181d413400001c0c58a94007004007584e00b10098041c980001c0740c58111071007915001003520050120321481d01030181c0b80301104050300742c0c10035140e81002c9540f50 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 276357742 1250 276356492 276356527
    0x1305040312050c090d080c0f06041a100b03131131050c1c0603081801020f06060105090d141c0908010c02060a050604140c03010924120503 61
    0xa0194071000c803100e5070602444100c0340300074103489024001340200000f94565503031103000c960b4015507082d81e42c1a111111498801038120710700040c8a0141000b0402c5401c03014440e041d00301110640e1103450b0802d4007843c0e404180500007600c001800001c00100b9105000c4207014003c240c01142108130700d010071104080c7c0610f0485d90b00000039040458280300f15140581c0504c1e04041045041c0320441070b8551152140410040390000107001d4015030960140e0b000b198004401590b03082c040c0200586269a84a680d001d40a034042d0041d10060108441d48034141c140e40b05464202d03c0c00030002028030310002950b201710b803650707a4580d02204001c0602403581108084d00010103103600200078107011303004002e1990500004411580d0005441504150401c10200d800c0d601d940c04180108259900c0c1540006004140003800c2c0442c4015410307900b2584050240c0c6901c0c5811300ca203002c61103c903441000010100b0800380d045c40d007442c24914810b1059030301c3c0c120000c2195140f0b0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 276358992 1250 276357742 276357751
    0xa0504020f1206060f0103051504020c03040f060e0108010b0304020d1401021e030a23070f050c010f05040c0f0308040311030307200102070f06020c0d0201050409060806010302130e1009021305 84
    0x741e002d1010720000d4031700002c01100140c400d103801c1c040c61918003c1400c1203008016aa0300aa801160b000c0201c3c0d4240207a50141503031244d000401980c559000b0150060310828501142e0440c00100d201c008917400c580c0f140e0313000b078070a9821000c580c0c2e81610f01060710a608290b07540c00c0c88000464046510542e5030541c11641d0142c803824800205001c072207401c401c546600e01078441c141044a100001c40e41d0011310f03400d1400c3c041c42204016219071103a0321801300e040d4a02404450400d0681d070003603010b6400303130080101d83c1c0d4030707440184040c1c405801b010307207075000c107000c2000040c8504820205a000140c20360781403041699079003500010741c0395507002e01400c00d1040500f9580c1004070400405014810029051070001c0c007139220706d02c0fa1800c900030107401c81d81d0740543e401107003118001c2c42003020408c4025618045944c6415081c00102d20a10343c1c06031210740341c40c1078007d843c034889074240601002d2242c5200380c8000d040c030402c01ca03008002014030703041d4081c486c480d05205 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 276360242 1250 276358992 276359029
    0xf0207020a0504090302060c03040302010b121c020d140306041d0a060b030327030f0607030c030e0d0509210a12030510150e0102030408031b070e0f0a0504020f 70
    0x5800403481000103468064200c0750040749070a0640003c00d44c00074095410580c8138001e00e940361641d01b0128050180711000f80d401800403948603505090000700109105110300c6074031840d050b10752080341c4603001d04045200080c40c42202c002c800340c00c20010754201740000c0000400703003205020004240324180640200c2c1e08982404000d20502e40100e40c0f604004401030743c80c1c081e60800b49617800101d40488014501c04100c2c001250304c4c05c1001c2c000d100506401c0b200f452800c4c80c0c00034090001e500c0001300080c1050300e102c14200c00001c002d003060025840d400d051106500901800d0895407142d40c9003589050300311501d101e414031001c00711740c0c0100d00226070107071444005000d03070b00e000c1c001c14403402104100700500124200700f02030500d1140340c80020881e491004031302e14000ca8011400c603020004100e00828280700c0300080844202045c0d03211640d4898030707149580c004440c661844c0d261000080c076108559840301340d03c544000c00c0c00c91116070300d4010908204030011310703440 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 276361492 1250 276360242 276360247
    0x60f09310e03160602070b13030824090405030a020d0507020916211b08040c050609030111041706070801060806010c02011418091501020730051006140d1b090f02 71
    0x5000024182648c043e00c05800340c049010b003682c0003802e60358000c064021413000f40d80ca03c5000c40003100300ea41400b4004005001c0c90506d03080003503ca1344410304040151090081801c80c10303004409036075020390010200e004603644c400300d1002e112036540c80f1008020b00301c40c180045800992803200d01842032200014a1940d00404020400281134010141b00d114000c0000182c00301b0700520a60314141e4640342c903815000c010a000d06038070a4544441c000c0484c0101e1440c02d50020503282d405c0c84411101d5a89a5805c10348615a0a01950340050418000940194080c0100200700d910614042128070308203240c286c101d030000441c0e10a60540d082c1c3c151810700c0c09403903080d004004049000c24207503010001035520729451240c020500911311001c1400034140b144800e4900b141d100c0504240042c1c50102e494082031091700c0718442c60101d01041055114511815804c000341200c0a00c04160700c800400750301d0454000d000c030384000b0002c074442c1c505d4000c0d91400c082e501e00158 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 276362742 1250 276361492 276361507
    0x1b03060606050306130b041107060b040501090209030a0f030203040306090336030303051008030c062e0620010606020a0309140607170702060f09310e03160602 70
    0x5054900340da004008105060003800243e545050500912410340440080c1d841c0c6035401050207041c10030480c214058001c100b07941030184c00c0d04290320858089404020f42d81e218403000040b4060020308076050303405000d844001030150035004031440d000780101c0c0d043c2a907aa0300c0d10143d600e0705c0b400b2400a01301c42089071200b0b11004001c9811150459401440702030304030420b442041e83d01c0040c00305506d91021a09000c0e881200c08040c00b40b081c1030740d0303a0f203450a82c00f0390303559020741d28040c440552003403d019505500d4056480543c407150607084c01c43c40c00008480524600c400b0391005202c0945403452082c0074032403040204000e40181a0444c000d0901518024540e48210700c05900000e200a036503840310100c4202a0f84501451081009840e0341040350180b0000290050740c0028003003100705490014062004007140c40540d84000003254265100e11a0310b603061a041081c50310440b825190070941c8000c0b21101103905041c1e08641241c294030184409480b125400684d45 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 276363992 1250 276362742 276362753
    0x40903051b0a0305030c0a18060504051c1502030a0e070807050310021207030c1106040b152202180405010b0d1d0709090c1e050a05040b03060613091b03 67
    0x506901d40700d5025060706072407618050124840240a00160200000d41c1301c68140150008003034005208441c807840794030341c035014209602c5030080c507100346068004120500d24810740125110f03800201100389042d03d0b041c3c000a508054180ba20319522a029443c0c010020840d00004040040080100b58585024036040180c84440c087d24a0700401031013501d1400d50f65604e800c09420b14001070040c000f200c0445501c001e005d9810412302510061100b070000516500b4002e02000390307908000040c000070480c0e6402d00c43d25012a20349a510081c150721a694017a080d9820a98000038003c0c007000000b40458509800030201d85001080090b4030100350322030307031000d16460141b0102101414017003991b07401180c412009200e45030144c0400f081a1180550001e001801075580d0310008000f010100d0655070044034001c01407080c0000d51480d06005122440d1005005000da5846100034403443d882c00c0b6440080c5142c42e07000101c0000c0710110b2000c100c00c41402440740c00d508504d0903 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 276365242 1250 276363992 276364027
    0xf040614070f05011e090b060d051507020303013011060d0213140103021315050d02030106050304030e01081603020c01090209010303020f010f140703020318010c020c0112061202090403020a0204090305 88
    0x72028010f00e0000e01d00700241f051a003140e080401220040010682864110f14046151070702a400500070700500c024650004065810380d0385200e003c0750100c0c110a5404e00f07500c0300101031000c44106500c1040413682c0d071202d180501c00f0141c4074a2038050b40303508510599102c41a018040030481008015115010108840000d030074a010352616103041602030b601681d50003016915903084150220f6030303014030b04940c07204044200c00c2d5141d603551500a88240c01c02c45003600401d121126490f082d62180d071503540b01d00c0842c0d40c2c0d01101c2403407141c00c600030740001c0716030461996288070100141e542c121109000314800c1d0300509488a5803081e1070300b962220841c003203130141410b003070b0501714681603441c5900c82100d20700140c90341e44402d1503d080407030740095075615500c3c04000f008895800f00e40769807291400c0c1c850001d00404081d095044520031700c100d5841c0d401521300f450041c501400b030f0300c1d00140244100c07007200d0182c0d00000d04860300b100048002c078100003038a2080b440c45100 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 276366492 1250 276365242 276365291
    0x50f0c040b09010e07050c1501060905030607090e0714130f210203030f0c0c040501030c0603060b1606090804080d03050610020a0201020c0907031508010504170f040614070f0501 78
    0x4001c030043d49010000c1104140140a00741400f82c08a0002252403041200c1d00160140d400c070803069594441c4060b040c0d1606005040c064040d8000199a241c050103070841100d50000d040601581c41070070403200c0994413110715041c1e038400c20510908000032946480074000036103060481c10310389005130340510b0450007911031075011984e10740301582e004070a461055500c2e2511655401405141c9030030042414000799009140100110520000342205010340700652030822801d41c55401d00d1800740142c04110500c00c001810310320009d0219004460194400c101e00c50806132506145400d0184111010002a0381c1c0c0c0200403c81c548003540224842043c0080c00d07a100b00c90300002e444458001106000e01018404965124401c0e4003c000302d81041c02c036541e10300d803250b40031406010291003da8161143c07280c039120184c10031003203ca8a25100801d40d2505241c14420340d0381050315241841c2500091091030041080e0500802100303114000001e11042c02214101c0003180c07560 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 276367742 1250 276366492 276366499
    0x1b03071505090906010e060d0c0e060405030712060207050d0804050714100c05030f0f091305060904061e0e030d0c030204060c06090501020706110a02010c21051003050f0c040b 77
    0xa00c841025600302003242e501d04000d5501042e59990b20005035000301e0301c5400c1030380210f40006c94078000766103940140318100155480401070720700c840c2045418051401110b502d80c0212404100950003a100e02da15103116003005801c0c40540d44a076810318502101c103030003003168402004200030f0144815005010751940300c901000410010034064000000c014045c0410344403004103214041060324001410b2030b092541d55180440d4045458100b010004e0055062050303048201245000e0203106445c050490030309540e407074840b90040c107905040c0312070022202c0305220341d082850040c144c0000c9ea18005558610701e2154280c201c40710a82030000f0103105000c240105035220050700415130b0041d0010072080207a08240e0300900c01d40350020200c52030000184055000364020305020485500208000840250113582c0b01c6510480541c0f441041c07005500030000690019801c2038204015904044d1a5500d0703524008030b0000c20380ca107a0010300228020f103890f018401041c0e1081c0c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 276368992 1250 276367742 276367769
    0x2109030b130b01091a030f010906110307050a081305010c09031505060f040213050a030b06100302090d030f110607081006090815040206070c0306150506130510050c1b0307 75
    0x985400d104294107002e4480c100c0c0d1102c10030b0404402421780310b034031a00c0050603140c440a5986440d8000d10a04404440e0141441c1c02d644400c04414180c80c4103c03d1500e81c286001c50b032041c200ca03201401404545402201c0088001044092280d03003803c10448c0c840650960a41c2885111920f110141003507035800c05082200e940c480458007034810406540250f16114500c0c0c20661401c1c490300026000f03242d4540000c14800c810142c2801382c001501c043d07043d5a04168118264803400315216000049904d20314006842216150b60000c2c1038508401c0000c2081c8110b800c0c40d40650760140000c0781721040c0a6091958405d000c01000c003400d011300210f00d0000c4044d15050707a400180d54240b607400004055480312812181d035983d100300c04104140c0c891074000000c01076285050390070b1a10a001140e0703400d25004892501986100c400b00961800b030401103107040007169102080700c28016015440c20400c58a00030f0700091000c0b5028903805410302d4640b020f50380c0002e9a84410 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 276370242 1250 276368992 276369031
    0xa08072c130b0901150e18011a0f15030103031d04020d09110103150b0703050c0303130302010c031e0e031c09060c180b03061c1524122109030b 63
    0x2c05024604586c1c45407038488099031880c0003490000000318220b0115424201d502116406500403445810422110501a0311260091204a10000c582103904000800050000c21b0040030700404640b00c800003000002c40705008034081c1c0e04171540e201100c0348c5850120701006078406141ca250282880c040202601c00e4420300e81303800c000c0c070410980b04000901001454407480895200703034aa04d040341d40d43d0900041d86090a481d04c0020f4005518003401c080c0c4640c841c1c024494044900e40c0c03c8190180d03400c20600050400341200f0080384010001c078a10700200c0c2c0360340d104180c103482e000a4100360508101d070550f00d1004003201000b510200d01c0644042034241c941c165100c0c0c0d044c0c1360302d80d81c501c8007085641c03042510055100400b40c492208110b15014034400c046071111040c0000c2c440c000c10020001c43c0c400b143e82c4004140907043c016600400312840100d4050000d5001411946113284001142e004041d40002c460550074009c0c0310305860f6180c0c01c03059000544040710380 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 276371492 1250 276370242 276370271
    0x10b0f101b05010f052712040501050a0c02130f0609050622060506070f030e0a05011b030c080f0405210c04240b0310050a08072c130b0901 61
    0x411005010307142250048201c00c2c4542544041980c103152801088281803d441403448000340c92441820055081d000c0b2101c010003040d14140c05404401d83c604060a002c01580c0c50b412000c0750740200303c1e110341c0301e10150b910003803021f040c056140c90021b80910702c1c00c0c0d010b017510019000820030504050a12429031101c46220030f030540da1501e0342121811590750080503211030392141c0d9100f0b90104500c41400400300321503203054429121403140500d107205000c0600100e20616021070641600513040c1c00c101319407100c0062007480e0408480342c01b0f0b41c90a0144d007242c0815541c804000c1424080c5081094081404148a0b0b901010501c02503204640c1c0d61880c0e108207000b252684884070401820b0304c0d08103410b8002c00e0020301c0043d101d500f10b548641081301c01c8445882e4601c000111410005030f2003003621482e8020b0500c00b4204075202e914950311020300ca120031200002e4030124401d003a05c460042c1c02410454080081904044013401800750100380c50764500903005400e0304 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 276372742 1250 276371492 276371507
    0xd0f0c02010c05040f1202150f0306010806190509090106051909050106050403083a0b0f0a0305030d020c03090d0309060818030316020118050c030d020105160311091002010b0f10 78
    0x201e550803099506c20840c408a65406056944500956404200302d16600c03141000b8601c182000c2c0e0b00d0914550311581006010b07041c2c5030b008602440c50f50030070700075814031400041d4003a500e03c0011a0082e541d101281000e025070b10104824518444140881f04040c080c143c018201c6103002d500705800c58032080c16034401d108885071200715420340110b40c40c501d2151110703240c08200c004120004c08400030300181c110700c0000c1c1e02c100d1204070380100c145060903014090300e07000f000460030b007200706440c0802940076400d103458900c018054440c0750784da00404e103000c4600c130755104403a15180000292038000042d049582d124a0100130650f1034000200b6260b10100c01c07030764a0504400c0080a0b0b0041c095448003448100040740d42c1c005208000502200c00c40b0300b03908aa14584040360101e080740c1023510345009a40303100c0d419450042c40382d0005a00403141c1c80e0a21725110070b80700040c8a86e1104103240c4090b0351100c0c1074101d2803a00031007200c0b0140003518280008403c05400070b20f483e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 276373992 1250 276372742 276372749
    0x614010806180c1c05010c1409040911030d050a020609010621020a0f091401080312010e040c08070e0a1b050306130e100605120a02150309030d0f0c02010c05040f 71
    0x40d001001e441c0d694003004040042d0302c01030104640c004c1d1400d12080c03140310003601a102503003030601d800b00d0031344242492801e010070382d008a401c0c0b8406004000240001990640702c40741001c0b0148490399003482440999040703a00c54a64807214410b0203420594002c001c00d8840c4d240c660208082e10200310401a42032112002110003c0244005803413850076800405030340c01c42d2a0003188107c01548000070460b58101800e4044c1c0e41c0b86a802d03628482d80c00304100600c1c40c1c0e4010411802803000b030542041c4120f02c0086920b4880800c20325082044c0e000c0041241100c0501440d8070442c801c0100c01a054203043c4c2640300300c03d00c094460b00c00940700c980a403c111440398801429640544029048042540c12102d11013903c0340240465000c1d082c4101c641c14840e9060460000b80210216800760082c185030708500c202e0845500010007e13201c50004000d01c6912120034428014198010f07040003c055425010080c219230f940d078140c20a04c40200002e01c10048000340903000c9 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 276375242 1250 276373992 276374011
    0x9150103030f030e070b0d060509130204020318060c0a0305010e06090718030503070b150d1e020112020a0206190c02060a11090d03270506070b04030504080a0b040614010806 76
    0x40c0000b4020803001800e561500c4240b40c080c003900403071604515001001d088806800a2004170b03110010882c032014141d485640c104040321a070720050030150091540807079100d84907640180d100d90f9060810034120740f20025a071000444401640d0148609800740032507444070b200600c4c182c408150350000c0580003074240714240f4100400381c8680740740403002d1a8000c00352900c0e0805440c018050100603034000406c807885604c402901e0030030050250949400220380c1e6003c1c0307103030349108000100300841a030400c1825402c0480c0002c09000910403c41c0b16401000245001c0c3d409045443c241c0010f03da41c1030a200100f4010355000801a4100c04044400981e2101551416940b4406c0038034180c0c200703500480800906402c860401441031910a812560000ba460100440310483c0180780d8030980500050011410300c210030340d42b06209040040c83c1c20740f01c013400c5107405100f0342d080302c0e0720341844104401c2120f41e0207107102d02d1000003010711143d414103464135140d40c03000f0f02404d41e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 276376492 1250 276375242 276375257
    0x4030e1306081f061e0306020702010302120f0a0e0105070e09060d0606031a0703090b010b09010c05120903120901020a0b13060c09032109060509030102071202060f0915010303 77
    0xc4406550700450007414030700c00320350500741401450060800d0202c80102090301d006000034400c40500c074603580200d06400c0529102d81550b031418000e4100e0385090303040590a02c10000a5250044210f000f0300760320422100300d00e00b09204006a610076864080540d0503d810f2181142e00400054181d00c1d040340d103002e40d6035502004c41c2842080210113040541072800000c141f00e04058891280c400141090125603a092002e6065130380d800d0000307103031210007401006121120030242540d07080514100103226050386841d0300d0414240301d000750b507503400901841b01d4513041004108003107049060328185054440083e4545500b100050000c0e01120002604400d0300c80d40c407000150322100070400c6009509000301a0055400111081201c0c90880c4042c0e09054a201e1a49140780d920b24061a00304441120700c0c2d00b01c4044c258166400344840000210140042100803102e42c1c010201c62a00c6455010000405400c061850300706c41107002903c03513503010850640380c05040c00c92 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 276377742 1250 276376492 276376519
    0xc050906030c1e1309080a09120203030d020c0a02040e0601060210060e0708040302030c01240816050402130306050108210301080304060810050907090326030105041d03030c030a0c0804030e 83
    0x440d103481380d2109542042c40d1028100801c5144005000c114144e40c0d900b00169460340310034074480601c1d1001961550060042c0c941c0e185160300104002044082954800140c0b58041000c1d5514274001403601d070803160062101e42d41c100240480c01d401884182703c00c5181808104034000060140700400c00010002000c0c507008004660342007120f00300800600c19258006030340491038400007000004800c00c001a03140001a0421002e081c0754a01c0c042680b030070007044000e50100c80703003000140c003056001001c0742d60703481a01e008190f60340140114545408a819815150342004c6421500510052040e124000207031016202e09091030750721511036211201d8501c1381640003c0d4408442c0f41048000d0345c0c8005135008481c85491321b82400b005400d80d005416080d401c51001900080c0010492442c00d904030719620000000c0411945046e11086425540b04072031038504010008144650001e66100d00c20840590745000281401d041d03031b0043c0180b480d481e009214480404614 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 276378992 1250 276377742 276377749
    0xd0f0905040c021e0a050606040b031506030f0d05030603010b2202070c12150c0906020c0f040906050c03041b0303080408031e0106031d01050702120c010e0105040c050906030c1e 78
    0x1340101510520718960f1245010742c02580c824000c01c0889040c00f0794001b24146041900a044443c00000d01602c0c01e0007a04060f00ba00d0b4030001c00701079040c4200300d008481414180703c000100382c01c990791280e903441c1120905007528411b0a034640120555400d004c00d1806c0c10460381c207000303081c0c1405aa074031034904284c0600c06c2190403900100900e2610102001034802e02c1c08442c0007560024080030400d0241518806110300c102c00260300040100301d56450f110800b80e141c2c15008100140c400f92a0325440101c59040313030016001400001031000380f040e808582d410101d000c80403052414110340e8000c0c003110014000400b490004400b248090040e044d110030a00012803048240e50303942c180041c0540741514000c1d50104040400304030102c010300500b40f00b086560010316900c42421040c19140e84110003003032031556144070190050b0400c1c010640114015a0003400240c200f00410021b1040900158031075841034030b0034941e54407021804070401080102c955806008000071 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 276380242 1250 276378992 276379003
    0x30902060406050301061d0f01121104060f1806170411300105010b0909060d0f24020a09090c09031a0a05101d1b070f050d0f0905040c02 60
    0xd500000c0464007081c11070b80030b80614101c607002d5070790010701840f41c90b100540038000c402d003541000d102c0080b54a19401070140c8055038040400020312840010206855500640c110f0b034000790091000548041d4803040c850f40d0028004102d9a00d41d14100d03000d010444442150005006075400040500980c0941c100b0411005421800f210928192500d00000d15440905040003448034460340f0110500c60030381a03c4212012621b4090020100603c4803001800d49501c5480c1481940c0082c4058040c01e54a1b481500049004031000c801c5444c01c4425200c0702c81558418000c180030154000c640004960504d280050031003110786003111294500d0f00050b28491440782141010804000300074811046904200001d4a407180407800e20b0f1814440d508003a0b0706664112080c0c1603050b8401d17001300000b2207065250710040c0a4084980021400f41d49003040c500f12003080c043c080c011444005514540390000c075011042c060712080f840d029042c0203e40e00c29049003118020082c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 276381492 1250 276380242 276380261
    0xa0e091e04050c100f021504080403150902041a1c1b080304080d020303161206030b15130513170903030c0706090e1003080d090209160305061801060f03 67
    0x30358032498505410a80da80d41d0f20103628034040c1c0c00c90014401c10030300c00c00480703101c6a80795015204c041e002c600740d200c580c1d00140c4280c480800807c0008005403014906030041076266802141081d01c07401008211192410652042e078400c041481c2e055440c1d01440e5542c126541c8e80740c3e0b60b03020302c5c1008041e8042c0c1400c108110100074a0104c4c400310000054821070349580d007202e1503500c42c080201c0c2c0f43e000542d504007549056486001c0703043e01490f400c2a050a00903000102144d4a4403041010710056449800c07900401c4a5202c450400240d1640c1c000784818003403005092074844e110380315505e208007401c951100072120b44c50114120446a02030f034000c1c101c07601c0d403101070740e040e403548101d12440020407812100041c400c040144418801e4030b01c14001040d4901d1034664100a910424412412607564021500165a5090803602803c90410344c0d036061081500701a040300c3c40600344070b1098005014031600003000f02d900d581074030135510b48907156800c01c0c84160082c4ca80200c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 276382742 1250 276381492 276381541
    0xd060e15100f0803041a031b0f03070e040b091803040f030c0f06030b01020303070c0503090306010902090a0911030606071b0603091505131704030b010e0a110a0e09 72
    0x81800101e01d210740e40c600642e88101021402182e460a140303503a44034603c1041c0c100d440401a25610b108180c014540c131405071002c0e40e2200d40c400d0099035042d4044104510035070030200078409915482607030013030030354015034007000118000750006101c50070041001500c1c2c01c281071010814a011300540f4018081602c901106e240c036403411140c2d11005005588514500070400644148240180403c02806030050b5265444c4c11104642d5a07908100903500e0384410010900a601d003005064001d001d25180143c03180500320401081c46280e50109030078604011640042c022030108880e005403080340e00513030310100c61910101424100340341c44180c0d0350744040081c4142d05a0000d422091245290014810b0b1100011003180d10076a6a03461440a0619410000d2445e91a450040c14085e01050425660350b480c3e0401c2c68090700807518074a0f508007408440500c3c0d00540381e0401078103401904003075144400620000151030140c1c4204c0040f000b2845e0700400e820b03007001521051 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 276383992 1250 276382742 276382783
    0x105031929130203010b010f0c030c02010903051911061c020921060901181101030509011d0313080721110d03020c0a080f070b090a1203210207020d060e 67
    0x14007100580704070310900b03a001c1d501b0103c003801c1641c42124001c1d402621600d451200820544044942020300c641c100c0c18490868800b1011542c03c1000e490100501143e901850300c980c9840111115401c2407035003d154103100011000507107840d9403a8141003440010b0300caa18000010f03c0040d444140c0780c01c2026414400501c40350042109407107075003004001d0000c510b4140407000010303813000700a019164a0458056158444d801c01e6801c01495000840c004400030b00e0040c2881c1c4107050000541d00006502d41c0c411203201c3c0e000014241c01d400303008281d141c074004208110b41095401d031081140010031040100405048000c03c202805104140f0b070300f8039000c1d40d00c00120301c01a00c580200040041c00300000204451189000710252903214a40a1504441c0d00b05811050303000107410f00100f8031080d4440c0c0902c5c03050203a03455400d0001d001e001c001c161082602d0020350035004021040268484144032248503601140020b1800350090210f801c01161589801c00c0f060711 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 276385242 1250 276383992 276384001
    0x906140f0a05100f030e03030105011715030111040303020709020c120c281406010303050d0906140f0f0106110304030b090109150c02190b06010f020a06020f0a080105031929 76
    0x104c503402181403003549042101104403c0c1240c3e5901092041c540051180300b205038008200007884d64111012403400e004035201c10740080c3c03e45a03504100c21005c074000c50100185541002000d00406050f1021468601d800c0f0b800c9496a40e226400600c400002441c9034031440100004500c00c3c19404510150368400c1d00410200340345a0410b0360880c00491a41684c45408560681203c1e8140c8481e072400300941c026070054040d0000590340c00f50343d91600150010042c918a1081100301100b10b02ca01d007101d00c805c4075800c1a0401c50401c8041e0155644c1484000119019243c000300c0c4423401c0d50703451101c1400b40000d50750080c6034400d17a0001c081c111800e900480c10070001034094403c040000600482c0d06544100d000d407088641001003080d5500500300400b40c03001c58030545240c211a61100b03c2030f64040407184540420003d002d2081030f038400b651902500341180a03001d031720580c2c3d000019a13200ca03080502042c00ca095086045e88c034402100c00e010401c002600c806151 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 276386492 1250 276385242 276385247
    0xc05121801030b22060905010914130b0a0225030201090309080d0806130e0d020307020a270b060d060801240b030c0a0311030901150906140f0a0510 65
    0x420340e08105081516415560090054480350000901400040d035007407003166018104005440d490743c1c0d96104003180129050060303501801e1105408522100502090700070010000d1408141d40c0d00c03240554000340303c00c2c841640054280d14090b845030b881c283d10300882e0b956030008058a000d0210501c04060f019080010758a0080d111004106d550b25503094850601c1840040006c1e411070020b00b4901d0940b48241040342000d500043c2c1a9114410b5840c052041404202503400410030f80114074200403030360050309500007900d0b00380410410301c400308172050010700611910741e00382020a403141410b603804c0164505080c084166500c002c05c0c020804102d010315041c00891000650032400c172005021282c09800340d510b55500c0f19600500780c0c0000d2074a00426803100f10340c2480c240c2140c0694001c8058000001700004140e410030780200e00381c0d0080d840d56003070060420603242d407074041d54a01c0e00181c0d80d2712000e10003e40020105402c5070000c950001d40102511281603 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 276387742 1250 276386492 276386497
    0x9070e0a0b09180607080105010f03020f120f041e02010c02040e0a0b070c0b100302030703200d0b150306090601060f110615130b060a0f030213030302060603010c0302040e0411010c0512 81
    0x82443c0a903111500d480c5401c03504808240110b40c04103024000030100e40d0321aa0060207148250803009043c119000048150150143d070010309801300c2c24280000d000150220228100a918aa84485400b0f60000c2c000340f10020010b8826035440310013031130b41c11051040050103540080302d4041c074984013002400848581030107580c0e00030614001a9120b00c0c0420013415680c000300100150f41c55907913080004402e20194038220640140c0e03200c0f15842312000752020071b200381041d0300c5c00d1030144007981503060800700e10303840780c0d01c010141f20040354081341450548449181488001c040711b142901e9050501c0642c0c00144902d20811941c201c8102200c101c1d180c007245c444c0d441543d005054010b032000f0745c0c001540a00108041070b28680a807114044e0120395050250409521a44008000d0556071058025800c80420440c99240a100702301c400b0040d0300701141006c0c100f918680200c04000c1004101d0740010140408982c099201c2c01d1040d075000040b511707020f004405050264 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 276388992 1250 276387742 276387781
    0x15090c0b0a09050a050307261f0b0103090b31050d09050102030a080708070e0613050103061a040302151c1406040507080f04081605030418020309070e0a0b09 69
    0x240d032240040391504e8600c480c002210310081c01002c0c04c40c1401c6444180c2c200d640001c139800f11501c85c401c0d600709070500c5031002c1c00002c007034402500940f8005103015603031070120305410145082040c50004200e24042c503000107540900702500301d140b54107540c201d000140004840b220b201000801c1010006201c000c8444d25a6614040e982da0b9005a84e280540040300c000710300d40c400050601c0744030b40031a541c84141442c1002c45481c5010200d207640d80300000b00000011003e4060100e56054003926000707000703c44080340302c0408000c0d800001d01940c080248604610a40e582400d618082514045140c41401c4201d0181041150000702500a940001e955202002980524040c420b041c82b5108580702d148182e551010b511281210040044a040805100303424460b01d42c2294004224400c1004503070315410896a20b5002460b9000b26012500400801900500c0130079080111011001401a03d403601600071014000b40041c00360060760810800c504c0410103500c500e1742 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 276390242 1250 276388992 276388997
    0x6090207050f0f0307081602090c0a03050609071b06060b0c0303010e01080d090e13080309280c030f06020c030d0222050901170106091a10020a03080415090c0b0a 71
    0x4080d41c000c243d48407075800c1800c8501c1c0d0000e2140001141c448401851b90b04a50a00070240303100ca60b000812141098030f21562031440400e60050322501841056040300c002c91350300c0980d00c0c181e5001081070903002d030f03690202620340100c003040084513000712002d090007150840c0c0740c1d500540c1190fa20f402c2441038000c0003488200000d080388002c6408400c1c0d008507980d4200c02810310045001641000d040c82c100513841140e040046400d410207103028500c62005800900c0103500a410402c403050848010320781c80c41844000901421154000c80740d11200742ca00d121000d0504900a0060100b220468000000d0703015a1318400c0c0d0003070500e0030044040c280c0c01c0300c0e50003601803901c000780233441d004941c80006109140d9013200090715500b0600c0080b44541d100c541c00015241c000788240704806c007003020304507a0320340b5003071003082448644010804040d40741c800078008a0301070406401e0180c010450403080105420004502e40c010001030000f0399282500c100c90b034000180c4400 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 276391492 1250 276390242 276390253
    0x120a0219030803040f0302030c0607110d02070e0a1d070e0103231203060d060207060902090c0a1d0a0902031003060615090e07050702100509011218060902040f0609020705 75
    0x280345580c08405060700c0c0c1151407241141d03690303501d114001901c403605034250700c03050100441c0080c0807c5100d2003002c0640d00d051035030484441c038a140200b40b031040015074108240622031b4500c401d1109a0010a2541c003141800c4480740e81d030320019000c162804035008030007003c6040694440143d04032481810802000c26268043e030000061088020209030008041415803620501c041d54100310010043d101c1030aa035074a4201720380c00351000311501c2da201d269050552804014169015580308040c41c5080c0c01010001d2607945140450b05424000010850880e01c0300f00e0030070050300e6503c000319500c1c140280c4541e00c040140c80f040320903d0401c41c1c08180d0801924401081a00c1900c07030391803090502d20446088807004103110100281801800090394400d00380107442401900c1d81d42c0d40d56040000104044681082c419002c0c2c10201c840b40000b1a1000d60b1400c0ea0704031100007488401131000030003130b0148000039102d0604003040484d0040711540202002407280e4202c41 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 276392742 1250 276391492 276391519
    0x2130e10060e0708011203080603240f16020601030b0717040308100501030605060909130203010204170105060a0e06090702070911041e0b300106050304050c090606040510030605120a02 81
    0x460204c8240a5500461121680d0b100005d0003441c0c00754014000600b80e8402c8442031f0354113400c0f4176141010121000147d001d00a04c2040c8204003074010114100f070502201c810b080284d6101c0301840b004000b680d0710000200880c0c4207003420200c202c14034a4020b0b00c8e00701818010102141660b050842c0c0001c074200045560092144008a1b2070161030141441c540008000f24200c00600e070241d1525010000c50043c0c0d400e100500c05040c2e0410070100c950f00b8045607d0031190300810080c001d80300c29400780401d42c26010115070041040342c04011540d1110310480c03e0903480e5100032030a0341000400105000e041c0050026103206060148503200c0b1855024240540c501c20100781d520100010090a450f00c5c0d03120350745d5491a4100381001c0380d0f1035180c1c0c030000c1090784150001003010080c07100b00801441400301c03c2c2e20441c1c0003a02401c14000180300c0d44101d229607842844000d000104043c042e400440c002d2800401421981681084603a101c1c40e4002e4102e1048241600382d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 276393992 1250 276392742 276392747
    0xc070b1023011e020102160305040819050a201905131401090b03070e0405060402040612020a0603020c01150308070209160504050609060f0a110705010e090402130e10060e07 76
    0xc191944140e4034200241c00100802c0c009541d035841160445d502042045081c540660b82c140241d8420b40e21a035030341d403a002c6084d040034240b03003000b200e0010692001c00400c200007404130300395400080480940d2003209200202c444500d80c1e4a4011150384000c4c820b521101c0d084804846e815240d00a02d085d00458443c2240e038050244002000080c005000f215196400600b003c00083c3c1100c402d035491ba03150f00750050003110b04640c540d000604000440c2050f024140042080f031005200e510030310740c0003c030f114411740a84000c0607030100e2050000602500304c0018100d01c00c14600c1c9003501d0b414030b801031354082c04040e80112080c4011a080b01000428820000c156554145c1070a051004210059016611881c2d10070401d00c400d1041d031010000800704550b25845902544016141e01400e220499000905018217418040c2154403501d404640c1300d503040b9114200340e810f000d112070044c0b130301501c10000340c0301b00050360f40c00b43d07070662245040c0d440d849103044840c1d882c0c5004 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 276395242 1250 276393992 276394049
    0x13090506060d0201020a1419061a01030b0306240d060e011104050904030503060105040e1f080327120d080708160e090411030115030303050c0a0c0b0c070b10 69
    0x740103070b10501c00c080200e00304400701c0160994403001c3d41c40248e400c4103883e007080400d11003a00c40c2603881038416204400c005400340c03000000e08090040402300e10009840307010050412880c04005038a401c08201c00d66040744891344006c280c0f0001030b485045c000010614855148003e61801a601c0301410b043c0058800b01d0700010502c00307607650fa42d030b4100c036140c00103440c07241402000c1c400400e4001025060500c124101c840d0a403109444155109a4802c0d42d4000038240d001045180901140c070f500114011444298505110303c03101b001c00e5201c860b6003480030785401486420500181c0c003a2000d030289401e0b90314030390552903e080c51000fa83d2802c041d0000b0030314680c0d1415207800c1903556150b025005034034920102034a900440d003034070038140140c9106a1002000d104040e09481065001303e144071301c0ca801e000c600c20b005800c00c3c0c11184003030408805200000c2828262000303c541c42e5602c040d91359407034144686542000c03c041d00584401402007031507900c5030320807804c1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 276396492 1250 276395242 276395269
    0x10e040b1504020a020a1b030b1303020309130b0102300c070801050a0209010908010606021f24090f020f0f0714070609210f061808070c0911030c07030f05091309050606 74
    0x8521f42540701e0280c0c0c4990ac05d03002c64124150f000621103503c2640d40c030f290103c5e480b03011800104480050500090500520382c44a074000d5048203414407120480810b1028501d04000c4416602d240c9501c3c020701d85012540000420f41c240030802150303070200e230050048407000b030301c0c2d40c140c80fa11400071a080e141d6900516006900641c101001e462980c00e580c000704241100016005030a1010000c1180f40c001070300804112101c010000c12189102e010700b8640d02c002c003103003490b0007240c0c01d0390184074030075211207051004030300c0d00284410510541480c080240499004075542e4001900c5450b0503ca004a1090500e408500a40c12500140c0d6040c2d8018100a444440c0381c0e2008000d200802d03c244500b1003010182e0000f80080c0d000b040f1080c000c44400300d07400c0c601100035069401c81610b00f04000c41c14401e0082c1101844140c0350b00c1941400d10005250003203800b10b45600589100300e0b4404c402e051801145d48207070341b002c8070a40c0240103440c0c15668960901294030450913 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 276397742 1250 276396492 276396503
    0x2300f0606010f0e31060305060c042102040e030414030c01031431061a0301060b03010608041e03030b01020727020c010204030b0403110c09010e040b1504020a020a1b03 74
    0x22482c0900e031403511600740341810460445c203032044459512803059248525080c2d203039101810310600c202000b145a1100480c40c00c0c0c0e107080d04049a00354884c0e4501410307030485000d00c1e008021540c8036002803000300141005c0320b03140c59a600d5003400c0300d105514050702a0203068201d5150f0b502c05d0151030b4141d01d01c603154000701d4039100c114000b800c91804004005000c11324040300b1001c89000e00003c0300380503000101d04090441540e0f01159400640c40784282c0c906803081040d02020707001c3d0380c111344550401741c0c110394035030803d1006444200024105551403008880426803d80d004510030503003030b400c40d40c106858660480b081092450040034a01d2020410140030410340c00620111343c10f0300015091556039581c95010850640e400c501150740c5a03005182194200402c4150481c21900207845514000c50200c80e50000340010b0460703280c110004031540700c0c0300070280003d80d0207031003195a252941c00c020348403164007008550402030042e4a209944007000074009503038008 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 276398992 1250 276397742 276397757
    0xa03090206071407170102121f1a070b010506091809010204031e051e0c040f0b0402070303140c0313030e121f0605010507050d0309020a0906150e03030a020a02300f0606010f 76
    0x4827005501c1803840011903044110000d0204031501000c01525449000c1002180c440a1790b01e01212600740582100c1c1c01001d052045114564880010000c20301604002c907400d500d5188800b406880386420140c841082c6000504080c1e000c846c040901c24014425154000c5142d841140c0c02ea06e15109240d880e4005180c0c0549440c0940c800e40845800740c000188440350740b00440d09a8020310000e0300466510036191030001c0c940700c42964040b103641c810a00c1c7d45081e18440f50304226000380a020061043c0c142d1400742c032450086044500c00004550160102041d0544142c0b404070042c0507260034880c0020701c950152044c0c90416074418058882809088411401001d888000340d0b031144e1131040020f10b003c03052080d84040c2041604070104034590b5280a001845d505000c0c40c0660300400c40098255804a41d500301103034100c0380286d05981400140c100304040301d0104e00004480e242c2680c00365400200351001f0581c3c20255038080d40d401005503140c800090110f40402d000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 276400242 1250 276398992 276399001
    0xf030209090105040b15060c01050a1a01080106020607032d0516110307120e1c0605060a03081c020405062d120a050916030b09150c0a0309020607140717010212 70
    0x22500e4a140d0f90016101509110883d1480350944006584845520344e3310b071103001d4000001c411210f1250420f09260442d545400b4000f5601c0c00010040020950780f5000252010b00c0512071110844440200d881e5181d071040e41c107801003000381c0d514025004200e030148200b500800c040901c03643c0c0580518100009070722000300c3d8880210949040015242c1003000310395400f0007280d10180250140049c0e44983c2c0742050441c0c90103048107205503c202001c000203042842166403210f1a001305030740000701c154414020b809107820081d80300402054102140301c10121000300ac0a15241d841181c0184c60a01c0e01d0a10a1f00844030207448108006030008049810080e04518244119903503a088101607200e036101907007040358040c0f0752005002d0001400c002d011100c4040d58020f00c00f50400c200c44009a100700040c5400341500d900c250b10030340d600d11701550748003078104107c601d0092442d942c4544035203003030191101840b5402003044441c0c01c14400d84560380003003400c02a03a501c0c1d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 276401492 1250 276400242 276400261
    0x1a060f03062701090c1e0e01020109060c0c022704080a1112040e09010606020d1803210225050d050c0a080106050a050f0604030303051f0f030209090105040b 69
    0x4000d00007500b10740d5048007100c2410030407540b0340203101e4041d2525865410401c00505940070026200e04009014a80c074640c590369440b0168020742e1810080c1140703241e040181e0140c440b0a001800d884d02c0c1403054001c032501f141e00f48040c0343c801c840a5484400210f07400c02c40e44202c06405052240040002e0000359109005003001d0103181402c1c42c0c00400c15004074940015045074090400307000c20104603503c0007844160300304040f907000380105420980b009513207084031a130072400c00000904000c40c28103e01c5418020715044180340ca0010010003103075030728a141a01c090014231030b884180c3d00c801f00202c1c001d040300720b01c81d40c0c0c02c40c1c0515110070083c0c100f0400105603228010450394140b90340e5081503ea00514038200081803642ca000c042041c04c550f2644101d0003101203041c03e41040c1d89002c100e4040c1e035454100003491707071100b0188141551a9014503002608581e20200340b00035152801d0003202c1c400c9038089034a54441500900fa140250340042000035550b012400290 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 276402742 1250 276401492 276401497
    0x1e0503150a0806180a05014104080d1e0c140301060905040c050409090c0306060506161b03140304050f040212040f030522290d020a0507020907030f1a060f 68
    0x16404c4c0844c1c00c0004982c40d503c1c2120f110b420070420304003442e4800740c820002c3e000508241d100e24624a456640040108081c003940100000c1041500180e0b002943c1516031101c4a0b1400031200383c0d18108009031600700a01607444800003162140b0078800545400508481c180c07452951940c14091803c414000a003c01400c00c600348101840701003200f5403944140461140111340600c0d01d1451800d05108603030a94103c540240c10400110260010000f0102e240c26409a40c200400080e10745c80d5601d5282d50308000c211508040160925420020245c001e645088030b041050050307035000c000880c8901700140c002ca041c4080068085944a503049158a0080c18220300d1310342c000c0942e80341852a0031101a14400c01e400602110034040d01900b0000e400740c5120203001441a0070b01c54500490f001001d60b40c2cdc000644120940c890f50549e00f45070341c0500b8403640790418000c043c0c0a080744604240c0c1403803800810007040c0040d8114416009805440345113000f801400c114150f6 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 276403992 1250 276402742 276402781
    0x16180c03020415080402191a09031504080d0609330e0a0e0f0c0303070f17070605090c010f080c16051501051e090105010507031e0503150a0806 63
    0xd58203010001e80d0414070241a085520f16954014991a2034410846640340144140030949604c000c28840c0090000200d000310241e00d80c0700f6203413290703080001d14252800c1030302d080042440b400d100c10041e03000050b100540543c00706009807070321040d004040352a0000c00000580130359030f66451007401100c2c41003046200b54200d0154035200c01101f80020700c1500c0c003138038440d501d2a0b412080340040c040351200d425140c001d4100300002000203582c0b4054175030050300320740401241c00f080010340007504500003404100c06444a516007014001801e01301e0f89212180180c0d040c0850300d600c607851a02c0303004038903142e42d07400c0d031101990301e00c8541144e15201a000d08a40301d80001c2507080010080b00c807006021010150f0520041c85240c0886180030a4002da1401041125540b99070600d41510003c0c6415626552141811502c001944d40034803500d00d107815041c1000303507005e001144240d50b01c41c16501c5842440e01032110080e0203101d50426030f001031000c282813500c006000d0207803 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 276405242 1250 276403992 276403997
    0x1e051603110109030509030c01051c0b03030d1b08070e090f060607020303041203020120040504050c0d0906060303110a03090b031005150304030e0411070204050a15080a0516180c 78
    0xa01c1c46410420342101c055401c2034010840200f0a6505032404000c1c40c1c400071400c0c80c01c6401d0119664a0740c202c800350242c080b050644401d14030327495840401c161144040c3d0000103003d00c6080040d100d20986075420320200048284001a5041e030062006000c8034074007801410b0140d45010040e0058000a0a0103034413000c2008a003015a4040010380040c3c58521017501d111401c0c4d00d006070031600703000c01a050142114140f10011500711080e102110400e0301c001c00e66549074100b0f22068410301c0c00c4440304034a04030642e4280990ba40c010400c0d6482601d400503400300050101d0342c0d406401100900041d07050009003c001d41400195030440c0306c0000b07454516441d030380011201da06040800303580440c040108802d140c1c2c0072111085182c0180c0301044203500294100d0100d10500c08040d0043d83c40300045926180310754001200c80c00720b010b414040a41310003c99171039804000c020359007071107401c1d001c1114080e540c0c922011250b04481165881c1310420750100541250a0103a09 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 276406492 1250 276405242 276405257
    0x3110d050c060a090906050906130e1f1e0b03030414030f01020f0c0c0f060724021b060a05060d330914070609060507060902030f010b011e051603 64
    0x8068545001403c24a2096103445082d2030515034044122201a4802485580d08100340482a196981c0001065400c82d8004c0354050290b0882391412090880c0c5569060642905c405002071660140100c80390020510003a00809072640042d101c6003003c080e4141c104000c10000c400445600d0784030000c024083c3e41c04a4059040103089030040070b0401e1901c0d030001984805003c060101c548508411182d100d86101601c1c04604940100c0344020800341d48007050999100b0007070b40e400f00391100204c083d5038030f018102e001300124000400f1201c0034850030010480802c124022284109006480007800c9031180c3c4511034640d1f8081c40e001061201d18060301d00348100300c500a215017590b4180030070403010724030b814524500390209106894100d000300348601c40c0e010310200125400340c40e050f6103904660500340e004140d1084020361501c2440460059208190002e6150450989910010300140d484084c169029a000340000400030492000c561400b050120400d502a18120301c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 276407742 1250 276406492 276406513
    0xf0510030308131a0c0301050a0f03050d050f221823190603030314060d0510200301090b0a080601081f09060e06090601061805040c05071b0504060902030103110d05 72
    0x18504c0100380c0d090503c3d903e0000060089042c055286401058441400d144c424916150a0303141c242e000c40c0e4074100400041c10461011851003652101426401001d920f00380803440c0034640501c600ca200d00d498042d09480001c005d003442540c01e0880000740d06a4500300006100350702501c01031100025080c20950070051050900c1004c01851080d14000358641c48170380c81200800000708004c0c4180040003040000940c08110380c21510030350400891040a0740424250886002d01e0740c054091022000092100c0c146d08401d14100b001d44070004400e40341c1d038005483d00d009000d55082903102c1c0b5201c502d004d110700302000b007010400c00700048044042e40c800042d9031a0520400f015445041440144034041c046280106918106140120a10258245042498070a481c82503580d01c140702c0f00c0b1070050007203a0415a00400c0d00d4954140c100050440c20302c0c40c02103030700462502c400883c491859208482c141e90b0089440b103200c0312a0340800034400c0c1400ba0481c0d031801010f0103c5d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 276408992 1250 276407742 276407783
    0x120e03071506030b01170307140c130f0501060203040303020316080f0703021c080610120212010b0a021b0a0902030402040915020703020c0306040305070f05070e0a0f051003030813 79
    0x20341a80c0780d07400020503000e140d07040c0f01c910401c06030046070024845000004c45140008221005194401c5010103480c10600303086051400e01c603c0180c1159400d030591403010707103a0340161103100014108000d1662104405c036502d00541c0401800b580c0100112500307020000580140b0500c51201107240c4001001070700016008400110301603030000010f402038201c3da5401c20726810540c03800c40d51074540795000900c4480542d10035401e000c003020181e10b80c0d0b100d1744c048a036011140003100416503940e11a03082c0d103a1182013800010302684461204180c040c008180c65410014054240d043c01c0c1003a04000307600c00342c0300b03d9100c1c1da100c80d2040040c0c1c0d40425054480d140101c01a20b0380308509004e8100001d802c01d2500c81d0f0094810440020f410a040ea903400f0381260809841a0081c0b400c0c500c1c100c1143c10010401c81910f040060000d0107800864001c00d00600503c59a142c44c1c600600702d4503207010040225100a00050640380044102d44a0368010070340300801a0084101 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 276410242 1250 276408992 276409013
    0x170408070b0d0b220e030c0d0230030c0a030f0e030301091a060a181a040f080d0e01030c03060302131506050f0d0203070309151b0e01120e0307 63
    0x1001910030086402402c202091040d400b00d440700b5038400b0440200c03c002d03010240f040c10351507890943d49a05580c0c44420070003e40d1540c031850811078101c40090038000e13545034903030650ba8842c0384807102811101d008100d0000c8c0142004441c1505645905d04059000c0d00400300b007000700740eaa04002504904e6500808c0062007181d80599565410062030005460006a18211500c16101c1503005a1a2042103403094180e9140c0141c82801070a09040c68030b800c0c0d800342c040590301c1032900550140400007002241c4450b90b4000c5e0325582c50344806c2e2541c10310005100403412a0212001e1940660000b48c0407030460b1600040b041c0c1c6a130700280403940b102c0340c12a4640c0d69003c0055100c003040d003c00014280d1414814140311402d0b045088511444041d0403845070080045400c49020b078010201c0703a0ba01054100701400e0455202e4002c3c81c68042004068000038400c0740380c01c2c041c3c000e40202e501c041e5140902c0304c070003494400150084000002c402d00c8100014004145e01160 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 276411492 1250 276410242 276410249
    0x7020306040c1502010603020303031f03210318050c010f030f0c081608100303030f0b0d03050304021806030304050904080f0309030c060a0c09290d0b0102010501080a0f17040807 78
    0x7040402d5401e208921407400380d0803025034107583c07500340c00344056a0000300348e91784003100085070701490140e450700c90203400c4035a00043c031074003411b904056448210f181c40c21140c005564104400301881000310345c402e911810152494215030750188070f951180280b6603980c03840b800e001c200c0d84401c0b12104101c070100142000019180c01c1400b028000c80000001e05c080785245c01c605078201052113541044840c40010281640c4403040f20919525070029060540300030a1492090360074240035025901c00c840c00c80c032a102907200343d003c840407001c1c450300441010300158102070920307082c443d540034054019507a8100502c0010018202d0b80020f52041c81d001c03003e15160403e04000c145444406442580c02c1420721810700c210341e51100c000c0341226030407948030003821441202d0803101d0525019402c02c2000c00204110035050315000590908400e074002c000d181c1e41c40410a07241c0300005002400c0c66600510000420103000603412074407000c5a4003880d05698014040c075140c402ea0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 276412742 1250 276411492 276411503
    0xc030f0703150e0d0813050601150324050607031107240809121b1203060f01020c10111f0f0e0a0c0308130315062103020d140702030604 60
    0x42041c010041c60b44684110036150180901003108601c2c0e02c5511021801d03407060800403000006941c0c048201b080103003070b68014003580c1c040c0d6140c011001c200c1e82d038000c81e4001310781050b240c22092040031039020a881030000b41081900e00f44802c00209910050080e01000003c1d4400c1040300c8051000400524201804422208104c103062001c0b00a04500340d040c810441d0070882c54180104004420341c03061001c0540c0e40072021071000180074205d07069041441008260b8070646000c000550150300100e40300004126a40c00490742d078031169610700d400c1001c84044034146401f503490601c9801004098030408205154503c51381981c0341c2001110a07100ea01d10840300c0300030b21854800103180e0016241032580c1e0f44034021043c981e88070080c0140e0340000c4004c00c440c1c4c0c441451015590000000000805a50700721015010b10b01031100d00c503800351881ea00320000d006c450242958103401a1420403086441626052000140b600348031802304125030041e9002e00025100c0c2d40704e403 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 276413992 1250 276412742 276412753
    0x1b0a0c0b2a0d0b0328080c030a0c0203010b1e0d080c03031306060905010608060108070207050a080102071506030c1707030b09033130141b0d08030402030c030f 70
    0x880344801d81d030101c0c05041c080d801850303041d440181025411100b18940f040e41340c0080d00e176450403130000d10840050a500d80000310315103800c2a1720160f402101d0340210020301c980780d074144c100680042405c01c07040840303d03c0100c6421509040360150036081c021440350341000d01490101d0308591080781c040a2130314800ca2000c00b08642803281d10b0180095a508010b150f05000010b802018007400e094144140c420019400901c04c2081c0000350101902101041e0380d2401710901030b400980044403920024100d89080c16058481d200803241c00c21100e503440c500c4c05440d035a00e0503810202040c14040c403200800442c0700480c071f41d03004141035001541d86610000e440a540c8503122311440340c001060f401031100000e0503504005446108600050f26003001c0d01031068991301c00498807181034040310301011700800302c03410b03195024070200b07854115001c0001440e0003441e0f04240741d4032480c1c2d009090040744284010390740c464402340c22180d40c03c00c040c000a14100b1560020301140d07122 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 276415242 1250 276413992 276414007
    0x50910020a120e0d09030206090d060c0e041407200c0613050f010f0e0111010e0703141005091b03030d0e070f09020c10090309031a1b0a0c0b2a 63
    0x5110f511601030140014024054060100404010585c8806071007001d0102d42210b03507035200e80c00d180c900340d031041c03041202c00985030b409000b400000714428811450842c802c1b54001c10289507500c030b126542c3d9a85140d001070340e01c82180c40001031520210b0305c5129001c1030251629401002c04990802040001c03d03d443c4c10489080740b41c0700300c181000015501d55101c1c0382c100007844030154090a190360181c140e5000300f801080c0554580c5118410200001300384500300340c0d00b82c0500704c1c0750203031142440600d50050540d10203031400402e680c00306c0340c0b5249031100c5400c030f25216440242968904580600c44005488204000c44441c2e08052402c04c602e0500030f2881c401001521415410250156840358403072243c3c891002c141610b0341c02100802d0b210310031880c040c540c07103d148450304540102020b03034101c044440803100c1c10440b502100d0080c4510559401604554405a03002c0e0303203985900c000c80024080903040c2c1454644500f101c0414501d0b080d0300703078210220035140c4030b5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 276416492 1250 276415242 276415277
    0xb090309041d0a08030c0f160515010b1911061006230d0203130b04080a02280312110c030c010506220e0309120606030f060106050409050910020a 64
    0x207010b203031003507901c01c0140d910108000032071158815908034812585951310a4580c409034030030307000740580da10300c0090341104c1d0340386131000580c49130b02841c21141c2500303401552101a010138040e1415420080c04140b100050300a0070305003512035032420041d9002d401c21483e20b0a00f084d42d1000704412610307828010a9402000a00110f0b00c0e8441008944448007007060381d4030a0001c540c04207500040040c180c44e0b1200d08004203540d02180083c090702c1d05050000090b080104004018002d255040d82d07070725201031010b00c6060018400c801c00a00d5aa4203403100303041240701c101c1031502ca509040b10079050101070520300840c400515a41c0744042440b0742110300041000b031084000e014010002d500e008014520b90f000c0362000070303001e981d0135034513461400740e220019070140030524095604080030840c240a10010b40c03c0728482000d5140c80d6482d68400d004000c00600c040c0b20410402d13500d908010b4201d1805806e54071190400c0c0768010680e80130544200c08910104a080074201 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 276417742 1250 276416492 276416501
    0x1501121e11180f0c13060c0f0f030804060507020102031909030e0a1211120c060d02121504230a0903090306020c0607080c040f030201030218030d1d0a03020306010608130b09030904 79
    0x310407001e141c0350500c904460561103000380031b2003007048800c080c0c00d401c0007030205014841c02d070044583c0300441c1d400e00c0c000b0003024086074221401414a00813802c001c1c0140240c90046103015070a901c20481100c0c81002041029015410401e040894100a0f00d0300078081018010303070540114450301d00d0034440c3c0032039428142140a08418800b0990104c804540d41d814a0412140c0c1680e61100744445006030041144500c04040d118043c810300790041142c402100303506072810b0048080420f858921545912038015280b110b210009880503015480080854420300b04100750681320f4940c82d089812820306911564040000e000340c40d5080940710b50f2013030724000068601428016002c8080505103c028181600805d03400e6440c0302d5050481070192000c0c049600a003040840100100b8118400912100c02160340b4003050a002010340181c90300540140316592a1400c00c6486090040c00d004d02c4e0b120501486000600c01450707540100340030305c01140c8a2494a0400c000c98 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 276418992 1250 276417742 276417751
    0x501050711150406090309180f06050d03081b071a01030b06030609070b0913140105010807030209090c030601030e030a0306080c0d1214090a03051501121e11180f 71
    0x394081c10b0016030104401015940c0164410004220801c2615017518440c181d5041403c0880c0031100f0700000020592091100079144d000520043d1b0b0350308180500804800c1e405070006d00820300080c4040d00850b4030040108c5030425681c9004525128000080c603851b0081c0020140f80b0010000e00402e917180c5078100104034050106810000c5407a6074400c4a1b1086410103e804107125070f0b1682e401c010f02d050015031050900204a00e540e000c25070000900440b408500d0704004181d0301d52081c800e4989508020300081040c1d02d8101800c501a000107090310704158568040c07145903042400505003e10305034401240c018100b0801d68102590141d000b4090b0030041c03062000f0440085203401c6200d500c2c1420721aa4000299180b194401d030b4580c1500203902d4400003040210024a540c0c21075040d9400c0f54059032140c070111854200300d00050101c031070002e0100080c1d0034440a0240c0288140c05100b23210311590b000c200242c2e0610003048400381c140003006450401d0080c00b6521 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 276420242 1250 276418992 276419027
    0x8270304121106030c07060b01030902120d03060602060108150a020d0e030c010c08072c0303041409090a031719050f0108100e070b070501060f09020406020f03121801150305010507 79
    0x2540f400e42d417409014068080041d100d40d403942c10811242c0d000e68083c030a059000b6214200d021524807910755200c4c042a48440040e2030000c002555600c041051816285000058403e400000130f6822490740007a2089004d5503081055400c01484c80c4141c85540c00c1002c007458484140d00c584900310f5115400040c10b2221041c10000c0140d0301c50030b100841d4003107540e07103074410488152000d15200300e40441d079010f200000f4042002c01000c562546000070460f0800240e5a66258103611280b039104010049640205148001303d02c3c0c0081903800808050051444082412070505031101581c2202c0c2c4944500018840c10a040c020351320641580c03502400b242100d4111150340740c043c0c0c41440d03d4030201060500401c0400c1d08070000410518115540c201c6d203d51344140254441d00c5040003512904150241069000c41a04c03021b1192010449183d900c2c2c003454104402c415241100d695a11501259008a00411180518051400040c2034036280b04003078100105075030300c50213 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 276421492 1250 276420242 276420247
    0x914070b0412020d14060901020c010c0e06031503161d010b031005040b01030902120c0f030a030f050f070f030e0405010f050904020d0201030e060108030304020103050705090108270304121106 84
    0x300d115075248111003e90583d0a54a030803a2414803a54070801400700702100c0c000c29003400131811054020b44040a200340080000101c240000d880d80210b440006800c500b003440090101d030369455025415240160030744144c8652410380c01c030b04001542050300c0303d4250700e4246c60030020320600c16025141c000021480c40c2030907040649080058031909220b540c07942e0103129140d2090300701c81007048d4041d208240d15400000043d4447c00c10000050052002e109002810f15000920400c3c441e015212451300914208040355540d01141c03845810070790411203000011101000042c00a000b079481c0c0c20100c100c681004142d60042c4d00c00410f1008080b070070300940e03441d8400349400583c1102c456070080e80d1840113070058517032842141524041c3c0380000415410100003103100728400da80c02c014130358411200362002c2c0940c06100e40000d00e1203000803003074004100350019451321070610012255448441c940755500c42d400c04070b11407400c43d407400d0802000d242c0e40c40001d07100701e403e2070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 276422742 1250 276421492 276421499
    0x2d09050607060213210b0c0f040b0c060f0402061204020316030501020a0f05180d0c0e010e07020f07060c080903070e0c070606290d02040806070503090c181f0503010914070b04 77
    0x281242602d19006e02400d4545010402d41c10401045405044602c400107440301c4d40d0b155200815000404141c00c54024040040d0300641c034621054421a802040141020032080c000c20264000400c2243c02d849199a00c00405010300b020f07800540c420f100247e030b5120310030740c0101101840241141070003002d101007902002c020a1101040c441500e22855160050424070503000413580200c035604085000811040340500b111403040466800f1681040e0310142040d588010751311400340043c00842d941c100243c010b4000b0405582d00908981c01c00351241c04081800c0c000740d4032603000d6500082e102c03013045454020040103013004a4650f80f42c40321201039404840e6260800c0030031a0002400c519032080c0e50b41928054031103182240ca103403400b41400750660740241c401030010300c5200010800e0740b400480001480030540c0d050245038031610405d00801a48266019900b4000031010403d61024440c4a0419006241242060602610349030500d51140c00c03440964004000a1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 276423992 1250 276422742 276422789
    0xf09030305182106040b0c0f12091005100f0503012003060a15171f09320f010608160c06020c01020a0c11012d09050607060213 56
    0x140e85507407801e0b0461080404000c0000d210503141e4240d014100c48100408841140004a0910581c4112035000503920382d6100e200c00da008558098041810403c40c1248026038400925007003061501102d041300c1d201d201c410b00340c60381101c61100102009404001d800c800000c2c02e0024001640208840310306449070301c4240038031062041e01c1c0000000070604545414465400905031040d19200c0313901d0400c1c0c000c10544600100d0f4071a4503202d0042070810400345003242041c801c0e100c0b202e0203186004020009407030802c00140c0d003100c00000b1442480001c0b0300384001144100c4114281d4640419000c829403010381254040000100c2080001c1304017013541080440320b0300f17181e540f45c10189884006889030a038285103550000c00c6091101da00010a910070754411031b0580003441c41c80004603582000080308513030406a0381030140c505103200542c1c0714007a500e4585075400588800214030141e11100c8111007840c1d0010304a48624040c282a401601e9040104400010001c201 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 276425242 1250 276423992 276423997
    0x2a03090305180f090403020c100905090a0c050c010f05010816050d08031f060e0307060203090102070918080403080d0b0102010501050901090e011512050f0a0f0b13021905010f09030305 81
    0x710610500401d0b580c145983c0c0b0f240350443d03034040040a071a50380c5414a4000d454a00c11341809015002110035000524041e112100a0f40c0f00507050100c0381d0b4030141c1090140800880c128148001000000d003074210a028580352840808008101949000c015a1031b02e8142c101c4018105c3c20014107216a03034401c00c458030401d401c580d1240d241d0b100e501115502885d40380440c07080d20250714000903801c0d00300c07183c4c260880088003507510041e0384101c26a140e205600d0241d0051300040c00034005010103a201805090601c18415a1420075940c2d52203198080d40040c1c4003003002250074680c1c0400382c00b070403418440a2000380243c0d494200403074642c40046c002e000b103142e1601a10700c0100d40941c00700000500030601020701d0342d500c403c40070b001440301c034050700d141c06200c40c038600e880400502440c9170b0358019108009690140c5179642140070103420842d9140b501b00c050001340e0b40320b51000c000040d030300c484451203034544400546181072042202c0c05100000344200042030b0001c09 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 276426492 1250 276425242 276425257
    0xe04020d0213020d060e07081008100f0b0a09061802040b0301030b0415090b010501031104080601030303021b0a0c1508040203120d061d070305012301051c2a03090305 73
    0x828a08401407042c8910190141450b406800ba19007000040c03e40c004280e814022407281c3c1f40c58001d0384984007040414105801000c4090b40b11400034401c3c006a0f900c07114075807450081c00642400080b0000c0c0101070a680082005910f9840910a43d40188a003000c4030f101e4000461800c0c1c5000002d0006010510000c0d011304140d00c0040c0c05c2c006d034a282c4c2c030380d11031074584104007244aa02d80042112401e004a50020b890720340b0744e102404e40b000458060b11050340007802107070b185680c1140650f0000f100202d80142072445030228400c00c2041e043c2c0c15101e12543c41e2400d00700081a1240c00b40040c3c108200030004090001503100414103d44981009504580e00e0303c81804042c041c11880d03000d43d100c018564009030042c00c0d2a9200760003100729035400c1c8401e0340d8800c403c0d5100c40c1042e481d1604407a44100e5001e09602402c0100400d036039000390348032a5503100701c0b50412140e03081c05d44000061460111403da5120f0000b00c043c03201c0505003001a05069103004282d405041c2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 276427742 1250 276426492 276426499
    0x207030f03080a0609020705071403010b010c110a0b190f050a170a0e0a0302031b1501090903200307030e060a0c0609050a0803091612020607030302090103090c1d010e04020d02 77
    0x42080d040f000e40000026200540b02955114158900aa0384414602c201b14602c6c44080000e030041c94103005106440b041652001d0760801191a0000362a40f8804103540c000000b00000503c09100d0014000f191a0040300000c920034681e0040c0030859000d00020812004004800016412420201c0e103140c0400840d9940c0d45d500000d00010724400d21504100c0c80364000100401d980000148003240342a406401d19107150380c1d0f041e0381e5000001000035980b461318010320400030190302000c116800780c90f201c801404510312010780e184480010243e143c0000071000203040e00626400050b032000d6a1003031501a80c000010095000c64000034422516001003900b0300c4001c0280110442d00040d101e80c0d40d0400809169607130700e50061890340d2219003440001d141c00d01d4141e40c80388a4004e0300f00ba1805800742c0e800c0b402540807003861810300d59110302210110310024168005000c54004104080010404101e00604140c2c41074442c2420b5008200050f01c0b601c014102860b4150f = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 276428992 1250 276427742 276427757
    0x30504140409080f040f050301050912030a1b1707080f19090605070810090504110d14060108030307092c040c0e0a06260c151e0310060207030f03 64
    0x25000601622041d0406000c41a02242605684a00c00c00030800c60b01074031b400c07001003959101410700383c803000c031894075854202ca8141000514494001d59004480c1440007510014004a02ca074115200c000d14001503c14241885030f8544040f010b80c2011160620010b545001c4070380025440c0b00400200590046001030303c02905103400a0750107590000e000e01c0305140c403d1004180e00340454860450807480380000842a40b036214141c001d0303402c241415240781e80b0b030040c800c0c40040c01c0000c40d1780fa55240660700c00740000f07100440c0a0000900903680d00c0c1802040108000c22980025138511074240c0080444075407034030820012003050001059a690307074103041403042c000f41e00a000c3e640790002003124110140d4030560a81d15211550004596020740d284c41e1a030f2028070310307403059106048400c00d074502841c480d28006108025140385c8054450b00c0310710240800c0ca940003e000c040180102d81c0c101c0401100541030a20040000c285507480b9000c500460704809014000300 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 276430242 1250 276428992 276429029
    0x6040c030516180b040b0a030c081003031d0306152701050d050c0a080f0601151d12030f1b030712030209010c020406120302010c030e0d080a0213080d1209030504 71
    0x700c1660f00c020301c252480e140e00c0ba6912a8003048076405500350000080c5054400c45289004a10190150f480011030122160a41d50165524080c505891a100d0011070160380b40e56010040244100a640c00c0c20408040c0340041c80700d40d030129800101c0c0c0d210302d6446d01d040d000300003100c10b045460840f080f030ba050b401d40c105076040807040000c09400143c20800030584020001e02281c40359062400c0310700c540e80e01e00c801d1038a065652046000240c1261402161504203000e010800e94010101e21102802c0070009143d540312440304407240708003155481e810018440c550801144060145180c8182030f032b1180c03105007000c4105e03404d040c3d010600c004680d209114140c011607024004111440d10f9108074251070040b104c00710015805d00703001c0080f49110340a80b1500b00c8100005194082140e10306488911006201c811100d07030030701c1721410f42c0922655007801401500c024180700a44010f009000900303054a10710b02d0f80c1000503690001f5031000803281100d022004902d90b20030b5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 276431492 1250 276430242 276430277
    0xa0c060b041a2803030903050d030605012c040204090f0e121902011512050f0c210a020405100602070b03250c060c020c03010b0f0d0f020d0f0302010506040c030516 72
    0x41d00e0400c503002c1900c1d540e01004140c0c000c8010402c3d48d0044003140c3d0074841b4800d0071400c0d02d400307001e400d0029103468151101c00d02019410117000300c51074080c00080c038075000070400b00d800030342c89000c0464841241c6e440022007449108444a03407607000d0f15050f070000c1d5900d680c0748103c00045c032855107901c580d8008c4c94400c0d0700c00b4010f0511203520003212641da5018580d041000340060707809000c0c512000c00b98042c00102d031103403e0f602810300d0342d80154441c54094510000d412000242c06191201401650f403032258900c119500c0040c2e01020341001d00003890318125070800075044204200344082c0c44445941c090b0b000e90072801e82c20141a0325402160f01480710b07800200351608100901c01c440360042040b0740c0400c415002005044541c001701305019112020b555003041e0884a0240031582005482c0c000ea40043c0017859603000300d80c0c1305103620010310802c2d0014bd54981c2404407503e090701034a080000c3c130740b80501c114100341100103010007000c0034480500c2047d1910030310208 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 276432742 1250 276431492 276431539
    0x1d060306031911040b01020d0e13180606030b01081f0f0b030f010501140d081b0708030d020408100b030c3a020a1a030f1b0a0c060b041a 60
    0x108280c024030202d089072518050808240f40890320a500384140002954400034010411240c00d0b81c864031801c4142090103480310003e002c0d11000c6480f008038079080d4100741c04aa00181c800c81002941034590b08005804880c1a0807801e00d81c0c200280301092981c503000c51040c91300005400289902051801f4002000800006601401455907801d07888806500850403079920baa6103031122440402000f03680f040031400101454020f001d03031101c07801100011070b400745d000f204460b261038a412001e0314517000440a610392503000a130910108070300384414040488051400d115450701c8100207a183c142007600c0c00d00640c203d0241e0044a07042814807a00c0094400e01444010000c66004440b043e000780207a0169408040000d444411501c84c20300105041000a0840c0c8500d481601c2005000d030802d00840b610300031003941c030481c500061001031255213410701c0310b091600d40b0109039840c4c13281c2070b44954503002402859480001540000c0f4400300d82c604100d005d420300016596 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 276433992 1250 276432742 276432763
    0x108011503060b0f0a06030905060f09031c0e120408010f05040f0609170417071d0f07050c01230a06060918021b01020a080c04060c020105090607060e0c101d06030603 73
    0x178021400024003a0709980318034103903030160054800b01d5481d20701034100000c060342c02100c1d46d0b0007000104081040c0d101601040c00300504081010f5000317000403441c0039000070400043d8540010200301245003403040c04174480f1801800e00551030191503041c0440250080903140a888012403001c1000c242c0703d050100003600c4107175448540f1010b8002c01c260241c8400700051003405000305420200950f940e0320311010000e1110290345010102c008520081c15403c1408014005050000800c0c007901c040f0340350b00c0000041e103500641e220318020001410382c610310342c5092000d0107450b900c0b10040c415541d980c14111b0303100d0700702d5450314024811440b00400d211a40304008400d400190003c0110490301d0340c640762280c492072442011482284100c0000c0390341201c10200550142020b07207080800140a41e080600bd921a401600c5207030740300580c581c1103000c81c001c10f450321a03c43c2040b4841450f0030714481d00100150f0800d2a005242c07148aa40701100150083e07070304010340b401c01c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 276435242 1250 276433992 276433999
    0x618030f030c010b010806150703120504030f0e010503060306070e2d09222402030f071b0309140f060d0209010e0609130c05042c0108011503060b0f 65
    0x4160381524003680300e400c5054142515403d2007540c0c1c04940c8a089403a024010080205103c1001480c88103001d90000008505014600080003803c6003684030380703842070740a40c64030380d5031651030100141104108a0303550705200c014401d000c5079490001d0216484505401c00e12112a03080d400180e48035540700b1243c003044000c5416012031114084038018080007900e040e4410380341e400741c0c0301140b612004400c56522128100f4000700d18200100313551140601c00b80340d08052148118002d0f42c0c803c807080e42510401c0300038440c9081e4404c00e00810600715840700c5d100a80c107a60024035800051040202148034540d4043e52030307403a050352003489070b0020403140d9243c82981e103a01c003a401004405001c14400088420181000b130100e1f4a4a00010301d01e14107011040e40c2a00242802e81ca1402041410300020811074460420700c10308182428280c1001c204e62404c500365030304144c00003041d9034105001101c542044443c4001502e030701000109800d40840701064242d215206510f52 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 276436492 1250 276435242 276435253
    0x20f0a0302100b1512130b01031b05120309090c221401020a0201120906200c010b04020a0e060307020307080301060e03010e010b10050903010f09060b09070206060f061803 75
    0x4054000500039568901c1d0030003800f42201140030040a081d400c1c2141c02c079280c04200d040107071900029804c1e4484044000c420303040c5400e445001004100340c0080f0b5444074528202000f00d02c40186d520020002183e920203165420710701c880e00d900425803002d001710b0400c008038110b0504002900e0740d03007400800c03030205065100c03c1000b66152078841e0100b45504101340000c0c43d4404101da25610303030180c4030000c24180000351140103141c0c10310199921641c1b5241d5180f080b2130140743c21155072006000c143c482c004103038003a0031603000300e030300c00d01c582d00c10003400340d4103a00180449200310041752116229034074043c06038110b2240d400300a207030880000003c40c203a0307044914040503d50a50007005540203036402c1c070782210850502e440d070040d00c080a800c0c25920400c01009499805030011981403807241801c8290350b10303510100e8030662100c404108070f0030500030299100e07405100424540c02c0480200d2100090900c0301c2e805160001030007400071040a984005014021301203c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 276437742 1250 276436492 276436513
    0x1020106120503040e180706080c090a080607090e0603060711190605070e030d020c060306040e0109050102090103050f15151204030f080c0f09063103020f09070f0c03020f 75
    0xf0340303c0d4800d0041c68600104440801c00281c80e00b441b0031403001c0401c008158a50500c0800d4409040042c00d0005100e42040304618544610704603c0040c218040200700c1810580e5014008078219005050390713074801c1d0100409070303500144a54000d1010700b8804c01b6814000700e1141804a1810b03144003508401c2440010804c084e07100c140300c0c0c05a5038032382c01d0301107194040585541c65525090010782c05201190300c10b1500701c00441c0c00c0725008000141004031003c1d0715003500c2103110280e90a940c0401c8181ca556094011507602c1022128048000d03d00609030403400c4e8a681d00310f41c05034030310040f540c540007074000c11100124100300c089030705441c0501d0010a56036144499800103001d40020072201e0200d501900c01300100c040310300d0b003443d0011007445820342004602403c9100d030314400304c0d04200e0250000c1c007524a138001c0078540e9421030050050007000b61070742902030480c80e010044551382c44400e4020002e810b14203280e07924400d00b4100d10300052a0704408150280b580100c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 276438848 1106 276437742 276437753
    0x2041413110109090f050118110307050a050403061a0415050d0b1003170a09050604050a09021305030d120b0405070c12050d0207141b06180102010612 66
    0x203143c41c0da580803080107580781001d007081442d82c0c41d0014048801d407500c0450300110044018031040c40300c2401c00841e8030004000d00100400424800291072103001290700841c1c1003841404440d960192804001c024032908a2041e840e0400002120b07180c2c07100b40d02201d10050006602070350302e8940d00c0759010300070720070420440607800c080001401d050018501d0b9410601090701c51a41c040041d10045281d0002c510511051200700b10950307401094100f6503920010150f25071050341042c444010780c64000603858000c0c44404034402d90720220a140c3c80320440424401028041f043c00700303d50040c0c0303002d40042c4480000001241c02c080200c40d038941140760103803070320a14aa80310304036000702100321400170003a040075031400030801000092011035441000ba0201e12800281184180c1c0f04982004075071140c0080142e000b940414010801c10f4180828040d031458803 = true := by decide +kernel

theorem cover : BRFrame.Cov 276258992 276438848 := by
  have h0 := BRFrame.cov_init 276258992
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276258992 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 276258992 ≤ n) (h2 : n < 276438848) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
