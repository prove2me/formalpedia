-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0300
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:03:33.266677+00:00
-- url     : https://prove2.me/submissions/ee690922-ed58-47cb-9241-c0c099d20901

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 53776982 ≤ n < 53956838 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 53778232 1250 53776982 53776997
    0x70210111e03130209090303090d03110d0c1209060e0d020102040308030c0a03140103050307140c0d150b04060e0f0606190c050705060a020708161220061206010f 71
    0x318a451107880014035420904000000050320611148181811198010703141040364501040d00f60b0756544240c400594074420301100314105882070040c00c88400c0c4490a042c2048a04074444002c1c10900000c07205100d00942d48408900162051760780d258013807000454511045d242450401400038080400c5900411060010504140480fa000300e2141c4640daa51000b05204030000c1080c515400002d040c008000400c1c1721001002c1c00e070344e40c0524842c00c000000720030b8182d0345e905012209600b10b0404111007003c500090b00004031510f0405001c40c0081444000070101c400640110b01c440847c6020302140a042200c2568400f800b903400e80e01e811039250841390380f000c41412800070030890701b072980100034084c4004001000043c24035900c6c0c903070390200652501d20902490500784614041c0a400700e00c5002000f08071502c80b20080e80126550700c1c2c0040362040500c030031480072203141c0081c2070768951000402600340c144412a115051074400100703400e518101710300400010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 53779482 1250 53778232 53778247
    0x51503060f01080405030705030f030403020c04060e0c0703050405040f0c021c231b0601060e0a03150b03032515050f0109050711010e1b010f020705040c05090907021011 74
    0x103a806100c2504000d0034550002d513150b10b01140f031841040030090280c00003040b581100488040a540078900c80d4007a140401285418003003114024400c400e04000c030700780402d050745420001401c196020f85000d91800752120007084c00e84078140052890700740e807542600d08465040c0700302c907003c3d855800507070100c68a04d4030081c0011b01c11204a2250900031003000d0744004072401311001d00d40d806511184222407100c201d0344843c400d00c6014045616040b1220941c42e182c1c01b00d02c29250f011140c2c280d041c0c80961901c1c010590400607a07098442000b403844014003114040454410401c40d48092034030907e068110754032a442440a50307400e10040c050209060340743c1a065501240c80058560350300f90b0202d0720b1800036003264525502c1c085c07116115050104400101c02810120309580c4605d000044502003504165035005801c0f81a02703102614282d00603110401c02803905600300f02d010400034888020a852000c050b03408800342c2400803a041c050a03048800d0002520f0a245a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 53780732 1250 53779482 53779489
    0x4060806010e04020706052a070203030d09050a021f09060906120e01060b0d0504060b01050307020d0c020a03120f08060a050d060209041d07080c03190305031b0c0705150306 76
    0x10080c00450602070181e5012507542c0340d40d4140c525090304a8010b20844c1800603000890140c5410040124651100d0300900d00844000301d0b84080da01800444c50048460f4230403005000c0b15000325003e010b44581e00000d81d49404891040c2e82414074803e250034040d0001600b8a400e41d4003103400e00c890114100007041e08000b80048605107080e01084c0d030354401600500500d41d03034004103201e40d40440d621000e101c0a500261107144110010851800d10742c0c01526503000850309140181d0082c0701004050f44607003071000c1700c144040c0c400e07101f558403039a9a136108603411400d000003400203000c0740420350307014002c980c001c501034890100c154240000b2451505070b004025014580003c0e013401c0719103450303001480a111103001ca00291000c6c036011515146184500755040c4601c0001314a0b516010483c010b202051703004541c0c0502c1e180e41c003a5583d410050210120440404100804019850041001524020103460500d0502d0204a8010b10840603880403c80c01c0c400c008003500c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 53781982 1250 53780732 53780747
    0xe01060809061e1f090507020f060f0c030103120c05100203041a010f09021c06060f0f1416030509090702060702070f1401050f070c08010f06080c0102060411010309050105130b0c0406 80
    0xc0c012039000804141d06806240e500c1545d4802900036140c4810002025404146d0034042c038000f1042d14a5030b11040c40001038144296810300d0184000c00c0100300084130301e580410140c3c8107081c000d140c000d640e00c2e07040c00c00c03903800b211581d41c5030000104000c02407060761030009418002d1081c02d180d4188004090f490286004074543c8941c0010b0b8640f0040c0598020326141400d01020b02c2481d0b110500109815240c03080741c4080f03803243c00c06e050094010080d4110302d01506007094107203541581d50304846a055401501401402c210883c40b584980c84800e12802007500140303101e00704a603000b0b18042d80caa00c85007180e050084103221100014006145010302480e110361a40e03018000e03144a40b03c2c003480200707036810440c0e0004445106400c407061211404100b08203007541c4a9550340c45048014255006800000c00100010751145191001c000107140010b900c08841d910316084407000d171107040c8400c6c5201f800c0d4007004120040194015183e101e105d0801c1e01e403810280444 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 53783232 1250 53781982 53781991
    0xa06021f0216021c05070b03010614030402060d020c070302031c050d0e070e01091e020702030309011d12010207060c031404030503070201090b0a0b010f02060603070612060e01060809061e 82
    0xa81d00001c400e00c40710030290400c80c01c5a00108203001696094120308000f540401c0111014041c1e03c000055010b5983c003568101c80060716111007044007483e1000c0a9400100304917402003045c00b071100843c4030740c03000c1e0403284505401013511904500405281401c101c80742c044d0030304941e0ba51011a0341c85001d0f5801c000c0030041c00315401c0c02c103109803420700c030031600040c3c8005a0100005644402d58200c881c030045c1c510348801001d40c180c459035040c3d2103459030280d01540b007081100c54651040594205280203403050361240c0c0391120003d85039050310080701c5440e070b4000c90417505105241c80703040f020070350034203041219030181c4040410019000784068284080840000c0e1803500039000643c1503940081d400300b0601c0c01c01c03038400040c10358140700c42c0017031256545c80305124000038409000780d10040081010702d18004040f220081c0402c4035a50890f02c80d000040c25441c0c69060700c2c06018a0349a0380640c0ca40041228030f41000140441d2220901d0504207407607061128049400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 53784482 1250 53783232 53783293
    0x504090209060f0a0512010807030209041407030615060305010909020319030507060501030609031e0504090c02010e070305010b0108091504020f0f09010608010510090b0901030c020709020f03060a0602 88
    0x35000784030001100743c041c03e4034050b01003000160b05003030030358440e000b01050050300c1050345c07481c0d0b00c9201e42035840040740802500480e4601c0890003050102c039a03025030509880c21108016200e5503a0b0080d03852008a00e40b00350140d8a00340103264240c0112405001140d0041201051a03000280d60f02c0807601c2c011518449014030405043c400c03030480e00119086001407000396502c2c58410020b0081500a4000500c1d054562080c01100503044d01e02140c5a501e2030304003030400f0300000003401100d40d210195076980c103000602d100c09004400c001d5000380d000244240031000007510b0050010684415604024880a01642c1d000c441c1038106406450120b4240e41d0000418802d40e020010198000e914400008440303522200c0c5034103945040c0c84c00010072800c064155154946402400d00c07003202400200c4541d4442c0d80f2401403001c4ea8412160302070380c4c03158090101c0c0c1c007100030024100c0d400000c0003014100702d400c1d54020005032005061182082907140d01003134001c02c0d014007 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 53785732 1250 53784482 53784487
    0x5040807022724040b10180e040b0106020111040308030705070309030602070b04050d050a080103080a17070f020c091504050405120f0705060609090d050a02011805030703080901050705040902 84
    0x20541041d03602024101401c0018101820f000301400651800062489158450f0444006070360800f405021080341d00500340c18003080d001001625580c3c4d80c5d0800d2411000003820018100155442c1c860040d4007802d50030906c0d5041c480c00909494a0100203c2036000401c010800181e00314200ca07807250b850700d407040d1145d14502d021600200c01d0303800644458000f240c05403d00c0424500d807400355116104450003200c0c0b00f102a5038034000c888050010508000042020888070001800030740320604d0001005038040d6240a0041400e4501c480001c0302044941caa241d01084585140d09d8215120302451500200c0d07114445d68001c0b10700e009548890205040003410060a000c101c1103d02c2c642d150441007407140c0c034a82202d03c06503001d2140070042045410441c5002e8000c03060000036100f002d041e010165503591102104000310740d079a070f0f108800b451082c451100250303c6000a9035a83c0c030241001011203201508140b40d5925100c244042c45400c00212412555541000358 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 53786982 1250 53785732 53785759
    0x1050a0e01030b0604140306150f040905010e01090c06080109020f04261009021306030309050907090e0c04030201033b0705060a030615030614010809190c15030504080702 75
    0x28050310f07030040d2143c1c02a01c042001300d12011610b6101e44110307000c0e0120b503800e540d6130240b010160011143c4070341010541220300442c0c14160000354560740140004a40d950310004045e08481880609550880b24090300f44291540b00a8613401000b5880055007050001d80d4908164403c51040584000460001c000f450210f0114a00301d100a00207407003d014035281d00001030214200c0c201e1152885d44107000c0c002205102c0d001c10f507a01940d850f60998100300c01d215500c44054500000d0007501c1000140e006192042d031407081d0b4000400c980c54038607610000d01651002c1c0c845441c000d1031004101c20702400e0f580188046400701913401003020039042800d00f001429000141c0024000034440000751300764100c0b000720307207603d071040b141d51103100c00480403a50b40c0e00509000e1652807040501c83d45c840c221180d00a2840403c0d80c22002c08a045204407940c080c8007220b40042c1141c0410080300100c1c4012030903012418180301c4d51402d90345180c80345c0300700100203204191084901 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 53788232 1250 53786982 53786987
    0x601030b0f03070906050120030711060f040f06080606120412170c0703200c060306040f050a0e010e0111070807030e0a0f0305011a130507050c0a03051201080c01050a0e01 75
    0x392060740000e01550380003074a42008001812150140304d0105221183c880003c2d022510183e10005043d000386080c4161a41e42c1d03c2130f104001031060f2301c40c42c10b000e034004044610380100000c00540d588549100e14281020b0043c600c0100b42510850023072280c101240070f01d4101540c000c1d03100001c441c01056007101555901d0038aa0040302d0142ca0004000084092500a04a45020381c680d42c100040c000c0c480b20005001c04003111003500410318a109905025001d140c2090000b403000c0307080d00c210114a03003110700071550910400c0d26030703c002503138bc0028419015403299940003403040744001d0281e1001c5100d0908028903e01c0001a00300074103200c0c0da042060100010840590341d5641c11100c030540c181b0f4081a2460751038014083e840c0d00404494160400b0007074000c0c1d80d100313030020070100104802008070003800300401441e480e449040c4032151506110b522503e841e00c010401408400c94143c2060f803007640a0103038003440e80c0c4c000040c1d48a00f2110b20306200c0c440d4410004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 53789482 1250 53788232 53788249
    0x307170d081803041202030c0a0b0f070c0302060a0c0b0c040b16110301060303180b120103020d0611030c0c1203060f0607030c0c030f03020f0105040c0b07050102090a0b0a021506090601030b 83
    0x101550f00000c240810803440c003d00c006905802102160a480d2600c0104144101d003031242410550040088103640c0b54460301800e0351070300607003841001e10750745d40105d44a5070203c3d0f9401c000a005e49520410014002c01c1150466107c9006906003801c141001d607061003007003500c44044080c80d82040c1003080401303041c41101d030050f00030301c0080c5e81d9180184c100003481c525800c2d00d0954200c04542d2545403400d0301c282c8120b01440e0171a42c0d203180c09000d04ac01542e0420345840d600c40c11962915503190004600440e0301241c550364900003050000d0420745004001c2d0306e00b280030001d1102e683c0d5400340520b1444001c4488503600e03021483c080c0cad4500c082071030040c0400c80301c03000042449811064011038a009030280c4002c2d07000d9800a600300d880858000f00b90b1f1240c0c00c403e2040c0c0d1094409084568070860005140064000003d2500c4e405603010000c24400029240303100b60341800210203581c0d000d9540c80d45401d0010000b4407110004111904141d070b180d59417907642e6951000b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 53790732 1250 53789482 53789521
    0x902040b0301020f12090604020f0906030114011e05030a050c0603090f070303030c030b040516030f0b031219020d0e150706050f0105090705040308040b090307170604020307170d08 79
    0x1c655a00004c102400250043d030300e0b0600d9040c11400044009201107003540c03045500800d95044501e001d004c00c034a000f005002a50159606c4494100c0e90844c01d0505001e0704400e8242d41c607902049030b0103d07902c102500942d0107030b00000c10003400140002111340307400804545c101c0e2290344510348030780780c244818440c2c912440354000c00030038182c0640c400c10307050020350b0b424401d040f40078080c40140c410550b14800000c080756440030b90244030b80c0c4418441d1000110200c0c101c2c0750840064600407950101c0c880b40340740024605d9484d407140841054a201a0003d01110340c5505400b800d03200c030b0080841c0c003601c40f98501001212000d0219070101754412010041c504080c0700540d12800240a501d0141d81900301080c185401202a5003c0303d50203940f003031401d0f0409109400c82e030030003003815806205960f8007040c1000c1b04110407115000c0f54009100714a064010585800d406900c072120344441020010421070021070705d6441c4161904085c040360300d400e00120501c155494 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 53791982 1250 53790732 53790739
    0x30203120c03043803010f0e0402130902060408150a05010806060a031502120c03040b010927020a0b1c060b091509010e150a0e0f01200312040b071d0604090902040b 72
    0x44d0348080d2501c07042c0142d4141c81c0c02841c0300144035100c40d40150300d89015240a0b501244035007651200c03018540040041034030182c85541456a0740090900d4058412541401d000c144400c0000c90b071118450350f401440601e00800803400d00c1000b150300440c10340006032014040031442c0c4e600803802d070111148001d460301c512030301b840e10140d68002c682069800b2604c1c071112400002c2e4001140c000c0c110301c0c0c46800441420b011303003240c0c00124001921000c03a00b05924110000348000c1150103060120b05000321801da50441038039540460301c032078004070601e0b0400e10001e030040d10741e0440e980b500f4100c15100c507038921b014030041c1d56142c071000c42c2541c03004401c1c03140140c03c04000080d1a034040151503110051014408114500800c203008600041c40088400b03911041e200c4181414403618080d81d140c407680008410707105804440584801244400340300160341d00408450b104642e1014180e03002c0d00d000c0004400d44254400c4408941c0c4644040040d50b0791740d4850650200c008 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 53793232 1250 53791982 53792069
    0x30213060e0c03070f020a11041e02030f0603070f0f050409030e04050405012304110d021c080a170405070e0613140603010c080f0a020304061b09030203120c0304 71
    0x5002d028583d104841c110300198900d407214884500008428412960003410400300304281403c2c40020f00d607001d03000c0001c01406401c07804410b2244011405211300c451380140610f00841414940f00d4a1f41c040f0315030300c20f4007000b04180c10149509806455080302c020440509904085030103030b440340e128030b50040c503010a100c10403805502140f15030007248180100b0304041a045001e101040b02d028180d1100880b0007241480c03c4500b2485a071320080c244081d4540002e45005105034887d0120781c0c10b080015403d5035607070003100d01403141c1c0c540140c1011514165603a81c2d1901c0d00c61103407103500e44030400400c4559540d03803600c810520a1000c10441d99400c2c01c0c0e40243c131030b010340e11140294030f00790440c0c1405101710f0300c4070b10643da03410340008941c0b0349500000003544028420b4548542c4da1080604105401c400e0b501c8680f4159107039220b2a04500405041175402148003d8105041007005c00e0a6404410380d412510118422070604004100400c2c2030152200105000d0840 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 53794482 1250 53793232 53793241
    0xe0601200606010906020c01050d09080418020301050f09090d03090201030617030409061202010c030c0602160503030702010b04021801081003021809010516050910090e070c031202090901030213060e 87
    0x4100b445031400741d84010300107036541e00903600c4d0000650245e00184042001c048244856000006076900c1450194686940c42c030420418590030107628a60702d40000c010021403902c010660f80801003140c10b4149400c8c1202c20a41e10074540b00f84400781501c0342407003000e40e8003c3e800900180503802070001034810a614036900d981c0507000b0114214075095000c1a03010102d500034005540c182c4845040f12042d032030580f6009402e2400320342d00e41c1c007003081d80114610b66900801e40c07441240296220b090441c2c0190079148242c041c980075a02c1480903200400261420b40c0702c009d02030a142c0c0d0280c03902c8505460040164002039009580c00031410f04c041e1600980c0707032054003218000c10035603c074410710307203c8044000884400903d05202d00090351410705140318181c14141007242070385944010b1b00e0784150302201d07110702051a5144500500d600260400110440c1841c00c6180000000000714841c80c1804007034062a640400c01800d01e4940d48018041d01509c00103810302d141 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 53795732 1250 53794482 53794547
    0x80106090b0406090b010e010815031212130209060d03091a250309170a050d03050a0b0d080318030c0312040c06180b03090109080301120b0c130e0601 66
    0x14425011400b030380c5495800603034241d65200741030a21105a40c0e13200c15440c1840111a241c01c050001a6009503a071000f11007a903041160034940e04000003007945039411400c0c140c501f07150080400d103c1c001800b00b1640140d9882c80c0d02540700c00103c42ca07924509860600701c0e031a400307980001c100d054403a4003803890f040c038100c06400260401d08008081620a250181180c00c0c07004005021807402c1000f0b1265004112001c0410106181110442d081545031240b805900048100c00b00340c1c2c40d010b108100195009441d030840c0140c4d19594080310350703540c04243d480000c102000000c860410f600c41c080050044030400410701040300e4441a4100c2e520654220540342104d404098110020b0035500654900c0c07844003240c260354a000b4036003900d40300c481d44000e0840c00c09541e21840c07200041e842c18003542c003170b01c01c04048500645079440c014240040160840400707402c2801400001400c412081c020356280e040401d03500e0300c9000c0140d8501c003942025200010345800c41c0b420100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 53796982 1250 53795732 53795741
    0x503070f050f370f080402010305060f0607060504050105070507030905090c12090309030618190c08070905011a07021003090602090d06140708062107080609030c01110f07061508010609 81
    0x11201d0503000408500c82d0065808020305610b030801700300b480c0c000901640c041d60003181c0c8014082c04000881c016a40014200d50109004940080e80d80c404e02c01488000d2040035800181ca0034a1850305a09803409011a8098480c59120740348000001e1814020035043c0c50180c03880c54401c2503079044c40c80703840343c407034200c0700e0071030700903c074140010b0107045103040b840c6440c410034406817105007010582c818110b6141c1c02d0540c0c10a0a00c200014001d0b0304112260042c03038107060005442d41058201d40c1d00a0180380d02c1e100c036180602c0710034050780c2c42c0041044915802c0c04c0c0050034480c1441c01d20042d0007124003160348040c029030700c1400d04c40c154110202181d540001c0c042c1555503204252180078040c2d030103580190250b0b00944000510b043c503004200b4034141111011079aa41116103888030444030300031603030000301e9002c0320041d0034011072407442601095203041900a0071504114024114003038485a150f81d40c28109150162a580191414030001c1c068187c6034640003002d003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 53798232 1250 53796982 53797057
    0x2030903040b0307090312050f040915080321010503060705030708090c0d030302070b07080c040501110f0a0606050a080601080d0509010e09040606180213091e0c08160503070f050f 79
    0x7c004090244050b07510a104541c600010004203900305803c11403001d00408100e91850a10203a07000081941ca138100040c0c00f8480450a96101c100f8603035000320b070301c0300781a400740d406a8020300c180700541c1d4005e001c0d80c0d400841c524000c12165211104145070070716401c411b03904079440c420083c06040c4c1c10740080007154000c4020795050b0329154000c40c0e55070003c60305022000310522080c0030f513610410503c00040c120408481d8904503000401d42062406d800c1181c02e169211030412080c00c04403050402000b00a01400940d032414803280c1d191b4404480d04410003c00203034101e01a8002c0c42660102d2002800d400001c2c0b401f071801c0360042c22a40507003100c00b42400c981c0301e081c07003441c001c48002c001080d403032402081c40d0845540213808034000302a4007441a5041c0e1044ca4070901c10420b6400c03a03640e40360250709004071706202d1152a64200000c00c41d04004010f030580c2c01211100c1205035602d40595158003108085401d40103034454000c01e100440400064070310484800700c0e09 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 53799482 1250 53798232 53798243
    0x17090607030501170c09190509010506010e060c210706050403120f02090609091003080c0307110105072003120d0204080d0309020307031104091202031804061802030903040b03070903 80
    0x250b600c0e1512002041d080c242090340030752013141e01710300ca41440e00380507070002d4580810550190191a90809503581216502e409a41d60741c02c104456922501c010303184002515080e01d0314500070001d0b600d0720081c5850300381c55101c00c545010b5640c460303821500b1094008004001c80e040a20f402403654038001c00c14001c150510581d480708204500c21180500b000909840c0b4144204041c0941960000c064420fa004040000030110f80d00c0c500403d003441521028664540441c0740c83e541c50300e070440840f41040303001d00095001a508520b40ca5010741075840c00d4111000ca400040c1c50a072040e00c030b120400b000420101541c400580140c025100c256050759661011794404804442060f00081c0d856400740c041040820b4400000c02d0450502401c0807c070100c580e00c0e4481d41d514080140307c01640300040b40c0b00725402900303840d4144ea50465040c4001460400340803281d9242044403100103070b00101144680304100304850040120696850712460008005001078800340320a555 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 53800732 1250 53799482 53799491
    0x18040c0c11010908030a0e0310090305041806031a04020d060204140a050301020a0816020106030c0303091d0106090915090903081009050601080103030309060b0414010f060c0f020609011709060703 86
    0x1080d6000f0114001030358081e0b40111305000888404a03041040207507281e070140211442466840228001e525005d4025290b00782c1d5903190002044074661504100d03e6500c0c9081c2050001401c1100d0006021000303071201300e85600e450001400c048021400104001d01c00200040c1e6510441c2e8040118007049580d840c4069607041454242d00c240c1c240d510003e0010700016481107074690044026030351a200005181d03031203641c2c06c03007a54842d4000f50013040b042032080041c40000130a10800c42456490010b03503500d08000030306140e2107805011003941c2c84544224800040c81a001300400c420842841041150304003c1c24281041c2c85040443d03100300408209103109004080c02031206a40d036000030303807842e00d0840c024031042c0070840b40c0640b5079110150541d154040c0d00c034041d01d00f220a0080b940350003003400585085034804005c4c8919000600c01180618418100054040d1225560768550000494038a464010350f80b0f100b488120a01c00b0b501c40c006849403091039151030030030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 53801982 1250 53800732 53800763
    0x1306030905030d0e0d11060f0a090312020403081801023009031005011508070e01180e0a0f1b0c0b0a0e03120f0f0f16180b070c050f090c18040c0c 64
    0x203447d260100c4d914400945258080b5900880b80c0d4080f005035402071401100006207136101034180c0c0c0c050383c0306444d4910007003070f40e06c00e40c003400450384c0c803640c1d09000800c1300d090f1003000038260002c1134a154001441c00120400501c043c8400c40e4140c0300c0040c240c4209500c5112401e00a00b4280509404010b001c4d40d016079242c01109864007552460b160320184010420045550456480c0052202c081001d40003030011850403889020385518280031502c0e01038140446c00f1585484009502e003501c1c51401e006d919008070b0950b01081d001101c96415a94070343e00703003001d8000d81001800c14800000d611004890031030b5418000e11b503500d2000001c1c0c0f900c061149808009440400e03a549185c004500d50741090700300e2465640c110b00b04140c0a6400442051401445074000f101c0d403e000034090007006625144c1102070728040f01c2d9a0603096909002c40c200e1100203040d850010000254508492180b1000c590210001081032008080000380203080440c00c82007151807006d001c0f0140e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 53803232 1250 53801982 53802017
    0x60b1c0c090305070b0a02010902040c111011040b0706021201081608010b0603060105030a061505070302010e030307210b0301060b0414040c080601030c0c020306010b1207051306030905030d0e0d 85
    0x200071283c1290042490340d0a03e25420326a51003001050290340d030341c1c00f00c580141c1301ca02032014105c3c00d0743c6444000c0382c40c0d41406810714641d0903050544900c1c02c0c42a0384444441c1054400b6221b4020066449030030500d0032000903c2102082002040948000598684005070a0845c0d040d581d0401c0000b9550f0484613003600d49a030a210750160040c0001003840d44180040d5600801006002c07515980d01c44141c5007a00482c801d40d000618001080014903809001e001001148074004614624000000409040840920303881070041911031650481503600001c06030718008000b0840d1654940721003000e5405842112400414500310440d10700d007603c90000311404540700c101680d65508011030042c828101010b080c40030440c0914096201044000c0c00f80051011260799030450070168609200001c01d5a000c00c42d040008070442c2070301036813820855000d802d02040c42003140c03030a60706501640415601c15490041c040c08101000100e001041c94a81c440600007201210308 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 53804482 1250 53803232 53803247
    0xc1203040609050418020a08010605040b0603090715050d051006030b01020c090103030305101d0604060f12080d02120405070608090a0c0e0403030209090a090b1e070e04060b1c0c 78
    0x41d980840c00000041285041c1600070000d0b410f214102030000001070760000e46e40c1403168001140704ea542c4d10342032245050901c641392040a088800074110728007180610743d25111401001c2101d040032405c2c038003442c014826102a030141800c248928946034640b0350340d01c0000d01c54480042d00700b5108198650000c2010800003c0180c40608560700350f4506401414010b001a2031040c800d00000030802c0401800343c4031030b152104e02000c0c501b829010481662403a4101c0131a1080030700040115601c40000810400d5202140c0c607120035100c54030744024018411900400d99010b400c200c1002400300c1c540b81a101a178403060000c0d150700303001980e906402c86c4020029401c1c0c02c014042d440c2c5400070f0b1544103100703143c007615111492b00440c120200585800c00c10b103880c0e4100008011070032503403c1e4440c451144038104101e00b4a0f00c6042800041e00c090140079800c2c2c940407143d2140d03008003000e048803105442e620b41450700340c10400518100b2000d00715140140d503c2c00309209000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 53805732 1250 53804482 53804489
    0x108011a0a03030f140f0a02030304020f040b0a0e07200a2109030305090604080a0311060601020d050307030b0a150c0c09060605040b210f1608071e050d06080c120304 73
    0xc52460002c0401c00580e40e039465001898400c2c00301b8411141c2001651000f882445c00a80c0038580b00d041a1040c031004404103d400e80c440c1d400c10f036180e2200e4807404000030480700c40c40010006070300d0760402958078a4451024001d140d0542d03000c0260352400003154444d407842a030000c40001c80c06800708440c250b00030050000141c20700010004240320308080c10130080000c055616103179840320307540c1c5801d8280c0c1044010542500c031840100c1001c5c42010380c050400e0000d00200c0c003403010001d009200c014410000c1c141c1e180114031164643d14900380103007181c0360742101e4126140001912103000e01c135045075a011980740101300202e140c0100c604888454a50604050030b100c0680120742000e000b00b4019446201c1e0521031120a4003958002e62610b2001e0140d030424442c0700c0c3c3c0c024050000601413004500900000c1a8000c42ca42d100a86040d181c4010800c2d058084855225060480b04801c0c01d0860200d011031000c10b410040391812101010b00010402e1203030f4a074004c070322 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 53806982 1250 53805732 53805737
    0x30106090e0d030902150a0201020c0d020d0f03060b0306090406090f03031a030f0304091e060b04052701171509070503070f03050a110d1a040201090f0506030402060a170108011a0a0303 81
    0x41b070391441140b0960107003038485480d00000d401d04200b24295842c10300c8006070f075401617200e918080340c090707040046500e0f09100c030b24062141d581090f4041d0840d10014004a020300b050340d00080500c1416402950059132090092400c903580c0e007401805414007200312000000c1500c110701c011700d80002c040c0c00c180c1d010400b4504140c80c1c410900010024041c4891512049500070b9160039038074444c039806802c1120400361228101428405000203800716450308200451510501302c0d030341002c05e070440b04862603c07001030102404182c108100b10944c122550b550605000708075030041a9001607600c01c5d001c44901556480c40043d262210348005407658005200a00c0864043c110b0001c2103180500b841c4055800303030b41c50001080e00d83c01c400c062000b047c0e051008540c0c0c4590004014400c0e514880201c609100000701c030740c032010348000c0c400d990021703001e44282d000e00f0b1880031811a4205114196079900000c0c2d000e4060581d540003403040041c2d03103410310301e050021041940d8065 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 53808232 1250 53806982 53806999
    0x190302060304050109051507021005060607061509090b0a050610050a050703090f0803030702010e0105060105040905060d0f050a030201051b030403030b0117011409010f0602060601050d0902030106090e0d030902 92
    0x54080c00140d51002e4029a90365494030040000304104114110700300080b00c1d01106140340801000b401e005403d42d45212131030030b202c01c2c001c1c2a621041610303d04e0707030002e0000420110388090401a000c8651100300002c4c1046008428004012003ea104008210042c45035907601e1040000c8072841080d200c0101c0c205106180c58030b440307030000c4e00c0036610906110403c642c07201000400744205601250042d8400000c100c0700503828002d0408100d641c1d0b00070b009500301540041c2c13060145001d414195903840740002e071147e4486449021994012030070324074100342400d006440f1491050160050742c02c0c507011401c55542d04880780e6454018a00f044e05503103440d9012005080c0449400781004800050341e00d11310841c000a034000e043c1c040451480028841c14494604016402441c0202402e041000820b0f000b00388146d00150900e00306564010740705804000701150070010b1f4056103000700205403501650701442180312340300115850b580118400310f060b10004503000350080f865 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 53809482 1250 53808232 53808239
    0x13080a03020a14030409050a090312050f0601030c140304050a1a011809030c0b0705040f05010905090103030e01021905060402010305010902030405100507030e010212040b0106050403051c090504020d150519 90
    0x1002e612a4080880f14150f030b00c0c1c166a0030079003042e60780595104015541e1440c1303627404c250b0030000b4600d58200c40701d4140101d00c2d015054a098542c01000c840c18141c854110740411440780c02003135545240c0b40041d80c0c50b0304050074429038031869a0012203404211000c2e40b5005081d96034010b04a444068200c55507468410740c50028154a27903040f1306000200d640c000004000030a01485100b032592190303222850403042c500092426406903052003d444001e0005440d15010030741074a806040c281261b407031140040b850034060400814410f07009400003410400e0101d01036000e2130003660300f40010f98075043c866007240300a0b140108558012100524000c000c1e0b0001c991004542c1030000e807909a88076000d0070784e441500b091400060000c10003081041c1c01c1030007030141403540340c0340703040a0442c0d035400ea88000031202c017501c040d07246034200341092140c4040809484081c1040d0340300d501e91176004010304003900d0060100c0d10140004150350504058130139549070032002a06080d4039 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 53810732 1250 53809482 53809493
    0x308070308072c0d0501021b0d09060e0906030a050a0b01090c080126010605060408010203040c0e090709050c0906190e040b03030909040c0b0a050d0b090114011101060806010b13080a03020a 83
    0xc0f4500010b40080c001c2d10701001003a4288003070b107075400c6800f02c4400c0204003001e50504102403c0701d12014000400401d20010760302450a503800380382070352a651291a07510002c0e140c001113100081642c03162240400412081c0405241211440c40007401551810300d4107541d00d00d000d0040300070700106002c0d20908110142c18980d49081008000143c3c1038640000c03441e2648260170085490f90000140f1003008000070300340004017590301300c160160400ca00029248c0100c1d210b10384940740c842c00401c9900c3c0c860400c03100c68400040c1200e55405403a4511742c1c0f121130f1050f03000f002c100d511460700b40300d040c18082c1300a6188001c1c060751503d10b00c4010450000310240041e51801c80116010407800c604500030101900d15440f01ca458440000800042d030340044041402199200010000c001d543c0301810403154007400d20098416440c0809401072505501101d994401c500000844480110051100808590200b00c0c4280c545201aa40d5048014010010b0b4480c81c0c0c0c0070013049 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 53811982 1250 53810732 53810807
    0x21c3204170a0201090209010b040501080112061b0f030b091911090307060201060510050403150c020307050601090e0d02150105010305190c020d0e1905040c020f07030807030807 78
    0x103101d641c01c04031070032000d00036a103150031411456001d0707955510001d040d0b1501041080c010441c2040082c07400d400c1500007009410107114154000340710b120004100180c50f044000d56400f0384010140d10965024010b00288031580e511000c245044000a09405c2080010b44900c00464a1170811244c500145000340000026040341c0e20080c4880303d80c1c0d1350284942c0d8000e091590001c100c0724201420002018210440c403001c1c04400c1104000050308241c08803002d103c4513600107991000300400f40c0c10b501c07401c54010464010480081003c10499000c2c4905180d00301c04c030b85104064000c203a036200a0021100d0b40f02c824500100000c0d0b2203508030b103074059032000100d0201c112488003541075401300108003016030031002c50521010b501550760110150120744e19241c8290804141813980c80d00d02645000ba41c41c1c25030614018020030407001502c40f0b0108452885940381804a840e400c80c10048001866034004220b003a44a40020519441c841c1158981c10350560040c25428 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 53813232 1250 53811982 53811991
    0x20f03010905150414160303050901030b120a03020d0e061206030a120f080c041404093305060612010b0304033006050102030310060311070501021c32 66
    0x1592a107001000041040c420784a86070094460031010703060a242102c5032840da204046019400030001402d9050704c054610f080700d82509005070f0358641d01e00120301034901c041d4040d80003515030010143c20400000d0410301d640c007940c2656858030004900300c1b0301100740038000380d22071000d120040b00043d61155a6811403c010102c072100a15a0f4602400075120740d0720700c0100340740a40420b2101c3c0c2100c95039600c06482800c1518203810021000210703501812081c0c01281d4607588036040004480b51101e40141c0d0240c0d1130010312000e00c00e884a0028203144800e114203100c08910035040c4801030300d681c803440c0903160039143c0c00e1400350b158540000308142c040120b40b841c5000b882103c0c0342c40c0200440c2a002252103501c2d010410720031340703c2990000307045500030810031084048850b000d505a912503c0c02154007109441c00c40050300039140c014080b54400030390001400b40d001805503000741d4003401031111150250088210383e01c140000b029841e141051100304085003107205a12 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 53814482 1250 53813232 53813239
    0x3070201181d0901020c151e060108040b1018020c010f050c04180f020310080613080f09010207030c060c0c080708030301030b061212031014131805010504030c0605070201020307020a020f 82
    0x2000300c186c04462501700d1301408120711140000a00c00c42c1c0c3c8103c45c0500c0c0034060005003003040c0c189000020150100284090f0100301424046104a401c1d864040300400351181220030a4070b12590060007940028140342076580b03800703071a07000482c070307402003600c106081019281041d19100b1000402a2080d880601407039660050410310000c038806140901d040ca400c1c3c521850802401520340180a0010170b4040c00280d0350000084007201111504240c140741280c9401d07080380141c0c034060003900300503d040e4007100045440d642c402c40e1002c0f1240140c0000d032555aa885480c0e80700d40b0340c1c0c00717200d0150b041000140046042e54850315006540034184800c0015002001810141044001602d03c0b00003c2440321000000f05240d0140290034004d1151800c1600056030a810701d00f002c1c04915180c200242c541c1019205c04a142900322000744040c0c58149801001c1400c0364100300c034402e1400380401c0449105101741c80c1b203441c95800801c000c54058081040350608030424590 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 53815732 1250 53814482 53814487
    0x9150b03150103060c080a052401050f0f03100b0c0c011b080c0604050c0604060e0d0309080d02010e150c1e090d030503220305030403030905031303030203070201181d090102 76
    0x2401c1ea40e40040d18001c40c002e1400107031110b0581c00003000380d03001603d030348a03041c10f00c4180080061100f05000860741d00600090b00d8140e580300580e402d01035640e2030040c0300c50110340d980169080d03d000710302c07560696040078003039515070640703a005018203100c048407903011000020031940a68100b040d650800c0403181d40e50101692061801c9d8070951980c18a50000c0040c081002030822110300c40d184101c0b60581824100180100a1150203c0b4903100f0080ca0f00c0c000c0034107000380c1d45400980204403d8440465088034068080c0407681301c4009244210760f030340511182160302e8035002c2c42c0f000e440c1501c0c0610780c01c503003080003d184845145049003044040010354460b101809814420340b01c05450b407906c2c80540511890b07490f01c590003400b0342c00350301c8002540070f400c595220f40d06082c00141c6101c039050031461030281e031001044038582e030322011080c144c0000141140328401d80c3c41c01d2195030840c009102200705880350118084c80b6078039202400c3d0560f1062076124511000050 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 53816982 1250 53815732 53815753
    0x4080715090b18131107110418050706180b0406030b01020f01020c0d14090d02090403020106080a0305030108011a0907110a17040f080d0804060504050c030a060e070909150b03 77
    0x10302550041e1a0012080800b00c1d107040d03e800c1c6200d4641e1041d03034581003007204080341104001c5d14450780c00000e20b52001140186019a174541c492400c0880b40d2040c44404440340c0b41c01c0780e03503a103180521004030b9500748242c0302c10b0011104080c10344102c6211241464502030040e400307002c06c00c058905500450702400515032007440506088080b40d0700a013016040e910340a04507050100e010a400700f001c101901d820b840c0c00040144469040c1c0c1e40c420710b41e4860030101c3c01002183c0103040036003e060000401e01d940400a141038840e000000c102441d020480c9507503841744148110f4101c82080c00060600380101e90141c10900e07100c05840c40e18809544a80504e94030390000000b143c0e01042c1442600c45a040b10006051080014090341d45440005031044100030b000401d91500c45000408028090080344c0c0c00001c06022130b81038010510b8190064480601810828480c060f0001003e800c0d80c01241d550f82c1d04003c000d0401e0800d0744190b03018104d06141e6a415120700c1d0f0392075 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 53818232 1250 53816982 53816999
    0x8090a02090403121a030703020907050d2d0b030a030509211b0d08250501022107021912030b03070303020a0201030b010c1e11060c03030a060b0408071509 68
    0x6205a03c699101c0b60080a0000088104c2e0008003008000c0f994400140440b614001015802e42e84c040b03407800141da0f16144100c03a180310307aa601100c090308103448a04050711400020041c1c001d41e0400e404c003581040b40344c2046681c880e20503075040d403150381c203240402c1c040c60003007025050160071205a109080c11042c440c140090400003030b80c2c040f0b00c51196459692881c64500942194074541c0200c50b626041024010128400a0019000a000e6035500e1084801810651200085d52949111070300000e02c680002c25981e46003030307800e0024805502c04a010450b0b820040c940481000d900d4481d01c0800c9410a010f2082c5691040d940c106c5a504100381c4004500c240c0c002e02c5580b41500c00101640d01c01c000141c140410000044c1c0081d00c13441444da45260703040d49089030503503542060b1110608406856400034400a41c2310750000b00440110704c03c105c07070081404042d642c0d5441122501c1176204450382a00419414806804000b90500c045e811030f1401e0041c06803600200c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 53819482 1250 53818232 53818249
    0xf05150603162007032a060815131a060903031b01020d050c0a0f08060f040b0f100302090307050d080909130c061101050a06080304060e060d0f0209090a020c0c0108090a02 75
    0x2207040c4c1d4020103081041021081303207210700b01000d110300080c082500c4150100c010081c0500c6080c0001e10000401070840600e8488011800520000345205111865001818044c90034403c044c407100081c0d0340741c10000211440010f015004503d002c641050b6000c0d20490f080c1001d1065400b0040d610304074950740246800703940030380d07840350352a0124000074007091140003e001c2403245503020040280c5c2c40c0e21046a000c24162800308030f04991100154902c060341da50750380d00c040e00901070b211141d031541c0901075840050382110300c41a120405c01603008080c40d4000e0098100700100086410000d80c40f64108a6403103400c00c40c1c900c6a80d500c061184207800c1180024400c00101c0d042c0e000c240a010340101e641007013004050f061811040d01c81c4124026402400940c00b1500200d40f41c541c02c94100000b2250200f0108807134000c0d100c0a58001d00e5050b00c55190b032008034406040034401c480e4100c0d51407004146501080740151400c68000f0a11f81603401350340908400358450404 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 53820732 1250 53819482 53819537
    0x81512010203090105071e09061214010605031801050415020c071a03070f1809150513020a020c03060705030411010509030a030201050a050108070806041b0b040602010f0515060316 79
    0x200c5c2524058100a100041201010b00603500c2e69501c86096a0051114002e0b290b0500d46059580c00840c00e0343e0207407901107024044062100c0002605030740c488042c40c05003054072f640708044896111110f0aaa00964003e003801045510101e40c00300c19900900d0380b2485441036882c65962004c0c0030003142088403444454076400420001800d610000406078a03256041c560066032094100d01e510071418040c40ca141a030b074071901004940030380000d4000b0103004045119040030301c50242e01a41080030102e0241c490003c10b0300c8185000f04203548140d0899941c139055544513100c0302509403140c00341c5414010301708800d43e1980c500b030007140403850280d00040390304d0400d08d1010045810583c085d5289400415050000001c0440c610341c0041d000b107480c00c0500c0c1010510840320420717911041000d0400a00001c22030b0701908564030303006907254100b090b56a00f90070360100e04420007060b41c0c880030400c000b4501d00101c0d51410401c1c111498a030000b1044ca003a10803d1503031186 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 53821982 1250 53820732 53820751
    0x510020a02011b0b0609060310060b0408010c0f0f051606050103031106010509061806150301030f11010e0d020405090a0c0f0801110a0504170c03070603022701081512010203 76
    0x1940d040c2503580290441200000c1488036180c1e1462035141c0a10400d406000c482c07003801d9420100d442644c041140300006940c1040801c1710950341d180301c181683c443e11404485500b40b04500103500d000d480743d182d40c5405c0b5183c4084859540e0030441c1c040d444200c5500340303800c0c40d13070521010403418890319029602c08d80700c8098800102d00100e1415005030700c00f5204e05401c504108450310785c1e142100c1c003850704407031030026500c2d01c2c400203ca0b4680716214080392a40807000000b4032140b105081015401a000075880c107800381c00442e40c0c5084449620f0300b20400429450040c1465448030754040302c40740503180c00c0c401c159200074450103d130303011400203044140107110344107082c0305880440803902c82c083e00d04180c1d09000780150045100b1070320010f030001400140035030240011003035010001c0550f0a0142c4684000e0003e400400c3d4030b103110345008000d494840b81501004134040c00c16100c03603440f65034101400003080d05031a04182c0014419141042851090000d103008031030340d4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 53823232 1250 53821982 53821993
    0xc0304030c270b0a0b090d121806020a0308010e0421030c020d020712060207080d0207050714030a0510050a0e0109050a0b100e0a05182a0d050c0603060a051002 70
    0x22030150030348030900e010707022025207083c007044820303070310240c0c40b80407207607045203042d25a0b440400050741118003000140c4401d4081510351401940303c0c8a103000c0640c01c804600300203460341d200701d81e40e02448074014040340001c0c0040c0401064207000d41d60042c880d0340301c84098400046c1603905142e11003801000319845402c0d4502c00c58051080c5181b1802a20040200524010489200c6141c0c070300f020f81060380c00103020052024010498403558803890095554480300d18186503100c1c602c3c400c0c024140c40e0140112071f21b14010444a02940d040802040400508048600202030181c4a0145540d440307055400d140400c2c01940c4a40f0301803405400c400d8110304000000440040c16020268031074075090280301000d01c2e000da0000c10f51003000801e643e0b001884442041590030040c618420039080020242911075680d549070984203410340300142200034404000071702400102141c1101d1402c12460504001855100c0401030016000d166500e012801c0050f40030310b10741c01078002c0c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 53824482 1250 53823232 53823269
    0x1502150a0608150a050901110301050f060c16090c050319051f120605070c0201170403020705090a020d0b0303030c0702040e10020f120601021902130f0e0c0312040302090103080c0304030c 82
    0x85200301c581c49603030000240a23004030340e2001d450512050040c41d01c10310340159100d142c3d0303c3e01c40903905d00000c80c10032030340d41c3e01024200c0c1d40d6906c260b100d8545600e0410f951080d550303100300d041d40d0080301c5521041c1703120000002004081e00740240b00c5000c40c00c184007029214945410020000e0000c290402141115070130844140c49005090000303000d450000b11300141d90000303c440301501808560f000b95125490120304021807640550360210082091000e100c0040c0e0040400e101e03080310400c03110050100385074403030000301d03425413a14a00303200710405801d0a4101c3c95070240ca0405844a00300301c2581c4030120307007004500191151000c20481038181c1c4054445400100034002803030107603406480144030003110740d4024055540301008a983d0080d5401020b02d00030014414407102c425050038503680c1d00041c0250f03102e0301c10307807810901048035a412501504e8003e0700130b81c070a07070858445603016800300c1c0360340c4454401044000041000d8084000c09401d0b0f44410361810340c1e4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 53825732 1250 53824482 53824501
    0x606060302070620090613080a03030209040c020703030905040209060f0a0206010608130804091812111501030b0414030d0c1806050310060305071403090102040e011502150a060815 79
    0x94803034482844e444c030790311501c0d07210658019141d0590040f01d5450b682c100440a24004000313540c0a2002403245d480c3c01c03030405806401070a104041918100004039080a04a9a503001480003402060350241c0501481c241500100354429000d000c8070b16000d000e034014500c47e407081c046100141c022200502000d0390110705150008080410040e0440d9103413110401c42c07141d032045c1203003540c2d5555150b10003096501280d400d6a0400001c0c104848403010180502c401045110214011031503031003011401c0e0584c1a05994210524201c2951603565a180341c42190304140d03000d100501a4280c07913a10390040a40004081c0d40d02403502076031b011a124002c81d00d0f0800c07000e104050007041610561013080004a62042c6400300d15619404015a9064008605041c03048400007c100160a0540040044913101401404541e0b40c802c0d1901035000e5000c1c090006070001d044001141d640c8101c820313088550048000b81055a80c500c0f6031900c0700b044110481c1c412518100083c0c1c21 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 53826982 1250 53825732 53825741
    0x20306030d14030c130b1b060106020115030b04050a0c1202010f08060d0f02120111030f01060207080d03020703170103060b030f0705030705012d020615030a030507020f030a06060603020706 83
    0x103060b070415440300c0030002d1591000e0f01008180c40003020010a05c04943c040e802d100c1c1000f40324281020750364200b20001c800c51240354198560061041d040005101841441401014840044070301b0203281140c0d21403a060201a100b60349034464002a00e010540b000c1d00030b002002409455984240035100140c0603da2814580c41406112010040c440c1c81d00f180d0300410603071090b403803902280d840c4002a080300c180340b00c5135025807030414044980c02085006500802c0788288440d42c90303070f0300c4001b00d80d03480303041c000d05134a81c002800c4006528026000380150a1080c2800c9441d88510340f01c00481100c2640144c0780d558032840d440c40c0300d080c2405480204118440a491141d0601001c0fa99558140c8503090400c0a612082e102244580c03a4112400130508280c40702e40c01120b40080d07481d02d099403005c3d6171004881401c01c0c0f40c81e001548140199150b00d5241c1001090740030840511f0810441e280c060240443c1080000c40078030804010b0030003600c0c0183c594125051140444 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 53828232 1250 53826982 53827003
    0x40606081c031103100e060a03170a08060a0b1e0d020d050403031406060901210c08091207170d0906060308031b07020a03020f01020307210f03021306120209090a02030603 75
    0x500c42001400302c291407410381d0f1170585140c010800c1c6a601d50034040344803040c142d80080c12008903202c41d001c402c034800b03000b0b200c0701189603201c10264841000700440d40c0c5441c49820142d400410452010802c0c00c1207140704040e0125400d0304060a0408103400d81c1e010f180001c1c1501d80c0d4404000c10103170548607000415100c11045070305850302102254451041c1e0340e40c2d90500001454500c10811494064040202038244c20b1000c036000d0721010703001c100292240615800384c007410500340c11040040d03801150308610010700b003014141c40c83e02c0545c000d403603081849403102890300c04107800340241c000135441600b4140c0e803498400d212001240c6103840b15034002400700a140050781e1411110429207404503004640d1440304c50042c0e103903100740a00105880400b07140003905d00c5403a41c913022440342c80c0e12504401c011100044040b4464440720b16032505507614140032641c0300d0314500e00501e405890043c88c2c000e503807000818080b001c41b003664905c1d40000030049103003414408032011 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 53829482 1250 53828232 53828261
    0xf0307051006080a030905121e0d02010c081509070909050403080901051e0a0f020714010c0e040c17090f1605031e19080f0708030402040c0e0105040905040606081c03 73
    0x44c110340d80d001040446280305180c8500e081401c0305102c050103120124550301c1041400c2c01e02042450074980b10240131140e4400343d480d1a1440d1011809452100d204000880c0070049140d4108200411780302c029001d4420025032203000b00341c403c0c6900c60075024a010f51500c0d0010320b013040b60142568801000747c80340d041030345000700011084401594014145410200d08805071f400074400074001e0080c041c3c102c95a08880355400b60341940940b0842980d5070b01d070b041d403901250030f000c00d0f1030250700c1c00c03030000305c02c4031000a01d1180d440080742c01040c00e0007540d20080c09001c0e11841c0407000403d440d40480740c1081000140f031704111030341e030203e50004920001e0031044a8540c442c03040d800c0d4004400c0c04201948108407400c021250200d407003402007074076074456081a001c00e40046408130f000e289800181c000213806864550640141651081c0c075060400c070140010f0003010b03000704e07400340d101c0c10049004001070091030800c02c008640d644140000117802421f9800758045080e8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 53830732 1250 53829482 53829493
    0xa050c0a06020307030311072307050f090a05150909070f05040606020304061d09130227070e060405150702010f0305250e1e0a080609150402030f030705100608 70
    0x80340b41c01206448105405003000585c801c80d00f1001807881c400d40c08001c1154401903011117032031900480e400c2c01f0321202000c8400c0780c0e45440c14071650350510780b40a41d0000484000462000507504100ea0181c1e031a080c80300c5050814003c1a038050302a40c42c074140b50402d11092102010500c207680040c80c04542c00d118092401d003019450340315a000365000c000c01c440b460100c2d00390700803030800c01c400c001e4424451441c1220000e401c400740c20400300d11a1440d29030701c0c009002030380407040c408404282c403a4469242e880c0c080d1130203103c50750042d40189040c0030004440e900c1d0108071045200e08240d00b60344001c01c0c800105520039a003c0c203010f2629100c240800030f035440c0880021903081c2e001c08004071404580c1656002280d070481039120000c458281264403504900b80f03020241601e9054002d500d4400e10754031a5000c94403150180d0212008907900c2d0114600250414009420340b98401400d108030fa003554410b410030b0300d0035170003240800a0204144502c41c001c12500d8041c00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 53831982 1250 53830732 53830739
    0xc02030717090f18041b0e0a02030709120506010521010203090615010c030c02060304020109260d03020906090409080f07050a02030d030c0807030507050d2409020708030109020a0306170a050c0a 85
    0x82c0888050005801c5100c00fa9540c81041b0300c00c3e2491016202c608810ba07050b00c0c1c10010000a0352003202c0e0740002519042000405200700381307075005040c0d0b11070060900345e030034130003800891074801109019640034001c000304621028402180914840300142c013080c40e081010b14000410041500e0401c600c1c4c070a00300c0440e03881400100700750b41c111040e030394988640c001251b942c540340d00301d44c0c41c1c06482c00c01017a21036120000d96a6040210044d43e020300401c100690490017503401c141c3e00520300300a4062185440d50011102c944141090341c108920b90119032505c1e02300301c2c811a40daa000210000561800b04881030961a01e4070b0140151005240020b055800c041c040c02c05258452000c50066401035003a0b0f40c0040c454a000c001c910011114003c0030f4420603014604040d04c10300204591380c4034022a80140d4008503424070396441c00d000e01c2c00030742c803100f1401e041654811010802100101d01e0628048444004000c064464107206041503091006c2c2e0307129410380201003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 53833232 1250 53831982 53832019
    0x305100b120d121e05070905060a1704060207051f1b09061d1e01140f09010c06090b010b0306120f0634090e010608010503100c02030717090f 62
    0x1207011200340ca0003d80d051421082034018110003107801140400c212080306407204a9404944950200c2ea0f030304141607038540c1800994407424602c440061141700d4815481a61000000d420503c9070500514008043e02c1d40703810040440e00c83d144070149032902100340030311802422064203035211102491110400c020342211102c2c452203046c00800700341030b03103807070a00245402080d0000d000200c0002c0c003400c03181203404c502ea010502088107c01415061816001561203005460b0303601450050340000540d0050500b440449a4580b244410310014004500c800d00078960004a20307100c0c113102040101241f1440803000056122401c1c0702d51088000030855080018160343c0b504a803842200348400d0002e00e000c0c0e00c41600100c50801c5801d0b4000c100408a640d091601141079807620f80440d40d509080c41525455440200074020881076644030303004440003030045a01e00001c50340c40040c031800e900418440a031003c2980c5245003004641a480340e0b00484003044a2518100c14 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 53834482 1250 53833232 53833243
    0x30702010c030507051f0c08010806010e090304080d09090e0c130506040b0603090c010818120a0915030b0901120b0408090102010603020603041b05010e060a0e0303040f0305100b12 79
    0xa41003000e1408658103250007041101c40d40c03038002013a00d04100d9140140144801c1000ca01180d1514280c1e10980c40703486952805c2c1680c22020241c0b46691130030518030141480980403001a000410002070941c10070040e00a440070b05032105080c2c18904a00603085860361001e078101f54201c0010200d259440e0f40465240c5802c03820001029240c0e00041402840c0d2240758980020f0004280304c8498000100b1940355807099880c0d05065995503803c0c28801c1d54a0071090043d07009444441400a45030003410b0703803580745d180490202c3d5460070210b100b82100031200000c01c3e1344454200107828410a45405004030f06004003400001c1d03030751160000c2000344042d1140301e01040e64585c5a1007900720100441d00103224913203e0400d41010407007252203100500b01e680200d0400180c43d401400c200d00102c90041695042414005042d25088846004640c4c580408c02010450130006130302400034501500040c403060104104003001c80e43c80300c00040c8190180c80101c41c910800050707 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 53835732 1250 53834482 53834497
    0x20609061e070c06061715130201080a02030a02070204061404051008120c0a080f0d0605010905011b060905071203141912020409090b040209061516080708071a0106030e03 75
    0x140b8120707500041c01c081c03005100c150046d0313460002000a1178080d00c40042d2100351400301c1c034090811521856001c0201d00b401c03102c000d010030507000c00a07004a441f0317400303190303c40800b5001510780240c2d0f5000030115503041d00702401e0880c8031100c0744124100f80c4100d980c401030620840c10014204000d00d0358803071008c0162041481c0c00600c484c0b40c0301c1c041c0451100d66a0000c01592550300070040320351540c00c40010b0b2615940340c090002019846540c00004565068465181c1d01d84941c000940140703565000b41c070000e40340c01d20800058400c20a200081000962038081c00469140007800404a40240c1541d00360911407580c0444480500e6141c100d200d082014480d0300c85403a040c040c6c0160f501c0300c1131039071500c040f9401388460400700c40d110700c2c801c841c01d0394160340f02801c1000703001e0f035140171a500c24018000c101d810501c50104854a40c051003415060414035a02c6014550108404442080000d8846a0704040101206014180600b03050000f411112901d82d1341780181e02 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 53836982 1250 53835732 53835737
    0x1406010807121502040605092b03050921030903010b040501051f020f0d0c06110a1205060a080a050c040510060206040b0a020d0f0b010206070504121202120406020609061e07 76
    0x2074680d0304104248000355a80e480d03040b029910750b03507500384c0609550083d20146003d03e10007003e140018044510b110070400310501500e0270f202d074a86007191070380c0000c06078640000140b12540e1403015a11120b1460b440308900442e90b400c0e2200506003964240c07082603020b07900740001030140f80e0f2210041040a600c40002554003440b4070f0302245001040c00f80705805001c0c01e440131049680c40306072144036074010703203081c41401d0407488030417828402d0030580c20010300c010007090b06400713035604055000a4001d0500240d980c0f5250719500b0030f403010340300300c071036500c807a52900d4281400d02540c0e51107812001e000003001d103813940181d15940c0060000f02110081030008200070402d60584552017017002c07003085802c1c02c0c100701300002d000002010f40503100310000940d8061241e8100e030180d6062000c510303541003041c1d940003908910b6a105a080d070156085090780d2105000c041d10003070088c1e83c010200e604018082a003010b401400b0201c010198100d07080041c12101c4000e0703046411031 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 53838232 1250 53836982 53837009
    0x20f09040e03040f1503050c090303030402100915090f05030604021003050901110706020d0b040e030405060304050709020c031309020307050a081f060306090e0a02010225030203191406010807 84
    0x8540590a510a0b07130400d95110111007004520710904100b1036141c508140c600300140d45a071021074416005000180794103a004000140050a1510550f051403a050404c82d840b9519200752104900c0c10307039132070300c0000c2c01840104000020700340280300610041e00079000900f010b80114a58060303000041050644550100b44400303c2503010103004144d40d50f04503210b840f149801d501075805200100f0040e13003440a084840d00c3c0510550740c645406a000358038081c98501400800d410041c41952076000340ca60014458040b03000070300c00c0d900210080d40c2e0b0340d104d42c003407140700425a40016044520500c04c0200701038000044036a200901d04006440717a0312480007408c0102071600b8940d00c0b05903070200148654158201a080d41c001d8038040c0442d0005208043ea94400418045d0040c1d10050a42994003400c060b034600b046586010380300015105e4001c079190400c130526504400c04200703511410b1040003456000021848400b80440754540914141c0c1c95085004081e0300c40b511 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 53839482 1250 53838232 53838251
    0x609010503070503190906021215010f0f0909090c0f090b130f0b040903020105090d080f041b03050706171e01031118090a0314040605030a0c03020c010504050d030e01020f0904 77
    0x7184045804545c2c00e040a000f61121342c81d118000e50000901d038141e54031400c0100b0000e500d100070f114202e40040c1c3d00d041c1c000c1c542c50000c40c0d802c80c0e0362451909110b840340e80403036044007602609071928010701c08141c02c140390044c51417184405500455081c0e29000e05086907503101c0c1460300843d2009903011841d241915404002084080242503101d403424500300c0405030103411103445aa120400d40700e1401d4000c40c1a9115401100c050b0903640a200c000341c006400d9500e03402148600919007090540c9a5072018a4017178560060030114500200541528101264251340103540603400711408a13008182c41c108a418000100071b81c2c03d204038841c081c0c0b9281100070b10b5a920088044144c00d10101140e1190f014280136400600d502d03c50740d00c00d40540040b98121681a40c405241d40d5030724168100401c00d201e00f00c420035401b0040c04940c0342c02400384500031405440909010218948050100c480103602490396900501521482c03560800503030342402410364000c1604040b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 53840732 1250 53839482 53839501
    0x403021011060a0501080c040b030a0204020703020111040303020a0b0c0901211104170601081c0e010207121202010e011806180501050f04050c030613260313030e0609010503070503 79
    0x1d00d04480d003214400c1d10104040038000c3c2e00000c1c1201e0071201a0341c40d0115003000e0005444080f400250194000031265005040c00d500a020b0700340240f000042041c10080c1e100c80030b42c0150300c25401a0b0000c4e100c8002d010021038801d4014410b019054a8411220b00180104104804c203d81618494815503042042c58100080b80c0d401404455a00c50b01c40302c40300c40e41040c00040c61400d1040b01d0020400e00c10020f00909000f0064290481c0402c070101c00b1a07000c02c1c80281c1d24114003941c48005000c020a0341c1c44462580311303081c13440e980f80e01c40c0002801c4501c5290f81040c940c0c1807516000320a0b034040c00407801c03180c00c450007140700d101c4076020f03c4441050300781c028130035840c0208204400c110034104034000d9215105071882c410111007003680d12101a2542c1070302000074001c000000306072649411101d28070691200004640851019146d04100d0f088481001d0520389402010b81c0300800007400314044035411f00b4110305400003440b6000040c102014002c0000118500d0765 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 53841982 1250 53840732 53840747
    0x10c021b1002100510030c0806041106030703060e0c0306040c020706081803090a0902270315090c09070f14120105040c0c080309070306052a030c040503070f1502030a0504030210 78
    0x140d101c0424042810601500917034014607110a0f100340b552650045038984010600c1030107150000b00b000c9400440c10b040154582c40688658240360380c035007000071640405646544100d2900c41c145440f4945881880f05554059941c42c085410800e0b080c000503070000e03078140c0c0080305071200d4500720035581d01080c038500c1607081c01940b01c105040002283c4420303400070080200c06e46640c80054070b41210040b0380c1c031000c96050f0380c140c00c4001e4504901c010305d98050340c000f07829011240c215202ca40071800c512000e455142c0050401c40c80500c2003a0021031902c100b179203d90f001031030716140380688003140c0018007030580f24030f8036116110390132032144c94242c185540140b00107540c2c1c05e041c21856560001480103c0d15242804001409409107811007002c00e5007000700354207900e1034010210480d90000340561402541403101040b5a1402c0000c4070240c00030b0341a00128504090007a04a45c0c42d4142d404110741c020001400b5056004041ea02217a40c1560040540c1210480984080 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 53843232 1250 53841982 53842003
    0x10902090414120705030405042d0b01110a0206040e0402030a050d0e1e010f120f09062405030a030f02121615021303021509090403050c010c021b1002 66
    0x481500344002d215440b0003003032412900d4000c550f5005140100c2071003500a4035806005508140410001403c00d81c01080c4c14103d550a07524070007440070103901d0010000d610300c4800070344d165004442542c200d041e4015a030100f6000b0041242264002240d911a030f004050b00315500c0b6002c5001c40d1001c01011000560210903100341c144501801440c401c425071819104024030400d801c141021380e0347c0d00302c0b0104184d40f038940b00400c900f0300303469841c030490a030305960f0b96500302511044150710959070140d2040b0303800f0501d4400c80d80140000070b084503400364161500d000070030503947c1c0054040c80c85a851b060050705aa00e04c1000d038103014a0541e0004a80400504c981c1d81011002444038810702c504110005106510f2010089000d08651605a0070b070980051026243c04030141880b0101e150f071a42c0f13040581c202080f1442815034080740816004140390750408404e000e2809003403007601c024030088520226078020207102103400e50007000c4c1030300c2040c442c40c400d01800c1e054 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 53844482 1250 53843232 53843239
    0x60b1503011a1b0a050a060c05030c12060d050d050408010614031e0c060403030c031b0b0106030902030313060201061805130f02040f1109040c02031204110d06050c0d0f0e0a080903010902 82
    0x1152682d0170103644440340341d00100ca80d1490007030501c40d070320300600c1580d002d17a100d146410704001c5809a40c0d5451880a029141e00030075100c0b005c0300081040200c0c240c00c56255880a44a45c40c050740c09003540c401e030300030f1403500911b00b03441300391620b00007980481c8202e800210b030065241e00008600303120202d5012038004030002000b1050542001c400b51150f0312035940e1f07100d0b442111200c0250400f0189009240d1f00f101c5004001c45840303600310740d040b10f0009003900c2c50031550241c10003501c0d030154800000f50751220010482c1d051001103045003106150820b00061600f003040280001c000b50000b0400e0218114030015912164021644191460030030017076080710350041007094004409640c812030a2030b800c400350900c044181d42c41c6e8a030044081050740c0701c1d5540d0581d80d0860b40241d0750851881415080031404074000c1710300901d0176800c180d0b0740d104074684100c05c0e2a540b10307600b591942090b0780c01800100000e80030450301d40010500d41c0b560200300000303015003100e5001a51 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 53845732 1250 53844482 53844493
    0x20105070b01140112021810090504061707050a140402030703060308181c0201020613030c080d020a0914060a030b0a05060a0e030d090e040f1509060b1503011a1b 71
    0x400f440462804062224240c03191014282030140c0c401c00e03446001d0700d045009000150711078490030310040c1981840e8082c00c0c0700110540b50400305045801507880214400711340040036850300420f0240c070002c0c1030142e680303856980c10080220314940d803130140140120b80c004001030509200381d010348051580100980d94403200700101d001021400c8001522907804001c4040d001c844a103c151042c59068015003226a03508000c80016a0100c00075003c0c04082d8422500103007a00c130050041d48150032006840f03110426000b051080d19410041c54403101c4203c04546640300740a84241840500d4081000011f088c0800c2c8a01850340c841c0341c015030f0202c0d410002c1500315809003020f0000354101c0c4c420417003c29088030520000d10644904032140008a004640e5400800c0c440c50f0062a86500c903c1c075803801e1004440c0c18590669089556403160103007480d0201c40c0000442c0c03602c1c50b99065505108065032805620503030700090440001d401c11520000002c90103041e0005403c0c0ca0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 53846982 1250 53845732 53845739
    0x90d02040e0307111f0e0f09010602070602060703060e010905090708030c031809040812090a0c0e01150806030c0d05011503060e0708010e0307030c060e1f06060809100207020105070b01 81
    0x96594010503001c55560300c015604c1d5100781401c044080040c08038280c082e415011400042e282038054402582d009400030030300000989612a55034001d1005078000c10745149015002800c01da80541500109800e01908001d0500e0552b21a81540c104800c0007665481e003c405034134001c03155000c000c10f8040415150360b202408805440c2c200300705040e1000c0c4e894401c0801849141c2110024803640090100030040c0c4003080c80103600071058421601d50130b901d42c80e080c016400503070000030340c1155180148440c00c204100007041c2007a60078560020f0800c1800203440b41c51300c1e2159806205030b19811024400250040c8230001111040d501d01c582d22030800801030000210b1181562003080310008141805105008070009498055401d156903030342d080707a40c04142d15003507403181c0d11403040002c0d0326014080e6460340eaa040c9001524403008062a00030340ba010340c0000140038010040200c10a004a1076500110350848016074591140c4016946402a001c020305025040c80010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 53848232 1250 53846982 53847011
    0x14010e1003020c07060314010b0a05042102041a10050f0d110702040605030d0203090618040f090507080a0c0504110c06040305090102060c2503020106121b05030d080705090d0204 78
    0x24000750880d00f06a81c0342c01d4a54400b9803e4980c1040e00c01064403814004000720f0b00860b0140071900300790f14116140c1541c410b02c0410100c031004000d40c0d25105641e0440840c0f0b0184a00144502c80c94007990301c40180c54001410402031504240900c240002d09548000e80c0303404844600380c2805c8100b21201804030007400c2604060382c01ca0040386008008580c9180001d450084c1d01260360046d444d140e2644d0510445812050001c050004082542c81d840d503141d0140e00740c4418900b07000103142d41c03141001480c042840e4000d0300c1d16041018000c001c140200030103005e484050b00c0110f8010b40520080015110f094402609800360b04117000405600c48010021404241d08443d0070f926200e15100b8039106440271154552141d940700105c0c0c07200c200940382180d0180c0000184c10303980f40c1050b10030b95242402101e1034034451801c5a1409101055400541021b600401d0625041e840240480c88040e00f4882800b8001c101d0300c0076581d03007001d10321280398040c005010f02c1c0301181e0309 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 53849482 1250 53848232 53848237
    0x20a0c02030d050408030d020d021b0c010e040b01050406140904090b01030b1024032417010b03030702010c14030d0e0c01080c090418060911090108030c0714010e100302 74
    0x301c1c0300c2d0103010300041c95240304900782c6040c1d80c1c070000a18500041110311500951201c440030340d00395000d1001c07010100d5580484000c6207203900140002907540c0000509036401c00c0d0b120f900c00c80c42c0c10410030059034000d080c0c400b540e10307508168401501486245500303004225400c0e90103401c140c079840820002003c2c1034103d9101c0c844078003107621607081c542002800c0f07008105400d00c40c0480c200344410800703c451300d1001e0350b003000101143c0b02c481d00c06507102800340f080c4104000d90000c100b00b0140100680328803003c08001c001044e00c12002039101d12502d400681040141c1d001c100c1400241020310356400d14034001c60b96525800300c501c0024004001824480d8020342003421540d5014000d018460303201800e900d8640b110a604100c000c1599010b41c4400e441d590030103000240d924420038081d68010071801d1500c0c0302000412001c007805801007212a0010310100c41c0d40800051140192482030030038041801003640102e90b0304046980035540f084500c0f507411807441c0c15500 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 53850732 1250 53849482 53849507
    0x9060603080c1002120f061f03020a020c060301080604110310020a0309060b01020c01020d03020a14040b0c0606010c0c05040504030c06021b010b0a180b030313090509070611060f19020a 81
    0x503905a0950442c5030804c900030380081200000308080050316500e2507049032544101c00034040005c0b50429112160f500541c5000800825070010384284c03420b4040088150406049808a02d55810720700c132a5110403018200424507000c012141c552903500340880649460201d604548801c0d8921004025283c41d40050304c0b03103031800320160ba06500c0459039504c004410380080200105404c4124001d43c4821001805c104541030070a00c3d4000b0782c00200010039640c40c0458942c0110301c0141e08003103010300400e061000c1e25071a9400200e01440310004c481044070001003a6a0b01e007000d5030302c1c00f1840401001d042c40018449400b10800d007066121020f694001c10010011105101c4a0384c010f000b00021144801070017040b50206802c0010110380240542e81040c0360203041d050501d400b070300311741d0f0056122010800c03d14001c0203000001c01043c07a0007102c3c059941c02094135510701514920b80e14513000001107108c43d141020a5200e520034604540e2582c4038800185804100c24 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 53851982 1250 53850732 53850757
    0x201080105040b030a030e0f0301060602030903061e1603060b0a080a0507020303070509040209150a0807021c0c0204050402181503070b0702011b030c050607051206030d0906030209040906060308 85
    0x18004201400c140c8120400c4020280040c01a07000c1030b20305a88642000400550084100f141810b054600303005548c0148000d4008545400c0410101404d20728000d200b0b5205081d05421081c1e04da084440341a005031040341030038245c481140d400c601414045e0059030b2860800101f00961591080b902441550b0b800410401c50f140c1010032038070781c8820345070100064001d02494003a80f500394001d000400d002032a400d449202c2040340ca80541000c000c54001c15904010091110340501c6180010006030346054101c4d80c0801c0301a0104d425400b0290055965038001811500c6407100a2000381e40d03000380840314506045842c545281c00c004450080c010000c0008200c0518015100340399070585620480035680c15590080c001c40707103420750420a00b09000c0c0c000c00c80030303c649401038103295507940d9070701c810251180d054100070341034502070340c4a05c040040740380d070203e04101a1801c914015985000e40070003d0007401034a58090000c1d450000000200141d40c4002d000000428 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 53853232 1250 53851982 53851997
    0xc050102120105010f030b30010905030703080f10090504080d090809040b0a0b03010e090a080313020109050907020a06020c0f0f10200301120807060c02010501061b1119050904060203040201 83
    0x705d0301101907410004c0d00e02d0300715000c600c103074040c07260f5090901c07020440c0c074031300415042c141541c1a081d640820f0b011b6400d90400542003003410b41c450f080707aa0188504001a5030b0307003440140f04814407a140700d400c480d241d0342e001182c1048420b400700e4280c55a4030100788a40c0720036003800c0300280d10400b0310f248614601200300380301d824110b0300d03072003100c40003c40e13242140e107006071802030104000c01c501c0681c0102002500021480c8002e14000c80c06500b001c42080e81074400900006800e4020612403c83d04003041540703a40040d0022106034407801c00350712040007201e5a4030340000c03540c0c0f04029021380c90080041d030b0300020b045952001e00000c103029441d1561034052031000c1c03040c28240500002c100500c000f0769603c4044020318030800e490f13417a000c2d01d40c0f6140101c0351168403170030040c0d441c0c0004100b059400020704400780200c56120101b0080741d510306100b101600d116074021b14400e034030428520000701ea000006c00000d065601d4a1915281c010000d41c4200d604034007142c550b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 53854482 1250 53853232 53853257
    0x904050d031a010813030302070c03030c1a01030809040903021c0203030a0507090b0a140403061404030807020c010203090114040906080607110d0801031b0302100e2d09070c05010212010501 83
    0x1c1d0707402d0054100c041e180e46400f81ca445018503580141000e06800303043c1c00700aa0300000390810f00c00c000450007640c442030480c1482c50724400c9884004d01c40300004100f100144003051390b00d811104600710489000859042924099043ca40040c0c902421000000f8013007518a4020000b1803280921510420807582c40700070a6030010054000e58030412428072207003111074005c00c2c900b450100112602400e041c2d40b42d83e0306055a19416880100d4503540307081c0003c042d0001c60003070300511130340080d100c043e100b00e0000396607018241c07019040054a11040620040490469002d061074a009000654581d101e5175a212000e40e4840001003a02c424180003040105e81c183d09842d0540e142c0304581d01c4c60304e4410b040c1005220005001845580001c0141d4605d20300b0708d11120262100f01045440c4010001204103004a4102d9a45900c0b48c0c2e506641101c004540b47e010211146070091300d510504031400b29600c01c00407c19032000174040c078041100540d40341240e0090703a0300d41d140c0b000c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 53855732 1250 53854482 53854511
    0xf080108070323030c0d0f02191e080714070501020f060108030a1215080601050102070b090303030a0c0c050601030b150409150507050f0d1a120c01030b06090904050d03 74
    0x310740b10140003103e220b2031101c00d1480080002d5080340c070400481c0c3c00d00403120420782c1880c4069a040000c46e22903c00b083d040b6030180500a00c0384d503d5401203000b031a40703840b850300d810080d101091000d10402e510b10100140c4d1410744600d503412400c0c0000582207031075415558045800350b0740c094401c007180041340b0b0200041660580c2d202c18041c5051505100c02a40c40c0180c00c21103996480c1c5a129401040321581100001429040e0080c51030b0b5150a001a040c034001d42c0054800031700030018420161000000c90303420203224040069119242d52045482413880c1c0703001402ca0041d90000000e0000c2803680c00d0042c4521640c0c03005040403042008200d850000d00108580143c1d086288089482e50120b5800b2095042003803821412504422156100544200342c40790740e06100600c01105099818080005503503041c1000310b007111003941d134544841110304140c0c4030104003205444000030345520500160002c00750b030802d8034000c1e403580007005143c4006440d014409000c0c01 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 53856982 1250 53855732 53855743
    0xc090308030a0608120f0a0804020d0b040b16140f0a0318110102010c030b090604090c26070501020106030812070c0204060303050a020c03210310081603060c03140a021b07060f080108 80
    0x5250070720f201e180840b2502c040d0f818520040099034021703455441d5601144c5043c0102cdd124512411a0384102e1400b00b401c1070025010300070130710800c032001e0f1a10244060040440380d0090040d030003140c6a1800d128110702516048a8100c900b071b001c03810100400c600c2c0c485035040b03940260024030034807007104002c07006c64207102200c40d404000c24000c1742c034a08195009581c1c0a00a03540a0030464541d58407000c3c0f5041d41101c8801c036440c2d03c144114084007407054602609003440240f00c16450f40d00c441c0040c3c011015100540300842000c1350300c20b806802140c144139130180092007420b5403030070007805130740141c0c02142c0503006988000d511032401144c500c0e88040c44c409a07103044c540440c0c5081007038000900a44420b0003100020030071280070081000b0342c0300b0000c801c807291419403920b0803e9402c1607007041c05050504400d5110100c0c2480d40b6a8404141c030301c0141c40d04210180110105100301040c035945c0161311000c280254002c100250191090301c4040c5142d070b80d18101503990 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 53858232 1250 53856982 53856997
    0x80402010903060c0c05030a02030d0501080610061107050a0e0105030d11031e0909040c0315020711090a0213030c09270209071e0905100305060102060a0c090308030a060812 76
    0xc81441042c40002c01c40d50040741d6004d2a0f2508401c40e43d066524103141d42d000380707000d00240c2e1010602d0303030504610380200d40c003402008000d801c990505105e040e10350611030080c102405882e000f40560080e0403c0090000c0c54001c000900d040d0f640c2140c0b1144103028010540280545001d003480c0078051140c49500c01e00c04002545000c100d08481c0350700d20300419105c9006001040200e85aa540c841001d004d82e000c1c1400341c160b5031a518015860010f884042c6100c9401800500f0103d43c0c81841c00003000c03c00c0d5950b400a56510401078000d102e1088812000070802c1c10210a200102d039841c816121403900402456200752141840480320951084e001c0855925006c014104445e029420040354100441900808005544071103e50340d07020001a000400420041c0351680505584032124101080103051420000f5140c800040c0702c58121034035800504c075524454903602004580010301c03103803a030416034a418040c1c4a14403880340c8610a0141007a2889804012104032 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 53859482 1250 53858232 53858237
    0xe04020a05040b0a0e09010e010e0d020705150d0207050705011209080f0702010c0507030f03020c0418030e060f13030c05060901090303030b04090605010b07030f0306050102030a08150307030c1508040201 89
    0x1034a050200310192680c0c500b41034010211410000b170300300e02007119038041d07100e8900100e96040c02a040900710b501000360807070f081d400038064041c45030b0003040c0c0100391882503410020004140851048511405124401151000400d44140803012420400f0b4075000d130380c1c801e8070303c60022040e02641c1003000c1c060079070b1008008418217441800001c0408500c103060207621074081d42c17039550405e40c2640c4144e50306075080d00c0060805030706029179034080d20100e5040014840303031020320074018480c180c020244a040400c0e40b840e9a0382c141510180141180d007207541d40c0042c01d051301d0022031031100300d0b60401e1181c4013003014900103055030108041a50b07500141491a20100c010b0720300040071a4109075604041000302c0c00a0203024040e10f130009013166100c0785494000e00c1101c03080d909008151810b40d040c0101c0e030f4044200c0d42000c400707291a03041c1c1c5e11150071745082c0c109401500c9505200c0d20000004000700070308940200c41c2c038917242401d00240681c09450216048400900 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 53860732 1250 53859482 53859499
    0x70c080606220609150f1d040803060103110a0908070803071119090906050601080a0b01143702101b03020c0f010c18050a0515070302160f0f0e0402 65
    0x2c0b089403140c00640701021540800c281d035072a1074003001c413803d0142401901c0305500d82032041000c0300310940700418000c184001d40110300b018011001d01c0140000302006070001c045401c0b03a1080e00700c0a41004c814005a50f22240c00e00d000c1d010003050702c00d59081c0e0013034000000c0c031150080203982c3c440703400150308601d005001c002c00101500c1c3e101c40c81c9940c00e5518011800c050140300300b0703000c1485080002076506040c1e0000d0003104008203030305501401c0030001001d03030f60301100d480c2e01c4e00c0c2800030294032241301c0c903110100c12449841d00070191a041c1c80940100c418080d10398941f000395001d039261445010f003c00700340e0314a6504180310111800d9001c100318800e50060010600c1c000650311485001e0b0800d07400e5a940d004074000042d0107442c000324880b00c2e035140f9401010101c4024000b42e1030500030903007050710103800b00171214021a0750018580248006010039094481241c40d254071426003080e1702d4124011800f040206000101c0c4900c80e40000a011301e400608098 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 53861982 1250 53860732 53860759
    0x106090e0c0f01110102040b03310b070507060203040c0603050c180d03030e1504060f021c021305030d0305040b06090403080f04051f06080c010c0804140301090b070302070c080606 79
    0x4082102c00c039030641045011200f071014003e007803014201518000400c107a49041090502e0a41408001590760411041940e1002c0122040d826030b1890350100010303096030b4540b0000d840d030f401038880c041c144034000020001081207400c1c0010940380182c40402130ba444441c6121100c1c0920214518101d1060350070403c249410302c0d4080c251442880e0109a1000020b0f0003802c00310504a0b1103c030400c8038081c8403c00a10740914138030140440411030404c41c00c0c840000381d03030301ca0000c0c0ca00e803c1e50001d03000c0c51011240d07080310081d1030090110b0391040014500100149001c84042e5402d038600c4000c126149404480c603401150941d4668a454858003800004e03c80080c1044446200380c41c103d01c2c816100380040004040c280d400000d00078500185a030508084500d00c038108080007030613000141d148001e682c281c441401c2c50302d04054945010070b00404210324041c207c0348018080101c51036042d001050503510a0703c0660199654540603540c4107415185d0340d034483c00507481d25 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 53863232 1250 53861982 53861989
    0x10b03040f0807060204081c0302190c0c030203070e18060408070201110c04150f090b090118020409020d09050f0f0316060b0603040605040308091902010c0305130f05030106090e0c 79
    0x81075450080d01410310f040c041d5501e100480e0320951290100350445240c0e0202d401c03002c207280b414521581015840d0604903080c0c034502c3c00541c416802400302040421003400b80d0340d9001000385074090700312254552165260b0070960011214034002030044001041705100100307015000c0d561041c42d040c11f008540d070041d01d00f6082c400240b80306102d920002103450340c0758029080c05a4100380040661400c1c0710341010a02c00e940c1089201070300301900554161202c0c10300e02d046a0002200c100d000c1880d08000f8003910aa41c44946124004580c291016025030b101200e4a446001160100e925940b43c003070300c0e4031410b1903102c4ac541060041340c0900110380ca040380264400d8400003400c4994000003507894005a606441550392042040101500000d209401492000c02050202c0c1e02e050298400168410f000741040030b44444902050300a005540191141848210540d40c4400d0880341e907512174454144250b08104e4001509400c5105620645c04000084d00802c00d018091 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 53864482 1250 53863232 53863253
    0x20706050904020c070e070f020120070f050d081e0403020a030513030512030906010f0806010b18030303090d0e0f060f090a15090303140319110408120403020315010b0304 75
    0x900d070810780070000d04901100900c4040c020301b841c0941e02609040401d0020451400c00a0083c19685840492198601800c1948550b62880b540542c0d0710070061604000464403844000c10a105002044103441c1d000a6101e02c42c1d03000340c0a030030001e407851707805840c00c00f0f050f6000340158211920304008240f080004007001c0e8640d01052110641da0340d00c007845c1003003c0020700726110020052004114061001390b0042c440840a01c03222800c1c440c14a459a01c10311507150352001c0002e82644c00c8814442206890700e00400341c1e03449140400d105d640748d41c0095010340020300d10310007008080ca043c0384444882440645101d0a2404509408800d5400720308c0d066800340250070001502c03146021101160040d035034580368428035515002d0a2860050340c01010080207008002c6256100901c20085400c0f4442c0407420849000f45101103125542150565000701c000007982403005c0303801007045078030030786c1101c520440c102e5503120803d4003802040c0c841d040800109000c03c0c0c15054 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 53865732 1250 53864482 53864497
    0x6030605031926130b03180a030516020109090501060507050f030c100f020f04031406060f13090f02060a020106030c12080909040c050d11130b03280f060b0a060f02070605 75
    0xf1014900f4100400e0040741040a80c070108400c0400001c1001908401540030b0340130340341000030100c42070700b40e4014000c0c0c041c401c9407020390742c4a2405401560b205120180040c0840702d0b04004558460b44001c4c441c0d48111001d6407240318091508208500001c00c4404001801c07018101da207101c40c912402500080380e04500b4a6001e000c03405180e007580000304021807040800304100d4501d41002400c0030700003030100f40310314550841020f85450304004022184090400080e4400d50351a018200303031211240650805400b003100343c1ea05405520100c252401507550021003660382d41400e001e02003580e001000024144155401428a0524142c115204054203003000341c0344c5c1c01051031403041d00819290748040c0c02e44113030281020400d00074007001e80740d428060340703100602103135031852004410415014a07d091403600039079488581c40c502d52008a1054a0140781000d03005000d286031072600c0b84d401d610001a4280c000c030901c4c050307500a40c0240000901d0010700380c0e4550403540 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 53866982 1250 53865732 53865803
    0x24010b0d09050d18060e010f08040204090c080c01110604020d03051c11120901050f0412020a080c03090a0b0310030803070e030a060e010c0e0d0b150a060306050319 72
    0x1200800080c4040c09907901d0412590355041200c4d4610014480340030b1250b200100f40200c802c4000c1c910b90b400310480c4189919030800300480d40303031440450024240c50401502050070407030003080d564000318101582d101c1c2682d031040c1c0421701c004080d88442c42610025071000d0f10b1541d180019024078041c000d0315000d600c40a60f4010100100e40560703007864139144543d2400a03480d40d491152031a01500f02c04918000c10062400340308401c401c2c0c0003c0d0000d130400b89855464180c02e8030070070152151030b5001100769202c03411885100d560382c2002000f5845408128008250619070b070b003d0f02e00c02c03010581280f07591443e42d00c0b4080c95a002030f001d4002c10101d0410022180c0342041180e1741144640700c0028013000920704607003101d1105442208108944007800301c0303560b8080782003074a19002404084941c8540c603100c08521841904160040c103040e4000a00b6901a4403007411a5029800d9845001921000c5c2080140d410002801040340c140101000820303062031036800c0381d400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 53868232 1250 53866982 53866991
    0x10021b0316030b01050406090c0804141218240f0703020a0803041401060b0301080c12010204050a0e07080a020a05030121050106090f06080d05030f0705040515030924010b0d 76
    0x7071800304050300190070603030300c1881d003d00412807070400d440740e40001c040b00302c82001010300c03d28000340005409400602051070341c40c2c00581c105001c1c064141e0869a0000403591150043c1e040d400c80940048000e1113040e441c014919440075240b0306002c21001d400041e0b14103800b800212490317400504e410750071131103100d40038000120100000c6009500985401c88040d003801d03940f50039525560444050f0080510042000b903c1c00904508412411500015030802c10840309009000790381c08190312080506002840f8402c00400d640903016640c0e8030740260351009481c1080c0c2c40740301520000540b08000421590001d0120807400380c0510405a5408010303465103801c0d80d0440d0002c1d051a0394407101d102959070f0394480d04000b8844080680000d500101002d40a4000109480d521818200000726001e10030405c68000c0d1400804c05502c1404520250070240c108031440c1c036072840f65080ca0a94003401c42c400324402c8800440d0820386a01f4040410700c541c000da901c4107500c90720b6 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 53869482 1250 53868232 53868253
    0x13150207020a06120b030115090c0212130305060c030103020f060c030903100c030606080105030a1101120606030b0406050f0f0f0f031b01020607080108070902070f06140f0610021b03 80
    0x10030700c62800801c219a503004c2050110f00d40c0b40e04440703078104040d100ba8902401307101e041040620140488040d0507000841144401c816030410f0f11020040f141000002580481e01005030600380941c3d0181080303c01e15a5148046802c5200078000a980080140100c12141c68080000d142608040702900c2c203202141e00464a4900c000d414000c1d200c0e12070910313100b0301d0340c10b1154500401d42490031800740d5161101194607486a403402600a13148a074a118490b4020000b01d0b402007502d480402286a03140c0c001001840c110318138038070407402c01070b0005051804e1004100c61103001009001941c1c05c1804011105c195210140d4000c01d00d00cac1152a60381d0f0610482d0000700c500c030301c5600e09000800009040c042e00030080fa0074492620b00500c148140052090140d940c0a400103950719001e042a4160302407802009000d9403c042031401c10a000d45001401054489200c002c16151001040362120410030010016440000c40002420400c4503020700000b014090700c44c14280c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 53870732 1250 53869482 53869489
    0x130209090a0614040605011b060608030f0a0207050103020a05091e040e0102070b01050303030906070f020c060c0d0206150303091c140f0c030109120f090b030114040e01051315020702 80
    0x2200c810040959688080000301850880c0f0701c010701045504000c910304085c000f03005140304d484890a0100d050320344100300900c85e40908050404201200c5d12121ba61901c2149640300c02c0c01d06005004804000400c2c2d4041d009031032000c07016485180c20240c114040c0506c07018001c5124004a070200c0148089032101c0c0b04800300740344450e0004d0b0f90741440741400802c4041c103a024901a5008104008500701c01282690300070301d840c134120641d80c0b400d040891a00b520300071483d070300200000700440c0d00c120004840740300c02c05503001d81f4040d648615117401042c200e500c140b03805401c104220102c520703140d240e01540011042141d520075920351900300101c1940a2031440a6001100c0f80ca61482e0401c000c120810f811002801481002d0340c8403d01800c0d600d407404140161011880d2010307025a6807400584520b41244e5160b40e500e5007540000d010440c04c040c002e5152514550b90301e9010300840c2d00c01c0400e0030148201c40da480e50f880002c02c03070721b6003a240742c96800c4c0682801a40c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 53871982 1250 53870732 53870749
    0x207150c030e010e160e15060a03020702190501020709020c070b0c0a020a240305060103090210020705100903080405010c0201020a0b091029011218080703030e060c03010302130209 79
    0x80e120707900021008020090942141d4458400c0503903039114101246903440c25118030415030b14560040c07001500c803070702c1c0c4000b4280e80c5040545e00400105002c018150705a003c0c0c80341e076008440440403040c640e45510011200341c004c1d5401070f08925000d1023021441c0d0020041c80011034125540103039900581e22841d0030035110900030342c00c000c0c1d00c1c0301036140c810300031400f61003141034120b440341042400703c81c442801c032840b6050640f03840008071568007035482101102c1e00640307044140385980100035120708950040c5072041c5480c0e802e00d4500741c4201429404d490b40038281d24505800e14005483c0e02a005104070304510441b81c01c480000c18000c1c5083c06039500310001c02c0b0920806c844041075030486c8080880d9041d024203c90b68404034991440400c03142801d000d903413107901203404009030417a0440444545084003e0404002c0f0720b40040441c58040e03070b0200003a41d00e4080307480d180c98055900e482c0511041c0010310151078011441109061a0440140b1388401d0001040491 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 53873232 1250 53871982 53872001
    0x31e01030c090e0610030b070c080712091e0302040b0d08040e060a0b0f160c0504020a1e0e0a0e090313081605040c14030a0914031801090e0703020715 66
    0x1c0360103602040005080d0041484402c10000988100d250032105030102042510010b402010002c01281006000b01c44001103181c0010642d5074882d6103081082d0700700860f050680006032450000a154841c0d0b03030b14940f14101d0b0503048802145140c0800028100020b070190f400300303140c840c050024010800801c020410b00003802c001d03203810010014a8240c40d0b10003401c49508100c15013582c440385045a0441d4907410454400380c5007420030100403007054028a40051000031002c2050f41c000003400c1d041000e0b40059007060b0344074507007115000581c81541d40c002e102c3c4038092044424a0406651101c982403c607030034640301114100b203100013503000c0c211a0304564030304041100d02d41d9044019001c155811701c5103698064000704804001003540702000008404101400820b42200d6081034002c2d001640040c001229541c582d48800c01022400c03e0030001c0300d4031940510451800c44d122000d50b0000c0f581c61510540c082d6001c0c0d10101d4074000e003d046181003010601c141c0682 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 53874482 1250 53873232 53873243
    0x60803070f060b030a020d061a0a080304090b0a080c060309010912080118110a050705010b0312040e01080601030203060a0c0c02040606050a03140108060412120c18050607050a08031e0103 82
    0x4010760303041040880354200c540500940041d220303800903840392180d13009840ea229200040f252801600c2d29410450511640d0303224002440005114400102400c03c1d03c1c144501000240114420005000c07094812a41e10b0780003c1e404034040d240400c05140e0002c039200010406101d070799110301d80c0c41c454620030000f081239600140011510300c202c0c06800c00d1116000c0101e120800e51028071801040208000c0143c00200790041110a40000c0d542030006030032500d44040e101803910083d00540035154084072000d00004074020001a81812240c020700500842c0d02e88074030101c0038000f5038901c0d10510030803422060050300e840c810000149216541c19481c2e568650004040da1401901808444220b2005100c40500854019040795201d01020b4402841c40710503105514101e10300b015003841c2c002c1000e0f903550000044040c040c9a0802800116201d80070040c240c000d6a1700030f040e550204035034500260f0050001d6402c118010000344102191a03a095007210090300122103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 53875732 1250 53874482 53874503
    0x51b0607030b03011406040b010e030f03040806091902040902041103040303090b070c03081602010915050106020715170604020d0c0201022508030a020f04170c010807030501051c0606080307 83
    0x440681c5803248005154048000b03000c1001303020a803a241c0031700603004601c102d03034480b40d60925a0050b1400f62a4000c094140e845031030b400c4e49866100c1c4c003d4071a0301c10383c0c001c01001585107207010039000c02402c0200e910701400e07080c40e005e100c010301e5003005c120713002651100301c040500780d4100594403c0c2c0c0f107580d021a00c80c100d440c21902c4104043e100005221411208000007030308074040540c042101e5801d4140c4c1500114100c0c050070b030a0304050040202042540040c009642103241600d0264085441d03241d50f03601107103041d03400540c6c960001444411003981d45d111001e8160b402941c0104050308000d498000c4500306c41c5030030a440c0141c1e50000700d4003421041e00b003540000d2000b05020791030050709522500802d200040c9040070303060780007550071401d403684410785000c2c140d0400c0c01c0381d2020151400903510001650081d0108241100003044c907480703402110b042e550090090452000100d048200494038410104c8100362111008100f140e010005000c620f40160300009 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 53876982 1250 53875732 53875741
    0x51c0c030b0105030c0a0503040f020909070f0506031b0309010e06130614070206010b0c0307050601030f051506010e0d1712100e01030b040201080901090209010e0718050a0e07051b06 80
    0x40c21101c415400c141801018030802524500b24002c1e150302c1650340c201181e1766965890724450f24007101d1b00c003c2d0f0142b080340c20b003c00c502c00003c1c0b00c002d40e1100c0f10240740e600c2c0c445040142601003280d198074144030f150115402007804002558105c00101c0000c10310205406d00d0030b051041c00c40e40c40c807800d4044900700003402164007504402c0840c40548240c207080c216402500c501d0140241e03d165400000c4054034a80c040080b03a40190b0400b050b251256180d00c1e00c1c0d8102a00f0b8541500c5a100b01c0b412010f0000400800e00d0041405031125074a0b0005c803801c0c00300b0f44014800907640c1541d62000d003540c480850000307060364228070346501e05518007140715000131720396030304118280488000140300140108942d540c04c00d409007001c24599035810611409020780d40c0d0025004030444d800028160401011640110501d403204103148030880c0c280c10121000d4440d403036010b1a01c250410646240348221504100186003951600030184000068114469120700c1c16a002e01c0801 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 53878232 1250 53876982 53876987
    0x60509011206120f0c0b030c070b07020105150f0a09050a0902011107030308130f0f030c0605180312090304170715030203010311040f020405040f05150114030103030e01051c0c 77
    0x1040365000d02034200300c01410441203110300d45003000028880c007440c81301801405805d00c1054000c024035824907075607203800d4505031525085003004449418000000c00d0380300d4010702072240310f042112400c83c80d0704c01480c1003000a0302050030407034000c0c620300303808034289089004251048620b02000700b000705070f034030006082143c4e0300390403100343d08241d400340700095010b101c0f19040000440c0044c0030030700c0c60411802607454608002d02c00510041c0b400201500510b48500050050b842004650f88005114070b0030440c0c104001c0640d0010407044100400b0204031a421003079960880f410252200310322807035542401c540c200150b11a00c0100510701290140800d41400c0f450b0035070a551559484044150000c10800e200c0c948524144064000c241c4c1a1002090010018821280030b0201e0b003008040071b45440052500252031101d4030350007151040c50130000442d54600d903a296843c100e903108990b10400b4100882045000c1404810201780e00504c42121000a0000e030401c001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 53879482 1250 53878232 53878247
    0x30f02030c04020a081302130c0807080901020c1e0f0f070824010605070f02040f091103010b0916140d0501060f030b1003021606020301030501021905030906070f021606050901 77
    0x101e03440345004000c603241c09075010581c0c1b40c0003c02110b0782e15a0101c284005040c54105c0c130004100700345064081d80025a00c10012070266080b919256010384440b500365082c0c4c4240c007500942c1d0350140d020b03c00701c000484107900503804540152808404403c12450030805202c2c13003510315502c40c40d007e1000c004140221700040c05280b107000314214101e00a00400001440341000b4004007180c00c0080c0410f60702d0350003101d80e0040c010000c6c28403903000640101715202080e980c1c081b0b0206070039614101485014400c2000400402c515501d562055031610074440c001030811481100c000f00310000700340178205030303c0c00950200d045d40c103082c8020811104000c241c81014200b40040700e44d5228a13408100a440500c0c0160b941d140c40b1100d030345009208a0010901440040000280310043d4042c1c200c546080003120b055070702c58401240d581c08259003e1450360016004a04940d004000f401c00e550001e0041c6c0c0e8200010300e00c8115503103840c3d844400416000940700845603400b048 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 53880732 1250 53879482 53879503
    0x30c080303160201020315090a0e10020406090f030809090c0c010203090309040e0d0801180b06040f150512060409060f09060606090b0406050f090f0a0b0403050c062508090a030f0203 80
    0xc500754600148041030742640398180e98011485c11000c00c2290650381c001d02b8500040200722802000c900c04c0c124001d50042c8a0075000860703500f4081020300640042608070707034210704070501b440440c00070040140c102804c1a07003100020802118090028009036100c0c030b1546c006581c030f9003110802e02c02600c0c8660391182040d00814400d500b6250000520340c11343d0031243ea0000d5910b29941040000c3c609150700950154003c6400a110f04903003100000751410246c40c01c0c1090b40c501c106847c540940c26508440540709070000300c040c10554800c285141c05100086200c15490814a04441031100c1c250b0301240c44050501003140c10038680401400c0e44080903182506e40740b00201103020344024917034110b000140440040d51280c500c038103080401031003100d819a4858000c00954403502c800ca0b01070007070480c910785514014040e41c009580c82035030701d00c8921051186182c0c804144204440da440180054020b40c0c0750492000065417050207200b49120007030041514007180642c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 53881982 1250 53880732 53880737
    0x3010306060b032503021b1f05220201090e01060309051621320d020303040c0501050a0c2012010c020c010f1b06020d0b030c0901060c020406030c08030316 68
    0x9120410010813000301000f00c100c201180c0c101d84e981c00880191060001001042032600140400b841d40172662012681151075050a080b640960359000c3c1d60b411200b810b180800039400004c2420300d20042d40b03906105141c03845040c6e0300d805040c0d0701c2e6102030b005800002c1c1e071050070800f00141001419044043e503c02410414500304040c4036a007081400454411080607100c010441c3e640000300380c40401c200e400e40340c03245210380b0701140f4240441503040c0c0c0c400c6c9036611949a00102c00c0328000c64004c43c11140395400c2c0320042d036041d0700110030703070703042080c407054281c041508200c0c0200c040c1046120b00324005441810440402c0c540a0144030a91410401d0b102d502c2d00020007910800d42801c0442d00c1711110300741070314158051900c0102001210001c80204070541d801400d64240e105400c00844107171006045d079649031030301020781204000005111080c05013041860280c13001b0000b01d460780c0c0340d030f44010b0034902c980c0c003500403030344003000380000c1000d500c44c040c99240191 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 53883232 1250 53881982 53881987
    0x110604020f0607060e030412020118060503070819060320180f061201050c0a080c030402013006080a030801050d0c051309050d02060f011203021f0b0d0803010306060b 73
    0x290005100100700030502407007414002010020030100350002c031042c03186242501d455035030f103900201984650030401c0380000c008000c070b8407041c0000c0140d88255412a55141d043da03507409001c0e10354420280803100040d9440d0f607014040310440c02040051449213102e24860300e102100a00d04400e9551101d104892441a01e141002c5100d0003c0e031094487e1b08a0146481d2034020030a00700c00a41c64100d903500340010840301b40d00190003042d0301071075942c8940c4a1707a0f41013042c998902060310b0083c001a08641c0301c0801e580141c5040f186218650100b1591001142034041202c801c0ea02207991034003c00b6188080c50381104c85540100340c141d5205ca4010301640d522503210344280280761048130507428180c5116101c2d1320031100030364424100c031890540c02c0c201955039001111080340202ea00d000214100340000d20046400f685070300140b00b1a414080304041c81008101c24039032441e039a08500d0b07020b9851710500d404103030244070707036641d07a505500307000d01600d1440d00300940c030700e004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 53884482 1250 53883232 53883241
    0x70f090b010804020607060e0d0503040c06050703020615010e0310060905070302030103120503100b03190501080f070e09030c06010e070815010801060c03090504020301060306090506030a03230d02191106 89
    0x10b1a6034040d5045421942e00d18061420200811081007560402d03c0703030440c065070642d007140041d8022400380c400c264942ea5216030841c0e1a2060400040050b0060004903c410405101c46965820141000c100316021b500c0828544044000140c441c2c80d26a01c04001c6c4a5140c4a4660403828034501540343d90304507224490305c000400d0410080020001c0041d0500d0b0b000284500038201100079a992801c010601501110108542d03807401490030000207250348002a944101c50307500406046000c0c904500c47e101c00c04002d201c824140410805803041b800144451406840c148031174002a0070200001005000c000345110881d2000c4104a00c00e81e80001c803550442c3c11310b25010b0b529480300c3c501295001003d90003650018004400070840a03010380006080e44d01841081020742da8070b1003015928041c0306400303808504c000b01410951000943c0c0221108600a81146004120300e01501241e001c100440940c81c451203400c17400c01d42c4030010910403e183d03402031850f07090 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 53885732 1250 53884482 53884487
    0x60a0503120703090504020403030504050301181e030207050303070506010e100f140409051e12070213051b0403060516050c1203070215010e01030311060c03040303050403030b0d05070f090b01 84
    0x10303201d0440c24521000c58020100b40c8030f20001406881c0c0548107540340ca9a03441d01821640150080c7c62095080c042c00304a060191102c04012031340285a401ca10f110382c05503520a884001c005a04600070602c0105103a101000140030480c414402882d8070740c5403c01d0803c07180340161081c0085980ba050421003804a1403019099034807007148a200c0613101000200203002c3e1210080c09800350700e40380d84420a0041c0705059008100043d2480e005c03280490755280e20404000075444607208840c1a0007080b658040c6501c50480400046044020a1410016006a4070480b11281c41c4d00070440e8404010642441c5404075046c0b4600340300c40800b0ba142c41c3e003131240c1003040310783d40400040c1542d48208854010850032130740352034555845202d108800ba000740000d50105024140c24000b84c41c00040b030b00c0c4036400c8943c00c1400c54507070381d42c11400317040050400d404041d1a16000042c40e9906080c804d81e06124034000d210480c6480c000c22141103e0354440c05420707250410301256640c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 53886982 1250 53885732 53885743
    0x503030711040209220c090803040612020c01090b04050303041109040213110904090606080105060303070b010e04030509040f02120603030a0905090405010908030106021b0307051003020c010905010e01020909060a0503 95
    0x264102d070056151002500403400081c408020a44410990303016400d11521940c00010014030710b5648200340c3d9203981400d44d80384181e00c11600043d0001b030390031a40c4803080d4085c08204043d1000032400c01020b0320f610000e5001510140c40c0d640000050000304441e040d000b00b11020f090341c030510701c2c1c07901c1d40000e100345030070440c0511825215a28407144c254042c2c01c460390b20388000c1080203141c0550501000400c10348c000d8041c01e61822010a10703514000043d03900865100d50454541d030b080100704036008101510480c14480d00340600340c140e035254003411500c24a100c40c010388074488000c00c080780e90f1000c0c020301c0c02a00300304600e000385076000d9500002c0d00e10580c1c4d1300c121074645141c554018222340c1c0f0301411805010001044003540807442018031440c080287d018540c1001c02c040d1101c40704d21a103540581c8042402041602035009800e2160901c000003840c4030340d503101c0900355981d01c801c24109950010f092a81440d0801c900e5030001130985120305110700340f10200e9541d8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 53888232 1250 53886982 53887013
    0xa03050f01050f10032a08180601060f020c060f070b070306030b150f030a1b0b040e01090e03090d0501021309110a0309020a030c0e0105090a14010302060901020f010203010e0402030705030307 84
    0x48142d0b0310580d56450003a0011141c107900b031401b44100800310140d9000d02c0301c01610310800035035108003103840e1180d010025076800000d04050213440e440c0003829504001032408110940c003516425006035601c043c0944901d5202140059503540e092500600c1294010206010316140180500c081003101c104140d101142280941c4842c00020016983c20800c020440d0b0622401c01901d003001100f0513906404100c140c203080c4102c1c1c5400c503040b810b0099021300841403001800400841d8195084204a04c442c0801d43e450250b4950104080a0854070142c2d0780c0da400003001e80c1c2d500c5030b0355a0003006000c0031104000480b100c6440e0f900c1449024a42403c041c5c44030132100556481d031071038500460b40700b61903910950340d0b803010303201e4003609205040c03140c20341d54001110002140030300152000c2c031a01724a0b0980c00c0d5400c100300364100f54492411803042080c00c944070802440110702a054540c3d03010394a1400e4810145015203581049010b50024046840006c0103903000a0b40c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 53889482 1250 53888232 53888239
    0x90c0c0309031401150f050f030604030e040b06092e0c030203040302090a020c070314010c0c0203150405011506020c1302270f040908030403170712051b030103080a03050f01050f 78
    0x110140312803c0f40c0940310002070000445161000007541042e444240c0080b41c03c11382d0322207604e055080c101070b00c5d40d004480c0680440d842c1c40c00d015041ca066801010900001051107040080b07a002051050180c4451046940c1c1d684800027200c8140d003a0241640026103040750740c012455030000d40b2030295100c02401420750001040c440300c180d40540c0d02c0c41800404580c09251349003042461006261542c1c3d404d03510b00440c80342c80511461108400d2074002d0300401000302e00446800b000760000b001955075560300d1508044980c8804000030013080903034018401e50611604100b2950080e1040002c11803040108280485181c8005000704c040c0082010307040701c082001c61503507444002506d138407a00d018190820000782c0b0003c2c42c0580d000340d4407401d159191402c20710301c400007614000b021030b031611690840610240c000c40d5000b18000e21000385e60244050112154100384c004503510b49002ca507030042954144107481e072040107004404100c0d451310020980001900550600 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 53890732 1250 53889482 53889503
    0x30319110a020301090b0403090501030204030f0b060312030a0b0108100e130503070c030b0f060d0215072f030f210a110706030f0f0b06030a02091f0504090c0c030903 73
    0x11018024054040709540107002800551050324200d035103010304031422070105081a0000c981035200b4400e80c0c086d268060340105845070503403141491018000d0500e5814820b03c1018681000800041c50041034003400215110030b0f00c00014002e0000100001c41c01840800c04000210034580196041380d41c80209520039509424010704501c40c0100203415050004400010040d50043e168856801d000c0341100640740d4904100c50306c01030120195002483c0caa002c0380042801008000462285c021003038214881102075065680c11841d407031000c9110150141c2c035060a106006500320302801510346241561090040c40c00f0070198800c81c1c0002041b5140702da806019019196902c2208440e00300d035440030001d010f03180c9800980c00c221309050203041202814001c42c440d504000b44600e04640d2515540e0b0020341002020f0781d88120302c20405880840d0000602000c40440d6440b113540321308080460007643c0000b60b4400c00c00800c03911220200e5030042060f8262940f01c0703900e05 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 53891982 1250 53890732 53890757
    0xe0d0305220f05010903090f0602010c020d0503061c05010207021801030b07230309060910230c04050603040302010c17060d03030f0b060d090c0501180b0a0306030b040b1005030319 79
    0x10012074030b4220050140d07180010f10420b040c0c105210608548480d08204012911210224241c032040741041025900c15407409102e0b5000d07401071a4030940150131212122550081c0780c454200c98141a206654005424025414900e0602c55034000d00c1266075619491696040c0e1480c070003d0140040080041040702200103071000006202180a121520790030007103a40781d256039090b0740d28842da00c644841000910b00a020390790300804807615a08030f5400c01680c440142900034100310080790204070201d00e90f56094040e60003a8042da00000310b071880c68002030704a691504c0e40240301e003451420800c00d0380e65124038040d003550515012a000d9803021101c0080d0445011981c0e0014020074046440582d542c020b814060058502c401307080d6a801c019161102103081ea01c01042d400c82060114100d46001400e4030342c01c51070300081ca03e950782c9034a6086001a14121036a5091400303120440021200c0f0344090031044020b14508140541143d08000e0b850050605100519031042d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 53893232 1250 53891982 53891993
    0x605030603010f0e1b031209090a0906110301030311120313150501140a0b040602070b0a09030609030806101d1c080a0807080a0207050307080304061e0e0d030522 71
    0x2040e0001c10f600074008400d0f201036840c1c80b549058411222201a414203185c2440e00040d03058840c10130320302d00c524108a1406002400200401e400c030240e840d403200c00b001400c144104005000c42806507130312941540350050001c0e40d000c2411000f58400700e845484000440100c0340c0000017614440900501d61a0002c0c40c5001040c58840c0ba03407511000149032000b141170480c003800103d82c900e05c1c03d81c8500d40284d840c01240180c000580c003242040c081d80001800501116100d802c1c800b40050780c0350ba803403094400741c0030103d000841420a014190030a00e00c60701c406a0903040c1803d05240320064444010703140300c007541c850307041600c00f54112245082562442d582201160795681d1035954040c080c0308040d03d88100041d01c6500180c0c40f00814030076140c402c2c0d40100550302d0f00c1c201c5e4a0381c42d49130708003500603034a060380e501c40001440d0328107000403c0001840c0022a080d9043c145e03113402d004035218424241420541048a413041030b40407180461910b1408012290160601 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 53894482 1250 53893232 53893241
    0x10b030a0b12071503050411010c02010c0503040b0a0306080c01020d1d060c01050702061003050c040903030e030a020d030501080c09060405040305190201020301080712030c120203160b0609070e0a060503060301 92
    0x35600700c0b200300812100100c000c0303040d03003d07141140039404615200d68030813001c41c4d400f00c4015109001c90a41c2c04c10350741c490200c447c00640145003052200c50380342c0380c2d00e0a6500941c4845020000041c100c40c1e00d5416010711b0000b04050000303092202503490010303417a00d1400707503400208001c41d00d501c6e2a251041800040d10300015241c203446103441c0d51011f001b00425030703189001d4231910f4009078114407c824044256035000740a81092440343c01800084c0180740f038120240350311102c0300350040604001801841d081540181209411600e01808443d0180c00c0030855400100d803058a5440321441180c220320107a0740050a5603560400300c13064000d00c03aa00024204035502041810350540155050345c42103810b44801c15520298070300c09440440004004c80c00c015800401700d03c7d02e504201815001b40180da151540d900c0411800e032281e010210ba03100801001d000540c140300e05029840700f414103285070035440ca0b00002c0c4e2040050f10603581040b01c0040014003e4500390031 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 53895732 1250 53894482 53894501
    0x315130603030206060f060405100309080412080a080106020d051c110f070b0a140a0e0106030209010b070308090c011e05040e0406020a0f0e090723070302011b030b0306010b030a 78
    0x900300121a1603140003034944c070701992442d214840c240138030b03c420302d80310088070120b0308000c041070100d0454000640251466801c10b030350441b42444001a107058045c115103c0910070400c5560b62840d00801404043c0180c000c80110350140151460058112003160103484040400c04074014603080d02102400c15843d400071030b0000420f0010001c00450054407120303210303005042c1c1982d200c031100011241d070f050b56001461411004071b010b840c5280e001c00d0790919402c2c004a24541c0301e8001c02d4405400713074008214402c000543c841455840905a03400c0501100600610440300000900c07003101060703a0a400e04100389a68013a030301440031540145070400a6007224606400c4ca01d0081d04410f12200105150040c0280039a114516003481214010585000b07915104012551409501c203a0140d8404150f00c0700c41150f40307a0702a0550a03c40c2e4000b144000440708600c1c290f440407002c40c4241403e22403184081d550101d681415102030841c00d6460390380b610381000140c0200304 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 53896982 1250 53895732 53895769
    0x60f01052e080417031006080c12010311130e0d0807020f0607020102070c061b1209090504050709060e040b0121021008010602070605090901120218070c0b010b030c0315 74
    0x21441c016402c0300000344a1070081c00c40b403646104403985002c00d803204071011898008911406d2141d43d00803a092604100307600b07040c0307060140c1c140100e40ca00c40c003170700700f501c16010199002e03907980741ca99260345809800607824051020070f161640c1d61840720a180b401030001c40e0340000c070a01d2007080500300d00c41518044845609150710007034000d62156030706030744290310070f0000300b4864000c1c0e445084509043d40d8000ca81c1e10311f9281c0b0076103103031001609e00410801001c0040c0e80d0401d400350600603400341000c0c0580c1c0b89403585d8641150503603448402c0d00c460703000c10400425180c03000c3c281196032150344480b403219551015800c000d50a98029440305083c0c10030340c04994000c0400d030582c2d9607a000c07a12040c0e1115000c2c0e0707807030140802c9180c0c084e08180041c00200d826110101c036080c40079110380d01c0707a52000020240c1030070032a5070400242d40d9205c114140107088164600500f0f50640c1e1a25506140e03200c00c8407880004c00303901040f500c0c5442c203411a203414410185034041c80d03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 53898232 1250 53896982 53897059
    0x70506010609030c06030506010f030c020708070311040c0e03030f03060a0b040603020c01050f090a030509031603140d0503070e0d050a080c07081002090d15060306090b090f060f0105 80
    0x140400b500c0a0340d940800c1d43c0d059400080410300c1c038068030490780190416150210306841022088024207525148442180900741c40003030440c0742009201c0207035100b0000d0040380e0002c407040c803040b20303034010482040000c51201c004460700c011045445020324002c816540c6d65410011401a841c5640006092000080c0001e040703603040d8040d1100e6804e0300028011a1585d07121105484020b1303a01c8013983c1c01085101c3e0009001c0c0000b440c02c2031024080c0d4039070380b401031050b11000302a80d1040c0c44540b50388500060b8550305104000320b40400e82041811400d150038000d000c01d102c2d00015005078068005902480820400c003d88142d2002040740d03560000940e294884401c0d204905051103580e4020911020324000d079002e014000c0c0c50003561075203903140d030304d05516180000d000580e40d0750301c0070000c58082d001c2c1c0070400b8050042d4041d01d04100c10352500c0c00d8042c05601101d5003142c030030b01010040205981e0304403041100d07080c8180c00d0350507207904400130010081980d005070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 53899482 1250 53898232 53898239
    0x312060b0d0c0807080402030303061009050d030509030715090504050702100905100605010c02060307030518100218010804150e010f05010806010f0501020304060912140d0c0b01080106030203031b0307050601 91
    0x154002c900c0315019659010844e8a030580180e602000545000b50b05800600000b602414a00c82d0310289140b20316010786140e0b5120082504042022025800a5400030b1a0750b20760808020003401864034042c0c034040ca0016000003055240715006440c842c60f210310110b11039501c200b10364103000440c1c0b034042103211503600d0aa5940c00d502c0034020b14040c20418001513942c0a165072600c03040d0054402c500d1603407082022002001c000703000156028042e0550041f898081042c0000740604100c0143e9440c4d600346c150401400b9a1003041c1008082000c100010307400b480a00c0c4058650300c00400c4801c1200c248901418005c06c060000300d1400c0c000148c0c40500042e0b841c120b6680e0204800065141c2c1c0049882c4d20503070042d1404203e00300303410800484200320000701d0314000d507142e01c070b040b004c1c0004a0400406490102c00205a045034105005c508401d40f0300400104008214086c61075020940b02d01480041103040341080e04607000f02003080c41103402031984401030352040d684 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 53900732 1250 53899482 53899507
    0x1003050603011b020a08030403020f1501030b0a0204120605060301020417070f060201020a020703120903080f1206010306051e0a05060310080c010305041e02030a0503030702030a110105060d0312060b 87
    0x20485080c1d1103982401180100e21031801102010a0340943c06840c5d4240b280d00d4038000b680c009841242184103502054504680510814010700301c180301c0c000300e65255003003103055004054062000300d0f00c100020044c800a06d00420002ca511083c08103680ea07405002a0080c00f45502180c00d6410f1480b602640c01c6022074000151940300c0c042c00c05080d12903000b2800c0740290484100580d2244d42d090020803c510600903a002c1a0311740000e04030744a40c0d5481d8181c0105034181e5401c4004103910035a110469802c80d0f00000a10701004090719050000340700e105210846c6a11105004900c519501c030040d100c005000003400103035032420415a8200740800303074461044203024441a01d070706036219020300c501803900800c6022600300c10880960483c603058908990510440095000091082c009580310345c141c1e80245803190002003014040c1e091046444000d039140408006c0b465440a40c02e889030346c5c05140800000c4114085040201995042100c4031100850403d20102c0c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 53901982 1250 53900732 53900741
    0x5070813060e160602160f050607151a01020c220b0301090c0f06091a04030206180a030c14030102030c040e09070902040305101a030d030e012406032301060c080403021003 75
    0xc0041e1700311154541400703140d0410300480d008000944c4e0b4800c100708070b140740600103002e03071034044d650607001c0d083c01d0040c0c80101c0e40d074003070459200704514142c00440d603014032441003640015a50303506049007000b007221045418480b44850150382d0040201c00b900c003580020074ac40d0380700e500070b081d0030784515841d500748016111394000910042d00101c1d0b41d00c82001003610403ca40300c0f0050034142142d00708a0305400c90301c80000c80d2a41d95100913020b503100b840d520019801501c6103000181480c0b00d240480c807540030316601a030f004005200200e020201220211800307111204101d4840462050400e55280d0100407100d0001c500401444400701c0c081d421490f00c41010001e020700d0030991701041805801e4203a05412860b42c0d90090340c020780149400d01d0001c0c000052100b8407940c00b5404062a441c03484451084a0b814442e0542622811240316110001d0740700d540410250300001007014094481006201c4142204009446090702d0245074001c000c0451681c800000400a0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 53903232 1250 53901982 53901989
    0x2c01050a05070504030c050609040f09110306010515160c030c090c030f0b130c030e0102040b0711030a0b041e1e020a060f020307020d15050f04060b0405070813060e16 73
    0x10700d0480400c4030a070282080300c04883d88826029103c038074080c2004103d411858100e80c10a44070200300d00510260322510f1400380c0306480403c0c8002c041d0060516002d41601f000b4020340d204100c7c4041803103040d007540c140c2c5152441c0c4a02c50a030610b41035211641c683d000820f00c401e9a00003042400c1c030303038110302001100380e07030b0400405c0d040040c500e06940300b035001190064040c01c40b84682c0c0303103250071040040301e550501241c181400e0b50784a00b2648568090107000a001c2100030410050740c1906105c4a81100208440ba081e40c4409403140c0015000a004c15001c62800c55162801040702403980e80003a0401c039030341c0e0310107507401d802c3c58030510480c4901d00c17485022071306901849048145072200d0b401503080840070350911140c08140a015114500041148039551085010702480340c0701e4005404040c0c01e20b0700d40003043da060b40c800144150f040ca03041210343daa00c514a554440786110250840c0e4119003042d20041992000030501c601a8001c40942c209613112084100c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 53904482 1250 53903232 53903251
    0x2031218060306130506210c03060a2a021c08070e0102070303020601050d0c0302090a09150207120302160b090303010503100e030a050705071206050618090604062c0105 74
    0x20032100c100308002031108881d00c40e8000c41c042d40c2d420802c1042d903c110303404407015000741c07401d02c10303100b00007441c0c415132410500b5588490307860f10840c2800c1c0880d40e00543d100310184140c1d0240c81c010950354195009100801500410906203076100704015010818000c181c040108003c1e00003c20405003180c42e000868284034113104594400034010741102d40607400f81280d80d080c18200081c480c0300c800c09840c1c0c0c000c500303808805030390707050b0507280290f03800f16000490340c90a1803c0c0004001400442901601c107101040100d111000b10601940451900680c1c40481c1c4000c450111200341000e4240010762040265000002006505843d001c90880d2504207000000409030b510000d42006560000d0111900c0c5902600103401307030912540c2911605900d81b000d01140d0443c40405031901e589940904c0058100441200f402c0380003801f80b24120314000c0d51556644001a00c014901c560b02c448102e10f00c2014144080d244041c08624010410407440d5503010b04001d840d03a548 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 53905732 1250 53904482 53904517
    0x604120c0911040e070807080615070819180b0901080403030f020a030608010b0402091f0908030a09051e0120160306090b0708040201020709110418020c0705010906120216020312 78
    0x22864040d1850604c12600b50359008d500342e896409014841140d0b0f050a0708481e418854000000e818402410070350002c40303050010600c54a2000705800750005c10302c0813440d52868240442d0710024111104018282496245915940740840003022840e1703a038004c413403000c1501d10b01c40ba85500680100d55000700244800c4543c001007100300c0c840c44100c0d0341d015408074a0300d0b42c44006000480e03140011814181d400a43d111511800d42c1d015000c81d2000030a118000d210f00c0c0303440d0458076428840082184400000500041c0162100300301120300303600c440c500b0300b50076041080303590300729424008081c0020359203260440141805690844040c00e9540c0001d0704203100365005482150160700603c903c0d868445458024001102201c3c1e1001040201040c00d4805240f5111040200d040c0103035a400580402400e08425420160410031503180c01c01c5001e0b4811614205544401c10040e900d0302100c4001641441e01580250540681c2d0340003940000508090b140b48201520b84c0031 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 53906982 1250 53905732 53905741
    0x130305030d05010b09030c0d0206090d03020d02070801020307080106122901090506090616110301060321140406030f0902030105100e01061e080403020a0b0a020a1701050604120c0911040e 82
    0x3113650240d018156016440880b4800b540d103018a040b991903400580f4661a105040300402d249500091050b005684031402c030164040c0c1c100000001060800021401e50900388030085c07030004180305807020000ca02c90a03004020b4190b10007074540c1c013a040104510950104415a211155450780340450884d04000449003031000454803000d030000d00440c50030754141c0c0390318154113024000341c4e200b0310605015460394401340701e40300145015101c1e03c40c81480205001486120135000982040800b810000300e403400d07a026902643d02c1424040343c0b09040e80c4114008001100c8065419030910040c0f040080d001e4a5079008e89840d4240c240d1141c1e203588003641c203184d081c40201000102d0954450025101d00c14a540091007441594084a003e85400881c00403e03138030416036950020305203941c15001000075280081126100f0040d40c03402000455600840c454082e0b01080c00318100108a800040e01c80a4007942d101004140c0d801c402184d0507400c6406200e0031040c0c3c0d81c0108 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 53908232 1250 53906982 53906999
    0x106050a050307030b0c0f040305030d2906030612011107030e0109081b180414010b03010603020609041109060f0706271b090c0206061c050d14130305030d0501 70
    0x91058401c0503006009103403850390b61a8602000800d0401c40d100c0c184030380d0240c1d0040030020001140100002e540b42d0300100d54400843d8941d003018070000410414202c01d1003141348012900c2c1307000b10340c03183c2c40b85e90b4034001c01c0f289180c1b081c40316142d51800701d801d0001e04190010744642c80c002c1d038525808034034010056440300301c03e0141c0241c3c2d40c008e01c00000500c1075a0305003120100c0240c8840016007030f03660051220001500c08844800c201d111001d80c2440900c144880300c00f045009000281c0380d600412091f1247c44aa01c2c040c0e1340f1451038400c0c501c004002c91704440000b510543d40c031a140c0b00040b8064000e03136005c5542a0424008405c40066000c100b0b51601003207041c183c0c80340e01c0f40d03500072040c0c400b042c00b010415200d600004100d01148591000b85c0d5268014bca002c0c9400410061003d0001c2d040c920110901a000800f045000400c2e840760501820060568206820108014000c0414100c6001c042c080088100200031002d040c40d4902c2c0407044c03205036242c0c4410b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 53909482 1250 53908232 53908249
    0x302030d0e1b030327010309060507021e010b010e0f030102040510080711070f0b0c070b130314031e0d09020307180e0d0e190302091003020108010909030f081801050f0108010605 78
    0x8100d140c2c404e40701c580c205200c400c0444040d1709050500140b02415561841d05071a4203c0341000941c122070807110800d1546c01007a109a00d00000030446419580000f802d01c43c10b6400080c05900403088001c0705481c250f0440f070240c00000d10a10115810040041120504071409000a140588118203c00c4009499029150b15000721007006041000c940038503001504c20341101d21802e480080e04851200050030b030342d80340b00c403000b5403503055003002001e400310b4250444065104001c58814555580e51910405043c2d18019039200c80d002144000340900040280d4103000b41e1b0320005d1082d44d240c004050011000c5c1f01071103114030006400b07441d08404403600c0c010640b41d0088650524250080040280d0301400c03c041aa0b107d402003020550b040303504a19171511000c00b80155a0030100f018010700300001c080c40841203603a4010a40801a80480140500c00307000c80c0400d484144540c40311044240200800c2c07070700f0031491421031402c1c400c07400103510b45403010070703642020f080 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 53910732 1250 53909482 53909497
    0x100501030b0402010f0c0b0106050c0706080108060a051905070201140a0b0d151d0109030305060607030e040504060b06070c03140a08041703070c0e0907050a05030a0f0302030d0e1b0303 81
    0x1140c00300c0b55200d4005641401c3c000d0f60040422140e00302007000070741c1452085020b44840d540c0c00b41c8580c0007804051030005260405000d22010784010410080d00195055000031040303400308540c1c5549044030010400c5512604416041c8000c103c2c11a5055122540510103aa00000c680c4c4070052000111541c80000b80d030000c101008007400700320788052044031100d040900088020028025108030800d140e1100c40310394407040610203140d418068a03400610450703080349800300e50f5501a000c03544444106015641341e200250034840543d02c07141c68128003070107041c0c0d2108030b80b030f15085200490004a03882c3c1c2c000c9510441074540012204c90031648050f00314909810821901d1040c001540901e21a100400280c0c000501d40c000010041500300204080c6040040a041c10300c1c3c4241c00c00381c007071404841c0402595600144881d0010303045980300d18009590304080b42541b0514000d03002442c146801100c00aa0008094001c0e0454007822a02a03054008050301d0b442400d4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 53911982 1250 53910732 53910743
    0x204180f27030c031206060c0b090601050a1a070609080c01050108010c1d0f1002030c01050f0705070807150e0f010f0203040203060f090705040510050f0a0e01180f060e040510050103 80
    0x700c80002030040c0301121840c0e0207824a1780e14003110400b0501a81c1c4190044c000281d41e04101030b0800602c180c107141c220310360328098185503040c05d000c40e42c0d41a140c401c0d1031052191111080e203029000044654007504202c00303204900c1e46041040c05544001c84100084d0310749000000d1005040c4110403910b109a5500d055140503082001c0c0780c005031040a503800341c2501c074040d1503035a0b0310902103190341c175030340155441d4200700c0101d40c21110000c04d040d101c64010010070070340c0d5a01c0400c458400398460002e640b128168141352120a40f081d5142c04000e00d0201117540d05800000e40810380e41c1014001c0c40140c0d1082c40d184180c0c0400c0d6802034266110f000490204528219101ea012442d40c0031184c4141da924001400e42d94203940d00d000d68030030307110144600d0600341c542074003260050703803205012032030003901d010000c00511844003008a103468540c3d421903140c1002e681c201036818203120b480d866042d0b0301010f400507102265980300d0308400b211040c04a0090034100c03a00107 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 53913232 1250 53911982 53912051
    0x1103010605010e0103020c070801020d1b0c080405010507080c01110c0c0604140405060303070501050403050a1409030601030303150902071208100b1e0c0a030801050306070c08030c0a030204180f 85
    0x3d100640c06904424811138490080207030124009500344003502941ca800c64010945181014010070001d003003183d01000c004604032903c01251011044404a660a10708299141d00130b04018519005425200e81c0c2035003045484e05a03402ca0720041c00004c4144802d8490a2504900700802c0340304034440c2c2d421400c1514061807a0f450b00c1d910843d80000082c043d80d2425409a41c3d0300c0c01c44401700c41c1200859004200000d8055000d00c895102c20381d070003da1132410b08034600007583c0c2d56052000404250f15400e03091248008202060024014420155100c089600d00030a10031403100a2034009a4500001f40e50006031103111b90844425200385071800c84052a4442240c207070494012501c4010070005ea0310110400410300700c00c0c080d0f9503048095062008160070910094040340400c003c0c0f841c500d0104100d50110b0780c01c80f01441c01c0c5a0f071488514410b4001c0e010303560018003024100101d10012070080c0d00140d9144c00100003c1180322840080103040e09800400b103486107140 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 53914482 1250 53913232 53913257
    0x605010c06021e070305041d04030c020d0302010e030c01050a0c03020301050d030f02010b060417010c030e030a1b02150c06012304091106031303030b040606020c010503040c030816110301060501 85
    0x196005209211610040e03600c2d6214400344103ea5620a2504800003980024200310394010b14545030000c0c1e001c010b000080b8200b540f0010400000d0040c0644102c11540b850301c03c2500035845100800820001e503501ca0fa00041814001d11007100e80d94403080c06d204441c03140d140301c2c0c402c990613500000c0c0010490309040e2000c85060384814848000e542d070320085103441e50303200d001070801080103108521078140309083d1242901c0030035844c0c0040c5401c20014801004010056403001a900d00d0801400e44044454001c05040d649000e508207640c2c04840c0038000c0140002c10602000c00100d07020743e41c2c2d40c40d00d548032401c1010b0429100140081460003860543c00c50070f45503008012010021001e20300151803a80241c50418159800c1c2c10344108054240c041d2984030901101c2c00c00c4072900c0c0a0000e501d4801d6084224104071001000800304165a403050028503000703811191500c200400386401040e0005040d82d1121419000c41c000b4a41400340030103840069498444031840d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 53915732 1250 53914482 53914493
    0x1003030f0504051905130603021c1a090105010302120303071d010c170a1202040308091018080c1c0309090b0607060e010c080c04150e0609120601030210030605010c 72
    0x210309980300401104100010722035a40030303983c26603107409015022115180c07100b0040300d01042800340b40380301d091440410142e038503000d04030003006814008034901c08039882c1c141074660505d0f0010101104841c103000400b9015440700781038074400c2e40d810482411b0312170b086540b400102c135504006040904603a240da0041201190040010b0404862080455481c3d41110481c00031040303010002140344c00840768819171001c1d001d14800021850175086031031784100e41c81040c0c50786005091300c0d006034000b51310801d0741c5031925412070744074440d8035219480c883d2118042c7c2d115620941c803146101c0b001c855000300c0b44000703d81c580c4483c108141780c450b0590140c1001c040680e4000c006111410216a4500440071890400000000ca41020000c00b8041030304c00341c00c03105100400e000501c02201041044101d651240c06c106e0050030706140040c00d540b10300140ca85d0444100507948a050300e00040e0700341a41d07c00c84140460001d0f2910807822a4400d20806000031810560180440d8 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 53916982 1250 53915732 53915747
    0x40f020d1d0f19110607030206040b01060903150207030905090c030601030b040e101e0f061e0b0301060305060d1415060118050904020607060c021f020307080a0e0a020901060f03050f100303 83
    0x3e1003134004000030007282c40060040e070000701c015000340e00910108000c005946020901400e16400d0a8411034190317225840d414901b4145401d0040d400605a400d050060301c100c0002d00004051210074500084203070025002981c0c042c0c003080c1814031512480c90b141c000c80144c0740000c4010880c00c415051454050b010741d0809200d8a80c10742303d03c3c00249858042c640740c1840300c480100e2141d00d00322401c1d54290036203148031489030700d01e030040c4001c2120004032070440708107140100e02501c0d13500015080c0010341c42c00800280c25080c4c0080170290114084080c0410020705401c295546401905c503850310074801c07850051907100c2405549010344105030040d001810481c100802907039484219801165100c02603030115100f8414080441000610125808000d42c1542414007000d400044042e002c146411348078488484142c0042080c54003c68005080b25003550b521103029009480e6810307220006414500041c46005040650340d0144100600022115243d5101101d201 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 53918232 1250 53916982 53917033
    0xd020d06050411060315011407020619140406080403081b09040905010207050303090c100903050d050a0203130f050103060b0f030403050a02100608060a0e06070c060b040f020d1d0f 79
    0x100c12240c10340f000342c3c4400e0040c0d44500004594010800203a40001d0102c2181018131120032008000d02001602c2d504140e039441640c800c01c141c001800c1040a556020040c0341072040c1860120700000e0295018403681d01a500945400030144c88d00c0800034850040c0103250051481d080000e001c450900b130744050034450240700014108071250b0348150440d401940d0b5104039a00040f14081985084604080000041d060009005146030307540ca407140c442030500814002c000c01c000040a00a108880b080c4041c454100c10441c0c481c4210785041001e03004103400a440c1040104e443c0040320116020344a001c0640c0341159680d5030b00700c2d41070340048882d40440c01034007000408010303540905009003a000000d0a85840c00110150480d8500c070720107602c46e800b00c1d0030302410682000b108202a03401002c081104245d000210300036000f2081d1445004d1b01c0040c001c02a00401c1d44900200e10190380348030b080280280d42c1a40d03c0d0f070300342d200342110742104000003905581e025044007103 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 53919482 1250 53918232 53918243
    0x9030d0509210a050c09070210050c04030501050a050106030e03070f150b0a0308040e0709061d12120c190b0109020705010f0204060201090b0708010b0405060c0f0d0c0605060d020d060504 82
    0x4281c1c06801610b10b0000c0b502100b01d54041c202d03c50400c10144004001c801081d690741c1042d1500340c8000350303150350140030310341200d44d2070020444180e011411200907503003000090095003066032060703004003424030501000a1030525503181440d0084115810300d500800030b8000c40070141c980350000c086a030703111052566170751407071421500c1d0507010400547c0100030b05078031146030030038540901d207005140c00d040040011092142503009283c007640300f0640348805da05010717440013040b00c00710280054a410312070203280320640304003000203003800c1e001c6400341c41d003504014070301c4461603c144e17000419141484005101503542640508500c9009100100f0303445140c44144c0c040342e03c940c11400040c1d440300740c000148084e180e01c081d044041844c0640311907142c441450300318080c81c010103101e200b0000303c0c44800d6030100325554040c1141e030103903400b00c40b003503030301600c00208420300312201400c00c000540180340080841c1d010640141201c04103040d01c0c4d95260081c10300403c00c559 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 53920732 1250 53919482 53919499
    0x5060414060d0c080a060509010f06030903272603030f0406060b0708030105180705031602070302210f0d090303030b120a060b030106050904021c0c03080c01020703030605030309030d0509 82
    0x9000310b5018100107600b0300d860720ba003141004440c103400c0d00d200c0e400507401043c14000400026072918020001c82d2450320700012005060b20b0115900c1c11003c4042c03480145280d200c20f0f8116003d841001120349003024101e104001c01c003000c64409030180a84001e41040c400104549081d201c0f455001c0d10403c3c0c001019525541c12160b00c0c0c1111a060300c0c442c3c0d011006110700c0c00c0007224401d010041038401012480c3c5840000c04600c001032640903c40b240f90440003825008100300d1003d1a070040c04250451904401c403e900c040c2d441d034a40c0b25101c0c100c001e14403001d001c5410804641e065032041c030200d06680b41900038010400c01c0c690030510480c1881c0c514401405040e03c40e5205800200c0d850301c001041500b503900941087d0300c5021400c042c0001659045028082e01800720640484c0c10590704141800c076113140d102a04250340000d0f250420441940100f03041d900c41d0f00d0400205807108141581c038081c030300c00c080d0154011403003151124065005444c8001c2d00038007020 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 53921982 1250 53920732 53920747
    0x10030b040f051014070e280902031620060f06010903080313050c0427020d02060a02030c011514040f0b0607051f020f07150609050702150c040506041406 67
    0xc1c640f0241c00f681d44005540c07003844000e0088108410303600020b140c0f0342000a0a407040020303d042110015000000d0720b41110b070b10004034840d0454000707000f00c04085480c3e1070120b03905e60051108003003000000380041029800000c0d110480d5100c00e030000004c100995540705140704205001d0106410300004600000008030148020351181503040602545040790740f070402d203403165410300c4e54400c0d82030a00b01c0d5120488909240060b1180c80c60345407015400340007065005a541c0c001940240c8002214010240c001008200401040c0000c0280800340e1494014040c0c00c3d0041d200b0f80c40c03005001d9012032400d42c2260403a440c561000103000b00c56a80000c5c920380c00300c9402c0741c803900000d07014030390346041218003551052880010746ca0311600380e4100000348220300005003909041d1081c108000142d5010f0300192020303010030044c504001c00301035913426101411900c9051210300141c2c03039110354816181103c10141c811030a050424144540d50208440c0072508207005200701d4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 53923232 1250 53921982 53921993
    0x30c0309080703030b0316080330010330081305010608240f070915030b040203010308120603070503060604090f0b010303030c020f030702010903020d02010315032910030b040f 77
    0x245041c0f84240c40018030003440b4020f05003012150244c1c1c40c14561391443c100801e640100c01c85000750051440070841601103a04094080958001044451580000441003203400b89031548164100310490303000d6040b00c0d9000c1540081c0c00d0aa100041020700891003111420f003108407200d02c558004101c0a450f140358a00d0104a00070b40c00045c001c1c07034000e020100710f0b440351540101402040c1a00c1c0d1400200240c0720310704078807500300805420183c070300c00c20348250311031090800b00520543da00d59680c00e01c2c0c95990050b122034071b00702d441c134004162207150006400d012128050050b0200381c1d10607040000800d214003050301c440c200a0701c6500010090800c15001c0c6100e03480018481e20f8450000345024008480c15905500420038100540c2c2c20400c100201c0e0b604440020b0184081d2004138013404021500030a600078003807000c41000113040f500080c0b0a0b1110038201c0001880c070307000700442c1e010b452102c51119814810300c00f0945820fa10350388075001d00c407003e000242c1ca6451 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 53924482 1250 53923232 53923237
    0x90614091e04110f091302090c0c0f0304090b06030702100f0b0301060b0a260a0504060e1006180605010504152f07050a0506030a0b04060b0f1c0912030c030908 70
    0x844540c410000280c45a1500e1400214803031025501400d81b0303e450001c01c01c40b81c10342d610103407040c111400090354280c000411100000d070351a0030345008203100350010b81d4942042c0181c00d20503080c9413004007141080c0042ea80f141c1b6147e03005104103500511204020094200d8401032140c0302d42050305a0744090081c540142002e52109545400702107009250040c0e0007000001c42c01d80c954070100090200034a039130014101c0350005000d40310fa180100c01400741c02c4450140307000760749181000c8046030388840e0032103410340c049058010150750280100c4115006443c0820380030f20060000354031003100700e0340000517420807441c28041c14a94101c0301e2030710745c1c8104507100ca04654845000701400fa40d8001d01c0700b540d1060140d800c0c080001c5803404018840442103546035000d091955a54010300002c0544407985980c0d032a41060706285c03503101e1a611040211690447c0326401520321502208903007104c802c502c20150350341e04901030601c1c0400700c0101030311460404045000740c0c00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 53925732 1250 53924482 53924491
    0x20c0d0203070c0806010305150903070b0408070203010e030322020406030c030b040c05060f0702010f030912020a03020c030f070b0d060b1b0d11060106030c05040e040318090614091e 80
    0x31070701d8482526103c00039900d0764002c00701c0343c0c000741c00402c0001c0340040c0078201030b105090000711640d15000c03a03d103540101900504000c0d80d140038031003440101c000400689000ba002030001502d69403041e44d0b24402a1040304514110741e02480c1c0410010500340c20b9548020404a06603941e42c0f51403d00321507940065900700c90000600080042d4240c469008040546040c0e0809107014040040e600540300041c0c10b20007c0c40c08090304070311950100d0780b1241c0c01010045590800440290350380c1c2500d000310b0240c4680e08102d0078a10740011a040c15800c05402000300c02d007803840c1e03521039400940740305000070f458000110b200d450300d0015200e841c41801e502c40d51084070b607403e18902940c00003648240b0101c840707081e100c49808038880d810f4a00c5810007090885e520401224203206d60351180d0740c1c0180d407609204c01c041d88040342c0d2800d200c41100c01017219403500f60203070445085100718041c498103209190101c0c140135a07400c0d0f010300c2d00c3c11207540d80844501e01d403034071540844 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 53926982 1250 53925732 53925737
    0x1209080c0d0f020703020a05090411150c0c01031b0c1a13030e06090a0302040203090f060412090b03100e07030e150105040c05361c031209210201020c0d 67
    0x1a20503060342d52102c480000042640300500e0395070314540105003040c209001e020b00030041c8000050030b000620803074001c1d91901500728204924007a80a1020350012500b51410b0f0041c0c5656007242c2d840b07400340100d11304e9208203070f82c00c14405107000d840c00c000110080b268070b2045903644668040c00b62885220b501881d082002002d070368940100822116155540b003404240000034030754440c1007510003035a506442c0140d0740d45400050500d0004140d15540941c80741c0b908110070400450303803600a041094841c10440c903116518440d030380c0004c64400c1402d40142e20200051405880c220f030300200c0c2804c0000e12034940c400e038203061201754815a01022071100040003d81014030495202080500d00a410050241e0070405900b150220812946040c0010304152021813150131941c4200101105500360008240b40001d00a119064000c43c0c51001c01030074046090144441c42684802c11034010702d040c00c07040c61844540c690410856509001d103482c100000c0180c2c1c10700b202c568 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 53928232 1250 53926982 53926993
    0x906040b0d050619050a060b3106120501060f0c060203130206030c0315010305060102030f2a070e01090203221713170111030103020d031206180e0114071209080c 71
    0x400c1c00b001900c1c1d0103400706d401c891801c0010400880e50100b034581201e00b00401052600f4201d0005065590011801032840f690032070008907560004184091503600300d1007400710380ea0b540016618090003800340408100d412880100149141d4000d55008041070702c156507490944c0c010440c40e8000320380707081d450702000041c42500040340d4058240c10009103010702c054943340d00000c0d268012003000085200f80410740e01c001b01c8101c819041e4042d0550312400c400c0030f03920881c50340c40d8491f100c0c0615040f0f4038000407c03c1280d500849100c0c400b40c0b1188005005820706002b108001e203d000da40505c0000503804001122400810107100b5507440d0070328550420700c01140d000f414064441950b8582007084096102e80410303241104c2d01181c00c101000700e20708003500c2e480528021052481d2401e04042150a80074010140c0500c0c100410020840740050103401c8981c000f0300e0340160381da5200003c1850307108030f01a9100b60240380010038801c14680d542c03020b83e0803140039000c241e0040d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 53929482 1250 53928232 53928271
    0x11040e070809060c160c0b0c1612110f0607050105040309170601080703260a0c0b0105011106150102150405010b030c150d15120b0f060a03020906040b0d0506 69
    0xc241500b00b090903001d03041c0c41c204418801d81c80d2003004420001c4031889407884c828003074012401c800602155060540e5280442901920b9490180d11039413060702c450004182c02810316000100d0070780c0981c906161402800c01c0212200303280c01c503580c1c410410090000042e40a002d440c0c091442610764214481c2041d042d461210060b1400340c00c20781c4160010480314500041c19400c80f900480c481702c82e80b85614488050700c02c42c0c03080b5806848005611074080354007a01c0c840c0f9a6000341812441642c850300110344400001000c040d0750740c0b000002c0b8681140c41d480b01003080d141401261a07840d980d00c1c2d030a0701e445080f24151107a955494a61010307007418800480c6d545000c4030019012002c00d03100841501408509201459803259110100351101d0810f6020388101545044c43c3c0500c1d1600d03a41c080801c0b1340c600c1d190224003002c1886402c002e6800400e40354000d000005554562051100902200347c1195001c1d100c3da10700000303d4010700005016080310803503000480c01 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 53930732 1250 53929482 53929487
    0x118050d020d08040b090703080307080106020706090b07020f060409061811090a06030506010e0a08010c110c0f0108130206071217040f080d0f05090109050c0d0b040b040611040e07 79
    0x800038461419900b120829004240e80040c0e00d43c4c0c45a48002d102c4c466403110b054040c54408107030401002c001b00003080c404500d401030070a0741210400d50840312416101c0c41d0449141c202403081c40c0e4500307010703c80c400051a009020f40d40d00000507010a00713081ea162141002d54003654440c40d448920303985064455440e034040c0300e0050b44d1a80340c261400040d440440c2132005544500c80130550f9840c0400e169078480c00c0c20b41c2d1151802480d0300c980984802940b4000e1500c5444100800c0400044236440b801c0032420202040c0010000301ca030403d0540152000d00d0003c0984c0b00c0d4109610000b00182d40710405012943d0040141c00030010074824040c150749a170380c0e85015101302c0303401040000b038004c044404c9003503400b4000e0768440038503942840140907400503558615041204109405005500468400d03000d0011102d4116032003090121002068a024191404030400180072490802503e13800030b10802d4001415004c036100d1074030320342042e0007101040000205100045a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 53931982 1250 53930732 53930743
    0xc0301020a0e330703020307050d0906030c020d020714030c311401050d03050c010c03051b0708030106030c0504030804030305040302040f1802010e0604030204060f0510170a020d0b03011805 83
    0x291103101030520002103843c61003503414402640b03150381c0000a000040510910944105941c4a402c8801400812001414aa085020341400289000c00f100c20707943c80000e0341c075540d90494000d456100c2c100060020022200e81404ea0140b2840c0d07204009a2280415003540c0b068903601c2c900107404480f041036004182710790a0583d0381c03c00340e480046200b600012070440f8000c44441e00d26050500c0c00740c603640920040a0199441e000c1e5421074540c0540240e0b124032001030300407595452444e600300705801119005040d980040c0f00602030309019510004865505060940c1002c2c2c0e42d0f5100745295010340c01c200c0c005440071030100110b003000d00a81c480024543d0081c050034020f000c0f105828144c440002c0e0400440d10415911902c4910403070f006903030017078024009192075001d11061202c8504c512400f44006101d00d040e00382c0714160341451400b580d0b50304240b1340c44000d03014019401004441c42803d0b542d040003042d070342d024441c02c030010b1400c101840e14031800c1d040041c00c10 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 53933232 1250 53931982 53932009
    0x804080c0d030f0518090f06030613030806040905070b07030302040915060806090415090605011401020c09040b0a0f0c08040c06030b0a0501030e030409020406020a050d0219020409050c0301020a0e 86
    0x1816154541c10000e5040031921481e40c0040c542103413242d100a400c038500c0300b07542c0c150030340069105091013290004102524030880003502210703030640701c00c1c03080f0343c09000400000c3c0000d84000b02103400b41c503080d0890020300740150100c03401235072100b00b0115203510495044000ca03034001020071004c074080c0502400c40459449040d0130628042001c0c06001c0001c000e98171604803640010200142c0340b0482d0450803900b50200480f811616003000101001c0c01a80100c41d0b82058042c4190310000d40921521005040e414054440c1d9480c00c188140241c0517502440c0c0300e440aa05601580c801c0828000e6580e80c0e00300d0306d04007070825406010658002d5001c150900141109681315070403032000307c4100b8600051010140088070f420741c0155000300c002c103800001c0000c0c03016400141c500c40d450040c0203070fa0400010041c2641d454182c1900410700400724412040035141541c408000c5034000c0045d11040c0c010400000d0880c3d01001010000c1881c4c40d212000508040005407401d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 53934482 1250 53933232 53933239
    0xc0509040201050414041512030e040605031e0109050114010e09010501320603070203041e081203040201050c0607021006170c06090307030f03051b1c0807090806040804080c 76
    0xd0800d03400083c01ca21580c01a00d9084124941140058a403070344074003040720751075990480706602c840120104105042c0141c0020710b04c41540c1c1554605480351000321407000f002058001a50340348081d031040d04511180055594102c07010115000b8015440035013603000d05004158104403c0d00b6423204040e114549503890038006102580e4440034140d6000c20005c12802d0f40043c1e0030305800000c0903229880d0700401d02005000c83c090300040030b002907403140341c40c1c000c0140d445401e0f904501e44600c1581c9440d0710055100c0039404ea04070003140c015006140030307460641344190440c600306e4251a450010b034840101b41d40c4034101403040ca0090400d002102c3c141c145071030f124654441200305c40d1889a80c0024040f18281d4080282400940e0f1102c0707000c488142c4c030300f009005a000a9016400c0203040101010319900c0800c0008600088004643c000d139800d02c011284180000d0010b424043c540d240440d51140401400d0711892003040401d543d981042d05c050b0902901c40141c901 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 53935732 1250 53934482 53934499
    0x10c050c1e03222301020d0e06070c14040506060a0f05130503030310090c1b02060d150b030a06060c030203030a050406110d05060a060e01020709020307180308090102070f05061b0a02031501030c05 86
    0x80503a40407d1b040303104406c602c0c01c650341100300c1000400c907210340380c4d00030300c649041d10002503891003002c042180381c1c900319420801031f03840606000039403182c1700b81140028910845207403003a0050018060a50003044482c0c05035449001203883c683c0155107a1580506690082050312030901820025043c0351504503081c141c007403140000d100d000c400c020b21810f0003040044c1c94441503440b0450b4030388441245000d0300d950f5550340400c1d50043d00c5500d91542441030119016011320b004645807549a80114a5646d44924010081801a00072610780d9159044004118490700c00b800d12198100c0c0d0000b001d0400500300480200c656002805210241160b00101da80108121086505031500560b40c3c0e5210182155290b007040701d4008081c1c0010004014400d4200c00343c0065182a0201d4421688501403080090114800d61b07a021034104000c001361041c4c4e022100741b0f803000b601154000002030340080d0904144600d0107405030001c01c010010301140c0508a00248020707a0b0340784 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 53936982 1250 53935732 53935799
    0x616110f0607020d050309030312010305151b03060d170912011103040803090a0210050304050d11030901030e030c0a0b0603060705030402090a020c0c1f02010c050c1e0322 75
    0xc805005000703021340b042008481c0b40040c410b050048500240d4018280c0350380b28254003468610110a00040c3d610b03202d9444107180d05042000d03840c0c0a450071403200000e041c0036800604542d4030082405421110f105c00c4040002c520781c0160400392a20101151200d03031003018440c04190111000226130b040002c00c0015011100442c1e4101d900b1400b5140e80707640b454019031030403006982c0250490401313500007080941c8440a107004078030070010b070380d4138031742000003102c140e1012815120035820411401036031358003c0d030100c600f10380c4241c280d030b0405218504182c101409040140ca0f00c4104c00200400b624040c45000d40c0003c083c105a8203504003600413901014005007681c00482e40002c01e103048440400c0300d1805e1a000070810208006017412407807015a280c04044007640c02c041003015880e0165050303825041401c3c4c0100005440503030300541850881d07490591601040290a0006002100d03030564100c5203140044460318150840d05000c8000d900107000300441107542 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 53938232 1250 53936982 53936989
    0xa0b09010201180f0209060d0c08150708100623030a050412020703081602040209030303090d08010f050f04090c1230081501050c0f06060f3007050616110f 68
    0x507a0383e280c040d106c16149599610109031500b0420b0000380585c200490f00240603000041c1d0401008082c8804640c02d484654081d519601e05981081e004591020b0500c1a00c4c882d440c807111440044a2200e9141030805a401060b0701c103131400b0803501d40746c10420007848010800414200300e103100824107245541c8820155000d58a69005c160981540ba1401c1d90390b40e07010790384814002410f6a40c0ea06001a00940e0340c03692000c3c10003c01d03e00400060100040d60b4600120740d00a1300e2000c0b01c8920a0402c001082e505e40100c581483c0010040742d03150542c107030361148612500400d4102d24990001c02d4403010b0b44805500844004a03101406681c003445d8150052210304503d41d990100d400181c0d21400743c007100d448070788102540030079111000604540122000d40303029142c1460402031141c0d6106401608002100d1245524595145030b02403024600040080c4d40b04c0c2c540ba080069507a03403210844e0b4a080301101e44200500200308001040c0c801c2c02c031441e229150142020 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 53939482 1250 53938232 53938253
    0x60806060604260312070c0213150306020f0d090b0406050a0612030302090307030611280e0603073f060f090f14040c030524010911090a0b0901020118 66
    0x807540d100b03400b00020743d1280c0042082c1e50152540b1a410512031074451402440a2601d8500340e02c074031440c0c81240c9542d840c44c415842884070004418030311508507207641c0301a60003404c074800740250400c01513502400c24490306002c1740c842d08401d002e1307081c1800c0c2a820360340098401c604191418070304201181405c6000307210f0b6a814140540c0301c074210400242410915403010300f51506121903208803440c80304c000c16851030713075003000e5010b150640011131a0380f48407851000815085410030ba11460000e0181d50300c1001c604d000f40b82c11568a12550540c4180c0d10907015940071400a440780c044002d00000c1c2c014541c4904000c1c0358604501c41e4101006441446174855640f44d54541d01e60064004182c21001034200301c2c003500701458002610f0540b40700c2650540030b01804800c180314050300c200b83c3c100249508031a17590915200700000c01020400c2003444004020043c426268010203200401241c11400d844003004000079082d1000c05d1808202d06803603414060005820541 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 53940732 1250 53939482 53939519
    0xf06010302120a0b01090f0f0204080309061e0c0d0305012103030509011121060d0308040809010306090905060612030406081501020c130605040f05010b0304031110020409060806060604 81
    0x103407038003902115440d0500f800040728001d084804204000b04080c0707140e80003c52070b01301e289010000030052821483c01ca01441c000c05046070010032482c0d080c0e203001d42c09040000714814141c0070036102c00748540425441008100f08903008051a508420b4040c4680c9005080400f90807100700c00c4a0b8200300040c1074418024245031340d032004180d520209501c000c01b01c422041c03e641d0765401c11000802c0c808504000a10500c01010005195091140804580f1a03068a6450194890b035880701d00d030303800c0000118101955a0070014815055000f0143c440340500e002d04441d003041001d01c0020fa01000003102c190707000f04000c00c1950b522450603a408422008d0300360005d021400101d00300001c40c480d095102c01c0c80d150b0441c400759582e020404480701140c0400201c030300c101200051340d60074411942e24032801c0c000600441e000301902640601d145d425104001820b190190480c1c00c6900400212a80c5043c10b104c41401040f81c40d810500880d0800c1c140303849d12461140d08a00940d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 53941982 1250 53940732 53940739
    0x2071a04081e07020907020f030a1b0204020f03040c0905010620010617150906070e01080a06051203070c080102030405031b07081b1905010219020105070c0906080607020f06010302 79
    0x80014003403050304029105200c8a81200c0040e40d0b80d000300c045443c0d0012102079119130010004540c0c001d00000781002605401b4020350309010750208142c0c0c201a000060605c8402c02c00f00b2900140da81d48010000c01140704591500d03414141071414080140d0f0304410f0086103418018456240c100d52580c420070300c9004001d0300c03150391014031400762945501036030035480c0c5003d40103000200070a000d215218054000542c0c0e0b40c030b50700f21543e90442a509c4601180340700c1503820305544582e400940c440180d4002290103030740c500100c0c6440690f4541c400c01600003040c06020020040b050f54018440e0400a60035800c05403140c9032244650f00c4084602d69185000c400c45110500c0448010404001603480309050082c90000058000c1c16145c8681c180c1c86c100071004240d402900d0545406030f00410256a01000100c0341391041c0074182c0c18840c2c00d0100c600028840180c0d440901801400407402031b2424070709915198000d4580308c01e6411070804481a91000036120341141d4048 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 53943232 1250 53941982 53942033
    0x30a0507120602040e010b090915060406051b0a051b0301060b0d020a1101181205030f07050904020c010608030405010906050c0604150902030105151003060f0510030e030403050109150207 82
    0x28030b440e07002407003035502ca588403025503c00050441c0718038000d018003c009039500565581ca288200440038059420309900107414003090001c1403141002e0411910141c40060032304250060b41864200032044c121075036400200c2d20301e1140c000b07148004031150150005d03c0820305004440e0118050036500145859020074100030030352040351051240da4a004c000c000103500315400541c0325001c00700c01d0b00c5400c0680d03004900c481c401c40481c0d00c10000640b0784440742e2102001102c1c154003a0300030b603a000c1c2e000d101c030030700d04038007845000f0060101000442e40c5038900000906503000c0c907800380c03003480380604c01c100440401161103540560b100426015044021020070001e1001800c0690152300c0e110400102d210140150154001b00b1910082c00c8813403100700710140d0f070285c0200c01001041910412490515038401c0300840b0381410017094001d11001d080e45144c0040d4810355040c0e45407803d040901c240656010014085404154600b0201d901c03059065242c08901c0b0b00460b000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 53944482 1250 53943232 53943269
    0xa0207120606030b1510080402010519031b090905060904020d0f031b060213170a0b040503070204090b070e0402040308030f04030c1e0501110a0206070f020f070b0c0c030a0507 77
    0x40c2d000d00095a8070070b000444070f0509903107034100090903e1203140680c03140840c41007914080d04d01c00c1c3c4500e0303050792085d15007456003002c209060046c080035000d041d100c2d0b00a0103181c4403511040e008002640ea02100645481e02500c207480e4083d00315401001c9141c00d10000d078560320031160a43d600510b58244c800307003a03c3c040360702490580c80c0843e2800307604000010030074681c00034101050344581c01c06482e515002c41030b0508403000403014140c5d02c124044d0002130380c0c100e2401d80c054081d4081c0d81c00c105c00c94022a050b282e00440807100c082c281c5003003101441c2c0202100d0603405042c4c404504080c01c60b81d51170800d1001a0654500c03020860011301010b100e141040b501c5507121224030070380401c0c0110348261001d0312030100d40c40d508000074002d01c0305402c0140d4400540940c010020b60f02c2c0d0040075201c980c01c0041c41e10460151203080c65014000b08101c130010240007a40300d43d40c0f404043e80a003000c0c5150000d51203600414142d0004c81c1d40000e0365030643d0856010000c41c040f5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 53945732 1250 53944482 53944493
    0xf12030e0406150e0a140d0807060216020901060837091b05010302090d060216050313060e0105070b0a0507020309031606030b060705060f06040e06090c0102070b0a020712 75
    0x44030348400340e00030b0621a000c241d10b610011106200941522801c110191071800c024a20f8114020551111a1101308440d1880c2c07108a4103509409440110703c0c0000d82c0c0c60301c409903441440d4280070700d03e04500f40f05c1141400e02c0380c1401040c051601e2880340c2085035480510103183c1d04a040b079100540390004004207410055002069030200410420076145071034542c170243c008200c401803502c00b400040030750203802221039640c1e00601c0400c851030956207600003900941c01f100040c2d222203010b2000980300700020800c048079081c40c114181d01c0d01d400200170101d003003070460402c1410702000c00028100f40c1490f41129180c280400c0f02c1d41c405400303d10358020b417180f9903407511910403220840010010a602550b038607a50900c68288400240003881c807c1d0400103200e43c3c8890001250859140c0e40d040e00154014008901c003e048244103250034000ea81042480e088040d001d1302643e0100840d0f00104078908140e410800c2080029490300d01c2846418a400008a1a03108009 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 53946982 1250 53945732 53945747
    0xe06061b0a050d030b0102030c03090402070f02090108160b070206092209081b01090302030d020913050109021c0605030a020904080f1315020105040c0303200f0d180f1203 75
    0x440001c032801458507061850b5601050b50389240031070725224040143d54400300895458050f60001149450b540740244402540304c450241c03484042004481c005a031500c01f098020008a4010200d403500c10361488416446a4001c01480200700118070058403054144d40d200c040448600c0c040429503800043c0d03422140d03110410b007a00c3c120003070041068030400382440a4401885444a44584596500b01d512a45c00a03015910521102c4035800b00e40d0020500d41c04042d00e8a246010f11611050682e00280c00030340c0d900fa0007003942c0c0080c1400c101c80d034100d2003056406020181ca80404a40c41d0388c0781c8000039005003041c1300018180300021085400114003e0703131083d80c815003840c00100c1000e482c000c24240c0b03c042c1400000092050007540d00954002c80041440c0d80345503030540b8141108200610000164403800942150a204100c180312001000d0015044980c02c01801292078000d00c0c400445085810312103184000a1b41d41034a200c00d00200d284e540a040c262001c4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 53948232 1250 53946982 53947027
    0xa03060e0c0c01060b03060607080c031c05220b070309020f0607030c120804120305060102100903020102030601030b09090703081c05010b0702090a0c0e1c0515060909070e0606 77
    0x10404032090151406084004003240c1241d000200806a11a40e5010852105560159001c0414000c0c0d5000c82d501e400240303030000c14002224030740b9407803030942c510b900f0245000b18411b594130390401040300c800d50700b1107440d008140d520681500040d83c5429908070701901d044101980d03401ea410840d2910080d255002e44020710503600d030340b00ca140060800d407840a08850f460301185904800074002c09500f8010342d030000042d406000c03907440441c01802d00801e045d045124032103c1c15241c2c0c05ca4481c0b02d1000303010b98001341e500c0c5008000134050792001d2000b81d001d03403038035400c0140d032043c04224801581d42c0b10b410303555218401000705180174243c0d00302100c100e180c030000045000340c080050100c188261258443c5076907444002040b901006200d00210f58850f029a00c05d01d080c1c01030865802884120856030346140d207030030f864554491960700c18000404103008240c6080d0403880d9006d50480000e0a00c0c5040c56001480302802400060240c140490354610114401180c0260b6 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 53949482 1250 53948232 53948249
    0xf0309051b010c0c0b03091c1b0c0b0a09090605010c0302031c06080319020607030c020604020909010204090f051b0301050d03050702030102070b09060a0f06061710090c0512010e0f0105060a0306 85
    0x7162641045c14055105031085641342c0724420005035617140a201014490a00d62185441d2800031000c0314240952000b00701e4100d003042c1008920b81840402510035212280c4e035540c0964200700e1542c0480743d003500f081d0b0500c00d4440300a00043e41c0002103511400d08a4505c101e245201407096001d800e05802c200038501000c20146000d240001c140d10174644150300f03e4801c0d868000d8154100c0300402c01420040e00004005009402c01421160300b2041940006281c00d59034201c00c01201c2100301c40c0c40c5115202c40074001c180ca4440078881003100da00e81c07054950751400c1c0004035400d5003040c0c01000e2250204a480a555007076065511190300401d88540c1e9150220b103954851908030744c121205407400107082051003462060702c007581c4c1c1c5611034020071083c0603081003100c94014403188604898481c08161031100e805165110f270460707291243c403040300c0c86100700d1504050304107004ca211400108240b58441c14a01411104255070090b9602d40c0b600c000c5000d4002d581100c40b9 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 53950732 1250 53949482 53949503
    0x70501060b07030e09010b03010e06030a050d02010608060f070e011202040b0406050901120e1f021e0304120e01020303070c0f0f0b060307140609010e1f030c0f0309051b010c 76
    0x800040c401e00038110030744240d44d0a2032060a4500304200010f003805415a1200140014007142402100c1c00d81c00c414028216070074144550760b10b501d48100c4280c104c006035185c04d0200454002000038507003251001c0486805c0e45003603030004100840f4107003070a0401480c16403103106503549034100c4000e0007040f0340e4590303921b0300d400000e0402d511071040c5500003941400005040c12140c81141d9680f00c0c0358000c1c00310018a0a1100f10480d03a40d80c4400381d180d0b08021081000c091886203080201881c813910351240303007504103034a984082c1f0750400144024024070441581c2d010080384e91088003400c10380d5134030140c2d04107118601441c0d14010151030a00c0328010a0007103155003948501d9084080ba10031350b80307900590900300718084646410010601540c0403541c0600d00b240004240038008101c10f00c2c00d03a481d13401e60208402c10300046586c500000e6201c590140c2c00300420078180c1402e02c00c0003003950f1816a030b030b09400c80308242508540000009030380b00d1103600c1082c6401008800f07 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 53951982 1250 53950732 53950739
    0x203061303091203020c0f0303090306010509070909050115080708010f030314040806150a14011407020616030f0e0d0203030a080a06050303070614070219060e030715020a020601271107050106 84
    0x80d51006c3c0380e8001c9200d08406a41d008103440d00100703d0b052035a014010302200d910340001c2c0100c05001420381821b0180f440e2020424440c0c0e4802c2600138141044007080c1118500c001521b000320180a404c00c02c2070707000040c0144189140410201ca61503e045030b02000c0d88180070f04140200e0b003191070240904018840304200003203c0070241d210841d012807016641d01000c121502c445519140031a103100b00880000b400840681561800900110306d0101c11403412036030003040000440100384000c800e200c5c001c0e4450450f1000e5803082d1448845807026800084e07aa00420f158401080403400004410710040d4110000500e0041c0480780c0f41e5070742d0703d80751001c0d0000c0d06842204146610001d40c3c4070780300003840c44a0003a4410803021395011900c0b01400b078200c1c900141058417041200c1000907030380d0084100440e010a10043e1203002e0844024109141a4031001c0d04210b842808685128200180390b8022070a2a0000b000c200c0050080c080380584c81c00508154600040003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 53953232 1250 53951982 53951987
    0x10f1401030f0609050f0a020408150a0902030307150b0303030103080708030a06030212030a02010e0d09180209030303100305010b0a0b18040b09100609060507030c0807030536030102070203061303091203 89
    0x36021b11503c25610384103641d84400d0100728051485200c44680c043c900c0b02801031080038090790003980d996004104218550046481c40d40000b500301c3d2061241e4184589000451084000b1000120b018620319451600c45c00a01d000d080b001415070f107000808210b14007450b41c007038401981c0c0136000c0a0280e80740c03220603459810003180c0300d0242d4282096821010004640101000c0298440c40360b00d5081590459030146138401a40b56250300b004181245e58007040a180304549111007228001d00b189441c034290340d034044c1041c0c02760007007540c2400710904401c10345850525001a0a040e1001000081d0140817200e0000d60001aa2024041c0c0c2c0d00180342140c05460103500e48244890740c031a401c9a01d4400d0344c8000d800500c0d10401103002581c80030092000c0c5009152050801100f00c40030307210902001200c4200c00601081607107003450640524001c17440841c0210704190f0f0903008640c0f0b030308008160403040d044d103002e040201030186130003e02030005c811041306001c00902c4c02 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 53954482 1250 53953232 53953241
    0x6011209030818010209150f04091505181003060515120a02040e070b070836030c01020106031a090124060206010e010b0d0507021c020102040504060b03010f1401030f0609 75
    0x410880f0031500f140f242416505008960550102921510340600c403d5055211034000b007031080c0701c8403000c200001d481c50036070140d00441004c8031400031106150104000100e0100d03007403480703911082c0b01081040071695240c4c4007100d40040002c20540c1c1d44c1360010f00203110601003075902c209002d0010304030140010307800c01c4941c42641c0401c0300c119603400150381e9803000e200d8113030f40500803c241400520300d00c0140c00c00c04901e600920f1001d805c030199a201c83c0ea00d14844203100e5070302810040910f0100b0054607181c0c0e080c0003c201007400c60702c0d0382000024080341010315407070a0000c50503d81c000d5000145e0200c0c003a40c25025a2000d444000185802d17100b0076005104000002c1580d8a0f4003c0842c103c0d01c00c40c8a861509280d003400c1c1000d810020001d2083d8000c003a07413040b1610110915100c0d00c0c43c0760b0300040e0b5650500d0200000c480c00b940042d000720500303000501504000369641000d8032400c64680314070426080048025000e1300c0140d41084d8240360340055a00f815412 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 53955732 1250 53954482 53954491
    0x60503030a03091a040203030d0e0309150d11030114011d04060b04080c0612070c0201030603050601080115150504030b0c070f060603141216080405031507090807030b01030605060112090308 83
    0x2450480344d207510312840c03a02001954040d50581040140c480c0d14240c40c2c0c465651808054103490402d00a40009011003429070f004240300d4500044010000080b8441c42c001c0d84c941140d01401c1d5410815616413031a08801054144811b140d00004200c4120190005d0500010428030009868038040d580315081031007a03803c58851300d41c6400c001d20b13000041d40d001e42114002002c0c00d503107140d42182e0030549110f0a038140360750782c48007001190007030116034040c00c80d08002080c2084200018004071b551a4482d101034082124540407080d03000d8111012250081064030715501d51055901a80c411000c00074046140c1d80c0a03042001059004401100d00030984016070288450032661a2403540d000c15250000421180c0e01c4680c200311075907151070095186a0900e07845601191400c40104041408407484000b084281ca61088198010700390907005004468a185c4d618181c0501c10f0200900c4292202c0000f0800d920841c0540f640d849482014021502d403414042d120703060588 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 53956838 1106 53955732 53955743
    0x207140609030318060f0606031012060b040b010203090a03120903060e030309070f0312081b07030906090501030608030702040203181c120608060a0c03060503030a0309 74
    0x280ca07109058800003141c0c2c03030401c1d2405099880c0e60700c0499080b80e000200300b15080d030f01c00714002d401900640b0303401d40301e840d0f00340300781c1456003181c05c440c085a01824044040c040c039034000b1800010182c504112005201004a88a00c103100c00326411806411082000407800c006800c0d100b02280f40464843e9200d0740d4074002d50340c107002080740580c400700038441846d400b402080014941155a100c20700e15581d904100d2503a1000d207041400300074000264035941c44505008081540c0d090345607070f1461403070b001e030800002d405180d000482e03101002c109540603105407010f54644100550400d41d50f5404c00001c1e500044c184500441d1115602c2c00000303040103011440180e03010341c40d80c0e2092014000742006225402d0090450500c10104117181740131544c41d800560820020a0382c20a01c2000d030090200c540c00207425202c001655542c1c99030642c0400305162084 = true := by decide +kernel

theorem cover : BRFrame.Cov 53776982 53956838 := by
  have h0 := BRFrame.cov_init 53776982
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53776982 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 53776982 ≤ n) (h2 : n < 53956838) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
